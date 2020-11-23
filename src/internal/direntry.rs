use crate::internal::consts::{self, MAX_REGULAR_STREAM_ID, NO_STREAM};
use crate::internal::{self, Version};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use std::io::{self, Read, Write};
use uuid::Uuid;

// ========================================================================= //

macro_rules! malformed {
    ($e:expr) => { invalid_data!("Malformed directory entry ({})", $e) };
    ($fmt:expr, $($arg:tt)+) => {
        invalid_data!("Malformed directory entry ({})",
                      format!($fmt, $($arg)+))
    };
}

// ========================================================================= //

#[derive(Clone)]
pub struct DirEntry {
    pub name: String,
    pub obj_type: u8,
    pub color: u8,
    pub left_sibling: u32,
    pub right_sibling: u32,
    pub child: u32,
    pub clsid: Uuid,
    pub state_bits: u32,
    pub creation_time: u64,
    pub modified_time: u64,
    pub start_sector: u32,
    pub stream_len: u64,
}

impl DirEntry {
    pub fn unallocated() -> DirEntry {
        DirEntry {
            name: String::new(),
            obj_type: consts::OBJ_TYPE_UNALLOCATED,
            color: 0,
            left_sibling: NO_STREAM,
            right_sibling: NO_STREAM,
            child: NO_STREAM,
            clsid: Uuid::nil(),
            state_bits: 0,
            creation_time: 0,
            modified_time: 0,
            start_sector: 0,
            stream_len: 0,
        }
    }

    pub fn read_clsid<R: Read>(reader: &mut R) -> io::Result<Uuid> {
        let d1 = reader.read_u32::<LittleEndian>()?;
        let d2 = reader.read_u16::<LittleEndian>()?;
        let d3 = reader.read_u16::<LittleEndian>()?;
        let mut d4 = [0u8; 8];
        reader.read_exact(&mut d4)?;
        Ok(Uuid::from_fields(d1, d2, d3, &d4).unwrap())
    }

    pub fn write_clsid<W: Write>(
        writer: &mut W,
        clsid: &Uuid,
    ) -> io::Result<()> {
        let (d1, d2, d3, d4) = clsid.as_fields();
        writer.write_u32::<LittleEndian>(d1)?;
        writer.write_u16::<LittleEndian>(d2)?;
        writer.write_u16::<LittleEndian>(d3)?;
        writer.write_all(d4)?;
        Ok(())
    }

    pub fn read_from<R: Read>(
        reader: &mut R,
        version: Version,
    ) -> io::Result<DirEntry> {
        let name: String = {
            let mut name_chars: Vec<u16> = Vec::with_capacity(32);
            for _ in 0..32 {
                name_chars.push(reader.read_u16::<LittleEndian>()?);
            }
            let name_len_bytes = reader.read_u16::<LittleEndian>()?;
            if name_len_bytes > 64 {
                malformed!("name length too large: {}", name_len_bytes);
            } else if name_len_bytes % 2 != 0 {
                malformed!("odd name length: {}", name_len_bytes);
            }
            let name_len_chars = if name_len_bytes > 0 {
                (name_len_bytes / 2 - 1) as usize
            } else {
                0
            };
            debug_assert!(name_len_chars < name_chars.len());
            if name_chars[name_len_chars] != 0 {
                malformed!("name not null-terminated");
            }
            match String::from_utf16(&name_chars[0..name_len_chars]) {
                Ok(name) => name,
                Err(_) => malformed!("name not valid UTF-16"),
            }
        };
        internal::path::validate_name(&name)?;
        let obj_type = reader.read_u8()?;
        if obj_type != consts::OBJ_TYPE_UNALLOCATED
            && obj_type != consts::OBJ_TYPE_STORAGE
            && obj_type != consts::OBJ_TYPE_STREAM
            && obj_type != consts::OBJ_TYPE_ROOT
        {
            malformed!("invalid object type: {}", obj_type);
        }
        let color = reader.read_u8()?;
        if color != consts::COLOR_RED && color != consts::COLOR_BLACK {
            malformed!("invalid color: {}", color);
        }
        let left_sibling = reader.read_u32::<LittleEndian>()?;
        if left_sibling != NO_STREAM && left_sibling > MAX_REGULAR_STREAM_ID {
            malformed!("invalid left sibling: {}", left_sibling);
        }
        let right_sibling = reader.read_u32::<LittleEndian>()?;
        if right_sibling != NO_STREAM && right_sibling > MAX_REGULAR_STREAM_ID
        {
            malformed!("invalid right sibling: {}", right_sibling);
        }
        let child = reader.read_u32::<LittleEndian>()?;
        if child != NO_STREAM {
            if obj_type == consts::OBJ_TYPE_STREAM {
                malformed!("non-empty stream child: {}", child);
            } else if child > MAX_REGULAR_STREAM_ID {
                malformed!("invalid child: {}", child);
            }
        }
        let clsid = DirEntry::read_clsid(reader)?;
        if obj_type == consts::OBJ_TYPE_STREAM && !clsid.is_nil() {
            malformed!("non-null stream CLSID: {:?}", clsid);
        }
        let state_bits = reader.read_u32::<LittleEndian>()?;
        let creation_time = reader.read_u64::<LittleEndian>()?;
        let modified_time = reader.read_u64::<LittleEndian>()?;
        let start_sector = reader.read_u32::<LittleEndian>()?;

        // Spec say this is suppose to be zero for DirEntries
        // but some cfb implementations set start_sector to FREE_SECTOR instead
        if obj_type == consts::OBJ_TYPE_STORAGE
            && !(start_sector == 0 || start_sector == consts::FREE_SECTOR)
        {
            malformed!("non-zero storage start sector: {}", start_sector);
        }
        let stream_len =
            reader.read_u64::<LittleEndian>()? & version.stream_len_mask();
        if obj_type == consts::OBJ_TYPE_STORAGE && stream_len != 0 {
            malformed!("non-zero storage stream length: {}", stream_len);
        }
        Ok(DirEntry {
            name,
            obj_type,
            color,
            left_sibling,
            right_sibling,
            child,
            clsid,
            state_bits,
            creation_time,
            modified_time,
            start_sector,
            stream_len,
        })
    }

    pub fn write_to<W: Write>(&self, writer: &mut W) -> io::Result<()> {
        debug_assert!(internal::path::validate_name(&self.name).is_ok());
        let name_utf16: Vec<u16> = self.name.encode_utf16().collect();
        debug_assert!(name_utf16.len() < 32);
        for &chr in name_utf16.iter() {
            writer.write_u16::<LittleEndian>(chr)?;
        }
        for _ in name_utf16.len()..32 {
            writer.write_u16::<LittleEndian>(0)?;
        }
        writer.write_u16::<LittleEndian>((name_utf16.len() as u16 + 1) * 2)?;
        writer.write_u8(self.obj_type)?;
        writer.write_u8(self.color)?;
        writer.write_u32::<LittleEndian>(self.left_sibling)?;
        writer.write_u32::<LittleEndian>(self.right_sibling)?;
        writer.write_u32::<LittleEndian>(self.child)?;
        DirEntry::write_clsid(writer, &self.clsid)?;
        writer.write_u32::<LittleEndian>(self.state_bits)?;
        writer.write_u64::<LittleEndian>(self.creation_time)?;
        writer.write_u64::<LittleEndian>(self.modified_time)?;
        writer.write_u32::<LittleEndian>(self.start_sector)?;
        writer.write_u64::<LittleEndian>(self.stream_len)?;
        Ok(())
    }
}

// ========================================================================= //

#[cfg(test)]
mod tests {
    use super::DirEntry;
    use crate::internal::consts;
    use crate::internal::Version;
    use uuid::Uuid;

    #[test]
    fn parse_valid_storage_entry() {
        let input: [u8; consts::DIR_ENTRY_LEN] = [
            // Name:
            70, 0, 111, 0, 111, 0, 98, 0, 97, 0, 114, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 14, 0, // name length
            1, // obj type
            1, // color,
            12, 0, 0, 0, // left sibling
            34, 0, 0, 0, // right sibling
            56, 0, 0, 0, // child
            0xe0, 0x85, 0x9f, 0xf2, 0xf9, 0x4f, 0x68, 0x10, // CLSID
            0xab, 0x91, 0x08, 0x00, 0x2b, 0x27, 0xb3, 0xd9, // CLSID
            239, 190, 173, 222, // state bits
            0, 0, 0, 0, 0, 0, 0, 0, // created
            0, 0, 0, 0, 0, 0, 0, 0, // modified
            0, 0, 0, 0, // start sector
            0, 0, 0, 0, 0, 0, 0, 0, // stream length
        ];
        let dir_entry =
            DirEntry::read_from(&mut (&input as &[u8]), Version::V4).unwrap();
        assert_eq!(&dir_entry.name, "Foobar");
        assert_eq!(dir_entry.obj_type, consts::OBJ_TYPE_STORAGE);
        assert_eq!(dir_entry.color, consts::COLOR_BLACK);
        assert_eq!(dir_entry.left_sibling, 12);
        assert_eq!(dir_entry.right_sibling, 34);
        assert_eq!(dir_entry.child, 56);
        assert_eq!(
            dir_entry.clsid,
            Uuid::parse_str("F29F85E0-4FF9-1068-AB91-08002B27B3D9").unwrap()
        );
        assert_eq!(dir_entry.state_bits, 0xdeadbeef);
        assert_eq!(dir_entry.creation_time, 0);
        assert_eq!(dir_entry.modified_time, 0);
        assert_eq!(dir_entry.start_sector, 0);
        assert_eq!(dir_entry.stream_len, 0);
    }

    #[test]
    #[should_panic(expected = "Malformed directory entry \
                               (invalid object type: 3)")]
    fn invalid_object_type() {
        let input: [u8; consts::DIR_ENTRY_LEN] = [
            // Name:
            70, 0, 111, 0, 111, 0, 98, 0, 97, 0, 114, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 14, 0, // name length
            3, // obj type
            1, // color,
            12, 0, 0, 0, // left sibling
            34, 0, 0, 0, // right sibling
            56, 0, 0, 0, // child
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // CLSID
            239, 190, 173, 222, // state bits
            0, 0, 0, 0, 0, 0, 0, 0, // created
            0, 0, 0, 0, 0, 0, 0, 0, // modified
            0, 0, 0, 0, // start sector
            0, 0, 0, 0, 0, 0, 0, 0, // stream length
        ];
        DirEntry::read_from(&mut (&input as &[u8]), Version::V4).unwrap();
    }

    #[test]
    #[should_panic(expected = "Malformed directory entry (invalid color: 2)")]
    fn invalid_color() {
        let input: [u8; consts::DIR_ENTRY_LEN] = [
            // Name:
            70, 0, 111, 0, 111, 0, 98, 0, 97, 0, 114, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 14, 0, // name length
            1, // obj type
            2, // color,
            12, 0, 0, 0, // left sibling
            34, 0, 0, 0, // right sibling
            56, 0, 0, 0, // child
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // CLSID
            239, 190, 173, 222, // state bits
            0, 0, 0, 0, 0, 0, 0, 0, // created
            0, 0, 0, 0, 0, 0, 0, 0, // modified
            0, 0, 0, 0, // start sector
            0, 0, 0, 0, 0, 0, 0, 0, // stream length
        ];
        DirEntry::read_from(&mut (&input as &[u8]), Version::V4).unwrap();
    }
}

// ========================================================================= //
