use crate::internal::consts::{self, MAX_REGULAR_STREAM_ID, NO_STREAM};
use crate::internal::{self, Color, ObjType, Timestamp, Validation, Version};
use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use std::io::{self, Read, Write};
use uuid::Uuid;

//===========================================================================//

macro_rules! malformed {
    ($e:expr) => { invalid_data!("Malformed directory entry ({})", $e) };
    ($fmt:expr, $($arg:tt)+) => {
        invalid_data!("Malformed directory entry ({})",
                      format!($fmt, $($arg)+))
    };
}

//===========================================================================//

#[derive(Clone)]
pub struct DirEntry {
    pub name: String,
    pub obj_type: ObjType,
    pub color: Color,
    pub left_sibling: u32,
    pub right_sibling: u32,
    pub child: u32,
    pub clsid: Uuid,
    pub state_bits: u32,
    pub creation_time: Timestamp,
    pub modified_time: Timestamp,
    pub start_sector: u32,
    pub stream_len: u64,
}

impl DirEntry {
    pub fn new(
        name: &str,
        obj_type: ObjType,
        timestamp: Timestamp,
    ) -> DirEntry {
        debug_assert_ne!(obj_type, ObjType::Unallocated);
        DirEntry {
            name: name.to_string(),
            obj_type,
            color: Color::Black,
            left_sibling: consts::NO_STREAM,
            right_sibling: consts::NO_STREAM,
            child: consts::NO_STREAM,
            clsid: Uuid::nil(),
            state_bits: 0,
            creation_time: timestamp,
            modified_time: timestamp,
            start_sector: if obj_type == ObjType::Storage {
                // According to the MS-CFB spec section 2.6.3, the starting
                // sector should be set to zero for storage entries.
                0
            } else {
                consts::END_OF_CHAIN
            },
            stream_len: 0,
        }
    }

    pub fn unallocated() -> DirEntry {
        // According to the MS-CFB spec section 2.6.3, unallocated directory
        // entries must consist of all zeros except for the sibling and child
        // fields, which must be NO_STREAM.
        DirEntry {
            name: String::new(),
            obj_type: ObjType::Unallocated,
            color: Color::Red,
            left_sibling: NO_STREAM,
            right_sibling: NO_STREAM,
            child: NO_STREAM,
            clsid: Uuid::nil(),
            state_bits: 0,
            creation_time: Timestamp::zero(),
            modified_time: Timestamp::zero(),
            start_sector: 0,
            stream_len: 0,
        }
    }

    pub fn empty_root_entry() -> DirEntry {
        DirEntry::new(consts::ROOT_DIR_NAME, ObjType::Root, Timestamp::zero())
    }

    fn read_clsid<R: Read>(reader: &mut R) -> io::Result<Uuid> {
        let d1 = reader.read_u32::<LittleEndian>()?;
        let d2 = reader.read_u16::<LittleEndian>()?;
        let d3 = reader.read_u16::<LittleEndian>()?;
        let mut d4 = [0u8; 8];
        reader.read_exact(&mut d4)?;
        Ok(Uuid::from_fields(d1, d2, d3, &d4))
    }

    fn write_clsid<W: Write>(writer: &mut W, clsid: &Uuid) -> io::Result<()> {
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
        validation: Validation,
    ) -> io::Result<DirEntry> {
        let mut name: String = {
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
            // According to section 2.6.1 of the MS-CFB spec, "The name MUST be
            // terminated with a UTF-16 terminating null character."  (Even
            // though the directory entry aready includes the length of the
            // name.  And also, that length *includes* the null character?
            // Look, CFB is a weird format.)  Anyway, some CFB files in the
            // wild don't do this, so under Permissive validation we don't
            // enforce it.
            if validation.is_strict() && name_chars[name_len_chars] != 0 {
                malformed!("name not null-terminated");
            }
            match String::from_utf16(&name_chars[0..name_len_chars]) {
                Ok(name) => name,
                Err(_) => malformed!("name not valid UTF-16"),
            }
        };

        let obj_type = {
            let obj_type_byte = reader.read_u8()?;
            match ObjType::from_byte(obj_type_byte) {
                Some(obj_type) => obj_type,
                None => malformed!("invalid object type: {}", obj_type_byte),
            }
        };

        // According to section 2.6.2 of the MS-CFB spec, "The root directory
        // entry's Name field MUST contain the null-terminated string 'Root
        // Entry' in Unicode UTF-16."  However, some CFB files in the wild
        // don't do this, so under Permissive validation we don't enforce it;
        // instead, for the root entry we just ignore the actual name in the
        // file and treat it as though it were what it's supposed to be.
        if obj_type == ObjType::Root {
            if name != consts::ROOT_DIR_NAME {
                if validation.is_strict() {
                    malformed!(
                        "root entry name is {:?}, but should be {:?}",
                        name,
                        consts::ROOT_DIR_NAME
                    );
                }
                name = consts::ROOT_DIR_NAME.to_string();
            }
        } else {
            internal::path::validate_name(&name)?;
        }

        let color = {
            let color_byte = reader.read_u8()?;
            match Color::from_byte(color_byte) {
                Some(color) => color,
                None => malformed!("invalid color: {}", color_byte),
            }
        };
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
            if obj_type == ObjType::Stream {
                malformed!("non-empty stream child: {}", child);
            } else if child > MAX_REGULAR_STREAM_ID {
                malformed!("invalid child: {}", child);
            }
        }

        // Section 2.6.1 of the MS-CFB spec states that "In a stream object,
        // this [CLSID] field MUST be set to all zeroes."  However, some CFB
        // files in the wild violate this, so under Permissive validation we
        // don't enforce it; instead, for non-storage objects we just ignore
        // the CLSID data entirely and treat it as though it were nil.
        let mut clsid = DirEntry::read_clsid(reader)?;
        if obj_type == ObjType::Stream && !clsid.is_nil() {
            if validation.is_strict() {
                malformed!("non-null stream CLSID: {:?}", clsid);
            }
            clsid = Uuid::nil();
        }

        let state_bits = reader.read_u32::<LittleEndian>()?;

        // Section 2.6.1 of the MS-CFB spec states that "for a stream object,
        // [creation time and modified time] MUST be all zeroes."  However,
        // under Permissive validation, we don't enforce this, but instead just
        // treat these fields as though they were zero.
        let mut creation_time = Timestamp::read_from(reader)?;
        if obj_type == ObjType::Stream && creation_time != Timestamp::zero() {
            if validation.is_strict() {
                malformed!(
                    "non-zero stream creation time: {}",
                    creation_time.value()
                );
            }
            creation_time = Timestamp::zero();
        }
        let mut modified_time = Timestamp::read_from(reader)?;
        if obj_type == ObjType::Stream && modified_time != Timestamp::zero() {
            if validation.is_strict() {
                malformed!(
                    "non-zero stream modified time: {}",
                    modified_time.value()
                );
            }
            modified_time = Timestamp::zero();
        }

        // According to the MS-CFB spec section 2.6.3, the starting sector and
        // stream length fields should both be set to zero for storage entries.
        // However, some CFB implementations use FREE_SECTOR or END_OF_CHAIN
        // instead for the starting sector, or even just leave these fields
        // with uninitialized garbage values, so under Permissive validation we
        // don't enforce this; instead, for storage objects we just treat these
        // fields as though they were zero.
        let mut start_sector = reader.read_u32::<LittleEndian>()?;
        let mut stream_len =
            reader.read_u64::<LittleEndian>()? & version.stream_len_mask();
        if obj_type == ObjType::Storage {
            if validation.is_strict() && start_sector != 0 {
                malformed!("non-zero storage start sector: {}", start_sector);
            }
            start_sector = 0;
            if validation.is_strict() && stream_len != 0 {
                malformed!("non-zero storage stream length: {}", stream_len);
            }
            stream_len = 0;
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
        writer.write_u8(self.obj_type.as_byte())?;
        writer.write_u8(self.color.as_byte())?;
        writer.write_u32::<LittleEndian>(self.left_sibling)?;
        writer.write_u32::<LittleEndian>(self.right_sibling)?;
        writer.write_u32::<LittleEndian>(self.child)?;
        DirEntry::write_clsid(writer, &self.clsid)?;
        writer.write_u32::<LittleEndian>(self.state_bits)?;
        self.creation_time.write_to(writer)?;
        self.modified_time.write_to(writer)?;
        writer.write_u32::<LittleEndian>(self.start_sector)?;
        writer.write_u64::<LittleEndian>(self.stream_len)?;
        Ok(())
    }
}

//===========================================================================//

#[cfg(test)]
mod tests {
    use super::DirEntry;
    use crate::internal::{
        consts, Color, ObjType, Timestamp, Validation, Version,
    };
    use std::time::UNIX_EPOCH;
    use uuid::Uuid;

    #[test]
    fn parse_valid_storage_entry_with_end_of_chain_start() {
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
            0xfe, 0xff, 0xff, 0xff, // start sector
            0, 0, 0, 0, 0, 0, 0, 0, // stream length
        ];
        let dir_entry = DirEntry::read_from(
            &mut (&input as &[u8]),
            Version::V4,
            Validation::Permissive,
        )
        .unwrap();
        assert_eq!(&dir_entry.name, "Foobar");
        assert_eq!(dir_entry.obj_type, ObjType::Storage);
        assert_eq!(dir_entry.color, Color::Black);
        assert_eq!(dir_entry.left_sibling, 12);
        assert_eq!(dir_entry.right_sibling, 34);
        assert_eq!(dir_entry.child, 56);
        assert_eq!(
            dir_entry.clsid,
            Uuid::parse_str("F29F85E0-4FF9-1068-AB91-08002B27B3D9").unwrap()
        );
        assert_eq!(dir_entry.state_bits, 0xdeadbeef);
        assert_eq!(dir_entry.creation_time, Timestamp::zero());
        assert_eq!(dir_entry.modified_time, Timestamp::zero());
        assert_eq!(dir_entry.start_sector, 0);
        assert_eq!(dir_entry.stream_len, 0);
    }

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
            0, 128, 62, 213, 222, 177, 157, 1, // modified
            0, 0, 0, 0, // start sector
            0, 0, 0, 0, 0, 0, 0, 0, // stream length
        ];
        let dir_entry = DirEntry::read_from(
            &mut (&input as &[u8]),
            Version::V4,
            Validation::Strict,
        )
        .unwrap();
        assert_eq!(&dir_entry.name, "Foobar");
        assert_eq!(dir_entry.obj_type, ObjType::Storage);
        assert_eq!(dir_entry.color, Color::Black);
        assert_eq!(dir_entry.left_sibling, 12);
        assert_eq!(dir_entry.right_sibling, 34);
        assert_eq!(dir_entry.child, 56);
        assert_eq!(
            dir_entry.clsid,
            Uuid::parse_str("F29F85E0-4FF9-1068-AB91-08002B27B3D9").unwrap()
        );
        assert_eq!(dir_entry.state_bits, 0xdeadbeef);
        assert_eq!(dir_entry.creation_time, Timestamp::zero());
        assert_eq!(
            dir_entry.modified_time,
            Timestamp::from_system_time(UNIX_EPOCH)
        );
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
        DirEntry::read_from(
            &mut (&input as &[u8]),
            Version::V4,
            Validation::Permissive,
        )
        .unwrap();
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
        DirEntry::read_from(
            &mut (&input as &[u8]),
            Version::V4,
            Validation::Permissive,
        )
        .unwrap();
    }

    const NON_ZERO_CREATION_TIME_ON_STREAM: [u8; consts::DIR_ENTRY_LEN] = [
        70, 0, 111, 0, 111, 0, 98, 0, 97, 0, 114, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, // name
        14, 0, // name length
        2, // obj type
        1, // color,
        12, 0, 0, 0, // left sibling
        34, 0, 0, 0, // right sibling
        0xff, 0xff, 0xff, 0xff, // child
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // CLSID
        0, 0, 0, 0, // state bits
        37, 0, 0, 0, 0, 0, 0, 0, // created
        0, 0, 0, 0, 0, 0, 0, 0, // modified
        0, 0, 0, 0, // start sector
        0, 0, 0, 0, 0, 0, 0, 0, // stream length
    ];

    #[test]
    #[should_panic(
        expected = "Malformed directory entry (non-zero stream creation time: \
                    37)"
    )]
    fn non_zero_creation_time_on_stream_strict() {
        let mut input: &[u8] = &NON_ZERO_CREATION_TIME_ON_STREAM;
        DirEntry::read_from(&mut input, Version::V4, Validation::Strict)
            .unwrap();
    }

    #[test]
    fn non_zero_creation_time_on_stream_permissive() {
        let mut input: &[u8] = &NON_ZERO_CREATION_TIME_ON_STREAM;
        let dir_entry = DirEntry::read_from(
            &mut input,
            Version::V4,
            Validation::Permissive,
        )
        .unwrap();
        assert_eq!(dir_entry.obj_type, ObjType::Stream);
        assert_eq!(dir_entry.creation_time, Timestamp::zero());
    }

    const NON_ZERO_MODIFIED_TIME_ON_STREAM: [u8; consts::DIR_ENTRY_LEN] = [
        70, 0, 111, 0, 111, 0, 98, 0, 97, 0, 114, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, // name
        14, 0, // name length
        2, // obj type
        1, // color,
        12, 0, 0, 0, // left sibling
        34, 0, 0, 0, // right sibling
        0xff, 0xff, 0xff, 0xff, // child
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // CLSID
        0, 0, 0, 0, // state bits
        0, 0, 0, 0, 0, 0, 0, 0, // created
        0, 1, 0, 0, 0, 0, 0, 0, // modified
        0, 0, 0, 0, // start sector
        0, 0, 0, 0, 0, 0, 0, 0, // stream length
    ];

    #[test]
    #[should_panic(
        expected = "Malformed directory entry (non-zero stream modified time: \
                    256)"
    )]
    fn non_zero_modified_time_on_stream_strict() {
        let mut input: &[u8] = &NON_ZERO_MODIFIED_TIME_ON_STREAM;
        DirEntry::read_from(&mut input, Version::V4, Validation::Strict)
            .unwrap();
    }

    #[test]
    fn non_zero_modified_time_on_stream_permissive() {
        let mut input: &[u8] = &NON_ZERO_MODIFIED_TIME_ON_STREAM;
        let dir_entry = DirEntry::read_from(
            &mut input,
            Version::V4,
            Validation::Permissive,
        )
        .unwrap();
        assert_eq!(dir_entry.obj_type, ObjType::Stream);
        assert_eq!(dir_entry.modified_time, Timestamp::zero());
    }

    const NON_NULL_CLSID_ON_STREAM: [u8; consts::DIR_ENTRY_LEN] = [
        70, 0, 111, 0, 111, 0, 98, 0, 97, 0, 114, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, // name
        14, 0, // name length
        2, // obj type
        1, // color,
        12, 0, 0, 0, // left sibling
        34, 0, 0, 0, // right sibling
        0xff, 0xff, 0xff, 0xff, // child
        1, 2, 3, 4, 5, 6, 7, 8, 9, 8, 7, 6, 5, 4, 3, 2, // CLSID
        0, 0, 0, 0, // state bits
        0, 0, 0, 0, 0, 0, 0, 0, // created
        0, 0, 0, 0, 0, 0, 0, 0, // modified
        0, 0, 0, 0, // start sector
        0, 0, 0, 0, 0, 0, 0, 0, // stream length
    ];

    #[test]
    #[should_panic(
        expected = "Malformed directory entry (non-null stream CLSID: \
                    04030201-0605-0807-0908-070605040302)"
    )]
    fn non_null_clsid_on_stream_strict() {
        let mut input: &[u8] = &NON_NULL_CLSID_ON_STREAM;
        DirEntry::read_from(&mut input, Version::V4, Validation::Strict)
            .unwrap();
    }

    // Regression test for https://github.com/mdsteele/rust-cfb/issues/26
    #[test]
    fn non_null_clsid_on_stream_permissive() {
        let mut input: &[u8] = &NON_NULL_CLSID_ON_STREAM;
        // Section 2.6.1 of the MS-CFB spec states that "In a stream object,
        // this [CLSID] field MUST be set to all zeroes."  However, some CFB
        // files in the wild violate this.  So we allow parsing a stream dir
        // entry with a non-nil CLSID under Permissive validation, but we
        // ignore that CLSID and just set it to all zeroes.
        let dir_entry = DirEntry::read_from(
            &mut input,
            Version::V4,
            Validation::Permissive,
        )
        .unwrap();
        assert_eq!(dir_entry.obj_type, ObjType::Stream);
        assert!(dir_entry.clsid.is_nil());
    }

    const NON_NULL_TERMINATED_NAME: [u8; consts::DIR_ENTRY_LEN] = [
        70, 0, 111, 0, 111, 0, 98, 0, 97, 0, 114, 0, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
        0, // name
        14, 0, // name length
        2, // obj type
        1, // color,
        12, 0, 0, 0, // left sibling
        34, 0, 0, 0, // right sibling
        0xff, 0xff, 0xff, 0xff, // child
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // CLSID
        0, 0, 0, 0, // state bits
        0, 0, 0, 0, 0, 0, 0, 0, // created
        0, 0, 0, 0, 0, 0, 0, 0, // modified
        0, 0, 0, 0, // start sector
        0, 0, 0, 0, 0, 0, 0, 0, // stream length
    ];

    #[test]
    #[should_panic(
        expected = "Malformed directory entry (name not null-terminated)"
    )]
    fn non_null_terminated_name_strict() {
        let mut input: &[u8] = &NON_NULL_TERMINATED_NAME;
        DirEntry::read_from(&mut input, Version::V4, Validation::Strict)
            .unwrap();
    }

    // Regression test for https://github.com/mdsteele/rust-cfb/issues/26
    #[test]
    fn non_null_terminated_name_permissive() {
        let mut input: &[u8] = &NON_NULL_TERMINATED_NAME;
        // According to section 2.6.1 of the MS-CFB spec, "The name MUST be
        // terminated with a UTF-16 terminating null character."  But some CFB
        // files in the wild don't do this, so under Permissive validation we
        // just rely on the name length field.
        let dir_entry = DirEntry::read_from(
            &mut input,
            Version::V4,
            Validation::Permissive,
        )
        .unwrap();
        assert_eq!(dir_entry.name, "Foobar");
    }

    #[test]
    fn nonzero_storage_starting_sector_strict() {
        let mut dir_entry =
            DirEntry::new("Foobar", ObjType::Storage, Timestamp::zero());
        dir_entry.start_sector = 58;
        let mut input = Vec::<u8>::new();
        dir_entry.write_to(&mut input).unwrap();
        let result = DirEntry::read_from(
            &mut input.as_slice(),
            Version::V4,
            Validation::Strict,
        );
        assert_eq!(
            result.err().unwrap().to_string(),
            "Malformed directory entry (non-zero storage start sector: 58)"
        );
    }

    #[test]
    fn nonzero_storage_stream_len_strict() {
        let mut dir_entry =
            DirEntry::new("Foobar", ObjType::Storage, Timestamp::zero());
        dir_entry.stream_len = 574;
        let mut input = Vec::<u8>::new();
        dir_entry.write_to(&mut input).unwrap();
        let result = DirEntry::read_from(
            &mut input.as_slice(),
            Version::V4,
            Validation::Strict,
        );
        assert_eq!(
            result.err().unwrap().to_string(),
            "Malformed directory entry (non-zero storage stream length: 574)"
        );
    }

    // Regression test for https://github.com/mdsteele/rust-cfb/issues/27
    #[test]
    fn nonzero_storage_starting_sector_and_stream_len_permissive() {
        let mut dir_entry =
            DirEntry::new("Foobar", ObjType::Storage, Timestamp::zero());
        dir_entry.start_sector = 58;
        dir_entry.stream_len = 574;
        let mut input = Vec::<u8>::new();
        dir_entry.write_to(&mut input).unwrap();
        // According to section 2.6.3 of the MS-CFB spec, the starting sector
        // location and stream size fields should be set to zero in a storage
        // directory entry.  But some CFB files in the wild don't do this, so
        // when parsing a storage entry under Permissive validation, just
        // ignore those fields' values and pretend they're zero.
        let dir_entry = DirEntry::read_from(
            &mut (&input as &[u8]),
            Version::V4,
            Validation::Permissive,
        )
        .unwrap();
        assert_eq!(dir_entry.obj_type, ObjType::Storage);
        assert_eq!(dir_entry.start_sector, 0);
        assert_eq!(dir_entry.stream_len, 0);
    }

    const ROOT_ENTRY_WITH_INCORRECT_NAME: [u8; consts::DIR_ENTRY_LEN] = [
        70, 0, 111, 0, 111, 0, 98, 0, 97, 0, 114, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, // name
        14, 0, // name length
        5, // obj type
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

    #[test]
    #[should_panic(
        expected = "Malformed directory entry (root entry name is \
                    \\\"Foobar\\\", but should be \\\"Root Entry\\\")"
    )]
    fn root_entry_with_incorrect_name_strict() {
        let mut input: &[u8] = &ROOT_ENTRY_WITH_INCORRECT_NAME;
        DirEntry::read_from(&mut input, Version::V4, Validation::Strict)
            .unwrap();
    }

    // Regression test for https://github.com/mdsteele/rust-cfb/issues/29
    #[test]
    fn root_entry_with_incorrect_name_permissive() {
        let mut input: &[u8] = &ROOT_ENTRY_WITH_INCORRECT_NAME;
        // According to section 2.6.2 of the MS-CFB spec, the name field MUST
        // be set to "Root Entry" in the root directory entry.  But some CFB
        // files in the wild don't do this, so when parsing the root entry
        // under Permissive validation, just ignore the name in the file and
        // pretend it's correct.
        let dir_entry = DirEntry::read_from(
            &mut input,
            Version::V4,
            Validation::Permissive,
        )
        .unwrap();
        assert_eq!(dir_entry.obj_type, ObjType::Root);
        assert_eq!(dir_entry.name, "Root Entry");
    }
}

//===========================================================================//
