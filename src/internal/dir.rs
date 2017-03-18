use byteorder::{LittleEndian, ReadBytesExt, WriteBytesExt};
use internal;
use internal::consts::{self, MAX_REGULAR_STREAM_ID, NO_STREAM};
use internal::version::Version;
use std::io::{self, Read, Write};

// ========================================================================= //

pub struct DirEntry {
    pub name: String,
    pub obj_type: u8,
    pub color: u8,
    pub left_sibling: u32,
    pub right_sibling: u32,
    pub child: u32,
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
            // Values of fields below don't really matter:
            color: 0,
            left_sibling: 0,
            right_sibling: 0,
            child: 0,
            state_bits: 0,
            creation_time: 0,
            modified_time: 0,
            start_sector: 0,
            stream_len: 0,
        }
    }

    pub fn read<R: Read>(reader: &mut R, version: Version)
                         -> io::Result<DirEntry> {
        let name: String = {
            let mut name_chars: Vec<u16> = Vec::with_capacity(32);
            for _ in 0..32 {
                name_chars.push(reader.read_u16::<LittleEndian>()?);
            }
            let name_len_bytes = reader.read_u16::<LittleEndian>()?;
            if name_len_bytes > 64 || name_len_bytes % 2 != 0 {
                invalid_data!("Invalid name length ({}) in directory entry",
                              name_len_bytes);
            }
            let name_len_chars = if name_len_bytes > 0 {
                (name_len_bytes / 2 - 1) as usize
            } else {
                0
            };
            debug_assert!(name_len_chars < name_chars.len());
            if name_chars[name_len_chars] != 0 {
                invalid_data!("Directory entry name must be null-terminated");
            }
            String::from_utf16_lossy(&name_chars[0..name_len_chars])
        };
        internal::path::validate_name(&name)?;
        let obj_type = reader.read_u8()?;
        let color = reader.read_u8()?;
        if color != consts::COLOR_RED && color != consts::COLOR_BLACK {
            invalid_data!("Invalid color in directory entry ({})", color);
        }
        let left_sibling = reader.read_u32::<LittleEndian>()?;
        if left_sibling != NO_STREAM && left_sibling > MAX_REGULAR_STREAM_ID {
            invalid_data!("Invalid left sibling in directory entry ({})",
                          left_sibling);
        }
        let right_sibling = reader.read_u32::<LittleEndian>()?;
        if right_sibling != NO_STREAM &&
           right_sibling > MAX_REGULAR_STREAM_ID {
            invalid_data!("Invalid right sibling in directory entry ({})",
                          right_sibling);
        }
        let child = reader.read_u32::<LittleEndian>()?;
        if child != NO_STREAM && child > MAX_REGULAR_STREAM_ID {
            invalid_data!("Invalid child in directory entry ({})", child);
        }
        let mut clsid = [0u8; 16];
        reader.read_exact(&mut clsid)?;
        let state_bits = reader.read_u32::<LittleEndian>()?;
        let creation_time = reader.read_u64::<LittleEndian>()?;
        let modified_time = reader.read_u64::<LittleEndian>()?;
        let start_sector = reader.read_u32::<LittleEndian>()?;
        let stream_len = reader.read_u64::<LittleEndian>()? &
                         version.stream_len_mask();
        Ok(DirEntry {
            name: name,
            obj_type: obj_type,
            color: color,
            left_sibling: left_sibling,
            right_sibling: right_sibling,
            child: child,
            state_bits: state_bits,
            creation_time: creation_time,
            modified_time: modified_time,
            start_sector: start_sector,
            stream_len: stream_len,
        })
    }

    pub fn write<W: Write>(&self, writer: &mut W) -> io::Result<()> {
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
        writer.write_all(&[0; 16])?; // TODO: CLSID
        writer.write_u32::<LittleEndian>(self.state_bits)?;
        writer.write_u64::<LittleEndian>(self.creation_time)?;
        writer.write_u64::<LittleEndian>(self.modified_time)?;
        writer.write_u32::<LittleEndian>(self.start_sector)?;
        writer.write_u64::<LittleEndian>(self.stream_len)?;
        Ok(())
    }
}

// ========================================================================= //
