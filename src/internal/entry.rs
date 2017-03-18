use internal;
use internal::consts;
use internal::dir::DirEntry;
use std::path::{Path, PathBuf};
use std::time::SystemTime;

// ========================================================================= //

/// Metadata about a single object (storage or stream) in a compound file.
#[derive(Clone)]
pub struct Entry {
    name: String,
    path: PathBuf,
    obj_type: u8,
    creation_time: u64,
    modified_time: u64,
    stream_len: u64,
}

pub fn new_entry(dir_entry: &DirEntry, path: PathBuf) -> Entry {
    Entry {
        name: dir_entry.name.clone(),
        path: path,
        obj_type: dir_entry.obj_type,
        creation_time: dir_entry.creation_time,
        modified_time: dir_entry.modified_time,
        stream_len: dir_entry.stream_len,
    }
}


impl Entry {
    /// Returns the name of the object that this entry represents.
    pub fn name(&self) -> &str { &self.name }

    /// Returns the full path to the object that this entry represents.
    pub fn path(&self) -> &Path { &self.path }

    /// Returns whether this entry is for a stream object (i.e. a "file" within
    /// the compound file).
    pub fn is_stream(&self) -> bool {
        self.obj_type == consts::OBJ_TYPE_STREAM
    }

    /// Returns whether this entry is for a storage object (i.e. a "directory"
    /// within the compound file), either the root or a nested storage.
    pub fn is_storage(&self) -> bool {
        self.obj_type == consts::OBJ_TYPE_STORAGE ||
        self.obj_type == consts::OBJ_TYPE_ROOT
    }

    /// Returns whether this entry is specifically for the root storage object
    /// of the compound file.
    pub fn is_root(&self) -> bool { self.obj_type == consts::OBJ_TYPE_ROOT }

    /// Returns the size, in bytes, of the stream that this metadata is for.
    pub fn len(&self) -> u64 { self.stream_len }

    /// Returns the time when the object that this entry represents was
    /// created.
    pub fn created(&self) -> SystemTime {
        internal::time::system_time_from_timestamp(self.creation_time)
    }

    /// Returns the time when the object that this entry represents was last
    /// modified.
    pub fn modified(&self) -> SystemTime {
        internal::time::system_time_from_timestamp(self.modified_time)
    }

    // TODO: CLSID
    // TODO: state bits
}

// ========================================================================= //

/// Iterator over the entries in a storage object.
pub struct Entries<'a> {
    directory: &'a Vec<DirEntry>,
    path: PathBuf,
    stack: Vec<u32>,
    current: u32,
}

pub fn new_entries<'a>(directory: &'a Vec<DirEntry>, path: PathBuf,
                       start: u32)
                       -> Entries<'a> {
    Entries {
        directory: directory,
        path: path,
        stack: Vec::new(),
        current: start,
    }
}

impl<'a> Iterator for Entries<'a> {
    type Item = Entry;

    fn next(&mut self) -> Option<Entry> {
        while self.current != consts::NO_STREAM {
            self.stack.push(self.current);
            self.current = self.directory[self.current as usize].left_sibling;
        }
        if let Some(parent) = self.stack.pop() {
            let dir_entry = &self.directory[parent as usize];
            self.current = dir_entry.right_sibling;
            Some(new_entry(dir_entry, self.path.join(&dir_entry.name)))
        } else {
            None
        }
    }
}

// ========================================================================= //
