use crate::internal::{self, consts, DirEntry};
use std::path::{Path, PathBuf};
use std::time::SystemTime;
use uuid::Uuid;

// ========================================================================= //

/// Metadata about a single object (storage or stream) in a compound file.
#[derive(Clone)]
pub struct Entry {
    name: String,
    path: PathBuf,
    obj_type: u8,
    clsid: Uuid,
    state_bits: u32,
    creation_time: u64,
    modified_time: u64,
    stream_len: u64,
}

impl Entry {
    pub(crate) fn new(dir_entry: &DirEntry, path: PathBuf) -> Entry {
        Entry {
            name: dir_entry.name.clone(),
            path,
            obj_type: dir_entry.obj_type,
            clsid: dir_entry.clsid,
            state_bits: dir_entry.state_bits,
            creation_time: dir_entry.creation_time,
            modified_time: dir_entry.modified_time,
            stream_len: dir_entry.stream_len,
        }
    }

    /// Returns the name of the object that this entry represents.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns the full path to the object that this entry represents.
    pub fn path(&self) -> &Path {
        &self.path
    }

    /// Returns whether this entry is for a stream object (i.e. a "file" within
    /// the compound file).
    pub fn is_stream(&self) -> bool {
        self.obj_type == consts::OBJ_TYPE_STREAM
    }

    /// Returns whether this entry is for a storage object (i.e. a "directory"
    /// within the compound file), either the root or a nested storage.
    pub fn is_storage(&self) -> bool {
        self.obj_type == consts::OBJ_TYPE_STORAGE
            || self.obj_type == consts::OBJ_TYPE_ROOT
    }

    /// Returns whether this entry is specifically for the root storage object
    /// of the compound file.
    pub fn is_root(&self) -> bool {
        self.obj_type == consts::OBJ_TYPE_ROOT
    }

    /// Returns the size, in bytes, of the stream that this metadata is for.
    pub fn len(&self) -> u64 {
        self.stream_len
    }

    /// Returns the CLSID (that is, the object class GUID) for this object.
    /// This will always be all zeros for stream objects.
    pub fn clsid(&self) -> &Uuid {
        &self.clsid
    }

    /// Returns the user-defined bitflags set for this object.
    pub fn state_bits(&self) -> u32 {
        self.state_bits
    }

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
}

// ========================================================================= //

#[derive(Clone, Copy, Eq, PartialEq)]
pub enum EntriesOrder {
    Nonrecursive,
    Preorder,
}

// ========================================================================= //

/// An iterator over the entries in a storage object.
pub struct Entries<'a> {
    order: EntriesOrder,
    directory: &'a Vec<DirEntry>,
    stack: Vec<(PathBuf, u32, bool)>,
}

impl<'a> Entries<'a> {
    pub(crate) fn new(
        order: EntriesOrder,
        directory: &'a Vec<DirEntry>,
        parent_path: PathBuf,
        start: u32,
    ) -> Entries<'a> {
        let mut entries = Entries { order, directory, stack: Vec::new() };
        match order {
            EntriesOrder::Nonrecursive => {
                entries.stack_left_spine(&parent_path, start);
            }
            EntriesOrder::Preorder => {
                entries.stack.push((parent_path, start, false));
            }
        }
        entries
    }

    fn join_path(parent_path: &Path, dir_entry: &DirEntry) -> PathBuf {
        if dir_entry.obj_type == consts::OBJ_TYPE_ROOT {
            parent_path.to_path_buf()
        } else {
            parent_path.join(&dir_entry.name)
        }
    }

    fn stack_left_spine(&mut self, parent_path: &Path, mut current_id: u32) {
        while current_id != consts::NO_STREAM {
            let dir_entry = &self.directory[current_id as usize];
            self.stack.push((parent_path.to_path_buf(), current_id, true));
            current_id = dir_entry.left_sibling;
        }
    }
}

impl<'a> Iterator for Entries<'a> {
    type Item = Entry;

    fn next(&mut self) -> Option<Entry> {
        if let Some((parent, stream_id, visit_siblings)) = self.stack.pop() {
            let dir_entry = &self.directory[stream_id as usize];
            let path = Entries::join_path(&parent, dir_entry);
            if visit_siblings {
                self.stack_left_spine(&parent, dir_entry.right_sibling);
            }
            if self.order == EntriesOrder::Preorder
                && dir_entry.obj_type != consts::OBJ_TYPE_STREAM
                && dir_entry.child != consts::NO_STREAM
            {
                self.stack_left_spine(&path, dir_entry.child);
            }
            Some(Entry::new(dir_entry, path))
        } else {
            None
        }
    }
}

// ========================================================================= //

#[cfg(test)]
mod tests {
    use super::{Entries, EntriesOrder, Entry};
    use crate::internal::consts::{
        NO_STREAM, OBJ_TYPE_ROOT, OBJ_TYPE_STORAGE, OBJ_TYPE_STREAM,
        ROOT_DIR_NAME,
    };
    use crate::internal::DirEntry;
    use std::path::PathBuf;

    fn make_entry(
        name: &str,
        obj_type: u8,
        left: u32,
        child: u32,
        right: u32,
    ) -> DirEntry {
        let mut dir_entry = DirEntry::unallocated();
        dir_entry.name = name.to_string();
        dir_entry.obj_type = obj_type;
        dir_entry.left_sibling = left;
        dir_entry.child = child;
        dir_entry.right_sibling = right;
        dir_entry
    }

    fn make_directory() -> Vec<DirEntry> {
        // Root contains:      3 contains:
        //      5                  8
        //     / \                / \
        //    3   6              7   9
        //   / \
        //  1   4
        //   \
        //    2
        vec![
            make_entry(ROOT_DIR_NAME, OBJ_TYPE_ROOT, NO_STREAM, 5, NO_STREAM),
            make_entry("1", OBJ_TYPE_STREAM, NO_STREAM, NO_STREAM, 2),
            make_entry("2", OBJ_TYPE_STREAM, NO_STREAM, NO_STREAM, NO_STREAM),
            make_entry("3", OBJ_TYPE_STORAGE, 1, 8, 4),
            make_entry("4", OBJ_TYPE_STREAM, NO_STREAM, NO_STREAM, NO_STREAM),
            make_entry("5", OBJ_TYPE_STREAM, 3, NO_STREAM, 6),
            make_entry("6", OBJ_TYPE_STORAGE, NO_STREAM, NO_STREAM, NO_STREAM),
            make_entry("7", OBJ_TYPE_STREAM, NO_STREAM, NO_STREAM, NO_STREAM),
            make_entry("8", OBJ_TYPE_STREAM, 7, NO_STREAM, 9),
            make_entry("9", OBJ_TYPE_STREAM, NO_STREAM, NO_STREAM, NO_STREAM),
        ]
    }

    fn paths_for_entries<'a>(entries: &'a [Entry]) -> Vec<&'a str> {
        entries.iter().map(|entry| entry.path().to_str().unwrap()).collect()
    }

    #[test]
    fn nonrecursive_entries_from_root() {
        let directory = make_directory();
        let entries: Vec<Entry> = Entries::new(
            EntriesOrder::Nonrecursive,
            &directory,
            PathBuf::from("/"),
            5,
        )
        .collect();
        let paths = paths_for_entries(&entries);
        assert_eq!(paths, vec!["/1", "/2", "/3", "/4", "/5", "/6"]);
    }

    #[test]
    fn nonrecursive_entries_from_storage() {
        let directory = make_directory();
        let entries: Vec<Entry> = Entries::new(
            EntriesOrder::Nonrecursive,
            &directory,
            PathBuf::from("/3"),
            8,
        )
        .collect();
        let paths = paths_for_entries(&entries);
        assert_eq!(paths, vec!["/3/7", "/3/8", "/3/9"]);
    }

    #[test]
    fn preorder_entries_from_root() {
        let directory = make_directory();
        let entries: Vec<Entry> = Entries::new(
            EntriesOrder::Preorder,
            &directory,
            PathBuf::from("/"),
            0,
        )
        .collect();
        let paths = paths_for_entries(&entries);
        assert_eq!(
            paths,
            vec![
                "/", "/1", "/2", "/3", "/3/7", "/3/8", "/3/9", "/4", "/5",
                "/6",
            ]
        );
    }

    #[test]
    fn preorder_entries_from_storage() {
        let directory = make_directory();
        let entries: Vec<Entry> = Entries::new(
            EntriesOrder::Preorder,
            &directory,
            PathBuf::from("/"),
            3,
        )
        .collect();
        let paths = paths_for_entries(&entries);
        assert_eq!(paths, vec!["/3", "/3/7", "/3/8", "/3/9"]);
    }
}

// ========================================================================= //
