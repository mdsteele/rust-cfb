use crate::internal::{consts, DirEntry, MiniAllocator, ObjType, Timestamp};
use std::fmt;
use std::path::{Path, PathBuf};
use std::sync::{Arc, OnceLock, RwLock};
use uuid::Uuid;
use web_time::SystemTime;

//===========================================================================//

/// Metadata about a single object (storage or stream) in a compound file.
#[derive(Clone)]
pub struct Entry {
    name: String,
    /// The full path, built when first asked for if the entry came from
    /// iterating over a storage.
    path: OnceLock<PathBuf>,
    /// The storage this entry was found in, if `path` wasn't known up front.
    parent: Option<Arc<PathPrefix>>,
    obj_type: ObjType,
    clsid: Uuid,
    state_bits: u32,
    creation_time: Timestamp,
    modified_time: Timestamp,
    stream_len: u64,
}

impl Entry {
    pub(crate) fn new(dir_entry: &DirEntry, path: PathBuf) -> Entry {
        let mut entry = Entry::new_in_storage(dir_entry, None);
        entry.path = OnceLock::from(path);
        entry
    }

    fn new_in_storage(
        dir_entry: &DirEntry,
        parent: Option<Arc<PathPrefix>>,
    ) -> Entry {
        Entry {
            name: dir_entry.name.clone(),
            path: OnceLock::new(),
            parent,
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
        self.path.get_or_init(|| {
            let parent = self.parent.as_ref().expect("entry without path");
            if self.obj_type == ObjType::Root {
                parent.to_path_buf(None)
            } else {
                parent.to_path_buf(Some(&self.name))
            }
        })
    }

    /// Returns whether this entry is for a stream object (i.e. a "file" within
    /// the compound file).
    pub fn is_stream(&self) -> bool {
        self.obj_type == ObjType::Stream
    }

    /// Returns whether this entry is for a storage object (i.e. a "directory"
    /// within the compound file), either the root or a nested storage.
    pub fn is_storage(&self) -> bool {
        self.obj_type == ObjType::Storage || self.obj_type == ObjType::Root
    }

    /// Returns whether this entry is specifically for the root storage object
    /// of the compound file.
    pub fn is_root(&self) -> bool {
        self.obj_type == ObjType::Root
    }

    /// Returns the size, in bytes, of the stream that this metadata is for.
    pub fn len(&self) -> u64 {
        self.stream_len
    }

    /// Returns true if the stream is empty.
    pub fn is_empty(&self) -> bool {
        self.stream_len == 0
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
        self.creation_time.to_system_time()
    }

    /// Returns the time when the object that this entry represents was last
    /// modified.
    pub fn modified(&self) -> SystemTime {
        self.modified_time.to_system_time()
    }
}

impl fmt::Debug for Entry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(
            f,
            "{path} ({len} bytes)",
            path = self.path().display(),
            len = self.len()
        )
    }
}

//===========================================================================//

/// The path of a storage, as its name plus a link to the storage it is in.
///
/// Storages can be nested without limit, and the path of every entry holds
/// the names of all the storages above it.  Giving each entry its own copy
/// of that path would cost time and memory quadratic in the nesting depth,
/// so entries found by iteration share these instead and only build their
/// full path when asked for it.
pub(crate) struct PathPrefix {
    parent: Option<Arc<PathPrefix>>,
    /// The path that iteration started from, for the outermost prefix.
    base: PathBuf,
    /// The name of the storage.  The root storage and the outermost prefix
    /// have none.
    name: Option<String>,
}

impl PathPrefix {
    fn base(path: PathBuf) -> Arc<PathPrefix> {
        Arc::new(PathPrefix { parent: None, base: path, name: None })
    }

    /// The prefix for what is inside the storage `dir_entry`, which is
    /// itself inside `parent`.
    fn child(
        parent: &Arc<PathPrefix>,
        dir_entry: &DirEntry,
    ) -> Arc<PathPrefix> {
        let name = if dir_entry.obj_type == ObjType::Root {
            None
        } else {
            Some(dir_entry.name.clone())
        };
        Arc::new(PathPrefix {
            parent: Some(parent.clone()),
            base: PathBuf::new(),
            name,
        })
    }

    /// The path of this storage, or of `name` within it.
    fn to_path_buf(&self, name: Option<&str>) -> PathBuf {
        let mut prefixes = Vec::new();
        let mut len = name.map_or(0, |name| name.len() + 1);
        let mut current = Some(self);
        while let Some(prefix) = current {
            len += prefix.base.as_os_str().len()
                + prefix.name.as_ref().map_or(0, |name| name.len() + 1);
            prefixes.push(prefix);
            current = prefix.parent.as_deref();
        }
        let mut path = PathBuf::with_capacity(len);
        for prefix in prefixes.into_iter().rev() {
            if prefix.parent.is_none() {
                path.push(&prefix.base);
            }
            if let Some(name) = prefix.name.as_ref() {
                path.push(name);
            }
        }
        if let Some(name) = name {
            path.push(name);
        }
        path
    }
}

impl Drop for PathPrefix {
    fn drop(&mut self) {
        // Release the storages above this one in a loop; leaving it to the
        // compiler would recurse once per level of nesting.
        let mut parent = self.parent.take();
        while let Some(prefix) = parent {
            parent = match Arc::try_unwrap(prefix) {
                Ok(mut prefix) => prefix.parent.take(),
                Err(_) => None,
            };
        }
    }
}

//===========================================================================//

#[derive(Clone, Copy, Eq, PartialEq)]
pub enum EntriesOrder {
    Nonrecursive,
    Preorder,
}

//===========================================================================//

/// An iterator over the entries in a storage object.
pub struct Entries<'a, F: 'a> {
    order: EntriesOrder,
    // TODO: Consider storing a Weak<RefCell<MiniAllocator<F>>> here instead of
    // a reference to the Rc.  That would allow e.g. opening streams during
    // iteration.  But we'd need to think about how the iterator should behave
    // if the CFB tree structure is modified during iteration.
    minialloc: &'a Arc<RwLock<MiniAllocator<F>>>,
    stack: Vec<(Arc<PathPrefix>, u32, bool)>,
}

impl<'a, F> Entries<'a, F> {
    pub(crate) fn new(
        order: EntriesOrder,
        minialloc: &'a Arc<RwLock<MiniAllocator<F>>>,
        parent_path: PathBuf,
        start: u32,
    ) -> Entries<'a, F> {
        let mut entries = Entries { order, minialloc, stack: Vec::new() };
        let parent = PathPrefix::base(parent_path);
        match order {
            EntriesOrder::Nonrecursive => {
                entries.stack_left_spine(&parent, start);
            }
            EntriesOrder::Preorder => {
                entries.stack.push((parent, start, false));
            }
        }
        entries
    }

    fn stack_left_spine(
        &mut self,
        parent: &Arc<PathPrefix>,
        mut current_id: u32,
    ) {
        let minialloc = self.minialloc.read().unwrap();
        while current_id != consts::NO_STREAM {
            self.stack.push((parent.clone(), current_id, true));
            current_id = minialloc.dir_entry(current_id).left_sibling;
        }
    }
}

impl<'a, F> Iterator for Entries<'a, F> {
    type Item = Entry;

    fn next(&mut self) -> Option<Entry> {
        let (parent, stream_id, visit_siblings) = self.stack.pop()?;
        let (entry, right_sibling, children) = {
            let minialloc = self.minialloc.read().unwrap();
            let dir_entry = minialloc.dir_entry(stream_id);
            let children = if self.order == EntriesOrder::Preorder
                && dir_entry.obj_type != ObjType::Stream
                && dir_entry.child != consts::NO_STREAM
            {
                Some((PathPrefix::child(&parent, dir_entry), dir_entry.child))
            } else {
                None
            };
            let entry = Entry::new_in_storage(dir_entry, Some(parent.clone()));
            (entry, dir_entry.right_sibling, children)
        };
        if visit_siblings {
            self.stack_left_spine(&parent, right_sibling);
        }
        if let Some((prefix, child)) = children {
            self.stack_left_spine(&prefix, child);
        }
        Some(entry)
    }
}

//===========================================================================//

#[cfg(test)]
mod tests {
    use super::{Entries, EntriesOrder, Entry};
    use crate::internal::consts::{self, NO_STREAM, ROOT_DIR_NAME};
    use crate::internal::{
        Allocator, DirEntry, Directory, MiniAllocator, ObjType, Sectors,
        Timestamp, Validation, Version,
    };
    use std::path::{Path, PathBuf};
    use std::sync::{Arc, RwLock};

    fn make_entry(
        name: &str,
        obj_type: ObjType,
        left: u32,
        child: u32,
        right: u32,
    ) -> DirEntry {
        let mut dir_entry = DirEntry::new(name, obj_type, Timestamp::zero());
        dir_entry.left_sibling = left;
        dir_entry.child = child;
        dir_entry.right_sibling = right;
        dir_entry
    }

    fn make_minialloc() -> Arc<RwLock<MiniAllocator<()>>> {
        // Root contains:      3 contains:
        //      5                  8
        //     / \                / \
        //    3   6              7   9
        //   / \
        //  1   4
        //   \
        //    2
        let dir_entries = vec![
            make_entry(ROOT_DIR_NAME, ObjType::Root, NO_STREAM, 5, NO_STREAM),
            make_entry("1", ObjType::Stream, NO_STREAM, NO_STREAM, 2),
            make_entry("2", ObjType::Stream, NO_STREAM, NO_STREAM, NO_STREAM),
            make_entry("3", ObjType::Storage, 1, 8, 4),
            make_entry("4", ObjType::Stream, NO_STREAM, NO_STREAM, NO_STREAM),
            make_entry("5", ObjType::Stream, 3, NO_STREAM, 6),
            make_entry("6", ObjType::Storage, NO_STREAM, NO_STREAM, NO_STREAM),
            make_entry("7", ObjType::Stream, NO_STREAM, NO_STREAM, NO_STREAM),
            make_entry("8", ObjType::Stream, 7, NO_STREAM, 9),
            make_entry("9", ObjType::Stream, NO_STREAM, NO_STREAM, NO_STREAM),
        ];
        let version = Version::V3;
        let sectors =
            Sectors::new(version, 3 * version.sector_len() as u64, ());
        let allocator = Allocator::new(
            sectors,
            vec![],
            vec![0],
            vec![consts::FAT_SECTOR, consts::END_OF_CHAIN],
            Validation::Strict,
        )
        .unwrap();
        let directory =
            Directory::new(allocator, dir_entries, 1, Validation::Strict)
                .unwrap();
        let minialloc = MiniAllocator::new(
            directory,
            vec![],
            consts::END_OF_CHAIN,
            Validation::Strict,
        )
        .unwrap();
        Arc::new(RwLock::new(minialloc))
    }

    fn paths_for_entries(entries: &[Entry]) -> Vec<&Path> {
        entries.iter().map(|entry| entry.path()).collect()
    }

    #[test]
    fn nonrecursive_entries_from_root() {
        let minialloc = make_minialloc();
        let entries: Vec<Entry> = Entries::new(
            EntriesOrder::Nonrecursive,
            &minialloc,
            PathBuf::from("/"),
            5,
        )
        .collect();
        let paths = paths_for_entries(&entries);
        assert_eq!(
            paths,
            vec![
                Path::new("/1"),
                Path::new("/2"),
                Path::new("/3"),
                Path::new("/4"),
                Path::new("/5"),
                Path::new("/6")
            ]
        );
    }

    #[test]
    fn nonrecursive_entries_from_storage() {
        let minialloc = make_minialloc();
        let entries: Vec<Entry> = Entries::new(
            EntriesOrder::Nonrecursive,
            &minialloc,
            PathBuf::from("/3"),
            8,
        )
        .collect();
        let paths = paths_for_entries(&entries);
        assert_eq!(
            paths,
            vec![Path::new("/3/7"), Path::new("/3/8"), Path::new("/3/9")]
        );
    }

    #[test]
    fn preorder_entries_from_root() {
        let minialloc = make_minialloc();
        let entries: Vec<Entry> = Entries::new(
            EntriesOrder::Preorder,
            &minialloc,
            PathBuf::from("/"),
            0,
        )
        .collect();
        let paths = paths_for_entries(&entries);
        assert_eq!(
            paths,
            vec![
                Path::new("/"),
                Path::new("/1"),
                Path::new("/2"),
                Path::new("/3"),
                Path::new("/3/7"),
                Path::new("/3/8"),
                Path::new("/3/9"),
                Path::new("/4"),
                Path::new("/5"),
                Path::new("/6"),
            ]
        );
    }

    #[test]
    fn preorder_entries_from_storage() {
        let minialloc = make_minialloc();
        let entries: Vec<Entry> = Entries::new(
            EntriesOrder::Preorder,
            &minialloc,
            PathBuf::from("/"),
            3,
        )
        .collect();
        let paths = paths_for_entries(&entries);
        assert_eq!(
            paths,
            vec![
                Path::new("/3"),
                Path::new("/3/7"),
                Path::new("/3/8"),
                Path::new("/3/9")
            ]
        );
    }
}

//===========================================================================//
