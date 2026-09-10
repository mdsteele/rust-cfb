use crate::internal::{
    self, consts, Allocator, Chain, Color, DirEntry, ObjType, Sector,
    SectorInit, Timestamp, Validation, Version,
};
use crate::WriteLeNumber;
use fnv::{FnvHashMap, FnvHashSet};
use std::cmp::Ordering;
use std::io::{self, Seek, Write};

//===========================================================================//

macro_rules! malformed {
    ($e:expr) => { invalid_data!("Malformed directory ({})", $e) };
    ($fmt:expr, $($arg:tt)+) => {
        invalid_data!("Malformed directory ({})", format!($fmt, $($arg)+))
    };
}

//===========================================================================//

/// What points at the root of a subtree of a storage's sibling tree: either
/// the storage's own `child` field, or a sibling pointer of another node.
#[derive(Clone, Copy)]
enum Link {
    Storage(u32),
    Node(u32),
}

//===========================================================================//

/// A wrapper around the sector allocator that additionally provides management
/// of the CFB directory chain.
pub struct Directory<F> {
    allocator: Allocator<F>,
    dir_entries: Vec<DirEntry>,
    /// The sector IDs of the directory chain, in order. Locating the slot of
    /// a directory entry in the file only needs an index into this; walking
    /// the FAT chain from the start for every entry write made creating `n`
    /// entries cost `O(n²)`. The chain only ever grows (see
    /// `allocate_dir_entry`), so it is walked once and extended in place.
    dir_sector_ids: Vec<u32>,
    /// Stream IDs of unallocated directory entries, available for reuse;
    /// the lowest one is on top.
    free_entries: Vec<u32>,
    /// Every entry's stream ID by `(parent stream ID, name key)`. Files
    /// written by other implementations often have unbalanced sibling trees,
    /// which would make a lookup by walking the tree cost `O(siblings)`; the
    /// index makes it `O(1)` whatever shape the tree is in.
    name_index: FnvHashMap<(u32, (usize, String)), u32>,
}

impl<F> Directory<F> {
    pub fn new(
        allocator: Allocator<F>,
        dir_entries: Vec<DirEntry>,
        dir_start_sector: u32,
        validation: Validation,
    ) -> io::Result<Directory<F>> {
        let mut directory = Directory {
            allocator,
            dir_entries,
            dir_sector_ids: Vec::new(),
            free_entries: Vec::new(),
            name_index: FnvHashMap::default(),
        };
        directory.validate(validation)?;
        directory.dir_sector_ids = directory
            .allocator
            .open_chain(dir_start_sector, SectorInit::Dir)?
            .sector_ids()
            .to_vec();
        directory.free_entries = directory
            .dir_entries
            .iter()
            .enumerate()
            .rev()
            .filter(|(_, entry)| entry.obj_type == ObjType::Unallocated)
            .map(|(stream_id, _)| stream_id as u32)
            .collect();
        directory.build_name_index();
        Ok(directory)
    }

    /// Moves the index entries of the sibling tree rooted at `child` — the
    /// children of one storage — from `old_parent` to `new_parent`.
    fn rekey_children(
        &mut self,
        child: u32,
        old_parent: u32,
        new_parent: u32,
    ) {
        let mut stack = vec![child];
        while let Some(stream_id) = stack.pop() {
            if stream_id == consts::NO_STREAM {
                continue;
            }
            let dir_entry = self.dir_entry(stream_id);
            let key = internal::path::name_key(&dir_entry.name);
            stack.push(dir_entry.left_sibling);
            stack.push(dir_entry.right_sibling);
            self.name_index.remove(&(old_parent, key.clone()));
            self.name_index.insert((new_parent, key), stream_id);
        }
    }

    /// Fills `name_index` from the sibling trees, visiting every entry once.
    fn build_name_index(&mut self) {
        let mut index = FnvHashMap::default();
        let mut stack = vec![(consts::ROOT_STREAM_ID, consts::ROOT_STREAM_ID)];
        while let Some((stream_id, parent_id)) = stack.pop() {
            let dir_entry = self.dir_entry(stream_id);
            if stream_id != consts::ROOT_STREAM_ID {
                index.insert(
                    (parent_id, internal::path::name_key(&dir_entry.name)),
                    stream_id,
                );
            }
            for sibling in [dir_entry.left_sibling, dir_entry.right_sibling] {
                if sibling != consts::NO_STREAM {
                    stack.push((sibling, parent_id));
                }
            }
            if dir_entry.child != consts::NO_STREAM {
                stack.push((dir_entry.child, stream_id));
            }
        }
        self.name_index = index;
    }

    pub fn version(&self) -> Version {
        self.allocator.version()
    }

    pub fn inner(&self) -> &F {
        self.allocator.inner()
    }

    pub fn sector_len(&self) -> usize {
        self.allocator.sector_len()
    }

    pub fn into_inner(self) -> F {
        self.allocator.into_inner()
    }

    pub fn stream_id_for_name_chain(&self, names: &[&str]) -> Option<u32> {
        let mut stream_id = consts::ROOT_STREAM_ID;
        for name in names.iter() {
            let key = (stream_id, internal::path::name_key(name));
            stream_id = *self.name_index.get(&key)?;
        }
        Some(stream_id)
    }

    pub fn open_chain(
        &mut self,
        start_sector_id: u32,
        init: SectorInit,
    ) -> io::Result<Chain<'_, F>> {
        self.allocator.open_chain(start_sector_id, init)
    }

    pub fn root_dir_entry(&self) -> &DirEntry {
        self.dir_entry(consts::ROOT_STREAM_ID)
    }

    pub fn dir_entry(&self, stream_id: u32) -> &DirEntry {
        &self.dir_entries[stream_id as usize]
    }

    fn dir_entry_mut(&mut self, stream_id: u32) -> &mut DirEntry {
        &mut self.dir_entries[stream_id as usize]
    }

    fn validate(&self, validation: Validation) -> io::Result<()> {
        if self.dir_entries.is_empty() {
            malformed!("root entry is missing");
        }
        let root_entry = self.root_dir_entry();
        if root_entry.stream_len % consts::MINI_SECTOR_LEN as u64 != 0 {
            malformed!(
                "root stream len is {}, but should be multiple of {}",
                root_entry.stream_len,
                consts::MINI_SECTOR_LEN
            );
        }
        let mut visited = FnvHashSet::default();
        let mut stack = vec![(consts::ROOT_STREAM_ID, false)];
        while let Some((stream_id, parent_is_red)) = stack.pop() {
            if visited.contains(&stream_id) {
                malformed!("loop in tree");
            }
            visited.insert(stream_id);
            let dir_entry = self.dir_entry(stream_id);
            if stream_id == consts::ROOT_STREAM_ID {
                if dir_entry.obj_type != ObjType::Root {
                    malformed!(
                        "root entry has object type {:?}",
                        dir_entry.obj_type
                    );
                }
            } else if dir_entry.obj_type != ObjType::Storage
                && dir_entry.obj_type != ObjType::Stream
            {
                malformed!(
                    "non-root entry with object type {:?}",
                    dir_entry.obj_type
                );
            }
            let node_is_red = dir_entry.color == Color::Red;
            // The MS-CFB spec section 2.6.4 says that two consecutive nodes in
            // the red-black tree for siblings within a storage object MUST NOT
            // both be red, but apparently some implementations don't obey this
            // (see https://github.com/mdsteele/rust-cfb/issues/10).  We still
            // want to be able to read these files, so we only consider this an
            // error under Strict validation.
            if parent_is_red && node_is_red && validation.is_strict() {
                malformed!("RB tree has adjacent red nodes");
            }
            let left_sibling = dir_entry.left_sibling;
            if left_sibling != consts::NO_STREAM {
                if left_sibling as usize >= self.dir_entries.len() {
                    malformed!(
                        "left sibling index is {}, but directory entry count \
                         is {}",
                        left_sibling,
                        self.dir_entries.len()
                    );
                }
                let entry = &self.dir_entry(left_sibling);
                if internal::path::compare_names(&entry.name, &dir_entry.name)
                    != Ordering::Less
                {
                    malformed!(
                        "name ordering, {:?} vs {:?}",
                        dir_entry.name,
                        entry.name
                    );
                }
                stack.push((left_sibling, node_is_red));
            }
            let right_sibling = dir_entry.right_sibling;
            if right_sibling != consts::NO_STREAM {
                if right_sibling as usize >= self.dir_entries.len() {
                    malformed!(
                        "right sibling index is {}, but directory entry count \
                         is {}",
                        right_sibling, self.dir_entries.len());
                }
                let entry = &self.dir_entry(right_sibling);
                if internal::path::compare_names(&dir_entry.name, &entry.name)
                    != Ordering::Less
                {
                    malformed!(
                        "name ordering, {:?} vs {:?}",
                        dir_entry.name,
                        entry.name
                    );
                }
                stack.push((right_sibling, node_is_red));
            }
            let child = dir_entry.child;
            if child != consts::NO_STREAM {
                if child as usize >= self.dir_entries.len() {
                    malformed!(
                        "child index is {}, but directory entry count is {}",
                        child,
                        self.dir_entries.len()
                    );
                }
                stack.push((child, false));
            }
        }
        Ok(())
    }

    /// Sets the color of a node, remembering it as needing to be written.
    fn set_color(
        &mut self,
        stream_id: u32,
        color: Color,
        dirty: &mut Vec<u32>,
    ) {
        self.dir_entry_mut(stream_id).color = color;
        dirty.push(stream_id);
    }

    /// Makes whatever pointed at `old` (a subtree root) point at `new`.
    fn relink(&mut self, up: Link, old: u32, new: u32, dirty: &mut Vec<u32>) {
        match up {
            Link::Storage(parent_id) => {
                debug_assert_eq!(self.dir_entry(parent_id).child, old);
                self.dir_entry_mut(parent_id).child = new;
                dirty.push(parent_id);
            }
            Link::Node(node_id) => {
                let node = self.dir_entry_mut(node_id);
                if node.left_sibling == old {
                    node.left_sibling = new;
                } else {
                    debug_assert_eq!(node.right_sibling, old);
                    node.right_sibling = new;
                }
                dirty.push(node_id);
            }
        }
    }

    /// Rotates the subtree rooted at `x` to the left: its right child takes
    /// its place, and `x` becomes that child's left child.
    fn rotate_left(&mut self, x: u32, up: Link, dirty: &mut Vec<u32>) {
        let y = self.dir_entry(x).right_sibling;
        debug_assert_ne!(y, consts::NO_STREAM);
        let y_left = self.dir_entry(y).left_sibling;
        self.dir_entry_mut(x).right_sibling = y_left;
        self.dir_entry_mut(y).left_sibling = x;
        self.relink(up, x, y, dirty);
        dirty.push(x);
        dirty.push(y);
    }

    /// Rotates the subtree rooted at `x` to the right: its left child takes
    /// its place, and `x` becomes that child's right child.
    fn rotate_right(&mut self, x: u32, up: Link, dirty: &mut Vec<u32>) {
        let y = self.dir_entry(x).left_sibling;
        debug_assert_ne!(y, consts::NO_STREAM);
        let y_right = self.dir_entry(y).right_sibling;
        self.dir_entry_mut(x).left_sibling = y_right;
        self.dir_entry_mut(y).right_sibling = x;
        self.relink(up, x, y, dirty);
        dirty.push(x);
        dirty.push(y);
    }

    /// Restores the red-black tree invariants of the sibling tree of storage
    /// `parent_id` after the red node at the end of `path` was attached to
    /// it as a leaf.  `path` runs from the root of the sibling tree down to
    /// that node, and stands in for parent pointers, which directory entries
    /// don't have.  This is the standard insertion fixup (recolor while the
    /// uncle is red, otherwise one or two rotations), so the tree stays
    /// balanced and any reader that walks it finds a name in `O(log n)`
    /// steps.
    fn rebalance_after_insert(
        &mut self,
        parent_id: u32,
        path: &mut Vec<u32>,
        dirty: &mut Vec<u32>,
    ) {
        loop {
            let depth = path.len();
            let node = path[depth - 1];
            if depth == 1 {
                // The node is the root of the sibling tree, which must be
                // black.
                self.set_color(node, Color::Black, dirty);
                return;
            }
            let parent = path[depth - 2];
            if self.dir_entry(parent).color == Color::Black {
                return;
            }
            if depth == 2 {
                // A red root (which the spec forbids, but some writers
                // produce); making it black fixes both that and the red-red
                // pair.
                self.set_color(parent, Color::Black, dirty);
                return;
            }
            let grandparent = path[depth - 3];
            let grandparent_entry = self.dir_entry(grandparent);
            let parent_is_left = grandparent_entry.left_sibling == parent;
            let uncle = if parent_is_left {
                grandparent_entry.right_sibling
            } else {
                grandparent_entry.left_sibling
            };
            if uncle != consts::NO_STREAM
                && self.dir_entry(uncle).color == Color::Red
            {
                self.set_color(parent, Color::Black, dirty);
                self.set_color(uncle, Color::Black, dirty);
                self.set_color(grandparent, Color::Red, dirty);
                path.truncate(depth - 2);
                continue;
            }
            let node_is_left = self.dir_entry(parent).left_sibling == node;
            let above_grandparent = if depth >= 4 {
                Link::Node(path[depth - 4])
            } else {
                Link::Storage(parent_id)
            };
            if parent_is_left {
                if !node_is_left {
                    self.rotate_left(parent, Link::Node(grandparent), dirty);
                }
                let pivot = self.dir_entry(grandparent).left_sibling;
                self.set_color(pivot, Color::Black, dirty);
                self.set_color(grandparent, Color::Red, dirty);
                self.rotate_right(grandparent, above_grandparent, dirty);
            } else {
                if node_is_left {
                    self.rotate_right(parent, Link::Node(grandparent), dirty);
                }
                let pivot = self.dir_entry(grandparent).right_sibling;
                self.set_color(pivot, Color::Black, dirty);
                self.set_color(grandparent, Color::Red, dirty);
                self.rotate_left(grandparent, above_grandparent, dirty);
            }
            return;
        }
    }
}

impl<F: Seek> Directory<F> {
    pub fn seek_within_sector(
        &mut self,
        sector_id: u32,
        offset_within_sector: u64,
    ) -> io::Result<Sector<'_, F>> {
        self.allocator.seek_within_sector(sector_id, offset_within_sector)
    }

    pub fn seek_within_header(
        &mut self,
        offset_within_header: u64,
    ) -> io::Result<Sector<'_, F>> {
        self.allocator.seek_within_header(offset_within_header)
    }

    fn seek_to_dir_entry(
        &mut self,
        stream_id: u32,
    ) -> io::Result<Sector<'_, F>> {
        self.seek_within_dir_entry(stream_id, 0)
    }

    fn seek_within_dir_entry(
        &mut self,
        stream_id: u32,
        offset_within_dir_entry: usize,
    ) -> io::Result<Sector<'_, F>> {
        seek_within_dir_entry(
            &mut self.allocator,
            &self.dir_sector_ids,
            stream_id,
            offset_within_dir_entry,
        )
    }
}

/// Seeks to `offset_within_dir_entry` bytes into the slot of directory entry
/// `stream_id`, given the sector IDs of the directory chain.  (A free function
/// so that a caller can hold a borrow of another field of the `Directory` at
/// the same time.)
fn seek_within_dir_entry<'a, F: Seek>(
    allocator: &'a mut Allocator<F>,
    dir_sector_ids: &[u32],
    stream_id: u32,
    offset_within_dir_entry: usize,
) -> io::Result<Sector<'a, F>> {
    let dir_entries_per_sector =
        allocator.version().dir_entries_per_sector() as u32;
    let index_within_sector = stream_id % dir_entries_per_sector;
    let sector_index = (stream_id / dir_entries_per_sector) as usize;
    let Some(&directory_sector) = dir_sector_ids.get(sector_index) else {
        invalid_data!(
            "Directory entry {} is beyond the {} directory sectors",
            stream_id,
            dir_sector_ids.len()
        );
    };
    allocator.seek_within_subsector(
        directory_sector,
        index_within_sector,
        consts::DIR_ENTRY_LEN,
        offset_within_dir_entry as u64,
    )
}

impl<F: Write + Seek> Directory<F> {
    /// Allocates a new chain with one sector, and returns the starting sector
    /// number.
    pub fn begin_chain(&mut self, init: SectorInit) -> io::Result<u32> {
        self.allocator.begin_chain(init)
    }

    /// Given the starting sector (or any internal sector) of a chain, extends
    /// the end of that chain by one sector and returns the new sector number,
    /// updating the FAT as necessary.
    pub fn extend_chain(
        &mut self,
        start_sector_id: u32,
        init: SectorInit,
    ) -> io::Result<u32> {
        self.allocator.extend_chain(start_sector_id, init)
    }

    /// Given the start sector of a chain, deallocates the entire chain.
    pub fn free_chain(&mut self, start_sector_id: u32) -> io::Result<()> {
        self.allocator.free_chain(start_sector_id)
    }

    /// Inserts a new directory entry into the tree under the specified parent
    /// entry, then returns the new stream ID.
    pub fn insert_dir_entry(
        &mut self,
        parent_id: u32,
        name: &str,
        obj_type: ObjType,
    ) -> io::Result<u32> {
        debug_assert!(
            obj_type == ObjType::Storage || obj_type == ObjType::Stream
        );
        // Create a new directory entry.
        let stream_id = self.allocate_dir_entry()?;
        // 2.6.1 streams must have creation and modified time of 0
        let mut ts = Timestamp::zero();
        if obj_type == ObjType::Storage {
            ts = Timestamp::now();
        }
        let mut dir_entry = DirEntry::new(name, obj_type, ts);
        // A node joins the red-black tree red; the fixup below recolors it
        // if it ends up as the root.
        dir_entry.color = Color::Red;
        *self.dir_entry_mut(stream_id) = dir_entry;

        // Find the leaf position for the new entry, remembering the way down
        // for the rebalancing.
        let mut path = Vec::new();
        let mut sibling_id = self.dir_entry(parent_id).child;
        let mut ordering = Ordering::Equal;
        while sibling_id != consts::NO_STREAM {
            path.push(sibling_id);
            let sibling = self.dir_entry(sibling_id);
            ordering = internal::path::compare_names(name, &sibling.name);
            sibling_id = match ordering {
                Ordering::Less => sibling.left_sibling,
                Ordering::Greater => sibling.right_sibling,
                Ordering::Equal => panic!("internal error: insert duplicate"),
            };
        }
        let mut dirty = vec![stream_id];
        match path.last() {
            None => {
                self.dir_entry_mut(parent_id).child = stream_id;
                dirty.push(parent_id);
            }
            Some(&leaf_id) => {
                let leaf = self.dir_entry_mut(leaf_id);
                if ordering == Ordering::Less {
                    leaf.left_sibling = stream_id;
                } else {
                    leaf.right_sibling = stream_id;
                }
                dirty.push(leaf_id);
            }
        }
        path.push(stream_id);
        self.rebalance_after_insert(parent_id, &mut path, &mut dirty);
        self.name_index
            .insert((parent_id, internal::path::name_key(name)), stream_id);

        // Write every entry the insertion touched to the underlying file.
        dirty.sort_unstable();
        dirty.dedup();
        for touched_id in dirty {
            self.write_dir_entry(touched_id)?;
        }
        Ok(stream_id)
    }

    /// Removes a directory entry from the tree and deallocates it.
    pub fn remove_dir_entry(
        &mut self,
        parent_id: u32,
        name: &str,
    ) -> io::Result<()> {
        // Find the directory entry with the given name below the parent.
        let mut stream_ids = Vec::new();
        let mut stream_id = self.dir_entry(parent_id).child;
        loop {
            debug_assert_ne!(stream_id, consts::NO_STREAM);
            debug_assert!(!stream_ids.contains(&stream_id));
            stream_ids.push(stream_id);
            let dir_entry = self.dir_entry(stream_id);
            match internal::path::compare_names(name, &dir_entry.name) {
                Ordering::Equal => break,
                Ordering::Less => stream_id = dir_entry.left_sibling,
                Ordering::Greater => stream_id = dir_entry.right_sibling,
            }
        }
        debug_assert_eq!(self.dir_entry(stream_id).child, consts::NO_STREAM);
        self.name_index.remove(&(parent_id, internal::path::name_key(name)));

        // Restructure the tree.
        let mut replacement_id = consts::NO_STREAM;
        loop {
            let left_sibling = self.dir_entry(stream_id).left_sibling;
            let right_sibling = self.dir_entry(stream_id).right_sibling;
            if left_sibling == consts::NO_STREAM
                && right_sibling == consts::NO_STREAM
            {
                break;
            } else if left_sibling == consts::NO_STREAM {
                replacement_id = right_sibling;
                break;
            } else if right_sibling == consts::NO_STREAM {
                replacement_id = left_sibling;
                break;
            }
            let mut predecessor_id = left_sibling;
            loop {
                stream_ids.push(predecessor_id);
                let next_id = self.dir_entry(predecessor_id).right_sibling;
                if next_id == consts::NO_STREAM {
                    break;
                }
                predecessor_id = next_id;
            }
            let mut pred_entry = self.dir_entry(predecessor_id).clone();
            debug_assert_eq!(pred_entry.right_sibling, consts::NO_STREAM);
            pred_entry.left_sibling = left_sibling;
            pred_entry.right_sibling = right_sibling;
            // The predecessor takes over the removed node's place in the
            // tree, including its color, so the red-black coloring around
            // this slot is unchanged.
            pred_entry.color = self.dir_entry(stream_id).color;
            pred_entry.write_to(&mut self.seek_to_dir_entry(stream_id)?)?;
            // The predecessor now lives in this slot; its old slot is the
            // one that ends up freed. If it is a storage, its children were
            // indexed under the old slot and follow it.
            self.name_index.insert(
                (parent_id, internal::path::name_key(&pred_entry.name)),
                stream_id,
            );
            self.rekey_children(pred_entry.child, predecessor_id, stream_id);
            *self.dir_entry_mut(stream_id) = pred_entry;
            stream_id = predecessor_id;
        }

        // Remove the entry.
        debug_assert_eq!(stream_ids.last(), Some(&stream_id));
        stream_ids.pop();
        let removed_is_red = self.dir_entry(stream_id).color == Color::Red;
        if let Some(&sibling_id) = stream_ids.last() {
            if self.dir_entry(sibling_id).left_sibling == stream_id {
                self.dir_entry_mut(sibling_id).left_sibling = replacement_id;
                let mut sector = self.seek_within_dir_entry(sibling_id, 68)?;
                sector.write_le_u32(replacement_id)?;
            } else {
                debug_assert_eq!(
                    self.dir_entry(sibling_id).right_sibling,
                    stream_id
                );
                self.dir_entry_mut(sibling_id).right_sibling = replacement_id;
                let mut sector = self.seek_within_dir_entry(sibling_id, 72)?;
                sector.write_le_u32(replacement_id)?;
            }
        } else {
            self.dir_entry_mut(parent_id).child = replacement_id;
            let mut sector = self.seek_within_dir_entry(parent_id, 76)?;
            sector.write_le_u32(replacement_id)?;
        }
        // Removing a black node changes the black height of the tree, which
        // this doesn't restore (no reader depends on it); but the spliced-in
        // node must not form a red-red pair with its new parent, and the
        // root of the sibling tree must be black.
        if replacement_id != consts::NO_STREAM && !removed_is_red {
            let parent_is_red = match stream_ids.last() {
                Some(&sibling_id) => {
                    self.dir_entry(sibling_id).color == Color::Red
                }
                None => true,
            };
            if parent_is_red
                && self.dir_entry(replacement_id).color == Color::Red
            {
                self.dir_entry_mut(replacement_id).color = Color::Black;
                self.write_dir_entry(replacement_id)?;
            }
        }
        self.free_dir_entry(stream_id)?;
        Ok(())
    }

    /// Adds a new (uninitialized) entry to the directory and returns the new
    /// stream ID.
    fn allocate_dir_entry(&mut self) -> io::Result<u32> {
        // If there's an existing unalloated directory entry, use that.
        if let Some(stream_id) = self.free_entries.pop() {
            debug_assert_eq!(
                self.dir_entry(stream_id).obj_type,
                ObjType::Unallocated
            );
            return Ok(stream_id);
        }
        // Otherwise, we need a new entry; if there's not room in the directory
        // chain to add it, then first we need to add a new directory sector.
        let dir_entries_per_sector = self.version().dir_entries_per_sector();
        let unallocated_dir_entry = DirEntry::unallocated();
        if self.dir_entries.len()
            >= self.dir_sector_ids.len() * dir_entries_per_sector
        {
            // Extending from the chain's last sector avoids walking it from
            // the start; `extend_chain` accepts any sector of the chain.
            let last_sector = *self.dir_sector_ids.last().unwrap();
            let new_sector =
                self.allocator.extend_chain(last_sector, SectorInit::Dir)?;
            self.dir_sector_ids.push(new_sector);
            self.update_num_dir_sectors()?;
        }
        // Add a new entry to the end of the directory and return it.
        let stream_id = self.dir_entries.len() as u32;
        self.dir_entries.push(unallocated_dir_entry);
        Ok(stream_id)
    }

    /// Increase header num_dir_sectors if version V4
    /// note: not updating this value breaks ole32 compatibility
    fn update_num_dir_sectors(&mut self) -> io::Result<()> {
        if self.version() == Version::V4 {
            let num_dir_sectors = self.dir_sector_ids.len() as u32;
            self.seek_within_header(40)?.write_le_u32(num_dir_sectors)?;
        }
        Ok(())
    }

    /// Deallocates the specified directory entry.
    fn free_dir_entry(&mut self, stream_id: u32) -> io::Result<()> {
        debug_assert_ne!(stream_id, consts::ROOT_STREAM_ID);
        let dir_entry = DirEntry::unallocated();
        dir_entry.write_to(&mut self.seek_to_dir_entry(stream_id)?)?;
        *self.dir_entry_mut(stream_id) = dir_entry;
        self.free_entries.push(stream_id);
        // TODO: Truncate directory chain if last directory sector is now all
        //       unallocated.
        //       In that case, also call update_num_dir_sectors()
        Ok(())
    }

    /// Calls the given function with a mutable reference to the specified
    /// directory entry, then writes the updated directory entry to the
    /// underlying file once the function returns.
    pub fn with_dir_entry_mut<W>(
        &mut self,
        stream_id: u32,
        func: W,
    ) -> io::Result<()>
    where
        W: FnOnce(&mut DirEntry),
    {
        func(&mut self.dir_entries[stream_id as usize]);
        self.write_dir_entry(stream_id)
    }

    /// Calls the given function with a mutable reference to the root directory
    /// entry, then writes the updated directory entry to the underlying file
    /// once the function returns.
    pub fn with_root_dir_entry_mut<W>(&mut self, func: W) -> io::Result<()>
    where
        W: FnOnce(&mut DirEntry),
    {
        self.with_dir_entry_mut(consts::ROOT_STREAM_ID, func)
    }

    fn write_dir_entry(&mut self, stream_id: u32) -> io::Result<()> {
        let mut sector = seek_within_dir_entry(
            &mut self.allocator,
            &self.dir_sector_ids,
            stream_id,
            0,
        )?;
        self.dir_entries[stream_id as usize].write_to(&mut sector)
    }

    /// Flushes all changes to the underlying file.
    pub fn flush(&mut self) -> io::Result<()> {
        self.allocator.flush()
    }
}

//===========================================================================//

#[cfg(test)]
mod tests {
    use super::Directory;
    use crate::internal::{
        consts, Allocator, Color, DirEntry, ObjType, Sectors, Timestamp,
        Validation, Version,
    };
    use std::io::Cursor;

    fn make_directory(
        entries: Vec<DirEntry>,
        validation: Validation,
    ) -> Directory<Cursor<Vec<u8>>> {
        let version = Version::V3;
        let num_sectors = 3;
        let data_len = (1 + num_sectors) * version.sector_len();
        let cursor = Cursor::new(vec![0; data_len]);
        let sectors = Sectors::new(version, data_len as u64, cursor);
        let mut fat = vec![consts::END_OF_CHAIN; num_sectors];
        fat[0] = consts::FAT_SECTOR;
        let allocator =
            Allocator::new(sectors, vec![], vec![0], fat, validation).unwrap();
        Directory::new(allocator, entries, 1, validation).unwrap()
    }

    #[test]
    #[should_panic(expected = "Malformed directory (root entry is missing)")]
    fn no_root_entry() {
        make_directory(vec![], Validation::Permissive);
    }

    #[test]
    #[should_panic(
        expected = "Malformed directory (root stream len is 147, but should \
                    be multiple of 64)"
    )]
    fn invalid_mini_stream_len() {
        let mut root_entry = DirEntry::empty_root_entry();
        root_entry.start_sector = 2;
        root_entry.stream_len = 147;
        make_directory(vec![root_entry], Validation::Permissive);
    }

    #[test]
    #[should_panic(expected = "Malformed directory (loop in tree)")]
    fn storage_is_child_of_itself() {
        let mut root_entry = DirEntry::empty_root_entry();
        root_entry.child = 1;
        let mut storage =
            DirEntry::new("foo", ObjType::Storage, Timestamp::zero());
        storage.child = 1;
        make_directory(vec![root_entry, storage], Validation::Permissive);
    }

    #[test]
    #[should_panic(
        expected = "Malformed directory (root entry has object type Storage)"
    )]
    fn root_has_wrong_type() {
        let mut root_entry = DirEntry::empty_root_entry();
        root_entry.obj_type = ObjType::Storage;
        make_directory(vec![root_entry], Validation::Permissive);
    }

    #[test]
    #[should_panic(
        expected = "Malformed directory (non-root entry with object type Root)"
    )]
    fn nonroot_has_wrong_type() {
        let mut root_entry = DirEntry::empty_root_entry();
        root_entry.child = 1;
        let storage = DirEntry::new("foo", ObjType::Root, Timestamp::zero());
        make_directory(vec![root_entry, storage], Validation::Permissive);
    }

    #[test]
    fn tolerate_red_root() {
        // The MS-CFB spec section 2.6.4 says the root entry MUST be colored
        // black, but apparently some implementations don't do this (see
        // https://social.msdn.microsoft.com/Forums/sqlserver/en-US/
        // 9290d877-d91f-4509-ace9-cb4575c48514/red-black-tree-in-mscfb).  So
        // we shouldn't complain if the root is red.
        let mut root_entry = DirEntry::empty_root_entry();
        root_entry.color = Color::Red;
        make_directory(vec![root_entry], Validation::Permissive);
    }

    fn make_entries_with_adjacent_red_nodes() -> Vec<DirEntry> {
        let mut root_entry = DirEntry::empty_root_entry();
        root_entry.child = 1;
        let mut storage1 =
            DirEntry::new("foo", ObjType::Storage, Timestamp::zero());
        storage1.color = Color::Red;
        storage1.left_sibling = 2;
        let mut storage2 =
            DirEntry::new("bar", ObjType::Storage, Timestamp::zero());
        storage2.color = Color::Red;
        vec![root_entry, storage1, storage2]
    }

    #[test]
    #[should_panic(
        expected = "Malformed directory (RB tree has adjacent red nodes)"
    )]
    fn adjacent_red_nodes_strict() {
        make_directory(
            make_entries_with_adjacent_red_nodes(),
            Validation::Strict,
        );
    }

    #[test]
    fn adjacent_red_nodes_permissive() {
        make_directory(
            make_entries_with_adjacent_red_nodes(),
            Validation::Permissive,
        );
    }
}

//===========================================================================//

#[cfg(test)]
mod tree_tests {
    use super::Directory;
    use crate::internal::{
        consts, path, Allocator, Color, DirEntry, ObjType, Sectors, Timestamp,
        Validation, Version,
    };
    use std::cmp::Ordering;
    use std::io::Cursor;

    fn make_directory() -> Directory<Cursor<Vec<u8>>> {
        let version = Version::V3;
        let num_sectors = 2; // FAT, directory
        let data_len = (1 + num_sectors) * version.sector_len();
        let cursor = Cursor::new(vec![0; data_len]);
        let sectors = Sectors::new(version, data_len as u64, cursor);
        let mut fat = vec![consts::END_OF_CHAIN; num_sectors];
        fat[0] = consts::FAT_SECTOR;
        let allocator =
            Allocator::new(sectors, vec![], vec![0], fat, Validation::Strict)
                .unwrap();
        let entries = vec![DirEntry::empty_root_entry()];
        Directory::new(allocator, entries, 1, Validation::Strict).unwrap()
    }

    /// Checks the red-black and search tree invariants of the sibling tree
    /// under `parent_id`, returning the number of nodes and the depth of the
    /// deepest one.
    fn check_tree(
        directory: &Directory<Cursor<Vec<u8>>>,
        parent_id: u32,
    ) -> (usize, usize) {
        let root = directory.dir_entry(parent_id).child;
        if root == consts::NO_STREAM {
            return (0, 0);
        }
        assert_eq!(directory.dir_entry(root).color, Color::Black);
        let mut count = 0;
        let mut max_depth = 0;
        let mut stack = vec![(root, 1, false, None::<u32>, None::<u32>)];
        while let Some((id, depth, parent_red, lower, upper)) = stack.pop() {
            count += 1;
            max_depth = max_depth.max(depth);
            let entry = directory.dir_entry(id);
            let red = entry.color == Color::Red;
            assert!(!(red && parent_red), "red-red pair at {}", entry.name);
            if let Some(lower) = lower {
                let lower = &directory.dir_entry(lower).name;
                assert_eq!(
                    path::compare_names(lower, &entry.name),
                    Ordering::Less
                );
            }
            if let Some(upper) = upper {
                let upper = &directory.dir_entry(upper).name;
                assert_eq!(
                    path::compare_names(&entry.name, upper),
                    Ordering::Less
                );
            }
            if entry.left_sibling != consts::NO_STREAM {
                stack.push((
                    entry.left_sibling,
                    depth + 1,
                    red,
                    lower,
                    Some(id),
                ));
            }
            if entry.right_sibling != consts::NO_STREAM {
                stack.push((
                    entry.right_sibling,
                    depth + 1,
                    red,
                    Some(id),
                    upper,
                ));
            }
        }
        (count, max_depth)
    }

    fn max_red_black_depth(count: usize) -> usize {
        // A red-black tree with n nodes is at most 2 * log2(n + 1) deep.
        2 * (usize::BITS - count.leading_zeros()) as usize
    }

    fn check_inserted(names: &[String]) {
        let mut directory = make_directory();
        for name in names {
            directory
                .insert_dir_entry(
                    consts::ROOT_STREAM_ID,
                    name,
                    ObjType::Stream,
                )
                .unwrap();
        }
        let (count, depth) = check_tree(&directory, consts::ROOT_STREAM_ID);
        assert_eq!(count, names.len());
        assert!(
            depth <= max_red_black_depth(count),
            "{} nodes are {} deep",
            count,
            depth
        );
        for name in names {
            assert!(directory.stream_id_for_name_chain(&[name]).is_some());
        }
    }

    #[test]
    fn ascending_inserts_stay_balanced() {
        let names: Vec<String> =
            (0..2000).map(|i| format!("Item{i}")).collect();
        check_inserted(&names);
    }

    #[test]
    fn descending_inserts_stay_balanced() {
        let names: Vec<String> =
            (0..2000).rev().map(|i| format!("Item{i}")).collect();
        check_inserted(&names);
    }

    #[test]
    fn shuffled_inserts_stay_balanced() {
        // A fixed linear congruential shuffle keeps the test reproducible.
        let mut names: Vec<String> =
            (0..2000).map(|i| format!("Item{i}")).collect();
        let mut state = 12345u64;
        for i in (1..names.len()).rev() {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            let j = (state >> 33) as usize % (i + 1);
            names.swap(i, j);
        }
        check_inserted(&names);
    }

    fn insert(
        directory: &mut Directory<Cursor<Vec<u8>>>,
        parent: u32,
        name: &str,
    ) -> u32 {
        directory.insert_dir_entry(parent, name, ObjType::Stream).unwrap()
    }

    fn color_of(directory: &Directory<Cursor<Vec<u8>>>, name: &str) -> Color {
        let id = directory.stream_id_for_name_chain(&[name]).unwrap();
        directory.dir_entry(id).color
    }

    /// Removing the root of a sibling tree, and a node whose replacement
    /// is red under a red parent, leaves a valid tree with a black root.
    #[test]
    fn removing_the_root_and_red_replacements() {
        let mut directory = make_directory();
        // b becomes the root with a and c as red children.
        for name in ["a", "b", "c"] {
            insert(&mut directory, consts::ROOT_STREAM_ID, name);
        }
        assert_eq!(color_of(&directory, "b"), Color::Black);
        assert_eq!(color_of(&directory, "a"), Color::Red);
        assert_eq!(color_of(&directory, "c"), Color::Red);
        // Removing the root promotes its predecessor a, which takes over
        // the root's black color.
        directory.remove_dir_entry(consts::ROOT_STREAM_ID, "b").unwrap();
        let root = directory.dir_entry(consts::ROOT_STREAM_ID).child;
        assert_eq!(directory.dir_entry(root).name, "a");
        assert_eq!(color_of(&directory, "a"), Color::Black);
        check_tree(&directory, consts::ROOT_STREAM_ID);
        // d joins as a red child of c; removing c splices d under the
        // black root a.
        insert(&mut directory, consts::ROOT_STREAM_ID, "d");
        directory.remove_dir_entry(consts::ROOT_STREAM_ID, "c").unwrap();
        check_tree(&directory, consts::ROOT_STREAM_ID);
        directory.remove_dir_entry(consts::ROOT_STREAM_ID, "a").unwrap();
        // Only d is left: it is the root, so it must be black now.
        let root = directory.dir_entry(consts::ROOT_STREAM_ID).child;
        assert_eq!(directory.dir_entry(root).name, "d");
        assert_eq!(color_of(&directory, "d"), Color::Black);
        // Removing the last node empties the tree; inserting again works.
        directory.remove_dir_entry(consts::ROOT_STREAM_ID, "d").unwrap();
        assert_eq!(
            directory.dir_entry(consts::ROOT_STREAM_ID).child,
            consts::NO_STREAM
        );
        for name in ["x", "y", "z"] {
            insert(&mut directory, consts::ROOT_STREAM_ID, name);
        }
        let (count, _) = check_tree(&directory, consts::ROOT_STREAM_ID);
        assert_eq!(count, 3);
    }

    /// A red node spliced in under a red parent is made black.
    #[test]
    fn spliced_red_child_under_red_parent_is_blackened() {
        let mut directory = make_directory();
        // Ascending inserts of 1..=6 give the shape
        //          2(B)
        //      1(B)    4(R)
        //            3(B) 5(B)
        //                    6(R)
        for name in ["n1", "n2", "n3", "n4", "n5", "n6"] {
            insert(&mut directory, consts::ROOT_STREAM_ID, name);
        }
        assert_eq!(color_of(&directory, "n4"), Color::Red);
        assert_eq!(color_of(&directory, "n5"), Color::Black);
        assert_eq!(color_of(&directory, "n6"), Color::Red);
        // Removing the black n5 splices the red n6 under the red n4.
        directory.remove_dir_entry(consts::ROOT_STREAM_ID, "n5").unwrap();
        assert_eq!(color_of(&directory, "n6"), Color::Black);
        check_tree(&directory, consts::ROOT_STREAM_ID);
    }

    /// Storages keep separate sibling trees; rebalancing one relinks
    /// through that storage's child pointer and leaves the other alone.
    #[test]
    fn storages_are_balanced_independently() {
        let mut directory = make_directory();
        let left = directory
            .insert_dir_entry(consts::ROOT_STREAM_ID, "Left", ObjType::Storage)
            .unwrap();
        let right = directory
            .insert_dir_entry(
                consts::ROOT_STREAM_ID,
                "Right",
                ObjType::Storage,
            )
            .unwrap();
        for i in 0..300 {
            insert(&mut directory, left, &format!("L{i}"));
            if i % 3 == 0 {
                insert(&mut directory, right, &format!("R{i}"));
            }
        }
        let (count, depth) = check_tree(&directory, left);
        assert_eq!(count, 300);
        assert!(depth <= max_red_black_depth(count));
        let (count, depth) = check_tree(&directory, right);
        assert_eq!(count, 100);
        assert!(depth <= max_red_black_depth(count));
        assert_eq!(check_tree(&directory, consts::ROOT_STREAM_ID).0, 2);
        for i in 0..300 {
            assert!(directory
                .stream_id_for_name_chain(&["Left", &format!("L{i}")])
                .is_some());
            assert_eq!(
                directory
                    .stream_id_for_name_chain(&["Right", &format!("R{i}")])
                    .is_some(),
                i % 3 == 0
            );
        }
    }

    /// Builds a directory whose root sibling tree is one long right-leaning
    /// chain of black nodes named `Item0..ItemN` in order, the shape this
    /// crate used to write.
    fn make_degenerate_directory(
        count: u32,
        colors: impl Fn(u32) -> Color,
    ) -> Directory<Cursor<Vec<u8>>> {
        let mut entries = vec![DirEntry::empty_root_entry()];
        entries[0].child = 1;
        for i in 0..count {
            let mut entry = DirEntry::new(
                &format!("Item{i}"),
                ObjType::Stream,
                Timestamp::zero(),
            );
            entry.color = colors(i);
            if i + 1 < count {
                entry.right_sibling = i + 2;
            }
            entries.push(entry);
        }
        let version = Version::V3;
        let num_dir_sectors = entries.len().div_ceil(4);
        let num_sectors = 1 + num_dir_sectors;
        let data_len = (1 + num_sectors) * version.sector_len();
        let cursor = Cursor::new(vec![0; data_len]);
        let sectors = Sectors::new(version, data_len as u64, cursor);
        // Sector 0 is the FAT; the directory chain is sectors 1..=n.
        let mut fat = vec![consts::END_OF_CHAIN; num_sectors];
        fat[0] = consts::FAT_SECTOR;
        for (sector, next) in fat.iter_mut().enumerate().skip(1) {
            if sector < num_dir_sectors {
                *next = sector as u32 + 1;
            }
        }
        let allocator = Allocator::new(
            sectors,
            vec![],
            vec![0],
            fat,
            Validation::Permissive,
        )
        .unwrap();
        Directory::new(allocator, entries, 1, Validation::Permissive).unwrap()
    }

    /// Inserting into a tree an older writer left as a long chain keeps
    /// it a valid search tree; it does not have to become balanced.
    #[test]
    fn inserting_into_a_degenerate_tree() {
        let mut directory = make_degenerate_directory(9, |_| Color::Black);
        for name in ["Item10", "Aardvark", "Item5a", "Zebra"] {
            insert(&mut directory, consts::ROOT_STREAM_ID, name);
        }
        let (count, _) = check_tree(&directory, consts::ROOT_STREAM_ID);
        assert_eq!(count, 13);
        for name in ["Item0", "Item8", "Item10", "Aardvark", "Item5a", "Zebra"]
        {
            assert!(directory.stream_id_for_name_chain(&[name]).is_some());
        }
    }

    /// A file with adjacent red nodes (tolerated when opened permissively)
    /// still accepts inserts and removals, and every name stays findable.
    #[test]
    fn inserting_into_a_tree_with_adjacent_reds() {
        let mut directory = make_degenerate_directory(6, |_| Color::Red);
        for name in ["Item7", "Item8", "Item9", "Apple", "Item9a"] {
            insert(&mut directory, consts::ROOT_STREAM_ID, name);
        }
        directory.remove_dir_entry(consts::ROOT_STREAM_ID, "Item3").unwrap();
        directory.remove_dir_entry(consts::ROOT_STREAM_ID, "Item8").unwrap();
        // The tree stays a search tree with a black root, even if the
        // pre-existing red-red pairs are not all repaired.
        let root = directory.dir_entry(consts::ROOT_STREAM_ID).child;
        assert_eq!(directory.dir_entry(root).color, Color::Black);
        let mut stack = vec![root];
        let mut seen = 0;
        while let Some(id) = stack.pop() {
            seen += 1;
            let entry = directory.dir_entry(id);
            for sibling in [entry.left_sibling, entry.right_sibling] {
                if sibling != consts::NO_STREAM {
                    let other = &directory.dir_entry(sibling).name;
                    let ordering = path::compare_names(other, &entry.name);
                    assert_eq!(
                        ordering == Ordering::Less,
                        sibling == entry.left_sibling
                    );
                    stack.push(sibling);
                }
            }
        }
        assert_eq!(seen, 9);
        for name in ["Item0", "Item5", "Item7", "Item9", "Apple", "Item9a"] {
            assert!(directory.stream_id_for_name_chain(&[name]).is_some());
        }
        for name in ["Item3", "Item8"] {
            assert!(directory.stream_id_for_name_chain(&[name]).is_none());
        }
    }

    #[test]
    fn removals_keep_the_tree_valid() {
        let names: Vec<String> =
            (0..500).map(|i| format!("Item{i}")).collect();
        let mut directory = make_directory();
        for name in &names {
            directory
                .insert_dir_entry(
                    consts::ROOT_STREAM_ID,
                    name,
                    ObjType::Stream,
                )
                .unwrap();
        }
        for name in names.iter().step_by(3) {
            directory.remove_dir_entry(consts::ROOT_STREAM_ID, name).unwrap();
        }
        let (count, _) = check_tree(&directory, consts::ROOT_STREAM_ID);
        assert_eq!(count, names.len() - names.iter().step_by(3).count());
        for (i, name) in names.iter().enumerate() {
            let found = directory.stream_id_for_name_chain(&[name]).is_some();
            assert_eq!(found, i % 3 != 0, "{name}");
        }
        // Freed slots are reused before the directory grows.
        let before = directory.dir_entries.len();
        directory
            .insert_dir_entry(consts::ROOT_STREAM_ID, "Again", ObjType::Stream)
            .unwrap();
        assert_eq!(directory.dir_entries.len(), before);
        check_tree(&directory, consts::ROOT_STREAM_ID);
    }
}

//===========================================================================//
