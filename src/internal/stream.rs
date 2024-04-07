use crate::internal::{consts, MiniAllocator, ObjType, SectorInit};
use std::io::{self, BufRead, Read, Seek, SeekFrom, Write};
use std::sync::{Arc, RwLock, Weak};

//===========================================================================//

const BUFFER_SIZE: usize = 8192;

//===========================================================================//

/// A stream entry in a compound file, much like a filesystem file.
pub struct Stream<F> {
    minialloc: Weak<RwLock<MiniAllocator<F>>>,
    stream_id: u32,
    total_len: u64,
    buffer: Box<[u8; BUFFER_SIZE]>,
    buf_pos: usize,
    buf_cap: usize,
    buf_offset_from_start: u64,
    flusher: Option<Box<dyn Flusher<F>>>,
}

impl<F> Stream<F> {
    pub(crate) fn new(
        minialloc: &Arc<RwLock<MiniAllocator<F>>>,
        stream_id: u32,
    ) -> Stream<F> {
        let total_len =
            minialloc.read().unwrap().dir_entry(stream_id).stream_len;
        Stream {
            minialloc: Arc::downgrade(minialloc),
            stream_id,
            total_len,
            buffer: Box::new([0; BUFFER_SIZE]),
            buf_pos: 0,
            buf_cap: 0,
            buf_offset_from_start: 0,
            flusher: None,
        }
    }

    fn minialloc(&self) -> io::Result<Arc<RwLock<MiniAllocator<F>>>> {
        self.minialloc.upgrade().ok_or_else(|| {
            io::Error::new(io::ErrorKind::Other, "CompoundFile was dropped")
        })
    }

    /// Returns the current length of the stream, in bytes.
    pub fn len(&self) -> u64 {
        self.total_len
    }

    /// Returns true if the stream is empty.
    pub fn is_empty(&self) -> bool {
        self.total_len == 0
    }

    fn current_position(&self) -> u64 {
        self.buf_offset_from_start + (self.buf_pos as u64)
    }

    fn flush_changes(&mut self) -> io::Result<()> {
        if let Some(flusher) = self.flusher.take() {
            flusher.flush_changes(self)?;
        }
        Ok(())
    }
}

impl<F: Read + Write + Seek> Stream<F> {
    /// Truncates or extends the stream, updating the size of this stream to
    /// become `size`.
    ///
    /// If `size` is less than the stream's current size, then the stream will
    /// be shrunk.  If it is greater than the stream's current size, then the
    /// stream will be padded with zero bytes.
    ///
    /// Does not change the current read/write position within the stream,
    /// unless the stream is truncated to before the current position, in which
    /// case the position becomes the new end of the stream.
    pub fn set_len(&mut self, size: u64) -> io::Result<()> {
        if size != self.total_len {
            let new_position = self.current_position().min(size);
            self.flush_changes()?;
            let minialloc = self.minialloc()?;
            resize_stream(
                &mut minialloc.write().unwrap(),
                self.stream_id,
                size,
            )?;
            self.total_len = size;
            self.buf_offset_from_start = new_position;
            self.buf_pos = 0;
            self.buf_cap = 0;
        }
        Ok(())
    }

    fn mark_modified(&mut self) {
        if self.flusher.is_none() {
            let flusher: Box<dyn Flusher<F>> = Box::new(FlushBuffer);
            self.flusher = Some(flusher);
        }
    }
}

impl<F: Read + Seek> BufRead for Stream<F> {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        if self.buf_pos >= self.buf_cap
            && self.current_position() < self.total_len
        {
            self.flush_changes()?;
            self.buf_offset_from_start += self.buf_pos as u64;
            self.buf_pos = 0;
            let minialloc = self.minialloc()?;
            self.buf_cap = read_data_from_stream(
                &mut minialloc.write().unwrap(),
                self.stream_id,
                self.buf_offset_from_start,
                &mut self.buffer[..],
            )?;
        }
        Ok(&self.buffer[self.buf_pos..self.buf_cap])
    }

    fn consume(&mut self, amt: usize) {
        self.buf_pos = self.buf_cap.min(self.buf_pos + amt);
    }
}

impl<F: Read + Seek> Read for Stream<F> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let mut buffered_data = self.fill_buf()?;
        let num_bytes = buffered_data.read(buf)?;
        self.consume(num_bytes);
        Ok(num_bytes)
    }
}

impl<F: Read + Seek> Seek for Stream<F> {
    fn seek(&mut self, pos: SeekFrom) -> io::Result<u64> {
        let new_pos: u64 =
            match pos {
                SeekFrom::Start(delta) => {
                    if delta > self.total_len {
                        invalid_input!(
                        "Cannot seek to {} bytes from start, because stream \
                         length is only {} bytes",
                        delta, self.total_len,
                    );
                    }
                    delta
                }
                SeekFrom::End(delta) => {
                    if delta > 0 {
                        invalid_input!(
                        "Cannot seek to {} bytes past the end of the stream",
                        delta,
                    );
                    } else {
                        let delta = (-delta) as u64;
                        if delta > self.total_len {
                            invalid_input!(
                                "Cannot seek to {} bytes before end, because \
                             stream length is only {} bytes",
                                delta,
                                self.total_len,
                            );
                        }
                        self.total_len - delta
                    }
                }
                SeekFrom::Current(delta) => {
                    let old_pos = self.current_position();
                    debug_assert!(old_pos <= self.total_len);
                    if delta < 0 {
                        let delta = (-delta) as u64;
                        if delta > old_pos {
                            invalid_input!(
                            "Cannot seek to {} bytes before current position, \
                             which is only {}",
                            delta, old_pos,
                        );
                        }
                        old_pos - delta
                    } else {
                        let delta = delta as u64;
                        let remaining = self.total_len - old_pos;
                        if delta > remaining {
                            invalid_input!(
                            "Cannot seek to {} bytes after current position, \
                             because there are only {} bytes remaining in the \
                             stream",
                            delta, remaining,
                        );
                        }
                        old_pos + delta
                    }
                }
            };
        if new_pos < self.buf_offset_from_start
            || new_pos > self.buf_offset_from_start + self.buf_cap as u64
        {
            self.flush_changes()?;
            self.buf_offset_from_start = new_pos;
            self.buf_pos = 0;
            self.buf_cap = 0;
        } else {
            self.buf_pos = (new_pos - self.buf_offset_from_start) as usize;
        }
        Ok(new_pos)
    }
}

impl<F: Read + Write + Seek> Write for Stream<F> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        debug_assert!(self.buf_pos <= self.buffer.len());
        if self.buf_pos >= self.buffer.len() {
            self.flush_changes()?;
            self.buf_offset_from_start += self.buf_pos as u64;
            self.buf_pos = 0;
            self.buf_cap = 0;
        }
        let num_bytes_written =
            (&mut self.buffer[self.buf_pos..]).write(buf)?;
        self.mark_modified();
        self.buf_pos += num_bytes_written;
        debug_assert!(self.buf_pos <= self.buffer.len());
        self.buf_cap = self.buf_cap.max(self.buf_pos);
        self.total_len = self
            .total_len
            .max(self.buf_offset_from_start + self.buf_cap as u64);
        Ok(num_bytes_written)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.flush_changes()?;
        let minialloc = self.minialloc()?;
        minialloc.write().unwrap().flush()?;
        Ok(())
    }
}

impl<F> Drop for Stream<F> {
    fn drop(&mut self) {
        let _ = self.flush_changes();
    }
}

//===========================================================================//

trait Flusher<F> {
    fn flush_changes(&self, stream: &mut Stream<F>) -> io::Result<()>;
}

struct FlushBuffer;

impl<F: Read + Write + Seek> Flusher<F> for FlushBuffer {
    fn flush_changes(&self, stream: &mut Stream<F>) -> io::Result<()> {
        let minialloc = stream.minialloc()?;
        write_data_to_stream(
            &mut minialloc.write().unwrap(),
            stream.stream_id,
            stream.buf_offset_from_start,
            &stream.buffer[..stream.buf_cap],
        )?;
        debug_assert_eq!(
            minialloc.read().unwrap().dir_entry(stream.stream_id).stream_len,
            stream.total_len
        );
        Ok(())
    }
}

//===========================================================================//

fn read_data_from_stream<F: Read + Seek>(
    minialloc: &mut MiniAllocator<F>,
    stream_id: u32,
    buf_offset_from_start: u64,
    buf: &mut [u8],
) -> io::Result<usize> {
    let (start_sector, stream_len) = {
        let dir_entry = minialloc.dir_entry(stream_id);
        debug_assert_eq!(dir_entry.obj_type, ObjType::Stream);
        (dir_entry.start_sector, dir_entry.stream_len)
    };
    let num_bytes = if buf_offset_from_start >= stream_len {
        0
    } else {
        let remaining = stream_len - buf_offset_from_start;
        if remaining < buf.len() as u64 {
            remaining as usize
        } else {
            buf.len()
        }
    };
    if num_bytes > 0 {
        if stream_len < consts::MINI_STREAM_CUTOFF as u64 {
            let mut chain = minialloc.open_mini_chain(start_sector)?;
            chain.seek(SeekFrom::Start(buf_offset_from_start))?;
            chain.read_exact(&mut buf[..num_bytes])?;
        } else {
            let mut chain =
                minialloc.open_chain(start_sector, SectorInit::Zero)?;
            chain.seek(SeekFrom::Start(buf_offset_from_start))?;
            chain.read_exact(&mut buf[..num_bytes])?;
        }
    }
    Ok(num_bytes)
}

fn write_data_to_stream<F: Read + Write + Seek>(
    minialloc: &mut MiniAllocator<F>,
    stream_id: u32,
    buf_offset_from_start: u64,
    buf: &[u8],
) -> io::Result<()> {
    let (old_start_sector, old_stream_len) = {
        let dir_entry = minialloc.dir_entry(stream_id);
        debug_assert_eq!(dir_entry.obj_type, ObjType::Stream);
        (dir_entry.start_sector, dir_entry.stream_len)
    };
    debug_assert!(buf_offset_from_start <= old_stream_len);
    let new_stream_len =
        old_stream_len.max(buf_offset_from_start + buf.len() as u64);
    let new_start_sector = if old_start_sector == consts::END_OF_CHAIN {
        // Case 1: The stream has no existing chain.  The stream is empty, and
        // we are writing at the start.
        debug_assert_eq!(old_stream_len, 0);
        debug_assert_eq!(buf_offset_from_start, 0);
        if new_stream_len < consts::MINI_STREAM_CUTOFF as u64 {
            // Case 1a: The data we're writing is small enough that it
            // should be placed into a new mini chain.
            let mut chain = minialloc.open_mini_chain(consts::END_OF_CHAIN)?;
            chain.write_all(buf)?;
            chain.start_sector_id()
        } else {
            // Case 1b: The data we're writing is large enough that it should
            // be placed into a new regular chain.
            let mut chain = minialloc
                .open_chain(consts::END_OF_CHAIN, SectorInit::Zero)?;
            chain.write_all(buf)?;
            chain.start_sector_id()
        }
    } else if old_stream_len < consts::MINI_STREAM_CUTOFF as u64 {
        // Case 2: The stream currently exists in a mini chain.
        if new_stream_len < consts::MINI_STREAM_CUTOFF as u64 {
            // Case 2a: After the write, the stream will still be small enough
            // to stay in the mini stream.  Therefore, we should write into
            // this stream's existing mini chain.
            let mut chain = minialloc.open_mini_chain(old_start_sector)?;
            chain.seek(SeekFrom::Start(buf_offset_from_start))?;
            chain.write_all(buf)?;
            debug_assert_eq!(chain.start_sector_id(), old_start_sector);
            old_start_sector
        } else {
            // Case 2b: After the write, the stream will be large enough that
            // it cannot be in the mini stream.  Therefore, we should migrate
            // the stream into a new regular chain.
            debug_assert!(
                buf_offset_from_start < consts::MINI_STREAM_CUTOFF as u64
            );
            let mut tmp = vec![0u8; buf_offset_from_start as usize];
            let mut chain = minialloc.open_mini_chain(old_start_sector)?;
            chain.read_exact(&mut tmp)?;
            chain.free()?;
            let mut chain = minialloc
                .open_chain(consts::END_OF_CHAIN, SectorInit::Zero)?;
            chain.write_all(&tmp)?;
            chain.write_all(buf)?;
            chain.start_sector_id()
        }
    } else {
        // Case 3: The stream currently exists in a regular chain.  After the
        // write, it will of course still be too big to be in the mini stream.
        // Therefore, we should write into this stream's existing chain.
        debug_assert!(new_stream_len >= consts::MINI_STREAM_CUTOFF as u64);
        let mut chain =
            minialloc.open_chain(old_start_sector, SectorInit::Zero)?;
        chain.seek(SeekFrom::Start(buf_offset_from_start))?;
        chain.write_all(buf)?;
        debug_assert_eq!(chain.start_sector_id(), old_start_sector);
        old_start_sector
    };
    // Update the directory entry for this stream.
    minialloc.with_dir_entry_mut(stream_id, |dir_entry| {
        dir_entry.start_sector = new_start_sector;
        dir_entry.stream_len = new_stream_len;
    })
}

/// If `new_stream_len` is less than the stream's current length, then the
/// stream will be truncated.  If it is greater than the stream's current size,
/// then the stream will be padded with zero bytes.
fn resize_stream<F: Read + Write + Seek>(
    minialloc: &mut MiniAllocator<F>,
    stream_id: u32,
    new_stream_len: u64,
) -> io::Result<()> {
    let (old_start_sector, old_stream_len) = {
        let dir_entry = minialloc.dir_entry(stream_id);
        debug_assert_eq!(dir_entry.obj_type, ObjType::Stream);
        (dir_entry.start_sector, dir_entry.stream_len)
    };
    let new_start_sector = if old_start_sector == consts::END_OF_CHAIN {
        // Case 1: The stream has no existing chain.  We will allocate a new
        // chain that is all zeroes.
        debug_assert_eq!(old_stream_len, 0);
        if new_stream_len < consts::MINI_STREAM_CUTOFF as u64 {
            // Case 1a: The new length is small enough that it should be placed
            // into a new mini chain.
            let mut chain = minialloc.open_mini_chain(consts::END_OF_CHAIN)?;
            chain.set_len(new_stream_len)?;
            chain.start_sector_id()
        } else {
            // Case 1b: The new length is large enough that it should be placed
            // into a new regular chain.
            let mut chain = minialloc
                .open_chain(consts::END_OF_CHAIN, SectorInit::Zero)?;
            chain.set_len(new_stream_len)?;
            chain.start_sector_id()
        }
    } else if old_stream_len < consts::MINI_STREAM_CUTOFF as u64 {
        // Case 2: The stream currently exists in a mini chain.
        if new_stream_len == 0 {
            // Case 2a: The new length is zero.  Free the existing mini chain.
            minialloc.free_mini_chain(old_start_sector)?;
            consts::END_OF_CHAIN
        } else if new_stream_len < consts::MINI_STREAM_CUTOFF as u64 {
            // Case 2b: The new length is still small enough to fit in a mini
            // chain.  Therefore, we just need to adjust the length of the
            // existing chain.
            let mut chain = minialloc.open_mini_chain(old_start_sector)?;
            chain.set_len(new_stream_len)?;
            debug_assert_eq!(chain.start_sector_id(), old_start_sector);
            old_start_sector
        } else {
            // Case 2c: The new length is too large to fit in a mini chain.
            // Therefore, we should migrate the stream into a new regular
            // chain.
            let mut tmp = vec![0u8; old_stream_len as usize];
            let mut chain = minialloc.open_mini_chain(old_start_sector)?;
            chain.read_exact(&mut tmp)?;
            chain.free()?;
            let mut chain = minialloc
                .open_chain(consts::END_OF_CHAIN, SectorInit::Zero)?;
            chain.write_all(&tmp)?;
            chain.set_len(new_stream_len)?;
            chain.start_sector_id()
        }
    } else {
        // Case 3: The stream currently exists in a regular chain.
        if new_stream_len == 0 {
            // Case 3a: The new length is zero.  Free the existing chain.
            minialloc.free_chain(old_start_sector)?;
            consts::END_OF_CHAIN
        } else if new_stream_len < consts::MINI_STREAM_CUTOFF as u64 {
            // Case 3b: The new length is small enough to fit in a mini chain.
            // Therefore, we should migrate the stream into a new mini chain.
            debug_assert!(new_stream_len < old_stream_len);
            let mut tmp = vec![0u8; new_stream_len as usize];
            let mut chain =
                minialloc.open_chain(old_start_sector, SectorInit::Zero)?;
            chain.read_exact(&mut tmp)?;
            chain.free()?;
            let mut chain = minialloc.open_mini_chain(consts::END_OF_CHAIN)?;
            chain.write_all(&tmp)?;
            chain.start_sector_id()
        } else {
            // Case 3c: The new length is still too large to fit in a mini
            // chain.  Therefore, we just need to adjust the length of the
            // existing chain.
            let mut chain =
                minialloc.open_chain(old_start_sector, SectorInit::Zero)?;
            chain.set_len(new_stream_len)?;
            debug_assert_eq!(chain.start_sector_id(), old_start_sector);
            old_start_sector
        }
    };
    // Update the directory entry for this stream.
    minialloc.with_dir_entry_mut(stream_id, |dir_entry| {
        dir_entry.start_sector = new_start_sector;
        dir_entry.stream_len = new_stream_len;
    })
}

//===========================================================================//
