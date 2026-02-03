const STREAM_BUFFER_MIN: usize = 1024;
const STREAM_BUFFER_GROWTH_FACTOR: usize = 4;

pub(crate) const DEFAULT_STREAM_MAX_BUFFER_SIZE: usize = 1024 * 1024;

use std::convert::TryFrom;
use std::io::{self, Write};

/// A buffer for stream data that grows up to a configurable maximum.
///
/// The buffer starts at a minimum size, grows by a fixed factor, and never
/// exceeds the configured max.
pub(crate) struct StreamBuffer {
    data: Vec<u8>,
    pos: usize,
    cap: usize,
    max_size: usize,
}

impl Default for StreamBuffer {
    fn default() -> Self {
        StreamBuffer::new(DEFAULT_STREAM_MAX_BUFFER_SIZE)
    }
}

impl StreamBuffer {
    pub(crate) fn new(max_buffer_size: usize) -> StreamBuffer {
        StreamBuffer {
            data: vec![0; STREAM_BUFFER_MIN],
            pos: 0,
            cap: 0,
            max_size: max_buffer_size.max(STREAM_BUFFER_MIN),
        }
    }

    pub(crate) fn cursor(&self) -> usize {
        self.pos
    }

    pub(crate) fn filled_len(&self) -> usize {
        self.cap
    }

    pub(crate) fn has_remaining(&self) -> bool {
        self.pos < self.cap
    }

    pub(crate) fn remaining_slice(&self) -> &[u8] {
        &self.data[self.pos..self.cap]
    }

    pub(crate) fn filled_slice(&self) -> &[u8] {
        &self.data[..self.cap]
    }

    pub(crate) fn refill_with<F>(
        &mut self,
        remaining: u64,
        fill: F,
    ) -> io::Result<()>
    where
        F: FnOnce(&mut [u8]) -> io::Result<usize>,
    {
        self.pos = 0;
        self.grow_for_read_remaining(remaining);
        let cap = fill(&mut self.data)?;
        self.set_cap(cap);
        Ok(())
    }

    /// Writes bytes into the buffer at the current cursor.
    /// Returns the number of bytes written, or None if the buffer cannot grow.
    pub(crate) fn write_bytes(&mut self, input: &[u8]) -> Option<usize> {
        debug_assert!(self.pos <= self.data.len());
        if self.pos >= self.data.len() && !self.grow() {
            return None;
        }
        let written = (&mut self.data[self.pos..]).write(input).unwrap_or(0);
        self.pos += written;
        debug_assert!(self.pos <= self.data.len());
        if self.cap < self.pos {
            self.cap = self.pos;
        }
        Some(written)
    }

    /// Moves the cursor to an absolute position within the buffer.
    pub(crate) fn seek(&mut self, pos: usize) {
        debug_assert!(pos <= self.data.len());
        self.pos = pos;
        if self.cap < self.pos {
            self.cap = self.pos;
        }
    }

    fn set_cap(&mut self, cap: usize) {
        debug_assert!(cap <= self.data.len());
        self.cap = cap;
        if self.pos > self.cap {
            self.pos = self.cap;
        }
    }

    /// Clears the filled region and resets the cursor to 0.
    pub(crate) fn clear(&mut self) {
        self.pos = 0;
        self.cap = 0;
    }

    /// Consumes bytes from the filled region, asserting it stays in-bounds.
    pub(crate) fn consume(&mut self, amt: usize) {
        debug_assert!(self.pos + amt <= self.cap);
        self.pos += amt;
    }

    /// Attempts to grow the buffer, returning false if at max size.
    fn grow(&mut self) -> bool {
        if self.data.len() >= self.max_size {
            return false;
        }
        let new_len =
            (self.data.len() * STREAM_BUFFER_GROWTH_FACTOR).min(self.max_size);
        self.data.resize(new_len, 0);
        true
    }

    fn grow_for_read_remaining(&mut self, remaining: u64) {
        let current_len = self.data.len() as u64;
        if remaining <= current_len {
            return;
        }
        let remaining_usize =
            usize::try_from(remaining).unwrap_or(self.max_size);
        let desired =
            remaining_usize.min(self.max_size).max(STREAM_BUFFER_MIN);
        self.data.resize(desired, 0);
    }

    #[cfg(test)]
    fn data_len(&self) -> usize {
        self.data.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stream_buffer_advance() {
        let mut buffer = StreamBuffer::default();
        buffer.refill_with(8, |_| Ok(8)).unwrap();
        buffer.consume(3);
        assert_eq!(buffer.cursor(), 3);
        buffer.consume(5);
        assert_eq!(buffer.cursor(), 8);
    }

    #[test]
    #[should_panic]
    fn stream_buffer_consume_panics_past_cap() {
        let mut buffer = StreamBuffer::default();
        buffer.refill_with(4, |_| Ok(4)).unwrap();
        buffer.consume(5);
    }

    #[test]
    fn stream_buffer_grows_until_max() {
        const STREAM_BUFFER_MAX: usize = 1024 * 1024;
        let mut buffer = StreamBuffer::new(STREAM_BUFFER_MAX);
        let mut expected = STREAM_BUFFER_MIN;
        while expected < STREAM_BUFFER_MAX {
            assert!(buffer.grow());
            expected = (expected * STREAM_BUFFER_GROWTH_FACTOR)
                .min(STREAM_BUFFER_MAX);
            assert_eq!(buffer.data_len(), expected);
        }
        assert!(!buffer.grow());
        assert_eq!(buffer.data_len(), STREAM_BUFFER_MAX);
    }

    #[test]
    fn stream_buffer_respects_custom_max() {
        const CUSTOM_MAX: usize = 1024 * 4;
        let mut buffer = StreamBuffer::new(CUSTOM_MAX);
        assert!(buffer.grow());
        assert_eq!(buffer.data_len(), CUSTOM_MAX);
        assert!(!buffer.grow());
    }

    #[test]
    fn stream_buffer_refill_resets_cursor() {
        let mut buffer = StreamBuffer::default();
        buffer.seek(5);
        buffer.refill_with(3, |_| Ok(3)).unwrap();
        assert_eq!(buffer.cursor(), 0);
        assert_eq!(buffer.filled_len(), 3);
    }

    #[test]
    fn stream_buffer_seek_expands_cap() {
        let mut buffer = StreamBuffer::default();
        buffer.seek(4);
        assert_eq!(buffer.cursor(), 4);
        assert_eq!(buffer.filled_len(), 4);
    }

    #[test]
    fn stream_buffer_seek_allows_len_boundary() {
        let mut buffer = StreamBuffer::default();
        let len = STREAM_BUFFER_MIN;
        buffer.seek(len);
        assert_eq!(buffer.cursor(), len);
        assert_eq!(buffer.filled_len(), len);
    }

    #[test]
    fn stream_buffer_set_cap_allows_len_boundary() {
        let mut buffer = StreamBuffer::default();
        let len = STREAM_BUFFER_MIN;
        buffer.refill_with(len as u64, |_| Ok(len)).unwrap();
        assert_eq!(buffer.filled_len(), len);
    }

    #[test]
    fn stream_buffer_grow_preserves_pos_and_cap() {
        let mut buffer = StreamBuffer::default();
        buffer.refill_with(12, |_| Ok(12)).unwrap();
        buffer.seek(8);
        assert!(buffer.grow());
        assert_eq!(buffer.cursor(), 8);
        assert_eq!(buffer.filled_len(), 12);
    }

    #[test]
    fn stream_buffer_clamps_max_below_min() {
        let mut buffer = StreamBuffer::new(1);
        assert_eq!(buffer.data_len(), STREAM_BUFFER_MIN);
        assert!(!buffer.grow());
    }

    #[test]
    fn stream_buffer_refill_error_keeps_cap() {
        let mut buffer = StreamBuffer::default();
        buffer.refill_with(4, |_| Ok(4)).unwrap();
        buffer.seek(2);
        let result = buffer.refill_with(4, |_| Err(io::Error::other("fail")));
        assert!(result.is_err());
        assert_eq!(buffer.cursor(), 0);
        assert_eq!(buffer.filled_len(), 4);
    }

    #[test]
    fn stream_buffer_write_bytes_returns_none_when_full() {
        let mut buffer = StreamBuffer::new(STREAM_BUFFER_MIN);
        buffer.seek(STREAM_BUFFER_MIN);
        assert!(buffer.write_bytes(&[1]).is_none());
        assert_eq!(buffer.cursor(), STREAM_BUFFER_MIN);
        assert_eq!(buffer.filled_len(), STREAM_BUFFER_MIN);
    }

    #[test]
    fn stream_buffer_remaining_slice_matches_advance() {
        let mut buffer = StreamBuffer::default();
        buffer.refill_with(6, |_| Ok(6)).unwrap();
        buffer.consume(2);
        assert_eq!(buffer.remaining_slice().len(), 4);
        buffer.consume(4);
        assert!(buffer.remaining_slice().is_empty());
    }

    #[test]
    fn write_buffer_grows_when_full() {
        let mut buffer = StreamBuffer::new(STREAM_BUFFER_MIN * 8);
        let input = vec![0u8; STREAM_BUFFER_MIN];
        assert_eq!(buffer.write_bytes(&input), Some(STREAM_BUFFER_MIN));
        let initial_len = buffer.data_len();
        assert_eq!(buffer.write_bytes(&[1]), Some(1));
        let grown_len = buffer.data_len();

        assert_eq!(initial_len, STREAM_BUFFER_MIN);
        assert_eq!(grown_len, STREAM_BUFFER_MIN * 4);
    }

    #[test]
    fn read_buffer_aggressively_grows_on_refill() {
        let mut buffer = StreamBuffer::new(STREAM_BUFFER_MIN * 8);
        let initial_len = buffer.data_len();
        let remaining = (STREAM_BUFFER_MIN * 64) as u64;
        buffer.refill_with(remaining, |buf| Ok(buf.len())).unwrap();
        let grown_len = buffer.data_len();

        assert_eq!(initial_len, STREAM_BUFFER_MIN);
        assert_eq!(grown_len, STREAM_BUFFER_MIN * 8);
    }
}
