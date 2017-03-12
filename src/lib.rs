//! A library for encoding/decoding reading/writing [Compound File Binary](
//! https://msdn.microsoft.com/en-us/library/dd942138.aspx) (structured
//! storage) files.

#![warn(missing_docs)]

extern crate byteorder;

/// A compound file, backed by an underlying reader/writer (such as a `File` or
/// `Vec<u8>`).
pub struct CompoundFile<F> {
    inner: F,
}

impl<F> CompoundFile<F> {
    /// Consumes the `CompoundFile`, returning the underlying reader/writer.
    pub fn into_inner(self) -> F { self.inner }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {}
}
