//! Shared little-endian byte cursor for the twin wire readers (`wire::decode`,
//! `deserialize_account_writes`). Error-agnostic: every method returns `Option`,
//! `None` on truncation — each call site supplies its own error variant via
//! `.ok_or(...)`, so the two formats keep their distinct error types.

pub(crate) struct ByteCursor<'a> {
    buf: &'a [u8],
    pos: usize,
}

impl<'a> ByteCursor<'a> {
    pub(crate) fn new(buf: &'a [u8]) -> Self {
        Self { buf, pos: 0 }
    }

    /// Advance past the next `n` bytes and return them; `None` if fewer remain.
    pub(crate) fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        if self.pos + n > self.buf.len() {
            return None;
        }
        let s = &self.buf[self.pos..self.pos + n];
        self.pos += n;
        Some(s)
    }

    pub(crate) fn skip(&mut self, n: usize) -> Option<()> {
        self.take(n).map(|_| ())
    }

    pub(crate) fn u8(&mut self) -> Option<u8> {
        Some(self.take(1)?[0])
    }

    pub(crate) fn u32(&mut self) -> Option<u32> {
        let b = self.take(4)?;
        Some(u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
    }

    pub(crate) fn u64(&mut self) -> Option<u64> {
        let b = self.take(8)?;
        Some(u64::from_le_bytes([
            b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7],
        ]))
    }

    /// Fill `dst` from the next `dst.len()` bytes.
    pub(crate) fn read_into(&mut self, dst: &mut [u8]) -> Option<()> {
        let s = self.take(dst.len())?;
        dst.copy_from_slice(s);
        Some(())
    }
}
