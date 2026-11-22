//! Differential tests of `qsag_migrate::hem::zcash` against the reference Zcash
//! crates (`orchard` 0.16.0, `zcash_address` 0.14). The tests are in `tests/`.
//!
//! ```text
//! cd validation/zcash
//! cargo test --release --test reference
//! cargo test --release --test reference -- --ignored --nocapture   # builds the relation
//! ```

/// A deterministic byte stream for test inputs (SplitMix64).
pub struct Stream(pub u64);

impl Stream {
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    pub fn bytes<const N: usize>(&mut self) -> [u8; N] {
        let mut out = [0u8; N];
        for chunk in out.chunks_mut(8) {
            let word = self.next_u64().to_le_bytes();
            chunk.copy_from_slice(&word[..chunk.len()]);
        }
        out
    }
}
