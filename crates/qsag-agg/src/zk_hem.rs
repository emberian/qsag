//! Zero-knowledge and recursive `Hem` subsystem over Quintic `Fp5` (`[DKT26]` `< 2^{-128}` QROM):
//! - [`v2`]: Quintic `Fp5` committed-mask zero-knowledge SNARK (`QSAGZKH2` / `QSAGZKS2`).
//! - [`relation`]: R1CS + native width-12 / width-24 `Poseidon2` $x^7$ S-box & LogUp constraint system.
//! - [`blind_vc`]: Anonymous selective-disclosure credentials over `v2`.
//! - [`multisig`]: Threshold/quorum `JortsPoseidon2` multisignatures over `v2`.
//! - [`capability`]: Batched delegated capability verification over `v2`.
//! - [`recursive_ivc`]: `[DKT26]` `< 2^{-128}` QROM binary recursive IVC (`QSAGIVC1`).
//! - [`bounds`]: Exact integer `MilliBits` proximity & QROM security calculator primitives.

use alloc::vec::Vec;

pub mod blind_vc;
pub mod bounds;
pub mod capability;
pub mod multisig;
pub mod recursive_ivc;
pub mod relation;
pub mod v2;

use crate::field::{Goldilocks, GoldilocksOps as _};
use crate::sponge::{
    cshake256_from_midstate_32, cshake256_seed_counter_words_x4, cshake256_static_midstate,
};

/// Expands a 32-byte seed into uniform canonical `Goldilocks` / `Fp5` elements: 8-byte candidates
/// from `cSHAKE256(domain, seed || counter)` blocks, rejecting candidates `>= p`.
///
/// Block `counter` does not depend on any other block, so [`Self::fill_base`] computes
/// many blocks at once (four per permutation call via [`cshake256_seed_counter_words_x4`],
/// and on several threads with `std`). The element sequence is that of repeated
/// [`Self::next_base`] in every case.
pub struct SeedStream {
    /// Sponge state after the customization block; public.
    midstate: [u64; 25],
    input: [u8; 40],
    block: [u8; 32],
    pos: usize,
    counter: u64,
}

/// Fewest whole blocks for which [`SeedStream::fill_base`] leaves the one-block path.
const SEED_STREAM_BULK_BLOCKS: usize = 16;
/// Fewest blocks given to one worker thread.
#[cfg(feature = "std")]
const SEED_STREAM_PAR_BLOCKS: usize = 1 << 10;

/// Candidate words of the blocks `counter, counter + 1, ..` in stream order, four per
/// block; `words.len()` is a multiple of four.
fn seed_stream_words(midstate: &[u64; 25], seed: &[u64; 4], mut counter: u64, words: &mut [u64]) {
    let (quads, rest) = words.as_chunks_mut::<16>();
    for quad in quads {
        let mut blocks = cshake256_seed_counter_words_x4(midstate, seed, counter);
        for (dst, src) in quad.as_chunks_mut::<4>().0.iter_mut().zip(&blocks) {
            *dst = *src;
        }
        for block in &mut blocks {
            qsag_asm::volatile_fill(block, 0u64);
        }
        counter = counter.wrapping_add(4);
    }
    if !rest.is_empty() {
        let mut blocks = cshake256_seed_counter_words_x4(midstate, seed, counter);
        for (dst, src) in rest.as_chunks_mut::<4>().0.iter_mut().zip(&blocks) {
            *dst = *src;
        }
        for block in &mut blocks {
            qsag_asm::volatile_fill(block, 0u64);
        }
    }
}

/// Fill `out` (a multiple of four cells) from the candidate words of the blocks
/// `counter..counter + out.len() / 4`, which `words(first_block, buffer)` produces. Returns
/// how many cells were filled: `out.len()` less the rejected candidates.
fn seed_stream_fill_blocks(
    out: &mut [Goldilocks],
    counter: u64,
    words: &(impl Fn(u64, &mut [u64]) + Sync),
) -> usize {
    debug_assert!(out.len().is_multiple_of(4));
    let run = |base: usize, part: &mut [Goldilocks]| -> Vec<usize> {
        let mut rejected = Vec::new();
        let mut buf = [0u64; 256];
        for (n, cells) in part.chunks_mut(buf.len()).enumerate() {
            let at = base + n * buf.len();
            let buf = &mut buf[..cells.len()];
            words(counter.wrapping_add((at / 4) as u64), buf);
            for (i, (cell, &word)) in cells.iter_mut().zip(buf.iter()).enumerate() {
                match Goldilocks::from_canonical_u64(word) {
                    Some(x) => *cell = x,
                    None => {
                        *cell = Goldilocks::ZERO;
                        rejected.push(at + i);
                    }
                }
            }
        }
        qsag_asm::volatile_fill(&mut buf, 0u64);
        rejected
    };
    #[cfg(feature = "std")]
    let rejected: Vec<usize> = {
        let blocks = out.len() / 4;
        let workers = crate::parallel_workers().min(blocks / SEED_STREAM_PAR_BLOCKS);
        if workers > 1 {
            let chunk = 4 * blocks.div_ceil(workers);
            let run = &run;
            std::thread::scope(|scope| {
                let handles: Vec<_> = out
                    .chunks_mut(chunk)
                    .enumerate()
                    .map(|(k, part)| crate::spawn_bounded(scope, move || run(k * chunk, part)))
                    .collect();
                handles.into_iter().flat_map(crate::join_worker).collect()
            })
        } else {
            run(0, out)
        }
    };
    #[cfg(not(feature = "std"))]
    let rejected: Vec<usize> = run(0, out);

    let Some(&first) = rejected.first() else {
        return out.len();
    };
    let mut skip = rejected.iter().copied().peekable();
    let mut write = first;
    for read in first..out.len() {
        if skip.peek() == Some(&read) {
            skip.next();
        } else {
            out[write] = out[read];
            write += 1;
        }
    }
    qsag_asm::volatile_fill(&mut out[write..], Goldilocks::ZERO);
    write
}

impl SeedStream {
    /// `domain` is a customization string of 1 to 128 bytes.
    pub fn new(domain: &'static [u8], seed: &[u8; 32]) -> Self {
        let mut input = [0u8; 40];
        input[..32].copy_from_slice(seed);
        Self {
            midstate: cshake256_static_midstate(domain),
            input,
            block: [0u8; 32],
            pos: 32,
            counter: 0,
        }
    }

    /// Draw a fresh raw block for byte-domain nonces and salt seeds. Discard
    /// any partial field-element block so each counter is used only once.
    pub(crate) fn next_bytes32(&mut self) -> [u8; 32] {
        self.pos = 32;
        self.input[32..].copy_from_slice(&self.counter.to_le_bytes());
        self.counter += 1;
        cshake256_from_midstate_32(&self.midstate, &self.input)
    }

    pub fn next_base(&mut self) -> Goldilocks {
        loop {
            if self.pos == 32 {
                self.input[32..].copy_from_slice(&self.counter.to_le_bytes());
                self.block = cshake256_from_midstate_32(&self.midstate, &self.input);
                self.counter += 1;
                self.pos = 0;
            }
            let mut word = [0u8; 8];
            word.copy_from_slice(&self.block[self.pos..self.pos + 8]);
            self.pos += 8;
            if let Some(x) = Goldilocks::from_canonical_u64(u64::from_le_bytes(word)) {
                return x;
            }
        }
    }

    /// `out[i] = self.next_base()` for every `i` in order, computed many blocks at a time.
    pub fn fill_base(&mut self, out: &mut [Goldilocks]) {
        let mut done = 0;
        while done < out.len() && self.pos != 32 {
            out[done] = self.next_base();
            done += 1;
        }
        let blocks = (out.len() - done) / 4;
        if blocks >= SEED_STREAM_BULK_BLOCKS {
            let mut seed: [u64; 4] = core::array::from_fn(|lane| {
                u64::from_le_bytes(core::array::from_fn(|b| self.input[8 * lane + b]))
            });
            let midstate = &self.midstate;
            done += seed_stream_fill_blocks(
                &mut out[done..done + 4 * blocks],
                self.counter,
                &|counter, words: &mut [u64]| seed_stream_words(midstate, &seed, counter, words),
            );
            qsag_asm::volatile_fill(&mut seed, 0u64);
            self.counter += blocks as u64;
        }
        for slot in &mut out[done..] {
            *slot = self.next_base();
        }
    }

    pub fn next_fp5(&mut self) -> v2::field5::Fp5 {
        v2::field5::Fp5::from_limbs(core::array::from_fn(|_| self.next_base()))
    }
}

impl Drop for SeedStream {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.input, 0u8);
        qsag_asm::volatile_fill(&mut self.block, 0u8);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    #[test]
    fn seed_stream_fill_base_matches_sequential_next_base() {
        for len in [0usize, 1, 7, 64, 65, 259, 8_205] {
            let mut seq = SeedStream::new(b"QSAG.TEST.SEED.STREAM", &[0x5A; 32]);
            let mut bulk = SeedStream::new(b"QSAG.TEST.SEED.STREAM", &[0x5A; 32]);
            // Advance past one element so unaligned `pos != 32` prefix handling is exercised.
            assert_eq!(seq.next_base(), bulk.next_base());
            let want: Vec<Goldilocks> = (0..len).map(|_| seq.next_base()).collect();
            let mut got = vec![Goldilocks::ZERO; len];
            bulk.fill_base(&mut got);
            assert_eq!(got, want, "len={len}");
            assert_eq!(seq.next_fp5(), bulk.next_fp5());
        }
    }
}
