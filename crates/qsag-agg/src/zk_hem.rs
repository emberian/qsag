//! Zero-knowledge and recursive `Hem` subsystem over Quintic `Fp5` (`[DKT26]` `< 2^{-128}` QROM):
//! - [`v2`]: Quintic `Fp5` committed-mask zero-knowledge SNARK (`QSAGZKH2` / `QSAGZKS2`).
//! - [`relation`]: R1CS + native width-12 / width-24 `Poseidon2` $x^7$ S-box & LogUp constraint system.
//! - [`blind_vc`]: Anonymous selective-disclosure credentials over `v2`.
//! - [`multisig`]: Threshold/quorum `JortsPoseidon2` multisignatures over `v2`.
//! - [`capability`]: Batched delegated capability verification over `v2`.
//! - [`recursive_ivc`]: `[DKT26]` `< 2^{-128}` QROM binary recursive IVC (`QSAGIVC1`).
//! - [`bounds`]: Exact integer `MilliBits` proximity & QROM security calculator primitives.

#[cfg(any(test, feature = "std"))]
use alloc::vec::Vec;

pub mod blind_vc;
pub mod bounds;
pub mod capability;
pub mod multisig;
pub mod recursive_ivc;
pub mod relation;
pub mod v2;

use crate::field::Goldilocks;
use crate::sponge::{
    cshake256_from_midstate_32, cshake256_seed_counter_words_x4, cshake256_static_midstate,
};

/// Expand a seed into canonical field elements using one counter block per
/// element. Reducing its first 192 bits has statistical distance below 2^-192
/// from uniform because 2^192 = 1 mod p. Work and addresses depend only on
/// the requested length. The wide stream uses a distinct seed derivation.
///
/// Block `counter` does not depend on any other block, so [`Self::fill_base`] computes
/// many blocks at once (four per permutation call via [`cshake256_seed_counter_words_x4`],
/// and on several threads with `std`). The element sequence is that of repeated
/// [`Self::next_base`] in every case.
pub struct SeedStream {
    /// Sponge state after the customization block; public.
    midstate: [u64; 25],
    input: [u8; 40],
    counter: u64,
}

/// Four independent counter blocks per SIMD permutation.
fn seed_stream_fill_blocks(
    midstate: &[u64; 25],
    seed: &[u64; 4],
    counter: u64,
    groups: &mut [[Goldilocks; 4]],
) {
    for (i, cells) in groups.iter_mut().enumerate() {
        let mut blocks = cshake256_seed_counter_words_x4(midstate, seed, counter + 4 * i as u64);
        for (dst, words) in cells.iter_mut().zip(&mut blocks) {
            let mut bytes = [0u8; 24];
            for (chunk, word) in bytes.as_chunks_mut::<8>().0.iter_mut().zip(words.iter()) {
                *chunk = word.to_le_bytes();
            }
            *dst = Goldilocks::from_bytes24_unbiased(&bytes);
            qsag_asm::volatile_fill(&mut bytes, 0);
            qsag_asm::volatile_fill(words, 0);
        }
    }
}

impl SeedStream {
    /// `domain` is a customization string of 1 to 128 bytes.
    pub fn new(domain: &'static [u8], seed: &[u8; 32]) -> Self {
        let mut input = [0u8; 40];
        crate::sponge::cshake256_into(b"QSAG.SEEDSTREAM.WIDE192/v1", seed, &mut input[..32]);
        Self {
            midstate: cshake256_static_midstate(domain),
            input,
            counter: 0,
        }
    }

    /// Draw the next complete counter block for a nonce or salt.
    pub(crate) fn next_bytes32(&mut self) -> [u8; 32] {
        self.input[32..].copy_from_slice(&self.counter.to_le_bytes());
        self.counter += 1;
        cshake256_from_midstate_32(&self.midstate, &self.input)
    }

    pub fn next_base(&mut self) -> Goldilocks {
        let mut block = self.next_bytes32();
        let element = Goldilocks::from_bytes24_unbiased(block.first_chunk::<24>().unwrap());
        qsag_asm::volatile_fill(&mut block, 0);
        element
    }

    /// Draw exactly the same field elements as repeated calls to `next_base`.
    pub fn fill_base(&mut self, out: &mut [Goldilocks]) {
        let (bulk, tail) = out.as_chunks_mut::<4>();
        let mut seed = core::array::from_fn(|i| {
            u64::from_le_bytes(core::array::from_fn(|j| self.input[8 * i + j]))
        });
        let counter = self.counter;
        self.counter += 4 * bulk.len() as u64;
        let run = |offset: usize, cells: &mut [[Goldilocks; 4]]| {
            seed_stream_fill_blocks(&self.midstate, &seed, counter + 4 * offset as u64, cells);
        };
        #[cfg(feature = "std")]
        {
            let workers = crate::parallel_workers().min(bulk.len() / 256);
            if workers > 1 {
                // Round the number of groups up and workers down to powers of
                // two. This bounds thread count without a hardware division.
                let chunk = bulk.len().next_power_of_two() >> workers.ilog2();
                std::thread::scope(|scope| {
                    let mut handles = Vec::with_capacity(workers);
                    let mut pending = bulk;
                    let mut offset = 0;
                    while !pending.is_empty() {
                        let (cells, rest) = pending.split_at_mut(chunk.min(pending.len()));
                        handles.push(crate::spawn_bounded(scope, move || run(offset, cells)));
                        offset += chunk;
                        pending = rest;
                    }
                    handles.into_iter().for_each(crate::join_worker);
                });
            } else {
                run(0, bulk);
            }
        }
        #[cfg(not(feature = "std"))]
        run(0, bulk);
        qsag_asm::volatile_fill(&mut seed, 0u64);
        for slot in tail {
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
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    #[test]
    fn seed_stream_wide_reduction_known_answer() {
        let mut stream = SeedStream::new(b"QSAG.TEST.SEED.STREAM", &[0x5a; 32]);
        let mut fields = [Goldilocks::ZERO; 4];
        stream.fill_base(&mut fields);
        // Independent SP 800-185 cSHAKE and integer reduction modulo p.
        assert_eq!(
            fields.map(Goldilocks::canonical),
            [
                0x6355359f7d90f5d3,
                0xc7fbcc6b527972e7,
                0x3126158e5b1212c9,
                0x80497f1325029b3d
            ]
        );
    }

    #[test]
    fn seed_stream_fill_base_matches_sequential_next_base() {
        for len in [0usize, 1, 7, 64, 65, 259, 8_205] {
            let mut seq = SeedStream::new(b"QSAG.TEST.SEED.STREAM", &[0x5A; 32]);
            let mut bulk = SeedStream::new(b"QSAG.TEST.SEED.STREAM", &[0x5A; 32]);
            // Start at an unaligned counter and check the following raw block too.
            assert_eq!(seq.next_base(), bulk.next_base());
            let want: Vec<Goldilocks> = (0..len).map(|_| seq.next_base()).collect();
            let mut got = vec![Goldilocks::ZERO; len];
            bulk.fill_base(&mut got);
            assert_eq!(got, want, "len={len}");
            assert_eq!(seq.next_fp5(), bulk.next_fp5());
            assert_eq!(seq.next_bytes32(), bulk.next_bytes32());
        }
    }
}
