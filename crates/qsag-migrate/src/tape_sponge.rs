//! Word-aligned SHAKE tape with oblivious lookahead and cursor advancement.
use crate::secret::Secret;
use qsag_accel::{
    ct::{ct_eq_mask_u64, ct_zeroize_u64s},
    keccak::keccak_f1600,
};

pub(crate) struct TapeSponge {
    state: [u64; 25],
    pos: u64,
}
impl Drop for TapeSponge {
    fn drop(&mut self) {
        ct_zeroize_u64s(&mut self.state);
        ct_zeroize_u64s(core::slice::from_mut(&mut self.pos));
    }
}
impl TapeSponge {
    pub fn new(seed: &[u8; 32]) -> Self {
        let mut state = [0; 25];
        let label = b"QSAG.MIGRATE.TAPE.V3";
        for (i, byte) in label.iter().chain(seed).enumerate() {
            state[i / 8] ^= u64::from(*byte) << (8 * (i % 8));
        }
        let end = label.len() + seed.len();
        state[end / 8] ^= 0x1f << (8 * (end % 8));
        state[16] ^= 0x8000_0000_0000_0000;
        keccak_f1600(&mut state);
        Self { state, pos: 0 }
    }

    // One permutation and fixed-address scans regardless of the secret cursor.
    // N <= 4, so lookahead spans at most two rate blocks.
    fn lookahead<const N: usize>(&self) -> (Secret<[u64; 25]>, Secret<[u64; N]>) {
        let mut next = Secret(self.state);
        keccak_f1600(&mut next);
        let mut words = Secret([0; N]);
        for (i, word) in words.iter_mut().enumerate() {
            for j in 0..17 {
                *word |= self.state[j] & ct_eq_mask_u64(self.pos + i as u64, j as u64);
                *word |= next[j] & ct_eq_mask_u64(self.pos + i as u64, (j + 17) as u64);
            }
        }
        (next, words)
    }

    fn advance(&mut self, next: &[u64; 25], count: u64) {
        let end = self.pos + count;
        let crossed = 0u64.wrapping_sub((end >= 17) as u64);
        self.pos = end - (17 & crossed);
        for (s, n) in self.state.iter_mut().zip(next) {
            *s ^= (*s ^ n) & crossed;
        }
    }

    pub fn squeeze(&mut self, out: &mut [u8]) {
        assert!(out.len() % 8 == 0);
        for chunk in out.chunks_exact_mut(8) {
            let (next, words) = self.lookahead::<1>();
            chunk.copy_from_slice(&words[0].to_le_bytes());
            self.advance(&next, 1);
        }
    }

    pub fn gold(&mut self) -> u64 {
        loop {
            let (next, words) = self.lookahead::<3>();
            let mut found = 0;
            let mut value = 0;
            let mut count = 3;
            for (i, &word) in words.iter().enumerate() {
                let valid =
                    0u64.wrapping_sub((word < qsag_accel::goldilocks::GOLDILOCKS_PRIME) as u64);
                let choose = valid & !found;
                value |= word & choose;
                count ^= (count ^ (i as u64 + 1)) & choose;
                found |= valid;
            }
            self.advance(&next, count);
            // Three rejected uniform words have probability < 2^-96. Only
            // this exceptional aggregate event changes the work performed.
            if found != 0 {
                return value;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use qsag_accel::{goldilocks::GOLDILOCKS_PRIME, keccak::Shake256};

    #[test]
    fn lookahead_preserves_rejection_stream_and_mixed_draws() {
        for seed in [[0; 32], [42; 32], [255; 32]] {
            let mut fast = TapeSponge::new(&seed);
            let mut reference = Shake256::new();
            reference.absorb(b"QSAG.MIGRATE.TAPE.V3");
            reference.absorb(&seed);
            reference.finalize(0x1f);
            for i in 0..300 {
                if i % 3 == 0 {
                    let expected = loop {
                        let mut raw = [0; 8];
                        reference.squeeze(&mut raw);
                        let v = u64::from_le_bytes(raw);
                        if v < GOLDILOCKS_PRIME {
                            break v;
                        }
                    };
                    assert_eq!(fast.gold(), expected);
                } else {
                    let mut a = [0; 32];
                    let mut b = [0; 32];
                    fast.squeeze(&mut a);
                    reference.squeeze(&mut b);
                    assert_eq!(a, b);
                }
            }
        }
    }

    #[test]
    fn selects_first_accepted_word_without_discarding_suffix() {
        for pos in 0..17 {
            for rejects in 0..3 {
                let mut tape = TapeSponge::new(&[9; 32]);
                tape.pos = pos;
                for j in 0..rejects {
                    if pos + j < 17 {
                        tape.state[(pos + j) as usize] = u64::MAX;
                    }
                }
                let (_, candidates) = tape.lookahead::<3>();
                let index = candidates
                    .iter()
                    .position(|&v| v < GOLDILOCKS_PRIME)
                    .unwrap();
                let expected = candidates[index];
                assert_eq!(tape.gold(), expected);
                assert_eq!(tape.pos, (pos + index as u64 + 1) % 17);
            }
        }
    }
}
