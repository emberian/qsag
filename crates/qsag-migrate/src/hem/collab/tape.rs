//! Canonical secret tape encoding. Callers must seal the bytes before persistence.
use super::engine::{Preprocessing, Sb};
use alloc::vec::Vec;
use qsag_agg::field::Goldilocks as F;
use qsag_core::wipe::SecretBuffer;

impl Preprocessing {
    /// Exact length of the private encoding, including its format and counts.
    pub fn secret_byte_len(triples: usize, randoms: usize) -> Option<usize> {
        triples
            .checked_mul(3)?
            .checked_add(randoms)?
            .checked_mul(24)?
            .checked_add(40)
    }

    pub fn to_secret_bytes(&self) -> SecretBuffer<Vec<u8>> {
        let mut out = Vec::with_capacity(
            Self::secret_byte_len(self.triples.len(), self.randoms.len())
                .expect("resident material"),
        );
        out.extend_from_slice(b"QSMTAPE1");
        out.extend_from_slice(&(self.triples.len() as u64).to_le_bytes());
        out.extend_from_slice(&(self.randoms.len() as u64).to_le_bytes());
        for k in self.key {
            out.extend_from_slice(&k.to_le_bytes());
        }
        for share in self.triples.iter().flatten().chain(&self.randoms) {
            for v in [share.v, share.m[0], share.m[1]] {
                out.extend_from_slice(&v.to_le_bytes());
            }
        }
        SecretBuffer(out)
    }

    pub fn from_secret_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.get(..8)? != b"QSMTAPE1" {
            return None;
        }
        let mut words = bytes[8..]
            .chunks_exact(8)
            .map(|b| u64::from_le_bytes(b.try_into().unwrap()));
        let t = usize::try_from(words.next()?).ok()?;
        let r = usize::try_from(words.next()?).ok()?;
        if Self::secret_byte_len(t, r)? != bytes.len() {
            return None;
        }
        let mut field = || F::from_canonical(words.next()?).ok();
        let mut tape = Self {
            key: [field()?, field()?],
            triples: Vec::new(),
            randoms: Vec::new(),
        };
        tape.triples.try_reserve_exact(t).ok()?;
        tape.randoms.try_reserve_exact(r).ok()?;
        let mut share = || {
            Some(Sb {
                v: field()?,
                m: [field()?, field()?],
            })
        };
        for _ in 0..t {
            tape.triples.push([share()?, share()?, share()?]);
        }
        for _ in 0..r {
            tape.randoms.push(share()?);
        }
        Some(tape)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    #[test]
    fn tape_codec_rejects_invalid_counts_trailing_bytes_and_noncanonical_fields() {
        let s = Sb {
            v: F::ONE,
            m: [F::TWO, F::ONE],
        };
        let tape = Preprocessing {
            key: [F::TWO, F::ONE],
            triples: vec![[s; 3]],
            randoms: vec![s, s],
        };
        let bytes = tape.to_secret_bytes();
        let copy = Preprocessing::from_secret_bytes(&bytes).unwrap();
        assert_eq!(tape.tape_id(), copy.tape_id());
        for cut in 0..bytes.len() {
            assert!(Preprocessing::from_secret_bytes(&bytes[..cut]).is_none());
        }
        for offset in [8, 16, 24, 40, bytes.len() - 8] {
            let mut bad = bytes.to_vec();
            bad[offset..offset + 8].fill(255);
            assert!(Preprocessing::from_secret_bytes(&bad).is_none());
        }
        let mut bad = bytes.to_vec();
        bad.push(0);
        assert!(Preprocessing::from_secret_bytes(&bad).is_none());
    }
}
