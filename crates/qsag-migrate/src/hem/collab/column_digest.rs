//! LigeSIS column hashing for a row-wise, rate-1/2 Reed–Solomon matrix.
//! The hash is linear on shares of the canonical **bits** of each encoded
//! symbol. Converting arithmetic shares to those bits is an MPC operation.
//! Outputs retain both MACs and must remain secret until a protocol authorizes
//! opening them. Binding relies on the short-input subset-sum assumption.
use super::engine::{Engine, Sb};
use super::net::Transport;
use super::witgen::{Count, Unit, Witgen, WitgenError};
use alloc::{vec, vec::Vec};
use qsag_agg::field::{Goldilocks as F, ntt_goldilocks};
use qsag_agg::pcs::hypercube_to_monomial_in_place;
use qsag_agg::sponge::cshake256_into;
use qsag_agg::zk_hem::relation::{ConstraintSystem, Def, Lc, Source};
use qsag_core::wipe::SecretBuffer;

/// Seven base-2^43 coordinates per public subset-sum weight (LigeSIS §3).
pub const DIGEST_WIDTH: usize = 7;
type Digest = [F; DIGEST_WIDTH];

/// The public matrix for a fixed number of rows. At most 2^20 bits enter
/// each digest, so every unreduced output is strictly below 2^63.
pub struct ColumnKey {
    rows: Vec<Vec<Digest>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ColumnError {
    Shape,
    Conversion(WitgenError),
}

fn constrain_limb(cs: &mut ConstraintSystem, value: &Lc, bits: &[Lc; 64]) {
    for b in bits {
        cs.enforce_boolean(b);
    }
    let pack = |bits: &[Lc]| {
        Lc::combine(
            &bits
                .iter()
                .enumerate()
                .map(|(i, b)| (F::from_u64_reduced(1u64 << i), b))
                .collect::<Vec<_>>(),
        )
    };
    cs.enforce_equal(value, &pack(bits));
    // p - 1 = 0xffffffff_00000000. If every high bit is one,
    // the low half must vanish. The product has depth five.
    let mut high = bits[32..].to_vec();
    while high.len() > 1 {
        high = high
            .chunks_exact(2)
            .map(|v| cs.mul(&v[0], &v[1]).into())
            .collect();
    }
    cs.enforce_mul(high.pop().unwrap(), pack(&bits[..32]), Lc::zero());
}

impl ColumnKey {
    /// Derive the fixed public parameters for this geometry.
    pub fn new(rows: usize) -> Result<Self, ColumnError> {
        if !rows.is_power_of_two() || rows > 1 << 14 {
            return Err(ColumnError::Shape);
        }
        let rows = (0..rows)
            .map(|i| {
                (0..64)
                    .map(|bit| {
                        let index = (i * 64 + bit) as u64;
                        let mut bytes = [0; 56];
                        cshake256_into(
                            b"QSAG.LIGESIS.COLUMN.43.V1",
                            &index.to_le_bytes(),
                            &mut bytes,
                        );
                        core::array::from_fn(|j| {
                            F::from_u64_reduced(
                                u64::from_le_bytes(bytes.as_chunks::<8>().0[j]) & ((1 << 43) - 1),
                            )
                        })
                    })
                    .collect()
            })
            .collect();
        Ok(Self { rows })
    }

    /// Reference digest on decoded field elements.
    pub fn digest(&self, values: &[F]) -> Result<Digest, ColumnError> {
        if values.len() != self.rows.len() {
            return Err(ColumnError::Shape);
        }
        let mut out = [F::ZERO; DIGEST_WIDTH];
        for (value, row) in values.iter().zip(&self.rows) {
            let word = value.to_canonical_u64();
            for (bit, weights) in row.iter().enumerate() {
                let mask = 0u64.wrapping_sub((word >> bit) & 1);
                for (sum, w) in out.iter_mut().zip(weights) {
                    *sum += F::from_u64_reduced(mask & w.to_canonical_u64());
                }
            }
        }
        Ok(out)
    }

    /// Send canonical bits, bounded recompositions and digest equations into
    /// the caller's zk-Hem relation. The caller binds the returned expressions
    /// to the corresponding digest in the outer commitment.
    pub fn constrain_column(
        &self,
        cs: &mut ConstraintSystem,
        values: &[Lc],
    ) -> Result<[Lc; DIGEST_WIDTH], ColumnError> {
        if values.len() != self.rows.len() {
            return Err(ColumnError::Shape);
        }
        let mut digits = Vec::with_capacity(values.len() * 64);
        for value in values {
            let word = cs.eval(value).to_canonical_u64();
            let source = cs.source(|| Source::Form {
                lc: value.clone(),
                bits: 64,
            });
            let bits: [Lc; 64] = core::array::from_fn(|j| {
                cs.alloc_defined(F::from_u64_reduced((word >> j) & 1), || Def::Bits {
                    source,
                    lo: j as u32,
                    width: 1,
                })
                .into()
            });
            constrain_limb(cs, value, &bits);
            digits.extend(bits);
        }
        Ok(core::array::from_fn(|j| {
            Lc::combine(
                &digits
                    .iter()
                    .zip(self.rows.iter().flatten())
                    .map(|(b, w)| (w[j], b))
                    .collect::<Vec<_>>(),
            )
        }))
    }

    fn width(&self, cells: usize) -> Result<usize, ColumnError> {
        if cells < self.rows.len() || !cells.is_power_of_two() {
            return Err(ColumnError::Shape);
        }
        let width = cells / self.rows.len();
        if width.trailing_zeros() >= 32 || width.checked_mul(2).is_none() {
            return Err(ColumnError::Shape);
        }
        Ok(width)
    }

    /// Preprocessing for conversion, excluding rare random-mask retries.
    pub fn demand(&self, cells: usize) -> Result<Count, ColumnError> {
        let encoded = 2 * self.width(cells)?;
        let mut count = Count::default();
        // Every full batch has the same shape. Scale its demand instead of
        // simulating a preprocessing tape the size of the entire witness.
        for (len, repeats) in [(32, encoded / 32), (encoded % 32, 1)] {
            if repeats == 0 || len == 0 {
                continue;
            }
            let mut batch = Count::default();
            Witgen::new(&mut batch)
                .canonical_bits(&vec![Unit; len])
                .map_err(ColumnError::Conversion)?;
            let times = self
                .rows
                .len()
                .checked_mul(repeats)
                .ok_or(ColumnError::Shape)?;
            let add = |a: &mut usize, b: usize| -> Result<(), ColumnError> {
                *a = a
                    .checked_add(b.checked_mul(times).ok_or(ColumnError::Shape)?)
                    .ok_or(ColumnError::Shape)?;
                Ok(())
            };
            add(&mut count.triples, batch.triples)?;
            add(&mut count.randoms, batch.randoms)?;
            add(&mut count.opened, batch.opened)?;
            add(&mut count.checks, batch.checks)?;
            add(&mut count.rounds, batch.rounds)?;
        }
        Ok(count)
    }

    /// Encode locally on authenticated shares, convert the resulting symbols
    /// to bit shares, and hash each column. Returns one authenticated share
    /// of each digest coordinate. Conversion costs are included in engine stats.
    pub fn digest_matrix<T: Transport>(
        &self,
        e: &mut Engine<T>,
        table: &[Sb],
    ) -> Result<SecretBuffer<Vec<[Sb; DIGEST_WIDTH]>>, ColumnError> {
        let width = self.width(table.len())?;
        let mut out = SecretBuffer::new(vec![[Sb::ZERO; DIGEST_WIDTH]; 2 * width]);
        for (row, key) in table.chunks_exact(width).zip(&self.rows) {
            let mut code = SecretBuffer::new(vec![Sb::ZERO; 2 * width]);
            // The same linear transform applies to the value and both MACs.
            for k in 0..3 {
                let mut words = SecretBuffer::new(vec![F::ZERO; 2 * width]);
                for (a, s) in words.iter_mut().zip(row) {
                    *a = if k == 0 { s.v } else { s.m[k - 1] };
                }
                hypercube_to_monomial_in_place(&mut words[..width], 32768);
                let mut shift = F::ONE;
                for w in &mut words[..width] {
                    *w *= shift;
                    shift *= F::NON_RESIDUE;
                }
                ntt_goldilocks(&mut words);
                for (s, &x) in code.iter_mut().zip(words.iter()) {
                    if k == 0 { s.v = x } else { s.m[k - 1] = x }
                }
            }
            let work = Witgen::new(e);
            for (symbols, digests) in code.chunks(32).zip(out.chunks_mut(32)) {
                let bits = work
                    .canonical_bits(symbols)
                    .map_err(ColumnError::Conversion)?;
                for (symbol, digest) in bits.iter().zip(digests) {
                    for (&b, w) in symbol.iter().zip(key) {
                        for (sum, &weight) in digest.iter_mut().zip(w) {
                            *sum += b.scale(weight);
                        }
                    }
                }
            }
        }
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hem::collab::{
        engine::{Dealer, tests::run_parties},
        prover::tests::deal_clear_assignment_and_prove,
    };
    use qsag_agg::field::GOLDILOCKS_PRIME;
    use qsag_agg::zk_hem::v2::{params::Profile, protocol::verify_split};

    #[test]
    fn collab_column_rejects_modular_aliases_and_long_digits() {
        let check = |word: u64, alter: bool| {
            let mut cs = ConstraintSystem::new();
            let value: Lc = cs.public_input(F::from_u64_reduced(word)).into();
            let bits = core::array::from_fn(|i| {
                let mut d = F::from_u64_reduced((word >> i) & 1);
                if alter && i == 0 {
                    d += F::TWO;
                }
                if alter && i == 1 {
                    d -= F::ONE;
                }
                cs.alloc(d).into()
            });
            constrain_limb(&mut cs, &value, &bits);
            let (shape, z) = cs.finish_v2();
            shape.is_satisfied(&z)
        };
        assert!(check(0, false));
        assert!(check(GOLDILOCKS_PRIME - 1, false));
        assert!(!check(GOLDILOCKS_PRIME, false));
        assert!(!check(u64::MAX, false));
        assert!(!check(2, true));
        let key = ColumnKey::new(1).unwrap();
        let one = key.digest(&[F::ONE]).unwrap();
        assert_ne!(one.map(|x| x + x), key.digest(&[F::TWO]).unwrap());
    }

    #[test]
    fn collab_column_authenticated_matrix_matches_clear_rs() {
        use qsag_agg::{field::encode_rs_coset_goldilocks, pcs::hypercube_to_monomial_coeffs};
        let key = ColumnKey::new(4).unwrap();
        let values: Vec<_> = (0..16)
            .map(|j| F::from_u64_reduced(GOLDILOCKS_PRIME - 1 - j * j))
            .collect();
        let mut dealer = Dealer::new(3, &[0x48; 32]);
        let shares: Vec<_> = values.iter().map(|&x| dealer.share(x)).collect();
        let count = key.demand(values.len()).unwrap();
        let preps = dealer.preprocessing(count.triples, count.randoms);
        let expected: Vec<_> = values
            .chunks_exact(4)
            .map(|r| encode_rs_coset_goldilocks(&hypercube_to_monomial_coeffs(r), 2))
            .collect();
        let expected: Vec<_> = (0..8)
            .flat_map(|j| {
                key.digest(&expected.iter().map(|r| r[j]).collect::<Vec<_>>())
                    .unwrap()
            })
            .collect();
        let start = std::time::Instant::now();
        let all = run_parties(preps, |mut e| {
            let local = SecretBuffer::new(shares.iter().map(|s| s[e.me()]).collect::<Vec<_>>());
            let partials = key.digest_matrix(&mut e, &local).unwrap();
            assert_eq!(e.remaining(), (0, 0));
            let conversion = e.stats.bytes_sent;
            let got = e.open(partials.as_flattened()).unwrap();
            e.check().unwrap();
            assert_eq!(got, expected);
            (conversion, e.stats.bytes_sent - conversion)
        });
        let conversion: u64 = all.iter().map(|x| x.0).sum();
        let opening: u64 = all.iter().map(|x| x.1).sum();
        std::println!(
            "3 custodians, 4x4 witness, 32 encoded symbols: conversion {conversion} bytes, authenticated digest opening {opening} bytes, {:?}, {} triples per party",
            start.elapsed(),
            count.triples
        );
    }

    #[test]
    fn collab_column_opening_binds_digest_in_split_proof() {
        let key = ColumnKey::new(2).unwrap();
        let values = [F::from_u64_reduced(GOLDILOCKS_PRIME - 1), F::TWO];
        let digest = key.digest(&values).unwrap();
        let mut cs = ConstraintSystem::new();
        let public = digest.map(|x| Lc::from(cs.public_input(x)));
        let vars = values.map(|x| Lc::from(cs.alloc(x)));
        let computed = key.constrain_column(&mut cs, &vars).unwrap();
        for (a, b) in computed.iter().zip(&public) {
            cs.enforce_equal(a, b);
        }
        let (shape, z) = cs.finish_v2();
        let stmt = b"QSAG.TEST.COLUMN.OPEN";
        let start = std::time::Instant::now();
        let out = deal_clear_assignment_and_prove(&shape, &z, stmt, 3, 125, |_, _| {}, |_, _| {});
        let proof = out[0].0.as_ref().unwrap();
        assert!(out.iter().all(|(p, _)| p.as_ref() == Ok(proof)));
        assert!(verify_split(
            &shape,
            &digest,
            stmt,
            Profile::default(),
            proof
        ));
        let elapsed = start.elapsed();
        let bytes: u64 = out.iter().map(|x| x.1.bytes_sent).sum();
        std::println!(
            "3-custodian column relation, split proof {} bytes, online payload {bytes} bytes, {elapsed:?}",
            proof.to_bytes().len()
        );
        let mut tampered = digest;
        tampered[3] += F::ONE;
        assert!(!verify_split(
            &shape,
            &tampered,
            stmt,
            Profile::default(),
            proof
        ));
    }
}
