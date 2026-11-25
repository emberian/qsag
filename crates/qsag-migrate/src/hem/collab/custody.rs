//! From custody shares of a secret to authenticated shares of its bits.
//!
//! Custody is bytewise Shamir sharing over `TowerGf256` with custodian `p` holding the
//! evaluation at `p + 1` (the layout of `qsag_core::field::tower`), or plain XOR
//! sharing. A proving quorum of `k` custodians of a `(k, n)` sharing turns its Shamir
//! shares into XOR shares locally ([`xor_share_from_shamir`]); nobody reconstructs a
//! byte. [`input_secret_bits`] then gives the quorum authenticated arithmetic shares of
//! every bit of the secret: each custodian inputs the bits of its XOR share, every input
//! is checked to be a bit, and the inputs are XORed with one product per bit and
//! custodian.
//!
//! Corruption bound: the proving quorum's sharing is additive, private against any
//! `k - 1` of its members, so overall against fewer than `k` custodians, the custody
//! threshold. A custodian that inputs other bits than its share changes the secret by a
//! difference it knows; the statement then does not hold for the shared secret and the
//! prover stops at its zero test.

use alloc::vec::Vec;

use qsag_agg::field::Goldilocks;
use qsag_core::field::tower::{TowerGf256, lagrange_weights_zero_gf256};

use qsag_core::wipe::{SecretBuffer, SecretScratch};

use super::engine::{EXT_MUL_TRIPLES, Engine, MpcError, Sb, Sh};
use super::net::Transport;
use qsag_agg::zk_hem::v2::{field5::Fp5, params::LIMBS};

type F = Goldilocks;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InputError {
    Mpc(MpcError),
    /// Some custodian's input is not a bit.
    NotBits,
}

impl From<MpcError> for InputError {
    fn from(e: MpcError) -> Self {
        Self::Mpc(e)
    }
}

/// The XOR contribution of custodian `party` to a secret that `quorum` (distinct custodian
/// indices, at least the sharing's threshold many) reconstructs: its Shamir share times
/// its Lagrange weight at zero. `None` if `party` is not in `quorum` or the quorum has a
/// repeated or out-of-range index.
pub fn xor_share_from_shamir(quorum: &[usize], party: usize, share: &[u8]) -> Option<Vec<u8>> {
    let pos = quorum.iter().position(|&p| p == party)?;
    if quorum.iter().any(|&p| p >= 255)
        || (0..quorum.len()).any(|i| quorum[..i].contains(&quorum[i]))
    {
        return None;
    }
    let points: Vec<TowerGf256> = quorum.iter().map(|&p| TowerGf256((p + 1) as u8)).collect();
    let weight = lagrange_weights_zero_gf256(&points)?[pos].0;
    let weights = alloc::vec![weight; share.len()];
    let mut out = alloc::vec![0u8; share.len()];
    qsag_asm::gf256_shamir_mul(&mut out, share, &weights);
    Some(out)
}

/// Triples and uniform values one custodian consumes in [`input_secret_bits`].
pub const fn input_demand(parties: usize, bytes: usize) -> (usize, usize) {
    if parties == 0 {
        return (0, 0);
    }
    let bits = 8usize.saturating_mul(bytes);
    (
        bits.saturating_mul(2usize.saturating_mul(parties).saturating_sub(1))
            .saturating_add(EXT_MUL_TRIPLES),
        bits.saturating_add(LIMBS)
            .saturating_mul(parties)
            .saturating_add(LIMBS),
    )
}

/// Authenticated shares of the bits of the secret whose XOR shares the custodians hold,
/// bit `k` of byte `i` at index `8 i + k`.
pub fn input_secret_bits<T: Transport>(
    e: &mut Engine<T>,
    xor_share: &[u8],
) -> Result<Vec<Sb>, InputError> {
    let (me, parties) = (e.me(), e.parties());
    let count = 8 * xor_share.len();
    let mine: SecretScratch<F> = (0..count)
        .map(|i| F::from_u64_reduced(u64::from((xor_share[i / 8] >> (i % 8)) & 1)))
        .collect();
    let mut inputs = SecretBuffer(Vec::with_capacity(parties));
    for owner in 0..parties {
        inputs.push(e.input(owner, (owner == me).then_some(&mine[..]), count)?);
    }
    drop(mine);

    let flat: SecretScratch<Sb> = inputs.iter().flatten().copied().collect();
    verify_bits(e, &flat)?;

    let mut acc = SecretBuffer(core::mem::take(&mut inputs[0]));
    for next in &inputs[1..] {
        let both = SecretScratch::from(e.mul(&acc, next)?);
        for ((a, &b), &ab) in acc.iter_mut().zip(next).zip(&both) {
            *a = *a + b - ab.scale(F::TWO);
        }
    }
    Ok(acc.into_inner())
}

fn verify_bits<T: Transport>(e: &mut Engine<T>, bits: &[Sb]) -> Result<(), InputError> {
    let minus_one = e.public(F::ZERO - F::ONE);
    let shifted: SecretScratch<Sb> = bits.iter().map(|&b| b + minus_one).collect();
    let products = SecretScratch::from(e.mul(bits, &shifted)?);
    e.check()?;
    let mut coins = e.public_coins(b"COLLAB-INPUT-BIT-CHECK")?;
    let sum = SecretBuffer(
        products
            .iter()
            .fold(Sh::ZERO, |s, &p| s + p.scale_ext(coins.next_fp5())),
    );
    let rho = SecretBuffer(e.random_ext()?);
    let blinded =
        SecretScratch::from(e.mul_ext(core::slice::from_ref(&*sum), core::slice::from_ref(&*rho))?);
    e.check()?;
    let opened = e.open_ext(&blinded)?;
    e.check()?;
    if opened[0] != Fp5::ZERO {
        e.poison();
        return Err(InputError::NotBits);
    }
    Ok(())
}

#[cfg(test)]
pub(super) mod tests {
    use super::super::engine::Dealer;
    use super::super::engine::tests::run_parties;
    use super::*;
    use qsag_core::field::tower::eval_poly_gf256;

    /// `(k, n)` Shamir shares of `secret`, custodian `p` at point `p + 1`.
    pub(in super::super) fn shamir(secret: &[u8], k: usize, n: usize, tag: u8) -> Vec<Vec<u8>> {
        let mut shares = alloc::vec![Vec::new(); n];
        for (i, &byte) in secret.iter().enumerate() {
            let coeffs: Vec<TowerGf256> = (0..k)
                .map(|j| {
                    if j == 0 {
                        TowerGf256(byte)
                    } else {
                        TowerGf256(
                            (i as u8)
                                .wrapping_mul(31)
                                .wrapping_add(tag)
                                .wrapping_add(j as u8 * 77),
                        )
                    }
                })
                .collect();
            for (p, share) in shares.iter_mut().enumerate() {
                share.push(eval_poly_gf256(&coeffs, TowerGf256((p + 1) as u8)).0);
            }
        }
        shares
    }

    #[test]
    fn a_shamir_quorum_shares_the_bits_of_the_secret() {
        let secret: Vec<u8> = (0..32u8).map(|i| i.wrapping_mul(73) ^ 0xa5).collect();
        for (k, n, quorum) in [
            (2usize, 3usize, alloc::vec![0usize, 2]),
            (3, 5, alloc::vec![4, 1, 2]),
        ] {
            let shares = shamir(&secret, k, n, 9);
            let xor: Vec<Vec<u8>> = quorum
                .iter()
                .map(|&p| xor_share_from_shamir(&quorum, p, &shares[p]).unwrap())
                .collect();
            // The XOR shares reconstruct the secret, and no proper subset of them does.
            let fold = |parts: &[Vec<u8>]| {
                parts.iter().fold(alloc::vec![0u8; 32], |mut acc, s| {
                    acc.iter_mut().zip(s).for_each(|(a, b)| *a ^= b);
                    acc
                })
            };
            assert_eq!(fold(&xor), secret);
            assert_ne!(fold(&xor[1..]), secret);
            let outside = (0..n).find(|p| !quorum.contains(p)).unwrap();
            assert!(xor_share_from_shamir(&quorum, outside, &shares[outside]).is_none());
            assert!(xor_share_from_shamir(&[0, 0], 0, &shares[0]).is_none());

            let mut dealer = Dealer::new(k, &[5; 32]);
            let (triples, randoms) = input_demand(k, secret.len());
            let preps = dealer.preprocessing(triples, randoms);
            let out = run_parties(preps, |mut e| {
                let me = e.me();
                let bits = input_secret_bits(&mut e, &xor[me]).unwrap();
                let opened = e.open(&bits).unwrap();
                e.check().unwrap();
                assert_eq!(e.remaining(), (0, 0));
                opened
            });
            let expected: Vec<F> = (0..256)
                .map(|i| F::from_u64_reduced(u64::from((secret[i / 8] >> (i % 8)) & 1)))
                .collect();
            assert!(out.iter().all(|bits| bits == &expected));
        }
    }

    #[test]
    fn invalid_mask_share_fails_before_the_owner_broadcasts_input() {
        for byte in [0, 0xff] {
            let mut dealer = Dealer::new(2, &[0xa8 ^ byte; 32]);
            let (t, r) = input_demand(2, 1);
            let mut tapes = dealer.preprocessing(t, r);
            tapes[1].randoms[0].v -= F::ONE;
            let out = run_parties(tapes, |mut e| {
                let result = input_secret_bits(&mut e, &[byte]);
                assert_eq!(e.stats.triples_used, 0);
                assert_eq!(e.stats.mac_checks, 1);
                result
            });
            assert!(
                out.iter()
                    .all(|r| *r == Err(InputError::Mpc(MpcError::MacCheck)))
            );
        }
    }

    /// A custodian whose input is not a bit is caught before the bits are combined.
    #[test]
    fn an_input_that_is_not_a_bit_is_refused() {
        let mut dealer = Dealer::new(2, &[6; 32]);
        let (triples, randoms) = input_demand(2, 1);
        let preps = dealer.preprocessing(triples, randoms);
        let out = run_parties(preps, |mut e| {
            if e.me() == 1 {
                // Follow the input protocol by hand with the value 2 in the first slot.
                let mut values = alloc::vec![F::ZERO; 8];
                values[0] = F::TWO;
                let mut inputs = alloc::vec![e.input(0, None, 8).unwrap()];
                inputs.push(e.input(1, Some(&values), 8).unwrap());
                let flat: Vec<Sb> = inputs.iter().flatten().copied().collect();
                return verify_bits(&mut e, &flat);
            }
            input_secret_bits(&mut e, &[0x3c]).map(|_| ())
        });
        assert_eq!(out[0], Err(InputError::NotBits));
        assert_eq!(out[1], Err(InputError::NotBits));
    }

    #[test]
    fn tooth_input_demand_zero_parties_does_not_underflow() {
        // `#tooth`: `input_demand(0, 32)` previously panicked with `2 * 0 - 1` underflow.
        assert_eq!(input_demand(0, 32), (0, 0));
        assert_eq!(input_demand(1, 4), (41, 42));
        assert_eq!(input_demand(3, 4), (169, 116));
    }
}
