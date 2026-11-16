//! Preprocessing for the authenticated general-quorum engine (`threshold_mpc`).
//!
//! One ceremony yields, for every quorum member, a [`MacKeyShare`] and a
//! [`PartyPreprocessing`] store of authenticated material under those keys.
//! The material is independent of the witness and of the statement, is used
//! once, and is consumed in the same order by every member.
use crate::{
    outer_mpc::Error,
    threshold_mpc::{AuthWord, BooleanTriple, DaBitWord, FieldShare, FieldTriple, ThresholdField},
};
use alloc::{collections::VecDeque, vec::Vec};

pub mod dealerless;

/// How much material one stream needs, per kind and field.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Demand {
    pub boolean_triples: usize,
    pub auth_words: usize,
    /// Indexed by [`ThresholdField`] discriminant.
    pub field_triples: [usize; 5],
    pub field_randoms: [usize; 5],
    pub dabits: [usize; 5],
}

/// One quorum member's one-use material for one stream. A transport serves
/// its `take_*` methods from here; a request beyond what is stored fails
/// closed and consumes nothing.
#[derive(Default)]
pub struct PartyPreprocessing {
    boolean_triples: VecDeque<BooleanTriple>,
    auth_words: VecDeque<AuthWord>,
    field_triples: [VecDeque<FieldTriple>; 5],
    field_randoms: [VecDeque<FieldShare>; 5],
    dabits: [VecDeque<DaBitWord>; 5],
}

fn take<V>(queue: &mut VecDeque<V>, count: usize) -> Result<Vec<V>, Error> {
    if queue.len() < count {
        return Err(Error::MissingPreprocessing);
    }
    Ok(queue.drain(..count).collect())
}

impl PartyPreprocessing {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn remaining(&self) -> Demand {
        Demand {
            boolean_triples: self.boolean_triples.len(),
            auth_words: self.auth_words.len(),
            field_triples: core::array::from_fn(|i| self.field_triples[i].len()),
            field_randoms: core::array::from_fn(|i| self.field_randoms[i].len()),
            dabits: core::array::from_fn(|i| self.dabits[i].len()),
        }
    }
    pub fn add_boolean_triples(&mut self, items: impl IntoIterator<Item = BooleanTriple>) {
        self.boolean_triples.extend(items);
    }
    pub fn add_auth_words(&mut self, items: impl IntoIterator<Item = AuthWord>) {
        self.auth_words.extend(items);
    }
    pub fn add_field_triples(
        &mut self,
        field: ThresholdField,
        items: impl IntoIterator<Item = FieldTriple>,
    ) {
        self.field_triples[field.index()].extend(items);
    }
    pub fn add_field_randoms(
        &mut self,
        field: ThresholdField,
        items: impl IntoIterator<Item = FieldShare>,
    ) {
        self.field_randoms[field.index()].extend(items);
    }
    pub fn add_dabits(
        &mut self,
        field: ThresholdField,
        items: impl IntoIterator<Item = DaBitWord>,
    ) {
        self.dabits[field.index()].extend(items);
    }
    pub fn take_boolean_triples(&mut self, count: usize) -> Result<Vec<BooleanTriple>, Error> {
        take(&mut self.boolean_triples, count)
    }
    pub fn take_auth_words(&mut self, count: usize) -> Result<Vec<AuthWord>, Error> {
        take(&mut self.auth_words, count)
    }
    pub fn take_field_triples(
        &mut self,
        field: ThresholdField,
        count: usize,
    ) -> Result<Vec<FieldTriple>, Error> {
        take(&mut self.field_triples[field.index()], count)
    }
    pub fn take_field_randoms(
        &mut self,
        field: ThresholdField,
        count: usize,
    ) -> Result<Vec<FieldShare>, Error> {
        take(&mut self.field_randoms[field.index()], count)
    }
    pub fn take_dabits(
        &mut self,
        field: ThresholdField,
        count: usize,
    ) -> Result<Vec<DaBitWord>, Error> {
        take(&mut self.dabits[field.index()], count)
    }
}

#[cfg(any(test, feature = "test-dealer"))]
pub use fixture::FixtureDealer;

#[cfg(any(test, feature = "test-dealer"))]
mod fixture {
    use super::*;
    use crate::{
        circuit::{Domain, Value, ZERO},
        threshold_mpc::{BlindOtPeer, MacKeyShare, ThresholdConfig, mac_scale, mac_sub},
    };
    use qsag_accel::keccak::Shake256;

    /// Deterministic single-process generator of consistent material for a
    /// whole quorum, for tests and benchmarks of the online protocol.
    ///
    /// It knows every MAC key and every shared value, and after seeding it
    /// expands with a non-cryptographic generator. It exists only under
    /// `cfg(test)` or the `test-dealer` feature.
    pub struct FixtureDealer {
        state: [u64; 4],
        members: usize,
        boolean_keys: Vec<u128>,
        field_keys: Vec<[Value; 5]>,
        blind_ot: Vec<Vec<BlindOtPeer>>,
    }

    impl FixtureDealer {
        pub fn new(config: &ThresholdConfig, seed: [u8; 32]) -> Self {
            let mut xof = Shake256::new();
            xof.absorb(b"QSAG.OUTER.SPDZ.FIXTURE.V1");
            xof.absorb(&config.binding());
            xof.absorb(&seed);
            xof.finalize(0x1f);
            let mut bytes = [0u8; 32];
            xof.squeeze(&mut bytes);
            let state = core::array::from_fn(|i| {
                u64::from_le_bytes(bytes[8 * i..8 * i + 8].try_into().unwrap()) | 1
            });
            let members = config.quorum().len();
            let mut dealer = Self {
                state,
                members,
                boolean_keys: Vec::new(),
                field_keys: Vec::new(),
                blind_ot: Vec::new(),
            };
            for _ in 0..members {
                let boolean = dealer.u128();
                let field = ThresholdField::ALL.map(|f| dealer.mac(f.domain()));
                dealer.boolean_keys.push(boolean);
                dealer.field_keys.push(field);
            }
            let slot_of = |owner: usize, peer: usize| -> usize {
                if peer < owner { peer } else { peer - 1 }
            };
            let mut blind_ot: Vec<Vec<BlindOtPeer>> = (0..members)
                .map(|_| {
                    (0..members.saturating_sub(1))
                        .map(|_| BlindOtPeer {
                            sender_delta: 0,
                            sender_seeds: [[0u8; 32]; 128],
                            receiver_seeds: [[[0u8; 32]; 2]; 128],
                            counter: 0,
                        })
                        .collect()
                })
                .collect();
            for sender in 0..members {
                for receiver in 0..members {
                    if sender == receiver {
                        continue;
                    }
                    let delta = dealer.u128();
                    let mut chosen = [[0u8; 32]; 128];
                    let mut pairs = [[[0u8; 32]; 2]; 128];
                    for col in 0..128 {
                        let s0 = dealer.bytes32();
                        let s1 = dealer.bytes32();
                        pairs[col] = [s0, s1];
                        chosen[col] = if ((delta >> col) & 1) != 0 { s1 } else { s0 };
                    }
                    let s_slot = slot_of(sender, receiver);
                    let r_slot = slot_of(receiver, sender);
                    blind_ot[sender][s_slot].sender_delta = delta;
                    blind_ot[sender][s_slot].sender_seeds = chosen;
                    blind_ot[receiver][r_slot].receiver_seeds = pairs;
                }
            }
            dealer.blind_ot = blind_ot;
            dealer
        }

        /// Key shares by quorum position.
        pub fn mac_key_shares(&self) -> Vec<MacKeyShare> {
            self.boolean_keys
                .iter()
                .zip(&self.field_keys)
                .zip(&self.blind_ot)
                .map(|((&boolean, &field), blind_ot)| MacKeyShare {
                    boolean,
                    field,
                    blind_ot: blind_ot.clone(),
                })
                .collect()
        }

        // xoshiro256**
        fn u64(&mut self) -> u64 {
            let s = &mut self.state;
            let out = s[1].wrapping_mul(5).rotate_left(7).wrapping_mul(9);
            let t = s[1] << 17;
            s[2] ^= s[0];
            s[3] ^= s[1];
            s[1] ^= s[2];
            s[0] ^= s[3];
            s[2] ^= t;
            s[3] = s[3].rotate_left(45);
            out
        }
        fn u128(&mut self) -> u128 {
            (self.u64() as u128) | ((self.u64() as u128) << 64)
        }
        fn bytes32(&mut self) -> [u8; 32] {
            let mut out = [0u8; 32];
            for chunk in out.chunks_exact_mut(8) {
                chunk.copy_from_slice(&self.u64().to_le_bytes());
            }
            out
        }
        fn field(&mut self, d: Domain) -> Value {
            loop {
                let mut v = ZERO;
                for limb in &mut v[..d.limbs_len()] {
                    *limb = self.u64();
                }
                if d == Domain::Ed || d == Domain::PallasFp {
                    v[3] &= 0x7fff_ffff_ffff_ffff;
                } else if d == Domain::BlsFp {
                    v[5] &= 0x1fff_ffff_ffff_ffff;
                }
                if d.canonical(v) {
                    return v;
                }
            }
        }
        fn mac(&mut self, d: Domain) -> Value {
            if d == Domain::Gold {
                [self.field(d)[0], self.field(d)[0], 0, 0, 0, 0]
            } else {
                self.field(d)
            }
        }
        fn boolean_key(&self) -> u128 {
            self.boolean_keys.iter().fold(0, |a, b| a ^ b)
        }
        fn field_key(&self, field: ThresholdField) -> Value {
            let d = field.domain();
            self.field_keys.iter().fold(ZERO, |a, k| {
                crate::threshold_mpc::mac_add(d, a, k[field.index()])
            })
        }

        fn share_word(&mut self, word: u64, key: u128) -> Vec<AuthWord> {
            let mut shares: Vec<AuthWord> = (0..self.members)
                .map(|_| AuthWord {
                    share: 0,
                    macs: [0; 64],
                })
                .collect();
            let mut rest = word;
            let mut macs: [u128; 64] =
                core::array::from_fn(|k| key & 0u128.wrapping_sub(((word >> k) & 1) as u128));
            for share in &mut shares[1..] {
                share.share = self.u64();
                rest ^= share.share;
                for (mac, total) in share.macs.iter_mut().zip(&mut macs) {
                    *mac = self.u128();
                    *total ^= *mac;
                }
            }
            shares[0].share = rest;
            shares[0].macs = macs;
            shares
        }

        fn share_field(
            &mut self,
            value: Value,
            field: ThresholdField,
            key: Value,
        ) -> Vec<FieldShare> {
            let d = field.domain();
            let mut rest = [value, mac_scale(d, key, value)];
            let mut shares = Vec::with_capacity(self.members);
            for _ in 1..self.members {
                let share = [self.field(d), self.mac(d)];
                rest = [d.sub(rest[0], share[0]), mac_sub(d, rest[1], share[1])];
                shares.push(FieldShare(share));
            }
            shares.insert(0, FieldShare(rest));
            shares
        }

        fn rows<V>(&self, count: usize) -> Vec<Vec<V>> {
            (0..self.members)
                .map(|_| Vec::with_capacity(count))
                .collect()
        }
        fn push<V>(rows: &mut [Vec<V>], shares: Vec<V>) {
            for (row, share) in rows.iter_mut().zip(shares) {
                row.push(share);
            }
        }

        /// Output indexed by quorum position, then item.
        pub fn auth_words(&mut self, count: usize) -> Vec<Vec<AuthWord>> {
            let key = self.boolean_key();
            let mut rows = self.rows(count);
            for _ in 0..count {
                let word = self.u64();
                Self::push(&mut rows, self.share_word(word, key));
            }
            rows
        }

        pub fn boolean_triples(&mut self, count: usize) -> Vec<Vec<BooleanTriple>> {
            let key = self.boolean_key();
            let mut rows = self.rows(count);
            for _ in 0..count {
                let (a, b) = (self.u64(), self.u64());
                let parts = [
                    self.share_word(a, key),
                    self.share_word(b, key),
                    self.share_word(a & b, key),
                ];
                let [a, b, c] = parts.map(Vec::into_iter);
                let triples = a
                    .zip(b)
                    .zip(c)
                    .map(|((a, b), c)| BooleanTriple { a, b, c })
                    .collect();
                Self::push(&mut rows, triples);
            }
            rows
        }

        pub fn field_randoms(
            &mut self,
            field: ThresholdField,
            count: usize,
        ) -> Vec<Vec<FieldShare>> {
            let key = self.field_key(field);
            let mut rows = self.rows(count);
            for _ in 0..count {
                let value = self.field(field.domain());
                Self::push(&mut rows, self.share_field(value, field, key));
            }
            rows
        }

        pub fn field_triples(
            &mut self,
            field: ThresholdField,
            count: usize,
        ) -> Vec<Vec<FieldTriple>> {
            let d = field.domain();
            let key = self.field_key(field);
            let mut rows = self.rows(count);
            for _ in 0..count {
                let (a, b) = (self.field(d), self.field(d));
                let parts = [
                    self.share_field(a, field, key),
                    self.share_field(b, field, key),
                    self.share_field(d.mul(a, b), field, key),
                ];
                let [a, b, c] = parts.map(Vec::into_iter);
                let triples = a
                    .zip(b)
                    .zip(c)
                    .map(|((a, b), c)| FieldTriple([a, b, c]))
                    .collect();
                Self::push(&mut rows, triples);
            }
            rows
        }

        pub fn dabits(&mut self, field: ThresholdField, count: usize) -> Vec<Vec<DaBitWord>> {
            let boolean_key = self.boolean_key();
            let key = self.field_key(field);
            let mut rows = self.rows(count);
            for _ in 0..count {
                let word = self.u64();
                let bits = self.share_word(word, boolean_key);
                let mut lanes: Vec<Vec<FieldShare>> = self.rows(64);
                for lane in 0..64 {
                    let value = [(word >> lane) & 1, 0, 0, 0, 0, 0];
                    Self::push(&mut lanes, self.share_field(value, field, key));
                }
                let dabits = bits
                    .into_iter()
                    .zip(lanes)
                    .map(|(bits, lanes)| DaBitWord {
                        bits,
                        field: lanes.try_into().unwrap_or_else(|_| unreachable!()),
                    })
                    .collect();
                Self::push(&mut rows, dabits);
            }
            rows
        }

        /// The Boolean MAC key, for tests that check shares against it.
        #[cfg(test)]
        pub(crate) fn boolean_mac_of(&self, word: u64) -> u128 {
            qsag_accel::gf2_128::gf2_128_mul(self.boolean_key(), word as u128)
        }
    }
}
