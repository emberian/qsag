//! General custodian quorums, separate from the three virtual ZKBoo views.
//!
//! This backend uses additive online sharing and one-use trusted-dealer Beaver
//! triples. Online additive privacy requires at least one honest participant;
//! Shamir custody additionally requires fewer than `t` colluding custodians.
//! It does NOT provide the RSS backend's active-security
//! guarantee. Pairwise authentication detects transport corruption, not malicious
//! computation. Preprocessing must be independent of witnesses, never reused,
//! delivered confidentially, and erased by the dealer before online execution.
use crate::{
    circuit::{Domain, Value},
    outer_mpc::{Bit, Engine, Envelope, Error, FieldWord, Transport, Word},
    secret::{Secret, SecretVec},
};
use alloc::{vec, vec::Vec};
use qsag_accel::{
    ct::{ct_eq_bytes_mask, ct_zeroize_bytes, ct_zeroize_u64s},
    keccak::{Shake256, cshake256_framed_32},
};

/// Immutable roster and ordered active quorum. Party identities are zero based;
/// Shamir evaluation points are `party + 1` in the AES GF(256) polynomial basis.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ThresholdConfig {
    threshold: usize,
    parties: usize,
    quorum: Vec<usize>,
}
impl ThresholdConfig {
    pub fn new(threshold: usize, parties: usize, quorum: Vec<usize>) -> Result<Self, Error> {
        if !(2..=64).contains(&parties)
            || !(2..=parties).contains(&threshold)
            || quorum.len() < threshold
            || quorum.len() > parties
            || quorum.iter().any(|&p| p >= parties)
            || quorum.windows(2).any(|w| w[0] >= w[1])
        {
            return Err(Error::InvalidConfiguration);
        }
        Ok(Self {
            threshold,
            parties,
            quorum,
        })
    }
    pub fn threshold(&self) -> usize {
        self.threshold
    }
    pub fn parties(&self) -> usize {
        self.parties
    }
    pub fn quorum(&self) -> &[usize] {
        &self.quorum
    }
    pub(crate) fn binding(&self) -> Vec<u8> {
        let mut b = vec![self.threshold as u8, self.parties as u8];
        b.extend(self.quorum.iter().map(|&p| p as u8));
        b
    }
    /// Convert a bytewise degree-(t-1) Shamir share to its XOR contribution,
    /// without reconstructing any byte of the witness locally.
    pub fn shamir_contribution(&self, party: usize, share: &[u8; 32]) -> Result<[u8; 32], Error> {
        if !self.quorum.contains(&party) {
            return Err(Error::InvalidConfiguration);
        }
        let x = (party + 1) as u8;
        let mut weight = 1;
        for &peer in &self.quorum {
            if peer != party {
                let y = (peer + 1) as u8;
                weight = gf_mul(weight, gf_mul(y, gf_pow(x ^ y, 254)));
            }
        }
        Ok(share.map(|b| gf_mul(b, weight)))
    }
}
fn gf_mul(mut a: u8, mut b: u8) -> u8 {
    let mut out = 0;
    for _ in 0..8 {
        out ^= a & 0u8.wrapping_sub(b & 1);
        a = (a << 1) ^ (0x1b & 0u8.wrapping_sub(a >> 7));
        b >>= 1;
    }
    out
}
fn gf_pow(mut a: u8, mut n: u8) -> u8 {
    let mut out = 1;
    while n != 0 {
        if n & 1 != 0 {
            out = gf_mul(out, a);
        }
        a = gf_mul(a, a);
        n >>= 1;
    }
    out
}

/// Field identifier for preprocessing requests; independent of private circuit types.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ThresholdField {
    Goldilocks,
    Secp256k1,
    Ed25519,
}
impl ThresholdField {
    fn domain(self) -> Domain {
        match self {
            Self::Goldilocks => Domain::Gold,
            Self::Secp256k1 => Domain::Secp,
            Self::Ed25519 => Domain::Ed,
        }
    }
    pub(crate) fn from_domain(d: Domain) -> Self {
        match d {
            Domain::Gold => Self::Goldilocks,
            Domain::Secp => Self::Secp256k1,
            Domain::Ed => Self::Ed25519,
            Domain::Bit => unreachable!(),
        }
    }
}
/// One party's one-use XOR shares of 64 independent Boolean triples `(a,b,a&b)`.
/// The type is intentionally neither Clone nor Copy.
pub struct BooleanTriple(pub [u64; 3]);
impl Drop for BooleanTriple {
    fn drop(&mut self) {
        ct_zeroize_u64s(&mut self.0);
    }
}
/// One party's one-use additive shares of a field triple `(a,b,a*b)`.
pub struct FieldTriple(pub [[u64; 4]; 3]);
impl Drop for FieldTriple {
    fn drop(&mut self) {
        ct_zeroize_u64s(self.0.as_flattened_mut());
    }
}

/// Offline trusted preprocessing generator. Construct once with fresh secret
/// entropy; consume batches in the same order at all quorum members. Never give
/// this object or its entropy to an online custodian. Recreating it with the same
/// entropy/session reuses triples and destroys privacy.
pub struct TrustedDealer {
    rng: Shake256,
    config: ThresholdConfig,
}
impl TrustedDealer {
    pub fn new(config: ThresholdConfig, session: &[u8; 32], mut entropy: [u8; 32]) -> Self {
        let mut rng = Shake256::new();
        rng.absorb(b"QSAG.OUTER.TRUSTED.PREPROCESS.V1");
        rng.absorb(session);
        rng.absorb(&config.binding());
        rng.absorb(&entropy);
        rng.finalize(0x1f);
        ct_zeroize_bytes(&mut entropy);
        Self { rng, config }
    }
    fn word(&mut self) -> u64 {
        let mut bytes = [0; 8];
        self.rng.squeeze(&mut bytes);
        let word = u64::from_le_bytes(bytes);
        ct_zeroize_bytes(&mut bytes);
        word
    }
    fn field(&mut self, d: Domain) -> Value {
        loop {
            let mut v = Secret([0; 4]);
            for x in &mut v[..d.width().div_ceil(64)] {
                *x = self.word();
            }
            if d == Domain::Ed {
                v[3] &= 0x7fff_ffff_ffff_ffff;
            }
            if d.canonical(*v) {
                return *v;
            }
        }
    }
    /// Output indexed by active quorum position, then gate index.
    pub fn boolean_triples(&mut self, count: usize) -> Vec<Vec<BooleanTriple>> {
        let n = self.config.quorum.len();
        let mut out: Vec<_> = (0..n).map(|_| Vec::with_capacity(count)).collect();
        for _ in 0..count {
            let a = Secret(self.word());
            let b = Secret(self.word());
            let mut total = Secret([*a, *b, *a & *b]);
            for row in &mut out[..n - 1] {
                let shares = core::array::from_fn(|_| self.word());
                for (sum, share) in total.iter_mut().zip(shares) {
                    *sum ^= share;
                }
                row.push(BooleanTriple(shares));
            }
            out[n - 1].push(BooleanTriple(*total));
        }
        out
    }
    /// Output indexed by active quorum position, then scalar multiplication index.
    pub fn field_triples(&mut self, field: ThresholdField, count: usize) -> Vec<Vec<FieldTriple>> {
        let d = field.domain();
        let n = self.config.quorum.len();
        let mut out: Vec<_> = (0..n).map(|_| Vec::with_capacity(count)).collect();
        for _ in 0..count {
            let a = Secret(self.field(d));
            let b = Secret(self.field(d));
            let mut total = Secret([*a, *b, d.mul(*a, *b)]);
            for row in &mut out[..n - 1] {
                let shares = core::array::from_fn(|_| self.field(d));
                for (sum, share) in total.iter_mut().zip(shares) {
                    *sum = d.sub(*sum, share);
                }
                row.push(FieldTriple(shares));
            }
            out[n - 1].push(FieldTriple(*total));
        }
        out
    }
}

pub(crate) struct State {
    pub config: ThresholdConfig,
    pub party: usize,
    session: [u8; 32],
    keys: Vec<[u8; 32]>,
    sequence: u64,
    failed: bool,
}
impl Drop for State {
    fn drop(&mut self) {
        for key in &mut self.keys {
            ct_zeroize_bytes(key);
        }
    }
}
impl State {
    pub fn new(
        config: ThresholdConfig,
        party: usize,
        session: [u8; 32],
        keys: Vec<[u8; 32]>,
    ) -> Result<Self, Error> {
        if !config.quorum.contains(&party) || keys.len() != config.quorum.len() - 1 {
            return Err(Error::InvalidConfiguration);
        }
        let session =
            cshake256_framed_32(b"QSAG.OUTER.THRESHOLD.V1", &[&session, &config.binding()]);
        Ok(Self {
            config,
            party,
            session,
            keys,
            sequence: 0,
            failed: false,
        })
    }
    fn tag(&self, key: &[u8; 32], sender: usize, recipient: usize, payload: &[u64]) -> [u8; 32] {
        let mut encoded: Vec<u8> = payload.iter().flat_map(|w| w.to_le_bytes()).collect();
        let tag = cshake256_framed_32(
            b"QSAG.OUTER.THRESHOLD.MAC.V1",
            &[
                key,
                &self.session,
                &(sender as u64).to_le_bytes(),
                &(recipient as u64).to_le_bytes(),
                &self.sequence.to_le_bytes(),
                &encoded,
            ],
        );
        ct_zeroize_bytes(&mut encoded);
        tag
    }
    fn broadcast<T: Transport>(
        &mut self,
        transport: &mut T,
        own: &[u64],
    ) -> Result<Vec<SecretVec<u64>>, Error> {
        if self.failed {
            return Err(Error::MultiplicationCheck);
        }
        // Any error consumes the session. Only complete authenticated rounds unpoison it.
        self.failed = true;
        let peers: Vec<_> = self
            .config
            .quorum
            .iter()
            .copied()
            .filter(|&p| p != self.party)
            .collect();
        let outgoing = peers
            .iter()
            .zip(&self.keys)
            .map(|(&peer, key)| Envelope {
                sender: self.party,
                recipient: peer,
                sequence: self.sequence,
                payload: own.to_vec(),
                tag: self.tag(key, self.party, peer, own),
            })
            .collect();
        let incoming = transport.exchange_many(outgoing)?;
        if incoming.len() != peers.len() {
            return Err(Error::InvalidConfiguration);
        }
        let mut result = Vec::with_capacity(peers.len());
        for ((mut message, &peer), key) in incoming.into_iter().zip(&peers).zip(&self.keys) {
            if message.sender != peer
                || message.recipient != self.party
                || message.sequence != self.sequence
                || message.payload.len() != own.len()
                || ct_eq_bytes_mask(
                    &message.tag,
                    &self.tag(key, peer, self.party, &message.payload),
                ) != u64::MAX
            {
                return Err(Error::Authentication(peer));
            }
            result.push(core::mem::take(&mut message.payload).into());
        }
        self.sequence = self
            .sequence
            .checked_add(1)
            .ok_or(Error::InvalidConfiguration)?;
        self.failed = false;
        Ok(result)
    }
    pub fn agree<T: Transport>(&mut self, t: &mut T, root: [u8; 32]) -> Result<(), Error> {
        let own: Vec<_> = root
            .chunks_exact(8)
            .map(|b| u64::from_le_bytes(b.try_into().unwrap()))
            .collect();
        let received = self.broadcast(t, &own)?;
        if received.iter().any(|r| r.as_ref() != own.as_slice()) {
            self.failed = true;
            return Err(Error::InvalidProof);
        }
        Ok(())
    }
    pub fn open_bits<T: Transport>(&mut self, t: &mut T, own: &[u64]) -> Result<Vec<u64>, Error> {
        let mut out: SecretVec<_> = own.iter().copied().collect();
        for row in self.broadcast(t, own)? {
            for (a, b) in out.iter_mut().zip(row.iter()) {
                *a ^= b;
            }
        }
        Ok(out.iter().copied().collect())
    }
    pub fn open_fields<T: Transport>(
        &mut self,
        t: &mut T,
        own: &[Value],
        d: Domain,
    ) -> Result<Vec<Value>, Error> {
        let mut out: SecretVec<_> = own.iter().copied().collect();
        for row in self.broadcast(t, own.as_flattened())? {
            for (a, b) in out.iter_mut().zip(row.chunks_exact(4)) {
                let b = b.try_into().unwrap();
                if !d.canonical(b) {
                    self.failed = true;
                    return Err(Error::InvalidConfiguration);
                }
                *a = d.add(*a, b);
            }
        }
        Ok(out.iter().copied().collect())
    }
    pub fn and<T: Transport>(&mut self, t: &mut T, pairs: &[(Bit, Bit)]) -> Result<Word, Error> {
        if self.failed {
            return Err(Error::MultiplicationCheck);
        }
        self.failed = true;
        let triples = t.take_boolean_triples(pairs.len())?;
        if triples.len() != pairs.len() {
            return Err(Error::InvalidConfiguration);
        }
        let masks: SecretVec<u64> = pairs
            .iter()
            .zip(&triples)
            .flat_map(|(&(a, b), r)| [a.0[0] ^ r.0[0], b.0[0] ^ r.0[1]])
            .collect();
        self.failed = false;
        let opened = self.open_bits(t, &masks)?;
        Ok(triples
            .iter()
            .zip(opened.chunks_exact(2))
            .map(|(r, v)| {
                Bit([
                    r.0[2]
                        ^ (v[0] & r.0[1])
                        ^ (v[1] & r.0[0])
                        ^ if self.party == self.config.quorum[0] {
                            v[0] & v[1]
                        } else {
                            0
                        },
                    0,
                ])
            })
            .collect())
    }
    pub fn mul<T: Transport>(
        &mut self,
        t: &mut T,
        pairs: &[(&FieldWord, &FieldWord)],
        d: Domain,
    ) -> Result<Vec<FieldWord>, Error> {
        if self.failed {
            return Err(Error::MultiplicationCheck);
        }
        self.failed = true;
        let triples = t.take_field_triples(ThresholdField::from_domain(d), pairs.len() * 64)?;
        if triples.len() != pairs.len() * 64
            || triples.iter().any(|r| r.0.iter().any(|v| !d.canonical(*v)))
        {
            return Err(Error::InvalidConfiguration);
        }
        let masks: SecretVec<Value> = pairs
            .iter()
            .flat_map(|(a, b)| a.iter().zip(b.iter()))
            .zip(&triples)
            .flat_map(|((a, b), r)| [d.sub(a[0], r.0[0]), d.sub(b[0], r.0[1])])
            .collect();
        self.failed = false;
        let opened = self.open_fields(t, &masks, d)?;
        let values: FieldWord = triples
            .iter()
            .zip(opened.chunks_exact(2))
            .map(|(r, v)| {
                let mut value = d.add(r.0[2], d.add(d.mul(v[0], r.0[1]), d.mul(v[1], r.0[0])));
                if self.party == self.config.quorum[0] {
                    value = d.add(value, d.mul(v[0], v[1]));
                }
                [value, [0; 4]]
            })
            .collect();
        Ok(values
            .chunks_exact(64)
            .map(|w| w.iter().copied().collect())
            .collect())
    }
}

impl<T: Transport> Engine<T> {
    pub(crate) fn threshold_lift(
        &mut self,
        bits: &[Bit],
        d: Domain,
    ) -> Result<Vec<FieldWord>, Error> {
        let quorum = self.threshold.as_ref().unwrap().config.quorum.clone();
        let party = self.party;
        let make = |owner: usize| -> Vec<FieldWord> {
            bits.iter()
                .map(|bit| {
                    (0..64)
                        .map(|lane| {
                            [
                                [
                                    if party == owner {
                                        (bit.0[0] >> lane) & 1
                                    } else {
                                        0
                                    },
                                    0,
                                    0,
                                    0,
                                ],
                                [0; 4],
                            ]
                        })
                        .collect()
                })
                .collect()
        };
        let mut sum = make(quorum[0]);
        for owner in quorum.into_iter().skip(1) {
            let next = make(owner);
            let pairs: Vec<_> = sum.iter().zip(&next).collect();
            let products = self.fmul_many(&pairs, d)?;
            sum = sum
                .iter()
                .zip(&next)
                .zip(&products)
                .map(|((a, b), ab)| {
                    self.fsub(&self.fadd(a, b, d), &self.fscale(ab, [2, 0, 0, 0], d), d)
                })
                .collect();
        }
        Ok(sum)
    }
    pub(crate) fn threshold_bits_to_field(
        &mut self,
        words: &[Word],
        d: Domain,
    ) -> Result<Vec<FieldWord>, Error> {
        let mut out = Vec::with_capacity(words.len());
        // Bound temporary lifted bits while batching conversions across words.
        // Each lifted bit contains 64 scalar lanes; 1024 bits is about 4 MiB.
        let words_per_batch = (1024 / d.width()).max(1);
        for chunk in words.chunks(words_per_batch) {
            let bits: Word = chunk.iter().flat_map(|word| word.iter().copied()).collect();
            let lifted = self.threshold_lift(&bits, d)?;
            let mut offset = 0;
            for word in chunk {
                let mut sum = self.fconstant([0; 4]);
                let mut weight = [1, 0, 0, 0];
                for bit in &lifted[offset..offset + word.len()] {
                    sum = self.fadd(&sum, &self.fscale(bit, weight, d), d);
                    weight = d.add(weight, weight);
                }
                offset += word.len();
                out.push(sum);
            }
        }
        Ok(out)
    }
    pub(crate) fn threshold_field_to_bits(
        &mut self,
        words: &[&FieldWord],
        d: Domain,
    ) -> Result<Vec<Word>, Error> {
        let quorum = self.threshold.as_ref().unwrap().config.quorum.clone();
        let mut sum: Vec<Word> = words
            .iter()
            .map(|_| self.number([0; 4], d.width()))
            .collect();
        for owner in quorum {
            let components: Vec<Word> = words
                .iter()
                .map(|word| {
                    (0..d.width())
                        .map(|bit| {
                            let local = if self.party == owner {
                                word.iter().enumerate().fold(0, |v, (lane, p)| {
                                    v | (((p[0][bit / 64] >> (bit % 64)) & 1) << lane)
                                })
                            } else {
                                0
                            };
                            Bit([local, 0])
                        })
                        .collect()
                })
                .collect();
            sum = self.field_add_many(&sum, &components, d)?;
        }
        Ok(sum)
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use std::{
        collections::BTreeMap,
        sync::{Arc, Mutex, mpsc},
        time::Duration,
    };

    enum Batch {
        Bits(Vec<Option<Vec<BooleanTriple>>>),
        Fields(ThresholdField, Vec<Option<Vec<FieldTriple>>>),
    }
    struct DealerRounds {
        dealer: TrustedDealer,
        batches: BTreeMap<usize, Batch>,
    }
    pub(crate) struct Network {
        position: usize,
        config: ThresholdConfig,
        senders: Vec<mpsc::Sender<Envelope>>,
        incoming: mpsc::Receiver<Envelope>,
        pending: BTreeMap<(u64, usize), Envelope>,
        dealer: Arc<Mutex<DealerRounds>>,
        round: usize,
    }
    impl Transport for Network {
        fn exchange_many(&mut self, outgoing: Vec<Envelope>) -> Result<Vec<Envelope>, Error> {
            let sequence = outgoing[0].sequence;
            for envelope in outgoing {
                self.senders[envelope.recipient]
                    .send(envelope)
                    .map_err(|_| Error::Transport)?;
            }
            let mut received = Vec::new();
            for &peer in &self.config.quorum {
                if peer == self.config.quorum[self.position] {
                    continue;
                }
                let key = (sequence, peer);
                while !self.pending.contains_key(&key) {
                    let envelope = self
                        .incoming
                        .recv_timeout(Duration::from_secs(30))
                        .map_err(|_| Error::Transport)?;
                    assert!(
                        self.pending
                            .insert((envelope.sequence, envelope.sender), envelope)
                            .is_none()
                    );
                }
                received.push(self.pending.remove(&key).unwrap());
            }
            Ok(received)
        }
        fn take_boolean_triples(&mut self, count: usize) -> Result<Vec<BooleanTriple>, Error> {
            let mut dealer = self.dealer.lock().unwrap();
            if !dealer.batches.contains_key(&self.round) {
                let shares = dealer
                    .dealer
                    .boolean_triples(count)
                    .into_iter()
                    .map(Some)
                    .collect();
                dealer.batches.insert(self.round, Batch::Bits(shares));
            }
            let Batch::Bits(rows) = dealer.batches.get_mut(&self.round).unwrap() else {
                panic!("preprocessing domain disagreement")
            };
            let result = rows[self.position].take().unwrap();
            assert_eq!(result.len(), count);
            if rows.iter().all(Option::is_none) {
                dealer.batches.remove(&self.round);
            }
            self.round += 1;
            Ok(result)
        }
        fn take_field_triples(
            &mut self,
            field: ThresholdField,
            count: usize,
        ) -> Result<Vec<FieldTriple>, Error> {
            let mut dealer = self.dealer.lock().unwrap();
            if !dealer.batches.contains_key(&self.round) {
                let shares = dealer
                    .dealer
                    .field_triples(field, count)
                    .into_iter()
                    .map(Some)
                    .collect();
                dealer
                    .batches
                    .insert(self.round, Batch::Fields(field, shares));
            }
            let Batch::Fields(domain, rows) = dealer.batches.get_mut(&self.round).unwrap() else {
                panic!("preprocessing domain disagreement")
            };
            assert_eq!(*domain, field);
            let result = rows[self.position].take().unwrap();
            assert_eq!(result.len(), count);
            if rows.iter().all(Option::is_none) {
                dealer.batches.remove(&self.round);
            }
            self.round += 1;
            Ok(result)
        }
    }
    pub(crate) fn keys(config: &ThresholdConfig, party: usize) -> Vec<[u8; 32]> {
        config
            .quorum
            .iter()
            .filter(|&&p| p != party)
            .map(|&p| {
                cshake256_framed_32(
                    b"TEST.THRESHOLD.KEY",
                    &[&[party.min(p) as u8, party.max(p) as u8]],
                )
            })
            .collect()
    }
    pub(crate) fn run<F: Fn(usize, Network) + Sync>(config: ThresholdConfig, f: F) {
        let dealer = Arc::new(Mutex::new(DealerRounds {
            dealer: TrustedDealer::new(config.clone(), &[9; 32], [13; 32]),
            batches: BTreeMap::new(),
        }));
        let (senders, receivers): (Vec<_>, Vec<_>) =
            (0..config.parties).map(|_| mpsc::channel()).unzip();
        let mut receivers: Vec<_> = receivers.into_iter().map(Some).collect();
        std::thread::scope(|scope| {
            for (position, &party) in config.quorum.iter().enumerate() {
                let network = Network {
                    position,
                    config: config.clone(),
                    senders: senders.clone(),
                    incoming: receivers[party].take().unwrap(),
                    pending: BTreeMap::new(),
                    dealer: dealer.clone(),
                    round: 0,
                };
                let f = &f;
                scope.spawn(move || f(party, network));
            }
        });
        assert!(dealer.lock().unwrap().batches.is_empty());
    }
    pub(crate) fn shamir_share(party: usize, threshold: usize, witness: &[u8; 32]) -> [u8; 32] {
        let x = (party + 1) as u8;
        core::array::from_fn(|byte| {
            let mut out = witness[byte];
            let mut power = x;
            for degree in 1..threshold {
                let coefficient = (byte as u8)
                    .wrapping_mul(31)
                    .wrapping_add(degree as u8)
                    .wrapping_mul(13);
                out ^= gf_mul(power, coefficient);
                power = gf_mul(power, x);
            }
            out
        })
    }
    #[test]
    fn shamir_quorums_cover_every_supported_threshold_and_size() {
        let witness = core::array::from_fn(|i| i as u8 * 7);
        for n in 2..=64 {
            for t in 2..=n {
                // Include nonconsecutive, high party identifiers.
                let quorum: Vec<_> = (0..n)
                    .rev()
                    .take(t)
                    .collect::<Vec<_>>()
                    .into_iter()
                    .rev()
                    .collect();
                let cfg = ThresholdConfig::new(t, n, quorum).unwrap();
                let mut reconstructed = [0; 32];
                for &p in cfg.quorum() {
                    let share = shamir_share(p, t, &witness);
                    for (a, b) in reconstructed
                        .iter_mut()
                        .zip(cfg.shamir_contribution(p, &share).unwrap())
                    {
                        *a ^= b;
                    }
                }
                assert_eq!(reconstructed, witness, "{t}-of-{n}");
            }
        }
        let cfg = ThresholdConfig::new(2, 64, vec![0, 31, 63]).unwrap();
        let mut reconstructed = [0; 32];
        for &p in cfg.quorum() {
            for (a, b) in reconstructed.iter_mut().zip(
                cfg.shamir_contribution(p, &shamir_share(p, 2, &witness))
                    .unwrap(),
            ) {
                *a ^= b;
            }
        }
        assert_eq!(reconstructed, witness);
        for (t, n, q) in [
            (1, 3, vec![0, 1]),
            (4, 3, vec![0, 1, 2]),
            (2, 65, vec![0, 1]),
            (2, 3, vec![0]),
            (2, 3, vec![0, 0]),
            (2, 3, vec![1, 0]),
            (2, 3, vec![0, 3]),
        ] {
            assert!(ThresholdConfig::new(t, n, q).is_err());
        }
    }
    #[test]
    fn additive_engines_support_sparse_and_full_64_party_rosters() {
        for cfg in [
            ThresholdConfig::new(2, 64, vec![0, 63]).unwrap(),
            ThresholdConfig::new(3, 9, vec![1, 4, 8]).unwrap(),
            ThresholdConfig::new(64, 64, (0..64).collect()).unwrap(),
        ] {
            run(cfg.clone(), |party, network| {
                let mut engine =
                    Engine::new_threshold(party, [9; 32], cfg.clone(), keys(&cfg, party), network)
                        .unwrap();
                engine.mix_entropy(&[party as u8; 32]);
                engine.agree([17; 32]).unwrap();
                let a = engine
                    .share(&[0xa55a_u64.wrapping_mul(party as u64 + 1)])
                    .unwrap();
                let b = engine
                    .share(&[0x81f0_u64.wrapping_mul(party as u64 + 7)])
                    .unwrap();
                let c = engine.and(&[(a[0], b[0])]).unwrap();
                let expected_a = cfg
                    .quorum
                    .iter()
                    .fold(0, |v, &p| v ^ 0xa55a_u64.wrapping_mul(p as u64 + 1));
                let expected_b = cfg
                    .quorum
                    .iter()
                    .fold(0, |v, &p| v ^ 0x81f0_u64.wrapping_mul(p as u64 + 7));
                assert_eq!(engine.open(&c).unwrap(), vec![expected_a & expected_b]);
                for d in [Domain::Gold, Domain::Secp, Domain::Ed] {
                    let a = engine.fconstant([7, 0, 0, 0]);
                    let b = engine.fconstant([9, 0, 0, 0]);
                    let product = engine.fmul(&a, &b, d).unwrap();
                    let own: Vec<_> = product.iter().map(|p| p[0]).collect();
                    let result = engine
                        .threshold
                        .as_mut()
                        .unwrap()
                        .open_fields(&mut engine.transport, &own, d)
                        .unwrap();
                    assert_eq!(result, vec![[63, 0, 0, 0]; 64]);
                }
            });
        }
    }
    #[test]
    fn threshold_mixed_conversions_and_inverse_match_native() {
        let cfg = ThresholdConfig::new(3, 7, vec![1, 3, 6]).unwrap();
        run(cfg.clone(), |party, network| {
            let mut engine =
                Engine::new_threshold(party, [9; 32], cfg.clone(), keys(&cfg, party), network)
                    .unwrap();
            engine.mix_entropy(&[party as u8; 32]);
            for d in [Domain::Gold, Domain::Secp, Domain::Ed] {
                let value = d.sub(d.modulus(), [1, 0, 0, 0]);
                let expected: Vec<Value> = (0..64)
                    .map(|lane| if lane % 2 == 0 { value } else { [17, 0, 0, 0] })
                    .collect();
                let own: Vec<_> = (0..d.width())
                    .map(|bit| {
                        expected.iter().enumerate().fold(0, |v, (lane, x)| {
                            v | (((x[bit / 64] >> (bit % 64)) & 1) << lane)
                        })
                    })
                    .collect();
                // Three local XOR components, deliberately distinct from public constants.
                let share: Vec<_> = own
                    .iter()
                    .enumerate()
                    .map(|(bit, &v)| match party {
                        1 => v ^ (bit as u64).wrapping_mul(0x12345678),
                        3 => (bit as u64).wrapping_mul(0x12345678) ^ 0xabcdef,
                        _ => 0xabcdef,
                    })
                    .collect();
                let bits = engine.share(&share).unwrap();
                let field = engine.bits_to_field(&bits, d).unwrap();
                let roundtrip = engine.field_to_bits(&field, d).unwrap();
                assert_eq!(engine.open(&roundtrip).unwrap(), own);
                let inverse = engine.finverse(&field, d).unwrap();
                let product = engine.fmul(&inverse, &field, d).unwrap();
                let encoded = engine.field_to_bits(&product, d).unwrap();
                let opened = engine.open(&encoded).unwrap();
                assert_eq!(opened[0], u64::MAX);
                assert!(opened[1..].iter().all(|&x| x == 0));
            }
        });
    }
    #[test]
    fn malformed_authenticated_rounds_and_invalid_custody_are_rejected() {
        struct Altered;
        impl Transport for Altered {
            fn exchange_many(&mut self, out: Vec<Envelope>) -> Result<Vec<Envelope>, Error> {
                Ok(out
                    .iter()
                    .map(|m| Envelope {
                        sender: m.recipient,
                        recipient: m.sender,
                        sequence: m.sequence,
                        payload: m.payload.clone(),
                        tag: [0; 32],
                    })
                    .collect())
            }
        }
        let cfg = ThresholdConfig::new(2, 64, vec![0, 63]).unwrap();
        let mut state = State::new(cfg.clone(), 0, [9; 32], keys(&cfg, 0)).unwrap();
        assert_eq!(
            state.open_bits(&mut Altered, &[42]),
            Err(Error::Authentication(63))
        );
        assert_eq!(
            state.open_bits(&mut Altered, &[42]),
            Err(Error::MultiplicationCheck)
        );
        assert!(
            crate::CoZkCustodianShare::new_shamir(
                1,
                cfg.clone(),
                [0; 32],
                [0; 32],
                [0; 32],
                keys(&cfg, 0)
            )
            .is_err()
        );
        assert!(
            crate::CoZkCustodianShare::new_shamir(0, cfg, [0; 32], [0; 32], [0; 32], vec![])
                .is_err()
        );
        for parties in [0, 1, 65, usize::MAX] {
            assert!(
                crate::CoZkCustodianShare::new_additive(
                    0,
                    parties,
                    [0; 32],
                    [0; 32],
                    [0; 32],
                    vec![]
                )
                .is_err()
            );
        }
        assert!(
            crate::CoZkCustodianShare::new_additive(
                63,
                64,
                [0; 32],
                [0; 32],
                [0; 32],
                vec![[1; 32]; 63]
            )
            .is_ok()
        );
    }

    #[test]
    fn missing_preprocessing_and_bad_transport_poison_the_session() {
        struct Empty;
        impl Transport for Empty {}
        let cfg = ThresholdConfig::new(2, 2, vec![0, 1]).unwrap();
        let mut state = State::new(cfg.clone(), 0, [9; 32], keys(&cfg, 0)).unwrap();
        assert!(matches!(
            state.and(&mut Empty, &[(Bit([0, 0]), Bit([0, 0]))]),
            Err(Error::MissingPreprocessing)
        ));
        assert_eq!(
            state.open_bits(&mut Empty, &[0]),
            Err(Error::MultiplicationCheck)
        );
        let mut state = State::new(cfg.clone(), 0, [9; 32], keys(&cfg, 0)).unwrap();
        assert_eq!(
            state.open_bits(&mut Empty, &[0]),
            Err(Error::InvalidConfiguration)
        );
        assert_eq!(
            state.open_bits(&mut Empty, &[0]),
            Err(Error::MultiplicationCheck)
        );
    }
}
