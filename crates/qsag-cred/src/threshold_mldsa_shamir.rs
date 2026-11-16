//! Shamir key custody for threshold ML-DSA committees of up to 64 custodians.
//!
//! Replicated sharing ([`crate::rss_mpc`]) keeps one key component per
//! `(t - 1)`-subset of the committee and stops at sixteen custodians. Here every
//! custodian holds a single degree-`t - 1` Shamir share over `F_q` of `(s1, s2)`,
//! whatever `n` is. Signing is the protocol of [`crate::threshold_mldsa`], unchanged,
//! after a checked conversion of the quorum's Shamir shares
//! (`threshold_mldsa::shamir_session_key`).
//!
//! # Model
//! `n <= 64` custodians, privacy threshold `t`, `n >= 2t - 1`, at most `t - 1`
//! statically and maliciously corrupt, security with abort. A signing quorum has
//! `2t - 1 <= m <= 16` custodians, so `t <= 8`. This is an honest-majority-of-quorum
//! protocol: `t` custodians alone cannot sign, and no SPDZ preprocessing is used. The
//! release gate is the engine's batched multiplication check plus the share
//! conversion check, both passed before anything is opened.
//!
//! # Ceremony
//! 1. The first `2t - 1` custodians (the sampling committee,
//!    [`ThresholdMlDsaDkgConfig::shamir_committee`]) run the dealerless replicated
//!    key generation among themselves. Any `2t - 1` custodians have an honest
//!    majority, so the key has the exact FIPS 204 distribution and nobody knows it.
//! 2. All `n` custodians run [`threshold_mldsa_shamir_expand_party`]:
//!    * Every holder of a replicated component deals a degree-`t - 1` Shamir sharing
//!      of it to all `n` custodians. Each component has `t` holders, so at least one
//!      dealing of it is honest. All custodians also commit to a coin share.
//!    * The coin is opened. For every component and every holder but the lowest, each
//!      custodian broadcasts the coin-weighted combination (in the degree-6 extension)
//!      of its shares of `dealing - lowest holder's dealing`. Those must lie on a
//!      degree-`t - 1` polynomial that vanishes at zero. The differences are sharings
//!      of zero under fresh randomness, so opening them reveals nothing; if the check
//!      passes, the lowest holder's dealing shares the same component as the honest
//!      holder's, on a polynomial of the right degree (error at most `len / q^6`).
//!    * Each custodian's share is the sum of the lowest holders' dealings. As an
//!      end-to-end check every custodian broadcasts `A * s1_i + s2_i`; these lie on a
//!      degree-`t - 1` polynomial through the public `t`. The values are determined by
//!      `t` and any `t - 1` shares, so they reveal nothing either.
//!    * All custodians confirm the same transcript.
//!
//! A custodian that deviates can abort the ceremony. It cannot make the committee
//! hold shares of a different key, and it learns nothing beyond its own shares.

use crate::fips204_ntt::{
    MLDSA_N, MLDSA_Q, MlDsaLevel, Poly256, expand_a_ntt, fq_add, fq_mul, fq_sub, mat_vec_mul_ntt, pk_encode,
    power2round,
};
use crate::rss_mpc::{
    K_ZERO, Kx, MAX_MPC_PARTIES, MpcError, MpcTransport, Prss, RoundInbox, RoundInfo, RoundKind,
    Structure, k_add, k_base, k_mul, k_scale, pack, unpack,
};
use crate::threshold_mldsa::{
    PHASE_DKG_SHAMIR, ShamirShare, ThresholdMlDsaDkgConfig, ThresholdMlDsaError,
    ThresholdMlDsaSignerShare, ThresholdVerificationPack, check_parameters, flatten, flatten_key,
    ids_bytes, inv_ntt_all, lagrange_weights, sorted_distinct, to_polys,
};
use alloc::vec;
use alloc::vec::Vec;
use qsag_accel::ct::ct_eq_bytes;
use qsag_accel::keccak::cshake256_framed_32;
use qsag_core::wipe::SecretBuffer;

const SHARE_MAGIC: &[u8; 8] = b"QTMLDSS1";
const PACK_MAGIC: &[u8; 8] = b"QTMLDSP1";

const fn level_byte(level: MlDsaLevel) -> u8 {
    match level {
        MlDsaLevel::MlDsa44 => 44,
        MlDsaLevel::MlDsa65 => 65,
        MlDsaLevel::MlDsa87 => 87,
    }
}

impl ThresholdMlDsaDkgConfig {
    /// Checks the configuration for the Shamir ceremony and returns the sorted
    /// custodian list: `n <= 64`, `n >= 2t - 1`, and a signing quorum of `2t - 1`
    /// custodians must fit the replicated session engine.
    pub fn validate_shamir(&self) -> Result<Vec<u16>, ThresholdMlDsaError> {
        check_parameters(self.level, self.threshold, self.party_ids.len())?;
        let quorum = 2 * self.threshold - 1;
        if quorum > MAX_MPC_PARTIES {
            return Err(MpcError::UnsupportedStructure {
                parties: quorum,
                threshold: self.threshold,
            }
            .into());
        }
        sorted_distinct(&self.party_ids)
    }

    /// The replicated key-generation ceremony of the sampling committee: the first
    /// `2t - 1` custodians in ascending order, under a session bound to the whole
    /// committee. Run it with [`crate::threshold_mldsa_dkg_party`].
    pub fn shamir_committee(&self) -> Result<Self, ThresholdMlDsaError> {
        let ids = self.validate_shamir()?;
        Ok(Self {
            level: self.level,
            threshold: self.threshold,
            party_ids: ids[..2 * self.threshold - 1].to_vec(),
            session_id: cshake256_framed_32(
                b"QSAG.TMLDSA.SHAMIR.COMMITTEE.V1",
                &[&self.session_id, &ids_bytes(&ids)],
            ),
        })
    }
}

impl ThresholdVerificationPack {
    /// Canonical encoding of the public key-generation result.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(64 + self.pk_bytes.len() + 3 * MLDSA_N * self.t.len());
        out.extend_from_slice(PACK_MAGIC);
        out.push(level_byte(self.level));
        out.push(self.threshold as u8);
        out.push(self.party_ids.len() as u8);
        out.extend_from_slice(&ids_bytes(&self.party_ids));
        out.extend_from_slice(&self.rho);
        out.extend_from_slice(&self.pk_bytes);
        pack(&flatten(&self.t), &mut out);
        out
    }

    /// Decode and check internal consistency (`pk` must encode `(rho, t1)`).
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, ThresholdMlDsaError> {
        let malformed = ThresholdMlDsaError::ProtocolInvariantViolated;
        if bytes.len() < 11 || &bytes[..8] != PACK_MAGIC {
            return Err(malformed);
        }
        let level = match bytes[8] {
            44 => MlDsaLevel::MlDsa44,
            65 => MlDsaLevel::MlDsa65,
            87 => MlDsaLevel::MlDsa87,
            _ => return Err(ThresholdMlDsaError::UnsupportedLevel),
        };
        let params = level.params();
        let (threshold, parties) = (bytes[9] as usize, bytes[10] as usize);
        check_parameters(level, threshold, parties)?;
        let t_len = params.k * MLDSA_N;
        if bytes.len() != 11 + 2 * parties + 32 + params.pk_bytes + 3 * t_len {
            return Err(malformed);
        }
        let (ids, rest) = bytes[11..].split_at(2 * parties);
        let party_ids: Vec<u16> = ids
            .as_chunks::<2>()
            .0
            .iter()
            .map(|pair| u16::from_le_bytes(*pair))
            .collect();
        let (rho, rest) = rest.split_at(32);
        let (pk_bytes, t) = rest.split_at(params.pk_bytes);
        let pack = Self {
            level,
            threshold,
            party_ids,
            rho: rho.try_into().map_err(|_| malformed.clone())?,
            pk_bytes: pk_bytes.to_vec(),
            t: to_polys(&unpack(t, t_len).ok_or(malformed.clone())?),
        };
        pack.validate()?;
        Ok(pack)
    }

    /// Checks everything signing relies on. The fields are public, so a pack
    /// that did not come from [`Self::from_bytes`] or a ceremony is checked
    /// here before it is used: supported parameters, custodian identifiers in
    /// strictly ascending order, exactly `k` polynomials of `t` with every
    /// coefficient below `q`, and `pk_bytes` equal to the FIPS 204 encoding of
    /// `(rho, Power2Round(t).1)`.
    pub fn validate(&self) -> Result<(), ThresholdMlDsaError> {
        let malformed = ThresholdMlDsaError::ProtocolInvariantViolated;
        check_parameters(self.level, self.threshold, self.party_ids.len())?;
        if sorted_distinct(&self.party_ids)? != self.party_ids {
            return Err(malformed);
        }
        let params = self.level.params();
        if self.t.len() != params.k
            || self.pk_bytes.len() != params.pk_bytes
            || self
                .t
                .iter()
                .flat_map(|poly| &poly.coeffs)
                .any(|&coeff| coeff >= MLDSA_Q)
        {
            return Err(malformed);
        }
        if self.pk_bytes != encode_public_key(self) {
            return Err(malformed);
        }
        Ok(())
    }
}

fn encode_public_key(pack: &ThresholdVerificationPack) -> Vec<u8> {
    let t1: Vec<Poly256> = pack
        .t
        .iter()
        .map(|poly| {
            let mut high = Poly256::zero();
            for (out, &value) in high.coeffs.iter_mut().zip(&poly.coeffs) {
                *out = power2round(value).0;
            }
            high
        })
        .collect();
    pk_encode(&pack.level.params(), &pack.rho, &t1)
}

impl ThresholdMlDsaSignerShare {
    /// This custodian's Shamir share and attempt epoch, or `None` for a replicated
    /// share. The bytes are secret: store them encrypted and authenticated.
    pub fn to_shamir_bytes(&self) -> Option<Vec<u8>> {
        let share = self.shamir.as_ref()?;
        let mut out =
            Vec::with_capacity(18 + 3 * MLDSA_N * (share.s1_hat.len() + share.s2_hat.len()));
        out.extend_from_slice(SHARE_MAGIC);
        out.extend_from_slice(&self.party_id.to_le_bytes());
        out.extend_from_slice(&self.next_epoch.to_le_bytes());
        for poly in share.s1_hat.iter().chain(&share.s2_hat) {
            pack(&poly.coeffs, &mut out);
        }
        Some(out)
    }

    /// Restore a Shamir share against the independently pinned public result.
    pub fn from_shamir_bytes(
        bytes: &[u8],
        pack: ThresholdVerificationPack,
        expected_party: u16,
    ) -> Result<Self, ThresholdMlDsaError> {
        pack.validate()?;
        let params = pack.level.params();
        let split = params.ell * MLDSA_N;
        let len = split + params.k * MLDSA_N;
        if bytes.len() != 18 + 3 * len || &bytes[..8] != SHARE_MAGIC {
            return Err(ThresholdMlDsaError::ProtocolInvariantViolated);
        }
        let party_id = u16::from_le_bytes([bytes[8], bytes[9]]);
        if party_id != expected_party || !pack.party_ids.contains(&party_id) {
            return Err(ThresholdMlDsaError::DuplicateOrUnknownParty { party_id });
        }
        let next_epoch = u64::from_le_bytes(
            bytes[10..18]
                .try_into()
                .map_err(|_| ThresholdMlDsaError::ProtocolInvariantViolated)?,
        );
        let flat = SecretBuffer(
            unpack(&bytes[18..], len).ok_or(ThresholdMlDsaError::ProtocolInvariantViolated)?,
        );
        Ok(Self {
            party_id,
            pack,
            subsets: Vec::new(),
            shamir: Some(ShamirShare {
                s1_hat: to_polys(&flat[..split]),
                s2_hat: to_polys(&flat[split..]),
            }),
            next_epoch,
        })
    }
}

fn hash_all(domain: &[u8], context: &[u8; 32], messages: &[Vec<u8>]) -> [u8; 32] {
    let mut parts: Vec<&[u8]> = vec![context];
    let lengths: Vec<[u8; 8]> = messages
        .iter()
        .map(|message| (message.len() as u64).to_le_bytes())
        .collect();
    for (message, length) in messages.iter().zip(&lengths) {
        parts.push(length);
        parts.push(message);
    }
    cshake256_framed_32(domain, &parts)
}

fn pack_k(values: &[Kx], out: &mut Vec<u8>) {
    for value in values {
        pack(value, out);
    }
}

/// `sum_i weights[i] * values[i]` in the extension field.
fn k_combine(weights: &[u32], values: &[Kx]) -> Kx {
    weights
        .iter()
        .zip(values)
        .fold(K_ZERO, |acc, (&weight, value)| {
            k_add(&acc, &k_scale(value, weight))
        })
}

/// Runs one custodian's side of the expansion of the sampling committee's key into
/// Shamir shares for all `n` custodians (see the module header).
///
/// Transport positions follow the ascending order of `config.party_ids`. The first
/// `2t - 1` custodians pass the share they obtained from the committee ceremony
/// ([`ThresholdMlDsaDkgConfig::shamir_committee`]); it is consumed. Everyone else
/// passes `None`. `entropy` must be fresh secret randomness.
pub fn threshold_mldsa_shamir_expand_party<T: MpcTransport>(
    config: &ThresholdMlDsaDkgConfig,
    party_id: u16,
    committee_share: Option<ThresholdMlDsaSignerShare>,
    entropy: &[u8; 32],
    net: &mut T,
) -> Result<ThresholdMlDsaSignerShare, ThresholdMlDsaError> {
    let ids = config.validate_shamir()?;
    let (n, t) = (ids.len(), config.threshold);
    let members = 2 * t - 1;
    let me = ids
        .iter()
        .position(|&id| id == party_id)
        .ok_or(ThresholdMlDsaError::DuplicateOrUnknownParty { party_id })?;
    let params = config.level.params();
    let structure = Structure::new(members, t)?;
    let subsets = structure.subsets.len();
    let split = params.ell * MLDSA_N;
    let len = split + params.k * MLDSA_N;
    let context = cshake256_framed_32(
        b"QSAG.TMLDSA.SHAMIR.CTX.V1",
        &[
            &config.session_id,
            &ids_bytes(&ids),
            &[t as u8, params.k as u8, params.ell as u8],
        ],
    );
    // The committee is the first `2t - 1` sorted custodians, so a committee position
    // is also a transport position.
    let committee = config.shamir_committee()?;
    match &committee_share {
        Some(share)
            if me < members
                && share.shamir.is_none()
                && share.party_id == party_id
                && share.pack.level == config.level
                && share.pack.threshold == t
                && share.pack.party_ids == committee.party_ids
                && share
                    .subsets
                    .iter()
                    .map(|subset| &subset.holders)
                    .eq(structure
                        .subsets_of(me)
                        .iter()
                        .map(|&s| &structure.subsets[s])) => {}
        None if me >= members => {}
        _ => return Err(ThresholdMlDsaError::WrongKeyShareKind),
    }
    let points: Vec<u32> = (1..=n as u32).collect();

    let mut index = 0u64;
    let mut round = |net: &mut T, kind: RoundKind, private: Vec<Vec<u8>>, broadcast: Vec<u8>| {
        let info = RoundInfo {
            index,
            phase: PHASE_DKG_SHAMIR,
            kind,
        };
        index += 1;
        let inbox: RoundInbox = net
            .exchange(info, private, broadcast)
            .map_err(|_| MpcError::Transport)?;
        if inbox.private.len() != n || inbox.broadcast.len() != n {
            return Err(MpcError::Transport);
        }
        Ok::<_, MpcError>(inbox)
    };

    // Round 1: dealings of every component this custodian holds, the public record,
    // and a commitment to a coin share.
    let seed = SecretBuffer(cshake256_framed_32(
        b"QSAG.TMLDSA.SHAMIR.COIN.SEED.V1",
        &[entropy, &context, &(me as u32).to_le_bytes()],
    ));
    let commitment = |party: usize, seed: &[u8]| {
        cshake256_framed_32(
            b"QSAG.TMLDSA.SHAMIR.COIN.COMMIT.V1",
            &[&context, &(party as u32).to_le_bytes(), seed],
        )
    };
    let mut broadcast = commitment(me, &seed[..]).to_vec();
    let mut private = vec![Vec::new(); n];
    // dealt[subset][holder rank] is this custodian's share of that holder's dealing.
    let mut dealt: SecretBuffer<Vec<Vec<Vec<u32>>>> =
        SecretBuffer(vec![vec![Vec::new(); t]; subsets]);
    let mut record = Vec::new();
    if let Some(share) = &committee_share {
        record.extend_from_slice(&share.pack.rho);
        record.extend_from_slice(&share.pack.pk_bytes);
        pack(&flatten(&share.pack.t), &mut record);
        broadcast.extend_from_slice(&record);
        let custody = share.custody_digest();
        for (component, &subset) in share.subsets.iter().zip(&structure.subsets_of(me)) {
            let secret = flatten_key(&component.s1_hat, &component.s2_hat);
            let key = SecretBuffer(cshake256_framed_32(
                b"QSAG.TMLDSA.SHAMIR.DEAL.V1",
                &[
                    entropy,
                    &context,
                    &custody[..],
                    &(subset as u32).to_le_bytes(),
                ],
            ));
            let mut stream = Prss::new(&key);
            let coefficients: SecretBuffer<Vec<Vec<u32>>> =
                SecretBuffer((1..t).map(|_| stream.elements(len)).collect());
            let rank = structure.subsets[subset]
                .iter()
                .position(|&holder| holder == me)
                .ok_or(ThresholdMlDsaError::ProtocolInvariantViolated)?;
            for (recipient, &point) in points.iter().enumerate() {
                let mut values = SecretBuffer(vec![0u32; len]);
                for (k, value) in values.iter_mut().enumerate() {
                    // Horner from the highest coefficient down to the secret.
                    let mut acc = 0u32;
                    for coefficient in coefficients.iter().rev() {
                        acc = fq_mul(fq_add(acc, coefficient[k]), point);
                    }
                    *value = fq_add(acc, secret[k]);
                }
                if recipient == me {
                    dealt[subset][rank] = values.into_inner();
                } else {
                    pack(&values, &mut private[recipient]);
                }
            }
        }
    }
    let first = round(net, RoundKind::Input, private, broadcast)?;
    for dealer in 0..members {
        let held = structure.subsets_of(dealer);
        let malformed = MpcError::MalformedMessage { from: dealer };
        if dealer != me {
            let message = &first.private[dealer];
            if message.len() != held.len() * len * 3 {
                return Err(malformed.into());
            }
            for (chunk, &subset) in message.chunks_exact(len * 3).zip(&held) {
                let rank = structure.subsets[subset]
                    .iter()
                    .position(|&holder| holder == dealer)
                    .ok_or(malformed)?;
                dealt[subset][rank] = unpack(chunk, len).ok_or(malformed)?;
            }
        }
    }
    // All committee members must publish the same record.
    let published = first.broadcast[0].get(32..).unwrap_or_default();
    for (party, message) in first.broadcast.iter().enumerate() {
        let expected = if party < members { published } else { &[][..] };
        if message.get(32..) != Some(expected) {
            return Err(MpcError::ConfirmationMismatch { party }.into());
        }
    }
    let t_len = params.k * MLDSA_N;
    if published.len() != 32 + params.pk_bytes + 3 * t_len || (me < members && published != record)
    {
        return Err(ThresholdMlDsaError::ShamirDealingInconsistent);
    }
    let pack_out = ThresholdVerificationPack {
        level: config.level,
        threshold: t,
        party_ids: ids.clone(),
        rho: published[..32]
            .try_into()
            .map_err(|_| ThresholdMlDsaError::ShamirDealingInconsistent)?,
        pk_bytes: published[32..32 + params.pk_bytes].to_vec(),
        t: to_polys(
            &unpack(&published[32 + params.pk_bytes..], t_len)
                .ok_or(ThresholdMlDsaError::ShamirDealingInconsistent)?,
        ),
    };
    if pack_out.pk_bytes != encode_public_key(&pack_out) {
        return Err(ThresholdMlDsaError::ShamirDealingInconsistent);
    }

    // Round 2: open the coin. The dealings were fixed before any seed was revealed.
    let second = round(net, RoundKind::Open, vec![Vec::new(); n], seed.to_vec())?;
    for (party, (opened, committed)) in second.broadcast.iter().zip(&first.broadcast).enumerate() {
        if opened.len() != 32 || !ct_eq_bytes(&commitment(party, opened), &committed[..32]) {
            return Err(MpcError::ConfirmationMismatch { party }.into());
        }
    }
    let coin_key = cshake256_framed_32(
        b"QSAG.TMLDSA.SHAMIR.COIN.V1",
        &[
            &hash_all(b"QSAG.TMLDSA.SHAMIR.R1.V1", &context, &first.broadcast),
            &hash_all(b"QSAG.TMLDSA.SHAMIR.R2.V1", &context, &second.broadcast),
        ],
    );
    let gamma: Kx = core::array::from_fn({
        let draws = Prss::new(&coin_key).elements(6);
        move |i| draws[i]
    });

    // Round 3: compressed differences against the lowest holder's dealing, and this
    // custodian's share of the public `t`.
    let mut differences = Vec::with_capacity(subsets * (t - 1));
    let mut mine = SecretBuffer(vec![0u32; len]);
    for holders in dealt.iter() {
        for dealing in &holders[1..] {
            let mut acc = K_ZERO;
            for (&value, &base) in dealing.iter().zip(&holders[0]) {
                acc = k_add(&k_mul(&acc, &gamma), &k_base(fq_sub(value, base)));
            }
            differences.push(acc);
        }
        for (slot, &value) in mine.iter_mut().zip(&holders[0]) {
            *slot = fq_add(*slot, value);
        }
    }
    let share = ShamirShare {
        s1_hat: to_polys(&mine[..split]),
        s2_hat: to_polys(&mine[split..]),
    };
    let a_hat = expand_a_ntt(&params, &pack_out.rho);
    let public_share: Vec<Poly256> = inv_ntt_all(mat_vec_mul_ntt(&a_hat, &share.s1_hat))
        .iter()
        .zip(inv_ntt_all(share.s2_hat.clone()))
        .map(|(product, error)| product.add(&error))
        .collect();
    let mut broadcast = Vec::with_capacity(18 * differences.len() + 3 * t_len);
    pack_k(&differences, &mut broadcast);
    pack(&flatten(&public_share), &mut broadcast);
    let third = round(net, RoundKind::Open, vec![Vec::new(); n], broadcast)?;
    let pairs = subsets * (t - 1);
    let mut columns: Vec<Vec<u32>> = Vec::with_capacity(n);
    for (party, message) in third.broadcast.iter().enumerate() {
        let malformed = MpcError::MalformedMessage { from: party };
        if message.len() != 18 * pairs + 3 * t_len {
            return Err(malformed.into());
        }
        columns.push(unpack(message, 6 * pairs + t_len).ok_or(malformed)?);
    }
    // Differences: degree below `t`, vanishing at zero. Interpolate through zero and
    // the first `t - 1` custodians and compare every other custodian.
    let mut nodes = vec![0u32];
    nodes.extend_from_slice(&points[..t - 1]);
    for (target, column) in columns.iter().enumerate().skip(t - 1) {
        let weights = lagrange_weights(&nodes, points[target]);
        for pair in 0..pairs {
            let at = |party: usize| -> Kx {
                core::array::from_fn(|limb| columns[party][6 * pair + limb])
            };
            let known: Vec<Kx> = (0..t - 1).map(at).collect();
            if k_combine(&weights[1..], &known)[..] != column[6 * pair..6 * pair + 6] {
                return Err(ThresholdMlDsaError::ShamirDealingInconsistent);
            }
        }
    }
    // Shares of `t`: degree below `t` through the public value at zero.
    let public_t = flatten(&pack_out.t);
    for target in core::iter::once(None).chain((t..n).map(Some)) {
        let weights = lagrange_weights(&points[..t], target.map_or(0, |party| points[party]));
        for (k, &expected) in public_t.iter().enumerate() {
            let at = 6 * pairs + k;
            let value = (0..t).fold(0u32, |acc, party| {
                fq_add(acc, fq_mul(weights[party], columns[party][at]))
            });
            if value != target.map_or(expected, |party| columns[party][at]) {
                return Err(ThresholdMlDsaError::ShamirDealingInconsistent);
            }
        }
    }

    // Round 4: everyone accepted the same transcript.
    let confirmation = cshake256_framed_32(
        b"QSAG.TMLDSA.SHAMIR.CONFIRM.V1",
        &[
            &context,
            &pack_out.pk_bytes,
            &hash_all(b"QSAG.TMLDSA.SHAMIR.R3.V1", &context, &third.broadcast),
        ],
    );
    let fourth = round(
        net,
        RoundKind::Confirm,
        vec![Vec::new(); n],
        confirmation.to_vec(),
    )?;
    if let Some(party) = fourth
        .broadcast
        .iter()
        .position(|message| message.as_slice() != confirmation)
    {
        return Err(MpcError::ConfirmationMismatch { party }.into());
    }
    Ok(ThresholdMlDsaSignerShare {
        party_id,
        pack: pack_out,
        subsets: Vec::new(),
        shamir: Some(share),
        next_epoch: 0,
    })
}
