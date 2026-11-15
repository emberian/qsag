//! Per-party committed SPDZ zero-test for scalar openings.
//! Requires authenticated reliable broadcast: every honest party must freeze the same
//! ordered commitment transcript before any MAC residual is opened. Transport and
//! persistent cross-process family quarantine are the caller's responsibility.
//! Opening masks come from the dealerless pairwise zero-sharing below.
//! Public callers can open only coefficients of the already-public relation A*s1+s2.
//! Arbitrary short-secret projections are not an authorized API.
use super::*;
use crate::seeds::CustodianSeeds;
use crate::zero_gate::{CommittedZeroGates, peer_transcript};
use qsag_accel::ct::ct_eq_bytes;
use qsag_accel::keccak::commit_mpc_broadcast;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HdEvalCommitment {
    pub party_id: u16,
    pub digest: [u8; 32],
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HdEvalShareOpening {
    pub party_id: u16,
    pub value: u32,
    pub salt: [u8; 32],
}
/// Committed MAC residuals. Available only after all MAC commitments are frozen.
/// A failed check can disclose the current MAC key; retire the entire family.
pub struct HdEvalMacOpening {
    pub party_id: u16,
    pub tags: [u32; SPDZ_LANES],
    pub salt: [u8; 32],
}

struct EvalState<'a> {
    share: &'a mut LinearModulePartyShare,
    session: [u8; 32],
    roster: Vec<(u16, u32)>,
    value: u32,
    gamma: [u32; SPDZ_LANES],
    alpha: [u32; SPDZ_LANES],
    value_salt: [u8; 32],
    mac_salt: [u8; 32],
    value_commitments: Vec<HdEvalCommitment>,
    mac_commitments: Vec<HdEvalCommitment>,
    mac_digest: [u8; 32],
    /// Verified custody of the MAC residuals from the moment they exist.
    zero_test: Option<CommittedZeroGates>,
    expected_value: Option<u32>,
    opened_value: Option<u32>,
    complete: bool,
    disclosure_started: core::cell::Cell<bool>,
}
impl EvalState<'_> {
    fn disclosure_authorized(&self) -> bool {
        if self.share.poisoned.load(Ordering::Acquire) {
            return false;
        }
        if let Some(journal) = &self.share.poison_journal {
            if self.disclosure_started.get() {
                journal.disclosure_active(self.session).unwrap_or(false)
            } else {
                !journal.is_poisoned().unwrap_or(true)
            }
        } else {
            self.share.testing_poison_journal
        }
    }
}
impl Drop for EvalState<'_> {
    fn drop(&mut self) {
        wipe(core::slice::from_mut(&mut self.value));
        wipe(&mut self.gamma);
        wipe(&mut self.alpha);
        wipe(&mut self.value_salt);
        wipe(&mut self.mac_salt);
        if !self.complete {
            self.share.poison();
        }
    }
}

pub struct HdThresholdEvalRound1Commit<'a>(EvalState<'a>);
pub struct HdThresholdEvalRound2OpenShareAndCommitMac<'a>(EvalState<'a>);
/// A party can release its residual only after freezing the complete MAC commitment set.
/// Earlier phases have no MAC-opening accessor.
/// ```compile_fail
/// use qsag_hd::linear_module::HdThresholdEvalRound2OpenShareAndCommitMac;
/// fn leak(s: &mut HdThresholdEvalRound2OpenShareAndCommitMac<'_>) { let _ = s.mac_opening(); }
/// ```
pub struct HdThresholdEvalRound3VerifyMac<'a>(EvalState<'a>);

fn tags_bytes(tags: &[u32; SPDZ_LANES]) -> [u8; SPDZ_LANES * 4] {
    let mut bytes = [0; SPDZ_LANES * 4];
    for (chunk, tag) in bytes.as_chunks_mut::<4>().0.iter_mut().zip(tags) {
        chunk.copy_from_slice(&tag.to_be_bytes());
    }
    bytes
}
fn freeze_commitments(
    state: &EvalState<'_>,
    messages: &[HdEvalCommitment],
    own: &HdEvalCommitment,
) -> Result<(), HdError> {
    if messages.len() != state.roster.len()
        || !messages.contains(own)
        || state
            .roster
            .iter()
            .any(|(id, _)| messages.iter().filter(|m| m.party_id == *id).count() != 1)
    {
        return Err(HdError::MacCheckFailed);
    }
    Ok(())
}
fn linear_value(
    form: &[RingPoly; MODULE_SECRET_L],
    values: &[SecretRingPoly; MODULE_SECRET_L],
) -> u32 {
    form.iter().zip(values).fold(0, |sum, (weights, poly)| {
        weights
            .coeffs
            .iter()
            .zip(&poly.expose().coeffs)
            .fold(sum, |acc, (&a, &b)| mod_q_add(acc, mod_q_mul(a, b)))
    })
}

/// Closed projection allowlist. Each result is already in the enrolled public key.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AuthorizedHdProjection {
    PublicRelationCoefficient { row: usize, coefficient: usize },
}
impl AuthorizedHdProjection {
    fn form(self, expected: &LinearModuleXPub) -> Result<[RingPoly; MODULE_SECRET_L], HdError> {
        let Self::PublicRelationCoefficient { row, coefficient } = self;
        if row >= MODULE_K || coefficient >= MODULE_N || expected.matrix.seed != expected.seed_a {
            return Err(HdError::InvalidThresholdParameters);
        }
        let mut form = core::array::from_fn(|_| RingPoly::zero());
        for (j, weights) in form.iter_mut().take(MODULE_L).enumerate() {
            let a = inverse(expected.matrix.ntt[row][j].clone());
            for (i, weight) in weights.coeffs.iter_mut().enumerate() {
                *weight = if i <= coefficient {
                    a.coeffs[coefficient - i]
                } else {
                    mod_q_sub(0, a.coeffs[MODULE_N + coefficient - i])
                };
            }
        }
        form[MODULE_L + row].coeffs[coefficient] = 1;
        Ok(form)
    }
    /// Migration adapter for old callers. Rejects every form not exactly one of
    /// the already-public relation coefficients, including radix-packed secrets.
    pub fn from_form(
        expected: &LinearModuleXPub,
        form: &[RingPoly; MODULE_SECRET_L],
    ) -> Result<Self, HdError> {
        let mut selected = None;
        for (row, poly) in form[MODULE_L..].iter().enumerate() {
            for (coefficient, &value) in poly.coeffs.iter().enumerate() {
                if value != 0 {
                    if value != 1 || selected.is_some() {
                        return Err(HdError::UnauthorizedProjection);
                    }
                    selected = Some(Self::PublicRelationCoefficient { row, coefficient });
                }
            }
        }
        let projection = selected.ok_or(HdError::UnauthorizedProjection)?;
        if projection.form(expected)? != *form {
            return Err(HdError::UnauthorizedProjection);
        }
        Ok(projection)
    }
}

impl<'a> HdThresholdEvalRound1Commit<'a> {
    /// Opens only an explicitly allowed coefficient of the public relation.
    pub fn begin(
        share: &'a mut LinearModulePartyShare,
        expected: &LinearModuleXPub,
        roster: &[(u16, u32)],
        projection: AuthorizedHdProjection,
        session_id: [u8; 32],
        mask: OpeningMask,
        private_entropy: [u8; 32],
    ) -> Result<Self, HdError> {
        let AuthorizedHdProjection::PublicRelationCoefficient { row, coefficient } = projection;
        let form = projection.form(expected)?;
        if mask.projection != Some(projection) {
            return Err(HdError::InvalidThresholdParameters);
        }
        Self::begin_inner_with_expected(
            share,
            expected,
            roster,
            &form,
            Some(expected.t_vec[row].coeffs[coefficient]),
            session_id,
            mask,
            private_entropy,
        )
    }

    #[cfg(test)]
    fn begin_inner(
        share: &'a mut LinearModulePartyShare,
        expected: &LinearModuleXPub,
        roster: &[(u16, u32)],
        form: &[RingPoly; MODULE_SECRET_L],
        session_id: [u8; 32],
        mask: OpeningMask,
        private_entropy: [u8; 32],
    ) -> Result<Self, HdError> {
        let inferred_expected = AuthorizedHdProjection::from_form(expected, form).ok().map(
            |AuthorizedHdProjection::PublicRelationCoefficient { row, coefficient }| {
                expected.t_vec[row].coeffs[coefficient]
            },
        );
        Self::begin_inner_with_expected(
            share,
            expected,
            roster,
            form,
            inferred_expected,
            session_id,
            mask,
            private_entropy,
        )
    }

    /// Consumes an exclusive borrow of exactly one custodian. Fresh private entropy
    /// salts the commitments; it must never be a coordinator-supplied public coin.
    /// The form is a coefficient-wise scalar inner product across all eight polynomials.
    #[allow(clippy::too_many_arguments)]
    fn begin_inner_with_expected(
        share: &'a mut LinearModulePartyShare,
        expected: &LinearModuleXPub,
        roster: &[(u16, u32)],
        form: &[RingPoly; MODULE_SECRET_L],
        expected_value: Option<u32>,
        session_id: [u8; 32],
        mask: OpeningMask,
        mut private_entropy: [u8; 32],
    ) -> Result<Self, HdError> {
        let entropy = RedactedSecret::new(private_entropy);
        wipe(&mut private_entropy);
        share.require_poison_journal()?;
        let (threshold, own_x) = match share.scheme {
            ShareScheme::Shamir {
                threshold,
                eval_point,
            } => (threshold, eval_point),
            ShareScheme::Additive { num_parties } => {
                if roster != share.committee || roster.len() != usize::from(num_parties) {
                    return Err(HdError::InvalidThresholdParameters);
                }
                (
                    num_parties,
                    share
                        .committee
                        .iter()
                        .find(|entry| entry.0 == share.party_id)
                        .ok_or(HdError::InvalidThresholdParameters)?
                        .1,
                )
            }
        };
        if share.is_poisoned()
            || (share.hardened && expected.chain_code.is_some())
            || threshold == 0
            || roster.len() < usize::from(threshold)
            || share.seed_a != expected.seed_a
            || share.t_vec != expected.t_vec
            || share.depth_used != expected.depth_used
            || share.max_depth != expected.max_depth
            || expected
                .chain_code
                .is_some_and(|cc| share.chain_code.expose() != &cc)
            || !roster.contains(&(share.party_id, own_x))
            || roster.windows(2).any(|w| w[0].0 >= w[1].0)
            || roster.iter().any(|entry| !share.committee.contains(entry))
            || form.iter().any(|p| p.coeffs.iter().any(|&c| c >= MODULE_Q))
        {
            return Err(HdError::InvalidThresholdParameters);
        }
        if mask.party_id != share.party_id || mask.roster != roster || mask.session != session_id {
            return Err(HdError::InvalidThresholdParameters);
        }
        share.burn_query()?;
        let xs: Vec<_> = roster.iter().map(|entry| entry.1).collect();
        validate_shamir_eval_points(&xs)?;
        let lambda = match share.scheme {
            ShareScheme::Shamir { .. } => interpolation_weight(&xs, own_x),
            ShareScheme::Additive { .. } => 1,
        };
        let value = mod_q_add(
            mod_q_mul(lambda, linear_value(form, &share.s_shares)),
            mask.value,
        );
        let gamma = core::array::from_fn(|lane| {
            mod_q_mul(lambda, linear_value(form, &share.spdz_macs[lane]))
        });
        let alpha = core::array::from_fn(|lane| mod_q_mul(lambda, share.spdz_alpha_shares[lane]));
        let mut context = Vec::new();
        context.extend_from_slice(&hash_t_vec(&expected.seed_a, &expected.t_vec));
        context.extend_from_slice(&expected.depth_used.to_be_bytes());
        context.extend_from_slice(&expected.max_depth.to_be_bytes());
        context.push(u8::from(expected.chain_code.is_some()));
        if let Some(cc) = expected.chain_code {
            context.extend_from_slice(&cc);
        }
        context.push(u8::from(matches!(
            share.scheme,
            ShareScheme::Additive { .. }
        )));
        context.extend_from_slice(&threshold.to_be_bytes());
        for &(id, x) in roster {
            context.extend_from_slice(&id.to_be_bytes());
            context.extend_from_slice(&x.to_be_bytes());
        }
        for poly in form {
            context.extend_from_slice(&poly.to_bytes());
        }
        let session = cshake256_framed_32(b"QSAG.HD.EVAL.CONTEXT.V2", &[&session_id, &context]);
        let value_salt =
            cshake256_framed_32(b"QSAG.HD.EVAL.VALUE_SALT.V1", &[entropy.expose(), &session]);
        let mac_salt =
            cshake256_framed_32(b"QSAG.HD.EVAL.MAC_SALT.V1", &[entropy.expose(), &session]);
        Ok(Self(EvalState {
            share,
            session,
            roster: roster.to_vec(),
            value,
            gamma,
            alpha,
            value_salt,
            mac_salt,
            value_commitments: Vec::new(),
            mac_commitments: Vec::new(),
            mac_digest: [0; 32],
            zero_test: None,
            expected_value,
            opened_value: None,
            complete: false,
            disclosure_started: core::cell::Cell::new(false),
        }))
    }
    pub fn commitment(&self) -> HdEvalCommitment {
        HdEvalCommitment {
            party_id: self.0.share.party_id,
            digest: commit_mpc_broadcast(
                &self.0.session,
                1,
                self.0.share.party_id,
                &self.0.value.to_be_bytes(),
                &self.0.value_salt,
            ),
        }
    }
    pub fn freeze(
        mut self,
        commitments: &[HdEvalCommitment],
    ) -> Result<HdThresholdEvalRound2OpenShareAndCommitMac<'a>, HdError> {
        freeze_commitments(&self.0, commitments, &self.commitment())?;
        self.0.value_commitments = commitments.to_vec();
        Ok(HdThresholdEvalRound2OpenShareAndCommitMac(self.0))
    }
}
impl<'a> HdThresholdEvalRound2OpenShareAndCommitMac<'a> {
    pub fn share_opening(&self) -> HdEvalShareOpening {
        HdEvalShareOpening {
            party_id: self.0.share.party_id,
            value: self.0.value,
            salt: self.0.value_salt,
        }
    }
    /// Checks all value commitments before producing a MAC commitment. This is
    /// single-use, including on failure; an error poisons the owning share immediately.
    pub fn commit_mac(
        &mut self,
        openings: &[HdEvalShareOpening],
    ) -> Result<HdEvalCommitment, HdError> {
        let result = self.commit_mac_inner(openings);
        if result.is_err() {
            self.0.share.poison();
        }
        result
    }
    fn commit_mac_inner(
        &mut self,
        openings: &[HdEvalShareOpening],
    ) -> Result<HdEvalCommitment, HdError> {
        if self.0.share.is_poisoned()
            || self.0.opened_value.is_some()
            || openings.len() != self.0.roster.len()
        {
            return Err(HdError::MacCheckFailed);
        }
        let mut value = 0;
        for expected in &self.0.value_commitments {
            let mut found = openings.iter().filter(|m| m.party_id == expected.party_id);
            let opening = found.next().ok_or(HdError::MacCheckFailed)?;
            if found.next().is_some() || opening.value >= MODULE_Q {
                return Err(HdError::MacCheckFailed);
            }
            let actual = commit_mpc_broadcast(
                &self.0.session,
                1,
                opening.party_id,
                &opening.value.to_be_bytes(),
                &opening.salt,
            );
            if !ct_eq_bytes(&actual, &expected.digest) {
                return Err(HdError::MacCheckFailed);
            }
            value = mod_q_add(value, opening.value);
        }
        // Check reconstructed scalar against the expected public coefficient BEFORE computing,
        // committing, or releasing any of the 7 SPDZ MAC tags, preventing a wrong-opening abort
        // from disclosing `alpha[0..7]`!
        if let Some(expected_val) = self.0.expected_value
            && value != expected_val
        {
            return Err(HdError::MacCheckFailed);
        }
        let mut tags: [u32; SPDZ_LANES] = core::array::from_fn(|lane| {
            mod_q_sub(self.0.gamma[lane], mod_q_mul(self.0.alpha[lane], value))
        });
        self.0.mac_digest = commit_mpc_broadcast(
            &self.0.session,
            2,
            self.0.share.party_id,
            &tags_bytes(&tags),
            &self.0.mac_salt,
        );
        self.0.zero_test = Some(CommittedZeroGates::hold(
            self.0.session,
            MODULE_Q,
            &mut tags,
        ));
        self.0.opened_value = Some(value);
        Ok(self.mac_commitment())
    }
    fn mac_commitment(&self) -> HdEvalCommitment {
        HdEvalCommitment {
            party_id: self.0.share.party_id,
            digest: self.0.mac_digest,
        }
    }
    pub fn freeze_mac(
        mut self,
        commitments: &[HdEvalCommitment],
    ) -> Result<HdThresholdEvalRound3VerifyMac<'a>, HdError> {
        if self.0.share.is_poisoned() || self.0.opened_value.is_none() {
            return Err(HdError::MacCheckFailed);
        }
        freeze_commitments(&self.0, commitments, &self.mac_commitment())?;
        let peers = peer_transcript(
            &self.0.session,
            self.0.share.party_id,
            commitments.iter().map(|c| (c.party_id, c.digest)),
        );
        self.0
            .zero_test
            .as_mut()
            .ok_or(HdError::MacCheckFailed)?
            .freeze(peers)?;
        self.0.mac_commitments = commitments.to_vec();
        Ok(HdThresholdEvalRound3VerifyMac(self.0))
    }
}
impl HdThresholdEvalRound3VerifyMac<'_> {
    /// Broadcast only after agreement on the frozen commitment transcript.
    /// This message may leak alpha on failure; no further family operations may
    /// proceed until every participating custodian has accepted the zero-test.
    pub fn mac_opening(&mut self) -> Result<HdEvalMacOpening, HdError> {
        if !self.0.disclosure_authorized()
            || self
                .0
                .expected_value
                .is_some_and(|exp| self.0.opened_value != Some(exp))
        {
            return Err(HdError::MacCheckFailed);
        }
        if !self.0.disclosure_started.get() {
            if let Some(journal) = &self.0.share.poison_journal {
                journal
                    .begin_disclosure(self.0.session)
                    .map_err(|_| HdError::MacCheckFailed)?;
            }
            self.0.disclosure_started.set(true);
        }
        let residuals = self
            .0
            .zero_test
            .as_mut()
            .ok_or(HdError::MacCheckFailed)?
            .open()?;
        Ok(HdEvalMacOpening {
            party_id: self.0.share.party_id,
            tags: core::array::from_fn(|lane| residuals[lane]),
            salt: self.0.mac_salt,
        })
    }
    /// Only this transition releases an authenticated scalar result. Failure or
    /// abandoning any phase wipes and poisons this custodian's key material.
    pub fn verify(mut self, openings: &[HdEvalMacOpening]) -> Result<u32, HdError> {
        if !self.0.disclosure_authorized() || openings.len() != self.0.roster.len() {
            return Err(HdError::MacCheckFailed);
        }
        let own = self.0.share.party_id;
        let mut peer_sums = [0; SPDZ_LANES];
        let mut recomputed = Vec::with_capacity(openings.len());
        for expected in &self.0.mac_commitments {
            let mut found = openings.iter().filter(|m| m.party_id == expected.party_id);
            let opening = found.next().ok_or(HdError::MacCheckFailed)?;
            if found.next().is_some() || opening.tags.iter().any(|&x| x >= MODULE_Q) {
                return Err(HdError::MacCheckFailed);
            }
            let actual = commit_mpc_broadcast(
                &self.0.session,
                2,
                opening.party_id,
                &tags_bytes(&opening.tags),
                &opening.salt,
            );
            if opening.party_id == own {
                // The local residual never re-enters from the network.
                if !ct_eq_bytes(&actual, &self.0.mac_digest) {
                    return Err(HdError::MacCheckFailed);
                }
                continue;
            }
            recomputed.push((opening.party_id, actual));
            for (sum, &tag) in peer_sums.iter_mut().zip(&opening.tags) {
                *sum = mod_q_add(*sum, tag);
            }
        }
        let peers = peer_transcript(&self.0.session, own, recomputed.into_iter());
        let accepted = self
            .0
            .zero_test
            .as_mut()
            .ok_or(HdError::MacCheckFailed)
            .and_then(|gates| gates.verify(peers, &peer_sums));
        wipe(&mut peer_sums);
        accepted?;
        let value = self.0.opened_value.ok_or(HdError::MacCheckFailed)?;
        if self.0.disclosure_started.get()
            && let Some(journal) = &self.0.share.poison_journal
        {
            journal
                .complete_disclosure(self.0.session)
                .map_err(|_| HdError::MacCheckFailed)?;
        }
        self.0.complete = true;
        Ok(value)
    }
}

impl Drop for HdEvalMacOpening {
    fn drop(&mut self) {
        wipe(&mut self.tags);
        wipe(&mut self.salt);
    }
}

/// Single-use additive zero-share for one opening. No Clone or Debug.
pub struct OpeningMask {
    party_id: u16,
    roster: Vec<(u16, u32)>,
    session: [u8; 32],
    projection: Option<AuthorizedHdProjection>,
    value: u32,
}
impl OpeningMask {
    #[cfg(test)]
    pub(crate) fn test_value(&self) -> u32 {
        self.value
    }
}
impl Drop for OpeningMask {
    fn drop(&mut self) {
        wipe(core::slice::from_mut(&mut self.value));
    }
}

/// Dealerless opening mask: this custodian's share of a pseudorandom additive
/// sharing of zero among `roster`, derived locally from the subset seeds.
///
/// For every other roster member the custodian adds (lower committee position) or
/// subtracts (higher position) a PRF output under their pairwise key, bound to the
/// session, roster and projection. The shares sum to zero by construction, whatever
/// a corrupt custodian does with its own. Any coalition of at most `t - 1`
/// custodians misses the pairwise key of every pair of honest roster members, so
/// the honest masks are jointly pseudorandom subject only to their sum. A mask is
/// accepted by `begin` only for the exact projection it was derived for; deriving
/// it twice for the same `(session, roster, projection)` repeats the same broadcast
/// and reveals nothing further. No private message and no dealer is involved.
pub fn dealerless_opening_mask(
    seeds: &CustodianSeeds,
    roster: &[(u16, u32)],
    session: [u8; 32],
    projection: AuthorizedHdProjection,
) -> Result<OpeningMask, HdError> {
    let config = seeds.config();
    let party_id = seeds.party_id();
    if roster.len() < usize::from(config.threshold())
        || roster.windows(2).any(|w| w[0].0 >= w[1].0)
        || roster.iter().any(|entry| !config.members().contains(entry))
        || !roster.iter().any(|entry| entry.0 == party_id)
    {
        return Err(HdError::InvalidThresholdParameters);
    }
    let AuthorizedHdProjection::PublicRelationCoefficient { row, coefficient } = projection;
    let mut context = Vec::with_capacity(16 + roster.len() * 6);
    context.extend_from_slice(&(row as u64).to_be_bytes());
    context.extend_from_slice(&(coefficient as u64).to_be_bytes());
    for &(id, x) in roster {
        context.extend_from_slice(&id.to_be_bytes());
        context.extend_from_slice(&x.to_be_bytes());
    }
    let own = seeds.position();
    let mut value = 0;
    for &(id, _) in roster {
        let other = config
            .position(id)
            .ok_or(HdError::InvalidThresholdParameters)?;
        let Some(key) = seeds.pairwise_key(other, b"QSAG.HD.OPENING_ZERO.PAIR.V1") else {
            continue;
        };
        let mut wide = SecretBuffer([0u8; 24]);
        cshake256_framed_xof(
            b"QSAG.HD.OPENING_ZERO.DEALERLESS.V1",
            &[&key[..], &session, &context],
            &mut wide[..],
        );
        let mut term = reduce_wide_mod_q(&wide[..]);
        value = if own < other {
            mod_q_add(value, term)
        } else {
            mod_q_sub(value, term)
        };
        wipe(&mut term);
    }
    Ok(OpeningMask {
        party_id,
        roster: roster.to_vec(),
        session,
        projection: Some(projection),
        value,
    })
}

/// Test-only trusted-dealer zero-sharing fixture for the historical regressions.
#[cfg(test)]
pub(crate) fn trusted_dealer_opening_masks(
    roster: &[(u16, u32)],
    session: [u8; 32],
    mut fresh_entropy: [u8; 32],
) -> Result<Vec<OpeningMask>, HdError> {
    let entropy = RedactedSecret::new(fresh_entropy);
    wipe(&mut fresh_entropy);
    if roster.is_empty() || roster.windows(2).any(|w| w[0].0 >= w[1].0) {
        return Err(HdError::InvalidThresholdParameters);
    }
    let xs: Vec<_> = roster.iter().map(|p| p.1).collect();
    validate_shamir_eval_points(&xs)?;
    let mut context = Vec::with_capacity(roster.len() * 6);
    for &(id, x) in roster {
        context.extend_from_slice(&id.to_be_bytes());
        context.extend_from_slice(&x.to_be_bytes());
    }
    let mask_seed = RedactedSecret::new(cshake256_framed_32(
        b"QSAG.HD.OPENING_ZERO.CONTEXT.V1",
        &[entropy.expose(), &session, &context],
    ));
    let mut coeffs: Vec<_> = (0..roster.len())
        .map(|i| {
            if i == 0 {
                0
            } else {
                sample_scalar_uniform_mod_q(
                    b"QSAG.HD.OPENING_ZERO.V1",
                    mask_seed.expose(),
                    i as u32,
                )
            }
        })
        .collect();
    let masks = roster
        .iter()
        .map(|&(id, x)| {
            let lambda = interpolation_weight(&xs, x);
            let z = coeffs
                .iter()
                .rev()
                .fold(0, |acc, &c| mod_q_add(mod_q_mul(acc, x), c));
            OpeningMask {
                party_id: id,
                roster: roster.to_vec(),
                session,
                projection: None,
                value: mod_q_mul(lambda, z),
            }
        })
        .collect();
    wipe(&mut coeffs);
    Ok(masks)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn production_share_requires_poison_journal() {
        let (_, mut shares) = setup_shamir_linear_module([4; 32], 2, &[1, 2, 3], 4).unwrap();
        shares[0].testing_poison_journal = false;
        assert_eq!(
            shares[0].require_poison_journal(),
            Err(HdError::MacCheckFailed)
        );
    }
    #[cfg(feature = "std")]
    #[test]
    fn mac_disclosing_abort_quarantines_recovered_family() {
        use crate::poison::{FsHdPoisonJournal, HdPoisonJournal};
        let dir = std::env::temp_dir().join(alloc::format!(
            "hd-eval-journal-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&dir).unwrap();
        let (pk, mut shares) = setup_shamir_linear_module([4; 32], 2, &[1, 2, 3], 4).unwrap();
        let family = shares[0].family_id();
        for (i, share) in shares.iter_mut().enumerate() {
            share.testing_poison_journal = false;
            share
                .attach_poison_journal(Arc::new(
                    FsHdPoisonJournal::create_new(dir.join(alloc::format!("{i}")), family, [9; 32])
                        .unwrap(),
                ))
                .unwrap();
        }
        assert!(verify_all(states(&mut shares, &pk, false)).is_ok());
        let mut rounds = states(&mut shares, &pk, false);
        for round in &mut rounds {
            round.mac_opening().unwrap();
        }
        drop(rounds);
        drop(shares);
        for i in 0..3 {
            let journal =
                FsHdPoisonJournal::open_existing(dir.join(alloc::format!("{i}")), family, [9; 32])
                    .unwrap();
            assert!(journal.is_poisoned().unwrap());
        }
        std::fs::remove_dir_all(dir).unwrap();
    }
    fn form() -> [RingPoly; MODULE_SECRET_L] {
        core::array::from_fn(|j| RingPoly {
            coeffs: core::array::from_fn(|i| ((j * 256 + i + 1) % 37) as u32),
        })
    }
    // Test harness routes public messages only; verification consumes one local
    // custodian state at a time, just as separate network endpoints would.
    fn verify_all(
        mut states: Vec<HdThresholdEvalRound3VerifyMac<'_>>,
    ) -> Result<Vec<u32>, HdError> {
        let openings: Vec<_> = states
            .iter_mut()
            .map(|s| s.mac_opening())
            .collect::<Result<_, _>>()?;
        states.into_iter().map(|s| s.verify(&openings)).collect()
    }
    fn states<'a>(
        shares: &'a mut [LinearModulePartyShare],
        pk: &LinearModuleXPub,
        fault: bool,
    ) -> Vec<HdThresholdEvalRound3VerifyMac<'a>> {
        states_with_repair(shares, pk, fault, None)
    }
    /// With `repair`, the first custodian commits to residuals shifted by those
    /// offsets before anyone freezes, as a corrupt party holding a leaked key would.
    fn states_with_repair<'a>(
        shares: &'a mut [LinearModulePartyShare],
        pk: &LinearModuleXPub,
        fault: bool,
        repair: Option<[u32; 7]>,
    ) -> Vec<HdThresholdEvalRound3VerifyMac<'a>> {
        let roster: Vec<_> = shares
            .iter()
            .map(|s| match s.scheme {
                ShareScheme::Shamir { eval_point, .. } => (s.party_id, eval_point),
                ShareScheme::Additive { .. } => *s
                    .committee
                    .iter()
                    .find(|entry| entry.0 == s.party_id)
                    .unwrap(),
            })
            .collect();
        let masks = trusted_dealer_opening_masks(&roster, [1; 32], [31; 32]).unwrap();
        let mut states: Vec<_> = shares
            .iter_mut()
            .zip(masks)
            .map(|(s, mask)| {
                HdThresholdEvalRound1Commit::begin_inner(
                    s,
                    pk,
                    &roster,
                    &form(),
                    [1; 32],
                    mask,
                    [2; 32],
                )
                .unwrap()
            })
            .collect();
        // EXACT report attack: commit a +1 value, retaining the honest gamma/alpha.
        if fault {
            states[0].0.value = mod_q_add(states[0].0.value, 1);
        }
        let commits: Vec<_> = states.iter().map(|s| s.commitment()).collect();
        let mut states: Vec<_> = states
            .into_iter()
            .map(|s| s.freeze(&commits).unwrap())
            .collect();
        let openings: Vec<_> = states.iter().map(|s| s.share_opening()).collect();
        let mut commits: Vec<_> = states
            .iter_mut()
            .map(|s| s.commit_mac(&openings).unwrap())
            .collect();
        if let Some(offsets) = repair {
            let first = &mut states[0].0;
            let value = first.opened_value.unwrap();
            let mut tags: [u32; SPDZ_LANES] = core::array::from_fn(|lane| {
                mod_q_add(
                    mod_q_sub(first.gamma[lane], mod_q_mul(first.alpha[lane], value)),
                    offsets[lane],
                )
            });
            first.mac_digest = commit_mpc_broadcast(
                &first.session,
                2,
                first.share.party_id,
                &tags_bytes(&tags),
                &first.mac_salt,
            );
            first.zero_test = Some(CommittedZeroGates::hold(first.session, MODULE_Q, &mut tags));
            commits[0] = states[0].mac_commitment();
        }
        states
            .into_iter()
            .map(|s| s.freeze_mac(&commits).unwrap())
            .collect()
    }
    fn residual_sums(states: &mut [HdThresholdEvalRound3VerifyMac<'_>]) -> [u32; 7] {
        let openings: Vec<_> = states
            .iter_mut()
            .map(|s| s.mac_opening().unwrap())
            .collect();
        core::array::from_fn(|lane| {
            openings
                .iter()
                .fold(0, |acc, o| mod_q_add(acc, o.tags[lane]))
        })
    }
    fn alpha(shares: &[LinearModulePartyShare], pk: &LinearModuleXPub) -> [u32; 7] {
        let weights = quorum_weights(shares, pk).unwrap();
        core::array::from_fn(|lane| {
            shares.iter().zip(&weights).fold(0, |sum, (s, &w)| {
                mod_q_add(sum, mod_q_mul(w, s.spdz_alpha_shares[lane]))
            })
        })
    }
    #[test]
    fn distributed_zero_test_rejects_fault_and_retires_each_custodian() {
        let (pk, mut shares) = setup_shamir_linear_module([61; 32], 3, &[1, 2, 3], 4).unwrap();
        let key = alpha(&shares, &pk);
        // Separate processes have separate quarantine latches. Every endpoint
        // must reject independently, not merely observe another endpoint's latch.
        for share in &mut shares {
            share.poisoned = Arc::new(AtomicBool::new(false));
        }
        let mut rounds = states(&mut shares, &pk, true);
        let openings: Vec<_> = rounds
            .iter_mut()
            .map(|s| s.mac_opening().unwrap())
            .collect();
        let leaked: [u32; 7] = core::array::from_fn(|lane| {
            mod_q_sub(
                0,
                openings
                    .iter()
                    .fold(0, |sum, o| mod_q_add(sum, o.tags[lane])),
            )
        });
        // Commitment prevents adaptive cancellation, NOT abort-transcript leakage.
        assert_eq!(leaked, key);
        for round in rounds {
            assert!(!round.0.share.is_poisoned());
            assert_eq!(round.verify(&openings), Err(HdError::MacCheckFailed));
        }
        for share in &shares {
            assert!(share.is_poisoned());
            assert_eq!(share.spdz_alpha_shares, [0; 7]);
        }
    }

    #[test]
    fn family_abort_blocks_pending_residual_release() {
        let (pk, mut shares) = setup_shamir_linear_module([63; 32], 3, &[1, 2, 3], 4).unwrap();
        // Model handles enrolled in the same local family quarantine context.
        let latch = Arc::new(AtomicBool::new(false));
        for share in &mut shares {
            share.poisoned = Arc::clone(&latch);
        }
        let mut rounds = states(&mut shares, &pk, false);
        // Abandoning one local state retires its shared family context.
        drop(rounds.pop());
        for mut round in rounds {
            assert!(matches!(round.mac_opening(), Err(HdError::MacCheckFailed)));
            assert_eq!(round.verify(&[]), Err(HdError::MacCheckFailed));
        }
        assert!(shares.iter().all(LinearModulePartyShare::is_poisoned));
    }

    #[test]
    fn distributed_zero_test_rejects_modified_opening_and_missing_party() {
        for missing in [false, true] {
            let (pk, mut shares) = setup_shamir_linear_module([62; 32], 3, &[1, 2, 3], 4).unwrap();
            for share in &mut shares {
                share.poisoned = Arc::new(AtomicBool::new(false));
            }
            let mut rounds = states(&mut shares, &pk, false);
            let mut openings: Vec<_> = rounds
                .iter_mut()
                .map(|s| s.mac_opening().unwrap())
                .collect();
            if missing {
                openings.pop();
            } else {
                openings[0].tags[0] = mod_q_add(openings[0].tags[0], 1);
            }
            for round in rounds {
                assert_eq!(round.verify(&openings), Err(HdError::MacCheckFailed));
            }
            assert!(shares.iter().all(LinearModulePartyShare::is_poisoned));
        }
    }

    #[test]
    fn exact_abort_extraction_cannot_forge_sibling_or_parent() {
        sibling_isolation(|_| {
            let (pk, mut parents) = setup_shamir_linear_module([77; 32], 2, &[1, 2, 3], 5).unwrap();
            let c1 = trusted_dealer_rekey_child(&mut parents, &pk, 1, [11; 32], false).unwrap();
            let c2 = trusted_dealer_rekey_child(&mut parents, &pk, 2, [12; 32], false).unwrap();
            ((pk, parents), c1, c2)
        });
    }

    /// The same exact attack against children produced by the dealerless rekey,
    /// for non-hardened and hardened siblings.
    #[test]
    fn dealerless_children_isolate_an_extracted_mac_key() {
        use crate::linear_module::harness::{committee, honest};
        let seeds = crate::seeds::run_seed_ceremony(&committee(2, 3), 0x66);
        sibling_isolation(|victim_is_parent| {
            let hardened = victim_is_parent;
            let (pk, parents) = honest(&seeds, None, 0, false, 1);
            let c1 = honest(&seeds, Some((&parents, &pk)), 1, hardened, 2);
            let c2 = honest(&seeds, Some((&parents, &pk)), 2, hardened, 3);
            ((pk, parents), c1, c2)
        });
    }

    type Family = (LinearModuleXPub, Vec<LinearModulePartyShare>);

    fn sibling_isolation(make: impl Fn(bool) -> (Family, Family, Family)) {
        for victim_is_parent in [false, true] {
            let ((pk, mut parents), (pk1, mut c1), (pk2, mut c2)) = make(victim_is_parent);
            let a0 = alpha(&parents, &pk);
            let a1 = alpha(&c1, &pk1);
            let a2 = alpha(&c2, &pk2);
            for lane in 0..7 {
                assert_ne!(a0[lane], a1[lane]);
                assert_ne!(a2[lane], a1[lane]);
            }
            let mut attack = states(&mut c1, &pk1, true);
            // A committed failed opening exposes c1's independent key.
            // The family must be retired before any subsequent use.
            let leaked = residual_sums(&mut attack).map(|sum| mod_q_sub(0, sum));
            assert_eq!(leaked, a1);
            // Corrupt party tries to repair the +1 using alpha extracted from c1.
            let (mut forged, key) = if victim_is_parent {
                (
                    states_with_repair(&mut parents, &pk, true, Some(leaked)),
                    a0,
                )
            } else {
                (states_with_repair(&mut c2, &pk2, true, Some(leaked)), a2)
            };
            {
                let sums = residual_sums(&mut forged);
                assert_eq!(
                    sums,
                    core::array::from_fn(|lane| mod_q_sub(leaked[lane], key[lane]))
                );
                assert!(sums.iter().any(|&x| x != 0));
                // Neither test may pass merely because a preceding abort set a latch.
                assert!(forged.iter().all(|s| !s.0.share.is_poisoned()));
                assert_eq!(verify_all(forged), Err(HdError::MacCheckFailed));
            }
            assert_eq!(verify_all(attack), Err(HdError::MacCheckFailed));
            assert!(parents.iter().all(LinearModulePartyShare::is_poisoned));
        }
    }
    #[test]
    fn additive_opening_authenticates_and_rejects_missing_party() {
        let (pk, shares) = setup_shamir_linear_module([18; 32], 3, &[1, 2, 3], 3).unwrap();
        let secret = reconstruct_for_recovery_or_test(&shares, &pk).unwrap();
        let expected = form().iter().zip(&secret).fold(0, |sum, (l, s)| {
            l.coeffs
                .iter()
                .zip(&s.coeffs)
                .fold(sum, |acc, (&a, &b)| mod_q_add(acc, mod_q_mul(a, b)))
        });
        let mut shares: Vec<_> = shares
            .into_iter()
            .map(|s| s.into_additive().unwrap())
            .collect();
        let short = [(0, 1), (1, 2)];
        let mask = trusted_dealer_opening_masks(&short, [7; 32], [31; 32])
            .unwrap()
            .remove(0);
        assert!(
            HdThresholdEvalRound1Commit::begin_inner(
                &mut shares[0],
                &pk,
                &short,
                &form(),
                [7; 32],
                mask,
                [2; 32]
            )
            .is_err()
        );
        assert_eq!(
            verify_all(states(&mut shares, &pk, false)).unwrap(),
            [expected; 3]
        );
        assert_eq!(
            verify_all(states(&mut shares, &pk, true)),
            Err(HdError::MacCheckFailed)
        );
    }

    #[test]
    fn fresh_zero_masks_and_honest_opening() {
        let roster = [(0, 1), (1, 2), (2, 3)];
        let a = trusted_dealer_opening_masks(&roster, [1; 32], [20; 32]).unwrap();
        let b = trusted_dealer_opening_masks(&roster, [1; 32], [21; 32]).unwrap();
        assert_eq!(a.iter().fold(0, |sum, m| mod_q_add(sum, m.value)), 0);
        assert_eq!(b.iter().fold(0, |sum, m| mod_q_add(sum, m.value)), 0);
        assert_ne!(a[0].value, b[0].value);
        let (pk, mut shares) = setup_shamir_linear_module([18; 32], 3, &[1, 2, 3], 3).unwrap();
        let secret = reconstruct_for_recovery_or_test(&shares, &pk).unwrap();
        let expected = form().iter().zip(&secret).fold(0, |sum, (l, s)| {
            l.coeffs
                .iter()
                .zip(&s.coeffs)
                .fold(sum, |acc, (&a, &b)| mod_q_add(acc, mod_q_mul(a, b)))
        });
        let weights = quorum_weights(&shares, &pk).unwrap();
        let projections: Vec<_> = shares
            .iter()
            .map(|s| linear_value(&form(), &s.s_shares))
            .collect();
        let rounds = states(&mut shares, &pk, false);
        // Exact old t>=3 transcript attack: divide each broadcast by its Lagrange
        // weight to recover the party's polynomial projection. Fresh masks defeat it.
        for ((state, &weight), &projection) in rounds.iter().zip(&weights).zip(&projections) {
            assert_ne!(
                mod_q_mul(state.0.value, mod_q_inv_or_zero(weight)),
                projection
            );
        }
        assert_eq!(verify_all(rounds).unwrap(), [expected; 3]);
    }
    #[test]
    fn exact_radix_five_recovery_forms_are_rejected() {
        let (pk, shares) = setup_shamir_linear_module([45; 32], 3, &[1, 2, 3], 4).unwrap();
        let secret = reconstruct_for_recovery_or_test(&shares, &pk).unwrap();
        let mut recovered = Vec::new();
        // Reproduce the old attack: 9 CBD2 coefficients per field opening, 228 queries.
        // Demonstrate recovery algebra, then send the exact same form to the new allowlist.
        for start in (0..2048).step_by(9) {
            let count = core::cmp::min(9, 2048 - start);
            let mut form = core::array::from_fn(|_| RingPoly::zero());
            let mut power = 1;
            let mut offset = 0;
            let mut opened = 0;
            for j in 0..count {
                let index = start + j;
                form[index / 256].coeffs[index % 256] = power;
                opened = mod_q_add(
                    opened,
                    mod_q_mul(power, secret[index / 256].coeffs[index % 256]),
                );
                offset += 2 * power;
                power *= 5;
            }
            let mut digits = mod_q_add(opened, offset);
            for _ in 0..count {
                recovered.push(mod_q_sub(digits % 5, 2));
                digits /= 5;
            }
            assert_eq!(
                AuthorizedHdProjection::from_form(&pk, &form),
                Err(HdError::UnauthorizedProjection)
            );
        }
        assert_eq!(
            recovered,
            secret.iter().flat_map(|p| p.coeffs).collect::<Vec<_>>()
        );
        // Positive control: every permitted projection matches the public relation.
        for row in 0..MODULE_K {
            for coefficient in [0, 1, 127, 255] {
                let projection =
                    AuthorizedHdProjection::PublicRelationCoefficient { row, coefficient };
                let form = projection.form(&pk).unwrap();
                assert_eq!(
                    AuthorizedHdProjection::from_form(&pk, &form),
                    Ok(projection)
                );
                let value = form.iter().zip(&secret).fold(0, |sum, (l, s)| {
                    l.coeffs
                        .iter()
                        .zip(&s.coeffs)
                        .fold(sum, |acc, (&a, &b)| mod_q_add(acc, mod_q_mul(a, b)))
                });
                assert_eq!(value, pk.t_vec[row].coeffs[coefficient]);
            }
        }
    }

    #[test]
    fn public_projection_begin_aborts_wrong_opened_scalar_before_releasing_mac_tags() {
        use crate::linear_module::harness::{committee, honest};
        let config = committee(2, 3);
        let seeds = crate::seeds::run_seed_ceremony(&config, 0x7A);
        let (pk, mut shares) = honest(&seeds, None, 0, false, 1);
        for share in &mut shares {
            share.poisoned = Arc::new(AtomicBool::new(false));
        }
        let roster = config.members().to_vec();
        let projection = AuthorizedHdProjection::PublicRelationCoefficient {
            row: 1,
            coefficient: 17,
        };
        let masks: Vec<_> = (0..3)
            .map(|p| dealerless_opening_mask(&seeds[p], &roster, [0x44; 32], projection).unwrap())
            .collect();
        let mut round1: Vec<_> = shares
            .iter_mut()
            .zip(masks)
            .enumerate()
            .map(|(idx, (share, mask))| {
                HdThresholdEvalRound1Commit::begin(
                    share,
                    &pk,
                    &roster,
                    projection,
                    [0x44; 32],
                    mask,
                    [idx as u8 + 1; 32],
                )
                .unwrap()
            })
            .collect();

        // Corrupt custodian 0 injects a +1 additive fault into its opened share.
        round1[0].0.value = mod_q_add(round1[0].0.value, 1);
        let commits: Vec<_> = round1.iter().map(|s| s.commitment()).collect();
        let mut round2: Vec<_> = round1
            .into_iter()
            .map(|s| s.freeze(&commits).unwrap())
            .collect();
        let share_openings: Vec<_> = round2.iter().map(|s| s.share_opening()).collect();

        // Every custodian MUST abort inside `commit_mac` BEFORE computing or releasing the 7 MAC tags!
        for state in &mut round2 {
            assert_eq!(
                state.commit_mac(&share_openings),
                Err(HdError::MacCheckFailed)
            );
            assert!(state.0.zero_test.is_none());
            assert_eq!(state.0.opened_value, None);
            assert!(state.0.share.is_poisoned());
        }
        for state in round2 {
            assert!(state.freeze_mac(&[]).is_err());
        }
        assert!(shares.iter().all(LinearModulePartyShare::is_poisoned));
    }

    #[cfg(feature = "std")]
    #[test]
    fn durable_budget_is_inherited_by_child_and_recovered_before_begin() {
        use crate::budget::DurableQueryBudget;
        use std::sync::Mutex;
        let dir = std::env::temp_dir().join(alloc::format!(
            "hd-eval-budget-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&dir).unwrap();
        let path = dir.join("journal");
        let (pk, mut parents) = setup_shamir_linear_module([51; 32], 1, &[1], 3).unwrap();
        let family = parents[0].family_id();
        let journal = Arc::new(Mutex::new(
            DurableQueryBudget::create(&path, family, [4; 32]).unwrap(),
        ));
        parents[0].attach_budget(Arc::clone(&journal)).unwrap();
        let (child_pk, mut child) =
            trusted_dealer_rekey_child(&mut parents, &pk, 7, [44; 32], true).unwrap();
        for _ in 0..127 {
            parents[0].burn_query().unwrap();
        }
        let mask = trusted_dealer_opening_masks(&[(0, 1)], [1; 32], [9; 32])
            .unwrap()
            .remove(0);
        let projection = AuthorizedHdProjection::PublicRelationCoefficient {
            row: 0,
            coefficient: 3,
        };
        let state = HdThresholdEvalRound1Commit::begin_inner(
            &mut child[0],
            &child_pk,
            &[(0, 1)],
            &projection.form(&child_pk).unwrap(),
            [1; 32],
            mask,
            [8; 32],
        )
        .unwrap();
        let commitment = state.commitment();
        let mut state = state.freeze(&[commitment]).unwrap();
        let opening = state.share_opening();
        let mac = state.commit_mac(&[opening]).unwrap();
        let state = state.freeze_mac(&[mac]).unwrap();
        assert_eq!(
            verify_all(alloc::vec![state]).unwrap(),
            [child_pk.t_vec[0].coeffs[3]]
        );
        drop(child);
        drop(parents);
        drop(journal);
        // A fresh process-equivalent root handle cannot reset the durable family counter.
        let (pk, mut restored) = setup_shamir_linear_module([51; 32], 1, &[1], 3).unwrap();
        let journal = Arc::new(Mutex::new(
            DurableQueryBudget::open(&path, family, [4; 32]).unwrap(),
        ));
        restored[0].attach_budget(Arc::clone(&journal)).unwrap();
        let mask = trusted_dealer_opening_masks(&[(0, 1)], [2; 32], [10; 32])
            .unwrap()
            .remove(0);
        assert!(matches!(
            HdThresholdEvalRound1Commit::begin_inner(
                &mut restored[0],
                &pk,
                &[(0, 1)],
                &projection.form(&pk).unwrap(),
                [2; 32],
                mask,
                [8; 32]
            ),
            Err(HdError::EvaluationBudgetExceeded)
        ));
        drop(restored);
        drop(journal);
        std::fs::remove_dir_all(dir).unwrap();
    }
}
