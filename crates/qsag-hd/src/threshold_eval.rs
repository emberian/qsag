//! Per-party committed SPDZ zero-test for scalar openings.
//! Requires authenticated reliable broadcast: every honest party must freeze the same
//! ordered commitment transcript before any MAC residual is opened. Transport and
//! persistent cross-process family quarantine are the caller's responsibility.
//! Opening masks come from the dealerless pairwise zero-sharing below.
//! Public callers can open only coefficients of the already-public relation A*s1+s2.
//! Arbitrary short-secret projections are not an authorized API.
use super::*;
use crate::seeds::CustodianSeeds;
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
    tags: [u32; SPDZ_LANES],
    expected_value: Option<u32>,
    opened_value: Option<u32>,
    complete: bool,
}
impl Drop for EvalState<'_> {
    fn drop(&mut self) {
        ct_zeroize_u32s(core::slice::from_mut(&mut self.value));
        ct_zeroize_u32s(&mut self.gamma);
        ct_zeroize_u32s(&mut self.alpha);
        ct_zeroize_u32s(&mut self.tags);
        ct_zeroize_bytes(&mut self.value_salt);
        ct_zeroize_bytes(&mut self.mac_salt);
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
/// fn leak(s: &HdThresholdEvalRound2OpenShareAndCommitMac<'_>) { let _ = s.mac_opening(); }
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
        ct_zeroize_bytes(&mut private_entropy);
        let (threshold, own_x) = match share.scheme {
            ShareScheme::Shamir {
                threshold,
                eval_point,
            } => (threshold, eval_point),
            _ => return Err(HdError::InvalidThresholdParameters),
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
        let mut numerator = 1;
        let mut denominator = 1;
        for &x in &xs {
            if x != own_x {
                numerator = mod_q_mul(numerator, mod_q_sub(0, x));
                denominator = mod_q_mul(denominator, mod_q_sub(own_x, x));
            }
        }
        let lambda = mod_q_mul(numerator, mod_q_inv_or_zero(denominator));
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
        context.extend_from_slice(&threshold.to_be_bytes());
        for &(id, x) in roster {
            context.extend_from_slice(&id.to_be_bytes());
            context.extend_from_slice(&x.to_be_bytes());
        }
        for poly in form {
            context.extend_from_slice(&poly.to_bytes());
        }
        let session = cshake256_framed_32(b"QSAG.HD.EVAL.CONTEXT.V1", &[&session_id, &context]);
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
            tags: [0; SPDZ_LANES],
            expected_value,
            opened_value: None,
            complete: false,
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
        self.0.tags = core::array::from_fn(|lane| {
            mod_q_sub(self.0.gamma[lane], mod_q_mul(self.0.alpha[lane], value))
        });
        self.0.opened_value = Some(value);
        Ok(self.mac_commitment())
    }
    fn mac_commitment(&self) -> HdEvalCommitment {
        HdEvalCommitment {
            party_id: self.0.share.party_id,
            digest: commit_mpc_broadcast(
                &self.0.session,
                2,
                self.0.share.party_id,
                &tags_bytes(&self.0.tags),
                &self.0.mac_salt,
            ),
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
        self.0.mac_commitments = commitments.to_vec();
        Ok(HdThresholdEvalRound3VerifyMac(self.0))
    }
}
impl HdThresholdEvalRound3VerifyMac<'_> {
    /// Broadcast only after agreement on the frozen commitment transcript.
    /// This message may leak alpha on failure; no further family operations may
    /// proceed until every participating custodian has accepted the zero-test.
    pub fn mac_opening(&self) -> Result<HdEvalMacOpening, HdError> {
        if self.0.share.is_poisoned()
            || self
                .0
                .expected_value
                .is_some_and(|exp| self.0.opened_value != Some(exp))
        {
            return Err(HdError::MacCheckFailed);
        }
        Ok(HdEvalMacOpening {
            party_id: self.0.share.party_id,
            tags: self.0.tags,
            salt: self.0.mac_salt,
        })
    }
    /// Only this transition releases an authenticated scalar result. Failure or
    /// abandoning any phase wipes and poisons this custodian's key material.
    pub fn verify(mut self, openings: &[HdEvalMacOpening]) -> Result<u32, HdError> {
        if self.0.share.is_poisoned() || openings.len() != self.0.roster.len() {
            return Err(HdError::MacCheckFailed);
        }
        let mut sums = [0; SPDZ_LANES];
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
            if !ct_eq_bytes(&actual, &expected.digest) {
                return Err(HdError::MacCheckFailed);
            }
            for (sum, &tag) in sums.iter_mut().zip(&opening.tags) {
                *sum = mod_q_add(*sum, tag);
            }
        }
        let invalid = sums.iter().fold(0, |acc, &x| acc | x) != 0;
        ct_zeroize_u32s(&mut sums);
        if invalid {
            return Err(HdError::MacCheckFailed);
        }
        let value = self.0.opened_value.ok_or(HdError::MacCheckFailed)?;
        self.0.complete = true;
        Ok(value)
    }
}

impl Drop for HdEvalMacOpening {
    fn drop(&mut self) {
        ct_zeroize_u32s(&mut self.tags);
        ct_zeroize_bytes(&mut self.salt);
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
        ct_zeroize_u32s(core::slice::from_mut(&mut self.value));
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
