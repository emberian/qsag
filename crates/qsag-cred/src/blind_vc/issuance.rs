use super::*;

// ============================================================================
// Phase 1 & 2: Blind Issuance (`holder_prepare_blind_issuance` + `threshold_issue_blind_vc`)
// ============================================================================

/// Holder secret state with redacted `Debug` and zeroizing `Drop`.
///
/// # Presentation freshness and replay
/// No verifier-controlled challenge history is kept. Refusing a challenge seen
/// at another verifier would let colluding verifiers recognize this holder;
/// even a bounded scoped history could reveal prior use through exhaustion.
/// Callers supply fresh private entropy for every presentation. The nonce binds
/// that entropy to the scope, challenge, mode, issuer root and disclosure; proof
/// randomness is additionally hedged with the complete public statement.
///
/// This preserves fresh randomized proofs and binding to the requested scope
/// and challenge. It deliberately gives up local duplicate-challenge refusal.
/// Captured-proof replay was never prevented by holder history. It is refused on
/// the verifier's side: [`verify_presentation`] consumes the presentation's
/// challenge from the verifier's [`PresentationChallenges`] ledger, which issued
/// it, expires it and accepts it once. A
/// repeated challenge is safe to answer with fresh entropy, but revealing the
/// same attributes or using `ScopedPseudonym` can still identify the holder.
///
/// This type has no serialization API or persisted challenge-history format.
pub struct HolderCredentialSecret {
    pub schema_id: u64,
    pub(super) arity: usize,
    pub(super) attrs: [u64; MAX_VC_ATTRS],
    pub(super) holder_blind: [u64; 4],
}

impl fmt::Debug for HolderCredentialSecret {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("HolderCredentialSecret")
            .field("schema_id", &self.schema_id)
            .field("attrs", &"<REDACTED>")
            .field("holder_blind", &"<REDACTED>")
            .finish()
    }
}

impl Drop for HolderCredentialSecret {
    fn drop(&mut self) {
        ct_zeroize_u64s(&mut self.attrs);
        ct_zeroize_u64s(&mut self.holder_blind);
    }
}

impl HolderCredentialSecret {
    /// Number of active Goldilocks attribute limbs (`<= MAX_VC_ATTRS`) committed by this credential.
    #[inline]
    pub const fn arity(&self) -> usize {
        self.arity
    }

    /// Borrow the active Goldilocks attribute limbs (`&self.attrs[..self.arity]`) for cross-proof
    /// (`BlindVC -> zk-Hem`) witness composition without copying secrets onto the stack.
    #[inline]
    pub fn attrs(&self) -> &[u64] {
        &self.attrs[..self.arity]
    }

    /// Borrow the 4-limb Goldilocks holder blinding factor committed inside `attr_commit`.
    #[inline]
    pub const fn holder_blind(&self) -> &[u64; 4] {
        &self.holder_blind
    }
}

/// Issuance request proving an attested-attribute commitment while hiding its holder blind.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlindIssuanceRequest {
    pub issuer_pk_digest: [u8; 32],
    pub issuer_epoch: u64,
    pub issuer_attested_attrs: Vec<u64>,
    pub session_id: [u8; 32],
    pub schema_id: u64,
    pub attr_commit: [u64; 6],
    pub opened_reps: Vec<OpenedZkBooRepetition>,
}

/// OPRF-issued credential enrolled in the issuer accumulator. The token is
/// erased on drop and compared without data-dependent timing.
#[derive(Clone)]
pub struct BlindVerifiableCredential {
    pub issuer_epoch: u64,
    pub schema_id: u64,
    pub attr_commit: [u64; 6],
    /// OPRF token; accumulator membership supplies public authorization.
    pub issuance_token: [u8; 32],
    pub accumulator_leaf_index: usize,
}

impl PartialEq for BlindVerifiableCredential {
    fn eq(&self, other: &Self) -> bool {
        let public = (self.issuer_epoch == other.issuer_epoch)
            & (self.schema_id == other.schema_id)
            & (self.attr_commit == other.attr_commit)
            & (self.accumulator_leaf_index == other.accumulator_leaf_index);
        ct_eq_bytes(&self.issuance_token, &other.issuance_token) & public
    }
}

impl Eq for BlindVerifiableCredential {}

impl BlindVerifiableCredential {
    pub(super) fn erase_secrets(&mut self) {
        ct_zeroize_bytes(&mut self.issuance_token);
    }
}

impl Drop for BlindVerifiableCredential {
    fn drop(&mut self) {
        self.erase_secrets();
    }
}

impl core::fmt::Debug for BlindVerifiableCredential {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("BlindVerifiableCredential")
            .field("issuer_epoch", &self.issuer_epoch)
            .field("schema_id", &self.schema_id)
            .field("attr_commit", &self.attr_commit)
            .field("issuance_token", &"<REDACTED>")
            .field("accumulator_leaf_index", &self.accumulator_leaf_index)
            .finish()
    }
}

/// Prepare an issuance request and holder secret from at most [`MAX_VC_ATTRS`]
/// canonical Goldilocks attributes. The request discloses those attributes.
pub fn holder_prepare_blind_issuance(
    schema_id: u64,
    issuer_attested_attrs: &[u64],
    issuer_pk_digest: [u8; 32],
    issuer_epoch: u64,
    holder_entropy: [u8; 32],
    session_id: [u8; 32],
) -> Result<(BlindIssuanceRequest, HolderCredentialSecret), BlindVcError> {
    holder_prepare_blind_issuance_with_profile(
        schema_id,
        issuer_attested_attrs,
        issuer_pk_digest,
        issuer_epoch,
        holder_entropy,
        session_id,
        ZkSoundnessProfile::Quantum128,
    )
}

/// Use an explicit verifier-selected soundness budget.
#[allow(clippy::too_many_arguments)]
pub fn holder_prepare_blind_issuance_with_profile(
    schema_id: u64,
    issuer_attested_attrs: &[u64],
    issuer_pk_digest: [u8; 32],
    issuer_epoch: u64,
    holder_entropy: [u8; 32],
    session_id: [u8; 32],
    profile: ZkSoundnessProfile,
) -> Result<(BlindIssuanceRequest, HolderCredentialSecret), BlindVcError> {
    let ent = qsag_accel::ct::RedactedSecret::new(holder_entropy);
    if !(1..=MAX_VC_ATTRS).contains(&issuer_attested_attrs.len()) {
        return Err(BlindVcError::AttributeCountExceeded {
            count: issuer_attested_attrs.len(),
        });
    }
    let mut attrs = SecretBuffer([0u64; MAX_VC_ATTRS]);
    for (i, &v) in issuer_attested_attrs.iter().enumerate() {
        if !gl_is_canonical(v) {
            return Err(BlindVcError::NonCanonicalGoldilocksAttribute { index: i });
        }
        attrs[i] = v;
    }

    let mut blind_ctx = Vec::with_capacity(60 + issuer_attested_attrs.len() * 8);
    blind_ctx.extend_from_slice(&session_id);
    blind_ctx.extend_from_slice(&schema_id.to_le_bytes());
    blind_ctx.extend_from_slice(&issuer_pk_digest);
    blind_ctx.extend_from_slice(&issuer_epoch.to_le_bytes());
    blind_ctx.extend_from_slice(&(issuer_attested_attrs.len() as u32).to_le_bytes());
    for value in issuer_attested_attrs {
        blind_ctx.extend_from_slice(&value.to_le_bytes());
    }
    let blind_vec =
        sample_canonical_gl_vec(b"QSAG.VC.HOLDER_BLIND.V1", ent.expose(), &blind_ctx, 4);
    let mut holder_blind =
        SecretBuffer(vec![blind_vec[0], blind_vec[1], blind_vec[2], blind_vec[3]]);
    drop(blind_vec);
    let holder_blind_arr = SecretBuffer([
        holder_blind[0],
        holder_blind[1],
        holder_blind[2],
        holder_blind[3],
    ]);
    let attr_commit = compute_vc_poseidon2_commit(
        schema_id,
        issuer_attested_attrs,
        &holder_blind_arr,
        VC_ATTR_COMMIT_TAG,
    )?;

    let attr_slots = issuer_attested_attrs.len().max(6);
    let input_wires = attr_slots + 4;
    let issuance_gates = attribute_commitment_gates(attr_slots);
    // Public attribute slots followed by four private holder-blind limbs.
    let mut inst_bytes = Vec::with_capacity(72);
    inst_bytes.extend_from_slice(&session_id);
    inst_bytes.extend_from_slice(&schema_id.to_le_bytes());
    inst_bytes.extend_from_slice(&issuer_pk_digest);
    inst_bytes.extend_from_slice(&issuer_epoch.to_le_bytes());
    inst_bytes.extend_from_slice(&(issuer_attested_attrs.len() as u32).to_le_bytes());
    for value in issuer_attested_attrs {
        inst_bytes.extend_from_slice(&value.to_le_bytes());
    }
    for &c in &attr_commit {
        inst_bytes.extend_from_slice(&c.to_le_bytes());
    }
    inst_bytes.extend_from_slice(profile.issuance_statement_tag());
    let statement_digest = cshake256_framed_32(b"QSAG.VC.ISS_STMT_DIGEST.V1", &[&inst_bytes]);
    let hedged_zk_seed = qsag_accel::ct::RedactedSecret::new(cshake256_framed_32(
        b"QSAG.VC.ISS_ZK_SEED.V1",
        &[&statement_digest, ent.expose(), &session_id],
    ));
    let mut tr = InterleavedTranscript::new(b"QSAG.BLIND_VC.ISSUE_ZK.V1", &inst_bytes);
    tr.absorb(b"VC_SOUNDNESS_PROFILE", profile.issuance_transcript_tag());

    let mut secret_wires = SecretBuffer(attrs[..attr_slots].to_vec());
    secret_wires.extend_wiping(&holder_blind);

    struct RepData {
        commits: [[u8; 32]; 3],
        salts: [[u8; 32]; 3],
        in_shares: [Vec<u64>; 3],
        tape_seeds: [[u8; 32]; 3],
        gate_outs: [Vec<u64>; 3],
        final_outs: [[u64; 3]; VC_FINAL_OUTPUTS],
    }
    impl Drop for RepData {
        fn drop(&mut self) {
            for row in &mut self.in_shares {
                ct_zeroize_u64s(row);
            }
            for row in &mut self.gate_outs {
                ct_zeroize_u64s(row);
            }
            for row in &mut self.tape_seeds {
                ct_zeroize_bytes(row);
            }
            for row in &mut self.salts {
                ct_zeroize_bytes(row);
            }
            for row in &mut self.final_outs {
                ct_zeroize_u64s(row);
            }
        }
    }

    let mut reps = Vec::with_capacity(profile.repetitions());
    let mut round1_bundle = Vec::with_capacity(profile.repetitions() * 192);

    for rep in 0..profile.repetitions() {
        let rep_be = (rep as u32).to_be_bytes();
        let mut share_ctx = [0u8; 36];
        share_ctx[..32].copy_from_slice(&statement_digest);
        share_ctx[32..].copy_from_slice(&rep_be);
        let in_rand = sample_canonical_gl_vec(
            b"QSAG.VC.ISS_IN_SH.V1",
            hedged_zk_seed.expose(),
            &share_ctx,
            2 * input_wires,
        );
        let mut in0 = Vec::with_capacity(input_wires);
        let mut in1 = Vec::with_capacity(input_wires);
        let mut in2 = Vec::with_capacity(input_wires);
        // Sized for the three padding wires appended before the permutation, so
        // the secret shares are never copied to a second heap block.
        let mut wire_3 = SecretBuffer(Vec::with_capacity(input_wires + 3));
        wire_3.resize(input_wires, [0u64; 3]);
        for (w, wire) in wire_3.iter_mut().enumerate() {
            let s = if w < attr_slots {
                [secret_wires[w], 0, 0]
            } else {
                split_secret_3(secret_wires[w], in_rand[2 * w], in_rand[2 * w + 1])
            };
            *wire = s;
            in0.push(s[0]);
            in1.push(s[1]);
            in2.push(s[2]);
        }

        let tape_seeds: [[u8; 32]; 3] = core::array::from_fn(|m| {
            cshake256_framed_32(
                b"QSAG.VC.ISS_TAPE.V1",
                &[
                    &statement_digest,
                    hedged_zk_seed.expose(),
                    &session_id,
                    &rep_be,
                    &[m as u8],
                ],
            )
        });
        let salts: [[u8; 32]; 3] = core::array::from_fn(|m| {
            cshake256_framed_32(
                b"QSAG.VC.ISS_SALT.V1",
                &[
                    &statement_digest,
                    hedged_zk_seed.expose(),
                    &session_id,
                    &rep_be,
                    &[m as u8],
                ],
            )
        });

        let mut prover = ZkBooProverTape::new(&tape_seeds, issuance_gates);
        let mut st = wire_3;
        st.extend_from_slice(&[
            [schema_id & 0xffff_ffff, 0, 0],
            [
                gl_add(schema_id >> 32, gl_reduce_u64(VC_ATTR_COMMIT_TAG)),
                0,
                0,
            ],
            [issuer_attested_attrs.len() as u64, 0, 0],
        ]);
        prover.perm12(&mut st);

        let mut final_outs = [[0u64; 3]; VC_FINAL_OUTPUTS];
        final_outs[..6].copy_from_slice(&st[..6]);
        drop(st);

        let in_shares = [in0, in1, in2];
        let commits: [[u8; 32]; 3] = core::array::from_fn(|m| {
            let f_m: [u64; 6] = core::array::from_fn(|j| final_outs[j][m]);
            let d = digest_party_view(&in_shares[m], &tape_seeds[m], &prover.out[m], &f_m);
            commit_mpc_broadcast(&session_id, rep as u32, m as u16, &d, &salts[m])
        });

        for c in &commits {
            round1_bundle.extend_from_slice(c);
        }
        for fout in final_outs.iter().take(6) {
            for &val in fout {
                round1_bundle.extend_from_slice(&val.to_le_bytes());
            }
        }

        reps.push(RepData {
            commits,
            salts,
            in_shares,
            tape_seeds,
            gate_outs: core::mem::take(&mut prover.out),
            final_outs,
        });
    }

    // Absorb ALL Round-1 view commitments & output shares BEFORE ZKBoo challenges!
    tr.absorb(b"VC_ISS_R1_COMMITS", &round1_bundle);
    let open_trits = squeeze_ternary_challenges(&mut tr, profile.repetitions());
    drop(hedged_zk_seed);
    drop(ent);
    drop(secret_wires);

    let mut opened_reps = Vec::with_capacity(profile.repetitions());
    for (rep_d, e) in reps.into_iter().zip(open_trits) {
        let e1 = (e + 1) % 3;
        let e2 = (e + 2) % 3;
        opened_reps.push(OpenedZkBooRepetition {
            e: e as u8,
            unopened_commitment: rep_d.commits[e2],
            salt_e: rep_d.salts[e],
            salt_e1: rep_d.salts[e1],
            in_shares_e: rep_d.in_shares[e].clone(),
            in_shares_e1: rep_d.in_shares[e1].clone(),
            tape_seed_e: rep_d.tape_seeds[e],
            tape_seed_e1: rep_d.tape_seeds[e1],
            gate_outs_e: rep_d.gate_outs[e].clone(),
            gate_outs_e1: rep_d.gate_outs[e1].clone(),
            final_outs_all3: rep_d.final_outs,
            num_active_final_outs: 6,
        });
    }

    let final_holder_blind = [
        holder_blind[0],
        holder_blind[1],
        holder_blind[2],
        holder_blind[3],
    ];
    let _ = &mut holder_blind;
    Ok((
        BlindIssuanceRequest {
            issuer_pk_digest,
            issuer_epoch,
            issuer_attested_attrs: issuer_attested_attrs.to_vec(),
            session_id,
            schema_id,
            attr_commit,
            opened_reps,
        },
        HolderCredentialSecret {
            schema_id,
            arity: issuer_attested_attrs.len(),
            attrs: *attrs,
            holder_blind: final_holder_blind,
        },
    ))
}

/// Verify a request against externally authorized attributes and schema.
pub fn verify_blind_issuance_request(
    req: &BlindIssuanceRequest,
    issuer_attested_attrs: &[u64],
    expected_schema_id: u64,
) -> bool {
    verify_blind_issuance_request_with_profile(
        req,
        issuer_attested_attrs,
        expected_schema_id,
        ZkSoundnessProfile::Quantum128,
    )
}

/// Use an explicit verifier-selected soundness budget.
#[allow(clippy::too_many_arguments)]
pub fn verify_blind_issuance_request_with_profile(
    req: &BlindIssuanceRequest,
    issuer_attested_attrs: &[u64],
    expected_schema_id: u64,
    profile: ZkSoundnessProfile,
) -> bool {
    if req.schema_id != expected_schema_id
        || !(1..=MAX_VC_ATTRS).contains(&issuer_attested_attrs.len())
        || req.issuer_attested_attrs != issuer_attested_attrs
        || !issuer_attested_attrs.iter().all(|&v| gl_is_canonical(v))
    {
        return false;
    }
    if req.opened_reps.len() != profile.repetitions() {
        return false;
    }
    for &c in &req.attr_commit {
        if !gl_is_canonical(c) {
            return false;
        }
    }

    let mut inst_bytes = Vec::with_capacity(72);
    inst_bytes.extend_from_slice(&req.session_id);
    inst_bytes.extend_from_slice(&req.schema_id.to_le_bytes());
    inst_bytes.extend_from_slice(&req.issuer_pk_digest);
    inst_bytes.extend_from_slice(&req.issuer_epoch.to_le_bytes());
    inst_bytes.extend_from_slice(&(issuer_attested_attrs.len() as u32).to_le_bytes());
    for value in issuer_attested_attrs {
        inst_bytes.extend_from_slice(&value.to_le_bytes());
    }
    for &c in &req.attr_commit {
        inst_bytes.extend_from_slice(&c.to_le_bytes());
    }
    inst_bytes.extend_from_slice(profile.issuance_statement_tag());
    let mut tr = InterleavedTranscript::new(b"QSAG.BLIND_VC.ISSUE_ZK.V1", &inst_bytes);
    tr.absorb(b"VC_SOUNDNESS_PROFILE", profile.issuance_transcript_tag());

    let mut round1_bundle = Vec::with_capacity(profile.repetitions() * 192);

    let attr_slots = issuer_attested_attrs.len().max(6);
    let input_wires = attr_slots + 4;
    let issuance_gates = attribute_commitment_gates(attr_slots);
    for (rep, o) in req.opened_reps.iter().enumerate() {
        let e = o.e as usize;
        if e >= 3
            || o.num_active_final_outs != 6
            || o.final_outs_all3[6..].iter().flatten().any(|&v| v != 0)
            || o.in_shares_e.len() != input_wires
            || o.in_shares_e1.len() != input_wires
        {
            return false;
        }
        let e1 = (e + 1) % 3;
        let e2 = (e + 2) % 3;

        for index in 0..attr_slots {
            let value = issuer_attested_attrs.get(index).copied().unwrap_or(0);
            if o.in_shares_e[index] != if e == 0 { value } else { 0 }
                || o.in_shares_e1[index] != if e1 == 0 { value } else { 0 }
            {
                return false;
            }
        }
        for &x in o.in_shares_e.iter().chain(o.in_shares_e1.iter()) {
            if !gl_is_canonical(x) {
                return false;
            }
        }
        for &x in o.gate_outs_e.iter().chain(o.gate_outs_e1.iter()) {
            if !gl_is_canonical(x) {
                return false;
            }
        }

        let mut verifier = ZkBooVerifierTape::new(
            e,
            &o.tape_seed_e,
            &o.tape_seed_e1,
            &o.gate_outs_e,
            &o.gate_outs_e1,
            issuance_gates,
        );
        let mut st: Vec<[u64; 2]> = o
            .in_shares_e
            .iter()
            .zip(&o.in_shares_e1)
            .map(|(&a, &b)| [a, b])
            .collect();
        st.extend_from_slice(&[
            verifier.add_const([0, 0], req.schema_id & 0xffff_ffff),
            verifier.add_const(
                [0, 0],
                gl_add(req.schema_id >> 32, gl_reduce_u64(VC_ATTR_COMMIT_TAG)),
            ),
            verifier.add_const([0, 0], issuer_attested_attrs.len() as u64),
        ]);
        verifier.perm12(&mut st);
        if !verifier.ok {
            return false;
        }

        for (j, wire) in st.iter().take(6).enumerate() {
            for &s_val in &o.final_outs_all3[j] {
                if !gl_is_canonical(s_val) {
                    return false;
                }
            }
            if wire[0] != o.final_outs_all3[j][e] || wire[1] != o.final_outs_all3[j][e1] {
                return false;
            }
            let recon = gl_add(
                o.final_outs_all3[j][0],
                gl_add(o.final_outs_all3[j][1], o.final_outs_all3[j][2]),
            );
            if recon != req.attr_commit[j] {
                return false;
            }
        }

        let f_e: [u64; 6] = core::array::from_fn(|j| o.final_outs_all3[j][e]);
        let f_e1: [u64; 6] = core::array::from_fn(|j| o.final_outs_all3[j][e1]);
        let d_e = digest_party_view(&o.in_shares_e, &o.tape_seed_e, &o.gate_outs_e, &f_e);
        let d_e1 = digest_party_view(&o.in_shares_e1, &o.tape_seed_e1, &o.gate_outs_e1, &f_e1);
        let com_e = commit_mpc_broadcast(&req.session_id, rep as u32, e as u16, &d_e, &o.salt_e);
        let com_e1 =
            commit_mpc_broadcast(&req.session_id, rep as u32, e1 as u16, &d_e1, &o.salt_e1);

        let mut commits = [[0u8; 32]; 3];
        commits[e] = com_e;
        commits[e1] = com_e1;
        commits[e2] = o.unopened_commitment;
        for c in &commits {
            round1_bundle.extend_from_slice(c);
        }
        for fout in o.final_outs_all3.iter().take(6) {
            for &val in fout {
                round1_bundle.extend_from_slice(&val.to_le_bytes());
            }
        }
    }

    tr.absorb(b"VC_ISS_R1_COMMITS", &round1_bundle);
    let expected_trits = squeeze_ternary_challenges(&mut tr, profile.repetitions());
    for (o, exp_e) in req.opened_reps.iter().zip(expected_trits) {
        if (o.e as usize) != exp_e {
            return false;
        }
    }
    true
}

/// Domain-separated 32-byte commitment tag binding `(issuer_pk_digest, issuer_epoch, accumulator_root)`.
pub fn compute_accumulator_root_tag(
    issuer_pk_digest: &[u8; 32],
    issuer_epoch: u64,
    accumulator_root: &[u64; 6],
) -> [u8; 32] {
    let mut root_le = [0u8; 48];
    for (i, &limb) in accumulator_root.iter().enumerate() {
        root_le[i * 8..(i + 1) * 8].copy_from_slice(&limb.to_le_bytes());
    }
    cshake256_framed_32(
        b"QSAG.VC.ACC_ROOT_TAG.V1",
        &[issuer_pk_digest, &issuer_epoch.to_le_bytes(), &root_le],
    )
}

/// Issuer-signed commitment/attestation binding `(issuer_pk_digest, issuer_epoch, accumulator_root)`
/// under FIPS 204 `ML-DSA` (compatible with both single-signer [`ml_dsa_sign_deterministic`] and
/// dealerless [`crate::threshold_mldsa::threshold_sign_mldsa_party`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IssuerRootAttestation {
    issuer_pk_digest: [u8; 32],
    mldsa_level: MlDsaLevel,
    issuer_mldsa_pk: Vec<u8>,
    pub(super) issuer_epoch: u64,
    pub(super) accumulator_root: [u64; 6],
    pub(super) root_tag: [u8; 32],
    mldsa_signature: Vec<u8>,
}

impl IssuerRootAttestation {
    pub const SIGNING_CONTEXT: &'static [u8] = b"QSAG.VC.ROOT_ATTEST.CTX.V1";

    pub fn signing_message(
        issuer_pk_digest: &[u8; 32],
        issuer_epoch: u64,
        accumulator_root: &[u64; 6],
        root_tag: &[u8; 32],
    ) -> [u8; 142] {
        let mut msg = [0u8; 142];
        msg[..22].copy_from_slice(b"QSAG.VC.ROOT_ATTEST.V1");
        msg[22..54].copy_from_slice(issuer_pk_digest);
        msg[54..62].copy_from_slice(&issuer_epoch.to_le_bytes());
        for (i, &limb) in accumulator_root.iter().enumerate() {
            msg[62 + i * 8..62 + (i + 1) * 8].copy_from_slice(&limb.to_le_bytes());
        }
        msg[110..142].copy_from_slice(root_tag);
        msg
    }

    pub const fn issuer_pk_digest(&self) -> &[u8; 32] {
        &self.issuer_pk_digest
    }

    pub const fn mldsa_level(&self) -> MlDsaLevel {
        self.mldsa_level
    }

    pub fn issuer_mldsa_pk(&self) -> &[u8] {
        &self.issuer_mldsa_pk
    }

    pub const fn issuer_epoch(&self) -> u64 {
        self.issuer_epoch
    }

    pub const fn accumulator_root(&self) -> &[u64; 6] {
        &self.accumulator_root
    }

    pub const fn root_tag(&self) -> &[u8; 32] {
        &self.root_tag
    }

    pub fn mldsa_signature(&self) -> &[u8] {
        &self.mldsa_signature
    }

    /// Cryptographically verify `(issuer_pk_digest, issuer_epoch, accumulator_root, root_tag)`
    /// against `expected_issuer_mldsa_pk` and `expected_oprf_pk`.
    pub fn verify(&self, expected_issuer_mldsa_pk: &[u8], expected_oprf_pk: &PublicKey) -> bool {
        if !ct_eq_bytes(&self.issuer_pk_digest, &expected_oprf_pk.commitment()) {
            return false;
        }
        if self.issuer_mldsa_pk.len() != expected_issuer_mldsa_pk.len()
            || !ct_eq_bytes(&self.issuer_mldsa_pk, expected_issuer_mldsa_pk)
        {
            return false;
        }
        if self.accumulator_root.iter().any(|&x| !gl_is_canonical(x)) {
            return false;
        }
        let expected_tag = compute_accumulator_root_tag(
            &self.issuer_pk_digest,
            self.issuer_epoch,
            &self.accumulator_root,
        );
        if !ct_eq_bytes(&self.root_tag, &expected_tag) {
            return false;
        }
        let msg = Self::signing_message(
            &self.issuer_pk_digest,
            self.issuer_epoch,
            &self.accumulator_root,
            &self.root_tag,
        );
        ml_dsa_verify(
            self.mldsa_level,
            expected_issuer_mldsa_pk,
            &msg,
            Self::SIGNING_CONTEXT,
            &self.mldsa_signature,
        )
    }
}

/// Holder-local authorization path; contains no other holders' leaves or tokens.
/// The token and the path are erased on drop, `Debug` does not print them, and
/// equality compares the token without data-dependent timing.
#[derive(Clone)]
pub struct CredentialMembershipWitness {
    pub leaf_index: usize,
    pub siblings: [[u64; 6]; VC_ACCUMULATOR_DEPTH],
    pub accumulator_root: [u64; 6],
    pub issuer_epoch: u64,
    pub issuer_pk_digest: [u8; 32],
    pub issuance_token: Option<[u8; 32]>,
}

/// Equality of optional issuance tokens. Whether a token is present is public
/// (it distinguishes test enrolment from issued credentials); its bytes are not.
pub(super) fn ct_eq_optional_token(a: &Option<[u8; 32]>, b: &Option<[u8; 32]>) -> bool {
    match (a, b) {
        (Some(a), Some(b)) => ct_eq_bytes(a, b),
        (None, None) => true,
        _ => false,
    }
}

impl PartialEq for CredentialMembershipWitness {
    fn eq(&self, other: &Self) -> bool {
        let public = (self.leaf_index == other.leaf_index)
            & (self.siblings == other.siblings)
            & (self.accumulator_root == other.accumulator_root)
            & (self.issuer_epoch == other.issuer_epoch)
            & (self.issuer_pk_digest == other.issuer_pk_digest);
        ct_eq_optional_token(&self.issuance_token, &other.issuance_token) & public
    }
}

impl Eq for CredentialMembershipWitness {}

impl CredentialMembershipWitness {
    pub(super) fn erase_secrets(&mut self) {
        self.issuance_token.secret_wipe();
        self.siblings.secret_wipe();
    }
}

impl Drop for CredentialMembershipWitness {
    fn drop(&mut self) {
        self.erase_secrets();
    }
}

impl fmt::Debug for CredentialMembershipWitness {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CredentialMembershipWitness")
            .field("leaf_index", &self.leaf_index)
            .field("accumulator_root", &self.accumulator_root)
            .field("issuer_epoch", &self.issuer_epoch)
            .field("issuer_pk_digest", &self.issuer_pk_digest)
            .field("siblings", &"<REDACTED>")
            .field("issuance_token", &"<REDACTED>")
            .finish()
    }
}

/// Authoritative issuer accumulator of OPRF-issued credential commitments.
///
/// It holds every holder's issuance token (`enrolled_tokens`, needed to hand
/// out membership witnesses). They are erased on drop, grown without leaving
/// copies in freed heap blocks, never printed by `Debug`, and compared without
/// data-dependent timing. The duplicate-issuance index stores a digest of
/// `(attr_commit, token)`, not the token.
#[derive(Clone)]
pub struct IssuerCredentialAccumulator {
    pub oprf_key: PublicKey,
    pub issuer_epoch: u64,
    pub(super) leaves: Vec<[u64; 6]>,
    pub(super) enrolled_tokens: Vec<Option<[u8; 32]>>,
    consumed_sessions: BTreeSet<[u8; 32]>,
    pub(super) issued_tokens: BTreeSet<[u8; 32]>,
    layers: Vec<Vec<[u64; 6]>>,
    pub(super) empty: Vec<[u64; 6]>,
}

impl PartialEq for IssuerCredentialAccumulator {
    fn eq(&self, other: &Self) -> bool {
        let public = (self.oprf_key == other.oprf_key)
            & (self.issuer_epoch == other.issuer_epoch)
            & (self.leaves == other.leaves)
            & (self.consumed_sessions == other.consumed_sessions)
            & (self.issued_tokens == other.issued_tokens)
            & (self.layers == other.layers)
            & (self.empty == other.empty)
            & (self.enrolled_tokens.len() == other.enrolled_tokens.len());
        let tokens = self
            .enrolled_tokens
            .iter()
            .zip(&other.enrolled_tokens)
            .fold(true, |acc, (a, b)| acc & ct_eq_optional_token(a, b));
        tokens & public
    }
}

impl Eq for IssuerCredentialAccumulator {}

impl Drop for IssuerCredentialAccumulator {
    fn drop(&mut self) {
        self.erase_secrets();
    }
}

impl fmt::Debug for IssuerCredentialAccumulator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("IssuerCredentialAccumulator")
            .field("oprf_key", &self.oprf_key)
            .field("issuer_epoch", &self.issuer_epoch)
            .field("leaves", &self.leaves.len())
            .field("root", &self.root())
            .field("enrolled_tokens", &"<REDACTED>")
            .finish()
    }
}

/// Index key of an issued `(attr_commit, token)` pair: a one-way digest, so the
/// duplicate-issuance set holds no token.
pub(super) fn issued_token_index(attr_commit: &[u64; 6], issuance_token: &[u8; 32]) -> [u8; 32] {
    let mut commit_bytes = [0u8; 48];
    for (chunk, limb) in commit_bytes
        .as_chunks_mut::<8>()
        .0
        .iter_mut()
        .zip(attr_commit)
    {
        *chunk = limb.to_le_bytes();
    }
    cshake256_framed_32(
        b"QSAG.VC.ISSUED_TOKEN_INDEX.V1",
        &[&commit_bytes, issuance_token],
    )
}

impl IssuerCredentialAccumulator {
    pub const CAPACITY: usize = 1 << VC_ACCUMULATOR_DEPTH;

    pub(super) fn erase_secrets(&mut self) {
        self.enrolled_tokens.secret_wipe();
    }

    pub fn new(oprf_key: PublicKey, issuer_epoch: u64) -> Self {
        let empty_leaf = [
            gl_reduce_u64(0x454D_5054_595F_4C30),
            gl_reduce_u64(0x454D_5054_595F_4C31),
            (issuer_epoch & 0xffff_ffff),
            issuer_epoch >> 32,
            0,
            0,
        ];
        let mut empty = vec![empty_leaf];
        for level in 0..VC_ACCUMULATOR_DEPTH {
            empty.push(merkle_hash_pair(
                &empty[level],
                &empty[level],
                issuer_epoch,
                level as u32,
            ));
        }
        Self {
            oprf_key,
            issuer_epoch,
            leaves: Vec::new(),
            enrolled_tokens: Vec::new(),
            consumed_sessions: BTreeSet::new(),
            issued_tokens: BTreeSet::new(),
            layers: vec![Vec::new(); VC_ACCUMULATOR_DEPTH + 1],
            empty,
        }
    }

    #[cfg(test)]
    pub(super) fn enroll(&mut self, attr_commit: [u64; 6]) -> Result<usize, BlindVcError> {
        if self.leaves.len() >= Self::CAPACITY {
            return Err(BlindVcError::AccumulatorFull);
        }
        let idx = self.leaves.len();
        self.leaves.push(attr_commit);
        self.append_merkle_leaf(attr_commit);
        secret_vec_push(&mut self.enrolled_tokens, None);
        Ok(idx)
    }

    pub(super) fn enroll_issued(
        &mut self,
        session_id: [u8; 32],
        attr_commit: [u64; 6],
        issuance_token: [u8; 32],
    ) -> Result<usize, BlindVcError> {
        let token_index = issued_token_index(&attr_commit, &issuance_token);
        if self.consumed_sessions.contains(&session_id) || self.issued_tokens.contains(&token_index)
        {
            return Err(BlindVcError::InvalidOprfEvaluation);
        }
        if self.leaves.len() >= Self::CAPACITY {
            return Err(BlindVcError::AccumulatorFull);
        }
        let idx = self.leaves.len();
        self.leaves.push(attr_commit);
        self.append_merkle_leaf(attr_commit);
        secret_vec_push(&mut self.enrolled_tokens, Some(issuance_token));
        self.consumed_sessions.insert(session_id);
        self.issued_tokens.insert(token_index);
        Ok(idx)
    }

    pub fn root_tag(&self) -> [u8; 32] {
        compute_accumulator_root_tag(&self.oprf_key.commitment(), self.issuer_epoch, &self.root())
    }

    /// Produce an authenticated [`IssuerRootAttestation`] over `(oprf_key, issuer_epoch, root())`
    /// using an arbitrary FIPS 204 `ML-DSA` signer (single-party or threshold MPC).
    pub fn attest_root<F>(
        &self,
        mldsa_level: MlDsaLevel,
        issuer_mldsa_pk: Vec<u8>,
        sign_fn: F,
    ) -> Result<IssuerRootAttestation, BlindVcError>
    where
        F: FnOnce(&[u8], &[u8]) -> Result<Vec<u8>, BlindVcError>,
    {
        let issuer_pk_digest = self.oprf_key.commitment();
        let accumulator_root = self.root();
        let root_tag =
            compute_accumulator_root_tag(&issuer_pk_digest, self.issuer_epoch, &accumulator_root);
        let msg = IssuerRootAttestation::signing_message(
            &issuer_pk_digest,
            self.issuer_epoch,
            &accumulator_root,
            &root_tag,
        );
        let mldsa_signature = sign_fn(&msg, IssuerRootAttestation::SIGNING_CONTEXT)?;
        let attestation = IssuerRootAttestation {
            issuer_pk_digest,
            mldsa_level,
            issuer_mldsa_pk,
            issuer_epoch: self.issuer_epoch,
            accumulator_root,
            root_tag,
            mldsa_signature,
        };
        if !attestation.verify(&attestation.issuer_mldsa_pk, &self.oprf_key) {
            return Err(BlindVcError::RootAttestationFailed);
        }
        Ok(attestation)
    }

    /// Convenience deterministic FIPS 204 `ML-DSA` attestation for single-key or test issuers.
    pub fn attest_root_deterministic(
        &self,
        mldsa_level: MlDsaLevel,
        issuer_mldsa_sk: &MlDsaSigningKey,
        issuer_mldsa_pk: Vec<u8>,
    ) -> Result<IssuerRootAttestation, BlindVcError> {
        self.attest_root(mldsa_level, issuer_mldsa_pk, |msg, ctx| {
            ml_dsa_sign_deterministic(issuer_mldsa_sk, msg, ctx)
                .ok_or(BlindVcError::RootAttestationFailed)
        })
    }

    // Only the new leaf's ancestors change. Cached layers also serve historical
    // membership paths without rebuilding or cloning the complete tree.
    fn append_merkle_leaf(&mut self, leaf: [u64; 6]) {
        let mut index = self.layers[0].len();
        self.layers[0].push(leaf);
        for level in 0..VC_ACCUMULATOR_DEPTH {
            let nodes = &self.layers[level];
            let parent = merkle_hash_pair(
                &nodes[index & !1],
                nodes.get((index & !1) + 1).unwrap_or(&self.empty[level]),
                self.issuer_epoch,
                level as u32,
            );
            index >>= 1;
            let next = &mut self.layers[level + 1];
            if index == next.len() {
                next.push(parent);
            } else {
                next[index] = parent;
            }
        }
    }

    pub fn root(&self) -> [u64; 6] {
        self.layers[VC_ACCUMULATOR_DEPTH]
            .first()
            .copied()
            .unwrap_or(self.empty[VC_ACCUMULATOR_DEPTH])
    }

    pub fn membership_witness(
        &self,
        leaf_index: usize,
    ) -> Result<CredentialMembershipWitness, BlindVcError> {
        Ok(CredentialMembershipWitness {
            leaf_index,
            siblings: self.merkle_path(leaf_index)?,
            accumulator_root: self.root(),
            issuer_epoch: self.issuer_epoch,
            issuer_pk_digest: self.oprf_key.commitment(),
            issuance_token: self.enrolled_tokens[leaf_index],
        })
    }

    pub fn merkle_path(
        &self,
        leaf_index: usize,
    ) -> Result<[[u64; 6]; VC_ACCUMULATOR_DEPTH], BlindVcError> {
        if leaf_index >= self.leaves.len() {
            return Err(BlindVcError::InvalidAccumulatorLeafIndex);
        }
        Ok(core::array::from_fn(|level| {
            self.layers[level]
                .get((leaf_index >> level) ^ 1)
                .copied()
                .unwrap_or(self.empty[level])
        }))
    }
}

/// Canonical input to the TOPRF, binding epoch, schema, blinded leaf, issuer key digest, and session.
pub fn issuance_input(req: &BlindIssuanceRequest) -> [u8; 136] {
    encode_issuance_message(
        req.issuer_epoch,
        req.schema_id,
        &req.attr_commit,
        &req.issuer_pk_digest,
        &req.session_id,
    )
}
/// Enroll an issuer-authorized request after obtaining its OPRF evaluation over
/// authenticated server channels. The issuer's independently provisioned receipt
/// key authenticates the evaluation before any accumulator mutation.
pub fn threshold_issue_blind_vc(
    accumulator: &mut IssuerCredentialAccumulator,
    req: &BlindIssuanceRequest,
    issuer_attested_attrs: &[u64],
    evaluation: &Evaluation,
    receipt_key: &crate::voprf::IssuanceReceiptKey,
    expected_schema_id: u64,
) -> Result<BlindVerifiableCredential, BlindVcError> {
    threshold_issue_blind_vc_with_profile(
        accumulator,
        req,
        issuer_attested_attrs,
        evaluation,
        receipt_key,
        expected_schema_id,
        ZkSoundnessProfile::Quantum128,
    )
}

/// Use an explicit verifier-selected soundness budget.
#[allow(clippy::too_many_arguments)]
pub fn threshold_issue_blind_vc_with_profile(
    accumulator: &mut IssuerCredentialAccumulator,
    req: &BlindIssuanceRequest,
    issuer_attested_attrs: &[u64],
    evaluation: &Evaluation,
    receipt_key: &crate::voprf::IssuanceReceiptKey,
    expected_schema_id: u64,
    profile: ZkSoundnessProfile,
) -> Result<BlindVerifiableCredential, BlindVcError> {
    if req.issuer_epoch != accumulator.issuer_epoch
        || !ct_eq_bytes(&req.issuer_pk_digest, &accumulator.oprf_key.commitment())
        || !verify_blind_issuance_request_with_profile(
            req,
            issuer_attested_attrs,
            expected_schema_id,
            profile,
        )
    {
        return Err(BlindVcError::BlindIssuanceProofInvalid);
    }
    let issuance_token = evaluation
        .authenticated_value_for(&accumulator.oprf_key, &issuance_input(req), receipt_key)
        .ok_or(BlindVcError::InvalidOprfEvaluation)?;
    if ct_eq_bytes(&issuance_token, &[0u8; 32]) {
        return Err(BlindVcError::InvalidOprfEvaluation);
    }
    let accumulator_leaf_index =
        accumulator.enroll_issued(req.session_id, req.attr_commit, issuance_token)?;
    Ok(BlindVerifiableCredential {
        issuer_epoch: accumulator.issuer_epoch,
        schema_id: req.schema_id,
        attr_commit: req.attr_commit,
        issuance_token,
        accumulator_leaf_index,
    })
}
