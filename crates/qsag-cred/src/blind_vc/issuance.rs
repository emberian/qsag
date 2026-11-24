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
