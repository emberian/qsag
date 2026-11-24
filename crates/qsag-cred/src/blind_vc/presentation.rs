use super::*;

// ============================================================================
// Phase 3: Unlinkable Selective-Disclosure Presentation (`prove_selective_disclosure`)
// ============================================================================

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PresentationMode {
    UnlinkableFresh,
    ScopedPseudonym([u8; 32]),
}

pub(super) fn presentation_scope(
    scope: &[u8],
    challenge: &[u8; 32],
    nonce: &[u8; 32],
    mode: PresentationMode,
) -> [u64; 4] {
    let domain = match mode {
        PresentationMode::UnlinkableFresh => {
            cshake256_framed_32(b"QSAG.VC.FRESH.V1", &[scope, challenge, nonce])
        }
        PresentationMode::ScopedPseudonym(id) => {
            cshake256_framed_32(b"QSAG.VC.SCOPED.V1", &[scope, &id])
        }
    };
    hash_verifier_scope_to_limbs(&domain)
}

/// Last-party (`party = 255`) additive offset bundle included iff `hidden_party != 255`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LimboPartyAux {
    pub delta_w: Vec<u64>,
    pub delta_z: Vec<u64>,
    pub delta_c: [u64; 5],
}

/// Opened `N = 256` seed-tree + polynomial-multiplication-check repetition (`~285 KiB`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpenedLimboRepetition {
    pub hidden_party: u8,
    pub ggm_copath: [[u8; 32]; VC_SD_GGM_DEPTH],
    pub com_1_hidden: [u8; 32],
    pub aux: Option<LimboPartyAux>,
    pub r_poly_without_b: Vec<[u64; 5]>,
    pub alpha: Vec<[u64; 5]>,
    pub beta: Vec<[u64; 5]>,
}

/// Unlinkable selective-disclosure presentation (`0` `attr_commit`, `0` `leaf_idx`, `0` `issuance_token`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SelectiveDisclosurePresentation {
    pub arity: usize,
    pub verifier_challenge: [u8; 32],
    pub mode: PresentationMode,
    pub presentation_nonce: [u8; 32],
    pub issuer_epoch: u64,
    pub schema_id: u64,
    pub accumulator_root: [u64; 6],
    /// Domain-separated commitment tag binding `(issuer_pk_digest, issuer_epoch, accumulator_root)`.
    pub issuer_root_tag: [u8; 32],
    pub verifier_scope_limbs: [u64; 4],
    /// Sorted `(attr_index, disclosed_value)` pairs.
    pub disclosed_attrs: Vec<(usize, u64)>,
    /// Fresh per-presentation rerandomized commitment `Poseidon2(attrs, pres_blind)`.
    pub pres_commit: [u64; 6],
    /// Scope-bound pseudonym/nullifier `Poseidon2(holder_blind, verifier_scope_limbs)`.
    pub scope_tag: [u64; 6],
    pub opened_reps: Vec<OpenedLimboRepetition>,
}

/// The public statement of a selective-disclosure proof.
pub(super) struct SdInstance<'a> {
    arity: usize,
    presentation_nonce: &'a [u8; 32],
    issuer_epoch: u64,
    schema_id: u64,
    accumulator_root: &'a [u64; 6],
    issuer_root_tag: &'a [u8; 32],
    verifier_scope_limbs: &'a [u64; 4],
    disclosed_attrs: &'a [(usize, u64)],
    pres_commit: &'a [u64; 6],
    scope_tag: &'a [u64; 6],
}

pub(super) fn serialize_sd_instance(instance: &SdInstance<'_>) -> Vec<u8> {
    let SdInstance {
        arity,
        presentation_nonce,
        issuer_epoch,
        schema_id,
        accumulator_root,
        issuer_root_tag,
        verifier_scope_limbs,
        disclosed_attrs,
        pres_commit,
        scope_tag,
    } = *instance;
    let mut out = Vec::with_capacity(256);
    out.extend_from_slice(&(arity as u64).to_le_bytes());
    out.extend_from_slice(presentation_nonce);
    out.extend_from_slice(&issuer_epoch.to_le_bytes());
    out.extend_from_slice(&schema_id.to_le_bytes());
    out.extend_from_slice(issuer_root_tag);
    for &x in accumulator_root
        .iter()
        .chain(verifier_scope_limbs.iter())
        .chain(pres_commit.iter())
        .chain(scope_tag.iter())
    {
        out.extend_from_slice(&x.to_le_bytes());
    }
    out.extend_from_slice(&(disclosed_attrs.len() as u32).to_le_bytes());
    for &(idx, val) in disclosed_attrs {
        out.extend_from_slice(&(idx as u32).to_le_bytes());
        out.extend_from_slice(&val.to_le_bytes());
    }
    out
}

/// What the verifier asked for: its scope, its fresh challenge (from
/// [`VerifierChallengeLedger::issue`] or the durable ledger), and whether
/// presentations to it may be linked.
pub struct PresentationRequest<'a> {
    pub verifier_scope: &'a [u8],
    pub verifier_challenge: &'a [u8; 32],
    pub mode: PresentationMode,
}

/// Generate a selective-disclosure ZK presentation revealing only `disclosed_indices`.
///
/// `presentation_entropy` must be 32 fresh private random bytes for each call,
/// including retries. Reusing both entropy and a request repeats the proof;
/// statement hedging protects distinct statements, not identical requests.
/// Challenges are not blacklisted: see [`HolderCredentialSecret`].
pub fn prove_selective_disclosure(
    cred: &BlindVerifiableCredential,
    holder_secret: &HolderCredentialSecret,
    membership: &CredentialMembershipWitness,
    disclosed_indices: &[usize],
    request: PresentationRequest<'_>,
    presentation_entropy: [u8; 32],
) -> Result<SelectiveDisclosurePresentation, BlindVcError> {
    prove_selective_disclosure_with_profile(
        cred,
        holder_secret,
        membership,
        disclosed_indices,
        request,
        presentation_entropy,
        ZkSoundnessProfile::Quantum128,
    )
}

/// Generate a selective-disclosure presentation under an explicit soundness profile.
/// The fresh-private-entropy contract of [`prove_selective_disclosure`] applies.
#[allow(clippy::too_many_arguments)]
pub fn prove_selective_disclosure_with_profile(
    cred: &BlindVerifiableCredential,
    holder_secret: &HolderCredentialSecret,
    membership: &CredentialMembershipWitness,
    disclosed_indices: &[usize],
    request: PresentationRequest<'_>,
    presentation_entropy: [u8; 32],
    profile: ZkSoundnessProfile,
) -> Result<SelectiveDisclosurePresentation, BlindVcError> {
    let mut ent = SecretBuffer(presentation_entropy);
    let PresentationRequest {
        verifier_scope,
        verifier_challenge,
        mode,
    } = request;
    let mut sorted_idx = disclosed_indices.to_vec();
    sorted_idx.sort_unstable();
    for (pos, &idx) in sorted_idx.iter().enumerate() {
        if idx >= holder_secret.arity {
            return Err(BlindVcError::InvalidDisclosedAttributeIndex { index: idx });
        }
        if pos > 0 && sorted_idx[pos - 1] == idx {
            return Err(BlindVcError::DuplicateDisclosedAttributeIndex { index: idx });
        }
    }

    if cred.issuer_epoch != membership.issuer_epoch || cred.schema_id != holder_secret.schema_id {
        return Err(BlindVcError::CredentialBindingMismatch);
    }
    let expected_attr_commit = compute_vc_poseidon2_commit(
        holder_secret.schema_id,
        &holder_secret.attrs[..holder_secret.arity],
        &holder_secret.holder_blind,
        VC_ATTR_COMMIT_TAG,
    )?;
    if cred.attr_commit != expected_attr_commit
        || membership.leaf_index != cred.accumulator_leaf_index
        || membership.leaf_index >= IssuerCredentialAccumulator::CAPACITY
    {
        return Err(BlindVcError::CredentialBindingMismatch);
    }
    if let Some(expected_tok) = &membership.issuance_token
        && !ct_eq_bytes(&cred.issuance_token, expected_tok)
    {
        return Err(BlindVcError::CredentialBindingMismatch);
    }

    let siblings = membership.siblings;
    let accumulator_root = membership.accumulator_root;
    if siblings
        .iter()
        .flatten()
        .chain(accumulator_root.iter())
        .any(|&v| !gl_is_canonical(v))
    {
        return Err(BlindVcError::CredentialBindingMismatch);
    }
    let mut node = cred.attr_commit;
    for (level, sibling) in siblings.iter().enumerate() {
        node = if (membership.leaf_index >> level) & 1 == 0 {
            merkle_hash_pair(&node, sibling, cred.issuer_epoch, level as u32)
        } else {
            merkle_hash_pair(sibling, &node, cred.issuer_epoch, level as u32)
        };
    }
    if node != accumulator_root {
        return Err(BlindVcError::CredentialBindingMismatch);
    }
    let issuer_root_tag = compute_accumulator_root_tag(
        &membership.issuer_pk_digest,
        cred.issuer_epoch,
        &accumulator_root,
    );

    let mut nonce_bind = Vec::with_capacity(64 + sorted_idx.len() * 12);
    nonce_bind.extend_from_slice(&cred.issuer_epoch.to_le_bytes());
    nonce_bind.extend_from_slice(&cred.schema_id.to_le_bytes());
    nonce_bind.extend_from_slice(&issuer_root_tag);
    match mode {
        PresentationMode::UnlinkableFresh => nonce_bind.push(0),
        PresentationMode::ScopedPseudonym(id) => {
            nonce_bind.push(1);
            nonce_bind.extend_from_slice(&id);
        }
    }
    nonce_bind.extend_from_slice(&(sorted_idx.len() as u32).to_le_bytes());
    for &idx in &sorted_idx {
        nonce_bind.extend_from_slice(&(idx as u32).to_le_bytes());
        nonce_bind.extend_from_slice(&holder_secret.attrs[idx].to_le_bytes());
    }
    let presentation_nonce = cshake256_framed_32(
        b"QSAG.VC.PRES_NONCE.V1",
        &[&ent[..], verifier_scope, verifier_challenge, &nonce_bind],
    );
    let verifier_scope_limbs = presentation_scope(
        verifier_scope,
        verifier_challenge,
        &presentation_nonce,
        mode,
    );
    let pres_blind_vec =
        sample_canonical_gl_vec(b"QSAG.VC.PRES_BLIND.V1", &ent, &presentation_nonce, 4);
    let mut pres_blind = [
        pres_blind_vec[0],
        pres_blind_vec[1],
        pres_blind_vec[2],
        pres_blind_vec[3],
    ];
    drop(pres_blind_vec);

    let pres_commit = match compute_vc_poseidon2_commit(
        cred.schema_id,
        &holder_secret.attrs[..holder_secret.arity],
        &pres_blind,
        VC_PRES_COMMIT_TAG,
    ) {
        Ok(commit) => commit,
        Err(err) => {
            ct_zeroize_u64s(&mut pres_blind);
            ct_zeroize_bytes(&mut ent[..]);
            return Err(err);
        }
    };
    let scope_tag = compute_vc_scope_tag(
        cred.schema_id,
        &holder_secret.holder_blind,
        &verifier_scope_limbs,
    );

    let disclosed_attrs: Vec<(usize, u64)> = sorted_idx
        .iter()
        .map(|&idx| (idx, holder_secret.attrs[idx]))
        .collect();

    let mut secret_vals = SecretBuffer(Vec::with_capacity(
        MAX_VC_ATTRS + 8 + 7 * VC_ACCUMULATOR_DEPTH,
    ));
    for (attr_i, &attr_val) in holder_secret.attrs[..holder_secret.arity]
        .iter()
        .enumerate()
    {
        if !sorted_idx.contains(&attr_i) {
            secret_vals.0.push(attr_val);
        }
    }
    secret_vals.0.extend_from_slice(&holder_secret.holder_blind);
    secret_vals.0.extend_from_slice(&pres_blind);
    ct_zeroize_u64s(&mut pres_blind);
    for lvl in 0..VC_ACCUMULATOR_DEPTH {
        secret_vals
            .0
            .push(((cred.accumulator_leaf_index >> lvl) & 1) as u64);
    }
    for sib in &siblings {
        secret_vals.0.extend_from_slice(sib);
    }
    let num_secret_wires = secret_vals.len();

    let mut expected_final_outs = [0u64; VC_FINAL_OUTPUTS];
    expected_final_outs[0..6].copy_from_slice(&accumulator_root);
    expected_final_outs[6..12].copy_from_slice(&pres_commit);
    expected_final_outs[12..18].copy_from_slice(&scope_tag);

    let trace = eval_sd_plaintext_circuit(
        holder_secret.arity,
        cred.issuer_epoch,
        cred.schema_id,
        &verifier_scope_limbs,
        &disclosed_attrs,
        &expected_final_outs,
        &secret_vals,
    );
    if trace.final_outs != expected_final_outs {
        ct_zeroize_bytes(&mut ent[..]);
        return Err(BlindVcError::CredentialBindingMismatch);
    }

    let profile_tag: &[u8] = match profile {
        ZkSoundnessProfile::Classical128 => b"QSAG.VC.SD.LIMBO256.Classical128:17",
        ZkSoundnessProfile::Quantum128 => b"QSAG.VC.SD.LIMBO256.Quantum128:33",
    };

    let mut inst_bytes = serialize_sd_instance(&SdInstance {
        arity: holder_secret.arity,
        presentation_nonce: &presentation_nonce,
        issuer_epoch: cred.issuer_epoch,
        schema_id: cred.schema_id,
        accumulator_root: &accumulator_root,
        issuer_root_tag: &issuer_root_tag,
        verifier_scope_limbs: &verifier_scope_limbs,
        disclosed_attrs: &disclosed_attrs,
        pres_commit: &pres_commit,
        scope_tag: &scope_tag,
    });
    inst_bytes.extend_from_slice(verifier_challenge);
    inst_bytes.extend_from_slice(profile_tag);

    let statement_digest = cshake256_framed_32(b"QSAG.VC.SD_STMT_DIGEST.V2", &[&inst_bytes]);
    let mut hedged_zk_seed = SecretBuffer(cshake256_framed_32(
        b"QSAG.VC.SD_ZK_SEED.V2",
        &[&statement_digest, &ent[..]],
    ));
    ct_zeroize_bytes(&mut ent[..]);

    let mut tr = InterleavedTranscript::new(b"QSAG.BLIND_VC.SD_LIMBO.V1", &inst_bytes);
    tr.absorb(b"VC_SOUNDNESS_PROFILE", profile_tag);

    let tau = profile.sd_repetitions();
    let total_party_limbs = PARTY_EXT_LIMBS + num_secret_wires + SD_TOTAL_GATES;

    struct R1RepState {
        ggm_tree: SecretBuffer<Vec<[u8; 32]>>,
        com_1: Vec<[u8; 32]>,
        delta_w: SecretBuffer<Vec<u64>>,
        delta_z: SecretBuffer<Vec<u64>>,
        delta_c: Fp5,
        u_sum: SecretBuffer<Vec<Fp5>>,
        v_sum: SecretBuffer<Vec<Fp5>>,
        c_plain: Fp5,
        m_sum: SecretBuffer<Vec<Fp5>>,
    }

    // Box::new only moves small headers and two field elements, even without optimization.
    const _: () = assert!(core::mem::size_of::<R1RepState>() < 256);

    impl R1RepState {
        fn zeroed(num_secret_wires: usize) -> Self {
            Self {
                ggm_tree: SecretBuffer(vec![[0u8; 32]; 2 * VC_SD_LIMBO_PARTIES]),
                com_1: vec![[0u8; 32]; VC_SD_LIMBO_PARTIES],
                delta_w: SecretBuffer(Vec::with_capacity(num_secret_wires)),
                delta_z: SecretBuffer(Vec::with_capacity(SD_TOTAL_GATES)),
                delta_c: Fp5::ZERO,
                u_sum: SecretBuffer(vec![Fp5::ZERO; SD_GRID_L]),
                v_sum: SecretBuffer(vec![Fp5::ZERO; SD_GRID_L]),
                c_plain: Fp5::ZERO,
                m_sum: SecretBuffer(vec![Fp5::ZERO; SD_RPOLY_COEFFS]),
            }
        }
    }

    impl Drop for R1RepState {
        fn drop(&mut self) {
            self.delta_c.secret_wipe();
            self.c_plain.secret_wipe();
        }
    }

    // Round 1 (parallel across repetitions): expand GGM trees in place on the heap, stream
    // 8-party SIMD tapes, accumulate mask sums, compute Party 255 `aux`, and commit all 256 parties
    // without materializing 25+ KiB of secret seeds/masks on worker stacks.
    let r1_reps: Vec<alloc::boxed::Box<R1RepState>> = parallel_map_indexed(tau, |rep| {
        let rep_u32 = rep as u32;
        let mut state = alloc::boxed::Box::new(R1RepState::zeroed(num_secret_wires));
        let root_seed = SecretBuffer(cshake256_framed_32(
            b"QSAG.VC.SD_GGM_ROOT.V1",
            &[
                &statement_digest,
                &hedged_zk_seed[..],
                &presentation_nonce,
                &rep_u32.to_le_bytes(),
            ],
        ));
        expand_ggm_tree_256_into(
            &root_seed,
            &presentation_nonce,
            rep_u32,
            &mut state.ggm_tree.0,
        );

        let mut c_pad_sum = SecretBuffer(Fp5::ZERO);
        let mut w_mask_sum = SecretBuffer(vec![0u64; num_secret_wires]);
        let mut z_mask_sum = SecretBuffer(vec![0u64; SD_TOTAL_GATES]);
        let mut salt_255 = [0u8; 32];

        let mut batch_tapes = SecretBuffer(core::array::from_fn::<_, 8, _>(|_| {
            Vec::<u64>::with_capacity(total_party_limbs)
        }));
        for batch in 0..(VC_SD_LIMBO_PARTIES / 8) {
            let base_p = batch * 8;
            let seeds_8 = SecretBuffer(core::array::from_fn::<_, 8, _>(|lane| {
                state.ggm_tree.0[VC_SD_LIMBO_PARTIES + base_p + lane]
            }));
            let mut prg = Shake256PartyBatch8::new(&presentation_nonce, rep_u32, base_p, &seeds_8);
            let salts = prg.extract_salts_1();
            prg.squeeze_canonical_gl([true; 8], &mut batch_tapes, total_party_limbs);

            for (lane, tape) in batch_tapes.iter_mut().enumerate() {
                let p = base_p + lane;
                let party_masks = SecretBuffer(unpack_party_ext_masks(&tape[..PARTY_EXT_LIMBS]));
                let (u_p, v_p, c_p, m_p) = &*party_masks;
                for ((u_acc, v_acc), (&u_val, &v_val)) in state
                    .u_sum
                    .0
                    .iter_mut()
                    .zip(state.v_sum.0.iter_mut())
                    .zip(u_p.iter().zip(v_p.iter()))
                {
                    *u_acc = u_acc.add(u_val);
                    *v_acc = v_acc.add(v_val);
                }
                *c_pad_sum = c_pad_sum.add(*c_p);
                for (m_acc, &m_val) in state.m_sum.0.iter_mut().zip(m_p.iter()) {
                    *m_acc = m_acc.add(m_val);
                }
                let w_slice = &tape[PARTY_EXT_LIMBS..PARTY_EXT_LIMBS + num_secret_wires];
                for (acc, &wv) in w_mask_sum.0.iter_mut().zip(w_slice) {
                    *acc = gl_add(*acc, wv);
                }
                let z_slice = &tape[PARTY_EXT_LIMBS + num_secret_wires..];
                for (acc, &zv) in z_mask_sum.0.iter_mut().zip(z_slice) {
                    *acc = gl_add(*acc, zv);
                }
                if p < VC_SD_LIMBO_PARTIES - 1 {
                    state.com_1[p] = commit_limbo_party_r1(
                        &presentation_nonce,
                        rep_u32,
                        p as u16,
                        &seeds_8[lane],
                        None,
                        &salts[lane],
                    );
                } else {
                    salt_255 = salts[lane];
                }
                ct_zeroize_u64s(tape);
            }
        }

        for k in 0..num_secret_wires {
            state.delta_w.0.push(gl_sub(secret_vals[k], w_mask_sum[k]));
        }
        for g in 0..SD_TOTAL_GATES {
            state.delta_z.0.push(gl_sub(trace.z[g], z_mask_sum[g]));
        }
        for l in 0..SD_GRID_L {
            state.c_plain = state.c_plain.add(state.u_sum.0[l].mul(state.v_sum.0[l]));
        }
        state.delta_c = state.c_plain.sub(*c_pad_sum);

        let aux_digest =
            digest_limbo_aux(&state.delta_w, &state.delta_z, &state.delta_c.to_limbs());
        state.com_1[VC_SD_LIMBO_PARTIES - 1] = commit_limbo_party_r1(
            &presentation_nonce,
            rep_u32,
            (VC_SD_LIMBO_PARTIES - 1) as u16,
            &state.ggm_tree.0[VC_SD_LIMBO_PARTIES + VC_SD_LIMBO_PARTIES - 1],
            Some(&aux_digest),
            &salt_255,
        );
        ct_zeroize_bytes(&mut salt_255);

        state
    });

    ct_zeroize_bytes(&mut hedged_zk_seed[..]);
    drop(secret_vals);

    let mut r1_bundle = Vec::with_capacity(tau * VC_SD_LIMBO_PARTIES * 32);
    for r1 in &r1_reps {
        for c in &r1.com_1 {
            r1_bundle.extend_from_slice(c);
        }
    }
    tr.absorb(b"VC_SD_LIMBO_R1_COMS", &r1_bundle);
    drop(r1_bundle);

    // Round 2a: squeeze folding challenge seed and compute masked polynomial R~(X) (degree <= 2B, coeff B == 0).
    let mut gamma_seed = [0u8; 32];
    tr.squeeze_bytes(b"VC_SD_LIMBO_GAMMA", &mut gamma_seed);

    type R2aPolyRep = ([Fp5; SD_GRID_B], [Fp5; SD_GRID_L], Vec<[u64; 5]>);
    let r2a_polys: Vec<R2aPolyRep> = parallel_map_indexed(tau, |rep| {
        let r1 = &r1_reps[rep];
        let (theta, eta) = expand_gamma_weights(&gamma_seed, rep as u32);
        const MASK64: u128 = 0xffff_ffff_ffff_ffff;
        let mut poly_lo = SecretBuffer([[0u128; 5]; 2 * SD_GRID_B + 1]);
        let mut poly_hi = SecretBuffer([[0u128; 5]; 2 * SD_GRID_B + 1]);
        let mut poly_v = SecretBuffer([Fp5::ZERO; 2 * SD_GRID_B + 1]);

        for (l, &eta_l) in eta.iter().enumerate() {
            // P_l(X) = u_l + sum_{b=0}^{B-1} (theta_b * eta_l * x_{b,l}) * X^{b+1}
            // Q_l(X) = sum_{k=0}^{B-1} y_{B-1-k, l} * X^k + v_l * X^B
            let mut p_coeffs = SecretBuffer([Fp5::ZERO; SD_GRID_B + 1]);
            p_coeffs[0] = r1.u_sum[l];
            for (b, &theta_b) in theta.iter().enumerate() {
                let xv = trace.x[b * SD_GRID_L + l];
                if xv != 0 {
                    p_coeffs[b + 1] = theta_b.mul(eta_l).scale_fp(xv);
                }
            }
            let mut y_col = SecretBuffer([0u128; SD_GRID_B]);
            for (k, y_slot) in y_col.iter_mut().enumerate() {
                *y_slot = trace.y[(SD_GRID_B - 1 - k) * SD_GRID_L + l] as u128;
            }
            let v_l = r1.v_sum[l];
            for (j, &pj) in p_coeffs.iter().enumerate() {
                if pj.is_zero() {
                    continue;
                }
                let pj_u128 = pj.to_wide_limbs();
                // Degrees k in 0..B have scalar GF(p) coefficients y_{B-1-k, l}
                for (k, &yv) in y_col.iter().enumerate() {
                    if yv != 0 {
                        let dst = j + k;
                        for c in 0..5 {
                            let p = pj_u128[c] * yv;
                            poly_lo[dst][c] += p & MASK64;
                            poly_hi[dst][c] += p >> 64;
                        }
                    }
                }
                poly_v[j + SD_GRID_B] = poly_v[j + SD_GRID_B].add(pj.mul(v_l));
            }
        }
        let mut poly_full = SecretBuffer([Fp5::ZERO; 2 * SD_GRID_B + 1]);
        for d in 0..=(2 * SD_GRID_B) {
            poly_full[d] = reduce_fp5_split(&poly_lo[d], &poly_hi[d]).add(poly_v[d]);
        }

        // Verify degree-B coefficient equals `c_plain + sum_{b,l} theta_b * eta_l * z_{b,l}`:
        let mut z_comb = Fp5::ZERO;
        for (l, &eta_l) in eta.iter().enumerate() {
            let mut col_z = Fp5::ZERO;
            for (b, &theta_b) in theta.iter().enumerate() {
                let zv = trace.z[b * SD_GRID_L + l];
                if zv != 0 {
                    col_z = col_z.add(theta_b.scale_fp(zv));
                }
            }
            z_comb = z_comb.add(eta_l.mul(col_z));
        }
        debug_assert_eq!(poly_full[SD_GRID_B], r1.c_plain.add(z_comb));

        let mut r_poly_without_b = Vec::with_capacity(SD_RPOLY_COEFFS);
        for (&pf, &ms) in poly_full[..SD_GRID_B].iter().zip(&r1.m_sum[..SD_GRID_B]) {
            r_poly_without_b.push(pf.add(ms).to_limbs());
        }
        for (&pf, &ms) in poly_full[SD_GRID_B + 1..=SD_RPOLY_COEFFS]
            .iter()
            .zip(&r1.m_sum[SD_GRID_B..SD_RPOLY_COEFFS])
        {
            r_poly_without_b.push(pf.add(ms).to_limbs());
        }
        (theta, eta, r_poly_without_b)
    });
    ct_zeroize_bytes(&mut gamma_seed);
    drop(trace);

    let mut rpoly_bundle = Vec::with_capacity(tau * SD_RPOLY_COEFFS * 40);
    for (_, _, r_poly) in &r2a_polys {
        for coeff in r_poly {
            for &limb in coeff {
                rpoly_bundle.extend_from_slice(&limb.to_le_bytes());
            }
        }
    }
    tr.absorb(b"VC_SD_LIMBO_RPOLY", &rpoly_bundle);
    drop(rpoly_bundle);

    // Round 2b: squeeze non-zero evaluation points r_rep in GF(p^5)* and evaluate all 256 parties' shares.
    let eval_points = squeeze_nonzero_eval_points(&mut tr, tau);
    let holder_arity = holder_secret.arity;
    let issuer_epoch = cred.issuer_epoch;
    let schema_id = cred.schema_id;

    struct R2bRepOut {
        alpha: Vec<[u64; 5]>,
        beta: Vec<[u64; 5]>,
        h_online: [[u8; 32]; VC_SD_LIMBO_PARTIES],
    }

    let r2b_outs: Vec<R2bRepOut> = parallel_map_indexed(tau, |rep| {
        let rep_u32 = rep as u32;
        let r1 = &r1_reps[rep];
        let (ref theta, ref eta, ref r_poly_without_b) = r2a_polys[rep];
        let tables = EvalTables::new(*theta, *eta, eval_points[rep]);

        let mut alpha_sum = [Fp5::ZERO; SD_GRID_L];
        let mut beta_sum = [Fp5::ZERO; SD_GRID_L];
        let mut sigma_sum = Fp5::ZERO;
        let mut h_online = [[0u8; 32]; VC_SD_LIMBO_PARTIES];

        let mut batch_tapes = SecretBuffer(core::array::from_fn::<_, 8, _>(|_| {
            Vec::with_capacity(total_party_limbs)
        }));
        let mut x_grid = SecretBuffer(vec![0u64; SD_GRID_B * SD_GRID_L]);
        let mut y_grid = SecretBuffer(vec![0u64; SD_GRID_B * SD_GRID_L]);
        let mut z_grid = SecretBuffer(vec![0u64; SD_GRID_B * SD_GRID_L]);
        let x_arr: &mut [u64; SD_GRID_B * SD_GRID_L] = x_grid.as_mut_slice().try_into().unwrap();
        let y_arr: &mut [u64; SD_GRID_B * SD_GRID_L] = y_grid.as_mut_slice().try_into().unwrap();
        let z_arr: &mut [u64; SD_GRID_B * SD_GRID_L] = z_grid.as_mut_slice().try_into().unwrap();
        let mut w_buf = SecretBuffer(vec![0u64; num_secret_wires]);
        let mut z_buf = SecretBuffer(vec![0u64; SD_TOTAL_GATES]);

        for batch in 0..(VC_SD_LIMBO_PARTIES / 8) {
            let base_p = batch * 8;
            let seeds_8 = SecretBuffer(core::array::from_fn::<_, 8, _>(|lane| {
                r1.ggm_tree.0[VC_SD_LIMBO_PARTIES + base_p + lane]
            }));
            let mut prg = Shake256PartyBatch8::new(&presentation_nonce, rep_u32, base_p, &seeds_8);
            let _ = prg.extract_salts_1();
            prg.squeeze_canonical_gl([true; 8], &mut batch_tapes, total_party_limbs);

            for (lane, tape) in batch_tapes.iter_mut().enumerate() {
                let p = base_p + lane;
                let party_masks = SecretBuffer(unpack_party_ext_masks(&tape[..PARTY_EXT_LIMBS]));
                let (u_p, v_p, c_p, m_p) = &*party_masks;
                let mut c_p = SecretBuffer(*c_p);
                let w_raw = &tape[PARTY_EXT_LIMBS..PARTY_EXT_LIMBS + num_secret_wires];
                let z_raw = &tape[PARTY_EXT_LIMBS + num_secret_wires..];

                if p == VC_SD_LIMBO_PARTIES - 1 {
                    for ((dst, &wr), &dw) in w_buf.0.iter_mut().zip(w_raw).zip(r1.delta_w.iter()) {
                        *dst = gl_add(wr, dw);
                    }
                    for ((dst, &zr), &dz) in z_buf.0.iter_mut().zip(z_raw).zip(r1.delta_z.iter()) {
                        *dst = gl_add(zr, dz);
                    }
                    *c_p = c_p.add(r1.delta_c);
                    eval_sd_party_shares(
                        p,
                        holder_arity,
                        issuer_epoch,
                        schema_id,
                        &verifier_scope_limbs,
                        &disclosed_attrs,
                        &expected_final_outs,
                        &w_buf,
                        &z_buf,
                        x_arr,
                        y_arr,
                        z_arr,
                    );
                } else {
                    eval_sd_party_shares(
                        p,
                        holder_arity,
                        issuer_epoch,
                        schema_id,
                        &verifier_scope_limbs,
                        &disclosed_attrs,
                        &expected_final_outs,
                        w_raw,
                        z_raw,
                        x_arr,
                        y_arr,
                        z_arr,
                    );
                }

                let evaluated = SecretBuffer(eval_party_polynomial_shares(
                    u_p, v_p, *c_p, m_p, x_arr, y_arr, z_arr, &tables,
                ));
                let (alpha_i, beta_i, sigma_i) = &*evaluated;
                for l in 0..SD_GRID_L {
                    alpha_sum[l] = alpha_sum[l].add(alpha_i[l]);
                    beta_sum[l] = beta_sum[l].add(beta_i[l]);
                }
                sigma_sum = sigma_sum.add(*sigma_i);
                h_online[p] = hash_limbo_party_online(
                    &presentation_nonce,
                    rep_u32,
                    p as u16,
                    alpha_i,
                    beta_i,
                    *sigma_i,
                );
                ct_zeroize_u64s(tape);
            }
        }
        ct_zeroize_u64s(&mut x_grid);
        ct_zeroize_u64s(&mut y_grid);
        ct_zeroize_u64s(&mut z_grid);

        #[cfg(debug_assertions)]
        {
            let mut prod_at_r = Fp5::ZERO;
            for l in 0..SD_GRID_L {
                prod_at_r = prod_at_r.add(alpha_sum[l].mul(beta_sum[l]));
            }
            let r_tilde_at_r = eval_r_poly_without_b(r_poly_without_b, &tables.r_powers);
            debug_assert_eq!(sigma_sum, prod_at_r.sub(r_tilde_at_r));
        }
        let _ = (r_poly_without_b, sigma_sum);

        R2bRepOut {
            alpha: alpha_sum.iter().map(|v| v.to_limbs()).collect(),
            beta: beta_sum.iter().map(|v| v.to_limbs()).collect(),
            h_online,
        }
    });

    let mut r2b_bundle = Vec::with_capacity(tau * (2 * SD_GRID_L * 40 + VC_SD_LIMBO_PARTIES * 32));
    for out in &r2b_outs {
        for v in out.alpha.iter().chain(out.beta.iter()) {
            for &limb in v {
                r2b_bundle.extend_from_slice(&limb.to_le_bytes());
            }
        }
        for h in &out.h_online {
            r2b_bundle.extend_from_slice(h);
        }
    }
    tr.absorb(b"VC_SD_LIMBO_R2_ONLINE", &r2b_bundle);
    drop(r2b_bundle);

    // Round 3: squeeze tau unbiased hidden-party indices in 0..=255.
    let mut hidden_parties = vec![0u8; tau];
    tr.squeeze_bytes(b"VC_SD_LIMBO_OPEN", &mut hidden_parties);

    let mut opened_reps = Vec::with_capacity(tau);
    for (((r1, (_, _, r_poly_without_b)), r2b), hidden_party) in r1_reps
        .into_iter()
        .zip(r2a_polys)
        .zip(r2b_outs)
        .zip(hidden_parties)
    {
        let ggm_copath = extract_ggm_copath(&r1.ggm_tree, hidden_party);
        let com_1_hidden = r1.com_1[hidden_party as usize];
        let aux = if (hidden_party as usize) == VC_SD_LIMBO_PARTIES - 1 {
            None
        } else {
            Some(LimboPartyAux {
                delta_w: r1.delta_w.0.clone(),
                delta_z: r1.delta_z.0.clone(),
                delta_c: r1.delta_c.to_limbs(),
            })
        };
        opened_reps.push(OpenedLimboRepetition {
            hidden_party,
            ggm_copath,
            com_1_hidden,
            aux,
            r_poly_without_b,
            alpha: r2b.alpha,
            beta: r2b.beta,
        });
    }

    Ok(SelectiveDisclosurePresentation {
        arity: holder_secret.arity,
        verifier_challenge: *verifier_challenge,
        mode,
        presentation_nonce,
        issuer_epoch: cred.issuer_epoch,
        schema_id: cred.schema_id,
        accumulator_root,
        issuer_root_tag,
        verifier_scope_limbs,
        disclosed_attrs,
        pres_commit,
        scope_tag,
        opened_reps,
    })
}

/// Verify an unlinkable [`SelectiveDisclosurePresentation`] against an issuer-signed
/// [`IssuerRootAttestation`] (`trusted_root`), `expected_issuer_mldsa_pk`, `expected_oprf_pk`,
/// and `verifier_scope`.
///
/// # Replay
/// The proof is checked against the challenge the presentation carries
/// (`pres.verifier_challenge`). When the proof and every statement check have
/// passed, that challenge is consumed from `challenges` for `verifier_scope`, and
/// the result is `true` only if the consumption succeeded. An invalid presentation
/// never consumes a challenge. With a [`VerifierChallengeLedger`] (`ledger.at(now)`)
/// or `FsVerifierChallengeLedger`, a presentation is therefore accepted at most
/// once, only for a challenge this verifier issued for this scope, and only while
/// that challenge is live. [`ReplayNotPrevented`] is the explicit opt-out for proof
/// audit; with it, repeated calls with the same valid proof return `true`.
#[allow(clippy::too_many_arguments)]
pub fn verify_presentation(
    pres: &SelectiveDisclosurePresentation,
    trusted_root: &IssuerRootAttestation,
    expected_issuer_mldsa_pk: &[u8],
    expected_oprf_pk: &PublicKey,
    verifier_scope: &[u8],
    challenges: &mut dyn PresentationChallenges,
    mode: PresentationMode,
    expected_schema_id: u64,
    expected_arity: usize,
) -> bool {
    verify_presentation_with_profile(
        pres,
        trusted_root,
        expected_issuer_mldsa_pk,
        expected_oprf_pk,
        verifier_scope,
        challenges,
        mode,
        expected_schema_id,
        expected_arity,
        ZkSoundnessProfile::Quantum128,
    )
}

/// Verify a [`SelectiveDisclosurePresentation`] under an explicit soundness profile.
/// The challenge is consumed from `challenges` exactly as in [`verify_presentation`].
#[allow(clippy::too_many_arguments)]
pub fn verify_presentation_with_profile(
    pres: &SelectiveDisclosurePresentation,
    trusted_root: &IssuerRootAttestation,
    expected_issuer_mldsa_pk: &[u8],
    expected_oprf_pk: &PublicKey,
    verifier_scope: &[u8],
    challenges: &mut dyn PresentationChallenges,
    mode: PresentationMode,
    expected_schema_id: u64,
    expected_arity: usize,
    profile: ZkSoundnessProfile,
) -> bool {
    challenges.is_live(verifier_scope, &pres.verifier_challenge)
        && presentation_proof_holds(
            pres,
            trusted_root,
            expected_issuer_mldsa_pk,
            expected_oprf_pk,
            verifier_scope,
            mode,
            expected_schema_id,
            expected_arity,
            profile,
        )
        && challenges
            .consume(verifier_scope, &pres.verifier_challenge)
            .is_ok()
}

/// Everything [`verify_presentation_with_profile`] checks except that the challenge
/// is one the verifier issued: the proof is for `pres.verifier_challenge`.
#[allow(clippy::too_many_arguments)]
pub(super) fn presentation_proof_holds(
    pres: &SelectiveDisclosurePresentation,
    trusted_root: &IssuerRootAttestation,
    expected_issuer_mldsa_pk: &[u8],
    expected_oprf_pk: &PublicKey,
    verifier_scope: &[u8],
    mode: PresentationMode,
    expected_schema_id: u64,
    expected_arity: usize,
    profile: ZkSoundnessProfile,
) -> bool {
    let verifier_challenge = &pres.verifier_challenge;
    if !trusted_root.verify(expected_issuer_mldsa_pk, expected_oprf_pk) {
        return false;
    }
    if !(1..=MAX_VC_ATTRS).contains(&expected_arity)
        || pres.arity != expected_arity
        || pres.schema_id != expected_schema_id
        || pres.mode != mode
        || pres.issuer_epoch != trusted_root.issuer_epoch
        || pres.accumulator_root != trusted_root.accumulator_root
        || !ct_eq_bytes(&pres.issuer_root_tag, &trusted_root.root_tag)
    {
        return false;
    }
    let expected_scope_limbs = presentation_scope(
        verifier_scope,
        verifier_challenge,
        &pres.presentation_nonce,
        mode,
    );
    if pres.verifier_scope_limbs != expected_scope_limbs {
        return false;
    }
    let tau = profile.sd_repetitions();
    if pres.opened_reps.len() != tau || pres.disclosed_attrs.len() > expected_arity {
        return false;
    }
    for (pos, &(idx, val)) in pres.disclosed_attrs.iter().enumerate() {
        if idx >= expected_arity || !gl_is_canonical(val) {
            return false;
        }
        if pos > 0 && pres.disclosed_attrs[pos - 1].0 >= idx {
            return false;
        }
    }
    for &x in pres.pres_commit.iter().chain(pres.scope_tag.iter()) {
        if !gl_is_canonical(x) {
            return false;
        }
    }

    let expected_num_secret_wires = (expected_arity - pres.disclosed_attrs.len())
        + 4
        + 4
        + VC_ACCUMULATOR_DEPTH
        + 6 * VC_ACCUMULATOR_DEPTH;

    // Validate repetition structural shapes and canonical Goldilocks limbs up front.
    for o in &pres.opened_reps {
        let is_last_hidden = (o.hidden_party as usize) == VC_SD_LIMBO_PARTIES - 1;
        match (&o.aux, is_last_hidden) {
            (None, true) => {}
            (Some(aux), false) => {
                if aux.delta_w.len() != expected_num_secret_wires
                    || aux.delta_z.len() != SD_TOTAL_GATES
                    || Fp5::from_canonical_limbs(aux.delta_c).is_none()
                    || aux.delta_w.iter().any(|&v| !gl_is_canonical(v))
                    || aux.delta_z.iter().any(|&v| !gl_is_canonical(v))
                {
                    return false;
                }
            }
            _ => return false,
        }
        if o.r_poly_without_b.len() != SD_RPOLY_COEFFS
            || o.alpha.len() != SD_GRID_L
            || o.beta.len() != SD_GRID_L
        {
            return false;
        }
        for arr in o
            .r_poly_without_b
            .iter()
            .chain(o.alpha.iter())
            .chain(o.beta.iter())
        {
            if Fp5::from_canonical_limbs(*arr).is_none() {
                return false;
            }
        }
    }

    let profile_tag: &[u8] = match profile {
        ZkSoundnessProfile::Classical128 => b"QSAG.VC.SD.LIMBO256.Classical128:17",
        ZkSoundnessProfile::Quantum128 => b"QSAG.VC.SD.LIMBO256.Quantum128:33",
    };

    let mut inst_bytes = serialize_sd_instance(&SdInstance {
        arity: expected_arity,
        presentation_nonce: &pres.presentation_nonce,
        issuer_epoch: pres.issuer_epoch,
        schema_id: pres.schema_id,
        accumulator_root: &pres.accumulator_root,
        issuer_root_tag: &pres.issuer_root_tag,
        verifier_scope_limbs: &pres.verifier_scope_limbs,
        disclosed_attrs: &pres.disclosed_attrs,
        pres_commit: &pres.pres_commit,
        scope_tag: &pres.scope_tag,
    });
    inst_bytes.extend_from_slice(verifier_challenge);
    inst_bytes.extend_from_slice(profile_tag);

    let mut tr = InterleavedTranscript::new(b"QSAG.BLIND_VC.SD_LIMBO.V1", &inst_bytes);
    tr.absorb(b"VC_SOUNDNESS_PROFILE", profile_tag);

    // Step V1 (parallel): reconstruct 255 GGM leaf seeds and Round-1 party commitments
    // (requiring only the first Keccak block per party to extract `salt_1[i]`).
    type LimboPartyBytes = [[u8; 32]; VC_SD_LIMBO_PARTIES];
    let v_r1: Vec<(LimboPartyBytes, LimboPartyBytes)> = parallel_map_indexed(tau, |rep| {
        let rep_u32 = rep as u32;
        let o = &pres.opened_reps[rep];
        let hidden = o.hidden_party as usize;
        let leaves = reconstruct_ggm_leaves_256(
            &o.ggm_copath,
            o.hidden_party,
            &pres.presentation_nonce,
            rep_u32,
        );
        let aux_digest = o
            .aux
            .as_ref()
            .map(|a| digest_limbo_aux(&a.delta_w, &a.delta_z, &a.delta_c));

        let mut com_1 = [[0u8; 32]; VC_SD_LIMBO_PARTIES];
        com_1[hidden] = o.com_1_hidden;
        for batch in 0..(VC_SD_LIMBO_PARTIES / 8) {
            let base_p = batch * 8;
            let seeds_8: [[u8; 32]; 8] = core::array::from_fn(|lane| leaves[base_p + lane]);
            let mut prg =
                Shake256PartyBatch8::new(&pres.presentation_nonce, rep_u32, base_p, &seeds_8);
            let salts = prg.extract_salts_1();
            for lane in 0..8 {
                let p = base_p + lane;
                if p == hidden {
                    continue;
                }
                let ad = if p == VC_SD_LIMBO_PARTIES - 1 {
                    aux_digest.as_ref()
                } else {
                    None
                };
                com_1[p] = commit_limbo_party_r1(
                    &pres.presentation_nonce,
                    rep_u32,
                    p as u16,
                    &seeds_8[lane],
                    ad,
                    &salts[lane],
                );
            }
        }
        (leaves, com_1)
    });

    let mut r1_bundle = Vec::with_capacity(tau * VC_SD_LIMBO_PARTIES * 32);
    for (_, com_1) in &v_r1 {
        for c in com_1 {
            r1_bundle.extend_from_slice(c);
        }
    }
    tr.absorb(b"VC_SD_LIMBO_R1_COMS", &r1_bundle);
    drop(r1_bundle);

    let mut gamma_seed = [0u8; 32];
    tr.squeeze_bytes(b"VC_SD_LIMBO_GAMMA", &mut gamma_seed);

    let mut rpoly_bundle = Vec::with_capacity(tau * SD_RPOLY_COEFFS * 40);
    for o in &pres.opened_reps {
        for coeff in &o.r_poly_without_b {
            for &limb in coeff {
                rpoly_bundle.extend_from_slice(&limb.to_le_bytes());
            }
        }
    }
    tr.absorb(b"VC_SD_LIMBO_RPOLY", &rpoly_bundle);
    drop(rpoly_bundle);

    let eval_points = squeeze_nonzero_eval_points(&mut tr, tau);

    let mut expected_final_outs = [0u64; VC_FINAL_OUTPUTS];
    expected_final_outs[0..6].copy_from_slice(&pres.accumulator_root);
    expected_final_outs[6..12].copy_from_slice(&pres.pres_commit);
    expected_final_outs[12..18].copy_from_slice(&pres.scope_tag);

    let total_party_limbs = PARTY_EXT_LIMBS + expected_num_secret_wires + SD_TOTAL_GATES;

    // Step V2 (single streaming pass per repetition, parallel across 16 cores):
    // evaluate all 255 opened parties and reconstruct the hidden party's online broadcast hash.
    let v_h_online: Vec<[[u8; 32]; VC_SD_LIMBO_PARTIES]> = parallel_map_indexed(tau, |rep| {
        let rep_u32 = rep as u32;
        let o = &pres.opened_reps[rep];
        let hidden = o.hidden_party as usize;
        let (ref leaves, _) = v_r1[rep];
        let (theta, eta) = expand_gamma_weights(&gamma_seed, rep_u32);
        let tables = EvalTables::new(theta, eta, eval_points[rep]);

        let mut open_alpha_sum = [Fp5::ZERO; SD_GRID_L];
        let mut open_beta_sum = [Fp5::ZERO; SD_GRID_L];
        let mut open_sigma_sum = Fp5::ZERO;
        let mut h_online = [[0u8; 32]; VC_SD_LIMBO_PARTIES];

        let mut batch_tapes: [Vec<u64>; 8] = core::array::from_fn(|_| Vec::new());
        let mut x_grid = vec![0u64; SD_GRID_B * SD_GRID_L];
        let mut y_grid = vec![0u64; SD_GRID_B * SD_GRID_L];
        let mut z_grid = vec![0u64; SD_GRID_B * SD_GRID_L];
        let x_arr: &mut [u64; SD_GRID_B * SD_GRID_L] = x_grid.as_mut_slice().try_into().unwrap();
        let y_arr: &mut [u64; SD_GRID_B * SD_GRID_L] = y_grid.as_mut_slice().try_into().unwrap();
        let z_arr: &mut [u64; SD_GRID_B * SD_GRID_L] = z_grid.as_mut_slice().try_into().unwrap();
        let mut w_buf = SecretBuffer(vec![0u64; expected_num_secret_wires]);
        let mut z_buf = SecretBuffer(vec![0u64; SD_TOTAL_GATES]);

        for batch in 0..(VC_SD_LIMBO_PARTIES / 8) {
            let base_p = batch * 8;
            let seeds_8: [[u8; 32]; 8] = core::array::from_fn(|lane| leaves[base_p + lane]);
            let active_mask: [bool; 8] = core::array::from_fn(|lane| base_p + lane != hidden);
            let mut prg =
                Shake256PartyBatch8::new(&pres.presentation_nonce, rep_u32, base_p, &seeds_8);
            let _ = prg.extract_salts_1();
            prg.squeeze_canonical_gl(active_mask, &mut batch_tapes, total_party_limbs);

            for (lane, tape) in batch_tapes.iter_mut().enumerate() {
                let p = base_p + lane;
                if p == hidden {
                    continue;
                }
                let (u_p, v_p, mut c_p, m_p) = unpack_party_ext_masks(&tape[..PARTY_EXT_LIMBS]);
                let w_raw = &tape[PARTY_EXT_LIMBS..PARTY_EXT_LIMBS + expected_num_secret_wires];
                let z_raw = &tape[PARTY_EXT_LIMBS + expected_num_secret_wires..];

                if p == VC_SD_LIMBO_PARTIES - 1 {
                    let aux = o.aux.as_ref().expect("validated aux for opened party 255");
                    for ((dst, &wr), &dw) in w_buf.0.iter_mut().zip(w_raw).zip(&aux.delta_w) {
                        *dst = gl_add(wr, dw);
                    }
                    for ((dst, &zr), &dz) in z_buf.0.iter_mut().zip(z_raw).zip(&aux.delta_z) {
                        *dst = gl_add(zr, dz);
                    }
                    c_p = c_p.add(Fp5::from_limbs(aux.delta_c));
                    eval_sd_party_shares(
                        p,
                        expected_arity,
                        pres.issuer_epoch,
                        pres.schema_id,
                        &pres.verifier_scope_limbs,
                        &pres.disclosed_attrs,
                        &expected_final_outs,
                        &w_buf,
                        &z_buf,
                        x_arr,
                        y_arr,
                        z_arr,
                    );
                } else {
                    eval_sd_party_shares(
                        p,
                        expected_arity,
                        pres.issuer_epoch,
                        pres.schema_id,
                        &pres.verifier_scope_limbs,
                        &pres.disclosed_attrs,
                        &expected_final_outs,
                        w_raw,
                        z_raw,
                        x_arr,
                        y_arr,
                        z_arr,
                    );
                }

                let (alpha_i, beta_i, sigma_i) = eval_party_polynomial_shares(
                    &u_p, &v_p, c_p, &m_p, x_arr, y_arr, z_arr, &tables,
                );
                for l in 0..SD_GRID_L {
                    open_alpha_sum[l] = open_alpha_sum[l].add(alpha_i[l]);
                    open_beta_sum[l] = open_beta_sum[l].add(beta_i[l]);
                }
                open_sigma_sum = open_sigma_sum.add(sigma_i);
                h_online[p] = hash_limbo_party_online(
                    &pres.presentation_nonce,
                    rep_u32,
                    p as u16,
                    &alpha_i,
                    &beta_i,
                    sigma_i,
                );
                ct_zeroize_u64s(tape);
            }
        }

        let mut alpha_hidden = [Fp5::ZERO; SD_GRID_L];
        let mut beta_hidden = [Fp5::ZERO; SD_GRID_L];
        let mut prod_at_r = Fp5::ZERO;
        for l in 0..SD_GRID_L {
            let a_l = Fp5::from_limbs(o.alpha[l]);
            let b_l = Fp5::from_limbs(o.beta[l]);
            alpha_hidden[l] = a_l.sub(open_alpha_sum[l]);
            beta_hidden[l] = b_l.sub(open_beta_sum[l]);
            prod_at_r = prod_at_r.add(a_l.mul(b_l));
        }
        let r_tilde_at_r = eval_r_poly_without_b(&o.r_poly_without_b, &tables.r_powers);
        let sigma_total = prod_at_r.sub(r_tilde_at_r);
        let sigma_hidden = sigma_total.sub(open_sigma_sum);

        h_online[hidden] = hash_limbo_party_online(
            &pres.presentation_nonce,
            rep_u32,
            hidden as u16,
            &alpha_hidden,
            &beta_hidden,
            sigma_hidden,
        );
        h_online
    });
    ct_zeroize_bytes(&mut gamma_seed);

    let mut r2b_bundle = Vec::with_capacity(tau * (2 * SD_GRID_L * 40 + VC_SD_LIMBO_PARTIES * 32));
    for (o, h_online) in pres.opened_reps.iter().zip(&v_h_online) {
        for v in o.alpha.iter().chain(o.beta.iter()) {
            for &limb in v {
                r2b_bundle.extend_from_slice(&limb.to_le_bytes());
            }
        }
        for h in h_online {
            r2b_bundle.extend_from_slice(h);
        }
    }
    tr.absorb(b"VC_SD_LIMBO_R2_ONLINE", &r2b_bundle);
    drop(r2b_bundle);

    let mut expected_hidden = vec![0u8; tau];
    tr.squeeze_bytes(b"VC_SD_LIMBO_OPEN", &mut expected_hidden);
    let actual_hidden: Vec<u8> = pres.opened_reps.iter().map(|o| o.hidden_party).collect();
    ct_eq_bytes(&actual_hidden, &expected_hidden)
}
