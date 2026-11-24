use super::*;

/// SPDZ-authenticated `Goldilocks` wire share `([val]_p, [mac]_p)` held by a single party.
#[derive(Clone, Copy)]
pub(super) struct AuthGlWire {
    pub(super) val: Goldilocks,
    pub(super) mac: GoldilocksExt2,
}

impl AuthGlWire {
    pub(super) const ZERO: Self = Self {
        val: Goldilocks::ZERO,
        mac: GoldilocksExt2::ZERO,
    };

    #[inline]
    pub(super) fn public_const(c: Goldilocks, alpha_share: GoldilocksExt2) -> Self {
        Self {
            val: c,
            mac: alpha_share.mul_base(c),
        }
    }

    #[inline]
    pub(super) fn add(self, rhs: Self) -> Self {
        Self {
            val: self.val + rhs.val,
            mac: self.mac + rhs.mac,
        }
    }

    #[inline]
    fn sub(self, rhs: Self) -> Self {
        Self {
            val: self.val - rhs.val,
            mac: self.mac - rhs.mac,
        }
    }

    #[inline]
    pub(super) fn scale(self, c: Goldilocks) -> Self {
        Self {
            val: self.val * c,
            mac: self.mac.mul_base(c),
        }
    }

    #[inline]
    fn neg(self) -> Self {
        Self {
            val: self.val.const_neg(),
            mac: GoldilocksExt2::ZERO - self.mac,
        }
    }
}

impl SecretWipe for AuthGlWire {
    #[inline]
    fn secret_wipe(&mut self) {
        self.val.secret_wipe();
        self.mac.secret_wipe();
    }
}

/// Single party's non-clonable SPDZ-authenticated `Poseidon2` secret key share (`SK.seed`, `SK.prf`).
///
/// Redacts all field/MAC shares in `fmt::Debug` and volatile-wipes all secret storage on `Drop`
/// or `poison_and_wipe()`.
pub struct Poseidon2SpdzAuthenticatedKeyShare {
    pub party_id: usize,
    /// Number of members `n` the key was shared among; fixed when the share is authenticated.
    pub committee_size: usize,
    pub eval_point: Goldilocks,
    pub pk_seed: [u8; 32],
    pub mac_alpha_share: GoldilocksExt2,
    pub(crate) sk_seed_bytes: [Goldilocks; 32],
    pub(crate) sk_seed_macs: [GoldilocksExt2; 32],
    pub(crate) sk_prf_bytes: [Goldilocks; 32],
    pub(crate) sk_prf_macs: [GoldilocksExt2; 32],
    pub(crate) enrolled_profile: Option<(PqHashParams, PqPublicKey)>,
    pub(crate) enrolled_hem_profile: Option<(HemJortsPublicKey, HemDigest4)>,
    pub(crate) enrolled_latch_authority: Option<EpochLatchAuthorityPublic>,
    pub poisoned: bool,
}

impl fmt::Debug for Poseidon2SpdzAuthenticatedKeyShare {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Poseidon2SpdzAuthenticatedKeyShare")
            .field("party_id", &self.party_id)
            .field("poisoned", &self.poisoned)
            .finish_non_exhaustive()
    }
}

impl Poseidon2SpdzAuthenticatedKeyShare {
    /// Enrolled `(PqHashParams, PqPublicKey)` profile pinned to this key share, if any.
    #[inline]
    pub fn enrolled_profile(&self) -> Option<&(PqHashParams, PqPublicKey)> {
        self.enrolled_profile.as_ref()
    }

    /// Pin `(params, pk)` to this key share once. Re-enrolling the exact same `(params, pk)` is
    /// idempotent; any different `params` or `pk` returns [`Poseidon2MpcError::KeyProfileMismatch`].
    pub fn enroll_key_profile(
        &mut self,
        params: PqHashParams,
        pk: PqPublicKey,
    ) -> Result<(), Poseidon2MpcError> {
        if !params.is_well_formed() {
            return Err(Poseidon2MpcError::InvalidParams);
        }
        if !ct_eq_bytes32(&pk.pk_seed, &self.pk_seed) {
            return Err(Poseidon2MpcError::PublicSeedMismatch);
        }
        match &self.enrolled_profile {
            None => {
                self.enrolled_profile = Some((params, pk));
                Ok(())
            }
            Some((ep, epk)) => {
                if *ep == params
                    && ct_eq_bytes32(&epk.pk_seed, &pk.pk_seed)
                    && ct_eq_bytes32(&epk.pk_root, &pk.pk_root)
                {
                    Ok(())
                } else {
                    Err(Poseidon2MpcError::KeyProfileMismatch)
                }
            }
        }
    }

    /// Enrolled `Hem`-aggregatable `(HemJortsPublicKey, prf_check)` profile pinned to this share.
    #[inline]
    pub fn enrolled_hem_profile(&self) -> Option<&(HemJortsPublicKey, HemDigest4)> {
        self.enrolled_hem_profile.as_ref()
    }

    /// Pin a `Hem`-aggregatable `(HemJortsPublicKey, prf_check)` profile to this key share once.
    /// Re-enrolling the exact same `(pk, prf_check)` is idempotent; any mismatch returns
    /// [`Poseidon2MpcError::KeyProfileMismatch`].
    pub fn enroll_hem_key_profile(
        &mut self,
        pk: HemJortsPublicKey,
        prf_check: HemDigest4,
    ) -> Result<(), Poseidon2MpcError> {
        if pk.pk_seed != hem_pk_seed_from_bytes32(&self.pk_seed) {
            return Err(Poseidon2MpcError::PublicSeedMismatch);
        }
        match &self.enrolled_hem_profile {
            None => {
                self.enrolled_hem_profile = Some((pk, prf_check));
                Ok(())
            }
            Some((epk, eprf)) => {
                if *epk == pk && *eprf == prf_check {
                    Ok(())
                } else {
                    Err(Poseidon2MpcError::KeyProfileMismatch)
                }
            }
        }
    }

    /// Enrolled committee latch MAC authority pinned to this key share, if any.
    #[inline]
    pub fn enrolled_latch_authority(&self) -> Option<&EpochLatchAuthorityPublic> {
        self.enrolled_latch_authority.as_ref()
    }

    /// Pin a committee [`EpochLatchAuthorityPublic`] to this key share once. Re-enrolling the
    /// exact same authority is idempotent; any different authority or committee size returns
    /// `LatchCertificateRejected(CertificateCommitteeMismatch)`.
    pub fn enroll_latch_authority(
        &mut self,
        authority: EpochLatchAuthorityPublic,
    ) -> Result<(), Poseidon2MpcError> {
        if authority.committee_size() != self.committee_size {
            return Err(Poseidon2MpcError::LatchCertificateRejected(
                QuorumLatchError::CertificateCommitteeMismatch,
            ));
        }
        match &self.enrolled_latch_authority {
            None => {
                self.enrolled_latch_authority = Some(authority);
                Ok(())
            }
            Some(existing) if *existing == authority => Ok(()),
            Some(_) => Err(Poseidon2MpcError::LatchCertificateRejected(
                QuorumLatchError::CertificateCommitteeMismatch,
            )),
        }
    }

    /// Permanently burn this key share and volatile-wipe its secret byte shares and MACs.
    pub fn poison_and_wipe(&mut self) {
        self.poisoned = true;
        wipe_goldilocks(&mut self.sk_seed_bytes);
        wipe_ext2(&mut self.sk_seed_macs);
        wipe_goldilocks(&mut self.sk_prf_bytes);
        wipe_ext2(&mut self.sk_prf_macs);
        wipe_ext2(core::slice::from_mut(&mut self.mac_alpha_share));
    }
}

impl Drop for Poseidon2SpdzAuthenticatedKeyShare {
    fn drop(&mut self) {
        self.poison_and_wipe();
        wipe_bytes32(&mut self.pk_seed);
    }
}

/// Queued intermediate SPDZ wire openings (`y = x + r`, Beaver `d, e`, A2B `z = x - r`) that MUST
/// pass committed zero-masked `GoldilocksExt2` `MacCheck` **strictly before** any cut-boundary
/// digest is opened.
pub(super) struct SpdzGoldilocksPendingChecks {
    opening_tables: Option<(
        usize,
        Vec<Goldilocks>,
        alloc::sync::Arc<crate::preprocessing::GoldilocksOpeningTables>,
    )>,
    quorum_size: usize,
    pub(super) shares_per_party: Vec<Vec<Goldilocks>>,
    pub(super) macs_per_party: Vec<Vec<GoldilocksExt2>>,
}

impl SpdzGoldilocksPendingChecks {
    pub(super) fn new(quorum_size: usize) -> Self {
        Self {
            opening_tables: None,
            quorum_size,
            shares_per_party: vec![Vec::new(); quorum_size],
            macs_per_party: vec![Vec::new(); quorum_size],
        }
    }

    fn tables(
        &mut self,
        t: usize,
        points: &[Goldilocks],
    ) -> Result<alloc::sync::Arc<crate::preprocessing::GoldilocksOpeningTables>, PreprocessError>
    {
        if let Some((threshold, cached_points, tables)) = &self.opening_tables
            && *threshold == t
            && cached_points == points
        {
            return Ok(alloc::sync::Arc::clone(tables));
        }
        let tables = alloc::sync::Arc::new(crate::preprocessing::GoldilocksOpeningTables::new(
            t, points,
        )?);
        self.opening_tables = Some((t, points.to_vec(), alloc::sync::Arc::clone(&tables)));
        Ok(tables)
    }

    #[inline]
    fn record_batch(&mut self, wires_per_party: &[Vec<AuthGlWire>]) {
        debug_assert_eq!(wires_per_party.len(), self.quorum_size);
        let q = self.quorum_size;
        for ((shares, macs), wires) in self.shares_per_party[..q]
            .iter_mut()
            .zip(self.macs_per_party[..q].iter_mut())
            .zip(wires_per_party[..q].iter())
        {
            secret_vec_reserve(shares, wires.len());
            secret_vec_reserve(macs, wires.len());
            for w in wires {
                secret_vec_push(shares, w.val);
                secret_vec_push(macs, w.mac);
            }
        }
    }

    pub(super) fn clear_and_wipe(&mut self) {
        for p in 0..self.quorum_size {
            wipe_goldilocks(&mut self.shares_per_party[p]);
            wipe_ext2(&mut self.macs_per_party[p]);
            self.shares_per_party[p].clear();
            self.macs_per_party[p].clear();
        }
    }
}

impl Drop for SpdzGoldilocksPendingChecks {
    fn drop(&mut self) {
        self.clear_and_wipe();
    }
}

pub(super) fn poison_all_on_abort(
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
) {
    for ks in key_shares.iter_mut() {
        ks.poison_and_wipe();
    }
    for v in vaults.iter_mut() {
        v.poison_and_wipe();
    }
}

/// Authenticate distributed `ShamirPoseidonSeedShare`s (`SK.seed`, `SK.prf`, `pk_seed`) and
/// simultaneously generate correlated `PreprocessedPoseidonPartyVault`s under a single unified
/// dealerless `GoldilocksExt2` SPDZ MAC key $\alpha \in \mathbb{F}_{p^2}$ (`0` central RAM).
#[expect(
    clippy::too_many_arguments,
    reason = "One setup ceremony: session, quorum, both DKG transcripts, three tuple budgets, OT mesh and party randomness"
)]
pub fn authenticate_poseidon_dkg_shares_and_preprocess(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[Goldilocks],
    pk_seed: [u8; 32],
    sk_seed_dkg: &[ShamirPoseidonSeedShare],
    sk_prf_dkg: &[ShamirPoseidonSeedShare],
    num_pow7: usize,
    num_extra_beaver: usize,
    num_a2b_masks: usize,
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<
    (
        Vec<Poseidon2SpdzAuthenticatedKeyShare>,
        Vec<PreprocessedPoseidonPartyVault>,
    ),
    Poseidon2MpcError,
> {
    let n = eval_points.len();
    if t < 2
        || t > n
        || sk_seed_dkg.len() != n
        || sk_prf_dkg.len() != n
        || party_rngs.len() != n
        || ot_mesh.n != n
    {
        return Err(Poseidon2MpcError::InvalidQuorum { t, n });
    }
    validate_all_eval_points_goldilocks(eval_points)?;

    for p in 0..n {
        if !sk_seed_dkg[p].is_valid()
            || !sk_prf_dkg[p].is_valid()
            || sk_seed_dkg[p].eval_point != eval_points[p]
            || sk_prf_dkg[p].eval_point != eval_points[p]
        {
            return Err(Poseidon2MpcError::KeySharePoisoned { party_id: p });
        }
    }

    // 1. Pack 256 Boolean-verified DKG bit shares locally into 32 canonical `[0, 255]` byte shares
    let mut flat_bytes_per_party = SecretBuffer(vec![vec![Goldilocks::ZERO; 64]; n]);
    for p in 0..n {
        for byte_idx in 0..32 {
            let mut acc_seed = SecretBuffer(Goldilocks::ZERO);
            let mut acc_prf = SecretBuffer(Goldilocks::ZERO);
            let mut pow2 = Goldilocks::ONE;
            for bit in 0..8 {
                *acc_seed += pow2 * sk_seed_dkg[p].bit_shares[8 * byte_idx + bit];
                *acc_prf += pow2 * sk_prf_dkg[p].bit_shares[8 * byte_idx + bit];
                pow2 = pow2 + pow2;
            }
            flat_bytes_per_party[p][byte_idx] = *acc_seed;
            flat_bytes_per_party[p][32 + byte_idx] = *acc_prf;
        }
    }

    // 2. Establish unified dealerless `GoldilocksExt2` SPDZ MAC key `\alpha` across `0..n`
    let alpha_sid = cshake256_32(b"QSAG.POS2.UNIFIED.ALPHA/v1", &session_id);
    let (alpha_contribs_raw, alpha_shamir_raw) =
        spdz_setup_alpha_goldilocks(&alpha_sid, t, eval_points, party_rngs)?;
    let alpha_contribs = SecretBuffer(alpha_contribs_raw);
    let alpha_shamir = SecretBuffer(alpha_shamir_raw);

    // 3. Authenticate all 64 secret byte shares via LHL Gilboa OLE + SPDZ sacrifice (`0` central RAM!)
    let key_auth_sid = cshake256_32(b"QSAG.POS2.KEY.AUTH/v1", &session_id);
    let key_macs = SecretBuffer(spdz_authenticate_goldilocks_batch_ext2(
        &key_auth_sid,
        t,
        eval_points,
        ot_mesh,
        &alpha_contribs,
        &alpha_shamir,
        &flat_bytes_per_party,
        party_rngs,
    )?);

    // 4. Generate correlated `Π_pow7` + Beaver + Canonical `< p` A2B vaults under the SAME `\alpha`
    let vault_sid = cshake256_32(b"QSAG.POS2.VAULT.POW7/v1", &session_id);
    let vaults = run_dealerless_pi_pow7_with_alpha(
        vault_sid,
        t,
        eval_points,
        num_pow7,
        num_extra_beaver,
        num_a2b_masks,
        &alpha_contribs,
        &alpha_shamir,
        ot_mesh,
        party_rngs,
    )?;
    drop(alpha_contribs);

    let mut key_shares = Vec::with_capacity(n);
    for p in 0..n {
        let mut sk_seed_bytes = [Goldilocks::ZERO; 32];
        let mut sk_seed_macs = [GoldilocksExt2::ZERO; 32];
        let mut sk_prf_bytes = [Goldilocks::ZERO; 32];
        let mut sk_prf_macs = [GoldilocksExt2::ZERO; 32];
        sk_seed_bytes.copy_from_slice(&flat_bytes_per_party[p][0..32]);
        sk_seed_macs.copy_from_slice(&key_macs[p][0..32]);
        sk_prf_bytes.copy_from_slice(&flat_bytes_per_party[p][32..64]);
        sk_prf_macs.copy_from_slice(&key_macs[p][32..64]);
        key_shares.push(Poseidon2SpdzAuthenticatedKeyShare {
            party_id: p,
            committee_size: n,
            eval_point: eval_points[p],
            pk_seed,
            mac_alpha_share: alpha_shamir[p],
            sk_seed_bytes,
            sk_seed_macs,
            sk_prf_bytes,
            sk_prf_macs,
            enrolled_profile: None,
            enrolled_hem_profile: None,
            enrolled_latch_authority: None,
            poisoned: false,
        });
    }

    Ok((key_shares, vaults))
}

#[inline]
fn apply_m4_auth(b: [AuthGlWire; 4]) -> [AuthGlWire; 4] {
    let s = b[0].add(b[1]).add(b[2].add(b[3]));
    [
        s.add(b[0].add(b[1].scale(Goldilocks::TWO))),
        s.add(b[1].add(b[2].scale(Goldilocks::TWO))),
        s.add(b[2].add(b[3].scale(Goldilocks::TWO))),
        s.add(b[3].add(b[0].scale(Goldilocks::TWO))),
    ]
}

fn apply_me_auth(st: &mut [AuthGlWire; 12]) {
    // M4 tensor P3: transpose lanes, apply P3 tensor M4, transpose back.
    *st = [
        st[0], st[3], st[6], st[9], st[1], st[4], st[7], st[10], st[2], st[5], st[8], st[11],
    ];
    let y0 = apply_m4_auth([st[0], st[1], st[2], st[3]]);
    let y1 = apply_m4_auth([st[4], st[5], st[6], st[7]]);
    let y2 = apply_m4_auth([st[8], st[9], st[10], st[11]]);
    for i in 0..4 {
        let s = y0[i].add(y1[i]).add(y2[i]);
        st[i] = y0[i].add(s);
        st[4 + i] = y1[i].add(s);
        st[8 + i] = y2[i].add(s);
    }
    *st = [
        st[0], st[4], st[8], st[1], st[5], st[9], st[2], st[6], st[10], st[3], st[7], st[11],
    ];
}

fn apply_mi_auth(st: &mut [AuthGlWire; 12]) {
    let mut s = AuthGlWire::ZERO;
    for lane in st.iter() {
        s = s.add(*lane);
    }
    st[0] = st[0].scale(Goldilocks::from_u64_reduced(64)).neg().add(s);
    st[1] = st[1].add(s);
    let mut d = Goldilocks::TWO;
    for lane in st.iter_mut().skip(2) {
        *lane = lane.scale(d).add(s);
        d = d + d;
    }
}

/// Evaluate a batch of $x \mapsto x^7 \bmod p$ S-boxes in 1 communication round across the quorum
/// using pre-verified [`AuthenticatedPower7Share`]s and Binomial expansion $(y - r)^7$.
fn eval_sbox7_batch_spdz(
    tables: &crate::preprocessing::GoldilocksOpeningTables,
    inputs_per_party: &[Vec<AuthGlWire>],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    pending: &mut SpdzGoldilocksPendingChecks,
) -> Result<Vec<Vec<AuthGlWire>>, PreprocessError> {
    let m = inputs_per_party.len();
    let count = inputs_per_party[0].len();
    let mut tuples_p = Vec::with_capacity(m);
    let alphas = SecretBuffer(vaults.iter().map(|v| v.mac_alpha_share).collect::<Vec<_>>());
    let mut masked_wires = secret_vecs_with_capacity(m, count);
    for (p, vault) in vaults.iter_mut().enumerate() {
        let p_tups = vault.reserve_pow7(count)?;
        for (input, tup) in inputs_per_party[p][..count].iter().zip(&p_tups) {
            let r_wire = AuthGlWire {
                val: tup.r_pows[0],
                mac: tup.r_macs[0],
            };
            secret_vec_push(&mut masked_wires[p], input.add(r_wire));
        }
        tuples_p.push(p_tups);
    }

    pending.record_batch(&masked_wires);

    let mut y_opened = Vec::with_capacity(count);
    let mut sh_buf = SecretBuffer(vec![Goldilocks::ZERO; m]);
    for k in 0..count {
        for (buf, wires) in sh_buf.iter_mut().zip(masked_wires.iter()) {
            *buf = wires[k].val;
        }
        y_opened.push(tables.open(&sh_buf, "pos2_sbox7_y")?);
    }
    drop(sh_buf);

    let c7 = Goldilocks::from_u64_reduced(7);
    let c21 = Goldilocks::from_u64_reduced(21);
    let c35 = Goldilocks::from_u64_reduced(35);

    let mut out = secret_vecs_with_capacity(m, count);
    for p in 0..m {
        let alpha_p = alphas[p];
        for k in 0..count {
            let y = y_opened[k];
            let y2 = y * y;
            let y3 = y2 * y;
            let y4 = y2 * y2;
            let y5 = y4 * y;
            let y6 = y3 * y3;
            let y7 = y6 * y;
            let tup = &tuples_p[p][k];
            let rw = |idx: usize| AuthGlWire {
                val: tup.r_pows[idx],
                mac: tup.r_macs[idx],
            };
            // (y - r)^7 = y^7 - 7 y^6 r + 21 y^5 r^2 - 35 y^4 r^3 + 35 y^3 r^4 - 21 y^2 r^5 + 7 y r^6 - r^7
            let mut acc = AuthGlWire::public_const(y7, alpha_p);
            acc = acc.sub(rw(0).scale(c7 * y6));
            acc = acc.add(rw(1).scale(c21 * y5));
            acc = acc.sub(rw(2).scale(c35 * y4));
            acc = acc.add(rw(3).scale(c35 * y3));
            acc = acc.sub(rw(4).scale(c21 * y2));
            acc = acc.add(rw(5).scale(c7 * y));
            acc = acc.sub(rw(6));
            secret_vec_push(&mut out[p], acc);
        }
    }
    Ok(core::mem::take(&mut out.0))
}

/// Evaluate $B$ parallel Width-12 `poseidon2_perm12` permutations in SPDZ (`30` S-box rounds total
/// regardless of batch size $B$, consuming `118 * B` `AuthenticatedPower7Share`s).
pub(super) fn eval_spdz_poseidon2_perm12_batch(
    t: usize,
    quorum_pts: &[Goldilocks],
    states_per_party: &mut [Vec<[AuthGlWire; 12]>],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    pending: &mut SpdzGoldilocksPendingChecks,
) -> Result<(), PreprocessError> {
    let m = quorum_pts.len();
    let batch = states_per_party[0].len();
    if batch == 0 {
        return Ok(());
    }

    for states in &mut states_per_party[..m] {
        for st in &mut states[..batch] {
            apply_me_auth(st);
        }
    }

    let opening_tables = pending.tables(t, quorum_pts)?;

    // First 4 external rounds (`tag = 0`)
    for r in 0..POSEIDON2_HALF_EXTERNAL_ROUNDS {
        let mut sbox_in = secret_vecs_with_capacity(m, batch * 12);
        for p in 0..m {
            let alpha_p = vaults[p].mac_alpha_share;
            for st in &states_per_party[p][..batch] {
                for (lane, wire) in st.iter().enumerate() {
                    let rc =
                        AuthGlWire::public_const(poseidon2_const_at(0, r, lane as u64), alpha_p);
                    secret_vec_push(&mut sbox_in[p], wire.add(rc));
                }
            }
        }
        let sbox_out = SecretBuffer(eval_sbox7_batch_spdz(
            &opening_tables,
            &sbox_in,
            vaults,
            pending,
        )?);
        for p in 0..m {
            for b in 0..batch {
                for lane in 0..12 {
                    states_per_party[p][b][lane] = sbox_out[p][12 * b + lane];
                }
                apply_me_auth(&mut states_per_party[p][b]);
            }
        }
    }

    // 22 internal partial rounds (`tag = 1`, S-box on lane 0 BEFORE `apply_mi`)
    for r in 0..POSEIDON2_INTERNAL_ROUNDS {
        let mut sbox_in = secret_vecs_with_capacity(m, batch);
        for p in 0..m {
            let alpha_p = vaults[p].mac_alpha_share;
            let rc0 = AuthGlWire::public_const(poseidon2_const_at(1, r, 0), alpha_p);
            for st in &states_per_party[p][..batch] {
                secret_vec_push(&mut sbox_in[p], st[0].add(rc0));
            }
        }
        let sbox_out = SecretBuffer(eval_sbox7_batch_spdz(
            &opening_tables,
            &sbox_in,
            vaults,
            pending,
        )?);
        for p in 0..m {
            for b in 0..batch {
                states_per_party[p][b][0] = sbox_out[p][b];
                apply_mi_auth(&mut states_per_party[p][b]);
            }
        }
    }

    // Final 4 external rounds (`tag = 2`)
    for r in 0..POSEIDON2_HALF_EXTERNAL_ROUNDS {
        let mut sbox_in = secret_vecs_with_capacity(m, batch * 12);
        for p in 0..m {
            let alpha_p = vaults[p].mac_alpha_share;
            for st in &states_per_party[p][..batch] {
                for (lane, wire) in st.iter().enumerate() {
                    let rc =
                        AuthGlWire::public_const(poseidon2_const_at(2, r, lane as u64), alpha_p);
                    secret_vec_push(&mut sbox_in[p], wire.add(rc));
                }
            }
        }
        let sbox_out = SecretBuffer(eval_sbox7_batch_spdz(
            &opening_tables,
            &sbox_in,
            vaults,
            pending,
        )?);
        for p in 0..m {
            for b in 0..batch {
                for lane in 0..12 {
                    states_per_party[p][b][lane] = sbox_out[p][12 * b + lane];
                }
                apply_me_auth(&mut states_per_party[p][b]);
            }
        }
    }

    Ok(())
}

/// Pack a batch of `(template_with_zeroed_32b_slot, secret_offset)` preimages paired with 32
/// SPDZ-authenticated canonical `[0, 255]` secret byte shares per item, and evaluate the full
/// `Poseidon2` rate-8 sponge (`bytes_to_limbs56` + `poseidon2_pad`), returning the 4 output
/// squeeze lanes `st[0..4]` per batch item (`0` A2B conversions on input!).
pub(super) fn eval_spdz_poseidon2_hash32_templates(
    t: usize,
    quorum_pts: &[Goldilocks],
    templates: &[(Vec<u8>, usize)],
    secrets_per_party: &[Vec<[AuthGlWire; 32]>],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    pending: &mut SpdzGoldilocksPendingChecks,
) -> Result<Vec<Vec<[AuthGlWire; 4]>>, PreprocessError> {
    let m = quorum_pts.len();
    let batch = templates.len();
    if batch == 0 {
        return Ok(vec![Vec::new(); m]);
    }

    // Precompute public padded limbs and block count for each template
    let mut padded_templates: Vec<Vec<Goldilocks>> = Vec::with_capacity(batch);
    let mut max_blocks = 0usize;
    for (tmpl, _) in templates {
        let mut limbs = bytes_to_limbs56(tmpl);
        poseidon2_pad(&mut limbs);
        max_blocks = max_blocks.max(limbs.len() / 8);
        padded_templates.push(limbs);
    }

    // Build authenticated limb vectors per `(party, item)` using exact 56-bit byte weights
    let mut item_limbs_p: SecretBuffer<Vec<Vec<Vec<AuthGlWire>>>> =
        secret_vecs_with_capacity(m, batch);
    for p in 0..m {
        let alpha_p = vaults[p].mac_alpha_share;
        for item in 0..batch {
            let mut limbs: Vec<AuthGlWire> = padded_templates[item]
                .iter()
                .map(|&c| AuthGlWire::public_const(c, alpha_p))
                .collect();
            let off = templates[item].1;
            for (k, secret) in secrets_per_party[p][item].iter().enumerate() {
                let pos = off + k;
                let limb_idx = pos / 7;
                let byte_slot = pos % 7;
                let weight = Goldilocks::from_u64_reduced(1u64 << ((6 - byte_slot) * 8));
                limbs[limb_idx] = limbs[limb_idx].add(secret.scale(weight));
            }
            item_limbs_p[p].push(limbs);
        }
    }

    // Initialize sponge states to `POSEIDON2_INIT_STATE`
    let mut states_p: SecretBuffer<Vec<Vec<[AuthGlWire; 12]>>> =
        secret_vecs_with_capacity(m, batch);
    for p in 0..m {
        let alpha_p = vaults[p].mac_alpha_share;
        let mut init_st = [AuthGlWire::ZERO; 12];
        for lane in 0..12 {
            init_st[lane] = AuthGlWire::public_const(POSEIDON2_INIT_STATE[lane], alpha_p);
        }
        for _ in 0..batch {
            secret_vec_push(&mut states_p[p], init_st);
        }
    }

    // Step through absorb blocks in lockstep across active items
    for blk in 0..max_blocks {
        let active_indices: Vec<usize> = (0..batch)
            .filter(|&item| blk < padded_templates[item].len() / 8)
            .collect();
        let mut sub_states = secret_vecs_with_capacity(m, active_indices.len());
        for p in 0..m {
            for &item in &active_indices {
                let mut st = states_p[p][item];
                for lane in 0..8 {
                    st[lane] = st[lane].add(item_limbs_p[p][item][8 * blk + lane]);
                }
                secret_vec_push(&mut sub_states[p], st);
            }
        }
        eval_spdz_poseidon2_perm12_batch(t, quorum_pts, &mut sub_states, vaults, pending)?;
        for p in 0..m {
            for (slot, &item) in active_indices.iter().enumerate() {
                states_p[p][item] = sub_states[p][slot];
            }
        }
    }

    let mut out = secret_vecs_with_capacity(m, batch);
    for p in 0..m {
        for st in &states_p[p][..batch] {
            secret_vec_push(&mut out[p], [st[0], st[1], st[2], st[3]]);
        }
    }
    Ok(core::mem::take(&mut out.0))
}

/// Batched SPDZ Beaver multiplication `[x_k * y_k]` in 1 communication round, recording all
/// `(d_k, e_k)` masked wires into `pending` for pre-cut SPDZ `MacCheck`.
fn eval_spdz_beaver_mul_batch(
    t: usize,
    quorum_pts: &[Goldilocks],
    xs_per_party: &[Vec<AuthGlWire>],
    ys_per_party: &[Vec<AuthGlWire>],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    pending: &mut SpdzGoldilocksPendingChecks,
) -> Result<Vec<Vec<AuthGlWire>>, PreprocessError> {
    let m = quorum_pts.len();
    let count = xs_per_party[0].len();
    if count == 0 {
        return Ok(vec![Vec::new(); m]);
    }
    let mut triples_p = Vec::with_capacity(m);
    let alphas = SecretBuffer(vaults.iter().map(|v| v.mac_alpha_share).collect::<Vec<_>>());
    let mut de_wires = secret_vecs_with_capacity(m, 2 * count);
    for (p, vault) in vaults.iter_mut().enumerate() {
        let p_tr = vault.reserve_beaver(count)?;
        for (k, tr) in p_tr.iter().enumerate() {
            let a_w = AuthGlWire {
                val: tr.a,
                mac: tr.a_mac,
            };
            let b_w = AuthGlWire {
                val: tr.b,
                mac: tr.b_mac,
            };
            secret_vec_push(&mut de_wires[p], xs_per_party[p][k].sub(a_w));
            secret_vec_push(&mut de_wires[p], ys_per_party[p][k].sub(b_w));
        }
        triples_p.push(p_tr);
    }

    pending.record_batch(&de_wires);

    let opening_tables = pending.tables(t, quorum_pts)?;
    let mut de_open = Vec::with_capacity(2 * count);
    let mut sh_buf = SecretBuffer(vec![Goldilocks::ZERO; m]);
    for idx in 0..(2 * count) {
        for (buf, wires) in sh_buf.iter_mut().zip(de_wires.iter()) {
            *buf = wires[idx].val;
        }
        de_open.push(opening_tables.open(&sh_buf, "pos2_beaver_de")?);
    }
    drop(sh_buf);

    let mut out = secret_vecs_with_capacity(m, count);
    for p in 0..m {
        let alpha_p = alphas[p];
        for k in 0..count {
            let d = de_open[2 * k];
            let e = de_open[2 * k + 1];
            let tr = &triples_p[p][k];
            let a_w = AuthGlWire {
                val: tr.a,
                mac: tr.a_mac,
            };
            let b_w = AuthGlWire {
                val: tr.b,
                mac: tr.b_mac,
            };
            let c_w = AuthGlWire {
                val: tr.c,
                mac: tr.c_mac,
            };
            let de_const = AuthGlWire::public_const(d * e, alpha_p);
            let z = c_w.add(b_w.scale(d)).add(a_w.scale(e)).add(de_const);
            secret_vec_push(&mut out[p], z);
        }
    }
    Ok(core::mem::take(&mut out.0))
}

/// Exact canonical `< p` Arithmetic-to-Binary (`A2B`) conversion of a batch of 4-lane sponge
/// outputs (`st[0..4]`) into 32 canonical big-endian byte shares `[0, 255]` (`to_be_bytes()`)
/// WITHOUT opening `st[0..4]`.
///
/// Consumes `4` [`CanonicalBitMask64Share`]s + `760` [`GoldilocksBeaverShare`]s per 32-byte digest.
pub(super) fn eval_spdz_canonical_a2b_state4_batch_to_bytes32(
    t: usize,
    quorum_pts: &[Goldilocks],
    states4_per_party: &[Vec<[AuthGlWire; 4]>],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    pending: &mut SpdzGoldilocksPendingChecks,
) -> Result<Vec<Vec<[AuthGlWire; 32]>>, PreprocessError> {
    let opening_tables = pending.tables(t, quorum_pts)?;
    let m = quorum_pts.len();
    let batch = states4_per_party[0].len();
    let num_lanes = 4 * batch;
    if num_lanes == 0 {
        return Ok(vec![Vec::new(); m]);
    }

    // 1. Pop 1 `CanonicalBitMask64Share` (`r < p`) per lane and open `z = (x - r) mod p`
    let mut r_bits_p: SecretBuffer<Vec<Vec<[AuthGlWire; 64]>>> =
        secret_vecs_with_capacity(m, num_lanes);
    let mut z_wires = secret_vecs_with_capacity(m, num_lanes);
    for p in 0..m {
        for st4 in &states4_per_party[p][..batch] {
            for lane_wire in st4 {
                let mask = vaults[p].pop_a2b_mask()?;
                let r_sum = AuthGlWire {
                    val: mask.field_sum_share,
                    mac: mask.field_sum_mac,
                };
                secret_vec_push(&mut z_wires[p], lane_wire.sub(r_sum));
                let rb: [AuthGlWire; 64] = core::array::from_fn(|bit| AuthGlWire {
                    val: mask.bit_shares[bit],
                    mac: mask.bit_macs[bit],
                });
                secret_vec_push(&mut r_bits_p[p], rb);
            }
        }
    }

    pending.record_batch(&z_wires);

    let mut z_pub = Vec::with_capacity(num_lanes);
    let mut sh_buf = SecretBuffer(vec![Goldilocks::ZERO; m]);
    for idx in 0..num_lanes {
        for (buf, wires) in sh_buf.iter_mut().zip(z_wires.iter()) {
            *buf = wires[idx].val;
        }
        let z_f = opening_tables.open(&sh_buf, "pos2_a2b_z")?;
        z_pub.push(z_f.to_canonical_u64());
    }
    drop(sh_buf);

    // 2. Run dual 64-bit public+secret ripple adders in lockstep across all `num_lanes`:
    //    Adder A: `z + r` -> sum bits `u_bits[0..64]`
    //    Adder B: `(z + 2^32 - 1) + r` -> sum bits `v_bits[0..64]`, carry `c_b` (`c_b == 1 iff z + r >= p`)
    let mut u_bits_p = SecretBuffer(vec![vec![[AuthGlWire::ZERO; 64]; num_lanes]; m]);
    let mut v_bits_p = SecretBuffer(vec![vec![[AuthGlWire::ZERO; 64]; num_lanes]; m]);
    let mut carry_a_p = SecretBuffer(vec![vec![AuthGlWire::ZERO; num_lanes]; m]);
    let mut carry_b_p = SecretBuffer(vec![vec![AuthGlWire::ZERO; num_lanes]; m]);

    // Bit 0 (`carry_in == 0`, 0 Beaver triples!)
    for p in 0..m {
        let alpha_p = vaults[p].mac_alpha_share;
        let one_c = AuthGlWire::public_const(Goldilocks::ONE, alpha_p);
        for idx in 0..num_lanes {
            let za0 = (z_pub[idx] & 1) == 1;
            let zb0 = ((z_pub[idx] + GOLDILOCKS_EPSILON) & 1) == 1;
            let r0 = r_bits_p[p][idx][0];
            if za0 {
                u_bits_p[p][idx][0] = one_c.sub(r0);
                carry_a_p[p][idx] = r0;
            } else {
                u_bits_p[p][idx][0] = r0;
                carry_a_p[p][idx] = AuthGlWire::ZERO;
            }
            if zb0 {
                v_bits_p[p][idx][0] = one_c.sub(r0);
                carry_b_p[p][idx] = r0;
            } else {
                v_bits_p[p][idx][0] = r0;
                carry_b_p[p][idx] = AuthGlWire::ZERO;
            }
        }
    }

    // Bits 1..64 (`2 * num_lanes` Beaver multiplications per bit position across all lanes in parallel)
    for bit in 1..64 {
        let mut mul_x = secret_vecs_with_capacity(m, 2 * num_lanes);
        let mut mul_y = secret_vecs_with_capacity(m, 2 * num_lanes);
        for p in 0..m {
            for idx in 0..num_lanes {
                let rk = r_bits_p[p][idx][bit];
                secret_vec_push(&mut mul_x[p], rk);
                secret_vec_push(&mut mul_y[p], carry_a_p[p][idx]);
                secret_vec_push(&mut mul_x[p], rk);
                secret_vec_push(&mut mul_y[p], carry_b_p[p][idx]);
            }
        }
        let prods = SecretBuffer(eval_spdz_beaver_mul_batch(
            t, quorum_pts, &mul_x, &mul_y, vaults, pending,
        )?);
        for p in 0..m {
            let alpha_p = vaults[p].mac_alpha_share;
            let one_c = AuthGlWire::public_const(Goldilocks::ONE, alpha_p);
            for idx in 0..num_lanes {
                let rk = r_bits_p[p][idx][bit];
                let ca = carry_a_p[p][idx];
                let cb = carry_b_p[p][idx];
                let pa = prods[p][2 * idx];
                let pb = prods[p][2 * idx + 1];

                let za = ((z_pub[idx] >> bit) & 1) == 1;
                if za {
                    // u_k = 1 - r_k - c_a + 2 * (r_k * c_a), c_a' = r_k + c_a - (r_k * c_a)
                    u_bits_p[p][idx][bit] = one_c.sub(rk).sub(ca).add(pa.scale(Goldilocks::TWO));
                    carry_a_p[p][idx] = rk.add(ca).sub(pa);
                } else {
                    // u_k = r_k + c_a - 2 * (r_k * c_a), c_a' = r_k * c_a
                    u_bits_p[p][idx][bit] = rk.add(ca).sub(pa.scale(Goldilocks::TWO));
                    carry_a_p[p][idx] = pa;
                }

                let zb = (((z_pub[idx] + GOLDILOCKS_EPSILON) >> bit) & 1) == 1;
                if zb {
                    v_bits_p[p][idx][bit] = one_c.sub(rk).sub(cb).add(pb.scale(Goldilocks::TWO));
                    carry_b_p[p][idx] = rk.add(cb).sub(pb);
                } else {
                    v_bits_p[p][idx][bit] = rk.add(cb).sub(pb.scale(Goldilocks::TWO));
                    carry_b_p[p][idx] = pb;
                }
            }
        }
    }

    // 3. Mux all 64 bits in 1 batched Beaver round: `x_k = u_k + c_b * (v_k - u_k)`
    let mut mux_x = secret_vecs_with_capacity(m, 64 * num_lanes);
    let mut mux_y = secret_vecs_with_capacity(m, 64 * num_lanes);
    for p in 0..m {
        for idx in 0..num_lanes {
            let cb = carry_b_p[p][idx];
            for bit in 0..64 {
                secret_vec_push(&mut mux_x[p], cb);
                secret_vec_push(
                    &mut mux_y[p],
                    v_bits_p[p][idx][bit].sub(u_bits_p[p][idx][bit]),
                );
            }
        }
    }
    let mux_prods = SecretBuffer(eval_spdz_beaver_mul_batch(
        t, quorum_pts, &mux_x, &mux_y, vaults, pending,
    )?);

    // 4. Pack canonical big-endian bytes `to_be_bytes()` (`byte 0` = bits `56..64`, ..., `byte 7` = bits `0..8`)
    let mut out_bytes_p = secret_vecs_with_capacity(m, batch);
    for p in 0..m {
        for item in 0..batch {
            let mut bytes32 = [AuthGlWire::ZERO; 32];
            for lane in 0..4 {
                let idx = 4 * item + lane;
                for byte_in_lane in 0..8 {
                    let bit_lo = 8 * (7 - byte_in_lane);
                    let mut acc = AuthGlWire::ZERO;
                    let mut pow2 = Goldilocks::ONE;
                    for b in 0..8 {
                        let bit = bit_lo + b;
                        let x_bit = u_bits_p[p][idx][bit].add(mux_prods[p][64 * idx + bit]);
                        acc = acc.add(x_bit.scale(pow2));
                        pow2 = pow2 + pow2;
                    }
                    bytes32[8 * lane + byte_in_lane] = acc;
                }
            }
            secret_vec_push(&mut out_bytes_p[p], bytes32);
        }
    }
    Ok(core::mem::take(&mut out_bytes_p.0))
}

/// Publicly opened cut-boundary values: `(4-lane digests as 32 bytes, extra canonical byte blocks)`.
type CutOpenings = (Vec<[u8; 32]>, Vec<[u8; 32]>);

/// Strictly verify ALL queued intermediate SPDZ wires AND open a batch of cut-boundary 4-lane
/// digests (`[u8; 32]` via `Goldilocks::to_be_bytes()`) using committed zero-masked SPDZ `MacCheck`.
///
/// If any wire or cut digest fails commitment, degree-`< t`, or `GoldilocksExt2` `MacCheck`,
/// immediately burns (`poison_and_wipe()`) all key shares and preprocessing vaults!
#[expect(
    clippy::too_many_arguments,
    reason = "One cut-boundary opening: transcript context, quorum, both cut batches, pending checks and per-party state"
)]
pub(super) fn flush_verify_and_open_cut_states4(
    session_id: &[u8; 32],
    phase: &'static str,
    t: usize,
    quorum_pts: &[Goldilocks],
    cut_states4_per_party: &[Vec<[AuthGlWire; 4]>],
    extra_cut_bytes_per_party: &[Vec<[AuthGlWire; 32]>],
    pending: &mut SpdzGoldilocksPendingChecks,
    key_shares: &mut [&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &mut [&mut PreprocessedPoseidonPartyVault],
    party_rngs: &mut [PartyPrivateRng],
) -> Result<CutOpenings, Poseidon2MpcError> {
    let m = quorum_pts.len();
    let num_states = cut_states4_per_party[0].len();
    let num_byte_blocks = extra_cut_bytes_per_party[0].len();
    let pend_len = pending.shares_per_party[0].len();
    // Intermediate openings must authenticate before any unmasked cut share is copied.
    let alpha = SecretBuffer(vaults.iter().map(|v| v.mac_alpha_share).collect::<Vec<_>>());
    let intermediate = commit_and_open_spdz_goldilocks_batch_quorum(
        session_id,
        "pre_cut_intermediate_mac",
        t,
        quorum_pts,
        &pending.shares_per_party,
        &pending.macs_per_party,
        &alpha,
        party_rngs,
    );
    pending.clear_and_wipe();
    match intermediate {
        Ok(mut values) => wipe_goldilocks(&mut values),
        Err(e) => {
            poison_all_on_abort(key_shares, vaults);
            return Err(Poseidon2MpcError::Preprocess(e));
        }
    }
    let _ = pend_len;
    let pend_len = 0;
    let total_wires = 4 * num_states + 32 * num_byte_blocks;

    let mut all_sh = secret_vecs_with_capacity(m, total_wires);
    let mut all_mac = secret_vecs_with_capacity(m, total_wires);
    let mut alpha_sh = SecretBuffer(Vec::with_capacity(m));
    for p in 0..m {
        secret_vec_push(&mut alpha_sh, vaults[p].mac_alpha_share);
        for st in &cut_states4_per_party[p] {
            for w in st {
                secret_vec_push(&mut all_sh[p], w.val);
                secret_vec_push(&mut all_mac[p], w.mac);
            }
        }
        for blk in &extra_cut_bytes_per_party[p] {
            for w in blk {
                secret_vec_push(&mut all_sh[p], w.val);
                secret_vec_push(&mut all_mac[p], w.mac);
            }
        }
    }
    pending.clear_and_wipe();

    let opened_res = commit_and_open_spdz_goldilocks_batch_quorum(
        session_id, phase, t, quorum_pts, &all_sh, &all_mac, &alpha_sh, party_rngs,
    );
    drop(all_sh);
    drop(all_mac);
    drop(alpha_sh);

    let opened = SecretBuffer(match opened_res {
        Ok(v) => v,
        Err(e) => {
            poison_all_on_abort(key_shares, vaults);
            return Err(Poseidon2MpcError::Preprocess(e));
        }
    });

    let mut out_digests = Vec::with_capacity(num_states);
    for s in 0..num_states {
        let base = pend_len + 4 * s;
        let mut d32 = [0u8; 32];
        for lane in 0..4 {
            d32[8 * lane..8 * (lane + 1)].copy_from_slice(&opened[base + lane].to_be_bytes());
        }
        out_digests.push(d32);
    }

    let mut out_extra = Vec::with_capacity(num_byte_blocks);
    let extra_base = pend_len + 4 * num_states;
    for blk in 0..num_byte_blocks {
        let mut b32 = [0u8; 32];
        for b in 0..32 {
            let v = opened[extra_base + 32 * blk + b].to_canonical_u64();
            if v > 255 {
                poison_all_on_abort(key_shares, vaults);
                return Err(Poseidon2MpcError::Preprocess(
                    PreprocessError::NonBooleanBitDetected { phase },
                ));
            }
            b32[b] = v as u8;
        }
        out_extra.push(b32);
    }

    Ok((out_digests, out_extra))
}

pub(super) fn validate_quorum_slices(
    t: usize,
    key_shares: &[&mut Poseidon2SpdzAuthenticatedKeyShare],
    vaults: &[&mut PreprocessedPoseidonPartyVault],
    party_rngs: &[PartyPrivateRng],
) -> Result<([u8; 32], Vec<Goldilocks>), Poseidon2MpcError> {
    let m = key_shares.len();
    if t < 2 || m < t || vaults.len() != m || party_rngs.len() != m {
        return Err(Poseidon2MpcError::InvalidQuorum { t, n: m });
    }
    let pk_seed = key_shares[0].pk_seed;
    let n = key_shares[0].committee_size;
    if m > n
        || key_shares
            .iter()
            .any(|ks| ks.committee_size != n || ks.party_id >= n)
    {
        return Err(Poseidon2MpcError::InvalidQuorum { t, n: m });
    }
    let mut pts = Vec::with_capacity(m);
    for p in 0..m {
        if key_shares[p].poisoned || vaults[p].is_poisoned() {
            return Err(Poseidon2MpcError::KeySharePoisoned {
                party_id: key_shares[p].party_id,
            });
        }
        if !ct_eq_bytes32(&key_shares[p].pk_seed, &pk_seed)
            || key_shares[p].eval_point != vaults[p].eval_point
        {
            return Err(Poseidon2MpcError::PublicSeedMismatch);
        }
        pts.push(key_shares[p].eval_point);
    }
    validate_all_eval_points_goldilocks(&pts)?;
    Ok((pk_seed, pts))
}

#[inline]
pub(super) fn key_seed_wires(ks: &Poseidon2SpdzAuthenticatedKeyShare) -> [AuthGlWire; 32] {
    core::array::from_fn(|i| AuthGlWire {
        val: ks.sk_seed_bytes[i],
        mac: ks.sk_seed_macs[i],
    })
}

#[inline]
pub(super) fn key_prf_wires(ks: &Poseidon2SpdzAuthenticatedKeyShare) -> [AuthGlWire; 32] {
    core::array::from_fn(|i| AuthGlWire {
        val: ks.sk_prf_bytes[i],
        mac: ks.sk_prf_macs[i],
    })
}
