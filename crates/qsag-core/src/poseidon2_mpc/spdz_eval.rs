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
