//! Authenticated power tuples, Beaver triples and canonical bit masks for Poseidon.

use super::goldilocks_auth::shamir_share_goldilocks;
use super::*;

/// One party's isolated 1-round Binomial Power-7 tuple share `([r], [r^2], ..., [r^7])`
/// paired with full `GoldilocksExt2` SPDZ Shamir MAC shares `r_macs[0..7]` (`!Clone`, wiped on `Drop`).
pub struct AuthenticatedPower7Share {
    pub r_pows: [Goldilocks; 7],
    /// Full SPDZ Shamir MAC shares `([\alpha \cdot r], [\alpha \cdot r^2], ..., [\alpha \cdot r^7])`.
    pub r_macs: [GoldilocksExt2; 7],
    /// Convenience alias equal to `r_macs[0]` (`[\alpha \cdot r]`).
    pub r1_mac: GoldilocksExt2,
}

impl fmt::Debug for AuthenticatedPower7Share {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("AuthenticatedPower7Share([REDACTED])")
    }
}

impl AuthenticatedPower7Share {
    /// Transfer this reservation and erase its original storage.
    pub fn take_and_wipe(&mut self) -> Self {
        let material = Self {
            r_pows: self.r_pows,
            r_macs: self.r_macs,
            r1_mac: self.r1_mac,
        };
        self.wipe();
        material
    }
    fn wipe(&mut self) {
        wipe_goldilocks(&mut self.r_pows);
        wipe_ext2(&mut self.r_macs);
        wipe_ext2(core::slice::from_mut(&mut self.r1_mac));
    }
}
impl Drop for AuthenticatedPower7Share {
    fn drop(&mut self) {
        self.wipe();
    }
}

/// One party's isolated `Goldilocks` Beaver triple share `([a], [b], [c])` paired with
/// `GoldilocksExt2` SPDZ Shamir MAC shares (`a_mac, b_mac, c_mac`) (`!Clone`, wiped on `Drop`).
pub struct GoldilocksBeaverShare {
    pub a: Goldilocks,
    pub b: Goldilocks,
    pub c: Goldilocks,
    pub a_mac: GoldilocksExt2,
    pub b_mac: GoldilocksExt2,
    pub c_mac: GoldilocksExt2,
}

impl fmt::Debug for GoldilocksBeaverShare {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("GoldilocksBeaverShare([REDACTED])")
    }
}

impl GoldilocksBeaverShare {
    /// Transfer this reservation and erase its original storage.
    pub fn take_and_wipe(&mut self) -> Self {
        let material = Self {
            a: self.a,
            b: self.b,
            c: self.c,
            a_mac: self.a_mac,
            b_mac: self.b_mac,
            c_mac: self.c_mac,
        };
        self.wipe();
        material
    }
    fn wipe(&mut self) {
        wipe_goldilocks(core::slice::from_mut(&mut self.a));
        wipe_goldilocks(core::slice::from_mut(&mut self.b));
        wipe_goldilocks(core::slice::from_mut(&mut self.c));
        wipe_ext2(core::slice::from_mut(&mut self.a_mac));
        wipe_ext2(core::slice::from_mut(&mut self.b_mac));
        wipe_ext2(core::slice::from_mut(&mut self.c_mac));
    }
}
impl Drop for GoldilocksBeaverShare {
    fn drop(&mut self) {
        self.wipe();
    }
}

/// One party's isolated canonical `< p` 64-bit A2B bit-mask share `([b_0], ..., [b_63])`
/// verified in preprocessing via SPDZ `MacCheck` to satisfy $b_k \in \{0, 1\}$ AND
/// $\sum_{k=0}^{63} 2^k b_k < p$, paired with full `GoldilocksExt2` SPDZ MAC shares.
pub struct CanonicalBitMask64Share {
    pub bit_shares: [Goldilocks; 64],
    pub field_sum_share: Goldilocks,
    pub bit_macs: [GoldilocksExt2; 64],
    pub field_sum_mac: GoldilocksExt2,
}

impl fmt::Debug for CanonicalBitMask64Share {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("CanonicalBitMask64Share([REDACTED])")
    }
}

impl CanonicalBitMask64Share {
    /// Transfer this reservation and erase its original storage.
    pub fn take_and_wipe(&mut self) -> Self {
        let material = Self {
            bit_shares: self.bit_shares,
            field_sum_share: self.field_sum_share,
            bit_macs: self.bit_macs,
            field_sum_mac: self.field_sum_mac,
        };
        self.wipe();
        material
    }
    fn wipe(&mut self) {
        wipe_goldilocks(&mut self.bit_shares);
        wipe_goldilocks(core::slice::from_mut(&mut self.field_sum_share));
        wipe_ext2(&mut self.bit_macs);
        wipe_ext2(core::slice::from_mut(&mut self.field_sum_mac));
    }
}
impl Drop for CanonicalBitMask64Share {
    fn drop(&mut self) {
        self.wipe();
    }
}

/// Per-party isolated vault of dealerless-preprocessed `Poseidon2` `Π_pow7` tuples,
/// `Goldilocks` Beaver triples, and canonical `< p` 64-bit A2B masks (`!Clone`, wiped on `Drop`,
/// permanently poisoned and zeroized on any `MacCheck` abort).
pub struct PreprocessedPoseidonPartyVault {
    pub party_id: usize,
    pub eval_point: Goldilocks,
    /// Degree-`< t` Shamir share $[\alpha]_p \in \mathbb{F}_{p^2}$ of the global SPDZ MAC key.
    pub mac_alpha_share: GoldilocksExt2,
    pub(super) pow7_tuples: Vec<AuthenticatedPower7Share>,
    pow7_cursor: usize,
    beaver_triples: Vec<GoldilocksBeaverShare>,
    beaver_cursor: usize,
    pub(super) a2b_masks: Vec<CanonicalBitMask64Share>,
    a2b_cursor: usize,
    poisoned: bool,
}

impl fmt::Debug for PreprocessedPoseidonPartyVault {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "PreprocessedPoseidonPartyVault(party={}, pow7_rem={}, beaver_rem={}, a2b_rem={}, poisoned={})",
            self.party_id,
            self.remaining_pow7(),
            self.remaining_beaver(),
            self.remaining_a2b(),
            self.poisoned
        )
    }
}

impl Drop for PreprocessedPoseidonPartyVault {
    fn drop(&mut self) {
        wipe_ext2(core::slice::from_mut(&mut self.mac_alpha_share));
    }
}

impl PreprocessedPoseidonPartyVault {
    /// Trusted dealer fixture for large online-protocol tests only. Small production
    /// preprocessing tests separately exercise OT, sacrifice and canonicality checks.
    #[cfg(test)]
    pub(crate) fn fill_two_party_online_fixture(
        vaults: &mut [Self],
        budget: (usize, usize, usize),
        rng: &mut PartyPrivateRng,
    ) {
        assert_eq!(vaults.len(), 2);
        let pts = [vaults[0].eval_point, vaults[1].eval_point];
        let alpha = open_and_check_degree_ext2(
            2,
            &pts,
            &[vaults[0].mac_alpha_share, vaults[1].mac_alpha_share],
            "online fixture alpha",
        )
        .unwrap();
        let share = |value: Goldilocks, rng: &mut PartyPrivateRng| {
            let slope = rng.next_goldilocks();
            let mac_slope = rng.next_ext2();
            pts.map(|x| {
                (
                    value + slope * x,
                    alpha.mul_base(value) + mac_slope.mul_base(x),
                )
            })
        };
        for vault in vaults.iter_mut() {
            assert_eq!(
                (
                    vault.remaining_pow7(),
                    vault.remaining_beaver(),
                    vault.remaining_a2b()
                ),
                (0, 0, 0)
            );
            vault.pow7_tuples.reserve(budget.0);
            vault.beaver_triples.reserve(budget.1);
            vault.a2b_masks.reserve(budget.2);
        }
        for _ in 0..budget.0 {
            let r = rng.next_goldilocks();
            let mut power = Goldilocks::ONE;
            let shares: [[(Goldilocks, GoldilocksExt2); 2]; 7] = core::array::from_fn(|_| {
                power *= r;
                share(power, rng)
            });
            for (p, vault) in vaults.iter_mut().enumerate() {
                vault.pow7_tuples.push(AuthenticatedPower7Share {
                    r_pows: core::array::from_fn(|k| shares[k][p].0),
                    r_macs: core::array::from_fn(|k| shares[k][p].1),
                    r1_mac: shares[0][p].1,
                });
            }
        }
        for _ in 0..budget.1 {
            let a = rng.next_goldilocks();
            let b = rng.next_goldilocks();
            let shares = [a, b, a * b].map(|x| share(x, rng));
            for (p, vault) in vaults.iter_mut().enumerate() {
                vault.beaver_triples.push(GoldilocksBeaverShare {
                    a: shares[0][p].0,
                    b: shares[1][p].0,
                    c: shares[2][p].0,
                    a_mac: shares[0][p].1,
                    b_mac: shares[1][p].1,
                    c_mac: shares[2][p].1,
                });
            }
        }
        for _ in 0..budget.2 {
            let r = rng.next_goldilocks().to_canonical_u64();
            let shares: [[(Goldilocks, GoldilocksExt2); 2]; 64] = core::array::from_fn(|bit| {
                share(Goldilocks::from_u64_reduced((r >> bit) & 1), rng)
            });
            for (p, vault) in vaults.iter_mut().enumerate() {
                let bit_shares = core::array::from_fn(|k| shares[k][p].0);
                let bit_macs = core::array::from_fn(|k| shares[k][p].1);
                let mut sum = Goldilocks::ZERO;
                let mut mac = GoldilocksExt2::ZERO;
                for k in 0..64 {
                    let weight = Goldilocks::from_u64_reduced(1u64 << k);
                    sum += weight * bit_shares[k];
                    mac += bit_macs[k].mul_base(weight);
                }
                vault.a2b_masks.push(CanonicalBitMask64Share {
                    bit_shares,
                    bit_macs,
                    field_sum_share: sum,
                    field_sum_mac: mac,
                });
            }
        }
    }

    /// Degree-`< t` Shamir correlation fixture for large online-protocol tests across any
    /// `(t, n)` quorum (`t >= 2`). Small preprocessing tests separately exercise full OT/sacrifice.
    #[cfg(any(test, feature = "testing-ephemeral"))]
    pub fn fill_quorum_online_fixture(
        t: usize,
        vaults: &mut [Self],
        budget: (usize, usize, usize),
        rng: &mut PartyPrivateRng,
    ) {
        let n = vaults.len();
        assert!(t >= 2 && t <= n);
        let pts: Vec<Goldilocks> = vaults.iter().map(|v| v.eval_point).collect();
        let alphas: Vec<GoldilocksExt2> = vaults.iter().map(|v| v.mac_alpha_share).collect();
        let alpha =
            open_and_check_degree_ext2(t, &pts, &alphas, "online quorum fixture alpha").unwrap();

        let share =
            |value: Goldilocks, rng: &mut PartyPrivateRng| -> Vec<(Goldilocks, GoldilocksExt2)> {
                let mut val_coeffs = Vec::with_capacity(t - 1);
                let mut mac_coeffs = Vec::with_capacity(t - 1);
                for _ in 1..t {
                    val_coeffs.push(rng.next_goldilocks());
                    mac_coeffs.push(rng.next_ext2());
                }
                pts.iter()
                    .map(|&x| {
                        let mut v_acc = value;
                        let mut m_acc = alpha.mul_base(value);
                        let mut x_pow = x;
                        for deg in 0..(t - 1) {
                            v_acc += val_coeffs[deg] * x_pow;
                            m_acc += mac_coeffs[deg].mul_base(x_pow);
                            x_pow *= x;
                        }
                        (v_acc, m_acc)
                    })
                    .collect()
            };

        for vault in vaults.iter_mut() {
            assert_eq!(
                (
                    vault.remaining_pow7(),
                    vault.remaining_beaver(),
                    vault.remaining_a2b()
                ),
                (0, 0, 0)
            );
            vault.pow7_tuples.reserve(budget.0);
            vault.beaver_triples.reserve(budget.1);
            vault.a2b_masks.reserve(budget.2);
        }
        for _ in 0..budget.0 {
            let r = rng.next_goldilocks();
            let mut power = Goldilocks::ONE;
            let shares: [Vec<(Goldilocks, GoldilocksExt2)>; 7] = core::array::from_fn(|_| {
                power *= r;
                share(power, rng)
            });
            for (p, vault) in vaults.iter_mut().enumerate() {
                vault.pow7_tuples.push(AuthenticatedPower7Share {
                    r_pows: core::array::from_fn(|k| shares[k][p].0),
                    r_macs: core::array::from_fn(|k| shares[k][p].1),
                    r1_mac: shares[0][p].1,
                });
            }
        }
        for _ in 0..budget.1 {
            let a = rng.next_goldilocks();
            let b = rng.next_goldilocks();
            let shares = [a, b, a * b].map(|x| share(x, rng));
            for (p, vault) in vaults.iter_mut().enumerate() {
                vault.beaver_triples.push(GoldilocksBeaverShare {
                    a: shares[0][p].0,
                    b: shares[1][p].0,
                    c: shares[2][p].0,
                    a_mac: shares[0][p].1,
                    b_mac: shares[1][p].1,
                    c_mac: shares[2][p].1,
                });
            }
        }
        for _ in 0..budget.2 {
            let r = rng.next_goldilocks().to_canonical_u64();
            let shares: [Vec<(Goldilocks, GoldilocksExt2)>; 64] = core::array::from_fn(|bit| {
                share(Goldilocks::from_u64_reduced((r >> bit) & 1), rng)
            });
            for (p, vault) in vaults.iter_mut().enumerate() {
                let bit_shares = core::array::from_fn(|k| shares[k][p].0);
                let bit_macs = core::array::from_fn(|k| shares[k][p].1);
                let mut sum = Goldilocks::ZERO;
                let mut mac = GoldilocksExt2::ZERO;
                for k in 0..64 {
                    let weight = Goldilocks::from_u64_reduced(1u64 << k);
                    sum += weight * bit_shares[k];
                    mac += bit_macs[k].mul_base(weight);
                }
                vault.a2b_masks.push(CanonicalBitMask64Share {
                    bit_shares,
                    bit_macs,
                    field_sum_share: sum,
                    field_sum_mac: mac,
                });
            }
        }
    }

    #[cfg(test)]
    pub(crate) fn empty_for_barrier_test(party_id: usize, eval_point: Goldilocks) -> Self {
        Self {
            party_id,
            eval_point,
            mac_alpha_share: GoldilocksExt2::ONE,
            pow7_tuples: Vec::new(),
            pow7_cursor: 0,
            beaver_triples: Vec::new(),
            beaver_cursor: 0,
            a2b_masks: Vec::new(),
            a2b_cursor: 0,
            poisoned: false,
        }
    }

    #[inline]
    pub fn is_poisoned(&self) -> bool {
        self.poisoned
    }

    /// Permanently burn the SPDZ MAC key share and wipe all remaining preprocessed material.
    pub fn poison_and_wipe(&mut self) {
        self.poisoned = true;
        wipe_ext2(core::slice::from_mut(&mut self.mac_alpha_share));
        self.pow7_tuples.clear();
        self.pow7_cursor = 0;
        self.beaver_triples.clear();
        self.beaver_cursor = 0;
        self.a2b_masks.clear();
        self.a2b_cursor = 0;
    }

    #[inline]
    pub fn remaining_pow7(&self) -> usize {
        if self.poisoned {
            0
        } else {
            self.pow7_tuples.len().saturating_sub(self.pow7_cursor)
        }
    }

    #[inline]
    pub fn remaining_beaver(&self) -> usize {
        if self.poisoned {
            0
        } else {
            self.beaver_triples.len().saturating_sub(self.beaver_cursor)
        }
    }

    #[inline]
    pub fn remaining_a2b(&self) -> usize {
        if self.poisoned {
            0
        } else {
            self.a2b_masks.len().saturating_sub(self.a2b_cursor)
        }
    }

    /// Monotonically burn a disjoint range before exposing its material. All quorums
    /// sharing this vault use the same cursor; abandoned reservations are never reclaimed.
    pub fn reserve_pow7(
        &mut self,
        count: usize,
    ) -> Result<Vec<AuthenticatedPower7Share>, PreprocessError> {
        let range = reserve_material(
            &mut self.pow7_cursor,
            self.pow7_tuples.len(),
            count,
            self.poisoned,
            "Poseidon2 pow7",
        )?;
        Ok(self.pow7_tuples[range]
            .iter_mut()
            .map(AuthenticatedPower7Share::take_and_wipe)
            .collect())
    }

    #[inline]
    pub fn pop_pow7(&mut self) -> Result<AuthenticatedPower7Share, PreprocessError> {
        let range = reserve_material(
            &mut self.pow7_cursor,
            self.pow7_tuples.len(),
            1,
            self.poisoned,
            "Poseidon2 pow7",
        )?;
        Ok(self.pow7_tuples[range.start].take_and_wipe())
    }

    /// Monotonically burn a disjoint range before exposing its material. All quorums
    /// sharing this vault use the same cursor; abandoned reservations are never reclaimed.
    pub fn reserve_beaver(
        &mut self,
        count: usize,
    ) -> Result<Vec<GoldilocksBeaverShare>, PreprocessError> {
        let range = reserve_material(
            &mut self.beaver_cursor,
            self.beaver_triples.len(),
            count,
            self.poisoned,
            "Goldilocks Beaver",
        )?;
        Ok(self.beaver_triples[range]
            .iter_mut()
            .map(GoldilocksBeaverShare::take_and_wipe)
            .collect())
    }

    #[inline]
    pub fn pop_beaver(&mut self) -> Result<GoldilocksBeaverShare, PreprocessError> {
        let range = reserve_material(
            &mut self.beaver_cursor,
            self.beaver_triples.len(),
            1,
            self.poisoned,
            "Goldilocks Beaver",
        )?;
        Ok(self.beaver_triples[range.start].take_and_wipe())
    }

    /// Monotonically burn a disjoint range before exposing its material. All quorums
    /// sharing this vault use the same cursor; abandoned reservations are never reclaimed.
    pub fn reserve_a2b_masks(
        &mut self,
        count: usize,
    ) -> Result<Vec<CanonicalBitMask64Share>, PreprocessError> {
        let range = reserve_material(
            &mut self.a2b_cursor,
            self.a2b_masks.len(),
            count,
            self.poisoned,
            "Poseidon2 A2B mask",
        )?;
        Ok(self.a2b_masks[range]
            .iter_mut()
            .map(CanonicalBitMask64Share::take_and_wipe)
            .collect())
    }

    #[inline]
    pub fn pop_a2b_mask(&mut self) -> Result<CanonicalBitMask64Share, PreprocessError> {
        let range = reserve_material(
            &mut self.a2b_cursor,
            self.a2b_masks.len(),
            1,
            self.poisoned,
            "Poseidon2 A2B mask",
        )?;
        Ok(self.a2b_masks[range.start].take_and_wipe())
    }
}
/// Evaluate 1 batch of parallel SPDZ-authenticated Shamir Beaver multiplications `[x_k * y_k]`,
/// opening `(delta_k, eps_k)` via `commit_and_open_spdz_goldilocks_batch_quorum` AND propagating
/// exact `GoldilocksExt2` SPDZ MAC shares `(out_shares, out_macs)`!
#[allow(clippy::too_many_arguments)]
fn eval_spdz_shamir_beaver_batch_goldilocks(
    session_id: &[u8; 32],
    t: usize,
    eval_points: &[Goldilocks],
    alpha_shamir: &[GoldilocksExt2],
    xs: &[Vec<Goldilocks>],
    xs_mac: &[Vec<GoldilocksExt2>],
    ys: &[Vec<Goldilocks>],
    ys_mac: &[Vec<GoldilocksExt2>],
    ta: &[Vec<Goldilocks>],
    ta_mac: &[Vec<GoldilocksExt2>],
    tb: &[Vec<Goldilocks>],
    tb_mac: &[Vec<GoldilocksExt2>],
    tc: &[Vec<Goldilocks>],
    tc_mac: &[Vec<GoldilocksExt2>],
    phase: &'static str,
    party_rngs: &mut [PartyPrivateRng],
    ot_mesh: &mut OtMesh,
) -> Result<(PartyValues<Goldilocks>, PartyValues<GoldilocksExt2>), PreprocessError> {
    let n = eval_points.len();
    let count = xs[0].len();
    if count == 0 {
        return Ok((vec![Vec::new(); n], vec![Vec::new(); n]));
    }
    let mut de_sh = crate::wipe::secret_vecs_with_capacity(n, 2 * count);
    let mut de_mac = crate::wipe::secret_vecs_with_capacity(n, 2 * count);
    for p in 0..n {
        for k in 0..count {
            de_sh[p].push(xs[p][k] - ta[p][k]);
            de_mac[p].push(xs_mac[p][k] - ta_mac[p][k]);
            de_sh[p].push(ys[p][k] - tb[p][k]);
            de_mac[p].push(ys_mac[p][k] - tb_mac[p][k]);
        }
    }
    let opened = commit_and_open_spdz_goldilocks_batch_quorum_with_mesh(
        session_id,
        phase,
        t,
        eval_points,
        &de_sh,
        &de_mac,
        alpha_shamir,
        party_rngs,
        Some(ot_mesh),
    )?;

    let mut out = vec![vec![Goldilocks::ZERO; count]; n];
    let mut out_mac = vec![vec![GoldilocksExt2::ZERO; count]; n];
    for k in 0..count {
        let delta = opened[2 * k];
        let eps = opened[2 * k + 1];
        let de = delta * eps;
        for p in 0..n {
            out[p][k] = tc[p][k] + delta * tb[p][k] + eps * ta[p][k] + de;
            out_mac[p][k] = tc_mac[p][k]
                + tb_mac[p][k].mul_base(delta)
                + ta_mac[p][k].mul_base(eps)
                + alpha_shamir[p].mul_base(de);
        }
    }
    Ok((out, out_mac))
}

/// Generate a pool of SPDZ-MAC-authenticated `Goldilocks` Beaver triples verified via
/// SPDZ-MAC-authenticated `GoldilocksExt2` companion sacrifice (`< 2^{-127}` soundness, `0`
/// unauthenticated openings even under dishonest majority!).
#[expect(
    clippy::too_many_arguments,
    reason = "Quorum, value shares, MAC shares and private randomness are separate protocol inputs"
)]
fn generate_verified_spdz_beaver_pool_goldilocks<F>(
    session_id: &[u8; 32],
    t: usize,
    eval_points: &[Goldilocks],
    ot_mesh: &mut OtMesh,
    alpha_contribs: &[GoldilocksExt2],
    alpha_shamir: &[GoldilocksExt2],
    count: usize,
    party_rngs: &mut [PartyPrivateRng],
    fault_hook: &mut F,
) -> Result<GoldilocksBeaverMaterial, PreprocessError>
where
    F: FnMut(usize, &mut [Goldilocks]),
{
    let n = eval_points.len();
    if count == 0 {
        return Ok((
            vec![Vec::new(); n],
            vec![Vec::new(); n],
            vec![Vec::new(); n],
            vec![Vec::new(); n],
            vec![Vec::new(); n],
            vec![Vec::new(); n],
        ));
    }

    let ole_pairs = 3 * count;
    let mut u_vec = vec![vec![Goldilocks::ZERO; ole_pairs]; n];
    let mut v_vec = vec![vec![Goldilocks::ZERO; ole_pairs]; n];
    for i in 0..n {
        for k in 0..count {
            let ai = party_rngs[i].next_goldilocks();
            let bi = party_rngs[i].next_goldilocks();
            let at0 = party_rngs[i].next_goldilocks();
            let at1 = party_rngs[i].next_goldilocks();
            u_vec[i][3 * k] = ai;
            v_vec[i][3 * k] = bi;
            u_vec[i][3 * k + 1] = at0;
            v_vec[i][3 * k + 1] = bi;
            u_vec[i][3 * k + 2] = at1;
            v_vec[i][3 * k + 2] = bi;
        }
    }
    let mut w_vec = pairwise_gilboa_ole_goldilocks(ot_mesh, &u_vec, &v_vec, party_rngs)?;

    let mut a_sh = vec![vec![Goldilocks::ZERO; count]; n];
    let mut b_sh = vec![vec![Goldilocks::ZERO; count]; n];
    let mut c_sh = vec![vec![Goldilocks::ZERO; count]; n];
    let mut at0_sh = vec![vec![Goldilocks::ZERO; count]; n];
    let mut at1_sh = vec![vec![Goldilocks::ZERO; count]; n];
    let mut ct0_sh = vec![vec![Goldilocks::ZERO; count]; n];
    let mut ct1_sh = vec![vec![Goldilocks::ZERO; count]; n];

    for i in 0..n {
        for k in 0..count {
            let sa = shamir_share_goldilocks(t, eval_points, u_vec[i][3 * k], &mut party_rngs[i]);
            let sb = shamir_share_goldilocks(t, eval_points, v_vec[i][3 * k], &mut party_rngs[i]);
            let sc = shamir_share_goldilocks(t, eval_points, w_vec[i][3 * k], &mut party_rngs[i]);
            let sat0 =
                shamir_share_goldilocks(t, eval_points, u_vec[i][3 * k + 1], &mut party_rngs[i]);
            let sat1 =
                shamir_share_goldilocks(t, eval_points, u_vec[i][3 * k + 2], &mut party_rngs[i]);
            let sct0 =
                shamir_share_goldilocks(t, eval_points, w_vec[i][3 * k + 1], &mut party_rngs[i]);
            let sct1 =
                shamir_share_goldilocks(t, eval_points, w_vec[i][3 * k + 2], &mut party_rngs[i]);
            for p in 0..n {
                a_sh[p][k] += sa[p];
                b_sh[p][k] += sb[p];
                c_sh[p][k] += sc[p];
                at0_sh[p][k] += sat0[p];
                at1_sh[p][k] += sat1[p];
                ct0_sh[p][k] += sct0[p];
                ct1_sh[p][k] += sct1[p];
            }
        }
        wipe_goldilocks(&mut u_vec[i]);
        wipe_goldilocks(&mut v_vec[i]);
        wipe_goldilocks(&mut w_vec[i]);
    }

    for (p, c_sh_p_item) in c_sh[..n].iter_mut().enumerate() {
        fault_hook(p, &mut *c_sh_p_item);
    }

    // Authenticate all `7 * count` wires under the global SPDZ MAC BEFORE sacrifice!
    let packed: Vec<Vec<Goldilocks>> = (0..n)
        .map(|p| {
            let mut v = Vec::with_capacity(7 * count);
            v.extend_from_slice(&a_sh[p]);
            v.extend_from_slice(&b_sh[p]);
            v.extend_from_slice(&c_sh[p]);
            v.extend_from_slice(&at0_sh[p]);
            v.extend_from_slice(&at1_sh[p]);
            v.extend_from_slice(&ct0_sh[p]);
            v.extend_from_slice(&ct1_sh[p]);
            v
        })
        .collect();
    let all_macs = spdz_authenticate_goldilocks_batch_ext2(
        session_id,
        t,
        eval_points,
        ot_mesh,
        alpha_contribs,
        alpha_shamir,
        &packed,
        party_rngs,
    )?;

    let mut a_mac = vec![vec![GoldilocksExt2::ZERO; count]; n];
    let mut b_mac = vec![vec![GoldilocksExt2::ZERO; count]; n];
    let mut c_mac = vec![vec![GoldilocksExt2::ZERO; count]; n];
    let mut at0_mac = vec![vec![GoldilocksExt2::ZERO; count]; n];
    let mut at1_mac = vec![vec![GoldilocksExt2::ZERO; count]; n];
    let mut ct0_mac = vec![vec![GoldilocksExt2::ZERO; count]; n];
    let mut ct1_mac = vec![vec![GoldilocksExt2::ZERO; count]; n];
    for p in 0..n {
        a_mac[p].copy_from_slice(&all_macs[p][0..count]);
        b_mac[p].copy_from_slice(&all_macs[p][count..2 * count]);
        c_mac[p].copy_from_slice(&all_macs[p][2 * count..3 * count]);
        at0_mac[p].copy_from_slice(&all_macs[p][3 * count..4 * count]);
        at1_mac[p].copy_from_slice(&all_macs[p][4 * count..5 * count]);
        ct0_mac[p].copy_from_slice(&all_macs[p][5 * count..6 * count]);
        ct1_mac[p].copy_from_slice(&all_macs[p][6 * count..7 * count]);
    }

    // SPDZ-MAC-authenticated `GoldilocksExt2` companion sacrifice (`< 2^{-127}`, `0` unauthenticated openings!)
    let coin = run_commit_and_open_coin(session_id, b"PI_POW7_SACRIFICE", session_id, party_rngs)?;
    let rho = GoldilocksExt2::new(
        Goldilocks::from_bytes24_unbiased(&core::array::from_fn(|array_index| {
            (coin[0..24])[array_index]
        })),
        Goldilocks::from_u128_reduced(
            u128::from_le_bytes(core::array::from_fn(|array_index| {
                (coin[16..32])[array_index]
            })) | 1,
        ),
    );

    let mut u_coords_sh = crate::wipe::secret_vecs_with_capacity(n, 2 * count);
    let mut u_coords_mac = crate::wipe::secret_vecs_with_capacity(n, 2 * count);
    for p in 0..n {
        for k in 0..count {
            // `u = rho * a_k - (at0_k + u * at1_k)`
            u_coords_sh[p].push(rho.c0 * a_sh[p][k] - at0_sh[p][k]);
            u_coords_mac[p].push(a_mac[p][k].mul_base(rho.c0) - at0_mac[p][k]);
            u_coords_sh[p].push(rho.c1 * a_sh[p][k] - at1_sh[p][k]);
            u_coords_mac[p].push(a_mac[p][k].mul_base(rho.c1) - at1_mac[p][k]);
        }
    }
    let u_opened = commit_and_open_spdz_goldilocks_batch_quorum_with_mesh(
        session_id,
        "pi_pow7_sac_u",
        t,
        eval_points,
        &u_coords_sh,
        &u_coords_mac,
        alpha_shamir,
        party_rngs,
        Some(ot_mesh),
    )?;

    let mut res_coords_sh = crate::wipe::secret_vecs_with_capacity(n, 2 * count);
    let mut res_coords_mac = crate::wipe::secret_vecs_with_capacity(n, 2 * count);
    for p in 0..n {
        for k in 0..count {
            let u_op = GoldilocksExt2::new(u_opened[2 * k], u_opened[2 * k + 1]);
            res_coords_sh[p].push((rho.c0 * c_sh[p][k] - ct0_sh[p][k]) - u_op.c0 * b_sh[p][k]);
            res_coords_mac[p].push(
                (c_mac[p][k].mul_base(rho.c0) - ct0_mac[p][k]) - b_mac[p][k].mul_base(u_op.c0),
            );
            res_coords_sh[p].push((rho.c1 * c_sh[p][k] - ct1_sh[p][k]) - u_op.c1 * b_sh[p][k]);
            res_coords_mac[p].push(
                (c_mac[p][k].mul_base(rho.c1) - ct1_mac[p][k]) - b_mac[p][k].mul_base(u_op.c1),
            );
        }
        wipe_goldilocks(&mut at0_sh[p]);
        wipe_goldilocks(&mut at1_sh[p]);
        wipe_goldilocks(&mut ct0_sh[p]);
        wipe_goldilocks(&mut ct1_sh[p]);
        wipe_ext2(&mut at0_mac[p]);
        wipe_ext2(&mut at1_mac[p]);
        wipe_ext2(&mut ct0_mac[p]);
        wipe_ext2(&mut ct1_mac[p]);
    }
    let res_opened = commit_and_open_spdz_goldilocks_batch_quorum_with_mesh(
        session_id,
        "pi_pow7_sac_res",
        t,
        eval_points,
        &res_coords_sh,
        &res_coords_mac,
        alpha_shamir,
        party_rngs,
        Some(ot_mesh),
    )?;
    for &rv in &res_opened {
        if rv != Goldilocks::ZERO {
            return Err(PreprocessError::SacrificeResidualNonZero { phase: "pi_pow7" });
        }
    }

    Ok((a_sh, b_sh, c_sh, a_mac, b_mac, c_mac))
}

/// Run the **100% dealerless `Π_pow7` + Canonical `< p` A2B** offline preprocessing protocol:
/// - Dealerless `GoldilocksExt2` Shamir SPDZ MAC setup (`spdz_setup_alpha_goldilocks`);
/// - LHL-amplified Gilboa OLE (`< 2^{-129}` selective-failure immunity, `< 2^{-192}` unbiased pads);
/// - SPDZ-MAC-authenticated `GoldilocksExt2` companion sacrifice (`< 2^{-127}` soundness, `0`
///   unauthenticated openings even under dishonest majority!);
/// - 3-round SPDZ-MAC-propagating Beaver power-tree (`evalPow7BeaverTree`) producing all 7
///   authenticated powers `r_pows[0..7]` + `r_macs[0..7]`;
/// - Exact `while` loop producing `num_a2b_masks` canonical `< p` 64-bit A2B bit-masks
///   verified via $b_k^2 - b_k = 0$ and `is_ge_p == 0` under SPDZ `MacCheck`.
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the public preprocessing API used by other protocol modules"
)]
pub fn run_dealerless_pi_pow7(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[Goldilocks],
    num_pow7: usize,
    num_extra_beaver: usize,
    num_a2b_masks: usize,
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<PreprocessedPoseidonPartyVault>, PreprocessError> {
    run_dealerless_pi_pow7_with_fault(
        session_id,
        t,
        eval_points,
        num_pow7,
        num_extra_beaver,
        num_a2b_masks,
        ot_mesh,
        party_rngs,
        |_, _| {},
    )
}

/// Fault-injectable entry point for adversarial unit tests of `Π_pow7`.
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the public preprocessing API used by other protocol modules"
)]
pub fn run_dealerless_pi_pow7_with_fault<F>(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[Goldilocks],
    num_pow7: usize,
    num_extra_beaver: usize,
    num_a2b_masks: usize,
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
    fault_hook: F,
) -> Result<Vec<PreprocessedPoseidonPartyVault>, PreprocessError>
where
    F: FnMut(usize, &mut [Goldilocks]),
{
    let n = eval_points.len();
    if t == 0 || t > n || party_rngs.len() != n || ot_mesh.n != n {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_goldilocks(eval_points)?;

    let (mut alpha_contribs, mut alpha_shamir) =
        spdz_setup_alpha_goldilocks(&session_id, t, eval_points, party_rngs)?;
    let res = run_dealerless_pi_pow7_with_alpha_and_fault(
        session_id,
        t,
        eval_points,
        num_pow7,
        num_extra_beaver,
        num_a2b_masks,
        &alpha_contribs,
        &alpha_shamir,
        ot_mesh,
        party_rngs,
        fault_hook,
    );
    wipe_ext2(&mut alpha_contribs);
    wipe_ext2(&mut alpha_shamir);
    res
}

/// Run dealerless `Π_pow7` + Canonical `< p` A2B bound to an existing session SPDZ MAC key
/// `(alpha_contribs, alpha_shamir)` (used when Poseidon2 key shares and `PreprocessedPoseidonPartyVault`
/// share a single global `GoldilocksExt2` MAC key $\alpha$).
#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the public preprocessing API used by other protocol modules"
)]
pub fn run_dealerless_pi_pow7_with_alpha(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[Goldilocks],
    num_pow7: usize,
    num_extra_beaver: usize,
    num_a2b_masks: usize,
    alpha_contribs: &[GoldilocksExt2],
    alpha_shamir: &[GoldilocksExt2],
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
) -> Result<Vec<PreprocessedPoseidonPartyVault>, PreprocessError> {
    run_dealerless_pi_pow7_with_alpha_and_fault(
        session_id,
        t,
        eval_points,
        num_pow7,
        num_extra_beaver,
        num_a2b_masks,
        alpha_contribs,
        alpha_shamir,
        ot_mesh,
        party_rngs,
        |_, _| {},
    )
}

#[expect(
    clippy::too_many_arguments,
    reason = "Preserve the public preprocessing API used by other protocol modules"
)]
fn run_dealerless_pi_pow7_with_alpha_and_fault<F>(
    session_id: [u8; 32],
    t: usize,
    eval_points: &[Goldilocks],
    num_pow7: usize,
    num_extra_beaver: usize,
    num_a2b_masks: usize,
    alpha_contribs: &[GoldilocksExt2],
    alpha_shamir: &[GoldilocksExt2],
    ot_mesh: &mut OtMesh,
    party_rngs: &mut [PartyPrivateRng],
    mut fault_hook: F,
) -> Result<Vec<PreprocessedPoseidonPartyVault>, PreprocessError>
where
    F: FnMut(usize, &mut [Goldilocks]),
{
    let n = eval_points.len();
    if t == 0
        || t > n
        || party_rngs.len() != n
        || ot_mesh.n != n
        || alpha_contribs.len() != n
        || alpha_shamir.len() != n
    {
        return Err(PreprocessError::InvalidThreshold { t, n });
    }
    validate_all_eval_points_goldilocks(eval_points)?;

    let base_triples = 6 * num_pow7 + num_extra_beaver;
    let (mut a_sh, mut b_sh, mut c_sh, mut a_mac, mut b_mac, mut c_mac) =
        generate_verified_spdz_beaver_pool_goldilocks(
            &session_id,
            t,
            eval_points,
            ot_mesh,
            alpha_contribs,
            alpha_shamir,
            base_triples,
            party_rngs,
            &mut fault_hook,
        )?;

    // Joint `Π_rand` + SPDZ `Π_MAC` + 3-Round Parallel Beaver Power-Tree (`evalPow7BeaverTree`)
    let mut r1_sh = vec![vec![Goldilocks::ZERO; num_pow7]; n];
    for party_rngs_i_item in party_rngs[..n].iter_mut() {
        #[expect(
            clippy::needless_range_loop,
            reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
        )]
        for k in 0..num_pow7 {
            let ri = (*party_rngs_i_item).next_goldilocks();
            let s_ri = shamir_share_goldilocks(t, eval_points, ri, &mut *party_rngs_i_item);
            for p in 0..n {
                r1_sh[p][k] += s_ri[p];
            }
        }
    }
    let r1_mac = spdz_authenticate_goldilocks_batch_ext2(
        &session_id,
        t,
        eval_points,
        ot_mesh,
        alpha_contribs,
        alpha_shamir,
        &r1_sh,
        party_rngs,
    )?;

    let slice_spdz_triples = |a: &[Vec<Goldilocks>],
                              b: &[Vec<Goldilocks>],
                              c: &[Vec<Goldilocks>],
                              am: &[Vec<GoldilocksExt2>],
                              bm: &[Vec<GoldilocksExt2>],
                              cm: &[Vec<GoldilocksExt2>],
                              start: usize,
                              len: usize| {
        let ta: Vec<Vec<Goldilocks>> = (0..n).map(|p| a[p][start..start + len].to_vec()).collect();
        let tb: Vec<Vec<Goldilocks>> = (0..n).map(|p| b[p][start..start + len].to_vec()).collect();
        let tc: Vec<Vec<Goldilocks>> = (0..n).map(|p| c[p][start..start + len].to_vec()).collect();
        let tam: Vec<Vec<GoldilocksExt2>> =
            (0..n).map(|p| am[p][start..start + len].to_vec()).collect();
        let tbm: Vec<Vec<GoldilocksExt2>> =
            (0..n).map(|p| bm[p][start..start + len].to_vec()).collect();
        let tcm: Vec<Vec<GoldilocksExt2>> =
            (0..n).map(|p| cm[p][start..start + len].to_vec()).collect();
        (ta, tb, tc, tam, tbm, tcm)
    };

    let (
        (mut r2_sh, mut r2_mac),
        (mut r3_sh, mut r3_mac),
        (mut r4_sh, mut r4_mac),
        (mut r5_sh, mut r5_mac),
        (mut r6_sh, mut r6_mac),
        (mut r7_sh, mut r7_mac),
    ) = if num_pow7 > 0 {
        let (t2a, t2b, t2c, t2am, t2bm, t2cm) =
            slice_spdz_triples(&a_sh, &b_sh, &c_sh, &a_mac, &b_mac, &c_mac, 0, num_pow7);
        let (t3a, t3b, t3c, t3am, t3bm, t3cm) = slice_spdz_triples(
            &a_sh, &b_sh, &c_sh, &a_mac, &b_mac, &c_mac, num_pow7, num_pow7,
        );
        let (t4a, t4b, t4c, t4am, t4bm, t4cm) = slice_spdz_triples(
            &a_sh,
            &b_sh,
            &c_sh,
            &a_mac,
            &b_mac,
            &c_mac,
            2 * num_pow7,
            num_pow7,
        );
        let (t5a, t5b, t5c, t5am, t5bm, t5cm) = slice_spdz_triples(
            &a_sh,
            &b_sh,
            &c_sh,
            &a_mac,
            &b_mac,
            &c_mac,
            3 * num_pow7,
            num_pow7,
        );
        let (t6a, t6b, t6c, t6am, t6bm, t6cm) = slice_spdz_triples(
            &a_sh,
            &b_sh,
            &c_sh,
            &a_mac,
            &b_mac,
            &c_mac,
            4 * num_pow7,
            num_pow7,
        );
        let (t7a, t7b, t7c, t7am, t7bm, t7cm) = slice_spdz_triples(
            &a_sh,
            &b_sh,
            &c_sh,
            &a_mac,
            &b_mac,
            &c_mac,
            5 * num_pow7,
            num_pow7,
        );

        let (r2, r2m) = eval_spdz_shamir_beaver_batch_goldilocks(
            &session_id,
            t,
            eval_points,
            alpha_shamir,
            &r1_sh,
            &r1_mac,
            &r1_sh,
            &r1_mac,
            &t2a,
            &t2am,
            &t2b,
            &t2bm,
            &t2c,
            &t2cm,
            "pow7_r2",
            party_rngs,
            ot_mesh,
        )?;
        let (r3, r3m) = eval_spdz_shamir_beaver_batch_goldilocks(
            &session_id,
            t,
            eval_points,
            alpha_shamir,
            &r2,
            &r2m,
            &r1_sh,
            &r1_mac,
            &t3a,
            &t3am,
            &t3b,
            &t3bm,
            &t3c,
            &t3cm,
            "pow7_r3",
            party_rngs,
            ot_mesh,
        )?;
        let (r4, r4m) = eval_spdz_shamir_beaver_batch_goldilocks(
            &session_id,
            t,
            eval_points,
            alpha_shamir,
            &r2,
            &r2m,
            &r2,
            &r2m,
            &t4a,
            &t4am,
            &t4b,
            &t4bm,
            &t4c,
            &t4cm,
            "pow7_r4",
            party_rngs,
            ot_mesh,
        )?;
        let (r5, r5m) = eval_spdz_shamir_beaver_batch_goldilocks(
            &session_id,
            t,
            eval_points,
            alpha_shamir,
            &r4,
            &r4m,
            &r1_sh,
            &r1_mac,
            &t5a,
            &t5am,
            &t5b,
            &t5bm,
            &t5c,
            &t5cm,
            "pow7_r5",
            party_rngs,
            ot_mesh,
        )?;
        let (r6, r6m) = eval_spdz_shamir_beaver_batch_goldilocks(
            &session_id,
            t,
            eval_points,
            alpha_shamir,
            &r4,
            &r4m,
            &r2,
            &r2m,
            &t6a,
            &t6am,
            &t6b,
            &t6bm,
            &t6c,
            &t6cm,
            "pow7_r6",
            party_rngs,
            ot_mesh,
        )?;
        let (r7, r7m) = eval_spdz_shamir_beaver_batch_goldilocks(
            &session_id,
            t,
            eval_points,
            alpha_shamir,
            &r4,
            &r4m,
            &r3,
            &r3m,
            &t7a,
            &t7am,
            &t7b,
            &t7bm,
            &t7c,
            &t7cm,
            "pow7_r7",
            party_rngs,
            ot_mesh,
        )?;
        (
            (r2, r2m),
            (r3, r3m),
            (r4, r4m),
            (r5, r5m),
            (r6, r6m),
            (r7, r7m),
        )
    } else {
        (
            (vec![Vec::new(); n], vec![Vec::new(); n]),
            (vec![Vec::new(); n], vec![Vec::new(); n]),
            (vec![Vec::new(); n], vec![Vec::new(); n]),
            (vec![Vec::new(); n], vec![Vec::new(); n]),
            (vec![Vec::new(); n], vec![Vec::new(); n]),
            (vec![Vec::new(); n], vec![Vec::new(); n]),
        )
    };

    // Dealerless Canonical `< p` 64-Bit A2B Masks (`while` loop guarantees exact `num_a2b_masks`!)
    let mut a2b_masks_per_party: Vec<Vec<CanonicalBitMask64Share>> =
        (0..n).map(|_| Vec::with_capacity(num_a2b_masks)).collect();

    while a2b_masks_per_party[0].len() < num_a2b_masks {
        let need = num_a2b_masks - a2b_masks_per_party[0].len();
        let batch_cands = need + 1;
        let total_bits = 64 * batch_cands;

        // Fold each party's private random bits via LHL-amplified `pairwise_gilboa_ole_goldilocks`
        // (`B ^ c_i = B + c_i - 2 * B * c_i` — `0` un-combined OT choice bits!)
        let mut cur_shares = vec![vec![Goldilocks::ZERO; total_bits]; n];
        #[expect(
            clippy::needless_range_loop,
            reason = "Indices address overlapping party matrices; retain explicit indexing instead of conflicting borrows"
        )]
        for m in 0..total_bits {
            let b0 = party_rngs[0].next_u64() & 1;
            cur_shares[0][m] = Goldilocks::from_u64_reduced(b0);
        }
        for i in 1..n {
            let mut u_party = vec![vec![Goldilocks::ZERO; total_bits]; n];
            let mut v_party = vec![vec![Goldilocks::ZERO; total_bits]; n];
            for m in 0..total_bits {
                let ci = party_rngs[i].next_u64() & 1;
                u_party[i][m] = Goldilocks::from_u64_reduced(ci);
                for p in 0..n {
                    v_party[p][m] = cur_shares[p][m];
                }
            }
            let mut prod = pairwise_gilboa_ole_goldilocks(ot_mesh, &u_party, &v_party, party_rngs)?;
            for m in 0..total_bits {
                cur_shares[i][m] += u_party[i][m];
                for p in 0..n {
                    let two_prod = prod[p][m] + prod[p][m];
                    cur_shares[p][m] -= two_prod;
                }
            }
            for p in 0..n {
                wipe_goldilocks(&mut u_party[p]);
                wipe_goldilocks(&mut v_party[p]);
                wipe_goldilocks(&mut prod[p]);
            }
        }

        let mut b_shamir = vec![vec![Goldilocks::ZERO; total_bits]; n];
        for i in 0..n {
            for m in 0..total_bits {
                let sb =
                    shamir_share_goldilocks(t, eval_points, cur_shares[i][m], &mut party_rngs[i]);
                for p in 0..n {
                    b_shamir[p][m] += sb[p];
                }
            }
            wipe_goldilocks(&mut cur_shares[i]);
        }

        let b_mac = spdz_authenticate_goldilocks_batch_ext2(
            &session_id,
            t,
            eval_points,
            ot_mesh,
            alpha_contribs,
            alpha_shamir,
            &b_shamir,
            party_rngs,
        )?;

        // Generate `127 * batch_cands` verified SPDZ Beaver triples:
        // - `64 * batch_cands` to prove `b_m^2 - b_m == 0` under SPDZ `MacCheck`
        // - `63 * batch_cands` to evaluate exact `is_ge_p == 0` under SPDZ `MacCheck`
        let mut no_fault = |_: usize, _: &mut [Goldilocks]| {};
        let (ba, bb, bc, bam, bbm, bcm) = generate_verified_spdz_beaver_pool_goldilocks(
            &session_id,
            t,
            eval_points,
            ot_mesh,
            alpha_contribs,
            alpha_shamir,
            127 * batch_cands,
            party_rngs,
            &mut no_fault,
        )?;

        let (sq_a, sq_b, sq_c, sq_am, sq_bm, sq_cm) =
            slice_spdz_triples(&ba, &bb, &bc, &bam, &bbm, &bcm, 0, total_bits);
        let (bsq_sh, bsq_mac) = eval_spdz_shamir_beaver_batch_goldilocks(
            &session_id,
            t,
            eval_points,
            alpha_shamir,
            &b_shamir,
            &b_mac,
            &b_shamir,
            &b_mac,
            &sq_a,
            &sq_am,
            &sq_b,
            &sq_bm,
            &sq_c,
            &sq_cm,
            "a2b_bit_sq",
            party_rngs,
            ot_mesh,
        )?;
        let diff_sh: Vec<Vec<Goldilocks>> = (0..n)
            .map(|p| {
                (0..total_bits)
                    .map(|m| bsq_sh[p][m] - b_shamir[p][m])
                    .collect()
            })
            .collect();
        let diff_mac: Vec<Vec<GoldilocksExt2>> = (0..n)
            .map(|p| {
                (0..total_bits)
                    .map(|m| bsq_mac[p][m] - b_mac[p][m])
                    .collect()
            })
            .collect();
        let diffs_opened = commit_and_open_spdz_goldilocks_batch_quorum_with_mesh(
            &session_id,
            "a2b_bool_diff",
            t,
            eval_points,
            &diff_sh,
            &diff_mac,
            alpha_shamir,
            party_rngs,
            Some(ot_mesh),
        )?;
        for &dv in &diffs_opened {
            if dv != Goldilocks::ZERO {
                return Err(PreprocessError::NonBooleanBitDetected { phase: "a2b_bits" });
            }
        }

        let mut t_off = total_bits;
        for cand in 0..batch_cands {
            if a2b_masks_per_party[0].len() == num_a2b_masks {
                break;
            }
            let mut cur_nodes: Vec<Vec<Goldilocks>> = (0..n)
                .map(|p| {
                    let mut v = Vec::with_capacity(64);
                    for k in 0..32 {
                        v.push(Goldilocks::ONE - b_shamir[p][64 * cand + k]);
                    }
                    for k in 32..64 {
                        v.push(b_shamir[p][64 * cand + k]);
                    }
                    v
                })
                .collect();
            let mut cur_macs: Vec<Vec<GoldilocksExt2>> = (0..n)
                .map(|p| {
                    let mut v = Vec::with_capacity(64);
                    for k in 0..32 {
                        v.push(alpha_shamir[p] - b_mac[p][64 * cand + k]);
                    }
                    for k in 32..64 {
                        v.push(b_mac[p][64 * cand + k]);
                    }
                    v
                })
                .collect();

            for _ in 0..5 {
                let pairs = cur_nodes[0].len() / 2;
                let lhs: Vec<Vec<Goldilocks>> = (0..n)
                    .map(|p| (0..pairs).map(|j| cur_nodes[p][2 * j]).collect())
                    .collect();
                let lhs_m: Vec<Vec<GoldilocksExt2>> = (0..n)
                    .map(|p| (0..pairs).map(|j| cur_macs[p][2 * j]).collect())
                    .collect();
                let rhs: Vec<Vec<Goldilocks>> = (0..n)
                    .map(|p| (0..pairs).map(|j| cur_nodes[p][2 * j + 1]).collect())
                    .collect();
                let rhs_m: Vec<Vec<GoldilocksExt2>> = (0..n)
                    .map(|p| (0..pairs).map(|j| cur_macs[p][2 * j + 1]).collect())
                    .collect();
                let (ta, tb, tc, tam, tbm, tcm) =
                    slice_spdz_triples(&ba, &bb, &bc, &bam, &bbm, &bcm, t_off, pairs);
                t_off += pairs;
                let (next_n, next_m) = eval_spdz_shamir_beaver_batch_goldilocks(
                    &session_id,
                    t,
                    eval_points,
                    alpha_shamir,
                    &lhs,
                    &lhs_m,
                    &rhs,
                    &rhs_m,
                    &ta,
                    &tam,
                    &tb,
                    &tbm,
                    &tc,
                    &tcm,
                    "a2b_ge_p_tree",
                    party_rngs,
                    ot_mesh,
                )?;
                cur_nodes = next_n;
                cur_macs = next_m;
            }

            let lhs: Vec<Vec<Goldilocks>> = (0..n).map(|p| alloc::vec![cur_nodes[p][1]]).collect();
            let lhs_m: Vec<Vec<GoldilocksExt2>> =
                (0..n).map(|p| alloc::vec![cur_macs[p][1]]).collect();
            let rhs: Vec<Vec<Goldilocks>> = (0..n)
                .map(|p| alloc::vec![Goldilocks::ONE - cur_nodes[p][0]])
                .collect();
            let rhs_m: Vec<Vec<GoldilocksExt2>> = (0..n)
                .map(|p| alloc::vec![alpha_shamir[p] - cur_macs[p][0]])
                .collect();
            let (ta, tb, tc, tam, tbm, tcm) =
                slice_spdz_triples(&ba, &bb, &bc, &bam, &bbm, &bcm, t_off, 1);
            t_off += 1;
            let (ge_p_vec, ge_p_mvec) = eval_spdz_shamir_beaver_batch_goldilocks(
                &session_id,
                t,
                eval_points,
                alpha_shamir,
                &lhs,
                &lhs_m,
                &rhs,
                &rhs_m,
                &ta,
                &tam,
                &tb,
                &tbm,
                &tc,
                &tcm,
                "a2b_ge_p_final",
                party_rngs,
                ot_mesh,
            )?;
            let ge_p_sh: Vec<Goldilocks> = (0..n).map(|p| ge_p_vec[p][0]).collect();
            let ge_p_mac: Vec<GoldilocksExt2> = (0..n).map(|p| ge_p_mvec[p][0]).collect();
            let is_ge_p = commit_and_open_spdz_goldilocks_quorum(
                &session_id,
                "a2b_ge_p_open",
                t,
                eval_points,
                &ge_p_sh,
                &ge_p_mac,
                alpha_shamir,
                party_rngs,
            )?;
            if is_ge_p == Goldilocks::ZERO {
                for p in 0..n {
                    let mut bit_shares = [Goldilocks::ZERO; 64];
                    let mut bit_macs = [GoldilocksExt2::ZERO; 64];
                    let mut sum_sh = Goldilocks::ZERO;
                    let mut sum_mac = GoldilocksExt2::ZERO;
                    for k in 0..64 {
                        let bk = b_shamir[p][64 * cand + k];
                        let bmk = b_mac[p][64 * cand + k];
                        let pow2 = Goldilocks::from_u64_reduced(1u64 << k);
                        bit_shares[k] = bk;
                        bit_macs[k] = bmk;
                        sum_sh += pow2 * bk;
                        sum_mac += bmk.mul_base(pow2);
                    }
                    a2b_masks_per_party[p].push(CanonicalBitMask64Share {
                        bit_shares,
                        field_sum_share: sum_sh,
                        bit_macs,
                        field_sum_mac: sum_mac,
                    });
                }
            }
        }
        for b_shamir_p_item in b_shamir[..n].iter_mut() {
            wipe_goldilocks(&mut *b_shamir_p_item);
        }
    }

    // Package isolated per-party vaults and wipe all temporary vectors
    let extra_start = 6 * num_pow7;
    let mut vaults = Vec::with_capacity(n);
    for p in 0..n {
        let mut pow7_tuples = Vec::with_capacity(num_pow7);
        for k in 0..num_pow7 {
            let r1_m = r1_mac[p][k];
            pow7_tuples.push(AuthenticatedPower7Share {
                r_pows: [
                    r1_sh[p][k],
                    r2_sh[p][k],
                    r3_sh[p][k],
                    r4_sh[p][k],
                    r5_sh[p][k],
                    r6_sh[p][k],
                    r7_sh[p][k],
                ],
                r_macs: [
                    r1_m,
                    r2_mac[p][k],
                    r3_mac[p][k],
                    r4_mac[p][k],
                    r5_mac[p][k],
                    r6_mac[p][k],
                    r7_mac[p][k],
                ],
                r1_mac: r1_m,
            });
        }
        wipe_goldilocks(&mut r1_sh[p]);
        wipe_goldilocks(&mut r2_sh[p]);
        wipe_goldilocks(&mut r3_sh[p]);
        wipe_goldilocks(&mut r4_sh[p]);
        wipe_goldilocks(&mut r5_sh[p]);
        wipe_goldilocks(&mut r6_sh[p]);
        wipe_goldilocks(&mut r7_sh[p]);
        wipe_ext2(&mut r2_mac[p]);
        wipe_ext2(&mut r3_mac[p]);
        wipe_ext2(&mut r4_mac[p]);
        wipe_ext2(&mut r5_mac[p]);
        wipe_ext2(&mut r6_mac[p]);
        wipe_ext2(&mut r7_mac[p]);

        let mut beaver_triples = Vec::with_capacity(num_extra_beaver);
        for k in 0..num_extra_beaver {
            let idx = extra_start + k;
            beaver_triples.push(GoldilocksBeaverShare {
                a: a_sh[p][idx],
                b: b_sh[p][idx],
                c: c_sh[p][idx],
                a_mac: a_mac[p][idx],
                b_mac: b_mac[p][idx],
                c_mac: c_mac[p][idx],
            });
        }
        wipe_goldilocks(&mut a_sh[p]);
        wipe_goldilocks(&mut b_sh[p]);
        wipe_goldilocks(&mut c_sh[p]);
        wipe_ext2(&mut a_mac[p]);
        wipe_ext2(&mut b_mac[p]);
        wipe_ext2(&mut c_mac[p]);

        let alpha = alpha_shamir[p];
        vaults.push(PreprocessedPoseidonPartyVault {
            party_id: p,
            eval_point: eval_points[p],
            mac_alpha_share: alpha,
            pow7_tuples,
            pow7_cursor: 0,
            beaver_triples,
            beaver_cursor: 0,
            a2b_masks: core::mem::take(&mut a2b_masks_per_party[p]),
            a2b_cursor: 0,
            poisoned: false,
        });
    }
    Ok(vaults)
}
