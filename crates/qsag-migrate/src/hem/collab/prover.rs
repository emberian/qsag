//! One custodian's side of the collaborative `zk-Hem v2` prover (`QuinticGoldilocks`).
//!
//! Every custodian runs [`prove_party`] with its MAC-authenticated shares of the
//! assignment (`Sb`) and ends with the same [`ZkHemV2SplitProof`] (`QSAGZKS2`), which it
//! verifies locally before returning.
//!
//! # Algebra & MPC Upgrades (`zk-Hem v2`)
//!
//! * **9-triple Toom-3 `Fp5` Beaver products:** Every extension-field multiplication in the
//!   row sumcheck (rounds `1..`), the LogUp lookup sumcheck, and the pre-opening SPDZ zero
//!   test runs [`Engine::mul_ext`] at `9` base-field triples per `Fp5` product (43.75%
//!   fewer triples than `Fp4` schoolbook's 16).
//! * **Per-tree 256-bit `tree_nonce`:** Each custodian samples a fresh 32-byte `tree_nonce`
//!   alongside its `salt_seed` and `mask_poly` for every Stage-0 Merkle tree, eliminating
//!   multi-tree salt birthday collisions across custodians and helper tables.
//! * **Authenticated Stage-0 folding (`0` triples):** After the SPDZ zero test confirms
//!   `<table, cell_weights> == value` (and `<helper, helper_weights> == helper_value`),
//!   custodians convert their authenticated hypercube shares to monomial shares locally and
//!   run WHIR Stage-0 Rounds 7–9 (`MASK_EVAL`, `FOLD_A`, `FOLD_B`) directly on authenticated
//!   `Sh` shares (`0` Beaver triples, MAC-checked before every round opening and before the
//!   reduced masked polynomial `g = P_s + beta_R R` is revealed).

use alloc::vec;
use alloc::vec::Vec;

use qsag_agg::field::Goldilocks;
use qsag_agg::pcs::hypercube_to_monomial_coeffs;
use qsag_agg::zk_hem::relation::{Csr, Lookups, Shape};
use qsag_agg::zk_hem::v2::field5::Fp5;
use qsag_agg::zk_hem::v2::hash::{Digest, Transcript};
use qsag_agg::zk_hem::v2::params::{
    COL_DEGREE, COL_MASK_BITS, DIGEST_BYTES, EXT_BYTES, LIMBS, LOOKUP_DEGREE, LOOKUP_MASK_BITS,
    LookupLayout, MASK_POINTS, Profile, ROW_DEGREE, ROW_MASK_BITS, Schedule, TREE_NONCE_BYTES,
};
use qsag_agg::zk_hem::v2::pcs::{
    self, Committed, MAX_STAGE0_SHARES, SplitOpening, Stage0Query,
};
use qsag_agg::zk_hem::v2::protocol::{
    FrontMessages, LookupMessages, Mask, SplitLookupV2Proof, ZkHemV2SplitProof,
    absorb_lookup_roots, cell_weights_to_kernel, column_table, eq_table, layout_of, limb_basis,
    lookup_column_add, lookup_masks_full_rank, replay_front, row_challenge_good, split_transcript,
    verify_split,
};

use qsag_core::wipe::{SecretBuffer, SecretScratch};

use super::engine::{EXT_MUL_TRIPLES, Engine, MpcError, Sb, Sh};
use super::net::Transport;

type E = Fp5;
type F = Goldilocks;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProveError {
    Mpc(MpcError),
    /// The relation does not fit a v2 commitment, or the quorum is too large.
    Unsupported,
    /// The relation has S-box rows.
    SboxRows,
    /// The share vector does not have one entry per variable.
    Malformed,
    /// A peer's Stage-0 opening or root does not decode.
    BadPeerMessage {
        from: usize,
    },
    /// A row or lookup challenge hit a degenerate point.
    DegenerateChallenge,
    /// A verifier coin fell outside the event `Good`; rerun with fresh material.
    MaskRankDeficient,
    /// The shared assignment does not satisfy the relation. Nothing that depends on the
    /// assignment beyond this one bit has been opened.
    Unsatisfied,
    /// The assembled proof does not verify: some custodian committed to tables that are
    /// not its shares, or opened a wrong leaf.
    Rejected,
}

impl From<MpcError> for ProveError {
    fn from(e: MpcError) -> Self {
        Self::Mpc(e)
    }
}

/// A point where a custodian may deviate, for adversarial tests: the hook receives what
/// the custodian is about to use or send and may change it.
pub enum Fault<'a> {
    /// The value table about to be committed (the custodian's shares of `Z`).
    Table(&'a mut Vec<F>),
    /// The share of a masked row-round polynomial about to be opened.
    RoundShare(&'a mut Vec<Sh>),
    /// The share of the reduced Stage-0 masked polynomial `g` about to be sent, 40 bytes/coeff.
    Word(&'a mut Vec<u8>),
    /// The Stage-0 leaves about to be opened.
    Leaves(&'a mut Stage0Query),
}

/// Triples and uniform values one custodian's [`prove_party`] consumes for `shape`.
pub fn prover_demand(shape: &Shape, _profile: Profile) -> Option<(usize, usize)> {
    if shape.num_sbox != 0 {
        return None;
    }
    let layout = layout_of(shape)?;
    let half = 1usize << (shape.log_rows - 1);
    // Round 0 multiplies base-field values (1 triple each); rounds 1.. multiply Fp5 values
    // via 9-triple Toom-3 (2 * 9 = 18 triples per pair); the zero test is 1 Fp5 product (9).
    let triples = 2 * half + (2 * EXT_MUL_TRIPLES) * (half - 1) + EXT_MUL_TRIPLES;
    let randoms = (shape.num_vars - shape.mask_var_base)
        + LIMBS * (shape.log_rows * (ROW_DEGREE + 1) + layout.var_bits * (COL_DEGREE + 1))
        + layout.blind_cells
        + LIMBS;
    let (lookup_triples, lookup_randoms) = match (shape.lookups(), &layout.lookup) {
        (Some(lookups), Some(ll)) => lookup_demand(lookups, ll)?,
        _ => (0, 0),
    };
    Some((triples + lookup_triples, randoms + lookup_randoms))
}

/// How the helper of one fraction is computed from shares.
enum Helper {
    /// Public value `v`: `h = n / (alpha - v)`.
    PublicValue,
    /// Public numerator and shared value with this many shared tuple columns.
    Inversion { shared_columns: usize },
}

/// The public constant a linear form evaluates to, if it has no other term.
fn public_form(matrix: &Csr, i: usize) -> Option<F> {
    matrix
        .row(i)
        .try_fold(F::ZERO, |acc, (col, val)| (col == 0).then_some(acc + val))
}

/// `None` for a fraction with a shared numerator over a shared value, which the builder
/// only places in the unconstrained masking corner `checked..`.
fn helper_kind(lookups: &Lookups, i: usize) -> Option<Helper> {
    let shared_columns = lookups
        .den
        .iter()
        .filter(|m| public_form(m, i).is_none())
        .count();
    if shared_columns == 0 {
        Some(Helper::PublicValue)
    } else {
        public_form(&lookups.num, i).map(|_| Helper::Inversion { shared_columns })
    }
}

/// Live pairs of lookup-sumcheck round `round`: those not entirely above the selector
/// boundary.
fn lookup_live_pairs(lookups: &Lookups, round: usize) -> usize {
    let pairs = lookups.num_entries() >> (round + 1);
    ((lookups.num_checked() >> round) / 2 + 1).min(pairs)
}

/// Triples and uniform values the lookup steps consume.
fn lookup_demand(lookups: &Lookups, ll: &LookupLayout) -> Option<(usize, usize)> {
    let d = lookups.log_entries;
    let (mut triples, mut randoms) = (0, 0);
    for i in 0..lookups.num_checked() {
        if let Helper::Inversion { shared_columns } = helper_kind(lookups, i)? {
            triples += LIMBS * shared_columns;
            randoms += LIMBS;
        }
    }
    triples += (0..d)
        .map(|round| (3 * EXT_MUL_TRIPLES) * lookup_live_pairs(lookups, round))
        .sum::<usize>();
    // Second zero-test product and its Fp5 multiplier.
    triples += EXT_MUL_TRIPLES;
    randoms += LIMBS * (lookups.num_entries() - lookups.num_checked()) + LIMBS * d * (LOOKUP_DEGREE + 1) + ll.blind_cells + LIMBS;
    Some((triples, randoms))
}

/// An authenticated separable sumcheck mask: the three SPDZ components (`v`, `m[0]`, `m[1]`)
/// of its `Fp5` coefficient shares.
struct MaskShare {
    parts: [Mask; 3],
}

impl MaskShare {
    fn new(coef: &[SecretScratch<Sh>]) -> Self {
        let part = |pick: fn(&Sh) -> E| {
            Mask::from_coeffs(coef.iter().map(|row| row.iter().map(pick).collect()).collect())
        };
        Self {
            parts: [part(|s| s.v), part(|s| s.m[0]), part(|s| s.m[1])],
        }
    }

    fn sum(&self) -> Sh {
        Sh {
            v: self.parts[0].sum(),
            m: [self.parts[1].sum(), self.parts[2].sum()],
        }
    }

    fn round_poly(&self, prefix: &[E]) -> SecretBuffer<Vec<Sh>> {
        let mut parts = self.parts.each_ref().map(|p| p.round_poly(prefix));
        let out = (0..parts[0].len()).map(|i| Sh {
            v: parts[0][i],
            m: [parts[1][i], parts[2][i]],
        }).collect();
        for part in &mut parts {
            qsag_asm::volatile_fill(part, E::ZERO);
        }
        SecretBuffer(out)
    }
}

/// Sample one separable mask: per round `degree + 1` coefficients, each from five uniform
/// base values, and write the corresponding hypercube values into `table`.
fn sample_mask<T: Transport>(
    e: &mut Engine<T>,
    table: &mut [Sb],
    rounds: usize,
    degree: usize,
    bits: usize,
    block: impl Fn(usize, usize) -> usize,
) -> Result<MaskShare, MpcError> {
    let unit = limb_basis();
    let mut coef = Vec::with_capacity(rounds);
    for i in 0..rounds {
        let mut cells = SecretScratch::from(vec![[Sb::ZERO; LIMBS]; 1 << bits]);
        let mut row = SecretScratch::with_capacity(degree + 1);
        for cell in cells.iter_mut().take(degree + 1) {
            let mut c = SecretBuffer(Sh::ZERO);
            for j in 0..LIMBS {
                cell[j] = e.random()?;
                *c += cell[j].scale_ext(unit[j]);
            }
            row.push(*c);
        }
        // Monomial coefficients to hypercube values, limb by limb.
        for b in 0..bits {
            for idx in 0..cells.len() {
                if (idx >> b) & 1 == 1 {
                    let lower = cells[idx ^ (1 << b)];
                    for j in 0..LIMBS {
                        cells[idx][j] += lower[j];
                    }
                }
            }
        }
        for j in 0..LIMBS {
            let off = block(i, j);
            for (slot, cell) in table[off..off + cells.len()].iter_mut().zip(&cells) {
                *slot = cell[j];
            }
        }
        coef.push(row);
    }
    Ok(MaskShare::new(&coef))
}

fn eval_poly_sh(coeffs: &[Sh], x: E) -> Sh {
    coeffs
        .iter()
        .rev()
        .fold(Sh::ZERO, |acc, &c| acc.scale(x) + c)
}

/// Add the masked share of a round polynomial: `poly + rho * mask`.
fn masked(poly: &[Sh], mut mask: SecretBuffer<Vec<Sh>>, rho: E) -> SecretBuffer<Vec<Sh>> {
    for (k, g) in mask.iter_mut().enumerate() {
        *g = g.scale(rho) + poly.get(k).copied().unwrap_or(Sh::ZERO);
    }
    mask
}

/// In-place hypercube-to-monomial Möbius transform on authenticated `Sb` shares.
fn hypercube_to_monomial_sb(coeffs: &mut [Sb]) {
    let n = coeffs.len();
    assert!(n.is_power_of_two());
    let vars = n.trailing_zeros() as usize;
    for b in 0..vars {
        let step = 1usize << b;
        for block in coeffs.chunks_exact_mut(step << 1) {
            let (lo, hi) = block.split_at_mut(step);
            for (l, h) in lo.iter().zip(hi.iter_mut()) {
                *h = *h - *l;
            }
        }
    }
}

/// Commit to the value part of `table` shares, a local random degree-bounded masking
/// polynomial `R^(c)`, a local `salt_seed`, and a fresh 256-bit `tree_nonce`.
fn commit_shares<T: Transport>(
    e: &mut Engine<T>,
    profile: Profile,
    log_cells: usize,
    table: &[Sb],
    schedule: &Schedule,
    fault: &mut dyn FnMut(Fault<'_>),
) -> Committed {
    let mut vals = SecretBuffer(table.iter().map(|s| s.v).collect::<Vec<_>>());
    fault(Fault::Table(&mut vals));
    let coeffs = hypercube_to_monomial_coeffs(&vals);
    drop(vals);

    let step_vars = schedule.stages[0].step_vars;
    let mask_len = pcs::mask_len(log_cells, step_vars);
    let mask_poly: Vec<E> = (0..mask_len).map(|_| e.local_ext()).collect();
    let mut salt_seed = [0u8; 32];
    for chunk in salt_seed.chunks_mut(8) {
        chunk.copy_from_slice(&e.local_base().to_le_bytes());
    }
    let mut tree_nonce = [0u8; TREE_NONCE_BYTES];
    for chunk in tree_nonce.chunks_mut(8) {
        chunk.copy_from_slice(&e.local_base().to_le_bytes());
    }
    let committed = pcs::commit(
        profile,
        log_cells,
        schedule,
        coeffs,
        mask_poly,
        &salt_seed,
        &tree_nonce,
    );
    qsag_asm::volatile_fill(&mut salt_seed, 0u8);
    committed
}

/// Broadcast `(tree_nonce, root)` and collect every custodian's pair in party order.
fn exchange_roots<T: Transport>(
    e: &mut Engine<T>,
    nonce: &[u8; TREE_NONCE_BYTES],
    root: &Digest,
) -> Result<(Vec<[u8; TREE_NONCE_BYTES]>, Vec<Digest>), ProveError> {
    let mut payload = Vec::with_capacity(TREE_NONCE_BYTES + DIGEST_BYTES);
    payload.extend_from_slice(nonce);
    payload.extend_from_slice(root);
    let messages = e.exchange(payload)?;
    let mut nonces = Vec::with_capacity(e.parties());
    let mut roots = Vec::with_capacity(e.parties());
    for (from, bytes) in messages.iter().enumerate() {
        if bytes.len() != TREE_NONCE_BYTES + DIGEST_BYTES {
            return Err(ProveError::BadPeerMessage { from });
        }
        nonces.push(bytes[..TREE_NONCE_BYTES].try_into().unwrap());
        roots.push(bytes[TREE_NONCE_BYTES..].try_into().unwrap());
    }
    Ok((nonces, roots))
}

struct RowOutput {
    mask_sum: E,
    rounds: Vec<Vec<E>>,
    point: Vec<E>,
    values: [E; 3],
}

/// Masked row sumcheck of `eq(tau, x) (a b - c)` on authenticated shares (`num_sbox == 0`).
fn row_sumcheck<T: Transport>(
    e: &mut Engine<T>,
    shape: &Shape,
    tr: &mut Transcript,
    tau: &[E],
    base: [SecretScratch<Sb>; 3],
    mask: &MaskShare,
    fault: &mut dyn FnMut(Fault<'_>),
) -> Result<RowOutput, ProveError> {
    let n = tau.len();
    e.check()?;
    let mask_sum = e.open_ext(&SecretBuffer([mask.sum()])[..])?[0];
    tr.absorb_fp5_slice(b"ROW_MASK_SUM", &[mask_sum]);
    let rho = tr.squeeze_fp5_nonzero(b"RHO1");

    let mut base = Some(base);
    let mut ext: [SecretScratch<Sh>; 3] = core::array::from_fn(|_| SecretScratch::new());
    let mut eq_rest = eq_table(&tau[1..]);
    let mut eq_bound = E::ONE;
    let mut claim = SecretBuffer(Sh::ZERO);
    let mut rounds = Vec::with_capacity(n);
    let mut point: Vec<E> = Vec::with_capacity(n);
    for &t in tau {
        let (l0, l1) = (eq_bound * (E::ONE - t), eq_bound * (t + t - E::ONE));
        if (l0 + l1).is_zero() {
            return Err(ProveError::DegenerateChallenge);
        }
        let sum_inv = (l0 + l1).inverse();
        let pairs = eq_rest.len();
        let (mut h0, mut h2) = (SecretBuffer(Sh::ZERO), SecretBuffer(Sh::ZERO));
        if let Some([a, b, c]) = &base {
            let mut xs = SecretScratch::with_capacity(2 * pairs);
            let mut ys = SecretScratch::with_capacity(2 * pairs);
            for k in 0..pairs {
                xs.extend([a[2 * k], a[2 * k + 1] - a[2 * k]]);
                ys.extend([b[2 * k], b[2 * k + 1] - b[2 * k]]);
            }
            let products = SecretScratch::from(e.mul(&xs, &ys)?);
            for k in 0..pairs {
                *h0 += (products[2 * k] - c[2 * k]).scale_ext(eq_rest[k]);
                *h2 += products[2 * k + 1].scale_ext(eq_rest[k]);
            }
        } else {
            let [a, b, c] = &ext;
            let mut xs = SecretScratch::with_capacity(2 * pairs);
            let mut ys = SecretScratch::with_capacity(2 * pairs);
            for k in 0..pairs {
                xs.extend([a[2 * k], a[2 * k + 1] - a[2 * k]]);
                ys.extend([b[2 * k], b[2 * k + 1] - b[2 * k]]);
            }
            let products = SecretScratch::from(e.mul_ext(&xs, &ys)?);
            for k in 0..pairs {
                *h0 += (products[2 * k] - c[2 * k]).scale(eq_rest[k]);
                *h2 += products[2 * k + 1].scale(eq_rest[k]);
            }
        }
        let h1 = SecretBuffer((*claim - h0.scale(l0)).scale(sum_inv) - *h0 - *h2);
        let pending = SecretBuffer([
            h0.scale(l0),
            h1.scale(l0) + h0.scale(l1),
            h2.scale(l0) + h1.scale(l1),
            h2.scale(l1),
        ]);
        let mut share = masked(&pending[..], mask.round_poly(&point), rho);
        fault(Fault::RoundShare(&mut share));
        e.check()?;
        let poly = e.open_ext(&share)?;
        tr.absorb_fp5_slice(b"ROW_ROUND", &poly);
        let c = tr.squeeze_fp5(b"ROW_ROUND");
        *claim = eval_poly_sh(&pending[..], c);
        if let Some(tables) = base.take() {
            for (dst, src) in ext.iter_mut().zip(&tables) {
                *dst = src
                    .chunks_exact(2)
                    .map(|p| p[0].lift() + (p[1] - p[0]).scale_ext(c))
                    .collect();
            }
        } else {
            for table in &mut ext {
                let half = table.len() / 2;
                for k in 0..half {
                    table[k] = table[2 * k] + (table[2 * k + 1] - table[2 * k]).scale(c);
                }
                table.truncate(half);
            }
        }
        let tc = t * c;
        eq_bound *= E::ONE - t - c + tc + tc;
        if eq_rest.len() > 1 {
            eq_rest = eq_rest.chunks_exact(2).map(|p| p[0] + p[1]).collect();
        }
        rounds.push(poly);
        point.push(c);
    }
    if !row_challenge_good(shape, &point) {
        return Err(ProveError::MaskRankDeficient);
    }
    e.check()?;
    let opened = e.open_ext(&SecretBuffer([ext[0][0], ext[1][0], ext[2][0]])[..])?;
    Ok(RowOutput {
        mask_sum,
        rounds,
        point,
        values: [opened[0], opened[1], opened[2]],
    })
}

/// Masked column sumcheck of `M(y) Z(y)` for the public `M`: linear in the shares.
fn column_sumcheck<T: Transport>(
    e: &mut Engine<T>,
    tr: &mut Transcript,
    mut matrix: Vec<E>,
    z: &[Sb],
    mask: &MaskShare,
) -> Result<(E, Vec<Vec<E>>), ProveError> {
    let n = matrix.len().trailing_zeros() as usize;
    e.check()?;
    let mask_sum = e.open_ext(&SecretBuffer([mask.sum()])[..])?[0];
    tr.absorb_fp5_slice(b"COL_MASK_SUM", &[mask_sum]);
    let rho = tr.squeeze_fp5_nonzero(b"RHO2");
    let mut ext: SecretScratch<Sh> = SecretScratch::new();
    let mut rounds = Vec::with_capacity(n);
    let mut point: Vec<E> = Vec::with_capacity(n);
    for round in 0..n {
        let mut q = SecretBuffer([Sh::ZERO; COL_DEGREE + 1]);
        let mut add = |m: &[E], z0: Sh, z1: Sh| {
            let (dm, dz) = (m[1] - m[0], z1 - z0);
            q[0] += z0.scale(m[0]);
            q[1] += dz.scale(m[0]) + z0.scale(dm);
            q[2] += dz.scale(dm);
        };
        if round == 0 {
            for (m, p) in matrix.chunks_exact(2).zip(z.chunks_exact(2)) {
                add(m, p[0].lift(), p[1].lift());
            }
        } else {
            for (m, p) in matrix.chunks_exact(2).zip(ext.chunks_exact(2)) {
                add(m, p[0], p[1]);
            }
        }
        let share = masked(&q[..], mask.round_poly(&point), rho);
        e.check()?;
        let poly = e.open_ext(&share)?;
        tr.absorb_fp5_slice(b"COL_ROUND", &poly);
        let c = tr.squeeze_fp5(b"COL_ROUND");
        ext = if round == 0 {
            z.chunks_exact(2)
                .map(|p| p[0].lift() + (p[1] - p[0]).scale_ext(c))
                .collect()
        } else {
            ext.chunks_exact(2)
                .map(|p| p[0] + (p[1] - p[0]).scale(c))
                .collect()
        };
        matrix = matrix
            .chunks_exact(2)
            .map(|p| p[0] + c * (p[1] - p[0]))
            .collect();
        rounds.push(poly);
        point.push(c);
    }
    Ok((mask_sum, rounds))
}

fn poly_times(shared: &[Sh], public: &[E]) -> SecretScratch<Sh> {
    let mut out = SecretScratch::from(vec![Sh::ZERO; shared.len() + public.len() - 1]);
    for (i, &s) in shared.iter().enumerate() {
        for (j, &p) in public.iter().enumerate() {
            out[i + j] += s.scale(p);
        }
    }
    out
}

struct LookupOutput {
    gamma: E,
    helper_tree_nonces: Vec<[u8; TREE_NONCE_BYTES]>,
    helper_roots: Vec<Digest>,
    state: Committed,
    table: SecretScratch<Sb>,
    mask_sum: E,
    rounds: Vec<Vec<E>>,
    point: Vec<E>,
    values: [E; 3],
}

/// LogUp lookup front-end (Rounds L1–L3) on authenticated shares.
fn lookup_front<T: Transport>(
    e: &mut Engine<T>,
    profile: Profile,
    tr: &mut Transcript,
    lookups: &Lookups,
    ll: &LookupLayout,
    z: &[Sb],
) -> Result<LookupOutput, ProveError> {
    let d = lookups.log_entries;
    let (entries, checked) = (lookups.num_entries(), lookups.num_checked());
    let gamma = tr.squeeze_fp5(b"LK_GAMMA");
    let alpha = tr.squeeze_fp5(b"LK_ALPHA");
    let unit = limb_basis();
    let form = |matrix: &Csr, i: usize| {
        matrix
            .row(i)
            .fold(Sb::ZERO, |acc, (col, val)| acc + z[col].scale(val))
    };

    let mut n: SecretScratch<Sh> = (0..entries).map(|i| form(&lookups.num, i).lift()).collect();
    let mut v: SecretScratch<Sh> = (0..entries)
        .map(|i| {
            lookups
                .den
                .iter()
                .rev()
                .fold(Sh::ZERO, |acc, m| acc.scale(gamma) + form(m, i).lift())
        })
        .collect();

    let mut h = SecretScratch::from(vec![Sh::ZERO; entries]);
    let mut inversions = SecretScratch::new();
    let (mut xs, mut ys) = (SecretScratch::new(), SecretScratch::new());
    for i in 0..checked {
        match helper_kind(lookups, i).ok_or(ProveError::Unsupported)? {
            Helper::PublicValue => {
                let value = lookups.den.iter().rev().fold(E::ZERO, |acc, m| {
                    acc * gamma + E::from_base(public_form(m, i).unwrap_or(F::ZERO))
                });
                if (alpha - value).is_zero() {
                    return Err(ProveError::DegenerateChallenge);
                }
                if lookups.num.row(i).next().is_some() {
                    h[i] = n[i].scale((alpha - value).inverse());
                }
            }
            Helper::Inversion { .. } => {
                let mut r = SecretBuffer([Sb::ZERO; LIMBS]);
                for limb in r.iter_mut() {
                    *limb = e.random()?;
                }
                for m in &lookups.den {
                    if public_form(m, i).is_none() {
                        let column = form(m, i);
                        xs.extend_from_slice(&r[..]);
                        ys.extend([column; LIMBS]);
                    }
                }
                inversions.push((i, *r));
            }
        }
    }
    let products = SecretScratch::from(e.mul(&xs, &ys)?);
    let mut next = products.chunks_exact(LIMBS);
    let mut masked_values = SecretScratch::with_capacity(inversions.len());
    let mut pads = SecretScratch::with_capacity(inversions.len());
    for (i, r) in &inversions {
        let i = *i;
        let pad = SecretBuffer(Sh::from_limbs(*r));
        let mut rv = SecretBuffer(Sh::ZERO);
        let mut weight = E::ONE;
        for m in &lookups.den {
            match public_form(m, i) {
                Some(constant) => *rv += pad.scale(weight.mul_base(constant)),
                None => {
                    let limbs = next.next().ok_or(ProveError::Malformed)?;
                    for j in 0..LIMBS {
                        *rv += limbs[j].scale_ext(weight * unit[j]);
                    }
                }
            }
            weight *= gamma;
        }
        masked_values.push(pad.scale(alpha) - *rv);
        pads.push(*pad);
    }
    e.check()?;
    let opened = e.open_ext(&masked_values)?;
    e.check()?;
    for ((&(i, _), pad), w) in inversions.iter().zip(&pads).zip(opened) {
        if w.is_zero() {
            return Err(ProveError::DegenerateChallenge);
        }
        let numerator = public_form(&lookups.num, i).ok_or(ProveError::Unsupported)?;
        h[i] = pad.scale(w.inverse().mul_base(numerator));
    }
    for slot in &mut h[checked..] {
        *slot = e.random_ext()?;
    }

    let cells = 1usize << ll.log_cells;
    let mut table = SecretScratch::from(vec![Sb::ZERO; cells]);
    for (i, value) in h.iter().enumerate() {
        for j in 0..LIMBS {
            table[ll.limb_block(j) + i] = value.limb(j);
        }
    }
    let mask = sample_mask(e, &mut table, d, LOOKUP_DEGREE, LOOKUP_MASK_BITS, |i, j| {
        ll.mask_block(i, j)
    })?;
    for slot in &mut table[cells - ll.blind_cells..] {
        *slot = e.random()?;
    }
    let state = commit_shares(e, profile, ll.log_cells, &table, &ll.schedule, &mut |_| {});
    let (helper_tree_nonces, helper_roots) = exchange_roots(
        e,
        &state.tree_nonce(),
        &state.root(),
    )?;
    absorb_lookup_roots(tr, &helper_tree_nonces, &helper_roots);

    let tau: Vec<E> = (0..d).map(|_| tr.squeeze_fp5(b"LK_TAU")).collect();
    let lambda = tr.squeeze_fp5(b"LK_BATCH");
    e.check()?;
    let mask_sum = e.open_ext(&SecretBuffer([mask.sum()])[..])?[0];
    tr.absorb_fp5_slice(b"LK_MASK_SUM", &[mask_sum]);
    let rho = tr.squeeze_fp5_nonzero(b"LK_RHO");
    let mut eq = eq_table(&tau);
    let (mut count, mut boundary) = (checked, E::ZERO);
    let mut rounds = Vec::with_capacity(d);
    let mut point: Vec<E> = Vec::with_capacity(d);
    let mut claim = SecretBuffer(Sh::ZERO);
    for round in 0..d {
        let live = lookup_live_pairs(lookups, round);
        let mut xs = SecretScratch::with_capacity(3 * live);
        let mut ys = SecretScratch::with_capacity(3 * live);
        for k in 0..live {
            xs.extend([h[2 * k], h[2 * k + 1], h[2 * k + 1] - h[2 * k]]);
            ys.extend([v[2 * k], v[2 * k + 1], v[2 * k + 1] - v[2 * k]]);
        }
        let products = SecretScratch::from(e.mul_ext(&xs, &ys)?);
        let mut pending = SecretScratch::from(vec![Sh::ZERO; LOOKUP_DEGREE + 1]);
        for k in 0..live {
            let [q0, q_one, q2] = [products[3 * k], products[3 * k + 1], products[3 * k + 2]];
            let (h0, dh) = (h[2 * k], h[2 * k + 1] - h[2 * k]);
            let (n0, dn) = (n[2 * k], n[2 * k + 1] - n[2 * k]);
            let inner = [
                h0.scale(alpha) - q0 - n0,
                dh.scale(alpha) - (q_one - q0 - q2) - dn,
                Sh::ZERO - q2,
            ];
            let eq_line = [lambda * eq[2 * k], lambda * (eq[2 * k + 1] - eq[2 * k])];
            let mut gate = poly_times(&inner, &eq_line);
            gate[0] += h0;
            gate[1] += dh;
            let at = |j: usize| match j.cmp(&count) {
                core::cmp::Ordering::Less => E::ONE,
                core::cmp::Ordering::Equal => boundary,
                core::cmp::Ordering::Greater => E::ZERO,
            };
            let sel_line = [at(2 * k), at(2 * k + 1) - at(2 * k)];
            for (slot, term) in pending.iter_mut().zip(poly_times(&gate, &sel_line)) {
                *slot += term;
            }
        }
        pending[1] = *claim - pending[0] - pending[0] - pending[2] - pending[3] - pending[4];
        let share = masked(&pending[..], mask.round_poly(&point), rho);
        e.check()?;
        let poly = e.open_ext(&share)?;
        tr.absorb_fp5_slice(b"LK_ROUND", &poly);
        let c = tr.squeeze_fp5(b"LK_ROUND");
        *claim = eval_poly_sh(&pending[..], c);
        for shares in [&mut n, &mut v, &mut h] {
            let half = shares.len() / 2;
            for k in 0..half {
                shares[k] = shares[2 * k] + (shares[2 * k + 1] - shares[2 * k]).scale(c);
            }
            shares.truncate(half);
        }
        eq = eq
            .chunks_exact(2)
            .map(|p| p[0] + c * (p[1] - p[0]))
            .collect();
        boundary = if count & 1 == 1 {
            E::ONE + c * (boundary - E::ONE)
        } else {
            boundary - c * boundary
        };
        count >>= 1;
        rounds.push(poly);
        point.push(c);
    }
    if !lookup_masks_full_rank(lookups, &point) {
        return Err(ProveError::MaskRankDeficient);
    }
    e.check()?;
    let opened = e.open_ext(&SecretBuffer([n[0], v[0], h[0]])[..])?;
    let values = [opened[0], opened[1], opened[2]];
    tr.absorb_fp5_slice(b"LK_VALUES", &values);
    Ok(LookupOutput {
        gamma,
        helper_tree_nonces,
        helper_roots,
        state,
        table,
        mask_sum,
        rounds,
        point,
        values,
    })
}

/// Fold one WHIR Stage-0 step on authenticated shares (`0` Beaver triples).
#[allow(clippy::type_complexity)]
fn prove_stage0_fold_shared<T: Transport>(
    e: &mut Engine<T>,
    poly_base: Option<&[Sb]>,
    poly_ext: &[Sh],
    st: &mut pcs::Folding,
    tr: &mut Transcript,
) -> Result<(SecretScratch<Sh>, [E; 5], [E; 3]), ProveError> {
    let m = poly_base.map_or(poly_ext.len(), <[Sb]>::len);
    assert_eq!(st.kernel.len(), m);
    let half = m.div_ceil(2);
    let tail = pcs::point_tail(&st.points, m, 3);
    let k_at = |i: usize| if i < m { st.kernel[i] } else { tail[i - m] };
    let p_at = |i: usize| -> Sh {
        match poly_base {
            Some(b) => b.get(i).map_or(Sh::ZERO, |s| s.lift()),
            None => poly_ext.get(i).copied().unwrap_or(Sh::ZERO),
        }
    };

    let mut sigma_even = SecretBuffer(Sh::ZERO);
    let mut tau_01 = SecretBuffer(Sh::ZERO);
    let mut tau_10 = SecretBuffer(Sh::ZERO);
    for n in 0..half {
        let (f, g) = (p_at(2 * n), p_at(2 * n + 1));
        let (ke, ko) = (k_at(2 * n), k_at(2 * n + 1));
        *sigma_even += f.scale(ke);
        *tau_01 += f.scale(ko);
        *tau_10 += g.scale(ke);
    }
    e.check()?;
    let fold_a = e.open_ext(&SecretBuffer([*sigma_even, *tau_01, *tau_10])[..])?;
    tr.absorb_fp5_slice(b"FOLD_A", &fold_a);
    let phi = tr.squeeze_fp5(b"FOLD_PHI");
    let xs: Vec<E> = st.points[..MASK_POINTS].iter().map(|p| p.1).collect();
    if !pcs::fold_challenge_good(phi, &xs) {
        return Err(ProveError::MaskRankDeficient);
    }

    let mut v = vec![E::ZERO; half + 1];
    for (n, slot) in v.iter_mut().enumerate() {
        *slot = k_at(2 * n) + phi * k_at(2 * n + 1);
    }
    let (mut c_f, mut c_g) = (SecretBuffer(Sh::ZERO), SecretBuffer(Sh::ZERO));
    for n in 0..half {
        *c_f += p_at(2 * n).scale(v[n + 1]);
        *c_g += p_at(2 * n + 1).scale(v[n + 1]);
    }
    e.check()?;
    let fold_b = e.open_ext(&SecretBuffer([*c_f, *c_g])[..])?;
    tr.absorb_fp5_slice(b"FOLD_B", &fold_b);
    let chals = [
        tr.squeeze_fp5(b"FOLD_THETA"),
        tr.squeeze_fp5(b"FOLD_ALPHA"),
        tr.squeeze_fp5(b"FOLD_BETA"),
    ];
    let [theta, alpha, beta] = chals;
    let wire = [fold_a[0], fold_a[1], fold_a[2], fold_b[0], fold_b[1]];

    let h_at = |n: usize| p_at(2 * n) + p_at(2 * n + 1).scale(theta);
    let mut next = SecretScratch::from(vec![Sh::ZERO; half + 1]);
    for (n, slot) in next.iter_mut().enumerate() {
        let mut acc = Sh::ZERO;
        if n < half {
            acc = p_at(2 * n + 1) + h_at(n).scale(alpha);
        }
        if n > 0 {
            acc += h_at(n - 1).scale(beta);
        }
        *slot = acc;
    }

    st.claim = pcs::next_claim(&wire, st.claim, phi, chals);
    st.kernel = v;
    pcs::fold_points(&mut st.points, phi);
    Ok((next, wire, chals))
}

/// Open one committed table whose linear claim has already passed the SPDZ zero test.
#[allow(clippy::too_many_arguments)]
fn open_table<T: Transport>(
    e: &mut Engine<T>,
    profile: Profile,
    tr: &mut Transcript,
    tree_nonces: &[[u8; TREE_NONCE_BYTES]],
    roots: &[Digest],
    log_cells: usize,
    schedule: &Schedule,
    state: &Committed,
    mut table: SecretScratch<Sb>,
    mut kernel: Vec<E>,
    value: E,
    fault: &mut dyn FnMut(Fault<'_>),
) -> Result<SplitOpening, ProveError> {
    let parties = e.parties();
    let dims = pcs::stage_dims(log_cells, schedule).ok_or(ProveError::Unsupported)?;
    let d0 = &dims[0];
    let step_vars = d0.step_vars;

    // Monomial coefficients on authenticated shares (`0` communication, `0` triples).
    hypercube_to_monomial_sb(&mut table);

    let omegas: [E; MASK_POINTS] = core::array::from_fn(|_| tr.squeeze_fp5(b"MASK_POINT"));
    if !pcs::mask_points_good(&omegas, step_vars) {
        return Err(ProveError::MaskRankDeficient);
    }
    let eval_shares = SecretBuffer(core::array::from_fn::<_, MASK_POINTS, _>(|j| {
        let x = omegas[j];
        table
            .iter()
            .rev()
            .fold(Sh::ZERO, |acc, &c| acc.scale(x) + c.lift())
    }));
    e.check()?;
    let opened_evals = e.open_ext(&eval_shares[..])?;
    let mask_evals: [E; MASK_POINTS] = opened_evals.try_into().unwrap();
    tr.absorb_fp5_slice(b"MASK_EVAL", &mask_evals);
    let weights: [E; MASK_POINTS] = core::array::from_fn(|_| tr.squeeze_fp5(b"MASK_WEIGHT"));
    if weights.iter().any(|w| w.is_zero()) {
        return Err(ProveError::MaskRankDeficient);
    }

    let point_terms: Vec<(E, E)> = weights.into_iter().zip(omegas).collect();
    pcs::add_points(&mut kernel, &point_terms);
    let mut fold_st = pcs::Folding {
        kernel,
        claim: mask_evals
            .iter()
            .zip(&weights)
            .fold(value, |acc, (&a, &w)| acc + w * a),
        points: point_terms,
    };

    let mut stage0_folds = Vec::with_capacity(step_vars);
    let mut prev_chals = Vec::with_capacity(step_vars);
    let (mut poly_sh, wire0, c0) =
        prove_stage0_fold_shared(e, Some(&table), &[], &mut fold_st, tr)?;
    drop(table);
    stage0_folds.push(wire0);
    prev_chals.push(c0);
    for _ in 1..step_vars {
        let (next, wire, c) = prove_stage0_fold_shared(e, None, &poly_sh, &mut fold_st, tr)?;
        poly_sh = next;
        stage0_folds.push(wire);
        prev_chals.push(c);
    }

    // Settle all pending MACs before broadcasting unauthenticated Stage-0 mask claim & reduced word!
    e.check()?;

    pcs::extend_kernel(&mut fold_st.kernel, &fold_st.points, state.mask().len());
    let own_mask_claim = state
        .mask()
        .iter()
        .zip(&fold_st.kernel)
        .fold(E::ZERO, |acc, (&r, &k)| acc + r * k);
    let mut mask_claim = E::ZERO;
    for (from, bytes) in e.exchange_guarded(own_mask_claim.to_le_bytes().to_vec())?.iter().enumerate() {
        let chunk: [u8; EXT_BYTES] = bytes
            .as_slice()
            .try_into()
            .map_err(|_| ProveError::BadPeerMessage { from })?;
        mask_claim += E::from_le_bytes_canonical(chunk)
            .ok_or(ProveError::BadPeerMessage { from })?;
    }
    tr.absorb_fp5_slice(b"MASK_CLAIM", &[mask_claim]);
    let beta_r = tr.squeeze_fp5_nonzero(b"MASK_BETA");
    fold_st.claim += beta_r * mask_claim;

    let mask_len = state.mask().len();
    let mut word_payload = Vec::with_capacity(EXT_BYTES * mask_len);
    for n in 0..mask_len {
        let u = poly_sh.get(n).map_or(E::ZERO, |s| s.v) + beta_r * state.mask()[n];
        word_payload.extend_from_slice(&u.to_le_bytes());
    }
    drop(poly_sh);
    fault(Fault::Word(&mut word_payload));
    let mut g = vec![E::ZERO; mask_len];
    for (from, bytes) in e.exchange_guarded(word_payload)?.iter().enumerate() {
        if bytes.len() != EXT_BYTES * mask_len {
            return Err(ProveError::BadPeerMessage { from });
        }
        for (slot, chunk) in g.iter_mut().zip(bytes.chunks_exact(EXT_BYTES)) {
            let arr: [u8; EXT_BYTES] = chunk.try_into().unwrap();
            *slot += E::from_le_bytes_canonical(arr)
                .ok_or(ProveError::BadPeerMessage { from })?;
        }
    }

    let mut failure: Option<ProveError> = None;
    let opening = pcs::open_from_reduced_split(
        profile,
        log_cells,
        schedule,
        tree_nonces,
        roots,
        mask_evals,
        stage0_folds,
        mask_claim,
        g,
        fold_st,
        prev_chals,
        beta_r,
        tr,
        &mut |idx| {
            let mut own = pcs::stage0_answer(state, idx);
            fault(Fault::Leaves(&mut own));
            let mut encoded = Vec::new();
            pcs::push_stage0_query(&mut encoded, &own);
            match e.exchange_guarded(encoded) {
                Ok(messages) => {
                    let mut all = Vec::with_capacity(parties);
                    for (from, bytes) in messages.iter().enumerate() {
                        match pcs::read_stage0_query_exact(bytes, d0) {
                            Some(q) => all.push(q),
                            None => {
                                failure.get_or_insert(ProveError::BadPeerMessage { from });
                                return None;
                            }
                        }
                    }
                    Some(all)
                }
                Err(err) => {
                    failure.get_or_insert(err.into());
                    None
                }
            }
        },
    );
    if let Some(err) = failure {
        return Err(err);
    }
    opening.ok_or(ProveError::Rejected)
}

/// Prove that the shared assignment satisfies `shape`, bound to `statement`, under `profile`.
