//! Experimental algebraic component of the WHIR child verifier.
//!
//! A row proves the CWYZ last-duet arithmetic on caller-supplied inputs. It does
//! NOT authenticate those inputs, derive transcript challenges, check Merkle paths,
//! or authorize a hierarchy. The existing cSHAKE commitment profile is unchanged.
//! The 64-column layout has 27 statement limbs, 24 intermediate limbs and 13 zero
//! padding limbs (ignored by the relation). Its 55 residuals have degree at most two; an equality selector
//! makes the batched row sumcheck degree three. This small relation is composable
//! with future authenticated-input/transcript relations, not a recursive verifier.

use crate::field::{
    Goldilocks as F, GoldilocksExt4 as E, build_eq_table_ext4, eq_poly_ext4, eval_univariate_ext4,
    mle_eval_ext4,
};
use crate::pcs::{
    CanopyCommitment, HemWhirOpeningProof, WhirSchedule, WhirSecurityRegime,
    whir_commit_owned_with_schedule, whir_open, whir_verify_with_schedule,
};
use crate::sponge::{FiatShamirTranscript, InstanceBound};
use alloc::{vec, vec::Vec};

pub const FOLD_COLUMNS: usize = 64;
pub const FOLD_RESIDUALS: usize = 55;
/// Maximum rows in one `DuetFoldProof` (`64 * MAX_FOLD_ROWS <= 2^MAX_PCS_NUM_VARS` cells).
pub const MAX_FOLD_ROWS: usize = 1usize << (crate::pcs::MAX_PCS_NUM_VARS - 6);

/// Inputs must be authenticated by a surrounding verifier. This type is not evidence.
/// In particular, inverse/domain consistency of `inv_two`, `inv_two_x`, and `x_sq`
/// is supplied by that verifier, not established by this arithmetic component.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DuetFoldStatement {
    pub v0: E,
    pub v1: E,
    pub theta: E,
    pub alpha: E,
    pub beta: E,
    pub inv_two: F,
    pub inv_two_x: F,
    pub x_sq: F,
    pub claimed: E,
}
impl DuetFoldStatement {
    fn limbs(&self) -> [F; 27] {
        let mut r = [F::ZERO; 27];
        for (i, v) in [
            self.v0,
            self.v1,
            self.theta,
            self.alpha,
            self.beta,
            self.claimed,
        ]
        .iter()
        .enumerate()
        {
            r[4 * i..4 * i + 4].copy_from_slice(&v.to_limbs());
        }
        r[24] = self.inv_two;
        r[25] = self.inv_two_x;
        r[26] = self.x_sq;
        r
    }
    pub fn witness_row(&self) -> [F; FOLD_COLUMNS] {
        let even = (self.v0 + self.v1).mul_base(self.inv_two);
        let odd = (self.v0 - self.v1).mul_base(self.inv_two_x);
        let gamma = self.alpha + self.beta.mul_base(self.x_sq);
        let theta_odd = self.theta * odd;
        let mixed = even + theta_odd;
        let product = gamma * mixed;
        let mut r = [F::ZERO; FOLD_COLUMNS];
        r[..27].copy_from_slice(&self.limbs());
        for (i, v) in [even, odd, gamma, theta_odd, mixed, product]
            .iter()
            .enumerate()
        {
            r[27 + 4 * i..31 + 4 * i].copy_from_slice(&v.to_limbs());
        }
        r
    }
    /// Exact polynomial gate check, used by the native child verifier as well.
    pub fn accepts(&self) -> bool {
        residuals(&self.witness_row(), &self.limbs())
            .iter()
            .all(|x| *x == F::ZERO)
    }
}

// Tower order is [1,u,v,uv], u^2=7 and v^2=u. Kept as base-field
// bilinear polynomials, rather than multiplying E values representing four limbs.
trait Limb:
    Copy + core::ops::Add<Output = Self> + core::ops::Sub<Output = Self> + core::ops::Mul<Output = Self>
{
    const ZERO: Self;
}
impl Limb for F {
    const ZERO: Self = F::ZERO;
}
impl Limb for E {
    const ZERO: Self = E::ZERO;
}
fn seven<T: Limb>(x: T) -> T {
    let x2 = x + x;
    let x4 = x2 + x2;
    x4 + x2 + x
}
fn tower_mul<T: Limb>(a: &[T], b: &[T]) -> [T; 4] {
    [
        a[0] * b[0] + seven(a[1] * b[1] + a[2] * b[3] + a[3] * b[2]),
        a[0] * b[1] + a[1] * b[0] + a[2] * b[2] + seven(a[3] * b[3]),
        a[0] * b[2] + a[2] * b[0] + seven(a[1] * b[3] + a[3] * b[1]),
        a[0] * b[3] + a[3] * b[0] + a[1] * b[2] + a[2] * b[1],
    ]
}
/// Polynomial evaluator valid also at non-Boolean extension-field row points.
/// Padding columns are unused; they carry no semantic state.
pub fn fold_residuals(r: &[E; FOLD_COLUMNS], public: &[E; 27]) -> [E; FOLD_RESIDUALS] {
    residuals(r, public)
}
fn residuals<T: Limb>(r: &[T; FOLD_COLUMNS], public: &[T; 27]) -> [T; FOLD_RESIDUALS] {
    let mut out = [T::ZERO; FOLD_RESIDUALS];
    for i in 0..27 {
        out[i] = r[i] - public[i];
    }
    let theta_odd = tower_mul(&r[8..12], &r[31..35]);
    let product = tower_mul(&r[35..39], &r[43..47]);
    for i in 0..4 {
        out[27 + i] = r[27 + i] - (r[i] + r[4 + i]) * r[24];
        out[31 + i] = r[31 + i] - (r[i] - r[4 + i]) * r[25];
        out[35 + i] = r[35 + i] - r[12 + i] - r[16 + i] * r[26];
        out[39 + i] = r[39 + i] - theta_odd[i];
        out[43 + i] = r[43 + i] - r[27 + i] - r[39 + i];
        out[47 + i] = r[47 + i] - product[i];
        out[51 + i] = r[20 + i] - r[31 + i] - r[47 + i];
    }
    out
}
fn relation(r: &[E; 64], public: &[E; 27], eq: E, gamma: E) -> E {
    let mut acc = E::ZERO;
    for v in fold_residuals(r, public).iter().rev() {
        acc = acc * gamma + *v;
    }
    acc * eq
}

/// Proof of the explicit arithmetic statements only. No evidence-token conversion exists.
#[derive(Clone, Debug)]
pub struct DuetFoldProof {
    pub commitment: CanopyCommitment,
    pub round_polynomials: Vec<[E; 4]>,
    pub column_evaluations: [E; 64],
    pub opening: HemWhirOpeningProof,
}
fn shape(n: usize) -> Option<(usize, usize)> {
    if n == 0 || n > MAX_FOLD_ROWS {
        return None;
    }
    let rows = n.next_power_of_two().max(2);
    Some((rows, rows.trailing_zeros() as usize))
}
fn init(
    context: &[u8; 32],
    statements: &[DuetFoldStatement],
    schedule: &WhirSchedule,
) -> FiatShamirTranscript<InstanceBound> {
    let mut bytes = Vec::with_capacity(statements.len() * 27 * 8);
    for s in statements {
        for x in s.limbs() {
            bytes.extend_from_slice(&x.to_le_bytes());
        }
    }
    FiatShamirTranscript::new()
        .bind_relation(
            b"QSAG.EXPERIMENTAL.CWYZ.DUET/v1",
            &(statements.len() as u64).to_le_bytes(),
            schedule,
        )
        .bind_instance(&[context, &bytes])
}
fn absorb(t: &mut FiatShamirTranscript<InstanceBound>, label: &[u8], xs: &[E]) {
    let mut bytes = Vec::with_capacity(xs.len() * 32);
    for x in xs {
        bytes.extend_from_slice(&x.to_le_bytes());
    }
    t.absorb(label, &bytes);
}
fn fold<const N: usize>(table: &mut Vec<[E; N]>, r: E) {
    let h = table.len() / 2;
    let (lo, hi) = table.split_at_mut(h);
    for (dst, src) in lo.iter_mut().zip(&hi[..h]) {
        for (d_val, &s_val) in dst.iter_mut().zip(src.iter()) {
            let d = s_val - *d_val;
            *d_val += r * d;
        }
    }
    table.truncate(h);
}
fn cubic(y: [E; 4]) -> [E; 4] {
    let two = F::from_u64_reduced(2);
    let three = F::from_u64_reduced(3);
    let c3 = (y[3] - y[2].mul_base(three) + y[1].mul_base(three) - y[0])
        .mul_base(F::from_u64_reduced(6).inv());
    let c2 = (y[2] - y[1].mul_base(two) + y[0]).mul_base(two.inv()) - c3.mul_base(three);
    [y[0], y[1] - y[0] - c2 - c3, c2, c3]
}
/// Prove one or more valid duet gates under a caller-provided context digest.
/// The caller must link that context and the statements to a child verifier separately.
pub fn prove_duet_folds(
    context: &[u8; 32],
    statements: &[DuetFoldStatement],
    salt: &[u8; 32],
) -> Option<DuetFoldProof> {
    let (n, log) = shape(statements.len())?;
    if !statements.iter().all(DuetFoldStatement::accepts) {
        return None;
    }
    let schedule = WhirSecurityRegime::BciksJohnsonQrom128.schedule(log + 6);
    let mut base = vec![[F::ZERO; 64]; n];
    let mut public = vec![[E::ZERO; 27]; n];
    for (i, s) in statements.iter().enumerate() {
        base[i] = s.witness_row();
        public[i] = s.limbs().map(E::from_base);
    }
    let (commitment, state) = whir_commit_owned_with_schedule(
        base.iter().flat_map(|r| r.iter().copied()).collect(),
        salt,
        &schedule,
    );
    let mut t = init(context, statements, &schedule);
    t.absorb(b"COMM", &commitment.to_bytes());
    let tau = t.squeeze_ext4_vec(b"TAU", log);
    let gamma = t.squeeze_ext4(b"GAMMA");
    let mut eq: Vec<[E; 1]> = build_eq_table_ext4(&tau).into_iter().map(|x| [x]).collect();
    let mut rows: Vec<[E; 64]> = base.iter().map(|r| r.map(E::from_base)).collect();
    let mut round_polynomials = Vec::with_capacity(log);
    let mut rx = Vec::with_capacity(log);
    for _ in 0..log {
        let h = rows.len() / 2;
        let mut y = [E::ZERO; 4];
        for (k, yk) in y.iter_mut().enumerate() {
            let k = E::from_base(F::from_u64_reduced(k as u64));
            for i in 0..h {
                let r = core::array::from_fn(|j| rows[i][j] + k * (rows[i + h][j] - rows[i][j]));
                let p =
                    core::array::from_fn(|j| public[i][j] + k * (public[i + h][j] - public[i][j]));
                *yk += relation(&r, &p, eq[i][0] + k * (eq[i + h][0] - eq[i][0]), gamma);
            }
        }
        let poly = cubic(y);
        absorb(&mut t, b"ROUND", &poly);
        let r = t.squeeze_ext4(b"R");
        round_polynomials.push(poly);
        rx.push(r);
        fold(&mut rows, r);
        fold(&mut public, r);
        fold(&mut eq, r);
    }
    let column_evaluations = rows[0];
    absorb(&mut t, b"COLS", &column_evaluations);
    let mut point = t.squeeze_ext4_vec(b"Z", 6);
    let value = mle_eval_ext4(&column_evaluations, &point);
    rx.reverse();
    point.extend_from_slice(&rx);
    let opening = whir_open(&state, &point, value, &mut t);
    Some(DuetFoldProof {
        commitment,
        round_polynomials,
        column_evaluations,
        opening,
    })
}
/// Verify only the arithmetic gate relation described at module scope.
pub fn verify_duet_folds(
    context: &[u8; 32],
    statements: &[DuetFoldStatement],
    proof: &DuetFoldProof,
) -> bool {
    let Some((n, log)) = shape(statements.len()) else {
        return false;
    };
    if proof.round_polynomials.len() != log {
        return false;
    }
    let schedule = WhirSecurityRegime::BciksJohnsonQrom128.schedule(log + 6);
    let mut t = init(context, statements, &schedule);
    t.absorb(b"COMM", &proof.commitment.to_bytes());
    let tau = t.squeeze_ext4_vec(b"TAU", log);
    let gamma = t.squeeze_ext4(b"GAMMA");
    let mut claim = E::ZERO;
    let mut rx = Vec::with_capacity(log);
    for poly in &proof.round_polynomials {
        if poly[0] + poly.iter().copied().fold(E::ZERO, |a, b| a + b) != claim {
            return false;
        }
        absorb(&mut t, b"ROUND", poly);
        let r = t.squeeze_ext4(b"R");
        claim = eval_univariate_ext4(poly, r);
        rx.push(r);
    }
    absorb(&mut t, b"COLS", &proof.column_evaluations);
    rx.reverse();
    let weights = build_eq_table_ext4(&rx);
    debug_assert_eq!(weights.len(), n);
    let mut public = [E::ZERO; 27];
    for (i, s) in statements.iter().enumerate() {
        for (j, x) in s.limbs().iter().enumerate() {
            public[j] += weights[i].mul_base(*x);
        }
    }
    if claim
        != relation(
            &proof.column_evaluations,
            &public,
            eq_poly_ext4(&tau, &rx),
            gamma,
        )
    {
        return false;
    }
    let mut point = t.squeeze_ext4_vec(b"Z", 6);
    let value = mle_eval_ext4(&proof.column_evaluations, &point);
    point.extend_from_slice(&rx);
    whir_verify_with_schedule(
        &proof.commitment,
        log + 6,
        &point,
        value,
        &proof.opening,
        &mut t,
        &schedule,
    )
}

#[cfg(all(test, feature = "std"))]
static CAPTURE_SESSION_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
#[cfg(all(test, feature = "std"))]
static CAPTURE: std::sync::Mutex<Option<Vec<DuetFoldStatement>>> = std::sync::Mutex::new(None);
#[cfg(all(test, feature = "std"))]
pub(crate) fn capture_gate(s: &DuetFoldStatement) {
    if let Ok(mut guard) = CAPTURE.lock()
        && let Some(rows) = guard.as_mut()
    {
        rows.push(s.clone());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn statement() -> DuetFoldStatement {
        let e = |k: u64| {
            E::from_limbs(core::array::from_fn(|i| {
                F::from_u64_reduced(k + 17 * i as u64)
            }))
        };
        let mut s = DuetFoldStatement {
            v0: e(3),
            v1: e(7),
            theta: e(11),
            alpha: e(13),
            beta: e(19),
            inv_two: F::from_u64_reduced(2).inv(),
            inv_two_x: F::from_u64_reduced(14).inv(),
            x_sq: F::from_u64_reduced(49),
            claimed: E::ZERO,
        };
        let even = (s.v0 + s.v1).mul_base(s.inv_two);
        let odd = (s.v0 - s.v1).mul_base(s.inv_two_x);
        s.claimed = odd + (s.alpha + s.beta.mul_base(s.x_sq)) * (even + s.theta * odd);
        s
    }
    #[test]
    fn quadratic_gate_binds_every_used_witness_limb() {
        let s = statement();
        assert!(s.accepts());
        let public = s.limbs().map(E::from_base);
        let row = s.witness_row().map(E::from_base);
        for i in 0..51 {
            let mut bad = row;
            bad[i] += E::ONE;
            assert!(
                fold_residuals(&bad, &public).iter().any(|r| !r.is_zero()),
                "unbound column {i}"
            );
        }
        let mut bad = s.clone();
        bad.claimed += E::ONE;
        assert!(!bad.accepts());
        assert!(prove_duet_folds(&[1; 32], &[bad], &[2; 32]).is_none());
        // Independent agreement with the extracted gate, including nontrivial tower limbs.
        let to = |v: E| {
            let l = v.to_limbs().map(F::to_canonical_u64);
            qsag_whir_verified::Ext4 {
                a: l[0],
                b: l[2],
                c: l[1],
                d: l[3],
            }
        };
        assert!(qsag_whir_verified::verify_cwyz_duet_fold_step(
            to(s.v0),
            to(s.v1),
            s.inv_two_x.to_canonical_u64(),
            s.inv_two.to_canonical_u64(),
            s.x_sq.to_canonical_u64(),
            to(s.theta),
            to(s.alpha),
            to(s.beta),
            to(s.claimed)
        ));
    }
    #[test]
    fn fold_component_proof_accepts_and_rejects_context_and_witness_tampering() {
        let rows = vec![statement(); 3];
        let context = [41; 32];
        let proof = prove_duet_folds(&context, &rows, &[8; 32]).unwrap();
        assert!(verify_duet_folds(&context, &rows, &proof));
        assert!(!verify_duet_folds(&[42; 32], &rows, &proof));
        let mut bad = rows.clone();
        bad[1].claimed += E::ONE;
        assert!(!verify_duet_folds(&context, &bad, &proof));
        let mut bad = proof.clone();
        bad.column_evaluations[39] += E::ONE;
        assert!(!verify_duet_folds(&context, &rows, &bad));
        let mut bad = proof.clone();
        bad.round_polynomials[0][2] += E::ONE;
        assert!(!verify_duet_folds(&context, &rows, &bad));
        let mut bad = proof.clone();
        bad.opening.stage0_ood_evals[0] += E::ONE;
        assert!(!verify_duet_folds(&context, &rows, &bad));
        let mut bad = proof.clone();
        bad.commitment.root[0] ^= 1;
        assert!(!verify_duet_folds(&context, &rows, &bad));
        let mut bad = proof.clone();
        bad.round_polynomials.pop();
        assert!(!verify_duet_folds(&context, &rows, &bad));
        assert!(!verify_duet_folds(&context, &[], &proof));
    }
    #[test]
    #[cfg(feature = "std")]
    fn real_child_fold_gates_have_a_component_proof() {
        use crate::{
            AggSigProfile, SignerBitmap, SigningMode, ValidatorKeypair, aggregate_signatures,
            verify_aggregate,
        };
        let mut key =
            ValidatorKeypair::keygen_deterministic(AggSigProfile::JortsPoseidon2, &[91; 32], 0);
        let msg = b"actual-child-fold-component";
        let signature = key.sign_stateful_for_unit_test(msg, 0).unwrap();
        let bitmap = SignerBitmap::from_active_indices(1, &[0]).unwrap();
        let mode = SigningMode::SharedMessage(msg);
        let child =
            aggregate_signatures(&[key.pk], &bitmap, &mode, &[signature], [92; 32]).unwrap();
        let gates = {
            let _session = CAPTURE_SESSION_LOCK
                .lock()
                .unwrap_or_else(|e| e.into_inner());
            *CAPTURE.lock().unwrap_or_else(|e| e.into_inner()) = Some(Vec::new());
            assert!(verify_aggregate(&[key.pk], &mode, &child));
            CAPTURE
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .take()
                .unwrap()
        };
        assert!(!gates.is_empty());
        assert!(gates.len() <= MAX_FOLD_ROWS);
        let context = crate::sponge::cshake256_32(b"QSAG.TEST.CHILD", &child.to_bytes());
        let proof = prove_duet_folds(&context, &gates, &[93; 32]).unwrap();
        assert!(verify_duet_folds(&context, &gates, &proof));
        let mut bad = gates.clone();
        bad[0].theta += E::ONE;
        assert!(!verify_duet_folds(&context, &bad, &proof));
        assert!(!verify_aggregate(
            &[key.pk],
            &SigningMode::SharedMessage(b"wrong-context"),
            &child
        ));
        let mut malformed_child = child.clone();
        malformed_child.committee_root[0] ^= 1;
        assert!(!verify_aggregate(&[key.pk], &mode, &malformed_child));
        std::println!(
            "real child duet component: gates={}, rows={}, cells={}, sumcheck_rounds={}, opening_bytes={}",
            gates.len(),
            shape(gates.len()).unwrap().0,
            shape(gates.len()).unwrap().0 * FOLD_COLUMNS,
            proof.round_polynomials.len(),
            {
                let mut bytes = Vec::new();
                proof.opening.push_bytes(&mut bytes);
                bytes.len()
            }
        );
    }
}
