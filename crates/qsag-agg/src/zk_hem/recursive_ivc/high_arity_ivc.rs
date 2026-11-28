//! One stacked witness commitment for a batch of Jorts signers. The public
//! roster records completed signer unions in shard order. A common row
//! sumcheck, a cubic instance reduction and a column sumcheck end at one
//! multilinear evaluation, opened with the production quintic WHIR schedule.
//! The public sumchecks reveal witness evaluations.
use super::*;
use crate::zk_hem::{
    SeedStream,
    multisig::MultisigParams,
    relation::{ConstraintSystem, Lc, Shape},
    v2::{
        hash::{Digest, Transcript},
        params::Profile,
        protocol,
    },
};
use alloc::sync::Arc;
use qsag_core::wipe::SecretBuffer;
mod fold;
#[cfg(test)]
mod tests;
mod wire;
#[cfg(all(test, feature = "std"))]
mod workload;

const MAGIC: &[u8; 8] = b"QSAGIVC2";
/// Oracle calls of the main transcript, including INIT and sampler retries.
const FS_CALLS: u16 = 4096;
const COMMITTEE: MultisigParams = MultisigParams {
    capacity: 1,
    depth: 8,
};

fn populate(cs: &mut ConstraintSystem, s: &IvcSubtreeStatement, w: &leaf::Witness) {
    let inputs: Vec<Lc> = s
        .public_inputs()
        .map(|x| cs.public_input(x).into())
        .to_vec();
    leaf::populate_signature(cs, &inputs, w);
}
fn compile() -> Arc<Shape> {
    let mut cs = ConstraintSystem::with_row_templates();
    populate(
        &mut cs,
        &IvcSubtreeStatement::blank(),
        &leaf::Witness::blank(COMMITTEE),
    );
    Arc::new(cs.finish().0)
}
fn shape() -> Arc<Shape> {
    #[cfg(feature = "std")]
    {
        static LEAF: std::sync::OnceLock<Arc<Shape>> = std::sync::OnceLock::new();
        LEAF.get_or_init(compile).clone()
    }
    #[cfg(not(feature = "std"))]
    compile()
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Roster {
    id: u64,
    threshold: u16,
    bitmap: [u8; IVC_BITMAP_BYTES],
}
impl Roster {
    fn count(&self) -> usize {
        self.bitmap.iter().map(|v| v.count_ones() as usize).sum()
    }
    fn signers(&self) -> impl Iterator<Item = usize> + '_ {
        (0..256).filter(|&i| self.bitmap[i / 8] & (1 << (i % 8)) != 0)
    }
    fn statement(&self, root: [u8; 32], msg: [u8; 32]) -> Option<IvcSubtreeStatement> {
        let count = self.count();
        if self.threshold == 0 || count < self.threshold as usize {
            return None;
        }
        Some(IvcSubtreeStatement {
            policy_registry_root: root,
            message_digest: msg,
            shard_lo: self.id,
            shard_hi: self.id.checked_add(1)?,
            shard_threshold: self.threshold.into(),
            total_signers: count as u64,
            signer_bitmap: self.bitmap,
        })
    }
    fn single(&self, root: [u8; 32], msg: [u8; 32], i: usize) -> IvcSubtreeStatement {
        let mut bitmap = [0; IVC_BITMAP_BYTES];
        bitmap[i / 8] = 1 << (i % 8);
        IvcSubtreeStatement {
            policy_registry_root: root,
            message_digest: msg,
            shard_lo: self.id,
            shard_hi: self.id + 1,
            shard_threshold: self.threshold.into(),
            total_signers: 1,
            signer_bitmap: bitmap,
        }
    }
}

fn aggregate(roster: &[Roster], root: [u8; 32], msg: [u8; 32]) -> Option<IvcSubtreeStatement> {
    let (first, rest) = roster.split_first()?;
    rest.iter().try_fold(first.statement(root, msg)?, |s, rec| {
        if s.shard_hi != rec.id {
            return None;
        }
        IvcSubtreeStatement::merge(&s, &rec.statement(root, msg)?)
    })
}

// At this code length the extra Johnson proximity loss for a projection
// challenge fits the 400-bit profile (see the security calculation).
const MAX_CODE_LOG: usize = 24;

/// Why [`prove_high_arity_tree`] produced no proof.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HighArityError {
    /// The rate-half profiles (wire tags 18 and 19) are rejected: the projection
    /// analysis, the schedule and the oracle-call account here are the Johnson ones.
    UnsupportedProfile,
    /// The groups are not complete, ascending, validly signed committees of the
    /// registry, or the batch exceeds the supported size.
    InvalidBatch,
    /// A transcript event of negligible probability. Retry with a fresh seed.
    ChallengeRejected,
}
use HighArityError::{ChallengeRejected, InvalidBatch, UnsupportedProfile};

enum Commitment {
    Scalar(pcs::Committed),
    Vector(pcs::interleave::Interleaved),
}
struct Geometry {
    columns: usize,
    instances: usize,
    stripes: usize,
    log: usize,
    schedule: Schedule,
}
impl Geometry {
    /// The only source of a schedule, so every prover, decoder and verifier
    /// path refuses a profile without a `QSAGIVC2` security account.
    fn new(profile: Profile, shape: &Shape, count: usize) -> Result<Self, HighArityError> {
        if profile.rate_half() {
            return Err(UnsupportedProfile);
        }
        let sized = || {
            let columns = shape.num_vars.next_power_of_two().ilog2() as usize;
            let instances = count.checked_next_power_of_two()?.ilog2().max(1) as usize;
            let full = (columns + instances).max(params::MIN_LOG_CELLS);
            let log = full.min(MAX_CODE_LOG);
            let stripes = 1usize.checked_shl((full - log) as u32)?;
            let schedule = profile.schedule(log)?;
            let words = stripes.checked_shl(schedule.stages[0].step_vars as u32)?;
            (count != 0 && words <= pcs::interleave::MAX_FIBER_WORDS).then_some(Self {
                columns,
                instances,
                stripes,
                log,
                schedule,
            })
        };
        sized().ok_or(InvalidBatch)
    }
}

/// A public batch argument with one v2 PCS opening. Parse untrusted bytes with
/// [`HighArityProof::from_bytes`] before verifying the claimed root statement.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HighArityProof {
    profile: Profile,
    roster: Vec<Roster>,
    nonce: [u8; 32],
    root: Digest,
    row: Vec<Vec<E>>,
    fold: fold::Fold,
    col: Vec<Vec<E>>,
    z: E,
    opening: pcs::Opening,
}
fn start(
    profile: Profile,
    shape: &Shape,
    stmt: &IvcSubtreeStatement,
    roster: &[Roster],
    nonce: &[u8; 32],
    root: &Digest,
) -> fold::Channel {
    let public: Vec<_> = stmt
        .public_inputs()
        .iter()
        .flat_map(|x| x.to_le_bytes())
        .collect();
    let binding = wire::roster_bytes(roster);
    let mut tr = Transcript::new(
        profile,
        &[MAGIC, &shape.digest(), &public, &binding, nonce, root],
    );
    tr.limit_calls(FS_CALLS);
    fold::Channel { profile, tr }
}

struct Column {
    matrix: Vec<E>,
    claim: E,
}

/// The constant one and the public inputs of every single-signer statement,
/// folded with the instance weights `eq_u`.
fn public_prefix(
    stmt: &IvcSubtreeStatement,
    roster: &[Roster],
    eq_u: &[E],
) -> [E; STATEMENT_WORDS + 1] {
    let mut prefix = [E::ZERO; STATEMENT_WORDS + 1];
    let mut weights = eq_u.iter();
    for rec in roster {
        for i in rec.signers() {
            let w = *weights.next().expect("validated instance count");
            let s = rec.single(stmt.policy_registry_root, stmt.message_digest, i);
            prefix[0] += w;
            for (sum, x) in prefix[1..].iter_mut().zip(s.public_inputs()) {
                *sum += w.mul_base(x);
            }
        }
    }
    prefix
}

fn column(
    ch: &mut fold::Channel,
    shape: &Shape,
    g: &Geometry,
    rx: &[E],
    prefix: [E; STATEMENT_WORDS + 1],
    abc: [E; 3],
) -> Column {
    let alpha = ch.tr.squeeze_fp5(b"COLUMN_BATCH");
    let comb = [E::ONE, alpha, alpha.square()];
    let mut matrix = protocol::column_table(shape, &protocol::eq_table(rx), &comb, 1 << g.columns);
    let mut claim = abc[0] + comb[1] * abc[1] + comb[2] * abc[2];
    let mut power = comb[2] * alpha;
    for (m, public) in matrix.iter_mut().zip(prefix) {
        *m += power;
        claim += power * public;
        power *= alpha;
    }
    Column { matrix, claim }
}

fn evaluation_point(g: &Geometry, mut y: Vec<E>, u: &[E]) -> Vec<E> {
    y.extend_from_slice(&u[..u.len() - g.stripes.ilog2() as usize]);
    y.resize(g.log, E::ZERO);
    y
}
fn kernel(point: &[E]) -> Vec<E> {
    let mut k = vec![E::ONE; 1 << point.len()];
    for (i, &r) in point.iter().enumerate() {
        let (lo, hi) = k[..2 << i].split_at_mut(1 << i);
        pcs::par_chunks_mut(hi, |off, part| {
            for (out, &v) in part.iter_mut().zip(&lo[off..]) {
                *out = v * r;
            }
        });
    }
    k
}

/// Prove completed committees in ascending order. Several adjacent groups may
/// name the same shard. A member present in multiple groups contributes once.
/// Supply a fresh private seed for each proof.
pub fn prove_high_arity_tree(
    registry: &IvcPolicyRegistry,
    message_digest: [u8; 32],
    shards: &[IvcShard<'_>],
    profile: Profile,
    seed: &[u8; 32],
) -> Result<(IvcSubtreeStatement, HighArityProof), HighArityError> {
    use alloc::collections::BTreeMap;
    // Refuse before any witness is derived. `Geometry::new` enforces the same gate.
    if profile.rate_half() {
        return Err(UnsupportedProfile);
    }
    let policy_root = registry.root();
    let mut roster = Vec::new();
    let mut witnesses = Vec::new();
    if registry.committee.depth != COMMITTEE.depth {
        return Err(InvalidBatch);
    }
    for run in shards.chunk_by(|a, b| a.shard_id == b.shard_id) {
        let first = &run[0];
        let id = first.shard_id;
        id.checked_add(1).ok_or(InvalidBatch)?;
        let mut rec = Roster {
            id,
            threshold: first.policy.threshold().try_into().or(Err(InvalidBatch))?,
            bitmap: [0; IVC_BITMAP_BYTES],
        };
        let mut members = BTreeMap::new();
        for group in run {
            if group.signers.is_empty()
                || group.signers.len() > registry.committee.capacity
                || group
                    .signers
                    .windows(2)
                    .any(|p| p[0].member_index >= p[1].member_index)
                || group.policy.threshold() != first.policy.threshold()
            {
                return Err(InvalidBatch);
            }
            for signer in group.signers {
                let i = signer.member_index;
                *rec.bitmap.get_mut(i / 8).ok_or(InvalidBatch)? |= 1 << (i % 8);
                let single = rec.single(policy_root, message_digest, i);
                let leaf = IvcShard {
                    shard_id: id,
                    policy: group.policy,
                    signers: core::slice::from_ref(signer),
                };
                let witness = leaf::Witness::for_committee(registry, &single, &leaf, COMMITTEE)
                    .ok_or(InvalidBatch)?;
                members.entry(i).or_insert((single, witness));
            }
        }
        witnesses.extend(members.into_values());
        roster.push(rec);
    }
    let stmt = aggregate(&roster, policy_root, message_digest).ok_or(InvalidBatch)?;
    let shape = shape();
    let g = Geometry::new(profile, &shape, witnesses.len())?;
    let width = 1 << g.columns;
    let cells = g
        .stripes
        .checked_mul(1 << g.log)
        .filter(|&n| core::alloc::Layout::array::<F>(n).is_ok())
        .ok_or(InvalidBatch)?;
    let mut table = SecretBuffer::new(vec![F::ZERO; cells]);
    let mut bases = Vec::with_capacity(witnesses.len());
    for (block, (s, w)) in table.chunks_exact_mut(width).zip(witnesses) {
        let mut cs = ConstraintSystem::witness_only();
        populate(&mut cs, &s, &w);
        let z = SecretBuffer::new(cs.finish_assignment(&shape).ok_or(InvalidBatch)?);
        bases.push(protocol::row_tables(&shape, &z, true).ok_or(InvalidBatch)?);
        block[..z.len()].copy_from_slice(&z);
    }
    let mut coins = SeedStream::new(b"QSAG.IVC2.PCS/v1", seed);
    let nonce = coins.next_bytes32();
    let salt = SecretBuffer::new(coins.next_bytes32());
    let m = pcs::mask_len(g.log, g.schedule.stages[0].step_vars);
    let mut mask = vec![E::ZERO; m];
    for v in &mut mask {
        *v = coins.next_fp5();
    }
    let (committed, root) = if g.stripes == 1 {
        let c = pcs::commit(
            profile,
            g.log,
            &g.schedule,
            crate::pcs::hypercube_to_monomial_coeffs(&table),
            mask,
            &salt,
            &nonce,
        );
        let root = c.root();
        (Commitment::Scalar(c), root)
    } else {
        let c = pcs::interleave::Interleaved::commit(
            profile,
            g.log,
            &g.schedule,
            &table,
            mask,
            nonce,
            *salt,
        )
        .ok_or(InvalidBatch)?;
        let root = c.root();
        (Commitment::Vector(c), root)
    };
    let mut ch = start(profile, &shape, &stmt, &roster, &nonce, &root);
    let t = ch.point(b"INSTANCE_POINT", g.instances);
    let tau = ch.point(b"ROW_POINT", shape.log_rows);
    let (row, rx, abc) = protocol::batched_row_sumcheck(
        &tau,
        &protocol::eq_table(&t),
        shape.num_sbox,
        bases,
        |co| ch.round(b"ROW", co),
    );
    if protocol::eq_eval(&tau, &rx).is_zero() {
        return Err(ChallengeRejected);
    }
    let (fold, u) = fold::prove(
        &mut ch,
        &t,
        protocol::prefix_indicator(&rx, shape.num_sbox),
        abc,
    );
    let eq_u = protocol::eq_table(&u);
    let mut folded = vec![E::ZERO; width];
    pcs::par_chunks_mut(&mut folded, |off, part| {
        for (&w, block) in eq_u.iter().zip(table.chunks_exact(width)) {
            for (out, &v) in part.iter_mut().zip(&block[off..]) {
                *out += w.mul_base(v);
            }
        }
    });
    drop(table);
    let prefix = public_prefix(&stmt, &roster, &eq_u);
    let col = column(&mut ch, &shape, &g, &rx, prefix, fold.abc);
    let (col, y, [_, z]) =
        fold::sumcheck(&mut ch, b"COLUMN", 2, [col.matrix, folded], |[m, z]| m * z);
    ch.bind(b"OPEN_VALUE", &[z]);
    let k = kernel(&evaluation_point(&g, y, &u));
    let opening = match committed {
        Commitment::Scalar(c) => pcs::open(&c, k, z, &mut ch.tr).ok(),
        Commitment::Vector(c) => c.open(
            &protocol::eq_table(&u[u.len() - g.stripes.ilog2() as usize..]),
            k,
            z,
            &mut ch.tr,
        ),
    }
    .filter(|_| !ch.tr.exhausted())
    .ok_or(ChallengeRejected)?;
    Ok((
        stmt,
        HighArityProof {
            profile,
            roster,
            nonce,
            root,
            row,
            fold,
            col,
            z,
            opening,
        },
    ))
}

/// Verify the complete interval and signer count against the caller's expected
/// registry root and application digest in `stmt`.
pub fn verify_high_arity_tree(stmt: &IvcSubtreeStatement, proof: &HighArityProof) -> bool {
    verify(stmt, proof).is_some()
}
fn verify(stmt: &IvcSubtreeStatement, p: &HighArityProof) -> Option<()> {
    if aggregate(&p.roster, stmt.policy_registry_root, stmt.message_digest)?.ne(stmt) {
        return None;
    }
    let shape = shape();
    let g = Geometry::new(p.profile, &shape, stmt.total_signers.try_into().ok()?).ok()?;
    let mut ch = start(p.profile, &shape, stmt, &p.roster, &p.nonce, &p.root);
    let t = ch.point(b"INSTANCE_POINT", g.instances);
    let tau = ch.point(b"ROW_POINT", shape.log_rows);
    let (rx, claim) = fold::check_rounds(&mut ch, b"ROW", &p.row, E::ZERO)?;
    let u = p.fold.check(
        &mut ch,
        &t,
        protocol::prefix_indicator(&rx, shape.num_sbox),
        protocol::eq_eval(&tau, &rx),
        claim,
    )?;
    let prefix = public_prefix(stmt, &p.roster, &protocol::eq_table(&u));
    let col = column(&mut ch, &shape, &g, &rx, prefix, p.fold.abc);
    let (y, end) = fold::check_rounds(&mut ch, b"COLUMN", &p.col, col.claim)?;
    let m = protocol::eq_table(&y)
        .into_iter()
        .zip(col.matrix)
        .fold(E::ZERO, |a, (w, x)| a + w * x);
    if end != m * p.z {
        return None;
    }
    ch.bind(b"OPEN_VALUE", &[p.z]);
    let term = pcs::TensorTerm {
        weight: E::ONE,
        point: evaluation_point(&g, y, &u),
    };
    let accepted = if g.stripes == 1 {
        pcs::verify(
            p.profile,
            &p.nonce,
            &p.root,
            g.log,
            &g.schedule,
            &[term],
            p.z,
            &p.opening,
            &mut ch.tr,
        )
    } else {
        let weights = protocol::eq_table(&u[u.len() - g.stripes.ilog2() as usize..]);
        pcs::interleave::verify(
            p.profile,
            &p.nonce,
            &p.root,
            g.log,
            &g.schedule,
            &weights,
            &term,
            p.z,
            &p.opening,
            &mut ch.tr,
        )
    };
    (accepted && !ch.tr.exhausted()).then_some(())
}
