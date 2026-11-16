//! Bounded, canonical decoder for the split carrier. Lengths never reserve memory
//! before the corresponding bytes have been read; no allocation trusts a count alone.
use super::*;
use crate::zk_hem::recursive_whir::{Ext, FixedPathQuery};

type E = GoldilocksExt4;
struct Reader<'a>(&'a [u8]);
impl<'a> Reader<'a> {
    fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        let (head, tail) = self.0.split_at_checked(n)?;
        self.0 = tail;
        Some(head)
    }
    fn byte(&mut self) -> Option<u8> { Some(self.take(1)?[0]) }
    fn size(&mut self) -> Option<usize> {
        usize::try_from(u64::from_le_bytes(self.take(8)?.try_into().ok()?)).ok()
    }
    fn f(&mut self) -> Option<F> {
        F::from_canonical(u64::from_le_bytes(self.take(8)?.try_into().ok()?)).ok()
    }
    fn digest(&mut self) -> Option<[F; 4]> { Some([self.f()?, self.f()?, self.f()?, self.f()?]) }
    fn e(&mut self) -> Option<E> { Some(E::from_limbs(self.digest()?)) }
    fn vector<T>(&mut self, minimum_bytes: usize, mut parse: impl FnMut(&mut Self) -> Option<T>) -> Option<Vec<T>> {
        let n = self.size()?;
        if n > self.0.len() / minimum_bytes { return None; }
        let mut values = Vec::new();
        for _ in 0..n { values.push(parse(self)?); }
        Some(values)
    }
    fn queries(&mut self) -> Option<Vec<FixedPathQuery>> {
        self.vector(16, |r| Some(FixedPathQuery {
            values: r.vector(32, Self::e)?,
            siblings: r.vector(32, Self::digest)?,
        }))
    }
    fn opening(&mut self) -> Option<Correlated3WhirProof> {
        let mut cross_evals = [[E::ZERO; 3]; 3];
        for e in cross_evals.iter_mut().flatten() { *e = self.e()?; }
        let mut stage0_canopy_leaves = [Vec::new(), Vec::new(), Vec::new()];
        for leaves in &mut stage0_canopy_leaves { *leaves = self.vector(32, Self::digest)?; }
        let stage0_queries = self.vector(3 * (8 + 16), |r| r.queries()?.try_into().ok())?;
        let later_stage_roots = self.vector(32, Self::digest)?;
        let later_canopy_leaves = self.vector(8, |r| r.vector(32, Self::digest))?;
        let ood_evals = self.vector(64, |r| Some([r.e()?, r.e()?]))?;
        let fold_polys = self.vector(160, |r| Some([r.e()?, r.e()?, r.e()?, r.e()?, r.e()?]))?;
        let mut nonces = || self.vector(8, |r| Some([
            u32::from_le_bytes(r.take(4)?.try_into().ok()?),
            u32::from_le_bytes(r.take(4)?.try_into().ok()?),
        ]));
        let fold_nonces = nonces()?;
        let query_nonces = nonces()?;
        let later_queries = self.vector(8, Self::queries)?;
        let final_coeffs = self.vector(32, Self::e)?;
        Some(Correlated3WhirProof { cross_evals, stage0_canopy_leaves, stage0_queries,
            later_stage_roots, later_canopy_leaves, ood_evals, fold_polys, fold_nonces,
            query_nonces, later_queries, final_coeffs })
    }
    fn edge(&mut self) -> Option<Edge> {
        let regime = WhirSecurityRegime::from_u8(self.byte()?)?;
        let num_vars = self.size()?;
        if !regime.uses_poseidon2_canopy() || !(2..=crate::pcs::MAX_PCS_NUM_VARS).contains(&num_vars) { return None; }
        let mut transcript = [F::ZERO; 12];
        for word in &mut transcript { *word = self.f()?; }
        let roots = [self.digest()?, self.digest()?, self.digest()?];
        let mut points = [Vec::new(), Vec::new(), Vec::new()];
        for point in &mut points {
            *point = self.vector(32, |r| Some(Ext(r.digest()?)))?;
            if point.len() != num_vars { return None; }
        }
        let mut claims: [[Option<Ext<F>>; 3]; 3] = core::array::from_fn(|_| core::array::from_fn(|_| None));
        for claim in claims.iter_mut().flatten() {
            *claim = match self.byte()? { 0 => None, 1 => Some(Ext(self.digest()?)), _ => return None };
        }
        let prior = self.digest()?;
        let opening = self.opening()?;
        Some(Edge { claim: DeferredPcsClaim { regime, num_vars, transcript, roots, points, claims }, opening, prior })
    }
}

pub(super) fn decode(vk: &ShapeVerifierKey, bytes: &[u8]) -> Option<SplitSubtreeAggregate> {
    if vk.num_public != PUBLIC_WORDS || !vk.is_well_formed() { return None; }
    let mut r = Reader(bytes);
    if r.take(8)? != b"QSAGSPD1" { return None; }
    let subtree_registry_root = r.digest()?;
    let epoch_floor = r.f()?;
    let mut message_digest = [F::ZERO; 5];
    for word in &mut message_digest { *word = r.f()?; }
    let total_active_signers = r.f()?;
    let min_key_idx = r.f()?.to_canonical_u64();
    let max_key_idx = r.f()?.to_canonical_u64();
    let total_active_weight = r.f()?.to_canonical_u64();
    if min_key_idx > max_key_idx || max_key_idx >= 1 << 58
        || total_active_signers == F::ZERO || total_active_signers.to_canonical_u64() >= 1 << 62
        || total_active_weight == 0 || total_active_weight >= 1 << 62 { return None; }
    let public = SubtreePublic { subtree_registry_root, epoch_floor, message_digest,
        total_active_signers, min_key_idx, max_key_idx, total_active_weight };
    let n = r.size()?;
    let proof = HologramPublicProof::from_bytes(r.take(n)?, vk)?;
    let ledger = r.vector(2 * 200, |r| Some(LedgerNode { edges: [r.edge()?, r.edge()?] }))?;
    if !r.0.is_empty() || ledger.is_empty() { return None; }
    Some(SplitSubtreeAggregate { public, proof, ledger })
}
