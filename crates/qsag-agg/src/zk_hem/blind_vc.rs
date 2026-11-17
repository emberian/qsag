//! `BlindVC` selective-disclosure presentation as a zk-Hem relation.
//!
//! Presentations use the committed-mask protocol, whose zero-knowledge and knowledge-
//! soundness statements are summarised on [`protocol::prove`] and given in
//! `crates/qsag-agg/SECURITY.md`. Selective disclosure describes which attributes are public
//! inputs; the proof reveals nothing else about the witness within those bounds.
//!
//! The statement is the one of `qsag-cred::blind_vc::eval_sd_plaintext_circuit`: the holder
//! knows attributes, a holder blind, a presentation blind and an accumulator path such that
//!
//! * `commit = sponge12(attrs[..max(arity, 6)] || holder_blind || schema words(ATTR) || arity)`
//!   is a leaf under the public accumulator root (depth 20, one Boolean and six limb swaps
//!   per level, `sponge12` of the ordered pair with epoch, level and node tag),
//! * the public presentation commitment is the same sponge with the presentation blind and
//!   the `PRES` tag,
//! * the public scope tag is `sponge12(holder_blind || scope || 0 || 0 || schema words(SCOPE))`,
//! * disclosed attributes equal their public values.
//!
//! Hashing uses this crate's canonical width-12 Poseidon2. `qsag-cred` takes its permutation
//! from `qsag-accel`; the two agree once that crate carries the canonical profile.

use alloc::vec::Vec;

use super::protocol::{self, ZkHemError, ZkHemProof};
use super::relation::{ConstraintSystem, Lc, Shape, sponge12, sponge12_native};
use crate::field::Goldilocks;
use crate::pcs::WhirSecurityRegime;
use crate::sponge::POSEIDON2_CONST_IV;

type F = Goldilocks;

pub const MAX_VC_ATTRS: usize = 32;
pub const VC_ACCUMULATOR_DEPTH: usize = 20;

const VC_ATTR_COMMIT_TAG: u64 = 0x5643_4154_5452_5631; // "VCATTRV1"
const VC_PRES_COMMIT_TAG: u64 = 0x5643_5052_4553_5631; // "VCPRESV1"
const VC_SCOPE_TAG_DOM: u64 = 0x5643_5343_4F50_5631; // "VCSCOPV1"
const VC_MERKLE_NODE_TAG: u64 = 0x5643_4D4B_4C45_5631; // "VCMKLEV1"

#[inline]
fn f(x: u64) -> F {
    F::from_u64_reduced(x)
}

/// `[schema_id & 0xffff_ffff, (schema_id >> 32) + tag]`.
fn schema_words(schema_id: u64, tag: u64) -> [F; 2] {
    [f(schema_id & 0xffff_ffff), f(schema_id >> 32) + f(tag)]
}

fn merkle_tail(epoch: u64, level: usize) -> [F; 4] {
    [
        f(epoch & 0xffff_ffff),
        f(level as u64),
        f(VC_MERKLE_NODE_TAG),
        f(epoch >> 32) + f(POSEIDON2_CONST_IV),
    ]
}

/// Public part of a presentation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlindVcStatement {
    pub arity: usize,
    pub issuer_epoch: u64,
    pub schema_id: u64,
    pub scope: [F; 4],
    /// `(attribute index, value)`, strictly ascending by index.
    pub disclosed: Vec<(usize, F)>,
    pub accumulator_root: [F; 6],
    pub presentation_commitment: [F; 6],
    pub scope_tag: [F; 6],
}

/// Secret part of a presentation.
#[derive(Clone, PartialEq, Eq)]
pub struct BlindVcWitness {
    /// All `arity` attributes, disclosed ones included.
    pub attrs: Vec<F>,
    pub holder_blind: [F; 4],
    pub presentation_blind: [F; 4],
    /// `true` when the running node is the right child at that level.
    pub path_bits: [bool; VC_ACCUMULATOR_DEPTH],
    pub siblings: [[F; 6]; VC_ACCUMULATOR_DEPTH],
}

impl Drop for BlindVcWitness {
    fn drop(&mut self) {
        qsag_asm::volatile_fill(&mut self.attrs, F::ZERO);
        qsag_asm::volatile_fill(&mut self.holder_blind, F::ZERO);
        qsag_asm::volatile_fill(&mut self.presentation_blind, F::ZERO);
        qsag_asm::volatile_fill(&mut self.path_bits, false);
        for sibling in &mut self.siblings {
            qsag_asm::volatile_fill(sibling, F::ZERO);
        }
    }
}

impl BlindVcStatement {
    fn well_formed(&self) -> bool {
        (1..=MAX_VC_ATTRS).contains(&self.arity)
            && self.disclosed.iter().all(|&(i, _)| i < self.arity)
            && self.disclosed.windows(2).all(|w| w[0].0 < w[1].0)
    }

    /// The statement a holder derives from its secrets.
    pub fn derive(
        witness: &BlindVcWitness,
        issuer_epoch: u64,
        schema_id: u64,
        scope: [F; 4],
        disclosed_indices: &[usize],
    ) -> Self {
        let arity = witness.attrs.len();
        let commit = |blind: &[F; 4], tag: u64| -> [F; 6] {
            let mut msg = witness.attrs.clone();
            msg.resize(arity.max(6), F::ZERO);
            msg.extend_from_slice(blind);
            msg.extend_from_slice(&schema_words(schema_id, tag));
            msg.push(f(arity as u64));
            let st = sponge12_native(&msg);
            qsag_asm::volatile_fill(&mut msg, F::ZERO);
            core::array::from_fn(|j| st[j])
        };
        let mut node = commit(&witness.holder_blind, VC_ATTR_COMMIT_TAG);
        for (level, (&bit, sibling)) in witness.path_bits.iter().zip(&witness.siblings).enumerate()
        {
            let (left, right) = if bit {
                (sibling, &node)
            } else {
                (&node, sibling)
            };
            let mut msg = Vec::with_capacity(16);
            msg.extend_from_slice(left);
            msg.extend_from_slice(right);
            msg.extend_from_slice(&merkle_tail(issuer_epoch, level));
            let st = sponge12_native(&msg);
            node = core::array::from_fn(|j| st[j]);
        }
        let mut scope_msg = witness.holder_blind.to_vec();
        scope_msg.extend_from_slice(&scope);
        scope_msg.extend_from_slice(&[F::ZERO, F::ZERO]);
        scope_msg.extend_from_slice(&schema_words(schema_id, VC_SCOPE_TAG_DOM));
        let scope_state = sponge12_native(&scope_msg);
        qsag_asm::volatile_fill(&mut scope_msg, F::ZERO);
        Self {
            arity,
            issuer_epoch,
            schema_id,
            scope,
            disclosed: disclosed_indices
                .iter()
                .map(|&i| (i, witness.attrs[i]))
                .collect(),
            accumulator_root: node,
            presentation_commitment: commit(&witness.presentation_blind, VC_PRES_COMMIT_TAG),
            scope_tag: core::array::from_fn(|j| scope_state[j]),
        }
    }

    /// Transcript binding of the public values and the verifier's fresh `context`.
    fn statement_bytes(&self, context: &[u8]) -> Vec<u8> {
        let mut out = b"QSAG.ZKHEM.BLINDVC/v1".to_vec();
        for n in [
            self.arity as u64,
            self.issuer_epoch,
            self.schema_id,
            self.disclosed.len() as u64,
        ] {
            out.extend_from_slice(&n.to_le_bytes());
        }
        for &(i, v) in &self.disclosed {
            out.extend_from_slice(&(i as u64).to_le_bytes());
            out.extend_from_slice(&v.to_le_bytes());
        }
        for v in self
            .scope
            .iter()
            .chain(&self.accumulator_root)
            .chain(&self.presentation_commitment)
            .chain(&self.scope_tag)
        {
            out.extend_from_slice(&v.to_le_bytes());
        }
        out.extend_from_slice(&(context.len() as u64).to_le_bytes());
        out.extend_from_slice(context);
        out
    }

    /// The relation, with the assignment for `witness`. Its structure depends only on
    /// `arity` and the disclosed index set.
    fn synthesize(&self, witness: &BlindVcWitness) -> (Shape, Vec<F>) {
        let mut cs = ConstraintSystem::new();
        let attrs: Vec<Lc> = (0..self.arity.max(6))
            .map(|i| {
                if i >= self.arity {
                    Lc::zero()
                } else if let Some(&(_, v)) = self.disclosed.iter().find(|&&(d, _)| d == i) {
                    Lc::constant(v)
                } else {
                    cs.alloc(witness.attrs[i]).into()
                }
            })
            .collect();
        let holder: [Lc; 4] = core::array::from_fn(|i| cs.alloc(witness.holder_blind[i]).into());
        let pres: [Lc; 4] =
            core::array::from_fn(|i| cs.alloc(witness.presentation_blind[i]).into());
        let commit = |cs: &mut ConstraintSystem, blind: &[Lc; 4], tag: u64| -> [Lc; 6] {
            let mut msg = attrs.clone();
            msg.extend_from_slice(blind);
            msg.extend(schema_words(self.schema_id, tag).map(Lc::constant));
            msg.push(Lc::constant(f(self.arity as u64)));
            let st = sponge12(cs, &msg);
            core::array::from_fn(|j| st[j].clone())
        };
        let pin = |cs: &mut ConstraintSystem, got: &[Lc; 6], want: &[F; 6]| {
            for (g, &w) in got.iter().zip(want) {
                cs.enforce_zero(g.plus_const(F::ZERO - w));
            }
        };

        let mut node = commit(&mut cs, &holder, VC_ATTR_COMMIT_TAG);
        for level in 0..VC_ACCUMULATOR_DEPTH {
            let bit: Lc = cs.alloc(f(u64::from(witness.path_bits[level]))).into();
            cs.enforce_boolean(&bit);
            let mut msg: Vec<Lc> = Vec::with_capacity(16);
            let mut right = Vec::with_capacity(6);
            for (j, cur) in node.iter().enumerate() {
                let sibling: Lc = cs.alloc(witness.siblings[level][j]).into();
                let delta: Lc = cs.mul(&bit, &sibling.minus(cur)).into();
                msg.push(cur.plus(&delta));
                right.push(sibling.minus(&delta));
            }
            msg.extend(right);
            msg.extend(merkle_tail(self.issuer_epoch, level).map(Lc::constant));
            let st = sponge12(&mut cs, &msg);
            node = core::array::from_fn(|j| st[j].clone());
        }
        pin(&mut cs, &node, &self.accumulator_root);

        let presentation = commit(&mut cs, &pres, VC_PRES_COMMIT_TAG);
        pin(&mut cs, &presentation, &self.presentation_commitment);

        let mut scope_msg: Vec<Lc> = holder.to_vec();
        scope_msg.extend(self.scope.map(Lc::constant));
        scope_msg.extend([Lc::zero(), Lc::zero()]);
        scope_msg.extend(schema_words(self.schema_id, VC_SCOPE_TAG_DOM).map(Lc::constant));
        let scope_state = sponge12(&mut cs, &scope_msg);
        pin(
            &mut cs,
            &core::array::from_fn(|j| scope_state[j].clone()),
            &self.scope_tag,
        );
        cs.finish()
    }

    /// The public relation. `None` for a malformed statement.
    pub fn shape(&self) -> Option<Shape> {
        if !self.well_formed() {
            return None;
        }
        let placeholder = BlindVcWitness {
            attrs: alloc::vec![F::ZERO; self.arity],
            holder_blind: [F::ZERO; 4],
            presentation_blind: [F::ZERO; 4],
            path_bits: [false; VC_ACCUMULATOR_DEPTH],
            siblings: [[F::ZERO; 6]; VC_ACCUMULATOR_DEPTH],
        };
        Some(self.synthesize(&placeholder).0)
    }
}

/// Prove a presentation. `context` is the verifier's fresh challenge; `seed` must be uniform
/// and secret.
pub fn prove_presentation(
    statement: &BlindVcStatement,
    witness: &BlindVcWitness,
    context: &[u8],
    regime: WhirSecurityRegime,
    seed: &[u8; 32],
) -> Result<ZkHemProof, ZkHemError> {
    if !statement.well_formed() || witness.attrs.len() != statement.arity {
        return Err(ZkHemError::Unsatisfied);
    }
    let (shape, assignment) = statement.synthesize(witness);
    protocol::prove(
        &shape,
        assignment,
        &statement.statement_bytes(context),
        regime,
        seed,
    )
}

/// Verify a presentation against a statement whose root, epoch, schema and scope the
/// verifier has pinned, and its own fresh `context`.
pub fn verify_presentation(
    statement: &BlindVcStatement,
    context: &[u8],
    regime: WhirSecurityRegime,
    proof: &ZkHemProof,
) -> bool {
    statement.shape().is_some_and(|shape| {
        protocol::verify(
            &shape,
            &[],
            &statement.statement_bytes(context),
            regime,
            proof,
        )
    })
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use super::*;

    fn witness(arity: usize) -> BlindVcWitness {
        BlindVcWitness {
            attrs: (0..arity).map(|i| f(1_000 + 17 * i as u64)).collect(),
            holder_blind: core::array::from_fn(|i| f(0xA000 + i as u64)),
            presentation_blind: core::array::from_fn(|i| f(0xB000 + i as u64)),
            path_bits: core::array::from_fn(|i| i % 3 == 1),
            siblings: core::array::from_fn(|l| core::array::from_fn(|j| f((l * 6 + j) as u64 + 5))),
        }
    }

    fn scope() -> [F; 4] {
        [f(11), f(22), f(33), f(44)]
    }

    #[test]
    fn relation_has_the_expected_size_and_is_witness_independent() {
        let w = witness(MAX_VC_ATTRS);
        let st = BlindVcStatement::derive(&w, 7, 0x1234_5678_9ABC, scope(), &[0, 5]);
        let (shape, z) = st.synthesize(&w);
        assert!(shape.is_satisfied(&z));
        assert_eq!(shape, st.shape().unwrap());
        // 7 + 7 commitment permutations, 3 per accumulator level, 3 for the scope tag.
        assert_eq!(shape.num_sbox, (14 + 3 * VC_ACCUMULATOR_DEPTH + 3) * 118);
        assert_eq!(shape.log_rows, 14);
    }

    #[test]
    fn presentation_verifies_and_binds_statement_and_context() {
        let regime = WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128;
        let w = witness(8);
        let st = BlindVcStatement::derive(&w, 7, 99, scope(), &[1, 6]);
        let proof = prove_presentation(&st, &w, b"nonce-1", regime, &[21; 32]).unwrap();
        assert!(verify_presentation(&st, b"nonce-1", regime, &proof));
        assert!(!verify_presentation(&st, b"nonce-2", regime, &proof));

        let mut other = st.clone();
        other.disclosed[0].1 += F::ONE;
        assert!(!verify_presentation(&other, b"nonce-1", regime, &proof));
        let mut other = st.clone();
        other.accumulator_root[3] += F::ONE;
        assert!(!verify_presentation(&other, b"nonce-1", regime, &proof));
        let mut other = st.clone();
        other.scope_tag[0] += F::ONE;
        assert!(!verify_presentation(&other, b"nonce-1", regime, &proof));
        let mut other = st.clone();
        other.disclosed.pop();
        assert!(!verify_presentation(&other, b"nonce-1", regime, &proof));
    }

    #[test]
    fn prover_refuses_a_credential_outside_the_accumulator() {
        let regime = WhirSecurityRegime::BciksJohnsonQrom128;
        let w = witness(6);
        let st = BlindVcStatement::derive(&w, 1, 2, scope(), &[]);
        let mut wrong = witness(6);
        wrong.siblings[4][2] += F::ONE;
        assert_eq!(
            prove_presentation(&st, &wrong, b"n", regime, &[1; 32]),
            Err(ZkHemError::Unsatisfied)
        );
        let mut wrong = witness(6);
        wrong.holder_blind[0] += F::ONE;
        assert_eq!(
            prove_presentation(&st, &wrong, b"n", regime, &[1; 32]),
            Err(ZkHemError::Unsatisfied)
        );
    }

    #[test]
    #[ignore = "measurement: run with --ignored --nocapture"]
    fn bench_blind_vc_presentation() {
        for regime in [
            WhirSecurityRegime::BciksJohnsonQrom128,
            WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128,
        ] {
            let w = witness(MAX_VC_ATTRS);
            let st = BlindVcStatement::derive(&w, 7, 0x1234_5678_9ABC, scope(), &[0, 5, 9]);
            let shape = st.shape().unwrap();
            let layout = protocol::Layout::new(&shape, regime).unwrap();
            let median = |mut v: Vec<f64>| {
                v.sort_by(f64::total_cmp);
                v[v.len() / 2]
            };
            let mut prove_ms = Vec::new();
            let mut proof = None;
            for run in 0..3u8 {
                let t = std::time::Instant::now();
                proof = Some(prove_presentation(&st, &w, b"ctx", regime, &[run; 32]).unwrap());
                prove_ms.push(t.elapsed().as_secs_f64() * 1e3);
            }
            let proof = proof.unwrap();
            let bytes = proof.to_bytes();
            let time_verify = || {
                median(
                    (0..5)
                        .map(|_| {
                            let t = std::time::Instant::now();
                            let decoded = ZkHemProof::from_bytes(&bytes, &shape, regime).unwrap();
                            assert!(verify_presentation(&st, b"ctx", regime, &decoded));
                            t.elapsed().as_secs_f64() * 1e3
                        })
                        .collect(),
                )
            };
            let verify_all = time_verify();
            let verify_one = crate::with_worker_limit(1, time_verify);
            std::println!(
                "ZKHEM_BLINDVC regime={regime:?} sbox_rows={} rows=2^{} vars={} cells=2^{} \
                 blind_cells={} proof_bytes={} proof_kib={:.2} prove_ms_median={:.1} \
                 verify_ms_all_workers={verify_all:.2} verify_ms_1_worker={verify_one:.2} \
                 workers={}",
                shape.num_sbox,
                shape.log_rows,
                shape.num_vars,
                layout.log_cells,
                layout.blind_cells,
                bytes.len(),
                bytes.len() as f64 / 1024.0,
                median(prove_ms),
                crate::parallel_workers(),
            );
        }
    }
}
