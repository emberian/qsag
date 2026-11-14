module
/-
# Qsag.SuccinctAggregationIop — Packed 4-Limb Goldilocks Signature Engine, Degree-8 Row Sumcheck Arithmetization, the 256-Column `StepOp` Table, Steiner Merkle-Canopy Multi-Proofs, and the `GoldilocksExt4` WHIR Layer

Constructive formalization of four layers of the `qsag-agg` succinct post-quantum signature
aggregation engine (`crates/qsag-agg/src/`):
1. **§1 (`sig.rs`)**: Packed 4-limb `Digest4` (`[Goldilocks; 4]`) Width-12 `Poseidon2` WOTS+C
   (`w = 4`, constant target sum, injective packed tweak address `packWotsAddrLimb`, Jive
   feed-forward step `poseidon2Compress12FF`, 256-bit-capacity endpoint sponge, and 2-block
   full-`pkSeed` `merkleNodeHash` with 1-based node levels) + hypertree / FORS authentication
   engine, with unconditional completeness (`aggNativeSig_completeness`) and secret-anchored
   forgery extraction (`aggNativeSig_wots_merkle_soundness`). The FORS instance is addressed as
   in `recover_fors_pk`: `(kp_idx, tree_idx)` is the split of `leaf_global_idx` at the subtree
   height (`corduroy_fors_addr_split`), the leaf tweak packs `(kp_idx << 24) | (j << a) | idx_j`,
   the roots sponge binds `[kp_idx, tree_idx, FORS_TREES]`, and every internal node of FORS
   tree `j` is hashed at node index `(kp_idx << 16) + ((j << (a - 1 - lvl)) + parent_idx)`
   (`forsNodeAddr_injective`, `tooth_fors_cross_tree_transplant_rejected`).
2. **`GoldilocksExt4` (`field.rs`)**: the quartic extension `GoldilocksExt2[v] / (v^2 - u)`
   (`v^4 = 7`) as a lawful commutative ring without zero divisors and the base-field embedding
   `embedBase`; it is the field of every sumcheck challenge below.
3. **§2 (`arithmetize.rs`, `trace.rs`)**:
   - the degree-8 row sumcheck round polynomial (`ROW_SUMCHECK_DEGREE = 8` -> `9` coefficients:
     degree `1` equality kernel times degree `7` gates), the equality kernel `evalEqExt4`, the
     kernels `evalEqNotLastExt4` / `evalShiftKernelExt4` of the inter-row shift, and the
     `RowGate7` gate AST with its `GoldilocksExt4` evaluation, all over `GoldilocksExt4`;
   - structured per-signer witness blocks whose residuals vanish exactly for valid signatures
     (`signerTraceResiduals_sound`, `signerTraceResiduals_complete`);
   - the 256-column `StepOp` execution table of `trace.rs`: the column layout (`StepOpRow`),
     the fixed program `buildSignerProgram`, the constraint classes with `step_c0`
     (`stepOpKindAndC0`), Group A (`stepOpPermTrace`, `stepOp256_groupA_exact`), the boundary
     constraints, the transition constraints of every opcode class (`stepOpConstraints`), and
     the ungated inter-row shift constraints (`stepOp256_shift_iff`,
     `stepOp256_shift_links_rows`); over `GoldilocksExt4`, the shift claim at a hypercube point
     is `NEXT_STATE(u) - PREV_STATE(u + 1)` (`stepOpShiftClaimExt4_hypercube`), and the
     `gamma`-batched intra-row claim is the batched residuals of that row, zero for at most
     `length - 1` challenges when a residual is non-zero (`stepOp256_ext4_sumcheck_sound`);
     unrestricted `tau` root counts for the actual equality and shift claims
     (`stepOpEqClaimExt4_random_tau_roots_le`, `stepOpShiftClaimExt4_random_tau_roots_le`),
     and fixed-order constraint-column batching at arbitrary `tau`
     (`stepOpEqClaimExt4_batch`, `stepOp256_gamma_roots_le`);
     `#tooth`s `tooth_stepOp256_state_splice_breaks_shift_constraint` and
     `tooth_stepOp256_zero_rows_rejected`; completeness for inactive slots
     (`stepOp256_inactive_table_complete`).
4. **§3 (`pcs.rs`, `CanopyMultiProof`)**: the Steiner-deduplicated Merkle multi-proof verifier
   `verifyCanopyMultiproof` over abstract node / root hashes: the sibling count is a function of
   the index set alone (`verifyCanopyMultiproof_exact_sibling_count`, with the missing- and
   extra-sibling rejections as corollaries), and two distinct accepted openings of one index set
   yield an explicit hash collision (`verifyCanopyMultiproof_binding`).
5. **§4 (`field.rs`, `pcs.rs`)**:
   - the canonical 32-byte encoding of `GoldilocksExt4` (`decodeExt4Bytes32_encode`,
     `decodeExt4Bytes32_canonical`);
   - the rate-escalation schedule `whirStageSchedule` (stage geometry `whirLegacyStageGeometry`
     with the query counts of a `WhirSecurityRegime`), its per-stage query and proof-of-work
     denominators, and error denominators over `p^4 > 2^255`
     (`ext4_error_denominator_bound`, against `ext2_error_denominator_cliff`);
   - a row-committed witness layout: an `AggExecutionTrace` is its committed rows only;
     `extractSignerWitnessesFromRows` reads every signer's witness block out of the rows, and
     rows satisfying the row constraints determine valid witnesses
     (`committed_rows_extract_valid_witnesses`,
     `trace_satisfies_constraints_iff_all_k_sigs_valid`,
     `tooth_tampered_committed_row_breaks_gate_or_binding`);
   - `extractCanopyCollision`, a `Type`-valued extractor returning an explicit hash collision
     from two accepted multi-proof transcripts (`extractHashCollisionFromCanopyTranscripts`
     for a byte-string hash, inhabited over the 32-byte digest `canopyPrefixHash`).

Scope. Two row layouts appear and they are not yet connected. The row-committed layout of §4
is one row per signer (14 boundary columns followed by a canonical cell stream of the
structured witness block), and for it constraint vanishing is equivalent to signature validity.
The 256-column `StepOp` table of §2 transcribes the deployed constraint system; for it this
module proves the Group A, shift, batching and `#tooth` statements listed above, and
completeness for inactive slots only. It does not prove that an honest signature yields a
satisfying `StepOp` table for an active slot, nor that a satisfying `StepOp` table yields a
signature accepted by `verifyAggNativeSig`: the simulation between the 44-limb step machine and
the verifier is open. The equality and shift claims have constructive random-`tau` root bounds
of `ell * |S|^(ell - 1)` on `S^ell`, and fixed-order constraint-column batching has a separate
`gamma` root bound. Instantiating that column list with the deployed unique-op offsets, the
transcript binding of the opening, and the recursive merge tree (`lib.rs`) remain open. §4 accounts for error denominators and query counts; it does not prove a
Reed-Solomon proximity-gap or list-decoding statement, so the per-query agreement bound (`ρ`,
or `sqrt ρ` in the Johnson regime) is an input of the accounting.
-/

public import Qsag.ConcreteSecurityBudget
import all Qsag.ConcreteSecurityBudget
public import Qsag.Constructive
public import Qsag.Goldilocks
import all Qsag.Goldilocks
public import Qsag.Keccak
public import Qsag.Poseidon2
import all Qsag.Poseidon2
public import Qsag.UcGames
public import Qsag.Aggregation
import all Qsag.Aggregation

public section
namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
attribute [local irreducible] poseidon2Perm12 poseidon2Perm12Inv

set_option autoImplicit false
set_option exponentiation.threshold 2048

/-! ## §1. Packed 4-Limb Goldilocks Field-Native Corduroy / XMSS Signature Engine (`sig.rs`) -/

/-- Packed 4-limb Goldilocks digest `[Goldilocks; 4]` (`256`-bit sponge block, `sig.rs:28`). -/
abbrev Digest4 := Lane4

/-- Signature profile selector matching `AggSigProfile` in `crates/qsag-agg/src/sig.rs`. -/
inductive AggSigProfile where
  | xmssPoseidon2
  | corduroyPoseidon2
  deriving DecidableEq, Repr

/-- Exact 64-bit ASCII domain-separation tags from `crates/qsag-agg/src/sig.rs`. -/
def domainPrfWots : Goldilocks := Goldilocks.ofNat 0x5153414757505246
def domainWotsStep : Goldilocks := Goldilocks.ofNat 0x5153414757535450
def domainWotsPk : Goldilocks := Goldilocks.ofNat 0x5153414757504B31
def domainMerkleNode : Goldilocks := Goldilocks.ofNat 0x515341474D524B4C
def domainHMsgStateful : Goldilocks := Goldilocks.ofNat 0x51534147484D5331
def domainHMsgDetTree : Goldilocks := Goldilocks.ofNat 0x5153414748445452
def domainHMsgStateless : Goldilocks := Goldilocks.ofNat 0x515341474853544C
def domainForsPrf : Goldilocks := Goldilocks.ofNat 0x5153414746505246
def domainForsLeaf : Goldilocks := Goldilocks.ofNat 0x51534147464C4546
def domainForsNode : Goldilocks := Goldilocks.ofNat 0x51534147464E4F44
def domainForsRoots : Goldilocks := Goldilocks.ofNat 0x5153414746525453
def poseidon2IvTag : Goldilocks := Goldilocks.ofNat 0x504F53325F474C31

theorem aggSigDomains_nonzero_and_distinct :
    domainPrfWots ≠ Goldilocks.zero ∧
    domainWotsStep ≠ Goldilocks.zero ∧
    domainWotsPk ≠ Goldilocks.zero ∧
    domainMerkleNode ≠ Goldilocks.zero ∧
    domainHMsgStateful ≠ Goldilocks.zero ∧
    domainHMsgDetTree ≠ Goldilocks.zero ∧
    domainPrfWots ≠ domainWotsStep ∧
    domainMerkleNode ≠ domainForsNode ∧
    domainHMsgStateful ≠ domainHMsgDetTree := by
  decide +kernel

/-- Parameterized geometry for field-native WOTS+C + XMSS / FORS hypertree signatures. -/
structure AggSigGeometry where
  profile       : AggSigProfile
  wotsChains    : Nat
  targetSum     : Nat
  numLayers     : Nat
  subtreeHeight : Nat
  forsTrees     : Nat
  forsHeight    : Nat
  deriving DecidableEq, Repr

/-- Well-formedness of an `AggSigGeometry` (`w = 4` chains, non-trivial target sum `< 3 * ell1`). -/
@[expose] def AggSigGeometry.wellFormed (g : AggSigGeometry) : Bool :=
  (0 < g.wotsChains) &&
  (g.wotsChains % 2 == 0) &&
  (g.wotsChains ≤ 128) &&
  (0 < g.targetSum) &&
  (g.targetSum < 3 * g.wotsChains) &&
  (0 < g.numLayers) &&
  (0 < g.subtreeHeight) &&
  (g.numLayers * g.subtreeHeight ≤ 64) &&
  (if g.forsTrees == 0 then g.forsHeight == 0
   else (g.forsTrees % 2 == 0) && (g.forsTrees ≤ 32) && (0 < g.forsHeight) && (g.forsHeight ≤ 8))

/-- Deployed stateful `XmssPoseidon2` geometry (`ell1 = 128, targetSum = 192, d = 1, h' = 6`). -/
def xmssPoseidon2Geom : AggSigGeometry where
  profile       := .xmssPoseidon2
  wotsChains    := 128
  targetSum     := 192
  numLayers     := 1
  subtreeHeight := 6
  forsTrees     := 0
  forsHeight    := 0

/-- Deployed stateless `CorduroyPoseidon2` geometry (`ell1 = 128, targetSum = 192, k = 32, a = 8, d = 16, h' = 4`). -/
def corduroyPoseidon2Geom : AggSigGeometry where
  profile       := .corduroyPoseidon2
  wotsChains    := 128
  targetSum     := 192
  numLayers     := 16
  subtreeHeight := 4
  forsTrees     := 32
  forsHeight    := 8

/-- Compact kernel-computable audit geometry (`ell1 = 2, targetSum = 3, d = 1, h' = 1`) for build-time `#tooth` tests. -/
def compactAuditGeom : AggSigGeometry where
  profile       := .xmssPoseidon2
  wotsChains    := 2
  targetSum     := 3
  numLayers     := 1
  subtreeHeight := 1
  forsTrees     := 0
  forsHeight    := 0

theorem deployedAggGeometries_wellFormed :
    xmssPoseidon2Geom.wellFormed = true ∧
    corduroyPoseidon2Geom.wellFormed = true ∧
    compactAuditGeom.wellFormed = true := by
  decide +kernel

/-- Validator public key (`65`-byte wire model: `profile` + 4-limb `pkSeed` + 4-limb `pkRoot`). -/
structure AggValidatorPk where
  profile : AggSigProfile
  pkSeed  : Digest4
  pkRoot  : Digest4
  deriving DecidableEq, Repr

/-- Jive feed-forward 12-to-4 `Poseidon2` compression (`poseidon2_compress12_ff` in `sig.rs:88`). -/
def poseidon2Compress12FF (in0 in1 tweak : Digest4) : Digest4 :=
  let permOut := poseidon2Perm12 ⟨in0, in1, tweak⟩
  lane4Add permOut.b0 in0

/-- Bijective `< 2^62` packed WOTS+C address limb (`pack_wots_addr_limb` in `sig.rs:285`). -/
def packWotsAddrLimb (layer kpIdx chainIdx stepIdx : Nat) : Goldilocks :=
  Goldilocks.ofNat
    ((layer % 64) * (2 ^ 44) +
     (kpIdx % (2 ^ 28)) * (2 ^ 16) +
     (chainIdx % 4096) * 16 +
     (stepIdx % 16))

private theorem pack4_unpack {l k c s : Nat}
    (hl : l < 64) (hk : k < 2 ^ 28) (hc : c < 4096) (hs : s < 16) :
    let v := l * 2 ^ 44 + k * 2 ^ 16 + c * 16 + s
    v < goldilocksPrime ∧
    v % 16 = s ∧
    (v / 16) % 4096 = c ∧
    ((v / 16) / 4096) % (2 ^ 28) = k ∧
    ((v / 16) / 4096) / (2 ^ 28) = l := by
  intro v
  have h1 : c * 16 + s < 2 ^ 16 := by
    have h16 : (2 : Nat) ^ 16 = 65536 := rfl
    rw [h16]; omega
  have h2 : k * 2 ^ 16 + (c * 16 + s) < 2 ^ 44 := by
    calc k * 2 ^ 16 + (c * 16 + s)
      _ < k * 2 ^ 16 + 2 ^ 16 := Nat.add_lt_add_left h1 _
      _ = (k + 1) * 2 ^ 16 := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ (2 ^ 28) * 2 ^ 16 := Nat.mul_le_mul_right _ hk
      _ = 2 ^ 44 := rfl
  have hLtP : v < goldilocksPrime := by
    calc v
      _ = l * 2 ^ 44 + (k * 2 ^ 16 + (c * 16 + s)) := by dsimp only [v]; simp [Nat.add_assoc]
      _ < l * 2 ^ 44 + 2 ^ 44 := Nat.add_lt_add_left h2 _
      _ = (l + 1) * 2 ^ 44 := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ 64 * 2 ^ 44 := Nat.mul_le_mul_right _ hl
      _ < goldilocksPrime := by decide
  have hFac : v = s + ((c + (k + l * 2 ^ 28) * 4096) * 16) := by
    dsimp only [v]
    have e1 : (2 : Nat) ^ 44 = (2 ^ 28) * (4096 * 16) := rfl
    have e2 : (2 : Nat) ^ 16 = 4096 * 16 := rfl
    rw [e1, e2]
    simp only [Nat.add_mul, Nat.mul_assoc, Nat.add_comm]
  have hsMod : v % 16 = s := by
    rw [hFac, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  have hv16 : v / 16 = c + (k + l * 2 ^ 28) * 4096 := by
    rw [hFac, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt hs, Nat.zero_add]
  have hcMod : (v / 16) % 4096 = c := by
    rw [hv16, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hc]
  have hv4096 : (v / 16) / 4096 = k + l * 2 ^ 28 := by
    rw [hv16, Nat.add_mul_div_right _ _ (by decide), Nat.div_eq_of_lt hc, Nat.zero_add]
  have hkMod : ((v / 16) / 4096) % (2 ^ 28) = k := by
    rw [hv4096, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  have hlDiv : ((v / 16) / 4096) / (2 ^ 28) = l := by
    rw [hv4096, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide)), Nat.div_eq_of_lt hk, Nat.zero_add]
  exact ⟨hLtP, hsMod, hcMod, hkMod, hlDiv⟩

theorem packWotsAddrLimb_injective
    {l1 k1 c1 s1 l2 k2 c2 s2 : Nat}
    (hl1 : l1 < 64) (hk1 : k1 < 2 ^ 28) (hc1 : c1 < 4096) (hs1 : s1 < 16)
    (hl2 : l2 < 64) (hk2 : k2 < 2 ^ 28) (hc2 : c2 < 4096) (hs2 : s2 < 16)
    (hEq : packWotsAddrLimb l1 k1 c1 s1 = packWotsAddrLimb l2 k2 c2 s2) :
    l1 = l2 ∧ k1 = k2 ∧ c1 = c2 ∧ s1 = s2 := by
  have hVal := congrArg Goldilocks.val hEq
  unfold packWotsAddrLimb Goldilocks.ofNat at hVal
  dsimp only at hVal
  rw [Nat.mod_eq_of_lt hl1, Nat.mod_eq_of_lt hk1, Nat.mod_eq_of_lt hc1, Nat.mod_eq_of_lt hs1,
      Nat.mod_eq_of_lt hl2, Nat.mod_eq_of_lt hk2, Nat.mod_eq_of_lt hc2, Nat.mod_eq_of_lt hs2] at hVal
  obtain ⟨hb1, hs1', hc1', hk1', hl1'⟩ := pack4_unpack hl1 hk1 hc1 hs1
  obtain ⟨hb2, hs2', hc2', hk2', hl2'⟩ := pack4_unpack hl2 hk2 hc2 hs2
  rw [Nat.mod_eq_of_lt hb1, Nat.mod_eq_of_lt hb2] at hVal
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hl1', ← hl2', hVal]
  · rw [← hk1', ← hk2', hVal]
  · rw [← hc1', ← hc2', hVal]
  · rw [← hs1', ← hs2', hVal]

/-- Secret chain start `PRF_wots(skSeed, pkSeed, layer, treeIdx, kpIdx, chainIdx)` (`sig.rs:124`). -/
def wotsSecretStart (skSeed pkSeed : Digest4) (layer treeIdx kpIdx chainIdx : Nat) : Digest4 :=
  let tweak : Digest4 :=
    ⟨domainPrfWots,
     packWotsAddrLimb layer kpIdx chainIdx 0,
     Goldilocks.ofNat (treeIdx % (2 ^ 32)),
     Goldilocks.ofNat ((treeIdx / (2 ^ 32)) % (2 ^ 32))⟩
  poseidon2Compress12FF skSeed pkSeed tweak

/-- Domain-separated WOTS+C chain step hash (`wots_step_hash_injective` in `sig.rs:295`). -/
def wotsStepHash (pkSeed cur : Digest4) (layer treeIdx kpIdx chainIdx stepIdx : Nat) : Digest4 :=
  let tweak : Digest4 :=
    ⟨domainWotsStep,
     packWotsAddrLimb layer kpIdx chainIdx stepIdx,
     Goldilocks.ofNat (treeIdx % (2 ^ 32)),
     Goldilocks.ofNat ((treeIdx / (2 ^ 32)) % (2 ^ 32))⟩
  poseidon2Compress12FF cur pkSeed tweak

private def natIterAt {σ : Type} (step : Nat → σ → σ) : Nat → Nat → σ → σ
  | 0, _, s => s
  | n + 1, idx, s => natIterAt step n (idx + 1) (step idx s)

private theorem natIterAt_add {σ : Type} (step : Nat → σ → σ) :
    ∀ (a b idx : Nat) (s : σ),
      natIterAt step (a + b) idx s = natIterAt step b (idx + a) (natIterAt step a idx s)
  | 0, b, idx, s => by
    rw [Nat.zero_add, Nat.add_zero]
    rfl
  | a + 1, b, idx, s => by
    rw [Nat.succ_add]
    dsimp only [natIterAt]
    rw [natIterAt_add step a b (idx + 1)]
    have hShift : idx + 1 + a = idx + (a + 1) := by omega
    rw [hShift]

/-- Iterated WOTS+C forward chain walk starting at `startStep` for `numSteps` applications. -/
def wotsChainWalk (pkSeed : Digest4) (layer treeIdx kpIdx chainIdx startStep steps : Nat)
    (cur : Digest4) : Digest4 :=
  natIterAt (fun stp v => wotsStepHash pkSeed v layer treeIdx kpIdx chainIdx stp) steps startStep cur

theorem wotsChainWalk_add (pkSeed : Digest4) (layer treeIdx kpIdx chainIdx : Nat)
    (a b startStep : Nat) (cur : Digest4) :
    wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx startStep (a + b) cur =
      wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx (startStep + a) b
        (wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx startStep a cur) :=
  natIterAt_add _ a b startStep cur

def absorbPairsPoly {D S : Type} (perm1 : S → D → S) (perm2 : S → D → D → S) :
    List D → S → Option D → S
  | [], st, none => st
  | [], st, some e0 => perm1 st e0
  | e :: rest, st, none => absorbPairsPoly perm1 perm2 rest st (some e)
  | e1 :: rest, st, some e0 => absorbPairsPoly perm1 perm2 rest (perm2 st e0 e1) none

private def absorbDigest4Pairs (st : Poseidon2State12) (xs : List Digest4) : Poseidon2State12 :=
  absorbPairsPoly
    (fun s e0 => poseidon2Perm12 ⟨lane4Add s.b0 e0, s.b1, s.b2⟩)
    (fun s e0 e1 => poseidon2Perm12 ⟨lane4Add s.b0 e0, lane4Add s.b1 e1, s.b2⟩)
    xs st none

/-- 256-bit-capacity `Poseidon2` sponge compressing WOTS+C endpoints (`compress_wots_endpoints_sponge`, `sig.rs:318`). -/
def compressWotsEndpointsSponge (pkSeed : Digest4) (layer treeIdx kpIdx : Nat)
    (endpoints : List Digest4) : Digest4 :=
  let layerKp := Goldilocks.ofNat ((layer % (2 ^ 32)) * (2 ^ 32) + (kpIdx % (2 ^ 32)))
  let initSt : Poseidon2State12 :=
    ⟨pkSeed,
     ⟨layerKp,
      Goldilocks.ofNat (treeIdx % (2 ^ 32)),
      Goldilocks.ofNat ((treeIdx / (2 ^ 32)) % (2 ^ 32)),
      Goldilocks.ofNat endpoints.length⟩,
     ⟨domainWotsPk, Goldilocks.zero, Goldilocks.zero, poseidon2IvTag⟩⟩
  let st0 := poseidon2Perm12 initSt
  let stAbs := absorbDigest4Pairs st0 endpoints
  let stPad : Poseidon2State12 :=
    ⟨⟨Goldilocks.add stAbs.b0.x0 Goldilocks.one, stAbs.b0.x1, stAbs.b0.x2, stAbs.b0.x3⟩,
     stAbs.b1, stAbs.b2⟩
  (poseidon2Perm12 stPad).b0

/-- 2-block full-`pkSeed` binary Merkle node sponge (`merkle_node_hash` in `sig.rs:358`). -/
def merkleNodeHash (domainTag : Goldilocks) (pkSeed : Digest4)
    (layer treeIdx level nodeIdx : Nat) (left right : Digest4) : Digest4 :=
  let meta0 := Goldilocks.ofNat
    ((layer % 65536) * (2 ^ 48) + (level % 65536) * (2 ^ 32) + (nodeIdx % (2 ^ 32)))
  let st0 := poseidon2Perm12
    ⟨pkSeed,
     left,
     ⟨domainTag,
      meta0,
      Goldilocks.ofNat (treeIdx % (2 ^ 32)),
      Goldilocks.ofNat ((treeIdx / (2 ^ 32)) % (2 ^ 32))⟩⟩
  let b0' := lane4Add st0.b0 right
  let b1' : Digest4 :=
    ⟨Goldilocks.add st0.b1.x0 Goldilocks.one,
     Goldilocks.add st0.b1.x1 poseidon2IvTag,
     st0.b1.x2,
     st0.b1.x3⟩
  (poseidon2Perm12 ⟨b0', b1', st0.b2⟩).b0

private def merkleWalkPoly {D : Type} (nodeHash : Nat → Nat → D → D → D) :
    List D → Nat → Nat → D → D
  | [], _, _, cur => cur
  | sib :: rest, lvl, idx, cur =>
    let parentIdx := idx / 2
    let parent :=
      if idx % 2 == 0 then nodeHash lvl parentIdx cur sib
      else nodeHash lvl parentIdx sib cur
    merkleWalkPoly nodeHash rest (lvl + 1) parentIdx parent

private def buildMerkleNodePoly {D : Type} (nodeHash : Nat → Nat → D → D → D) :
    Nat → (Nat → D) → Nat → Nat → D
  | 0, leafFn, _, nodeIdx => leafFn nodeIdx
  | h + 1, leafFn, lvl, nodeIdx =>
    let left := buildMerkleNodePoly nodeHash h leafFn lvl (2 * nodeIdx)
    let right := buildMerkleNodePoly nodeHash h leafFn lvl (2 * nodeIdx + 1)
    nodeHash (lvl + h) nodeIdx left right

private def buildMerkleAuthPathPoly {D : Type} (nodeHash : Nat → Nat → D → D → D) :
    Nat → (Nat → D) → Nat → Nat → List D
  | 0, _, _, _ => []
  | h + 1, leafFn, lvl, idx =>
    let sibIdx := if idx % 2 == 0 then idx + 1 else idx - 1
    let sib := leafFn sibIdx
    let parentLeafFn := fun pIdx => nodeHash lvl pIdx (leafFn (2 * pIdx)) (leafFn (2 * pIdx + 1))
    sib :: buildMerkleAuthPathPoly nodeHash h parentLeafFn (lvl + 1) (idx / 2)

private theorem buildMerkleNodePoly_shift {D : Type} (nodeHash : Nat → Nat → D → D → D) :
    ∀ (h : Nat) (leafFn : Nat → D) (lvl nodeIdx : Nat),
      buildMerkleNodePoly nodeHash h
        (fun pIdx => nodeHash lvl pIdx (leafFn (2 * pIdx)) (leafFn (2 * pIdx + 1)))
        (lvl + 1) nodeIdx =
      buildMerkleNodePoly nodeHash (h + 1) leafFn lvl nodeIdx
  | 0, _, _, _ => rfl
  | h + 1, leafFn, lvl, nodeIdx => by
    let pFn := fun pIdx => nodeHash lvl pIdx (leafFn (2 * pIdx)) (leafFn (2 * pIdx + 1))
    change nodeHash ((lvl + 1) + h) nodeIdx
        (buildMerkleNodePoly nodeHash h pFn (lvl + 1) (2 * nodeIdx))
        (buildMerkleNodePoly nodeHash h pFn (lvl + 1) (2 * nodeIdx + 1)) =
      nodeHash (lvl + (h + 1)) nodeIdx
        (buildMerkleNodePoly nodeHash (h + 1) leafFn lvl (2 * nodeIdx))
        (buildMerkleNodePoly nodeHash (h + 1) leafFn lvl (2 * nodeIdx + 1))
    rw [buildMerkleNodePoly_shift nodeHash h leafFn lvl (2 * nodeIdx),
        buildMerkleNodePoly_shift nodeHash h leafFn lvl (2 * nodeIdx + 1)]
    have hLvl : (lvl + 1) + h = lvl + (h + 1) := by omega
    rw [hLvl]

private theorem buildMerkleAuthPathPoly_length {D : Type} (nodeHash : Nat → Nat → D → D → D) :
    ∀ (h : Nat) (leafFn : Nat → D) (lvl idx : Nat),
      (buildMerkleAuthPathPoly nodeHash h leafFn lvl idx).length = h
  | 0, _, _, _ => rfl
  | h + 1, leafFn, lvl, idx => by
    dsimp only [buildMerkleAuthPathPoly]
    rw [List.length_cons, buildMerkleAuthPathPoly_length nodeHash h]

private theorem merkleWalkPoly_buildMerkleAuthPathPoly {D : Type} (nodeHash : Nat → Nat → D → D → D) :
    ∀ (h : Nat) (leafFn : Nat → D) (lvl idx : Nat),
      idx < 2 ^ h →
      merkleWalkPoly nodeHash (buildMerkleAuthPathPoly nodeHash h leafFn lvl idx) lvl idx (leafFn idx) =
        buildMerkleNodePoly nodeHash h leafFn lvl 0
  | 0, _, _, idx, hLt => by
    have h0 : idx = 0 := by simp at hLt; omega
    subst h0
    rfl
  | h + 1, leafFn, lvl, idx, hLt => by
    dsimp only [buildMerkleAuthPathPoly, merkleWalkPoly]
    let parentLeafFn := fun pIdx => nodeHash lvl pIdx (leafFn (2 * pIdx)) (leafFn (2 * pIdx + 1))
    have hDivLt : idx / 2 < 2 ^ h := by
      rw [Nat.pow_succ] at hLt
      omega
    have hParEq :
        (if idx % 2 == 0 then
          nodeHash lvl (idx / 2) (leafFn idx) (leafFn (if idx % 2 == 0 then idx + 1 else idx - 1))
        else
          nodeHash lvl (idx / 2) (leafFn (if idx % 2 == 0 then idx + 1 else idx - 1)) (leafFn idx)) =
        parentLeafFn (idx / 2) := by
      cases hPar : (idx % 2 == 0)
      · have hOdd : idx % 2 = 1 := by
          cases hRem : idx % 2 with
          | zero => simp [hRem] at hPar
          | succ m => omega
        have hL : idx - 1 = 2 * (idx / 2) := by omega
        have hR : idx = 2 * (idx / 2) + 1 := by omega
        simp only [Bool.false_eq_true, ↓reduceIte]
        dsimp only [parentLeafFn]
        rw [hL, ← hR]
      · have hEven : idx % 2 = 0 := eq_of_beq hPar
        have hL : idx = 2 * (idx / 2) := by omega
        have hR : idx + 1 = 2 * (idx / 2) + 1 := by omega
        simp only [↓reduceIte]
        dsimp only [parentLeafFn]
        rw [hR]
        conv => lhs; arg 3; rw [hL]
    rw [hParEq,
        merkleWalkPoly_buildMerkleAuthPathPoly nodeHash h parentLeafFn (lvl + 1) (idx / 2) hDivLt,
        buildMerkleNodePoly_shift nodeHash h leafFn lvl 0]

private structure PolyMerkleCollision {D : Type} (nodeHash : Nat → Nat → D → D → D) where
  level    : Nat
  nodeIdx  : Nat
  left1    : D
  right1   : D
  left2    : D
  right2   : D
  neInputs : (left1, right1) ≠ (left2, right2)
  hashEq   : nodeHash level nodeIdx left1 right1 = nodeHash level nodeIdx left2 right2

private def extractMerkleLeafPoly {D : Type} [DecidableEq D] (nodeHash : Nat → Nat → D → D → D) :
    ∀ (h : Nat) (leafFn : Nat → D) (lvl idx : Nat) (forgedLeaf : D) (path : List D),
      path.length = h →
      idx < 2 ^ h →
      merkleWalkPoly nodeHash path lvl idx forgedLeaf = buildMerkleNodePoly nodeHash h leafFn lvl 0 →
      PSum (forgedLeaf = leafFn idx) (PolyMerkleCollision nodeHash)
  | 0, leafFn, _, idx, forgedLeaf, [], _, hLt, hRoot =>
    have hIdx0 : idx = 0 := by simp at hLt; omega
    .inl (by subst hIdx0; exact hRoot)
  | h + 1, leafFn, lvl, idx, forgedLeaf, sib :: rest, hCons, hLt, hRoot =>
    let parentLeafFn := fun pIdx => nodeHash lvl pIdx (leafFn (2 * pIdx)) (leafFn (2 * pIdx + 1))
    let pIdx := idx / 2
    let l1 := if idx % 2 == 0 then forgedLeaf else sib
    let r1 := if idx % 2 == 0 then sib else forgedLeaf
    let forgedParent := nodeHash lvl pIdx l1 r1
    have hStepWalk :
        merkleWalkPoly nodeHash rest (lvl + 1) pIdx forgedParent =
          buildMerkleNodePoly nodeHash h parentLeafFn (lvl + 1) 0 := by
      have hParEq :
          (if idx % 2 == 0 then nodeHash lvl pIdx forgedLeaf sib
           else nodeHash lvl pIdx sib forgedLeaf) = forgedParent := by
        dsimp only [forgedParent, l1, r1]
        cases (idx % 2 == 0) <;> rfl
      rw [buildMerkleNodePoly_shift, ← hRoot]
      dsimp only [merkleWalkPoly]
      change merkleWalkPoly nodeHash rest (lvl + 1) pIdx forgedParent =
        merkleWalkPoly nodeHash rest (lvl + 1) pIdx
          (if idx % 2 == 0 then nodeHash lvl pIdx forgedLeaf sib
           else nodeHash lvl pIdx sib forgedLeaf)
      rw [hParEq]
    have hDivLt : pIdx < 2 ^ h := by
      dsimp only [pIdx]
      rw [Nat.pow_succ] at hLt
      omega
    match extractMerkleLeafPoly nodeHash h parentLeafFn (lvl + 1) pIdx
            forgedParent rest (Nat.succ.inj hCons) hDivLt hStepWalk with
    | .inr col => .inr col
    | .inl hParentEq =>
      if hPair : (l1, r1) = (leafFn (2 * pIdx), leafFn (2 * pIdx + 1)) then
        .inl (by
          have hFst := congrArg Prod.fst hPair
          have hSnd := congrArg Prod.snd hPair
          dsimp only [l1, r1, pIdx] at hFst hSnd
          cases hEven : (idx % 2 == 0)
          · simp only [hEven, Bool.false_eq_true, ↓reduceIte] at hSnd
            have hOddEq : 2 * (idx / 2) + 1 = idx := by
              cases hRem : idx % 2 with
              | zero => simp [hRem] at hEven
              | succ m => omega
            rw [hOddEq] at hSnd
            exact hSnd
          · simp only [hEven, ↓reduceIte] at hFst
            have hEvenEq : 2 * (idx / 2) = idx := by
              have hr : idx % 2 = 0 := eq_of_beq hEven
              omega
            rw [hEvenEq] at hFst
            exact hFst)
      else
        .inr {
          level    := lvl
          nodeIdx  := pIdx
          left1    := l1
          right1   := r1
          left2    := leafFn (2 * pIdx)
          right2   := leafFn (2 * pIdx + 1)
          neInputs := hPair
          hashEq   := hParentEq
        }

/-- Node addressing of an XMSS subtree (`verify_individual_signature`): at every level the
    `node_idx` limb is the in-tree parent index. -/
def xmssNodeAddr : Nat → Nat → Nat := fun _ parentIdx => parentIdx

/-- Node addressing of FORS tree `j` under key pair `kpIdx` (`recover_fors_pk`): at the 1-based
    `level = lvl + 1` the `node_idx` limb is
    `(kp_idx << 16) | ((j << (FORS_HEIGHT - 1 - lvl)) + parent_idx)`. -/
def forsNodeAddr (forsHeight kpIdx j : Nat) : Nat → Nat → Nat :=
  fun level parentIdx => (kpIdx <<< 16) + ((j <<< (forsHeight - level)) + parentIdx)

/-- The 2-block node hash of one tree under the node addressing `addr : level → parentIdx → node_idx`. -/
def merkleAddrNodeHash (domainTag : Goldilocks) (pkSeed : Digest4) (layer treeIdx : Nat)
    (addr : Nat → Nat → Nat) : Nat → Nat → Digest4 → Digest4 → Digest4 :=
  fun level parentIdx => merkleNodeHash domainTag pkSeed layer treeIdx level (addr level parentIdx)

/-- Walk an authentication path from `(leafIdx, curNode)` up to the subtree root. -/
def merkleWalkRoot (domainTag : Goldilocks) (pkSeed : Digest4) (layer treeIdx : Nat)
    (addr : Nat → Nat → Nat) (lvl idx : Nat)
    (cur : Digest4) (path : List Digest4) : Digest4 :=
  merkleWalkPoly (merkleAddrNodeHash domainTag pkSeed layer treeIdx addr) path lvl idx cur

/-- Deterministic binary Merkle subtree root at level `lvl` and node offset `nodeIdx` of remaining height `h`. -/
def buildMerkleNodeAt (domainTag : Goldilocks) (pkSeed : Digest4) (layer treeIdx : Nat)
    (addr : Nat → Nat → Nat) (leafFn : Nat → Digest4) (h lvl nodeIdx : Nat) : Digest4 :=
  buildMerkleNodePoly (merkleAddrNodeHash domainTag pkSeed layer treeIdx addr) h leafFn lvl nodeIdx

/-- Constructive sibling authentication path for `idx < 2^h` from level `lvl`. -/
def buildMerkleAuthPathAt (domainTag : Goldilocks) (pkSeed : Digest4) (layer treeIdx : Nat)
    (addr : Nat → Nat → Nat) (leafFn : Nat → Digest4) (h lvl idx : Nat) : List Digest4 :=
  buildMerkleAuthPathPoly (merkleAddrNodeHash domainTag pkSeed layer treeIdx addr) h leafFn lvl idx

theorem buildMerkleAuthPathAt_length (domainTag : Goldilocks) (pkSeed : Digest4)
    (layer treeIdx : Nat) (addr : Nat → Nat → Nat) (leafFn : Nat → Digest4) (h lvl idx : Nat) :
    (buildMerkleAuthPathAt domainTag pkSeed layer treeIdx addr leafFn h lvl idx).length = h :=
  buildMerkleAuthPathPoly_length _ h leafFn lvl idx

theorem merkleWalkRoot_buildMerkleAuthPathAt (domainTag : Goldilocks) (pkSeed : Digest4)
    (layer treeIdx : Nat) (addr : Nat → Nat → Nat) (h : Nat) (leafFn : Nat → Digest4)
    (lvl idx : Nat) (hLt : idx < 2 ^ h) :
    merkleWalkRoot domainTag pkSeed layer treeIdx addr lvl idx (leafFn idx)
      (buildMerkleAuthPathAt domainTag pkSeed layer treeIdx addr leafFn h lvl idx) =
    buildMerkleNodeAt domainTag pkSeed layer treeIdx addr leafFn h lvl 0 :=
  merkleWalkPoly_buildMerkleAuthPathPoly _ h leafFn lvl idx hLt

/-- Concrete witness of a 2-block `merkleNodeHash` collision under `pkSeed`. -/
structure MerkleNodeCollisionWitness (pkSeed : Digest4) where
  domainTag : Goldilocks
  layer     : Nat
  treeIdx   : Nat
  level     : Nat
  nodeIdx   : Nat
  left1     : Digest4
  right1    : Digest4
  left2     : Digest4
  right2    : Digest4
  neInputs  : (left1, right1) ≠ (left2, right2)
  hashEq    : merkleNodeHash domainTag pkSeed layer treeIdx level nodeIdx left1 right1 =
              merkleNodeHash domainTag pkSeed layer treeIdx level nodeIdx left2 right2

/-- Constructive Merkle path extractor: if a walked path from `forgedLeaf`
    equals the honest subtree root `buildMerkleNodeAt ... h lvl 0`, either `forgedLeaf = leafFn idx`
    or we extract an explicit `MerkleNodeCollisionWitness pkSeed`! -/
def extractMerkleLeafOrCollision (domainTag : Goldilocks) (pkSeed : Digest4)
    (layer treeIdx : Nat) (addr : Nat → Nat → Nat) (h : Nat) (leafFn : Nat → Digest4) (lvl idx : Nat)
    (forgedLeaf : Digest4) (path : List Digest4)
    (hLen : path.length = h) (hLt : idx < 2 ^ h)
    (hRoot : merkleWalkRoot domainTag pkSeed layer treeIdx addr lvl idx forgedLeaf path =
               buildMerkleNodeAt domainTag pkSeed layer treeIdx addr leafFn h lvl 0) :
    PSum (forgedLeaf = leafFn idx) (MerkleNodeCollisionWitness pkSeed) :=
  match extractMerkleLeafPoly (merkleAddrNodeHash domainTag pkSeed layer treeIdx addr)
          h leafFn lvl idx forgedLeaf path hLen hLt hRoot with
  | .inl hEq => .inl hEq
  | .inr col => .inr {
      domainTag := domainTag
      layer     := layer
      treeIdx   := treeIdx
      level     := col.level
      nodeIdx   := addr col.level col.nodeIdx
      left1     := col.left1
      right1    := col.right1
      left2     := col.left2
      right2    := col.right2
      neInputs  := col.neInputs
      hashEq    := col.hashEq
    }

/-! ### Base-4 Digit Extraction, Anti-Monotone Target Sum, and Message Representative `mu` -/

/-- Sum of a list of natural numbers. -/
def listNatSum : List Nat → Nat
  | [] => 0
  | x :: xs => x + listNatSum xs

/-- Extract `count` base-4 digits (`0..3`), least-significant digit first (`sig.rs:479`). -/
def extractLimbBase4Digits : Nat → Nat → List Nat
  | 0, _ => []
  | count + 1, v => (v % 4) :: extractLimbBase4Digits count (v / 4)

/-- Reconstruct an integer from base-4 digits (`d_0 + 4 * d_1 + ...`). -/
def evalBase4Digits : List Nat → Nat
  | [] => 0
  | d :: ds => d + 4 * evalBase4Digits ds

theorem extractLimbBase4Digits_length :
    ∀ (count v : Nat), (extractLimbBase4Digits count v).length = count
  | 0, _ => rfl
  | count + 1, v => by
    simp [extractLimbBase4Digits, extractLimbBase4Digits_length count]

theorem extractLimbBase4Digits_all_lt_four :
    ∀ (count v d : Nat), d ∈ extractLimbBase4Digits count v → d < 4
  | 0, _, _, h => by cases h
  | count + 1, v, d, h => by
    rcases List.mem_cons.mp h with rfl | hTail
    · omega
    · exact extractLimbBase4Digits_all_lt_four count (v / 4) d hTail

theorem evalBase4Digits_extractLimbBase4Digits :
    ∀ (count v : Nat),
      evalBase4Digits (extractLimbBase4Digits count v) + (4 ^ count) * (v / (4 ^ count)) = v
  | 0, v => by simp [extractLimbBase4Digits, evalBase4Digits]
  | count + 1, v => by
    have ih := evalBase4Digits_extractLimbBase4Digits count (v / 4)
    have hDiv : (v / 4) / (4 ^ count) = v / (4 ^ (count + 1)) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
    have hPow : 4 ^ (count + 1) = 4 * 4 ^ count := by rw [Nat.pow_succ, Nat.mul_comm]
    calc evalBase4Digits (extractLimbBase4Digits (count + 1) v) + (4 ^ (count + 1)) * (v / (4 ^ (count + 1)))
      _ = v % 4 + 4 * evalBase4Digits (extractLimbBase4Digits count (v / 4)) +
            4 * ((4 ^ count) * ((v / 4) / (4 ^ count))) := by
          simp only [extractLimbBase4Digits, evalBase4Digits]
          rw [← hDiv, hPow, Nat.mul_assoc]
      _ = v % 4 + 4 * (evalBase4Digits (extractLimbBase4Digits count (v / 4)) +
            (4 ^ count) * ((v / 4) / (4 ^ count))) := by
          rw [Nat.left_distrib, Nat.add_assoc]
      _ = v % 4 + 4 * (v / 4) := by rw [ih]
      _ = v := Nat.mod_add_div v 4

/-- Wrap-around-free `< 2^63` check on all 5 limbs of `Digest5` (`sig.rs:471`). -/
def checkDigest5Limbs63 (d : Digest5) : Bool :=
  (d.limb0.val < 2 ^ 63) &&
  (d.limb1.val < 2 ^ 63) &&
  (d.limb2.val < 2 ^ 63) &&
  (d.limb3.val < 2 ^ 63) &&
  (d.limb4.val < 2 ^ 63)

/-- Checked extraction of `geom.wotsChains` base-4 digits (`128` at deployed profiles, `sig.rs:470`). -/
def extractWotsDigitsChecked (geom : AggSigGeometry) (d : Digest5) : Option (List Nat) :=
  if checkDigest5Limbs63 d then
    let all128 :=
      extractLimbBase4Digits 31 d.limb0.val ++
      extractLimbBase4Digits 31 d.limb1.val ++
      extractLimbBase4Digits 31 d.limb2.val ++
      extractLimbBase4Digits 31 d.limb3.val ++
      extractLimbBase4Digits 4 d.limb4.val
    some (all128.take geom.wotsChains)
  else
    none

private theorem length_extractAll128 (d : Digest5) :
    (extractLimbBase4Digits 31 d.limb0.val ++
     extractLimbBase4Digits 31 d.limb1.val ++
     extractLimbBase4Digits 31 d.limb2.val ++
     extractLimbBase4Digits 31 d.limb3.val ++
     extractLimbBase4Digits 4 d.limb4.val).length = 128 := by
  simp [extractLimbBase4Digits_length]

theorem extractWotsDigitsChecked_spec {geom : AggSigGeometry} {d : Digest5} {ds : List Nat}
    (hLenLe : geom.wotsChains ≤ 128)
    (hExt : extractWotsDigitsChecked geom d = some ds) :
    ds.length = geom.wotsChains ∧ (∀ x ∈ ds, x < 4) := by
  unfold extractWotsDigitsChecked at hExt
  cases hChk : checkDigest5Limbs63 d
  · simp [hChk] at hExt
  · simp only [hChk, ↓reduceIte, Option.some.injEq] at hExt
    subst hExt
    refine ⟨?_, ?_⟩
    · rw [List.length_take, length_extractAll128]
      omega
    · intro x hx
      have hMem := List.mem_of_mem_take hx
      simp only [List.mem_append] at hMem
      rcases hMem with (((h0 | h1) | h2) | h3) | h4
      · exact extractLimbBase4Digits_all_lt_four 31 _ x h0
      · exact extractLimbBase4Digits_all_lt_four 31 _ x h1
      · exact extractLimbBase4Digits_all_lt_four 31 _ x h2
      · exact extractLimbBase4Digits_all_lt_four 31 _ x h3
      · exact extractLimbBase4Digits_all_lt_four 4 _ x h4

structure SmallerDigitWitness (honest forged : List Nat) where
  idx      : Nat
  hHonest  : idx < honest.length
  hForged  : idx < forged.length
  strictLt : forged[idx]'hForged < honest[idx]'hHonest

/-- Constructive anti-monotonicity: if `forged` and `honest` have equal length,
    `listNatSum forged ≤ listNatSum honest`, and `forged ≠ honest`, locates an explicit chain index `c`
    where **`forged[c] < honest[c]`**! -/
def findSmallerDigitIdx :
    ∀ (honest forged : List Nat),
      honest.length = forged.length →
      listNatSum forged ≤ listNatSum honest →
      forged ≠ honest →
      SmallerDigitWitness honest forged
  | [], [], _, _, hNe => False.elim (hNe rfl)
  | [], _ :: _, hLen, _, _ => False.elim (Nat.succ_ne_zero _ hLen.symm)
  | _ :: _, [], hLen, _, _ => False.elim (Nat.succ_ne_zero _ hLen)
  | xH :: xsH, xF :: xsF, hLen, hSum, hNe =>
    if hLt : xF < xH then
      ⟨0, Nat.zero_lt_succ _, Nat.zero_lt_succ _, hLt⟩
    else if hEq : xF = xH then
      have hSubSum : listNatSum xsF ≤ listNatSum xsH := by
        simp only [listNatSum] at hSum
        omega
      have hTailNe : xsF ≠ xsH := fun hT => hNe (by rw [hEq, hT])
      let w := findSmallerDigitIdx xsH xsF (Nat.succ.inj hLen) hSubSum hTailNe
      ⟨w.idx + 1, Nat.succ_lt_succ w.hHonest, Nat.succ_lt_succ w.hForged, w.strictLt⟩
    else
      have hStrictTail : listNatSum xsF < listNatSum xsH := by
        simp only [listNatSum] at hSum
        omega
      have hTailNe : xsF ≠ xsH := fun hT => by rw [hT] at hStrictTail; exact Nat.lt_irrefl _ hStrictTail
      let w := findSmallerDigitIdx xsH xsF (Nat.succ.inj hLen) (Nat.le_of_lt hStrictTail) hTailNe
      ⟨w.idx + 1, Nat.succ_lt_succ w.hHonest, Nat.succ_lt_succ w.hForged, w.strictLt⟩

structure DigitLtThreeWitness (digits : List Nat) where
  idx : Nat
  hIn : idx < digits.length
  lt3 : digits[idx]'hIn < 3

/-- Constructive search for a chain index with `digits[c] < 3` whenever `listNatSum digits < 3 * digits.length`. -/
def findDigitLtThreeIdx :
    ∀ (digits : List Nat),
      listNatSum digits < 3 * digits.length →
      DigitLtThreeWitness digits
  | [], hSum => False.elim (by simp [listNatSum] at hSum)
  | d :: ds, hSum =>
    if hLt : d < 3 then
      ⟨0, Nat.zero_lt_succ _, hLt⟩
    else
      have hTail : listNatSum ds < 3 * ds.length := by
        simp only [listNatSum, List.length_cons] at hSum
        omega
      let w := findDigitLtThreeIdx ds hTail
      ⟨w.idx + 1, Nat.succ_lt_succ w.hIn, w.lt3⟩

/-- Pack 32 bytes losslessly into 5 canonical `< 2^56` / `< 2^32` Goldilocks limbs (`bytes32_to_limbs56`). -/
def bytes32ToDigest5 (bs : List UInt8) : Digest5 :=
  let b := (bs ++ List.replicate (32 - bs.length) (0 : UInt8)).take 32
  let l0 := ofBE (b.take 7)
  let l1 := ofBE ((b.drop 7).take 7)
  let l2 := ofBE ((b.drop 14).take 7)
  let l3 := ofBE ((b.drop 21).take 7)
  let l4 := ofBE ((b.drop 28).take 4)
  have h7 : ∀ xs : List UInt8, xs.length ≤ 7 → ofBE xs < goldilocksPrime := fun xs hx => by
    have hLt := ofBE_lt xs
    have hPow : 256 ^ xs.length ≤ 256 ^ 7 := Nat.pow_le_pow_right (by decide) hx
    exact Nat.lt_of_lt_of_le hLt (Nat.le_trans hPow (by decide))
  have h4 : ∀ xs : List UInt8, xs.length ≤ 4 → ofBE xs < goldilocksPrime := fun xs hx => by
    have hLt := ofBE_lt xs
    have hPow : 256 ^ xs.length ≤ 256 ^ 4 := Nat.pow_le_pow_right (by decide) hx
    exact Nat.lt_of_lt_of_le hLt (Nat.le_trans hPow (by decide))
  { limb0 := ⟨l0, h7 _ (List.length_take_le _ _)⟩
    limb1 := ⟨l1, h7 _ (List.length_take_le _ _)⟩
    limb2 := ⟨l2, h7 _ (List.length_take_le _ _)⟩
    limb3 := ⟨l3, h7 _ (List.length_take_le _ _)⟩
    limb4 := ⟨l4, h4 _ (List.length_take_le _ _)⟩ }

/-- Canonical byte serialization of `AggValidatorPk` (`65` bytes). -/
def encodeAggValidatorPkBytes (pk : AggValidatorPk) : List UInt8 :=
  let profByte : UInt8 := match pk.profile with
    | .xmssPoseidon2 => 1
    | .corduroyPoseidon2 => 2
  profByte ::
    be 8 pk.pkSeed.x0.val ++ be 8 pk.pkSeed.x1.val ++ be 8 pk.pkSeed.x2.val ++ be 8 pk.pkSeed.x3.val ++
    be 8 pk.pkRoot.x0.val ++ be 8 pk.pkRoot.x1.val ++ be 8 pk.pkRoot.x2.val ++ be 8 pk.pkRoot.x3.val

/-- ASCII byte tag `"QSAG.MU/v2"` (`0x51 0x53 0x41 0x47 0x2e 0x4d 0x55 0x2f 0x76 0x32`). -/
def qsagMuV2TagBytes : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2e, 0x4d, 0x55, 0x2f, 0x76, 0x32]

/-- Domain-framed 5-limb message representative `mu` (`compute_message_mu` in `sig.rs:260`). -/
def computeMessageMu (pk : AggValidatorPk) (msg : List UInt8) : Digest5 :=
  let framed := encodeMultiFrame [qsagMuV2TagBytes, encodeAggValidatorPkBytes pk, msg]
  bytes32ToDigest5 (poseidon2Hash32 framed)

/-- Stateful layer-0 randomized message hash `compute_hmsg_stateful` (`sig.rs:396`). -/
def computeHmsgStateful (pk : AggValidatorPk) (rRand : Digest4) (mu : Digest5)
    (kpIdx tswCtr : Nat) : Digest5 :=
  let kpCtr := Goldilocks.ofNat ((kpIdx % (2 ^ 32)) * (2 ^ 32) + (tswCtr % (2 ^ 32)))
  let st0 := poseidon2Perm12
    ⟨pk.pkSeed,
     pk.pkRoot,
     ⟨domainHMsgStateful, kpCtr, mu.limb4, poseidon2IvTag⟩⟩
  let muLow : Digest4 := ⟨mu.limb0, mu.limb1, mu.limb2, mu.limb3⟩
  let st1 := poseidon2Perm12 ⟨lane4Add st0.b0 rRand, lane4Add st0.b1 muLow, st0.b2⟩
  let st2 := poseidon2Perm12
    ⟨⟨Goldilocks.add st1.b0.x0 Goldilocks.one, st1.b0.x1, st1.b0.x2, st1.b0.x3⟩,
     st1.b1, st1.b2⟩
  { limb0 := st2.b0.x0
    limb1 := st2.b0.x1
    limb2 := st2.b0.x2
    limb3 := st2.b0.x3
    limb4 := st2.b1.x0 }

/-- Deterministic `rRand`-free & `mu`-free tree `H_msg` (`compute_hmsg_det_tree` in `sig.rs:433`). -/
def computeHmsgDetTree (pk : AggValidatorPk) (layer treeIdx kpIdx tswCtr : Nat)
    (childOrForsRoot : Digest4) : Digest5 :=
  let layerKp := Goldilocks.ofNat ((layer % (2 ^ 32)) * (2 ^ 32) + (kpIdx % (2 ^ 32)))
  let st0 := poseidon2Perm12
    ⟨pk.pkSeed,
     pk.pkRoot,
     ⟨domainHMsgDetTree,
      layerKp,
      Goldilocks.ofNat (treeIdx % (2 ^ 32)),
      Goldilocks.ofNat ((treeIdx / (2 ^ 32)) % (2 ^ 32))⟩⟩
  let b0' := lane4Add st0.b0 childOrForsRoot
  let b1' : Digest4 :=
    ⟨Goldilocks.add st0.b1.x0 (Goldilocks.ofNat (tswCtr % (2 ^ 32))),
     Goldilocks.add st0.b1.x1 Goldilocks.one,
     st0.b1.x2,
     st0.b1.x3⟩
  let st1 := poseidon2Perm12 ⟨b0', b1', st0.b2⟩
  { limb0 := st1.b0.x0
    limb1 := st1.b0.x1
    limb2 := st1.b0.x2
    limb3 := st1.b0.x3
    limb4 := st1.b1.x0 }

/-! ### FORS & Hypertree Signing, Verification, Completeness, and Constructive Soundness -/

/-- FORS tree opening (`secretVal` + sibling authentication path of height `forsHeight`). -/
structure AggForsTreeOpening where
  secretVal : Digest4
  authPath  : List Digest4
  deriving DecidableEq, Repr

/-- Single hypertree layer signature (`tswCtr` + `wotsChains` + `merklePath`). -/
structure WotsLayerSig where
  tswCtr     : Nat
  wotsChains : List Digest4
  merklePath : List Digest4
  deriving DecidableEq, Repr

/-- Field-native validator signature matching `ValidatorSignature` in `crates/qsag-agg/src/sig.rs`. -/
structure AggNativeSignature where
  profile         : AggSigProfile
  rRand           : Digest4
  statefulLeafIdx : Nat
  forsOpenings    : List AggForsTreeOpening
  layers          : List WotsLayerSig
  deriving DecidableEq, Repr

/-- Key-pair index of the bottom hypertree leaf that owns the FORS instance
    (`kp_idx = leaf_global_idx & ((1 << CORDUROY_SUBTREE_HEIGHT) - 1)` in `recover_fors_pk`). -/
def forsKpIdx (geom : AggSigGeometry) (leafGlobalIdx : Nat) : Nat :=
  leafGlobalIdx % 2 ^ geom.subtreeHeight

/-- Bottom-layer hypertree tree index of the FORS instance
    (`tree_idx = leaf_global_idx >> CORDUROY_SUBTREE_HEIGHT` in `recover_fors_pk`). -/
def forsHyperTreeIdx (geom : AggSigGeometry) (leafGlobalIdx : Nat) : Nat :=
  leafGlobalIdx / 2 ^ geom.subtreeHeight

/-- In the deployed geometry the split is `(leaf_global_idx & 0xF, leaf_global_idx >> 4)`. -/
theorem corduroy_fors_addr_split (leafGlobalIdx : Nat) :
    forsKpIdx corduroyPoseidon2Geom leafGlobalIdx = leafGlobalIdx % 16 ∧
    forsHyperTreeIdx corduroyPoseidon2Geom leafGlobalIdx = leafGlobalIdx / 16 :=
  ⟨rfl, rfl⟩

/-- Packed FORS leaf address limb `(kp_idx << 24) | ((j << FORS_HEIGHT) | idx_j)`. -/
def forsLeafAddr (geom : AggSigGeometry) (leafGlobalIdx j idx : Nat) : Nat :=
  (forsKpIdx geom leafGlobalIdx <<< 24) ||| ((j <<< geom.forsHeight) ||| idx)

/-- In the deployed geometry the leaf address limb is `(kp_idx << 24) | (j << 8) | idx_j`. -/
theorem corduroy_forsLeafAddr (leafGlobalIdx j idx : Nat) :
    forsLeafAddr corduroyPoseidon2Geom leafGlobalIdx j idx =
      ((leafGlobalIdx % 16) <<< 24) ||| ((j <<< 8) ||| idx) := by
  unfold forsLeafAddr forsKpIdx
  rfl

/-- Tweak of the FORS leaf PRF / leaf hash:
    `[domain, (kp_idx << 24) | (j << FORS_HEIGHT) | idx_j, tree_idx & 0xFFFF_FFFF, tree_idx >> 32]`. -/
def forsLeafTweak4 (domainTag : Goldilocks) (geom : AggSigGeometry)
    (leafGlobalIdx j idx : Nat) : Digest4 :=
  ⟨domainTag,
   Goldilocks.ofNat (forsLeafAddr geom leafGlobalIdx j idx),
   Goldilocks.ofNat (forsHyperTreeIdx geom leafGlobalIdx % (2 ^ 32)),
   Goldilocks.ofNat ((forsHyperTreeIdx geom leafGlobalIdx / (2 ^ 32)) % (2 ^ 32))⟩

/-- FORS leaf secret of leaf `idx` in FORS tree `j` (`fors_leaf_secret` in `sig.rs`). -/
def forsSecretVal (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (leafGlobalIdx j idx : Nat) : Digest4 :=
  poseidon2Compress12FF skSeed pkSeed (forsLeafTweak4 domainForsPrf geom leafGlobalIdx j idx)

/-- FORS leaf hash of leaf `idx` in FORS tree `j` (`recover_fors_pk` in `sig.rs`). -/
def forsLeafHash (geom : AggSigGeometry) (pkSeed val : Digest4)
    (leafGlobalIdx j idx : Nat) : Digest4 :=
  poseidon2Compress12FF val pkSeed (forsLeafTweak4 domainForsLeaf geom leafGlobalIdx j idx)

/-- Node addressing of FORS tree `j` of the instance at `leafGlobalIdx`. -/
def forsTreeNodeAddr (geom : AggSigGeometry) (leafGlobalIdx j : Nat) : Nat → Nat → Nat :=
  forsNodeAddr geom.forsHeight (forsKpIdx geom leafGlobalIdx) j

/-- Rate-8 sponge over the FORS roots (`recover_fors_pk`): the capacity block is
    `[kp_idx, tree_idx & 0xFFFF_FFFF, tree_idx >> 32, FORS_TREES]`. -/
def compressForsRootsSponge (geom : AggSigGeometry) (pkSeed : Digest4) (leafGlobalIdx : Nat)
    (roots : List Digest4) : Digest4 :=
  let initSt : Poseidon2State12 :=
    ⟨pkSeed,
     ⟨Goldilocks.ofNat (forsKpIdx geom leafGlobalIdx),
      Goldilocks.ofNat (forsHyperTreeIdx geom leafGlobalIdx % (2 ^ 32)),
      Goldilocks.ofNat ((forsHyperTreeIdx geom leafGlobalIdx / (2 ^ 32)) % (2 ^ 32)),
      Goldilocks.ofNat geom.forsTrees⟩,
     ⟨domainForsRoots, Goldilocks.zero, Goldilocks.zero, poseidon2IvTag⟩⟩
  let st0 := poseidon2Perm12 initSt
  let stAbs := absorbDigest4Pairs st0 roots
  let stPad : Poseidon2State12 :=
    ⟨⟨Goldilocks.add stAbs.b0.x0 Goldilocks.one, stAbs.b0.x1, stAbs.b0.x2, stAbs.b0.x3⟩,
     stAbs.b1, stAbs.b2⟩
  (poseidon2Perm12 stPad).b0

/-- Two-block stateless XOF sponge state (`derive_stateless_fors_and_leaf_checked`, `sig.rs:494`). -/
def statelessXofSpongeState (pk : AggValidatorPk) (rRand : Digest4) (mu : Digest5) : Poseidon2State12 :=
  let st0 := poseidon2Perm12
    ⟨pk.pkSeed, pk.pkRoot, ⟨domainHMsgStateless, mu.limb4, Goldilocks.zero, poseidon2IvTag⟩⟩
  let muLow : Digest4 := ⟨mu.limb0, mu.limb1, mu.limb2, mu.limb3⟩
  poseidon2Perm12 ⟨lane4Add st0.b0 rRand, lane4Add st0.b1 muLow, st0.b2⟩

/-- Stateless XOF deriving `leafGlobalIdx` and `forsTrees` leaf offsets (`derive_stateless_fors_and_leaf_checked`, `sig.rs:494`). -/
def deriveStatelessLeafAndForsChecked (geom : AggSigGeometry) (pk : AggValidatorPk)
    (rRand : Digest4) (mu : Digest5) : Option (Nat × List Nat) :=
  let st1 := statelessXofSpongeState pk rRand mu
  let sq := [st1.b0.x0, st1.b0.x1, st1.b0.x2, st1.b0.x3, st1.b1.x0, st1.b1.x1, st1.b1.x2]
  if sq.all (fun l => decide (l.val < 2 ^ 63)) then
    let totalTreeBits := geom.numLayers * geom.subtreeHeight
    let rawLeaf := (st1.b1.x1.val % (2 ^ 32)) + ((st1.b1.x2.val % (2 ^ 32)) * (2 ^ 32))
    let leafGlobalIdx := rawLeaf % (2 ^ totalTreeBits)
    let treeMod := 2 ^ geom.forsHeight
    let indices := (List.range geom.forsTrees).map fun t =>
      let limbVal := match t / 7 with
        | 0 => st1.b0.x0.val
        | 1 => st1.b0.x1.val
        | 2 => st1.b0.x2.val
        | 3 => st1.b0.x3.val
        | _ => st1.b1.x0.val
      (limbVal / (256 ^ (t % 7))) % treeMod
    some (leafGlobalIdx, indices)
  else
    none

/-- Honest WOTS+C chain endpoints for `(layer, treeIdx, kpIdx)`. -/
def honestWotsEndpoints (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (layer treeIdx kpIdx : Nat) : List Digest4 :=
  (List.range geom.wotsChains).map fun c =>
    wotsChainWalk pkSeed layer treeIdx kpIdx c 0 3
      (wotsSecretStart skSeed pkSeed layer treeIdx kpIdx c)

/-- Honest WOTS+C public key leaf for `(layer, treeIdx, kpIdx)`. -/
def honestWotsPk (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (layer treeIdx kpIdx : Nat) : Digest4 :=
  compressWotsEndpointsSponge pkSeed layer treeIdx kpIdx
    (honestWotsEndpoints geom skSeed pkSeed layer treeIdx kpIdx)

/-- Honest XMSS subtree root at `(layer, treeIdx)`. -/
def honestSubtreeRoot (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (layer treeIdx : Nat) : Digest4 :=
  buildMerkleNodeAt domainMerkleNode pkSeed layer treeIdx xmssNodeAddr
    (honestWotsPk geom skSeed pkSeed layer treeIdx) geom.subtreeHeight 1 0

/-- Derive validator public key from `(geom, skSeed, pkSeed)`. -/
def deriveAggPublicKey (geom : AggSigGeometry) (skSeed pkSeed : Digest4) : AggValidatorPk :=
  { profile := geom.profile
    pkSeed  := pkSeed
    pkRoot  := honestSubtreeRoot geom skSeed pkSeed (geom.numLayers - 1) 0 }

/-- Honest FORS leaf `off` of FORS tree `j` at `leafGlobalIdx`. -/
def honestForsLeaf (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (leafGlobalIdx j off : Nat) : Digest4 :=
  forsLeafHash geom pkSeed (forsSecretVal geom skSeed pkSeed leafGlobalIdx j off) leafGlobalIdx j off

/-- Honest root of FORS tree `j` at `leafGlobalIdx`. -/
def honestForsTreeRoot (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (leafGlobalIdx j : Nat) : Digest4 :=
  buildMerkleNodeAt domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
    (forsTreeNodeAddr geom leafGlobalIdx j)
    (honestForsLeaf geom skSeed pkSeed leafGlobalIdx j)
    geom.forsHeight 1 0

/-- Honest FORS public key at `leafGlobalIdx`. -/
def honestForsPk (geom : AggSigGeometry) (skSeed pkSeed : Digest4) (leafGlobalIdx : Nat) : Digest4 :=
  compressForsRootsSponge geom pkSeed leafGlobalIdx
    ((List.range geom.forsTrees).map (honestForsTreeRoot geom skSeed pkSeed leafGlobalIdx))

private def recoverEndpointsPoly {D : Type} (walkFn : Nat → Nat → Nat → D → D) :
    List Nat → List D → Nat → List D
  | [], _, _ => []
  | _, [], _ => []
  | d :: ds, sigVal :: rest, c =>
    walkFn c d (3 - d) sigVal :: recoverEndpointsPoly walkFn ds rest (c + 1)

private theorem recoverEndpointsPoly_honest {D : Type}
    (stepFn : Nat → Nat → D → D) (secretFn : Nat → D) :
    ∀ (digits : List Nat) (startC : Nat),
      (∀ d ∈ digits, d < 4) →
      recoverEndpointsPoly (fun c st n v => natIterAt (stepFn c) n st v)
        digits
        ((List.range digits.length).map fun i =>
          natIterAt (stepFn (startC + i)) (digits[i]!) 0 (secretFn (startC + i)))
        startC =
      (List.range digits.length).map fun i =>
        natIterAt (stepFn (startC + i)) 3 0 (secretFn (startC + i))
  | [], _, _ => rfl
  | d :: ds, startC, hLt => by
    have hd4 : d < 4 := hLt d (List.mem_cons_self ..)
    have hAdd3 : d + (3 - d) = 3 := by omega
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_cons]
    dsimp only [recoverEndpointsPoly]
    simp only [Nat.add_zero, List.getElem!_cons_zero]
    congr 1
    · conv => lhs; arg 3; rw [← Nat.zero_add d]
      rw [← natIterAt_add (stepFn startC) d (3 - d) 0, hAdd3]
    · simp only [List.map_map]
      have hFn1 :
          ((fun i => natIterAt (stepFn (startC + i)) ((d :: ds)[i]!) 0 (secretFn (startC + i))) ∘ Nat.succ) =
          (fun i => natIterAt (stepFn (startC + 1 + i)) (ds[i]!) 0 (secretFn (startC + 1 + i))) := by
        funext i
        have hIdx : startC + (i + 1) = startC + 1 + i := by omega
        simp [Function.comp, hIdx]
      have hFn2 :
          ((fun i => natIterAt (stepFn (startC + i)) 3 0 (secretFn (startC + i))) ∘ Nat.succ) =
          (fun i => natIterAt (stepFn (startC + 1 + i)) 3 0 (secretFn (startC + 1 + i))) := by
        funext i
        have hIdx : startC + (i + 1) = startC + 1 + i := by omega
        simp [Function.comp, hIdx]
      rw [hFn1, hFn2]
      exact recoverEndpointsPoly_honest stepFn secretFn ds (startC + 1)
        (fun x hx => hLt x (List.mem_cons_of_mem _ hx))

/-- Recover WOTS+C endpoints from signature chains and extracted base-4 digits (`0..3`). -/
def recoverAggWotsEndpoints (pkSeed : Digest4) (layer treeIdx kpIdx startC : Nat)
    (ds : List Nat) (chains : List Digest4) : List Digest4 :=
  recoverEndpointsPoly (wotsChainWalk pkSeed layer treeIdx kpIdx) ds chains startC

private theorem recoverAggWotsEndpoints_honest (pkSeed skSeed : Digest4) (layer treeIdx kpIdx : Nat)
    (digits : List Nat) (startC : Nat) (hLt : ∀ d ∈ digits, d < 4) :
    recoverAggWotsEndpoints pkSeed layer treeIdx kpIdx startC digits
      ((List.range digits.length).map fun i =>
        wotsChainWalk pkSeed layer treeIdx kpIdx (startC + i) 0 (digits[i]!)
          (wotsSecretStart skSeed pkSeed layer treeIdx kpIdx (startC + i))) =
    (List.range digits.length).map fun i =>
      wotsChainWalk pkSeed layer treeIdx kpIdx (startC + i) 0 3
        (wotsSecretStart skSeed pkSeed layer treeIdx kpIdx (startC + i)) :=
  recoverEndpointsPoly_honest
    (fun c stp v => wotsStepHash pkSeed v layer treeIdx kpIdx c stp)
    (wotsSecretStart skSeed pkSeed layer treeIdx kpIdx)
    digits startC hLt

/-- Verify one WOTS+C + XMSS subtree layer and return the walked subtree root. -/
def verifyWotsLayer (geom : AggSigGeometry) (pk : AggValidatorPk)
    (layer treeIdx kpIdx : Nat) (hmsg : Digest5) (lsig : WotsLayerSig) : Option Digest4 :=
  if lsig.wotsChains.length == geom.wotsChains && lsig.merklePath.length == geom.subtreeHeight then
    match extractWotsDigitsChecked geom hmsg with
    | none => none
    | some digits =>
      if listNatSum digits == geom.targetSum then
        let endpoints := recoverAggWotsEndpoints pk.pkSeed layer treeIdx kpIdx 0 digits lsig.wotsChains
        let wotsPk := compressWotsEndpointsSponge pk.pkSeed layer treeIdx kpIdx endpoints
        some (merkleWalkRoot domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr 1 kpIdx wotsPk
          lsig.merklePath)
      else
        none
  else
    none

private def verifyForsPoly {OP D : Type} (step : Nat → Nat → OP → Option D) :
    List Nat → List OP → Nat → Option (List D)
  | [], [], _ => some []
  | idx :: idxs, op :: ops, t =>
    match step t idx op with
    | none => none
    | some rt =>
      match verifyForsPoly step idxs ops (t + 1) with
      | none => none
      | some rest => some (rt :: rest)
  | _, _, _ => none

/-- Verify the opening of leaf `idx` of FORS tree `j` (`recover_fors_pk`): the Merkle walk hashes
    under `tree_idx = leaf_global_idx >> h'`, the 1-based level `lvl + 1`, and the node index
    `(kp_idx << 16) + ((j << (FORS_HEIGHT - 1 - lvl)) + parent_idx)`. -/
def verifySingleForsOpening (geom : AggSigGeometry) (pkSeed : Digest4)
    (leafGlobalIdx j idx : Nat) (op : AggForsTreeOpening) : Option Digest4 :=
  if idx < 2 ^ geom.forsHeight && op.authPath.length == geom.forsHeight then
    let leaf := forsLeafHash geom pkSeed op.secretVal leafGlobalIdx j idx
    some (merkleWalkRoot domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
      (forsTreeNodeAddr geom leafGlobalIdx j) 1 idx leaf op.authPath)
  else
    none

/-- Verify FORS openings and recover `forsPk`. -/
def verifyForsTreesAux (geom : AggSigGeometry) (pkSeed : Digest4) (leafGlobalIdx startT : Nat)
    (idxs : List Nat) (ops : List AggForsTreeOpening) : Option (List Digest4) :=
  verifyForsPoly (verifySingleForsOpening geom pkSeed leafGlobalIdx) idxs ops startT

def verifyAndRecoverForsPk (geom : AggSigGeometry) (pkSeed : Digest4) (leafGlobalIdx : Nat)
    (indices : List Nat) (openings : List AggForsTreeOpening) : Option Digest4 :=
  if indices.length == geom.forsTrees && openings.length == geom.forsTrees then
    match verifyForsTreesAux geom pkSeed leafGlobalIdx 0 indices openings with
    | none => none
    | some roots => some (compressForsRootsSponge geom pkSeed leafGlobalIdx roots)
  else
    none

/-- The node address of FORS tree `j` determines `j`: within one key pair and one level, two
    in-range parent indices of trees `j₁`, `j₂` share an address only if `j₁ = j₂`. -/
theorem forsNodeAddr_injective (forsHeight kpIdx j₁ j₂ level p₁ p₂ : Nat)
    (hp₁ : p₁ < 2 ^ (forsHeight - level)) (hp₂ : p₂ < 2 ^ (forsHeight - level))
    (hEq : forsNodeAddr forsHeight kpIdx j₁ level p₁ = forsNodeAddr forsHeight kpIdx j₂ level p₂) :
    j₁ = j₂ ∧ p₁ = p₂ := by
  unfold forsNodeAddr at hEq
  have hPos : 0 < 2 ^ (forsHeight - level) := Nat.pow_pos (by decide)
  have hE : 2 ^ (forsHeight - level) * j₁ + p₁ = 2 ^ (forsHeight - level) * j₂ + p₂ := by
    have h := Nat.add_left_cancel hEq
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.mul_comm j₁, Nat.mul_comm j₂] at h
    exact h
  have hD := congrArg (· / 2 ^ (forsHeight - level)) hE
  have hM := congrArg (· % 2 ^ (forsHeight - level)) hE
  rw [Nat.mul_add_div hPos, Nat.mul_add_div hPos, Nat.div_eq_of_lt hp₁, Nat.div_eq_of_lt hp₂,
    Nat.add_zero, Nat.add_zero] at hD
  rw [Nat.mul_add_mod, Nat.mul_add_mod, Nat.mod_eq_of_lt hp₁, Nat.mod_eq_of_lt hp₂] at hM
  exact ⟨hD, hM⟩

/-- Top node of a non-empty Merkle walk: the last hash is taken at level `lvl + (len - 1)` and
    parent index `idx / 2 ^ len`. -/
private def merkleWalkPolyTopNode {D : Type} (nodeHash : Nat → Nat → D → D → D) :
    ∀ (path : List D) (lvl idx : Nat) (cur : D), path ≠ [] →
      { lr : D × D // merkleWalkPoly nodeHash path lvl idx cur =
          nodeHash (lvl + (path.length - 1)) (idx / 2 ^ path.length) lr.1 lr.2 }
  | [], _, _, _, h => absurd rfl h
  | [sib], lvl, idx, cur, _ =>
    match hE : (idx % 2 == 0) with
    | true => ⟨(cur, sib), by dsimp only [merkleWalkPoly]; rw [hE]; exact rfl⟩
    | false => ⟨(sib, cur), by dsimp only [merkleWalkPoly]; rw [hE]; exact rfl⟩
  | sib :: s2 :: rest, lvl, idx, cur, _ =>
    let parent :=
      if idx % 2 == 0 then nodeHash lvl (idx / 2) cur sib else nodeHash lvl (idx / 2) sib cur
    let top := merkleWalkPolyTopNode nodeHash (s2 :: rest) (lvl + 1) (idx / 2) parent
      (List.cons_ne_nil _ _)
    ⟨top.1, by
      have hLvl : lvl + 1 + ((s2 :: rest).length - 1) = lvl + ((sib :: s2 :: rest).length - 1) := by
        simp only [List.length_cons]
        omega
      have hIdx : idx / 2 / 2 ^ (s2 :: rest).length = idx / 2 ^ (sib :: s2 :: rest).length := by
        rw [Nat.div_div_eq_div_mul, List.length_cons (a := sib), Nat.pow_succ, Nat.mul_comm]
      rw [← hLvl, ← hIdx]
      exact top.2⟩

/-- One `merkleNodeHash` output shared by the top nodes of two FORS trees `j₁`, `j₂` of one
    instance, whose `node_idx` limbs `(kp_idx << 16) + j₁` and `(kp_idx << 16) + j₂` differ
    whenever `j₁ ≠ j₂`. -/
structure ForsCrossTreeNodeCollision (geom : AggSigGeometry) (pkSeed : Digest4)
    (leafGlobalIdx j₁ j₂ : Nat) where
  left1  : Digest4
  right1 : Digest4
  left2  : Digest4
  right2 : Digest4
  hashEq :
    merkleNodeHash domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx) geom.forsHeight
        ((forsKpIdx geom leafGlobalIdx <<< 16) + j₁) left1 right1 =
      merkleNodeHash domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx) geom.forsHeight
        ((forsKpIdx geom leafGlobalIdx <<< 16) + j₂) left2 right2

theorem forsTreeNodeAddr_top (geom : AggSigGeometry) (leafGlobalIdx j : Nat) :
    forsTreeNodeAddr geom leafGlobalIdx j geom.forsHeight 0 =
      (forsKpIdx geom leafGlobalIdx <<< 16) + j := by
  unfold forsTreeNodeAddr forsNodeAddr
  rw [Nat.sub_self, Nat.shiftLeft_zero, Nat.add_zero]

/-- An opening accepted with the same root in two FORS trees `j₁`, `j₂` exhibits a
    `ForsCrossTreeNodeCollision`: the two walks end in top-node hashes under the two tree
    addresses. -/
def extractForsCrossTreeCollision (geom : AggSigGeometry) (pkSeed : Digest4)
    (leafGlobalIdx j₁ j₂ idx : Nat) (op : AggForsTreeOpening) (rt : Digest4)
    (hH : 0 < geom.forsHeight)
    (h₁ : verifySingleForsOpening geom pkSeed leafGlobalIdx j₁ idx op = some rt)
    (h₂ : verifySingleForsOpening geom pkSeed leafGlobalIdx j₂ idx op = some rt) :
    ForsCrossTreeNodeCollision geom pkSeed leafGlobalIdx j₁ j₂ := by
  unfold verifySingleForsOpening at h₁ h₂
  cases hChk : (decide (idx < 2 ^ geom.forsHeight) && (op.authPath.length == geom.forsHeight))
  · exact absurd h₁ (by simp [hChk])
  · simp only [hChk, ↓reduceIte, Option.some.injEq] at h₁ h₂
    rcases Bool.and_eq_true_iff.mp hChk with ⟨hIdxLtDec, hPathLenBeq⟩
    have hIdxLt : idx < 2 ^ geom.forsHeight := of_decide_eq_true hIdxLtDec
    have hPathLen : op.authPath.length = geom.forsHeight := eq_of_beq hPathLenBeq
    have hNeNil : op.authPath ≠ [] := by
      intro hNil
      rw [hNil] at hPathLen
      exact absurd hPathLen.symm (Nat.ne_of_gt hH)
    have hTop : ∀ (j : Nat) (a b : Digest4),
        merkleAddrNodeHash domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
            (forsTreeNodeAddr geom leafGlobalIdx j)
            (1 + (op.authPath.length - 1)) (idx / 2 ^ op.authPath.length) a b =
          merkleNodeHash domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
            geom.forsHeight ((forsKpIdx geom leafGlobalIdx <<< 16) + j) a b := by
      intro j a b
      have hL : 1 + (op.authPath.length - 1) = geom.forsHeight := by
        rw [hPathLen]
        omega
      have hI : idx / 2 ^ op.authPath.length = 0 := by
        rw [hPathLen]
        exact Nat.div_eq_of_lt hIdxLt
      rw [hL, hI]
      unfold merkleAddrNodeHash
      rw [forsTreeNodeAddr_top]
    let t1 := merkleWalkPolyTopNode
      (merkleAddrNodeHash domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
        (forsTreeNodeAddr geom leafGlobalIdx j₁))
      op.authPath 1 idx (forsLeafHash geom pkSeed op.secretVal leafGlobalIdx j₁ idx) hNeNil
    let t2 := merkleWalkPolyTopNode
      (merkleAddrNodeHash domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
        (forsTreeNodeAddr geom leafGlobalIdx j₂))
      op.authPath 1 idx (forsLeafHash geom pkSeed op.secretVal leafGlobalIdx j₂ idx) hNeNil
    exact
      { left1 := t1.1.1, right1 := t1.1.2, left2 := t2.1.1, right2 := t2.1.2
        hashEq := (hTop j₁ _ _).symm.trans
          ((t1.2.symm.trans h₁).trans ((t2.2.symm.trans h₂).symm.trans (hTop j₂ _ _))) }

/-- **`#tooth`: cross-FORS-tree node transplant.** With `j₁ ≠ j₂` the top-node addresses of
    the two trees differ, and an opening accepted in tree `j₁` is rejected in tree `j₂` unless
    the two differently-addressed top-node hashes collide. -/
theorem tooth_fors_cross_tree_transplant_rejected (geom : AggSigGeometry) (pkSeed : Digest4)
    (leafGlobalIdx j₁ j₂ idx : Nat) (op : AggForsTreeOpening) (rt : Digest4)
    (hH : 0 < geom.forsHeight) (hNe : j₁ ≠ j₂)
    (hNoCol : ForsCrossTreeNodeCollision geom pkSeed leafGlobalIdx j₁ j₂ → False)
    (h₁ : verifySingleForsOpening geom pkSeed leafGlobalIdx j₁ idx op = some rt) :
    forsTreeNodeAddr geom leafGlobalIdx j₁ geom.forsHeight 0 ≠
        forsTreeNodeAddr geom leafGlobalIdx j₂ geom.forsHeight 0 ∧
      verifySingleForsOpening geom pkSeed leafGlobalIdx j₂ idx op ≠ some rt := by
  refine ⟨?_, fun h₂ =>
    hNoCol (extractForsCrossTreeCollision geom pkSeed leafGlobalIdx j₁ j₂ idx op rt hH h₁ h₂)⟩
  rw [forsTreeNodeAddr_top, forsTreeNodeAddr_top]
  exact fun h => hNe (Nat.add_left_cancel h)

private def verifyUpperPoly {LS D : Type} (step : Nat → Nat → D → LS → Option (Nat × D)) :
    List LS → Nat → Nat → D → Option D
  | [], _, _, curRoot => some curRoot
  | lsig :: rest, layer, remTreeIdx, curRoot =>
    match step layer remTreeIdx curRoot lsig with
    | none => none
    | some (nextRem, nextRoot) => verifyUpperPoly step rest (layer + 1) nextRem nextRoot

/-- Walk upper hypertree layers `startLayer .. startLayer + remLayers - 1` from `curChildRoot`. -/
def verifyUpperLayers (geom : AggSigGeometry) (pk : AggValidatorPk)
    (layer remTreeIdx : Nat) (curRoot : Digest4) (ls : List WotsLayerSig) : Option Digest4 :=
  verifyUpperPoly
    (fun l rem cur lsig =>
      let kpIdx := rem % (2 ^ geom.subtreeHeight)
      let treeIdx := rem / (2 ^ geom.subtreeHeight)
      let hmsg := computeHmsgDetTree pk l treeIdx kpIdx lsig.tswCtr cur
      match verifyWotsLayer geom pk l treeIdx kpIdx hmsg lsig with
      | none => none
      | some nextRoot => some (treeIdx, nextRoot))
    ls layer remTreeIdx curRoot

def verifyAggNativeSigStateful (geom : AggSigGeometry) (pk : AggValidatorPk)
    (mu : Digest5) (sig : AggNativeSignature) (lsig0 : WotsLayerSig) (upperLayers : List WotsLayerSig) : Bool :=
  if !sig.forsOpenings.isEmpty ||
     !(sig.statefulLeafIdx < 2 ^ (geom.numLayers * geom.subtreeHeight)) then
    false
  else
    let kpIdx0 := sig.statefulLeafIdx % (2 ^ geom.subtreeHeight)
    let treeIdx0 := sig.statefulLeafIdx / (2 ^ geom.subtreeHeight)
    let hmsg0 := computeHmsgStateful pk sig.rRand mu kpIdx0 lsig0.tswCtr
    match verifyWotsLayer geom pk 0 treeIdx0 kpIdx0 hmsg0 lsig0 with
    | none => false
    | some root0 =>
      match verifyUpperLayers geom pk 1 treeIdx0 root0 upperLayers with
      | none => false
      | some topRoot => topRoot == pk.pkRoot

private def evalStatelessFlow {Idx Ops FPk R0 Rt : Type}
    (statefulNz : Bool)
    (xofRes : Option (Idx × Ops))
    (verFors : Idx → Ops → Option FPk)
    (verLayer0 : Idx → FPk → Option R0)
    (verUpper : Idx → R0 → Option Rt)
    (checkTop : Rt → Bool) : Bool :=
  if statefulNz then false
  else match xofRes with
  | none => false
  | some pair =>
    match verFors pair.1 pair.2 with
    | none => false
    | some fpk =>
      match verLayer0 pair.1 fpk with
      | none => false
      | some r0 =>
        match verUpper pair.1 r0 with
        | none => false
        | some top => checkTop top

private theorem evalStatelessFlow_ok {Idx Ops FPk R0 Rt : Type}
    (xofRes : Option (Idx × Ops))
    (verFors : Idx → Ops → Option FPk)
    (verLayer0 : Idx → FPk → Option R0)
    (verUpper : Idx → R0 → Option Rt)
    (checkTop : Rt → Bool)
    (idx : Idx) (ops : Ops) (fpk : FPk) (r0 : R0) (top : Rt)
    (hXof : xofRes = some (idx, ops))
    (hFors : verFors idx ops = some fpk)
    (hL0 : verLayer0 idx fpk = some r0)
    (hUp : verUpper idx r0 = some top)
    (hTop : checkTop top = true) :
    evalStatelessFlow false xofRes verFors verLayer0 verUpper checkTop = true := by
  subst hXof
  simp only [evalStatelessFlow, Bool.false_eq_true, ↓reduceIte, hFors, hL0, hUp]
  exact hTop

private structure StatelessFlowUnpack {Idx Ops FPk R0 Rt : Type}
    (statefulNz : Bool)
    (xofRes : Option (Idx × Ops))
    (verFors : Idx → Ops → Option FPk)
    (verLayer0 : Idx → FPk → Option R0)
    (verUpper : Idx → R0 → Option Rt)
    (checkTop : Rt → Bool) where
  idx   : Idx
  ops   : Ops
  fpk   : FPk
  r0    : R0
  top   : Rt
  hNz   : statefulNz = false
  hXof  : xofRes = some (idx, ops)
  hFors : verFors idx ops = some fpk
  hL0   : verLayer0 idx fpk = some r0
  hUp   : verUpper idx r0 = some top
  hTop  : checkTop top = true

private def unpackStatelessFlow {Idx Ops FPk R0 Rt : Type}
    {statefulNz : Bool}
    {xofRes : Option (Idx × Ops)}
    {verFors : Idx → Ops → Option FPk}
    {verLayer0 : Idx → FPk → Option R0}
    {verUpper : Idx → R0 → Option Rt}
    {checkTop : Rt → Bool}
    (hOk : evalStatelessFlow statefulNz xofRes verFors verLayer0 verUpper checkTop = true) :
    StatelessFlowUnpack statefulNz xofRes verFors verLayer0 verUpper checkTop := by
  cases hNz : statefulNz
  · simp only [evalStatelessFlow, hNz, Bool.false_eq_true, ↓reduceIte] at hOk
    cases hXof : xofRes with
    | none => simp [hXof] at hOk
    | some pair =>
      rcases pair with ⟨idx, ops⟩
      simp only [hXof] at hOk
      cases hFors : verFors idx ops with
      | none => simp [hFors] at hOk
      | some fpk =>
        simp only [hFors] at hOk
        cases hL0 : verLayer0 idx fpk with
        | none => simp [hL0] at hOk
        | some r0 =>
          simp only [hL0] at hOk
          cases hUp : verUpper idx r0 with
          | none => simp [hUp] at hOk
          | some top =>
            simp only [hUp] at hOk
            exact ⟨idx, ops, fpk, r0, top, rfl, rfl, hFors, hL0, hUp, hOk⟩
  · simp [evalStatelessFlow, hNz] at hOk

def verifyAggNativeSigStateless (geom : AggSigGeometry) (pk : AggValidatorPk)
    (mu : Digest5) (sig : AggNativeSignature) (lsig0 : WotsLayerSig) (upperLayers : List WotsLayerSig) : Bool :=
  evalStatelessFlow
    (sig.statefulLeafIdx != 0)
    (deriveStatelessLeafAndForsChecked geom pk sig.rRand mu)
    (fun leafGlobalIdx forsIndices =>
      verifyAndRecoverForsPk geom pk.pkSeed leafGlobalIdx forsIndices sig.forsOpenings)
    (fun leafGlobalIdx forsPk =>
      let kpIdx0 := leafGlobalIdx % (2 ^ geom.subtreeHeight)
      let treeIdx0 := leafGlobalIdx / (2 ^ geom.subtreeHeight)
      let hmsg0 := computeHmsgDetTree pk 0 treeIdx0 kpIdx0 lsig0.tswCtr forsPk
      verifyWotsLayer geom pk 0 treeIdx0 kpIdx0 hmsg0 lsig0)
    (fun leafGlobalIdx root0 =>
      verifyUpperLayers geom pk 1 (leafGlobalIdx / 2 ^ geom.subtreeHeight) root0 upperLayers)
    (fun topRoot => topRoot == pk.pkRoot)

/-- Full standalone verifier for `AggNativeSignature` (`verify_individual_signature` in `sig.rs`). -/
@[expose] def verifyAggNativeSig (geom : AggSigGeometry) (pk : AggValidatorPk)
    (msg : List UInt8) (sig : AggNativeSignature) : Bool :=
  if !geom.wellFormed || pk.profile != geom.profile || sig.profile != geom.profile ||
     sig.layers.length != geom.numLayers then
    false
  else
    let mu := computeMessageMu pk msg
    match sig.layers with
    | [] => false
    | lsig0 :: upperLayers =>
      if geom.forsTrees == 0 then
        verifyAggNativeSigStateful geom pk mu sig lsig0 upperLayers
      else
        verifyAggNativeSigStateless geom pk mu sig lsig0 upperLayers

/-- Sign a single WOTS+C + XMSS subtree layer given valid target-sum `digits` (`digits.length = geom.wotsChains`). -/
def signWotsLayerWithDigits (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (layer treeIdx kpIdx tswCtr : Nat) (digits : List Nat) : WotsLayerSig :=
  let chains := (List.range digits.length).map fun c =>
    wotsChainWalk pkSeed layer treeIdx kpIdx c 0 (digits[c]!)
      (wotsSecretStart skSeed pkSeed layer treeIdx kpIdx c)
  let path := buildMerkleAuthPathAt domainMerkleNode pkSeed layer treeIdx xmssNodeAddr
    (honestWotsPk geom skSeed pkSeed layer treeIdx) geom.subtreeHeight 1 kpIdx
  { tswCtr := tswCtr, wotsChains := chains, merklePath := path }

@[simp] private theorem signWotsLayerWithDigits_tswCtr (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (layer treeIdx kpIdx tswCtr : Nat) (digits : List Nat) :
    (signWotsLayerWithDigits geom skSeed pkSeed layer treeIdx kpIdx tswCtr digits).tswCtr = tswCtr :=
  rfl

attribute [local irreducible]
  packWotsAddrLimb checkDigest5Limbs63 extractWotsDigitsChecked
  wotsSecretStart wotsStepHash forsSecretVal forsLeafHash forsLeafTweak4
  poseidon2Compress12FF merkleNodeHash compressWotsEndpointsSponge compressForsRootsSponge
  computeHmsgStateful computeHmsgDetTree statelessXofSpongeState

/-- Witness bundle of pre-searched `tsw_ctr` counters whose extracted base-4 digits hit `geom.targetSum`. -/
structure ValidSigningCtrs (geom : AggSigGeometry) (skSeed : Digest4) (pk : AggValidatorPk)
    (msg : List UInt8) (rRand : Digest4) (statefulLeafIdx : Nat) where
  layer0Ctr    : Nat
  upperCtrs    : List Nat
  lenUpper     : upperCtrs.length + 1 = geom.numLayers
  leafInRange  : geom.forsTrees = 0 → statefulLeafIdx < 2 ^ (geom.numLayers * geom.subtreeHeight)
  statelessZero : geom.forsTrees ≠ 0 → statefulLeafIdx = 0
  statelessXofOk : geom.forsTrees ≠ 0 →
    deriveStatelessLeafAndForsChecked geom pk rRand (computeMessageMu pk msg) ≠ none
  layer0Valid  :
    let mu := computeMessageMu pk msg
    let leafIdx :=
      if geom.forsTrees == 0 then statefulLeafIdx
      else match deriveStatelessLeafAndForsChecked geom pk rRand mu with
           | some pair => pair.1
           | none => 0
    let kp0 := leafIdx % (2 ^ geom.subtreeHeight)
    let tr0 := leafIdx / (2 ^ geom.subtreeHeight)
    let hmsg0 :=
      if geom.forsTrees == 0 then computeHmsgStateful pk rRand mu kp0 layer0Ctr
      else computeHmsgDetTree pk 0 tr0 kp0 layer0Ctr (honestForsPk geom skSeed pk.pkSeed leafIdx)
    ∃ ds0, extractWotsDigitsChecked geom hmsg0 = some ds0 ∧ listNatSum ds0 = geom.targetSum
  upperValid   :
    let mu := computeMessageMu pk msg
    let leafIdx :=
      if geom.forsTrees == 0 then statefulLeafIdx
      else match deriveStatelessLeafAndForsChecked geom pk rRand mu with
           | some pair => pair.1
           | none => 0
    ∀ (j : Nat) (hj : j < upperCtrs.length),
      let l := j + 1
      let remIdx := leafIdx / (2 ^ (l * geom.subtreeHeight))
      let kpL := remIdx % (2 ^ geom.subtreeHeight)
      let trL := remIdx / (2 ^ geom.subtreeHeight)
      let childRt := honestSubtreeRoot geom skSeed pk.pkSeed j remIdx
      let hmsgL := computeHmsgDetTree pk l trL kpL (upperCtrs[j]'hj) childRt
      ∃ dsL, extractWotsDigitsChecked geom hmsgL = some dsL ∧ listNatSum dsL = geom.targetSum

private def signUpperPoly {LS : Type} (step : Nat → Nat → Nat → (Nat × LS)) :
    List Nat → Nat → Nat → List LS
  | [], _, _ => []
  | ctr :: rest, layer, remTreeIdx =>
    let (treeIdx, lsig) := step layer remTreeIdx ctr
    lsig :: signUpperPoly step rest (layer + 1) treeIdx

private theorem signUpperPoly_length {LS : Type} (step : Nat → Nat → Nat → (Nat × LS)) :
    ∀ (cs : List Nat) (layer remIdx : Nat),
      (signUpperPoly step cs layer remIdx).length = cs.length
  | [], _, _ => rfl
  | _ :: rest, layer, remIdx => by
    dsimp only [signUpperPoly]
    rw [List.length_cons, signUpperPoly_length step rest]
    rfl

private def signUpperLayersAux (geom : AggSigGeometry) (skSeed : Digest4) (pk : AggValidatorPk)
    (layer remTreeIdx : Nat) (cs : List Nat) : List WotsLayerSig :=
  signUpperPoly
    (fun l rem ctr =>
      let kpIdx := rem % (2 ^ geom.subtreeHeight)
      let treeIdx := rem / (2 ^ geom.subtreeHeight)
      let childRt := honestSubtreeRoot geom skSeed pk.pkSeed (l - 1) rem
      let hmsg := computeHmsgDetTree pk l treeIdx kpIdx ctr childRt
      let digits := (extractWotsDigitsChecked geom hmsg).getD []
      (treeIdx, signWotsLayerWithDigits geom skSeed pk.pkSeed l treeIdx kpIdx ctr digits))
    cs layer remTreeIdx

private def signForsPoly {OP : Type} (step : Nat → Nat → OP) :
    List Nat → Nat → List OP
  | [], _ => []
  | off :: offs, t => step t off :: signForsPoly step offs (t + 1)

private theorem signForsPoly_length {OP : Type} (step : Nat → Nat → OP) :
    ∀ (offs : List Nat) (t : Nat), (signForsPoly step offs t).length = offs.length
  | [], _ => rfl
  | _ :: offs, t => by
    dsimp only [signForsPoly]
    rw [List.length_cons, signForsPoly_length step offs (t + 1)]
    rfl

/-- Sign all FORS openings at `leafGlobalIdx` for `indices`. -/
def signForsTreesAux (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (leafGlobalIdx startT : Nat) (offs : List Nat) : List AggForsTreeOpening :=
  signForsPoly
    (fun t off =>
      let sec := forsSecretVal geom skSeed pkSeed leafGlobalIdx t off
      let path := buildMerkleAuthPathAt domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
        (forsTreeNodeAddr geom leafGlobalIdx t)
        (honestForsLeaf geom skSeed pkSeed leafGlobalIdx t)
        geom.forsHeight 1 off
      { secretVal := sec, authPath := path })
    offs startT

/-- Honest `AggNativeSignature` constructor matching `sign_stateful` / `sign_stateless` in `sig.rs`. -/
def signAggNative (geom : AggSigGeometry) (skSeed : Digest4) (pk : AggValidatorPk)
    (msg : List UInt8) (rRand : Digest4) (statefulLeafIdx : Nat)
    (layer0Ctr : Nat) (upperCtrs : List Nat) : AggNativeSignature :=
  let mu := computeMessageMu pk msg
  let (leafIdx, forsOps) :=
    if geom.forsTrees == 0 then
      (statefulLeafIdx, [])
    else
      match deriveStatelessLeafAndForsChecked geom pk rRand mu with
      | none => (0, [])
      | some pair =>
        (pair.1, signForsTreesAux geom skSeed pk.pkSeed pair.1 0 pair.2)
  let kp0 := leafIdx % (2 ^ geom.subtreeHeight)
  let tr0 := leafIdx / (2 ^ geom.subtreeHeight)
  let hmsg0 :=
    if geom.forsTrees == 0 then computeHmsgStateful pk rRand mu kp0 layer0Ctr
    else computeHmsgDetTree pk 0 tr0 kp0 layer0Ctr (honestForsPk geom skSeed pk.pkSeed leafIdx)
  let digits0 := (extractWotsDigitsChecked geom hmsg0).getD []
  let lsig0 := signWotsLayerWithDigits geom skSeed pk.pkSeed 0 tr0 kp0 layer0Ctr digits0
  let upper := signUpperLayersAux geom skSeed pk 1 tr0 upperCtrs
  { profile         := geom.profile
    rRand           := rRand
    statefulLeafIdx := if geom.forsTrees == 0 then statefulLeafIdx else 0
    forsOpenings    := forsOps
    layers          := lsig0 :: upper }

private theorem verifyWotsLayer_signWotsLayerWithDigits
    (geom : AggSigGeometry) (skSeed : Digest4) (pk : AggValidatorPk)
    (hChainsLe : geom.wotsChains ≤ 128)
    (layer treeIdx kpIdx tswCtr : Nat)
    (hKpLt : kpIdx < 2 ^ geom.subtreeHeight)
    (hmsg : Digest5) (digits : List Nat)
    (hExt : extractWotsDigitsChecked geom hmsg = some digits)
    (hSum : listNatSum digits = geom.targetSum) :
    verifyWotsLayer geom pk layer treeIdx kpIdx hmsg
      (signWotsLayerWithDigits geom skSeed pk.pkSeed layer treeIdx kpIdx tswCtr digits) =
    some (honestSubtreeRoot geom skSeed pk.pkSeed layer treeIdx) := by
  obtain ⟨hLenD, hLt4⟩ := extractWotsDigitsChecked_spec hChainsLe hExt
  unfold verifyWotsLayer signWotsLayerWithDigits
  have hChainsLen :
      ((List.range digits.length).map fun c =>
        wotsChainWalk pk.pkSeed layer treeIdx kpIdx c 0 (digits[c]!)
          (wotsSecretStart skSeed pk.pkSeed layer treeIdx kpIdx c)).length = geom.wotsChains := by
    rw [List.length_map, List.length_range, hLenD]
  have hPathLen :
      (buildMerkleAuthPathAt domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr
        (honestWotsPk geom skSeed pk.pkSeed layer treeIdx) geom.subtreeHeight 1 kpIdx).length =
      geom.subtreeHeight :=
    buildMerkleAuthPathAt_length _ _ _ _ _ _ _ _ _
  simp only [hChainsLen, hPathLen, beq_self_eq_true, Bool.and_self, ↓reduceIte, hExt, hSum]
  have hZeroMap :
      ((List.range digits.length).map fun c =>
        wotsChainWalk pk.pkSeed layer treeIdx kpIdx c 0 (digits[c]!)
          (wotsSecretStart skSeed pk.pkSeed layer treeIdx kpIdx c)) =
      ((List.range digits.length).map fun i =>
        wotsChainWalk pk.pkSeed layer treeIdx kpIdx (0 + i) 0 (digits[i]!)
          (wotsSecretStart skSeed pk.pkSeed layer treeIdx kpIdx (0 + i))) := by
    congr 1; funext i; simp
  rw [hZeroMap, recoverAggWotsEndpoints_honest pk.pkSeed skSeed layer treeIdx kpIdx digits 0 hLt4]
  simp only [Nat.zero_add]
  have hEpEq :
      ((List.range digits.length).map fun i =>
        wotsChainWalk pk.pkSeed layer treeIdx kpIdx i 0 3
          (wotsSecretStart skSeed pk.pkSeed layer treeIdx kpIdx i)) =
      honestWotsEndpoints geom skSeed pk.pkSeed layer treeIdx kpIdx := by
    unfold honestWotsEndpoints
    rw [hLenD]
  rw [hEpEq]
  have hWotsEq :
      compressWotsEndpointsSponge pk.pkSeed layer treeIdx kpIdx
        (honestWotsEndpoints geom skSeed pk.pkSeed layer treeIdx kpIdx) =
      honestWotsPk geom skSeed pk.pkSeed layer treeIdx kpIdx := rfl
  rw [hWotsEq]
  rw [merkleWalkRoot_buildMerkleAuthPathAt domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr
        geom.subtreeHeight (honestWotsPk geom skSeed pk.pkSeed layer treeIdx) 1 kpIdx hKpLt]
  rfl

private theorem signUpperLayersAux_length (geom : AggSigGeometry) (skSeed : Digest4) (pk : AggValidatorPk)
    (layer remIdx : Nat) (ctrs : List Nat) :
    (signUpperLayersAux geom skSeed pk layer remIdx ctrs).length = ctrs.length :=
  signUpperPoly_length _ ctrs layer remIdx

private theorem verifyUpperPoly_signUpperPoly {LS D : Type}
    (vStep : Nat → Nat → D → LS → Option (Nat × D))
    (sStep : Nat → Nat → Nat → (Nat × LS))
    (rootAt : Nat → Nat → D)
    (subH : Nat) :
    ∀ (ctrs : List Nat) (startLayer remIdx : Nat),
      0 < startLayer →
      (∀ (j : Nat) (hj : j < ctrs.length),
        let l := startLayer + j
        let curRem := remIdx / (2 ^ (j * subH))
        let (trOut, lsig) := sStep l curRem (ctrs[j]'hj)
        trOut = curRem / (2 ^ subH) ∧
        vStep l curRem (rootAt (l - 1) curRem) lsig =
          some (curRem / (2 ^ subH), rootAt l (curRem / (2 ^ subH)))) →
      verifyUpperPoly vStep (signUpperPoly sStep ctrs startLayer remIdx) startLayer remIdx
        (rootAt (startLayer - 1) remIdx) =
      some (rootAt (startLayer + ctrs.length - 1) (remIdx / (2 ^ (ctrs.length * subH))))
  | [], startLayer, remIdx, _, _ => by
    dsimp only [signUpperPoly, verifyUpperPoly]
    simp only [List.length_nil, Nat.add_zero, Nat.zero_mul, Nat.pow_zero, Nat.div_one]
  | ctr :: rest, startLayer, remIdx, hPos, hValid => by
    dsimp only [signUpperPoly]
    have h0 := hValid 0 (Nat.zero_lt_succ _)
    simp only [Nat.add_zero, Nat.zero_mul, Nat.pow_zero, Nat.div_one, List.getElem_cons_zero] at h0
    obtain ⟨tr0, lsig0, hs0⟩ : ∃ tr0 lsig0, sStep startLayer remIdx ctr = (tr0, lsig0) := ⟨_, _, rfl⟩
    simp only [hs0, verifyUpperPoly] at h0 ⊢
    rcases h0 with ⟨hTr0, hv0⟩
    rw [hTr0, hv0]
    dsimp only
    have hNextSub :
        rootAt startLayer (remIdx / 2 ^ subH) = rootAt ((startLayer + 1) - 1) (remIdx / 2 ^ subH) :=
      congrArg (fun l => rootAt l (remIdx / 2 ^ subH)) (Nat.add_sub_cancel startLayer 1).symm
    rw [hNextSub]
    have hRestValid :
        ∀ (j : Nat) (hj : j < rest.length),
          let l := (startLayer + 1) + j
          let curRem := (remIdx / 2 ^ subH) / (2 ^ (j * subH))
          let (trOut, lsig) := sStep l curRem (rest[j]'hj)
          trOut = curRem / (2 ^ subH) ∧
          vStep l curRem (rootAt (l - 1) curRem) lsig =
            some (curRem / (2 ^ subH), rootAt l (curRem / (2 ^ subH))) := by
      intro j hj
      have hStep := hValid (j + 1) (Nat.succ_lt_succ hj)
      have hL : startLayer + (j + 1) = (startLayer + 1) + j := by omega
      have hDivEq :
          (remIdx / 2 ^ subH) / (2 ^ (j * subH)) = remIdx / (2 ^ ((j + 1) * subH)) := by
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
        have hExp : subH + j * subH = (j + 1) * subH := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
        rw [hExp]
      simpa only [hL, hDivEq, List.getElem_cons_succ] using hStep
    rw [verifyUpperPoly_signUpperPoly vStep sStep rootAt subH rest
          (startLayer + 1) (remIdx / 2 ^ subH) (by omega) hRestValid]
    have hEndL : (startLayer + 1) + rest.length - 1 = startLayer + (ctr :: rest).length - 1 := by
      simp only [List.length_cons]; omega
    have hEndRem :
        (remIdx / 2 ^ subH) / (2 ^ (rest.length * subH)) =
        remIdx / (2 ^ ((ctr :: rest).length * subH)) := by
      simp only [List.length_cons]
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
      have hExp : subH + rest.length * subH = (rest.length + 1) * subH := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
      rw [hExp]
    rw [hEndL, hEndRem]

private theorem verifyUpperLayers_signUpperLayersAux
    (geom : AggSigGeometry) (skSeed : Digest4) (pk : AggValidatorPk)
    (hChainsLe : geom.wotsChains ≤ 128)
    (ctrs : List Nat) (startLayer remIdx : Nat)
    (hPos : 0 < startLayer)
    (hValid : ∀ (j : Nat) (hj : j < ctrs.length),
      let l := startLayer + j
      let curRem := remIdx / (2 ^ (j * geom.subtreeHeight))
      let kpL := curRem % (2 ^ geom.subtreeHeight)
      let trL := curRem / (2 ^ geom.subtreeHeight)
      let childRt := honestSubtreeRoot geom skSeed pk.pkSeed (l - 1) curRem
      let hmsgL := computeHmsgDetTree pk l trL kpL (ctrs[j]'hj) childRt
      ∃ dsL, extractWotsDigitsChecked geom hmsgL = some dsL ∧ listNatSum dsL = geom.targetSum) :
    verifyUpperLayers geom pk startLayer remIdx
      (honestSubtreeRoot geom skSeed pk.pkSeed (startLayer - 1) remIdx)
      (signUpperLayersAux geom skSeed pk startLayer remIdx ctrs) =
    some (honestSubtreeRoot geom skSeed pk.pkSeed (startLayer + ctrs.length - 1)
            (remIdx / (2 ^ (ctrs.length * geom.subtreeHeight)))) := by
  unfold verifyUpperLayers signUpperLayersAux
  refine verifyUpperPoly_signUpperPoly _ _ (honestSubtreeRoot geom skSeed pk.pkSeed)
    geom.subtreeHeight ctrs startLayer remIdx hPos ?_
  intro j hj
  obtain ⟨dsL, hExtL, hSumL⟩ := hValid j hj
  dsimp only
  refine ⟨rfl, ?_⟩
  have hGetD :
      (extractWotsDigitsChecked geom
        (computeHmsgDetTree pk (startLayer + j)
          ((remIdx / 2 ^ (j * geom.subtreeHeight)) / 2 ^ geom.subtreeHeight)
          ((remIdx / 2 ^ (j * geom.subtreeHeight)) % 2 ^ geom.subtreeHeight)
          (ctrs[j]'hj)
          (honestSubtreeRoot geom skSeed pk.pkSeed (startLayer + j - 1)
            (remIdx / 2 ^ (j * geom.subtreeHeight))))).getD [] = dsL := by
    rw [hExtL]; rfl
  rw [hGetD, signWotsLayerWithDigits_tswCtr]
  have hKpLt :
      (remIdx / 2 ^ (j * geom.subtreeHeight)) % (2 ^ geom.subtreeHeight) < 2 ^ geom.subtreeHeight :=
    Nat.mod_lt _ (Nat.pow_pos (by decide))
  rw [verifyWotsLayer_signWotsLayerWithDigits geom skSeed pk hChainsLe
        (startLayer + j)
        ((remIdx / 2 ^ (j * geom.subtreeHeight)) / 2 ^ geom.subtreeHeight)
        ((remIdx / 2 ^ (j * geom.subtreeHeight)) % 2 ^ geom.subtreeHeight)
        (ctrs[j]'hj) hKpLt _ dsL hExtL hSumL]

private theorem signForsTreesAux_length (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (leafGlobalIdx t : Nat) (offs : List Nat) :
    (signForsTreesAux geom skSeed pkSeed leafGlobalIdx t offs).length = offs.length :=
  signForsPoly_length _ offs t

private theorem verifyForsPoly_signForsPoly {OP D : Type}
    (vStep : Nat → Nat → OP → Option D)
    (sStep : Nat → Nat → OP)
    (rootAt : Nat → D) :
    ∀ (offs : List Nat) (startT : Nat),
      (∀ off ∈ offs, ∀ t, vStep t off (sStep t off) = some (rootAt t)) →
      verifyForsPoly vStep offs (signForsPoly sStep offs startT) startT =
      some ((List.range offs.length).map fun i => rootAt (startT + i))
  | [], _ => fun _ => rfl
  | off :: offs, startT => fun hStep => by
    dsimp only [signForsPoly, verifyForsPoly]
    rw [hStep off (List.mem_cons_self ..) startT]
    rw [verifyForsPoly_signForsPoly vStep sStep rootAt offs (startT + 1)
          (fun o ho => hStep o (List.mem_cons_of_mem _ ho))]
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, Nat.add_zero]
    simp only [Option.some.injEq, List.cons.injEq]
    refine ⟨rfl, ?_⟩
    rw [List.map_map]
    congr 1
    funext i
    have hShift : startT + (i + 1) = startT + 1 + i := by omega
    simp [Function.comp, hShift]

private theorem verifyForsTreesAux_signForsTreesAux
    (geom : AggSigGeometry) (skSeed pkSeed : Digest4) (leafGlobalIdx : Nat)
    (offs : List Nat) (startT : Nat)
    (hLt : ∀ o ∈ offs, o < 2 ^ geom.forsHeight) :
    verifyForsTreesAux geom pkSeed leafGlobalIdx startT offs
      (signForsTreesAux geom skSeed pkSeed leafGlobalIdx startT offs) =
    some ((List.range offs.length).map fun i =>
      honestForsTreeRoot geom skSeed pkSeed leafGlobalIdx (startT + i)) := by
  unfold verifyForsTreesAux signForsTreesAux
  refine verifyForsPoly_signForsPoly _ _
    (honestForsTreeRoot geom skSeed pkSeed leafGlobalIdx) offs startT ?_
  intro off ho t
  have hOffLt : off < 2 ^ geom.forsHeight := hLt off ho
  dsimp only [verifySingleForsOpening]
  have hPathLen :
      (buildMerkleAuthPathAt domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
        (forsTreeNodeAddr geom leafGlobalIdx t)
        (honestForsLeaf geom skSeed pkSeed leafGlobalIdx t)
        geom.forsHeight 1 off).length = geom.forsHeight :=
    buildMerkleAuthPathAt_length _ _ _ _ _ _ _ _ _
  simp only [hOffLt, decide_true, hPathLen, beq_self_eq_true, Bool.and_self, ↓reduceIte]
  exact congrArg some
    (merkleWalkRoot_buildMerkleAuthPathAt domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
      (forsTreeNodeAddr geom leafGlobalIdx t) geom.forsHeight
      (honestForsLeaf geom skSeed pkSeed leafGlobalIdx t) 1 off hOffLt)

attribute [local irreducible]
  honestSubtreeRoot honestForsTreeRoot verifyWotsLayer signWotsLayerWithDigits
  verifyUpperLayers signUpperLayersAux verifyForsTreesAux signForsTreesAux

private theorem deriveStatelessLeafAndForsChecked_spec
    {geom : AggSigGeometry} {pk : AggValidatorPk} {rRand : Digest4} {mu : Digest5}
    {leafIdx : Nat} {indices : List Nat}
    (hExt : deriveStatelessLeafAndForsChecked geom pk rRand mu = some (leafIdx, indices)) :
    leafIdx < 2 ^ (geom.numLayers * geom.subtreeHeight) ∧
    indices.length = geom.forsTrees ∧
    (∀ idx ∈ indices, idx < 2 ^ geom.forsHeight) := by
  unfold deriveStatelessLeafAndForsChecked at hExt
  generalize statelessXofSpongeState pk rRand mu = st1 at hExt
  dsimp only at hExt
  cases hAll : ([st1.b0.x0, st1.b0.x1, st1.b0.x2, st1.b0.x3, st1.b1.x0, st1.b1.x1, st1.b1.x2].all
      (fun l => decide (l.val < 2 ^ 63)))
  · simp [hAll] at hExt
  · simp only [hAll, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hExt
    rcases hExt with ⟨hL, hI⟩
    subst hL hI
    refine ⟨Nat.mod_lt _ (Nat.pow_pos (by decide)), by simp, ?_⟩
    intro idx hMem
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hMem
    exact Nat.mod_lt _ (Nat.pow_pos (by decide))

attribute [local irreducible] deriveStatelessLeafAndForsChecked honestForsPk computeMessageMu

private theorem signAggNative_profile
    (geom : AggSigGeometry) (skSeed : Digest4) (pk : AggValidatorPk)
    (msg : List UInt8) (rRand : Digest4) (statefulLeafIdx layer0Ctr : Nat) (upperCtrs : List Nat) :
    (signAggNative geom skSeed pk msg rRand statefulLeafIdx layer0Ctr upperCtrs).profile = geom.profile :=
  rfl

private theorem signAggNative_layers_length
    (geom : AggSigGeometry) (skSeed : Digest4) (pk : AggValidatorPk)
    (msg : List UInt8) (rRand : Digest4) (statefulLeafIdx layer0Ctr : Nat) (upperCtrs : List Nat) :
    (signAggNative geom skSeed pk msg rRand statefulLeafIdx layer0Ctr upperCtrs).layers.length =
      upperCtrs.length + 1 := by
  unfold signAggNative
  dsimp only
  rw [List.length_cons, signUpperLayersAux_length]

private theorem signAggNative_stateful_eq
    (geom : AggSigGeometry) (skSeed : Digest4) (pk : AggValidatorPk)
    (msg : List UInt8) (rRand : Digest4) (statefulLeafIdx layer0Ctr : Nat) (upperCtrs : List Nat)
    (hFors0 : (geom.forsTrees == 0) = true) :
    signAggNative geom skSeed pk msg rRand statefulLeafIdx layer0Ctr upperCtrs =
      let mu := computeMessageMu pk msg
      let kp0 := statefulLeafIdx % (2 ^ geom.subtreeHeight)
      let tr0 := statefulLeafIdx / (2 ^ geom.subtreeHeight)
      let hmsg0 := computeHmsgStateful pk rRand mu kp0 layer0Ctr
      let digits0 := (extractWotsDigitsChecked geom hmsg0).getD []
      { profile := geom.profile
        rRand := rRand
        statefulLeafIdx := statefulLeafIdx
        forsOpenings := []
        layers := signWotsLayerWithDigits geom skSeed pk.pkSeed 0 tr0 kp0 layer0Ctr digits0 ::
                  signUpperLayersAux geom skSeed pk 1 tr0 upperCtrs } := by
  unfold signAggNative
  simp only [hFors0, ↓reduceIte]

private theorem signAggNative_stateless_eq
    (geom : AggSigGeometry) (skSeed : Digest4) (pk : AggValidatorPk)
    (msg : List UInt8) (rRand : Digest4) (statefulLeafIdx layer0Ctr : Nat) (upperCtrs : List Nat)
    (idx : Nat) (forsIndices : List Nat)
    (hFors0 : (geom.forsTrees == 0) = false)
    (hXof : deriveStatelessLeafAndForsChecked geom pk rRand (computeMessageMu pk msg) = some (idx, forsIndices)) :
    signAggNative geom skSeed pk msg rRand statefulLeafIdx layer0Ctr upperCtrs =
      let kp0 := idx % (2 ^ geom.subtreeHeight)
      let tr0 := idx / (2 ^ geom.subtreeHeight)
      let hmsg0 := computeHmsgDetTree pk 0 tr0 kp0 layer0Ctr (honestForsPk geom skSeed pk.pkSeed idx)
      let digits0 := (extractWotsDigitsChecked geom hmsg0).getD []
      { profile := geom.profile
        rRand := rRand
        statefulLeafIdx := 0
        forsOpenings := signForsTreesAux geom skSeed pk.pkSeed idx 0 forsIndices
        layers := signWotsLayerWithDigits geom skSeed pk.pkSeed 0 tr0 kp0 layer0Ctr digits0 ::
                  signUpperLayersAux geom skSeed pk 1 tr0 upperCtrs } := by
  unfold signAggNative
  simp only [hFors0, Bool.false_eq_true, ↓reduceIte, hXof]

attribute [local irreducible] signAggNative

private theorem honestForsPk_def (geom : AggSigGeometry) (skSeed pkSeed : Digest4) (leafGlobalIdx : Nat) :
    compressForsRootsSponge geom pkSeed leafGlobalIdx
      ((List.range geom.forsTrees).map fun i => honestForsTreeRoot geom skSeed pkSeed leafGlobalIdx i) =
    honestForsPk geom skSeed pkSeed leafGlobalIdx := by
  unfold honestForsPk
  rfl

attribute [local irreducible] verifyAggNativeSigStateful verifyAggNativeSigStateless verifyAndRecoverForsPk

private theorem verifyAggNativeSig_stateful_of_ok
    (geom : AggSigGeometry) (pk : AggValidatorPk) (msg : List UInt8) (rRand : Digest4)
    (statefulLeafIdx : Nat) (lsig0 : WotsLayerSig) (upperLayers : List WotsLayerSig)
    (root0 : Digest4)
    (hWf : geom.wellFormed = true)
    (hPkProf : pk.profile = geom.profile)
    (hLen : upperLayers.length + 1 = geom.numLayers)
    (hFors0 : (geom.forsTrees == 0) = true)
    (hLeafLt : statefulLeafIdx < 2 ^ (geom.numLayers * geom.subtreeHeight))
    (hW0 : verifyWotsLayer geom pk 0 (statefulLeafIdx / 2 ^ geom.subtreeHeight)
             (statefulLeafIdx % 2 ^ geom.subtreeHeight)
             (computeHmsgStateful pk rRand (computeMessageMu pk msg)
               (statefulLeafIdx % 2 ^ geom.subtreeHeight) lsig0.tswCtr) lsig0 = some root0)
    (hUp : verifyUpperLayers geom pk 1 (statefulLeafIdx / 2 ^ geom.subtreeHeight) root0 upperLayers =
             some pk.pkRoot) :
    verifyAggNativeSig geom pk msg
      { profile := geom.profile, rRand := rRand, statefulLeafIdx := statefulLeafIdx,
        forsOpenings := [], layers := lsig0 :: upperLayers } = true := by
  unfold verifyAggNativeSig
  simp only [hWf, hPkProf, List.length_cons, hLen, bne_self_eq_false, Bool.not_true, Bool.or_self,
    Bool.false_eq_true, ↓reduceIte, hFors0]
  unfold verifyAggNativeSigStateful
  simp only [List.isEmpty_nil, Bool.not_true, hLeafLt, decide_true, Bool.or_self,
    Bool.false_eq_true, ↓reduceIte, hW0, hUp, beq_self_eq_true]

private theorem verifyAggNativeSig_stateless_of_ok
    (geom : AggSigGeometry) (pk : AggValidatorPk) (msg : List UInt8) (rRand : Digest4)
    (forsOps : List AggForsTreeOpening) (lsig0 : WotsLayerSig) (upperLayers : List WotsLayerSig)
    (leafIdx : Nat) (forsIndices : List Nat) (forsPk root0 : Digest4)
    (hWf : geom.wellFormed = true)
    (hPkProf : pk.profile = geom.profile)
    (hLen : upperLayers.length + 1 = geom.numLayers)
    (hFors0 : (geom.forsTrees == 0) = false)
    (hXof : deriveStatelessLeafAndForsChecked geom pk rRand (computeMessageMu pk msg) =
              some (leafIdx, forsIndices))
    (hForsVer : verifyAndRecoverForsPk geom pk.pkSeed leafIdx forsIndices forsOps = some forsPk)
    (hW0 : verifyWotsLayer geom pk 0 (leafIdx / 2 ^ geom.subtreeHeight)
             (leafIdx % 2 ^ geom.subtreeHeight)
             (computeHmsgDetTree pk 0 (leafIdx / 2 ^ geom.subtreeHeight)
               (leafIdx % 2 ^ geom.subtreeHeight) lsig0.tswCtr forsPk) lsig0 = some root0)
    (hUp : verifyUpperLayers geom pk 1 (leafIdx / 2 ^ geom.subtreeHeight) root0 upperLayers =
             some pk.pkRoot) :
    verifyAggNativeSig geom pk msg
      { profile := geom.profile, rRand := rRand, statefulLeafIdx := 0,
        forsOpenings := forsOps, layers := lsig0 :: upperLayers } = true := by
  unfold verifyAggNativeSig
  simp only [hWf, hPkProf, List.length_cons, hLen, bne_self_eq_false, Bool.not_true, Bool.or_self,
    Bool.false_eq_true, ↓reduceIte, hFors0]
  delta verifyAggNativeSigStateless
  exact evalStatelessFlow_ok _ _ _ _ _ leafIdx forsIndices forsPk root0 pk.pkRoot
    hXof hForsVer hW0 hUp (beq_iff_eq.mpr rfl)

private theorem wellFormed_chainsLe (geom : AggSigGeometry) (hWf : geom.wellFormed = true) :
    geom.wotsChains ≤ 128 := by
  unfold AggSigGeometry.wellFormed at hWf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hWf
  exact hWf.1.1.1.1.1.1.2

/-- **Packed 4-Limb `AggNativeSignature` Completeness (`aggNativeSig_completeness`)**:
    For every well-formed `AggSigGeometry` (both `XmssPoseidon2` stateful XMSS and
    `CorduroyPoseidon2` stateless FORS + 16-layer hypertree) and any `ValidSigningCtrs` witness
    bundle, `signAggNative` produces a signature accepted by `verifyAggNativeSig`! -/
theorem aggNativeSig_completeness
    (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (msg : List UInt8) (rRand : Digest4) (statefulLeafIdx : Nat)
    (hWf : geom.wellFormed = true)
    (ctrs : ValidSigningCtrs geom skSeed (deriveAggPublicKey geom skSeed pkSeed) msg rRand statefulLeafIdx) :
    verifyAggNativeSig geom (deriveAggPublicKey geom skSeed pkSeed) msg
      (signAggNative geom skSeed (deriveAggPublicKey geom skSeed pkSeed)
        msg rRand statefulLeafIdx ctrs.layer0Ctr ctrs.upperCtrs) = true := by
  have hChainsLe : geom.wotsChains ≤ 128 := wellFormed_chainsLe geom hWf
  have hPowSubPos : 0 < 2 ^ geom.subtreeHeight := Nat.pow_pos (by decide)
  cases hFors0 : (geom.forsTrees == 0)
  · -- Stateless FORS + Hypertree (`geom.forsTrees ≠ 0`)
    have hForsNe : geom.forsTrees ≠ 0 := by
      intro hZ; rw [hZ] at hFors0; simp at hFors0
    have hXofSome := ctrs.statelessXofOk hForsNe
    cases hXof : deriveStatelessLeafAndForsChecked geom (deriveAggPublicKey geom skSeed pkSeed) rRand
                   (computeMessageMu (deriveAggPublicKey geom skSeed pkSeed) msg) with
    | none => exact False.elim (hXofSome hXof)
    | some pair =>
      rcases pair with ⟨leafIdx, forsIndices⟩
      obtain ⟨hLeafLt, hForsLen, hForsAllLt⟩ := deriveStatelessLeafAndForsChecked_spec hXof
      have hL0 := ctrs.layer0Valid
      simp only [hFors0, Bool.false_eq_true, ↓reduceIte, hXof] at hL0
      obtain ⟨ds0, hExt0, hSum0⟩ := hL0
      have hUpperV :
          ∀ (j : Nat) (hj : j < ctrs.upperCtrs.length),
            let l := 1 + j
            let curRem := (leafIdx / 2 ^ geom.subtreeHeight) / (2 ^ (j * geom.subtreeHeight))
            let kpL := curRem % (2 ^ geom.subtreeHeight)
            let trL := curRem / (2 ^ geom.subtreeHeight)
            let childRt := honestSubtreeRoot geom skSeed (deriveAggPublicKey geom skSeed pkSeed).pkSeed (l - 1) curRem
            let hmsgL := computeHmsgDetTree (deriveAggPublicKey geom skSeed pkSeed) l trL kpL (ctrs.upperCtrs[j]'hj) childRt
            ∃ dsL, extractWotsDigitsChecked geom hmsgL = some dsL ∧ listNatSum dsL = geom.targetSum := by
        intro j hj
        have hU := ctrs.upperValid j hj
        simp only [hFors0, Bool.false_eq_true, ↓reduceIte, hXof] at hU
        have hDiv :
            (leafIdx / 2 ^ geom.subtreeHeight) / (2 ^ (j * geom.subtreeHeight)) =
            leafIdx / (2 ^ ((j + 1) * geom.subtreeHeight)) := by
          rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
          have hE : geom.subtreeHeight + j * geom.subtreeHeight = (j + 1) * geom.subtreeHeight := by
            rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
          rw [hE]
        have h1j : 1 + j = j + 1 := Nat.add_comm 1 j
        simpa only [h1j, Nat.add_sub_cancel, hDiv] using hU
      rw [signAggNative_stateless_eq geom skSeed (deriveAggPublicKey geom skSeed pkSeed)
            msg rRand statefulLeafIdx ctrs.layer0Ctr ctrs.upperCtrs leafIdx forsIndices hFors0 hXof]
      refine verifyAggNativeSig_stateless_of_ok geom (deriveAggPublicKey geom skSeed pkSeed)
        msg rRand _ _ _ leafIdx forsIndices
        (honestForsPk geom skSeed (deriveAggPublicKey geom skSeed pkSeed).pkSeed leafIdx)
        (honestSubtreeRoot geom skSeed (deriveAggPublicKey geom skSeed pkSeed).pkSeed 0
          (leafIdx / 2 ^ geom.subtreeHeight))
        hWf rfl ?_ hFors0 hXof ?_ ?_ ?_
      · rw [signUpperLayersAux_length]; exact ctrs.lenUpper
      · unfold verifyAndRecoverForsPk
        have hOpsLen :
            (signForsTreesAux geom skSeed (deriveAggPublicKey geom skSeed pkSeed).pkSeed leafIdx 0 forsIndices).length =
            geom.forsTrees := by
          rw [signForsTreesAux_length, hForsLen]
        simp only [hForsLen, hOpsLen, beq_self_eq_true, Bool.and_self, ↓reduceIte]
        rw [verifyForsTreesAux_signForsTreesAux geom skSeed (deriveAggPublicKey geom skSeed pkSeed).pkSeed
              leafIdx forsIndices 0 hForsAllLt]
        simp only [Nat.zero_add, hForsLen, Option.some.injEq]
        exact honestForsPk_def geom skSeed (deriveAggPublicKey geom skSeed pkSeed).pkSeed leafIdx
      · have hGetD0 :
            (extractWotsDigitsChecked geom
              (computeHmsgDetTree (deriveAggPublicKey geom skSeed pkSeed) 0
                (leafIdx / 2 ^ geom.subtreeHeight) (leafIdx % 2 ^ geom.subtreeHeight) ctrs.layer0Ctr
                (honestForsPk geom skSeed (deriveAggPublicKey geom skSeed pkSeed).pkSeed leafIdx))).getD [] = ds0 := by
          rw [hExt0]; rfl
        rw [hGetD0, signWotsLayerWithDigits_tswCtr]
        exact verifyWotsLayer_signWotsLayerWithDigits geom skSeed (deriveAggPublicKey geom skSeed pkSeed)
          hChainsLe 0 (leafIdx / 2 ^ geom.subtreeHeight) (leafIdx % 2 ^ geom.subtreeHeight)
          ctrs.layer0Ctr (Nat.mod_lt _ hPowSubPos) _ ds0 hExt0 hSum0
      · have hSub10 :
            honestSubtreeRoot geom skSeed (deriveAggPublicKey geom skSeed pkSeed).pkSeed 0
              (leafIdx / 2 ^ geom.subtreeHeight) =
            honestSubtreeRoot geom skSeed (deriveAggPublicKey geom skSeed pkSeed).pkSeed (1 - 1)
              (leafIdx / 2 ^ geom.subtreeHeight) := rfl
        rw [hSub10, verifyUpperLayers_signUpperLayersAux geom skSeed (deriveAggPublicKey geom skSeed pkSeed)
              hChainsLe ctrs.upperCtrs 1 (leafIdx / 2 ^ geom.subtreeHeight) (by decide) hUpperV]
        have hTopLayer : 1 + ctrs.upperCtrs.length - 1 = geom.numLayers - 1 := by
          have hL := ctrs.lenUpper; omega
        have hTopTree :
            (leafIdx / 2 ^ geom.subtreeHeight) / (2 ^ (ctrs.upperCtrs.length * geom.subtreeHeight)) = 0 := by
          rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
          have hE : geom.subtreeHeight + ctrs.upperCtrs.length * geom.subtreeHeight =
              geom.numLayers * geom.subtreeHeight := by
            rw [← ctrs.lenUpper, Nat.add_mul, Nat.one_mul, Nat.add_comm]
          rw [hE]
          exact Nat.div_eq_of_lt hLeafLt
        rw [hTopLayer, hTopTree]
        rfl
  · -- Stateful XMSS (`geom.forsTrees = 0`)
    have hForsEq0 : geom.forsTrees = 0 := eq_of_beq hFors0
    have hLeafLt := ctrs.leafInRange hForsEq0
    have hL0 := ctrs.layer0Valid
    simp only [hFors0, ↓reduceIte] at hL0
    obtain ⟨ds0, hExt0, hSum0⟩ := hL0
    have hUpperV :
        ∀ (j : Nat) (hj : j < ctrs.upperCtrs.length),
          let l := 1 + j
          let curRem := (statefulLeafIdx / 2 ^ geom.subtreeHeight) / (2 ^ (j * geom.subtreeHeight))
          let kpL := curRem % (2 ^ geom.subtreeHeight)
          let trL := curRem / (2 ^ geom.subtreeHeight)
          let childRt := honestSubtreeRoot geom skSeed (deriveAggPublicKey geom skSeed pkSeed).pkSeed (l - 1) curRem
          let hmsgL := computeHmsgDetTree (deriveAggPublicKey geom skSeed pkSeed) l trL kpL (ctrs.upperCtrs[j]'hj) childRt
          ∃ dsL, extractWotsDigitsChecked geom hmsgL = some dsL ∧ listNatSum dsL = geom.targetSum := by
      intro j hj
      have hU := ctrs.upperValid j hj
      simp only [hFors0, ↓reduceIte] at hU
      have hDiv :
          (statefulLeafIdx / 2 ^ geom.subtreeHeight) / (2 ^ (j * geom.subtreeHeight)) =
          statefulLeafIdx / (2 ^ ((j + 1) * geom.subtreeHeight)) := by
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
        have hE : geom.subtreeHeight + j * geom.subtreeHeight = (j + 1) * geom.subtreeHeight := by
          rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
        rw [hE]
      have h1j : 1 + j = j + 1 := Nat.add_comm 1 j
      simpa only [h1j, Nat.add_sub_cancel, hDiv] using hU
    rw [signAggNative_stateful_eq geom skSeed (deriveAggPublicKey geom skSeed pkSeed)
          msg rRand statefulLeafIdx ctrs.layer0Ctr ctrs.upperCtrs hFors0]
    refine verifyAggNativeSig_stateful_of_ok geom (deriveAggPublicKey geom skSeed pkSeed)
      msg rRand statefulLeafIdx _ _
      (honestSubtreeRoot geom skSeed (deriveAggPublicKey geom skSeed pkSeed).pkSeed 0
        (statefulLeafIdx / 2 ^ geom.subtreeHeight))
      hWf rfl ?_ hFors0 hLeafLt ?_ ?_
    · rw [signUpperLayersAux_length]; exact ctrs.lenUpper
    · have hGetD0 :
          (extractWotsDigitsChecked geom
            (computeHmsgStateful (deriveAggPublicKey geom skSeed pkSeed) rRand
              (computeMessageMu (deriveAggPublicKey geom skSeed pkSeed) msg)
              (statefulLeafIdx % 2 ^ geom.subtreeHeight) ctrs.layer0Ctr)).getD [] = ds0 := by
        rw [hExt0]; rfl
      rw [hGetD0, signWotsLayerWithDigits_tswCtr]
      exact verifyWotsLayer_signWotsLayerWithDigits geom skSeed (deriveAggPublicKey geom skSeed pkSeed)
        hChainsLe 0 (statefulLeafIdx / 2 ^ geom.subtreeHeight) (statefulLeafIdx % 2 ^ geom.subtreeHeight)
        ctrs.layer0Ctr (Nat.mod_lt _ hPowSubPos) _ ds0 hExt0 hSum0
    · have hSub10 :
          honestSubtreeRoot geom skSeed (deriveAggPublicKey geom skSeed pkSeed).pkSeed 0
            (statefulLeafIdx / 2 ^ geom.subtreeHeight) =
          honestSubtreeRoot geom skSeed (deriveAggPublicKey geom skSeed pkSeed).pkSeed (1 - 1)
            (statefulLeafIdx / 2 ^ geom.subtreeHeight) := rfl
      rw [hSub10, verifyUpperLayers_signUpperLayersAux geom skSeed (deriveAggPublicKey geom skSeed pkSeed)
            hChainsLe ctrs.upperCtrs 1 (statefulLeafIdx / 2 ^ geom.subtreeHeight) (by decide) hUpperV]
      have hTopLayer : 1 + ctrs.upperCtrs.length - 1 = geom.numLayers - 1 := by
        have hL := ctrs.lenUpper; omega
      have hTopTree :
          (statefulLeafIdx / 2 ^ geom.subtreeHeight) / (2 ^ (ctrs.upperCtrs.length * geom.subtreeHeight)) = 0 := by
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
        have hE : geom.subtreeHeight + ctrs.upperCtrs.length * geom.subtreeHeight =
            geom.numLayers * geom.subtreeHeight := by
          rw [← ctrs.lenUpper, Nat.add_mul, Nat.one_mul, Nat.add_comm]
        rw [hE]
        exact Nat.div_eq_of_lt hLeafLt
      rw [hTopLayer, hTopTree]
      rfl

/-! ### Constructive Secret-Key-Anchored Forgery Extraction (`aggNativeSig_wots_merkle_soundness`) -/

/-- Collision in `compressWotsEndpointsSponge` (`T_ell` WOTS+C public-key compression). -/
structure WotsPkSpongeCollisionWitness (pkSeed : Digest4) where
  layer     : Nat
  treeIdx   : Nat
  kpIdx     : Nat
  eps1      : List Digest4
  eps2      : List Digest4
  neInputs  : eps1 ≠ eps2
  spongeEq  : compressWotsEndpointsSponge pkSeed layer treeIdx kpIdx eps1 =
              compressWotsEndpointsSponge pkSeed layer treeIdx kpIdx eps2

/-- Collision in a single domain-separated WOTS+C chain step (`wotsStepHash`). -/
structure WotsStepCollisionWitness (pkSeed : Digest4) where
  layer    : Nat
  treeIdx  : Nat
  kpIdx    : Nat
  chainIdx : Nat
  stepIdx  : Nat
  in1      : Digest4
  in2      : Digest4
  neInputs : in1 ≠ in2
  stepEq   : wotsStepHash pkSeed in1 layer treeIdx kpIdx chainIdx stepIdx =
             wotsStepHash pkSeed in2 layer treeIdx kpIdx chainIdx stepIdx

/-- Collision in `forsLeafHash`. -/
structure ForsLeafCollisionWitness (geom : AggSigGeometry) (pkSeed : Digest4) where
  leafGlobalIdx : Nat
  treeIdx       : Nat
  leafOffset    : Nat
  val1          : Digest4
  val2          : Digest4
  neInputs      : val1 ≠ val2
  hashEq        : forsLeafHash geom pkSeed val1 leafGlobalIdx treeIdx leafOffset =
                  forsLeafHash geom pkSeed val2 leafGlobalIdx treeIdx leafOffset

/-- Collision in `compressForsRootsSponge`. -/
structure ForsRootsSpongeCollisionWitness (geom : AggSigGeometry) (pkSeed : Digest4) where
  leafGlobalIdx : Nat
  roots1        : List Digest4
  roots2        : List Digest4
  neInputs      : roots1 ≠ roots2
  spongeEq      : compressForsRootsSponge geom pkSeed leafGlobalIdx roots1 =
                  compressForsRootsSponge geom pkSeed leafGlobalIdx roots2

/-- Concrete record of a previously queried WOTS+C OTS keypair `(layer, treeIdx, kpIdx)`. -/
structure QueriedWotsEntry where
  tswCtr     : Nat
  rRand      : Digest4
  queriedMsg : List UInt8
  digits     : List Nat
  deriving DecidableEq, Repr

/-- Oracle mapping `(layer, treeIdx, kpIdx)` to an optional `QueriedWotsEntry`. -/
abbrev QueriedWotsDigitsOracle := Nat → Nat → Nat → Option QueriedWotsEntry

/-- Secret-key-anchored WOTS+C chain preimage break (`0` unconstrained fields):
    1. Either recovers the exact secret-derived chain node `x_c^{(d)}` at `d < 3` on an OTS
       `(layer, treeIdx, kpIdx)` that was **never** queried (`qWots layer treeIdx kpIdx = none`),
    2. Or on a queried OTS (`qWots layer treeIdx kpIdx = some entry`) inverts `wotsStepHash` **1 step
       backward** behind the revealed chain position `entry.digits[c]` (`≥ 1`), recovering
       `x_c^{(entry.digits[c] - 1)}`! -/
inductive WotsSecretChainBreak (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (qWots : QueriedWotsDigitsOracle) : Type where
  | unqueriedChainPreimage
      (layer treeIdx kpIdx chainIdx digit : Nat)
      (forgedNode : Digest4)
      (hFreshOts : qWots layer treeIdx kpIdx = none)
      (hChainLt : chainIdx < geom.wotsChains)
      (hDigitLt : digit < 3)
      (hExactSecret :
        forgedNode = wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx 0 digit
          (wotsSecretStart skSeed pkSeed layer treeIdx kpIdx chainIdx))
      (hWalkToPub :
        wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx digit (3 - digit) forgedNode =
          wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx 0 3
            (wotsSecretStart skSeed pkSeed layer treeIdx kpIdx chainIdx))
  | queriedBackwardInversion
      (layer treeIdx kpIdx chainIdx : Nat)
      (entry : QueriedWotsEntry) (hCQ : chainIdx < entry.digits.length)
      (preNode : Digest4)
      (hQueried : qWots layer treeIdx kpIdx = some entry)
      (hDqPos : 1 ≤ entry.digits[chainIdx]'hCQ)
      (hExactPre :
        preNode = wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx 0 ((entry.digits[chainIdx]'hCQ) - 1)
          (wotsSecretStart skSeed pkSeed layer treeIdx kpIdx chainIdx))
      (hStepInverts :
        wotsStepHash pkSeed preNode layer treeIdx kpIdx chainIdx ((entry.digits[chainIdx]'hCQ) - 1) =
          wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx 0 (entry.digits[chainIdx]'hCQ)
            (wotsSecretStart skSeed pkSeed layer treeIdx kpIdx chainIdx))

/-- Secret-key-anchored unqueried FORS leaf recovery (`op.secretVal = forsSecretVal ...` outside `revealedFors`). -/
structure ForsUnqueriedSecretBreak (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (revealedFors : List (Nat × Nat × Nat)) where
  leafGlobalIdx : Nat
  treeIdx       : Nat
  leafOffset    : Nat
  secretVal     : Digest4
  notRevealed   : (leafGlobalIdx, treeIdx, leafOffset) ∉ revealedFors
  exactSecret   : secretVal = forsSecretVal geom skSeed pkSeed leafGlobalIdx treeIdx leafOffset

/-- Codeword or `mu` collision witness when a queried OTS receives identical WOTS+C digits on a distinct input. -/
inductive HmsgOrMuCollisionBreak (geom : AggSigGeometry) (pk : AggValidatorPk) : Type where
  | muPoseidon2Collision (col : HashCollisionWitness poseidon2Hash32)
  | statefulCodewordCollision
      (kpIdx : Nat) (r1 r2 : Digest4) (mu1 mu2 : Digest5) (ctr1 ctr2 : Nat) (digits : List Nat)
      (hNe : (r1, mu1, ctr1) ≠ (r2, mu2, ctr2))
      (hExt1 : extractWotsDigitsChecked geom (computeHmsgStateful pk r1 mu1 kpIdx ctr1) = some digits)
      (hExt2 : extractWotsDigitsChecked geom (computeHmsgStateful pk r2 mu2 kpIdx ctr2) = some digits)
  | detTreeCodewordCollision
      (layer treeIdx kpIdx ctr1 ctr2 : Nat) (rt1 rt2 : Digest4) (digits : List Nat)
      (hNe : (ctr1, rt1) ≠ (ctr2, rt2))
      (hExt1 : extractWotsDigitsChecked geom (computeHmsgDetTree pk layer treeIdx kpIdx ctr1 rt1) = some digits)
      (hExt2 : extractWotsDigitsChecked geom (computeHmsgDetTree pk layer treeIdx kpIdx ctr2 rt2) = some digits)

/-- Stateless FORS multi-target subset-cover event (only inhabited when `geom.forsTrees > 0` and all
    `k` derived FORS leaves were previously revealed across adaptive signing queries). -/
structure StatelessForsSubsetCoverBreak (geom : AggSigGeometry) (pk : AggValidatorPk)
    (msg : List UInt8) (rRand : Digest4) (revealedFors : List (Nat × Nat × Nat)) where
  forsPos       : 0 < geom.forsTrees
  leafGlobalIdx : Nat
  indices       : List Nat
  xofEq         : deriveStatelessLeafAndForsChecked geom pk rRand (computeMessageMu pk msg) =
                  some (leafGlobalIdx, indices)
  allCovered    : ∀ (t : Nat) (ht : t < indices.length), (leafGlobalIdx, t, indices[t]'ht) ∈ revealedFors

/-- Complete constructive forgery break sum for `AggNativeSignature` (`sig.rs`). -/
inductive AggNativeForgeryBreak (geom : AggSigGeometry) (skSeed : Digest4) (pk : AggValidatorPk)
    (msg : List UInt8) (rRand : Digest4)
    (qWots : QueriedWotsDigitsOracle) (revealedFors : List (Nat × Nat × Nat)) : Type where
  | merkleCollision      (w : MerkleNodeCollisionWitness pk.pkSeed)
  | wotsPkCollision      (w : WotsPkSpongeCollisionWitness pk.pkSeed)
  | wotsStepCollision    (w : WotsStepCollisionWitness pk.pkSeed)
  | wotsSecretChainBreak (w : WotsSecretChainBreak geom skSeed pk.pkSeed qWots)
  | forsLeafCollision    (w : ForsLeafCollisionWitness geom pk.pkSeed)
  | forsRootsCollision   (w : ForsRootsSpongeCollisionWitness geom pk.pkSeed)
  | forsUnqueriedSecret  (w : ForsUnqueriedSecretBreak geom skSeed pk.pkSeed revealedFors)
  | hmsgOrMuCollision    (w : HmsgOrMuCollisionBreak geom pk)
  | statelessForsCover   (w : StatelessForsSubsetCoverBreak geom pk msg rRand revealedFors)

private structure PolyStepCollision {σ : Type} (step : Nat → σ → σ) where
  stepIdx  : Nat
  in1      : σ
  in2      : σ
  neInputs : in1 ≠ in2
  stepEq   : step stepIdx in1 = step stepIdx in2

private def extractNatIterEqOrCol {σ : Type} [DecidableEq σ] (step : Nat → σ → σ) :
    ∀ (steps startStep : Nat) (v1 v2 : σ),
      natIterAt step steps startStep v1 = natIterAt step steps startStep v2 →
      PSum (v1 = v2) (PolyStepCollision step)
  | 0, _, _, _, hEq => .inl hEq
  | steps + 1, startStep, v1, v2, hEq =>
    if hIn : v1 = v2 then
      .inl hIn
    else
      let nx1 := step startStep v1
      let nx2 := step startStep v2
      if hStep : nx1 = nx2 then
        .inr { stepIdx := startStep, in1 := v1, in2 := v2, neInputs := hIn, stepEq := hStep }
      else
        match extractNatIterEqOrCol step steps (startStep + 1) nx1 nx2 hEq with
        | .inl hNxEq => False.elim (hStep hNxEq)
        | .inr col => .inr col

/-- Constructive step-by-step WOTS+C walk extractor: if two walks from
    `startStep` for `steps` iterations end at the same `Digest4`, either `v1 = v2` or an explicit
    `WotsStepCollisionWitness` occurred along the chain! -/
def extractChainWalkEqOrStepCollision (pkSeed : Digest4)
    (layer treeIdx kpIdx chainIdx steps startStep : Nat) (v1 v2 : Digest4)
    (hEq : wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx startStep steps v1 =
             wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx startStep steps v2) :
    PSum (v1 = v2) (WotsStepCollisionWitness pkSeed) :=
  match extractNatIterEqOrCol (fun stp v => wotsStepHash pkSeed v layer treeIdx kpIdx chainIdx stp)
          steps startStep v1 v2 hEq with
  | .inl h => .inl h
  | .inr col => .inr {
      layer    := layer
      treeIdx  := treeIdx
      kpIdx    := kpIdx
      chainIdx := chainIdx
      stepIdx  := col.stepIdx
      in1      := col.in1
      in2      := col.in2
      neInputs := col.neInputs
      stepEq   := col.stepEq
    }

private theorem recoverEndpointsPoly_length {D : Type} (walkFn : Nat → Nat → Nat → D → D) :
    ∀ (ds : List Nat) (chains : List D) (startC : Nat),
      ds.length = chains.length →
      (recoverEndpointsPoly walkFn ds chains startC).length = ds.length
  | [], [], _, _ => rfl
  | [], _ :: _, _, hLen => False.elim (Nat.succ_ne_zero _ hLen.symm)
  | _ :: _, [], _, hLen => False.elim (Nat.succ_ne_zero _ hLen)
  | _ :: ds, _ :: cs, startC, hLen => by
    dsimp only [recoverEndpointsPoly]
    rw [List.length_cons, recoverEndpointsPoly_length walkFn ds cs (startC + 1) (Nat.succ.inj hLen)]
    rfl

private theorem recoverEndpointsPoly_getElem {D : Type} (walkFn : Nat → Nat → Nat → D → D) :
    ∀ (ds : List Nat) (chains : List D) (startC idx : Nat)
      (hLen : ds.length = chains.length)
      (hIdx : idx < ds.length)
      (hOut : idx < (recoverEndpointsPoly walkFn ds chains startC).length),
      (recoverEndpointsPoly walkFn ds chains startC)[idx]'hOut =
        walkFn (startC + idx) (ds[idx]'hIdx) (3 - (ds[idx]'hIdx)) (chains[idx]'(hLen ▸ hIdx))
  | [], _, _, _, _, hIdx, _ => False.elim (by simp at hIdx)
  | _ :: _, [], _, _, hLen, _, _ => False.elim (by simp at hLen)
  | _ :: _, _ :: _, _, 0, _, _, _ => rfl
  | _ :: ds, _ :: cs, startC, idx + 1, hLen, hIdx, hOut => by
    have ih := recoverEndpointsPoly_getElem walkFn ds cs (startC + 1) idx
      (Nat.succ.inj hLen) (Nat.lt_of_succ_lt_succ hIdx) (Nat.lt_of_succ_lt_succ hOut)
    have hShift : startC + 1 + idx = startC + (idx + 1) := by omega
    rw [hShift] at ih
    exact ih

private theorem recoverAggWotsEndpoints_length (pkSeed : Digest4) (layer treeIdx kpIdx startC : Nat)
    (ds : List Nat) (chains : List Digest4) (hLen : ds.length = chains.length) :
    (recoverAggWotsEndpoints pkSeed layer treeIdx kpIdx startC ds chains).length = ds.length :=
  recoverEndpointsPoly_length _ ds chains startC hLen

private theorem recoverAggWotsEndpoints_getElem (pkSeed : Digest4) (layer treeIdx kpIdx : Nat)
    (ds : List Nat) (chains : List Digest4) (startC idx : Nat)
    (hLen : ds.length = chains.length)
    (hIdx : idx < ds.length)
    (hOut : idx < (recoverAggWotsEndpoints pkSeed layer treeIdx kpIdx startC ds chains).length) :
    (recoverAggWotsEndpoints pkSeed layer treeIdx kpIdx startC ds chains)[idx]'hOut =
      wotsChainWalk pkSeed layer treeIdx kpIdx (startC + idx)
        (ds[idx]'hIdx) (3 - (ds[idx]'hIdx)) (chains[idx]'(hLen ▸ hIdx)) :=
  recoverEndpointsPoly_getElem _ ds chains startC idx hLen hIdx hOut

private theorem bytes32ToDigest5_vals_of_len32 {bs : List UInt8} (hLen : bs.length = 32) :
    (bytes32ToDigest5 bs).limb0.val = ofBE (bs.take 7) ∧
    (bytes32ToDigest5 bs).limb1.val = ofBE ((bs.drop 7).take 7) ∧
    (bytes32ToDigest5 bs).limb2.val = ofBE ((bs.drop 14).take 7) ∧
    (bytes32ToDigest5 bs).limb3.val = ofBE ((bs.drop 21).take 7) ∧
    (bytes32ToDigest5 bs).limb4.val = ofBE ((bs.drop 28).take 4) := by
  let b := (bs ++ List.replicate (32 - bs.length) (0 : UInt8)).take 32
  have hB : b = bs := by
    dsimp only [b]
    rw [hLen]
    simp only [Nat.sub_self, List.replicate_zero, List.append_nil]
    exact List.take_of_length_le (Nat.le_of_eq hLen)
  have e0 : (bytes32ToDigest5 bs).limb0.val = ofBE (b.take 7) := rfl
  have e1 : (bytes32ToDigest5 bs).limb1.val = ofBE ((b.drop 7).take 7) := rfl
  have e2 : (bytes32ToDigest5 bs).limb2.val = ofBE ((b.drop 14).take 7) := rfl
  have e3 : (bytes32ToDigest5 bs).limb3.val = ofBE ((b.drop 21).take 7) := rfl
  have e4 : (bytes32ToDigest5 bs).limb4.val = ofBE ((b.drop 28).take 4) := rfl
  rw [hB] at e0 e1 e2 e3 e4
  exact ⟨e0, e1, e2, e3, e4⟩

private theorem unpack_bytes32ToDigest5_of_len32 {bs : List UInt8} (hLen : bs.length = 32) :
    be 7 (bytes32ToDigest5 bs).limb0.val ++
    be 7 (bytes32ToDigest5 bs).limb1.val ++
    be 7 (bytes32ToDigest5 bs).limb2.val ++
    be 7 (bytes32ToDigest5 bs).limb3.val ++
    be 4 (bytes32ToDigest5 bs).limb4.val = bs := by
  obtain ⟨e0, e1, e2, e3, e4⟩ := bytes32ToDigest5_vals_of_len32 hLen
  rw [e0, e1, e2, e3, e4]
  have hBeOfBE : ∀ (xs : List UInt8) (k : Nat), xs.length = k → be k (ofBE xs) = xs := by
    intro xs k hk
    subst hk
    simpa [ofBE, be] using be_foldl_acc xs 0 0
  rw [hBeOfBE (bs.take 7) 7 (by simp [hLen]),
      hBeOfBE ((bs.drop 7).take 7) 7 (by simp [hLen]),
      hBeOfBE ((bs.drop 14).take 7) 7 (by simp [hLen]),
      hBeOfBE ((bs.drop 21).take 7) 7 (by simp [hLen]),
      hBeOfBE ((bs.drop 28).take 4) 4 (by simp [hLen])]
  have hSplit32 :
      bs.take 7 ++ ((bs.drop 7).take 7 ++ ((bs.drop 14).take 7 ++ ((bs.drop 21).take 7 ++ (bs.drop 28).take 4))) =
      bs := by
    have h28 : (bs.drop 28).take 4 = bs.drop 28 :=
      List.take_of_length_le (by simp [hLen])
    have h21 : (bs.drop 21).take 7 ++ bs.drop 28 = bs.drop 21 := by
      have hDrop : (bs.drop 21).drop 7 = bs.drop 28 := by rw [List.drop_drop]
      rw [← hDrop, List.take_append_drop]
    have h14 : (bs.drop 14).take 7 ++ bs.drop 21 = bs.drop 14 := by
      have hDrop : (bs.drop 14).drop 7 = bs.drop 21 := by rw [List.drop_drop]
      rw [← hDrop, List.take_append_drop]
    have h7 : (bs.drop 7).take 7 ++ bs.drop 14 = bs.drop 7 := by
      have hDrop : (bs.drop 7).drop 7 = bs.drop 14 := by rw [List.drop_drop]
      rw [← hDrop, List.take_append_drop]
    rw [h28, h21, h14, h7, List.take_append_drop]
  simpa only [List.append_assoc] using hSplit32

theorem bytes32ToDigest5_injective {b1 b2 : List UInt8}
    (h1 : b1.length = 32) (h2 : b2.length = 32)
    (hEq : bytes32ToDigest5 b1 = bytes32ToDigest5 b2) : b1 = b2 := by
  rw [← unpack_bytes32ToDigest5_of_len32 h1, ← unpack_bytes32ToDigest5_of_len32 h2, hEq]

/-- Constructive single-layer WOTS+C + XMSS extractor: given `verifyWotsLayer = some rt` where
    `rt = honestSubtreeRoot geom skSeed pk.pkSeed layer treeIdx`, either:
    1. `(qWots layer treeIdx kpIdx = some entry ∧ dsF = entry.digits)` (the exact queried digit vector was replayed), OR
    2. Extracts a concrete Merkle / WOTS-sponge / WOTS-step / secret-chain break! -/
def extractSingleWotsLayerOrBreak
    (geom : AggSigGeometry) (skSeed : Digest4) (pk : AggValidatorPk)
    (qWots : QueriedWotsDigitsOracle)
    (hChainsLe : geom.wotsChains ≤ 128)
    (hTargetBound : geom.targetSum < 3 * geom.wotsChains)
    (layer treeIdx kpIdx : Nat) (hKpLt : kpIdx < 2 ^ geom.subtreeHeight)
    (hmsg : Digest5) (lsig : WotsLayerSig) (rt : Digest4)
    (hVer : verifyWotsLayer geom pk layer treeIdx kpIdx hmsg lsig = some rt)
    (hRtEq : rt = honestSubtreeRoot geom skSeed pk.pkSeed layer treeIdx)
    (hOracleValid : ∀ entry, qWots layer treeIdx kpIdx = some entry →
      entry.digits.length = geom.wotsChains ∧
      listNatSum entry.digits = geom.targetSum ∧
      (∀ x ∈ entry.digits, x < 4)) :
    PSum { entry : QueriedWotsEntry // qWots layer treeIdx kpIdx = some entry ∧
                                       extractWotsDigitsChecked geom hmsg = some entry.digits }
         (PSum (MerkleNodeCollisionWitness pk.pkSeed)
           (PSum (WotsPkSpongeCollisionWitness pk.pkSeed)
             (PSum (WotsStepCollisionWitness pk.pkSeed)
               (WotsSecretChainBreak geom skSeed pk.pkSeed qWots)))) := by
  unfold verifyWotsLayer at hVer
  cases hLengths : (lsig.wotsChains.length == geom.wotsChains && lsig.merklePath.length == geom.subtreeHeight)
  · simp [hLengths] at hVer
  · simp only [hLengths, ↓reduceIte] at hVer
    rcases Bool.and_eq_true_iff.mp hLengths with ⟨hChainLenBeq, hPathLenBeq⟩
    have hChainLen : lsig.wotsChains.length = geom.wotsChains := eq_of_beq hChainLenBeq
    have hPathLen : lsig.merklePath.length = geom.subtreeHeight := eq_of_beq hPathLenBeq
    cases hExt : extractWotsDigitsChecked geom hmsg with
    | none => simp [hExt] at hVer
    | some dsF =>
      simp only [hExt] at hVer
      cases hSumBeq : (listNatSum dsF == geom.targetSum)
      · simp [hSumBeq] at hVer
      · simp only [hSumBeq, ↓reduceIte, Option.some.injEq] at hVer
        have hSumF : listNatSum dsF = geom.targetSum := eq_of_beq hSumBeq
        obtain ⟨hDsFLen, _⟩ := extractWotsDigitsChecked_spec hChainsLe hExt
        let epsF := recoverAggWotsEndpoints pk.pkSeed layer treeIdx kpIdx 0 dsF lsig.wotsChains
        let wotsPkF := compressWotsEndpointsSponge pk.pkSeed layer treeIdx kpIdx epsF
        unfold honestSubtreeRoot at hRtEq
        have hWalkEq :
            merkleWalkRoot domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr 1 kpIdx wotsPkF
                lsig.merklePath =
              buildMerkleNodeAt domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr
                (honestWotsPk geom skSeed pk.pkSeed layer treeIdx) geom.subtreeHeight 1 0 :=
          hVer.trans hRtEq
        match extractMerkleLeafOrCollision domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr
                geom.subtreeHeight (honestWotsPk geom skSeed pk.pkSeed layer treeIdx)
                1 kpIdx wotsPkF lsig.merklePath hPathLen hKpLt hWalkEq with
        | .inr mCol => exact .inr (.inl mCol)
        | .inl hWotsPkEq =>
          let epsH := honestWotsEndpoints geom skSeed pk.pkSeed layer treeIdx kpIdx
          if hEpsEq : epsF = epsH then
            cases hQ : qWots layer treeIdx kpIdx with
            | none =>
              have hSumLt3 : listNatSum dsF < 3 * dsF.length := by
                rw [hSumF, hDsFLen]; exact hTargetBound
              let ⟨c, hCF, hCLt3⟩ := findDigitLtThreeIdx dsF hSumLt3
              have hCG : c < geom.wotsChains := hDsFLen ▸ hCF
              have hCLen : dsF.length = lsig.wotsChains.length := hDsFLen.trans hChainLen.symm
              have hEpsFLen : epsF.length = dsF.length :=
                recoverAggWotsEndpoints_length pk.pkSeed layer treeIdx kpIdx 0 dsF lsig.wotsChains hCLen
              have hCEpsF : c < epsF.length := hEpsFLen.symm ▸ hCF
              have hCEpsH : c < epsH.length := by simp [epsH, honestWotsEndpoints, hCG]
              have hEndEq : epsF[c]'hCEpsF = epsH[c]'hCEpsH := by simp [hEpsEq]
              have hFGet := recoverAggWotsEndpoints_getElem pk.pkSeed layer treeIdx kpIdx
                dsF lsig.wotsChains 0 c hCLen hCF hCEpsF
              simp only [Nat.zero_add] at hFGet
              have hHGet : epsH[c]'hCEpsH =
                  wotsChainWalk pk.pkSeed layer treeIdx kpIdx c 0 3
                    (wotsSecretStart skSeed pk.pkSeed layer treeIdx kpIdx c) := by
                simp only [epsH, honestWotsEndpoints, List.getElem_map, List.getElem_range]
              let dC := dsF[c]'hCF
              let forgedVal := lsig.wotsChains[c]'(hCLen ▸ hCF)
              let honestMid := wotsChainWalk pk.pkSeed layer treeIdx kpIdx c 0 dC
                (wotsSecretStart skSeed pk.pkSeed layer treeIdx kpIdx c)
              have hSplit3 :
                  wotsChainWalk pk.pkSeed layer treeIdx kpIdx c 0 3
                    (wotsSecretStart skSeed pk.pkSeed layer treeIdx kpIdx c) =
                  wotsChainWalk pk.pkSeed layer treeIdx kpIdx c dC (3 - dC) honestMid := by
                have hAdd : dC + (3 - dC) = 3 := by omega
                conv => lhs; rw [← hAdd]
                rw [wotsChainWalk_add, Nat.zero_add]
              have hWalkBoth :
                  wotsChainWalk pk.pkSeed layer treeIdx kpIdx c dC (3 - dC) forgedVal =
                  wotsChainWalk pk.pkSeed layer treeIdx kpIdx c dC (3 - dC) honestMid := by
                calc wotsChainWalk pk.pkSeed layer treeIdx kpIdx c dC (3 - dC) forgedVal
                  _ = epsF[c]'hCEpsF := hFGet.symm
                  _ = epsH[c]'hCEpsH := hEndEq
                  _ = _ := hHGet.trans hSplit3
              match extractChainWalkEqOrStepCollision pk.pkSeed layer treeIdx kpIdx c
                      (3 - dC) dC forgedVal honestMid hWalkBoth with
              | .inr sCol => exact .inr (.inr (.inr (.inl sCol)))
              | .inl hExact =>
                exact .inr (.inr (.inr (.inr
                  (.unqueriedChainPreimage layer treeIdx kpIdx c dC forgedVal
                    hQ hCG hCLt3 hExact (by rw [hExact, ← hSplit3])))))
            | some entry =>
              if hDsEq : dsF = entry.digits then
                exact .inl ⟨entry, rfl, congrArg some hDsEq⟩
              else
                obtain ⟨hDqLen, hDqSum, hDqLt4⟩ := hOracleValid entry hQ
                have hLenEq : entry.digits.length = dsF.length := hDqLen.trans hDsFLen.symm
                have hSumLe : listNatSum dsF ≤ listNatSum entry.digits := by
                  rw [hSumF, hDqSum]; exact Nat.le_refl _
                let ⟨c, hCQ, hCF, hStrictLt⟩ := findSmallerDigitIdx entry.digits dsF hLenEq hSumLe hDsEq
                have hCG : c < geom.wotsChains := hDqLen ▸ hCQ
                have hCLen : dsF.length = lsig.wotsChains.length := hDsFLen.trans hChainLen.symm
                have hEpsFLen : epsF.length = dsF.length :=
                  recoverAggWotsEndpoints_length pk.pkSeed layer treeIdx kpIdx 0 dsF lsig.wotsChains hCLen
                have hCEpsF : c < epsF.length := hEpsFLen.symm ▸ hCF
                have hCEpsH : c < epsH.length := by simp [epsH, honestWotsEndpoints, hCG]
                have hEndEq : epsF[c]'hCEpsF = epsH[c]'hCEpsH := by simp [hEpsEq]
                have hFGet := recoverAggWotsEndpoints_getElem pk.pkSeed layer treeIdx kpIdx
                  dsF lsig.wotsChains 0 c hCLen hCF hCEpsF
                simp only [Nat.zero_add] at hFGet
                have hHGet : epsH[c]'hCEpsH =
                    wotsChainWalk pk.pkSeed layer treeIdx kpIdx c 0 3
                      (wotsSecretStart skSeed pk.pkSeed layer treeIdx kpIdx c) := by
                  simp only [epsH, honestWotsEndpoints, List.getElem_map, List.getElem_range]
                let dFC := dsF[c]'hCF
                let dQC := entry.digits[c]'hCQ
                have hDqC4 : dQC < 4 := hDqLt4 dQC (List.getElem_mem hCQ)
                let forgedVal := lsig.wotsChains[c]'(hCLen ▸ hCF)
                let honestAtFC := wotsChainWalk pk.pkSeed layer treeIdx kpIdx c 0 dFC
                  (wotsSecretStart skSeed pk.pkSeed layer treeIdx kpIdx c)
                have hSplit3 :
                    wotsChainWalk pk.pkSeed layer treeIdx kpIdx c 0 3
                      (wotsSecretStart skSeed pk.pkSeed layer treeIdx kpIdx c) =
                    wotsChainWalk pk.pkSeed layer treeIdx kpIdx c dFC (3 - dFC) honestAtFC := by
                  have hAdd : dFC + (3 - dFC) = 3 := by omega
                  conv => lhs; rw [← hAdd]
                  rw [wotsChainWalk_add, Nat.zero_add]
                have hWalkBoth :
                    wotsChainWalk pk.pkSeed layer treeIdx kpIdx c dFC (3 - dFC) forgedVal =
                    wotsChainWalk pk.pkSeed layer treeIdx kpIdx c dFC (3 - dFC) honestAtFC := by
                  calc wotsChainWalk pk.pkSeed layer treeIdx kpIdx c dFC (3 - dFC) forgedVal
                    _ = epsF[c]'hCEpsF := hFGet.symm
                    _ = epsH[c]'hCEpsH := hEndEq
                    _ = _ := hHGet.trans hSplit3
                match extractChainWalkEqOrStepCollision pk.pkSeed layer treeIdx kpIdx c
                        (3 - dFC) dFC forgedVal honestAtFC hWalkBoth with
                | .inr sCol => exact .inr (.inr (.inr (.inl sCol)))
                | .inl hExactFC =>
                  let preSteps := (dQC - 1) - dFC
                  let preNode := wotsChainWalk pk.pkSeed layer treeIdx kpIdx c dFC preSteps forgedVal
                  have hPreExact :
                      preNode = wotsChainWalk pk.pkSeed layer treeIdx kpIdx c 0 (dQC - 1)
                        (wotsSecretStart skSeed pk.pkSeed layer treeIdx kpIdx c) := by
                    dsimp only [preNode, preSteps]
                    rw [hExactFC]
                    dsimp only [honestAtFC]
                    have hZeroAdd : dFC = 0 + dFC := (Nat.zero_add dFC).symm
                    conv => lhs; arg 6; rw [hZeroAdd]
                    rw [← wotsChainWalk_add]
                    have hAdd : dFC + ((dQC - 1) - dFC) = dQC - 1 := by omega
                    rw [hAdd]
                  have hStepInv :
                      wotsStepHash pk.pkSeed preNode layer treeIdx kpIdx c (dQC - 1) =
                        wotsChainWalk pk.pkSeed layer treeIdx kpIdx c 0 dQC
                          (wotsSecretStart skSeed pk.pkSeed layer treeIdx kpIdx c) := by
                    rw [hPreExact]
                    have hSucc : dQC = (dQC - 1) + 1 := by omega
                    conv => rhs; rw [hSucc, wotsChainWalk_add]
                    rw [Nat.zero_add]
                    rfl
                  exact .inr (.inr (.inr (.inr
                    (.queriedBackwardInversion layer treeIdx kpIdx c entry hCQ preNode
                      hQ (by omega) hPreExact hStepInv))))
          else
            exact .inr (.inr (.inl {
              layer    := layer
              treeIdx  := treeIdx
              kpIdx    := kpIdx
              eps1     := epsF
              eps2     := epsH
              neInputs := hEpsEq
              spongeEq := hWotsPkEq
            }))

private def extractUpperPoly {LS D BRK : Type}
    (vStep : Nat → Nat → D → LS → Option (Nat × D))
    (rootAt : Nat → Nat → D)
    (subH : Nat)
    (hRem : ∀ l rem cur lsig trOut nextRt,
      vStep l rem cur lsig = some (trOut, nextRt) → trOut = rem / 2 ^ subH)
    (stepExt : ∀ (l rem : Nat) (cur nextRt : D) (lsig : LS),
      0 < l →
      vStep l rem cur lsig = some (rem / 2 ^ subH, nextRt) →
      nextRt = rootAt l (rem / 2 ^ subH) →
      PSum (cur = rootAt (l - 1) rem) BRK) :
    ∀ (upperLayers : List LS) (startLayer remTreeIdx : Nat) (curRoot topRoot : D),
      0 < startLayer →
      verifyUpperPoly vStep upperLayers startLayer remTreeIdx curRoot = some topRoot →
      topRoot = rootAt (startLayer + upperLayers.length - 1) (remTreeIdx / 2 ^ (upperLayers.length * subH)) →
      PSum (curRoot = rootAt (startLayer - 1) remTreeIdx) BRK
  | [], startLayer, remTreeIdx, curRoot, topRoot, _, hVer, hTop => by
    dsimp only [verifyUpperPoly] at hVer
    simp only [Option.some.injEq] at hVer
    simp only [List.length_nil, Nat.add_zero, Nat.zero_mul, Nat.pow_zero, Nat.div_one] at hTop
    exact .inl (hVer.trans hTop)
  | lsig :: rest, startLayer, remTreeIdx, curRoot, topRoot, hPos, hVer, hTop => by
    dsimp only [verifyUpperPoly] at hVer
    cases hSt : vStep startLayer remTreeIdx curRoot lsig with
    | none => simp [hSt] at hVer
    | some pair =>
      rcases pair with ⟨nextRem, nextRoot⟩
      simp only [hSt] at hVer
      have hRemEq : nextRem = remTreeIdx / 2 ^ subH := hRem _ _ _ _ _ _ hSt
      subst hRemEq
      have hTopShift :
          topRoot = rootAt ((startLayer + 1) + rest.length - 1)
            ((remTreeIdx / 2 ^ subH) / 2 ^ (rest.length * subH)) := by
        have hL : startLayer + (lsig :: rest).length - 1 = (startLayer + 1) + rest.length - 1 := by
          simp only [List.length_cons]; omega
        have hR : remTreeIdx / 2 ^ ((lsig :: rest).length * subH) =
            (remTreeIdx / 2 ^ subH) / 2 ^ (rest.length * subH) := by
          simp only [List.length_cons]
          rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
          have hE : subH + rest.length * subH = (rest.length + 1) * subH := by
            rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
          rw [hE]
        rwa [← hL, ← hR]
      match extractUpperPoly vStep rootAt subH hRem stepExt rest
              (startLayer + 1) (remTreeIdx / 2 ^ subH) nextRoot topRoot (by omega) hVer hTopShift with
      | .inr brk => exact .inr brk
      | .inl hNextEq =>
        exact stepExt startLayer remTreeIdx curRoot nextRoot lsig hPos hSt hNextEq

/-- Downward multi-layer hypertree extractor (`startLayer .. top`): given
    `verifyUpperLayers geom pk startLayer remTreeIdx curRoot upperLayers = some topRoot` where
    `topRoot = honestSubtreeRoot geom skSeed pk.pkSeed ...`, constructively proves EITHER
    `curRoot = honestSubtreeRoot geom skSeed pk.pkSeed (startLayer - 1) remTreeIdx` OR extracts a
    concrete `AggNativeForgeryBreak`! -/
def extractUpperHypertreeOrBreak
    (geom : AggSigGeometry) (skSeed : Digest4) (pk : AggValidatorPk)
    (msg : List UInt8) (rRand : Digest4)
    (qWots : QueriedWotsDigitsOracle) (revealedFors : List (Nat × Nat × Nat))
    (hChainsLe : geom.wotsChains ≤ 128)
    (hTargetBound : geom.targetSum < 3 * geom.wotsChains)
    (hOracleValid : ∀ l tr kp entry, qWots l tr kp = some entry →
      entry.digits.length = geom.wotsChains ∧
      listNatSum entry.digits = geom.targetSum ∧
      (∀ x ∈ entry.digits, x < 4))
    (hUpperHonest : ∀ (l rem : Nat) (entry : QueriedWotsEntry),
      0 < l →
      qWots l (rem / 2 ^ geom.subtreeHeight) (rem % 2 ^ geom.subtreeHeight) = some entry →
      extractWotsDigitsChecked geom
        (computeHmsgDetTree pk l (rem / 2 ^ geom.subtreeHeight) (rem % 2 ^ geom.subtreeHeight)
          entry.tswCtr (honestSubtreeRoot geom skSeed pk.pkSeed (l - 1) rem)) = some entry.digits)
    (upperLayers : List WotsLayerSig) (startLayer remTreeIdx : Nat) (curRoot topRoot : Digest4)
    (hPos : 0 < startLayer)
    (hVer : verifyUpperLayers geom pk startLayer remTreeIdx curRoot upperLayers = some topRoot)
    (hTop : topRoot = honestSubtreeRoot geom skSeed pk.pkSeed (startLayer + upperLayers.length - 1)
                        (remTreeIdx / 2 ^ (upperLayers.length * geom.subtreeHeight))) :
    PSum (curRoot = honestSubtreeRoot geom skSeed pk.pkSeed (startLayer - 1) remTreeIdx)
         (AggNativeForgeryBreak geom skSeed pk msg rRand qWots revealedFors) := by
  unfold verifyUpperLayers at hVer
  refine extractUpperPoly _ (honestSubtreeRoot geom skSeed pk.pkSeed) geom.subtreeHeight
    (fun l rem cur lsig trOut nextRt hSt => by
      dsimp only at hSt
      cases hW : verifyWotsLayer geom pk l (rem / 2 ^ geom.subtreeHeight) (rem % 2 ^ geom.subtreeHeight)
                   (computeHmsgDetTree pk l (rem / 2 ^ geom.subtreeHeight) (rem % 2 ^ geom.subtreeHeight)
                     lsig.tswCtr cur) lsig with
      | none => simp [hW] at hSt
      | some rt =>
        simp only [hW, Option.some.injEq, Prod.mk.injEq] at hSt
        exact hSt.1.symm)
    (fun l rem cur nextRt lsig hLPos hSt hNextHonest => by
      dsimp only at hSt
      let kpIdx := rem % (2 ^ geom.subtreeHeight)
      let treeIdx := rem / (2 ^ geom.subtreeHeight)
      let hmsg := computeHmsgDetTree pk l treeIdx kpIdx lsig.tswCtr cur
      cases hWots : verifyWotsLayer geom pk l treeIdx kpIdx hmsg lsig with
      | none =>
        change (match verifyWotsLayer geom pk l treeIdx kpIdx hmsg lsig with
                | none => none | some nextRoot => some (treeIdx, nextRoot)) = some _ at hSt
        rw [hWots] at hSt; cases hSt
      | some rtOut =>
        change (match verifyWotsLayer geom pk l treeIdx kpIdx hmsg lsig with
                | none => none | some nextRoot => some (treeIdx, nextRoot)) = some _ at hSt
        rw [hWots] at hSt
        simp only [Option.some.injEq, Prod.mk.injEq] at hSt
        rcases hSt with ⟨_, rfl⟩
        have hKpLt : kpIdx < 2 ^ geom.subtreeHeight := Nat.mod_lt _ (Nat.pow_pos (by decide))
        match extractSingleWotsLayerOrBreak geom skSeed pk qWots hChainsLe hTargetBound
                l treeIdx kpIdx hKpLt hmsg lsig rtOut hWots hNextHonest
                (hOracleValid l treeIdx kpIdx) with
        | .inr (.inl mCol) => exact .inr (.merkleCollision mCol)
        | .inr (.inr (.inl pCol)) => exact .inr (.wotsPkCollision pCol)
        | .inr (.inr (.inr (.inl sCol))) => exact .inr (.wotsStepCollision sCol)
        | .inr (.inr (.inr (.inr chBrk))) => exact .inr (.wotsSecretChainBreak chBrk)
        | .inl ⟨entry, hQ, hExtF⟩ =>
          let honestChildRt := honestSubtreeRoot geom skSeed pk.pkSeed (l - 1) rem
          if hChildEq : cur = honestChildRt then
            exact .inl hChildEq
          else
            have hHonExt := hUpperHonest l rem entry hLPos hQ
            have hPairNe : (lsig.tswCtr, cur) ≠ (entry.tswCtr, honestChildRt) :=
              fun hEq => hChildEq (congrArg Prod.snd hEq)
            exact .inr (.hmsgOrMuCollision
              (.detTreeCodewordCollision l treeIdx kpIdx lsig.tswCtr entry.tswCtr
                cur honestChildRt entry.digits hPairNe hExtF hHonExt)))
    upperLayers startLayer remTreeIdx curRoot topRoot hPos hVer hTop

private def extractForsPoly {OP D BRK : Type}
    (vStep : Nat → Nat → OP → Option D)
    (rootAt : Nat → D)
    (covPred : Nat → Nat → Prop)
    (treeExt : ∀ (t idx : Nat) (op : OP) (rt : D),
      vStep t idx op = some rt →
      rt = rootAt t →
      PSum { _u : Unit // covPred t idx } BRK) :
    ∀ (indices : List Nat) (ops : List OP) (startT : Nat) (roots : List D),
      verifyForsPoly vStep indices ops startT = some roots →
      roots = (List.range indices.length).map (fun i => rootAt (startT + i)) →
      PSum { _u : Unit // ∀ (i : Nat) (hi : i < indices.length), covPred (startT + i) (indices[i]'hi) } BRK
  | [], [], _, _, _, _ => .inl ⟨(), fun _ hi => False.elim (by simp at hi)⟩
  | [], _ :: _, _, _, hVer, _ => False.elim (by dsimp only [verifyForsPoly] at hVer; cases hVer)
  | _ :: _, [], _, _, hVer, _ => False.elim (by dsimp only [verifyForsPoly] at hVer; cases hVer)
  | idx :: idxs, op :: ops, startT, roots, hVer, hRootsEq => by
    dsimp only [verifyForsPoly] at hVer
    cases hSt : vStep startT idx op with
    | none => simp [hSt] at hVer
    | some rt =>
      simp only [hSt] at hVer
      cases hRest : verifyForsPoly vStep idxs ops (startT + 1) with
      | none => simp [hRest] at hVer
      | some restRoots =>
        simp only [hRest, Option.some.injEq] at hVer
        subst hVer
        rw [List.length_cons, List.range_succ_eq_map, List.map_cons, Nat.add_zero, List.map_map] at hRootsEq
        obtain ⟨hHeadRt, hTailRts⟩ := List.cons.inj hRootsEq
        have hTailShift :
            restRoots = (List.range idxs.length).map (fun i => rootAt (startT + 1 + i)) := by
          rw [hTailRts]
          congr 1
          funext i
          have hS : startT + (i + 1) = startT + 1 + i := by omega
          simp [Function.comp, hS]
        match treeExt startT idx op rt hSt hHeadRt with
        | .inr brk => exact .inr brk
        | .inl ⟨_, hHeadCov⟩ =>
          match extractForsPoly vStep rootAt covPred treeExt idxs ops (startT + 1) restRoots hRest hTailShift with
          | .inr brk => exact .inr brk
          | .inl ⟨_, hRestCov⟩ =>
            exact .inl ⟨(), fun i hi => by
              cases i with
              | zero => simpa only [Nat.add_zero, List.getElem_cons_zero] using hHeadCov
              | succ i' =>
                have hStep := hRestCov i' (Nat.lt_of_succ_lt_succ hi)
                have hS : startT + 1 + i' = startT + (i' + 1) := by omega
                simpa only [hS, List.getElem_cons_succ] using hStep⟩

/-- Constructive FORS tree-by-tree opening extractor. -/
def extractForsTreesOrBreak
    (geom : AggSigGeometry) (skSeed pkSeed : Digest4) (leafGlobalIdx : Nat)
    (revealedFors : List (Nat × Nat × Nat))
    (startT : Nat) (indices : List Nat) (ops : List AggForsTreeOpening) (roots : List Digest4)
    (hVer : verifyForsTreesAux geom pkSeed leafGlobalIdx startT indices ops = some roots)
    (hRootsEq : roots = (List.range indices.length).map (fun i =>
      honestForsTreeRoot geom skSeed pkSeed leafGlobalIdx (startT + i))) :
    PSum { _u : Unit // ∀ (i : Nat) (hi : i < indices.length),
                          (leafGlobalIdx, startT + i, indices[i]'hi) ∈ revealedFors }
         (PSum (MerkleNodeCollisionWitness pkSeed)
           (PSum (ForsLeafCollisionWitness geom pkSeed)
             (ForsUnqueriedSecretBreak geom skSeed pkSeed revealedFors))) := by
  unfold verifyForsTreesAux at hVer
  refine extractForsPoly
    (verifySingleForsOpening geom pkSeed leafGlobalIdx)
    (honestForsTreeRoot geom skSeed pkSeed leafGlobalIdx)
    (fun t o => (leafGlobalIdx, t, o) ∈ revealedFors)
    (fun t idx op rt hSt hRtEq => by
      dsimp only [verifySingleForsOpening] at hSt
      cases hChk : (decide (idx < 2 ^ geom.forsHeight) && (op.authPath.length == geom.forsHeight))
      · simp [hChk] at hSt
      · simp only [hChk, ↓reduceIte, Option.some.injEq] at hSt
        rcases Bool.and_eq_true_iff.mp hChk with ⟨hIdxLtDec, hPathLenBeq⟩
        have hIdxLt : idx < 2 ^ geom.forsHeight := of_decide_eq_true hIdxLtDec
        have hPathLen : op.authPath.length = geom.forsHeight := eq_of_beq hPathLenBeq
        unfold honestForsTreeRoot at hRtEq
        have hWalkEq := hSt.trans hRtEq
        let leafFn := honestForsLeaf geom skSeed pkSeed leafGlobalIdx t
        let forgedLeaf := forsLeafHash geom pkSeed op.secretVal leafGlobalIdx t idx
        match extractMerkleLeafOrCollision domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
                (forsTreeNodeAddr geom leafGlobalIdx t)
                geom.forsHeight leafFn 1 idx forgedLeaf op.authPath hPathLen hIdxLt hWalkEq with
        | .inr mCol => exact .inr (.inl mCol)
        | .inl hLeafEq =>
          let honestSec := forsSecretVal geom skSeed pkSeed leafGlobalIdx t idx
          if hSecEq : op.secretVal = honestSec then
            if hRev : (leafGlobalIdx, t, idx) ∈ revealedFors then
              exact .inl ⟨(), hRev⟩
            else
              exact .inr (.inr (.inr {
                leafGlobalIdx := leafGlobalIdx
                treeIdx       := t
                leafOffset    := idx
                secretVal     := op.secretVal
                notRevealed   := hRev
                exactSecret   := hSecEq
              }))
          else
            exact .inr (.inr (.inl {
              leafGlobalIdx := leafGlobalIdx
              treeIdx       := t
              leafOffset    := idx
              val1          := op.secretVal
              val2          := honestSec
              neInputs      := hSecEq
              hashEq        := hLeafEq
            })))
    indices ops startT roots hVer hRootsEq

/-- **Constructive Forgery Extractor (`extractAggNativeForgeryBreak`)**:
    Given `pk = deriveAggPublicKey geom skSeed pkSeed` and any signature `forgedSig` accepted on an
    unqueried message `msg ∉ queriedMsgs`, constructively extracts a concrete `AggNativeForgeryBreak`! -/
def extractAggNativeForgeryBreak
    (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (msg : List UInt8) (forgedSig : AggNativeSignature)
    (queriedMsgs : List (List UInt8))
    (qWots : QueriedWotsDigitsOracle)
    (revealedFors : List (Nat × Nat × Nat))
    (hFreshMsg : msg ∉ queriedMsgs)
    (hVer : verifyAggNativeSig geom (deriveAggPublicKey geom skSeed pkSeed) msg forgedSig = true)
    (hOracleValid : ∀ l tr kp entry, qWots l tr kp = some entry →
      entry.digits.length = geom.wotsChains ∧
      listNatSum entry.digits = geom.targetSum ∧
      (∀ x ∈ entry.digits, x < 4))
    (hUpperHonest : ∀ (l rem : Nat) (entry : QueriedWotsEntry),
      0 < l →
      qWots l (rem / 2 ^ geom.subtreeHeight) (rem % 2 ^ geom.subtreeHeight) = some entry →
      extractWotsDigitsChecked geom
        (computeHmsgDetTree (deriveAggPublicKey geom skSeed pkSeed) l
          (rem / 2 ^ geom.subtreeHeight) (rem % 2 ^ geom.subtreeHeight)
          entry.tswCtr (honestSubtreeRoot geom skSeed pkSeed (l - 1) rem)) = some entry.digits)
    (hStatefulHonest0 : geom.forsTrees = 0 →
      ∀ (tr0 kp0 : Nat) (entry : QueriedWotsEntry),
        qWots 0 tr0 kp0 = some entry →
        entry.queriedMsg ∈ queriedMsgs ∧
        extractWotsDigitsChecked geom
          (computeHmsgStateful (deriveAggPublicKey geom skSeed pkSeed) entry.rRand
            (computeMessageMu (deriveAggPublicKey geom skSeed pkSeed) entry.queriedMsg)
            kp0 entry.tswCtr) = some entry.digits)
    (hStatelessHonest0 : geom.forsTrees ≠ 0 →
      ∀ (leafIdx : Nat) (entry : QueriedWotsEntry),
        qWots 0 (leafIdx / 2 ^ geom.subtreeHeight) (leafIdx % 2 ^ geom.subtreeHeight) = some entry →
        extractWotsDigitsChecked geom
          (computeHmsgDetTree (deriveAggPublicKey geom skSeed pkSeed) 0
            (leafIdx / 2 ^ geom.subtreeHeight) (leafIdx % 2 ^ geom.subtreeHeight)
            entry.tswCtr (honestForsPk geom skSeed pkSeed leafIdx)) = some entry.digits) :
    AggNativeForgeryBreak geom skSeed (deriveAggPublicKey geom skSeed pkSeed)
      msg forgedSig.rRand qWots revealedFors := by
  let pk := deriveAggPublicKey geom skSeed pkSeed
  change verifyAggNativeSig geom pk msg forgedSig = true at hVer
  unfold verifyAggNativeSig at hVer
  cases hHdr : (!geom.wellFormed || pk.profile != geom.profile ||
                forgedSig.profile != geom.profile || forgedSig.layers.length != geom.numLayers)
  · simp only [hHdr, Bool.false_eq_true, ↓reduceIte] at hVer
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false', bne_eq_false_iff_eq] at hHdr
    have hWf : geom.wellFormed = true := hHdr.1.1.1
    have hLayersLen : forgedSig.layers.length = geom.numLayers := hHdr.2
    have hWfUnpack : geom.wotsChains ≤ 128 ∧ geom.targetSum < 3 * geom.wotsChains := by
      unfold AggSigGeometry.wellFormed at hWf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hWf
      exact ⟨hWf.1.1.1.1.1.1.2, hWf.1.1.1.1.2⟩
    obtain ⟨hChainsLe, hTargetBound⟩ := hWfUnpack
    let mu := computeMessageMu pk msg
    cases hLayers : forgedSig.layers with
    | nil => simp [hLayers] at hVer
    | cons lsig0 upperLayers =>
      simp only [hLayers] at hVer
      have hUpperLen : upperLayers.length + 1 = geom.numLayers := by
        rw [← hLayersLen, hLayers]; simp
      have hPowPos : 0 < 2 ^ geom.subtreeHeight := Nat.pow_pos (by decide)
      cases hFors0 : (geom.forsTrees == 0)
      · -- Stateless Corduroy (`geom.forsTrees ≠ 0`)
        simp only [hFors0, Bool.false_eq_true, ↓reduceIte] at hVer
        delta verifyAggNativeSigStateless at hVer
        have hForsNe : geom.forsTrees ≠ 0 := by intro hZ; rw [hZ] at hFors0; simp at hFors0
        have hForsPos : 0 < geom.forsTrees := Nat.pos_of_ne_zero hForsNe
        rcases unpackStatelessFlow hVer with
          ⟨leafGlobalIdx, forsIndices, forsPk, root0, topRoot, _, hXof, hForsVer, hW0, hUp, hTopBeq⟩
        have hTopEq : topRoot = pk.pkRoot := eq_of_beq hTopBeq
        obtain ⟨hLeafLt, hForsIdxLen, _⟩ := deriveStatelessLeafAndForsChecked_spec hXof
        let kp0 := leafGlobalIdx % (2 ^ geom.subtreeHeight)
        let tr0 := leafGlobalIdx / (2 ^ geom.subtreeHeight)
        let hmsg0 := computeHmsgDetTree pk 0 tr0 kp0 lsig0.tswCtr forsPk
        have hTopHonest :
            topRoot = honestSubtreeRoot geom skSeed pk.pkSeed
              (1 + upperLayers.length - 1) (tr0 / 2 ^ (upperLayers.length * geom.subtreeHeight)) := by
          have hL : 1 + upperLayers.length - 1 = geom.numLayers - 1 := by omega
          have hR : tr0 / 2 ^ (upperLayers.length * geom.subtreeHeight) = 0 := by
            dsimp only [tr0]
            rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
            have hE : geom.subtreeHeight + upperLayers.length * geom.subtreeHeight =
                geom.numLayers * geom.subtreeHeight := by
              rw [← hUpperLen, Nat.add_mul, Nat.one_mul, Nat.add_comm]
            rw [hE]
            exact Nat.div_eq_of_lt hLeafLt
          rw [hL, hR]
          exact hTopEq
        match extractUpperHypertreeOrBreak geom skSeed pk msg forgedSig.rRand qWots revealedFors
                hChainsLe hTargetBound hOracleValid hUpperHonest
                upperLayers 1 tr0 root0 topRoot (by decide) hUp hTopHonest with
        | .inr brk => exact brk
        | .inl hRoot0Eq =>
          match extractSingleWotsLayerOrBreak geom skSeed pk qWots hChainsLe hTargetBound
                  0 tr0 kp0 (Nat.mod_lt _ hPowPos) hmsg0 lsig0 root0 hW0 hRoot0Eq
                  (hOracleValid 0 tr0 kp0) with
          | .inr (.inl mCol) => exact .merkleCollision mCol
          | .inr (.inr (.inl pCol)) => exact .wotsPkCollision pCol
          | .inr (.inr (.inr (.inl sCol))) => exact .wotsStepCollision sCol
          | .inr (.inr (.inr (.inr chBrk))) => exact .wotsSecretChainBreak chBrk
          | .inl ⟨entry0, hQ0, hExt0⟩ =>
            let honestFPk := honestForsPk geom skSeed pkSeed leafGlobalIdx
            if hFPkEq : forsPk = honestFPk then
              unfold verifyAndRecoverForsPk at hForsVer
              cases hFLen : (forsIndices.length == geom.forsTrees &&
                             forgedSig.forsOpenings.length == geom.forsTrees)
              · simp [hFLen] at hForsVer
              · simp only [hFLen, ↓reduceIte] at hForsVer
                cases hFTrees : verifyForsTreesAux geom pk.pkSeed leafGlobalIdx 0
                                  forsIndices forgedSig.forsOpenings with
                | none => simp [hFTrees] at hForsVer
                | some rootsF =>
                  simp only [hFTrees, Option.some.injEq] at hForsVer
                  let rootsH := (List.range geom.forsTrees).map
                    (honestForsTreeRoot geom skSeed pkSeed leafGlobalIdx)
                  if hRtsEq : rootsF = rootsH then
                    have hRtsShift :
                        rootsF = (List.range forsIndices.length).map (fun i =>
                          honestForsTreeRoot geom skSeed pk.pkSeed leafGlobalIdx (0 + i)) := by
                      have hPkSeed : pk.pkSeed = pkSeed := rfl
                      rw [hRtsEq, hForsIdxLen, hPkSeed]
                      dsimp only [rootsH]
                      congr 1
                      funext i
                      rw [Nat.zero_add]
                    match extractForsTreesOrBreak geom skSeed pk.pkSeed leafGlobalIdx revealedFors
                            0 forsIndices forgedSig.forsOpenings rootsF hFTrees hRtsShift with
                    | .inr (.inl mCol) => exact .merkleCollision mCol
                    | .inr (.inr (.inl lCol)) => exact .forsLeafCollision lCol
                    | .inr (.inr (.inr uSec)) => exact .forsUnqueriedSecret uSec
                    | .inl ⟨_, hAllCov⟩ =>
                      exact .statelessForsCover {
                        forsPos       := hForsPos
                        leafGlobalIdx := leafGlobalIdx
                        indices       := forsIndices
                        xofEq         := hXof
                        allCovered    := fun t ht => by
                          simpa only [Nat.zero_add] using hAllCov t ht
                      }
                  else
                    have hHonFPkDef : honestFPk = compressForsRootsSponge geom pk.pkSeed leafGlobalIdx rootsH := by
                      dsimp only [honestFPk, rootsH, pk, deriveAggPublicKey]
                      unfold honestForsPk
                      rfl
                    exact .forsRootsCollision {
                      leafGlobalIdx := leafGlobalIdx
                      roots1        := rootsF
                      roots2        := rootsH
                      neInputs      := hRtsEq
                      spongeEq      := hForsVer.trans (hFPkEq.trans hHonFPkDef)
                    }
            else
              have hHon0 := hStatelessHonest0 hForsNe leafGlobalIdx entry0 hQ0
              have hPairNe : (lsig0.tswCtr, forsPk) ≠ (entry0.tswCtr, honestFPk) :=
                fun hEq => hFPkEq (congrArg Prod.snd hEq)
              exact .hmsgOrMuCollision
                (.detTreeCodewordCollision 0 tr0 kp0 lsig0.tswCtr entry0.tswCtr
                  forsPk honestFPk entry0.digits hPairNe hExt0 hHon0)
      · -- Stateful XMSS (`geom.forsTrees = 0`)
        simp only [hFors0, ↓reduceIte] at hVer
        unfold verifyAggNativeSigStateful at hVer
        have hForsEq0 : geom.forsTrees = 0 := eq_of_beq hFors0
        cases hSChk : (!forgedSig.forsOpenings.isEmpty ||
                       !(decide (forgedSig.statefulLeafIdx < 2 ^ (geom.numLayers * geom.subtreeHeight))))
        · simp only [hSChk, Bool.false_eq_true, ↓reduceIte] at hVer
          simp only [Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_true_eq] at hSChk
          have hLeafLt := hSChk.2
          let kp0 := forgedSig.statefulLeafIdx % (2 ^ geom.subtreeHeight)
          let tr0 := forgedSig.statefulLeafIdx / (2 ^ geom.subtreeHeight)
          let hmsg0 := computeHmsgStateful pk forgedSig.rRand mu kp0 lsig0.tswCtr
          change (match verifyWotsLayer geom pk 0 tr0 kp0 hmsg0 lsig0 with
                  | none => false
                  | some root0 =>
                    match verifyUpperLayers geom pk 1 tr0 root0 upperLayers with
                    | none => false
                    | some topRoot => topRoot == pk.pkRoot) = true at hVer
          cases hW0 : verifyWotsLayer geom pk 0 tr0 kp0 hmsg0 lsig0 with
          | none => rw [hW0] at hVer; cases hVer
          | some root0 =>
            rw [hW0] at hVer
            dsimp only at hVer
            cases hUp : verifyUpperLayers geom pk 1 tr0 root0 upperLayers with
            | none => rw [hUp] at hVer; cases hVer
            | some topRoot =>
              rw [hUp] at hVer
              dsimp only at hVer
              have hTopEq : topRoot = pk.pkRoot := eq_of_beq hVer
              have hTopHonest :
                  topRoot = honestSubtreeRoot geom skSeed pk.pkSeed
                    (1 + upperLayers.length - 1) (tr0 / 2 ^ (upperLayers.length * geom.subtreeHeight)) := by
                have hL : 1 + upperLayers.length - 1 = geom.numLayers - 1 := by omega
                have hR : tr0 / 2 ^ (upperLayers.length * geom.subtreeHeight) = 0 := by
                  dsimp only [tr0]
                  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
                  have hE : geom.subtreeHeight + upperLayers.length * geom.subtreeHeight =
                      geom.numLayers * geom.subtreeHeight := by
                    rw [← hUpperLen, Nat.add_mul, Nat.one_mul, Nat.add_comm]
                  rw [hE]
                  exact Nat.div_eq_of_lt hLeafLt
                rw [hL, hR]
                exact hTopEq
              match extractUpperHypertreeOrBreak geom skSeed pk msg forgedSig.rRand qWots revealedFors
                      hChainsLe hTargetBound hOracleValid hUpperHonest
                      upperLayers 1 tr0 root0 topRoot (by decide) hUp hTopHonest with
              | .inr brk => exact brk
              | .inl hRoot0Eq =>
                match extractSingleWotsLayerOrBreak geom skSeed pk qWots hChainsLe hTargetBound
                        0 tr0 kp0 (Nat.mod_lt _ hPowPos) hmsg0 lsig0 root0 hW0 hRoot0Eq
                        (hOracleValid 0 tr0 kp0) with
                | .inr (.inl mCol) => exact .merkleCollision mCol
                | .inr (.inr (.inl pCol)) => exact .wotsPkCollision pCol
                | .inr (.inr (.inr (.inl sCol))) => exact .wotsStepCollision sCol
                | .inr (.inr (.inr (.inr chBrk))) => exact .wotsSecretChainBreak chBrk
                | .inl ⟨entry0, hQ0, hExt0⟩ =>
                  obtain ⟨hMsgInQ, hHon0⟩ := hStatefulHonest0 hForsEq0 tr0 kp0 entry0 hQ0
                  have hMsgNe : msg ≠ entry0.queriedMsg := fun hEq => hFreshMsg (hEq ▸ hMsgInQ)
                  let muQ := computeMessageMu pk entry0.queriedMsg
                  if hMuEq : mu = muQ then
                    let f1 := encodeMultiFrame [qsagMuV2TagBytes, encodeAggValidatorPkBytes pk, msg]
                    let f2 := encodeMultiFrame [qsagMuV2TagBytes, encodeAggValidatorPkBytes pk, entry0.queriedMsg]
                    have hFrameNe : f1 ≠ f2 := fun hFEq => by
                      have hListEq := encodeMultiFrame_injective hFEq
                      simp only [List.cons.injEq, and_true, true_and] at hListEq
                      exact hMsgNe hListEq
                    have hHashEq : poseidon2Hash32 f1 = poseidon2Hash32 f2 := by
                      have hMuUnfold : bytes32ToDigest5 (poseidon2Hash32 f1) = bytes32ToDigest5 (poseidon2Hash32 f2) := by
                        dsimp only [mu, muQ, f1, f2] at hMuEq ⊢
                        unfold computeMessageMu at hMuEq
                        exact hMuEq
                      exact bytes32ToDigest5_injective (poseidon2Hash32_length f1) (poseidon2Hash32_length f2) hMuUnfold
                    exact .hmsgOrMuCollision (.muPoseidon2Collision ⟨f1, f2, hFrameNe, hHashEq⟩)
                  else
                    have hTupNe : (forgedSig.rRand, mu, lsig0.tswCtr) ≠
                                  (entry0.rRand, muQ, entry0.tswCtr) :=
                      fun hEq => hMuEq (congrArg (fun t => t.2.1) hEq)
                    exact .hmsgOrMuCollision
                      (.statefulCodewordCollision kp0 forgedSig.rRand entry0.rRand mu muQ
                        lsig0.tswCtr entry0.tswCtr entry0.digits hTupNe hExt0 hHon0)
        · simp [hSChk] at hVer
  · simp [hHdr] at hVer

/-- **Packed 4-Limb `Poseidon2` WOTS+C + Merkle EUF-CMA Soundness (`aggNativeSig_wots_merkle_soundness`)**:
    Any accepted signature `forgedSig` on an unqueried message `msg ∉ queriedMsgs` constructively
    yields a concrete `AggNativeForgeryBreak` (secret-anchored WOTS+C backward
    chain preimage, unqueried FORS secret, Merkle/sponge/step collision, or stateless FORS subset cover)! -/
theorem aggNativeSig_wots_merkle_soundness
    (geom : AggSigGeometry) (skSeed pkSeed : Digest4)
    (msg : List UInt8) (forgedSig : AggNativeSignature)
    (queriedMsgs : List (List UInt8))
    (qWots : QueriedWotsDigitsOracle)
    (revealedFors : List (Nat × Nat × Nat))
    (hFreshMsg : msg ∉ queriedMsgs)
    (hVer : verifyAggNativeSig geom (deriveAggPublicKey geom skSeed pkSeed) msg forgedSig = true)
    (hOracleValid : ∀ l tr kp entry, qWots l tr kp = some entry →
      entry.digits.length = geom.wotsChains ∧
      listNatSum entry.digits = geom.targetSum ∧
      (∀ x ∈ entry.digits, x < 4))
    (hUpperHonest : ∀ (l rem : Nat) (entry : QueriedWotsEntry),
      0 < l →
      qWots l (rem / 2 ^ geom.subtreeHeight) (rem % 2 ^ geom.subtreeHeight) = some entry →
      extractWotsDigitsChecked geom
        (computeHmsgDetTree (deriveAggPublicKey geom skSeed pkSeed) l
          (rem / 2 ^ geom.subtreeHeight) (rem % 2 ^ geom.subtreeHeight)
          entry.tswCtr (honestSubtreeRoot geom skSeed pkSeed (l - 1) rem)) = some entry.digits)
    (hStatefulHonest0 : geom.forsTrees = 0 →
      ∀ (tr0 kp0 : Nat) (entry : QueriedWotsEntry),
        qWots 0 tr0 kp0 = some entry →
        entry.queriedMsg ∈ queriedMsgs ∧
        extractWotsDigitsChecked geom
          (computeHmsgStateful (deriveAggPublicKey geom skSeed pkSeed) entry.rRand
            (computeMessageMu (deriveAggPublicKey geom skSeed pkSeed) entry.queriedMsg)
            kp0 entry.tswCtr) = some entry.digits)
    (hStatelessHonest0 : geom.forsTrees ≠ 0 →
      ∀ (leafIdx : Nat) (entry : QueriedWotsEntry),
        qWots 0 (leafIdx / 2 ^ geom.subtreeHeight) (leafIdx % 2 ^ geom.subtreeHeight) = some entry →
        extractWotsDigitsChecked geom
          (computeHmsgDetTree (deriveAggPublicKey geom skSeed pkSeed) 0
            (leafIdx / 2 ^ geom.subtreeHeight) (leafIdx % 2 ^ geom.subtreeHeight)
            entry.tswCtr (honestForsPk geom skSeed pkSeed leafIdx)) = some entry.digits) :
    Nonempty (AggNativeForgeryBreak geom skSeed (deriveAggPublicKey geom skSeed pkSeed)
                msg forgedSig.rRand qWots revealedFors) :=
  ⟨extractAggNativeForgeryBreak geom skSeed pkSeed msg forgedSig queriedMsgs qWots revealedFors
     hFreshMsg hVer hOracleValid hUpperHonest hStatefulHonest0 hStatelessHonest0⟩

/-- **`#tooth` Wrong WOTS+C Target-Sum Rejection (`tooth_wrong_wots_sum_rejected`)**:
    Any layer signature whose extracted base-4 digits fail `listNatSum ds = geom.targetSum` is
    unconditionally rejected by `verifyWotsLayer`. -/
theorem tooth_wrong_wots_sum_rejected
    (geom : AggSigGeometry) (pk : AggValidatorPk) (layer treeIdx kpIdx : Nat)
    (hmsg : Digest5) (lsig : WotsLayerSig) (ds : List Nat)
    (hExt : extractWotsDigitsChecked geom hmsg = some ds)
    (hBadSum : listNatSum ds ≠ geom.targetSum) :
    verifyWotsLayer geom pk layer treeIdx kpIdx hmsg lsig = none := by
  unfold verifyWotsLayer
  cases hLen : (lsig.wotsChains.length == geom.wotsChains && lsig.merklePath.length == geom.subtreeHeight)
  · simp
  · simp only [↓reduceIte, hExt]
    have hBeqF : (listNatSum ds == geom.targetSum) = false := beq_false_of_ne hBadSum
    simp [hBeqF]

/-- **`#tooth` Corrupted Public Root Rejection (`tooth_mismatched_top_root_rejected`)**:
    Replacing `pk.pkRoot` with any root differing from the walked hypertree top root causes
    `verifyAggNativeSig` to reject whenever `mu` is unchanged, and `verifyUpperLayers` comparison
    rejects any mismatched top root directly. -/
theorem tooth_mismatched_top_root_rejected
    (geom : AggSigGeometry) (pk : AggValidatorPk) (msg : List UInt8) (sig : AggNativeSignature)
    (hFors0 : geom.forsTrees = 0)
    (lsig0 : WotsLayerSig) (upper : List WotsLayerSig) (hLayers : sig.layers = lsig0 :: upper)
    (root0 topRoot : Digest4)
    (hW0 : verifyWotsLayer geom pk 0 (sig.statefulLeafIdx / 2 ^ geom.subtreeHeight)
             (sig.statefulLeafIdx % 2 ^ geom.subtreeHeight)
             (computeHmsgStateful pk sig.rRand (computeMessageMu pk msg)
               (sig.statefulLeafIdx % 2 ^ geom.subtreeHeight) lsig0.tswCtr) lsig0 = some root0)
    (hUp : verifyUpperLayers geom pk 1 (sig.statefulLeafIdx / 2 ^ geom.subtreeHeight) root0 upper = some topRoot)
    (hBadRoot : topRoot ≠ pk.pkRoot) :
    verifyAggNativeSig geom pk msg sig = false := by
  unfold verifyAggNativeSig
  cases hHdr : (!geom.wellFormed || pk.profile != geom.profile || sig.profile != geom.profile ||
                sig.layers.length != geom.numLayers)
  · simp only [Bool.false_eq_true, ↓reduceIte, hLayers, hFors0, beq_self_eq_true]
    unfold verifyAggNativeSigStateful
    cases hSChk : (!sig.forsOpenings.isEmpty ||
                   !(decide (sig.statefulLeafIdx < 2 ^ (geom.numLayers * geom.subtreeHeight))))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hW0]
      dsimp only
      rw [hUp]
      exact beq_false_of_ne hBadRoot
    · rfl
  · rfl

/-- Concrete inhabitedness witness for §1 (`xmssPoseidon2Geom` & `corduroyPoseidon2Geom` geometries +
    non-vacuous EUF-CMA reduction pipeline with concrete seeds and empty signing oracle). -/
def auditSkSeed : Digest4 :=
  ⟨Goldilocks.ofNat 11, Goldilocks.ofNat 22, Goldilocks.ofNat 33, Goldilocks.ofNat 44⟩
def auditPkSeed : Digest4 :=
  ⟨Goldilocks.ofNat 55, Goldilocks.ofNat 66, Goldilocks.ofNat 77, Goldilocks.ofNat 88⟩
def auditRRand : Digest4 :=
  ⟨Goldilocks.ofNat 99, Goldilocks.ofNat 101, Goldilocks.ofNat 102, Goldilocks.ofNat 103⟩
def auditMsg : List UInt8 := [0x51, 0x53, 0x41, 0x47]

theorem inhabited_aggNativeSig_euf_cma_pipeline :
    xmssPoseidon2Geom.wellFormed = true ∧
    corduroyPoseidon2Geom.wellFormed = true ∧
    compactAuditGeom.wellFormed = true ∧
    (∀ (ctrs : ValidSigningCtrs xmssPoseidon2Geom auditSkSeed
                 (deriveAggPublicKey xmssPoseidon2Geom auditSkSeed auditPkSeed)
                 auditMsg auditRRand 0),
      let pk := deriveAggPublicKey xmssPoseidon2Geom auditSkSeed auditPkSeed
      let sig := signAggNative xmssPoseidon2Geom auditSkSeed pk
                   auditMsg auditRRand 0 ctrs.layer0Ctr ctrs.upperCtrs
      verifyAggNativeSig xmssPoseidon2Geom pk auditMsg sig = true ∧
      Nonempty (AggNativeForgeryBreak xmssPoseidon2Geom auditSkSeed pk
                  auditMsg sig.rRand (fun _ _ _ => none) [])) := by
  refine ⟨deployedAggGeometries_wellFormed.1,
          deployedAggGeometries_wellFormed.2.1,
          deployedAggGeometries_wellFormed.2.2,
          fun ctrs => ?_⟩
  have hVer := aggNativeSig_completeness xmssPoseidon2Geom auditSkSeed auditPkSeed
    auditMsg auditRRand 0 deployedAggGeometries_wellFormed.1 ctrs
  refine ⟨hVer, ?_⟩
  exact aggNativeSig_wots_merkle_soundness
    xmssPoseidon2Geom auditSkSeed auditPkSeed auditMsg _ [] (fun _ _ _ => none) []
    (by simp) hVer
    (fun _ _ _ _ h => by cases h)
    (fun _ _ _ _ h => by cases h)
    (fun _ _ _ _ h => by cases h)
    (fun hNe => False.elim (hNe rfl))

/-! ## `GoldilocksExt4` (`field.rs`): the challenge field of the row sumcheck and of WHIR -/

/-! ### Quadratic-extension identities over an arbitrary `LawfulCommRing` -/

private theorem ringMulMulMulComm {R : Type} [LawfulCommRing R] (a b c d : R) :
    CommRingOps.mul (CommRingOps.mul a b) (CommRingOps.mul c d) =
      CommRingOps.mul (CommRingOps.mul a c) (CommRingOps.mul b d) := by
  rw [LawfulCommRing.mul_assoc, ← LawfulCommRing.mul_assoc b c d, LawfulCommRing.mul_comm b c,
    LawfulCommRing.mul_assoc c b d, ← LawfulCommRing.mul_assoc]

private theorem ringEqNegOfAddEqZero {R : Type} [LawfulCommRing R] {a b : R}
    (h : CommRingOps.add a b = CommRingOps.zero) : a = CommRingOps.neg b := by
  have h1 : CommRingOps.add (CommRingOps.add a b) (CommRingOps.neg b) =
      CommRingOps.add CommRingOps.zero (CommRingOps.neg b) :=
    congrArg (fun z => CommRingOps.add z (CommRingOps.neg b)) h
  rw [LawfulCommRing.add_assoc, LawfulCommRing.add_right_neg, LawfulCommRing.add_zero,
    LawfulCommRing.zero_add] at h1
  exact h1

private theorem quadExtMulComm0 {R : Type} [LawfulCommRing R] (n x0 x1 y0 y1 : R) :
    CommRingOps.add (CommRingOps.mul x0 y0) (CommRingOps.mul n (CommRingOps.mul x1 y1)) =
      CommRingOps.add (CommRingOps.mul y0 x0) (CommRingOps.mul n (CommRingOps.mul y1 x1)) := by
  rw [LawfulCommRing.mul_comm x0 y0, LawfulCommRing.mul_comm x1 y1]

private theorem quadExtMulComm1 {R : Type} [LawfulCommRing R] (x0 x1 y0 y1 : R) :
    CommRingOps.add (CommRingOps.mul x0 y1) (CommRingOps.mul x1 y0) =
      CommRingOps.add (CommRingOps.mul y0 x1) (CommRingOps.mul y1 x0) := by
  rw [LawfulCommRing.mul_comm x0 y1, LawfulCommRing.mul_comm x1 y0]
  exact LawfulCommRing.add_comm _ _

private theorem quadExtOneMul0 {R : Type} [LawfulCommRing R] (n x0 x1 : R) :
    CommRingOps.add (CommRingOps.mul CommRingOps.one x0)
      (CommRingOps.mul n (CommRingOps.mul CommRingOps.zero x1)) = x0 := by
  rw [LawfulCommRing.one_mul, LawfulCommRing.zero_mul, LawfulCommRing.mul_zero,
    LawfulCommRing.add_zero]

private theorem quadExtOneMul1 {R : Type} [LawfulCommRing R] (x0 x1 : R) :
    CommRingOps.add (CommRingOps.mul CommRingOps.one x1)
      (CommRingOps.mul CommRingOps.zero x0) = x1 := by
  rw [LawfulCommRing.one_mul, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]

private theorem quadExtMulOne0 {R : Type} [LawfulCommRing R] (n x0 x1 : R) :
    CommRingOps.add (CommRingOps.mul x0 CommRingOps.one)
      (CommRingOps.mul n (CommRingOps.mul x1 CommRingOps.zero)) = x0 := by
  rw [LawfulCommRing.mul_one, LawfulCommRing.mul_zero, LawfulCommRing.mul_zero,
    LawfulCommRing.add_zero]

private theorem quadExtMulOne1 {R : Type} [LawfulCommRing R] (x0 x1 : R) :
    CommRingOps.add (CommRingOps.mul x0 CommRingOps.zero)
      (CommRingOps.mul x1 CommRingOps.one) = x1 := by
  rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_one, LawfulCommRing.zero_add]

private theorem quadExtLeftDistrib0 {R : Type} [LawfulCommRing R] (n x0 x1 y0 y1 z0 z1 : R) :
    CommRingOps.add (CommRingOps.mul x0 (CommRingOps.add y0 z0))
      (CommRingOps.mul n (CommRingOps.mul x1 (CommRingOps.add y1 z1))) =
    CommRingOps.add
      (CommRingOps.add (CommRingOps.mul x0 y0) (CommRingOps.mul n (CommRingOps.mul x1 y1)))
      (CommRingOps.add (CommRingOps.mul x0 z0) (CommRingOps.mul n (CommRingOps.mul x1 z1))) := by
  rw [LawfulCommRing.left_distrib, LawfulCommRing.left_distrib, LawfulCommRing.left_distrib]
  exact LawfulCommRing.add_add_add_comm _ _ _ _

private theorem quadExtLeftDistrib1 {R : Type} [LawfulCommRing R] (x0 x1 y0 y1 z0 z1 : R) :
    CommRingOps.add (CommRingOps.mul x0 (CommRingOps.add y1 z1))
      (CommRingOps.mul x1 (CommRingOps.add y0 z0)) =
    CommRingOps.add
      (CommRingOps.add (CommRingOps.mul x0 y1) (CommRingOps.mul x1 y0))
      (CommRingOps.add (CommRingOps.mul x0 z1) (CommRingOps.mul x1 z0)) := by
  rw [LawfulCommRing.left_distrib, LawfulCommRing.left_distrib]
  exact LawfulCommRing.add_add_add_comm _ _ _ _

private theorem quadExtRightDistrib0 {R : Type} [LawfulCommRing R] (n x0 x1 y0 y1 z0 z1 : R) :
    CommRingOps.add (CommRingOps.mul (CommRingOps.add x0 y0) z0)
      (CommRingOps.mul n (CommRingOps.mul (CommRingOps.add x1 y1) z1)) =
    CommRingOps.add
      (CommRingOps.add (CommRingOps.mul x0 z0) (CommRingOps.mul n (CommRingOps.mul x1 z1)))
      (CommRingOps.add (CommRingOps.mul y0 z0) (CommRingOps.mul n (CommRingOps.mul y1 z1))) := by
  rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib, LawfulCommRing.left_distrib]
  exact LawfulCommRing.add_add_add_comm _ _ _ _

private theorem quadExtRightDistrib1 {R : Type} [LawfulCommRing R] (x0 x1 y0 y1 z0 z1 : R) :
    CommRingOps.add (CommRingOps.mul (CommRingOps.add x0 y0) z1)
      (CommRingOps.mul (CommRingOps.add x1 y1) z0) =
    CommRingOps.add
      (CommRingOps.add (CommRingOps.mul x0 z1) (CommRingOps.mul x1 z0))
      (CommRingOps.add (CommRingOps.mul y0 z1) (CommRingOps.mul y1 z0)) := by
  rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib]
  exact LawfulCommRing.add_add_add_comm _ _ _ _

private theorem quadExtMulAssoc0 {R : Type} [LawfulCommRing R] (n x0 x1 y0 y1 z0 z1 : R) :
    CommRingOps.add
      (CommRingOps.mul
        (CommRingOps.add (CommRingOps.mul x0 y0) (CommRingOps.mul n (CommRingOps.mul x1 y1))) z0)
      (CommRingOps.mul n
        (CommRingOps.mul (CommRingOps.add (CommRingOps.mul x0 y1) (CommRingOps.mul x1 y0)) z1)) =
    CommRingOps.add
      (CommRingOps.mul x0
        (CommRingOps.add (CommRingOps.mul y0 z0) (CommRingOps.mul n (CommRingOps.mul y1 z1))))
      (CommRingOps.mul n
        (CommRingOps.mul x1 (CommRingOps.add (CommRingOps.mul y0 z1) (CommRingOps.mul y1 z0)))) := by
  rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib,
      LawfulCommRing.left_distrib, LawfulCommRing.left_distrib,
      LawfulCommRing.left_distrib, LawfulCommRing.left_distrib]
  have t1 : CommRingOps.mul (CommRingOps.mul x0 y0) z0 =
      CommRingOps.mul x0 (CommRingOps.mul y0 z0) :=
    LawfulCommRing.mul_assoc _ _ _
  have t2 : CommRingOps.mul (CommRingOps.mul n (CommRingOps.mul x1 y1)) z0 =
      CommRingOps.mul n (CommRingOps.mul x1 (CommRingOps.mul y1 z0)) := by
    rw [LawfulCommRing.mul_assoc, LawfulCommRing.mul_assoc]
  have t3 : CommRingOps.mul n (CommRingOps.mul (CommRingOps.mul x0 y1) z1) =
      CommRingOps.mul x0 (CommRingOps.mul n (CommRingOps.mul y1 z1)) := by
    rw [LawfulCommRing.mul_assoc x0 y1 z1,
        ← LawfulCommRing.mul_assoc n x0 _,
        LawfulCommRing.mul_comm n x0,
        LawfulCommRing.mul_assoc]
  have t4 : CommRingOps.mul n (CommRingOps.mul (CommRingOps.mul x1 y0) z1) =
      CommRingOps.mul n (CommRingOps.mul x1 (CommRingOps.mul y0 z1)) := by
    rw [LawfulCommRing.mul_assoc]
  rw [t1, t2, t3, t4, LawfulCommRing.add_add_add_comm]
  congr 1
  exact LawfulCommRing.add_comm _ _

private theorem quadExtMulAssoc1 {R : Type} [LawfulCommRing R] (n x0 x1 y0 y1 z0 z1 : R) :
    CommRingOps.add
      (CommRingOps.mul
        (CommRingOps.add (CommRingOps.mul x0 y0) (CommRingOps.mul n (CommRingOps.mul x1 y1))) z1)
      (CommRingOps.mul
        (CommRingOps.add (CommRingOps.mul x0 y1) (CommRingOps.mul x1 y0)) z0) =
    CommRingOps.add
      (CommRingOps.mul x0
        (CommRingOps.add (CommRingOps.mul y0 z1) (CommRingOps.mul y1 z0)))
      (CommRingOps.mul x1
        (CommRingOps.add (CommRingOps.mul y0 z0) (CommRingOps.mul n (CommRingOps.mul y1 z1)))) := by
  rw [LawfulCommRing.right_distrib, LawfulCommRing.right_distrib,
      LawfulCommRing.left_distrib, LawfulCommRing.left_distrib]
  have s1 : CommRingOps.mul (CommRingOps.mul x0 y0) z1 =
      CommRingOps.mul x0 (CommRingOps.mul y0 z1) :=
    LawfulCommRing.mul_assoc _ _ _
  have s2 : CommRingOps.mul (CommRingOps.mul n (CommRingOps.mul x1 y1)) z1 =
      CommRingOps.mul x1 (CommRingOps.mul n (CommRingOps.mul y1 z1)) := by
    rw [LawfulCommRing.mul_assoc n _ z1,
        LawfulCommRing.mul_assoc x1 y1 z1,
        ← LawfulCommRing.mul_assoc n x1 _,
        LawfulCommRing.mul_comm n x1,
        LawfulCommRing.mul_assoc]
  have s3 : CommRingOps.mul (CommRingOps.mul x0 y1) z0 =
      CommRingOps.mul x0 (CommRingOps.mul y1 z0) :=
    LawfulCommRing.mul_assoc _ _ _
  have s4 : CommRingOps.mul (CommRingOps.mul x1 y0) z0 =
      CommRingOps.mul x1 (CommRingOps.mul y0 z0) :=
    LawfulCommRing.mul_assoc _ _ _
  rw [s1, s2, s3, s4, LawfulCommRing.add_add_add_comm]
  congr 1
  exact LawfulCommRing.add_comm _ _

/-- Karatsuba middle term: `(x0 + x1)(y0 + y1) - x0 y0 - x1 y1 = x0 y1 + x1 y0`. -/
private theorem quadExtKaratsubaMid {R : Type} [LawfulCommRing R] (x0 x1 y0 y1 : R) :
    CommRingOps.sub
      (CommRingOps.sub (CommRingOps.mul (CommRingOps.add x0 x1) (CommRingOps.add y0 y1))
        (CommRingOps.mul x0 y0))
      (CommRingOps.mul x1 y1) =
    CommRingOps.add (CommRingOps.mul x0 y1) (CommRingOps.mul x1 y0) := by
  have hsub : ∀ p q : R, CommRingOps.sub (CommRingOps.add p q) q = p := by
    intro p q
    rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc, LawfulCommRing.add_right_neg,
      LawfulCommRing.add_zero]
  have hexp : CommRingOps.mul (CommRingOps.add x0 x1) (CommRingOps.add y0 y1) =
      CommRingOps.add
        (CommRingOps.add (CommRingOps.add (CommRingOps.mul x0 y1) (CommRingOps.mul x1 y0))
          (CommRingOps.mul x1 y1))
        (CommRingOps.mul x0 y0) := by
    rw [LawfulCommRing.right_distrib, LawfulCommRing.left_distrib, LawfulCommRing.left_distrib,
      LawfulCommRing.add_comm (CommRingOps.mul x0 y0) (CommRingOps.mul x0 y1),
      LawfulCommRing.add_add_add_comm,
      LawfulCommRing.add_comm (CommRingOps.mul x0 y0) (CommRingOps.mul x1 y1),
      ← LawfulCommRing.add_assoc]
  rw [hexp, hsub, hsub]

/-! ### Quartic extension `GoldilocksExt4 = GoldilocksExt2[v] / (v^2 - u)` (`field.rs`) -/

/-- Quartic extension of `Goldilocks` as the quadratic tower over `GoldilocksExt2`
    (`field.rs:GoldilocksExt4`): an element is `c0 + c1 * v` with `v^2 = u` and `u^2 = 7`, so
    `v^4 = 7`. In the limb order of `field.rs:to_limbs`, `[l0, l1, l2, l3]` denotes
    `l0 + l1 * v^2 + l2 * v + l3 * v^3`. -/
structure GoldilocksExt4 where
  c0 : GoldilocksExt2
  c1 : GoldilocksExt2
  deriving DecidableEq, Repr

namespace GoldilocksExt4

/-- Non-residue of the upper quadratic step: `v^2 = u`. -/
def nonResidue : GoldilocksExt2 := GoldilocksExt2.uBasis

theorem ext {x y : GoldilocksExt4} (h0 : x.c0 = y.c0) (h1 : x.c1 = y.c1) : x = y := by
  cases x; cases y; simp only at h0 h1; subst h0 h1; rfl

/-- `field.rs:from_ext2`. -/
def ofExt2 (a : GoldilocksExt2) : GoldilocksExt4 := ⟨a, CommRingOps.zero⟩
/-- `field.rs:from_base`: embedding of the base field. -/
def embedBase (a : Goldilocks) : GoldilocksExt4 := ⟨GoldilocksExt2.ofBase a, CommRingOps.zero⟩
def zero : GoldilocksExt4 := ⟨CommRingOps.zero, CommRingOps.zero⟩
def one : GoldilocksExt4 := ⟨CommRingOps.one, CommRingOps.zero⟩
/-- `field.rs:V`. -/
def vBasis : GoldilocksExt4 := ⟨CommRingOps.zero, CommRingOps.one⟩
/-- `field.rs:from_limbs`. -/
def ofLimbs (l0 l1 l2 l3 : Goldilocks) : GoldilocksExt4 := ⟨⟨l0, l1⟩, ⟨l2, l3⟩⟩
/-- `field.rs:to_limbs`. -/
def toLimbs (x : GoldilocksExt4) : List Goldilocks := [x.c0.c0, x.c0.c1, x.c1.c0, x.c1.c1]

instance : Inhabited GoldilocksExt4 := ⟨zero⟩

def add (x y : GoldilocksExt4) : GoldilocksExt4 :=
  ⟨CommRingOps.add x.c0 y.c0, CommRingOps.add x.c1 y.c1⟩

def neg (x : GoldilocksExt4) : GoldilocksExt4 :=
  ⟨CommRingOps.neg x.c0, CommRingOps.neg x.c1⟩

def sub (x y : GoldilocksExt4) : GoldilocksExt4 :=
  ⟨CommRingOps.sub x.c0 y.c0, CommRingOps.sub x.c1 y.c1⟩

/-- Schoolbook product modulo `v^2 = u`. -/
def mul (x y : GoldilocksExt4) : GoldilocksExt4 :=
  ⟨CommRingOps.add (CommRingOps.mul x.c0 y.c0)
      (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1)),
   CommRingOps.add (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c1 y.c0)⟩

/-- `field.rs:const_mul`: the Karatsuba form with three `GoldilocksExt2` products. -/
def mulKaratsuba (x y : GoldilocksExt4) : GoldilocksExt4 :=
  ⟨CommRingOps.add (CommRingOps.mul x.c0 y.c0)
      (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1)),
   CommRingOps.sub
     (CommRingOps.sub (CommRingOps.mul (CommRingOps.add x.c0 x.c1) (CommRingOps.add y.c0 y.c1))
       (CommRingOps.mul x.c0 y.c0))
     (CommRingOps.mul x.c1 y.c1)⟩

instance : CommRingOps GoldilocksExt4 where
  zero := zero
  one := one
  add := add
  mul := mul
  neg := neg
  sub := sub

instance : LawfulCommRing GoldilocksExt4 where
  add_assoc x y z := by
    apply ext
    · exact LawfulCommRing.add_assoc x.c0 y.c0 z.c0
    · exact LawfulCommRing.add_assoc x.c1 y.c1 z.c1
  add_comm x y := by
    apply ext
    · exact LawfulCommRing.add_comm x.c0 y.c0
    · exact LawfulCommRing.add_comm x.c1 y.c1
  zero_add x := by
    apply ext
    · exact LawfulCommRing.zero_add x.c0
    · exact LawfulCommRing.zero_add x.c1
  add_zero x := by
    apply ext
    · exact LawfulCommRing.add_zero x.c0
    · exact LawfulCommRing.add_zero x.c1
  add_left_neg x := by
    apply ext
    · exact LawfulCommRing.add_left_neg x.c0
    · exact LawfulCommRing.add_left_neg x.c1
  sub_eq_add_neg x y := by
    apply ext
    · exact LawfulCommRing.sub_eq_add_neg x.c0 y.c0
    · exact LawfulCommRing.sub_eq_add_neg x.c1 y.c1
  mul_comm x y := by
    apply ext
    · exact quadExtMulComm0 nonResidue x.c0 x.c1 y.c0 y.c1
    · exact quadExtMulComm1 x.c0 x.c1 y.c0 y.c1
  one_mul x := by
    apply ext
    · exact quadExtOneMul0 nonResidue x.c0 x.c1
    · exact quadExtOneMul1 x.c0 x.c1
  mul_one x := by
    apply ext
    · exact quadExtMulOne0 nonResidue x.c0 x.c1
    · exact quadExtMulOne1 x.c0 x.c1
  left_distrib x y z := by
    apply ext
    · exact quadExtLeftDistrib0 nonResidue x.c0 x.c1 y.c0 y.c1 z.c0 z.c1
    · exact quadExtLeftDistrib1 x.c0 x.c1 y.c0 y.c1 z.c0 z.c1
  right_distrib x y z := by
    apply ext
    · exact quadExtRightDistrib0 nonResidue x.c0 x.c1 y.c0 y.c1 z.c0 z.c1
    · exact quadExtRightDistrib1 x.c0 x.c1 y.c0 y.c1 z.c0 z.c1
  mul_assoc x y z := by
    apply ext
    · exact quadExtMulAssoc0 nonResidue x.c0 x.c1 y.c0 y.c1 z.c0 z.c1
    · exact quadExtMulAssoc1 nonResidue x.c0 x.c1 y.c0 y.c1 z.c0 z.c1

/-- Commutativity of the quartic-extension product. -/
theorem mul_comm (x y : GoldilocksExt4) : CommRingOps.mul x y = CommRingOps.mul y x :=
  LawfulCommRing.mul_comm x y

/-- Associativity of the quartic-extension product. -/
theorem mul_assoc (x y z : GoldilocksExt4) :
    CommRingOps.mul (CommRingOps.mul x y) z = CommRingOps.mul x (CommRingOps.mul y z) :=
  LawfulCommRing.mul_assoc x y z

theorem add_comm (x y : GoldilocksExt4) : CommRingOps.add x y = CommRingOps.add y x :=
  LawfulCommRing.add_comm x y

theorem add_assoc (x y z : GoldilocksExt4) :
    CommRingOps.add (CommRingOps.add x y) z = CommRingOps.add x (CommRingOps.add y z) :=
  LawfulCommRing.add_assoc x y z

/-- `zero = (0, 0, 0, 0)` is the additive identity and `neg` the additive inverse. -/
theorem add_identity_inverse (x : GoldilocksExt4) :
    CommRingOps.add zero x = x ∧ CommRingOps.add x zero = x ∧
    CommRingOps.add (CommRingOps.neg x) x = zero ∧ CommRingOps.add x (CommRingOps.neg x) = zero :=
  ⟨LawfulCommRing.zero_add x, LawfulCommRing.add_zero x, LawfulCommRing.add_left_neg x,
    LawfulCommRing.add_right_neg x⟩

/-- `one = (1, 0, 0, 0)` is the multiplicative identity. -/
theorem mul_identity (x : GoldilocksExt4) :
    one = ofLimbs Goldilocks.one Goldilocks.zero Goldilocks.zero Goldilocks.zero ∧
    CommRingOps.mul one x = x ∧ CommRingOps.mul x one = x :=
  ⟨by rfl, LawfulCommRing.one_mul x, LawfulCommRing.mul_one x⟩

/-- `field.rs:const_mul` (Karatsuba) computes the schoolbook product. -/
theorem mulKaratsuba_eq_mul (x y : GoldilocksExt4) : mulKaratsuba x y = CommRingOps.mul x y := by
  apply ext
  · rfl
  · exact quadExtKaratsubaMid x.c0 x.c1 y.c0 y.c1

/-- `v^2 = u`. -/
theorem vBasis_sq : CommRingOps.mul vBasis vBasis = ofExt2 GoldilocksExt2.uBasis := by decide

/-- `v^4 = 7`: the tower is `Goldilocks[v] / (v^4 - 7)`. -/
theorem vBasis_pow_four :
    CommRingOps.mul (CommRingOps.mul vBasis vBasis) (CommRingOps.mul vBasis vBasis) =
      embedBase GoldilocksExt2.nonResidue := by decide

theorem embedBase_zero : embedBase Goldilocks.zero = zero := by rfl

theorem embedBase_one : embedBase Goldilocks.one = one := by rfl

theorem embedBase_injective {a b : Goldilocks} (h : embedBase a = embedBase b) : a = b :=
  GoldilocksExt2.ofBase_injective (congrArg c0 h)

theorem embedBase_add (a b : Goldilocks) :
    embedBase (CommRingOps.add a b) = CommRingOps.add (embedBase a) (embedBase b) := by
  apply ext
  · exact GoldilocksExt2.ofBase_add a b
  · exact (LawfulCommRing.add_zero (CommRingOps.zero : GoldilocksExt2)).symm

theorem embedBase_neg (a : Goldilocks) :
    embedBase (CommRingOps.neg a) = CommRingOps.neg (embedBase a) := by
  apply ext
  · apply GoldilocksExt2.ext
    · rfl
    · exact (LawfulCommRing.neg_zero Goldilocks).symm
  · exact (LawfulCommRing.neg_zero GoldilocksExt2).symm

private theorem quadExtEmbedMul0 {R : Type} [LawfulCommRing R] (n p : R) :
    p = CommRingOps.add p (CommRingOps.mul n (CommRingOps.mul CommRingOps.zero CommRingOps.zero)) := by
  rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

private theorem quadExtEmbedMul1 {R : Type} [LawfulCommRing R] (a b : R) :
    (CommRingOps.zero : R) =
      CommRingOps.add (CommRingOps.mul a CommRingOps.zero) (CommRingOps.mul CommRingOps.zero b) := by
  rw [LawfulCommRing.mul_zero, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]

theorem embedBase_mul (a b : Goldilocks) :
    embedBase (CommRingOps.mul a b) = CommRingOps.mul (embedBase a) (embedBase b) := by
  apply ext
  · exact (GoldilocksExt2.ofBase_mul a b).trans
      (quadExtEmbedMul0 nonResidue
        (CommRingOps.mul (GoldilocksExt2.ofBase a) (GoldilocksExt2.ofBase b)))
  · exact quadExtEmbedMul1 (GoldilocksExt2.ofBase a) (GoldilocksExt2.ofBase b)

theorem embedBase_sub (a b : Goldilocks) :
    embedBase (CommRingOps.sub a b) = CommRingOps.sub (embedBase a) (embedBase b) :=
  (congrArg embedBase (LawfulCommRing.sub_eq_add_neg a b)).trans
    ((embedBase_add a (CommRingOps.neg b)).trans
      ((congrArg (CommRingOps.add (embedBase a)) (embedBase_neg b)).trans
        (LawfulCommRing.sub_eq_add_neg (embedBase a) (embedBase b)).symm))

/-- `embedBase` is a ring homomorphism `Goldilocks → GoldilocksExt4`. -/
theorem embedBase_homomorphism (a b : Goldilocks) :
    embedBase Goldilocks.zero = zero ∧ embedBase Goldilocks.one = one ∧
    embedBase (CommRingOps.add a b) = CommRingOps.add (embedBase a) (embedBase b) ∧
    embedBase (CommRingOps.mul a b) = CommRingOps.mul (embedBase a) (embedBase b) ∧
    embedBase (CommRingOps.neg a) = CommRingOps.neg (embedBase a) :=
  ⟨embedBase_zero, embedBase_one, embedBase_add a b, embedBase_mul a b, embedBase_neg a⟩

/-- `2^48`: a square root of `-1` in `Goldilocks`, since `2^96 ≡ -1 (mod p)`. -/
def sqrtNegOne : Goldilocks := Goldilocks.ofNat 281474976710656

theorem sqrtNegOne_sq :
    CommRingOps.mul sqrtNegOne sqrtNegOne = CommRingOps.neg (CommRingOps.one : Goldilocks) := by
  apply Goldilocks.ext
  show (Goldilocks.mul sqrtNegOne sqrtNegOne).val = (Goldilocks.neg Goldilocks.one).val
  rw [Goldilocks.mul_val, Goldilocks.neg_val]
  decide

/-- `u` has no square root in `GoldilocksExt2`, so `v^2 - u` is irreducible over it. A root
    `a + b u` would give `a^2 + 7 b^2 = 0` with `b ≠ 0`, hence `(2^48 * a / b)^2 = 7`,
    contradicting `GoldilocksExt2.nonResidue_not_square`. -/
theorem nonResidue_not_square (y : GoldilocksExt2) : CommRingOps.mul y y ≠ nonResidue := by
  intro hsq
  have h0 : CommRingOps.add (CommRingOps.mul y.c0 y.c0)
      (CommRingOps.mul GoldilocksExt2.nonResidue (CommRingOps.mul y.c1 y.c1)) =
      (CommRingOps.zero : Goldilocks) := congrArg GoldilocksExt2.c0 hsq
  have h1 : CommRingOps.add (CommRingOps.mul y.c0 y.c1) (CommRingOps.mul y.c1 y.c0) =
      (CommRingOps.one : Goldilocks) := congrArg GoldilocksExt2.c1 hsq
  if hb : y.c1 = Goldilocks.zero then
    rw [hb] at h1
    have h1' : CommRingOps.add (CommRingOps.mul y.c0 (CommRingOps.zero : Goldilocks))
        (CommRingOps.mul (CommRingOps.zero : Goldilocks) y.c0) =
        (CommRingOps.one : Goldilocks) := h1
    rw [LawfulCommRing.mul_zero, LawfulCommRing.zero_mul, LawfulCommRing.add_zero] at h1'
    exact absurd (congrArg Goldilocks.val h1') (by decide)
  else
    have hbi : CommRingOps.mul y.c1 (Goldilocks.inv y.c1) = (CommRingOps.one : Goldilocks) :=
      Goldilocks.mul_inv_cancel hb
    have h0' : CommRingOps.mul y.c0 y.c0 =
        CommRingOps.neg (CommRingOps.mul GoldilocksExt2.nonResidue (CommRingOps.mul y.c1 y.c1)) :=
      ringEqNegOfAddEqZero h0
    have ht : CommRingOps.mul (CommRingOps.mul y.c0 (Goldilocks.inv y.c1))
        (CommRingOps.mul y.c0 (Goldilocks.inv y.c1)) =
        CommRingOps.neg GoldilocksExt2.nonResidue := by
      rw [ringMulMulMulComm y.c0 (Goldilocks.inv y.c1) y.c0 (Goldilocks.inv y.c1), h0',
        LawfulCommRing.neg_mul, LawfulCommRing.mul_assoc,
        ringMulMulMulComm y.c1 y.c1 (Goldilocks.inv y.c1) (Goldilocks.inv y.c1), hbi,
        LawfulCommRing.mul_one, LawfulCommRing.mul_one]
    have hq : CommRingOps.mul
        (CommRingOps.mul sqrtNegOne (CommRingOps.mul y.c0 (Goldilocks.inv y.c1)))
        (CommRingOps.mul sqrtNegOne (CommRingOps.mul y.c0 (Goldilocks.inv y.c1))) =
        GoldilocksExt2.nonResidue := by
      rw [ringMulMulMulComm sqrtNegOne (CommRingOps.mul y.c0 (Goldilocks.inv y.c1)) sqrtNegOne
          (CommRingOps.mul y.c0 (Goldilocks.inv y.c1)),
        sqrtNegOne_sq, ht, LawfulCommRing.mul_neg, LawfulCommRing.neg_mul,
        LawfulCommRing.one_mul, LawfulCommRing.neg_neg]
    exact GoldilocksExt2.nonResidue_not_square _ hq

/-- Relative norm to `GoldilocksExt2` (`field.rs:norm_to_ext2`). -/
def norm (z : GoldilocksExt4) : GoldilocksExt2 :=
  CommRingOps.sub (CommRingOps.mul z.c0 z.c0)
    (CommRingOps.mul nonResidue (CommRingOps.mul z.c1 z.c1))

theorem norm_ne_zero {z : GoldilocksExt4} (hz : z ≠ zero) : norm z ≠ GoldilocksExt2.zero := by
  intro hnorm
  change CommRingOps.sub (CommRingOps.mul z.c0 z.c0)
      (CommRingOps.mul nonResidue (CommRingOps.mul z.c1 z.c1)) =
      CommRingOps.zero at hnorm
  have hEq : CommRingOps.mul z.c0 z.c0 =
      CommRingOps.mul nonResidue (CommRingOps.mul z.c1 z.c1) :=
    LawfulCommRing.sub_eq_zero_iff.mp hnorm
  if hc1 : z.c1 = GoldilocksExt2.zero then
    have hrhs : CommRingOps.mul nonResidue (CommRingOps.mul z.c1 z.c1) =
        GoldilocksExt2.zero := by
      rw [hc1]
      change CommRingOps.mul nonResidue
        (CommRingOps.mul CommRingOps.zero CommRingOps.zero) = CommRingOps.zero
      rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_zero]
    rw [hrhs] at hEq
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hEq with hc0 | hc0 <;>
      exact hz (ext hc0 hc1)
  else
    let q := CommRingOps.mul z.c0 (GoldilocksExt2.inv z.c1)
    have hqSq : CommRingOps.mul q q = nonResidue := by
      dsimp only [q]
      have hassoc : CommRingOps.mul (CommRingOps.mul z.c0 (GoldilocksExt2.inv z.c1))
          (CommRingOps.mul z.c0 (GoldilocksExt2.inv z.c1)) =
          CommRingOps.mul (CommRingOps.mul z.c0 z.c0)
            (CommRingOps.mul (GoldilocksExt2.inv z.c1) (GoldilocksExt2.inv z.c1)) :=
        ringMulMulMulComm _ _ _ _
      rw [hassoc, hEq, LawfulCommRing.mul_assoc nonResidue]
      have hcancel : CommRingOps.mul (CommRingOps.mul z.c1 z.c1)
          (CommRingOps.mul (GoldilocksExt2.inv z.c1) (GoldilocksExt2.inv z.c1)) =
          CommRingOps.one := by
        rw [ringMulMulMulComm z.c1 z.c1 (GoldilocksExt2.inv z.c1) (GoldilocksExt2.inv z.c1),
          GoldilocksExt2.mul_inv_cancel hc1, LawfulCommRing.one_mul]
      rw [hcancel, LawfulCommRing.mul_one]
    exact nonResidue_not_square q hqSq

/-- Field inverse via the relative norm (`field.rs:inv`); `inv zero = zero`. -/
def inv (z : GoldilocksExt4) : GoldilocksExt4 :=
  ⟨CommRingOps.mul z.c0 (GoldilocksExt2.inv (norm z)),
   CommRingOps.neg (CommRingOps.mul z.c1 (GoldilocksExt2.inv (norm z)))⟩

theorem mul_inv_cancel {z : GoldilocksExt4} (hz : z ≠ zero) :
    CommRingOps.mul z (inv z) = CommRingOps.one := by
  have hnormNe := norm_ne_zero hz
  apply ext
  · change CommRingOps.add
        (CommRingOps.mul z.c0 (CommRingOps.mul z.c0 (GoldilocksExt2.inv (norm z))))
        (CommRingOps.mul nonResidue
          (CommRingOps.mul z.c1
            (CommRingOps.neg (CommRingOps.mul z.c1 (GoldilocksExt2.inv (norm z)))))) =
      CommRingOps.one
    rw [← LawfulCommRing.mul_assoc z.c0 z.c0 (GoldilocksExt2.inv (norm z)),
        LawfulCommRing.mul_neg z.c1, LawfulCommRing.mul_neg nonResidue,
        ← LawfulCommRing.mul_assoc z.c1 z.c1 (GoldilocksExt2.inv (norm z)),
        ← LawfulCommRing.mul_assoc nonResidue _ (GoldilocksExt2.inv (norm z)),
        ← LawfulCommRing.sub_eq_add_neg,
        ← LawfulCommRing.sub_mul]
    exact GoldilocksExt2.mul_inv_cancel hnormNe
  · change CommRingOps.add
        (CommRingOps.mul z.c0
          (CommRingOps.neg (CommRingOps.mul z.c1 (GoldilocksExt2.inv (norm z)))))
        (CommRingOps.mul z.c1 (CommRingOps.mul z.c0 (GoldilocksExt2.inv (norm z)))) =
      CommRingOps.zero
    rw [LawfulCommRing.mul_neg,
        ← LawfulCommRing.mul_assoc z.c0 z.c1 (GoldilocksExt2.inv (norm z)),
        ← LawfulCommRing.mul_assoc z.c1 z.c0 (GoldilocksExt2.inv (norm z)),
        LawfulCommRing.mul_comm z.c1 z.c0,
        LawfulCommRing.add_left_neg]

end GoldilocksExt4

/-- `GoldilocksExt4` is a field: it has no zero divisors. -/
instance : NoZeroDivisors GoldilocksExt4 where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    if ha : a = GoldilocksExt4.zero then
      exact .inl ha
    else
      right
      have hmul := congrArg (CommRingOps.mul (GoldilocksExt4.inv a)) h
      rw [LawfulCommRing.mul_zero, ← LawfulCommRing.mul_assoc,
          LawfulCommRing.mul_comm (GoldilocksExt4.inv a) a,
          GoldilocksExt4.mul_inv_cancel ha, LawfulCommRing.one_mul] at hmul
      exact hmul

/-! ## §2. Exact Degree-8 Row Sumcheck Arithmetization (`arithmetize.rs`, `trace.rs`, `ROW_SUMCHECK_DEGREE = 8`) -/

/-- Exact degree of each row-sumcheck univariate round polynomial (`1` from `eq(tau, x)` + `7` from `x^7`). -/
def rowSumcheckDegree : Nat := 8

/-- Number of `GoldilocksExt4` coefficients per row-sumcheck round polynomial (`8 + 1 = 9`). -/
def rowSumcheckCoeffs : Nat := 9

/-! ### Univariate Polynomial Ring Algebra & Exact Degree-8 Bound -/

private theorem ext4_one_eq : GoldilocksExt4.one = (CommRingOps.one : GoldilocksExt4) := by rfl
private theorem ext4_zero_eq : GoldilocksExt4.zero = (CommRingOps.zero : GoldilocksExt4) := by rfl
private theorem gold_one_eq : Goldilocks.one = (CommRingOps.one : Goldilocks) := by rfl
private theorem gold_zero_eq : Goldilocks.zero = (CommRingOps.zero : Goldilocks) := by rfl

/-- Ring identity behind the affine form of the equality factor:
    `(1 - τ) + x · (τ - (1 - τ)) = (1 - τ) · (1 - x) + τ · x`. -/
private theorem eqFactor_affine_identity {R : Type} [LawfulCommRing R] (tau x : R) :
    CommRingOps.add (CommRingOps.sub CommRingOps.one tau)
        (CommRingOps.mul x (CommRingOps.sub tau (CommRingOps.sub CommRingOps.one tau))) =
      CommRingOps.add
        (CommRingOps.mul (CommRingOps.sub CommRingOps.one tau) (CommRingOps.sub CommRingOps.one x))
        (CommRingOps.mul tau x) := by
  rw [LawfulCommRing.sub_eq_add_neg CommRingOps.one x,
      LawfulCommRing.left_distrib (CommRingOps.sub CommRingOps.one tau) CommRingOps.one (CommRingOps.neg x),
      LawfulCommRing.mul_one,
      LawfulCommRing.mul_neg,
      LawfulCommRing.add_assoc (CommRingOps.sub CommRingOps.one tau)]
  congr 1
  rw [LawfulCommRing.mul_comm (CommRingOps.sub CommRingOps.one tau) x,
      LawfulCommRing.mul_comm tau x,
      ← LawfulCommRing.mul_neg x (CommRingOps.sub CommRingOps.one tau),
      ← LawfulCommRing.left_distrib x,
      LawfulCommRing.add_comm (CommRingOps.neg (CommRingOps.sub CommRingOps.one tau)) tau,
      ← LawfulCommRing.sub_eq_add_neg]

def polyAddCoeffs {R : Type} [CommRingOps R] : List R → List R → List R
  | [], ds => ds
  | cs, [] => cs
  | c :: cs, d :: ds => CommRingOps.add c d :: polyAddCoeffs cs ds

theorem polyAddCoeffs_length {R : Type} [CommRingOps R] :
    ∀ (cs ds : List R), (polyAddCoeffs cs ds).length = Nat.max cs.length ds.length
  | [], ds => by simp [polyAddCoeffs]
  | c :: cs, [] => by simp [polyAddCoeffs]
  | c :: cs, d :: ds => by
    simp [polyAddCoeffs, polyAddCoeffs_length cs ds, Nat.succ_max_succ]

theorem evalCoeffs_polyAddCoeffs {R : Type} [LawfulCommRing R] :
    ∀ (cs ds : List R) (x : R),
      RoundPoly.evalCoeffs (polyAddCoeffs cs ds) x =
        CommRingOps.add (RoundPoly.evalCoeffs cs x) (RoundPoly.evalCoeffs ds x)
  | [], ds, x => by
    simp [polyAddCoeffs, RoundPoly.evalCoeffs, LawfulCommRing.zero_add]
  | c :: cs, [], x => by
    simp [polyAddCoeffs, RoundPoly.evalCoeffs, LawfulCommRing.add_zero]
  | c :: cs, d :: ds, x => by
    simp only [polyAddCoeffs, RoundPoly.evalCoeffs, evalCoeffs_polyAddCoeffs cs ds x]
    rw [LawfulCommRing.left_distrib, LawfulCommRing.add_add_add_comm]

def polyScaleCoeffs {R : Type} [CommRingOps R] (s : R) : List R → List R
  | [] => []
  | c :: cs => CommRingOps.mul s c :: polyScaleCoeffs s cs

theorem polyScaleCoeffs_length {R : Type} [CommRingOps R] (s : R) :
    ∀ (cs : List R), (polyScaleCoeffs s cs).length = cs.length
  | [] => rfl
  | _ :: cs => by simp [polyScaleCoeffs, polyScaleCoeffs_length s cs]

theorem evalCoeffs_polyScaleCoeffs {R : Type} [LawfulCommRing R] (s : R) :
    ∀ (cs : List R) (x : R),
      RoundPoly.evalCoeffs (polyScaleCoeffs s cs) x =
        CommRingOps.mul s (RoundPoly.evalCoeffs cs x)
  | [], _ => by
    simp [polyScaleCoeffs, RoundPoly.evalCoeffs, LawfulCommRing.mul_zero]
  | c :: cs, x => by
    simp only [polyScaleCoeffs, RoundPoly.evalCoeffs, evalCoeffs_polyScaleCoeffs s cs x]
    rw [LawfulCommRing.left_distrib,
        ← LawfulCommRing.mul_assoc s x _,
        LawfulCommRing.mul_comm s x,
        LawfulCommRing.mul_assoc x s _]

def polyMulCoeffs {R : Type} [CommRingOps R] : List R → List R → List R
  | [], _ => []
  | c :: rest, ds =>
    match rest with
    | [] => polyScaleCoeffs c ds
    | c1 :: cs =>
      polyAddCoeffs (polyScaleCoeffs c ds) (CommRingOps.zero :: polyMulCoeffs (c1 :: cs) ds)
  termination_by structural cs _ => cs

theorem polyMulCoeffs_length_le {R : Type} [CommRingOps R] :
    ∀ (cs ds : List R) (d1 d2 : Nat),
      cs.length ≤ d1 + 1 →
      ds.length ≤ d2 + 1 →
      (polyMulCoeffs cs ds).length ≤ d1 + d2 + 1
  | [], _, _, _, _, _ => by simp [polyMulCoeffs]
  | c :: rest, ds, d1, d2, h1, h2 =>
    match rest, h1 with
    | [], _ => by
      simp only [polyMulCoeffs, polyScaleCoeffs_length]
      omega
    | c1 :: cs, h1 => by
      cases d1 with
      | zero =>
        simp only [List.length_cons] at h1
        omega
      | succ d1' =>
        have hTail : (c1 :: cs).length ≤ d1' + 1 := by
          simp only [List.length_cons] at h1 ⊢
          omega
        have ih := polyMulCoeffs_length_le (c1 :: cs) ds d1' d2 hTail h2
        simp only [polyMulCoeffs, polyAddCoeffs_length, polyScaleCoeffs_length, List.length_cons]
        exact Nat.max_le.mpr ⟨by omega, by omega⟩
  termination_by structural cs _ _ _ _ _ => cs

theorem evalCoeffs_polyMulCoeffs {R : Type} [LawfulCommRing R] :
    ∀ (cs ds : List R) (x : R),
      RoundPoly.evalCoeffs (polyMulCoeffs cs ds) x =
        CommRingOps.mul (RoundPoly.evalCoeffs cs x) (RoundPoly.evalCoeffs ds x)
  | [], _, _ => by
    simp [polyMulCoeffs, RoundPoly.evalCoeffs, LawfulCommRing.zero_mul]
  | c :: rest, ds, x =>
    match rest with
    | [] => by
      simp only [polyMulCoeffs, RoundPoly.evalCoeffs, evalCoeffs_polyScaleCoeffs,
        LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    | c1 :: cs => by
      let tl := c1 :: cs
      have ih := evalCoeffs_polyMulCoeffs tl ds x
      simp only [polyMulCoeffs, evalCoeffs_polyAddCoeffs, evalCoeffs_polyScaleCoeffs,
        RoundPoly.evalCoeffs, LawfulCommRing.zero_add]
      rw [ih, ← LawfulCommRing.mul_assoc x (RoundPoly.evalCoeffs tl x) _,
          ← LawfulCommRing.right_distrib]
      rfl
  termination_by structural cs _ _ => cs

/-- Affine column interpolation `L(t) = v0 + t * (v1 - v0)` (`length = 2`, degree `≤ 1`). -/
def affineColPoly (v0 v1 : GoldilocksExt4) : List GoldilocksExt4 :=
  [v0, CommRingOps.sub v1 v0]

theorem affineColPoly_length (v0 v1 : GoldilocksExt4) :
    (affineColPoly v0 v1).length = 2 := by simp [affineColPoly]

theorem evalCoeffs_affineColPoly_zero (v0 v1 : GoldilocksExt4) :
    RoundPoly.evalCoeffs (affineColPoly v0 v1) GoldilocksExt4.zero = v0 := by
  change CommRingOps.add v0 (CommRingOps.mul CommRingOps.zero _) = v0
  rw [LawfulCommRing.zero_mul, LawfulCommRing.add_zero]

theorem evalCoeffs_affineColPoly_one (v0 v1 : GoldilocksExt4) :
    RoundPoly.evalCoeffs (affineColPoly v0 v1) GoldilocksExt4.one = v1 := by
  change CommRingOps.add v0
    (CommRingOps.mul CommRingOps.one
      (CommRingOps.add (CommRingOps.sub v1 v0) (CommRingOps.mul CommRingOps.one CommRingOps.zero))) = v1
  rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero, LawfulCommRing.one_mul,
      LawfulCommRing.add_sub_cancel_left]

/-- Equality factor `(1 - tau) * (1 - x) + tau * x` over `GoldilocksExt4`. -/
def eqFactorExt4 (tau x : GoldilocksExt4) : GoldilocksExt4 :=
  CommRingOps.add
    (CommRingOps.mul (CommRingOps.sub GoldilocksExt4.one tau) (CommRingOps.sub GoldilocksExt4.one x))
    (CommRingOps.mul tau x)

/-- Univariate degree-1 polynomial representation of `eqFactorExt4 tau` (`length = 2`). -/
def eqFactorPoly (tau : GoldilocksExt4) : List GoldilocksExt4 :=
  affineColPoly (CommRingOps.sub GoldilocksExt4.one tau) tau

theorem eqFactorPoly_length (tau : GoldilocksExt4) :
    (eqFactorPoly tau).length = 2 := by simp [eqFactorPoly, affineColPoly]

theorem evalCoeffs_eqFactorPoly (tau x : GoldilocksExt4) :
    RoundPoly.evalCoeffs (eqFactorPoly tau) x = eqFactorExt4 tau x := by
  unfold eqFactorPoly affineColPoly eqFactorExt4
  simp only [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  exact eqFactor_affine_identity tau x

/-- Degree-7 algebraic S-box lifted to `GoldilocksExt4`. -/
def ext4Pow7 (x : GoldilocksExt4) : GoldilocksExt4 :=
  let x2 := CommRingOps.mul x x
  let x3 := CommRingOps.mul x2 x
  let x4 := CommRingOps.mul x2 x2
  CommRingOps.mul x3 x4

theorem ext4Pow7_embedBase (a : Goldilocks) :
    ext4Pow7 (GoldilocksExt4.embedBase a) = GoldilocksExt4.embedBase (sbox7 a) := by
  unfold ext4Pow7 sbox7
  simp only [← GoldilocksExt4.embedBase_mul]
  rfl

/-- Univariate polynomial composition `p(t)^7` (`deg(p) ≤ 1 ⟹ deg(p^7) ≤ 7`, `length ≤ 8`). -/
def polyPow7 (p : List GoldilocksExt4) : List GoldilocksExt4 :=
  let p2 := polyMulCoeffs p p
  let p3 := polyMulCoeffs p2 p
  let p4 := polyMulCoeffs p2 p2
  polyMulCoeffs p3 p4

theorem polyPow7_length_le_eight {p : List GoldilocksExt4} (hp : p.length ≤ 2) :
    (polyPow7 p).length ≤ 8 := by
  unfold polyPow7
  have hp2 := polyMulCoeffs_length_le p p 1 1 hp hp
  have hp3 := polyMulCoeffs_length_le (polyMulCoeffs p p) p 2 1 hp2 hp
  have hp4 := polyMulCoeffs_length_le (polyMulCoeffs p p) (polyMulCoeffs p p) 2 2 hp2 hp2
  exact polyMulCoeffs_length_le _ _ 3 4 hp3 hp4

theorem evalCoeffs_polyPow7 (p : List GoldilocksExt4) (x : GoldilocksExt4) :
    RoundPoly.evalCoeffs (polyPow7 p) x = ext4Pow7 (RoundPoly.evalCoeffs p x) := by
  unfold polyPow7 ext4Pow7
  simp [evalCoeffs_polyMulCoeffs]

/-- **Exact Degree-8 Row-Sumcheck Round Polynomial Bound (`rowSumcheckRoundPoly_spec`)**:
    Multiplying the degree-1 equality factor `eq(tau_j, t)` by any degree-`≤ 7` batched row
    constraint polynomial `cPoly` (`cPoly.length ≤ 8`) produces a univariate polynomial of
    at most `rowSumcheckCoeffs = 9` `GoldilocksExt4` coefficients (`ROW_SUMCHECK_DEGREE = 8`)! -/
def buildRowSumcheckRoundPoly (tau_j : GoldilocksExt4) (cPoly : List GoldilocksExt4) :
    List GoldilocksExt4 :=
  polyMulCoeffs (eqFactorPoly tau_j) cPoly

theorem rowSumcheckRoundPoly_spec (tau_j : GoldilocksExt4) (cPoly : List GoldilocksExt4)
    (hDeg7 : cPoly.length ≤ 8) :
    (buildRowSumcheckRoundPoly tau_j cPoly).length ≤ rowSumcheckCoeffs ∧
    (∀ x : GoldilocksExt4,
      RoundPoly.evalCoeffs (buildRowSumcheckRoundPoly tau_j cPoly) x =
        CommRingOps.mul (eqFactorExt4 tau_j x) (RoundPoly.evalCoeffs cPoly x)) := by
  refine ⟨?_, fun x => ?_⟩
  · unfold buildRowSumcheckRoundPoly rowSumcheckCoeffs
    exact polyMulCoeffs_length_le (eqFactorPoly tau_j) cPoly 1 7 (by simp [eqFactorPoly, affineColPoly]) hDeg7
  · unfold buildRowSumcheckRoundPoly
    rw [evalCoeffs_polyMulCoeffs, evalCoeffs_eqFactorPoly]

/-- **Degree-8 Tightness (`rowSumcheckPoly_attains_degree_8`)**:
    On affine column `L(t) = t` (`v0 = 0, v1 = 1`) and `tau_j = 1`, `eq(1, t) · L(t)^7 = t^8`
    has exact length `9` with non-zero degree-8 leading coefficient `1`! -/
theorem rowSumcheckPoly_attains_degree_8 :
    let lPoly := affineColPoly GoldilocksExt4.zero GoldilocksExt4.one
    let rPoly := buildRowSumcheckRoundPoly GoldilocksExt4.one (polyPow7 lPoly)
    rPoly.length = rowSumcheckCoeffs ∧
    rPoly[8]? = some GoldilocksExt4.one := by
  decide +kernel

/-! ### Multilinear Equality & Inter-Row Shift Kernel (`arithmetize.rs:66-106`) -/

/-- Hypercube bit-vector encoding of `u < 2^ell` (LSB-first `GoldilocksExt4` 0/1 coordinates). -/
def hypercubePointExt4 : Nat → Nat → List GoldilocksExt4
  | 0, _ => []
  | ell + 1, u =>
    (if u % 2 == 0 then GoldilocksExt4.zero else GoldilocksExt4.one) ::
      hypercubePointExt4 ell (u / 2)

/-- Polymorphic zip-product over `{R : Type}` (compiles to pure `List.rec` in `< 1ms`). -/
private def evalZipProdPoly {R : Type} (oneVal zeroVal : R) (mulFn factorFn : R → R → R) :
    List R → List R → R
  | [], [] => oneVal
  | t :: ts, x :: xs => mulFn (factorFn t x) (evalZipProdPoly oneVal zeroVal mulFn factorFn ts xs)
  | [], _ :: _ => zeroVal
  | _ :: _, [] => zeroVal

/-- Multilinear equality kernel `eq(tau, rx) = ∏_j eqFactorExt4 tau[j] rx[j]`. -/
def evalEqExt4 (tau rx : List GoldilocksExt4) : GoldilocksExt4 :=
  evalZipProdPoly GoldilocksExt4.one GoldilocksExt4.zero CommRingOps.mul eqFactorExt4 tau rx

private theorem eqFactorExt4_bit_self (b : Bool) :
    let xb := if b then GoldilocksExt4.one else GoldilocksExt4.zero
    eqFactorExt4 xb xb = GoldilocksExt4.one := by
  cases b <;> decide +kernel

private theorem eqFactorExt4_bit_diff (b1 b2 : Bool) (hNe : b1 ≠ b2) :
    let x1 := if b1 then GoldilocksExt4.one else GoldilocksExt4.zero
    let x2 := if b2 then GoldilocksExt4.one else GoldilocksExt4.zero
    eqFactorExt4 x1 x2 = GoldilocksExt4.zero := by
  cases b1 <;> cases b2
  · exact False.elim (hNe rfl)
  · decide +kernel
  · decide +kernel
  · exact False.elim (hNe rfl)

private theorem lt_two_eq_of_beq_zero_eq :
    ∀ {a b : Nat}, a < 2 → b < 2 → (a == 0) = (b == 0) → a = b
  | 0, 0, _, _, _ => rfl
  | 1, 1, _, _, _ => rfl
  | 0, 1, _, _, h => absurd h (by decide)
  | 1, 0, _, _, h => absurd h (by decide)
  | _ + 2, _, ha, _, _ => absurd ha (Nat.not_lt_of_le (Nat.le_add_left 2 _))
  | _, _ + 2, _, hb, _ => absurd hb (Nat.not_lt_of_le (Nat.le_add_left 2 _))

/-- On `{0, 1}^ell`, `evalEqExt4 (hypercubePointExt4 ell u) (hypercubePointExt4 ell v)` is the
    exact Kronecker delta `if u = v then 1 else 0` (`u, v < 2^ell`). -/
theorem evalEqExt4_hypercube_kronecker :
    ∀ (ell u v : Nat),
      u < 2 ^ ell → v < 2 ^ ell →
      evalEqExt4 (hypercubePointExt4 ell u) (hypercubePointExt4 ell v) =
        if u = v then GoldilocksExt4.one else GoldilocksExt4.zero
  | 0, u, v, hu, hv => by
    have hu0 : u = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hu)
    have hv0 : v = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hv)
    subst hu0 hv0
    simp [hypercubePointExt4, evalEqExt4, evalZipProdPoly]
  | ell + 1, u, v, hu, hv => by
    unfold evalEqExt4
    dsimp only [hypercubePointExt4, evalZipProdPoly]
    change CommRingOps.mul _ (evalEqExt4 (hypercubePointExt4 ell (u / 2)) (hypercubePointExt4 ell (v / 2))) = _
    have huDiv : u / 2 < 2 ^ ell := by rw [Nat.pow_succ] at hu; omega
    have hvDiv : v / 2 < 2 ^ ell := by rw [Nat.pow_succ] at hv; omega
    rw [evalEqExt4_hypercube_kronecker ell (u / 2) (v / 2) huDiv hvDiv]
    if hBit : (u % 2 == 0) = (v % 2 == 0) then
      have hModEq : u % 2 = v % 2 :=
        lt_two_eq_of_beq_zero_eq (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) hBit
      have hF : eqFactorExt4
          (if u % 2 == 0 then GoldilocksExt4.zero else GoldilocksExt4.one)
          (if v % 2 == 0 then GoldilocksExt4.zero else GoldilocksExt4.one) = GoldilocksExt4.one := by
        rw [hBit]
        cases (v % 2 == 0) <;> decide +kernel
      rw [hF]
      refine (LawfulCommRing.one_mul _).trans ?_
      by_cases hDivEq : u / 2 = v / 2
      · have hUV : u = v := by omega
        rw [ite_eq_left hDivEq, ite_eq_left hUV]
      · have hUV : u ≠ v := fun hEq => hDivEq (by rw [hEq])
        rw [ite_eq_right hDivEq, ite_eq_right hUV]
    else
      have hUV : u ≠ v := fun hEq => hBit (by rw [hEq])
      have hF : eqFactorExt4
          (if u % 2 == 0 then GoldilocksExt4.zero else GoldilocksExt4.one)
          (if v % 2 == 0 then GoldilocksExt4.zero else GoldilocksExt4.one) = GoldilocksExt4.zero := by
        cases h1 : (u % 2 == 0) <;> cases h2 : (v % 2 == 0)
        · exact False.elim (hBit (by rw [h1, h2]))
        · decide +kernel
        · decide +kernel
        · exact False.elim (hBit (by rw [h1, h2]))
      rw [hF]
      refine (LawfulCommRing.zero_mul _).trans ?_
      rw [ite_eq_right hUV]
      rfl

/-! ### Exact Degree-≤7 Algebraic Row Gates (`Poseidon2PermWitness`, Base-4, Unary WOTS+C, Merkle) -/

/-- Check whether every `Goldilocks` residual in a list vanishes. -/
def allZeroGoldilocks (rs : List Goldilocks) : Bool :=
  rs.all (· == Goldilocks.zero)

theorem allZeroGoldilocks_append (a b : List Goldilocks) :
    allZeroGoldilocks (a ++ b) = (allZeroGoldilocks a && allZeroGoldilocks b) := by
  unfold allZeroGoldilocks
  exact List.all_append

theorem sub_eq_zero_iff_goldilocks (a b : Goldilocks) :
    (Goldilocks.sub a b == Goldilocks.zero) = true ↔ a = b := by
  rw [beq_iff_eq]
  exact LawfulCommRing.sub_eq_zero_iff

private theorem gold_sub_eq_zero_iff (a b : Goldilocks) :
    Goldilocks.sub a b = Goldilocks.zero ↔ a = b :=
  LawfulCommRing.sub_eq_zero_iff

private theorem list_map_eq_self_of_forall {α : Type} {f : α → α} :
    ∀ (l : List α), (∀ x ∈ l, f x = x) → l.map f = l
  | [], _ => rfl
  | a :: l, h => by
    rw [List.map_cons, h a (List.mem_cons_self ..),
        list_map_eq_self_of_forall l (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- Quartic base-4 gate `d * (d - 1) * (d - 2) * (d - 3)` (`degree 4 ≤ 7`, `arithmetize.rs`). -/
def quarticBase4 (d : Goldilocks) : Goldilocks :=
  Goldilocks.mul
    (Goldilocks.mul d (Goldilocks.sub d Goldilocks.one))
    (Goldilocks.mul (Goldilocks.sub d (Goldilocks.ofNat 2)) (Goldilocks.sub d (Goldilocks.ofNat 3)))

theorem quarticBase4_eq_zero_iff (d : Goldilocks) :
    quarticBase4 d = Goldilocks.zero ↔ d.val < 4 := by
  constructor
  · intro h
    unfold quarticBase4 at h
    change CommRingOps.mul
      (CommRingOps.mul d (CommRingOps.sub d Goldilocks.one))
      (CommRingOps.mul (CommRingOps.sub d (Goldilocks.ofNat 2)) (CommRingOps.sub d (Goldilocks.ofNat 3))) =
      CommRingOps.zero at h
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h with h01 | h23
    · rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h01 with h0 | h1
      · rw [h0]; decide
      · have hd1 : d = Goldilocks.one := LawfulCommRing.sub_eq_zero_iff.mp h1
        rw [hd1]; decide
    · rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h23 with h2 | h3
      · have hd2 : d = Goldilocks.ofNat 2 := LawfulCommRing.sub_eq_zero_iff.mp h2
        rw [hd2]; decide
      · have hd3 : d = Goldilocks.ofNat 3 := LawfulCommRing.sub_eq_zero_iff.mp h3
        rw [hd3]; decide
  · intro hLt
    have hCases : d = Goldilocks.zero ∨ d = Goldilocks.one ∨
                  d = Goldilocks.ofNat 2 ∨ d = Goldilocks.ofNat 3 := by
      rcases d with ⟨v, hv⟩
      dsimp only at hLt
      have hvCases : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by omega
      rcases hvCases with rfl | rfl | rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr (.inl (Goldilocks.ext rfl)))
      · exact .inr (.inr (.inr (Goldilocks.ext rfl)))
    rcases hCases with rfl | rfl | rfl | rfl <;> decide +kernel

/-- Quadratic Boolean bit gate `b * (b - 1)` (`degree 2 ≤ 7`). -/
def boolBitResidual (b : Goldilocks) : Goldilocks :=
  Goldilocks.mul b (Goldilocks.sub b Goldilocks.one)

theorem boolBitResidual_eq_zero_iff (b : Goldilocks) :
    boolBitResidual b = Goldilocks.zero ↔ (b = Goldilocks.zero ∨ b = Goldilocks.one) := by
  constructor
  · intro h
    change CommRingOps.mul b (CommRingOps.sub b Goldilocks.one) = CommRingOps.zero at h
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h with h0 | h1
    · exact .inl h0
    · exact .inr (LawfulCommRing.sub_eq_zero_iff.mp h1)
  · rintro (rfl | rfl) <;> decide +kernel

/-- Full 30-round Width-12 `Poseidon2` permutation row witness (`118` S-box wires + `12` output wires,
    matching `COL_SBOX_OUT = 12..130` in `trace.rs:32`). -/
structure Poseidon2PermWitness where
  input       : Poseidon2State12
  initExtSbox : List Poseidon2State12
  intSbox     : List Goldilocks
  termExtSbox : List Poseidon2State12
  output      : Poseidon2State12
  deriving DecidableEq, Repr

private def buildRoundsSboxPoly {RC ST SB : Type}
    (sboxFn : RC → ST → SB) (nextFn : ST → SB → ST) :
    List RC → ST → List SB
  | [], _ => []
  | rc :: rcs, cur =>
    let sb := sboxFn rc cur
    sb :: buildRoundsSboxPoly sboxFn nextFn rcs (nextFn cur sb)

private def roundsResidualsPoly {RC ST SB RES : Type}
    (sboxFn : RC → ST → SB) (nextFn : ST → SB → ST)
    (diffFn : SB → SB → List RES) (badRes : List RES) :
    List RC → List SB → ST → (ST × List RES)
  | [], [], cur => (cur, [])
  | rc :: rcs, sb :: sbs, cur =>
    let expected := sboxFn rc cur
    let (finalSt, restRes) := roundsResidualsPoly sboxFn nextFn diffFn badRes rcs sbs (nextFn cur sb)
    (finalSt, diffFn expected sb ++ restRes)
  | [], _ :: _, cur => (cur, badRes)
  | _ :: _, [], cur => (cur, badRes)

private theorem roundsResidualsPoly_honest {RC ST SB RES : Type}
    (sboxFn : RC → ST → SB) (nextFn : ST → SB → ST)
    (diffFn : SB → SB → List RES) (badRes : List RES)
    (roundFn : RC → ST → ST)
    (hRound : ∀ rc cur, nextFn cur (sboxFn rc cur) = roundFn rc cur)
    (zeroPred : List RES → Bool)
    (hNil : zeroPred [] = true)
    (hAppend : ∀ a b, zeroPred (a ++ b) = (zeroPred a && zeroPred b))
    (hDiffSelf : ∀ sb, zeroPred (diffFn sb sb) = true) :
    ∀ (rcs : List RC) (cur : ST),
      zeroPred (roundsResidualsPoly sboxFn nextFn diffFn badRes rcs
        (buildRoundsSboxPoly sboxFn nextFn rcs cur) cur).2 = true ∧
      (roundsResidualsPoly sboxFn nextFn diffFn badRes rcs
        (buildRoundsSboxPoly sboxFn nextFn rcs cur) cur).1 = runRounds roundFn rcs cur
  | [], cur => by
    dsimp only [buildRoundsSboxPoly, roundsResidualsPoly, runRounds]
    exact ⟨hNil, rfl⟩
  | rc :: rcs, cur => by
    dsimp only [buildRoundsSboxPoly, roundsResidualsPoly, runRounds]
    rw [hRound rc cur]
    have ih := roundsResidualsPoly_honest sboxFn nextFn diffFn badRes roundFn hRound
      zeroPred hNil hAppend hDiffSelf rcs (roundFn rc cur)
    rw [hAppend, hDiffSelf, ih.1]
    exact ⟨rfl, ih.2⟩

private theorem roundsResidualsPoly_allZero_iff {RC ST SB RES : Type}
    (sboxFn : RC → ST → SB) (nextFn : ST → SB → ST)
    (diffFn : SB → SB → List RES) (badRes : List RES)
    (roundFn : RC → ST → ST)
    (hRound : ∀ rc cur, nextFn cur (sboxFn rc cur) = roundFn rc cur)
    (zeroPred : List RES → Bool)
    (hNil : zeroPred [] = true)
    (hBad : zeroPred badRes = false)
    (hAppend : ∀ a b, zeroPred (a ++ b) = (zeroPred a && zeroPred b))
    (hDiffZeroIff : ∀ a b, zeroPred (diffFn a b) = true ↔ a = b) :
    ∀ (rcs : List RC) (sbs : List SB) (cur : ST),
      zeroPred (roundsResidualsPoly sboxFn nextFn diffFn badRes rcs sbs cur).2 = true ↔
        sbs = buildRoundsSboxPoly sboxFn nextFn rcs cur
  | [], [], _ => by
    dsimp only [roundsResidualsPoly, buildRoundsSboxPoly]
    simp [hNil]
  | [], _ :: _, _ => by
    dsimp only [roundsResidualsPoly, buildRoundsSboxPoly]
    simp [hBad]
  | _ :: _, [], _ => by
    dsimp only [roundsResidualsPoly, buildRoundsSboxPoly]
    simp [hBad]
  | rc :: rcs, sb :: sbs, cur => by
    dsimp only [roundsResidualsPoly, buildRoundsSboxPoly]
    rw [hAppend, Bool.and_eq_true, hDiffZeroIff, List.cons.injEq]
    constructor
    · rintro ⟨hSb, hRest⟩
      subst hSb
      rw [hRound rc cur] at hRest ⊢
      exact ⟨rfl, (roundsResidualsPoly_allZero_iff sboxFn nextFn diffFn badRes roundFn hRound
        zeroPred hNil hBad hAppend hDiffZeroIff rcs sbs (roundFn rc cur)).mp hRest⟩
    · rintro ⟨hSb, hSbs⟩
      subst hSb hSbs
      rw [hRound rc cur]
      have hSelf : ∀ x, zeroPred (diffFn x x) = true := fun x => (hDiffZeroIff x x).mpr rfl
      exact ⟨rfl, (roundsResidualsPoly_honest sboxFn nextFn diffFn badRes roundFn hRound
        zeroPred hNil hAppend hSelf rcs (roundFn rc cur)).1⟩

private def extRoundSboxFn (rc cur : Poseidon2State12) : Poseidon2State12 :=
  sboxState12 (state12Add cur rc)

private def extRoundNextFn (_cur sb : Poseidon2State12) : Poseidon2State12 :=
  applyME sb

private def intRoundSboxFn (rc : Goldilocks) (cur : Poseidon2State12) : Goldilocks :=
  sbox7 (Goldilocks.add cur.b0.x0 rc)

private def intRoundNextFn (cur : Poseidon2State12) (sb : Goldilocks) : Poseidon2State12 :=
  applyMI ⟨⟨sb, cur.b0.x1, cur.b0.x2, cur.b0.x3⟩, cur.b1, cur.b2⟩

def buildExtRoundsSbox (rcs : List Poseidon2State12) (cur : Poseidon2State12) : List Poseidon2State12 :=
  buildRoundsSboxPoly extRoundSboxFn extRoundNextFn rcs cur

def buildIntRoundsSbox (rcs : List Goldilocks) (cur : Poseidon2State12) : List Goldilocks :=
  buildRoundsSboxPoly intRoundSboxFn intRoundNextFn rcs cur

/-- Canonical honest `Poseidon2PermWitness` for `input`. -/
def honestPoseidon2PermWitness (input : Poseidon2State12) : Poseidon2PermWitness :=
  let s0 := applyME input
  let initSb := buildExtRoundsSbox poseidon2InitialExtConsts s0
  let s1 := runRounds externalRound poseidon2InitialExtConsts s0
  let intSb := buildIntRoundsSbox poseidon2InternalConsts s1
  let s2 := runRounds internalRound poseidon2InternalConsts s1
  let termSb := buildExtRoundsSbox poseidon2TerminalExtConsts s2
  let s3 := runRounds externalRound poseidon2TerminalExtConsts s2
  { input       := input
    initExtSbox := initSb
    intSbox     := intSb
    termExtSbox := termSb
    output      := s3 }

def extRoundsResiduals (rcs : List Poseidon2State12) (cur : Poseidon2State12)
    (sbs : List Poseidon2State12) : (Poseidon2State12 × List Goldilocks) :=
  roundsResidualsPoly extRoundSboxFn extRoundNextFn
    (fun a b => (state12Sub a b).toList) [Goldilocks.one] rcs sbs cur

def intRoundsResiduals (rcs : List Goldilocks) (cur : Poseidon2State12)
    (sbs : List Goldilocks) : (Poseidon2State12 × List Goldilocks) :=
  roundsResidualsPoly intRoundSboxFn intRoundNextFn
    (fun a b => [Goldilocks.sub a b]) [Goldilocks.one] rcs sbs cur

/-- Degree-7 S-box + linear round residuals (`118 + 12 = 130` residuals when well-shaped). -/
def poseidon2PermResiduals (w : Poseidon2PermWitness) : List Goldilocks :=
  let s0 := applyME w.input
  let (s1, res1) := extRoundsResiduals poseidon2InitialExtConsts s0 w.initExtSbox
  let (s2, res2) := intRoundsResiduals poseidon2InternalConsts s1 w.intSbox
  let (s3, res3) := extRoundsResiduals poseidon2TerminalExtConsts s2 w.termExtSbox
  res1 ++ res2 ++ res3 ++ (state12Sub s3 w.output).toList

private theorem state12Sub_toList_allZero_iff (a b : Poseidon2State12) :
    allZeroGoldilocks (state12Sub a b).toList = true ↔ a = b := by
  rcases a with ⟨⟨a0, a1, a2, a3⟩, ⟨a4, a5, a6, a7⟩, ⟨a8, a9, a10, a11⟩⟩
  rcases b with ⟨⟨b0, b1, b2, b3⟩, ⟨b4, b5, b6, b7⟩, ⟨b8, b9, b10, b11⟩⟩
  unfold allZeroGoldilocks state12Sub lane4Sub Poseidon2State12.toList
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    sub_eq_zero_iff_goldilocks, Poseidon2State12.mk.injEq, Lane4.mk.injEq]
  constructor
  · rintro ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩
    exact ⟨⟨e0, e1, e2, e3⟩, ⟨e4, e5, e6, e7⟩, ⟨e8, e9, e10, e11⟩⟩
  · rintro ⟨⟨e0, e1, e2, e3⟩, ⟨e4, e5, e6, e7⟩, ⟨e8, e9, e10, e11⟩⟩
    exact ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩

private theorem extRoundsResiduals_honest (rcs : List Poseidon2State12) (cur : Poseidon2State12) :
    allZeroGoldilocks (extRoundsResiduals rcs cur (buildExtRoundsSbox rcs cur)).2 = true ∧
    (extRoundsResiduals rcs cur (buildExtRoundsSbox rcs cur)).1 = runRounds externalRound rcs cur :=
  roundsResidualsPoly_honest extRoundSboxFn extRoundNextFn
    (fun a b => (state12Sub a b).toList) [Goldilocks.one] externalRound (fun _ _ => rfl)
    allZeroGoldilocks rfl allZeroGoldilocks_append
    (fun sb => (state12Sub_toList_allZero_iff sb sb).mpr rfl) rcs cur

private theorem extRoundsResiduals_allZero_iff
    (rcs : List Poseidon2State12) (cur : Poseidon2State12) (sbs : List Poseidon2State12) :
    allZeroGoldilocks (extRoundsResiduals rcs cur sbs).2 = true ↔
      sbs = buildExtRoundsSbox rcs cur :=
  roundsResidualsPoly_allZero_iff extRoundSboxFn extRoundNextFn
    (fun a b => (state12Sub a b).toList) [Goldilocks.one] externalRound (fun _ _ => rfl)
    allZeroGoldilocks rfl (by decide) allZeroGoldilocks_append state12Sub_toList_allZero_iff
    rcs sbs cur

private theorem intRoundsResiduals_honest (rcs : List Goldilocks) (cur : Poseidon2State12) :
    allZeroGoldilocks (intRoundsResiduals rcs cur (buildIntRoundsSbox rcs cur)).2 = true ∧
    (intRoundsResiduals rcs cur (buildIntRoundsSbox rcs cur)).1 = runRounds internalRound rcs cur :=
  roundsResidualsPoly_honest intRoundSboxFn intRoundNextFn
    (fun a b => [Goldilocks.sub a b]) [Goldilocks.one] internalRound (fun _ _ => rfl)
    allZeroGoldilocks rfl allZeroGoldilocks_append
    (fun sb => by
      change (Goldilocks.sub sb sb == Goldilocks.zero && true) = true
      rw [Bool.and_true]
      exact (sub_eq_zero_iff_goldilocks sb sb).mpr rfl) rcs cur

private theorem intRoundsResiduals_allZero_iff
    (rcs : List Goldilocks) (cur : Poseidon2State12) (sbs : List Goldilocks) :
    allZeroGoldilocks (intRoundsResiduals rcs cur sbs).2 = true ↔
      sbs = buildIntRoundsSbox rcs cur :=
  roundsResidualsPoly_allZero_iff intRoundSboxFn intRoundNextFn
    (fun a b => [Goldilocks.sub a b]) [Goldilocks.one] internalRound (fun _ _ => rfl)
    allZeroGoldilocks rfl (by decide) allZeroGoldilocks_append
    (fun a b => by
      change (Goldilocks.sub a b == Goldilocks.zero && true) = true ↔ a = b
      rw [Bool.and_true]
      exact sub_eq_zero_iff_goldilocks a b)
    rcs sbs cur

/-- **Exact 30-Round `Poseidon2` Row Constraint Soundness & Completeness (`poseidon2PermResiduals_allZero_iff`)**:
    All `130` degree-`≤ 7` residuals vanish if and only if `w` equals `honestPoseidon2PermWitness w.input`
    (fixing every intermediate S-box wire AND `w.output = poseidon2Perm12 w.input`)! -/
theorem poseidon2PermResiduals_allZero_iff (w : Poseidon2PermWitness) :
    allZeroGoldilocks (poseidon2PermResiduals w) = true ↔
      w = honestPoseidon2PermWitness w.input := by
  rcases w with ⟨inp, initSb, intSb, termSb, out⟩
  unfold poseidon2PermResiduals honestPoseidon2PermWitness
  dsimp only
  simp only [allZeroGoldilocks_append, Bool.and_eq_true, state12Sub_toList_allZero_iff,
    Poseidon2PermWitness.mk.injEq, true_and]
  let s0 := applyME inp
  let s1 := runRounds externalRound poseidon2InitialExtConsts s0
  let s2 := runRounds internalRound poseidon2InternalConsts s1
  let s3 := runRounds externalRound poseidon2TerminalExtConsts s2
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, hOut⟩
    have e1 : initSb = buildExtRoundsSbox poseidon2InitialExtConsts s0 :=
      (extRoundsResiduals_allZero_iff poseidon2InitialExtConsts s0 initSb).mp h1
    subst e1
    have st1 : (extRoundsResiduals poseidon2InitialExtConsts s0
                 (buildExtRoundsSbox poseidon2InitialExtConsts s0)).1 = s1 :=
      (extRoundsResiduals_honest poseidon2InitialExtConsts s0).2
    rw [st1] at h2 h3 hOut
    have e2 : intSb = buildIntRoundsSbox poseidon2InternalConsts s1 :=
      (intRoundsResiduals_allZero_iff poseidon2InternalConsts s1 intSb).mp h2
    subst e2
    have st2 : (intRoundsResiduals poseidon2InternalConsts s1
                 (buildIntRoundsSbox poseidon2InternalConsts s1)).1 = s2 :=
      (intRoundsResiduals_honest poseidon2InternalConsts s1).2
    rw [st2] at h3 hOut
    have e3 : termSb = buildExtRoundsSbox poseidon2TerminalExtConsts s2 :=
      (extRoundsResiduals_allZero_iff poseidon2TerminalExtConsts s2 termSb).mp h3
    subst e3
    have st3 : (extRoundsResiduals poseidon2TerminalExtConsts s2
                 (buildExtRoundsSbox poseidon2TerminalExtConsts s2)).1 = s3 :=
      (extRoundsResiduals_honest poseidon2TerminalExtConsts s2).2
    rw [st3] at hOut
    exact ⟨rfl, rfl, rfl, hOut.symm⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    have hE1 := extRoundsResiduals_honest poseidon2InitialExtConsts s0
    rw [hE1.2]
    have hI := intRoundsResiduals_honest poseidon2InternalConsts s1
    rw [hI.2]
    have hE2 := extRoundsResiduals_honest poseidon2TerminalExtConsts s2
    rw [hE2.2]
    exact ⟨⟨⟨hE1.1, hI.1⟩, hE2.1⟩, rfl⟩

theorem poseidon2PermResiduals_output_eq {w : Poseidon2PermWitness}
    (hZero : allZeroGoldilocks (poseidon2PermResiduals w) = true) :
    w.output = poseidon2Perm12 w.input := by
  have hHon := (poseidon2PermResiduals_allZero_iff w).mp hZero
  calc w.output
    _ = (honestPoseidon2PermWitness w.input).output := congrArg Poseidon2PermWitness.output hHon
    _ = poseidon2Perm12 w.input := by unfold poseidon2Perm12 honestPoseidon2PermWitness; rfl

/-- All-zero `Poseidon2PermWitness` (used in `#tooth` all-zero trace rejection). -/
def zeroPoseidon2PermWitness : Poseidon2PermWitness where
  input       := state12Zero
  initExtSbox := List.replicate 4 state12Zero
  intSbox     := List.replicate 22 Goldilocks.zero
  termExtSbox := List.replicate 4 state12Zero
  output      := state12Zero

theorem zeroPoseidon2PermWitness_rejected :
    allZeroGoldilocks (poseidon2PermResiduals zeroPoseidon2PermWitness) = false := by
  decide +kernel


/-! ### Multilinear Inter-Row Shift Kernel Identities (`arithmetize.rs:63-106`) -/

private theorem eqFactorExt4_zero_right (t : GoldilocksExt4) :
    eqFactorExt4 t GoldilocksExt4.zero = CommRingOps.sub GoldilocksExt4.one t := by
  unfold eqFactorExt4
  change CommRingOps.add
      (CommRingOps.mul (CommRingOps.sub CommRingOps.one t)
        (CommRingOps.sub CommRingOps.one CommRingOps.zero))
      (CommRingOps.mul t CommRingOps.zero) =
    CommRingOps.sub CommRingOps.one t
  rw [LawfulCommRing.sub_zero, LawfulCommRing.mul_one, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]

private theorem eqFactorExt4_one_right (t : GoldilocksExt4) :
    eqFactorExt4 t GoldilocksExt4.one = t := by
  unfold eqFactorExt4
  change CommRingOps.add
      (CommRingOps.mul (CommRingOps.sub CommRingOps.one t)
        (CommRingOps.sub CommRingOps.one CommRingOps.one))
      (CommRingOps.mul t CommRingOps.one) = t
  rw [LawfulCommRing.sub_self, LawfulCommRing.mul_zero, LawfulCommRing.mul_one, LawfulCommRing.zero_add]

/-- All-ones multilinear monomial `∏_i (tau_i * rx_i)` (`arithmetize.rs:69`). -/
def evalAllOnesExt4 (tau rx : List GoldilocksExt4) : GoldilocksExt4 :=
  evalZipProdPoly GoldilocksExt4.one GoldilocksExt4.zero CommRingOps.mul CommRingOps.mul tau rx

/-- Non-terminal equality kernel `E_not_last(tau, X) = eq(tau, X) - ∏_i (tau_i * X_i)` (`arithmetize.rs:66`). -/
def evalEqNotLastExt4 (tau rx : List GoldilocksExt4) : GoldilocksExt4 :=
  CommRingOps.sub (evalEqExt4 tau rx) (evalAllOnesExt4 tau rx)

private def evalShiftPoly {R : Type} (zeroVal : R) (addFn mulFn eqTermFn carryTermFn : R → R → R)
    (eqTailFn : List R → List R → R) : List R → List R → R
  | [], [] => zeroVal
  | t :: ts, x :: xs =>
    addFn
      (mulFn (eqTermFn t x) (eqTailFn ts xs))
      (mulFn (carryTermFn t x) (evalShiftPoly zeroVal addFn mulFn eqTermFn carryTermFn eqTailFn ts xs))
  | [], _ :: _ => zeroVal
  | _ :: _, [] => zeroVal

/-- Exact multilinear shift kernel `S_tau(X)` (`eval_shift_kernel_ext4` in `arithmetize.rs:80`). -/
def evalShiftKernelExt4 (tau rx : List GoldilocksExt4) : GoldilocksExt4 :=
  evalShiftPoly GoldilocksExt4.zero CommRingOps.add CommRingOps.mul
    (fun t x => CommRingOps.mul (CommRingOps.sub GoldilocksExt4.one t) x)
    (fun t x => CommRingOps.mul t (CommRingOps.sub GoldilocksExt4.one x))
    evalEqExt4 tau rx

private theorem evalAllOnesExt4_hypercube :
    ∀ (ell : Nat) (tau : List GoldilocksExt4) (v : Nat),
      tau.length = ell → v < 2 ^ ell →
      evalAllOnesExt4 tau (hypercubePointExt4 ell v) =
        if v + 1 = 2 ^ ell then evalEqExt4 tau (hypercubePointExt4 ell v) else GoldilocksExt4.zero
  | 0, [], v, _, hv => by
    have hv0 : v = 0 := by simp at hv; omega
    subst hv0
    simp [hypercubePointExt4, evalAllOnesExt4, evalEqExt4, evalZipProdPoly]
  | ell + 1, t :: ts, v, hLen, hv => by
    have hTsLen : ts.length = ell := Nat.succ.inj hLen
    have hvDiv : v / 2 < 2 ^ ell := by rw [Nat.pow_succ] at hv; omega
    unfold evalAllOnesExt4 evalEqExt4
    dsimp only [hypercubePointExt4, evalZipProdPoly]
    change CommRingOps.mul (CommRingOps.mul t _) (evalAllOnesExt4 ts (hypercubePointExt4 ell (v / 2))) =
      if v + 1 = 2 ^ (ell + 1) then
        CommRingOps.mul (eqFactorExt4 t _) (evalEqExt4 ts (hypercubePointExt4 ell (v / 2)))
      else GoldilocksExt4.zero
    cases hEven : (v % 2 == 0)
    · have hOdd : v % 2 = 1 := by
        cases r : v % 2 with
        | zero => simp [r] at hEven
        | succ m => omega
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [evalAllOnesExt4_hypercube ell ts (v / 2) hTsLen hvDiv]
      have hMulOne : CommRingOps.mul t GoldilocksExt4.one = t := LawfulCommRing.mul_one t
      rw [hMulOne, eqFactorExt4_one_right]
      have hPow2 : 2 ^ (ell + 1) = 2 * 2 ^ ell := by rw [Nat.pow_succ, Nat.mul_comm]
      by_cases hTop : v / 2 + 1 = 2 ^ ell
      · have hTopV : v + 1 = 2 ^ (ell + 1) := by omega
        simp [hTop, hTopV]
      · have hTopV : v + 1 ≠ 2 ^ (ell + 1) := by omega
        rw [ite_eq_right hTop, ite_eq_right hTopV]
        exact LawfulCommRing.mul_zero t
    · have hRem0 : v % 2 = 0 := eq_of_beq hEven
      have hPow2 : 2 ^ (ell + 1) = 2 * 2 ^ ell := by rw [Nat.pow_succ, Nat.mul_comm]
      have hNotLast : v + 1 ≠ 2 ^ (ell + 1) := by omega
      simp only [↓reduceIte, hNotLast]
      change CommRingOps.mul (CommRingOps.mul t CommRingOps.zero) _ = CommRingOps.zero
      rw [LawfulCommRing.mul_zero, LawfulCommRing.zero_mul]

/-- On `{0, 1}^ell`, `evalEqNotLastExt4` equals `eq(tau, v)` for `v + 1 < 2^ell` and `0` at `v = 2^ell - 1`. -/
theorem evalEqNotLastExt4_hypercube (ell : Nat) (tau : List GoldilocksExt4) (v : Nat)
    (hLen : tau.length = ell) (hv : v < 2 ^ ell) :
    evalEqNotLastExt4 tau (hypercubePointExt4 ell v) =
      if v + 1 = 2 ^ ell then GoldilocksExt4.zero else evalEqExt4 tau (hypercubePointExt4 ell v) := by
  unfold evalEqNotLastExt4
  rw [evalAllOnesExt4_hypercube ell tau v hLen hv]
  by_cases hLast : v + 1 = 2 ^ ell
  · rw [ite_eq_left hLast, ite_eq_left hLast]
    exact LawfulCommRing.sub_self _
  · simp only [hLast, ↓reduceIte]
    change CommRingOps.sub _ CommRingOps.zero = _
    rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.neg_zero, LawfulCommRing.add_zero]

/-- On `{0, 1}^ell`, `evalShiftKernelExt4` vanishes at `v = 0` and equals `eq(tau, v - 1)` for `1 ≤ v < 2^ell`. -/
theorem evalShiftKernelExt4_hypercube :
    ∀ (ell : Nat) (tau : List GoldilocksExt4) (v : Nat),
      tau.length = ell → v < 2 ^ ell →
      evalShiftKernelExt4 tau (hypercubePointExt4 ell v) =
        if v = 0 then GoldilocksExt4.zero else evalEqExt4 tau (hypercubePointExt4 ell (v - 1))
  | 0, [], v, _, hv => by
    have hv0 : v = 0 := by simp at hv; omega
    subst hv0
    simp [hypercubePointExt4, evalShiftKernelExt4, evalShiftPoly]
  | ell + 1, t :: ts, v, hLen, hv => by
    have hTsLen : ts.length = ell := Nat.succ.inj hLen
    have hvDiv : v / 2 < 2 ^ ell := by rw [Nat.pow_succ] at hv; omega
    unfold evalShiftKernelExt4
    dsimp only [hypercubePointExt4, evalShiftPoly]
    change CommRingOps.add
      (CommRingOps.mul (CommRingOps.mul (CommRingOps.sub GoldilocksExt4.one t) _)
        (evalEqExt4 ts (hypercubePointExt4 ell (v / 2))))
      (CommRingOps.mul (CommRingOps.mul t (CommRingOps.sub GoldilocksExt4.one _))
        (evalShiftKernelExt4 ts (hypercubePointExt4 ell (v / 2)))) = _
    cases hEven : (v % 2 == 0)
    · have hOdd : v % 2 = 1 := by
        cases r : v % 2 with
        | zero => simp [r] at hEven
        | succ m => omega
      have hvNe0 : v ≠ 0 := by omega
      have hPredEven : ((v - 1) % 2 == 0) = true := by
        have hp : (v - 1) % 2 = 0 := by omega
        simp [hp]
      have hPredDiv : (v - 1) / 2 = v / 2 := by omega
      have hEqUnf : evalEqExt4 (t :: ts) (hypercubePointExt4 (ell + 1) (v - 1)) =
          CommRingOps.mul (eqFactorExt4 t GoldilocksExt4.zero)
            (evalEqExt4 ts (hypercubePointExt4 ell (v / 2))) := by
        unfold evalEqExt4
        dsimp only [hypercubePointExt4, evalZipProdPoly]
        simp only [hPredEven, ↓reduceIte, hPredDiv]
      simp only [Bool.false_eq_true, ↓reduceIte, hvNe0]
      refine Eq.trans ?_ hEqUnf.symm
      rw [eqFactorExt4_zero_right]
      change CommRingOps.add
        (CommRingOps.mul (CommRingOps.mul (CommRingOps.sub CommRingOps.one t) CommRingOps.one)
          (evalEqExt4 ts (hypercubePointExt4 ell (v / 2))))
        (CommRingOps.mul (CommRingOps.mul t (CommRingOps.sub CommRingOps.one CommRingOps.one))
          (evalShiftKernelExt4 ts (hypercubePointExt4 ell (v / 2)))) =
        CommRingOps.mul (CommRingOps.sub CommRingOps.one t)
          (evalEqExt4 ts (hypercubePointExt4 ell (v / 2)))
      rw [LawfulCommRing.mul_one, LawfulCommRing.sub_self,
          LawfulCommRing.mul_zero, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
    · have hRem0 : v % 2 = 0 := eq_of_beq hEven
      rw [evalShiftKernelExt4_hypercube ell ts (v / 2) hTsLen hvDiv]
      by_cases hv0 : v = 0
      · subst hv0
        simp only [↓reduceIte]
        change CommRingOps.add
          (CommRingOps.mul (CommRingOps.mul _ CommRingOps.zero) _)
          (CommRingOps.mul _ CommRingOps.zero) = CommRingOps.zero
        rw [LawfulCommRing.mul_zero, LawfulCommRing.zero_mul, LawfulCommRing.mul_zero,
            LawfulCommRing.add_zero]
      · have hDivNe0 : v / 2 ≠ 0 := by omega
        have hPredOdd : ((v - 1) % 2 == 0) = false := by
          have hp : (v - 1) % 2 = 1 := by omega
          simp [hp]
        have hPredDiv : (v - 1) / 2 = v / 2 - 1 := by omega
        have hEqUnf : evalEqExt4 (t :: ts) (hypercubePointExt4 (ell + 1) (v - 1)) =
            CommRingOps.mul (eqFactorExt4 t GoldilocksExt4.one)
              (evalEqExt4 ts (hypercubePointExt4 ell (v / 2 - 1))) := by
          unfold evalEqExt4
          dsimp only [hypercubePointExt4, evalZipProdPoly]
          simp only [hPredOdd, Bool.false_eq_true, ↓reduceIte, hPredDiv]
        simp only [↓reduceIte, hv0, hDivNe0]
        refine Eq.trans ?_ hEqUnf.symm
        rw [eqFactorExt4_one_right]
        change CommRingOps.add
          (CommRingOps.mul (CommRingOps.mul _ CommRingOps.zero) _)
          (CommRingOps.mul (CommRingOps.mul t (CommRingOps.sub CommRingOps.one CommRingOps.zero)) _) = _
        rw [LawfulCommRing.mul_zero, LawfulCommRing.zero_mul, LawfulCommRing.zero_add,
            LawfulCommRing.sub_zero, LawfulCommRing.mul_one]

/-! ### 63-Bit Base-4 Limb Decomposition & `H_msg` Target-Sum Gates (`trace.rs:104`) -/

/-- Reconstruct a `Goldilocks` field element from LSB-first base-4 digit wires. -/
def evalGoldilocksBase4 : List Goldilocks → Goldilocks
  | [] => Goldilocks.zero
  | d :: ds => Goldilocks.add d (Goldilocks.mul (Goldilocks.ofNat 4) (evalGoldilocksBase4 ds))

theorem evalBase4Digits_lt_pow4 :
    ∀ (ds : List Nat), (∀ d ∈ ds, d < 4) → evalBase4Digits ds < 4 ^ ds.length
  | [], _ => by simp [evalBase4Digits]
  | d :: ds, hLt => by
    have hd : d < 4 := hLt d (List.mem_cons_self ..)
    have ih := evalBase4Digits_lt_pow4 ds (fun x hx => hLt x (List.mem_cons_of_mem _ hx))
    simp only [evalBase4Digits, List.length_cons, Nat.pow_succ]
    omega

theorem extractLimbBase4Digits_unique :
    ∀ (ds : List Nat) (q : Nat),
      (∀ d ∈ ds, d < 4) →
      extractLimbBase4Digits ds.length (evalBase4Digits ds + (4 ^ ds.length) * q) = ds ∧
      (evalBase4Digits ds + (4 ^ ds.length) * q) / (4 ^ ds.length) = q
  | [], q, _ => by
    simp [extractLimbBase4Digits, evalBase4Digits]
  | d :: ds, q, hLt => by
    have hd : d < 4 := hLt d (List.mem_cons_self ..)
    have ih := extractLimbBase4Digits_unique ds q (fun x hx => hLt x (List.mem_cons_of_mem _ hx))
    let m := evalBase4Digits ds + (4 ^ ds.length) * q
    have hRew : evalBase4Digits (d :: ds) + (4 ^ (d :: ds).length) * q = d + 4 * m := by
      dsimp only [evalBase4Digits, List.length_cons, m]
      have hPow : 4 ^ (ds.length + 1) = 4 * 4 ^ ds.length := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [hPow, Nat.mul_assoc, Nat.mul_add, Nat.add_assoc]
    have hMod : (d + 4 * m) % 4 = d := by omega
    have hDiv4 : (d + 4 * m) / 4 = m := by omega
    refine ⟨?_, ?_⟩
    · rw [hRew]
      dsimp only [List.length_cons, extractLimbBase4Digits]
      rw [hMod, hDiv4, ih.1]
    · rw [hRew]
      dsimp only [List.length_cons]
      have hPow : 4 ^ (ds.length + 1) = 4 * 4 ^ ds.length := by rw [Nat.pow_succ, Nat.mul_comm]
      rw [hPow, ← Nat.div_div_eq_div_mul, hDiv4, ih.2]

theorem evalGoldilocksBase4_val_of_lt4 :
    ∀ (ds : List Goldilocks),
      ds.length ≤ 31 →
      (∀ d ∈ ds, d.val < 4) →
      (evalGoldilocksBase4 ds).val = evalBase4Digits (ds.map Goldilocks.val)
  | [], _, _ => rfl
  | d :: ds, hLen, hLt => by
    have hd : d.val < 4 := hLt d (List.mem_cons_self ..)
    have hDsLen : ds.length ≤ 30 := by simp only [List.length_cons] at hLen; omega
    have ih := evalGoldilocksBase4_val_of_lt4 ds (by omega)
      (fun x hx => hLt x (List.mem_cons_of_mem _ hx))
    have hEvalLt : evalBase4Digits (ds.map Goldilocks.val) < 4 ^ ds.length := by
      have hMapLt : ∀ v ∈ ds.map Goldilocks.val, v < 4 := by
        intro v hv
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
        exact hLt x (List.mem_cons_of_mem _ hx)
      simpa only [List.length_map] using evalBase4Digits_lt_pow4 (ds.map Goldilocks.val) hMapLt
    have hPowBound : 4 ^ (ds.length + 1) ≤ 4 ^ 31 :=
      Nat.pow_le_pow_right (by decide) hLen
    have hPowLtP : 4 ^ 31 < goldilocksPrime := by decide
    have hMulLt : 4 * (evalGoldilocksBase4 ds).val < goldilocksPrime := by
      rw [ih]
      have hStep : 4 * evalBase4Digits (ds.map Goldilocks.val) < 4 ^ (ds.length + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]; omega
      exact Nat.lt_trans (Nat.lt_of_lt_of_le hStep hPowBound) hPowLtP
    have h4Val : (Goldilocks.ofNat 4).val = 4 := rfl
    have hMulVal : (Goldilocks.mul (Goldilocks.ofNat 4) (evalGoldilocksBase4 ds)).val =
        4 * evalBase4Digits (ds.map Goldilocks.val) := by
      rw [Goldilocks.mul_val, h4Val, Nat.mod_eq_of_lt hMulLt, ih]
    have hAddLt : d.val + 4 * evalBase4Digits (ds.map Goldilocks.val) < goldilocksPrime := by
      have hStep : d.val + 4 * evalBase4Digits (ds.map Goldilocks.val) < 4 ^ (ds.length + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm]; omega
      exact Nat.lt_trans (Nat.lt_of_lt_of_le hStep hPowBound) hPowLtP
    dsimp only [evalGoldilocksBase4, List.map_cons, evalBase4Digits]
    rw [Goldilocks.add_val, hMulVal, Nat.mod_eq_of_lt hAddLt]
    rfl

/-- Witness for `HmsgDecompLimb` / `StatelessDecompLimb` (`31` base-4 digits + `b62` bit, `trace.rs:104`). -/
structure Limb63DecompWitness where
  limbVal : Goldilocks
  digits  : List Goldilocks
  topBit  : Goldilocks
  deriving DecidableEq, Repr

def honestLimb63DecompWitness (limbVal : Goldilocks) : Limb63DecompWitness where
  limbVal := limbVal
  digits  := (extractLimbBase4Digits 31 limbVal.val).map Goldilocks.ofNat
  topBit  := Goldilocks.ofNat (limbVal.val / (4 ^ 31))

def limb63DecompResiduals (expectedLimb : Goldilocks) (w : Limb63DecompWitness) : List Goldilocks :=
  if w.digits.length == 31 then
    let recon := Goldilocks.add (evalGoldilocksBase4 w.digits)
      (Goldilocks.mul (Goldilocks.ofNat (4 ^ 31)) w.topBit)
    [Goldilocks.sub w.limbVal expectedLimb,
     boolBitResidual w.topBit,
     Goldilocks.sub recon w.limbVal] ++
      w.digits.map quarticBase4
  else
    [Goldilocks.one]

private theorem map_quarticBase4_allZero_iff (ds : List Goldilocks) :
    allZeroGoldilocks (ds.map quarticBase4) = true ↔ (∀ d ∈ ds, d.val < 4) := by
  induction ds with
  | nil => simp [allZeroGoldilocks]
  | cons d ds ih =>
    have hCons : allZeroGoldilocks (quarticBase4 d :: ds.map quarticBase4) =
        ((quarticBase4 d == Goldilocks.zero) && allZeroGoldilocks (ds.map quarticBase4)) := rfl
    simp only [List.map_cons, hCons, Bool.and_eq_true, beq_iff_eq, quarticBase4_eq_zero_iff,
      ih, List.mem_cons, forall_eq_or_imp]

theorem limb63DecompResiduals_allZero_iff (expectedLimb : Goldilocks) (w : Limb63DecompWitness) :
    allZeroGoldilocks (limb63DecompResiduals expectedLimb w) = true ↔
      (expectedLimb.val < 2 ^ 63 ∧ w = honestLimb63DecompWitness expectedLimb) := by
  unfold limb63DecompResiduals
  cases hLenBeq : (w.digits.length == 31)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hF : allZeroGoldilocks [Goldilocks.one] = false := by decide
    rw [hF]
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨_, rfl⟩
    simp [honestLimb63DecompWitness, extractLimbBase4Digits_length] at hLenBeq
  · have hLen : w.digits.length = 31 := eq_of_beq hLenBeq
    simp only [↓reduceIte]
    have hHeadSplit : ∀ (r0 r1 r2 : Goldilocks) (rest : List Goldilocks),
        allZeroGoldilocks ([r0, r1, r2] ++ rest) =
          ((r0 == Goldilocks.zero) && (r1 == Goldilocks.zero) &&
           (r2 == Goldilocks.zero) && allZeroGoldilocks rest) := by
      intro r0 r1 r2 rest
      simp [allZeroGoldilocks, Bool.and_assoc]
    rw [hHeadSplit]
    simp only [Bool.and_eq_true, beq_iff_eq, gold_sub_eq_zero_iff,
      boolBitResidual_eq_zero_iff, map_quarticBase4_allZero_iff]
    constructor
    · rintro ⟨⟨⟨hLimbEq, hBit⟩, hRecon⟩, hDigitsLt4⟩
      subst hLimbEq
      have hTopLt2 : w.topBit.val < 2 := by
        rcases hBit with h0 | h1
        · rw [h0]; decide
        · rw [h1]; decide
      have hEvalVal := evalGoldilocksBase4_val_of_lt4 w.digits (by omega) hDigitsLt4
      have hEvalBound : evalBase4Digits (w.digits.map Goldilocks.val) < 4 ^ 31 := by
        have hMapLt : ∀ v ∈ w.digits.map Goldilocks.val, v < 4 := by
          intro v hv
          obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
          exact hDigitsLt4 x hx
        have hB := evalBase4Digits_lt_pow4 (w.digits.map Goldilocks.val) hMapLt
        simpa only [List.length_map, hLen] using hB
      have hPowEq : (4 : Nat) ^ 31 = 2 ^ 62 := rfl
      have hPowVal : (Goldilocks.ofNat (4 ^ 31)).val = 4 ^ 31 := by decide
      have hTopProdLtP : (4 ^ 31) * w.topBit.val < goldilocksPrime := by
        have h263 : (2 : Nat) ^ 63 < goldilocksPrime := by decide
        have hLe : (4 ^ 31) * w.topBit.val ≤ 2 ^ 62 := by rw [hPowEq]; omega
        omega
      have hTopMulVal : (Goldilocks.mul (Goldilocks.ofNat (4 ^ 31)) w.topBit).val =
          (4 ^ 31) * w.topBit.val := by
        rw [Goldilocks.mul_val, hPowVal, Nat.mod_eq_of_lt hTopProdLtP]
      have hSumLt263 : evalBase4Digits (w.digits.map Goldilocks.val) + (4 ^ 31) * w.topBit.val < 2 ^ 63 := by
        have h263 : (2 : Nat) ^ 63 = 2 ^ 62 + 2 ^ 62 := rfl
        rw [hPowEq] at hEvalBound ⊢
        omega
      have hSumLtP : evalBase4Digits (w.digits.map Goldilocks.val) + (4 ^ 31) * w.topBit.val < goldilocksPrime :=
        Nat.lt_trans hSumLt263 (by decide)
      have hReconVal : w.limbVal.val =
          evalBase4Digits (w.digits.map Goldilocks.val) + (4 ^ 31) * w.topBit.val := by
        have hV := congrArg Goldilocks.val hRecon.symm
        rw [Goldilocks.add_val, hEvalVal, hTopMulVal, Nat.mod_eq_of_lt hSumLtP] at hV
        exact hV
      have hLimbLt263 : w.limbVal.val < 2 ^ 63 := hReconVal ▸ hSumLt263
      have hMapLt4 : ∀ v ∈ w.digits.map Goldilocks.val, v < 4 := by
        intro v hv; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv; exact hDigitsLt4 x hx
      have hMapLen : (w.digits.map Goldilocks.val).length = 31 := by simp [hLen]
      obtain ⟨hUniqDs, hUniqQ⟩ := extractLimbBase4Digits_unique (w.digits.map Goldilocks.val) w.topBit.val hMapLt4
      rw [hMapLen, ← hReconVal] at hUniqDs hUniqQ
      have hDigitsEq : w.digits = (extractLimbBase4Digits 31 w.limbVal.val).map Goldilocks.ofNat := by
        rw [hUniqDs, List.map_map]
        have hId : (Goldilocks.ofNat ∘ Goldilocks.val) = id := by
          funext x
          exact Goldilocks.ext (Nat.mod_eq_of_lt x.isLt)
        rw [hId, List.map_id]
      have hTopEq : w.topBit = Goldilocks.ofNat (w.limbVal.val / (4 ^ 31)) := by
        rw [hUniqQ]
        exact (Goldilocks.ext (Nat.mod_eq_of_lt w.topBit.isLt)).symm
      refine ⟨hLimbLt263, ?_⟩
      rcases w with ⟨lv, ds, tb⟩
      simp only [honestLimb63DecompWitness, Limb63DecompWitness.mk.injEq] at hDigitsEq hTopEq ⊢
      exact ⟨trivial, hDigitsEq, hTopEq⟩
    · rintro ⟨hLt263, rfl⟩
      have hMapVal :
          ((extractLimbBase4Digits 31 expectedLimb.val).map Goldilocks.ofNat).map Goldilocks.val =
          extractLimbBase4Digits 31 expectedLimb.val := by
        rw [List.map_map]
        have hIdOnLt4 : ∀ x ∈ extractLimbBase4Digits 31 expectedLimb.val,
            (Goldilocks.ofNat x).val = x := by
          intro x hx
          have hx4 := extractLimbBase4Digits_all_lt_four 31 expectedLimb.val x hx
          exact Nat.mod_eq_of_lt (Nat.lt_trans hx4 (by decide))
        exact list_map_eq_self_of_forall _ hIdOnLt4
      have hDsLt4 : ∀ d ∈ (honestLimb63DecompWitness expectedLimb).digits, d.val < 4 := by
        intro d hd
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hd
        have hx4 := extractLimbBase4Digits_all_lt_four 31 expectedLimb.val x hx
        have hVal : (Goldilocks.ofNat x).val = x := Nat.mod_eq_of_lt (Nat.lt_trans hx4 (by decide))
        omega
      have hDivLt2 : expectedLimb.val / (4 ^ 31) < 2 := by
        have hPowEq : (4 : Nat) ^ 31 = 2 ^ 62 := rfl
        have h263 : (2 : Nat) ^ 63 = 2 * 2 ^ 62 := rfl
        rw [hPowEq]; rw [h263] at hLt263; omega
      have hBitOr : (honestLimb63DecompWitness expectedLimb).topBit = Goldilocks.zero ∨
                    (honestLimb63DecompWitness expectedLimb).topBit = Goldilocks.one := by
        dsimp only [honestLimb63DecompWitness]
        cases hQ : expectedLimb.val / (4 ^ 31) with
        | zero => exact .inl (Goldilocks.ext rfl)
        | succ m =>
          have hm0 : m = 0 := by omega
          subst hm0
          exact .inr (Goldilocks.ext rfl)
      have hReconEq :
          Goldilocks.add (evalGoldilocksBase4 (honestLimb63DecompWitness expectedLimb).digits)
            (Goldilocks.mul (Goldilocks.ofNat (4 ^ 31)) (honestLimb63DecompWitness expectedLimb).topBit) =
          expectedLimb := by
        apply Goldilocks.ext
        have hEV := evalGoldilocksBase4_val_of_lt4 (honestLimb63DecompWitness expectedLimb).digits
          (by simp [honestLimb63DecompWitness, extractLimbBase4Digits_length]) hDsLt4
        dsimp only [honestLimb63DecompWitness] at hEV ⊢
        rw [hMapVal] at hEV
        have hTopVal : (Goldilocks.ofNat (expectedLimb.val / (4 ^ 31))).val = expectedLimb.val / (4 ^ 31) :=
          Nat.mod_eq_of_lt (Nat.lt_trans hDivLt2 (by decide))
        have hPowVal : (Goldilocks.ofNat (4 ^ 31)).val = 4 ^ 31 := by decide
        have hDecomp := evalBase4Digits_extractLimbBase4Digits 31 expectedLimb.val
        have hMulLtP : (4 ^ 31) * (expectedLimb.val / (4 ^ 31)) < goldilocksPrime := by
          have hLtP : expectedLimb.val < goldilocksPrime := expectedLimb.isLt
          omega
        have hMulVal : (Goldilocks.mul (Goldilocks.ofNat (4 ^ 31))
            (Goldilocks.ofNat (expectedLimb.val / (4 ^ 31)))).val =
            (4 ^ 31) * (expectedLimb.val / (4 ^ 31)) := by
          rw [Goldilocks.mul_val, hPowVal, hTopVal, Nat.mod_eq_of_lt hMulLtP]
        rw [Goldilocks.add_val, hEV, hMulVal, hDecomp, Nat.mod_eq_of_lt expectedLimb.isLt]
      exact ⟨⟨⟨rfl, hBitOr⟩, hReconEq⟩, hDsLt4⟩

/-- Field sum of a list of `Goldilocks` wires. -/
def sumGoldilocks : List Goldilocks → Goldilocks
  | [] => Goldilocks.zero
  | d :: ds => Goldilocks.add d (sumGoldilocks ds)

theorem listNatSum_le_three_mul :
    ∀ (ds : List Nat), (∀ d ∈ ds, d < 4) → listNatSum ds ≤ 3 * ds.length
  | [], _ => by simp [listNatSum]
  | d :: ds, hLt => by
    have hd : d < 4 := hLt d (List.mem_cons_self ..)
    have ih := listNatSum_le_three_mul ds (fun x hx => hLt x (List.mem_cons_of_mem _ hx))
    dsimp only [listNatSum, List.length_cons]
    omega

theorem sumGoldilocks_val_of_lt4 :
    ∀ (ds : List Goldilocks),
      ds.length ≤ 128 →
      (∀ d ∈ ds, d.val < 4) →
      (sumGoldilocks ds).val = listNatSum (ds.map Goldilocks.val)
  | [], _, _ => rfl
  | d :: ds, hLen, hLt => by
    have hd : d.val < 4 := hLt d (List.mem_cons_self ..)
    have hDsLen : ds.length ≤ 127 := by dsimp only [List.length_cons] at hLen; omega
    have ih := sumGoldilocks_val_of_lt4 ds (by omega)
      (fun x hx => hLt x (List.mem_cons_of_mem _ hx))
    have hMapLt : ∀ v ∈ ds.map Goldilocks.val, v < 4 := by
      intro v hv; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv
      exact hLt x (List.mem_cons_of_mem _ hx)
    have hTailBound : listNatSum (ds.map Goldilocks.val) ≤ 3 * ds.length := by
      simpa only [List.length_map] using listNatSum_le_three_mul (ds.map Goldilocks.val) hMapLt
    have hSumLtP : d.val + listNatSum (ds.map Goldilocks.val) < goldilocksPrime := by
      have h384 : (384 : Nat) < goldilocksPrime := by decide
      omega
    dsimp only [sumGoldilocks, List.map_cons, listNatSum]
    rw [Goldilocks.add_val, ih, Nat.mod_eq_of_lt hSumLtP]
    rfl

/-- 5-limb `Digest5` base-4 decomposition + target-sum check (`5 * HmsgDecompLimb`, `trace.rs:152`). -/
structure Hmsg5DecompWitness where
  l0 : Limb63DecompWitness
  l1 : Limb63DecompWitness
  l2 : Limb63DecompWitness
  l3 : Limb63DecompWitness
  l4 : Limb63DecompWitness
  deriving DecidableEq, Repr

def honestHmsg5DecompWitness (d : Digest5) : Hmsg5DecompWitness where
  l0 := honestLimb63DecompWitness d.limb0
  l1 := honestLimb63DecompWitness d.limb1
  l2 := honestLimb63DecompWitness d.limb2
  l3 := honestLimb63DecompWitness d.limb3
  l4 := honestLimb63DecompWitness d.limb4

def hmsg5DigitWires (geom : AggSigGeometry) (w : Hmsg5DecompWitness) : List Goldilocks :=
  (w.l0.digits ++ w.l1.digits ++ w.l2.digits ++ w.l3.digits ++ w.l4.digits.take 4).take geom.wotsChains

def hmsg5DecompResiduals (geom : AggSigGeometry) (expected : Digest5) (w : Hmsg5DecompWitness) :
    List Goldilocks :=
  limb63DecompResiduals expected.limb0 w.l0 ++
  limb63DecompResiduals expected.limb1 w.l1 ++
  limb63DecompResiduals expected.limb2 w.l2 ++
  limb63DecompResiduals expected.limb3 w.l3 ++
  limb63DecompResiduals expected.limb4 w.l4 ++
  [Goldilocks.sub (sumGoldilocks (hmsg5DigitWires geom w)) (Goldilocks.ofNat geom.targetSum)]

private theorem map_val_ofNat_extract (k v : Nat) :
    ((extractLimbBase4Digits k v).map Goldilocks.ofNat).map Goldilocks.val =
    extractLimbBase4Digits k v := by
  rw [List.map_map]
  refine list_map_eq_self_of_forall _ fun x hx => ?_
  have hx4 := extractLimbBase4Digits_all_lt_four k v x hx
  exact Nat.mod_eq_of_lt (Nat.lt_trans hx4 (by decide))

private theorem take4_extractLimbBase4Digits_31 (v : Nat) :
    (extractLimbBase4Digits 31 v).take 4 = extractLimbBase4Digits 4 v := rfl

theorem hmsg5DecompResiduals_allZero_iff
    (geom : AggSigGeometry) (expected : Digest5) (w : Hmsg5DecompWitness)
    (hChainsLe : geom.wotsChains ≤ 128)
    (hTargetBound : geom.targetSum < 3 * geom.wotsChains) :
    allZeroGoldilocks (hmsg5DecompResiduals geom expected w) = true ↔
      (w = honestHmsg5DecompWitness expected ∧
       ∃ ds, extractWotsDigitsChecked geom expected = some ds ∧
             listNatSum ds = geom.targetSum ∧
             (hmsg5DigitWires geom w).map Goldilocks.val = ds) := by
  unfold hmsg5DecompResiduals
  have hSingleZero : ∀ x : Goldilocks, allZeroGoldilocks [x] = (x == Goldilocks.zero) := by
    intro x; simp [allZeroGoldilocks]
  simp only [allZeroGoldilocks_append, Bool.and_eq_true, limb63DecompResiduals_allZero_iff,
    hSingleZero, sub_eq_zero_iff_goldilocks]
  have hHonDigitsMap :
      (hmsg5DigitWires geom (honestHmsg5DecompWitness expected)).map Goldilocks.val =
        (extractLimbBase4Digits 31 expected.limb0.val ++
         extractLimbBase4Digits 31 expected.limb1.val ++
         extractLimbBase4Digits 31 expected.limb2.val ++
         extractLimbBase4Digits 31 expected.limb3.val ++
         extractLimbBase4Digits 4 expected.limb4.val).take geom.wotsChains := by
    unfold hmsg5DigitWires honestHmsg5DecompWitness honestLimb63DecompWitness
    dsimp only
    simp only [List.map_take, List.map_append, map_val_ofNat_extract,
      take4_extractLimbBase4Digits_31]
  have hHonWiresLt4 :
      ∀ d ∈ hmsg5DigitWires geom (honestHmsg5DecompWitness expected), d.val < 4 := by
    intro d hd
    have hValMem : d.val ∈ (hmsg5DigitWires geom (honestHmsg5DecompWitness expected)).map Goldilocks.val :=
      List.mem_map_of_mem hd
    rw [hHonDigitsMap] at hValMem
    have hMem := List.mem_of_mem_take hValMem
    simp only [List.mem_append] at hMem
    rcases hMem with (((m0 | m1) | m2) | m3) | m4
    · exact extractLimbBase4Digits_all_lt_four 31 _ _ m0
    · exact extractLimbBase4Digits_all_lt_four 31 _ _ m1
    · exact extractLimbBase4Digits_all_lt_four 31 _ _ m2
    · exact extractLimbBase4Digits_all_lt_four 31 _ _ m3
    · exact extractLimbBase4Digits_all_lt_four 4 _ _ m4
  have hHonWiresLen :
      (hmsg5DigitWires geom (honestHmsg5DecompWitness expected)).length ≤ 128 := by
    unfold hmsg5DigitWires
    exact Nat.le_trans (List.length_take_le _ _) hChainsLe
  have hTargetVal : (Goldilocks.ofNat geom.targetSum).val = geom.targetSum := by
    have hLtP : geom.targetSum < goldilocksPrime := by
      have h384 : (384 : Nat) < goldilocksPrime := by decide
      omega
    exact Nat.mod_eq_of_lt hLtP
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨c0, e0⟩, ⟨c1, e1⟩⟩, ⟨c2, e2⟩⟩, ⟨c3, e3⟩⟩, ⟨c4, e4⟩⟩, hSumEq⟩
    have hWEq : w = honestHmsg5DecompWitness expected := by
      rcases w with ⟨l0, l1, l2, l3, l4⟩
      dsimp only at e0 e1 e2 e3 e4
      subst e0 e1 e2 e3 e4
      rfl
    subst hWEq
    have hChk63 : checkDigest5Limbs63 expected = true := by
      unfold checkDigest5Limbs63
      simp [c0, c1, c2, c3, c4]
    let ds := (hmsg5DigitWires geom (honestHmsg5DecompWitness expected)).map Goldilocks.val
    have hExt : extractWotsDigitsChecked geom expected = some ds := by
      unfold extractWotsDigitsChecked
      rw [hChk63]
      simp only [↓reduceIte, Option.some.injEq]
      exact hHonDigitsMap.symm
    have hSumVal := congrArg Goldilocks.val hSumEq
    rw [sumGoldilocks_val_of_lt4 _ hHonWiresLen hHonWiresLt4, hTargetVal] at hSumVal
    exact ⟨rfl, ds, hExt, hSumVal, rfl⟩
  · rintro ⟨rfl, ds, hExt, hSumDs, hMapDs⟩
    unfold extractWotsDigitsChecked at hExt
    cases hChk : checkDigest5Limbs63 expected
    · simp [hChk] at hExt
    · have hUnpack63 :
          expected.limb0.val < 2 ^ 63 ∧ expected.limb1.val < 2 ^ 63 ∧
          expected.limb2.val < 2 ^ 63 ∧ expected.limb3.val < 2 ^ 63 ∧
          expected.limb4.val < 2 ^ 63 := by
        unfold checkDigest5Limbs63 at hChk
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hChk
        exact ⟨hChk.1.1.1.1, hChk.1.1.1.2, hChk.1.1.2, hChk.1.2, hChk.2⟩
      obtain ⟨c0, c1, c2, c3, c4⟩ := hUnpack63
      have hSumField :
          sumGoldilocks (hmsg5DigitWires geom (honestHmsg5DecompWitness expected)) =
          Goldilocks.ofNat geom.targetSum := by
        apply Goldilocks.ext
        rw [sumGoldilocks_val_of_lt4 _ hHonWiresLen hHonWiresLt4, hMapDs, hSumDs, hTargetVal]
      exact ⟨⟨⟨⟨⟨⟨c0, rfl⟩, ⟨c1, rfl⟩⟩, ⟨c2, rfl⟩⟩, ⟨c3, rfl⟩⟩, ⟨c4, rfl⟩⟩, hSumField⟩

/-! ### Quadratic Multiplexer, Unary WOTS+C Chain, and 2-Block Merkle Gates (`trace.rs:112-139`) -/

/-- Degree-2 selector residual `bit * (out - aTrue) + (1 - bit) * (out - aFalse)`. -/
def muxGoldilocksResidual (bit aTrue aFalse out : Goldilocks) : Goldilocks :=
  Goldilocks.add
    (Goldilocks.mul bit (Goldilocks.sub out aTrue))
    (Goldilocks.mul (Goldilocks.sub Goldilocks.one bit) (Goldilocks.sub out aFalse))

theorem muxGoldilocksResidual_eq_zero_iff {bit : Goldilocks}
    (hBit : bit = Goldilocks.zero ∨ bit = Goldilocks.one)
    (aTrue aFalse out : Goldilocks) :
    (muxGoldilocksResidual bit aTrue aFalse out == Goldilocks.zero) = true ↔
      out = (if bit == Goldilocks.one then aTrue else aFalse) := by
  rcases hBit with rfl | rfl
  · have hZ1 : (Goldilocks.zero == Goldilocks.one) = false := by decide
    rw [hZ1]; simp only [Bool.false_eq_true, ↓reduceIte, beq_iff_eq]
    unfold muxGoldilocksResidual
    change CommRingOps.add
      (CommRingOps.mul CommRingOps.zero (CommRingOps.sub out aTrue))
      (CommRingOps.mul (CommRingOps.sub CommRingOps.one CommRingOps.zero) (CommRingOps.sub out aFalse)) =
      CommRingOps.zero ↔ out = aFalse
    rw [LawfulCommRing.zero_mul, LawfulCommRing.zero_add,
        LawfulCommRing.sub_zero, LawfulCommRing.one_mul]
    exact LawfulCommRing.sub_eq_zero_iff
  · simp only [beq_self_eq_true, ↓reduceIte, beq_iff_eq]
    unfold muxGoldilocksResidual
    change CommRingOps.add
      (CommRingOps.mul CommRingOps.one (CommRingOps.sub out aTrue))
      (CommRingOps.mul (CommRingOps.sub CommRingOps.one CommRingOps.one) (CommRingOps.sub out aFalse)) =
      CommRingOps.zero ↔ out = aTrue
    rw [LawfulCommRing.one_mul, LawfulCommRing.sub_self,
        LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
    exact LawfulCommRing.sub_eq_zero_iff

def muxDigest4Residuals (bit : Goldilocks) (aTrue aFalse out : Digest4) : List Goldilocks :=
  [muxGoldilocksResidual bit aTrue.x0 aFalse.x0 out.x0,
   muxGoldilocksResidual bit aTrue.x1 aFalse.x1 out.x1,
   muxGoldilocksResidual bit aTrue.x2 aFalse.x2 out.x2,
   muxGoldilocksResidual bit aTrue.x3 aFalse.x3 out.x3]

theorem muxDigest4Residuals_allZero_iff {bit : Goldilocks}
    (hBit : bit = Goldilocks.zero ∨ bit = Goldilocks.one)
    (aTrue aFalse out : Digest4) :
    allZeroGoldilocks (muxDigest4Residuals bit aTrue aFalse out) = true ↔
      out = (if bit == Goldilocks.one then aTrue else aFalse) := by
  rcases aTrue with ⟨t0, t1, t2, t3⟩
  rcases aFalse with ⟨f0, f1, f2, f3⟩
  rcases out with ⟨o0, o1, o2, o3⟩
  unfold muxDigest4Residuals allZeroGoldilocks
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    muxGoldilocksResidual_eq_zero_iff hBit]
  cases (bit == Goldilocks.one) <;> simp [Lane4.mk.injEq]

def wotsStepTweak4 (layer treeIdx kpIdx chainIdx stepIdx : Nat) : Digest4 :=
  ⟨domainWotsStep,
   packWotsAddrLimb layer kpIdx chainIdx stepIdx,
   Goldilocks.ofNat (treeIdx % (2 ^ 32)),
   Goldilocks.ofNat ((treeIdx / (2 ^ 32)) % (2 ^ 32))⟩

/-- Unary 3-step WOTS+C chain witness (`WotsChainStep0/1/2` in `trace.rs:112-125`). -/
structure UnaryWotsChainWitness where
  act0   : Goldilocks
  act1   : Goldilocks
  act2   : Goldilocks
  sigVal : Digest4
  s1     : Digest4
  s2     : Digest4
  endVal : Digest4
  perm0  : Poseidon2PermWitness
  perm1  : Poseidon2PermWitness
  perm2  : Poseidon2PermWitness
  deriving DecidableEq, Repr

def honestUnaryWotsChainWitness (pkSeed : Digest4) (layer treeIdx kpIdx chainIdx digit : Nat)
    (sigVal : Digest4) : UnaryWotsChainWitness :=
  let a0 := if digit == 0 then Goldilocks.one else Goldilocks.zero
  let a1 := if digit ≤ 1 then Goldilocks.one else Goldilocks.zero
  let a2 := if digit ≤ 2 then Goldilocks.one else Goldilocks.zero
  let p0 := honestPoseidon2PermWitness ⟨sigVal, pkSeed, wotsStepTweak4 layer treeIdx kpIdx chainIdx 0⟩
  let s1 := if a0 == Goldilocks.one then lane4Add p0.output.b0 sigVal else sigVal
  let p1 := honestPoseidon2PermWitness ⟨s1, pkSeed, wotsStepTweak4 layer treeIdx kpIdx chainIdx 1⟩
  let s2 := if a1 == Goldilocks.one then lane4Add p1.output.b0 s1 else s1
  let p2 := honestPoseidon2PermWitness ⟨s2, pkSeed, wotsStepTweak4 layer treeIdx kpIdx chainIdx 2⟩
  let s3 := if a2 == Goldilocks.one then lane4Add p2.output.b0 s2 else s2
  { act0 := a0, act1 := a1, act2 := a2, sigVal := sigVal,
    s1 := s1, s2 := s2, endVal := s3, perm0 := p0, perm1 := p1, perm2 := p2 }

def unaryWotsChainResiduals (pkSeed : Digest4) (layer treeIdx kpIdx chainIdx : Nat)
    (expectedDigit : Goldilocks) (w : UnaryWotsChainWitness) : List Goldilocks :=
  let mono01 := Goldilocks.mul w.act0 (Goldilocks.sub Goldilocks.one w.act1)
  let mono12 := Goldilocks.mul w.act1 (Goldilocks.sub Goldilocks.one w.act2)
  let sumEq  := Goldilocks.sub
    (Goldilocks.add expectedDigit (Goldilocks.add w.act0 (Goldilocks.add w.act1 w.act2)))
    (Goldilocks.ofNat 3)
  [boolBitResidual w.act0, boolBitResidual w.act1, boolBitResidual w.act2, mono01, mono12, sumEq] ++
  (state12Sub w.perm0.input ⟨w.sigVal, pkSeed, wotsStepTweak4 layer treeIdx kpIdx chainIdx 0⟩).toList ++
  poseidon2PermResiduals w.perm0 ++
  muxDigest4Residuals w.act0 (lane4Add w.perm0.output.b0 w.sigVal) w.sigVal w.s1 ++
  (state12Sub w.perm1.input ⟨w.s1, pkSeed, wotsStepTweak4 layer treeIdx kpIdx chainIdx 1⟩).toList ++
  poseidon2PermResiduals w.perm1 ++
  muxDigest4Residuals w.act1 (lane4Add w.perm1.output.b0 w.s1) w.s1 w.s2 ++
  (state12Sub w.perm2.input ⟨w.s2, pkSeed, wotsStepTweak4 layer treeIdx kpIdx chainIdx 2⟩).toList ++
  poseidon2PermResiduals w.perm2 ++
  muxDigest4Residuals w.act2 (lane4Add w.perm2.output.b0 w.s2) w.s2 w.endVal

private theorem monotone_bits_sum_three_unique {d a0 a1 a2 : Goldilocks}
    (hd : d.val < 4)
    (hb0 : a0 = Goldilocks.zero ∨ a0 = Goldilocks.one)
    (hb1 : a1 = Goldilocks.zero ∨ a1 = Goldilocks.one)
    (hb2 : a2 = Goldilocks.zero ∨ a2 = Goldilocks.one)
    (hm01 : Goldilocks.mul a0 (Goldilocks.sub Goldilocks.one a1) = Goldilocks.zero)
    (hm12 : Goldilocks.mul a1 (Goldilocks.sub Goldilocks.one a2) = Goldilocks.zero)
    (hSum : Goldilocks.add d (Goldilocks.add a0 (Goldilocks.add a1 a2)) = Goldilocks.ofNat 3) :
    a0 = (if d.val == 0 then Goldilocks.one else Goldilocks.zero) ∧
    a1 = (if d.val ≤ 1 then Goldilocks.one else Goldilocks.zero) ∧
    a2 = (if d.val ≤ 2 then Goldilocks.one else Goldilocks.zero) := by
  have hdCases : d = Goldilocks.zero ∨ d = Goldilocks.one ∨
                 d = Goldilocks.ofNat 2 ∨ d = Goldilocks.ofNat 3 := by
    rcases d with ⟨v, hv⟩
    dsimp only at hd
    have hvC : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by omega
    rcases hvC with rfl | rfl | rfl | rfl
    · exact .inl rfl
    · exact .inr (.inl rfl)
    · exact .inr (.inr (.inl (Goldilocks.ext rfl)))
    · exact .inr (.inr (.inr (Goldilocks.ext rfl)))
  rcases hdCases with rfl | rfl | rfl | rfl <;>
    rcases hb0 with rfl | rfl <;>
    rcases hb1 with rfl | rfl <;>
    rcases hb2 with rfl | rfl <;>
    revert hm01 hm12 hSum <;> decide +kernel

private theorem wotsStepHash_eq_tweak4 (pkSeed cur : Digest4) (layer treeIdx kpIdx chainIdx stp : Nat) :
    wotsStepHash pkSeed cur layer treeIdx kpIdx chainIdx stp =
      lane4Add (poseidon2Perm12 ⟨cur, pkSeed, wotsStepTweak4 layer treeIdx kpIdx chainIdx stp⟩).b0 cur := by
  unfold wotsStepHash poseidon2Compress12FF wotsStepTweak4
  rfl

private theorem wotsChainWalk_zero_steps (pkSeed : Digest4) (layer treeIdx kpIdx chainIdx s : Nat)
    (cur : Digest4) :
    wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx s 0 cur = cur := by
  unfold wotsChainWalk
  rw [natIterAt]

private theorem wotsChainWalk_succ_steps (pkSeed : Digest4) (layer treeIdx kpIdx chainIdx s n : Nat)
    (cur : Digest4) :
    wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx s (n + 1) cur =
      wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx (s + 1) n
        (wotsStepHash pkSeed cur layer treeIdx kpIdx chainIdx s) := by
  unfold wotsChainWalk
  rw [natIterAt]

theorem honestUnaryWotsChainWitness_endVal
    (pkSeed : Digest4) (layer treeIdx kpIdx chainIdx d : Nat) (sigVal : Digest4)
    (hd : d < 4) :
    (honestUnaryWotsChainWitness pkSeed layer treeIdx kpIdx chainIdx d sigVal).endVal =
      wotsChainWalk pkSeed layer treeIdx kpIdx chainIdx d (3 - d) sigVal := by
  have hPermOut : ∀ st : Poseidon2State12, (honestPoseidon2PermWitness st).output = poseidon2Perm12 st :=
    fun st => by unfold poseidon2Perm12 honestPoseidon2PermWitness; rfl
  have hCases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases hCases with rfl | rfl | rfl | rfl
  · unfold honestUnaryWotsChainWitness
    simp only [beq_self_eq_true, Nat.zero_le, ↓reduceIte]
    rw [hPermOut, hPermOut, hPermOut]
    simp only [Nat.reduceSub, wotsChainWalk_succ_steps, wotsChainWalk_zero_steps,
      wotsStepHash_eq_tweak4, Nat.reduceAdd]
  · unfold honestUnaryWotsChainWitness
    have hZ : ((1 : Nat) == 0) = false := by decide
    have hZ1 : (Goldilocks.zero == Goldilocks.one) = false := by decide
    simp only [hZ, Bool.false_eq_true, ↓reduceIte, hZ1, Nat.le_refl,
      show (1 : Nat) ≤ 2 by decide, beq_self_eq_true]
    rw [hPermOut, hPermOut]
    simp only [Nat.reduceSub, wotsChainWalk_succ_steps, wotsChainWalk_zero_steps,
      wotsStepHash_eq_tweak4, Nat.reduceAdd]
  · unfold honestUnaryWotsChainWitness
    have hZ0 : ((2 : Nat) == 0) = false := by decide
    have hZ1 : ¬ ((2 : Nat) ≤ 1) := by decide
    have hG01 : (Goldilocks.zero == Goldilocks.one) = false := by decide
    simp only [hZ0, hZ1, Bool.false_eq_true, ↓reduceIte, hG01, Nat.le_refl, beq_self_eq_true]
    rw [hPermOut]
    simp only [Nat.reduceSub, wotsChainWalk_succ_steps, wotsChainWalk_zero_steps,
      wotsStepHash_eq_tweak4, Nat.reduceAdd]
  · unfold honestUnaryWotsChainWitness
    have hZ0 : ((3 : Nat) == 0) = false := by decide
    have hZ1 : ¬ ((3 : Nat) ≤ 1) := by decide
    have hZ2 : ¬ ((3 : Nat) ≤ 2) := by decide
    have hG01 : (Goldilocks.zero == Goldilocks.one) = false := by decide
    simp only [hZ0, hZ1, hZ2, Bool.false_eq_true, ↓reduceIte, hG01]
    simp only [Nat.reduceSub, wotsChainWalk_zero_steps]

theorem unaryWotsChainResiduals_allZero_iff
    (pkSeed : Digest4) (layer treeIdx kpIdx chainIdx : Nat)
    (expectedDigit : Goldilocks) (w : UnaryWotsChainWitness)
    (hd : expectedDigit.val < 4) :
    allZeroGoldilocks (unaryWotsChainResiduals pkSeed layer treeIdx kpIdx chainIdx expectedDigit w) = true ↔
      w = honestUnaryWotsChainWitness pkSeed layer treeIdx kpIdx chainIdx expectedDigit.val w.sigVal := by
  unfold unaryWotsChainResiduals
  have hHead6 : ∀ (r0 r1 r2 r3 r4 r5 : Goldilocks),
      allZeroGoldilocks [r0, r1, r2, r3, r4, r5] =
        ((r0 == Goldilocks.zero) && (r1 == Goldilocks.zero) && (r2 == Goldilocks.zero) &&
         (r3 == Goldilocks.zero) && (r4 == Goldilocks.zero) && (r5 == Goldilocks.zero)) := by
    intros; simp [allZeroGoldilocks, Bool.and_assoc]
  simp only [allZeroGoldilocks_append, hHead6, Bool.and_eq_true, beq_iff_eq,
    boolBitResidual_eq_zero_iff, gold_sub_eq_zero_iff,
    state12Sub_toList_allZero_iff, poseidon2PermResiduals_allZero_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb0, hb1⟩, hb2⟩, hm01⟩, hm12⟩, hSum⟩, hIn0⟩, hP0⟩, hMux0⟩,
            hIn1⟩, hP1⟩, hMux1⟩, hIn2⟩, hP2⟩, hMux2⟩
    obtain ⟨ea0, ea1, ea2⟩ := monotone_bits_sum_three_unique hd hb0 hb1 hb2 hm01 hm12 hSum
    have es1 := (muxDigest4Residuals_allZero_iff hb0 _ _ w.s1).mp hMux0
    have es2 := (muxDigest4Residuals_allZero_iff hb1 _ _ w.s2).mp hMux1
    have ee  := (muxDigest4Residuals_allZero_iff hb2 _ _ w.endVal).mp hMux2
    rw [hIn0] at hP0
    rw [hP0, ea0] at es1
    rw [hIn1, es1] at hP1
    rw [hP1, es1, ea1] at es2
    rw [hIn2, es2] at hP2
    rw [hP2, es2, ea2] at ee
    rcases w with ⟨a0, a1, a2, sv, s1, s2, ev, p0, p1, p2⟩
    dsimp only at ea0 ea1 ea2 es1 es2 ee hP0 hP1 hP2
    subst ea0 ea1 ea2 hP0 es1 hP1 es2 hP2 ee
    rfl
  · intro hW
    obtain ⟨sv, hsv⟩ : ∃ sv, sv = w.sigVal := ⟨_, rfl⟩
    rw [← hsv] at hW
    subst hW
    clear hsv
    have hCases : expectedDigit = Goldilocks.zero ∨ expectedDigit = Goldilocks.one ∨
                  expectedDigit = Goldilocks.ofNat 2 ∨ expectedDigit = Goldilocks.ofNat 3 := by
      rcases expectedDigit with ⟨v, hv⟩
      dsimp only at hd
      have hvC : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by omega
      rcases hvC with rfl | rfl | rfl | rfl
      · exact .inl rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr (.inl (Goldilocks.ext rfl)))
      · exact .inr (.inr (.inr (Goldilocks.ext rfl)))
    have hFlags :
        let hw := honestUnaryWotsChainWitness pkSeed layer treeIdx kpIdx chainIdx expectedDigit.val sv
        (hw.act0 = Goldilocks.zero ∨ hw.act0 = Goldilocks.one) ∧
        (hw.act1 = Goldilocks.zero ∨ hw.act1 = Goldilocks.one) ∧
        (hw.act2 = Goldilocks.zero ∨ hw.act2 = Goldilocks.one) ∧
        Goldilocks.mul hw.act0 (Goldilocks.sub Goldilocks.one hw.act1) = Goldilocks.zero ∧
        Goldilocks.mul hw.act1 (Goldilocks.sub Goldilocks.one hw.act2) = Goldilocks.zero ∧
        Goldilocks.add expectedDigit (Goldilocks.add hw.act0 (Goldilocks.add hw.act1 hw.act2)) =
          Goldilocks.ofNat 3 := by
      dsimp only [honestUnaryWotsChainWitness]
      rcases hCases with rfl | rfl | rfl | rfl <;>
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        first | exact .inl (by decide +kernel) | exact .inr (by decide +kernel) | decide +kernel
    obtain ⟨hb0, hb1, hb2, hm01, hm12, hSum⟩ := hFlags
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb0, hb1⟩, hb2⟩, hm01⟩, hm12⟩, hSum⟩, rfl⟩, rfl⟩,
            (muxDigest4Residuals_allZero_iff hb0 _ _ _).mpr rfl⟩,
            rfl⟩, rfl⟩, (muxDigest4Residuals_allZero_iff hb1 _ _ _).mpr rfl⟩, rfl⟩, rfl⟩,
            (muxDigest4Residuals_allZero_iff hb2 _ _ _).mpr rfl⟩

/-- The four limbs of a `Lane4` / `Digest4` as a residual list. -/
def Lane4.toList (l : Lane4) : List Goldilocks :=
  [l.x0, l.x1, l.x2, l.x3]

/-! ### 2-Block Merkle, 2-Rate Sponge, `H_msg`, and Full `K`-Signer Trace Arithmetization -/

/-- Witness for a single 2-block `merkleNodeHash` level (`MerkleLeft` + `MerkleRight` in `trace.rs:132-139`). -/
structure MerkleLevelWitness where
  dirBit     : Goldilocks
  sibling    : Digest4
  leftChild  : Digest4
  rightChild : Digest4
  parent     : Digest4
  perm0      : Poseidon2PermWitness
  perm1      : Poseidon2PermWitness
  deriving DecidableEq, Repr

private def merkleNodeMeta0 (layer level nodeIdx : Nat) : Goldilocks :=
  Goldilocks.ofNat ((layer % 65536) * (2 ^ 48) + (level % 65536) * (2 ^ 32) + (nodeIdx % (2 ^ 32)))

private def merkleNodeTreeLo (treeIdx : Nat) : Goldilocks :=
  Goldilocks.ofNat (treeIdx % (2 ^ 32))

private def merkleNodeTreeHi (treeIdx : Nat) : Goldilocks :=
  Goldilocks.ofNat ((treeIdx / (2 ^ 32)) % (2 ^ 32))

private def merkleNodeState0 (domainTag : Goldilocks) (pkSeed : Digest4)
    (layer treeIdx level nodeIdx : Nat) (left : Digest4) : Poseidon2State12 :=
  ⟨pkSeed,
   left,
   ⟨domainTag, merkleNodeMeta0 layer level nodeIdx, merkleNodeTreeLo treeIdx, merkleNodeTreeHi treeIdx⟩⟩

private def merkleNodeState1 (st0 : Poseidon2State12) (right : Digest4) : Poseidon2State12 :=
  ⟨lane4Add st0.b0 right,
   ⟨Goldilocks.add st0.b1.x0 Goldilocks.one,
    Goldilocks.add st0.b1.x1 poseidon2IvTag,
    st0.b1.x2,
    st0.b1.x3⟩,
   st0.b2⟩

private theorem merkleNodeHash_eq_states (domainTag : Goldilocks) (pkSeed : Digest4)
    (layer treeIdx level nodeIdx : Nat) (left right : Digest4) :
    merkleNodeHash domainTag pkSeed layer treeIdx level nodeIdx left right =
      (poseidon2Perm12 (merkleNodeState1
        (poseidon2Perm12 (merkleNodeState0 domainTag pkSeed layer treeIdx level nodeIdx left))
        right)).b0 := by
  unfold merkleNodeHash merkleNodeState0 merkleNodeState1 merkleNodeMeta0 merkleNodeTreeLo merkleNodeTreeHi
  rfl

attribute [local irreducible] merkleNodeMeta0 merkleNodeTreeLo merkleNodeTreeHi merkleNodeState0 merkleNodeState1

def honestMerkleLevelWitness (domainTag : Goldilocks) (pkSeed : Digest4)
    (layer treeIdx : Nat) (addr : Nat → Nat → Nat) (level idx : Nat) (cur sib : Digest4) : MerkleLevelWitness :=
  let parentIdx := idx / 2
  let bit := if idx % 2 == 0 then Goldilocks.zero else Goldilocks.one
  let leftC := if idx % 2 == 0 then cur else sib
  let rightC := if idx % 2 == 0 then sib else cur
  let p0 := honestPoseidon2PermWitness (merkleNodeState0 domainTag pkSeed layer treeIdx level (addr level parentIdx) leftC)
  let p1 := honestPoseidon2PermWitness (merkleNodeState1 p0.output rightC)
  { dirBit := bit, sibling := sib, leftChild := leftC, rightChild := rightC,
    parent := p1.output.b0, perm0 := p0, perm1 := p1 }

def merkleLevelResiduals (domainTag : Goldilocks) (pkSeed : Digest4)
    (layer treeIdx : Nat) (addr : Nat → Nat → Nat) (level idx : Nat) (cur : Digest4) (w : MerkleLevelWitness) : List Goldilocks :=
  let parentIdx := idx / 2
  let expectedBit := if idx % 2 == 0 then Goldilocks.zero else Goldilocks.one
  [boolBitResidual w.dirBit, Goldilocks.sub w.dirBit expectedBit] ++
  muxDigest4Residuals w.dirBit w.sibling cur w.leftChild ++
  muxDigest4Residuals w.dirBit cur w.sibling w.rightChild ++
  (state12Sub w.perm0.input (merkleNodeState0 domainTag pkSeed layer treeIdx level (addr level parentIdx) w.leftChild)).toList ++
  poseidon2PermResiduals w.perm0 ++
  (state12Sub w.perm1.input (merkleNodeState1 w.perm0.output w.rightChild)).toList ++
  poseidon2PermResiduals w.perm1 ++
  (lane4Sub w.parent w.perm1.output.b0).toList

private theorem lane4Sub_toList_allZero_iff (a b : Digest4) :
    allZeroGoldilocks (lane4Sub a b).toList = true ↔ a = b := by
  rcases a with ⟨a0, a1, a2, a3⟩
  rcases b with ⟨b0, b1, b2, b3⟩
  unfold allZeroGoldilocks lane4Sub Lane4.toList
  simp [gold_sub_eq_zero_iff, Lane4.mk.injEq]

theorem honestMerkleLevelWitness_parent (domainTag : Goldilocks) (pkSeed : Digest4)
    (layer treeIdx : Nat) (addr : Nat → Nat → Nat) (level idx : Nat) (cur sib : Digest4) :
    (honestMerkleLevelWitness domainTag pkSeed layer treeIdx addr level idx cur sib).parent =
      (if idx % 2 == 0 then
         merkleNodeHash domainTag pkSeed layer treeIdx level (addr level (idx / 2)) cur sib
       else
         merkleNodeHash domainTag pkSeed layer treeIdx level (addr level (idx / 2)) sib cur) := by
  have hPermOut : ∀ st : Poseidon2State12, (honestPoseidon2PermWitness st).output = poseidon2Perm12 st :=
    fun st => by unfold poseidon2Perm12 honestPoseidon2PermWitness; rfl
  unfold honestMerkleLevelWitness
  dsimp only
  rw [hPermOut, hPermOut]
  cases hEven : (idx % 2 == 0) <;>
    simp only [Bool.false_eq_true, ↓reduceIte] <;>
    exact (merkleNodeHash_eq_states domainTag pkSeed layer treeIdx level (addr level (idx / 2)) _ _).symm

theorem merkleLevelResiduals_allZero_iff (domainTag : Goldilocks) (pkSeed : Digest4)
    (layer treeIdx : Nat) (addr : Nat → Nat → Nat) (level idx : Nat) (cur : Digest4) (w : MerkleLevelWitness) :
    allZeroGoldilocks (merkleLevelResiduals domainTag pkSeed layer treeIdx addr level idx cur w) = true ↔
      w = honestMerkleLevelWitness domainTag pkSeed layer treeIdx addr level idx cur w.sibling := by
  unfold merkleLevelResiduals
  have hPair : ∀ (r0 r1 : Goldilocks),
      allZeroGoldilocks [r0, r1] = ((r0 == Goldilocks.zero) && (r1 == Goldilocks.zero)) := by
    intros; simp [allZeroGoldilocks]
  simp only [allZeroGoldilocks_append, hPair, Bool.and_eq_true, beq_iff_eq,
    boolBitResidual_eq_zero_iff, gold_sub_eq_zero_iff,
    state12Sub_toList_allZero_iff, poseidon2PermResiduals_allZero_iff,
    lane4Sub_toList_allZero_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨hb, hBitEq0⟩, hMuxL⟩, hMuxR⟩, hIn0⟩, hP0⟩, hIn1⟩, hP1⟩, hPar⟩
    have hBitEq : w.dirBit = (if idx % 2 == 0 then Goldilocks.zero else Goldilocks.one) := by
      rw [hBitEq0]
      rcases Nat.mod_two_eq_zero_or_one idx with h | h <;> rw [h] <;> rfl
    have eL := (muxDigest4Residuals_allZero_iff hb w.sibling cur w.leftChild).mp hMuxL
    have eR := (muxDigest4Residuals_allZero_iff hb cur w.sibling w.rightChild).mp hMuxR
    have hDirCond :
        (w.dirBit == Goldilocks.one) = !(idx % 2 == 0) := by
      rw [hBitEq]
      cases (idx % 2 == 0) <;> decide
    have eL' : w.leftChild = (if idx % 2 == 0 then cur else w.sibling) := by
      rw [eL, hDirCond]
      cases (idx % 2 == 0) <;> rfl
    have eR' : w.rightChild = (if idx % 2 == 0 then w.sibling else cur) := by
      rw [eR, hDirCond]
      cases (idx % 2 == 0) <;> rfl
    rw [hIn0, eL'] at hP0
    rw [hIn1, hP0, eR'] at hP1
    rw [hP1] at hPar
    rcases w with ⟨db, sib, lc, rc, par, p0, p1⟩
    dsimp only at hBitEq eL' eR' hP0 hP1 hPar
    subst hBitEq eL' eR' hP0 hP1 hPar
    rfl
  · intro hW
    obtain ⟨sv, hsv⟩ : ∃ sv, sv = w.sibling := ⟨_, rfl⟩
    rw [← hsv] at hW
    subst hW
    clear hsv
    let hw := honestMerkleLevelWitness domainTag pkSeed layer treeIdx addr level idx cur sv
    have hb : hw.dirBit = Goldilocks.zero ∨ hw.dirBit = Goldilocks.one := by
      dsimp only [hw, honestMerkleLevelWitness]
      cases (idx % 2 == 0)
      · exact .inr rfl
      · exact .inl rfl
    have hMux : ∀ (b : Bool) (x y : Digest4),
        (if b = true then x else y) =
          if ((if b = true then Goldilocks.zero else Goldilocks.one) == Goldilocks.one) = true then y else x := by
      intro b x y
      cases b <;> rfl
    have hMuxL : allZeroGoldilocks (muxDigest4Residuals hw.dirBit hw.sibling cur hw.leftChild) = true := by
      rw [muxDigest4Residuals_allZero_iff hb]
      exact hMux (idx % 2 == 0) cur sv
    have hMuxR : allZeroGoldilocks (muxDigest4Residuals hw.dirBit cur hw.sibling hw.rightChild) = true := by
      rw [muxDigest4Residuals_allZero_iff hb]
      exact hMux (idx % 2 == 0) sv cur
    have hBitEq : hw.dirBit = (if idx % 2 = 0 then Goldilocks.zero else Goldilocks.one) := by
      dsimp only [hw, honestMerkleLevelWitness]
      rcases Nat.mod_two_eq_zero_or_one idx with h | h <;> rw [h] <;> rfl
    exact ⟨⟨⟨⟨⟨⟨⟨⟨hb, hBitEq⟩, hMuxL⟩, hMuxR⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩

/-- Polymorphic Merkle path witness builder & residual verifier (`< 5ms` elaboration). -/
private def buildMerklePathWitnessPoly {D LW : Type}
    (mkLvl : Nat → Nat → D → D → LW)
    (parentOf : LW → D) :
    List D → Nat → Nat → D → List LW
  | [], _, _, _ => []
  | sib :: sibs, lvl, idx, cur =>
    let w := mkLvl lvl idx cur sib
    w :: buildMerklePathWitnessPoly mkLvl parentOf sibs (lvl + 1) (idx / 2) (parentOf w)

private def merklePathResidualsPoly {D LW RES : Type}
    (lvlRes : Nat → Nat → D → LW → List RES)
    (parentOf : LW → D) :
    List LW → Nat → Nat → D → (D × List RES)
  | [], _, _, cur => (cur, [])
  | w :: ws, lvl, idx, cur =>
    let r0 := lvlRes lvl idx cur w
    let (finalRt, restRes) := merklePathResidualsPoly lvlRes parentOf ws (lvl + 1) (idx / 2) (parentOf w)
    (finalRt, r0 ++ restRes)

private theorem merklePathResidualsPoly_allZero_iff {D LW RES : Type}
    (mkLvl : Nat → Nat → D → D → LW)
    (lvlRes : Nat → Nat → D → LW → List RES)
    (sibOf : LW → D)
    (parentOf : LW → D)
    (nodeHash : Nat → Nat → D → D → D)
    (zeroPred : List RES → Bool)
    (hNil : zeroPred [] = true)
    (hAppend : ∀ a b, zeroPred (a ++ b) = (zeroPred a && zeroPred b))
    (hLvlIff : ∀ lvl idx cur w, zeroPred (lvlRes lvl idx cur w) = true ↔ w = mkLvl lvl idx cur (sibOf w))
    (hSibMk : ∀ lvl idx cur sib, sibOf (mkLvl lvl idx cur sib) = sib)
    (hParMk : ∀ lvl idx cur sib,
      parentOf (mkLvl lvl idx cur sib) =
        (if idx % 2 == 0 then nodeHash lvl (idx / 2) cur sib else nodeHash lvl (idx / 2) sib cur)) :
    ∀ (ws : List LW) (lvl idx : Nat) (cur : D),
      (zeroPred (merklePathResidualsPoly lvlRes parentOf ws lvl idx cur).2 = true ↔
        ws = buildMerklePathWitnessPoly mkLvl parentOf (ws.map sibOf) lvl idx cur) ∧
      (ws = buildMerklePathWitnessPoly mkLvl parentOf (ws.map sibOf) lvl idx cur →
        (merklePathResidualsPoly lvlRes parentOf ws lvl idx cur).1 =
          merkleWalkPoly nodeHash (ws.map sibOf) lvl idx cur)
  | [], _, _, _ => by
    exact ⟨⟨fun _ => rfl, fun _ => hNil⟩, fun _ => rfl⟩
  | w :: ws, lvl, idx, cur => by
    dsimp only [merklePathResidualsPoly, buildMerklePathWitnessPoly, merkleWalkPoly, List.map_cons]
    have ih := merklePathResidualsPoly_allZero_iff mkLvl lvlRes sibOf parentOf nodeHash
      zeroPred hNil hAppend hLvlIff hSibMk hParMk ws (lvl + 1) (idx / 2) (parentOf w)
    rw [hAppend, Bool.and_eq_true, hLvlIff]
    refine ⟨?_, ?_⟩
    · constructor
      · rintro ⟨hw, hRest⟩
        exact List.cons_eq_cons.mpr ⟨hw, hw ▸ ih.1.mp hRest⟩
      · intro hCons
        obtain ⟨hw, hTail⟩ := List.cons.inj hCons
        exact ⟨hw, ih.1.mpr (hw ▸ hTail)⟩
    · intro hCons
      obtain ⟨hw, hTail⟩ := List.cons.inj hCons
      have hTailRt := ih.2 (hw ▸ hTail)
      rw [hTailRt]
      have hParEq : parentOf w =
          (if idx % 2 == 0 then nodeHash lvl (idx / 2) cur (sibOf w)
           else nodeHash lvl (idx / 2) (sibOf w) cur) := by
        conv => lhs; rw [hw]
        exact hParMk lvl idx cur (sibOf w)
      rw [hParEq]
      rfl

def honestMerklePathWitness (domainTag : Goldilocks) (pkSeed : Digest4)
    (layer treeIdx : Nat) (addr : Nat → Nat → Nat) (startLvl idx : Nat) (cur : Digest4) (sibs : List Digest4) :
    List MerkleLevelWitness :=
  buildMerklePathWitnessPoly
    (honestMerkleLevelWitness domainTag pkSeed layer treeIdx addr)
    MerkleLevelWitness.parent
    sibs startLvl idx cur

def merklePathResiduals (domainTag : Goldilocks) (pkSeed : Digest4)
    (layer treeIdx : Nat) (addr : Nat → Nat → Nat) (startLvl idx : Nat) (cur : Digest4) (ws : List MerkleLevelWitness) :
    (Digest4 × List Goldilocks) :=
  merklePathResidualsPoly
    (merkleLevelResiduals domainTag pkSeed layer treeIdx addr)
    MerkleLevelWitness.parent
    ws startLvl idx cur

theorem merklePathResiduals_allZero_iff (domainTag : Goldilocks) (pkSeed : Digest4)
    (layer treeIdx : Nat) (addr : Nat → Nat → Nat) (startLvl idx : Nat) (cur : Digest4) (ws : List MerkleLevelWitness) :
    (allZeroGoldilocks (merklePathResiduals domainTag pkSeed layer treeIdx addr startLvl idx cur ws).2 = true ↔
      ws = honestMerklePathWitness domainTag pkSeed layer treeIdx addr startLvl idx cur
             (ws.map MerkleLevelWitness.sibling)) ∧
    (ws = honestMerklePathWitness domainTag pkSeed layer treeIdx addr startLvl idx cur
            (ws.map MerkleLevelWitness.sibling) →
      (merklePathResiduals domainTag pkSeed layer treeIdx addr startLvl idx cur ws).1 =
        merkleWalkRoot domainTag pkSeed layer treeIdx addr startLvl idx cur
          (ws.map MerkleLevelWitness.sibling)) :=
  merklePathResidualsPoly_allZero_iff
    (honestMerkleLevelWitness domainTag pkSeed layer treeIdx addr)
    (merkleLevelResiduals domainTag pkSeed layer treeIdx addr)
    MerkleLevelWitness.sibling
    MerkleLevelWitness.parent
    (merkleAddrNodeHash domainTag pkSeed layer treeIdx addr)
    allZeroGoldilocks rfl allZeroGoldilocks_append
    (merkleLevelResiduals_allZero_iff domainTag pkSeed layer treeIdx addr)
    (fun _ _ _ _ => rfl)
    (honestMerkleLevelWitness_parent domainTag pkSeed layer treeIdx addr)
    ws startLvl idx cur

/-- Polymorphic 2-rate-block sponge absorption witness (`compressWotsEndpointsSponge` & `compressForsRootsSponge`). -/
private def buildAbsorbPermsPoly {D S PW : Type}
    (mkPerm : S → PW) (outOf : PW → S)
    (in1 : S → D → S) (in2 : S → D → D → S) :
    List D → S → Option D → List PW
  | [], _, none => []
  | [], st, some e0 => [mkPerm (in1 st e0)]
  | e :: rest, st, none => buildAbsorbPermsPoly mkPerm outOf in1 in2 rest st (some e)
  | e1 :: rest, st, some e0 =>
    let pw := mkPerm (in2 st e0 e1)
    pw :: buildAbsorbPermsPoly mkPerm outOf in1 in2 rest (outOf pw) none

private def absorbPermsResidualsPoly {D S PW RES : Type}
    (permRes : S → PW → List RES) (outOf : PW → S) (badRes : List RES)
    (in1 : S → D → S) (in2 : S → D → D → S) :
    List D → List PW → S → Option D → (S × List RES)
  | [], [], st, none => (st, [])
  | [], [pw], st, some e0 => (outOf pw, permRes (in1 st e0) pw)
  | e :: rest, pws, st, none => absorbPermsResidualsPoly permRes outOf badRes in1 in2 rest pws st (some e)
  | e1 :: rest, pw :: pws, st, some e0 =>
    let r0 := permRes (in2 st e0 e1) pw
    let (finalSt, restRes) := absorbPermsResidualsPoly permRes outOf badRes in1 in2 rest pws (outOf pw) none
    (finalSt, r0 ++ restRes)
  | [], _ :: _, st, none => (st, badRes)
  | [], [], st, some _ => (st, badRes)
  | [], _ :: _ :: _, st, some _ => (st, badRes)
  | _ :: _, [], st, some _ => (st, badRes)

private theorem absorbPermsResidualsPoly_allZero_iff {D S PW RES : Type}
    (mkPerm : S → PW) (permRes : S → PW → List RES) (outOf : PW → S) (badRes : List RES)
    (permFn : S → S) (in1 : S → D → S) (in2 : S → D → D → S)
    (zeroPred : List RES → Bool)
    (hNil : zeroPred [] = true) (hBad : zeroPred badRes = false)
    (hAppend : ∀ a b, zeroPred (a ++ b) = (zeroPred a && zeroPred b))
    (hPermIff : ∀ expIn pw, zeroPred (permRes expIn pw) = true ↔ pw = mkPerm expIn)
    (hOutMk : ∀ s, outOf (mkPerm s) = permFn s) :
    ∀ (xs : List D) (pws : List PW) (st : S) (pend : Option D),
      (zeroPred (absorbPermsResidualsPoly permRes outOf badRes in1 in2 xs pws st pend).2 = true ↔
        pws = buildAbsorbPermsPoly mkPerm outOf in1 in2 xs st pend) ∧
      (pws = buildAbsorbPermsPoly mkPerm outOf in1 in2 xs st pend →
        (absorbPermsResidualsPoly permRes outOf badRes in1 in2 xs pws st pend).1 =
          absorbPairsPoly (fun s e0 => permFn (in1 s e0)) (fun s e0 e1 => permFn (in2 s e0 e1)) xs st pend)
  | [], [], _, none => by
    dsimp only [absorbPermsResidualsPoly, buildAbsorbPermsPoly, absorbPairsPoly]
    exact ⟨by simp [hNil], fun _ => rfl⟩
  | [], _ :: pws, _, none => by
    cases pws <;>
      exact ⟨⟨fun h => absurd (hBad.symm.trans h) Bool.false_ne_true, fun h => by cases h⟩,
        fun h => by cases h⟩
  | [], [], _, some _ => by
    dsimp only [absorbPermsResidualsPoly, buildAbsorbPermsPoly]
    exact ⟨by simp [hBad], fun h => by cases h⟩
  | [], [pw], st, some e0 => by
    dsimp only [absorbPermsResidualsPoly, buildAbsorbPermsPoly, absorbPairsPoly]
    rw [hPermIff]
    exact ⟨by simp, fun h => by obtain rfl := List.cons.inj h |>.1; exact hOutMk _⟩
  | [], _ :: _ :: _, _, some _ => by
    dsimp only [absorbPermsResidualsPoly, buildAbsorbPermsPoly]
    exact ⟨by simp [hBad], fun h => by injection h with _ hTl; cases hTl⟩
  | e :: rest, pws, st, none => by
    dsimp only [absorbPermsResidualsPoly, buildAbsorbPermsPoly, absorbPairsPoly]
    exact absorbPermsResidualsPoly_allZero_iff mkPerm permRes outOf badRes permFn in1 in2
      zeroPred hNil hBad hAppend hPermIff hOutMk rest pws st (some e)
  | _ :: _, [], _, some _ => by
    dsimp only [absorbPermsResidualsPoly, buildAbsorbPermsPoly]
    exact ⟨by simp [hBad], fun h => by cases h⟩
  | e1 :: rest, pw :: pws, st, some e0 => by
    dsimp only [absorbPermsResidualsPoly, buildAbsorbPermsPoly, absorbPairsPoly]
    have ih := absorbPermsResidualsPoly_allZero_iff mkPerm permRes outOf badRes permFn in1 in2
      zeroPred hNil hBad hAppend hPermIff hOutMk rest pws (outOf pw) none
    rw [hAppend, Bool.and_eq_true, hPermIff]
    refine ⟨?_, ?_⟩
    · constructor
      · rintro ⟨hpw, hRest⟩
        exact List.cons_eq_cons.mpr ⟨hpw, hpw ▸ ih.1.mp hRest⟩
      · intro hCons
        obtain ⟨hpw, hTail⟩ := List.cons.inj hCons
        exact ⟨hpw, ih.1.mpr (hpw ▸ hTail)⟩
    · intro hCons
      obtain ⟨hpw, hTail⟩ := List.cons.inj hCons
      rw [ih.2 (hpw ▸ hTail)]
      subst hpw
      rw [hOutMk]

/-- Sponge absorption witness (`initPerm` + `pairPerms` + `finalPerm` + `outDigest`). -/
structure SpongeAbsorbWitness where
  initPerm  : Poseidon2PermWitness
  pairPerms : List Poseidon2PermWitness
  finalPerm : Poseidon2PermWitness
  outDigest : Digest4
  deriving DecidableEq, Repr

def spongeIn1 (s : Poseidon2State12) (e0 : Digest4) : Poseidon2State12 :=
  ⟨lane4Add s.b0 e0, s.b1, s.b2⟩

def spongeIn2 (s : Poseidon2State12) (e0 e1 : Digest4) : Poseidon2State12 :=
  ⟨lane4Add s.b0 e0, lane4Add s.b1 e1, s.b2⟩

def spongePadOne (s : Poseidon2State12) : Poseidon2State12 :=
  ⟨⟨Goldilocks.add s.b0.x0 Goldilocks.one, s.b0.x1, s.b0.x2, s.b0.x3⟩, s.b1, s.b2⟩

def wotsPkInitState (pkSeed : Digest4) (layer treeIdx kpIdx len : Nat) : Poseidon2State12 :=
  let layerKp := Goldilocks.ofNat ((layer % (2 ^ 32)) * (2 ^ 32) + (kpIdx % (2 ^ 32)))
  ⟨pkSeed,
   ⟨layerKp,
    Goldilocks.ofNat (treeIdx % (2 ^ 32)),
    Goldilocks.ofNat ((treeIdx / (2 ^ 32)) % (2 ^ 32)),
    Goldilocks.ofNat len⟩,
   ⟨domainWotsPk, Goldilocks.zero, Goldilocks.zero, poseidon2IvTag⟩⟩

def forsRootsInitState (geom : AggSigGeometry) (pkSeed : Digest4) (leafGlobalIdx : Nat) :
    Poseidon2State12 :=
  ⟨pkSeed,
   ⟨Goldilocks.ofNat (forsKpIdx geom leafGlobalIdx),
    Goldilocks.ofNat (forsHyperTreeIdx geom leafGlobalIdx % (2 ^ 32)),
    Goldilocks.ofNat ((forsHyperTreeIdx geom leafGlobalIdx / (2 ^ 32)) % (2 ^ 32)),
    Goldilocks.ofNat geom.forsTrees⟩,
   ⟨domainForsRoots, Goldilocks.zero, Goldilocks.zero, poseidon2IvTag⟩⟩

private theorem compressWotsEndpointsSponge_eq_states (pkSeed : Digest4)
    (layer treeIdx kpIdx : Nat) (endpoints : List Digest4) :
    compressWotsEndpointsSponge pkSeed layer treeIdx kpIdx endpoints =
      (poseidon2Perm12 (spongePadOne
        (absorbPairsPoly (fun s e0 => poseidon2Perm12 (spongeIn1 s e0))
                         (fun s e0 e1 => poseidon2Perm12 (spongeIn2 s e0 e1))
                         endpoints
                         (poseidon2Perm12 (wotsPkInitState pkSeed layer treeIdx kpIdx endpoints.length))
                         none))).b0 := by
  unfold compressWotsEndpointsSponge absorbDigest4Pairs wotsPkInitState spongePadOne spongeIn1 spongeIn2
  rfl

private theorem compressForsRootsSponge_eq_states (geom : AggSigGeometry) (pkSeed : Digest4)
    (leafGlobalIdx : Nat) (roots : List Digest4) :
    compressForsRootsSponge geom pkSeed leafGlobalIdx roots =
      (poseidon2Perm12 (spongePadOne
        (absorbPairsPoly (fun s e0 => poseidon2Perm12 (spongeIn1 s e0))
                         (fun s e0 e1 => poseidon2Perm12 (spongeIn2 s e0 e1))
                         roots
                         (poseidon2Perm12 (forsRootsInitState geom pkSeed leafGlobalIdx))
                         none))).b0 := by
  unfold compressForsRootsSponge absorbDigest4Pairs forsRootsInitState spongePadOne spongeIn1 spongeIn2
  rfl

attribute [local irreducible] spongeIn1 spongeIn2 spongePadOne wotsPkInitState forsRootsInitState

private def permWithInputResiduals (expIn : Poseidon2State12) (pw : Poseidon2PermWitness) : List Goldilocks :=
  (state12Sub pw.input expIn).toList ++ poseidon2PermResiduals pw

private theorem permWithInputResiduals_allZero_iff (expIn : Poseidon2State12) (pw : Poseidon2PermWitness) :
    allZeroGoldilocks (permWithInputResiduals expIn pw) = true ↔ pw = honestPoseidon2PermWitness expIn := by
  unfold permWithInputResiduals
  rw [allZeroGoldilocks_append, Bool.and_eq_true, state12Sub_toList_allZero_iff,
      poseidon2PermResiduals_allZero_iff]
  constructor
  · rintro ⟨hIn, hHon⟩; rwa [hIn] at hHon
  · rintro rfl; exact ⟨rfl, rfl⟩

def honestSpongeAbsorbWitness (initSt : Poseidon2State12) (blocks : List Digest4) : SpongeAbsorbWitness :=
  let pInit := honestPoseidon2PermWitness initSt
  let pPairs := buildAbsorbPermsPoly honestPoseidon2PermWitness Poseidon2PermWitness.output
    spongeIn1 spongeIn2 blocks pInit.output none
  let stAbs := absorbPairsPoly (fun s e0 => poseidon2Perm12 (spongeIn1 s e0))
    (fun s e0 e1 => poseidon2Perm12 (spongeIn2 s e0 e1)) blocks pInit.output none
  let pFin := honestPoseidon2PermWitness (spongePadOne stAbs)
  { initPerm := pInit, pairPerms := pPairs, finalPerm := pFin, outDigest := pFin.output.b0 }

def spongeAbsorbResiduals (initSt : Poseidon2State12) (blocks : List Digest4)
    (w : SpongeAbsorbWitness) : List Goldilocks :=
  let rInit := permWithInputResiduals initSt w.initPerm
  let (stAbs, rPairs) := absorbPermsResidualsPoly permWithInputResiduals Poseidon2PermWitness.output
    [Goldilocks.one] spongeIn1 spongeIn2 blocks w.pairPerms w.initPerm.output none
  let rFin := permWithInputResiduals (spongePadOne stAbs) w.finalPerm
  rInit ++ rPairs ++ rFin ++ (lane4Sub w.outDigest w.finalPerm.output.b0).toList

theorem spongeAbsorbResiduals_allZero_iff (initSt : Poseidon2State12) (blocks : List Digest4)
    (w : SpongeAbsorbWitness) :
    (allZeroGoldilocks (spongeAbsorbResiduals initSt blocks w) = true ↔
      w = honestSpongeAbsorbWitness initSt blocks) ∧
    (w = honestSpongeAbsorbWitness initSt blocks →
      w.outDigest = (poseidon2Perm12 (spongePadOne
        (absorbPairsPoly (fun s e0 => poseidon2Perm12 (spongeIn1 s e0))
                         (fun s e0 e1 => poseidon2Perm12 (spongeIn2 s e0 e1))
                         blocks (poseidon2Perm12 initSt) none))).b0) := by
  have hPermOut : ∀ st : Poseidon2State12, (honestPoseidon2PermWitness st).output = poseidon2Perm12 st :=
    fun st => by unfold poseidon2Perm12 honestPoseidon2PermWitness; rfl
  unfold spongeAbsorbResiduals honestSpongeAbsorbWitness
  dsimp only
  have hAbs := absorbPermsResidualsPoly_allZero_iff honestPoseidon2PermWitness permWithInputResiduals
    Poseidon2PermWitness.output [Goldilocks.one] poseidon2Perm12 spongeIn1 spongeIn2
    allZeroGoldilocks rfl (by decide) allZeroGoldilocks_append permWithInputResiduals_allZero_iff hPermOut
    blocks w.pairPerms w.initPerm.output none
  simp only [allZeroGoldilocks_append, Bool.and_eq_true, permWithInputResiduals_allZero_iff,
    lane4Sub_toList_allZero_iff]
  refine ⟨?_, ?_⟩
  · constructor
    · rintro ⟨⟨⟨hInit, hPairs⟩, hFin⟩, hOut⟩
      have ePairs := hAbs.1.mp hPairs
      have stEq := hAbs.2 ePairs
      rw [hInit] at ePairs stEq hFin
      rw [stEq] at hFin
      rw [hFin] at hOut
      rcases w with ⟨pi, pp, pf, od⟩
      dsimp only at hInit ePairs hFin hOut
      subst hInit ePairs hFin hOut
      rfl
    · intro hW
      rcases w with ⟨pi, pp, pf, od⟩
      injection hW with hInit ePairs hFin hOut
      subst hInit ePairs
      rw [hAbs.2 rfl]
      subst hFin hOut
      exact ⟨⟨⟨rfl, hAbs.1.mpr rfl⟩, rfl⟩, rfl⟩
  · intro hW
    rw [hW]
    dsimp only
    rw [hPermOut, hPermOut]

theorem wotsPkSpongeResiduals_allZero_iff (pkSeed : Digest4) (layer treeIdx kpIdx : Nat)
    (endpoints : List Digest4) (w : SpongeAbsorbWitness) :
    (allZeroGoldilocks (spongeAbsorbResiduals (wotsPkInitState pkSeed layer treeIdx kpIdx endpoints.length)
       endpoints w) = true ↔
      w = honestSpongeAbsorbWitness (wotsPkInitState pkSeed layer treeIdx kpIdx endpoints.length) endpoints) ∧
    (w = honestSpongeAbsorbWitness (wotsPkInitState pkSeed layer treeIdx kpIdx endpoints.length) endpoints →
      w.outDigest = compressWotsEndpointsSponge pkSeed layer treeIdx kpIdx endpoints) := by
  have hBase := spongeAbsorbResiduals_allZero_iff
    (wotsPkInitState pkSeed layer treeIdx kpIdx endpoints.length) endpoints w
  exact ⟨hBase.1, fun hW => (hBase.2 hW).trans
    (compressWotsEndpointsSponge_eq_states pkSeed layer treeIdx kpIdx endpoints).symm⟩

theorem forsRootsSpongeResiduals_allZero_iff (geom : AggSigGeometry) (pkSeed : Digest4) (leafGlobalIdx : Nat)
    (roots : List Digest4) (w : SpongeAbsorbWitness) :
    (allZeroGoldilocks (spongeAbsorbResiduals (forsRootsInitState geom pkSeed leafGlobalIdx)
       roots w) = true ↔
      w = honestSpongeAbsorbWitness (forsRootsInitState geom pkSeed leafGlobalIdx) roots) ∧
    (w = honestSpongeAbsorbWitness (forsRootsInitState geom pkSeed leafGlobalIdx) roots →
      w.outDigest = compressForsRootsSponge geom pkSeed leafGlobalIdx roots) := by
  have hBase := spongeAbsorbResiduals_allZero_iff
    (forsRootsInitState geom pkSeed leafGlobalIdx) roots w
  exact ⟨hBase.1, fun hW => (hBase.2 hW).trans
    (compressForsRootsSponge_eq_states geom pkSeed leafGlobalIdx roots).symm⟩

/-- 3-block stateful `H_msg` trace witness (`computeHmsgStateful`, `sig.rs:396`). -/
structure HmsgStatefulTraceWitness where
  perm0  : Poseidon2PermWitness
  perm1  : Poseidon2PermWitness
  perm2  : Poseidon2PermWitness
  outMsg : Digest5
  deriving DecidableEq, Repr

private def hmsgStatefulIn0 (pk : AggValidatorPk) (mu : Digest5) (kpIdx tswCtr : Nat) : Poseidon2State12 :=
  let kpCtr := Goldilocks.ofNat ((kpIdx % (2 ^ 32)) * (2 ^ 32) + (tswCtr % (2 ^ 32)))
  ⟨pk.pkSeed, pk.pkRoot, ⟨domainHMsgStateful, kpCtr, mu.limb4, poseidon2IvTag⟩⟩

private def hmsgStatefulIn1 (st0 : Poseidon2State12) (rRand : Digest4) (mu : Digest5) : Poseidon2State12 :=
  let muLow : Digest4 := ⟨mu.limb0, mu.limb1, mu.limb2, mu.limb3⟩
  ⟨lane4Add st0.b0 rRand, lane4Add st0.b1 muLow, st0.b2⟩

private def state12OutDigest5 (st : Poseidon2State12) : Digest5 :=
  { limb0 := st.b0.x0, limb1 := st.b0.x1, limb2 := st.b0.x2, limb3 := st.b0.x3, limb4 := st.b1.x0 }

private theorem computeHmsgStateful_eq_states (pk : AggValidatorPk) (rRand : Digest4)
    (mu : Digest5) (kpIdx tswCtr : Nat) :
    computeHmsgStateful pk rRand mu kpIdx tswCtr =
      state12OutDigest5 (poseidon2Perm12 (spongePadOne
        (poseidon2Perm12 (hmsgStatefulIn1
          (poseidon2Perm12 (hmsgStatefulIn0 pk mu kpIdx tswCtr)) rRand mu)))) := by
  unfold computeHmsgStateful hmsgStatefulIn0 hmsgStatefulIn1 spongePadOne state12OutDigest5
  rfl

/-- 2-block deterministic tree `H_msg` trace witness (`computeHmsgDetTree`, `sig.rs:433`). -/
structure HmsgDetTreeTraceWitness where
  perm0  : Poseidon2PermWitness
  perm1  : Poseidon2PermWitness
  outMsg : Digest5
  deriving DecidableEq, Repr

private def hmsgDetTreeIn0 (pk : AggValidatorPk) (layer treeIdx kpIdx : Nat) : Poseidon2State12 :=
  let layerKp := Goldilocks.ofNat ((layer % (2 ^ 32)) * (2 ^ 32) + (kpIdx % (2 ^ 32)))
  ⟨pk.pkSeed, pk.pkRoot,
   ⟨domainHMsgDetTree, layerKp,
    Goldilocks.ofNat (treeIdx % (2 ^ 32)),
    Goldilocks.ofNat ((treeIdx / (2 ^ 32)) % (2 ^ 32))⟩⟩

private def hmsgDetTreeIn1 (st0 : Poseidon2State12) (tswCtr : Nat) (childRt : Digest4) : Poseidon2State12 :=
  ⟨lane4Add st0.b0 childRt,
   ⟨Goldilocks.add st0.b1.x0 (Goldilocks.ofNat (tswCtr % (2 ^ 32))),
    Goldilocks.add st0.b1.x1 Goldilocks.one,
    st0.b1.x2,
    st0.b1.x3⟩,
   st0.b2⟩

private theorem computeHmsgDetTree_eq_states (pk : AggValidatorPk)
    (layer treeIdx kpIdx tswCtr : Nat) (childRt : Digest4) :
    computeHmsgDetTree pk layer treeIdx kpIdx tswCtr childRt =
      state12OutDigest5 (poseidon2Perm12 (hmsgDetTreeIn1
        (poseidon2Perm12 (hmsgDetTreeIn0 pk layer treeIdx kpIdx)) tswCtr childRt)) := by
  unfold computeHmsgDetTree hmsgDetTreeIn0 hmsgDetTreeIn1 state12OutDigest5
  rfl

attribute [local irreducible] hmsgStatefulIn0 hmsgStatefulIn1 hmsgDetTreeIn0 hmsgDetTreeIn1 state12OutDigest5

private def digest5SubResiduals (a b : Digest5) : List Goldilocks :=
  [Goldilocks.sub a.limb0 b.limb0,
   Goldilocks.sub a.limb1 b.limb1,
   Goldilocks.sub a.limb2 b.limb2,
   Goldilocks.sub a.limb3 b.limb3,
   Goldilocks.sub a.limb4 b.limb4]

private theorem digest5SubResiduals_allZero_iff (a b : Digest5) :
    allZeroGoldilocks (digest5SubResiduals a b) = true ↔ a = b := by
  rcases a with ⟨a0, a1, a2, a3, a4⟩
  rcases b with ⟨b0, b1, b2, b3, b4⟩
  unfold digest5SubResiduals allZeroGoldilocks
  simp [gold_sub_eq_zero_iff, Digest5.mk.injEq]

def honestHmsgStatefulTraceWitness (pk : AggValidatorPk) (rRand : Digest4)
    (mu : Digest5) (kpIdx tswCtr : Nat) : HmsgStatefulTraceWitness :=
  let p0 := honestPoseidon2PermWitness (hmsgStatefulIn0 pk mu kpIdx tswCtr)
  let p1 := honestPoseidon2PermWitness (hmsgStatefulIn1 p0.output rRand mu)
  let p2 := honestPoseidon2PermWitness (spongePadOne p1.output)
  { perm0 := p0, perm1 := p1, perm2 := p2, outMsg := state12OutDigest5 p2.output }

def hmsgStatefulResiduals (pk : AggValidatorPk) (rRand : Digest4)
    (mu : Digest5) (kpIdx tswCtr : Nat) (w : HmsgStatefulTraceWitness) : List Goldilocks :=
  permWithInputResiduals (hmsgStatefulIn0 pk mu kpIdx tswCtr) w.perm0 ++
  permWithInputResiduals (hmsgStatefulIn1 w.perm0.output rRand mu) w.perm1 ++
  permWithInputResiduals (spongePadOne w.perm1.output) w.perm2 ++
  digest5SubResiduals w.outMsg (state12OutDigest5 w.perm2.output)

theorem hmsgStatefulResiduals_allZero_iff (pk : AggValidatorPk) (rRand : Digest4)
    (mu : Digest5) (kpIdx tswCtr : Nat) (w : HmsgStatefulTraceWitness) :
    (allZeroGoldilocks (hmsgStatefulResiduals pk rRand mu kpIdx tswCtr w) = true ↔
      w = honestHmsgStatefulTraceWitness pk rRand mu kpIdx tswCtr) ∧
    (w = honestHmsgStatefulTraceWitness pk rRand mu kpIdx tswCtr →
      w.outMsg = computeHmsgStateful pk rRand mu kpIdx tswCtr) := by
  have hPermOut : ∀ st : Poseidon2State12, (honestPoseidon2PermWitness st).output = poseidon2Perm12 st :=
    fun st => by unfold poseidon2Perm12 honestPoseidon2PermWitness; rfl
  unfold hmsgStatefulResiduals honestHmsgStatefulTraceWitness
  simp only [allZeroGoldilocks_append, Bool.and_eq_true, permWithInputResiduals_allZero_iff,
    digest5SubResiduals_allZero_iff]
  refine ⟨?_, ?_⟩
  · constructor
    · rintro ⟨⟨⟨h0, h1⟩, h2⟩, hOut⟩
      rw [h0] at h1
      rw [h1] at h2
      rw [h2] at hOut
      rcases w with ⟨p0, p1, p2, om⟩
      dsimp only at h0 h1 h2 hOut
      subst h0 h1 h2 hOut
      rfl
    · rintro rfl
      exact ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
  · intro hW
    rw [hW]
    dsimp only
    rw [hPermOut, hPermOut, hPermOut, computeHmsgStateful_eq_states]

def honestHmsgDetTreeTraceWitness (pk : AggValidatorPk)
    (layer treeIdx kpIdx tswCtr : Nat) (childRt : Digest4) : HmsgDetTreeTraceWitness :=
  let p0 := honestPoseidon2PermWitness (hmsgDetTreeIn0 pk layer treeIdx kpIdx)
  let p1 := honestPoseidon2PermWitness (hmsgDetTreeIn1 p0.output tswCtr childRt)
  { perm0 := p0, perm1 := p1, outMsg := state12OutDigest5 p1.output }

def hmsgDetTreeResiduals (pk : AggValidatorPk)
    (layer treeIdx kpIdx tswCtr : Nat) (childRt : Digest4) (w : HmsgDetTreeTraceWitness) : List Goldilocks :=
  permWithInputResiduals (hmsgDetTreeIn0 pk layer treeIdx kpIdx) w.perm0 ++
  permWithInputResiduals (hmsgDetTreeIn1 w.perm0.output tswCtr childRt) w.perm1 ++
  digest5SubResiduals w.outMsg (state12OutDigest5 w.perm1.output)

theorem hmsgDetTreeResiduals_allZero_iff (pk : AggValidatorPk)
    (layer treeIdx kpIdx tswCtr : Nat) (childRt : Digest4) (w : HmsgDetTreeTraceWitness) :
    (allZeroGoldilocks (hmsgDetTreeResiduals pk layer treeIdx kpIdx tswCtr childRt w) = true ↔
      w = honestHmsgDetTreeTraceWitness pk layer treeIdx kpIdx tswCtr childRt) ∧
    (w = honestHmsgDetTreeTraceWitness pk layer treeIdx kpIdx tswCtr childRt →
      w.outMsg = computeHmsgDetTree pk layer treeIdx kpIdx tswCtr childRt) := by
  have hPermOut : ∀ st : Poseidon2State12, (honestPoseidon2PermWitness st).output = poseidon2Perm12 st :=
    fun st => by unfold poseidon2Perm12 honestPoseidon2PermWitness; rfl
  unfold hmsgDetTreeResiduals honestHmsgDetTreeTraceWitness
  simp only [allZeroGoldilocks_append, Bool.and_eq_true, permWithInputResiduals_allZero_iff,
    digest5SubResiduals_allZero_iff]
  refine ⟨?_, ?_⟩
  · constructor
    · rintro ⟨⟨h0, h1⟩, hOut⟩
      rw [h0] at h1
      rw [h1] at hOut
      rcases w with ⟨p0, p1, om⟩
      dsimp only at h0 h1 hOut
      subst h0 h1 hOut
      rfl
    · rintro rfl
      exact ⟨⟨rfl, rfl⟩, rfl⟩
  · intro hW
    rw [hW]
    dsimp only
    rw [hPermOut, hPermOut, computeHmsgDetTree_eq_states]

/-! ### Polymorphic WOTS+C Layer, Hypertree, FORS, `RowGate7` AST, and `K`-Signer Trace Exactness -/

private theorem shapeIte_allZero (p : Prop) [Decidable p]
    (h : allZeroGoldilocks (if p then [] else [Goldilocks.one]) = true) : p := by
  by_cases hp : p
  · exact hp
  · simp only [hp, ↓reduceIte] at h
    exact absurd h (by decide)

private theorem shapeIte_allZero_of (p : Prop) [Decidable p] (hp : p) :
    allZeroGoldilocks (if p then [] else [Goldilocks.one]) = true := by
  simp only [hp, ↓reduceIte]
  rfl

private def buildChainListWitnessPoly {DW V CW : Type}
    (mkChain : Nat → DW → V → CW) :
    List DW → List V → Nat → List CW
  | [], _, _ => []
  | _, [], _ => []
  | d :: ds, v :: values, c => mkChain c d v :: buildChainListWitnessPoly mkChain ds values (c + 1)

private def chainListResidualsPoly {DW CW RES : Type}
    (cRes : Nat → DW → CW → List RES) (badRes : List RES) :
    List DW → List CW → Nat → List RES
  | [], [], _ => []
  | d :: ds, w :: ws, c => cRes c d w ++ chainListResidualsPoly cRes badRes ds ws (c + 1)
  | [], _ :: _, _ => badRes
  | _ :: _, [], _ => badRes

private theorem chainListResidualsPoly_allZero_iff {DW V CW RES : Type}
    (mkChain : Nat → DW → V → CW)
    (cRes : Nat → DW → CW → List RES)
    (natOf : DW → Nat)
    (sigOf : CW → V)
    (endOf : CW → V)
    (walkFn : Nat → Nat → Nat → V → V)
    (badRes : List RES)
    (zeroPred : List RES → Bool)
    (dValid : DW → Prop)
    (hNil : zeroPred [] = true) (hBad : zeroPred badRes = false)
    (hAppend : ∀ a b, zeroPred (a ++ b) = (zeroPred a && zeroPred b))
    (hChainIff : ∀ c d w, dValid d → (zeroPred (cRes c d w) = true ↔ w = mkChain c d (sigOf w)))
    (hEndMk : ∀ c d v, dValid d → endOf (mkChain c d v) = walkFn c (natOf d) (3 - natOf d) v) :
    ∀ (ds : List DW) (ws : List CW) (c : Nat),
      (∀ d ∈ ds, dValid d) →
      (zeroPred (chainListResidualsPoly cRes badRes ds ws c) = true ↔
        ds.length = ws.length ∧
        ws = buildChainListWitnessPoly mkChain ds (ws.map sigOf) c) ∧
      (ds.length = ws.length →
        ws = buildChainListWitnessPoly mkChain ds (ws.map sigOf) c →
        ws.map endOf = recoverEndpointsPoly walkFn (ds.map natOf) (ws.map sigOf) c)
  | [], [], _, _ => by
    dsimp only [chainListResidualsPoly, buildChainListWitnessPoly, recoverEndpointsPoly, List.map_nil]
    exact ⟨⟨fun _ => ⟨rfl, rfl⟩, fun _ => hNil⟩, fun _ _ => rfl⟩
  | [], _ :: _, _, _ => by
    dsimp only [chainListResidualsPoly]
    exact ⟨⟨fun h => (by rw [hBad] at h; cases h), fun h => absurd h.1 (Nat.succ_ne_zero _).symm⟩,
      fun h => absurd h (Nat.succ_ne_zero _).symm⟩
  | _ :: _, [], _, _ => by
    dsimp only [chainListResidualsPoly]
    exact ⟨⟨fun h => (by rw [hBad] at h; cases h), fun h => absurd h.1 (Nat.succ_ne_zero _)⟩,
      fun h => absurd h (Nat.succ_ne_zero _)⟩
  | d :: ds, w :: ws, c, hAll => by
    have hd : dValid d := hAll d (List.mem_cons_self ..)
    have hTailValid : ∀ x ∈ ds, dValid x := fun x hx => hAll x (List.mem_cons_of_mem _ hx)
    dsimp only [chainListResidualsPoly, buildChainListWitnessPoly, List.map_cons, recoverEndpointsPoly]
    have ih := chainListResidualsPoly_allZero_iff mkChain cRes natOf sigOf endOf walkFn badRes zeroPred dValid
      hNil hBad hAppend hChainIff hEndMk ds ws (c + 1) hTailValid
    rw [hAppend, Bool.and_eq_true, hChainIff c d w hd]
    refine ⟨?_, ?_⟩
    · constructor
      · rintro ⟨hw, hRest⟩
        obtain ⟨hLen, hWs⟩ := ih.1.mp hRest
        exact ⟨congrArg Nat.succ hLen, List.cons_eq_cons.mpr ⟨hw, hWs⟩⟩
      · rintro ⟨hLen, hCons⟩
        obtain ⟨hw, hWs⟩ := List.cons.inj hCons
        exact ⟨hw, ih.1.mpr ⟨Nat.succ.inj hLen, hWs⟩⟩
    · intro hLen hCons
      obtain ⟨hw, hWs⟩ := List.cons.inj hCons
      have hEnd0 : endOf w = walkFn c (natOf d) (3 - natOf d) (sigOf w) := by
        have hE := hEndMk c d (sigOf w) hd
        rw [← hw] at hE
        exact hE
      exact List.cons_eq_cons.mpr ⟨hEnd0, ih.2 (Nat.succ.inj hLen) hWs⟩

def honestWotsChainsWitness (pkSeed : Digest4) (layer treeIdx kpIdx : Nat)
    (digits : List Goldilocks) (sigVals : List Digest4) : List UnaryWotsChainWitness :=
  buildChainListWitnessPoly
    (fun c d v => honestUnaryWotsChainWitness pkSeed layer treeIdx kpIdx c d.val v)
    digits sigVals 0

def wotsChainsResiduals (pkSeed : Digest4) (layer treeIdx kpIdx : Nat)
    (digits : List Goldilocks) (ws : List UnaryWotsChainWitness) : List Goldilocks :=
  chainListResidualsPoly
    (unaryWotsChainResiduals pkSeed layer treeIdx kpIdx)
    [Goldilocks.one]
    digits ws 0

theorem wotsChainsResiduals_allZero_iff (pkSeed : Digest4) (layer treeIdx kpIdx : Nat)
    (digits : List Goldilocks) (ws : List UnaryWotsChainWitness)
    (hLt4 : ∀ d ∈ digits, d.val < 4) :
    (allZeroGoldilocks (wotsChainsResiduals pkSeed layer treeIdx kpIdx digits ws) = true ↔
      digits.length = ws.length ∧
      ws = honestWotsChainsWitness pkSeed layer treeIdx kpIdx digits (ws.map UnaryWotsChainWitness.sigVal)) ∧
    (digits.length = ws.length →
      ws = honestWotsChainsWitness pkSeed layer treeIdx kpIdx digits (ws.map UnaryWotsChainWitness.sigVal) →
      ws.map UnaryWotsChainWitness.endVal =
        recoverAggWotsEndpoints pkSeed layer treeIdx kpIdx 0
          (digits.map Goldilocks.val) (ws.map UnaryWotsChainWitness.sigVal)) :=
  chainListResidualsPoly_allZero_iff
    (fun c (d : Goldilocks) v => honestUnaryWotsChainWitness pkSeed layer treeIdx kpIdx c d.val v)
    (unaryWotsChainResiduals pkSeed layer treeIdx kpIdx)
    Goldilocks.val
    UnaryWotsChainWitness.sigVal
    UnaryWotsChainWitness.endVal
    (wotsChainWalk pkSeed layer treeIdx kpIdx)
    [Goldilocks.one]
    allZeroGoldilocks
    (fun d => d.val < 4)
    rfl (by decide) allZeroGoldilocks_append
    (fun c d w hd => unaryWotsChainResiduals_allZero_iff pkSeed layer treeIdx kpIdx c d w hd)
    (fun c (d : Goldilocks) v hd => honestUnaryWotsChainWitness_endVal pkSeed layer treeIdx kpIdx c d.val v hd)
    digits ws 0 hLt4


private theorem map_sigOf_buildChainListWitnessPoly {DW V CW : Type}
    (mkChain : Nat → DW → V → CW) (sigOf : CW → V)
    (hSig : ∀ c d v, sigOf (mkChain c d v) = v) :
    ∀ (ds : List DW) (values : List V) (c : Nat),
      ds.length = values.length →
      (buildChainListWitnessPoly mkChain ds values c).map sigOf = values
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => absurd h (Nat.succ_ne_zero _).symm
  | _ :: _, [], _, h => absurd h (Nat.succ_ne_zero _)
  | d :: ds, v :: values, c, h => by
    dsimp only [buildChainListWitnessPoly]
    rw [List.map_cons, hSig, map_sigOf_buildChainListWitnessPoly mkChain sigOf hSig ds values (c + 1) (Nat.succ.inj h)]

private theorem length_buildChainListWitnessPoly {DW V CW : Type}
    (mkChain : Nat → DW → V → CW) :
    ∀ (ds : List DW) (values : List V) (c : Nat),
      ds.length = values.length →
      (buildChainListWitnessPoly mkChain ds values c).length = values.length
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => absurd h (Nat.succ_ne_zero _).symm
  | _ :: _, [], _, h => absurd h (Nat.succ_ne_zero _)
  | _ :: ds, _ :: values, c, h => by
    dsimp only [buildChainListWitnessPoly]
    rw [List.length_cons, length_buildChainListWitnessPoly mkChain ds values (c + 1) (Nat.succ.inj h)]
    rfl

private theorem map_sibOf_buildMerklePathWitnessPoly {D LW : Type}
    (mkLvl : Nat → Nat → D → D → LW) (parentOf sibOf : LW → D)
    (hSib : ∀ lvl idx cur sib, sibOf (mkLvl lvl idx cur sib) = sib) :
    ∀ (sibs : List D) (lvl idx : Nat) (cur : D),
      (buildMerklePathWitnessPoly mkLvl parentOf sibs lvl idx cur).map sibOf = sibs
  | [], _, _, _ => rfl
  | sib :: sibs, lvl, idx, cur => by
    dsimp only [buildMerklePathWitnessPoly]
    rw [List.map_cons, hSib, map_sibOf_buildMerklePathWitnessPoly mkLvl parentOf sibOf hSib sibs]

private theorem length_buildMerklePathWitnessPoly {D LW : Type}
    (mkLvl : Nat → Nat → D → D → LW) (parentOf : LW → D) :
    ∀ (sibs : List D) (lvl idx : Nat) (cur : D),
      (buildMerklePathWitnessPoly mkLvl parentOf sibs lvl idx cur).length = sibs.length
  | [], _, _, _ => rfl
  | _ :: sibs, lvl, idx, cur => by
    dsimp only [buildMerklePathWitnessPoly]
    rw [List.length_cons, length_buildMerklePathWitnessPoly mkLvl parentOf sibs]
    rfl

/-- Single WOTS+C + XMSS subtree layer execution trace witness (`verifyWotsLayer` sub-circuit). -/
structure WotsLayerTraceWitness where
  tswCtr   : Nat
  decomp   : Hmsg5DecompWitness
  chains   : List UnaryWotsChainWitness
  pkSponge : SpongeAbsorbWitness
  merkle   : List MerkleLevelWitness
  rootOut  : Digest4
  deriving DecidableEq, Repr

def wotsLayerWitnessSig (w : WotsLayerTraceWitness) : WotsLayerSig :=
  { tswCtr     := w.tswCtr
    wotsChains := w.chains.map UnaryWotsChainWitness.sigVal
    merklePath := w.merkle.map MerkleLevelWitness.sibling }

def honestWotsLayerTraceWitness (geom : AggSigGeometry) (pk : AggValidatorPk)
    (layer treeIdx kpIdx : Nat) (hmsg : Digest5) (lsig : WotsLayerSig) : WotsLayerTraceWitness :=
  let dec := honestHmsg5DecompWitness hmsg
  let digitWires := hmsg5DigitWires geom dec
  let chs := honestWotsChainsWitness pk.pkSeed layer treeIdx kpIdx digitWires lsig.wotsChains
  let endpoints := chs.map UnaryWotsChainWitness.endVal
  let sp := honestSpongeAbsorbWitness
    (wotsPkInitState pk.pkSeed layer treeIdx kpIdx endpoints.length) endpoints
  let mPath := honestMerklePathWitness domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr 1 kpIdx sp.outDigest lsig.merklePath
  let rt := (merklePathResiduals domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr 1 kpIdx sp.outDigest mPath).1
  { tswCtr := lsig.tswCtr, decomp := dec, chains := chs, pkSponge := sp, merkle := mPath, rootOut := rt }

def wotsLayerTraceResiduals (geom : AggSigGeometry) (pk : AggValidatorPk)
    (layer treeIdx kpIdx : Nat) (hmsg : Digest5) (w : WotsLayerTraceWitness) : List Goldilocks :=
  let shapeRes :=
    if w.chains.length == geom.wotsChains && w.merkle.length == geom.subtreeHeight then []
    else [Goldilocks.one]
  let digitWires := hmsg5DigitWires geom w.decomp
  let endpoints := w.chains.map UnaryWotsChainWitness.endVal
  let (walkedRt, mRes) :=
    merklePathResiduals domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr 1 kpIdx w.pkSponge.outDigest w.merkle
  shapeRes ++
  hmsg5DecompResiduals geom hmsg w.decomp ++
  wotsChainsResiduals pk.pkSeed layer treeIdx kpIdx digitWires w.chains ++
  spongeAbsorbResiduals (wotsPkInitState pk.pkSeed layer treeIdx kpIdx endpoints.length) endpoints w.pkSponge ++
  mRes ++
  (lane4Sub w.rootOut walkedRt).toList

theorem wotsLayerTraceResiduals_sound (geom : AggSigGeometry) (pk : AggValidatorPk)
    (layer treeIdx kpIdx : Nat) (hmsg : Digest5) (w : WotsLayerTraceWitness)
    (hChainsLe : geom.wotsChains ≤ 128)
    (hTargetBound : geom.targetSum < 3 * geom.wotsChains)
    (hZero : allZeroGoldilocks (wotsLayerTraceResiduals geom pk layer treeIdx kpIdx hmsg w) = true) :
    verifyWotsLayer geom pk layer treeIdx kpIdx hmsg (wotsLayerWitnessSig w) = some w.rootOut := by
  unfold wotsLayerTraceResiduals at hZero
  dsimp only at hZero
  simp only [allZeroGoldilocks_append, Bool.and_eq_true, lane4Sub_toList_allZero_iff] at hZero
  rcases hZero with ⟨⟨⟨⟨⟨hShape, hDec⟩, hCh⟩, hSp⟩, hM⟩, hRtEq⟩
  have hLenChk := shapeIte_allZero _ hShape
  · obtain ⟨hDecEq, ds, hExt, hSum, hWiresMap⟩ :=
      (hmsg5DecompResiduals_allZero_iff geom hmsg w.decomp hChainsLe hTargetBound).mp hDec
    obtain ⟨_, hDsLt4⟩ := extractWotsDigitsChecked_spec hChainsLe hExt
    have hWiresLt4 : ∀ d ∈ hmsg5DigitWires geom w.decomp, d.val < 4 := by
      intro d hd
      have hMemMap : d.val ∈ (hmsg5DigitWires geom w.decomp).map Goldilocks.val := List.mem_map_of_mem hd
      rw [hWiresMap] at hMemMap
      exact hDsLt4 d.val hMemMap
    have hChIff := wotsChainsResiduals_allZero_iff pk.pkSeed layer treeIdx kpIdx
      (hmsg5DigitWires geom w.decomp) w.chains hWiresLt4
    obtain ⟨hDigLenEq, hChEq⟩ := hChIff.1.mp hCh
    have hEndEq := hChIff.2 hDigLenEq hChEq
    rw [hWiresMap] at hEndEq
    have hSpIff := wotsPkSpongeResiduals_allZero_iff pk.pkSeed layer treeIdx kpIdx
      (w.chains.map UnaryWotsChainWitness.endVal) w.pkSponge
    have hSpOut := hSpIff.2 (hSpIff.1.mp hSp)
    have hMIff := merklePathResiduals_allZero_iff domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr 1 kpIdx
      w.pkSponge.outDigest w.merkle
    have hWalkOut := hMIff.2 (hMIff.1.mp hM)
    unfold verifyWotsLayer wotsLayerWitnessSig
    have hSigShape :
        ((w.chains.map UnaryWotsChainWitness.sigVal).length == geom.wotsChains &&
         (w.merkle.map MerkleLevelWitness.sibling).length == geom.subtreeHeight) = true := by
      rw [List.length_map, List.length_map, Bool.and_eq_true]; exact hLenChk
    simp only [hSigShape, ↓reduceIte, hExt, hSum, beq_self_eq_true, Option.some.injEq]
    rw [← hEndEq, ← hSpOut, ← hWalkOut, ← hRtEq]

theorem wotsLayerTraceResiduals_complete (geom : AggSigGeometry) (pk : AggValidatorPk)
    (layer treeIdx kpIdx : Nat) (hmsg : Digest5) (lsig : WotsLayerSig) (rt : Digest4)
    (hChainsLe : geom.wotsChains ≤ 128)
    (hTargetBound : geom.targetSum < 3 * geom.wotsChains)
    (hVer : verifyWotsLayer geom pk layer treeIdx kpIdx hmsg lsig = some rt) :
    let w := honestWotsLayerTraceWitness geom pk layer treeIdx kpIdx hmsg lsig
    wotsLayerWitnessSig w = lsig ∧
    w.rootOut = rt ∧
    allZeroGoldilocks (wotsLayerTraceResiduals geom pk layer treeIdx kpIdx hmsg w) = true := by
  intro w
  unfold verifyWotsLayer at hVer
  cases hShape : (lsig.wotsChains.length == geom.wotsChains && lsig.merklePath.length == geom.subtreeHeight)
  · simp [hShape] at hVer
  · simp only [hShape, ↓reduceIte] at hVer
    rcases Bool.and_eq_true_iff.mp hShape with ⟨hChLenB, hMpLenB⟩
    have hChLen : lsig.wotsChains.length = geom.wotsChains := eq_of_beq hChLenB
    have hMpLen : lsig.merklePath.length = geom.subtreeHeight := eq_of_beq hMpLenB
    cases hExt : extractWotsDigitsChecked geom hmsg with
    | none => simp [hExt] at hVer
    | some ds =>
      simp only [hExt] at hVer
      cases hSumB : (listNatSum ds == geom.targetSum)
      · simp [hSumB] at hVer
      · simp only [hSumB, ↓reduceIte, Option.some.injEq] at hVer
        have hSum : listNatSum ds = geom.targetSum := eq_of_beq hSumB
        obtain ⟨hDsLen, hDsLt4⟩ := extractWotsDigitsChecked_spec hChainsLe hExt
        have hWiresMap :
            (hmsg5DigitWires geom (honestHmsg5DecompWitness hmsg)).map Goldilocks.val = ds := by
          unfold extractWotsDigitsChecked at hExt
          cases hChk : checkDigest5Limbs63 hmsg
          · simp [hChk] at hExt
          · simp only [hChk, ↓reduceIte, Option.some.injEq] at hExt
            subst hExt
            unfold hmsg5DigitWires honestHmsg5DecompWitness honestLimb63DecompWitness
            dsimp only
            simp only [List.map_take, List.map_append, map_val_ofNat_extract, take4_extractLimbBase4Digits_31]
        have hDecZero :
            allZeroGoldilocks (hmsg5DecompResiduals geom hmsg (honestHmsg5DecompWitness hmsg)) = true :=
          (hmsg5DecompResiduals_allZero_iff geom hmsg (honestHmsg5DecompWitness hmsg)
            hChainsLe hTargetBound).mpr ⟨rfl, ds, hExt, hSum, hWiresMap⟩
        let digWires := hmsg5DigitWires geom (honestHmsg5DecompWitness hmsg)
        have hDigWiresLen : digWires.length = lsig.wotsChains.length := by
          have h1 : digWires.length = ds.length := by rw [← hWiresMap, List.length_map]
          omega
        have hWiresLt4 : ∀ d ∈ digWires, d.val < 4 := by
          intro d hd
          have hm : d.val ∈ digWires.map Goldilocks.val := List.mem_map_of_mem hd
          rw [hWiresMap] at hm
          exact hDsLt4 d.val hm
        have hSigMap :
            (honestWotsChainsWitness pk.pkSeed layer treeIdx kpIdx digWires lsig.wotsChains).map
              UnaryWotsChainWitness.sigVal = lsig.wotsChains :=
          map_sigOf_buildChainListWitnessPoly
            (fun c (d : Goldilocks) v => honestUnaryWotsChainWitness pk.pkSeed layer treeIdx kpIdx c d.val v)
            UnaryWotsChainWitness.sigVal (fun _ _ _ => rfl) digWires lsig.wotsChains 0 hDigWiresLen
        have hChsLen :
            (honestWotsChainsWitness pk.pkSeed layer treeIdx kpIdx digWires lsig.wotsChains).length =
              geom.wotsChains := by
          unfold honestWotsChainsWitness
          rw [length_buildChainListWitnessPoly _ digWires lsig.wotsChains 0 hDigWiresLen, hChLen]
        have hSibMap :
            ∀ (cur : Digest4),
              (honestMerklePathWitness domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr 1 kpIdx cur lsig.merklePath).map
                MerkleLevelWitness.sibling = lsig.merklePath :=
          fun cur => map_sibOf_buildMerklePathWitnessPoly _ _ _ (fun _ _ _ _ => rfl) lsig.merklePath 1 kpIdx cur
        have hMpWLen :
            ∀ (cur : Digest4),
              (honestMerklePathWitness domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr 1 kpIdx cur lsig.merklePath).length =
                geom.subtreeHeight := by
          intro cur
          unfold honestMerklePathWitness
          rw [length_buildMerklePathWitnessPoly, hMpLen]
        have hSigEq : wotsLayerWitnessSig w = lsig := by
          rcases lsig with ⟨ctr, chs, mp⟩
          unfold wotsLayerWitnessSig
          dsimp only [w, honestWotsLayerTraceWitness]
          simp only [WotsLayerSig.mk.injEq]
          exact ⟨trivial, hSigMap, hSibMap _⟩
        have hChIff := wotsChainsResiduals_allZero_iff pk.pkSeed layer treeIdx kpIdx
          digWires (honestWotsChainsWitness pk.pkSeed layer treeIdx kpIdx digWires lsig.wotsChains) hWiresLt4
        have hChZero :
            allZeroGoldilocks (wotsChainsResiduals pk.pkSeed layer treeIdx kpIdx digWires
              (honestWotsChainsWitness pk.pkSeed layer treeIdx kpIdx digWires lsig.wotsChains)) = true := by
          apply hChIff.1.mpr
          refine ⟨?_, ?_⟩
          · rw [hChsLen, ← hChLen]; exact hDigWiresLen
          · rw [hSigMap]
        have hEndEq :
            (honestWotsChainsWitness pk.pkSeed layer treeIdx kpIdx digWires lsig.wotsChains).map
              UnaryWotsChainWitness.endVal =
            recoverAggWotsEndpoints pk.pkSeed layer treeIdx kpIdx 0 ds lsig.wotsChains := by
          have e0 := hChIff.2 (by rw [hChsLen, ← hChLen]; exact hDigWiresLen) (by rw [hSigMap])
          rw [hWiresMap, hSigMap] at e0
          exact e0
        let eps := (honestWotsChainsWitness pk.pkSeed layer treeIdx kpIdx digWires lsig.wotsChains).map
          UnaryWotsChainWitness.endVal
        let sp := honestSpongeAbsorbWitness (wotsPkInitState pk.pkSeed layer treeIdx kpIdx eps.length) eps
        have hSpIff := wotsPkSpongeResiduals_allZero_iff pk.pkSeed layer treeIdx kpIdx eps sp
        have hSpZero :
            allZeroGoldilocks (spongeAbsorbResiduals (wotsPkInitState pk.pkSeed layer treeIdx kpIdx eps.length) eps sp) = true :=
          hSpIff.1.mpr rfl
        have hSpOut : sp.outDigest =
            compressWotsEndpointsSponge pk.pkSeed layer treeIdx kpIdx
              (recoverAggWotsEndpoints pk.pkSeed layer treeIdx kpIdx 0 ds lsig.wotsChains) := by
          rw [hSpIff.2 rfl]
          exact congrArg _ hEndEq
        let mPath := honestMerklePathWitness domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr 1 kpIdx sp.outDigest lsig.merklePath
        have hMIff := merklePathResiduals_allZero_iff domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr 1 kpIdx sp.outDigest mPath
        have hMZero :
            allZeroGoldilocks (merklePathResiduals domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr 1 kpIdx sp.outDigest mPath).2 = true :=
          hMIff.1.mpr (by rw [hSibMap])
        have hWalkEq :
            (merklePathResiduals domainMerkleNode pk.pkSeed layer treeIdx xmssNodeAddr 1 kpIdx sp.outDigest mPath).1 = rt := by
          rw [hMIff.2 (by rw [hSibMap]), hSibMap, hSpOut, hVer]
        refine ⟨hSigEq, hWalkEq, ?_⟩
        unfold wotsLayerTraceResiduals
        dsimp only [w, honestWotsLayerTraceWitness]
        have hWShape :
            ((honestWotsChainsWitness pk.pkSeed layer treeIdx kpIdx digWires lsig.wotsChains).length == geom.wotsChains &&
             mPath.length == geom.subtreeHeight) = true := by
          rw [hChsLen, hMpWLen]; simp
        simp only [allZeroGoldilocks_append, Bool.and_eq_true, lane4Sub_toList_allZero_iff]
        exact ⟨⟨⟨⟨⟨shapeIte_allZero_of _ (Bool.and_eq_true_iff.mp hWShape), hDecZero⟩, hChZero⟩, hSpZero⟩,
          hMZero⟩, trivial⟩

/-- Single upper-hypertree layer trace node (`HmsgDetTree` + `WotsLayerTraceWitness`). -/
structure UpperLayerTraceNode where
  detHmsg  : HmsgDetTreeTraceWitness
  wotsStep : WotsLayerTraceWitness
  deriving DecidableEq, Repr

private def buildUpperTracePoly {D LS NW : Type}
    (mkNode : Nat → Nat → D → LS → (Nat × D × NW)) :
    List LS → Nat → Nat → D → List NW
  | [], _, _, _ => []
  | lsig :: rest, layer, rem, curRt =>
    let (nextRem, nextRt, nw) := mkNode layer rem curRt lsig
    nw :: buildUpperTracePoly mkNode rest (layer + 1) nextRem nextRt

private def upperTraceResidualsPoly {D NW RES : Type}
    (nodeRes : Nat → Nat → D → NW → (Nat × D × List RES)) :
    List NW → Nat → Nat → D → (D × List RES)
  | [], _, _, curRt => (curRt, [])
  | nw :: rest, layer, rem, curRt =>
    let (nextRem, nextRt, r0) := nodeRes layer rem curRt nw
    let (topRt, restRes) := upperTraceResidualsPoly nodeRes rest (layer + 1) nextRem nextRt
    (topRt, r0 ++ restRes)

private theorem upperTraceResidualsPoly_sound {D LS NW RES : Type}
    (nodeRes : Nat → Nat → D → NW → (Nat × D × List RES))
    (vStep : Nat → Nat → D → LS → Option (Nat × D))
    (sigOf : NW → LS)
    (zeroPred : List RES → Bool)
    (hAppend : ∀ a b, zeroPred (a ++ b) = (zeroPred a && zeroPred b))
    (hNodeSound : ∀ layer rem cur nw,
      zeroPred (nodeRes layer rem cur nw).2.2 = true →
      vStep layer rem cur (sigOf nw) = some ((nodeRes layer rem cur nw).1, (nodeRes layer rem cur nw).2.1)) :
    ∀ (nws : List NW) (layer rem : Nat) (curRt : D),
      zeroPred (upperTraceResidualsPoly nodeRes nws layer rem curRt).2 = true →
      verifyUpperPoly vStep (nws.map sigOf) layer rem curRt =
        some (upperTraceResidualsPoly nodeRes nws layer rem curRt).1
  | [], _, _, _, _ => rfl
  | nw :: rest, layer, rem, curRt, hZ => by
    dsimp only [upperTraceResidualsPoly] at hZ ⊢
    rw [List.map_cons]
    dsimp only [verifyUpperPoly]
    rw [hAppend, Bool.and_eq_true] at hZ
    rw [hNodeSound layer rem curRt nw hZ.1]
    exact upperTraceResidualsPoly_sound nodeRes vStep sigOf zeroPred hAppend hNodeSound
      rest (layer + 1) (nodeRes layer rem curRt nw).1 (nodeRes layer rem curRt nw).2.1 hZ.2

private theorem upperTraceResidualsPoly_complete {D LS NW RES : Type}
    (mkNode : Nat → Nat → D → LS → (Nat × D × NW))
    (nodeRes : Nat → Nat → D → NW → (Nat × D × List RES))
    (vStep : Nat → Nat → D → LS → Option (Nat × D))
    (sigOf : NW → LS)
    (zeroPred : List RES → Bool)
    (hNil : zeroPred [] = true)
    (hAppend : ∀ a b, zeroPred (a ++ b) = (zeroPred a && zeroPred b))
    (hNodeComplete : ∀ layer rem cur lsig nr nrt,
      vStep layer rem cur lsig = some (nr, nrt) →
      let out := mkNode layer rem cur lsig
      out.1 = nr ∧ out.2.1 = nrt ∧ sigOf out.2.2 = lsig ∧
      (nodeRes layer rem cur out.2.2).1 = nr ∧
      (nodeRes layer rem cur out.2.2).2.1 = nrt ∧
      zeroPred (nodeRes layer rem cur out.2.2).2.2 = true) :
    ∀ (ls : List LS) (layer rem : Nat) (curRt topRt : D),
      verifyUpperPoly vStep ls layer rem curRt = some topRt →
      let nws := buildUpperTracePoly mkNode ls layer rem curRt
      nws.map sigOf = ls ∧
      (upperTraceResidualsPoly nodeRes nws layer rem curRt).1 = topRt ∧
      zeroPred (upperTraceResidualsPoly nodeRes nws layer rem curRt).2 = true
  | [], _, _, _, _, hVer => by
    dsimp only [verifyUpperPoly, buildUpperTracePoly, upperTraceResidualsPoly, List.map_nil] at hVer ⊢
    injection hVer with hEq
    exact ⟨rfl, hEq, hNil⟩
  | lsig :: rest, layer, rem, curRt, topRt, hVer => by
    dsimp only [verifyUpperPoly] at hVer
    cases hSt : vStep layer rem curRt lsig with
    | none => simp [hSt] at hVer
    | some pair =>
      rcases pair with ⟨nr, nrt⟩
      simp only [hSt] at hVer
      obtain ⟨hMk1, hMk2, hSig, hRes1, hRes2, hResZ⟩ := hNodeComplete layer rem curRt lsig nr nrt hSt
      obtain ⟨ihMap, ihTop, ihZ⟩ := upperTraceResidualsPoly_complete mkNode nodeRes vStep sigOf
        zeroPred hNil hAppend hNodeComplete rest (layer + 1) nr nrt topRt hVer
      dsimp only [buildUpperTracePoly]
      obtain ⟨m1, m2, mnw, hMkEq⟩ : ∃ m1 m2 mnw, mkNode layer rem curRt lsig = (m1, m2, mnw) := ⟨_, _, _, rfl⟩
      rw [hMkEq] at hMk1 hMk2 hSig hRes1 hRes2 hResZ ⊢
      dsimp only at hMk1 hMk2 hSig hRes1 hRes2 hResZ ⊢
      subst hMk1 hMk2
      dsimp only [List.map_cons, upperTraceResidualsPoly]
      rw [hRes1, hRes2, hAppend, Bool.and_eq_true]
      exact ⟨List.cons_eq_cons.mpr ⟨hSig, ihMap⟩, ihTop, ⟨hResZ, ihZ⟩⟩


def honestUpperLayersTrace (geom : AggSigGeometry) (pk : AggValidatorPk)
    (startLayer remIdx : Nat) (curRt : Digest4) (ls : List WotsLayerSig) : List UpperLayerTraceNode :=
  buildUpperTracePoly
    (fun l rem cur lsig =>
      let kpIdx := rem % (2 ^ geom.subtreeHeight)
      let treeIdx := rem / (2 ^ geom.subtreeHeight)
      let dh := honestHmsgDetTreeTraceWitness pk l treeIdx kpIdx lsig.tswCtr cur
      let wl := honestWotsLayerTraceWitness geom pk l treeIdx kpIdx dh.outMsg lsig
      (treeIdx, wl.rootOut, { detHmsg := dh, wotsStep := wl }))
    ls startLayer remIdx curRt

def upperLayersTraceResiduals (geom : AggSigGeometry) (pk : AggValidatorPk)
    (startLayer remIdx : Nat) (curRt : Digest4) (nws : List UpperLayerTraceNode) :
    (Digest4 × List Goldilocks) :=
  upperTraceResidualsPoly
    (fun l rem cur nw =>
      let kpIdx := rem % (2 ^ geom.subtreeHeight)
      let treeIdx := rem / (2 ^ geom.subtreeHeight)
      let rH := hmsgDetTreeResiduals pk l treeIdx kpIdx nw.wotsStep.tswCtr cur nw.detHmsg
      let rW := wotsLayerTraceResiduals geom pk l treeIdx kpIdx nw.detHmsg.outMsg nw.wotsStep
      (treeIdx, nw.wotsStep.rootOut, rH ++ rW))
    nws startLayer remIdx curRt

theorem upperLayersTraceResiduals_sound (geom : AggSigGeometry) (pk : AggValidatorPk)
    (startLayer remIdx : Nat) (curRt : Digest4) (nws : List UpperLayerTraceNode)
    (hChainsLe : geom.wotsChains ≤ 128)
    (hTargetBound : geom.targetSum < 3 * geom.wotsChains)
    (hZero : allZeroGoldilocks (upperLayersTraceResiduals geom pk startLayer remIdx curRt nws).2 = true) :
    verifyUpperLayers geom pk startLayer remIdx curRt
      (nws.map fun nw => wotsLayerWitnessSig nw.wotsStep) =
      some (upperLayersTraceResiduals geom pk startLayer remIdx curRt nws).1 := by
  unfold upperLayersTraceResiduals at hZero ⊢
  unfold verifyUpperLayers
  refine upperTraceResidualsPoly_sound _ _ (fun (nw : UpperLayerTraceNode) => wotsLayerWitnessSig nw.wotsStep)
    allZeroGoldilocks allZeroGoldilocks_append ?_ nws startLayer remIdx curRt hZero
  intro l rem cur nw hNodeZ
  dsimp only at hNodeZ ⊢
  rw [allZeroGoldilocks_append, Bool.and_eq_true] at hNodeZ
  have hDetIff := hmsgDetTreeResiduals_allZero_iff pk l (rem / 2 ^ geom.subtreeHeight)
    (rem % 2 ^ geom.subtreeHeight) nw.wotsStep.tswCtr cur nw.detHmsg
  have hOutMsg := hDetIff.2 (hDetIff.1.mp hNodeZ.1)
  have hWSound := wotsLayerTraceResiduals_sound geom pk l (rem / 2 ^ geom.subtreeHeight)
    (rem % 2 ^ geom.subtreeHeight) nw.detHmsg.outMsg nw.wotsStep hChainsLe hTargetBound hNodeZ.2
  have hCtr : (wotsLayerWitnessSig nw.wotsStep).tswCtr = nw.wotsStep.tswCtr := rfl
  rw [hCtr, ← hOutMsg, hWSound]

theorem upperLayersTraceResiduals_complete (geom : AggSigGeometry) (pk : AggValidatorPk)
    (startLayer remIdx : Nat) (curRt topRt : Digest4) (ls : List WotsLayerSig)
    (hChainsLe : geom.wotsChains ≤ 128)
    (hTargetBound : geom.targetSum < 3 * geom.wotsChains)
    (hVer : verifyUpperLayers geom pk startLayer remIdx curRt ls = some topRt) :
    let nws := honestUpperLayersTrace geom pk startLayer remIdx curRt ls
    (nws.map fun nw => wotsLayerWitnessSig nw.wotsStep) = ls ∧
    (upperLayersTraceResiduals geom pk startLayer remIdx curRt nws).1 = topRt ∧
    allZeroGoldilocks (upperLayersTraceResiduals geom pk startLayer remIdx curRt nws).2 = true := by
  unfold verifyUpperLayers at hVer
  unfold honestUpperLayersTrace upperLayersTraceResiduals
  refine upperTraceResidualsPoly_complete _ _ _ (fun (nw : UpperLayerTraceNode) => wotsLayerWitnessSig nw.wotsStep)
    allZeroGoldilocks rfl allZeroGoldilocks_append ?_ ls startLayer remIdx curRt topRt hVer
  intro l rem cur lsig nr nrt hSt
  dsimp only at hSt ⊢
  let kpIdx := rem % (2 ^ geom.subtreeHeight)
  let treeIdx := rem / (2 ^ geom.subtreeHeight)
  let hmsg := computeHmsgDetTree pk l treeIdx kpIdx lsig.tswCtr cur
  change (match verifyWotsLayer geom pk l treeIdx kpIdx hmsg lsig with
          | none => none | some nextRoot => some (treeIdx, nextRoot)) = some (nr, nrt) at hSt
  cases hW : verifyWotsLayer geom pk l treeIdx kpIdx hmsg lsig with
  | none => rw [hW] at hSt; cases hSt
  | some rtOut =>
    rw [hW] at hSt
    simp only [Option.some.injEq, Prod.mk.injEq] at hSt
    rcases hSt with ⟨hNr, hNrt⟩
    subst hNr hNrt
    let dh := honestHmsgDetTreeTraceWitness pk l treeIdx kpIdx lsig.tswCtr cur
    have hDetIff := hmsgDetTreeResiduals_allZero_iff pk l treeIdx kpIdx lsig.tswCtr cur dh
    have hDhOut : dh.outMsg = hmsg := hDetIff.2 rfl
    have hDhZero : allZeroGoldilocks (hmsgDetTreeResiduals pk l treeIdx kpIdx lsig.tswCtr cur dh) = true :=
      hDetIff.1.mpr rfl
    have hWSub : verifyWotsLayer geom pk l treeIdx kpIdx dh.outMsg lsig = some rtOut := by
      rw [hDhOut]; exact hW
    obtain ⟨hWSig, hWRt, hWZero⟩ := wotsLayerTraceResiduals_complete geom pk l treeIdx kpIdx
      dh.outMsg lsig rtOut hChainsLe hTargetBound hWSub
    have hCtrEq : (honestWotsLayerTraceWitness geom pk l treeIdx kpIdx dh.outMsg lsig).tswCtr = lsig.tswCtr := rfl
    refine ⟨rfl, hWRt, hWSig, rfl, hWRt, ?_⟩
    rw [allZeroGoldilocks_append, Bool.and_eq_true, hCtrEq]
    exact ⟨hDhZero, hWZero⟩


/-! ### FORS Opening Sub-Circuit & 7-Limb `< 2^63` Stateless XOF Sub-Circuit -/

private theorem forsLeafHash_eq_perm (geom : AggSigGeometry) (pkSeed val : Digest4)
    (leafGlobalIdx j idx : Nat) :
    forsLeafHash geom pkSeed val leafGlobalIdx j idx =
      lane4Add (poseidon2Perm12
        ⟨val, pkSeed, forsLeafTweak4 domainForsLeaf geom leafGlobalIdx j idx⟩).b0 val := by
  unfold forsLeafHash poseidon2Compress12FF
  rfl

structure ForsOpeningTraceWitness where
  secretVal : Digest4
  leafPerm  : Poseidon2PermWitness
  merkle    : List MerkleLevelWitness
  treeRoot  : Digest4
  deriving DecidableEq, Repr

def forsOpeningWitnessSig (w : ForsOpeningTraceWitness) : AggForsTreeOpening :=
  { secretVal := w.secretVal
    authPath  := w.merkle.map MerkleLevelWitness.sibling }

def honestForsOpeningTraceWitness (geom : AggSigGeometry) (pkSeed : Digest4) (leafGlobalIdx t idx : Nat)
    (op : AggForsTreeOpening) : ForsOpeningTraceWitness :=
  let lp := honestPoseidon2PermWitness ⟨op.secretVal, pkSeed, forsLeafTweak4 domainForsLeaf geom leafGlobalIdx t idx⟩
  let leaf := lane4Add lp.output.b0 op.secretVal
  let mp := honestMerklePathWitness domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
      (forsTreeNodeAddr geom leafGlobalIdx t) 1 idx leaf op.authPath
  let rt := (merklePathResiduals domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
      (forsTreeNodeAddr geom leafGlobalIdx t) 1 idx leaf mp).1
  { secretVal := op.secretVal, leafPerm := lp, merkle := mp, treeRoot := rt }

def forsOpeningResiduals (geom : AggSigGeometry) (pkSeed : Digest4)
    (leafGlobalIdx t idx : Nat) (w : ForsOpeningTraceWitness) : List Goldilocks :=
  let shapeRes :=
    if decide (idx < 2 ^ geom.forsHeight) && (w.merkle.length == geom.forsHeight) then []
    else [Goldilocks.one]
  let leaf := lane4Add w.leafPerm.output.b0 w.secretVal
  let (walkedRt, mRes) := merklePathResiduals domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
      (forsTreeNodeAddr geom leafGlobalIdx t) 1 idx leaf w.merkle
  shapeRes ++
  permWithInputResiduals ⟨w.secretVal, pkSeed, forsLeafTweak4 domainForsLeaf geom leafGlobalIdx t idx⟩ w.leafPerm ++
  mRes ++
  (lane4Sub w.treeRoot walkedRt).toList

theorem forsOpeningResiduals_sound (geom : AggSigGeometry) (pkSeed : Digest4)
    (leafGlobalIdx t idx : Nat) (w : ForsOpeningTraceWitness)
    (hZero : allZeroGoldilocks (forsOpeningResiduals geom pkSeed leafGlobalIdx t idx w) = true) :
    verifySingleForsOpening geom pkSeed leafGlobalIdx t idx (forsOpeningWitnessSig w) = some w.treeRoot := by
  unfold forsOpeningResiduals at hZero
  dsimp only at hZero
  simp only [allZeroGoldilocks_append, Bool.and_eq_true, permWithInputResiduals_allZero_iff,
    lane4Sub_toList_allZero_iff] at hZero
  rcases hZero with ⟨⟨⟨hShape, hLp⟩, hM⟩, hRtEq⟩
  have hChk := shapeIte_allZero _ hShape
  · have hPermOut : (honestPoseidon2PermWitness ⟨w.secretVal, pkSeed, forsLeafTweak4 domainForsLeaf geom leafGlobalIdx t idx⟩).output =
        poseidon2Perm12 ⟨w.secretVal, pkSeed, forsLeafTweak4 domainForsLeaf geom leafGlobalIdx t idx⟩ := by
      unfold poseidon2Perm12 honestPoseidon2PermWitness; rfl
    have hLeafEq : lane4Add w.leafPerm.output.b0 w.secretVal =
        forsLeafHash geom pkSeed w.secretVal leafGlobalIdx t idx := by
      rw [hLp, hPermOut, forsLeafHash_eq_perm]
    have hMIff := merklePathResiduals_allZero_iff domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
      (forsTreeNodeAddr geom leafGlobalIdx t) 1 idx
      (lane4Add w.leafPerm.output.b0 w.secretVal) w.merkle
    have hWalkEq := hMIff.2 (hMIff.1.mp hM)
    unfold verifySingleForsOpening forsOpeningWitnessSig
    rcases hChk with ⟨hIdxDec, hMpLenB⟩
    have hIdxLt : idx < 2 ^ geom.forsHeight := of_decide_eq_true hIdxDec
    simp only [hIdxLt, decide_true, List.length_map, hMpLenB, Bool.true_and, ↓reduceIte, Option.some.injEq]
    rw [hRtEq, hWalkEq, hLeafEq]

theorem forsOpeningResiduals_complete (geom : AggSigGeometry) (pkSeed : Digest4)
    (leafGlobalIdx t idx : Nat) (op : AggForsTreeOpening) (rt : Digest4)
    (hVer : verifySingleForsOpening geom pkSeed leafGlobalIdx t idx op = some rt) :
    let w := honestForsOpeningTraceWitness geom pkSeed leafGlobalIdx t idx op
    forsOpeningWitnessSig w = op ∧
    w.treeRoot = rt ∧
    allZeroGoldilocks (forsOpeningResiduals geom pkSeed leafGlobalIdx t idx w) = true := by
  intro w
  unfold verifySingleForsOpening at hVer
  cases hChk : (decide (idx < 2 ^ geom.forsHeight) && (op.authPath.length == geom.forsHeight))
  · simp [hChk] at hVer
  · simp only [hChk, ↓reduceIte, Option.some.injEq] at hVer
    rcases Bool.and_eq_true_iff.mp hChk with ⟨hIdxDec, hMpLenB⟩
    have hMpLen : op.authPath.length = geom.forsHeight := eq_of_beq hMpLenB
    have hPermOut : (honestPoseidon2PermWitness ⟨op.secretVal, pkSeed, forsLeafTweak4 domainForsLeaf geom leafGlobalIdx t idx⟩).output =
        poseidon2Perm12 ⟨op.secretVal, pkSeed, forsLeafTweak4 domainForsLeaf geom leafGlobalIdx t idx⟩ := by
      unfold poseidon2Perm12 honestPoseidon2PermWitness; rfl
    let lp := honestPoseidon2PermWitness ⟨op.secretVal, pkSeed, forsLeafTweak4 domainForsLeaf geom leafGlobalIdx t idx⟩
    let leaf := lane4Add lp.output.b0 op.secretVal
    have hLeafEq : leaf = forsLeafHash geom pkSeed op.secretVal leafGlobalIdx t idx := by
      dsimp only [leaf, lp]; rw [hPermOut, forsLeafHash_eq_perm]
    let mp := honestMerklePathWitness domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
      (forsTreeNodeAddr geom leafGlobalIdx t) 1 idx leaf op.authPath
    have hSibMap : mp.map MerkleLevelWitness.sibling = op.authPath :=
      map_sibOf_buildMerklePathWitnessPoly _ _ _ (fun _ _ _ _ => rfl) op.authPath 1 idx leaf
    have hMpWLen : mp.length = geom.forsHeight := by
      dsimp only [mp]; unfold honestMerklePathWitness
      rw [length_buildMerklePathWitnessPoly, hMpLen]
    have hMIff := merklePathResiduals_allZero_iff domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
      (forsTreeNodeAddr geom leafGlobalIdx t) 1 idx leaf mp
    have hMZero : allZeroGoldilocks (merklePathResiduals domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
      (forsTreeNodeAddr geom leafGlobalIdx t) 1 idx leaf mp).2 = true :=
      hMIff.1.mpr (by rw [hSibMap])
    have hWalkEq : (merklePathResiduals domainForsNode pkSeed 0 (forsHyperTreeIdx geom leafGlobalIdx)
      (forsTreeNodeAddr geom leafGlobalIdx t) 1 idx leaf mp).1 = rt := by
      rw [hMIff.2 (by rw [hSibMap]), hSibMap, hLeafEq, hVer]
    have hSigEq : forsOpeningWitnessSig w = op := by
      rcases op with ⟨sv, ap⟩
      unfold forsOpeningWitnessSig
      dsimp only [w, honestForsOpeningTraceWitness]
      simp only [AggForsTreeOpening.mk.injEq]
      exact ⟨trivial, hSibMap⟩
    refine ⟨hSigEq, hWalkEq, ?_⟩
    unfold forsOpeningResiduals
    dsimp only [w, honestForsOpeningTraceWitness]
    have hWChk : (decide (idx < 2 ^ geom.forsHeight) && (mp.length == geom.forsHeight)) = true := by
      rw [hIdxDec, hMpWLen]; simp
    simp only [allZeroGoldilocks_append, Bool.and_eq_true,
      permWithInputResiduals_allZero_iff, lane4Sub_toList_allZero_iff]
    exact ⟨⟨⟨shapeIte_allZero_of _ (Bool.and_eq_true_iff.mp hWChk), trivial⟩, hMZero⟩, trivial⟩

private def buildForsTracePoly {OP FW : Type}
    (mkF : Nat → Nat → OP → FW) :
    List Nat → List OP → Nat → List FW
  | [], _, _ => []
  | _, [], _ => []
  | idx :: idxs, op :: ops, t => mkF t idx op :: buildForsTracePoly mkF idxs ops (t + 1)

private def forsTraceResidualsPoly {FW RES : Type}
    (fRes : Nat → Nat → FW → List RES) (badRes : List RES) :
    List Nat → List FW → Nat → List RES
  | [], [], _ => []
  | idx :: idxs, w :: ws, t => fRes t idx w ++ forsTraceResidualsPoly fRes badRes idxs ws (t + 1)
  | [], _ :: _, _ => badRes
  | _ :: _, [], _ => badRes

private theorem forsTraceResidualsPoly_sound {D OP FW RES : Type}
    (fRes : Nat → Nat → FW → List RES)
    (vStep : Nat → Nat → OP → Option D)
    (sigOf : FW → OP)
    (rtOf : FW → D)
    (badRes : List RES)
    (zeroPred : List RES → Bool)
    (hBad : zeroPred badRes = false)
    (hAppend : ∀ a b, zeroPred (a ++ b) = (zeroPred a && zeroPred b))
    (hStepSound : ∀ t idx w, zeroPred (fRes t idx w) = true → vStep t idx (sigOf w) = some (rtOf w)) :
    ∀ (idxs : List Nat) (ws : List FW) (t : Nat),
      zeroPred (forsTraceResidualsPoly fRes badRes idxs ws t) = true →
      idxs.length = ws.length ∧
      verifyForsPoly vStep idxs (ws.map sigOf) t = some (ws.map rtOf)
  | [], [], _, _ => ⟨rfl, rfl⟩
  | [], _ :: _, _, hZ => by dsimp only [forsTraceResidualsPoly] at hZ; rw [hBad] at hZ; cases hZ
  | _ :: _, [], _, hZ => by dsimp only [forsTraceResidualsPoly] at hZ; rw [hBad] at hZ; cases hZ
  | idx :: idxs, w :: ws, t, hZ => by
    dsimp only [forsTraceResidualsPoly] at hZ ⊢
    rw [List.map_cons, List.map_cons]
    dsimp only [verifyForsPoly]
    rw [hAppend, Bool.and_eq_true] at hZ
    rw [hStepSound t idx w hZ.1]
    obtain ⟨hLen, hRest⟩ := forsTraceResidualsPoly_sound fRes vStep sigOf rtOf badRes zeroPred
      hBad hAppend hStepSound idxs ws (t + 1) hZ.2
    rw [hRest]
    exact ⟨congrArg Nat.succ hLen, rfl⟩

private theorem forsTraceResidualsPoly_complete {D OP FW RES : Type}
    (mkF : Nat → Nat → OP → FW)
    (fRes : Nat → Nat → FW → List RES)
    (vStep : Nat → Nat → OP → Option D)
    (sigOf : FW → OP)
    (rtOf : FW → D)
    (badRes : List RES)
    (zeroPred : List RES → Bool)
    (hNil : zeroPred [] = true)
    (hAppend : ∀ a b, zeroPred (a ++ b) = (zeroPred a && zeroPred b))
    (hStepComplete : ∀ t idx op rt,
      vStep t idx op = some rt →
      sigOf (mkF t idx op) = op ∧
      rtOf (mkF t idx op) = rt ∧
      zeroPred (fRes t idx (mkF t idx op)) = true) :
    ∀ (idxs : List Nat) (ops : List OP) (t : Nat) (rts : List D),
      verifyForsPoly vStep idxs ops t = some rts →
      let ws := buildForsTracePoly mkF idxs ops t
      ws.map sigOf = ops ∧
      ws.map rtOf = rts ∧
      zeroPred (forsTraceResidualsPoly fRes badRes idxs ws t) = true
  | [], [], _, _, hVer => by
    dsimp only [verifyForsPoly, buildForsTracePoly, forsTraceResidualsPoly, List.map_nil] at hVer ⊢
    injection hVer with hEq
    exact ⟨rfl, hEq, hNil⟩
  | [], _ :: _, _, _, hVer => by dsimp only [verifyForsPoly] at hVer; cases hVer
  | _ :: _, [], _, _, hVer => by dsimp only [verifyForsPoly] at hVer; cases hVer
  | idx :: idxs, op :: ops, t, rts, hVer => by
    dsimp only [verifyForsPoly] at hVer
    cases hSt : vStep t idx op with
    | none => simp [hSt] at hVer
    | some rt0 =>
      simp only [hSt] at hVer
      cases hRest : verifyForsPoly vStep idxs ops (t + 1) with
      | none => simp [hRest] at hVer
      | some restRts =>
        simp only [hRest, Option.some.injEq] at hVer
        subst hVer
        obtain ⟨hS0, hR0, hZ0⟩ := hStepComplete t idx op rt0 hSt
        obtain ⟨ihS, ihR, ihZ⟩ := forsTraceResidualsPoly_complete mkF fRes vStep sigOf rtOf
          badRes zeroPred hNil hAppend hStepComplete idxs ops (t + 1) restRts hRest
        dsimp only [buildForsTracePoly, List.map_cons, forsTraceResidualsPoly]
        rw [hAppend, Bool.and_eq_true]
        exact ⟨List.cons_eq_cons.mpr ⟨hS0, ihS⟩, List.cons_eq_cons.mpr ⟨hR0, ihR⟩, ⟨hZ0, ihZ⟩⟩

/-- Full FORS multi-tree opening + `compressForsRootsSponge` sub-circuit witness. -/
structure ForsAndRecoverTraceWitness where
  openings    : List ForsOpeningTraceWitness
  rootsSponge : SpongeAbsorbWitness
  forsPkOut   : Digest4
  deriving DecidableEq, Repr

def honestForsAndRecoverTraceWitness (geom : AggSigGeometry) (pkSeed : Digest4) (leafGlobalIdx : Nat)
    (indices : List Nat) (ops : List AggForsTreeOpening) : ForsAndRecoverTraceWitness :=
  let fws := buildForsTracePoly (honestForsOpeningTraceWitness geom pkSeed leafGlobalIdx) indices ops 0
  let rts := fws.map ForsOpeningTraceWitness.treeRoot
  let sp := honestSpongeAbsorbWitness (forsRootsInitState geom pkSeed leafGlobalIdx) rts
  { openings := fws, rootsSponge := sp, forsPkOut := sp.outDigest }

def forsAndRecoverTraceResiduals (geom : AggSigGeometry) (pkSeed : Digest4) (leafGlobalIdx : Nat)
    (indices : List Nat) (w : ForsAndRecoverTraceWitness) : List Goldilocks :=
  let shapeRes :=
    if indices.length == geom.forsTrees && w.openings.length == geom.forsTrees then []
    else [Goldilocks.one]
  let rts := w.openings.map ForsOpeningTraceWitness.treeRoot
  shapeRes ++
  forsTraceResidualsPoly (forsOpeningResiduals geom pkSeed leafGlobalIdx) [Goldilocks.one] indices w.openings 0 ++
  spongeAbsorbResiduals (forsRootsInitState geom pkSeed leafGlobalIdx) rts w.rootsSponge ++
  (lane4Sub w.forsPkOut w.rootsSponge.outDigest).toList

theorem forsAndRecoverTraceResiduals_sound (geom : AggSigGeometry) (pkSeed : Digest4) (leafGlobalIdx : Nat)
    (indices : List Nat) (w : ForsAndRecoverTraceWitness)
    (hZero : allZeroGoldilocks (forsAndRecoverTraceResiduals geom pkSeed leafGlobalIdx indices w) = true) :
    verifyAndRecoverForsPk geom pkSeed leafGlobalIdx indices (w.openings.map forsOpeningWitnessSig) =
      some w.forsPkOut := by
  unfold forsAndRecoverTraceResiduals at hZero
  dsimp only at hZero
  simp only [allZeroGoldilocks_append, Bool.and_eq_true, lane4Sub_toList_allZero_iff] at hZero
  rcases hZero with ⟨⟨⟨hShape, hF⟩, hSp⟩, hOutEq⟩
  have hLenChk := shapeIte_allZero _ hShape
  · obtain ⟨_, hVerF⟩ := forsTraceResidualsPoly_sound
      (forsOpeningResiduals geom pkSeed leafGlobalIdx)
      (verifySingleForsOpening geom pkSeed leafGlobalIdx)
      forsOpeningWitnessSig ForsOpeningTraceWitness.treeRoot
      [Goldilocks.one] allZeroGoldilocks (by decide) allZeroGoldilocks_append
      (forsOpeningResiduals_sound geom pkSeed leafGlobalIdx) indices w.openings 0 hF
    have hSpIff := forsRootsSpongeResiduals_allZero_iff geom pkSeed leafGlobalIdx
      (w.openings.map ForsOpeningTraceWitness.treeRoot) w.rootsSponge
    have hSpOut := hSpIff.2 (hSpIff.1.mp hSp)
    unfold verifyAndRecoverForsPk verifyForsTreesAux
    have hMapLen :
        (indices.length == geom.forsTrees && (w.openings.map forsOpeningWitnessSig).length == geom.forsTrees) = true := by
      rw [List.length_map, Bool.and_eq_true]; exact hLenChk
    simp only [hMapLen, ↓reduceIte, hVerF, Option.some.injEq]
    rw [hOutEq, hSpOut]

theorem forsAndRecoverTraceResiduals_complete (geom : AggSigGeometry) (pkSeed : Digest4) (leafGlobalIdx : Nat)
    (indices : List Nat) (ops : List AggForsTreeOpening) (fpk : Digest4)
    (hVer : verifyAndRecoverForsPk geom pkSeed leafGlobalIdx indices ops = some fpk) :
    let w := honestForsAndRecoverTraceWitness geom pkSeed leafGlobalIdx indices ops
    w.openings.map forsOpeningWitnessSig = ops ∧
    w.forsPkOut = fpk ∧
    allZeroGoldilocks (forsAndRecoverTraceResiduals geom pkSeed leafGlobalIdx indices w) = true := by
  intro w
  unfold verifyAndRecoverForsPk verifyForsTreesAux at hVer
  cases hLenChk : (indices.length == geom.forsTrees && ops.length == geom.forsTrees)
  · simp [hLenChk] at hVer
  · simp only [hLenChk, ↓reduceIte] at hVer
    cases hFT : verifyForsPoly (verifySingleForsOpening geom pkSeed leafGlobalIdx) indices ops 0 with
    | none => simp [hFT] at hVer
    | some rts =>
      simp only [hFT, Option.some.injEq] at hVer
      obtain ⟨hMapS, hMapR, hFZ⟩ := forsTraceResidualsPoly_complete
        (honestForsOpeningTraceWitness geom pkSeed leafGlobalIdx)
        (forsOpeningResiduals geom pkSeed leafGlobalIdx)
        (verifySingleForsOpening geom pkSeed leafGlobalIdx)
        forsOpeningWitnessSig ForsOpeningTraceWitness.treeRoot
        [Goldilocks.one] allZeroGoldilocks rfl allZeroGoldilocks_append
        (forsOpeningResiduals_complete geom pkSeed leafGlobalIdx) indices ops 0 rts hFT
      let fws := buildForsTracePoly (honestForsOpeningTraceWitness geom pkSeed leafGlobalIdx) indices ops 0
      have hFwsLen : fws.length = ops.length := by
        have h1 : (fws.map forsOpeningWitnessSig).length = ops.length := by rw [hMapS]
        simpa only [List.length_map] using h1
      let rtsW := fws.map ForsOpeningTraceWitness.treeRoot
      let sp := honestSpongeAbsorbWitness (forsRootsInitState geom pkSeed leafGlobalIdx) rtsW
      have hSpIff := forsRootsSpongeResiduals_allZero_iff geom pkSeed leafGlobalIdx rtsW sp
      have hSpZ : allZeroGoldilocks (spongeAbsorbResiduals
          (forsRootsInitState geom pkSeed leafGlobalIdx) rtsW sp) = true := hSpIff.1.mpr rfl
      have hSpOut : sp.outDigest = fpk := by
        rw [hSpIff.2 rfl]
        have hRtsEq : rtsW = rts := hMapR
        rw [hRtsEq, hVer]
      refine ⟨hMapS, hSpOut, ?_⟩
      unfold forsAndRecoverTraceResiduals
      dsimp only [w, honestForsAndRecoverTraceWitness]
      have hWLenChk : (indices.length == geom.forsTrees && fws.length == geom.forsTrees) = true := by
        rw [hFwsLen]; exact hLenChk
      simp only [allZeroGoldilocks_append, Bool.and_eq_true, lane4Sub_toList_allZero_iff]
      exact ⟨⟨⟨shapeIte_allZero_of _ (Bool.and_eq_true_iff.mp hWLenChk), hFZ⟩, hSpZ⟩, trivial⟩

/-- 2-block stateless XOF + 7-limb `< 2^63` quartic/MSB algebraic witness (`sig.rs:494`). -/
structure StatelessXofTraceWitness where
  perm0 : Poseidon2PermWitness
  perm1 : Poseidon2PermWitness
  lim0  : Limb63DecompWitness
  lim1  : Limb63DecompWitness
  lim2  : Limb63DecompWitness
  lim3  : Limb63DecompWitness
  lim4  : Limb63DecompWitness
  lim5  : Limb63DecompWitness
  lim6  : Limb63DecompWitness
  deriving DecidableEq, Repr

private def statelessXofIn0 (pk : AggValidatorPk) (mu : Digest5) : Poseidon2State12 :=
  ⟨pk.pkSeed, pk.pkRoot, ⟨domainHMsgStateless, mu.limb4, Goldilocks.zero, poseidon2IvTag⟩⟩

private def statelessXofIn1 (st0 : Poseidon2State12) (rRand : Digest4) (mu : Digest5) : Poseidon2State12 :=
  let muLow : Digest4 := ⟨mu.limb0, mu.limb1, mu.limb2, mu.limb3⟩
  ⟨lane4Add st0.b0 rRand, lane4Add st0.b1 muLow, st0.b2⟩

private theorem statelessXofSpongeState_eq_states (pk : AggValidatorPk) (rRand : Digest4) (mu : Digest5) :
    statelessXofSpongeState pk rRand mu =
      poseidon2Perm12 (statelessXofIn1 (poseidon2Perm12 (statelessXofIn0 pk mu)) rRand mu) := by
  unfold statelessXofSpongeState statelessXofIn0 statelessXofIn1
  rfl

attribute [local irreducible] statelessXofIn0 statelessXofIn1

def honestStatelessXofTraceWitness (pk : AggValidatorPk) (rRand : Digest4) (mu : Digest5) :
    StatelessXofTraceWitness :=
  let p0 := honestPoseidon2PermWitness (statelessXofIn0 pk mu)
  let p1 := honestPoseidon2PermWitness (statelessXofIn1 p0.output rRand mu)
  let st := p1.output
  { perm0 := p0, perm1 := p1
    lim0 := honestLimb63DecompWitness st.b0.x0
    lim1 := honestLimb63DecompWitness st.b0.x1
    lim2 := honestLimb63DecompWitness st.b0.x2
    lim3 := honestLimb63DecompWitness st.b0.x3
    lim4 := honestLimb63DecompWitness st.b1.x0
    lim5 := honestLimb63DecompWitness st.b1.x1
    lim6 := honestLimb63DecompWitness st.b1.x2 }

def extractStatelessXofPair (geom : AggSigGeometry) (w : StatelessXofTraceWitness) : (Nat × List Nat) :=
  let st1 := w.perm1.output
  let totalTreeBits := geom.numLayers * geom.subtreeHeight
  let rawLeaf := (st1.b1.x1.val % (2 ^ 32)) + ((st1.b1.x2.val % (2 ^ 32)) * (2 ^ 32))
  let leafGlobalIdx := rawLeaf % (2 ^ totalTreeBits)
  let treeMod := 2 ^ geom.forsHeight
  let indices := (List.range geom.forsTrees).map fun t =>
    let limbVal := match t / 7 with
      | 0 => st1.b0.x0.val
      | 1 => st1.b0.x1.val
      | 2 => st1.b0.x2.val
      | 3 => st1.b0.x3.val
      | _ => st1.b1.x0.val
    (limbVal / (256 ^ (t % 7))) % treeMod
  (leafGlobalIdx, indices)

def statelessXofTraceResiduals (pk : AggValidatorPk) (rRand : Digest4) (mu : Digest5)
    (w : StatelessXofTraceWitness) : List Goldilocks :=
  let st := w.perm1.output
  permWithInputResiduals (statelessXofIn0 pk mu) w.perm0 ++
  permWithInputResiduals (statelessXofIn1 w.perm0.output rRand mu) w.perm1 ++
  limb63DecompResiduals st.b0.x0 w.lim0 ++
  limb63DecompResiduals st.b0.x1 w.lim1 ++
  limb63DecompResiduals st.b0.x2 w.lim2 ++
  limb63DecompResiduals st.b0.x3 w.lim3 ++
  limb63DecompResiduals st.b1.x0 w.lim4 ++
  limb63DecompResiduals st.b1.x1 w.lim5 ++
  limb63DecompResiduals st.b1.x2 w.lim6

theorem statelessXofTraceResiduals_sound (geom : AggSigGeometry) (pk : AggValidatorPk)
    (rRand : Digest4) (mu : Digest5) (w : StatelessXofTraceWitness)
    (hZero : allZeroGoldilocks (statelessXofTraceResiduals pk rRand mu w) = true) :
    deriveStatelessLeafAndForsChecked geom pk rRand mu = some (extractStatelessXofPair geom w) := by
  have hPermOut : ∀ st : Poseidon2State12, (honestPoseidon2PermWitness st).output = poseidon2Perm12 st :=
    fun st => by unfold poseidon2Perm12 honestPoseidon2PermWitness; rfl
  unfold statelessXofTraceResiduals at hZero
  simp only [allZeroGoldilocks_append, Bool.and_eq_true, permWithInputResiduals_allZero_iff,
    limb63DecompResiduals_allZero_iff] at hZero
  rcases hZero with ⟨⟨⟨⟨⟨⟨⟨⟨hP0, hP1⟩, ⟨c0, _⟩⟩, ⟨c1, _⟩⟩, ⟨c2, _⟩⟩, ⟨c3, _⟩⟩, ⟨c4, _⟩⟩, ⟨c5, _⟩⟩, ⟨c6, _⟩⟩
  have hStEq : w.perm1.output = statelessXofSpongeState pk rRand mu := by
    rw [hP1, hP0, hPermOut, hPermOut, statelessXofSpongeState_eq_states]
  unfold deriveStatelessLeafAndForsChecked extractStatelessXofPair
  rw [← hStEq]
  have hAll63 :
      ([w.perm1.output.b0.x0, w.perm1.output.b0.x1, w.perm1.output.b0.x2, w.perm1.output.b0.x3,
        w.perm1.output.b1.x0, w.perm1.output.b1.x1, w.perm1.output.b1.x2].all
        (fun l => decide (l.val < 2 ^ 63))) = true := by
    simp [c0, c1, c2, c3, c4, c5, c6]
  simp only [hAll63, ↓reduceIte]

theorem statelessXofTraceResiduals_complete (geom : AggSigGeometry) (pk : AggValidatorPk)
    (rRand : Digest4) (mu : Digest5) (leafIdx : Nat) (indices : List Nat)
    (hXof : deriveStatelessLeafAndForsChecked geom pk rRand mu = some (leafIdx, indices)) :
    let w := honestStatelessXofTraceWitness pk rRand mu
    extractStatelessXofPair geom w = (leafIdx, indices) ∧
    allZeroGoldilocks (statelessXofTraceResiduals pk rRand mu w) = true := by
  intro w
  have hPermOut : ∀ st : Poseidon2State12, (honestPoseidon2PermWitness st).output = poseidon2Perm12 st :=
    fun st => by unfold poseidon2Perm12 honestPoseidon2PermWitness; rfl
  have hStEq : w.perm1.output = statelessXofSpongeState pk rRand mu := by
    dsimp only [w, honestStatelessXofTraceWitness]
    rw [hPermOut, hPermOut, statelessXofSpongeState_eq_states]
  unfold deriveStatelessLeafAndForsChecked at hXof
  rw [← hStEq] at hXof
  cases hAll63 : ([w.perm1.output.b0.x0, w.perm1.output.b0.x1, w.perm1.output.b0.x2, w.perm1.output.b0.x3,
                   w.perm1.output.b1.x0, w.perm1.output.b1.x1, w.perm1.output.b1.x2].all
                   (fun l => decide (l.val < 2 ^ 63)))
  · simp [hAll63] at hXof
  · simp only [hAll63, ↓reduceIte, Option.some.injEq] at hXof
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at hAll63
    rcases hAll63 with ⟨c0, c1, c2, c3, c4, c5, c6⟩
    refine ⟨hXof, ?_⟩
    unfold statelessXofTraceResiduals
    dsimp only [w, honestStatelessXofTraceWitness]
    simp only [allZeroGoldilocks_append, Bool.and_eq_true, permWithInputResiduals_allZero_iff,
      limb63DecompResiduals_allZero_iff]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨trivial, trivial⟩, ⟨c0, trivial⟩⟩, ⟨c1, trivial⟩⟩, ⟨c2, trivial⟩⟩, ⟨c3, trivial⟩⟩, ⟨c4, trivial⟩⟩, ⟨c5, trivial⟩⟩, ⟨c6, trivial⟩⟩



/-! ### Full `AggSignerTraceWitness`, `RowGate7` AST, `AggExecutionTrace`, & AIR Constraint Exactness -/

/-- Non-zero field encoding of `AggSigProfile` (`1` for `XmssPoseidon2`, `2` for `CorduroyPoseidon2`). -/
def profileFieldTag : AggSigProfile → Goldilocks
  | .xmssPoseidon2 => Goldilocks.one
  | .corduroyPoseidon2  => Goldilocks.ofNat 2

theorem profileFieldTag_ne_zero (p : AggSigProfile) : profileFieldTag p ≠ Goldilocks.zero := by
  cases p <;> decide

theorem profileFieldTag_injective {p1 p2 : AggSigProfile}
    (h : profileFieldTag p1 = profileFieldTag p2) : p1 = p2 := by
  cases p1 <;> cases p2 <;> first | rfl | (exfalso; revert h; decide)

inductive AggSignerModeTrace where
  | stateful (leafIdx : Nat) (hmsg0 : HmsgStatefulTraceWitness)
  | stateless (xof : StatelessXofTraceWitness)
              (fors : ForsAndRecoverTraceWitness)
              (hmsg0 : HmsgDetTreeTraceWitness)
  deriving DecidableEq, Repr

structure AggSignerTraceWitness where
  profile    : AggSigProfile
  rRand      : Digest4
  modeTrace  : AggSignerModeTrace
  layer0     : WotsLayerTraceWitness
  upperNodes : List UpperLayerTraceNode
  deriving DecidableEq, Repr

def extractSignerWitnessSig (w : AggSignerTraceWitness) : AggNativeSignature :=
  let (leafIdx, forsOps) := match w.modeTrace with
    | .stateful idx _ => (idx, [])
    | .stateless _ fors _ => (0, fors.openings.map forsOpeningWitnessSig)
  { profile         := w.profile
    rRand           := w.rRand
    statefulLeafIdx := leafIdx
    forsOpenings    := forsOps
    layers          := wotsLayerWitnessSig w.layer0 ::
                       w.upperNodes.map (fun nw => wotsLayerWitnessSig nw.wotsStep) }

def signerTraceResiduals (geom : AggSigGeometry) (pk : AggValidatorPk) (msg : List UInt8)
    (w : AggSignerTraceWitness) : List Goldilocks :=
  let hdrOk := geom.wellFormed && (pk.profile == geom.profile) &&
               (w.profile == geom.profile) && (w.upperNodes.length + 1 == geom.numLayers)
  let hdrRes := if hdrOk then [] else [Goldilocks.one]
  let mu := computeMessageMu pk msg
  let bodyRes := match w.modeTrace with
    | .stateful leafIdx hmsgW =>
      let modeOk := (geom.forsTrees == 0) && decide (leafIdx < 2 ^ (geom.numLayers * geom.subtreeHeight))
      let modeRes := if modeOk then [] else [Goldilocks.one]
      let kp0 := leafIdx % (2 ^ geom.subtreeHeight)
      let tr0 := leafIdx / (2 ^ geom.subtreeHeight)
      let (topRt, upRes) := upperLayersTraceResiduals geom pk 1 tr0 w.layer0.rootOut w.upperNodes
      modeRes ++
      hmsgStatefulResiduals pk w.rRand mu kp0 w.layer0.tswCtr hmsgW ++
      wotsLayerTraceResiduals geom pk 0 tr0 kp0 hmsgW.outMsg w.layer0 ++
      upRes ++
      (lane4Sub topRt pk.pkRoot).toList
    | .stateless xofW forsW hmsgW =>
      let modeOk := !(geom.forsTrees == 0)
      let modeRes := if modeOk then [] else [Goldilocks.one]
      let (leafIdx, forsIndices) := extractStatelessXofPair geom xofW
      let kp0 := leafIdx % (2 ^ geom.subtreeHeight)
      let tr0 := leafIdx / (2 ^ geom.subtreeHeight)
      let (topRt, upRes) := upperLayersTraceResiduals geom pk 1 tr0 w.layer0.rootOut w.upperNodes
      modeRes ++
      statelessXofTraceResiduals pk w.rRand mu xofW ++
      forsAndRecoverTraceResiduals geom pk.pkSeed leafIdx forsIndices forsW ++
      hmsgDetTreeResiduals pk 0 tr0 kp0 w.layer0.tswCtr forsW.forsPkOut hmsgW ++
      wotsLayerTraceResiduals geom pk 0 tr0 kp0 hmsgW.outMsg w.layer0 ++
      upRes ++
      (lane4Sub topRt pk.pkRoot).toList
  hdrRes ++ bodyRes

private theorem wellFormed_unpack_wots (geom : AggSigGeometry) (hWf : geom.wellFormed = true) :
    geom.wotsChains ≤ 128 ∧ geom.targetSum < 3 * geom.wotsChains := by
  unfold AggSigGeometry.wellFormed at hWf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hWf
  exact ⟨hWf.1.1.1.1.1.1.2, hWf.1.1.1.1.2⟩

theorem signerTraceResiduals_sound (geom : AggSigGeometry) (pk : AggValidatorPk) (msg : List UInt8)
    (w : AggSignerTraceWitness)
    (hZero : allZeroGoldilocks (signerTraceResiduals geom pk msg w) = true) :
    verifyAggNativeSig geom pk msg (extractSignerWitnessSig w) = true := by
  unfold signerTraceResiduals at hZero
  dsimp only at hZero
  rw [allZeroGoldilocks_append, Bool.and_eq_true] at hZero
  rcases hZero with ⟨hHdr, hBody⟩
  cases hHdrB : (geom.wellFormed && (pk.profile == geom.profile) &&
                 (w.profile == geom.profile) && (w.upperNodes.length + 1 == geom.numLayers))
  · rw [hHdrB] at hHdr; exact absurd hHdr (by decide)
  · simp only [Bool.and_eq_true] at hHdrB
    rcases hHdrB with ⟨⟨⟨hWf, hPkProfB⟩, hWProfB⟩, hLenB⟩
    have hPkProf : pk.profile = geom.profile := eq_of_beq hPkProfB
    have hWProf : w.profile = geom.profile := eq_of_beq hWProfB
    have hUpperLen : w.upperNodes.length + 1 = geom.numLayers := eq_of_beq hLenB
    obtain ⟨hChainsLe, hTargetBound⟩ := wellFormed_unpack_wots geom hWf
    cases hMode : w.modeTrace with
    | stateful leafIdx hmsgW =>
      rw [hMode] at hBody
      dsimp only at hBody
      cases hMCond : ((geom.forsTrees == 0) && decide (leafIdx < 2 ^ (geom.numLayers * geom.subtreeHeight)))
      · rw [hMCond] at hBody
        simp only [allZeroGoldilocks_append, Bool.and_eq_true] at hBody
        exact absurd hBody.1.1.1.1 (by decide)
      · rw [hMCond] at hBody
        simp only [allZeroGoldilocks_append, Bool.and_eq_true, lane4Sub_toList_allZero_iff] at hBody
        rcases hBody with ⟨⟨⟨⟨-, hHm⟩, hW0⟩, hUp⟩, hTopEq⟩
        rcases Bool.and_eq_true_iff.mp hMCond with ⟨hFors0, hLeafDec⟩
        have hLeafLt : leafIdx < 2 ^ (geom.numLayers * geom.subtreeHeight) := of_decide_eq_true hLeafDec
        let mu := computeMessageMu pk msg
        let kp0 := leafIdx % (2 ^ geom.subtreeHeight)
        let tr0 := leafIdx / (2 ^ geom.subtreeHeight)
        have hHmIff := hmsgStatefulResiduals_allZero_iff pk w.rRand mu kp0 w.layer0.tswCtr hmsgW
        have hHmOut : hmsgW.outMsg = computeHmsgStateful pk w.rRand mu kp0 w.layer0.tswCtr :=
          hHmIff.2 (hHmIff.1.mp hHm)
        have hVer0 := wotsLayerTraceResiduals_sound geom pk 0 tr0 kp0 hmsgW.outMsg w.layer0
          hChainsLe hTargetBound hW0
        rw [hHmOut] at hVer0
        have hVerUp := upperLayersTraceResiduals_sound geom pk 1 tr0 w.layer0.rootOut w.upperNodes
          hChainsLe hTargetBound hUp
        rw [hTopEq] at hVerUp
        unfold extractSignerWitnessSig
        rw [hMode, hWProf]
        dsimp only
        refine verifyAggNativeSig_stateful_of_ok geom pk msg w.rRand leafIdx
          (wotsLayerWitnessSig w.layer0)
          (w.upperNodes.map fun nw => wotsLayerWitnessSig nw.wotsStep)
          w.layer0.rootOut hWf hPkProf ?_ hFors0 hLeafLt hVer0 hVerUp
        simpa only [List.length_map] using hUpperLen
    | stateless xofW forsW hmsgW =>
      rw [hMode] at hBody
      dsimp only at hBody
      simp only [allZeroGoldilocks_append, Bool.and_eq_true, lane4Sub_toList_allZero_iff] at hBody
      rcases hBody with ⟨⟨⟨⟨⟨⟨hModeOk, hXofZ⟩, hForsZ⟩, hHmZ⟩, hW0Z⟩, hUpZ⟩, hTopEq⟩
      cases hMCond : (!(geom.forsTrees == 0))
      · rw [hMCond] at hModeOk; exact absurd hModeOk (by decide)
      · have hFors0 : (geom.forsTrees == 0) = false := (Bool.not_eq_true' _).mp hMCond
        let mu := computeMessageMu pk msg
        have hXofOk := statelessXofTraceResiduals_sound geom pk w.rRand mu xofW hXofZ
        let pair := extractStatelessXofPair geom xofW
        have hForsOk := forsAndRecoverTraceResiduals_sound geom pk.pkSeed pair.1 pair.2 forsW hForsZ
        let kp0 := pair.1 % (2 ^ geom.subtreeHeight)
        let tr0 := pair.1 / (2 ^ geom.subtreeHeight)
        have hHmIff := hmsgDetTreeResiduals_allZero_iff pk 0 tr0 kp0 w.layer0.tswCtr forsW.forsPkOut hmsgW
        have hHmOut : hmsgW.outMsg = computeHmsgDetTree pk 0 tr0 kp0 w.layer0.tswCtr forsW.forsPkOut :=
          hHmIff.2 (hHmIff.1.mp hHmZ)
        have hVer0 := wotsLayerTraceResiduals_sound geom pk 0 tr0 kp0 hmsgW.outMsg w.layer0
          hChainsLe hTargetBound hW0Z
        rw [hHmOut] at hVer0
        have hVerUp := upperLayersTraceResiduals_sound geom pk 1 tr0 w.layer0.rootOut w.upperNodes
          hChainsLe hTargetBound hUpZ
        rw [hTopEq] at hVerUp
        unfold extractSignerWitnessSig
        rw [hMode, hWProf]
        dsimp only
        refine verifyAggNativeSig_stateless_of_ok geom pk msg w.rRand
          (forsW.openings.map forsOpeningWitnessSig)
          (wotsLayerWitnessSig w.layer0)
          (w.upperNodes.map fun nw => wotsLayerWitnessSig nw.wotsStep)
          pair.1 pair.2 forsW.forsPkOut w.layer0.rootOut
          hWf hPkProf ?_ hFors0 ?_ hForsOk hVer0 hVerUp
        · simpa only [List.length_map] using hUpperLen
        · exact hXofOk

def buildHonestSignerTraceWitness (geom : AggSigGeometry) (pk : AggValidatorPk) (msg : List UInt8)
    (sig : AggNativeSignature) : AggSignerTraceWitness :=
  let mu := computeMessageMu pk msg
  let lsig0 := sig.layers.headD { tswCtr := 0, wotsChains := [], merklePath := [] }
  let upperLs := sig.layers.tail
  if geom.forsTrees == 0 then
    let kp0 := sig.statefulLeafIdx % (2 ^ geom.subtreeHeight)
    let tr0 := sig.statefulLeafIdx / (2 ^ geom.subtreeHeight)
    let hmW := honestHmsgStatefulTraceWitness pk sig.rRand mu kp0 lsig0.tswCtr
    let w0 := honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0
    let upW := honestUpperLayersTrace geom pk 1 tr0 w0.rootOut upperLs
    { profile := sig.profile, rRand := sig.rRand,
      modeTrace := .stateful sig.statefulLeafIdx hmW,
      layer0 := w0, upperNodes := upW }
  else
    let xofW := honestStatelessXofTraceWitness pk sig.rRand mu
    let (leafIdx, forsIndices) := extractStatelessXofPair geom xofW
    let forsW := honestForsAndRecoverTraceWitness geom pk.pkSeed leafIdx forsIndices sig.forsOpenings
    let kp0 := leafIdx % (2 ^ geom.subtreeHeight)
    let tr0 := leafIdx / (2 ^ geom.subtreeHeight)
    let hmW := honestHmsgDetTreeTraceWitness pk 0 tr0 kp0 lsig0.tswCtr forsW.forsPkOut
    let w0 := honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0
    let upW := honestUpperLayersTrace geom pk 1 tr0 w0.rootOut upperLs
    { profile := sig.profile, rRand := sig.rRand,
      modeTrace := .stateless xofW forsW hmW,
      layer0 := w0, upperNodes := upW }

private theorem allZeroGoldilocks_append_intro {a b : List Goldilocks}
    (ha : allZeroGoldilocks a = true) (hb : allZeroGoldilocks b = true) :
    allZeroGoldilocks (a ++ b) = true := by
  rw [allZeroGoldilocks_append, ha, hb]
  rfl

theorem signerTraceResiduals_complete (geom : AggSigGeometry) (pk : AggValidatorPk) (msg : List UInt8)
    (sig : AggNativeSignature)
    (hVer : verifyAggNativeSig geom pk msg sig = true) :
    let w := buildHonestSignerTraceWitness geom pk msg sig
    extractSignerWitnessSig w = sig ∧
    allZeroGoldilocks (signerTraceResiduals geom pk msg w) = true := by
  intro w
  unfold verifyAggNativeSig at hVer
  rcases Bool.eq_false_or_eq_true (!geom.wellFormed || pk.profile != geom.profile ||
      sig.profile != geom.profile || sig.layers.length != geom.numLayers) with hHdr | hHdr
  · simp only [hHdr, ↓reduceIte] at hVer
    cases hVer
  · simp only [hHdr, Bool.false_eq_true, ↓reduceIte] at hVer
    simp only [Bool.or_eq_false_iff, Bool.not_eq_false', bne_eq_false_iff_eq] at hHdr
    rcases hHdr with ⟨⟨⟨hWf, hPkProf⟩, hSigProf⟩, hLayLen⟩
    obtain ⟨hChainsLe, hTargetBound⟩ := wellFormed_unpack_wots geom hWf
    cases hLayers : sig.layers with
    | nil => rw [hLayers] at hVer; cases hVer
    | cons lsig0 upperLs =>
      rw [hLayers] at hVer
      dsimp only at hVer
      have hUpperLen : upperLs.length + 1 = geom.numLayers := by
        rw [← hLayLen, hLayers]; simp
      let mu := computeMessageMu pk msg
      cases hFors0 : (geom.forsTrees == 0)
      · -- Stateless
        rw [hFors0] at hVer
        simp only [Bool.false_eq_true, ↓reduceIte] at hVer
        delta verifyAggNativeSigStateless at hVer
        rcases unpackStatelessFlow hVer with
          ⟨leafIdx, forsIndices, forsPk, root0, topRoot, hLeafNz, hXof, hForsVer, hW0, hUp, hTopBeq⟩
        have hLeafZ : sig.statefulLeafIdx = 0 := bne_eq_false_iff_eq.mp hLeafNz
        have hTopEq : topRoot = pk.pkRoot := eq_of_beq hTopBeq
        obtain ⟨hXofPair, hXofZ⟩ := statelessXofTraceResiduals_complete geom pk sig.rRand mu leafIdx forsIndices hXof
        obtain ⟨hForsMap, hForsOut, hForsZ⟩ := forsAndRecoverTraceResiduals_complete geom pk.pkSeed
          leafIdx forsIndices sig.forsOpenings forsPk hForsVer
        let kp0 := leafIdx % (2 ^ geom.subtreeHeight)
        let tr0 := leafIdx / (2 ^ geom.subtreeHeight)
        let hmW := honestHmsgDetTreeTraceWitness pk 0 tr0 kp0 lsig0.tswCtr forsPk
        have hHmIff := hmsgDetTreeResiduals_allZero_iff pk 0 tr0 kp0 lsig0.tswCtr forsPk hmW
        have hHmOut : hmW.outMsg = computeHmsgDetTree pk 0 tr0 kp0 lsig0.tswCtr forsPk := hHmIff.2 rfl
        have hHmZ : allZeroGoldilocks (hmsgDetTreeResiduals pk 0 tr0 kp0 lsig0.tswCtr forsPk hmW) = true :=
          hHmIff.1.mpr rfl
        have hW0Sub : verifyWotsLayer geom pk 0 tr0 kp0 hmW.outMsg lsig0 = some root0 := by
          rw [hHmOut]; exact hW0
        obtain ⟨hW0Sig, hW0Rt, hW0Z⟩ := wotsLayerTraceResiduals_complete geom pk 0 tr0 kp0
          hmW.outMsg lsig0 root0 hChainsLe hTargetBound hW0Sub
        have hUpSub : verifyUpperLayers geom pk 1 tr0
            (honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0).rootOut upperLs = some topRoot := by
          rw [hW0Rt]; exact hUp
        obtain ⟨hUpMap, hUpTop, hUpZ⟩ := upperLayersTraceResiduals_complete geom pk 1 tr0
          _ topRoot upperLs hChainsLe hTargetBound hUpSub
        have hUpWLen : (honestUpperLayersTrace geom pk 1 tr0
            (honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0).rootOut upperLs).length + 1 =
            geom.numLayers := by
          have h1 : ((honestUpperLayersTrace geom pk 1 tr0
              (honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0).rootOut upperLs).map
              (fun nw => wotsLayerWitnessSig nw.wotsStep)).length = upperLs.length := by rw [hUpMap]
          rw [List.length_map] at h1
          omega
        have hWDef : w = {
            profile := sig.profile, rRand := sig.rRand,
            modeTrace := .stateless (honestStatelessXofTraceWitness pk sig.rRand mu)
                           (honestForsAndRecoverTraceWitness geom pk.pkSeed leafIdx forsIndices sig.forsOpenings) hmW,
            layer0 := honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0,
            upperNodes := honestUpperLayersTrace geom pk 1 tr0
              (honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0).rootOut upperLs } := by
          dsimp only [w, buildHonestSignerTraceWitness]
          simp only [hLayers, List.headD_cons, List.tail_cons, hFors0, Bool.false_eq_true, ↓reduceIte]
          rw [hXofPair]
          dsimp only
          rw [hForsOut]
        rw [hWDef]
        refine ⟨?_, ?_⟩
        · rcases sig with ⟨pr, rr, sli, fops, lays⟩
          dsimp only at hLeafZ hLayers hForsMap hW0Sig hUpMap ⊢
          subst hLeafZ hLayers
          unfold extractSignerWitnessSig
          dsimp only
          simp only [AggNativeSignature.mk.injEq, List.cons.injEq]
          exact ⟨trivial, trivial, trivial, hForsMap, hW0Sig, hUpMap⟩
        · unfold signerTraceResiduals
          dsimp only
          have hHdrTrue :
              (geom.wellFormed && (pk.profile == geom.profile) &&
               (sig.profile == geom.profile) &&
               ((honestUpperLayersTrace geom pk 1 tr0
              (honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0).rootOut upperLs).length + 1 == geom.numLayers)) = true := by
            rw [hWf, hPkProf, hSigProf, hUpWLen]
            simp only [beq_self_eq_true, Bool.and_self]
          rw [hHdrTrue, hFors0, hXofPair, hForsOut]
          have hNil : allZeroGoldilocks (if true = true then [] else [Goldilocks.one]) = true := by decide
          have hNil' : allZeroGoldilocks (if (!false) = true then [] else [Goldilocks.one]) = true := by decide
          have hCtr0 : (honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0).tswCtr = lsig0.tswCtr := rfl
          refine allZeroGoldilocks_append_intro hNil
            (allZeroGoldilocks_append_intro
              (allZeroGoldilocks_append_intro
                (allZeroGoldilocks_append_intro
                  (allZeroGoldilocks_append_intro
                    (allZeroGoldilocks_append_intro
                      (allZeroGoldilocks_append_intro hNil' hXofZ) hForsZ) ?_) hW0Z) hUpZ)
              ((lane4Sub_toList_allZero_iff _ _).mpr (hUpTop.trans hTopEq)))
          rw [hCtr0]
          exact hHmZ
      · -- Stateful
        rw [hFors0] at hVer
        simp only [↓reduceIte] at hVer
        unfold verifyAggNativeSigStateful at hVer
        rcases Bool.eq_false_or_eq_true (!sig.forsOpenings.isEmpty ||
            !(decide (sig.statefulLeafIdx < 2 ^ (geom.numLayers * geom.subtreeHeight)))) with hSChk | hSChk
        · simp only [hSChk, ↓reduceIte] at hVer
          cases hVer
        · simp only [hSChk, Bool.false_eq_true, ↓reduceIte] at hVer
          simp only [Bool.or_eq_false_iff, Bool.not_eq_false', List.isEmpty_iff, decide_eq_true_eq] at hSChk
          rcases hSChk with ⟨hForsNil, hLeafLt⟩
          let kp0 := sig.statefulLeafIdx % (2 ^ geom.subtreeHeight)
          let tr0 := sig.statefulLeafIdx / (2 ^ geom.subtreeHeight)
          let hmsg0 := computeHmsgStateful pk sig.rRand mu kp0 lsig0.tswCtr
          change (match verifyWotsLayer geom pk 0 tr0 kp0 hmsg0 lsig0 with
                  | none => false
                  | some root0 =>
                    match verifyUpperLayers geom pk 1 tr0 root0 upperLs with
                    | none => false
                    | some topRoot => topRoot == pk.pkRoot) = true at hVer
          cases hW0 : verifyWotsLayer geom pk 0 tr0 kp0 hmsg0 lsig0 with
          | none => rw [hW0] at hVer; cases hVer
          | some root0 =>
            rw [hW0] at hVer; dsimp only at hVer
            cases hUp : verifyUpperLayers geom pk 1 tr0 root0 upperLs with
            | none => rw [hUp] at hVer; cases hVer
            | some topRoot =>
              rw [hUp] at hVer; dsimp only at hVer
              have hTopEq : topRoot = pk.pkRoot := eq_of_beq hVer
              let hmW := honestHmsgStatefulTraceWitness pk sig.rRand mu kp0 lsig0.tswCtr
              have hHmIff := hmsgStatefulResiduals_allZero_iff pk sig.rRand mu kp0 lsig0.tswCtr hmW
              have hHmOut : hmW.outMsg = hmsg0 := hHmIff.2 rfl
              have hHmZ : allZeroGoldilocks (hmsgStatefulResiduals pk sig.rRand mu kp0 lsig0.tswCtr hmW) = true :=
                hHmIff.1.mpr rfl
              have hW0Sub : verifyWotsLayer geom pk 0 tr0 kp0 hmW.outMsg lsig0 = some root0 := by
                rw [hHmOut]; exact hW0
              obtain ⟨hW0Sig, hW0Rt, hW0Z⟩ := wotsLayerTraceResiduals_complete geom pk 0 tr0 kp0
                hmW.outMsg lsig0 root0 hChainsLe hTargetBound hW0Sub
              have hUpSub : verifyUpperLayers geom pk 1 tr0
                  (honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0).rootOut upperLs = some topRoot := by
                rw [hW0Rt]; exact hUp
              obtain ⟨hUpMap, hUpTop, hUpZ⟩ := upperLayersTraceResiduals_complete geom pk 1 tr0
                _ topRoot upperLs hChainsLe hTargetBound hUpSub
              have hUpWLen : (honestUpperLayersTrace geom pk 1 tr0
                  (honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0).rootOut upperLs).length + 1 =
                  geom.numLayers := by
                have h1 : ((honestUpperLayersTrace geom pk 1 tr0
              (honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0).rootOut upperLs).map
                    (fun nw => wotsLayerWitnessSig nw.wotsStep)).length = upperLs.length := by rw [hUpMap]
                rw [List.length_map] at h1
                omega
              have hWDef : w = {
                  profile := sig.profile, rRand := sig.rRand,
                  modeTrace := .stateful sig.statefulLeafIdx hmW,
                  layer0 := honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0,
                  upperNodes := honestUpperLayersTrace geom pk 1 tr0
                    (honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0).rootOut upperLs } := by
                dsimp only [w, buildHonestSignerTraceWitness]
                simp only [hLayers, List.headD_cons, List.tail_cons, hFors0, ↓reduceIte, hmW, tr0, kp0, mu]
              rw [hWDef]
              refine ⟨?_, ?_⟩
              · rcases sig with ⟨pr, rr, sli, fops, lays⟩
                dsimp only at hForsNil hLayers hW0Sig hUpMap ⊢
                subst hForsNil hLayers
                unfold extractSignerWitnessSig
                dsimp only
                simp only [AggNativeSignature.mk.injEq, List.cons.injEq]
                exact ⟨trivial, trivial, trivial, trivial, hW0Sig, hUpMap⟩
              · unfold signerTraceResiduals
                dsimp only
                have hHdrTrue :
                    (geom.wellFormed && (pk.profile == geom.profile) &&
                     (sig.profile == geom.profile) &&
                     ((honestUpperLayersTrace geom pk 1 tr0
              (honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0).rootOut upperLs).length + 1 == geom.numLayers)) = true := by
                  rw [hWf, hPkProf, hSigProf, hUpWLen]
                  simp only [beq_self_eq_true, Bool.and_self]
                have hModeTrue :
                    ((geom.forsTrees == 0) && decide (sig.statefulLeafIdx < 2 ^ (geom.numLayers * geom.subtreeHeight))) = true := by
                  rw [hFors0, decide_eq_true hLeafLt]
                  rfl
                rw [hHdrTrue, hModeTrue]
                have hNil : allZeroGoldilocks (if true = true then [] else [Goldilocks.one]) = true := by decide
                have hCtr0 : (honestWotsLayerTraceWitness geom pk 0 tr0 kp0 hmW.outMsg lsig0).tswCtr = lsig0.tswCtr := rfl
                refine allZeroGoldilocks_append_intro hNil
                  (allZeroGoldilocks_append_intro
                    (allZeroGoldilocks_append_intro
                      (allZeroGoldilocks_append_intro
                        (allZeroGoldilocks_append_intro hNil ?_) hW0Z) hUpZ)
                    ((lane4Sub_toList_allZero_iff _ _).mpr (hUpTop.trans hTopEq)))
                rw [hCtr0]
                exact hHmZ

/-! ### Symbolic Degree-≤7 Row Gate AST (`trace.rs:ConstraintKind`) & Degree-8 Sumcheck Bridge -/

/-- Algebraic row gate AST covering every constraint family in `crates/qsag-agg/src/trace.rs`
    (constant, boundary pin, linear wire equality, Boolean selector, conditional mux, quartic
    base-4 digit check, and septic `x^7` `Poseidon2` S-box). -/
inductive RowGate7 where
  | constGate (c : Goldilocks)
  | colSubConst (col : Nat) (c : Goldilocks)
  | colDiff (colA colB : Nat)
  | boolBitGate (col : Nat)
  | muxGate (selCol aCol bCol outCol : Nat)
  | quarticBase4Gate (col : Nat)
  | septicSboxGate (inCol : Nat) (rc : Goldilocks) (outCol : Nat)
  deriving DecidableEq, Repr

/-- Base-field evaluation of a `RowGate7` on column assignment `row : Nat → Goldilocks`. -/
def evalRowGate7 (g : RowGate7) (row : Nat → Goldilocks) : Goldilocks :=
  match g with
  | .constGate c => c
  | .colSubConst col c => Goldilocks.sub (row col) c
  | .colDiff colA colB => Goldilocks.sub (row colA) (row colB)
  | .boolBitGate col => boolBitResidual (row col)
  | .muxGate selCol aCol bCol outCol =>
    Goldilocks.sub (row outCol)
      (Goldilocks.add (row aCol) (Goldilocks.mul (row selCol) (Goldilocks.sub (row bCol) (row aCol))))
  | .quarticBase4Gate col => quarticBase4 (row col)
  | .septicSboxGate inCol rc outCol =>
    Goldilocks.sub (sbox7 (Goldilocks.add (row inCol) rc)) (row outCol)

/-- Extension-field (`GoldilocksExt4`) evaluation of a `RowGate7`. -/
def evalRowGate7Ext4 (g : RowGate7) (row : Nat → GoldilocksExt4) : GoldilocksExt4 :=
  match g with
  | .constGate c => GoldilocksExt4.embedBase c
  | .colSubConst col c => CommRingOps.sub (row col) (GoldilocksExt4.embedBase c)
  | .colDiff colA colB => CommRingOps.sub (row colA) (row colB)
  | .boolBitGate col =>
    CommRingOps.mul (row col) (CommRingOps.sub (row col) GoldilocksExt4.one)
  | .muxGate selCol aCol bCol outCol =>
    CommRingOps.sub (row outCol)
      (CommRingOps.add (row aCol) (CommRingOps.mul (row selCol) (CommRingOps.sub (row bCol) (row aCol))))
  | .quarticBase4Gate col =>
    let d := row col
    CommRingOps.mul
      (CommRingOps.mul d (CommRingOps.sub d GoldilocksExt4.one))
      (CommRingOps.mul
        (CommRingOps.sub d (GoldilocksExt4.embedBase (Goldilocks.ofNat 2)))
        (CommRingOps.sub d (GoldilocksExt4.embedBase (Goldilocks.ofNat 3))))
  | .septicSboxGate inCol rc outCol =>
    CommRingOps.sub (ext4Pow7 (CommRingOps.add (row inCol) (GoldilocksExt4.embedBase rc))) (row outCol)

theorem evalRowGate7Ext4_embedBase (g : RowGate7) (row : Nat → Goldilocks) :
    evalRowGate7Ext4 g (fun col => GoldilocksExt4.embedBase (row col)) =
      GoldilocksExt4.embedBase (evalRowGate7 g row) := by
  have hOne : (GoldilocksExt4.one : GoldilocksExt4) = GoldilocksExt4.embedBase Goldilocks.one := rfl
  cases g with
  | constGate c => rfl
  | colSubConst col c =>
    dsimp only [evalRowGate7Ext4, evalRowGate7]
    exact (GoldilocksExt4.embedBase_sub _ _).symm
  | colDiff colA colB =>
    dsimp only [evalRowGate7Ext4, evalRowGate7]
    exact (GoldilocksExt4.embedBase_sub _ _).symm
  | boolBitGate col =>
    dsimp only [evalRowGate7Ext4, evalRowGate7, boolBitResidual]
    rw [hOne, ← GoldilocksExt4.embedBase_sub, ← GoldilocksExt4.embedBase_mul]
    rfl
  | muxGate selCol aCol bCol outCol =>
    dsimp only [evalRowGate7Ext4, evalRowGate7]
    rw [← GoldilocksExt4.embedBase_sub, ← GoldilocksExt4.embedBase_mul,
        ← GoldilocksExt4.embedBase_add, ← GoldilocksExt4.embedBase_sub]
    rfl
  | quarticBase4Gate col =>
    dsimp only [evalRowGate7Ext4, evalRowGate7, quarticBase4]
    rw [hOne, ← GoldilocksExt4.embedBase_sub, ← GoldilocksExt4.embedBase_sub,
        ← GoldilocksExt4.embedBase_sub, ← GoldilocksExt4.embedBase_mul,
        ← GoldilocksExt4.embedBase_mul, ← GoldilocksExt4.embedBase_mul]
    rfl
  | septicSboxGate inCol rc outCol =>
    dsimp only [evalRowGate7Ext4, evalRowGate7]
    rw [← GoldilocksExt4.embedBase_add, ext4Pow7_embedBase, ← GoldilocksExt4.embedBase_sub]
    rfl

/-- Affine column interpolation `row(t)(col) = row0(col) + t * (row1(col) - row0(col))`. -/
def interpolateRowExt4 (row0 row1 : Nat → GoldilocksExt4) (x : GoldilocksExt4) :
    Nat → GoldilocksExt4 :=
  fun col => RoundPoly.evalCoeffs (affineColPoly (row0 col) (row1 col)) x

/-- Univariate polynomial (`length ≤ 8`, degree `≤ 7`) of `g` along the affine line from `row0` to `row1`. -/
def evalRowGate7LinePoly (g : RowGate7) (row0 row1 : Nat → GoldilocksExt4) :
    List GoldilocksExt4 :=
  let colPoly (c : Nat) := affineColPoly (row0 c) (row1 c)
  match g with
  | .constGate c => [GoldilocksExt4.embedBase c]
  | .colSubConst col c => RoundPoly.subCoeffs (colPoly col) [GoldilocksExt4.embedBase c]
  | .colDiff colA colB => RoundPoly.subCoeffs (colPoly colA) (colPoly colB)
  | .boolBitGate col =>
    let p := colPoly col
    polyMulCoeffs p (RoundPoly.subCoeffs p [GoldilocksExt4.one])
  | .muxGate selCol aCol bCol outCol =>
    let ps := colPoly selCol
    let pa := colPoly aCol
    let pb := colPoly bCol
    let po := colPoly outCol
    RoundPoly.subCoeffs po (polyAddCoeffs pa (polyMulCoeffs ps (RoundPoly.subCoeffs pb pa)))
  | .quarticBase4Gate col =>
    let p := colPoly col
    let p01 := polyMulCoeffs p (RoundPoly.subCoeffs p [GoldilocksExt4.one])
    let p23 := polyMulCoeffs
      (RoundPoly.subCoeffs p [GoldilocksExt4.embedBase (Goldilocks.ofNat 2)])
      (RoundPoly.subCoeffs p [GoldilocksExt4.embedBase (Goldilocks.ofNat 3)])
    polyMulCoeffs p01 p23
  | .septicSboxGate inCol rc outCol =>
    let pin := polyAddCoeffs (colPoly inCol) [GoldilocksExt4.embedBase rc]
    RoundPoly.subCoeffs (polyPow7 pin) (colPoly outCol)

theorem evalRowGate7LinePoly_spec (g : RowGate7) (row0 row1 : Nat → GoldilocksExt4) :
    (evalRowGate7LinePoly g row0 row1).length ≤ 8 ∧
    (∀ x : GoldilocksExt4,
      RoundPoly.evalCoeffs (evalRowGate7LinePoly g row0 row1) x =
        evalRowGate7Ext4 g (interpolateRowExt4 row0 row1 x)) := by
  have hConstEval : ∀ (v x : GoldilocksExt4), RoundPoly.evalCoeffs [v] x = v := fun v x => by
    simp [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  cases g with
  | constGate c =>
    refine ⟨by simp [evalRowGate7LinePoly], fun x => hConstEval _ x⟩
  | colSubConst col c =>
    refine ⟨?_, fun x => ?_⟩
    · simp [evalRowGate7LinePoly, RoundPoly.subCoeffs_length, affineColPoly]
    · simp only [evalRowGate7LinePoly, RoundPoly.evalCoeffs_sub, hConstEval]
      rfl
  | colDiff colA colB =>
    refine ⟨?_, fun x => ?_⟩
    · simp [evalRowGate7LinePoly, RoundPoly.subCoeffs_length, affineColPoly]
    · simp only [evalRowGate7LinePoly, RoundPoly.evalCoeffs_sub]
      rfl
  | boolBitGate col =>
    refine ⟨?_, fun x => ?_⟩
    · dsimp only [evalRowGate7LinePoly]
      have h1 : (affineColPoly (row0 col) (row1 col)).length ≤ 2 := by simp [affineColPoly]
      have h2 : (RoundPoly.subCoeffs (affineColPoly (row0 col) (row1 col)) [GoldilocksExt4.one]).length ≤ 2 := by
        simp [RoundPoly.subCoeffs_length, affineColPoly]
      have hM := polyMulCoeffs_length_le _ _ 1 1 h1 h2
      omega
    · simp only [evalRowGate7LinePoly, evalCoeffs_polyMulCoeffs, RoundPoly.evalCoeffs_sub, hConstEval]
      rfl
  | muxGate selCol aCol bCol outCol =>
    refine ⟨?_, fun x => ?_⟩
    · dsimp only [evalRowGate7LinePoly]
      have hs : (affineColPoly (row0 selCol) (row1 selCol)).length ≤ 2 := by simp [affineColPoly]
      have hba : (RoundPoly.subCoeffs (affineColPoly (row0 bCol) (row1 bCol))
                    (affineColPoly (row0 aCol) (row1 aCol))).length ≤ 2 := by
        simp [RoundPoly.subCoeffs_length, affineColPoly]
      have hMul := polyMulCoeffs_length_le _ _ 1 1 hs hba
      rw [RoundPoly.subCoeffs_length, polyAddCoeffs_length]
      have ha : (affineColPoly (row0 aCol) (row1 aCol)).length = 2 := rfl
      have ho : (affineColPoly (row0 outCol) (row1 outCol)).length = 2 := rfl
      rw [ha, ho]
      exact Nat.max_le.mpr ⟨by decide, Nat.max_le.mpr ⟨by decide, by omega⟩⟩
    · simp only [evalRowGate7LinePoly, RoundPoly.evalCoeffs_sub, evalCoeffs_polyAddCoeffs,
        evalCoeffs_polyMulCoeffs]
      rfl
  | quarticBase4Gate col =>
    refine ⟨?_, fun x => ?_⟩
    · dsimp only [evalRowGate7LinePoly]
      have hp : (affineColPoly (row0 col) (row1 col)).length ≤ 2 := by simp [affineColPoly]
      have hs1 : (RoundPoly.subCoeffs (affineColPoly (row0 col) (row1 col)) [GoldilocksExt4.one]).length ≤ 2 := by
        simp [RoundPoly.subCoeffs_length, affineColPoly]
      have hs2 : (RoundPoly.subCoeffs (affineColPoly (row0 col) (row1 col))
                    [GoldilocksExt4.embedBase (Goldilocks.ofNat 2)]).length ≤ 2 := by
        simp [RoundPoly.subCoeffs_length, affineColPoly]
      have hs3 : (RoundPoly.subCoeffs (affineColPoly (row0 col) (row1 col))
                    [GoldilocksExt4.embedBase (Goldilocks.ofNat 3)]).length ≤ 2 := by
        simp [RoundPoly.subCoeffs_length, affineColPoly]
      have hp01 := polyMulCoeffs_length_le _ _ 1 1 hp hs1
      have hp23 := polyMulCoeffs_length_le _ _ 1 1 hs2 hs3
      have hTot := polyMulCoeffs_length_le _ _ 2 2 hp01 hp23
      omega
    · simp only [evalRowGate7LinePoly, evalCoeffs_polyMulCoeffs, RoundPoly.evalCoeffs_sub, hConstEval]
      rfl
  | septicSboxGate inCol rc outCol =>
    refine ⟨?_, fun x => ?_⟩
    · dsimp only [evalRowGate7LinePoly]
      have hPin : (polyAddCoeffs (affineColPoly (row0 inCol) (row1 inCol))
                    [GoldilocksExt4.embedBase rc]).length ≤ 2 := by
        simp [polyAddCoeffs_length, affineColPoly]
      have hP7 := polyPow7_length_le_eight hPin
      rw [RoundPoly.subCoeffs_length]
      have ho : (affineColPoly (row0 outCol) (row1 outCol)).length = 2 := rfl
      rw [ho]
      exact Nat.max_le.mpr ⟨hP7, by decide⟩
    · simp only [evalRowGate7LinePoly, RoundPoly.evalCoeffs_sub, evalCoeffs_polyPow7,
        evalCoeffs_polyAddCoeffs, hConstEval]
      rfl

/-- Gamma-batched univariate degree-`≤ 7` row constraint polynomial. -/
def batchRowGatesExt4 (gates : List (GoldilocksExt4 × RowGate7)) (row : Nat → GoldilocksExt4) :
    GoldilocksExt4 :=
  match gates with
  | [] => GoldilocksExt4.zero
  | (w, g) :: rest =>
    CommRingOps.add (CommRingOps.mul w (evalRowGate7Ext4 g row)) (batchRowGatesExt4 rest row)

def batchRowGatesLinePoly (gates : List (GoldilocksExt4 × RowGate7))
    (row0 row1 : Nat → GoldilocksExt4) : List GoldilocksExt4 :=
  match gates with
  | [] => []
  | (w, g) :: rest =>
    polyAddCoeffs (polyScaleCoeffs w (evalRowGate7LinePoly g row0 row1))
                  (batchRowGatesLinePoly rest row0 row1)

theorem batchRowGatesLinePoly_spec (gates : List (GoldilocksExt4 × RowGate7))
    (row0 row1 : Nat → GoldilocksExt4) :
    (batchRowGatesLinePoly gates row0 row1).length ≤ 8 ∧
    (∀ x : GoldilocksExt4,
      RoundPoly.evalCoeffs (batchRowGatesLinePoly gates row0 row1) x =
        batchRowGatesExt4 gates (interpolateRowExt4 row0 row1 x)) := by
  induction gates with
  | nil =>
    exact ⟨by simp [batchRowGatesLinePoly], fun _ => rfl⟩
  | cons wg rest ih =>
    rcases wg with ⟨w, g⟩
    obtain ⟨hG8, hGEval⟩ := evalRowGate7LinePoly_spec g row0 row1
    refine ⟨?_, fun x => ?_⟩
    · simp only [batchRowGatesLinePoly, polyAddCoeffs_length, polyScaleCoeffs_length]
      exact Nat.max_le.mpr ⟨hG8, ih.1⟩
    · simp only [batchRowGatesLinePoly, batchRowGatesExt4, evalCoeffs_polyAddCoeffs,
        evalCoeffs_polyScaleCoeffs, hGEval x, ih.2 x]

/-- **Exact Degree-8 Batched Row-Sumcheck Round Polynomial (`batchRowGatesRoundPoly_spec`)**:
    For ANY weighted batch of `RowGate7` constraints (`Poseidon2` S-box, quartic base-4, mux,
    Boolean selector, wire diff, and boundary pins), multiplying by `eq(tau_j, t)` yields at most
    `rowSumcheckCoeffs = 9` `GoldilocksExt4` coefficients (`ROW_SUMCHECK_DEGREE = 8`)! -/
theorem batchRowGatesRoundPoly_spec (tau_j : GoldilocksExt4)
    (gates : List (GoldilocksExt4 × RowGate7)) (row0 row1 : Nat → GoldilocksExt4) :
    (buildRowSumcheckRoundPoly tau_j (batchRowGatesLinePoly gates row0 row1)).length ≤ rowSumcheckCoeffs ∧
    (∀ x : GoldilocksExt4,
      RoundPoly.evalCoeffs (buildRowSumcheckRoundPoly tau_j (batchRowGatesLinePoly gates row0 row1)) x =
        CommRingOps.mul (eqFactorExt4 tau_j x)
          (batchRowGatesExt4 gates (interpolateRowExt4 row0 row1 x))) := by
  obtain ⟨h8, hEval⟩ := batchRowGatesLinePoly_spec gates row0 row1
  obtain ⟨h9, hR⟩ := rowSumcheckRoundPoly_spec tau_j (batchRowGatesLinePoly gates row0 row1) h8
  exact ⟨h9, fun x => (hR x).trans (congrArg (CommRingOps.mul (eqFactorExt4 tau_j x)) (hEval x))⟩

/-! ### Public Statement, Boundary Pinning, Execution Trace, & `trace_satisfies_constraints_iff_all_k_sigs_valid` -/

/-- Public arithmetization statement `(geom, msg, committeePks, logRows)` binding `K ≥ 1` distinct
    committee public keys and message `msg` to hypercube dimension `logRows` (`2^logRows` rows). -/
structure AggArithPublicStmt where
  geom         : AggSigGeometry
  msg          : List UInt8
  committeePks : List AggValidatorPk
  logRows      : Nat
  deriving DecidableEq, Repr

@[expose] def AggArithPublicStmt.wellFormed (stmt : AggArithPublicStmt) : Bool :=
  stmt.geom.wellFormed &&
  !stmt.committeePks.isEmpty &&
  decide stmt.committeePks.Nodup &&
  decide (stmt.committeePks.length ≤ 2 ^ stmt.logRows) &&
  stmt.committeePks.all (·.profile == stmt.geom.profile)

/-- 14 public boundary field elements pinned on row `k` for `(pk, msg)`:
    column `0` is `profileFieldTag pk.profile ∈ {1, 2}` (strictly non-zero for every `pk`),
    columns `1..4` are `pk.pkSeed`, columns `5..8` are `pk.pkRoot`, and columns `9..13` are
    `computeMessageMu pk msg` (`Digest5`). -/
def expectedBoundaryCols (pk : AggValidatorPk) (msg : List UInt8) : List Goldilocks :=
  let mu := computeMessageMu pk msg
  [profileFieldTag pk.profile] ++ pk.pkSeed.toList ++ pk.pkRoot.toList ++
    [mu.limb0, mu.limb1, mu.limb2, mu.limb3, mu.limb4]

private def boundaryGatesFrom (idx : Nat) : List Goldilocks → List RowGate7
  | [] => []
  | c :: cs => RowGate7.colSubConst idx c :: boundaryGatesFrom (idx + 1) cs

/-- Exact `RowGate7.colSubConst` boundary constraints for validator `pk` and `msg`. -/
def boundaryRowGates (pk : AggValidatorPk) (msg : List UInt8) : List RowGate7 :=
  boundaryGatesFrom 0 (expectedBoundaryCols pk msg)

/-- Evaluate a list of `RowGate7` gates on a concrete row `List Goldilocks`. -/
def evalRowGateList (gates : List RowGate7) (row : List Goldilocks) : List Goldilocks :=
  gates.map (fun g => evalRowGate7 g (fun col => row.getD col Goldilocks.zero))

private theorem boundaryGatesFrom_zero_at_col0 (c0 : Goldilocks) (cs : List Goldilocks)
    (row : List Goldilocks)
    (hZero : allZeroGoldilocks (evalRowGateList (boundaryGatesFrom 0 (c0 :: cs)) row) = true) :
    row.getD 0 Goldilocks.zero = c0 := by
  unfold boundaryGatesFrom evalRowGateList allZeroGoldilocks at hZero
  simp only [List.map_cons, List.all_cons, Bool.and_eq_true] at hZero
  exact (sub_eq_zero_iff_goldilocks _ _).mp hZero.1

private theorem boundaryGatesFrom_exact :
    ∀ (idx : Nat) (expected pfx sfx : List Goldilocks),
      pfx.length = idx →
      allZeroGoldilocks (evalRowGateList (boundaryGatesFrom idx expected) (pfx ++ expected ++ sfx)) = true
  | _, [], _, _, _ => rfl
  | idx, c :: cs, pfx, sfx, hLen => by
    have hGet : (pfx ++ (c :: cs) ++ sfx).getD idx Goldilocks.zero = c := by
      have hAssoc : pfx ++ (c :: cs) ++ sfx = pfx ++ (c :: (cs ++ sfx)) := by
        simp [List.append_assoc]
      rw [hAssoc, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
      simp [hLen]
    have hSub : pfx ++ (c :: cs) ++ sfx = (pfx ++ [c]) ++ cs ++ sfx := by
      simp [List.append_assoc]
    have ih := boundaryGatesFrom_exact (idx + 1) cs (pfx ++ [c]) sfx (by simp [hLen])
    unfold evalRowGateList allZeroGoldilocks at ih ⊢
    simp only [boundaryGatesFrom, List.map_cons, List.all_cons, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · dsimp only [evalRowGate7]
      rw [hGet]
      exact (sub_eq_zero_iff_goldilocks c c).mpr rfl
    · rw [← hSub] at ih
      exact ih

private theorem allZero_flatMap_replicate_zeros :
    ∀ (m n : Nat),
      allZeroGoldilocks ((List.replicate m (List.replicate n Goldilocks.zero)).flatMap id) = true
  | 0, _ => rfl
  | m + 1, n => by
    have hRepZero : ∀ k : Nat, allZeroGoldilocks (List.replicate k Goldilocks.zero) = true := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        unfold allZeroGoldilocks at ih ⊢
        simp only [List.replicate_succ, List.all_cons, beq_self_eq_true, Bool.true_and]
        exact ih
    simp only [List.replicate_succ, List.flatMap_cons, id_eq, allZeroGoldilocks_append, Bool.and_eq_true]
    exact ⟨hRepZero n, allZero_flatMap_replicate_zeros m n⟩

private theorem getD_zero_replicate_zero (numCols : Nat) :
    (List.replicate numCols Goldilocks.zero).getD 0 Goldilocks.zero = Goldilocks.zero := by
  cases numCols <;> rfl

/-! ### The 256-column `StepOp` execution table and its inter-row shift constraints (`trace.rs`) -/

section StepOpTable

local infixl:65 " +ₚ " => Goldilocks.add
local infixl:65 " -ₚ " => Goldilocks.sub
local infixl:70 " *ₚ " => Goldilocks.mul
local notation "‹" n "›" => Goldilocks.ofNat n

/-- `NUM_TRACE_COLS`. -/
def stepOpNumCols : Nat := 256

/-- `NUM_STATE_LIMBS`: the carried state registers `st[0..44]`. -/
def stepOpNumStateLimbs : Nat := 44

/-- `ST_CUR_ROOT` (4 limbs). -/
def stCurRoot : Nat := 0
/-- `ST_KP_IDX`. -/
def stKpIdx : Nat := 4
/-- `ST_TREE_LO`. -/
def stTreeLo : Nat := 5
/-- `ST_TREE_HI`. -/
def stTreeHi : Nat := 6
/-- `ST_REM_PACK` (6 limbs). -/
def stRemPack : Nat := 7
/-- `ST_MAIN_SPONGE` (12 limbs). -/
def stMainSponge : Nat := 13
/-- `ST_SUB_SPONGE` (12 limbs). -/
def stSubSponge : Nat := 25
/-- `ST_WORK` (4 limbs). -/
def stWork : Nat := 37
/-- `ST_CURSOR_IDX`. -/
def stCursorIdx : Nat := 41
/-- `ST_ACC_OR_U1`. -/
def stAccOrU1 : Nat := 42
/-- `ST_WOTS_U2`. -/
def stWotsU2 : Nat := 43

/-- One row of the execution table, grouped by the column blocks of `trace.rs`:
    `COL_ST_IN = 0..12`, `COL_SBOX_OUT = 12..130` (4 external rounds of 12 lanes, 22 internal
    rounds, 4 external rounds of 12 lanes), `COL_PREV_STATE = 130..174`,
    `COL_NEXT_STATE = 174..218`, `COL_AUX = 218..256`. -/
structure StepOpRow where
  stIn        : Poseidon2State12
  initExtSbox : List Poseidon2State12
  intSbox     : List Goldilocks
  termExtSbox : List Poseidon2State12
  prevState   : List Goldilocks
  nextState   : List Goldilocks
  aux         : List Goldilocks
  deriving DecidableEq, Repr

/-- The column blocks have their `trace.rs` widths. -/
def StepOpRow.wellShaped (r : StepOpRow) : Bool :=
  r.initExtSbox.length == 4 && r.intSbox.length == 22 && r.termExtSbox.length == 4 &&
  r.prevState.length == 44 && r.nextState.length == 44 && r.aux.length == 38

/-- The cells of a row in `trace.rs` column order. -/
def StepOpRow.cells (r : StepOpRow) : List Goldilocks :=
  r.stIn.toList ++ r.initExtSbox.flatMap Poseidon2State12.toList ++ r.intSbox ++
    r.termExtSbox.flatMap Poseidon2State12.toList ++ r.prevState ++ r.nextState ++ r.aux

private theorem flatMap_state12_length :
    ∀ (l : List Poseidon2State12), (l.flatMap Poseidon2State12.toList).length = 12 * l.length
  | [] => rfl
  | s :: l => by
    have h12 : s.toList.length = 12 := rfl
    rw [List.flatMap_cons, List.length_append, flatMap_state12_length l, List.length_cons, h12]
    omega

/-- A well-shaped row has exactly `NUM_TRACE_COLS = 256` cells. -/
theorem StepOpRow.cells_length (r : StepOpRow) (h : r.wellShaped = true) :
    r.cells.length = stepOpNumCols := by
  unfold StepOpRow.wellShaped at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  have h12 : r.stIn.toList.length = 12 := rfl
  have hc : r.cells.length =
      r.stIn.toList.length + 12 * r.initExtSbox.length + r.intSbox.length +
        12 * r.termExtSbox.length + r.prevState.length + r.nextState.length + r.aux.length := by
    unfold StepOpRow.cells
    simp only [List.length_append, flatMap_state12_length]
  unfold stepOpNumCols
  omega

/-- Deterministic step opcodes of the per-signer state machine (`StepOp` in `trace.rs`). -/
inductive StepOp where
  | idle
  | statefulHmsgBlock0
  | statefulHmsgBlock1
  | statefulHmsgSqueeze
  | statelessDeriveBlock0
  | statelessDeriveBlock1
  | statelessDecompLimb (limbIdx : Nat)
  | forsRootsSpongeInit
  | forsLeafHash (treeJ packSlot : Nat)
  | forsMerkleBlockA (treeJ lvl : Nat)
  | forsMerkleBlockB (lvl : Nat) (isTreeLast isOddTree : Bool)
  | forsRootsPairAbsorb (pairIdx : Nat)
  | forsRootsFinalSqueeze
  | detTreeHmsgBlock0 (layer : Nat)
  | detTreeHmsgBlock1 (layer : Nat)
  | hmsgDecompLimb (limbIdx : Nat)
  | wotsTellInit (layer : Nat)
  | wotsChainStep0 (layer chain packSlot : Nat)
  | wotsChainStep1 (layer chain : Nat)
  | wotsChainStep2 (layer chain : Nat) (isOdd : Bool)
  | wotsTellPairAbsorb (pairIdx : Nat)
  | wotsTellFinalSqueeze
  | xmssMerkleBlockA (layer lvl : Nat)
  | xmssMerkleBlockB (isLayerLast isTopFinal : Bool)
  deriving DecidableEq, Repr

/-- Algebraic constraint class of a step (`ConstraintKind` in `trace.rs`): the per-step public
    constants `layer`, `chain`, `tree_j`, `lvl` are factored into the scalar `step_c0`. -/
inductive StepConstraintKind where
  | idle
  | statefulHmsgBlock0
  | statefulHmsgBlock1
  | statefulHmsgSqueeze
  | statelessDeriveBlock0
  | statelessDeriveBlock1
  | statelessDecompLimb (limbIdx : Nat)
  | forsRootsSpongeInit
  | forsLeafHash (packSlot : Nat)
  | forsMerkleBlockA
  | forsMerkleBlockB (isTreeLast isOddTree : Bool)
  | forsRootsPairAbsorb (isLastPair : Bool)
  | forsRootsFinalSqueeze
  | detTreeHmsgBlock0
  | detTreeHmsgBlock1
  | hmsgDecompLimb (limbIdx : Nat)
  | wotsTellInit
  | wotsChainStep0 (packSlot : Nat)
  | wotsChainStep1
  | wotsChainStep2 (isOdd : Bool)
  | wotsTellPairAbsorb (isLastPair : Bool)
  | wotsTellFinalSqueeze
  | xmssMerkleBlockA
  | xmssMerkleBlockB (isLayerLast isTopFinal : Bool)
  deriving DecidableEq, Repr

/-- `wots_pack_slot`: the `ST_REM_PACK` limb holding the remaining-step count of a chain. -/
def wotsPackSlot (chain : Nat) : Nat :=
  if chain < 26 then 0 else if chain < 52 then 1 else if chain < 78 then 2
  else if chain < 103 then 3 else 4

/-- First chain of a `wots_pack_slot`. -/
def wotsPackSlotStart : Nat → Nat
  | 0 => 0
  | 1 => 26
  | 2 => 52
  | 3 => 78
  | _ => 103

/-- `push_layer_wots_and_merkle`: one WOTS+C layer (`T_ell` sponge interleaved with the 128
    three-step chains) followed by its subtree Merkle path. -/
def pushLayerWotsAndMerkle (layer subHeight : Nat) (isTopFinal : Bool) : List StepOp :=
  [StepOp.wotsTellInit layer] ++
  (List.range 64).flatMap (fun pair =>
    (List.range 2).flatMap (fun sub =>
      [StepOp.wotsChainStep0 layer (2 * pair + sub) (wotsPackSlot (2 * pair + sub)),
       StepOp.wotsChainStep1 layer (2 * pair + sub),
       StepOp.wotsChainStep2 layer (2 * pair + sub) (sub == 1)]) ++
    [StepOp.wotsTellPairAbsorb pair]) ++
  [StepOp.wotsTellFinalSqueeze] ++
  (List.range subHeight).flatMap (fun lvl =>
    [StepOp.xmssMerkleBlockA layer lvl,
     StepOp.xmssMerkleBlockB (lvl + 1 == subHeight) ((lvl + 1 == subHeight) && isTopFinal)])

/-- `rows_per_signer`. -/
def stepOpRowsPerSigner : AggSigProfile → Nat
  | .xmssPoseidon2 => 512
  | .corduroyPoseidon2 => 8192

/-- The opcodes of one signer before `Idle` padding. -/
def signerProgramBody : AggSigProfile → List StepOp
  | .xmssPoseidon2 =>
    [StepOp.statefulHmsgBlock0, StepOp.statefulHmsgBlock1, StepOp.statefulHmsgSqueeze] ++
    (List.range 5).map StepOp.hmsgDecompLimb ++
    pushLayerWotsAndMerkle 0 6 true
  | .corduroyPoseidon2 =>
    [StepOp.statelessDeriveBlock0, StepOp.statelessDeriveBlock1] ++
    (List.range 7).map StepOp.statelessDecompLimb ++
    [StepOp.forsRootsSpongeInit] ++
    (List.range 16).flatMap (fun pair =>
      (List.range 2).flatMap (fun sub =>
        [StepOp.forsLeafHash (2 * pair + sub) ((2 * pair + sub) / 6)] ++
        (List.range 8).flatMap (fun lvl =>
          [StepOp.forsMerkleBlockA (2 * pair + sub) lvl,
           StepOp.forsMerkleBlockB lvl (lvl + 1 == 8) (sub == 1)])) ++
      [StepOp.forsRootsPairAbsorb pair]) ++
    [StepOp.forsRootsFinalSqueeze] ++
    (List.range 16).flatMap (fun layer =>
      [StepOp.detTreeHmsgBlock0 layer, StepOp.detTreeHmsgBlock1 layer] ++
      (List.range 5).map StepOp.hmsgDecompLimb ++
      pushLayerWotsAndMerkle layer 4 (layer + 1 == 16))

/-- `build_signer_program`: the fixed-length program shared by prover and verifier. -/
def buildSignerProgram (profile : AggSigProfile) : List StepOp :=
  signerProgramBody profile ++
    List.replicate (stepOpRowsPerSigner profile - (signerProgramBody profile).length) StepOp.idle

/-- The program fills exactly `rows_per_signer` rows and ends in at least one `Idle` row
    (`470 < 512` and `8011 < 8192`). -/
theorem buildSignerProgram_length :
    (signerProgramBody .xmssPoseidon2).length = 470 ∧
    (signerProgramBody .corduroyPoseidon2).length = 8011 ∧
    (buildSignerProgram .xmssPoseidon2).length = 512 ∧
    (buildSignerProgram .corduroyPoseidon2).length = 8192 := by
  decide +kernel

/-- `step_op_to_kind_and_c0`: constraint class and per-step public constant `step_c0`. -/
def stepOpKindAndC0 : StepOp → StepConstraintKind × Nat
  | .idle => (.idle, 0)
  | .statefulHmsgBlock0 => (.statefulHmsgBlock0, 0)
  | .statefulHmsgBlock1 => (.statefulHmsgBlock1, 0)
  | .statefulHmsgSqueeze => (.statefulHmsgSqueeze, 0)
  | .statelessDeriveBlock0 => (.statelessDeriveBlock0, 0)
  | .statelessDeriveBlock1 => (.statelessDeriveBlock1, 0)
  | .statelessDecompLimb l => (.statelessDecompLimb l, 0)
  | .forsRootsSpongeInit => (.forsRootsSpongeInit, 0)
  | .forsLeafHash j slot => (.forsLeafHash slot, j * 2 ^ 8)
  | .forsMerkleBlockA j lvl => (.forsMerkleBlockA, (lvl + 1) * 2 ^ 32 + j * 2 ^ (7 - lvl))
  | .forsMerkleBlockB _ isTreeLast isOddTree => (.forsMerkleBlockB isTreeLast isOddTree, 0)
  | .forsRootsPairAbsorb pair => (.forsRootsPairAbsorb (pair + 1 == 16), 0)
  | .forsRootsFinalSqueeze => (.forsRootsFinalSqueeze, 0)
  | .detTreeHmsgBlock0 layer => (.detTreeHmsgBlock0, layer * 2 ^ 32)
  | .detTreeHmsgBlock1 _ => (.detTreeHmsgBlock1, 0)
  | .hmsgDecompLimb l => (.hmsgDecompLimb l, 0)
  | .wotsTellInit layer => (.wotsTellInit, layer * 2 ^ 32)
  | .wotsChainStep0 layer chain slot => (.wotsChainStep0 slot, layer * 2 ^ 44 + chain * 2 ^ 4)
  | .wotsChainStep1 layer chain => (.wotsChainStep1, layer * 2 ^ 44 + chain * 2 ^ 4 + 1)
  | .wotsChainStep2 layer chain isOdd =>
    (.wotsChainStep2 isOdd, layer * 2 ^ 44 + chain * 2 ^ 4 + 2)
  | .wotsTellPairAbsorb pair => (.wotsTellPairAbsorb (pair + 1 == 64), 0)
  | .wotsTellFinalSqueeze => (.wotsTellFinalSqueeze, 0)
  | .xmssMerkleBlockA layer lvl => (.xmssMerkleBlockA, layer * 2 ^ 48 + (lvl + 1) * 2 ^ 32)
  | .xmssMerkleBlockB isLayerLast isTopFinal => (.xmssMerkleBlockB isLayerLast isTopFinal, 0)

/-- Row values one opcode's transition constraints read (`OpRowInputs` in `trace.rs`). -/
structure StepOpRowInputs where
  prev    : Nat → Goldilocks
  next    : Nat → Goldilocks
  aux     : Nat → Goldilocks
  stIn    : Nat → Goldilocks
  permOut : Nat → Goldilocks
  pkSeed  : Nat → Goldilocks
  pkRoot  : Nat → Goldilocks
  mu      : Nat → Goldilocks

/-- `bool_check_generic`: `b * (1 - b)`. -/
def stepBoolCheck (b : Goldilocks) : Goldilocks := b *ₚ (Goldilocks.one -ₚ b)

/-- `Σ_{i < n} f i * w i`, accumulated from zero in index order. -/
def stepWeightedSum (f : Nat → Goldilocks) (w : Nat → Nat) (n : Nat) : Goldilocks :=
  (List.range n).foldl (fun acc i => acc +ₚ (f i *ₚ ‹w i›)) Goldilocks.zero

/-- `Σ_{i < n} f i`, accumulated from zero in index order. -/
def stepPlainSum (f : Nat → Goldilocks) (n : Nat) : Goldilocks :=
  (List.range n).foldl (fun acc i => acc +ₚ f i) Goldilocks.zero

/-- `j` lies in the register block `[a, a + n)`. -/
def stepInBlock (a n j : Nat) : Bool := decide (a ≤ j) && decide (j < a + n)

/-- `check_carry_unchanged`: every state limb outside `changed` is carried, `next = prev`. -/
def stepCarryUnchanged (x : StepOpRowInputs) (changed : Nat → Bool) : List Goldilocks :=
  (List.range 44).filterMap fun j => if changed j then none else some (x.next j -ₚ x.prev j)

/-- `check_zero_elsewhere`: every state limb outside `kept` is zero in `next`. -/
def stepZeroElsewhere (x : StepOpRowInputs) (kept : Nat → Bool) : List Goldilocks :=
  (List.range 44).filterMap fun j => if kept j then none else some (x.next j)

/-- `next[base + i] = perm_out[i]` for `i < n`. -/
def stepNextIsPerm (x : StepOpRowInputs) (base n : Nat) : List Goldilocks :=
  (List.range n).map fun i => x.next (base + i) -ₚ x.permOut i

/-- Base-4 digits `aux[0..31]`, top bit `aux[31]`, and the reconstruction
    `prev[ST_MAIN_SPONGE + l] = Σ aux[i] 4^i + aux[31] 2^62` of a `< 2^63` limb. -/
def stepLimb63Decomp (x : StepOpRowInputs) (l : Nat) : List Goldilocks :=
  (List.range 31).map (fun i => quarticBase4 (x.aux i)) ++
  [stepBoolCheck (x.aux 31),
   x.prev (stMainSponge + l) -ₚ
     (stepWeightedSum x.aux (fun i => 4 ^ i) 31 +ₚ (x.aux 31 *ₚ ‹2 ^ 62›))]

/-- Byte `sub` assembled from four base-4 digits of the limb. -/
def stepByteVal (x : StepOpRowInputs) (sub : Nat) : Goldilocks :=
  ((x.aux (4 * sub) +ₚ (x.aux (4 * sub + 1) *ₚ ‹4›)) +ₚ (x.aux (4 * sub + 2) *ₚ ‹16›)) +ₚ
    (x.aux (4 * sub + 3) *ₚ ‹64›)

/-- `expected_next[j]` after packing FORS indices `firstJ .. firstJ + count` (six bytes per
    `ST_REM_PACK` limb). -/
def stepForsPackExpected (x : StepOpRowInputs) (firstJ count j : Nat) : Goldilocks :=
  (List.range count).foldl
    (fun acc sub =>
      if stRemPack + (firstJ + sub) / 6 = j then
        acc +ₚ (stepByteVal x sub *ₚ ‹2 ^ (8 * ((firstJ + sub) % 6))›)
      else acc)
    (x.prev j)

/-- Upper 28 bits of a 32-bit half of `leaf_global_idx`: digits `aux[2..16]`. -/
def stepHi28 (x : StepOpRowInputs) : Goldilocks :=
  stepWeightedSum (fun i => x.aux (2 + i)) (fun i => 4 ^ i) 14

/-- `expected_next[j]` of `StatelessDecompLimb { limb_idx = l }`. -/
def stepStatelessDecompExpected (x : StepOpRowInputs) (l j : Nat) : Goldilocks :=
  if l < 4 then stepForsPackExpected x (7 * l) 7 j
  else if l = 4 then stepForsPackExpected x 28 4 j
  else if l = 5 then
    (if j = stKpIdx then x.aux 0 +ₚ (x.aux 1 *ₚ ‹4›)
     else if j = stTreeLo then stepHi28 x
     else x.prev j)
  else if l = 6 then
    (if j = stTreeLo then x.prev stTreeLo +ₚ ((x.aux 0 +ₚ (x.aux 1 *ₚ ‹4›)) *ₚ ‹2 ^ 28›)
     else if j = stTreeHi then stepHi28 x
     else x.prev j)
  else x.prev j

/-- `expected_next[j]` of `HmsgDecompLimb { limb_idx = l }`: the remaining-step counts
    `3 - d_r` packed two bits per chain, and the running digit sum. -/
def stepHmsgDecompExpected (x : StepOpRowInputs) (l j : Nat) : Goldilocks :=
  if j = stAccOrU1 then
    x.prev stAccOrU1 +ₚ stepPlainSum x.aux (if l < 4 then 31 else 4)
  else
    (List.range (if l < 4 then 31 else 4)).foldl
      (fun acc i =>
        if stRemPack + wotsPackSlot (31 * l + i) = j then
          acc +ₚ ((‹3› -ₚ x.aux i) *ₚ
            ‹2 ^ (2 * (31 * l + i - wotsPackSlotStart (wotsPackSlot (31 * l + i))))›)
        else acc)
      (x.prev j)

/-- Second sponge block of a 2-block Merkle node: `st_in = sub_sponge + [node, 1, IV, 0, ..]`. -/
def stepMerkleBlockBInput (x : StepOpRowInputs) : List Goldilocks :=
  (List.range 4).map (fun i => x.stIn i -ₚ (x.prev (stSubSponge + i) +ₚ x.prev (stWork + i))) ++
  [x.stIn 4 -ₚ (x.prev (stSubSponge + 4) +ₚ Goldilocks.one),
   x.stIn 5 -ₚ (x.prev (stSubSponge + 5) +ₚ poseidon2IvTag)] ++
  (List.range 6).map (fun i => x.stIn (6 + i) -ₚ x.prev (stSubSponge + 6 + i))

/-- First sponge block of a 2-block Merkle node with direction bit `aux[0]`, parent index
    `aux[1]`, sibling `aux[2..6]` and address limb `meta0`. -/
def stepMerkleBlockA (x : StepOpRowInputs) (domainTag meta0 : Goldilocks) : List Goldilocks :=
  [stepBoolCheck (x.aux 0), x.prev stCursorIdx -ₚ ((x.aux 0 +ₚ x.aux 1) +ₚ x.aux 1)] ++
  (List.range 4).flatMap (fun i =>
    [x.stIn i -ₚ x.pkSeed i,
     x.stIn (4 + i) -ₚ
       (((Goldilocks.one -ₚ x.aux 0) *ₚ x.prev (stWork + i)) +ₚ (x.aux 0 *ₚ x.aux (2 + i))),
     x.next (stWork + i) -ₚ
       ((x.aux 0 *ₚ x.prev (stWork + i)) +ₚ ((Goldilocks.one -ₚ x.aux 0) *ₚ x.aux (2 + i)))]) ++
  [x.stIn 8 -ₚ domainTag, x.stIn 9 -ₚ meta0, x.stIn 10 -ₚ x.prev stTreeLo,
   x.stIn 11 -ₚ x.prev stTreeHi] ++
  stepNextIsPerm x stSubSponge 12 ++
  [x.next stCursorIdx -ₚ x.aux 1] ++
  stepCarryUnchanged x
    (fun j => stepInBlock stSubSponge 12 j || stepInBlock stWork 4 j || j == stCursorIdx)

/-- Absorb `st_in = main_sponge + [blockA, blockB, 0]`. -/
def stepSpongeAbsorbInput (x : StepOpRowInputs) (blockA blockB : Nat → Goldilocks) :
    List Goldilocks :=
  (List.range 4).flatMap (fun i =>
    [x.stIn i -ₚ (x.prev (stMainSponge + i) +ₚ blockA i),
     x.stIn (4 + i) -ₚ (x.prev (stMainSponge + 4 + i) +ₚ blockB i),
     x.stIn (8 + i) -ₚ x.prev (stMainSponge + 8 + i)])

/-- Final squeeze `st_in = main_sponge + [1, 0, ..]`. -/
def stepSqueezeInput (x : StepOpRowInputs) : List Goldilocks :=
  [x.stIn 0 -ₚ (x.prev stMainSponge +ₚ Goldilocks.one)] ++
  (List.range 11).map (fun i => x.stIn (1 + i) -ₚ x.prev (stMainSponge + 1 + i))

/-- One WOTS+C chain step hashing `cur` under the address limb `step_c0 + kp_idx * 2^16`. -/
def stepWotsStepInput (x : StepOpRowInputs) (c0 : Goldilocks) : List Goldilocks :=
  [x.stIn 8 -ₚ domainWotsStep, x.stIn 9 -ₚ (c0 +ₚ (x.prev stKpIdx *ₚ ‹2 ^ 16›)),
   x.stIn 10 -ₚ x.prev stTreeLo, x.stIn 11 -ₚ x.prev stTreeHi]

/-- `eval_single_op_constraints_generic`: the transition constraints of one opcode class, in
    emission order. Every entry has degree at most 7 in the row cells. -/
def stepOpConstraints (kind : StepConstraintKind) (c0 : Goldilocks) (x : StepOpRowInputs) :
    List Goldilocks :=
  match kind with
  | .idle => (List.range 44).map x.next
  | .statefulHmsgBlock0 =>
    (List.range 6).map (fun i => stepBoolCheck (x.aux i)) ++
    (List.range 32).map (fun i => stepBoolCheck (x.aux (6 + i))) ++
    (List.range 4).flatMap (fun i =>
      [x.stIn i -ₚ x.pkSeed i, x.stIn (4 + i) -ₚ x.pkRoot i,
       x.next (stCurRoot + i) -ₚ x.pkRoot i]) ++
    [x.stIn 8 -ₚ domainHMsgStateful,
     x.stIn 9 -ₚ ((stepWeightedSum x.aux (fun i => 2 ^ i) 6 *ₚ ‹2 ^ 32›) +ₚ
       stepWeightedSum (fun i => x.aux (6 + i)) (fun i => 2 ^ i) 32),
     x.stIn 10 -ₚ x.mu 4, x.stIn 11 -ₚ poseidon2IvTag,
     x.next stKpIdx -ₚ stepWeightedSum x.aux (fun i => 2 ^ i) 6] ++
    stepNextIsPerm x stMainSponge 12 ++
    stepZeroElsewhere x
      (fun j => stepInBlock stCurRoot 4 j || j == stKpIdx || stepInBlock stMainSponge 12 j)
  | .statefulHmsgBlock1 =>
    stepSpongeAbsorbInput x x.aux x.mu ++
    stepNextIsPerm x stMainSponge 12 ++
    stepCarryUnchanged x (fun j => stepInBlock stMainSponge 12 j)
  | .statefulHmsgSqueeze =>
    stepSqueezeInput x ++
    stepNextIsPerm x stMainSponge 12 ++
    (List.range 6).map (fun s => x.next (stRemPack + s)) ++
    [x.next stAccOrU1] ++
    stepCarryUnchanged x
      (fun j => stepInBlock stRemPack 6 j || stepInBlock stMainSponge 12 j || j == stAccOrU1)
  | .statelessDeriveBlock0 =>
    (List.range 4).flatMap (fun i => [x.stIn i -ₚ x.pkSeed i, x.stIn (4 + i) -ₚ x.pkRoot i]) ++
    [x.stIn 8 -ₚ domainHMsgStateless, x.stIn 9 -ₚ x.mu 4, x.stIn 10,
     x.stIn 11 -ₚ poseidon2IvTag] ++
    stepNextIsPerm x stMainSponge 12 ++
    stepZeroElsewhere x (fun j => stepInBlock stMainSponge 12 j)
  | .statelessDeriveBlock1 =>
    stepSpongeAbsorbInput x x.aux x.mu ++
    stepNextIsPerm x stMainSponge 12 ++
    (List.range 6).map (fun s => x.next (stRemPack + s)) ++
    stepCarryUnchanged x (fun j => stepInBlock stMainSponge 12 j || stepInBlock stRemPack 6 j)
  | .statelessDecompLimb l =>
    stepLimb63Decomp x l ++
    (List.range 44).map (fun j => x.next j -ₚ stepStatelessDecompExpected x l j)
  | .forsRootsSpongeInit =>
    (List.range 4).map (fun i => x.stIn i -ₚ x.pkSeed i) ++
    [x.stIn 4 -ₚ x.prev stKpIdx, x.stIn 5 -ₚ x.prev stTreeLo, x.stIn 6 -ₚ x.prev stTreeHi,
     x.stIn 7 -ₚ ‹32›, x.stIn 8 -ₚ domainForsRoots, x.stIn 9, x.stIn 10,
     x.stIn 11 -ₚ poseidon2IvTag] ++
    stepNextIsPerm x stMainSponge 12 ++
    stepCarryUnchanged x (fun j => stepInBlock stMainSponge 12 j)
  | .forsLeafHash slot =>
    (List.range 4).map (fun k => quarticBase4 (x.aux (4 + k))) ++
    [x.prev (stRemPack + slot) -ₚ
       (stepWeightedSum (fun k => x.aux (4 + k)) (fun k => 4 ^ k) 4 +ₚ (x.aux 8 *ₚ ‹256›)),
     x.next (stRemPack + slot) -ₚ x.aux 8] ++
    (List.range 4).flatMap (fun i =>
      [x.stIn i -ₚ x.aux i, x.stIn (4 + i) -ₚ x.pkSeed i,
       x.next (stWork + i) -ₚ (x.permOut i +ₚ x.aux i)]) ++
    [x.stIn 8 -ₚ domainForsLeaf,
     x.stIn 9 -ₚ ((x.prev stKpIdx *ₚ ‹2 ^ 24›) +ₚ
       (c0 +ₚ stepWeightedSum (fun k => x.aux (4 + k)) (fun k => 4 ^ k) 4)),
     x.stIn 10 -ₚ x.prev stTreeLo, x.stIn 11 -ₚ x.prev stTreeHi,
     x.next stCursorIdx -ₚ stepWeightedSum (fun k => x.aux (4 + k)) (fun k => 4 ^ k) 4] ++
    stepCarryUnchanged x
      (fun j => j == stRemPack + slot || stepInBlock stWork 4 j || j == stCursorIdx)
  | .forsMerkleBlockA =>
    stepMerkleBlockA x domainForsNode ((c0 +ₚ (x.prev stKpIdx *ₚ ‹2 ^ 16›)) +ₚ x.aux 1)
  | .forsMerkleBlockB isTreeLast isOddTree =>
    stepMerkleBlockBInput x ++
    (if isTreeLast then [x.prev stCursorIdx] else []) ++
    (if isTreeLast && !isOddTree then
      stepNextIsPerm x stCurRoot 4 ++ stepCarryUnchanged x (fun j => stepInBlock stCurRoot 4 j)
     else
      stepNextIsPerm x stWork 4 ++ stepCarryUnchanged x (fun j => stepInBlock stWork 4 j))
  | .forsRootsPairAbsorb isLastPair =>
    (if isLastPair then (List.range 6).map (fun s => x.prev (stRemPack + s)) else []) ++
    stepSpongeAbsorbInput x (fun i => x.prev (stCurRoot + i)) (fun i => x.prev (stWork + i)) ++
    stepNextIsPerm x stMainSponge 12 ++
    stepCarryUnchanged x (fun j => stepInBlock stMainSponge 12 j)
  | .forsRootsFinalSqueeze =>
    stepSqueezeInput x ++
    stepNextIsPerm x stCurRoot 4 ++
    stepCarryUnchanged x (fun j => stepInBlock stCurRoot 4 j)
  | .detTreeHmsgBlock0 =>
    (List.range 4).flatMap (fun i => [x.stIn i -ₚ x.pkSeed i, x.stIn (4 + i) -ₚ x.pkRoot i]) ++
    [x.stIn 8 -ₚ domainHMsgDetTree, x.stIn 9 -ₚ (c0 +ₚ x.prev stKpIdx),
     x.stIn 10 -ₚ x.prev stTreeLo, x.stIn 11 -ₚ x.prev stTreeHi] ++
    stepNextIsPerm x stMainSponge 12 ++
    stepCarryUnchanged x (fun j => stepInBlock stMainSponge 12 j)
  | .detTreeHmsgBlock1 =>
    (List.range 32).map (fun i => stepBoolCheck (x.aux i)) ++
    (List.range 4).map (fun i =>
      x.stIn i -ₚ (x.prev (stMainSponge + i) +ₚ x.prev (stCurRoot + i))) ++
    [x.stIn 4 -ₚ (x.prev (stMainSponge + 4) +ₚ stepWeightedSum x.aux (fun i => 2 ^ i) 32),
     x.stIn 5 -ₚ (x.prev (stMainSponge + 5) +ₚ Goldilocks.one)] ++
    (List.range 6).map (fun i => x.stIn (6 + i) -ₚ x.prev (stMainSponge + 6 + i)) ++
    stepNextIsPerm x stMainSponge 12 ++
    (List.range 6).map (fun s => x.next (stRemPack + s)) ++
    [x.next stAccOrU1] ++
    stepCarryUnchanged x
      (fun j => stepInBlock stRemPack 6 j || stepInBlock stMainSponge 12 j || j == stAccOrU1)
  | .hmsgDecompLimb l =>
    stepLimb63Decomp x l ++
    (if l = 4 then [stepHmsgDecompExpected x l stAccOrU1 -ₚ ‹192›] else []) ++
    (List.range 44).map (fun j => x.next j -ₚ stepHmsgDecompExpected x l j)
  | .wotsTellInit =>
    (List.range 4).map (fun i => x.stIn i -ₚ x.pkSeed i) ++
    [x.stIn 4 -ₚ (c0 +ₚ x.prev stKpIdx), x.stIn 5 -ₚ x.prev stTreeLo,
     x.stIn 6 -ₚ x.prev stTreeHi, x.stIn 7 -ₚ ‹128›, x.stIn 8 -ₚ domainWotsPk, x.stIn 9,
     x.stIn 10, x.stIn 11 -ₚ poseidon2IvTag] ++
    stepNextIsPerm x stMainSponge 12 ++
    stepCarryUnchanged x (fun j => stepInBlock stMainSponge 12 j)
  | .wotsChainStep0 slot =>
    [stepBoolCheck (x.aux 4), stepBoolCheck (x.aux 5), stepBoolCheck (x.aux 6),
     x.aux 5 *ₚ (Goldilocks.one -ₚ x.aux 4), x.aux 6 *ₚ (Goldilocks.one -ₚ x.aux 5),
     x.prev (stRemPack + slot) -ₚ
       ((‹3› -ₚ ((x.aux 4 +ₚ x.aux 5) +ₚ x.aux 6)) +ₚ (x.aux 7 *ₚ ‹4›)),
     x.next (stRemPack + slot) -ₚ x.aux 7] ++
    (List.range 4).flatMap (fun i =>
      [x.stIn i -ₚ x.aux i, x.stIn (4 + i) -ₚ x.pkSeed i,
       x.next (stWork + i) -ₚ
         ((x.aux 4 *ₚ x.aux i) +ₚ ((Goldilocks.one -ₚ x.aux 4) *ₚ (x.permOut i +ₚ x.aux i)))]) ++
    stepWotsStepInput x c0 ++
    [x.next stAccOrU1 -ₚ x.aux 5, x.next stWotsU2 -ₚ x.aux 6] ++
    stepCarryUnchanged x
      (fun j => j == stRemPack + slot || stepInBlock stWork 4 j || j == stAccOrU1 ||
        j == stWotsU2)
  | .wotsChainStep1 =>
    (List.range 4).flatMap (fun i =>
      [x.stIn i -ₚ x.prev (stWork + i), x.stIn (4 + i) -ₚ x.pkSeed i,
       x.next (stWork + i) -ₚ
         ((x.prev stAccOrU1 *ₚ x.prev (stWork + i)) +ₚ
           ((Goldilocks.one -ₚ x.prev stAccOrU1) *ₚ (x.permOut i +ₚ x.prev (stWork + i))))]) ++
    stepWotsStepInput x c0 ++
    stepCarryUnchanged x (fun j => stepInBlock stWork 4 j)
  | .wotsChainStep2 isOdd =>
    (List.range 4).flatMap (fun i =>
      [x.stIn i -ₚ x.prev (stWork + i), x.stIn (4 + i) -ₚ x.pkSeed i,
       x.next ((if isOdd then stWork else stSubSponge) + i) -ₚ
         ((x.prev stWotsU2 *ₚ x.prev (stWork + i)) +ₚ
           ((Goldilocks.one -ₚ x.prev stWotsU2) *ₚ (x.permOut i +ₚ x.prev (stWork + i))))]) ++
    stepWotsStepInput x c0 ++
    stepCarryUnchanged x (fun j => stepInBlock (if isOdd then stWork else stSubSponge) 4 j)
  | .wotsTellPairAbsorb isLastPair =>
    (if isLastPair then (List.range 5).map (fun s => x.prev (stRemPack + s)) else []) ++
    stepSpongeAbsorbInput x (fun i => x.prev (stSubSponge + i)) (fun i => x.prev (stWork + i)) ++
    stepNextIsPerm x stMainSponge 12 ++
    stepCarryUnchanged x (fun j => stepInBlock stMainSponge 12 j)
  | .wotsTellFinalSqueeze =>
    stepSqueezeInput x ++
    stepNextIsPerm x stWork 4 ++
    [x.next stCursorIdx -ₚ x.prev stKpIdx] ++
    stepCarryUnchanged x (fun j => stepInBlock stWork 4 j || j == stCursorIdx)
  | .xmssMerkleBlockA =>
    stepMerkleBlockA x domainMerkleNode (c0 +ₚ x.aux 1)
  | .xmssMerkleBlockB isLayerLast isTopFinal =>
    stepMerkleBlockBInput x ++
    (if !isLayerLast then
      stepNextIsPerm x stWork 4 ++ stepCarryUnchanged x (fun j => stepInBlock stWork 4 j)
     else if isTopFinal then
      [x.prev stCursorIdx] ++
      (List.range 4).map (fun i => x.permOut i -ₚ x.pkRoot i) ++
      (List.range 44).map x.next
     else
      [x.prev stCursorIdx] ++
      (List.range 4).map (fun i => stepBoolCheck (x.aux i)) ++
      (List.range 14).map (fun i => quarticBase4 (x.aux (4 + i))) ++
      (List.range 2).map (fun i => quarticBase4 (x.aux (18 + i))) ++
      (List.range 14).map (fun i => quarticBase4 (x.aux (20 + i))) ++
      [x.prev stTreeLo -ₚ
         (stepWeightedSum x.aux (fun i => 2 ^ i) 4 +ₚ
           (stepWeightedSum (fun i => x.aux (4 + i)) (fun i => 4 ^ i) 14 *ₚ ‹16›)),
       x.prev stTreeHi -ₚ
         (stepWeightedSum (fun i => x.aux (18 + i)) (fun i => 4 ^ i) 2 +ₚ
           (stepWeightedSum (fun i => x.aux (20 + i)) (fun i => 4 ^ i) 14 *ₚ ‹16›))] ++
      stepNextIsPerm x stCurRoot 4 ++
      [x.next stKpIdx -ₚ stepWeightedSum x.aux (fun i => 2 ^ i) 4,
       x.next stTreeLo -ₚ
         (stepWeightedSum (fun i => x.aux (4 + i)) (fun i => 4 ^ i) 14 +ₚ
           (stepWeightedSum (fun i => x.aux (18 + i)) (fun i => 4 ^ i) 2 *ₚ ‹2 ^ 28›)),
       x.next stTreeHi -ₚ stepWeightedSum (fun i => x.aux (20 + i)) (fun i => 4 ^ i) 14] ++
      stepCarryUnchanged x
        (fun j => stepInBlock stCurRoot 4 j || j == stKpIdx || j == stTreeLo || j == stTreeHi))

/-- Group A (`eval_group_a_and_boundaries_generic`): the recomputed `Poseidon2` output of the
    row and the 118 S-box residuals `(lane + rc)^7 - sbox_out`, each of degree 7. -/
def stepOpPermTrace (row : StepOpRow) : Poseidon2State12 × List Goldilocks :=
  let r1 := extRoundsResiduals poseidon2InitialExtConsts (applyME row.stIn) row.initExtSbox
  let r2 := intRoundsResiduals poseidon2InternalConsts r1.1 row.intSbox
  let r3 := extRoundsResiduals poseidon2TerminalExtConsts r2.1 row.termExtSbox
  (r3.1, r1.2 ++ r2.2 ++ r3.2)

/-- **Group A exactness.** If the S-box residuals of a row vanish, its recomputed permutation
    output is `poseidon2Perm12` of its `COL_ST_IN` block. -/
theorem stepOp256_groupA_exact (row : StepOpRow)
    (h : allZeroGoldilocks (stepOpPermTrace row).2 = true) :
    (stepOpPermTrace row).1 = poseidon2Perm12 row.stIn := by
  have hKey : poseidon2PermResiduals
      { input := row.stIn, initExtSbox := row.initExtSbox, intSbox := row.intSbox,
        termExtSbox := row.termExtSbox, output := (stepOpPermTrace row).1 } =
      (stepOpPermTrace row).2 ++
        (state12Sub (stepOpPermTrace row).1 (stepOpPermTrace row).1).toList := rfl
  have hZ : allZeroGoldilocks (poseidon2PermResiduals
      { input := row.stIn, initExtSbox := row.initExtSbox, intSbox := row.intSbox,
        termExtSbox := row.termExtSbox, output := (stepOpPermTrace row).1 }) = true := by
    rw [hKey, allZeroGoldilocks_append, Bool.and_eq_true]
    exact ⟨h, (state12Sub_toList_allZero_iff _ _).mpr rfl⟩
  exact poseidon2PermResiduals_output_eq hZ

/-- Boundary constraints of row `t` of a signer block of `rowsPerSigner` rows: the first row
    has `prev = 0` and the last row has `next = 0`, for active and inactive slots alike. -/
def stepOpBoundaryResiduals (rowsPerSigner t : Nat) (row : StepOpRow) : List Goldilocks :=
  (List.range 44).flatMap fun j =>
    [if t = 0 then row.prevState.getD j Goldilocks.zero else Goldilocks.zero,
     if t + 1 = rowsPerSigner then row.nextState.getD j Goldilocks.zero else Goldilocks.zero]

/-- Public inputs of one signer slot `(pk, mu)`; `none` is an inactive (blinding) slot, whose
    opcode selectors are all gated off. -/
abbrev StepOpSlot : Type := Option (AggValidatorPk × Digest5)

/-- The values the opcode constraints of a row read. -/
def stepOpRowInputs (pub : AggValidatorPk × Digest5) (row : StepOpRow) : StepOpRowInputs where
  prev    := fun j => row.prevState.getD j Goldilocks.zero
  next    := fun j => row.nextState.getD j Goldilocks.zero
  aux     := fun i => row.aux.getD i Goldilocks.zero
  stIn    := fun i => row.stIn.toList.getD i Goldilocks.zero
  permOut := fun i => (stepOpPermTrace row).1.toList.getD i Goldilocks.zero
  pkSeed  := fun i => pub.1.pkSeed.toList.getD i Goldilocks.zero
  pkRoot  := fun i => pub.1.pkRoot.toList.getD i Goldilocks.zero
  mu      := fun i =>
    [pub.2.limb0, pub.2.limb1, pub.2.limb2, pub.2.limb3, pub.2.limb4].getD i Goldilocks.zero

/-- All intra-row constraints of row `t` of a signer block: Group A, the boundary constraints,
    and, for an active slot, the transition constraints of the opcode scheduled at `t`. -/
def stepOp256RowResiduals (profile : AggSigProfile) (slot : StepOpSlot) (t : Nat)
    (row : StepOpRow) : List Goldilocks :=
  (stepOpPermTrace row).2 ++
  stepOpBoundaryResiduals (stepOpRowsPerSigner profile) t row ++
  match slot with
  | none => []
  | some pub =>
    stepOpConstraints (stepOpKindAndC0 ((buildSignerProgram profile).getD t StepOp.idle)).1
      (Goldilocks.ofNat (stepOpKindAndC0 ((buildSignerProgram profile).getD t StepOp.idle)).2)
      (stepOpRowInputs pub row)

/-- Intra-row constraints of the rows from global index `g` on: row `g` belongs to slot
    `g / rows_per_signer` at step `g % rows_per_signer`. -/
def stepOp256IntraResidualsFrom (profile : AggSigProfile) (slots : List StepOpSlot) :
    Nat → List StepOpRow → List Goldilocks
  | _, [] => []
  | g, row :: rest =>
    stepOp256RowResiduals profile (slots.getD (g / stepOpRowsPerSigner profile) none)
      (g % stepOpRowsPerSigner profile) row ++
    stepOp256IntraResidualsFrom profile slots (g + 1) rest

/-- Inter-row shift constraints between two consecutive rows: `NEXT_STATE` of the first equals
    `PREV_STATE` of the second, limb by limb. They are not gated by any selector. -/
def stepOpShiftResiduals (row rowNext : StepOpRow) : List Goldilocks :=
  (List.range 44).map fun j =>
    row.nextState.getD j Goldilocks.zero -ₚ rowNext.prevState.getD j Goldilocks.zero

/-- Inter-row shift constraints of a table: one block per `r` with `r + 1 < T`. -/
def stepOp256ShiftResiduals : List StepOpRow → List Goldilocks
  | r :: r' :: rest => stepOpShiftResiduals r r' ++ stepOp256ShiftResiduals (r' :: rest)
  | _ => []

/-- A table of `slots.length * rows_per_signer` well-shaped rows on which every intra-row
    constraint and every inter-row shift constraint vanishes. -/
def stepOp256TableOk (profile : AggSigProfile) (slots : List StepOpSlot)
    (rows : List StepOpRow) : Bool :=
  decide (0 < slots.length) &&
  decide (rows.length = slots.length * stepOpRowsPerSigner profile) &&
  rows.all StepOpRow.wellShaped &&
  allZeroGoldilocks (stepOp256IntraResidualsFrom profile slots 0 rows) &&
  allZeroGoldilocks (stepOp256ShiftResiduals rows)

/-- Project an intra-row constraint block from the flat residual stream. -/
theorem stepOp256IntraResidualsFrom_row_at (profile : AggSigProfile) (slots : List StepOpSlot) :
    ∀ (rows : List StepOpRow) (g i : Nat) (row : StepOpRow),
      rows[i]? = some row →
      allZeroGoldilocks (stepOp256IntraResidualsFrom profile slots g rows) = true →
      allZeroGoldilocks (stepOp256RowResiduals profile
        (slots.getD ((g + i) / stepOpRowsPerSigner profile) none)
        ((g + i) % stepOpRowsPerSigner profile) row) = true
  | [], _, _, _, h, _ => by simp at h
  | r :: rs, g, 0, row, h, hz => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst row
    rw [stepOp256IntraResidualsFrom, allZeroGoldilocks_append, Bool.and_eq_true] at hz
    simpa only [Nat.add_zero] using hz.1
  | r :: rs, g, i + 1, row, h, hz => by
    rw [stepOp256IntraResidualsFrom, allZeroGoldilocks_append, Bool.and_eq_true] at hz
    have hr := stepOp256IntraResidualsFrom_row_at profile slots rs (g + 1) i row h hz.2
    simpa only [Nat.add_right_comm g 1 i, Nat.add_assoc] using hr

/-- Every row of a valid table satisfies its actual scheduled constraint block. -/
theorem stepOp256TableOk_row_at (profile : AggSigProfile) (slots : List StepOpSlot)
    (rows : List StepOpRow) (i : Nat) (row : StepOpRow)
    (h : stepOp256TableOk profile slots rows = true) (hi : rows[i]? = some row) :
    allZeroGoldilocks (stepOp256RowResiduals profile
      (slots.getD (i / stepOpRowsPerSigner profile) none)
      (i % stepOpRowsPerSigner profile) row) = true := by
  unfold stepOp256TableOk at h
  simp only [Bool.and_eq_true] at h
  simpa only [Nat.zero_add] using
    stepOp256IntraResidualsFrom_row_at profile slots rows 0 i row hi h.1.2

/-- The shift constraints between two rows vanish exactly when the state is handed over. -/
theorem stepOp256_shift_iff (r r' : StepOpRow) :
    allZeroGoldilocks (stepOpShiftResiduals r r') = true ↔
      ∀ j, j < 44 →
        r.nextState.getD j Goldilocks.zero = r'.prevState.getD j Goldilocks.zero := by
  unfold stepOpShiftResiduals allZeroGoldilocks
  rw [List.all_map, List.all_eq_true]
  constructor
  · intro h j hj
    exact (sub_eq_zero_iff_goldilocks _ _).mp (h j (List.mem_range.mpr hj))
  · intro h j hj
    exact (sub_eq_zero_iff_goldilocks _ _).mpr (h j (List.mem_range.mp hj))

/-- On a table whose shift constraints vanish, every pair of consecutive rows hands over its
    44 state limbs. -/
theorem stepOp256_shift_links_rows :
    ∀ (rows : List StepOpRow) (g : Nat) (r r' : StepOpRow),
      rows[g]? = some r → rows[g + 1]? = some r' →
      allZeroGoldilocks (stepOp256ShiftResiduals rows) = true →
      ∀ j, j < 44 →
        r.nextState.getD j Goldilocks.zero = r'.prevState.getD j Goldilocks.zero
  | [], _, _, _, h, _, _ => absurd h (by simp)
  | [_], _, _, _, _, h', _ => absurd h' (by simp)
  | r0 :: r1 :: rest, 0, r, r', h, h', hz => by
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h h'
    subst h h'
    unfold stepOp256ShiftResiduals at hz
    rw [allZeroGoldilocks_append, Bool.and_eq_true] at hz
    exact (stepOp256_shift_iff r0 r1).mp hz.1
  | r0 :: r1 :: rest, g + 1, r, r', h, h', hz => by
    simp only [List.getElem?_cons_succ] at h h'
    unfold stepOp256ShiftResiduals at hz
    rw [allZeroGoldilocks_append, Bool.and_eq_true] at hz
    exact stepOp256_shift_links_rows (r1 :: rest) g r r' h h' hz.2

/-- Pointwise completeness as well as soundness of the intra-row residual stream.
    The offset is retained so this also applies to a block inside a larger table. -/
theorem stepOp256IntraResidualsFrom_iff (profile : AggSigProfile) (slots : List StepOpSlot) :
    ∀ (rows : List StepOpRow) (g : Nat),
      allZeroGoldilocks (stepOp256IntraResidualsFrom profile slots g rows) = true ↔
      ∀ (i : Nat) (row : StepOpRow), rows[i]? = some row →
        allZeroGoldilocks (stepOp256RowResiduals profile
          (slots.getD ((g + i) / stepOpRowsPerSigner profile) none)
          ((g + i) % stepOpRowsPerSigner profile) row) = true
  | [], _ => by simp [stepOp256IntraResidualsFrom, allZeroGoldilocks]
  | r :: rs, g => by
    constructor
    · exact fun h i row hi => stepOp256IntraResidualsFrom_row_at profile slots _ g i row hi h
    · intro h
      rw [stepOp256IntraResidualsFrom, allZeroGoldilocks_append, Bool.and_eq_true]
      refine ⟨?_, (stepOp256IntraResidualsFrom_iff profile slots rs (g + 1)).mpr ?_⟩
      · simpa only [Nat.add_zero] using h 0 r rfl
      · intro i row hi
        have hr := h (i + 1) row (by simpa only [List.getElem?_cons_succ] using hi)
        simpa only [Nat.add_right_comm g 1 i, Nat.add_assoc] using hr

/-- The entire shift stream vanishes exactly when every adjacent pair hands over all
    44 limbs. This converse permits constructing tables from executions, including
    transitions across signer-block boundaries. -/
theorem stepOp256ShiftResiduals_iff :
    ∀ (rows : List StepOpRow),
      allZeroGoldilocks (stepOp256ShiftResiduals rows) = true ↔
      ∀ (i : Nat) (r r' : StepOpRow), rows[i]? = some r → rows[i + 1]? = some r' →
        ∀ j < 44, r.nextState.getD j Goldilocks.zero = r'.prevState.getD j Goldilocks.zero
  | [] => by simp [stepOp256ShiftResiduals, allZeroGoldilocks]
  | [r] => by simp [stepOp256ShiftResiduals, allZeroGoldilocks]
  | r :: r' :: rest => by
    constructor
    · exact fun h i a b ha hb => stepOp256_shift_links_rows _ i a b ha hb h
    · intro h
      rw [stepOp256ShiftResiduals, allZeroGoldilocks_append, Bool.and_eq_true]
      refine ⟨(stepOp256_shift_iff r r').mpr (h 0 r r' rfl rfl),
        (stepOp256ShiftResiduals_iff (r' :: rest)).mpr ?_⟩
      intro i a b ha hb
      exact h (i + 1) a b ha hb

/-- Both boundary gates are necessary and sufficient; no condition is imposed on an
    interior row by the boundary residuals. -/
theorem stepOpBoundaryResiduals_iff (rowsPerSigner t : Nat) (row : StepOpRow) :
    allZeroGoldilocks (stepOpBoundaryResiduals rowsPerSigner t row) = true ↔
      (∀ j < 44, t = 0 → row.prevState.getD j Goldilocks.zero = Goldilocks.zero) ∧
      (∀ j < 44, t + 1 = rowsPerSigner →
        row.nextState.getD j Goldilocks.zero = Goldilocks.zero) := by
  unfold stepOpBoundaryResiduals allZeroGoldilocks
  simp only [List.all_flatMap, List.all_eq_true, List.mem_range, List.all_cons,
    List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq]
  by_cases hFirst : t = 0 <;> by_cases hLast : t + 1 = rowsPerSigner <;>
    simp [hFirst, hLast, forall_and]

/-- A pointwise interface to the original 256-column table checker. All actual rows,
    including active slots, must satisfy their scheduled gate, and all adjacent rows
    must agree. Neither a signature-verifier premise nor a surrogate table is used. -/
theorem stepOp256TableOk_iff_rows (profile : AggSigProfile) (slots : List StepOpSlot)
    (rows : List StepOpRow) :
    stepOp256TableOk profile slots rows = true ↔
      0 < slots.length ∧
      rows.length = slots.length * stepOpRowsPerSigner profile ∧
      (∀ row ∈ rows, row.wellShaped = true) ∧
      (∀ (i : Nat) (row : StepOpRow), rows[i]? = some row →
        allZeroGoldilocks (stepOp256RowResiduals profile
          (slots.getD (i / stepOpRowsPerSigner profile) none)
          (i % stepOpRowsPerSigner profile) row) = true) ∧
      (∀ (i : Nat) (r r' : StepOpRow), rows[i]? = some r → rows[i + 1]? = some r' →
        ∀ j < 44, r.nextState.getD j Goldilocks.zero = r'.prevState.getD j Goldilocks.zero) := by
  unfold stepOp256TableOk
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    stepOp256IntraResidualsFrom_iff, stepOp256ShiftResiduals_iff, Nat.zero_add, and_assoc]

/-! #### Row sumcheck claims over `GoldilocksExt4` at hypercube points -/

/-- `Σ_{v < n} f v` over `GoldilocksExt4`. -/
def sumRangeExt4 (f : Nat → GoldilocksExt4) : Nat → GoldilocksExt4
  | 0 => GoldilocksExt4.zero
  | n + 1 => CommRingOps.add (sumRangeExt4 f n) (f n)

private theorem sumRangeExt4_congr (f g : Nat → GoldilocksExt4) :
    ∀ (n : Nat), (∀ v, v < n → f v = g v) → sumRangeExt4 f n = sumRangeExt4 g n
  | 0, _ => rfl
  | n + 1, h => by
    show CommRingOps.add (sumRangeExt4 f n) (f n) = CommRingOps.add (sumRangeExt4 g n) (g n)
    rw [sumRangeExt4_congr f g n (fun v hv => h v (Nat.lt_succ_of_lt hv)), h n (Nat.lt_succ_self n)]

private theorem sumRangeExt4_kronecker (u : Nat) (F : Nat → GoldilocksExt4) :
    ∀ (n : Nat),
      sumRangeExt4
        (fun v => CommRingOps.mul (if u = v then GoldilocksExt4.one else GoldilocksExt4.zero) (F v))
        n = if u < n then F u else GoldilocksExt4.zero
  | 0 => rfl
  | n + 1 => by
    show CommRingOps.add
      (sumRangeExt4
        (fun v => CommRingOps.mul (if u = v then GoldilocksExt4.one else GoldilocksExt4.zero) (F v))
        n)
      (CommRingOps.mul (if u = n then GoldilocksExt4.one else GoldilocksExt4.zero) (F n)) = _
    rw [sumRangeExt4_kronecker u F n]
    by_cases hLt : u < n
    · have hNe : u ≠ n := Nat.ne_of_lt hLt
      have hLt' : u < n + 1 := Nat.lt_succ_of_lt hLt
      simp only [hLt, hNe, hLt', ↓reduceIte]
      exact (congrArg (CommRingOps.add (F u)) (LawfulCommRing.zero_mul (F n))).trans
        (LawfulCommRing.add_zero (F u))
    · by_cases hEq : u = n
      · subst hEq
        simp only [Nat.lt_irrefl, Nat.lt_succ_self, ↓reduceIte]
        exact (congrArg (CommRingOps.add GoldilocksExt4.zero) (LawfulCommRing.one_mul (F u))).trans
          (LawfulCommRing.zero_add (F u))
      · have hLt' : ¬ u < n + 1 := fun h => by omega
        simp only [hLt, hEq, hLt', ↓reduceIte]
        exact (congrArg (CommRingOps.add GoldilocksExt4.zero) (LawfulCommRing.zero_mul (F n))).trans
          (LawfulCommRing.add_zero GoldilocksExt4.zero)

private theorem hypercubePointExt4_length :
    ∀ (ell u : Nat), (hypercubePointExt4 ell u).length = ell
  | 0, _ => rfl
  | ell + 1, u => by
    show ((if u % 2 == 0 then GoldilocksExt4.zero else GoldilocksExt4.one) ::
      hypercubePointExt4 ell (u / 2)).length = ell + 1
    rw [List.length_cons, hypercubePointExt4_length ell (u / 2)]

/-- Row-sumcheck claim of a term weighted by the equality kernel:
    `Σ_{x ∈ {0,1}^ell} eq(tau, x) * C(x)`. -/
def stepOpEqClaimExt4 (ell : Nat) (tau : List GoldilocksExt4) (C : Nat → GoldilocksExt4) :
    GoldilocksExt4 :=
  sumRangeExt4
    (fun v => CommRingOps.mul (evalEqExt4 tau (hypercubePointExt4 ell v)) (C v)) (2 ^ ell)

/-- At a hypercube point `tau = u` the equality-kernel claim is the value of the term at row
    `u`. -/
theorem stepOpEqClaimExt4_hypercube (ell u : Nat) (hu : u < 2 ^ ell)
    (C : Nat → GoldilocksExt4) :
    stepOpEqClaimExt4 ell (hypercubePointExt4 ell u) C = C u := by
  unfold stepOpEqClaimExt4
  rw [sumRangeExt4_congr _
    (fun v => CommRingOps.mul (if u = v then GoldilocksExt4.one else GoldilocksExt4.zero) (C v))
    (2 ^ ell)
    (fun v hv => by rw [evalEqExt4_hypercube_kronecker ell u v hu hv]),
    sumRangeExt4_kronecker u C (2 ^ ell)]
  simp only [hu, ↓reduceIte]

/-- Row-sumcheck claim of the inter-row shift constraint of one state limb with column
    evaluations `N` (`NEXT_STATE`) and `P` (`PREV_STATE`) on the hypercube
    (`eval_batched_row_constraints_ext4`): `Σ_x E_not_last(tau, x) * N(x) - Σ_x S_tau(x) * P(x)`. -/
def stepOpShiftClaimExt4 (ell : Nat) (tau : List GoldilocksExt4)
    (N P : Nat → GoldilocksExt4) : GoldilocksExt4 :=
  CommRingOps.sub
    (sumRangeExt4
      (fun v => CommRingOps.mul (evalEqNotLastExt4 tau (hypercubePointExt4 ell v)) (N v)) (2 ^ ell))
    (sumRangeExt4
      (fun v => CommRingOps.mul (evalShiftKernelExt4 tau (hypercubePointExt4 ell v)) (P v)) (2 ^ ell))

/-- **Inter-row shift equation over `GoldilocksExt4`.** At a hypercube point `tau = u` with
    `u + 1 < 2^ell`, the shift claim is `N(u) - P(u + 1)`: the kernels `E_not_last` and `S_tau`
    link `NEXT_STATE` of row `u` to `PREV_STATE` of row `u + 1`. -/
theorem stepOpShiftClaimExt4_hypercube (ell u : Nat) (hu : u + 1 < 2 ^ ell)
    (N P : Nat → GoldilocksExt4) :
    stepOpShiftClaimExt4 ell (hypercubePointExt4 ell u) N P =
      CommRingOps.sub (N u) (P (u + 1)) := by
  have huLt : u < 2 ^ ell := Nat.lt_of_succ_lt hu
  have hLen := hypercubePointExt4_length ell u
  unfold stepOpShiftClaimExt4
  have hN : sumRangeExt4
      (fun v => CommRingOps.mul
        (evalEqNotLastExt4 (hypercubePointExt4 ell u) (hypercubePointExt4 ell v)) (N v))
      (2 ^ ell) = N u := by
    rw [sumRangeExt4_congr _
      (fun v => CommRingOps.mul (if u = v then GoldilocksExt4.one else GoldilocksExt4.zero) (N v))
      (2 ^ ell)
      (fun v hv => by
        rw [evalEqNotLastExt4_hypercube ell _ v hLen hv,
          evalEqExt4_hypercube_kronecker ell u v huLt hv]
        by_cases hLast : v + 1 = 2 ^ ell
        · have hNe : u ≠ v := fun h => by omega
          simp only [hLast, hNe, ↓reduceIte]
        · simp only [hLast, ↓reduceIte]),
      sumRangeExt4_kronecker u N (2 ^ ell)]
    simp only [huLt, ↓reduceIte]
  have hP : sumRangeExt4
      (fun v => CommRingOps.mul
        (evalShiftKernelExt4 (hypercubePointExt4 ell u) (hypercubePointExt4 ell v)) (P v))
      (2 ^ ell) = P (u + 1) := by
    rw [sumRangeExt4_congr _
      (fun v => CommRingOps.mul
        (if u + 1 = v then GoldilocksExt4.one else GoldilocksExt4.zero) (P v))
      (2 ^ ell)
      (fun v hv => by
        rw [evalShiftKernelExt4_hypercube ell _ v hLen hv]
        by_cases hv0 : v = 0
        · have hNe : u + 1 ≠ v := fun h => by omega
          rw [ite_eq_left hv0, ite_eq_right hNe]
        · have hvPred : v - 1 < 2 ^ ell := by omega
          rw [evalEqExt4_hypercube_kronecker ell u (v - 1) huLt hvPred]
          by_cases hEq : u = v - 1
          · have hEq' : u + 1 = v := by omega
            rw [ite_eq_right hv0, ite_eq_left hEq, ite_eq_left hEq']
          · have hNe' : u + 1 ≠ v := fun h => by omega
            rw [ite_eq_right hv0, ite_eq_right hEq, ite_eq_right hNe']),
      sumRangeExt4_kronecker (u + 1) P (2 ^ ell)]
    simp only [hu, ↓reduceIte]
  rw [hN, hP]

/-- Horner `gamma`-batching of a list of base-field residuals over `GoldilocksExt4`
    (`eq_acc += g_pow * res; g_pow *= gamma`): `Σ_i gamma^i * res_i`. -/
def stepOpBatchedExt4 (gamma : GoldilocksExt4) (res : List Goldilocks) : GoldilocksExt4 :=
  RoundPoly.evalCoeffs (res.map GoldilocksExt4.embedBase) gamma

private theorem stepOpBatchedExt4_zero_of_allZero (gamma : GoldilocksExt4) :
    ∀ (res : List Goldilocks), allZeroGoldilocks res = true →
      stepOpBatchedExt4 gamma res = CommRingOps.zero
  | [], _ => rfl
  | c :: rest, h => by
    unfold allZeroGoldilocks at h
    rw [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    have ih := stepOpBatchedExt4_zero_of_allZero gamma rest h.2
    unfold stepOpBatchedExt4 at ih ⊢
    rw [List.map_cons, RoundPoly.evalCoeffs_cons, ih, h.1, LawfulCommRing.mul_zero,
      GoldilocksExt4.embedBase_zero]
    exact LawfulCommRing.add_zero GoldilocksExt4.zero

private theorem exists_ne_zero_of_not_allZero :
    ∀ (l : List Goldilocks), allZeroGoldilocks l = false →
      ∃ c, c ∈ l ∧ c ≠ Goldilocks.zero
  | [], h => absurd h (by decide)
  | c :: rest, h => by
    by_cases hc : c = Goldilocks.zero
    · have hb : (Goldilocks.zero == Goldilocks.zero) = true := by decide
      have hr : allZeroGoldilocks rest = false := by
        unfold allZeroGoldilocks at h ⊢
        rw [List.all_cons, hc, hb, Bool.true_and] at h
        exact h
      obtain ⟨c', hm, hne⟩ := exists_ne_zero_of_not_allZero rest hr
      exact ⟨c', List.mem_cons_of_mem _ hm, hne⟩
    · exact ⟨c, List.mem_cons_self .., hc⟩

private theorem filter_length_le_of_imp {α : Type} (p q : α → Bool)
    (h : ∀ a, p a = true → q a = true) :
    ∀ (l : List α), (l.filter p).length ≤ (l.filter q).length
  | [] => Nat.le_refl _
  | a :: l => by
    have ih := filter_length_le_of_imp p q h l
    cases hp : p a
    · cases hq : q a
      · simp only [List.filter_cons, hp, hq, Bool.false_eq_true, ↓reduceIte]
        exact ih
      · simp only [List.filter_cons, hp, hq, Bool.false_eq_true, ↓reduceIte, List.length_cons]
        exact Nat.le_succ_of_le ih
    · have hq := h a hp
      simp only [List.filter_cons, hp, hq, ↓reduceIte, List.length_cons]
      exact Nat.succ_le_succ ih

private theorem filter_or_length_le {α : Type} (p q : α → Bool) :
    ∀ (l : List α),
      (l.filter (fun a => p a || q a)).length ≤ (l.filter p).length + (l.filter q).length
  | [] => Nat.le_refl 0
  | a :: l => by
    have ih := filter_or_length_le p q l
    cases hp : p a <;> cases hq : q a <;>
      simp only [List.filter_cons, hp, hq, Bool.or_self, Bool.or_true,
        Bool.or_false, Bool.false_eq_true, ↓reduceIte, List.length_cons] <;>
      omega

private theorem filter_eq_length_zero_of_not_mem {α : Type} [DecidableEq α] (z : α) :
    ∀ (l : List α), z ∉ l → (l.filter (fun a => decide (a = z))).length = 0
  | [], _ => rfl
  | a :: l, h => by
    have hne : a ≠ z := fun e => h (List.mem_cons.mpr (Or.inl e.symm))
    have hd : decide (a = z) = false := decide_eq_false hne
    have hl : z ∉ l := fun hm => h (List.mem_cons_of_mem _ hm)
    rw [List.filter_cons, hd]
    exact filter_eq_length_zero_of_not_mem z l hl

private theorem nodup_filter_eq_length_le_one {α : Type} [DecidableEq α] (z : α) :
    ∀ (l : List α), l.Nodup → (l.filter (fun a => decide (a = z))).length ≤ 1
  | [], _ => Nat.zero_le 1
  | a :: l, hnd => by
    have hnd' := List.nodup_cons.mp hnd
    by_cases ha : a = z
    · have h0 := filter_eq_length_zero_of_not_mem z l (ha ▸ hnd'.1)
      have hd : decide (a = z) = true := decide_eq_true ha
      rw [List.filter_cons, hd]
      exact Nat.le_of_eq (congrArg Nat.succ h0)
    · have hd : decide (a = z) = false := decide_eq_false ha
      rw [List.filter_cons, hd]
      exact nodup_filter_eq_length_le_one z l hnd'.2

/-- **Root bound for `gamma`-batching.** A coefficient list over `GoldilocksExt4` with a
    non-zero entry, read as the polynomial `Σ_i gamma^i * c_i`, vanishes on at most
    `length - 1` challenges of any duplicate-free list. -/
theorem ext4_batched_roots_le (S : List GoldilocksExt4) (hS : S.Nodup) :
    ∀ (cs : List GoldilocksExt4),
      (∃ c, c ∈ cs ∧ c ≠ CommRingOps.zero) →
      (S.filter (fun r => decide (RoundPoly.evalCoeffs cs r = CommRingOps.zero))).length ≤
        cs.length - 1
  | [], h => by
    obtain ⟨c, hc, _⟩ := h
    cases hc
  | c :: rest, h => by
    by_cases hc0 : c = CommRingOps.zero
    · obtain ⟨c', hmem, hne⟩ := h
      have hmem' : c' ∈ rest := by
        rcases List.mem_cons.mp hmem with hEq | hIn
        · exact absurd (hEq.trans hc0) hne
        · exact hIn
      have hPos : 0 < rest.length := List.length_pos_of_mem hmem'
      have ih := ext4_batched_roots_le S hS rest ⟨c', hmem', hne⟩
      have hImp : ∀ r : GoldilocksExt4,
          decide (RoundPoly.evalCoeffs (c :: rest) r = CommRingOps.zero) = true →
          (decide (r = CommRingOps.zero) ||
            decide (RoundPoly.evalCoeffs rest r = CommRingOps.zero)) = true := by
        intro r hr
        have hr' := of_decide_eq_true hr
        rw [RoundPoly.evalCoeffs_cons, hc0, LawfulCommRing.zero_add] at hr'
        rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hr' with h0 | h1
        · rw [decide_eq_true h0, Bool.true_or]
        · rw [decide_eq_true h1, Bool.or_true]
      have h1 := filter_length_le_of_imp _ _ hImp S
      have h2 := filter_or_length_le (fun r : GoldilocksExt4 => decide (r = CommRingOps.zero))
        (fun r => decide (RoundPoly.evalCoeffs rest r = CommRingOps.zero)) S
      have h3 := nodup_filter_eq_length_le_one (CommRingOps.zero : GoldilocksExt4) S hS
      rw [List.length_cons]
      omega
    · have hNe : ∃ x₀ : GoldilocksExt4,
          RoundPoly.evalCoeffs (c :: rest) x₀ ≠ CommRingOps.zero := by
        refine ⟨CommRingOps.zero, ?_⟩
        rw [RoundPoly.evalCoeffs_cons, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
        exact hc0
      have hB := RoundPoly.roots_nodup_length_le rest.length (c :: rest) S hS
        (Nat.le_of_eq (List.length_cons)) hNe
      rw [List.length_cons, Nat.add_sub_cancel]
      exact hB

/-- **Terminal soundness of the batched row sumcheck at hypercube points.** Let `res v` be the
    intra-row residuals of row `v`, batched with powers of `gamma`, and let the sumcheck claim
    be taken at the hypercube point `tau = u`.
    1. The claim equals the batched residuals of row `u`.
    2. If every residual of row `u` vanishes, the claim is zero for every `gamma`.
    3. If some residual of row `u` does not vanish, the claim is zero for at most
       `(res u).length - 1` of the challenges `gamma` in any duplicate-free list. -/
theorem stepOp256_ext4_sumcheck_sound (ell u : Nat) (hu : u < 2 ^ ell)
    (res : Nat → List Goldilocks) (S : List GoldilocksExt4) (hS : S.Nodup) :
    (∀ gamma : GoldilocksExt4,
      stepOpEqClaimExt4 ell (hypercubePointExt4 ell u)
        (fun v => stepOpBatchedExt4 gamma (res v)) = stepOpBatchedExt4 gamma (res u)) ∧
    (allZeroGoldilocks (res u) = true →
      ∀ gamma : GoldilocksExt4,
        stepOpEqClaimExt4 ell (hypercubePointExt4 ell u)
          (fun v => stepOpBatchedExt4 gamma (res v)) = CommRingOps.zero) ∧
    (allZeroGoldilocks (res u) = false →
      (S.filter (fun gamma => decide
        (stepOpEqClaimExt4 ell (hypercubePointExt4 ell u)
          (fun v => stepOpBatchedExt4 gamma (res v)) = CommRingOps.zero))).length ≤
        (res u).length - 1) := by
  have hClaim : ∀ gamma : GoldilocksExt4,
      stepOpEqClaimExt4 ell (hypercubePointExt4 ell u)
        (fun v => stepOpBatchedExt4 gamma (res v)) = stepOpBatchedExt4 gamma (res u) :=
    fun gamma => stepOpEqClaimExt4_hypercube ell u hu _
  refine ⟨hClaim, fun hZ gamma => ?_, fun hNz => ?_⟩
  · rw [hClaim gamma]
    exact stepOpBatchedExt4_zero_of_allZero gamma (res u) hZ
  · have hf : (fun gamma => decide
        (stepOpEqClaimExt4 ell (hypercubePointExt4 ell u)
          (fun v => stepOpBatchedExt4 gamma (res v)) = CommRingOps.zero)) =
        (fun gamma => decide
          (RoundPoly.evalCoeffs ((res u).map GoldilocksExt4.embedBase) gamma =
            CommRingOps.zero)) := by
      funext gamma
      rw [hClaim gamma]
      rfl
    obtain ⟨c, hc, hne⟩ := exists_ne_zero_of_not_allZero (res u) hNz
    have hB := ext4_batched_roots_le S hS ((res u).map GoldilocksExt4.embedBase)
      ⟨GoldilocksExt4.embedBase c, List.mem_map.mpr ⟨c, hc, rfl⟩,
        fun h0 => hne (GoldilocksExt4.embedBase_injective h0)⟩
    rw [hf]
    rw [List.length_map] at hB
    exact hB

/-! #### Random-`tau` root counting -/

/-- Every coordinate slice is represented by at most two coefficients. This definition also
    covers inputs of the wrong length, on which the equality kernel is zero. -/
def Ext4MultiAffine (F : List GoldilocksExt4 → GoldilocksExt4) : Prop :=
  ∀ pre post, ∃ cs : List GoldilocksExt4, cs.length ≤ 2 ∧
    ∀ r, RoundPoly.evalCoeffs cs r = F (pre ++ r :: post)

private theorem ext4MultiAffine_scale (a : GoldilocksExt4)
    {F : List GoldilocksExt4 → GoldilocksExt4} (h : Ext4MultiAffine F) :
    Ext4MultiAffine (fun xs => CommRingOps.mul a (F xs)) := by
  intro pre post
  obtain ⟨cs, hlen, he⟩ := h pre post
  exact ⟨polyScaleCoeffs a cs, by rw [polyScaleCoeffs_length]; exact hlen,
    fun r => by rw [evalCoeffs_polyScaleCoeffs, he]⟩

private theorem ext4MultiAffine_add {F G : List GoldilocksExt4 → GoldilocksExt4}
    (hf : Ext4MultiAffine F) (hg : Ext4MultiAffine G) :
    Ext4MultiAffine (fun xs => CommRingOps.add (F xs) (G xs)) := by
  intro pre post
  obtain ⟨cs, hc, ec⟩ := hf pre post
  obtain ⟨ds, hd, ed⟩ := hg pre post
  exact ⟨polyAddCoeffs cs ds, by rw [polyAddCoeffs_length]; exact Nat.max_le.mpr ⟨hc, hd⟩,
    fun r => by rw [evalCoeffs_polyAddCoeffs, ec, ed]⟩

private theorem eqFactorExt4_comm (a b : GoldilocksExt4) :
    eqFactorExt4 a b = eqFactorExt4 b a := by
  unfold eqFactorExt4
  rw [LawfulCommRing.mul_comm (CommRingOps.sub _ a), LawfulCommRing.mul_comm a b]

private theorem evalEqExt4_slice :
    ∀ (pre post rx : List GoldilocksExt4),
      ∃ cs : List GoldilocksExt4, cs.length ≤ 2 ∧
        ∀ r, RoundPoly.evalCoeffs cs r = evalEqExt4 (pre ++ r :: post) rx
  | [], post, [] => ⟨[], by decide, fun _ => rfl⟩
  | [], post, x :: xs => by
    refine ⟨polyScaleCoeffs (evalEqExt4 post xs) (eqFactorPoly x), ?_, ?_⟩
    · rw [polyScaleCoeffs_length, eqFactorPoly_length]
      exact Nat.le_refl _
    · intro r
      rw [evalCoeffs_polyScaleCoeffs, evalCoeffs_eqFactorPoly, eqFactorExt4_comm x r]
      exact LawfulCommRing.mul_comm _ _
  | _ :: _, _, [] => ⟨[], by decide, fun _ => rfl⟩
  | t :: ts, post, x :: xs => by
    obtain ⟨cs, hc, he⟩ := evalEqExt4_slice ts post xs
    refine ⟨polyScaleCoeffs (eqFactorExt4 t x) cs, ?_, ?_⟩
    · rw [polyScaleCoeffs_length]; exact hc
    · intro r
      rw [evalCoeffs_polyScaleCoeffs, he]
      rfl

/-- The actual equality-weighted row claim is multilinear in `tau`, with no restriction to
    Boolean challenges. -/
theorem stepOpEqClaimExt4_multiaffine (ell : Nat) (C : Nat → GoldilocksExt4) :
    Ext4MultiAffine (fun tau => stepOpEqClaimExt4 ell tau C) := by
  have hs : ∀ n, Ext4MultiAffine (fun tau => sumRangeExt4
      (fun v => CommRingOps.mul (evalEqExt4 tau (hypercubePointExt4 ell v)) (C v)) n) := by
    intro n
    induction n with
    | zero => exact fun _ _ => ⟨[], by decide, fun _ => rfl⟩
    | succ n ih =>
      apply ext4MultiAffine_add ih
      have h := ext4MultiAffine_scale (C n)
        (F := fun tau => evalEqExt4 tau (hypercubePointExt4 ell n))
        (fun pre post => evalEqExt4_slice pre post (hypercubePointExt4 ell n))
      simpa only [LawfulCommRing.mul_comm (C n)] using h
  exact hs (2 ^ ell)

/-- Constructive multivariate Schwartz–Zippel bound. A nonzero multilinear function of `n`
    coordinates has at most `n * |S|^(n-1)` zeros on `S^n`, for any duplicate-free challenge
    list `S`. The witness need not belong to `S^n`. -/
theorem ext4_multiaffine_roots_le (S : List GoldilocksExt4) (hS : S.Nodup) :
    ∀ (w : List GoldilocksExt4) (F : List GoldilocksExt4 → GoldilocksExt4),
      Ext4MultiAffine F → F w ≠ CommRingOps.zero →
      ((challengeVectors S w.length).filter (fun xs => decide (F xs = CommRingOps.zero))).length ≤
        w.length * S.length ^ (w.length - 1)
  | [], F, _, hn => by
    simp only [List.length_nil, challengeVectors, List.filter_cons, decide_eq_false hn,
      Bool.false_eq_true, ↓reduceIte, List.filter_nil, Nat.zero_mul]
    exact Nat.le_refl _
  | a :: w, F, hm, hn => by
    let b := fun r => decide (F (r :: w) = CommRingOps.zero)
    let M := w.length * S.length ^ (w.length - 1)
    obtain ⟨cs, hc, he⟩ := hm [] w
    have hb : (S.filter b).length ≤ 1 := by
      have hn' : ∃ x, RoundPoly.evalCoeffs cs x ≠ CommRingOps.zero :=
        ⟨a, fun hz => hn ((he a).symm.trans hz)⟩
      have hr := RoundPoly.roots_nodup_length_le 1 cs S hS hc hn'
      simpa only [he, List.nil_append] using hr
    have hEach : ∀ r ∈ S,
        (((challengeVectors S w.length).map (fun xs => r :: xs)).filter
          (fun xs => decide (F xs = CommRingOps.zero))).length ≤
            if b r = true then S.length ^ w.length else M := by
      intro r _
      rw [filter_map_length]
      by_cases hz : F (r :: w) = CommRingOps.zero
      · simp only [b, decide_eq_true hz, ↓reduceIte]
        exact Nat.le_trans (filter_length_le_self _ _) (Nat.le_of_eq (challengeVectors_length S _))
      · simp only [b, decide_eq_false hz, Bool.false_eq_true, ↓reduceIte]
        exact ext4_multiaffine_roots_le S hS w (fun xs => F (r :: xs))
          (fun pre post => hm (r :: pre) post) hz
    have hsplit := length_flatMap_le_split b (S.length ^ w.length) M _ S hEach
    have hA := Nat.mul_le_mul_right (S.length ^ w.length) hb
    have hB : S.length * M ≤ w.length * S.length ^ w.length := by
      cases w with
      | nil => simp [M]
      | cons c ws =>
        simp only [M, List.length_cons, Nat.add_sub_cancel, Nat.pow_succ]
        rw [Nat.mul_left_comm, Nat.mul_comm S.length (S.length ^ ws.length)]
        exact Nat.le_refl _
    change ((S.flatMap (fun r => (challengeVectors S w.length).map (fun xs => r :: xs))).filter
      (fun xs => decide (F xs = CommRingOps.zero))).length ≤ _
    rw [filter_flatMap_eq]
    simp only [List.length_cons, Nat.add_sub_cancel, Nat.add_mul, Nat.one_mul]
    exact Nat.le_trans hsplit (by omega)

/-- A nonzero residual on the Boolean cube gives a nonzero multilinear equality-weighted
    polynomial. Its zero fraction for uniform `tau` in `S^ell` is at most `ell / |S|`.
    Taking `S` to enumerate `GoldilocksExt4` gives the quartic-field denominator. -/
theorem stepOpEqClaimExt4_random_tau_roots_le (ell u : Nat) (hu : u < 2 ^ ell)
    (C : Nat → GoldilocksExt4) (hn : C u ≠ CommRingOps.zero)
    (S : List GoldilocksExt4) (hS : S.Nodup) :
    ((challengeVectors S ell).filter
      (fun tau => decide (stepOpEqClaimExt4 ell tau C = CommRingOps.zero))).length ≤
        ell * S.length ^ (ell - 1) := by
  have h := ext4_multiaffine_roots_le S hS (hypercubePointExt4 ell u)
    (fun tau => stepOpEqClaimExt4 ell tau C) (stepOpEqClaimExt4_multiaffine ell C)
    (fun hz => hn ((stepOpEqClaimExt4_hypercube ell u hu C).symm.trans hz))
  simpa only [hypercubePointExt4_length] using h

/-- Random-challenge lift for the existing row-residual interface. A violated row has at
    most `length - 1` cancelling `gamma` values. For every other `gamma`, at most
    `ell * |S|^(ell - 1)` choices of unrestricted `tau` make the weighted claim vanish. -/
theorem stepOp256_ext4_random_tau_sound (ell u : Nat) (hu : u < 2 ^ ell)
    (res : Nat → List Goldilocks) (hn : allZeroGoldilocks (res u) = false)
    (S : List GoldilocksExt4) (hS : S.Nodup) :
    (S.filter (fun gamma => decide (stepOpBatchedExt4 gamma (res u) =
      CommRingOps.zero))).length ≤ (res u).length - 1 ∧
    ∀ gamma, stepOpBatchedExt4 gamma (res u) ≠ CommRingOps.zero →
      ((challengeVectors S ell).filter (fun tau => decide
        (stepOpEqClaimExt4 ell tau (fun v => stepOpBatchedExt4 gamma (res v)) =
          CommRingOps.zero))).length ≤ ell * S.length ^ (ell - 1) := by
  refine ⟨?_, fun gamma hg => stepOpEqClaimExt4_random_tau_roots_le ell u hu _ hg S hS⟩
  have h := (stepOp256_ext4_sumcheck_sound ell u hu res S hS).2.2 hn
  simpa only [stepOpEqClaimExt4_hypercube ell u hu] using h

private theorem sumRangeExt4_add (f g : Nat → GoldilocksExt4) :
    ∀ n, sumRangeExt4 (fun v => CommRingOps.add (f v) (g v)) n =
      CommRingOps.add (sumRangeExt4 f n) (sumRangeExt4 g n)
  | 0 => (LawfulCommRing.add_zero _).symm
  | n + 1 => by
    simp only [sumRangeExt4, sumRangeExt4_add f g n]
    rw [LawfulCommRing.add_assoc, ← LawfulCommRing.add_assoc (sumRangeExt4 g n),
      LawfulCommRing.add_comm (sumRangeExt4 g n) (f n), LawfulCommRing.add_assoc,
      ← LawfulCommRing.add_assoc]

private theorem sumRangeExt4_scale (a : GoldilocksExt4) (f : Nat → GoldilocksExt4) :
    ∀ n, sumRangeExt4 (fun v => CommRingOps.mul a (f v)) n =
      CommRingOps.mul a (sumRangeExt4 f n)
  | 0 => (LawfulCommRing.mul_zero _).symm
  | n + 1 => by
    simp only [sumRangeExt4, sumRangeExt4_scale a f n, LawfulCommRing.left_distrib]

private theorem stepOpEqClaimExt4_add (ell : Nat) (tau : List GoldilocksExt4)
    (f g : Nat → GoldilocksExt4) :
    stepOpEqClaimExt4 ell tau (fun v => CommRingOps.add (f v) (g v)) =
      CommRingOps.add (stepOpEqClaimExt4 ell tau f) (stepOpEqClaimExt4 ell tau g) := by
  unfold stepOpEqClaimExt4
  simp only [LawfulCommRing.left_distrib, sumRangeExt4_add]

private theorem stepOpEqClaimExt4_scale (ell : Nat) (tau : List GoldilocksExt4)
    (a : GoldilocksExt4) (f : Nat → GoldilocksExt4) :
    stepOpEqClaimExt4 ell tau (fun v => CommRingOps.mul a (f v)) =
      CommRingOps.mul a (stepOpEqClaimExt4 ell tau f) := by
  unfold stepOpEqClaimExt4
  rw [← sumRangeExt4_scale]
  apply sumRangeExt4_congr
  intro v _
  rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm _ a, LawfulCommRing.mul_assoc]

/-- Fixed-order constraint columns. Selector-gated constraints occupy separate entries, so
    each entry retains its own `gamma` exponent even at rows where its selector is zero. -/
def stepOpConstraintBatchExt4 (gamma : GoldilocksExt4)
    (constraints : List (Nat → GoldilocksExt4)) (v : Nat) : GoldilocksExt4 :=
  RoundPoly.evalCoeffs (constraints.map (fun C => C v)) gamma

/-- Equality weighting commutes with fixed-order `gamma` batching at every `tau`. -/
theorem stepOpEqClaimExt4_batch (ell : Nat) (tau : List GoldilocksExt4)
    (gamma : GoldilocksExt4) :
    ∀ constraints : List (Nat → GoldilocksExt4),
      stepOpEqClaimExt4 ell tau (stepOpConstraintBatchExt4 gamma constraints) =
        RoundPoly.evalCoeffs (constraints.map (stepOpEqClaimExt4 ell tau)) gamma
  | [] => by
    have hz : ∀ n, sumRangeExt4 (fun _ => (CommRingOps.zero : GoldilocksExt4)) n =
        CommRingOps.zero := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => simp only [sumRangeExt4, ih, LawfulCommRing.add_zero]
    simp only [stepOpEqClaimExt4, stepOpConstraintBatchExt4, List.map_nil,
      RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, hz]
  | C :: cs => by
    change stepOpEqClaimExt4 ell tau
      (fun v => CommRingOps.add (C v)
        (CommRingOps.mul gamma (stepOpConstraintBatchExt4 gamma cs v))) = _
    rw [stepOpEqClaimExt4_add, stepOpEqClaimExt4_scale, stepOpEqClaimExt4_batch ell tau gamma cs]
    rfl

/-- At an arbitrary `tau`, one nonzero constraint claim gives at most `n-1` bad `gamma`
    challenges, with one distinct power per constraint column. -/
theorem stepOp256_gamma_roots_le (ell : Nat) (tau : List GoldilocksExt4)
    (constraints : List (Nat → GoldilocksExt4))
    (hn : ∃ C, C ∈ constraints ∧ stepOpEqClaimExt4 ell tau C ≠ CommRingOps.zero)
    (S : List GoldilocksExt4) (hS : S.Nodup) :
    (S.filter (fun gamma => decide
      (stepOpEqClaimExt4 ell tau (stepOpConstraintBatchExt4 gamma constraints) =
        CommRingOps.zero))).length ≤ constraints.length - 1 := by
  simp only [stepOpEqClaimExt4_batch]
  obtain ⟨C, hc, hn⟩ := hn
  have h := ext4_batched_roots_le S hS (constraints.map (stepOpEqClaimExt4 ell tau))
    ⟨stepOpEqClaimExt4 ell tau C, List.mem_map.mpr ⟨C, hc, rfl⟩, hn⟩
  simpa only [List.length_map] using h

/-- Once a `gamma` preserves a nonzero row residual, the actual batched claim has the
    multilinear Schwartz–Zippel bound for independent, unrestricted `tau` coordinates. -/
theorem stepOp256_random_tau_roots_le (ell u : Nat) (hu : u < 2 ^ ell)
    (constraints : List (Nat → GoldilocksExt4)) (gamma : GoldilocksExt4)
    (hn : stepOpConstraintBatchExt4 gamma constraints u ≠ CommRingOps.zero)
    (S : List GoldilocksExt4) (hS : S.Nodup) :
    ((challengeVectors S ell).filter (fun tau => decide
      (stepOpEqClaimExt4 ell tau (stepOpConstraintBatchExt4 gamma constraints) =
        CommRingOps.zero))).length ≤ ell * S.length ^ (ell - 1) :=
  stepOpEqClaimExt4_random_tau_roots_le ell u hu _ hn S hS

private theorem ext4MultiAffine_sub {F G : List GoldilocksExt4 → GoldilocksExt4}
    (hf : Ext4MultiAffine F) (hg : Ext4MultiAffine G) :
    Ext4MultiAffine (fun xs => CommRingOps.sub (F xs) (G xs)) := by
  have h := ext4MultiAffine_add hf (ext4MultiAffine_scale
    (CommRingOps.neg (CommRingOps.one : GoldilocksExt4)) hg)
  simpa only [LawfulCommRing.neg_mul, LawfulCommRing.one_mul,
    ← LawfulCommRing.sub_eq_add_neg] using h

private theorem evalAllOnesExt4_slice :
    ∀ (pre post rx : List GoldilocksExt4),
      ∃ cs : List GoldilocksExt4, cs.length ≤ 2 ∧
        ∀ r, RoundPoly.evalCoeffs cs r = evalAllOnesExt4 (pre ++ r :: post) rx
  | [], _, [] => ⟨[], by decide, fun _ => rfl⟩
  | [], post, x :: xs => by
    refine ⟨[CommRingOps.zero, CommRingOps.mul x (evalAllOnesExt4 post xs)],
      Nat.le_refl 2, ?_⟩
    intro r
    simp only [RoundPoly.evalCoeffs, LawfulCommRing.mul_zero, LawfulCommRing.add_zero,
      LawfulCommRing.zero_add]
    exact (LawfulCommRing.mul_assoc _ _ _).symm
  | _ :: _, _, [] => ⟨[], by decide, fun _ => rfl⟩
  | t :: ts, post, x :: xs => by
    obtain ⟨cs, hc, he⟩ := evalAllOnesExt4_slice ts post xs
    refine ⟨polyScaleCoeffs (CommRingOps.mul t x) cs, ?_, ?_⟩
    · rw [polyScaleCoeffs_length]; exact hc
    · intro r; rw [evalCoeffs_polyScaleCoeffs, he]; rfl

private theorem evalShiftKernelExt4_slice :
    ∀ (pre post rx : List GoldilocksExt4),
      ∃ cs : List GoldilocksExt4, cs.length ≤ 2 ∧
        ∀ r, RoundPoly.evalCoeffs cs r = evalShiftKernelExt4 (pre ++ r :: post) rx
  | [], _, [] => ⟨[], by decide, fun _ => rfl⟩
  | [], post, x :: xs => by
    let a := CommRingOps.mul x (evalEqExt4 post xs)
    let b := CommRingOps.mul (CommRingOps.sub GoldilocksExt4.one x)
      (evalShiftKernelExt4 post xs)
    refine ⟨affineColPoly a b, by simp [affineColPoly], ?_⟩
    intro r
    have hm : RoundPoly.evalCoeffs (affineColPoly a b) r =
        CommRingOps.add (CommRingOps.mul (CommRingOps.sub GoldilocksExt4.one r) a)
          (CommRingOps.mul r b) := by
      simp only [affineColPoly, RoundPoly.evalCoeffs, LawfulCommRing.mul_zero,
        LawfulCommRing.add_zero]
      have ho : CommRingOps.mul GoldilocksExt4.one a = a := LawfulCommRing.one_mul a
      rw [LawfulCommRing.mul_sub, LawfulCommRing.sub_mul, ho]
      simp only [LawfulCommRing.sub_eq_add_neg]
      rw [LawfulCommRing.add_assoc, LawfulCommRing.add_comm (CommRingOps.mul r b)]
    rw [hm]
    simp only [a, b, ← LawfulCommRing.mul_assoc]
    rfl
  | _ :: _, _, [] => ⟨[], by decide, fun _ => rfl⟩
  | t :: ts, post, x :: xs => by
    obtain ⟨cs, hc, he⟩ := evalEqExt4_slice ts post xs
    obtain ⟨ds, hd, ed⟩ := evalShiftKernelExt4_slice ts post xs
    let a := CommRingOps.mul (CommRingOps.sub GoldilocksExt4.one t) x
    let b := CommRingOps.mul t (CommRingOps.sub GoldilocksExt4.one x)
    refine ⟨polyAddCoeffs (polyScaleCoeffs a cs) (polyScaleCoeffs b ds), ?_, ?_⟩
    · rw [polyAddCoeffs_length, polyScaleCoeffs_length, polyScaleCoeffs_length]
      exact Nat.max_le.mpr ⟨hc, hd⟩
    · intro r
      rw [evalCoeffs_polyAddCoeffs, evalCoeffs_polyScaleCoeffs,
        evalCoeffs_polyScaleCoeffs, he, ed]
      rfl

private theorem ext4MultiAffine_sum (F : Nat → List GoldilocksExt4 → GoldilocksExt4)
    (h : ∀ v, Ext4MultiAffine (F v)) :
    ∀ n, Ext4MultiAffine (fun xs => sumRangeExt4 (fun v => F v xs) n)
  | 0 => fun _ _ => ⟨[], by decide, fun _ => rfl⟩
  | n + 1 => ext4MultiAffine_add (ext4MultiAffine_sum F h n) (h n)

/-- Both kernels in the actual inter-row claim are multilinear in `tau`. -/
theorem stepOpShiftClaimExt4_multiaffine (ell : Nat) (N P : Nat → GoldilocksExt4) :
    Ext4MultiAffine (fun tau => stepOpShiftClaimExt4 ell tau N P) := by
  apply ext4MultiAffine_sub
  · apply ext4MultiAffine_sum
    intro v
    have he : Ext4MultiAffine (fun tau => evalEqExt4 tau (hypercubePointExt4 ell v)) :=
      fun pre post => evalEqExt4_slice pre post _
    have ha : Ext4MultiAffine (fun tau => evalAllOnesExt4 tau (hypercubePointExt4 ell v)) :=
      fun pre post => evalAllOnesExt4_slice pre post _
    have h := ext4MultiAffine_scale (N v) (ext4MultiAffine_sub he ha)
    simpa only [evalEqNotLastExt4, LawfulCommRing.mul_comm (N v)] using h
  · apply ext4MultiAffine_sum
    intro v
    have hs : Ext4MultiAffine (fun tau => evalShiftKernelExt4 tau (hypercubePointExt4 ell v)) :=
      fun pre post => evalShiftKernelExt4_slice pre post _
    have h := ext4MultiAffine_scale (P v) hs
    simpa only [LawfulCommRing.mul_comm (P v)] using h

/-- A nonzero inter-row state mismatch has the same random-`tau` root bound as an intra-row
    violation, for the deployed `E_not_last` and shift kernels themselves. -/
theorem stepOpShiftClaimExt4_random_tau_roots_le (ell u : Nat) (hu : u + 1 < 2 ^ ell)
    (N P : Nat → GoldilocksExt4)
    (hn : CommRingOps.sub (N u) (P (u + 1)) ≠ CommRingOps.zero)
    (S : List GoldilocksExt4) (hS : S.Nodup) :
    ((challengeVectors S ell).filter
      (fun tau => decide (stepOpShiftClaimExt4 ell tau N P = CommRingOps.zero))).length ≤
        ell * S.length ^ (ell - 1) := by
  have h := ext4_multiaffine_roots_le S hS (hypercubePointExt4 ell u)
    (fun tau => stepOpShiftClaimExt4 ell tau N P) (stepOpShiftClaimExt4_multiaffine ell N P)
    (fun hz => hn ((stepOpShiftClaimExt4_hypercube ell u hu N P).symm.trans hz))
  simpa only [hypercubePointExt4_length] using h

/-! #### `#tooth` rows -/

private theorem getD_replicate_zero :
    ∀ (n j : Nat),
      (List.replicate n Goldilocks.zero).getD j Goldilocks.zero = Goldilocks.zero
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | n + 1, j + 1 => getD_replicate_zero n j

/-- A row whose `Poseidon2` columns are the honest trace of the all-zero input, with carried
    state `prevState`, zero `NEXT_STATE` and auxiliary cells `aux` (unconstrained on `Idle` and
    inactive rows, where `populate_inactive_signer_rows` places the blinding limbs). -/
def stepOpIdleRow (prevState aux : List Goldilocks) : StepOpRow where
  stIn        := state12Zero
  initExtSbox := (honestPoseidon2PermWitness state12Zero).initExtSbox
  intSbox     := (honestPoseidon2PermWitness state12Zero).intSbox
  termExtSbox := (honestPoseidon2PermWitness state12Zero).termExtSbox
  prevState   := prevState
  nextState   := List.replicate 44 Goldilocks.zero
  aux         := aux

/-- The all-zero row: every one of the 256 cells is zero. -/
def stepOpZeroRow : StepOpRow where
  stIn        := state12Zero
  initExtSbox := List.replicate 4 state12Zero
  intSbox     := List.replicate 22 Goldilocks.zero
  termExtSbox := List.replicate 4 state12Zero
  prevState   := List.replicate 44 Goldilocks.zero
  nextState   := List.replicate 44 Goldilocks.zero
  aux         := List.replicate 38 Goldilocks.zero

private theorem stepOpIdleRow_groupA (prevState aux : List Goldilocks) :
    allZeroGoldilocks (stepOpPermTrace (stepOpIdleRow prevState aux)).2 = true := by
  have hKey : poseidon2PermResiduals (honestPoseidon2PermWitness state12Zero) =
      (stepOpPermTrace (stepOpIdleRow prevState aux)).2 ++
        (state12Sub (stepOpPermTrace (stepOpIdleRow prevState aux)).1
          (honestPoseidon2PermWitness state12Zero).output).toList := rfl
  have hZ := (poseidon2PermResiduals_allZero_iff (honestPoseidon2PermWitness state12Zero)).mpr rfl
  rw [hKey, allZeroGoldilocks_append, Bool.and_eq_true] at hZ
  exact hZ.1

private theorem allZero_zero_pairs :
    allZeroGoldilocks
      ((List.range 44).flatMap fun _ => [Goldilocks.zero, Goldilocks.zero]) = true := by
  decide

private theorem stepOpIdleRow_boundary (rowsPerSigner t : Nat) (prevState aux : List Goldilocks)
    (hP : t = 0 → prevState = List.replicate 44 Goldilocks.zero) :
    allZeroGoldilocks (stepOpBoundaryResiduals rowsPerSigner t (stepOpIdleRow prevState aux)) =
      true := by
  have hEq : stepOpBoundaryResiduals rowsPerSigner t (stepOpIdleRow prevState aux) =
      (List.range 44).flatMap fun _ => [Goldilocks.zero, Goldilocks.zero] := by
    unfold stepOpBoundaryResiduals stepOpIdleRow
    congr 1
    funext j
    by_cases ht : t = 0
    · simp only [ht, hP ht, ↓reduceIte, getD_replicate_zero, ite_self]
    · simp only [ht, ↓reduceIte, getD_replicate_zero, ite_self]
  rw [hEq]
  exact allZero_zero_pairs

private theorem allZero_zero_map :
    allZeroGoldilocks ((List.range 44).map fun _ => Goldilocks.zero) = true := by
  decide

/-- An `Idle` row passes every intra-row gate of an active slot at any step scheduled as
    `Idle`, whatever state it claims to have received (other than on the first row). -/
theorem stepOpIdleRow_intra_ok (profile : AggSigProfile) (pub : AggValidatorPk × Digest5)
    (t : Nat) (prevState aux : List Goldilocks)
    (hOp : (buildSignerProgram profile).getD t StepOp.idle = StepOp.idle)
    (hP : t = 0 → prevState = List.replicate 44 Goldilocks.zero) :
    allZeroGoldilocks
      (stepOp256RowResiduals profile (some pub) t (stepOpIdleRow prevState aux)) = true := by
  unfold stepOp256RowResiduals
  rw [allZeroGoldilocks_append, allZeroGoldilocks_append, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨stepOpIdleRow_groupA prevState aux, stepOpIdleRow_boundary _ t prevState aux hP⟩, ?_⟩
  rw [hOp]
  have hEq : stepOpConstraints (stepOpKindAndC0 StepOp.idle).1
      (Goldilocks.ofNat (stepOpKindAndC0 StepOp.idle).2)
      (stepOpRowInputs pub (stepOpIdleRow prevState aux)) =
      (List.range 44).map fun _ => Goldilocks.zero := by
    show (List.range 44).map
      (fun j => (List.replicate 44 Goldilocks.zero).getD j Goldilocks.zero) = _
    congr 1
    funext j
    exact getD_replicate_zero 44 j
  have hZ := allZero_zero_map
  rw [← hEq] at hZ
  exact hZ

/-- **`#tooth`: a state splice breaks the shift constraint.** Take any two rows `rA`, `rB` and
    a state limb `j` on which `NEXT_STATE` of `rA` differs from `PREV_STATE` of `rB`.
    1. The inter-row shift residuals between them do not vanish.
    2. Over `GoldilocksExt4`: for column evaluations `N`, `P` whose values at rows `u`, `u + 1`
       are the two limbs, the shift claim at the hypercube point `u` is non-zero.
    3. Such a splice exists among rows that pass every intra-row gate on their own: for an
       active `xmssPoseidon2` slot and any auxiliary cells, the `Idle` rows at steps `500` and
       `501` with carried state `0` and `[1, 0, ..]` both satisfy all intra-row constraints. -/
theorem tooth_stepOp256_state_splice_breaks_shift_constraint :
    (∀ (rA rB : StepOpRow) (j : Nat), j < 44 →
      rA.nextState.getD j Goldilocks.zero ≠ rB.prevState.getD j Goldilocks.zero →
      allZeroGoldilocks (stepOpShiftResiduals rA rB) = false ∧
      ∀ (ell u : Nat), u + 1 < 2 ^ ell → ∀ (N P : Nat → GoldilocksExt4),
        N u = GoldilocksExt4.embedBase (rA.nextState.getD j Goldilocks.zero) →
        P (u + 1) = GoldilocksExt4.embedBase (rB.prevState.getD j Goldilocks.zero) →
        stepOpShiftClaimExt4 ell (hypercubePointExt4 ell u) N P ≠ CommRingOps.zero) ∧
    (∀ (pub : AggValidatorPk × Digest5) (aux : List Goldilocks),
      allZeroGoldilocks (stepOp256RowResiduals .xmssPoseidon2 (some pub) 500
        (stepOpIdleRow (List.replicate 44 Goldilocks.zero) aux)) = true ∧
      allZeroGoldilocks (stepOp256RowResiduals .xmssPoseidon2 (some pub) 501
        (stepOpIdleRow (Goldilocks.one :: List.replicate 43 Goldilocks.zero) aux)) = true ∧
      allZeroGoldilocks (stepOpShiftResiduals
        (stepOpIdleRow (List.replicate 44 Goldilocks.zero) aux)
        (stepOpIdleRow (Goldilocks.one :: List.replicate 43 Goldilocks.zero) aux)) = false) := by
  have hSplice : ∀ (rA rB : StepOpRow) (j : Nat), j < 44 →
      rA.nextState.getD j Goldilocks.zero ≠ rB.prevState.getD j Goldilocks.zero →
      allZeroGoldilocks (stepOpShiftResiduals rA rB) = false := by
    intro rA rB j hj hNe
    apply Bool.eq_false_iff.mpr
    intro hZ
    exact hNe ((stepOp256_shift_iff rA rB).mp hZ j hj)
  refine ⟨fun rA rB j hj hNe => ⟨hSplice rA rB j hj hNe, ?_⟩, fun pub aux => ⟨?_, ?_, ?_⟩⟩
  · intro ell u hu N P hN hP hZero
    rw [stepOpShiftClaimExt4_hypercube ell u hu N P, hN, hP,
      ← GoldilocksExt4.embedBase_sub] at hZero
    have h0 : Goldilocks.sub (rA.nextState.getD j Goldilocks.zero)
        (rB.prevState.getD j Goldilocks.zero) = Goldilocks.zero :=
      GoldilocksExt4.embedBase_injective hZero
    exact hNe (LawfulCommRing.sub_eq_zero_iff.mp h0)
  · exact stepOpIdleRow_intra_ok .xmssPoseidon2 pub 500 _ aux (by decide +kernel)
      (fun h => absurd h (by decide))
  · exact stepOpIdleRow_intra_ok .xmssPoseidon2 pub 501 _ aux (by decide +kernel)
      (fun h => absurd h (by decide))
  · exact hSplice _ _ 0 (by decide)
      (fun h => (by decide : Goldilocks.zero ≠ Goldilocks.one) h)

private theorem honestZeroPerm_sbox_lengths :
    (honestPoseidon2PermWitness state12Zero).initExtSbox.length = 4 ∧
    (honestPoseidon2PermWitness state12Zero).intSbox.length = 22 ∧
    (honestPoseidon2PermWitness state12Zero).termExtSbox.length = 4 := by
  decide +kernel

/-- An `Idle` row with 44 carried limbs and 38 auxiliary cells has the 256-column shape. -/
theorem stepOpIdleRow_wellShaped (prevState aux : List Goldilocks)
    (hP : prevState.length = 44) (hA : aux.length = 38) :
    (stepOpIdleRow prevState aux).wellShaped = true := by
  obtain ⟨h1, h2, h3⟩ := honestZeroPerm_sbox_lengths
  unfold StepOpRow.wellShaped stepOpIdleRow
  simp only [h1, h2, h3, hP, hA, List.length_replicate, beq_self_eq_true, Bool.and_self]

private theorem getD_replicate_none {α : Type} :
    ∀ (k i : Nat), (List.replicate k (none : Option α)).getD i none = none
  | 0, _ => rfl
  | _ + 1, 0 => rfl
  | k + 1, i + 1 => getD_replicate_none k i

private theorem all_replicate_of {α : Type} (f : α → Bool) (a : α) (h : f a = true) :
    ∀ (n : Nat), (List.replicate n a).all f = true
  | 0 => rfl
  | n + 1 => Bool.and_eq_true_iff.mpr ⟨h, all_replicate_of f a h n⟩

private theorem stepOpInactive_intra (profile : AggSigProfile) (k : Nat) (aux : List Goldilocks) :
    ∀ (n g : Nat),
      allZeroGoldilocks (stepOp256IntraResidualsFrom profile (List.replicate k none) g
        (List.replicate n (stepOpIdleRow (List.replicate 44 Goldilocks.zero) aux))) = true
  | 0, _ => rfl
  | n + 1, g => by
    show allZeroGoldilocks
      (stepOp256RowResiduals profile
          ((List.replicate k none).getD (g / stepOpRowsPerSigner profile) none)
          (g % stepOpRowsPerSigner profile)
          (stepOpIdleRow (List.replicate 44 Goldilocks.zero) aux) ++
        stepOp256IntraResidualsFrom profile (List.replicate k none) (g + 1)
          (List.replicate n (stepOpIdleRow (List.replicate 44 Goldilocks.zero) aux))) = true
    rw [allZeroGoldilocks_append, Bool.and_eq_true, getD_replicate_none]
    refine ⟨?_, stepOpInactive_intra profile k aux n (g + 1)⟩
    unfold stepOp256RowResiduals
    rw [allZeroGoldilocks_append, allZeroGoldilocks_append, Bool.and_eq_true, Bool.and_eq_true]
    exact ⟨⟨stepOpIdleRow_groupA _ aux, stepOpIdleRow_boundary _ _ _ aux (fun _ => rfl)⟩, rfl⟩

private theorem stepOpInactive_shift (aux : List Goldilocks) :
    ∀ (n : Nat),
      allZeroGoldilocks (stepOp256ShiftResiduals
        (List.replicate n (stepOpIdleRow (List.replicate 44 Goldilocks.zero) aux))) = true
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
    show allZeroGoldilocks
      (stepOpShiftResiduals (stepOpIdleRow (List.replicate 44 Goldilocks.zero) aux)
          (stepOpIdleRow (List.replicate 44 Goldilocks.zero) aux) ++
        stepOp256ShiftResiduals
          (List.replicate (n + 1) (stepOpIdleRow (List.replicate 44 Goldilocks.zero) aux))) = true
    rw [allZeroGoldilocks_append, Bool.and_eq_true]
    exact ⟨(stepOp256_shift_iff _ _).mpr (fun _ _ => rfl), stepOpInactive_shift aux (n + 1)⟩

/-- **Completeness for inactive slots (`populate_inactive_signer_rows`).** A table of `k ≥ 1`
    inactive slots filled with `Idle` rows (honest `Poseidon2` trace of the zero input, zero
    carried state, arbitrary auxiliary cells) satisfies every intra-row and inter-row
    constraint. In particular `stepOp256TableOk` is satisfiable. -/
theorem stepOp256_inactive_table_complete (profile : AggSigProfile) (k : Nat) (hk : 0 < k)
    (aux : List Goldilocks) (hA : aux.length = 38) :
    stepOp256TableOk profile (List.replicate k none)
      (List.replicate (k * stepOpRowsPerSigner profile)
        (stepOpIdleRow (List.replicate 44 Goldilocks.zero) aux)) = true := by
  unfold stepOp256TableOk
  refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
    ⟨Bool.and_eq_true_iff.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact decide_eq_true (by rw [List.length_replicate]; exact hk)
  · exact decide_eq_true (by rw [List.length_replicate, List.length_replicate])
  · exact all_replicate_of _ _
      (stepOpIdleRow_wellShaped _ aux List.length_replicate hA) _
  · exact stepOpInactive_intra profile k aux _ 0
  · exact stepOpInactive_shift aux _

private theorem stepOpZeroRow_groupA :
    allZeroGoldilocks (stepOpPermTrace stepOpZeroRow).2 = false := by
  decide +kernel

/-- **`#tooth`: all-zero rows are rejected.** For every profile, every slot assignment and
    every row count `n`, the table of `n` all-zero rows is rejected: with `n = 0` the row count
    is wrong, and with `n > 0` the Group A S-box constraints of the first row fail, since
    `(0 + rc)^7 ≠ 0`. -/
theorem tooth_stepOp256_zero_rows_rejected (profile : AggSigProfile) (slots : List StepOpSlot)
    (n : Nat) :
    stepOp256TableOk profile slots (List.replicate n stepOpZeroRow) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  unfold stepOp256TableOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hPos, hLen⟩, _⟩, hIntra⟩, _⟩ := h
  cases n with
  | zero =>
    rw [List.replicate_zero, List.length_nil] at hLen
    cases profile <;> simp only [stepOpRowsPerSigner] at hLen <;> omega
  | succ m =>
    rw [List.replicate_succ] at hIntra
    unfold stepOp256IntraResidualsFrom stepOp256RowResiduals at hIntra
    rw [allZeroGoldilocks_append, allZeroGoldilocks_append, allZeroGoldilocks_append,
      Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hIntra
    rw [stepOpZeroRow_groupA] at hIntra
    exact absurd hIntra.1.1.1 (by decide)

end StepOpTable

/-! ## §3. Steiner-Deduplicated Merkle-Canopy Multi-Proofs (`pcs.rs`, `CanopyMultiProof`) -/

/-- Parent digest of the active node `(u, hu)` combined with an authentication sibling `s`
    consumed from the proof (`pcs.rs:verify_canopy_multiproof`, the `else` arm):
    `(u & 1) == 0` puts `hu` on the left, otherwise on the right; the node index fed to the hash is
    the parent `u >> 1`. -/
def canopyParentHash {D : Type} (nodeHash : Nat → D → D → D) (u : Nat) (hu s : D) : D :=
  if u &&& 1 = 0 then nodeHash (u >>> 1) hu s else nodeHash (u >>> 1) s hu

/-- One tree level of `verify_canopy_multiproof` (the inner `while k < active.len()` loop).
    Walks the active list of heap-indexed `(node, digest)` pairs left to right. If the next active
    entry is the sibling `u ^ 1`, the two are merged as `nodeHash (u >> 1) hu hv` (`k += 2`) and no
    proof digest is consumed. Otherwise exactly one digest is consumed from the sibling list
    (`k += 1`), and the walk fails (`none`) when the list is exhausted. Returns the next level's
    active list together with the unconsumed siblings. -/
def canopyLevelStep {D : Type} (nodeHash : Nat → D → D → D) :
    List (Nat × D) → List D → Option (List (Nat × D) × List D)
  | [], sibs => some ([], sibs)
  | [(u, hu)], sibs =>
    match sibs with
    | [] => none
    | s :: rest => some ([(u >>> 1, canopyParentHash nodeHash u hu s)], rest)
  | (u, hu) :: (v, hv) :: tl, sibs =>
    if v = u ^^^ 1 then
      (canopyLevelStep nodeHash tl sibs).map
        (fun r => ((u >>> 1, nodeHash (u >>> 1) hu hv) :: r.1, r.2))
    else
      match sibs with
      | [] => none
      | s :: rest =>
        (canopyLevelStep nodeHash ((v, hv) :: tl) rest).map
          (fun r => ((u >>> 1, canopyParentHash nodeHash u hu s) :: r.1, r.2))

/-- `depth` iterations of `canopyLevelStep` (the outer `while cur_depth > 0` loop), threading
    the sibling cursor as the list of unconsumed digests. -/
def canopyLevels {D : Type} (nodeHash : Nat → D → D → D) :
    Nat → List (Nat × D) → List D → Option (List (Nat × D) × List D)
  | 0, active, sibs => some (active, sibs)
  | depth + 1, active, sibs =>
    match canopyLevelStep nodeHash active sibs with
    | none => none
    | some r => canopyLevels nodeHash depth r.1 r.2

/-- Index pre-checks of `verify_canopy_multiproof`: the list is nonempty, strictly ascending on
    every adjacent window, and its last index is `< n`. -/
def canopyIndicesOk (n : Nat) : List Nat → Bool
  | [] => false
  | [i] => decide (i < n)
  | i :: j :: tl => decide (i < j) && canopyIndicesOk n (j :: tl)

/-- `pcs.rs:verify_canopy_multiproof`. Leaf `i` sits at heap index `2^logLeaves + i`; after
    `logLeaves` levels the walk must have consumed every proof digest (`sib_cursor == len`), the
    active list must be exactly `[(1, top)]`, and `rootHash logLeaves top` must equal the
    commitment. `nodeHash` models `hash_merkle_internal(node_idx, left, right)` and `rootHash`
    models `hash_tree_root(log_leaves, top)`. -/
def verifyCanopyMultiproof {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (rootHash : Nat → D → D)
    (logLeaves : Nat) (commitment : D) (leaves : List (Nat × D)) (proof : List D) : Bool :=
  decide (logLeaves ≤ 28) &&
  canopyIndicesOk (2 ^ logLeaves) (leaves.map Prod.fst) &&
  match canopyLevels nodeHash logLeaves
      (leaves.map (fun p => (2 ^ logLeaves + p.1, p.2))) proof with
  | some ([(u, top)], []) => decide (u = 1) && decide (rootHash logLeaves top = commitment)
  | _ => false

/-- `verifyCanopyMultiproof` with the exact-consumption check (`sib_cursor == len`) removed:
    unconsumed trailing digests are ignored. Defined only to show that the check is load-bearing
    (`canopyToy_relaxed_accepts_extra_sibling`). -/
def verifyCanopyMultiproofRelaxed {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (rootHash : Nat → D → D)
    (logLeaves : Nat) (commitment : D) (leaves : List (Nat × D)) (proof : List D) : Bool :=
  decide (logLeaves ≤ 28) &&
  canopyIndicesOk (2 ^ logLeaves) (leaves.map Prod.fst) &&
  match canopyLevels nodeHash logLeaves
      (leaves.map (fun p => (2 ^ logLeaves + p.1, p.2))) proof with
  | some ([(u, top)], _) => decide (u = 1) && decide (rootHash logLeaves top = commitment)
  | _ => false

/-- The level walk of `canopyLevelStep` on node indices alone: the next level's indices and the
    number of sibling digests the level consumes. -/
def steinerLevelStep : List Nat → List Nat × Nat
  | [] => ([], 0)
  | [u] => ([u >>> 1], 1)
  | u :: v :: tl =>
    if v = u ^^^ 1 then
      ((u >>> 1) :: (steinerLevelStep tl).1, (steinerLevelStep tl).2)
    else
      ((u >>> 1) :: (steinerLevelStep (v :: tl)).1, (steinerLevelStep (v :: tl)).2 + 1)

/-- Total number of sibling digests consumed over `depth` levels starting from `nodes`. -/
def steinerCountLevels : Nat → List Nat → Nat
  | 0, _ => 0
  | depth + 1, nodes =>
    (steinerLevelStep nodes).2 + steinerCountLevels depth (steinerLevelStep nodes).1

/-- Number of authentication siblings in the Steiner-deduplicated multiproof for the leaf index
    list `indices` in a tree with `2^logLeaves` leaves. A function of the indices only. -/
def steinerSiblingCount (logLeaves : Nat) (indices : List Nat) : Nat :=
  steinerCountLevels logLeaves (indices.map (fun i => 2 ^ logLeaves + i))

private theorem canopyLevelStep_nil {D : Type} (nodeHash : Nat → D → D → D)
    {s : List D} {b : List (Nat × D)} {t : List D}
    (h : canopyLevelStep nodeHash [] s = some (b, t)) : b = [] ∧ t = s := by
  simp only [canopyLevelStep] at h
  obtain ⟨hb, ht⟩ := Prod.mk.inj (Option.some.inj h)
  exact ⟨hb.symm, ht.symm⟩

private theorem canopyLevelStep_single {D : Type} (nodeHash : Nat → D → D → D)
    {u : Nat} {hu : D} {s : List D} {b : List (Nat × D)} {t : List D}
    (h : canopyLevelStep nodeHash [(u, hu)] s = some (b, t)) :
    ∃ c, s = c :: t ∧ b = [(u >>> 1, canopyParentHash nodeHash u hu c)] := by
  simp only [canopyLevelStep] at h
  match s, h with
  | [], h => cases h
  | c :: rest, h =>
    obtain ⟨hb, ht⟩ := Prod.mk.inj (Option.some.inj h)
    subst ht
    exact ⟨c, rfl, hb.symm⟩

private theorem canopyLevelStep_pair {D : Type} (nodeHash : Nat → D → D → D)
    {u v : Nat} {hu hv : D} {tl : List (Nat × D)} {s : List D} {b : List (Nat × D)} {t : List D}
    (hv' : v = u ^^^ 1)
    (h : canopyLevelStep nodeHash ((u, hu) :: (v, hv) :: tl) s = some (b, t)) :
    ∃ act, canopyLevelStep nodeHash tl s = some (act, t) ∧
      b = (u >>> 1, nodeHash (u >>> 1) hu hv) :: act := by
  have hc : (v = u ^^^ 1) = True := eq_true hv'
  simp only [canopyLevelStep, hc, ↓reduceIte] at h
  cases hs : canopyLevelStep nodeHash tl s with
  | none => rw [hs] at h; cases h
  | some r =>
    obtain ⟨act, rest⟩ := r
    rw [hs] at h
    obtain ⟨hb, ht⟩ := Prod.mk.inj (Option.some.inj h)
    subst ht
    exact ⟨act, rfl, hb.symm⟩

private theorem canopyLevelStep_solo {D : Type} (nodeHash : Nat → D → D → D)
    {u v : Nat} {hu hv : D} {tl : List (Nat × D)} {s : List D} {b : List (Nat × D)} {t : List D}
    (hv' : ¬ v = u ^^^ 1)
    (h : canopyLevelStep nodeHash ((u, hu) :: (v, hv) :: tl) s = some (b, t)) :
    ∃ c rest act, s = c :: rest ∧
      canopyLevelStep nodeHash ((v, hv) :: tl) rest = some (act, t) ∧
      b = (u >>> 1, canopyParentHash nodeHash u hu c) :: act := by
  simp only [canopyLevelStep, hv', ↓reduceIte] at h
  match s, h with
  | [], h => cases h
  | c :: rest, h =>
    dsimp only at h
    cases hs : canopyLevelStep nodeHash ((v, hv) :: tl) rest with
    | none => rw [hs] at h; cases h
    | some r =>
      obtain ⟨act, rest'⟩ := r
      rw [hs] at h
      obtain ⟨hb, ht⟩ := Prod.mk.inj (Option.some.inj h)
      subst ht
      exact ⟨c, rest, act, rfl, hs, hb.symm⟩

private theorem canopyLevels_succ {D : Type} (nodeHash : Nat → D → D → D)
    {d : Nat} {a : List (Nat × D)} {s : List D} {b : List (Nat × D)} {t : List D}
    (h : canopyLevels nodeHash (d + 1) a s = some (b, t)) :
    ∃ m r, canopyLevelStep nodeHash a s = some (m, r) ∧ canopyLevels nodeHash d m r = some (b, t) := by
  rw [canopyLevels] at h
  cases hs : canopyLevelStep nodeHash a s with
  | none => rw [hs] at h; cases h
  | some p =>
    obtain ⟨m, r⟩ := p
    rw [hs] at h
    exact ⟨m, r, rfl, h⟩

/-- A successful level step maps the index list by `steinerLevelStep` and consumes exactly the
    number of digests `steinerLevelStep` predicts. -/
private theorem canopyLevelStep_shape {D : Type} (nodeHash : Nat → D → D → D) :
    ∀ (n : Nat) (a : List (Nat × D)) (s : List D) (b : List (Nat × D)) (t : List D),
      a.length < n →
      canopyLevelStep nodeHash a s = some (b, t) →
      b.map Prod.fst = (steinerLevelStep (a.map Prod.fst)).1 ∧
      s.length = (steinerLevelStep (a.map Prod.fst)).2 + t.length := by
  intro n
  induction n with
  | zero => intro a s b t hLen _; exact absurd hLen (Nat.not_lt_zero _)
  | succ n ih =>
    intro a s b t hLen h
    match a, hLen, h with
    | [], _, h =>
      obtain ⟨hb, ht⟩ := canopyLevelStep_nil nodeHash h
      subst hb; subst ht
      exact ⟨rfl, (Nat.zero_add _).symm⟩
    | [(u, hu)], _, h =>
      obtain ⟨c, hs, hb⟩ := canopyLevelStep_single nodeHash h
      subst hs; subst hb
      exact ⟨rfl, Nat.add_comm _ _⟩
    | (u, hu) :: (v, hv) :: tl, hLen, h =>
      have hLen1 : ((v, hv) :: tl).length < n := Nat.lt_of_succ_lt_succ hLen
      have hLen2 : tl.length < n := Nat.lt_of_succ_lt hLen1
      by_cases hv' : v = u ^^^ 1
      · obtain ⟨act, hr, hb⟩ := canopyLevelStep_pair nodeHash hv' h
        obtain ⟨h1, h2⟩ := ih tl s act t hLen2 hr
        subst hb
        have hc : (v = u ^^^ 1) = True := eq_true hv'
        simp only [List.map_cons, steinerLevelStep, hc, ↓reduceIte]
        exact ⟨congrArg (List.cons (u >>> 1)) h1, h2⟩
      · obtain ⟨c, rest, act, hs, hr, hb⟩ := canopyLevelStep_solo nodeHash hv' h
        obtain ⟨h1, h2⟩ := ih ((v, hv) :: tl) rest act t hLen1 hr
        subst hs; subst hb
        simp only [List.map_cons] at h1 h2
        simp only [List.map_cons, steinerLevelStep, hv', ↓reduceIte, List.length_cons]
        refine ⟨congrArg (List.cons (u >>> 1)) h1, ?_⟩
        rw [h2]
        exact Nat.add_right_comm _ _ _

private theorem canopyLevels_count {D : Type} (nodeHash : Nat → D → D → D) :
    ∀ (d : Nat) (a : List (Nat × D)) (s : List D) (b : List (Nat × D)) (t : List D),
      canopyLevels nodeHash d a s = some (b, t) →
      s.length = steinerCountLevels d (a.map Prod.fst) + t.length
  | 0, a, s, b, t, h => by
    rw [canopyLevels] at h
    obtain ⟨_, ht⟩ := Prod.mk.inj (Option.some.inj h)
    subst ht
    exact (Nat.zero_add _).symm
  | d + 1, a, s, b, t, h => by
    obtain ⟨m, r, hStep, hRest⟩ := canopyLevels_succ nodeHash h
    obtain ⟨hm, hLen⟩ := canopyLevelStep_shape nodeHash _ a s m r (Nat.lt_succ_self _) hStep
    have ih := canopyLevels_count nodeHash d m r b t hRest
    rw [hm] at ih
    rw [steinerCountLevels, hLen, ih]
    exact (Nat.add_assoc _ _ _).symm

private theorem canopy_map_fst {D : Type} (n : Nat) :
    ∀ (leaves : List (Nat × D)),
      (leaves.map (fun p => (n + p.1, p.2))).map Prod.fst =
        (leaves.map Prod.fst).map (fun i => n + i)
  | [] => rfl
  | p :: tl => congrArg (List.cons (n + p.1)) (canopy_map_fst n tl)

private theorem canopy_lift_inj {D : Type} (n : Nat) :
    ∀ (l1 l2 : List (Nat × D)),
      l1.map (fun p => (n + p.1, p.2)) = l2.map (fun p => (n + p.1, p.2)) → l1 = l2
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | p :: t1, q :: t2, h => by
    have h' : (n + p.1, p.2) :: t1.map (fun p => (n + p.1, p.2)) =
        (n + q.1, q.2) :: t2.map (fun p => (n + p.1, p.2)) := h
    obtain ⟨hh, ht⟩ := List.cons.inj h'
    obtain ⟨h1, h2⟩ := Prod.mk.inj hh
    rw [canopy_lift_inj n t1 t2 ht]
    exact congrArg (fun x => x :: t2) (Prod.ext (Nat.add_left_cancel h1) h2)

private theorem canopy_accept_unpack {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (rootHash : Nat → D → D)
    (logLeaves : Nat) (commitment : D) (leaves : List (Nat × D)) (proof : List D)
    (h : verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves proof = true) :
    ∃ top, canopyLevels nodeHash logLeaves
        (leaves.map (fun p => (2 ^ logLeaves + p.1, p.2))) proof = some ([(1, top)], []) ∧
      rootHash logLeaves top = commitment := by
  unfold verifyCanopyMultiproof at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨_, hM⟩ := h
  split at hM
  next u top hEq =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hM
    obtain ⟨hu, hR⟩ := hM
    subst hu
    exact ⟨top, hEq, hR⟩
  next => cases hM

/-- **Exact sibling consumption is determined by the index set alone.** Whatever the hash
    functions, leaf digests and commitment, an accepted multiproof carries exactly
    `steinerSiblingCount logLeaves indices` authentication siblings. -/
theorem verifyCanopyMultiproof_exact_sibling_count {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (rootHash : Nat → D → D)
    (logLeaves : Nat) (commitment : D) (leaves : List (Nat × D)) (proof : List D)
    (hAcc : verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves proof = true) :
    proof.length = steinerSiblingCount logLeaves (leaves.map Prod.fst) := by
  obtain ⟨top, hL, _⟩ := canopy_accept_unpack nodeHash rootHash logLeaves commitment leaves proof hAcc
  have hCount := canopyLevels_count nodeHash logLeaves _ proof _ _ hL
  rw [canopy_map_fst] at hCount
  exact hCount

/-- Two proofs of different lengths for the same index list are never both accepted, for any
    hash functions, commitments and leaf digests. -/
theorem verifyCanopyMultiproof_length_mismatch_rejected {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (rootHash : Nat → D → D)
    (logLeaves : Nat) (commitment commitment' : D)
    (leaves leaves' : List (Nat × D)) (proof proof' : List D)
    (hAcc : verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves proof = true)
    (hIdx : leaves'.map Prod.fst = leaves.map Prod.fst)
    (hLen : proof'.length ≠ proof.length) :
    verifyCanopyMultiproof nodeHash rootHash logLeaves commitment' leaves' proof' = false := by
  apply Bool.eq_false_iff.mpr
  intro hAcc'
  apply hLen
  rw [verifyCanopyMultiproof_exact_sibling_count nodeHash rootHash logLeaves commitment' leaves' proof' hAcc',
    verifyCanopyMultiproof_exact_sibling_count nodeHash rootHash logLeaves commitment leaves proof hAcc, hIdx]

/-- **Extra-sibling tooth.** Appending one or more digests to an accepted proof yields a
    rejected proof, for any hash functions. -/
theorem verifyCanopyMultiproof_extra_sibling_rejected {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (rootHash : Nat → D → D)
    (logLeaves : Nat) (commitment : D) (leaves : List (Nat × D)) (proof : List D)
    (extra : D) (more : List D)
    (hAcc : verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves proof = true) :
    verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves
      (proof ++ extra :: more) = false := by
  refine verifyCanopyMultiproof_length_mismatch_rejected nodeHash rootHash logLeaves commitment
    commitment leaves leaves proof _ hAcc rfl ?_
  rw [List.length_append, List.length_cons]
  exact Nat.ne_of_gt (Nat.lt_add_of_pos_right (Nat.succ_pos _))

/-- **Missing-sibling tooth.** Dropping the last digest of an accepted nonempty proof yields a
    rejected proof, for any hash functions. -/
theorem verifyCanopyMultiproof_missing_sibling_rejected {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (rootHash : Nat → D → D)
    (logLeaves : Nat) (commitment : D) (leaves : List (Nat × D)) (proof : List D)
    (hNonempty : proof ≠ [])
    (hAcc : verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves proof = true) :
    verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves proof.dropLast = false := by
  refine verifyCanopyMultiproof_length_mismatch_rejected nodeHash rootHash logLeaves commitment
    commitment leaves leaves proof _ hAcc rfl ?_
  rw [List.length_dropLast]
  exact Nat.ne_of_lt (Nat.sub_lt (List.length_pos_iff.mpr hNonempty) Nat.one_pos)

private theorem canopyNode_binding {D : Type} [DecidableEq D] (nodeHash : Nat → D → D → D)
    {i : Nat} {l r l' r' : D} (h : nodeHash i l r = nodeHash i l' r') :
    (∃ (i : Nat) (l r l' r' : D), (l, r) ≠ (l', r') ∧ nodeHash i l r = nodeHash i l' r') ∨
    (l = l' ∧ r = r') := by
  by_cases he : (l, r) = (l', r')
  · exact Or.inr (Prod.mk.inj he)
  · exact Or.inl ⟨i, l, r, l', r', he, h⟩

private theorem canopyParentHash_binding {D : Type} [DecidableEq D] (nodeHash : Nat → D → D → D)
    {u : Nat} {hu s hu' s' : D}
    (h : canopyParentHash nodeHash u hu s = canopyParentHash nodeHash u hu' s') :
    (∃ (i : Nat) (l r l' r' : D), (l, r) ≠ (l', r') ∧ nodeHash i l r = nodeHash i l' r') ∨
    (hu = hu' ∧ s = s') := by
  unfold canopyParentHash at h
  by_cases hp : u &&& 1 = 0
  · simp only [hp, ↓reduceIte] at h
    exact canopyNode_binding nodeHash h
  · simp only [hp, ↓reduceIte] at h
    rcases canopyNode_binding nodeHash h with hc | ⟨e1, e2⟩
    · exact Or.inl hc
    · exact Or.inr ⟨e2, e1⟩

/-- Per-level binding: two successful level steps over the same index list that produce the
    same next level and the same unconsumed siblings either started from identical inputs or
    exhibit a `nodeHash` collision. -/
private theorem canopyLevelStep_binding {D : Type} [DecidableEq D] (nodeHash : Nat → D → D → D) :
    ∀ (n : Nat) (a1 a2 : List (Nat × D)) (s1 s2 : List D) (b : List (Nat × D)) (t : List D),
      a1.length < n →
      a1.map Prod.fst = a2.map Prod.fst →
      canopyLevelStep nodeHash a1 s1 = some (b, t) →
      canopyLevelStep nodeHash a2 s2 = some (b, t) →
      (∃ (i : Nat) (l r l' r' : D), (l, r) ≠ (l', r') ∧ nodeHash i l r = nodeHash i l' r') ∨
      (a1 = a2 ∧ s1 = s2) := by
  intro n
  induction n with
  | zero => intro a1 a2 s1 s2 b t hLen _ _ _; exact absurd hLen (Nat.not_lt_zero _)
  | succ n ih =>
    intro a1 a2 s1 s2 b t hLen hIdx h1 h2
    match a1, a2, hLen, hIdx, h1, h2 with
    | [], [], _, _, h1, h2 =>
      obtain ⟨_, ht1⟩ := canopyLevelStep_nil nodeHash h1
      obtain ⟨_, ht2⟩ := canopyLevelStep_nil nodeHash h2
      exact Or.inr ⟨rfl, ht1.symm.trans ht2⟩
    | [], _ :: _, _, hIdx, _, _ => cases hIdx
    | _ :: _, [], _, hIdx, _, _ => cases hIdx
    | [(u, hu)], [(u2, hu2)], _, hIdx, h1, h2 =>
      have hu_eq : u = u2 := (List.cons.inj hIdx).1
      subst hu_eq
      obtain ⟨c1, hs1, hb1⟩ := canopyLevelStep_single nodeHash h1
      obtain ⟨c2, hs2, hb2⟩ := canopyLevelStep_single nodeHash h2
      have hH := (Prod.mk.inj (List.cons.inj (hb1.symm.trans hb2)).1).2
      rcases canopyParentHash_binding nodeHash hH with hc | ⟨e1, e2⟩
      · exact Or.inl hc
      · subst e1; subst e2; subst hs1; subst hs2
        exact Or.inr ⟨rfl, rfl⟩
    | [_], _ :: _ :: _, _, hIdx, _, _ => cases (List.cons.inj hIdx).2
    | _ :: _ :: _, [_], _, hIdx, _, _ => cases (List.cons.inj hIdx).2
    | (u, hu) :: (v, hv) :: tl1, (u2, hu2) :: (v2, hv2) :: tl2, hLen, hIdx, h1, h2 =>
      have hu_eq : u = u2 := (List.cons.inj hIdx).1
      have hv_eq : v = v2 := (List.cons.inj (List.cons.inj hIdx).2).1
      have hTl : tl1.map Prod.fst = tl2.map Prod.fst := (List.cons.inj (List.cons.inj hIdx).2).2
      subst hu_eq; subst hv_eq
      have hLen1 : ((v, hv) :: tl1).length < n := Nat.lt_of_succ_lt_succ hLen
      have hLen2 : tl1.length < n := Nat.lt_of_succ_lt hLen1
      by_cases hv' : v = u ^^^ 1
      · obtain ⟨act1, hr1, hb1⟩ := canopyLevelStep_pair nodeHash hv' h1
        obtain ⟨act2, hr2, hb2⟩ := canopyLevelStep_pair nodeHash hv' h2
        obtain ⟨hHead, hAct⟩ := List.cons.inj (hb1.symm.trans hb2)
        subst hAct
        rcases canopyNode_binding nodeHash (Prod.mk.inj hHead).2 with hc | ⟨e1, e2⟩
        · exact Or.inl hc
        · rcases ih tl1 tl2 s1 s2 act1 t hLen2 hTl hr1 hr2 with hc | ⟨eT, eS⟩
          · exact Or.inl hc
          · subst e1; subst e2; subst eT; subst eS
            exact Or.inr ⟨rfl, rfl⟩
      · obtain ⟨c1, r1, act1, hs1, hr1, hb1⟩ := canopyLevelStep_solo nodeHash hv' h1
        obtain ⟨c2, r2, act2, hs2, hr2, hb2⟩ := canopyLevelStep_solo nodeHash hv' h2
        obtain ⟨hHead, hAct⟩ := List.cons.inj (hb1.symm.trans hb2)
        subst hAct
        rcases canopyParentHash_binding nodeHash (Prod.mk.inj hHead).2 with hc | ⟨e1, e2⟩
        · exact Or.inl hc
        · rcases ih ((v, hv) :: tl1) ((v, hv2) :: tl2) r1 r2 act1 t hLen1
              (congrArg (List.cons v) hTl) hr1 hr2 with hc | ⟨eT, eS⟩
          · exact Or.inl hc
          · subst e1; subst e2; subst eS; subst hs1; subst hs2
            exact Or.inr ⟨congrArg (List.cons (u, hu)) eT, rfl⟩

/-- Binding of the whole level iteration: equal final state and equal starting index list force
    equal starting digests and equal sibling lists, or a `nodeHash` collision. -/
private theorem canopyLevels_binding {D : Type} [DecidableEq D] (nodeHash : Nat → D → D → D) :
    ∀ (d : Nat) (a1 a2 : List (Nat × D)) (s1 s2 : List D) (b : List (Nat × D)) (t : List D),
      a1.map Prod.fst = a2.map Prod.fst →
      canopyLevels nodeHash d a1 s1 = some (b, t) →
      canopyLevels nodeHash d a2 s2 = some (b, t) →
      (∃ (i : Nat) (l r l' r' : D), (l, r) ≠ (l', r') ∧ nodeHash i l r = nodeHash i l' r') ∨
      (a1 = a2 ∧ s1 = s2)
  | 0, a1, a2, s1, s2, b, t, _, h1, h2 => by
    rw [canopyLevels] at h1 h2
    obtain ⟨ha, hs⟩ := Prod.mk.inj (Option.some.inj (h1.trans h2.symm))
    exact Or.inr ⟨ha, hs⟩
  | d + 1, a1, a2, s1, s2, b, t, hIdx, h1, h2 => by
    obtain ⟨m1, r1, hStep1, hRest1⟩ := canopyLevels_succ nodeHash h1
    obtain ⟨m2, r2, hStep2, hRest2⟩ := canopyLevels_succ nodeHash h2
    have hm1 := (canopyLevelStep_shape nodeHash _ a1 s1 m1 r1 (Nat.lt_succ_self _) hStep1).1
    have hm2 := (canopyLevelStep_shape nodeHash _ a2 s2 m2 r2 (Nat.lt_succ_self _) hStep2).1
    rw [hIdx] at hm1
    rcases canopyLevels_binding nodeHash d m1 m2 r1 r2 b t (hm1.trans hm2.symm) hRest1 hRest2
      with hc | ⟨eM, eR⟩
    · exact Or.inl hc
    · subst eM; subst eR
      exact canopyLevelStep_binding nodeHash _ a1 a2 s1 s2 m1 r1 (Nat.lt_succ_self _) hIdx
        hStep1 hStep2

/-- **Binding of the Steiner multiproof verifier (collision extraction).** If two distinct
    openings `(leaves₁, proof₁) ≠ (leaves₂, proof₂)` of the same index list are both accepted
    against the same commitment, then either `rootHash` collides on two distinct top nodes, or
    `nodeHash` collides at one node index on two distinct `(left, right)` pairs. -/
theorem verifyCanopyMultiproof_binding {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (rootHash : Nat → D → D)
    (logLeaves : Nat) (commitment : D)
    (leaves₁ leaves₂ : List (Nat × D)) (proof₁ proof₂ : List D)
    (hIdx : leaves₁.map Prod.fst = leaves₂.map Prod.fst)
    (hAcc₁ : verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves₁ proof₁ = true)
    (hAcc₂ : verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves₂ proof₂ = true)
    (hNe : (leaves₁, proof₁) ≠ (leaves₂, proof₂)) :
    (∃ top₁ top₂ : D, top₁ ≠ top₂ ∧ rootHash logLeaves top₁ = rootHash logLeaves top₂) ∨
    (∃ (i : Nat) (l r l' r' : D), (l, r) ≠ (l', r') ∧ nodeHash i l r = nodeHash i l' r') := by
  obtain ⟨top1, hL1, hR1⟩ :=
    canopy_accept_unpack nodeHash rootHash logLeaves commitment leaves₁ proof₁ hAcc₁
  obtain ⟨top2, hL2, hR2⟩ :=
    canopy_accept_unpack nodeHash rootHash logLeaves commitment leaves₂ proof₂ hAcc₂
  by_cases hTop : top1 = top2
  · subst hTop
    have hIdx' : (leaves₁.map (fun p => (2 ^ logLeaves + p.1, p.2))).map Prod.fst =
        (leaves₂.map (fun p => (2 ^ logLeaves + p.1, p.2))).map Prod.fst := by
      rw [canopy_map_fst, canopy_map_fst, hIdx]
    rcases canopyLevels_binding nodeHash logLeaves _ _ proof₁ proof₂ _ _ hIdx' hL1 hL2
      with hc | ⟨eA, eP⟩
    · exact Or.inr hc
    · have eL := canopy_lift_inj (2 ^ logLeaves) leaves₁ leaves₂ eA
      subst eL; subst eP
      exact absurd rfl hNe
  · exact Or.inl ⟨top1, top2, hTop, hR1.trans hR2.symm⟩

/-- **Tampered Steiner multiproof.** Starting from an accepted opening, any change to a leaf
    digest or to the sibling list (same index list, different data) is rejected, unless it
    exhibits a `rootHash` or `nodeHash` collision. -/
theorem verifyCanopyMultiproof_tamper_rejected_or_collision {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (rootHash : Nat → D → D)
    (logLeaves : Nat) (commitment : D)
    (leaves leaves' : List (Nat × D)) (proof proof' : List D)
    (hAcc : verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves proof = true)
    (hIdx : leaves'.map Prod.fst = leaves.map Prod.fst)
    (hNe : (leaves', proof') ≠ (leaves, proof)) :
    verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves' proof' = false ∨
    (∃ top₁ top₂ : D, top₁ ≠ top₂ ∧ rootHash logLeaves top₁ = rootHash logLeaves top₂) ∨
    (∃ (i : Nat) (l r l' r' : D), (l, r) ≠ (l', r') ∧ nodeHash i l r = nodeHash i l' r') := by
  cases hV : verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves' proof' with
  | false => exact Or.inl rfl
  | true =>
    exact Or.inr (verifyCanopyMultiproof_binding nodeHash rootHash logLeaves commitment
      leaves' leaves proof' proof hIdx hV hAcc hNe)

/-! ### Concrete instance: `logLeaves = 3`, opened leaves `{1, 2, 6}` -/

/-- Cantor pairing on `Nat`, used as a toy digest combiner. -/
def canopyToyPair (a b : Nat) : Nat := (a + b) * (a + b + 1) / 2 + b

/-- Toy `hash_merkle_internal`: pairs the node index with the pair of children. -/
def canopyToyNodeHash (i l r : Nat) : Nat := canopyToyPair i (canopyToyPair l r)

/-- Toy `hash_tree_root`: pairs `logLeaves` with the top node. -/
def canopyToyRootHash (logLeaves top : Nat) : Nat := canopyToyPair logLeaves top

/-- Toy leaf digest of leaf `i`. -/
def canopyToyLeaf (i : Nat) : Nat := 100 + i

/-- Commitment of the full 8-leaf toy tree, computed node by node (not through the verifier). -/
def canopyToyCommitment : Nat :=
  canopyToyRootHash 3
    (canopyToyNodeHash 1
      (canopyToyNodeHash 2
        (canopyToyNodeHash 4 (canopyToyLeaf 0) (canopyToyLeaf 1))
        (canopyToyNodeHash 5 (canopyToyLeaf 2) (canopyToyLeaf 3)))
      (canopyToyNodeHash 3
        (canopyToyNodeHash 6 (canopyToyLeaf 4) (canopyToyLeaf 5))
        (canopyToyNodeHash 7 (canopyToyLeaf 6) (canopyToyLeaf 7))))

/-- Opened leaves `{1, 2, 6}` with their digests. -/
def canopyToyLeaves : List (Nat × Nat) :=
  [(1, canopyToyLeaf 1), (2, canopyToyLeaf 2), (6, canopyToyLeaf 6)]

/-- Steiner multiproof for `{1, 2, 6}`: leaves `0`, `3`, `7` at the bottom level and internal
    node `6` one level up; nodes `4, 5` and `2, 3` merge without consuming a digest. -/
def canopyToyProof : List Nat :=
  [canopyToyLeaf 0, canopyToyLeaf 3, canopyToyLeaf 7,
   canopyToyNodeHash 6 (canopyToyLeaf 4) (canopyToyLeaf 5)]

theorem canopyToy_honest_accepted :
    verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      canopyToyLeaves canopyToyProof = true := by decide

theorem canopyToy_sibling_count :
    steinerSiblingCount 3 [1, 2, 6] = 4 := by decide

/-- A flipped sibling digest (leaf `7` replaced) is rejected. -/
theorem canopyToy_flipped_sibling_rejected :
    verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      canopyToyLeaves
      [canopyToyLeaf 0, canopyToyLeaf 3, canopyToyLeaf 7 + 1,
       canopyToyNodeHash 6 (canopyToyLeaf 4) (canopyToyLeaf 5)] = false := by decide

/-- A flipped leaf digest (leaf `2`) is rejected. -/
theorem canopyToy_flipped_leaf_rejected :
    verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      [(1, canopyToyLeaf 1), (2, canopyToyLeaf 2 + 1), (6, canopyToyLeaf 6)]
      canopyToyProof = false := by decide

/-- The proof with its last sibling removed is rejected. -/
theorem canopyToy_missing_sibling_rejected :
    verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      canopyToyLeaves canopyToyProof.dropLast = false := by decide

/-- The proof with one trailing digest appended is rejected. -/
theorem canopyToy_extra_sibling_rejected :
    verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      canopyToyLeaves (canopyToyProof ++ [999]) = false := by decide

/-- A duplicated index is rejected. -/
theorem canopyToy_duplicate_index_rejected :
    verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      [(1, canopyToyLeaf 1), (1, canopyToyLeaf 1), (2, canopyToyLeaf 2), (6, canopyToyLeaf 6)]
      canopyToyProof = false := by decide

/-- An unsorted index list is rejected. -/
theorem canopyToy_unsorted_index_rejected :
    verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      [(2, canopyToyLeaf 2), (1, canopyToyLeaf 1), (6, canopyToyLeaf 6)]
      canopyToyProof = false := by decide

/-- An index `≥ 2^logLeaves` is rejected. -/
theorem canopyToy_out_of_range_index_rejected :
    verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      [(1, canopyToyLeaf 1), (2, canopyToyLeaf 2), (8, canopyToyLeaf 6)]
      canopyToyProof = false := by decide

/-- **The exact-consumption check is load-bearing.** The relaxed verifier, which differs from
    `verifyCanopyMultiproof` only by ignoring unconsumed digests, accepts the honest proof with a
    trailing digest appended, while `verifyCanopyMultiproof` rejects the same input. -/
theorem canopyToy_relaxed_accepts_extra_sibling :
    verifyCanopyMultiproofRelaxed canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      canopyToyLeaves (canopyToyProof ++ [999]) = true ∧
    verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      canopyToyLeaves (canopyToyProof ++ [999]) = false := by decide

/-- Non-vacuity witness for §3: the honest toy opening is accepted, carries exactly
    `steinerSiblingCount` siblings, and every other opening of the same indices against the same
    commitment is rejected or exhibits a collision of the toy hashes. -/
theorem inhabited_canopy_multiproof_binding :
    verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
      canopyToyLeaves canopyToyProof = true ∧
    canopyToyProof.length = steinerSiblingCount 3 (canopyToyLeaves.map Prod.fst) ∧
    (∀ (leaves' : List (Nat × Nat)) (proof' : List Nat),
      leaves'.map Prod.fst = canopyToyLeaves.map Prod.fst →
      (leaves', proof') ≠ (canopyToyLeaves, canopyToyProof) →
      verifyCanopyMultiproof canopyToyNodeHash canopyToyRootHash 3 canopyToyCommitment
        leaves' proof' = false ∨
      (∃ top₁ top₂ : Nat, top₁ ≠ top₂ ∧ canopyToyRootHash 3 top₁ = canopyToyRootHash 3 top₂) ∨
      (∃ (i l r l' r' : Nat), (l, r) ≠ (l', r') ∧
        canopyToyNodeHash i l r = canopyToyNodeHash i l' r')) :=
  ⟨canopyToy_honest_accepted,
   verifyCanopyMultiproof_exact_sibling_count canopyToyNodeHash canopyToyRootHash 3
     canopyToyCommitment canopyToyLeaves canopyToyProof canopyToy_honest_accepted,
   fun leaves' proof' hIdx hNe =>
     verifyCanopyMultiproof_tamper_rejected_or_collision canopyToyNodeHash canopyToyRootHash 3
       canopyToyCommitment canopyToyLeaves leaves' canopyToyProof proof'
       canopyToy_honest_accepted hIdx hNe⟩

/-! ## §4. `GoldilocksExt4` Encoding, Multi-Stage WHIR Rate Escalation, Row-Committed Witnesses, and Transcript-Extracted Collisions (`field.rs`, `pcs.rs`) -/

/-! ### Canonical 32-byte little-endian encoding (`field.rs:to_le_bytes`, `from_le_bytes_canonical`) -/

/-- Byte `(n / d) mod 256`; `d` ranges over `256^i`. -/
def leByte (n d : Nat) : UInt8 := UInt8.ofNatLT (n / d % 256) (Nat.mod_lt _ (by decide))

theorem leByte_toNat (n d : Nat) : (leByte n d).toNat = n / d % 256 := by rfl

/-- Value of eight little-endian bytes. -/
def le64Value (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : Nat :=
  b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat +
    4294967296 * b4.toNat + 1099511627776 * b5.toNat + 281474976710656 * b6.toNat +
    72057594037927936 * b7.toNat

private theorem le64_recompose (n : Nat) (h : n < 18446744073709551616) :
    n / 1 % 256 + 256 * (n / 256 % 256) + 65536 * (n / 65536 % 256) +
      16777216 * (n / 16777216 % 256) + 4294967296 * (n / 4294967296 % 256) +
      1099511627776 * (n / 1099511627776 % 256) +
      281474976710656 * (n / 281474976710656 % 256) +
      72057594037927936 * (n / 72057594037927936 % 256) = n := by
  omega

private theorem le64_digit (v0 v1 v2 v3 v4 v5 v6 v7 : Nat)
    (h0 : v0 < 256) (h1 : v1 < 256) (h2 : v2 < 256) (h3 : v3 < 256)
    (h4 : v4 < 256) (h5 : v5 < 256) (h6 : v6 < 256) (h7 : v7 < 256)
    (N : Nat)
    (hN : N = v0 + 256 * v1 + 65536 * v2 + 16777216 * v3 + 4294967296 * v4 +
      1099511627776 * v5 + 281474976710656 * v6 + 72057594037927936 * v7) :
    N / 1 % 256 = v0 ∧ N / 256 % 256 = v1 ∧ N / 65536 % 256 = v2 ∧
    N / 16777216 % 256 = v3 ∧ N / 4294967296 % 256 = v4 ∧
    N / 1099511627776 % 256 = v5 ∧ N / 281474976710656 % 256 = v6 ∧
    N / 72057594037927936 % 256 = v7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- `field.rs:Goldilocks::to_le_bytes`: eight little-endian bytes of the canonical value. -/
def encodeGoldilocksLe8 (a : Goldilocks) : List UInt8 :=
  [leByte a.val 1, leByte a.val 256, leByte a.val 65536, leByte a.val 16777216,
   leByte a.val 4294967296, leByte a.val 1099511627776, leByte a.val 281474976710656,
   leByte a.val 72057594037927936]

/-- `field.rs:Goldilocks::from_le_bytes_canonical` on the first eight bytes: rejects a limb
    `≥ p` and returns the unconsumed tail. -/
def decodeGoldilocksLe8 : List UInt8 → Option (Goldilocks × List UInt8)
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
    if h : le64Value b0 b1 b2 b3 b4 b5 b6 b7 < goldilocksPrime then
      some (⟨le64Value b0 b1 b2 b3 b4 b5 b6 b7, h⟩, rest)
    else none
  | _ => none

theorem decodeGoldilocksLe8_encode (a : Goldilocks) (rest : List UInt8) :
    decodeGoldilocksLe8 (encodeGoldilocksLe8 a ++ rest) = some (a, rest) := by
  have hv : le64Value (leByte a.val 1) (leByte a.val 256) (leByte a.val 65536)
      (leByte a.val 16777216) (leByte a.val 4294967296) (leByte a.val 1099511627776)
      (leByte a.val 281474976710656) (leByte a.val 72057594037927936) = a.val :=
    le64_recompose a.val (Goldilocks.val_lt_two_pow_64 a)
  have hlt : le64Value (leByte a.val 1) (leByte a.val 256) (leByte a.val 65536)
      (leByte a.val 16777216) (leByte a.val 4294967296) (leByte a.val 1099511627776)
      (leByte a.val 281474976710656) (leByte a.val 72057594037927936) < goldilocksPrime := by
    rw [hv]; exact a.isLt
  show decodeGoldilocksLe8
      (leByte a.val 1 :: leByte a.val 256 :: leByte a.val 65536 :: leByte a.val 16777216 ::
        leByte a.val 4294967296 :: leByte a.val 1099511627776 ::
        leByte a.val 281474976710656 :: leByte a.val 72057594037927936 :: rest) = some (a, rest)
  rw [decodeGoldilocksLe8, dite_eq_left hlt]
  exact congrArg (fun g => some (g, rest)) (Goldilocks.ext hv)

theorem decodeGoldilocksLe8_canonical :
    ∀ (bs : List UInt8) (a : Goldilocks) (rest : List UInt8),
      decodeGoldilocksLe8 bs = some (a, rest) → bs = encodeGoldilocksLe8 a ++ rest
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r, a, rest, h => by
    rw [decodeGoldilocksLe8] at h
    by_cases hlt : le64Value b0 b1 b2 b3 b4 b5 b6 b7 < goldilocksPrime
    · rw [dite_eq_left hlt] at h
      obtain ⟨ha, hr⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ :=
        le64_digit b0.toNat b1.toNat b2.toNat b3.toNat b4.toNat b5.toNat b6.toNat b7.toNat
          (UInt8.toNat_lt b0) (UInt8.toNat_lt b1) (UInt8.toNat_lt b2) (UInt8.toNat_lt b3)
          (UInt8.toNat_lt b4) (UInt8.toNat_lt b5) (UInt8.toNat_lt b6) (UInt8.toNat_lt b7)
          (le64Value b0 b1 b2 b3 b4 b5 b6 b7) rfl
      rw [← ha, ← hr]
      show b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: r =
        leByte (le64Value b0 b1 b2 b3 b4 b5 b6 b7) 1 ::
        leByte (le64Value b0 b1 b2 b3 b4 b5 b6 b7) 256 ::
        leByte (le64Value b0 b1 b2 b3 b4 b5 b6 b7) 65536 ::
        leByte (le64Value b0 b1 b2 b3 b4 b5 b6 b7) 16777216 ::
        leByte (le64Value b0 b1 b2 b3 b4 b5 b6 b7) 4294967296 ::
        leByte (le64Value b0 b1 b2 b3 b4 b5 b6 b7) 1099511627776 ::
        leByte (le64Value b0 b1 b2 b3 b4 b5 b6 b7) 281474976710656 ::
        leByte (le64Value b0 b1 b2 b3 b4 b5 b6 b7) 72057594037927936 :: r
      rw [UInt8.toNat_inj.mp ((leByte_toNat _ 1).trans e0),
        UInt8.toNat_inj.mp ((leByte_toNat _ 256).trans e1),
        UInt8.toNat_inj.mp ((leByte_toNat _ 65536).trans e2),
        UInt8.toNat_inj.mp ((leByte_toNat _ 16777216).trans e3),
        UInt8.toNat_inj.mp ((leByte_toNat _ 4294967296).trans e4),
        UInt8.toNat_inj.mp ((leByte_toNat _ 1099511627776).trans e5),
        UInt8.toNat_inj.mp ((leByte_toNat _ 281474976710656).trans e6),
        UInt8.toNat_inj.mp ((leByte_toNat _ 72057594037927936).trans e7)]
    · rw [dite_eq_right hlt] at h; cases h
  | [], _, _, h => by cases h
  | [_], _, _, h => by cases h
  | [_, _], _, _, h => by cases h
  | [_, _, _], _, _, h => by cases h
  | [_, _, _, _], _, _, h => by cases h
  | [_, _, _, _, _], _, _, h => by cases h
  | [_, _, _, _, _, _], _, _, h => by cases h
  | [_, _, _, _, _, _, _], _, _, h => by cases h

/-- `field.rs:GoldilocksExt4::to_le_bytes`: the four limbs `[c0.c0, c0.c1, c1.c0, c1.c1]`, eight
    little-endian bytes each. -/
def encodeExt4Bytes32 (x : GoldilocksExt4) : List UInt8 :=
  encodeGoldilocksLe8 x.c0.c0 ++ (encodeGoldilocksLe8 x.c0.c1 ++
    (encodeGoldilocksLe8 x.c1.c0 ++ (encodeGoldilocksLe8 x.c1.c1 ++ [])))

/-- `field.rs:GoldilocksExt4::from_le_bytes_canonical`: accepts exactly 32 bytes whose four
    limbs are all `< p`. -/
def decodeExt4Bytes32 (bs : List UInt8) : Option GoldilocksExt4 :=
  match decodeGoldilocksLe8 bs with
  | none => none
  | some (l0, r0) =>
    match decodeGoldilocksLe8 r0 with
    | none => none
    | some (l1, r1) =>
      match decodeGoldilocksLe8 r1 with
      | none => none
      | some (l2, r2) =>
        match decodeGoldilocksLe8 r2 with
        | some (l3, []) => some (GoldilocksExt4.ofLimbs l0 l1 l2 l3)
        | _ => none

theorem encodeExt4Bytes32_length (x : GoldilocksExt4) : (encodeExt4Bytes32 x).length = 32 := by
  rfl

/-- **Canonical 32-byte roundtrip.** -/
theorem decodeExt4Bytes32_encode (x : GoldilocksExt4) :
    decodeExt4Bytes32 (encodeExt4Bytes32 x) = some x := by
  obtain ⟨⟨a0, a1⟩, ⟨a2, a3⟩⟩ := x
  simp only [decodeExt4Bytes32, encodeExt4Bytes32, decodeGoldilocksLe8_encode,
    GoldilocksExt4.ofLimbs]

/-- **Non-malleability.** Every accepted byte string is the canonical encoding of the decoded
    element; in particular a string with a limb `≥ p`, or of length other than 32, is rejected. -/
theorem decodeExt4Bytes32_canonical (bs : List UInt8) (x : GoldilocksExt4)
    (h : decodeExt4Bytes32 bs = some x) : encodeExt4Bytes32 x = bs := by
  unfold decodeExt4Bytes32 at h
  cases h0 : decodeGoldilocksLe8 bs with
  | none => rw [h0] at h; cases h
  | some p0 =>
    obtain ⟨l0, r0⟩ := p0
    rw [h0] at h
    dsimp only at h
    cases h1 : decodeGoldilocksLe8 r0 with
    | none => rw [h1] at h; cases h
    | some p1 =>
      obtain ⟨l1, r1⟩ := p1
      rw [h1] at h
      dsimp only at h
      cases h2 : decodeGoldilocksLe8 r1 with
      | none => rw [h2] at h; cases h
      | some p2 =>
        obtain ⟨l2, r2⟩ := p2
        rw [h2] at h
        dsimp only at h
        cases h3 : decodeGoldilocksLe8 r2 with
        | none => rw [h3] at h; cases h
        | some p3 =>
          obtain ⟨l3, r3⟩ := p3
          rw [h3] at h
          cases r3 with
          | cons _ _ => cases h
          | nil =>
            have hx : GoldilocksExt4.ofLimbs l0 l1 l2 l3 = x := Option.some.inj h
            rw [← hx, decodeGoldilocksLe8_canonical bs l0 r0 h0,
              decodeGoldilocksLe8_canonical r0 l1 r1 h1,
              decodeGoldilocksLe8_canonical r1 l2 r2 h2,
              decodeGoldilocksLe8_canonical r2 l3 [] h3]
            rfl

/-- Two byte strings that decode to the same element are equal. -/
theorem decodeExt4Bytes32_injective (bs bs' : List UInt8) (x : GoldilocksExt4)
    (h : decodeExt4Bytes32 bs = some x) (h' : decodeExt4Bytes32 bs' = some x) : bs = bs' :=
  (decodeExt4Bytes32_canonical bs x h).symm.trans (decodeExt4Bytes32_canonical bs' x h')

/-- A limb equal to `p` (non-canonical encoding of `0`) is rejected. -/
theorem decodeExt4Bytes32_rejects_noncanonical_limb :
    decodeExt4Bytes32
      ([1, 0, 0, 0, 255, 255, 255, 255] ++ List.replicate 24 (0 : UInt8)) = none ∧
    decodeExt4Bytes32 (List.replicate 32 (0 : UInt8)) = some GoldilocksExt4.zero := by
  decide

/-! ### Deployed multi-stage WHIR schedule and extension-field error denominators (`pcs.rs`) -/

/-- `pcs.rs:WhirStageSpec`. -/
structure WhirStageSpec where
  /-- Reed-Solomon blowup `1 / ρ_i` of the stage oracle. -/
  blowup : Nat
  /-- Multilinear variables folded during the stage. -/
  stepVars : Nat
  /-- Coset fibers opened from the stage oracle. -/
  numQueries : Nat
  deriving DecidableEq, Repr

/-- `pcs.rs:WhirSecurityRegime`: the query-accounting regime that fixes the per-stage query
    counts. The two `habr24` regimes count agreement `ρ` per query (up-to-capacity proximity,
    adopted by the source as a conjecture); `bciksJohnson128` counts agreement `sqrt ρ`. -/
inductive WhirSecurityRegime where
  | habr24Classical128
  | habr24PostQuantum128
  | bciksJohnson128
  | habr24Qrom128
  | bciksJohnsonQrom128
  deriving DecidableEq, Repr

/-- `pcs.rs:WhirSchedule`. -/
structure WhirSchedule where
  regime : WhirSecurityRegime
  earlyStopVars : Nat
  stages : List WhirStageSpec
  deriving DecidableEq, Repr

/-- `pcs.rs:PCS_POW_BITS`: per-stage transcript proof-of-work difficulty. -/
def whirPowBits : Nat := 16

/-- `pcs.rs:legacy_stage_geometry`, defined by the source for `2 ≤ numVars ≤ 24`: blowups,
    folded variables and early-stop count of every stage, carrying the fixed query counts
    `56 / 30 / 21 / 18` (`68` for a single stage) that `WhirSecurityRegime.schedule` overrides. -/
def whirLegacyStageGeometry (numVars : Nat) : WhirSchedule :=
  if numVars ≤ 6 then
    let es := if numVars ≤ 3 then 1 else 2
    ⟨.habr24PostQuantum128, es, [⟨16, numVars - es, 68⟩]⟩
  else if numVars ≤ 11 then
    let es := if numVars ≤ 8 then 3 else 4
    let rem := numVars - es
    let s0 := (rem + 1) / 2
    ⟨.habr24PostQuantum128, es, [⟨4, s0, 56⟩, ⟨16, rem - s0, 30⟩]⟩
  else if numVars ≤ 16 then
    let es := if numVars ≤ 13 then 4 else if numVars ≤ 15 then 5 else 6
    let rem := numVars - es
    let s0 := min 4 (rem - 4)
    let s1 := (rem - s0) / 2
    ⟨.habr24PostQuantum128, es, [⟨4, s0, 56⟩, ⟨16, s1, 30⟩, ⟨64, rem - s0 - s1, 21⟩]⟩
  else if numVars ≤ 20 then
    ⟨.habr24PostQuantum128, numVars - 12, [⟨4, 5, 56⟩, ⟨16, 3, 30⟩, ⟨64, 4, 21⟩]⟩
  else if numVars = 21 then
    ⟨.habr24PostQuantum128, 8, [⟨4, 6, 56⟩, ⟨16, 3, 30⟩, ⟨64, 4, 21⟩]⟩
  else if numVars = 22 then
    ⟨.habr24PostQuantum128, 8, [⟨4, 6, 56⟩, ⟨16, 4, 30⟩, ⟨64, 4, 21⟩]⟩
  else if numVars = 23 then
    ⟨.habr24PostQuantum128, 7, [⟨4, 6, 56⟩, ⟨16, 4, 30⟩, ⟨64, 3, 21⟩, ⟨256, 3, 18⟩]⟩
  else
    ⟨.habr24PostQuantum128, 8, [⟨4, 6, 56⟩, ⟨16, 4, 30⟩, ⟨64, 3, 21⟩, ⟨256, 3, 18⟩]⟩

/-- `log2` of a supported blowup (`blowup.trailing_zeros()` on `4 | 16 | 64 | 256`). -/
def whirLogBlowup : Nat → Nat
  | 4 => 2
  | 16 => 4
  | 64 => 6
  | 256 => 8
  | _ => 0

/-- Query-exponent target of a regime in bits of `blowup ^ numQueries`: `112`, `128`, `256`, or `512`
    (agreement `sqrt ρ` per query needs twice the exponent for `128` bits). -/
def WhirSecurityRegime.queryExponentBits : WhirSecurityRegime → Nat
  | .habr24Classical128 => 112
  | .habr24PostQuantum128 => 128
  | .bciksJohnson128 => 256
  | .habr24Qrom128 => 256
  | .bciksJohnsonQrom128 => 512

/-- Per-stage query count of `pcs.rs:WhirSecurityRegime::schedule`:
    `ceil(bits / log2 blowup)`, plus one classical or two QROM Johnson queries. -/
def WhirSecurityRegime.numQueries (r : WhirSecurityRegime) (blowup : Nat) : Nat :=
  let q := (r.queryExponentBits + whirLogBlowup blowup - 1) / whirLogBlowup blowup
  match r with
  | .bciksJohnson128 => q + 1
  | .bciksJohnsonQrom128 => q + 2
  | _ => q

/-- `pcs.rs:WhirSecurityRegime::schedule`: the legacy geometry with the regime's query counts. -/
def WhirSecurityRegime.schedule (r : WhirSecurityRegime) (numVars : Nat) : WhirSchedule :=
  ⟨r, (whirLegacyStageGeometry numVars).earlyStopVars,
    (whirLegacyStageGeometry numVars).stages.map
      (fun st => ⟨st.blowup, st.stepVars, r.numQueries st.blowup⟩)⟩

/-- `pcs.rs:whir_stage_schedule`: the default (`habr24Qrom128`) schedule. -/
def whirStageSchedule (numVars : Nat) : WhirSchedule :=
  WhirSecurityRegime.habr24Qrom128.schedule numVars

/-- Denominator `blowup ^ numQueries` of the stage query error `ρ_i ^ q_i`: the error of `q_i`
    fiber queries when a cheating oracle agrees with the code on a `ρ_i` fraction. That
    agreement bound is an input of this accounting; no proximity-gap statement is proved here. -/
def WhirStageSpec.queryErrorDenominator (st : WhirStageSpec) : Nat := st.blowup ^ st.numQueries

/-- Query error denominator times the classical grinding cost `2 ^ whirPowBits` of the stage
    proof of work. A quantum search over nonces pays only about `2 ^ (whirPowBits / 2)`. -/
def WhirStageSpec.fiatShamirDenominator (st : WhirStageSpec) : Nat :=
  2 ^ whirPowBits * st.queryErrorDenominator

/-- Consecutive blowups escalate by a factor of exactly `4`. -/
def whirBlowupsEscalate : List Nat → Bool
  | a :: b :: tl => (b == 4 * a) && whirBlowupsEscalate (b :: tl)
  | _ => true

/-- Production maximum number of sampled fibers per stage. -/
def whirMaxQueryCap : Nat := 512

/-- Structural and accounting checks on `r.schedule numVars` (the conditions of
    `pcs.rs:WhirSchedule::validate` together with the regime's query-exponent target). -/
def whirScheduleWellFormed (r : WhirSecurityRegime) (numVars : Nat) : Bool :=
  let s := r.schedule numVars
  decide (s.earlyStopVars + s.stages.foldl (fun acc st => acc + st.stepVars) 0 = numVars) &&
  decide (1 ≤ s.earlyStopVars) && decide (s.earlyStopVars ≤ 8) &&
  decide (1 ≤ s.stages.length) && decide (s.stages.length ≤ 4) &&
  whirBlowupsEscalate (s.stages.map (·.blowup)) &&
  s.stages.all (fun st =>
    decide (1 ≤ st.stepVars) && decide (st.stepVars ≤ 6) && decide (st.numQueries ≤ whirMaxQueryCap) &&
    decide (2 ^ r.queryExponentBits ≤ st.queryErrorDenominator))

/-- For every regime and every supported variable count the schedule consumes exactly `numVars`
    variables, has `1..4` stages of `1..6` folded variables, stops with `1..8` variables,
    escalates the rate by `4` per stage, opens at most `512` fibers per stage, and every stage
    reaches the regime's query-exponent target `ρ_i^{-q_i} ≥ 2^bits`. -/
theorem whirSchedule_wellFormed (r : WhirSecurityRegime) (numVars : Nat)
    (h2 : 2 ≤ numVars) (h24 : numVars ≤ 24) : whirScheduleWellFormed r numVars = true := by
  have hAll : ∀ (r : WhirSecurityRegime) (k : Nat), k < 25 → 2 ≤ k →
      whirScheduleWellFormed r k = true := by
    intro r
    cases r <;> decide +kernel
  exact hAll r numVars (Nat.lt_succ_of_le h24) h2

/-- Query counts of the three regimes at the supported blowups `4, 16, 64, 256`. -/
theorem whir_regime_query_counts :
    [4, 16, 64, 256].map WhirSecurityRegime.habr24Classical128.numQueries = [56, 28, 19, 14] ∧
    [4, 16, 64, 256].map WhirSecurityRegime.habr24PostQuantum128.numQueries = [64, 32, 22, 16] ∧
    [4, 16, 64, 256].map WhirSecurityRegime.bciksJohnson128.numQueries = [129, 65, 44, 33] := by
  decide

/-- QROM profiles of the production schedule, including the two-query Johnson slack. -/
theorem whir_qrom_regime_query_counts :
    [4, 16, 64, 256].map WhirSecurityRegime.habr24Qrom128.numQueries = [128, 64, 43, 32] ∧
    [4, 16, 64, 256].map WhirSecurityRegime.bciksJohnsonQrom128.numQueries = [258, 130, 88, 66] := by
  decide

/-- Deployed Johnson-QROM geometry at 24 variables. -/
theorem whir_johnson_qrom_schedule_deployed :
    WhirSecurityRegime.bciksJohnsonQrom128.schedule 24 =
      ⟨.bciksJohnsonQrom128, 8,
        [⟨4, 6, 258⟩, ⟨16, 4, 130⟩, ⟨64, 3, 88⟩, ⟨256, 3, 66⟩]⟩ := by decide

/-- Compatibility map from the historical IOP constructor names to the budget profiles. -/
def WhirSecurityRegime.toBudgetRegime : WhirSecurityRegime → Qsag.WhirBudgetRegime
  | .habr24Classical128 => .habr24Classical128
  | .habr24PostQuantum128 => .habr24Interactive128
  | .bciksJohnson128 => .bciksJohnsonClassical128
  | .habr24Qrom128 => .habr24Qrom128
  | .bciksJohnsonQrom128 => .bciksJohnsonQrom128

/-- The IOP and concrete security budget use the same stage geometry and query counts in
    every profile, including the deployed Johnson-QROM `(258,130,88,66)` schedule. -/
theorem whir_iop_budget_schedule_agreement (r : WhirSecurityRegime) :
    ((r.schedule 24).stages.map (fun st => (st.blowup, st.stepVars, st.numQueries))) =
      ((Qsag.whirSchedule4Stage r.toBudgetRegime).map
        (fun st => (st.sqrtBlowup ^ 2, st.stepVars, st.numQueries))) := by
  cases r <;> decide +kernel

/-- The default schedule at `numVars = 20` (the `K = 8` shard): `ρ = 1/4 → 1/16 → 1/64`,
    `q = (128, 64, 43)`, eight variables sent in the clear. -/
theorem whirStageSchedule_deployed :
    whirStageSchedule 20 =
      ⟨.habr24Qrom128, 8, [⟨4, 5, 128⟩, ⟨16, 3, 64⟩, ⟨64, 4, 43⟩]⟩ := by decide

/-- Query error denominators of the default schedule at `numVars = 20`: `2^256, 2^256, 2^258`,
    with no proof-of-work credit. -/
theorem whirStageSchedule_deployed_denominators :
    (whirStageSchedule 20).stages.map (·.queryErrorDenominator) =
      [2 ^ 256, 2 ^ 256, 2 ^ 258] := by decide

/-- The fixed-count legacy geometry at `numVars = 20`: `ρ = 1/4 → 1/16 → 1/64` with
    `q = (56, 30, 21)`. -/
theorem whirLegacyStageGeometry_k8 :
    whirLegacyStageGeometry 20 =
      ⟨.habr24PostQuantum128, 8, [⟨4, 5, 56⟩, ⟨16, 3, 30⟩, ⟨64, 4, 21⟩]⟩ := by decide

/-- Stage denominators of the `q = (56, 30, 21)` geometry: query errors `2^-112, 2^-120, 2^-126`;
    `2^-128, 2^-136, 2^-142` with the full 16-bit classical grinding credit; and
    `2^-120, 2^-128, 2^-134` with the 8-bit credit left by a quantum nonce search. -/
theorem whir_legacy_k8_stage_denominators :
    (whirLegacyStageGeometry 20).stages.map (·.queryErrorDenominator) =
      [2 ^ 112, 2 ^ 120, 2 ^ 126] ∧
    (whirLegacyStageGeometry 20).stages.map (·.fiatShamirDenominator) =
      [2 ^ 128, 2 ^ 136, 2 ^ 142] ∧
    (whirLegacyStageGeometry 20).stages.map (fun st => 2 ^ (whirPowBits / 2) * st.queryErrorDenominator) =
      [2 ^ 120, 2 ^ 128, 2 ^ 134] := by decide

/-- Union bound over the three stages of the `q = (56, 30, 21)` geometry with 16-bit grinding:
    `1/D_0 + 1/D_1 + 1/D_2 ≤ 2^-127` for the Fiat-Shamir denominators `D_i`. -/
theorem whir_legacy_k8_stage_union_bound :
    2 ^ 127 * (2 ^ 136 * 2 ^ 142 + 2 ^ 128 * 2 ^ 142 + 2 ^ 128 * 2 ^ 136) ≤
      2 ^ 128 * 2 ^ 136 * 2 ^ 142 := by decide

/-- Union bound over the three stages of the default schedule at `numVars = 20`, without any
    proof-of-work credit: `1/2^256 + 1/2^256 + 1/2^258 ≤ 2^-254`. -/
theorem whirStageSchedule_deployed_union_bound :
    2 ^ 254 * (2 ^ 256 * 2 ^ 258 + 2 ^ 256 * 2 ^ 258 + 2 ^ 256 * 2 ^ 256) ≤
      2 ^ 256 * 2 ^ 256 * 2 ^ 258 := by decide

/-- Every stage of every supported schedule of regime `r` has
    `ρ_i^{-q_i} ≥ 2 ^ r.queryExponentBits`. -/
theorem whirSchedule_stage_query_ge (r : WhirSecurityRegime) (numVars : Nat) (h2 : 2 ≤ numVars)
    (h24 : numVars ≤ 24) (st : WhirStageSpec) (hSt : st ∈ (r.schedule numVars).stages) :
    2 ^ r.queryExponentBits ≤ st.queryErrorDenominator := by
  have hWf := whirSchedule_wellFormed r numVars h2 h24
  unfold whirScheduleWellFormed at hWf
  simp only [Bool.and_eq_true] at hWf
  have hSt' := List.all_eq_true.mp hWf.2 st hSt
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hSt'
  exact hSt'.2

/-- Every stage of the default schedule has `ρ_i^{-q_i} ≥ 2^256` before any grinding credit. -/
theorem whirStageSchedule_stage_query_ge (numVars : Nat) (h2 : 2 ≤ numVars)
    (h24 : numVars ≤ 24) (st : WhirStageSpec) (hSt : st ∈ (whirStageSchedule numVars).stages) :
    2 ^ 256 ≤ st.queryErrorDenominator :=
  whirSchedule_stage_query_ge .habr24Qrom128 numVars h2 h24 st hSt

/-- `|GoldilocksExt4| = p^4 > 2^255`. -/
theorem goldilocksExt4_card_gt_two_pow_255 : 2 ^ 255 < goldilocksPrime ^ 4 := by decide

theorem goldilocksExt4_card_lt_two_pow_256 : goldilocksPrime ^ 4 < 2 ^ 256 := by decide

theorem goldilocksExt4_card_eq_ext2_card_sq :
    goldilocksPrime ^ 4 = goldilocksPrime ^ 2 * goldilocksPrime ^ 2 := by decide

/-- **Error denominators over `GoldilocksExt4`.** An event count (error numerator) `n ≤ 2^b`
    against a uniform challenge in a set of `p^4` elements has error `n / p^4 < 2^-(255 - b)`. -/
theorem ext4_error_denominator_bound (n b : Nat) (hb : b ≤ 255) (hn : n ≤ 2 ^ b) :
    n * 2 ^ (255 - b) < goldilocksPrime ^ 4 := by
  have h1 : n * 2 ^ (255 - b) ≤ 2 ^ b * 2 ^ (255 - b) := Nat.mul_le_mul_right _ hn
  have h2 : 2 ^ b * 2 ^ (255 - b) = 2 ^ 255 := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hb]
  rw [h2] at h1
  exact Nat.lt_of_le_of_lt h1 goldilocksExt4_card_gt_two_pow_255

/-- **The `GoldilocksExt2` cliff.** Over a challenge set of `p^2 < 2^128` elements, every error
    numerator `n ≥ 2^28` leaves fewer than `100` bits: `n / p^2 > 2^-100`. -/
theorem ext2_error_denominator_cliff (n : Nat) (hn : 2 ^ 28 ≤ n) :
    goldilocksPrime ^ 2 < n * 2 ^ 100 := by
  have h1 : goldilocksPrime ^ 2 < 2 ^ 28 * 2 ^ 100 := by decide
  exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_right _ hn)

/-- Sumcheck Schwartz-Zippel accounting: `rounds` rounds of degree-`d` round polynomials with
    `rounds * d ≤ 2^8` have total error `rounds * d / p^4 < 2^-247`. -/
theorem ext4_sumcheck_schwartz_zippel_denominator (rounds d : Nat) (h : rounds * d ≤ 2 ^ 8) :
    rounds * d * 2 ^ 247 < goldilocksPrime ^ 4 :=
  ext4_error_denominator_bound (rounds * d) 8 (by decide) h

/-- The degree-`8` row sumcheck (`ROW_SUMCHECK_DEGREE = 8`) with at most `32` rounds. -/
theorem ext4_row_sumcheck_denominator (rounds : Nat) (h : rounds ≤ 32) :
    rounds * 8 * 2 ^ 247 < goldilocksPrime ^ 4 :=
  ext4_sumcheck_schwartz_zippel_denominator rounds 8 (Nat.mul_le_mul_right 8 h)

/-- Out-of-domain and folding accounting for a numerator of the shape `|D|^2 * c` with
    `|D| = 2^logDomain ≤ 2^26` and a proximity-parameter factor `c ≤ 2^33` (an assumption on
    the parameters, not derived here): the error is below `2^-170` over `GoldilocksExt4`. -/
theorem ext4_folding_denominator (logDomain c : Nat) (hD : logDomain ≤ 26) (hc : c ≤ 2 ^ 33) :
    2 ^ (2 * logDomain) * c * 2 ^ 170 < goldilocksPrime ^ 4 := by
  have h1 : 2 ^ (2 * logDomain) ≤ 2 ^ 52 :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 2 hD)
  have h2 : 2 ^ (2 * logDomain) * c ≤ 2 ^ 85 :=
    Nat.le_trans (Nat.mul_le_mul h1 hc) (by decide)
  exact ext4_error_denominator_bound (2 ^ (2 * logDomain) * c) 85 (by decide) h2

/-- The same numerator at `|D| = 2^26`, `c = 2^33` leaves fewer than `44` bits over
    `GoldilocksExt2`. -/
theorem ext2_folding_denominator_cliff :
    goldilocksPrime ^ 2 < 2 ^ (2 * 26) * 2 ^ 33 * 2 ^ 44 := by decide

/-- **Schwartz-Zippel root bound over `GoldilocksExt4`.** A non-zero polynomial of formal degree
    `≤ d` has at most `d` roots in any duplicate-free list of challenges. Together with
    `ext4_error_denominator_bound` this is the `d / p^4` per-round sumcheck error. -/
theorem ext4_roundPoly_roots_le (d : Nat) (cs S : List GoldilocksExt4)
    (hS : S.Nodup) (hLen : cs.length ≤ d + 1)
    (hNe : ∃ x₀ : GoldilocksExt4, RoundPoly.evalCoeffs cs x₀ ≠ CommRingOps.zero) :
    (S.filter (fun r => decide (RoundPoly.evalCoeffs cs r = CommRingOps.zero))).length ≤ d :=
  RoundPoly.roots_nodup_length_le d cs S hS hLen hNe

/-- Inhabitedness witness for the schedule and the extension-field accounting. -/
theorem inhabited_whir_ext4_accounting :
    whirScheduleWellFormed .habr24PostQuantum128 20 = true ∧
    (whirStageSchedule 20).stages.length = 3 ∧
    2 ^ 255 < goldilocksPrime ^ 4 ∧
    8 * 32 * 2 ^ 247 < goldilocksPrime ^ 4 ∧
    goldilocksPrime ^ 2 < 2 ^ 28 * 2 ^ 100 ∧
    (CommRingOps.mul GoldilocksExt4.vBasis (GoldilocksExt4.inv GoldilocksExt4.vBasis) =
      (CommRingOps.one : GoldilocksExt4)) :=
  ⟨whirSchedule_wellFormed .habr24PostQuantum128 20 (by decide) (by decide), by decide,
   goldilocksExt4_card_gt_two_pow_255, by decide, by decide,
   GoldilocksExt4.mul_inv_cancel (by decide)⟩

/-! ### Row-committed witness cells: canonical codec, extraction, and binding -/

/-- A canonical prefix codec into trace cells: `dec` parses a value off the front of a cell
    list and returns the unconsumed tail; `enc_dec` says every accepted cell list is the
    canonical encoding followed by that tail. -/
structure CellCodec (α : Type) where
  enc : α → List Goldilocks
  dec : List Goldilocks → Option (α × List Goldilocks)
  dec_enc : ∀ (a : α) (rest : List Goldilocks), dec (enc a ++ rest) = some (a, rest)
  enc_dec : ∀ (cs : List Goldilocks) (a : α) (rest : List Goldilocks),
    dec cs = some (a, rest) → cs = enc a ++ rest

def cellMapDec {α β : Type} (da : List Goldilocks → Option (α × List Goldilocks))
    (f : α → β) (cs : List Goldilocks) : Option (β × List Goldilocks) :=
  match da cs with
  | none => none
  | some (a, r) => some (f a, r)

private theorem cellMapDec_some {α β : Type}
    {da : List Goldilocks → Option (α × List Goldilocks)} {f : α → β}
    {cs : List Goldilocks} {b : β} {rest : List Goldilocks}
    (h : cellMapDec da f cs = some (b, rest)) : ∃ a, da cs = some (a, rest) ∧ f a = b := by
  unfold cellMapDec at h
  cases h1 : da cs with
  | none => rw [h1] at h; cases h
  | some x =>
    obtain ⟨a, r⟩ := x
    rw [h1] at h
    obtain ⟨hb, hr⟩ := Prod.mk.inj (Option.some.inj h)
    subst hr
    exact ⟨a, rfl, hb⟩

private theorem cellMapDec_eq {α β : Type}
    {da : List Goldilocks → Option (α × List Goldilocks)} {f : α → β}
    {cs : List Goldilocks} {a : α} {rest : List Goldilocks}
    (h : da cs = some (a, rest)) : cellMapDec da f cs = some (f a, rest) := by
  simp only [cellMapDec, h]

def cellBind2 {α β γ : Type}
    (da : List Goldilocks → Option (α × List Goldilocks))
    (db : List Goldilocks → Option (β × List Goldilocks))
    (k : α → β → γ) (cs : List Goldilocks) : Option (γ × List Goldilocks) :=
  match da cs with
  | none => none
  | some (a, r1) =>
    match db r1 with
    | none => none
    | some (b, r2) => some (k a b, r2)

private theorem cellBind2_some {α β γ : Type}
    {da : List Goldilocks → Option (α × List Goldilocks)}
    {db : List Goldilocks → Option (β × List Goldilocks)}
    {k : α → β → γ} {cs : List Goldilocks} {c : γ} {rest : List Goldilocks}
    (h : cellBind2 da db k cs = some (c, rest)) :
    ∃ a b r1, da cs = some (a, r1) ∧ db r1 = some (b, rest) ∧ k a b = c := by
  unfold cellBind2 at h
  cases h1 : da cs with
  | none => rw [h1] at h; cases h
  | some x =>
    obtain ⟨a, r1⟩ := x
    rw [h1] at h
    dsimp only at h
    cases h2 : db r1 with
    | none => rw [h2] at h; cases h
    | some y =>
      obtain ⟨b, r2⟩ := y
      rw [h2] at h
      obtain ⟨hc, hr⟩ := Prod.mk.inj (Option.some.inj h)
      subst hr
      exact ⟨a, b, r1, rfl, h2, hc⟩

private theorem cellBind2_eq {α β γ : Type}
    {da : List Goldilocks → Option (α × List Goldilocks)}
    {db : List Goldilocks → Option (β × List Goldilocks)}
    {k : α → β → γ} {cs : List Goldilocks} {a : α} {b : β} {r1 rest : List Goldilocks}
    (h1 : da cs = some (a, r1)) (h2 : db r1 = some (b, rest)) :
    cellBind2 da db k cs = some (k a b, rest) := by
  simp only [cellBind2, h1, h2]

/-- One field element in one cell. -/
def cellFld : CellCodec Goldilocks where
  enc := fun a => [a]
  dec := fun cs =>
    match cs with
    | [] => none
    | c :: rest => some (c, rest)
  dec_enc := fun _ _ => rfl
  enc_dec := fun cs a rest h => by
    match cs, h with
    | [], h => cases h
    | c :: tl, h =>
      obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj h)
      rw [← h1, ← h2]
      rfl

/-- The empty encoding of `Unit`. -/
def cellUnit : CellCodec Unit where
  enc := fun _ => []
  dec := fun cs => some ((), cs)
  dec_enc := fun _ _ => rfl
  enc_dec := fun _ _ _ h => (Prod.mk.inj (Option.some.inj h)).2

/-- Concatenation of two codecs. -/
def cellSeq {α β : Type} (ca : CellCodec α) (cb : CellCodec β) : CellCodec (α × β) where
  enc := fun p => ca.enc p.1 ++ cb.enc p.2
  dec := cellBind2 ca.dec cb.dec Prod.mk
  dec_enc := fun p rest => by
    obtain ⟨a, b⟩ := p
    have e : (ca.enc a ++ cb.enc b) ++ rest = ca.enc a ++ (cb.enc b ++ rest) :=
      List.append_assoc _ _ _
    show cellBind2 ca.dec cb.dec Prod.mk ((ca.enc a ++ cb.enc b) ++ rest) = some ((a, b), rest)
    rw [e]
    exact cellBind2_eq (ca.dec_enc a _) (cb.dec_enc b rest)
  enc_dec := fun cs p rest h => by
    obtain ⟨a, b, r1, h1, h2, hk⟩ := cellBind2_some h
    rw [← hk, ca.enc_dec cs a r1 h1, cb.enc_dec r1 b rest h2]
    exact (List.append_assoc _ _ _).symm

/-- Transport of a codec along a bijection. -/
def cellIso {α β : Type} (c : CellCodec α) (f : α → β) (g : β → α)
    (hfg : ∀ b, f (g b) = b) (hgf : ∀ a, g (f a) = a) : CellCodec β where
  enc := fun b => c.enc (g b)
  dec := cellMapDec c.dec f
  dec_enc := fun b rest => by
    have h := cellMapDec_eq (f := f) (c.dec_enc (g b) rest)
    rw [hfg] at h
    exact h
  enc_dec := fun cs b rest h => by
    obtain ⟨a, h1, hf⟩ := cellMapDec_some h
    have e := c.enc_dec cs a rest h1
    rw [← hf]
    show cs = c.enc (g (f a)) ++ rest
    rw [hgf]
    exact e

def cellSumEnc {α β : Type} (ea : α → List Goldilocks) (eb : β → List Goldilocks) :
    Sum α β → List Goldilocks
  | .inl a => Goldilocks.zero :: ea a
  | .inr b => Goldilocks.one :: eb b

def cellSumDec {α β : Type} (da : List Goldilocks → Option (α × List Goldilocks))
    (db : List Goldilocks → Option (β × List Goldilocks)) :
    List Goldilocks → Option (Sum α β × List Goldilocks)
  | [] => none
  | m :: cs =>
    if m = Goldilocks.zero then cellMapDec da Sum.inl cs
    else if m = Goldilocks.one then cellMapDec db Sum.inr cs
    else none

private theorem goldilocks_one_ne_zero : ¬ (Goldilocks.one = Goldilocks.zero) := by decide

/-- Tagged union: selector cell `0` or `1` followed by the payload; any other selector is
    rejected. -/
def cellSum {α β : Type} (ca : CellCodec α) (cb : CellCodec β) : CellCodec (Sum α β) where
  enc := cellSumEnc ca.enc cb.enc
  dec := cellSumDec ca.dec cb.dec
  dec_enc := fun s rest => by
    match s with
    | .inl a =>
      show cellSumDec ca.dec cb.dec (Goldilocks.zero :: (ca.enc a ++ rest)) = some (Sum.inl a, rest)
      rw [cellSumDec, ite_eq_left rfl]
      exact cellMapDec_eq (ca.dec_enc a rest)
    | .inr b =>
      show cellSumDec ca.dec cb.dec (Goldilocks.one :: (cb.enc b ++ rest)) = some (Sum.inr b, rest)
      rw [cellSumDec, ite_eq_right goldilocks_one_ne_zero, ite_eq_left rfl]
      exact cellMapDec_eq (cb.dec_enc b rest)
  enc_dec := fun cs s rest h => by
    match cs, h with
    | [], h => cases h
    | m :: tl, h =>
      rw [cellSumDec] at h
      by_cases hm0 : m = Goldilocks.zero
      · rw [ite_eq_left hm0] at h
        obtain ⟨a, h1, hf⟩ := cellMapDec_some h
        rw [← hf, hm0, ca.enc_dec tl a rest h1]
        rfl
      · rw [ite_eq_right hm0] at h
        by_cases hm1 : m = Goldilocks.one
        · rw [ite_eq_left hm1] at h
          obtain ⟨b, h1, hf⟩ := cellMapDec_some h
          rw [← hf, hm1, cb.enc_dec tl b rest h1]
          rfl
        · rw [ite_eq_right hm1] at h; cases h

def cellListEnc {α : Type} (enc : α → List Goldilocks) : List α → List Goldilocks
  | [] => [Goldilocks.zero]
  | x :: xs => Goldilocks.one :: (enc x ++ cellListEnc enc xs)

def cellListDec {α : Type} (dec : List Goldilocks → Option (α × List Goldilocks)) :
    Nat → List Goldilocks → Option (List α × List Goldilocks)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, m :: cs =>
    if m = Goldilocks.zero then some ([], cs)
    else if m = Goldilocks.one then cellBind2 dec (cellListDec dec fuel) List.cons cs
    else none

private theorem cellListEnc_length_gt {α : Type} (enc : α → List Goldilocks) :
    ∀ (xs : List α), xs.length < (cellListEnc enc xs).length
  | [] => Nat.zero_lt_succ _
  | x :: xs => by
    have ih := cellListEnc_length_gt enc xs
    show xs.length + 1 < (enc x ++ cellListEnc enc xs).length + 1
    rw [List.length_append]
    exact Nat.succ_lt_succ (Nat.lt_of_lt_of_le ih (Nat.le_add_left _ _))

private theorem cellListDec_enc {α : Type} (c : CellCodec α) :
    ∀ (xs : List α) (fuel : Nat) (rest : List Goldilocks), xs.length < fuel →
      cellListDec c.dec fuel (cellListEnc c.enc xs ++ rest) = some (xs, rest)
  | _, 0, _, h => absurd h (Nat.not_lt_zero _)
  | [], f + 1, rest, _ => by
    show cellListDec c.dec (f + 1) (Goldilocks.zero :: rest) = some ([], rest)
    rw [cellListDec, ite_eq_left rfl]
  | x :: xs, f + 1, rest, h => by
    have ih := cellListDec_enc c xs f rest (Nat.lt_of_succ_lt_succ h)
    have hb := cellBind2_eq (k := List.cons) (c.dec_enc x (cellListEnc c.enc xs ++ rest)) ih
    have e : (c.enc x ++ cellListEnc c.enc xs) ++ rest =
        c.enc x ++ (cellListEnc c.enc xs ++ rest) := List.append_assoc _ _ _
    show cellListDec c.dec (f + 1)
      (Goldilocks.one :: ((c.enc x ++ cellListEnc c.enc xs) ++ rest)) = some (x :: xs, rest)
    rw [e, cellListDec, ite_eq_right goldilocks_one_ne_zero, ite_eq_left rfl]
    exact hb

private theorem cellListDec_canonical {α : Type} (c : CellCodec α) :
    ∀ (fuel : Nat) (cs : List Goldilocks) (xs : List α) (rest : List Goldilocks),
      cellListDec c.dec fuel cs = some (xs, rest) → cs = cellListEnc c.enc xs ++ rest
  | 0, _, _, _, h => by rw [cellListDec] at h; cases h
  | _ + 1, [], _, _, h => by rw [cellListDec] at h; cases h
  | fuel + 1, m :: tl, xs, rest, h => by
    rw [cellListDec] at h
    by_cases hm0 : m = Goldilocks.zero
    · rw [ite_eq_left hm0] at h
      obtain ⟨hx, hr⟩ := Prod.mk.inj (Option.some.inj h)
      rw [← hx, ← hr, hm0]
      rfl
    · rw [ite_eq_right hm0] at h
      by_cases hm1 : m = Goldilocks.one
      · rw [ite_eq_left hm1] at h
        obtain ⟨x, ys, r1, h1, h2, hk⟩ := cellBind2_some h
        rw [← hk, hm1, c.enc_dec tl x r1 h1, cellListDec_canonical c fuel r1 ys rest h2]
        exact (congrArg (List.cons Goldilocks.one) (List.append_assoc _ _ _)).symm
      · rw [ite_eq_right hm1] at h; cases h

/-- Continuation-marked list: each element is preceded by a cell `1`, and the list ends with a
    cell `0`. -/
def cellListOf {α : Type} (c : CellCodec α) : CellCodec (List α) where
  enc := cellListEnc c.enc
  dec := fun cs => cellListDec c.dec cs.length cs
  dec_enc := fun xs rest =>
    cellListDec_enc c xs _ rest
      (Nat.lt_of_lt_of_le (cellListEnc_length_gt c.enc xs)
        (by rw [List.length_append]; exact Nat.le_add_right _ _))
  enc_dec := fun cs xs rest h => cellListDec_canonical c cs.length cs xs rest h

/-- Radix of the natural-number cell encoding: `p - 1`. -/
def cellNatRadix : Nat := goldilocksPrime - 1

/-- The cell value `p - 1`, used as the carry marker of `cellNatEnc`. -/
def goldilocksTop : Goldilocks := ⟨goldilocksPrime - 1, by decide⟩

def cellNatEncAux : Nat → Goldilocks → List Goldilocks
  | 0, r => [r]
  | q + 1, r => goldilocksTop :: cellNatEncAux q r

/-- `n = q * (p - 1) + r` is encoded as `q` carry cells `p - 1` followed by the cell `r`. -/
def cellNatEnc (n : Nat) : List Goldilocks :=
  cellNatEncAux (n / cellNatRadix) (Goldilocks.ofNat (n % cellNatRadix))

def cellNatDec : List Goldilocks → Option (Nat × List Goldilocks)
  | [] => none
  | c :: cs =>
    if c = goldilocksTop then
      match cellNatDec cs with
      | none => none
      | some (n, r) => some (n + cellNatRadix, r)
    else some (c.val, cs)

private theorem goldilocks_val_lt_radix_of_ne_top {c : Goldilocks} (h : c ≠ goldilocksTop) :
    c.val < cellNatRadix := by
  have hne : c.val ≠ cellNatRadix := fun e => h (Goldilocks.ext e)
  have hM : cellNatRadix + 1 = goldilocksPrime := by decide
  have hlt : c.val < cellNatRadix + 1 := by rw [hM]; exact c.isLt
  exact Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt) hne

private theorem cellNatDec_encAux (r : Goldilocks) (hr : r ≠ goldilocksTop) :
    ∀ (q : Nat) (rest : List Goldilocks),
      cellNatDec (cellNatEncAux q r ++ rest) = some (q * cellNatRadix + r.val, rest)
  | 0, rest => by
    show cellNatDec (r :: rest) = some (0 * cellNatRadix + r.val, rest)
    rw [cellNatDec, ite_eq_right hr, Nat.zero_mul, Nat.zero_add]
  | q + 1, rest => by
    have ih := cellNatDec_encAux r hr q rest
    show cellNatDec (goldilocksTop :: (cellNatEncAux q r ++ rest)) =
      some ((q + 1) * cellNatRadix + r.val, rest)
    rw [cellNatDec, ite_eq_left rfl, ih]
    exact congrArg (fun n => some (n, rest))
      (show q * cellNatRadix + r.val + cellNatRadix = (q + 1) * cellNatRadix + r.val by
        rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_right_comm _ _ _)

private theorem cellNatDec_enc (n : Nat) (rest : List Goldilocks) :
    cellNatDec (cellNatEnc n ++ rest) = some (n, rest) := by
  have hpos : 0 < cellNatRadix := by decide
  have hmod : n % cellNatRadix < cellNatRadix := Nat.mod_lt n hpos
  have hRp : cellNatRadix < goldilocksPrime := by decide
  have hval : (Goldilocks.ofNat (n % cellNatRadix)).val = n % cellNatRadix :=
    Nat.mod_eq_of_lt (Nat.lt_trans hmod hRp)
  have hne : Goldilocks.ofNat (n % cellNatRadix) ≠ goldilocksTop := by
    intro e
    have e' : (Goldilocks.ofNat (n % cellNatRadix)).val = cellNatRadix :=
      congrArg Goldilocks.val e
    rw [hval] at e'
    rw [e'] at hmod
    exact Nat.lt_irrefl _ hmod
  have h := cellNatDec_encAux _ hne (n / cellNatRadix) rest
  rw [hval, Nat.div_add_mod'] at h
  exact h

private theorem cellNatDec_canonical :
    ∀ (cs : List Goldilocks) (n : Nat) (rest : List Goldilocks),
      cellNatDec cs = some (n, rest) → cs = cellNatEnc n ++ rest
  | [], _, _, h => by rw [cellNatDec] at h; cases h
  | c :: tl, n, rest, h => by
    have hpos : 0 < cellNatRadix := by decide
    rw [cellNatDec] at h
    by_cases hc : c = goldilocksTop
    · rw [ite_eq_left hc] at h
      cases hd : cellNatDec tl with
      | none => rw [hd] at h; cases h
      | some p =>
        obtain ⟨n', r⟩ := p
        rw [hd] at h
        obtain ⟨hn, hr⟩ := Prod.mk.inj (Option.some.inj h)
        rw [hc, cellNatDec_canonical tl n' r hd, ← hn, ← hr]
        show goldilocksTop ::
            (cellNatEncAux (n' / cellNatRadix) (Goldilocks.ofNat (n' % cellNatRadix)) ++ r) =
          cellNatEncAux ((n' + cellNatRadix) / cellNatRadix)
            (Goldilocks.ofNat ((n' + cellNatRadix) % cellNatRadix)) ++ r
        rw [Nat.add_div_right n' hpos, Nat.add_mod_right]
        rfl
    · rw [ite_eq_right hc] at h
      obtain ⟨hn, hr⟩ := Prod.mk.inj (Option.some.inj h)
      have hlt := goldilocks_val_lt_radix_of_ne_top hc
      have hc' : Goldilocks.ofNat c.val = c := Goldilocks.ext (Nat.mod_eq_of_lt c.isLt)
      rw [← hn, ← hr]
      show c :: tl =
        cellNatEncAux (c.val / cellNatRadix) (Goldilocks.ofNat (c.val % cellNatRadix)) ++ tl
      rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, hc']
      rfl

/-- Unbounded natural numbers in radix `p - 1` with unary carry cells. -/
def cellNat : CellCodec Nat where
  enc := cellNatEnc
  dec := cellNatDec
  dec_enc := cellNatDec_enc
  enc_dec := cellNatDec_canonical

def cellCodecLane4 : CellCodec Lane4 :=
  cellIso (cellSeq cellFld (cellSeq cellFld (cellSeq cellFld cellFld)))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩)
    (fun l => (l.x0, l.x1, l.x2, l.x3))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecDigest5 : CellCodec Digest5 :=
  cellIso (cellSeq cellFld (cellSeq cellFld (cellSeq cellFld (cellSeq cellFld cellFld))))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩)
    (fun d => (d.limb0, d.limb1, d.limb2, d.limb3, d.limb4))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecState12 : CellCodec Poseidon2State12 :=
  cellIso (cellSeq cellCodecLane4 (cellSeq cellCodecLane4 cellCodecLane4))
    (fun t => ⟨t.1, t.2.1, t.2.2⟩)
    (fun s => (s.b0, s.b1, s.b2))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecPerm : CellCodec Poseidon2PermWitness :=
  cellIso
    (cellSeq cellCodecState12 (cellSeq (cellListOf cellCodecState12)
      (cellSeq (cellListOf cellFld) (cellSeq (cellListOf cellCodecState12) cellCodecState12))))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩)
    (fun w => (w.input, w.initExtSbox, w.intSbox, w.termExtSbox, w.output))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecLimb63 : CellCodec Limb63DecompWitness :=
  cellIso (cellSeq cellFld (cellSeq (cellListOf cellFld) cellFld))
    (fun t => ⟨t.1, t.2.1, t.2.2⟩)
    (fun w => (w.limbVal, w.digits, w.topBit))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecHmsg5Decomp : CellCodec Hmsg5DecompWitness :=
  cellIso
    (cellSeq cellCodecLimb63 (cellSeq cellCodecLimb63 (cellSeq cellCodecLimb63
      (cellSeq cellCodecLimb63 cellCodecLimb63))))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩)
    (fun w => (w.l0, w.l1, w.l2, w.l3, w.l4))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecUnaryChain : CellCodec UnaryWotsChainWitness :=
  cellIso
    (cellSeq cellFld (cellSeq cellFld (cellSeq cellFld (cellSeq cellCodecLane4
      (cellSeq cellCodecLane4 (cellSeq cellCodecLane4 (cellSeq cellCodecLane4
        (cellSeq cellCodecPerm (cellSeq cellCodecPerm cellCodecPerm)))))))))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2.1,
      t.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2.2⟩)
    (fun w => (w.act0, w.act1, w.act2, w.sigVal, w.s1, w.s2, w.endVal, w.perm0, w.perm1, w.perm2))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecMerkleLevel : CellCodec MerkleLevelWitness :=
  cellIso
    (cellSeq cellFld (cellSeq cellCodecLane4 (cellSeq cellCodecLane4 (cellSeq cellCodecLane4
      (cellSeq cellCodecLane4 (cellSeq cellCodecPerm cellCodecPerm))))))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2⟩)
    (fun w => (w.dirBit, w.sibling, w.leftChild, w.rightChild, w.parent, w.perm0, w.perm1))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecSponge : CellCodec SpongeAbsorbWitness :=
  cellIso
    (cellSeq cellCodecPerm (cellSeq (cellListOf cellCodecPerm)
      (cellSeq cellCodecPerm cellCodecLane4)))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩)
    (fun w => (w.initPerm, w.pairPerms, w.finalPerm, w.outDigest))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecHmsgStateful : CellCodec HmsgStatefulTraceWitness :=
  cellIso
    (cellSeq cellCodecPerm (cellSeq cellCodecPerm (cellSeq cellCodecPerm cellCodecDigest5)))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩)
    (fun w => (w.perm0, w.perm1, w.perm2, w.outMsg))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecHmsgDetTree : CellCodec HmsgDetTreeTraceWitness :=
  cellIso (cellSeq cellCodecPerm (cellSeq cellCodecPerm cellCodecDigest5))
    (fun t => ⟨t.1, t.2.1, t.2.2⟩)
    (fun w => (w.perm0, w.perm1, w.outMsg))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecWotsLayer : CellCodec WotsLayerTraceWitness :=
  cellIso
    (cellSeq cellNat (cellSeq cellCodecHmsg5Decomp (cellSeq (cellListOf cellCodecUnaryChain)
      (cellSeq cellCodecSponge (cellSeq (cellListOf cellCodecMerkleLevel) cellCodecLane4)))))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2⟩)
    (fun w => (w.tswCtr, w.decomp, w.chains, w.pkSponge, w.merkle, w.rootOut))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecUpperNode : CellCodec UpperLayerTraceNode :=
  cellIso (cellSeq cellCodecHmsgDetTree cellCodecWotsLayer)
    (fun t => ⟨t.1, t.2⟩)
    (fun w => (w.detHmsg, w.wotsStep))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecForsOpening : CellCodec ForsOpeningTraceWitness :=
  cellIso
    (cellSeq cellCodecLane4 (cellSeq cellCodecPerm
      (cellSeq (cellListOf cellCodecMerkleLevel) cellCodecLane4)))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩)
    (fun w => (w.secretVal, w.leafPerm, w.merkle, w.treeRoot))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecForsAndRecover : CellCodec ForsAndRecoverTraceWitness :=
  cellIso (cellSeq (cellListOf cellCodecForsOpening) (cellSeq cellCodecSponge cellCodecLane4))
    (fun t => ⟨t.1, t.2.1, t.2.2⟩)
    (fun w => (w.openings, w.rootsSponge, w.forsPkOut))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecXof : CellCodec StatelessXofTraceWitness :=
  cellIso
    (cellSeq cellCodecPerm (cellSeq cellCodecPerm (cellSeq cellCodecLimb63
      (cellSeq cellCodecLimb63 (cellSeq cellCodecLimb63 (cellSeq cellCodecLimb63
        (cellSeq cellCodecLimb63 (cellSeq cellCodecLimb63 cellCodecLimb63))))))))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2.1, t.2.2.2.2.2.2.1,
      t.2.2.2.2.2.2.2.1, t.2.2.2.2.2.2.2.2⟩)
    (fun w => (w.perm0, w.perm1, w.lim0, w.lim1, w.lim2, w.lim3, w.lim4, w.lim5, w.lim6))
    (fun _ => rfl) (fun _ => rfl)

def cellCodecProfile : CellCodec AggSigProfile :=
  cellIso (cellSum cellUnit cellUnit)
    (fun s => match s with
      | .inl _ => AggSigProfile.xmssPoseidon2
      | .inr _ => AggSigProfile.corduroyPoseidon2)
    (fun p => match p with
      | .xmssPoseidon2 => Sum.inl ()
      | .corduroyPoseidon2 => Sum.inr ())
    (fun p => by cases p <;> rfl)
    (fun s => by cases s <;> rfl)

def cellCodecModeTrace : CellCodec AggSignerModeTrace :=
  cellIso
    (cellSum (cellSeq cellNat cellCodecHmsgStateful)
      (cellSeq cellCodecXof (cellSeq cellCodecForsAndRecover cellCodecHmsgDetTree)))
    (fun s => match s with
      | .inl t => AggSignerModeTrace.stateful t.1 t.2
      | .inr t => AggSignerModeTrace.stateless t.1 t.2.1 t.2.2)
    (fun m => match m with
      | .stateful i h => Sum.inl (i, h)
      | .stateless x f h => Sum.inr (x, f, h))
    (fun m => by cases m <;> rfl)
    (fun s => by cases s <;> rfl)

/-- Canonical cell stream of one signer's witness block: profile selector, `rRand`, the
    stateful / stateless mode trace, the bottom WOTS layer, and the upper hypertree layers. -/
def aggSignerWitnessCodec : CellCodec AggSignerTraceWitness :=
  cellIso
    (cellSeq cellCodecProfile (cellSeq cellCodecLane4 (cellSeq cellCodecModeTrace
      (cellSeq cellCodecWotsLayer (cellListOf cellCodecUpperNode)))))
    (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩)
    (fun w => (w.profile, w.rRand, w.modeTrace, w.layer0, w.upperNodes))
    (fun _ => rfl) (fun _ => rfl)

/-- Witness block committed in a row: the cells from column `14` on (columns `0..13` are the
    boundary columns of `expectedBoundaryCols`) must be exactly one canonical witness encoding,
    with no trailing cell. -/
def decodeRowWitness (row : List Goldilocks) : Option AggSignerTraceWitness :=
  match aggSignerWitnessCodec.dec (row.drop 14) with
  | some (w, []) => some w
  | _ => none

/-- A row decodes to `w` exactly when its cells from column `14` on are the encoding of `w`. -/
theorem decodeRowWitness_eq_some_iff (row : List Goldilocks) (w : AggSignerTraceWitness) :
    decodeRowWitness row = some w ↔ row.drop 14 = aggSignerWitnessCodec.enc w := by
  constructor
  · intro h
    unfold decodeRowWitness at h
    cases hd : aggSignerWitnessCodec.dec (row.drop 14) with
    | none => rw [hd] at h; cases h
    | some p =>
      obtain ⟨w', r⟩ := p
      rw [hd] at h
      cases r with
      | cons _ _ => cases h
      | nil =>
        have hw : w' = w := Option.some.inj h
        have e := aggSignerWitnessCodec.enc_dec _ _ _ hd
        rw [List.append_nil, hw] at e
        exact e
  · intro h
    have hd := aggSignerWitnessCodec.dec_enc w []
    rw [List.append_nil, ← h] at hd
    simp only [decodeRowWitness, hd]

/-- **Deterministic row projection.** Decodes the witness block of each of the first `K` rows;
    fails if a row is missing or does not carry a canonical witness encoding. -/
def extractSignerWitnessesFromRows :
    Nat → List (List Goldilocks) → Option (List AggSignerTraceWitness)
  | 0, _ => some []
  | _ + 1, [] => none
  | k + 1, row :: rows =>
    match decodeRowWitness row with
    | none => none
    | some w =>
      match extractSignerWitnessesFromRows k rows with
      | none => none
      | some ws => some (w :: ws)

/-- Row gate of one active row, a function of the committed row alone: the boundary columns
    `0..13` equal `expectedBoundaryCols`, the remaining cells decode to a witness block, and
    every transition residual of that block vanishes. -/
def committedRowOk (geom : AggSigGeometry) (msg : List UInt8) (pk : AggValidatorPk)
    (row : List Goldilocks) : Bool :=
  decide (row.take 14 = expectedBoundaryCols pk msg) &&
  match decodeRowWitness row with
  | none => false
  | some w => allZeroGoldilocks (signerTraceResiduals geom pk msg w)

def committedActiveRowsOk (geom : AggSigGeometry) (msg : List UInt8) :
    List AggValidatorPk → List (List Goldilocks) → Bool
  | [], padRows => allZeroGoldilocks (padRows.flatMap id)
  | _ :: _, [] => false
  | pk :: pks, row :: rows =>
    committedRowOk geom msg pk row && committedActiveRowsOk geom msg pks rows

/-- All row-gate and boundary constraints as a predicate on the committed `rows` only: no
    witness is supplied beside the rows. -/
def committedRowsSatisfyAllConstraints (stmt : AggArithPublicStmt)
    (rows : List (List Goldilocks)) : Bool :=
  stmt.wellFormed && decide (rows.length = 2 ^ stmt.logRows) &&
  committedActiveRowsOk stmt.geom stmt.msg stmt.committeePks rows

private theorem committedRowOk_unpack {geom : AggSigGeometry} {msg : List UInt8}
    {pk : AggValidatorPk} {row : List Goldilocks}
    (h : committedRowOk geom msg pk row = true) :
    row.take 14 = expectedBoundaryCols pk msg ∧
    ∃ w, decodeRowWitness row = some w ∧
      allZeroGoldilocks (signerTraceResiduals geom pk msg w) = true := by
  unfold committedRowOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hT, hM⟩ := h
  refine ⟨hT, ?_⟩
  cases hd : decodeRowWitness row with
  | none => rw [hd] at hM; cases hM
  | some w => rw [hd] at hM; exact ⟨w, rfl, hM⟩

private theorem committedRowOk_intro {geom : AggSigGeometry} {msg : List UInt8}
    {pk : AggValidatorPk} {row : List Goldilocks} {w : AggSignerTraceWitness}
    (hT : row.take 14 = expectedBoundaryCols pk msg)
    (hd : decodeRowWitness row = some w)
    (hZ : allZeroGoldilocks (signerTraceResiduals geom pk msg w) = true) :
    committedRowOk geom msg pk row = true := by
  unfold committedRowOk
  rw [hd, decide_eq_true hT]
  exact hZ

private theorem committedRow_boundary_gates_vanish {pk : AggValidatorPk} {msg : List UInt8}
    {row : List Goldilocks} (hT : row.take 14 = expectedBoundaryCols pk msg) :
    allZeroGoldilocks (evalRowGateList (boundaryRowGates pk msg) row) = true := by
  have h := boundaryGatesFrom_exact 0 (expectedBoundaryCols pk msg) [] (row.drop 14) rfl
  have hRow : [] ++ expectedBoundaryCols pk msg ++ row.drop 14 = row := by
    rw [List.nil_append, ← hT]
    exact List.take_append_drop 14 row
  rw [hRow] at h
  exact h

private theorem extractSignerWitnesses_succ_cons {k : Nat} {row : List Goldilocks}
    {rows : List (List Goldilocks)} {ws : List AggSignerTraceWitness}
    (h : extractSignerWitnessesFromRows (k + 1) (row :: rows) = some ws) :
    ∃ w wt, decodeRowWitness row = some w ∧
      extractSignerWitnessesFromRows k rows = some wt ∧ ws = w :: wt := by
  rw [extractSignerWitnessesFromRows] at h
  cases hd : decodeRowWitness row with
  | none => rw [hd] at h; cases h
  | some w =>
    rw [hd] at h
    dsimp only at h
    cases hE : extractSignerWitnessesFromRows k rows with
    | none => rw [hE] at h; cases h
    | some wt =>
      rw [hE] at h
      exact ⟨w, wt, rfl, rfl, (Option.some.inj h).symm⟩

private theorem committedActiveRowsOk_extract (geom : AggSigGeometry) (msg : List UInt8) :
    ∀ (pks : List AggValidatorPk) (rows : List (List Goldilocks)),
      committedActiveRowsOk geom msg pks rows = true →
      ∃ ws, extractSignerWitnessesFromRows pks.length rows = some ws ∧
        ws.length = pks.length ∧
        ∀ (k : Nat) (hk : k < pks.length) (hkW : k < ws.length),
          (rows.getD k []).take 14 = expectedBoundaryCols (pks[k]'hk) msg ∧
          decodeRowWitness (rows.getD k []) = some (ws[k]'hkW) ∧
          allZeroGoldilocks (signerTraceResiduals geom (pks[k]'hk) msg (ws[k]'hkW)) = true
  | [], _, _ => ⟨[], rfl, rfl, fun _ hk _ => absurd hk (Nat.not_lt_zero _)⟩
  | _ :: _, [], h => by rw [committedActiveRowsOk] at h; cases h
  | pk :: pks, row :: rows, h => by
    rw [committedActiveRowsOk, Bool.and_eq_true] at h
    obtain ⟨hRow, hRest⟩ := h
    obtain ⟨hT, w, hd, hZ⟩ := committedRowOk_unpack hRow
    obtain ⟨ws, hE, hLen, hA⟩ := committedActiveRowsOk_extract geom msg pks rows hRest
    refine ⟨w :: ws, ?_, congrArg Nat.succ hLen, ?_⟩
    · show extractSignerWitnessesFromRows (pks.length + 1) (row :: rows) = some (w :: ws)
      simp only [extractSignerWitnessesFromRows, hd, hE]
    · intro k hk hkW
      cases k with
      | zero => exact ⟨hT, hd, hZ⟩
      | succ k' => exact hA k' (Nat.lt_of_succ_lt_succ hk) (Nat.lt_of_succ_lt_succ hkW)

private theorem committedActiveRowsOk_at (geom : AggSigGeometry) (msg : List UInt8) :
    ∀ (pks : List AggValidatorPk) (rows : List (List Goldilocks)) (k : Nat)
      (hk : k < pks.length),
      committedActiveRowsOk geom msg pks rows = true →
      committedRowOk geom msg (pks[k]'hk) (rows.getD k []) = true
  | [], _, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | _ :: _, [], _, _, h => by rw [committedActiveRowsOk] at h; cases h
  | _ :: _, _ :: _, 0, _, h => by
    rw [committedActiveRowsOk, Bool.and_eq_true] at h
    exact h.1
  | _ :: pks, _ :: rows, k + 1, hk, h => by
    rw [committedActiveRowsOk, Bool.and_eq_true] at h
    exact committedActiveRowsOk_at geom msg pks rows k (Nat.lt_of_succ_lt_succ hk) h.2

private theorem extractSignerWitnesses_unique :
    ∀ (K : Nat) (rows : List (List Goldilocks)) (ws ws' : List AggSignerTraceWitness),
      extractSignerWitnessesFromRows K rows = some ws →
      ws'.length = K →
      (∀ (k : Nat) (hk : k < ws'.length),
        (rows.getD k []).drop 14 = aggSignerWitnessCodec.enc (ws'[k]'hk)) →
      ws' = ws
  | 0, _, _, _, hE, hLen, _ => by
    rw [extractSignerWitnessesFromRows] at hE
    rw [List.eq_nil_of_length_eq_zero hLen]
    exact Option.some.inj hE
  | _ + 1, [], _, _, hE, _, _ => by rw [extractSignerWitnessesFromRows] at hE; cases hE
  | _ + 1, _ :: _, _, [], _, hLen, _ => by cases hLen
  | K + 1, row :: rows, ws, w' :: ws', hE, hLen, hCells => by
    obtain ⟨w, wt, hd, hEt, hws⟩ := extractSignerWitnesses_succ_cons hE
    have hd' : decodeRowWitness row = some w' :=
      (decodeRowWitness_eq_some_iff row w').mpr (hCells 0 (Nat.zero_lt_succ _))
    have hw : w' = w := Option.some.inj (hd'.symm.trans hd)
    have ih := extractSignerWitnesses_unique K rows wt ws' hEt (Nat.succ.inj hLen)
      (fun k hk => hCells (k + 1) (Nat.succ_lt_succ hk))
    rw [hws, hw, ih]

/-- **Committed rows determine valid witnesses (`committed_rows_extract_valid_witnesses`).**
    If the committed `rows` alone satisfy every row-gate and boundary constraint, then the row
    projection `extractSignerWitnessesFromRows` returns `K` witness blocks; on row `k` the
    boundary gates vanish, the transition residuals of the extracted block vanish, and the block
    yields a signature accepted by `verifyAggNativeSig` for committee key `k`; and any other
    list of `K` witness blocks whose encodings occupy the witness cells of the same rows is
    equal to the extracted one. -/
theorem committed_rows_extract_valid_witnesses (stmt : AggArithPublicStmt)
    (rows : List (List Goldilocks))
    (hSat : committedRowsSatisfyAllConstraints stmt rows = true) :
    ∃ ws : List AggSignerTraceWitness,
      extractSignerWitnessesFromRows stmt.committeePks.length rows = some ws ∧
      ws.length = stmt.committeePks.length ∧
      (∀ (k : Nat) (hkP : k < stmt.committeePks.length) (hkW : k < ws.length),
        allZeroGoldilocks (evalRowGateList (boundaryRowGates (stmt.committeePks[k]'hkP) stmt.msg)
          (rows.getD k [])) = true ∧
        allZeroGoldilocks
          (signerTraceResiduals stmt.geom (stmt.committeePks[k]'hkP) stmt.msg (ws[k]'hkW)) = true ∧
        verifyAggNativeSig stmt.geom (stmt.committeePks[k]'hkP) stmt.msg
          (extractSignerWitnessSig (ws[k]'hkW)) = true) ∧
      (∀ ws' : List AggSignerTraceWitness,
        ws'.length = stmt.committeePks.length →
        (∀ (k : Nat) (hk : k < ws'.length),
          (rows.getD k []).drop 14 = aggSignerWitnessCodec.enc (ws'[k]'hk)) →
        ws' = ws) := by
  unfold committedRowsSatisfyAllConstraints at hSat
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hSat
  obtain ⟨⟨_, _⟩, hAct⟩ := hSat
  obtain ⟨ws, hE, hWsLen, hBody⟩ :=
    committedActiveRowsOk_extract stmt.geom stmt.msg stmt.committeePks rows hAct
  refine ⟨ws, hE, hWsLen, ?_, ?_⟩
  · intro k hkP hkW
    obtain ⟨hT, _, hZ⟩ := hBody k hkP hkW
    exact ⟨committedRow_boundary_gates_vanish hT, hZ,
      signerTraceResiduals_sound stmt.geom (stmt.committeePks[k]'hkP) stmt.msg _ hZ⟩
  · intro ws' hLen' hCells
    exact extractSignerWitnesses_unique _ rows ws ws' hE hLen' hCells

private theorem committedRowsSatisfy_row_at (stmt : AggArithPublicStmt)
    (rows : List (List Goldilocks)) (k : Nat) (hk : k < stmt.committeePks.length)
    (hSat : committedRowsSatisfyAllConstraints stmt rows = true) :
    committedRowOk stmt.geom stmt.msg (stmt.committeePks[k]'hk) (rows.getD k []) = true := by
  unfold committedRowsSatisfyAllConstraints at hSat
  simp only [Bool.and_eq_true] at hSat
  exact committedActiveRowsOk_at stmt.geom stmt.msg stmt.committeePks rows k hk hSat.2

/-- **`#tooth`: a tampered committed row breaks a gate or the binding.** Start from committed
    rows that satisfy every constraint and change any cell of an active row `k`. Then either the
    tampered rows are rejected, or row `k` now decodes to a different witness block (which the
    row gates then check in place of the original one). No change to an active row leaves both
    acceptance and the bound witness intact. -/
theorem tooth_tampered_committed_row_breaks_gate_or_binding (stmt : AggArithPublicStmt)
    (rows rows' : List (List Goldilocks)) (k : Nat) (hk : k < stmt.committeePks.length)
    (hSat : committedRowsSatisfyAllConstraints stmt rows = true)
    (hTamper : rows'.getD k [] ≠ rows.getD k []) :
    committedRowsSatisfyAllConstraints stmt rows' = false ∨
    decodeRowWitness (rows'.getD k []) ≠ decodeRowWitness (rows.getD k []) := by
  cases hV : committedRowsSatisfyAllConstraints stmt rows' with
  | false => exact Or.inl rfl
  | true =>
    refine Or.inr (fun hEq => hTamper ?_)
    obtain ⟨hT, w, hd, _⟩ := committedRowOk_unpack (committedRowsSatisfy_row_at stmt rows k hk hSat)
    obtain ⟨hT', w', hd', _⟩ :=
      committedRowOk_unpack (committedRowsSatisfy_row_at stmt rows' k hk hV)
    have hw : w' = w := Option.some.inj ((hd'.symm.trans hEq).trans hd)
    have hD := (decodeRowWitness_eq_some_iff _ w).mp hd
    have hD' := (decodeRowWitness_eq_some_iff _ w').mp hd'
    rw [hw] at hD'
    rw [← List.take_append_drop 14 (rows'.getD k []), ← List.take_append_drop 14 (rows.getD k []),
      hT, hT', hD, hD']

private theorem expectedBoundaryCols_length (pk : AggValidatorPk) (msg : List UInt8) :
    (expectedBoundaryCols pk msg).length = 14 := by
  unfold expectedBoundaryCols
  rfl

private theorem committedRowOk_honest (geom : AggSigGeometry) (msg : List UInt8)
    (pk : AggValidatorPk) (w : AggSignerTraceWitness)
    (hZ : allZeroGoldilocks (signerTraceResiduals geom pk msg w) = true) :
    committedRowOk geom msg pk (expectedBoundaryCols pk msg ++ aggSignerWitnessCodec.enc w) =
      true := by
  have hLen := expectedBoundaryCols_length pk msg
  exact committedRowOk_intro (List.take_left' hLen)
    ((decodeRowWitness_eq_some_iff _ w).mpr (List.drop_left' hLen)) hZ

/-- Honest committed rows: row `k` is the 14 boundary columns of validator `k` followed by the
    canonical cell stream of its honest witness block; padding rows are zero. -/
def buildCommittedRows (stmt : AggArithPublicStmt) (sigs : List AggNativeSignature) :
    List (List Goldilocks) :=
  (stmt.committeePks.zip sigs).map (fun (pk, sig) =>
    expectedBoundaryCols pk stmt.msg ++
      aggSignerWitnessCodec.enc (buildHonestSignerTraceWitness stmt.geom pk stmt.msg sig)) ++
  List.replicate (2 ^ stmt.logRows - stmt.committeePks.length)
    (List.replicate 14 Goldilocks.zero)

private theorem committedActiveRowsOk_honest (geom : AggSigGeometry) (msg : List UInt8) :
    ∀ (pks : List AggValidatorPk) (sigs : List AggNativeSignature)
      (padRows : List (List Goldilocks)),
      pks.length = sigs.length →
      allZeroGoldilocks (padRows.flatMap id) = true →
      (∀ (k : Nat) (hkP : k < pks.length) (hkS : k < sigs.length),
        verifyAggNativeSig geom (pks[k]'hkP) msg (sigs[k]'hkS) = true) →
      committedActiveRowsOk geom msg pks
        ((pks.zip sigs).map (fun (pk, sig) =>
          expectedBoundaryCols pk msg ++
            aggSignerWitnessCodec.enc (buildHonestSignerTraceWitness geom pk msg sig)) ++
          padRows) = true
  | [], [], _, _, hPad, _ => hPad
  | _ :: _, [], _, hLen, _, _ => by cases hLen
  | [], _ :: _, _, hLen, _, _ => by cases hLen
  | pk :: pks, sig :: sigs, padRows, hLen, hPad, hAll => by
    have hVer0 : verifyAggNativeSig geom pk msg sig = true :=
      hAll 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
    have hSigZ := (signerTraceResiduals_complete geom pk msg sig hVer0).2
    have ih := committedActiveRowsOk_honest geom msg pks sigs padRows (Nat.succ.inj hLen) hPad
      (fun k hkP hkS => hAll (k + 1) (Nat.succ_lt_succ hkP) (Nat.succ_lt_succ hkS))
    have hRow := committedRowOk_honest geom msg pk
      (buildHonestSignerTraceWitness geom pk msg sig) hSigZ
    simp only [List.zip_cons_cons, List.map_cons, List.cons_append, committedActiveRowsOk,
      Bool.and_eq_true]
    exact ⟨hRow, ih⟩

/-- **Completeness of the row-committed layout.** For valid signatures of all `K` committee
    keys, the honest committed rows satisfy every row-only constraint. -/
theorem buildCommittedRows_satisfy_constraints
    (stmt : AggArithPublicStmt) (sigs : List AggNativeSignature)
    (hWf : stmt.wellFormed = true)
    (hLen : sigs.length = stmt.committeePks.length)
    (hAll : ∀ (k : Nat) (hkP : k < stmt.committeePks.length) (hkS : k < sigs.length),
      verifyAggNativeSig stmt.geom (stmt.committeePks[k]'hkP) stmt.msg (sigs[k]'hkS) = true) :
    committedRowsSatisfyAllConstraints stmt (buildCommittedRows stmt sigs) = true := by
  have hKLePow : stmt.committeePks.length ≤ 2 ^ stmt.logRows := by
    unfold AggArithPublicStmt.wellFormed at hWf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hWf
    exact hWf.1.2
  have hRowsLen : (buildCommittedRows stmt sigs).length = 2 ^ stmt.logRows := by
    unfold buildCommittedRows
    rw [List.length_append, List.length_map, List.length_zip, List.length_replicate, hLen,
      Nat.min_self]
    exact Nat.add_sub_of_le hKLePow
  have hAct := committedActiveRowsOk_honest stmt.geom stmt.msg stmt.committeePks sigs
    (List.replicate (2 ^ stmt.logRows - stmt.committeePks.length)
      (List.replicate 14 Goldilocks.zero))
    hLen.symm (allZero_flatMap_replicate_zeros _ 14) hAll
  unfold committedRowsSatisfyAllConstraints
  rw [hWf, decide_eq_true hRowsLen]
  exact hAct

/-- Inhabitedness witness for the row-committed layout: for the audit key and any valid signing
    counters, the honest committed rows satisfy the row-only constraints, so the hypotheses of
    `committed_rows_extract_valid_witnesses` and of the `#tooth` are jointly satisfiable. -/
theorem inhabited_committed_row_extraction :
    let pk0 := deriveAggPublicKey xmssPoseidon2Geom auditSkSeed auditPkSeed
    let stmt : AggArithPublicStmt :=
      { geom := xmssPoseidon2Geom, msg := auditMsg, committeePks := [pk0], logRows := 1 }
    stmt.wellFormed = true ∧
    (∀ (ctrs : ValidSigningCtrs xmssPoseidon2Geom auditSkSeed pk0 auditMsg auditRRand 0),
      let sig0 := signAggNative xmssPoseidon2Geom auditSkSeed pk0 auditMsg auditRRand 0
                    ctrs.layer0Ctr ctrs.upperCtrs
      committedRowsSatisfyAllConstraints stmt (buildCommittedRows stmt [sig0]) = true) := by
  intro pk0 stmt
  have hGeomWf : xmssPoseidon2Geom.wellFormed = true := deployedAggGeometries_wellFormed.1
  have hPkProf : (pk0.profile == xmssPoseidon2Geom.profile) = true := rfl
  have hStmtWf : stmt.wellFormed = true := by
    unfold AggArithPublicStmt.wellFormed
    dsimp only [stmt]
    simp [hGeomWf, hPkProf]
  refine ⟨hStmtWf, fun ctrs => ?_⟩
  intro sig0
  have hVer0 := aggNativeSig_completeness xmssPoseidon2Geom auditSkSeed auditPkSeed
    auditMsg auditRRand 0 hGeomWf ctrs
  refine buildCommittedRows_satisfy_constraints stmt [sig0] hStmtWf rfl ?_
  intro k hkP _
  have hk0 : k = 0 := by simp [stmt] at hkP; omega
  subst hk0
  exact hVer0

/-! ### Execution trace: committed rows only -/

/-- Execution trace on `{0, 1}^logRows`: the committed rows and nothing else. Every witness
    block the constraints speak about is read out of `rows`. -/
structure AggExecutionTrace where
  rows : List (List Goldilocks)
  deriving DecidableEq, Repr

/-- The per-validator witness blocks of a trace, as a function of its committed rows. -/
def AggExecutionTrace.signerWitnesses (stmt : AggArithPublicStmt) (tr : AggExecutionTrace) :
    Option (List AggSignerTraceWitness) :=
  extractSignerWitnessesFromRows stmt.committeePks.length tr.rows

/-- Every row-gate and boundary constraint of the trace: `stmt.wellFormed`, exactly
    `2^stmt.logRows` rows, on each active row `k < K` the 14 boundary columns pinned to
    `(profileFieldTag, pkSeed, pkRoot, mu)` and the transition residuals of the witness block
    decoded from that row, and all-zero padding rows. -/
def traceSatisfiesAllConstraints (stmt : AggArithPublicStmt) (tr : AggExecutionTrace) : Bool :=
  committedRowsSatisfyAllConstraints stmt tr.rows

/-- The canonical honest execution trace of `K` valid `AggNativeSignature`s. -/
def buildHonestAggExecutionTrace (stmt : AggArithPublicStmt)
    (sigs : List AggNativeSignature) : AggExecutionTrace :=
  { rows := buildCommittedRows stmt sigs }

/-- All-zero execution trace (`2^logRows` zero rows of `numCols` cells). -/
def zeroAggExecutionTrace (logRows numCols : Nat) : AggExecutionTrace :=
  { rows := List.replicate (2 ^ logRows) (List.replicate numCols Goldilocks.zero) }

/-- **Per-validator signature extractor.** From a trace satisfying every constraint, reads the
    witness block out of row `k` and returns the signature it encodes, accepted by
    `verifyAggNativeSig` for committee key `k`. -/
def extractValidCommitteeSigsFromTrace (stmt : AggArithPublicStmt) (tr : AggExecutionTrace)
    (hSat : traceSatisfiesAllConstraints stmt tr = true) :
    ∀ (k : Nat) (hk : k < stmt.committeePks.length),
      { sig : AggNativeSignature //
        verifyAggNativeSig stmt.geom (stmt.committeePks[k]'hk) stmt.msg sig = true } :=
  fun k hk =>
    match hd : decodeRowWitness (tr.rows.getD k []) with
    | some w => ⟨extractSignerWitnessSig w, by
        obtain ⟨_, w', hd', hZ⟩ :=
          committedRowOk_unpack (committedRowsSatisfy_row_at stmt tr.rows k hk hSat)
        have hw : w' = w := Option.some.inj (hd'.symm.trans hd)
        rw [← hw]
        exact signerTraceResiduals_sound stmt.geom (stmt.committeePks[k]'hk) stmt.msg w' hZ⟩
    | none => False.elim (by
        obtain ⟨_, w', hd', _⟩ :=
          committedRowOk_unpack (committedRowsSatisfy_row_at stmt tr.rows k hk hSat)
        rw [hd] at hd'
        cases hd')

/-- **Honest execution trace completeness.** Whenever all `K` committee validators have valid
    `AggNativeSignature`s on `stmt.msg`, the honest trace satisfies every constraint. -/
theorem buildHonestAggExecutionTrace_satisfies_constraints
    (stmt : AggArithPublicStmt) (sigs : List AggNativeSignature)
    (hWf : stmt.wellFormed = true)
    (hLen : sigs.length = stmt.committeePks.length)
    (hAll : ∀ (k : Nat) (hkP : k < stmt.committeePks.length) (hkS : k < sigs.length),
      verifyAggNativeSig stmt.geom (stmt.committeePks[k]'hkP) stmt.msg (sigs[k]'hkS) = true) :
    traceSatisfiesAllConstraints stmt (buildHonestAggExecutionTrace stmt sigs) = true :=
  buildCommittedRows_satisfy_constraints stmt sigs hWf hLen hAll

/-- **Row-constraint exactness (`trace_satisfies_constraints_iff_all_k_sigs_valid`).**
    1. Every trace whose constraints vanish has `2^logRows` rows, and its rows decode to `K`
       witness blocks whose boundary gates vanish and which encode signatures accepted by
       `verifyAggNativeSig` for `(stmt.msg, stmt.committeePks[k])`.
    2. A constraint-satisfying trace exists if and only if all `K` committee keys have valid
       `AggNativeSignature`s on `stmt.msg`. -/
theorem trace_satisfies_constraints_iff_all_k_sigs_valid
    (stmt : AggArithPublicStmt) (hWf : stmt.wellFormed = true) :
    (∀ (tr : AggExecutionTrace),
      traceSatisfiesAllConstraints stmt tr = true →
      tr.rows.length = 2 ^ stmt.logRows ∧
      ∃ ws : List AggSignerTraceWitness,
        tr.signerWitnesses stmt = some ws ∧
        ws.length = stmt.committeePks.length ∧
        (∀ (k : Nat) (hkP : k < stmt.committeePks.length) (hkW : k < ws.length),
          allZeroGoldilocks (evalRowGateList (boundaryRowGates (stmt.committeePks[k]'hkP) stmt.msg)
            (tr.rows.getD k [])) = true ∧
          verifyAggNativeSig stmt.geom (stmt.committeePks[k]'hkP) stmt.msg
            (extractSignerWitnessSig (ws[k]'hkW)) = true)) ∧
    (Nonempty { tr : AggExecutionTrace // traceSatisfiesAllConstraints stmt tr = true } ↔
     Nonempty { sigs : List AggNativeSignature //
       sigs.length = stmt.committeePks.length ∧
       ∀ (k : Nat) (hkP : k < stmt.committeePks.length) (hkS : k < sigs.length),
         verifyAggNativeSig stmt.geom (stmt.committeePks[k]'hkP) stmt.msg (sigs[k]'hkS) = true }) := by
  have hSound : ∀ (tr : AggExecutionTrace),
      traceSatisfiesAllConstraints stmt tr = true →
      tr.rows.length = 2 ^ stmt.logRows ∧
      ∃ ws : List AggSignerTraceWitness,
        tr.signerWitnesses stmt = some ws ∧
        ws.length = stmt.committeePks.length ∧
        (∀ (k : Nat) (hkP : k < stmt.committeePks.length) (hkW : k < ws.length),
          allZeroGoldilocks (evalRowGateList (boundaryRowGates (stmt.committeePks[k]'hkP) stmt.msg)
            (tr.rows.getD k [])) = true ∧
          verifyAggNativeSig stmt.geom (stmt.committeePks[k]'hkP) stmt.msg
            (extractSignerWitnessSig (ws[k]'hkW)) = true) := by
    intro tr hSat
    have hLen : tr.rows.length = 2 ^ stmt.logRows := by
      have h := hSat
      unfold traceSatisfiesAllConstraints committedRowsSatisfyAllConstraints at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1.2
    obtain ⟨ws, hE, hWsLen, hPer, _⟩ := committed_rows_extract_valid_witnesses stmt tr.rows hSat
    exact ⟨hLen, ws, hE, hWsLen, fun k hkP hkW => ⟨(hPer k hkP hkW).1, (hPer k hkP hkW).2.2⟩⟩
  refine ⟨hSound, ?_⟩
  constructor
  · rintro ⟨⟨tr, hSat⟩⟩
    obtain ⟨_, ws, _, hWLen, hPerK⟩ := hSound tr hSat
    let sigs := ws.map extractSignerWitnessSig
    refine ⟨⟨sigs, by simp [sigs, hWLen], fun k hkP hkS => ?_⟩⟩
    have hkW : k < ws.length := by simp [sigs] at hkS; exact hkS
    have hEqSig : sigs[k]'hkS = extractSignerWitnessSig (ws[k]'hkW) := by
      simp [sigs]
    rw [hEqSig]
    exact (hPerK k hkP hkW).2
  · rintro ⟨⟨sigs, hLen, hAll⟩⟩
    exact ⟨⟨buildHonestAggExecutionTrace stmt sigs,
      buildHonestAggExecutionTrace_satisfies_constraints stmt sigs hWf hLen hAll⟩⟩

/-- **`#tooth`: the all-zero trace is rejected (`tooth_zero_trace_rejected_for_any_pk`).** For
    every well-formed statement, with no assumption on `pkSeed`, `pkRoot`, `msg` or `numCols`,
    the all-zero rows fail: boundary gate `(row = 0, col = 0)` pins
    `profileFieldTag pk0.profile ∈ {1, 2} ≠ 0`. -/
theorem tooth_zero_trace_rejected_for_any_pk
    (stmt : AggArithPublicStmt) (numCols : Nat)
    (hWf : stmt.wellFormed = true) :
    traceSatisfiesAllConstraints stmt (zeroAggExecutionTrace stmt.logRows numCols) = false := by
  apply Bool.eq_false_iff.mpr
  intro hSat
  have hNonEmpty : stmt.committeePks ≠ [] := by
    unfold AggArithPublicStmt.wellFormed at hWf
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hWf
    exact hWf.1.1.1.2
  have hk : 0 < stmt.committeePks.length := by
    cases hPks : stmt.committeePks with
    | nil => exact absurd hPks hNonEmpty
    | cons _ _ => exact Nat.zero_lt_succ _
  obtain ⟨hT, _⟩ := committedRowOk_unpack
    (committedRowsSatisfy_row_at stmt (zeroAggExecutionTrace stmt.logRows numCols).rows 0 hk hSat)
  have hB := committedRow_boundary_gates_vanish hT
  have hRowEq : (zeroAggExecutionTrace stmt.logRows numCols).rows.getD 0 [] =
      List.replicate numCols Goldilocks.zero := by
    dsimp only [zeroAggExecutionTrace]
    cases hPow : 2 ^ stmt.logRows with
    | zero => exact absurd hPow (Nat.ne_of_gt (Nat.two_pow_pos _))
    | succ m => rfl
  rw [hRowEq] at hB
  unfold boundaryRowGates expectedBoundaryCols at hB
  simp only [List.singleton_append] at hB
  have hCol0 := boundaryGatesFrom_zero_at_col0 (profileFieldTag _) _ _ hB
  rw [getD_zero_replicate_zero] at hCol0
  exact profileFieldTag_ne_zero _ hCol0.symm

/-- Inhabitedness witness for the row constraints: the audit statement is well formed, its
    all-zero trace is rejected, and the honest trace of any valid signing counters is accepted. -/
theorem inhabited_agg_arithmetization_pipeline :
    let pk0 := deriveAggPublicKey xmssPoseidon2Geom auditSkSeed auditPkSeed
    let stmt : AggArithPublicStmt :=
      { geom := xmssPoseidon2Geom, msg := auditMsg, committeePks := [pk0], logRows := 1 }
    stmt.wellFormed = true ∧
    traceSatisfiesAllConstraints stmt (zeroAggExecutionTrace 1 14) = false ∧
    (∀ (ctrs : ValidSigningCtrs xmssPoseidon2Geom auditSkSeed pk0 auditMsg auditRRand 0),
      let sig0 := signAggNative xmssPoseidon2Geom auditSkSeed pk0 auditMsg auditRRand 0
                    ctrs.layer0Ctr ctrs.upperCtrs
      traceSatisfiesAllConstraints stmt (buildHonestAggExecutionTrace stmt [sig0]) = true) := by
  intro pk0 stmt
  obtain ⟨hStmtWf, hHon⟩ := inhabited_committed_row_extraction
  exact ⟨hStmtWf, tooth_zero_trace_rejected_for_any_pk stmt 14 hStmtWf, hHon⟩

/-! ### Constructive collision extraction from two `CanopyMultiProof` transcripts -/

/-- An explicit `nodeHash` collision: one node index, two distinct `(left, right)` pairs, equal
    digests. -/
structure CanopyNodeCollision {D : Type} (nodeHash : Nat → D → D → D) where
  idx : Nat
  l : D
  r : D
  l' : D
  r' : D
  ne : (l, r) ≠ (l', r')
  eq : nodeHash idx l r = nodeHash idx l' r'

/-- An explicit `rootHash` collision on two distinct top nodes. -/
structure CanopyRootCollision {D : Type} (rootHash : Nat → D → D) (logLeaves : Nat) where
  top₁ : D
  top₂ : D
  ne : top₁ ≠ top₂
  eq : rootHash logLeaves top₁ = rootHash logLeaves top₂

private def canopyNodeExtract {D : Type} [DecidableEq D] (nodeHash : Nat → D → D → D)
    {i : Nat} {l r l' r' : D} (h : nodeHash i l r = nodeHash i l' r') :
    PSum (CanopyNodeCollision nodeHash) (l = l' ∧ r = r') :=
  if he : (l, r) = (l', r') then .inr (Prod.mk.inj he) else .inl ⟨i, l, r, l', r', he, h⟩

private def canopyParentExtract {D : Type} [DecidableEq D] (nodeHash : Nat → D → D → D)
    {u : Nat} {hu s hu' s' : D}
    (h : canopyParentHash nodeHash u hu s = canopyParentHash nodeHash u hu' s') :
    PSum (CanopyNodeCollision nodeHash) (hu = hu' ∧ s = s') :=
  if hp : u &&& 1 = 0 then
    canopyNodeExtract nodeHash (i := u >>> 1) (l := hu) (r := s) (l' := hu') (r' := s')
      (by unfold canopyParentHash at h; simp only [hp, ↓reduceIte] at h; exact h)
  else
    match canopyNodeExtract nodeHash (i := u >>> 1) (l := s) (r := hu) (l' := s') (r' := hu')
        (by unfold canopyParentHash at h; simp only [hp, ↓reduceIte] at h; exact h) with
    | .inl c => .inl c
    | .inr e => .inr ⟨e.2, e.1⟩

/-- One level of the lockstep walk over two transcripts: either both level inputs agree, or the
    first differing position is returned as a `nodeHash` collision. -/
private def canopyLevelStepExtract {D : Type} [DecidableEq D] (nodeHash : Nat → D → D → D) :
    (n : Nat) → (a1 a2 : List (Nat × D)) → (s1 s2 : List D) → (b : List (Nat × D)) →
      (t : List D) → a1.length < n → a1.map Prod.fst = a2.map Prod.fst →
      canopyLevelStep nodeHash a1 s1 = some (b, t) →
      canopyLevelStep nodeHash a2 s2 = some (b, t) →
      PSum (CanopyNodeCollision nodeHash) (a1 = a2 ∧ s1 = s2)
  | 0, _, _, _, _, _, _, hLen, _, _, _ => absurd hLen (Nat.not_lt_zero _)
  | _ + 1, [], [], _, _, _, _, _, _, h1, h2 =>
    .inr ⟨rfl, (canopyLevelStep_nil nodeHash h1).2.symm.trans (canopyLevelStep_nil nodeHash h2).2⟩
  | _ + 1, [], _ :: _, _, _, _, _, _, hIdx, _, _ => by cases hIdx
  | _ + 1, _ :: _, [], _, _, _, _, _, hIdx, _, _ => by cases hIdx
  | _ + 1, [_], _ :: _ :: _, _, _, _, _, _, hIdx, _, _ => by cases (List.cons.inj hIdx).2
  | _ + 1, _ :: _ :: _, [_], _, _, _, _, _, hIdx, _, _ => by cases (List.cons.inj hIdx).2
  | _ + 1, [(u, hu)], [(u2, hu2)], s1, s2, b, t, _, hIdx, h1, h2 => by
    have hu_eq : u = u2 := (List.cons.inj hIdx).1
    subst hu_eq
    match s1, s2, h1, h2 with
    | [], _, h1, _ => exact False.elim (by cases h1)
    | _ :: _, [], _, h2 => exact False.elim (by cases h2)
    | c1 :: r1, c2 :: r2, h1, h2 =>
      have f1 : r1 = t ∧ b = [(u >>> 1, canopyParentHash nodeHash u hu c1)] := by
        obtain ⟨c, hs, hb⟩ := canopyLevelStep_single nodeHash h1
        obtain ⟨hc, hr⟩ := List.cons.inj hs
        rw [hc]
        exact ⟨hr, hb⟩
      have f2 : r2 = t ∧ b = [(u >>> 1, canopyParentHash nodeHash u hu2 c2)] := by
        obtain ⟨c, hs, hb⟩ := canopyLevelStep_single nodeHash h2
        obtain ⟨hc, hr⟩ := List.cons.inj hs
        rw [hc]
        exact ⟨hr, hb⟩
      have hH : canopyParentHash nodeHash u hu c1 = canopyParentHash nodeHash u hu2 c2 :=
        (Prod.mk.inj (List.cons.inj (f1.2.symm.trans f2.2)).1).2
      match canopyParentExtract nodeHash hH with
      | .inl c => exact .inl c
      | .inr e => exact .inr ⟨by rw [e.1], by rw [e.2, f1.1, f2.1]⟩
  | n + 1, (u, hu) :: (v, hv) :: tl1, (u2, hu2) :: (v2, hv2) :: tl2, s1, s2, b, t,
      hLen, hIdx, h1, h2 => by
    have hu_eq : u = u2 := (List.cons.inj hIdx).1
    have hv_eq : v = v2 := (List.cons.inj (List.cons.inj hIdx).2).1
    have hTl : tl1.map Prod.fst = tl2.map Prod.fst := (List.cons.inj (List.cons.inj hIdx).2).2
    subst hu_eq; subst hv_eq
    have hLen1 : ((v, hv) :: tl1).length < n := Nat.lt_of_succ_lt_succ hLen
    have hLen2 : tl1.length < n := Nat.lt_of_succ_lt hLen1
    refine if hv' : v = u ^^^ 1 then ?_ else ?_
    · have f1 : canopyLevelStep nodeHash tl1 s1 = some (b.tail, t) ∧
          b = (u >>> 1, nodeHash (u >>> 1) hu hv) :: b.tail := by
        obtain ⟨act, hr, hb⟩ := canopyLevelStep_pair nodeHash hv' h1
        rw [hb]
        exact ⟨hr, rfl⟩
      have f2 : canopyLevelStep nodeHash tl2 s2 = some (b.tail, t) ∧
          b = (u >>> 1, nodeHash (u >>> 1) hu2 hv2) :: b.tail := by
        obtain ⟨act, hr, hb⟩ := canopyLevelStep_pair nodeHash hv' h2
        rw [hb]
        exact ⟨hr, rfl⟩
      have hHead : nodeHash (u >>> 1) hu hv = nodeHash (u >>> 1) hu2 hv2 :=
        (Prod.mk.inj (List.cons.inj (f1.2.symm.trans f2.2)).1).2
      match canopyNodeExtract nodeHash hHead with
      | .inl c => exact .inl c
      | .inr e =>
        match canopyLevelStepExtract nodeHash n tl1 tl2 s1 s2 b.tail t hLen2 hTl f1.1 f2.1 with
        | .inl c => exact .inl c
        | .inr e' => exact .inr ⟨by rw [e.1, e.2, e'.1], e'.2⟩
    · match s1, s2, h1, h2 with
      | [], _, h1, _ =>
        exact False.elim (by
          obtain ⟨_, _, _, hs, _, _⟩ := canopyLevelStep_solo nodeHash hv' h1
          cases hs)
      | _ :: _, [], _, h2 =>
        exact False.elim (by
          obtain ⟨_, _, _, hs, _, _⟩ := canopyLevelStep_solo nodeHash hv' h2
          cases hs)
      | c1 :: r1, c2 :: r2, h1, h2 =>
        have f1 : canopyLevelStep nodeHash ((v, hv) :: tl1) r1 = some (b.tail, t) ∧
            b = (u >>> 1, canopyParentHash nodeHash u hu c1) :: b.tail := by
          obtain ⟨c, rest, act, hs, hr, hb⟩ := canopyLevelStep_solo nodeHash hv' h1
          obtain ⟨hc, hrest⟩ := List.cons.inj hs
          rw [hb, hc, hrest]
          exact ⟨hr, rfl⟩
        have f2 : canopyLevelStep nodeHash ((v, hv2) :: tl2) r2 = some (b.tail, t) ∧
            b = (u >>> 1, canopyParentHash nodeHash u hu2 c2) :: b.tail := by
          obtain ⟨c, rest, act, hs, hr, hb⟩ := canopyLevelStep_solo nodeHash hv' h2
          obtain ⟨hc, hrest⟩ := List.cons.inj hs
          rw [hb, hc, hrest]
          exact ⟨hr, rfl⟩
        have hHead : canopyParentHash nodeHash u hu c1 = canopyParentHash nodeHash u hu2 c2 :=
          (Prod.mk.inj (List.cons.inj (f1.2.symm.trans f2.2)).1).2
        match canopyParentExtract nodeHash hHead with
        | .inl c => exact .inl c
        | .inr e =>
          match canopyLevelStepExtract nodeHash n ((v, hv) :: tl1) ((v, hv2) :: tl2) r1 r2
              b.tail t hLen1 (congrArg (List.cons v) hTl) f1.1 f2.1 with
          | .inl c => exact .inl c
          | .inr e' => exact .inr ⟨by rw [e.1, e'.1], by rw [e.2, e'.2]⟩

/-- The lockstep walk over all `d` levels, from the common final state back to the leaves. -/
private def canopyLevelsExtract {D : Type} [DecidableEq D] (nodeHash : Nat → D → D → D) :
    (d : Nat) → (a1 a2 : List (Nat × D)) → (s1 s2 : List D) → (b : List (Nat × D)) →
      (t : List D) → a1.map Prod.fst = a2.map Prod.fst →
      canopyLevels nodeHash d a1 s1 = some (b, t) →
      canopyLevels nodeHash d a2 s2 = some (b, t) →
      PSum (CanopyNodeCollision nodeHash) (a1 = a2 ∧ s1 = s2)
  | 0, _, _, _, _, _, _, _, h1, h2 => .inr (by
      rw [canopyLevels] at h1 h2
      exact Prod.mk.inj (Option.some.inj (h1.trans h2.symm)))
  | d + 1, a1, a2, s1, s2, b, t, hIdx, h1, h2 => by
    match hs1 : canopyLevelStep nodeHash a1 s1, hs2 : canopyLevelStep nodeHash a2 s2 with
    | none, _ =>
      exact False.elim (by
        obtain ⟨_, _, hStep, _⟩ := canopyLevels_succ nodeHash h1
        rw [hs1] at hStep
        cases hStep)
    | some _, none =>
      exact False.elim (by
        obtain ⟨_, _, hStep, _⟩ := canopyLevels_succ nodeHash h2
        rw [hs2] at hStep
        cases hStep)
    | some (m1, r1), some (m2, r2) =>
      have hRest1 : canopyLevels nodeHash d m1 r1 = some (b, t) := by
        obtain ⟨m, r, hStep, hRest⟩ := canopyLevels_succ nodeHash h1
        rw [hs1] at hStep
        obtain ⟨hm, hr⟩ := Prod.mk.inj (Option.some.inj hStep)
        rw [hm, hr]
        exact hRest
      have hRest2 : canopyLevels nodeHash d m2 r2 = some (b, t) := by
        obtain ⟨m, r, hStep, hRest⟩ := canopyLevels_succ nodeHash h2
        rw [hs2] at hStep
        obtain ⟨hm, hr⟩ := Prod.mk.inj (Option.some.inj hStep)
        rw [hm, hr]
        exact hRest
      have hm1 := (canopyLevelStep_shape nodeHash _ a1 s1 m1 r1 (Nat.lt_succ_self _) hs1).1
      have hm2 := (canopyLevelStep_shape nodeHash _ a2 s2 m2 r2 (Nat.lt_succ_self _) hs2).1
      rw [hIdx] at hm1
      match canopyLevelsExtract nodeHash d m1 m2 r1 r2 b t (hm1.trans hm2.symm) hRest1 hRest2 with
      | .inl c => exact .inl c
      | .inr e =>
        have hs2' : canopyLevelStep nodeHash a2 s2 = some (m1, r1) := by
          rw [hs2, e.1, e.2]
        exact canopyLevelStepExtract nodeHash _ a1 a2 s1 s2 m1 r1 (Nat.lt_succ_self _) hIdx
          hs1 hs2'

private def canopyTopOf {D : Type} (r : Option (List (Nat × D) × List D)) : Option D :=
  match r with
  | some ([(_, top)], []) => some top
  | _ => none

/-- **Constructive collision extractor over `CanopyMultiProof` transcripts.** Given two accepted
    openings of one index set against one commitment that differ in a leaf digest or a sibling,
    the function walks both transcripts level by level and returns an explicit collision: of
    `rootHash` on the two top nodes, or of `nodeHash` at the first node where the two
    transcripts hash different children to the same parent. The result is data in `Type`, built
    with `DecidableEq D` only. -/
def extractCanopyCollision {D : Type} [DecidableEq D]
    (nodeHash : Nat → D → D → D) (rootHash : Nat → D → D)
    (logLeaves : Nat) (commitment : D)
    (leaves₁ leaves₂ : List (Nat × D)) (proof₁ proof₂ : List D)
    (hIdx : leaves₁.map Prod.fst = leaves₂.map Prod.fst)
    (hAcc₁ : verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves₁ proof₁ = true)
    (hAcc₂ : verifyCanopyMultiproof nodeHash rootHash logLeaves commitment leaves₂ proof₂ = true)
    (hNe : (leaves₁, proof₁) ≠ (leaves₂, proof₂)) :
    PSum (CanopyRootCollision rootHash logLeaves) (CanopyNodeCollision nodeHash) := by
  match hT1 : canopyTopOf (canopyLevels nodeHash logLeaves
        (leaves₁.map (fun p => (2 ^ logLeaves + p.1, p.2))) proof₁),
      hT2 : canopyTopOf (canopyLevels nodeHash logLeaves
        (leaves₂.map (fun p => (2 ^ logLeaves + p.1, p.2))) proof₂) with
  | none, _ =>
    exact False.elim (by
      obtain ⟨top, hL, _⟩ :=
        canopy_accept_unpack nodeHash rootHash logLeaves commitment leaves₁ proof₁ hAcc₁
      rw [hL] at hT1
      cases hT1)
  | some _, none =>
    exact False.elim (by
      obtain ⟨top, hL, _⟩ :=
        canopy_accept_unpack nodeHash rootHash logLeaves commitment leaves₂ proof₂ hAcc₂
      rw [hL] at hT2
      cases hT2)
  | some top1, some top2 =>
    have hL1 : canopyLevels nodeHash logLeaves
          (leaves₁.map (fun p => (2 ^ logLeaves + p.1, p.2))) proof₁ = some ([(1, top1)], []) ∧
        rootHash logLeaves top1 = commitment := by
      obtain ⟨top, hL, hR⟩ :=
        canopy_accept_unpack nodeHash rootHash logLeaves commitment leaves₁ proof₁ hAcc₁
      rw [hL] at hT1
      have hEq : some top = some top1 := hT1
      rw [← Option.some.inj hEq]
      exact ⟨hL, hR⟩
    have hL2 : canopyLevels nodeHash logLeaves
          (leaves₂.map (fun p => (2 ^ logLeaves + p.1, p.2))) proof₂ = some ([(1, top2)], []) ∧
        rootHash logLeaves top2 = commitment := by
      obtain ⟨top, hL, hR⟩ :=
        canopy_accept_unpack nodeHash rootHash logLeaves commitment leaves₂ proof₂ hAcc₂
      rw [hL] at hT2
      have hEq : some top = some top2 := hT2
      rw [← Option.some.inj hEq]
      exact ⟨hL, hR⟩
    refine if hTop : top1 = top2 then ?_ else .inl ⟨top1, top2, hTop, hL1.2.trans hL2.2.symm⟩
    have hL2' : canopyLevels nodeHash logLeaves
        (leaves₂.map (fun p => (2 ^ logLeaves + p.1, p.2))) proof₂ = some ([(1, top1)], []) := by
      rw [hTop]; exact hL2.1
    have hIdx' : (leaves₁.map (fun p => (2 ^ logLeaves + p.1, p.2))).map Prod.fst =
        (leaves₂.map (fun p => (2 ^ logLeaves + p.1, p.2))).map Prod.fst := by
      rw [canopy_map_fst, canopy_map_fst, hIdx]
    match canopyLevelsExtract nodeHash logLeaves _ _ proof₁ proof₂ _ _ hIdx' hL1.1 hL2' with
    | .inl c => exact .inr c
    | .inr e =>
      exact False.elim (hNe (by
        rw [canopy_lift_inj (2 ^ logLeaves) leaves₁ leaves₂ e.1, e.2]))

/-- A 32-byte digest. -/
abbrev CanopyDigest32 : Type := { b : ByteArray // b.data.toList.length = 32 }

/-- An explicit collision of a byte-string hash `H`: two distinct inputs with equal outputs,
    as data (a subtype of pairs), not as an existence statement. -/
@[expose] def ExtractedHashCollision (H : ByteArray → ByteArray) : Type :=
  { p : ByteArray × ByteArray // p.1 ≠ p.2 ∧ H p.1 = H p.2 }

/-- `pcs.rs:hash_merkle_internal` input frame: `0x00 || node_idx (4 bytes LE) || left || right`. -/
def canopyNodeFrame (nodeIdx : Nat) (l r : CanopyDigest32) : ByteArray :=
  ⟨⟨(0 : UInt8) ::
    ([leByte nodeIdx 1, leByte nodeIdx 256, leByte nodeIdx 65536, leByte nodeIdx 16777216] ++
      (l.1.data.toList ++ r.1.data.toList))⟩⟩

/-- `pcs.rs:hash_tree_root` input frame: `0x01 || log_leaves || top`. -/
def canopyRootFrame (logLeaves : Nat) (top : CanopyDigest32) : ByteArray :=
  ⟨⟨(1 : UInt8) :: leByte logLeaves 1 :: top.1.data.toList⟩⟩

/-- Node hash induced by `H` on `canopyNodeFrame`, for `H` with 32-byte output. -/
def canopyNodeHashOf (H : ByteArray → ByteArray) (hOut : ∀ x, (H x).data.toList.length = 32)
    (nodeIdx : Nat) (l r : CanopyDigest32) : CanopyDigest32 :=
  ⟨H (canopyNodeFrame nodeIdx l r), hOut _⟩

/-- Root hash induced by `H` on `canopyRootFrame`. -/
def canopyRootHashOf (H : ByteArray → ByteArray) (hOut : ∀ x, (H x).data.toList.length = 32)
    (logLeaves : Nat) (top : CanopyDigest32) : CanopyDigest32 :=
  ⟨H (canopyRootFrame logLeaves top), hOut _⟩

private theorem byteArray_eq_of_toList_eq {a b : ByteArray}
    (h : a.data.toList = b.data.toList) : a = b := by
  obtain ⟨⟨la⟩⟩ := a
  obtain ⟨⟨lb⟩⟩ := b
  have h' : la = lb := h
  rw [h']

private theorem canopyNodeFrame_inj {i : Nat} {l r l' r' : CanopyDigest32}
    (h : canopyNodeFrame i l r = canopyNodeFrame i l' r') : l = l' ∧ r = r' := by
  have h1 : (0 : UInt8) ::
      ([leByte i 1, leByte i 256, leByte i 65536, leByte i 16777216] ++
        (l.1.data.toList ++ r.1.data.toList)) =
      (0 : UInt8) ::
      ([leByte i 1, leByte i 256, leByte i 65536, leByte i 16777216] ++
        (l'.1.data.toList ++ r'.1.data.toList)) :=
    congrArg (fun b : ByteArray => b.data.toList) h
  have h2 := List.append_cancel_left (List.cons.inj h1).2
  obtain ⟨e1, e2⟩ := List.append_inj h2 (l.2.trans l'.2.symm)
  exact ⟨Subtype.ext (byteArray_eq_of_toList_eq e1), Subtype.ext (byteArray_eq_of_toList_eq e2)⟩

private theorem canopyRootFrame_inj {k : Nat} {top top' : CanopyDigest32}
    (h : canopyRootFrame k top = canopyRootFrame k top') : top = top' := by
  have h1 : (1 : UInt8) :: leByte k 1 :: top.1.data.toList =
      (1 : UInt8) :: leByte k 1 :: top'.1.data.toList :=
    congrArg (fun b : ByteArray => b.data.toList) h
  exact Subtype.ext (byteArray_eq_of_toList_eq (List.cons.inj (List.cons.inj h1).2).2)

/-- **Transcript-extracted hash collision.** For a byte-string hash `H` with 32-byte output, two
    accepted `CanopyMultiProof` openings of one index set against one commitment that differ in
    a leaf digest or a sibling yield an explicit pair of distinct frames with equal `H` digests,
    computed from the two transcripts by `extractCanopyCollision`. -/
def extractHashCollisionFromCanopyTranscripts (H : ByteArray → ByteArray)
    (hOut : ∀ x, (H x).data.toList.length = 32)
    (logLeaves : Nat) (commitment : CanopyDigest32)
    (leaves₁ leaves₂ : List (Nat × CanopyDigest32)) (proof₁ proof₂ : List CanopyDigest32)
    (hIdx : leaves₁.map Prod.fst = leaves₂.map Prod.fst)
    (hAcc₁ : verifyCanopyMultiproof (canopyNodeHashOf H hOut) (canopyRootHashOf H hOut)
      logLeaves commitment leaves₁ proof₁ = true)
    (hAcc₂ : verifyCanopyMultiproof (canopyNodeHashOf H hOut) (canopyRootHashOf H hOut)
      logLeaves commitment leaves₂ proof₂ = true)
    (hNe : (leaves₁, proof₁) ≠ (leaves₂, proof₂)) : ExtractedHashCollision H :=
  match extractCanopyCollision (canopyNodeHashOf H hOut) (canopyRootHashOf H hOut) logLeaves
      commitment leaves₁ leaves₂ proof₁ proof₂ hIdx hAcc₁ hAcc₂ hNe with
  | .inl c =>
    ⟨(canopyRootFrame logLeaves c.top₁, canopyRootFrame logLeaves c.top₂),
      fun h => c.ne (canopyRootFrame_inj h), congrArg Subtype.val c.eq⟩
  | .inr c =>
    ⟨(canopyNodeFrame c.idx c.l c.r, canopyNodeFrame c.idx c.l' c.r'),
      fun h => c.ne (by
        obtain ⟨e1, e2⟩ := canopyNodeFrame_inj h
        rw [e1, e2]),
      congrArg Subtype.val c.eq⟩

/-- Two distinct leaf assignments accepted against one `CanopyMultiProof` commitment yield an
    explicit `H` collision. -/
def extractHashCollisionFromDistinctLeaves (H : ByteArray → ByteArray)
    (hOut : ∀ x, (H x).data.toList.length = 32)
    (logLeaves : Nat) (commitment : CanopyDigest32)
    (leaves₁ leaves₂ : List (Nat × CanopyDigest32)) (proof₁ proof₂ : List CanopyDigest32)
    (hIdx : leaves₁.map Prod.fst = leaves₂.map Prod.fst)
    (hAcc₁ : verifyCanopyMultiproof (canopyNodeHashOf H hOut) (canopyRootHashOf H hOut)
      logLeaves commitment leaves₁ proof₁ = true)
    (hAcc₂ : verifyCanopyMultiproof (canopyNodeHashOf H hOut) (canopyRootHashOf H hOut)
      logLeaves commitment leaves₂ proof₂ = true)
    (hNe : leaves₁ ≠ leaves₂) : ExtractedHashCollision H :=
  extractHashCollisionFromCanopyTranscripts H hOut logLeaves commitment leaves₁ leaves₂
    proof₁ proof₂ hIdx hAcc₁ hAcc₂ (fun h => hNe (Prod.mk.inj h).1)

/-- A concrete `ByteArray → ByteArray` digest with 32-byte output: the first 32 bytes of the
    input, zero-padded. It is not collision resistant (it ignores every byte past the 32nd),
    which is what makes the hypotheses of the extractor satisfiable. -/
def canopyPrefixHash (x : ByteArray) : ByteArray :=
  ⟨⟨(x.data.toList ++ List.replicate 32 (0 : UInt8)).take 32⟩⟩

theorem canopyPrefixHash_length (x : ByteArray) :
    (canopyPrefixHash x).data.toList.length = 32 := by
  show ((x.data.toList ++ List.replicate 32 (0 : UInt8)).take 32).length = 32
  rw [List.length_take, List.length_append, List.length_replicate]
  omega

/-- The 32-byte digest whose bytes all equal `b`. -/
def canopyConstDigest (b : UInt8) : CanopyDigest32 :=
  ⟨⟨⟨List.replicate 32 b⟩⟩, List.length_replicate⟩

/-- Commitment of the two-leaf tree with leaf `0` equal to `canopyConstDigest 5` under
    `canopyPrefixHash`; the node frame keeps only 27 bytes of the left child, so the commitment
    does not depend on the right child. -/
def canopyAuditCommitment : CanopyDigest32 :=
  canopyRootHashOf canopyPrefixHash canopyPrefixHash_length 1
    (canopyNodeHashOf canopyPrefixHash canopyPrefixHash_length 1
      (canopyConstDigest 5) (canopyConstDigest 7))

/-- Inhabitedness witness for the transcript extractor over a `ByteArray → ByteArray` 32-byte
    digest: under `canopyPrefixHash`, two `CanopyMultiProof` openings of leaf `0` with different
    siblings are both accepted against `canopyAuditCommitment`, so the hypotheses of
    `extractHashCollisionFromCanopyTranscripts` are jointly satisfiable, and the extractor
    returns an explicit pair of distinct byte strings with equal digests. -/
theorem inhabited_canopy_collision_extractor :
    verifyCanopyMultiproof (canopyNodeHashOf canopyPrefixHash canopyPrefixHash_length)
        (canopyRootHashOf canopyPrefixHash canopyPrefixHash_length) 1 canopyAuditCommitment
        [(0, canopyConstDigest 5)] [canopyConstDigest 7] = true ∧
    verifyCanopyMultiproof (canopyNodeHashOf canopyPrefixHash canopyPrefixHash_length)
        (canopyRootHashOf canopyPrefixHash canopyPrefixHash_length) 1 canopyAuditCommitment
        [(0, canopyConstDigest 5)] [canopyConstDigest 8] = true ∧
    Nonempty (ExtractedHashCollision canopyPrefixHash) :=
  ⟨by decide, by decide,
    ⟨extractHashCollisionFromCanopyTranscripts canopyPrefixHash canopyPrefixHash_length 1
      canopyAuditCommitment [(0, canopyConstDigest 5)] [(0, canopyConstDigest 5)]
      [canopyConstDigest 7] [canopyConstDigest 8] rfl (by decide) (by decide) (by decide)⟩⟩

end Qsag
end
