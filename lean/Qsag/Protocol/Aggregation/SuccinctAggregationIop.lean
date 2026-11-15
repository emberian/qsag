module
/-
# Qsag.Protocol.Aggregation.SuccinctAggregationIop — Packed 4-Limb Goldilocks Signature Engine, Degree-8 Row Sumcheck Arithmetization, the 256-Column `StepOp` Table, Steiner Merkle-Canopy Multi-Proofs, and the `GoldilocksExt4` WHIR Layer

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

Scope. Two row layouts appear. The row-committed layout of §4 is one row per signer (14
boundary columns followed by a canonical cell stream of the structured witness block), and for
it constraint vanishing is equivalent to signature validity. The 256-column `StepOp` table of
§2 transcribes the deployed constraint system; for it this module proves the Group A, shift,
batching and `#tooth` statements listed above, and completeness for inactive slots. The
simulation between the 44-limb step machine and `verifyAggNativeSig` is proved downstream, in
`Qsag.CorduroyAndHemAirCompleteness`: a satisfying `StepOp` table yields an accepted native
signature for every active slot of either profile (`stepOp256TableOk_xmss_extract`,
`stepOp256TableOk_corduroy_extract`), and through it an accepted row-committed trace; an
accepted `XmssPoseidon2` signature yields a satisfying table (`stepXmssRows_of_verify`), while
the `CorduroyPoseidon2` table constructor is not built. The
equality and shift claims have constructive random-`tau` root bounds
of `ell * |S|^(ell - 1)` on `S^ell`, and fixed-order constraint-column batching has a separate
`gamma` root bound. Instantiating that column list with the deployed unique-op offsets, the
transcript binding of the opening, and the recursive merge tree (`lib.rs`) remain open. §4 accounts for error denominators and query counts; it does not prove a
Reed-Solomon proximity-gap or list-decoding statement, so the per-query agreement bound (`ρ`,
or `sqrt ρ` in the Johnson regime) is an input of the accounting.
-/

public import Qsag.Oracle.ConcreteSecurityBudget
import all Qsag.Oracle.ConcreteSecurityBudget
public import Qsag.Math.Constructive
public import Qsag.Math.Goldilocks
import all Qsag.Math.Goldilocks
public import Qsag.Oracle.Keccak
public import Qsag.Oracle.Poseidon2
import all Qsag.Oracle.Poseidon2
public import Qsag.Oracle.UcGames
public import Qsag.Protocol.Aggregation.Aggregation
import all Qsag.Protocol.Aggregation.Aggregation

public import Qsag.Tactic.AssuranceKit

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

