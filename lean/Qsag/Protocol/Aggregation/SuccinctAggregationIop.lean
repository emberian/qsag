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
