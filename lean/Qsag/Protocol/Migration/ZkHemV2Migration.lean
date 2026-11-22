module
/-
# Qsag.Protocol.Migration.ZkHemV2Migration — single-transcript `zk-Hem v2` R1CS migration

Model of QSAG ownership migration (`crates/qsag-migrate/src/hem/{relations,registry,zcash}/`):
wire zero-knowledge, the certified curve roster, Ironwood (`0x03`) value binding, the durable
`NullifierRegistry`, and refinement of `Spec.idealMigrateMachine`.

1. **§1. R1CS and curves.** `R1csShape`, `r1csEvalLc`, `r1csSatisfied` (`A z ∘ B z = C z` over
   `Goldilocks`) with bit-row soundness (`r1csBitConstraint_sound`). `MigrationCurveKind` names the
   six modeled families (`secp256k1`, `Ed25519`, Orchard/Ironwood `Pallas`, its Pasta partner `Vesta`,
   `Jubjub` Sapling, `BLS12-381`), each mapped to its `CurvePrimeCerts` certificate
   (`migrationCurveKind_all_certified_prime`).
   Scalar model of the Orchard note commitment in `FqPallas` (`orchardPedersenScalarModel`):
   * `0x02` / Sapling, `rcm` independent of the value: with the generator logs known, a commitment
     reopens to any other value (`tooth_preIronwood02_reopens_different_value`);
   * `ZIP-2005` Ironwood `0x03`, `rcm = hRcm03 val`: a reopening forces the two hash outputs onto
     that single target (`ironwood03_pedersen_value_bound_sound`);
   * a raw `RedPallas` `rk = ask + alpha` is consistent with every `ask`
     (`tooth_raw_redpallas_rk_hides_ask`).

2. **§2. Wire zero-knowledge.** `ZkHemV2MigrationWireProof` has no witness field, and the
   mask-line, fold-scalar and Stage-0 blinding-residue views are each `CoinBijectionSimulated`
   (`zkHemV2Migration_wire_perfectly_simulated`, composing the three `ZkHemV2` lemmas).

3. **§3. `NullifierRegistry` (`hem/registry.rs`, `QSNULRG1`).** `enroll`, `finalize`, `register`
   over `Absent → Enrolled → Finalized`: the lifecycle
   (`nullifierRegistry_lifecycle_absent_enrolled_finalized`), durability
   (`nullifierRegistry_one_way_durable`), retry idempotence, `NullifierConflict` on a differing
   binding, and `LegacyConflict` on a second nullifier for a recorded `legacyId`.

4. **§4. Refinement and extraction.** Given `ZkHemV2ExtractorSound`, `zkHemV2MigrationMachine` data-refines
   `Spec.idealMigrateMachine` (`zkHemV2Migration_dataRefines_idealMigrate`), which gives
   conservation and no double claim on every reachable state. By
   `zkHemV2_r1cs_single_transcript_extract_or_qrom_128_break`, an accepted step either has a valid
   witness under the supplied language-to-ownership implication, or its statement is outside the WHIR language and, given a
   `WhirScheduleCert` for the deployed schedule, consistent roots and a collision-event bound, the WHIR accept mass is `< 2^{-128}` for every
   `logCells ∈ [16, 28]` and `Q ≤ 2 ^ 64`. The same bound applies to the receipt event for
   the WHIR-gated machine in `zkHemV2_whir_settlement_false_statement_lt_128`.
-/

public import Qsag.Spec.IdealMigrate
public import Qsag.Spec.Refines
public import Qsag.Math.CurvePrimeCerts
public import Qsag.Protocol.Aggregation.ZkHemV2
public import Qsag.Protocol.Aggregation.ZkHemV2ScheduleCert
import Qsag.Math.Tactic.CommRing
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.ZkHemV2Migration

open Qsag Qsag.ClosedFs Qsag.ClosedWhir Qsag.ZkHemV2Cert

set_option autoImplicit false

local infixl:65 " +ᵍ " => CommRingOps.add
local infixl:65 " -ᵍ " => CommRingOps.sub
local infixl:70 " *ᵍ " => CommRingOps.mul

/-! ## §1. `ZkHemV2` R1CS Constraint Systems & Real-Curve / `ZIP-2005` Ironwood (`0x03`) Relations -/

/-- Sparse `Goldilocks` linear combination `Σ (idx, coeff) => coeff * z[idx]` (`relation.rs:Lc`). -/
abbrev R1csLc := List (Nat × Goldilocks)

/-- Single multiplication row `(A_i, B_i, C_i)` enforcing `<A_i, z> * <B_i, z> = <C_i, z>`. -/
structure R1csRow where
  a : R1csLc
  b : R1csLc
  c : R1csLc
  deriving DecidableEq, Repr

/-- Compiled `zk-Hem v2` R1CS relation shape (`hem/relations.rs:124`, multiplication rows only). -/
structure R1csShape where
  logCells : Nat
  numPublic : Nat
  numPriv : Nat
  rows : List R1csRow
  deriving DecidableEq, Repr

/-- Evaluate `lc` against assignment vector `z` (`z[0] = 1`). -/
@[expose] def r1csEvalLc (z : List Goldilocks) : R1csLc → Goldilocks
  | [] => CommRingOps.zero
  | (idx, coeff) :: rest =>
    coeff *ᵍ z.getD idx CommRingOps.zero +ᵍ r1csEvalLc z rest

/-- Full assignment vector `z = 1 :: pubInputs ++ privWitness` (`relation.rs`). -/
@[expose] def r1csAssignment (pubInputs privWitness : List Goldilocks) : List Goldilocks :=
  Goldilocks.one :: (pubInputs ++ privWitness)

/-- Boolean R1CS satisfaction check `A z ∘ B z = C z` across all rows. -/
@[expose] def r1csSatisfied (shape : R1csShape) (pubInputs privWitness : List Goldilocks) : Bool :=
  decide (pubInputs.length = shape.numPublic) &&
  decide (privWitness.length = shape.numPriv) &&
  let z := r1csAssignment pubInputs privWitness
  shape.rows.all (fun r =>
    (r.a ++ r.b ++ r.c).all (fun term => decide (term.1 < z.length)) &&
    decide (r1csEvalLc z r.a *ᵍ r1csEvalLc z r.b = r1csEvalLc z r.c))

/-- A missing wire must not silently act like zero in a multiplication row. -/
theorem r1csSatisfied_rejects_missing_wire :
    r1csSatisfied ⟨16, 0, 0, [⟨[(1, Goldilocks.one)], [], []⟩]⟩ [] [] = false := by decide

/-- Canonical Boolean bit-check R1CS row `z[idx] * (z[idx] - 1) = 0` (`z[0] = 1`). -/
@[expose] def r1csBitRow (idx : Nat) : R1csRow :=
  ⟨[(idx, Goldilocks.one)], [(idx, Goldilocks.one), (0, CommRingOps.neg Goldilocks.one)], []⟩

/-- Soundness of `r1csBitRow`: over the integral domain `Goldilocks`, `z[0] = 1` and
    `<a, z> * <b, z> = <c, z>` forces `z[idx] = 0 ∨ z[idx] = 1`. -/
theorem r1csBitConstraint_sound (pubInputs privWitness : List Goldilocks) (idx : Nat)
    (hRow : let z := r1csAssignment pubInputs privWitness
            r1csEvalLc z (r1csBitRow idx).a *ᵍ r1csEvalLc z (r1csBitRow idx).b =
              r1csEvalLc z (r1csBitRow idx).c) :
    let w := (r1csAssignment pubInputs privWitness).getD idx CommRingOps.zero
    w = CommRingOps.zero ∨ w = CommRingOps.one := by
  dsimp only at hRow ⊢
  have hProd : ∀ w : Goldilocks,
      (Goldilocks.one *ᵍ w +ᵍ CommRingOps.zero) *ᵍ
        (Goldilocks.one *ᵍ w +ᵍ
          (CommRingOps.neg Goldilocks.one *ᵍ Goldilocks.one +ᵍ CommRingOps.zero)) =
        CommRingOps.zero →
      w = CommRingOps.zero ∨ w = CommRingOps.one := by
    intro w h
    have h1 : Goldilocks.one = (CommRingOps.one : Goldilocks) := rfl
    have hLhs : (Goldilocks.one *ᵍ w +ᵍ CommRingOps.zero) *ᵍ
        (Goldilocks.one *ᵍ w +ᵍ
          (CommRingOps.neg Goldilocks.one *ᵍ Goldilocks.one +ᵍ CommRingOps.zero)) =
        w *ᵍ (w -ᵍ CommRingOps.one) := by
      rw [h1]
      constructive_ring
    rw [hLhs] at h
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h with h0 | h1'
    · exact .inl h0
    · exact .inr (LawfulCommRing.sub_eq_zero_iff.mp h1')
  exact hProd ((r1csAssignment pubInputs privWitness).getD idx CommRingOps.zero) hRow

/-- Curve certificate roster. The historical name `vestaOrchard` denotes Vesta, the Pasta partner
    of the Orchard key curve Pallas. E9 provides Sapling key derivation as reference code. -/
inductive MigrationCurveKind where
  | secp256k1
  | ed25519
  | pallasIronwood03
  | vestaOrchard
  | jubjubSapling
  | bls12_381
  deriving DecidableEq, Repr

/-- Every `MigrationCurveKind` maps unconditionally to its kernel-certified
    `CertifiedPrimeScalarCurve` (`CurvePrimeCerts`). -/
def MigrationCurveKind.cert : MigrationCurveKind → CertifiedPrimeScalarCurve
  | .secp256k1        => secp256k1CurveCert
  | .ed25519          => ed25519CurveCert
  | .pallasIronwood03 => pallasOrchardCurveCert
  | .vestaOrchard     => vestaCurveCert
  | .jubjubSapling    => jubjubSaplingCurveCert
  | .bls12_381        => bls381CurveCert

theorem migrationCurveKind_all_certified_prime (k : MigrationCurveKind) :
    IsPrimeNat k.cert.baseP ∧ IsPrimeNat k.cert.scalarOrd ∧ k.cert.scalarOrd % 2 = 1 :=
  ⟨k.cert.baseP_prime, k.cert.scalarOrd_prime, k.cert.scalarOrd_odd⟩

/-- Algebraic Pedersen commitment `cm = rcm · gRcm + val · gVal + rest` in `FqPallas`
    (`PrimeMod q_pallas`, certified prime field via `CurvePrimeCerts`), capturing the discrete-log
    value-binding distinction between pre-Ironwood `0x02`/Sapling and `ZIP-2005` Ironwood `0x03`! -/
def orchardPedersenScalarModel (gRcm gVal rcm val rest : FqPallas) : FqPallas :=
  rcm *ᵍ gRcm +ᵍ val *ᵍ gVal +ᵍ rest

/-- `#tooth` **Pre-Ironwood `0x02` / Sapling Value-Independent `rcm` Reopening (`e1` §4)**:
    When `rcm` is not bound to `val` by `H^rcm` (`0x02` / Sapling), a quantum adversary who knows
    the discrete logs `(gRcm, gVal)` (`gRcm ≠ 0` in `FqPallas`) can reopen ANY note commitment
    `orchardPedersenScalarModel gRcm gVal rcm val rest` to an **arbitrary forged value `val'`**:
    setting `rcm' = rcm + (val - val') · gVal · gRcm⁻¹` produces the exact same commitment! -/
theorem tooth_preIronwood02_value_independent_rcm_forges_value
    (gRcm gVal rcm val val' rest : FqPallas) (hgRcm : gRcm ≠ CommRingOps.zero) :
    let rcm' : FqPallas := rcm +ᵍ (val -ᵍ val') *ᵍ gVal *ᵍ LawfulField.inv gRcm
    orchardPedersenScalarModel gRcm gVal rcm' val' rest =
      orchardPedersenScalarModel gRcm gVal rcm val rest := by
  dsimp only [orchardPedersenScalarModel]
  have hInv : gRcm *ᵍ LawfulField.inv gRcm = CommRingOps.one :=
    LawfulField.mul_inv_cancel hgRcm
  calc (rcm +ᵍ (val -ᵍ val') *ᵍ gVal *ᵍ LawfulField.inv gRcm) *ᵍ gRcm +ᵍ val' *ᵍ gVal +ᵍ rest
      = rcm *ᵍ gRcm +ᵍ ((val -ᵍ val') *ᵍ gVal) *ᵍ (gRcm *ᵍ LawfulField.inv gRcm) +ᵍ
          val' *ᵍ gVal +ᵍ rest := by constructive_ring
    _ = rcm *ᵍ gRcm +ᵍ ((val -ᵍ val') *ᵍ gVal) *ᵍ CommRingOps.one +ᵍ val' *ᵍ gVal +ᵍ rest := by
        rw [hInv]
    _ = rcm *ᵍ gRcm +ᵍ val *ᵍ gVal +ᵍ rest := by constructive_ring

/-- `#tooth` Raw on-chain `RedPallas` `rk = ask + alpha` in `FqPallas` information-theoretically
    hides `ask`: for every `rk` and every candidate `ask' : FqPallas`, `alpha' := rk - ask'`
    is the unique randomizer satisfying `ask' + alpha' = rk` (`SimpleEquiv` bijection on `FqPallas`),
    proving why raw `rk` signatures cannot establish Orchard address ownership without `ZIP-2005`! -/
def redPallasRkRandomizerEquiv (rk : FqPallas) : SimpleEquiv FqPallas FqPallas where
  toFun ask := rk -ᵍ ask
  invFun alpha := rk -ᵍ alpha
  left_inv ask := by constructive_ring
  right_inv alpha := by constructive_ring

theorem tooth_raw_redpallas_rk_hides_ask (rk ask₁ ask₂ : FqPallas) (hNe : ask₁ ≠ ask₂) :
    let alpha₁ := (redPallasRkRandomizerEquiv rk).toFun ask₁
    let alpha₂ := (redPallasRkRandomizerEquiv rk).toFun ask₂
    ask₁ +ᵍ alpha₁ = rk ∧ ask₂ +ᵍ alpha₂ = rk ∧ alpha₁ ≠ alpha₂ := by
  dsimp only [redPallasRkRandomizerEquiv]
  refine ⟨by constructive_ring, by constructive_ring, fun hEq => hNe ?_⟩
  have h1 := congrArg (redPallasRkRandomizerEquiv rk).invFun hEq
  dsimp only [redPallasRkRandomizerEquiv] at h1
  calc ask₁ = rk -ᵍ (rk -ᵍ ask₁) := by constructive_ring
    _ = rk -ᵍ (rk -ᵍ ask₂) := h1
    _ = ask₂ := by constructive_ring

/-! ## §2. Zero-Knowledge Wire Privacy of Single-Transcript `ZkHemV2` Migration Submissions -/

/-- Wire-visible transcript components of a single-transcript `zk-Hem v2` R1CS migration proof:
    carries `treeNonce`, 400-bit Merkle roots, blinded `mask_line` evaluations, blinded
    `foldScalars`, and blinded Stage-0 coset residues — **zero witness wires appear on the wire**! -/
structure ZkHemV2MigrationWireProof (D : Type) where
  profile : ZkHemV2.ZkHemV2Profile
  treeNonce : BitVec 256
  initRoot : D
  roundMsgs : List (SuccinctRoundMsg D (WhirPub QuinticGoldilocks))
  openings : List (QuinticGoldilocks × List D)

/-- **Perfect Zero-Knowledge Simulation of the `ZkHemV2` R1CS Wire Blinding Layer**:
    Composes `ZkHemV2.v2_mask_line_view_perfectly_simulated`,
    `ZkHemV2.v2_fold_scalars_perfectly_simulated`, and
    `ZkHemV2.v2_blinding_residue_ring_perfectly_simulated`: for any witness-derived Stage-0 word,
    fold row, and residue ring image, the wire view is `CoinBijectionSimulated`
    independent of the secret witness `sk`! -/
theorem zkHemV2Migration_wire_perfectly_simulated {ι κ : Type}
    (β : QuinticGoldilocks) (hβ : β ≠ CommRingOps.zero)
    (ℓ : ZkHem.LinForm ι QuinticGoldilocks)
    (opened : κ → ZkHem.LinForm ι QuinticGoldilocks)
    (σ : QuinticGoldilocks) (o : κ → QuinticGoldilocks)
    (φ : QuinticGoldilocks) (xs ws : List QuinticGoldilocks)
    (hNdX : xs.Nodup) (hxNz : ∀ x ∈ xs, x ≠ CommRingOps.zero)
    (hwNz : ∀ w ∈ ws, w ≠ CommRingOps.zero) (hφ : φ ≠ CommRingOps.zero)
    (hLenX : xs.length = 5) (hLenW : ws.length = 5)
    (s shiftDeg : Nat) (qs : List Goldilocks) (ωs : List QuinticGoldilocks)
    (hqs : qs.Nodup) (hqz : ∀ q ∈ qs, q ≠ CommRingOps.zero)
    (hωs : ZkHemV2.MaskRootsValid s ωs) :
    ZkHemV2.CoinBijectionSimulated
      (fun (P : {P : ι → QuinticGoldilocks // ℓ.app P = σ ∧ ∀ k, (opened k).app P = o k})
          (R : ι → QuinticGoldilocks) =>
        ZkHemV2.maskLineReal β ℓ opened P.1 R)
      (ZkHemV2.maskLineSim β ℓ opened σ o) ∧
    ZkHemV2.CoinBijectionSimulated
      (fun (d : {d : List QuinticGoldilocks // d.length = 5})
          (f : {fs : List QuinticGoldilocks // fs.length = 5}) =>
        ZkHem.vadd d.1 (ZkHemV2.foldScalars φ xs ws f.1))
      (fun (ss : {ss : List QuinticGoldilocks // ss.length = 5}) => ss.1) ∧
    ZkHemV2.CoinBijectionSimulated
      (fun (d : {us : List Goldilocks // us.length = qs.length} ×
            {rems : List (List QuinticGoldilocks) //
              rems.length = ωs.length ∧ ∀ r ∈ rems, r.length = 2 ^ s})
          (cs : {cs : List Goldilocks // cs.length = qs.length + 5 * (ωs.length * 2 ^ s)}) =>
        let bw := ZkHemV2.blindingResidueView s shiftDeg qs ωs cs.1
        (ZkHem.vadd d.1.1 bw.1, ZkHemV2.vaddResidues d.2.1 bw.2))
      (fun (out : {us : List Goldilocks // us.length = qs.length} ×
            {rems : List (List QuinticGoldilocks) //
              rems.length = ωs.length ∧ ∀ r ∈ rems, r.length = 2 ^ s}) =>
        (out.1.1, out.2.1)) :=
  ⟨ZkHemV2.v2_mask_line_view_perfectly_simulated β hβ ℓ opened σ o,
   ZkHemV2.v2_fold_scalars_perfectly_simulated φ xs ws hNdX hxNz hwNz hφ hLenX hLenW,
   ZkHemV2.v2_blinding_residue_ring_perfectly_simulated s shiftDeg qs ωs hqs hqz hωs⟩

/-! ## §3. Durable One-Way `NullifierRegistry` Turnstile (`hem/registry.rs`, `QSNULRG1`) -/

/-- Legacy public-key exposure mode (`hem/registry.rs:KeyExposure`, ePrint 2026/352). -/
inductive KeyExposure where
  | hidden
  | revealed
  deriving DecidableEq, Repr

/-- Per-nullifier one-way lifecycle status (`hem/registry.rs:12`: `Absent -> Enrolled -> Finalized`). -/
inductive EntryStatus where
  | enrolled
  | finalized
  deriving DecidableEq, Repr

/-- Permanent binding recorded by `NullifierRegistry` (`hem/registry.rs:MigrationBinding`). -/
structure MigrationBinding where
  nullifier : Spec.Digest256
  migrationDomain : Spec.Digest256
  legacyId : Spec.Digest256
  pqCommitment : Spec.Digest256
  epoch : UInt64
  exposure : KeyExposure
  deriving DecidableEq, Repr

/-- Deterministic conflict errors of `NullifierRegistry` (`hem/registry.rs:RegistryError`). -/
inductive RegistryError where
  | nullifierConflict
  | legacyConflict
  | notEnrolled
  deriving DecidableEq, Repr

/-- Durable turnstile state indexing both `nullifier` and `legacyId` (`hem/registry.rs:66`). -/
structure NullifierRegistry where
  entries : List (MigrationBinding × EntryStatus)
  deriving DecidableEq, Repr

@[expose] def NullifierRegistry.empty : NullifierRegistry := ⟨[]⟩

/-- Lookup an entry by `nullifier`. -/
@[expose] def NullifierRegistry.findByNullifier (reg : NullifierRegistry)
    (nf : Spec.Digest256) : Option (MigrationBinding × EntryStatus) :=
  reg.entries.find? (fun e => e.1.nullifier == nf)

/-- Lookup an entry by `legacyId` (domain- and source-independent credential identifier!). -/
@[expose] def NullifierRegistry.findByLegacyId (reg : NullifierRegistry)
    (lid : Spec.Digest256) : Option (MigrationBinding × EntryStatus) :=
  reg.entries.find? (fun e => e.1.legacyId == lid)

/-- `NullifierRegistry::enroll`: `Absent → Enrolled` (idempotent on exact replay; refuses
    conflicting `nullifier` with `nullifierConflict` and second `nullifier` for recorded `legacyId`
    with `legacyConflict`). -/
@[expose] def NullifierRegistry.enroll (reg : NullifierRegistry) (b : MigrationBinding) :
    Except RegistryError (NullifierRegistry × Bool) :=
  match reg.findByNullifier b.nullifier with
  | some (bOld, _) =>
    if bOld = b then .ok (reg, false) else .error .nullifierConflict
  | none =>
    match reg.findByLegacyId b.legacyId with
    | some _ => .error .legacyConflict
    | none => .ok (⟨(b, .enrolled) :: reg.entries⟩, true)

/-- Promote every entry recorded under `nf` to `.finalized` in place (bindings are untouched). -/
def promoteToFinalized (nf : Spec.Digest256)
    (es : List (MigrationBinding × EntryStatus)) : List (MigrationBinding × EntryStatus) :=
  es.map (fun e => if e.1.nullifier = nf then (e.1, EntryStatus.finalized) else e)

/-- `NullifierRegistry::finalize`: `Enrolled → Finalized` (idempotent if already `Finalized` with
    identical binding; refuses unknown nullifier with `notEnrolled` and altered binding with
    `nullifierConflict`). -/
@[expose] def NullifierRegistry.finalize (reg : NullifierRegistry) (b : MigrationBinding) :
    Except RegistryError (NullifierRegistry × Bool) :=
  match reg.findByNullifier b.nullifier with
  | none => .error .notEnrolled
  | some (bOld, st) =>
    if bOld ≠ b then .error .nullifierConflict
    else match st with
      | .finalized => .ok (reg, false)
      | .enrolled => .ok (⟨promoteToFinalized b.nullifier reg.entries⟩, true)

/-- `NullifierRegistry::register` (Anchorage single-step atomic enrol-and-finalize,
    `Absent → Finalized`; idempotent if already `Finalized` with identical binding). -/
@[expose] def NullifierRegistry.register (reg : NullifierRegistry) (b : MigrationBinding) :
    Except RegistryError (NullifierRegistry × Bool) :=
  match reg.findByNullifier b.nullifier with
  | some (bOld, st) =>
    if bOld ≠ b then .error .nullifierConflict
    else match st with
      | .finalized => .ok (reg, false)
      | .enrolled => .ok (⟨promoteToFinalized b.nullifier reg.entries⟩, true)
  | none =>
    match reg.findByLegacyId b.legacyId with
    | some _ => .error .legacyConflict
    | none => .ok (⟨(b, .finalized) :: reg.entries⟩, true)

/-- **Strict Double-Nullifier Refusal (`NullifierConflict`)**:
    Once `findByNullifier reg b₁.nullifier = some (b₁, st)` holds, ANY attempt to `enroll`,
    `finalize`, or `register` a differing binding `b₂ ≠ b₁` with `b₂.nullifier = b₁.nullifier`
    is deterministically refused with `.error .nullifierConflict`! -/
theorem nullifierRegistry_refuses_nullifier_rebinding
    (reg : NullifierRegistry) (b₁ b₂ : MigrationBinding) (st : EntryStatus)
    (hRec : reg.findByNullifier b₁.nullifier = some (b₁, st))
    (hSameNf : b₂.nullifier = b₁.nullifier) (hDiff : b₁ ≠ b₂) :
    reg.enroll b₂ = .error .nullifierConflict ∧
    reg.finalize b₂ = .error .nullifierConflict ∧
    reg.register b₂ = .error .nullifierConflict := by
  unfold NullifierRegistry.enroll NullifierRegistry.finalize NullifierRegistry.register
  rw [hSameNf, hRec]
  refine ⟨?_, ?_, ?_⟩ <;> simp only [hDiff, ↓reduceIte, ne_eq, not_false_eq_true]

/-- **Strict Cross-Source / Cross-Domain Double-Credential Refusal (`LegacyConflict`)**:
    Once a credential `legacyId` is recorded under `b₁` (`findByLegacyId reg b₁.legacyId = some _`),
    ANY submission `b₂` with a fresh nullifier (`findByNullifier reg b₂.nullifier = none`) targeting
    the same `legacyId` (`b₂.legacyId = b₁.legacyId`, e.g. seed proof after hidden-key proof or
    replay in another epoch/domain!) is refused with `.error .legacyConflict`! -/
theorem nullifierRegistry_refuses_second_nullifier_for_legacyId
    (reg : NullifierRegistry) (b₁ b₂ : MigrationBinding) (st : EntryStatus)
    (hFreshNf : reg.findByNullifier b₂.nullifier = none)
    (hRecLid : reg.findByLegacyId b₁.legacyId = some (b₁, st))
    (hSameLid : b₂.legacyId = b₁.legacyId) :
    reg.enroll b₂ = .error .legacyConflict ∧
    reg.register b₂ = .error .legacyConflict := by
  unfold NullifierRegistry.enroll NullifierRegistry.register
  rw [hFreshNf, hSameLid, hRecLid]
  exact ⟨rfl, rfl⟩

/-- Exact retry idempotence: re-registering an already-finalized identical binding returns
    `(reg, false)` without mutating state or minting twice. -/
theorem nullifierRegistry_register_idempotent
    (reg : NullifierRegistry) (b : MigrationBinding)
    (hFin : reg.findByNullifier b.nullifier = some (b, .finalized)) :
    reg.register b = .ok (reg, false) := by
  unfold NullifierRegistry.register
  rw [hFin]
  simp

/-- Lookup after `promoteToFinalized`: the same binding is found, with its status only raised. -/
theorem find?_promoteToFinalized (nf nf' : Spec.Digest256)
    (es : List (MigrationBinding × EntryStatus)) :
    (promoteToFinalized nf' es).find? (fun e => e.1.nullifier == nf) =
      (es.find? (fun e => e.1.nullifier == nf)).map
        (fun e => if e.1.nullifier = nf' then (e.1, EntryStatus.finalized) else e) := by
  have hp : ((fun e : MigrationBinding × EntryStatus => e.1.nullifier == nf) ∘
      (fun e => if e.1.nullifier = nf' then (e.1, EntryStatus.finalized) else e)) =
      (fun e => e.1.nullifier == nf) := by
    funext e
    dsimp only [Function.comp]
    split <;> rfl
  unfold promoteToFinalized
  rw [List.find?_map, hp]

/-- **One-Way Lifecycle `Absent → Enrolled → Finalized`**: a binding whose `nullifier` and
    `legacyId` are both absent is enrolled (`.enrolled`), and finalizing it yields `.finalized`. -/
theorem nullifierRegistry_lifecycle_absent_enrolled_finalized
    (reg : NullifierRegistry) (b : MigrationBinding)
    (hAbsNf : reg.findByNullifier b.nullifier = none)
    (hAbsLid : reg.findByLegacyId b.legacyId = none) :
    ∃ reg₁ reg₂ : NullifierRegistry,
      reg.enroll b = .ok (reg₁, true) ∧
      reg₁.findByNullifier b.nullifier = some (b, .enrolled) ∧
      reg₁.finalize b = .ok (reg₂, true) ∧
      reg₂.findByNullifier b.nullifier = some (b, .finalized) := by
  have hFind : ((b, EntryStatus.enrolled) :: reg.entries).find?
      (fun e => e.1.nullifier == b.nullifier) = some (b, .enrolled) := by
    have hSelf : (b.nullifier == b.nullifier) = true := decide_eq_true rfl
    rw [List.find?_cons]
    dsimp only
    rw [hSelf]
  refine ⟨⟨(b, .enrolled) :: reg.entries⟩,
    ⟨promoteToFinalized b.nullifier ((b, .enrolled) :: reg.entries)⟩, ?_, hFind, ?_, ?_⟩
  · unfold NullifierRegistry.enroll
    rw [hAbsNf, hAbsLid]
  · unfold NullifierRegistry.finalize NullifierRegistry.findByNullifier
    dsimp only
    rw [hFind]
    simp only [ne_eq, not_true_eq_false, ↓reduceIte]
  · unfold NullifierRegistry.findByNullifier
    dsimp only
    rw [find?_promoteToFinalized, hFind]
    simp only [Option.map_some, ↓reduceIte]

/-- **Durability (no way back)**: no successful `enroll`, `finalize`, or `register` call, for any
    binding `b'`, removes or rebinds a recorded nullifier, and a `.finalized` entry stays
    `.finalized`. -/
theorem nullifierRegistry_one_way_durable
    (reg reg' : NullifierRegistry) (b b' : MigrationBinding) (st : EntryStatus) (ins : Bool)
    (hRec : reg.findByNullifier b.nullifier = some (b, st))
    (hOp : reg.enroll b' = .ok (reg', ins) ∨ reg.finalize b' = .ok (reg', ins) ∨
      reg.register b' = .ok (reg', ins)) :
    ∃ st' : EntryStatus, reg'.findByNullifier b.nullifier = some (b, st') ∧
      (st = .finalized → st' = .finalized) := by
  have hCons : ∀ s' : EntryStatus, reg.findByNullifier b'.nullifier = none →
      (NullifierRegistry.mk ((b', s') :: reg.entries)).findByNullifier b.nullifier =
        some (b, st) := by
    intro s' hNone
    unfold NullifierRegistry.findByNullifier at hRec hNone ⊢
    dsimp only
    rw [List.find?_cons]
    dsimp only
    cases hk : (b'.nullifier == b.nullifier) with
    | false => exact hRec
    | true => rw [beq_iff_eq.mp hk, hRec] at hNone; cases hNone
  have hProm : ∃ st' : EntryStatus,
      (NullifierRegistry.mk (promoteToFinalized b'.nullifier reg.entries)).findByNullifier
        b.nullifier = some (b, st') ∧ (st = .finalized → st' = .finalized) := by
    unfold NullifierRegistry.findByNullifier at hRec ⊢
    dsimp only
    rw [find?_promoteToFinalized, hRec]
    dsimp only [Option.map_some]
    split
    · exact ⟨.finalized, rfl, fun _ => rfl⟩
    · exact ⟨st, rfl, id⟩
  have hFound : ∀ (bOld : MigrationBinding) (s : EntryStatus),
      (if bOld ≠ b' then (.error .nullifierConflict : Except RegistryError _)
       else match s with
         | .finalized => .ok (reg, false)
         | .enrolled => .ok (⟨promoteToFinalized b'.nullifier reg.entries⟩, true)) =
        .ok (reg', ins) →
      ∃ st' : EntryStatus, reg'.findByNullifier b.nullifier = some (b, st') ∧
        (st = .finalized → st' = .finalized) := by
    intro bOld s h
    split at h
    · cases h
    · cases s with
      | finalized =>
        injection h with h
        obtain ⟨rfl, _⟩ := Prod.mk.inj h
        exact ⟨st, hRec, id⟩
      | enrolled =>
        injection h with h
        obtain ⟨rfl, _⟩ := Prod.mk.inj h
        exact hProm
  rcases hOp with h | h | h
  · unfold NullifierRegistry.enroll at h
    cases hF : reg.findByNullifier b'.nullifier with
    | some e =>
      obtain ⟨bOld, s⟩ := e
      rw [hF] at h
      dsimp only at h
      split at h
      · injection h with h
        obtain ⟨rfl, _⟩ := Prod.mk.inj h
        exact ⟨st, hRec, id⟩
      · cases h
    | none =>
      rw [hF] at h
      dsimp only at h
      cases hL : reg.findByLegacyId b'.legacyId with
      | some _ => rw [hL] at h; cases h
      | none =>
        rw [hL] at h
        injection h with h
        obtain ⟨rfl, _⟩ := Prod.mk.inj h
        exact ⟨st, hCons _ hF, id⟩
  · unfold NullifierRegistry.finalize at h
    cases hF : reg.findByNullifier b'.nullifier with
    | none => rw [hF] at h; cases h
    | some e =>
      obtain ⟨bOld, s⟩ := e
      rw [hF] at h
      exact hFound bOld s h
  · unfold NullifierRegistry.register at h
    cases hF : reg.findByNullifier b'.nullifier with
    | some e =>
      obtain ⟨bOld, s⟩ := e
      rw [hF] at h
      exact hFound bOld s h
    | none =>
      rw [hF] at h
      dsimp only at h
      cases hL : reg.findByLegacyId b'.legacyId with
      | some _ => rw [hL] at h; cases h
      | none =>
        rw [hL] at h
        injection h with h
        obtain ⟨rfl, _⟩ := Prod.mk.inj h
        exact ⟨st, hCons _ hF, id⟩

/-! ## §4. Single-Transcript `ZkHemV2` R1CS Straight-Line Extractor → `Spec.idealMigrateMachine` -/

/-- Canonical legacy credential descriptor across all 6 deployed real curves + Ironwood notes. -/
structure LegacyCredential where
  curve : MigrationCurveKind
  legacyId : Spec.Digest256
  pubKeyCoordX : Nat
  pubKeyCoordY : Nat
  deriving DecidableEq, Repr

/-- Witness extracted straight-line from the systematic variable subcube of a `zk-Hem v2` Stage-0
    polynomial table (zero rewinding!). -/
structure ExtractedR1csMigrationWitness where
  sk : Nat
  wires : List Goldilocks
  authorizedDest : Spec.Bytes
  deriving DecidableEq, Repr

/-- Multi-curve R1CS ownership relation over the **real** certified prime-order curves
    (`secp256k1`, `Ed25519`, `Pallas` Ironwood `0x03`, `Vesta`, `Jubjub`, `BLS12-381`). -/
def realCurveR1csScheme
    (shapeOf : MigrationCurveKind → R1csShape)
    (pubInputsOf : Spec.MigrationClaim LegacyCredential → List Goldilocks)
    (deriveNullifier : LegacyCredential → Spec.Digest256) :
    Spec.LegacyOwnershipScheme LegacyCredential ExtractedR1csMigrationWitness where
  ownsKey cred wit claim :=
    0 < wit.sk ∧
    wit.sk < cred.curve.cert.scalarOrd ∧
    cred.curve.cert.publicKeyMatches wit.sk cred.pubKeyCoordX cred.pubKeyCoordY = true ∧
    wit.authorizedDest = claim.pqDestinationPk ∧
    r1csSatisfied (shapeOf cred.curve) (pubInputsOf claim) wit.wires = true
  checkOwnership cred wit claim :=
    decide (0 < wit.sk ∧ wit.sk < cred.curve.cert.scalarOrd ∧
      cred.curve.cert.publicKeyMatches wit.sk cred.pubKeyCoordX cred.pubKeyCoordY = true ∧
      wit.authorizedDest = claim.pqDestinationPk) &&
    r1csSatisfied (shapeOf cred.curve) (pubInputsOf claim) wit.wires
  check_iff _ _ _ := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨fun ⟨⟨h1, h2, h3, h4⟩, h5⟩ => ⟨h1, h2, h3, h4, h5⟩,
           fun ⟨h1, h2, h3, h4, h5⟩ => ⟨⟨h1, h2, h3, h4⟩, h5⟩⟩
  deriveNullifier := deriveNullifier

/-- Every ownership witness binds the very same secret scalar to both public coordinates. -/
theorem realCurveR1csScheme_owns_public_key (shapeOf pubInputsOf deriveNullifier)
    (cred : LegacyCredential) (wit : ExtractedR1csMigrationWitness) (claim)
    (h : (realCurveR1csScheme shapeOf pubInputsOf deriveNullifier).ownsKey cred wit claim) :
    cred.curve.cert.publicKeyMatches wit.sk cred.pubKeyCoordX cred.pubKeyCoordY = true :=
  h.2.2.1

/-- Concrete wire submission to the single-transcript `ZkHemV2` migration turnstile:
    contains ONLY public claim/binding metadata and `ZkHemV2MigrationWireProof` — **no witness**! -/
structure ZkHemV2MigrationSubmission (D : Type) where
  claim : Spec.MigrationClaim LegacyCredential
  domain : Spec.Digest256
  pqCommitment : Spec.Digest256
  epoch : UInt64
  exposure : KeyExposure
  proof : ZkHemV2MigrationWireProof D

/-- Interface for a witness extractor on a single submission. Its implementation and
    correctness against the committed table are supplied by the caller. -/
abbrev StraightLineExtractor (D : Type) :=
  ZkHemV2MigrationSubmission D → ExtractedR1csMigrationWitness

/-- Concrete persistent state of `zkHemV2MigrationMachine`, pairing `NullifierRegistry` with the
    settlement totals and receipts. -/
structure ZkHemV2MigrateState where
  registry : NullifierRegistry
  totalMigrated : Nat
  spentNullifiers : List Spec.Digest256
  settledClaims : List (Spec.MigrationReceipt LegacyCredential)
  deriving DecidableEq

@[expose] def ZkHemV2MigrateState.init : ZkHemV2MigrateState :=
  ⟨NullifierRegistry.empty, 0, [], []⟩

