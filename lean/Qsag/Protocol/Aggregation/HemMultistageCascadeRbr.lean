module
/-
# Hem affine-WHIR round-by-round soundness with non-empty fold cascades

`HemRbrSoundness` packages a two-round IOP (cascade, final opening) whose verifier rejects
every instance with a fold stage. This module runs the fold stages. For a static stage list
`stages` the IOP has `3 * stages.length + 2` rounds:

* round 0, the cascade: one batch oracle, challenge `(α, β) ∈ S × S` (unchanged from
  `HemRbrSoundness`);
* per stage, three rounds in the order of `affine.rs::prove_fold_in_place`:
  1. `cross`: the prover sends the cross wires `(w₀, w₁, w₂)`, the verifier answers `φ ∈ S` and
     folds the kernel (`hemKernelFold`);
  2. `shift`: the prover sends the shift wires `(c_F, c_G)`, the verifier answers
     `(θ, α, β) ∈ S³` and derives the next claim (`hemBridgeFoldClaim`);
  3. `commit`: the prover sends the table of the next stage oracle and the verifier checks it
     against `hemVirtualFoldOracle θ α β curDom st.domainPts curOracle` on the whole stage domain;
* the final round: the prover sends the final coefficients and the verifier checks them against
  the last oracle, kernel and claim.

The state after a `commit` round is `(stage table, hemKernelFold φ k, hemBridgeFoldClaim …)`; it
is live when some polynomial of the stage degree bound agrees with the stage table on at least
the stage agreement threshold and has `ringDot P kernel = claim`.

## What is idealized relative to `crates/qsag-agg/src/pcs.rs`

* **The cross-stage check is exhaustive.** The Rust verifier ties a stage commitment to the
  previous one with two out-of-domain evaluations and `num_queries` sampled coset openings whose
  folded values are batched into the running claim and kernel (`WHIR_SHIFT_GAMMA`,
  `KernelClaim::evaluation`). Here the verifier reads the whole stage table and compares it with
  the virtual fold, so no query, out-of-domain or Merkle term appears and the kernel and claim
  are not extended by evaluation claims. `tooth_dropped_stage_fold_check_accepts_false_claim`
  (`Qsag.Tests.HemMultistageCascadeTeeth`) shows that without this check a false claim is
  accepted for every challenge.
* **One binary fold per stage.** A Rust stage runs `step_vars` binary folds before it commits;
  `HemWhirStageSpec` and `verifyHemStages` model one.
* **Antipodal points are adjacent.** `curDom` lists `(x, -x)` at indices `(2 i, 2 i + 1)`, as
  `hemVirtualFoldOracle` reads them; the Rust coset order puts `-x` half a domain away.
* **One batch oracle**, as in `HemRbrSoundness`, and the final check counts agreements on
  the whole last domain.
* **Kernel parity is checked in every `cross` round.** `fold_kernel_into` pairs the kernel
  entries and drops an unpaired tail; the Rust kernel has length `2^n + 2`, so no tail exists.
* The fold proof-of-work nonces are not modelled, and challenges are uniform in a pool `S`
  rather than derived from a transcript hash.

## What is assumed

`HemMultistageRbrCert` carries, for the cascade, `HemCascadeRbrCert`, and for each stage `st` an
`AffineFoldDecompBound st.domainPts S st.degBound st.minAgree` together with two list-size
bounds (`HemStageFoldCert`). `hemWelchBerlekampStageCert` proves a stage certificate in the
unique-decoding regime with no further hypothesis, and
`inhabited_hemMultistage_state_restoration` instantiates everything on a 64/32/16-point chain.
At the Johnson radius the stage certificate needs the same `NonExcludedDecompBound` hypothesis as
`hemCwyz26JohnsonCert`.

The acceptance bridge to `verifyHemAffineWhir` goes from the checker to this IOP: a checker
transcript that also passes the fold checks is accepted here. The converse is false, because the
checker asks for a decoded polynomial at every stage and this verifier does not.
-/

public import Qsag.Protocol.Aggregation.Cwyz26EqualDegreeAndMultiFold
public import Qsag.Protocol.Aggregation.HemRbrSoundness
public import Qsag.Math.Tactic.CommRing
public import Qsag.Tactic.AssuranceKit
import Qsag.Protocol.Aggregation.HemOpening
import Qsag.Protocol.Aggregation.MultiRoundFsQrom
import Qsag.Protocol.Aggregation.ConcreteSecurityBudget
import Qsag.Coding.Cwyz26

public section
namespace Qsag

set_option autoImplicit false
set_option exponentiation.threshold 2048

/-! ## §1. Counting lemmas for the `cross` and `shift` rounds of one binary fold -/

private theorem affine_two_points_eq {F : Type} [LawfulField F] [DecidableEq F]
    {φ₁ φ₂ a b u v : F} (hNe : φ₁ ≠ φ₂)
    (h₁ : CommRingOps.add a (CommRingOps.mul φ₁ b) = CommRingOps.add u (CommRingOps.mul φ₁ v))
    (h₂ : CommRingOps.add a (CommRingOps.mul φ₂ b) = CommRingOps.add u (CommRingOps.mul φ₂ v)) :
    a = u ∧ b = v := by
  have hId : CommRingOps.mul (CommRingOps.sub φ₁ φ₂) (CommRingOps.sub b v) =
      CommRingOps.sub
        (CommRingOps.sub (CommRingOps.add a (CommRingOps.mul φ₁ b))
          (CommRingOps.add u (CommRingOps.mul φ₁ v)))
        (CommRingOps.sub (CommRingOps.add a (CommRingOps.mul φ₂ b))
          (CommRingOps.add u (CommRingOps.mul φ₂ v))) := by
    constructive_ring
  have h0 : CommRingOps.mul (CommRingOps.sub φ₁ φ₂) (CommRingOps.sub b v) = CommRingOps.zero := by
    rw [hId, h₁, h₂, LawfulCommRing.sub_self, LawfulCommRing.sub_self, LawfulCommRing.sub_self]
  have hbv : b = v := by
    rcases LawfulField.mul_eq_zero h0 with h | h
    · exact absurd (LawfulCommRing.sub_eq_zero_iff.mp h) hNe
    · exact LawfulCommRing.sub_eq_zero_iff.mp h
  refine ⟨?_, hbv⟩
  have e1 : a = CommRingOps.sub (CommRingOps.add a (CommRingOps.mul φ₁ b))
      (CommRingOps.mul φ₁ b) := by constructive_ring
  have e2 : CommRingOps.sub (CommRingOps.add u (CommRingOps.mul φ₁ v))
      (CommRingOps.mul φ₁ v) = u := by constructive_ring
  rw [hbv] at h₁ e1
  exact e1.trans ((congrArg (fun t => CommRingOps.sub t (CommRingOps.mul φ₁ v)) h₁).trans e2)

private theorem flatMap_pair_length {α β : Type} (ys : List β) :
    ∀ (xs : List α), (xs.flatMap (fun a => ys.map (fun b => (a, b)))).length =
      xs.length * ys.length
  | [] => (Nat.zero_mul ys.length).symm
  | _ :: rest => by
    rw [List.flatMap_cons, List.length_append, List.length_map, List.length_cons,
      flatMap_pair_length ys rest, Nat.succ_mul, Nat.add_comm]

private theorem ofCoeffs_mem_gsDecodeList {F : Type} [LawfulField F] [DecidableEq F]
    {d A : Nat} {D : List F} (word : F → F) (hD : D.Nodup) (hdA : d + 1 ≤ A)
    (P : List F) (hLen : P.length ≤ d + 1)
    (hAg : A ≤ (D.filter (fun z => decide (RoundPoly.evalCoeffs P z = word z))).length) :
    GsUniPoly.ofCoeffs P ∈ gsDecodeList d A D word := by
  refine (mem_gsDecodeList_iff word hD hdA _).mpr
    ⟨Nat.le_trans (trimPoly_length_le P) hLen, ?_⟩
  have hEqF : D.filter (fun z =>
      decide (RoundPoly.evalCoeffs (GsUniPoly.ofCoeffs P).val z = word z)) =
      D.filter (fun z => decide (RoundPoly.evalCoeffs P z = word z)) :=
    congrArg (fun q => List.filter q D) (funext fun z => by
      show decide (RoundPoly.evalCoeffs (trimPoly P) z = word z) = _
      rw [evalCoeffs_trimPoly])
  rw [hEqF]; exact hAg

private theorem polyWitnessValid_of_lookup_filter {F : Type} [CommRingOps F] [DecidableEq F]
    (D : List F) (hD : D.Nodup) (A d : Nat) (O : Nat → F) (k : List F) (c : F) (P : List F)
    (hLen : P.length ≤ d + 1)
    (hAg : A ≤ (D.filter (fun z =>
      decide (RoundPoly.evalCoeffs P z = lookupDomOracle D O z))).length)
    (hDot : ringDot P k = c) :
    polyWitnessValid D A d O k c P = true := by
  rw [polyWitnessValid_def]
  rw [hemCosetAgreeCount_eq_filter_lookup D O P hD, decide_eq_true hLen, decide_eq_true hAg,
    decide_eq_true hDot]
  rfl

private theorem polyWitnessValid_lookup_filter {F : Type} [CommRingOps F] [DecidableEq F]
    (D : List F) (hD : D.Nodup) (A d : Nat) (O : Nat → F) (k : List F) (c : F) (P : List F)
    (h : polyWitnessValid D A d O k c P = true) :
    P.length ≤ d + 1 ∧
    A ≤ (D.filter (fun z =>
      decide (RoundPoly.evalCoeffs P z = lookupDomOracle D O z))).length ∧
    ringDot P k = c := by
  rw [polyWitnessValid_def] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rw [hemCosetAgreeCount_eq_filter_lookup D O P hD] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **`cross` round of one binary fold.** Suppose `(curOracle, kernel, curClaim)` has no
    witness of degree `≤ curDeg` at agreement `curAgree` on `D_in`. Fix the cross wires
    `(w₀, w₁, w₂)`. Then the number of `φ ∈ S` after which BOTH halves have a witness of degree
    `≤ d` at agreement `A` on `D_out` against the folded kernel, for the claims
    `w₀ + φ w₁` (even half) and `w₂ + φ (curClaim - w₀)` (odd half), is at most the product of
    the two decoding-list sizes. The two agreements are separate, so the lift back to `D_in`
    intersects them: `curAgree + 2 |D_out| ≤ 4 A`. -/
theorem hemCrossRound_bad_phi_bound {F : Type} [LawfulField F] [DecidableEq F]
    (D_in D_out S kernel : List F) (d A m_K curDeg curAgree : Nat)
    (curOracle : Nat → F) (curClaim w₀ w₁ w₂ : F)
    (hPair : IsAntipodalDomainPair D_in D_out)
    (hS : S.Nodup) (hdA : d + 1 ≤ A)
    (hKernLen : kernel.length = 2 * m_K)
    (hDeg : 2 * (d + 1) ≤ curDeg + 1)
    (hAgree : curAgree + 2 * D_out.length ≤ 4 * A)
    (hInvalidIn : ∀ Q : List F,
      polyWitnessValid D_in curAgree curDeg curOracle kernel curClaim Q = false)
    (L : List (Fin S.length)) (hNd : L.Nodup)
    (hFlip : ∀ i ∈ L, ¬¬ ∃ Fp Gp : List F,
      polyWitnessValid D_out A d (cosetEvenOracle curOracle)
        (hemKernelFold (S.get i) kernel)
        (CommRingOps.add w₀ (CommRingOps.mul (S.get i) w₁)) Fp = true ∧
      polyWitnessValid D_out A d (cosetOddOracle D_in curOracle)
        (hemKernelFold (S.get i) kernel)
        (CommRingOps.add w₂ (CommRingOps.mul (S.get i) (CommRingOps.sub curClaim w₀)))
        Gp = true) :
    L.length ≤
      (gsDecodeList d A D_out (lookupDomOracle D_out (cosetEvenOracle curOracle))).length *
      (gsDecodeList d A D_out (lookupDomOracle D_out (cosetOddOracle D_in curOracle))).length := by
  let fE := lookupDomOracle D_out (cosetEvenOracle curOracle)
  let fO := lookupDomOracle D_out (cosetOddOracle D_in curOracle)
  let kE := (splitEvenOdd kernel).1
  let kO := (splitEvenOdd kernel).2
  have hkSpec0 := splitEvenOdd_spec m_K kernel CommRingOps.zero hKernLen
  have hkLenEq : kE.length = kO.length := hkSpec0.1.trans hkSpec0.2.1.symm
  have hkInt : hemInterleave kE kO = kernel := hkSpec0.2.2.1
  have hFoldDot : ∀ (φ : F) (P : List F),
      ringDot P (hemKernelFold φ kernel) =
        CommRingOps.add (ringDot P kE) (CommRingOps.mul φ (ringDot P kO)) := by
    intro φ P
    rw [(splitEvenOdd_spec m_K kernel φ hKernLen).2.2.2.1, ringDot_append_zero]
    exact ringDot_zipFold φ P kE kO hkLenEq
  let candF := gsDecodeList d A D_out fE
  let candG := gsDecodeList d A D_out fO
  let pairs := candF.flatMap (fun pF => candG.map (fun pG => (pF, pG)))
  have hPairsLen : pairs.length = candF.length * candG.length := flatMap_pair_length candG candF
  let matchPair : GsUniPoly F × GsUniPoly F → Fin S.length → Bool := fun fg i =>
    decide (CommRingOps.add (ringDot fg.1.val kE)
        (CommRingOps.mul (S.get i) (ringDot fg.1.val kO)) =
      CommRingOps.add w₀ (CommRingOps.mul (S.get i) w₁)) &&
    decide (CommRingOps.add (ringDot fg.2.val kE)
        (CommRingOps.mul (S.get i) (ringDot fg.2.val kO)) =
      CommRingOps.add w₂ (CommRingOps.mul (S.get i) (CommRingOps.sub curClaim w₀)))
  let anyMatch : Fin S.length → Bool := fun i => pairs.any (fun fg => matchPair fg i)
  have hAll : ∀ i ∈ L, anyMatch i = true := by
    intro i hi
    cases hAny : anyMatch i
    · exfalso
      refine hFlip i hi ?_
      rintro ⟨Fp, Gp, hFp, hGp⟩
      obtain ⟨hFLen, hFAg, hFDot⟩ :=
        polyWitnessValid_lookup_filter D_out hPair.nodup_out _ _ _ _ _ Fp hFp
      obtain ⟨hGLen, hGAg, hGDot⟩ :=
        polyWitnessValid_lookup_filter D_out hPair.nodup_out _ _ _ _ _ Gp hGp
      have hpFMem : GsUniPoly.ofCoeffs Fp ∈ candF :=
        ofCoeffs_mem_gsDecodeList fE hPair.nodup_out hdA Fp hFLen hFAg
      have hpGMem : GsUniPoly.ofCoeffs Gp ∈ candG :=
        ofCoeffs_mem_gsDecodeList fO hPair.nodup_out hdA Gp hGLen hGAg
      have hMemPairs : (GsUniPoly.ofCoeffs Fp, GsUniPoly.ofCoeffs Gp) ∈ pairs :=
        List.mem_flatMap.mpr ⟨_, hpFMem, List.mem_map.mpr ⟨_, hpGMem, rfl⟩⟩
      have hM1 : CommRingOps.add (ringDot (trimPoly Fp) kE)
          (CommRingOps.mul (S.get i) (ringDot (trimPoly Fp) kO)) =
          CommRingOps.add w₀ (CommRingOps.mul (S.get i) w₁) := by
        rw [ringDot_trimPoly_eq, ringDot_trimPoly_eq]
        exact (hFoldDot (S.get i) Fp).symm.trans hFDot
      have hM2 : CommRingOps.add (ringDot (trimPoly Gp) kE)
          (CommRingOps.mul (S.get i) (ringDot (trimPoly Gp) kO)) =
          CommRingOps.add w₂ (CommRingOps.mul (S.get i) (CommRingOps.sub curClaim w₀)) := by
        rw [ringDot_trimPoly_eq, ringDot_trimPoly_eq]
        exact (hFoldDot (S.get i) Gp).symm.trans hGDot
      have hM : matchPair (GsUniPoly.ofCoeffs Fp, GsUniPoly.ofCoeffs Gp) i = true :=
        (Bool.and_eq_true _ _).mpr ⟨decide_eq_true hM1, decide_eq_true hM2⟩
      have hT : anyMatch i = true := List.any_eq_true.mpr ⟨_, hMemPairs, hM⟩
      rw [hT] at hAny
      exact Bool.noConfusion hAny
    · rfl
  have hLEq : L.filter anyMatch = L := List.filter_eq_self.mpr hAll
  have hPer : ∀ fg ∈ pairs, (L.filter (matchPair fg)).length ≤ 1 := by
    intro fg hfg
    rcases List.mem_flatMap.mp hfg with ⟨pF, hpFMem, hInG⟩
    rcases List.mem_map.mp hInG with ⟨pG, hpGMem, rfl⟩
    generalize hFilt : L.filter (matchPair (pF, pG)) = fl
    have hFlNd : fl.Nodup := hFilt ▸ List.Pairwise.filter _ hNd
    rcases fl with _ | ⟨i₁, _ | ⟨i₂, _⟩⟩
    · exact Nat.zero_le 1
    · exact Nat.le_refl 1
    · exfalso
      have hMem₁ : i₁ ∈ L.filter (matchPair (pF, pG)) := by rw [hFilt]; exact .head _
      have hMem₂ : i₂ ∈ L.filter (matchPair (pF, pG)) := by
        rw [hFilt]; exact .tail _ (.head _)
      have hNeIdx : i₁ ≠ i₂ := fun h => (List.pairwise_cons.mp hFlNd).1 i₂ (.head _) h
      have hNeφ : S.get i₁ ≠ S.get i₂ := fun h => hNeIdx (nodup_get_inj hS h)
      have hB₁ := (Bool.and_eq_true _ _).mp (List.mem_filter.mp hMem₁).2
      have hB₂ := (Bool.and_eq_true _ _).mp (List.mem_filter.mp hMem₂).2
      have hFPair := affine_two_points_eq hNeφ (of_decide_eq_true hB₁.1) (of_decide_eq_true hB₂.1)
      have hGPair := affine_two_points_eq hNeφ (of_decide_eq_true hB₁.2) (of_decide_eq_true hB₂.2)
      have hFE : ringDot pF.val kE = w₀ := hFPair.1
      have hGO : ringDot pG.val kO = CommRingOps.sub curClaim w₀ := hGPair.2
      have hpF := (mem_gsDecodeList_iff fE hPair.nodup_out hdA pF).mp hpFMem
      have hpG := (mem_gsDecodeList_iff fO hPair.nodup_out hdA pG).mp hpGMem
      let Q := interleavePoly pF.val pG.val
      have hQLen : Q.length ≤ curDeg + 1 :=
        Nat.le_trans (interleavePoly_length_le (d + 1) pF.val pG.val hpF.1 hpG.1) hDeg
      let pA : F → Bool := fun y => decide (RoundPoly.evalCoeffs pF.val y = fE y)
      let pB : F → Bool := fun y => decide (RoundPoly.evalCoeffs pG.val y = fO y)
      let pJ : F → Bool := fun y => pA y && pB y
      have hOv : (D_out.filter pA).length + (D_out.filter pB).length ≤
          D_out.length + (D_out.filter pJ).length := filter_overlap_len pA pB D_out
      have h1 : A ≤ (D_out.filter pA).length := hpF.2
      have h2 : A ≤ (D_out.filter pB).length := hpG.2
      have hLift : 2 * (D_out.filter pJ).length ≤ hemCosetAgreeCount D_in curOracle Q :=
        antipodal_joint_agree_lifts hPair curOracle pF.val pG.val
      have hQAg : curAgree ≤ hemCosetAgreeCount D_in curOracle Q := by
        generalize (D_out.filter pA).length = nA at hOv h1
        generalize (D_out.filter pB).length = nB at hOv h2
        generalize (D_out.filter pJ).length = nJ at hOv hLift
        generalize hemCosetAgreeCount D_in curOracle Q = nQ at hLift ⊢
        generalize D_out.length = n at hOv hAgree
        omega
      have hQDot : ringDot Q kernel = curClaim := by
        rw [← hkInt, ringDot_interleavePoly_hemInterleave kE kO pF.val pG.val hkLenEq, hFE, hGO]
        constructive_ring
      have hVal : polyWitnessValid D_in curAgree curDeg curOracle kernel curClaim Q = true := by
        rw [polyWitnessValid_def]
        rw [decide_eq_true hQLen, decide_eq_true hQAg, decide_eq_true hQDot]
        rfl
      rw [hInvalidIn Q] at hVal
      exact Bool.noConfusion hVal
  have hBound : (L.filter anyMatch).length ≤ pairs.length * 1 :=
    filter_any_length_le pairs matchPair L 1 hPer
  rw [hLEq, hPairsLen, Nat.mul_one] at hBound
  exact hBound

/-- **`shift` round of one binary fold.** Suppose the two halves do NOT both have a witness of
    degree `≤ d` at agreement `A` on `D_out` against `kernel` for the claims `(e_f, e_g)`. Fix the
    shift wires `(c_F, c_G)`. Then the number of `(θ, α, β) ∈ S³` after which the virtual fold
    `hemVirtualFoldOracle θ α β D_in D_out curOracle` has a witness of degree `≤ d + 1` at
    agreement `A + 1` for the claim `hemFoldClaimUpdate e_f e_g c_F c_G θ α β` is bounded by
    `equal_degree_three_challenge_fold_bound`. -/
theorem hemShiftRound_bad_triples_bound {F : Type} [LawfulField F] [DecidableEq F]
    (D_in D_out S kernel : List F) (d A badMca : Nat)
    (curOracle : Nat → F) (e_f e_g c_F c_G : F)
    (hOut : D_out.Nodup) (hS : S.Nodup) (hdA : d + 2 ≤ A)
    (hDecomp : AffineFoldDecompBound D_out S (d + 1) (A + 1) badMca)
    (hInvalidMid : ¬ ∃ Fp Gp : List F,
      polyWitnessValid D_out A d (cosetEvenOracle curOracle) kernel e_f Fp = true ∧
      polyWitnessValid D_out A d (cosetOddOracle D_in curOracle) kernel e_g Gp = true)
    (L : List (Fin (threePool S S).length)) (hNd : L.Nodup)
    (hFlip : ∀ ch ∈ L, ¬¬ ∃ P : List F,
      polyWitnessValid D_out (A + 1) (d + 1)
        (hemVirtualFoldOracle ((threePool S S).get ch).1 ((threePool S S).get ch).2.1
          ((threePool S S).get ch).2.2 D_in D_out curOracle)
        kernel
        (hemFoldClaimUpdate e_f e_g c_F c_G ((threePool S S).get ch).1
          ((threePool S S).get ch).2.1 ((threePool S S).get ch).2.2) P = true) :
    L.length ≤ S.length * badMca +
      (gsDecodeList d A D_out (lookupDomOracle D_out (cosetEvenOracle curOracle))).length *
        (gsDecodeList d A D_out (lookupDomOracle D_out (cosetOddOracle D_in curOracle))).length *
        (S.length * S.length) +
      (gsDecodeList (d + 1) A D_out (lookupDomOracle D_out (cosetEvenOracle curOracle))).length *
        (gsDecodeList (d + 1) A D_out
          (lookupDomOracle D_out (cosetOddOracle D_in curOracle))).length *
        (S.length * S.length) := by
  let fE := lookupDomOracle D_out (cosetEvenOracle curOracle)
  let fO := lookupDomOracle D_out (cosetOddOracle D_in curOracle)
  have hdA1 : d + 1 ≤ A := Nat.le_of_succ_le hdA
  have hInvalidFG :
      (∀ Fw : List F, Fw.length ≤ d + 1 →
        A ≤ (D_out.filter (fun z => decide (RoundPoly.evalCoeffs Fw z = fE z))).length →
        ringDot Fw kernel ≠ e_f) ∨
      (∀ Gw : List F, Gw.length ≤ d + 1 →
        A ≤ (D_out.filter (fun z => decide (RoundPoly.evalCoeffs Gw z = fO z))).length →
        ringDot Gw kernel ≠ e_g) := by
    cases hHas : (gsDecodeList d A D_out fE).any (fun p => decide (ringDot p.val kernel = e_f))
    · left
      intro Fw hLen hAg hDot
      have hMem := ofCoeffs_mem_gsDecodeList fE hOut hdA1 Fw hLen hAg
      have hDotT : ringDot (trimPoly Fw) kernel = e_f := by
        rw [ringDot_trimPoly_eq]; exact hDot
      have hT : (gsDecodeList d A D_out fE).any
          (fun p => decide (ringDot p.val kernel = e_f)) = true :=
        List.any_eq_true.mpr ⟨_, hMem, decide_eq_true hDotT⟩
      rw [hT] at hHas
      exact Bool.noConfusion hHas
    · right
      rcases List.any_eq_true.mp hHas with ⟨pF, hpFMem, hpFDot⟩
      have hpF := (mem_gsDecodeList_iff fE hOut hdA1 pF).mp hpFMem
      intro Gw hLen hAg hDot
      exact hInvalidMid ⟨pF.val, Gw,
        polyWitnessValid_of_lookup_filter D_out hOut A d _ kernel e_f pF.val hpF.1 hpF.2
          (of_decide_eq_true hpFDot),
        polyWitnessValid_of_lookup_filter D_out hOut A d _ kernel e_g Gw hLen hAg hDot⟩
  refine equal_degree_three_challenge_fold_bound D_out S S kernel d A badMca fE fO
    e_f e_g c_F c_G hOut hS hS hdA hDecomp hInvalidFG L hNd ?_
  intro ch hch hNo
  refine hFlip ch hch (fun ⟨P, hP⟩ => hNo ?_)
  obtain ⟨hLen, hAg, hDot⟩ := polyWitnessValid_lookup_filter D_out hOut _ _ _ _ _ P hP
  have hEq : D_out.filter (fun y =>
      decide (RoundPoly.evalCoeffs P y =
        lookupDomOracle D_out (hemVirtualFoldOracle ((threePool S S).get ch).1
          ((threePool S S).get ch).2.1 ((threePool S S).get ch).2.2 D_in D_out curOracle) y)) =
      D_out.filter (fun y =>
        decide (RoundPoly.evalCoeffs P y =
          CommRingOps.add (fO y)
            (CommRingOps.mul
              (CommRingOps.add ((threePool S S).get ch).2.1
                (CommRingOps.mul ((threePool S S).get ch).2.2 y))
              (CommRingOps.add (fE y) (CommRingOps.mul ((threePool S S).get ch).1 (fO y)))))) :=
    hemVirtualFoldOracle_filter_eq D_in D_out hOut curOracle _ _ _ P
  rw [hEq] at hAg
  exact ⟨P, hLen, hAg, hDot⟩

/-! ## §2. Messages, states and round steps of the multi-stage IOP -/

instance hemWhirStageSpecDecEq : DecidableEq (HemWhirStageSpec QuarticGoldilocks)
  | ⟨d₁, g₁, a₁, l₁, q₁⟩, ⟨d₂, g₂, a₂, l₂, q₂⟩ =>
    if h : d₁ = d₂ ∧ g₁ = g₂ ∧ a₁ = a₂ ∧ l₁ = l₂ ∧ q₁ = q₂ then
      isTrue (by
        rcases h with ⟨h1, h2, h3, h4, h5⟩
        rw [h1, h2, h3, h4, h5])
    else
      isFalse (fun e => h (by
        cases e
        exact ⟨rfl, rfl, rfl, rfl, rfl⟩))

/-- Prover messages of the multi-stage IOP. -/
inductive HemFoldIopMsg where
  | cascade (absorbedShifts : List QuarticGoldilocks)
  | cross (w₀ w₁ w₂ : QuarticGoldilocks)
  | shift (c_F c_G : QuarticGoldilocks)
  | commit (stageTable : List QuarticGoldilocks)
  | final (finalCoeffs : List QuarticGoldilocks)
  deriving DecidableEq, Repr

/-- Verifier state between rounds. `cur` holds the oracle, kernel and claim of the stage
    reached so far together with that stage's domain, degree bound and agreement threshold;
    `mid` is the state between the `cross` and `shift` rounds of one fold. -/
inductive HemFoldIopState where
  | init
  | cur (dom : List QuarticGoldilocks) (deg agree : Nat) (oracle : Nat → QuarticGoldilocks)
      (kernel : List QuarticGoldilocks) (claim : QuarticGoldilocks)
  | mid (dIn dOut : List QuarticGoldilocks) (d A : Nat) (oracle : Nat → QuarticGoldilocks)
      (kernel : List QuarticGoldilocks) (e_f e_g : QuarticGoldilocks)
  | accepted
  | invalid

/-- Liveness of a verifier state.
    * `init`: the instance is well formed for the static stage list and its statement holds;
    * `cur`: some polynomial of degree `≤ deg` agrees with the oracle on `≥ agree` points of
      `dom` and meets the claim against the kernel;
    * `mid`: both halves of the oracle have such a witness on the fold domain, for the two
      half-claims fixed by the cross wires and `φ`. -/
def hemFoldIopLive (domPts : List QuarticGoldilocks) (d₀ A₀ : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks))
    (inst : HemWhirInstance QuarticGoldilocks) : HemFoldIopState → Prop
  | .init =>
    WellFormedHemCascadeInstance 1 domPts d₀ A₀ inst ∧ inst.stages = stages ∧
      HemStatementValid inst
  | .cur dom deg agree oracle kernel claim =>
    ∃ P : List QuarticGoldilocks, polyWitnessValid dom agree deg oracle kernel claim P = true
  | .mid dIn dOut d A oracle kernel e_f e_g =>
    ∃ Fp Gp : List QuarticGoldilocks,
      polyWitnessValid dOut A d (cosetEvenOracle oracle) kernel e_f Fp = true ∧
      polyWitnessValid dOut A d (cosetOddOracle dIn oracle) kernel e_g Gp = true
  | .accepted => True
  | .invalid => False

/-- A verifier check: keep the state when the check passes, reject otherwise. -/
def hemFoldGuard (b : Bool) (s : HemFoldIopState) : HemFoldIopState :=
  match b with
  | true => s
  | false => .invalid

theorem hemFoldGuard_true (s : HemFoldIopState) : hemFoldGuard true s = s := by rfl

theorem hemFoldGuard_false (s : HemFoldIopState) : hemFoldGuard false s = .invalid := by rfl

/-- Round 0: the single-batch cascade. The verifier checks the instance shape against the
    static parameters, including `inst.stages = stages`. -/
def hemFoldCascadeStep (S domPts : List QuarticGoldilocks) (d₀ A₀ : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks))
    (inst : HemWhirInstance QuarticGoldilocks) (s : HemFoldIopState)
    (m : HemFoldIopMsg) (ch : Nat) : HemFoldIopState :=
  match s, m with
  | .init, .cascade [s₀] =>
    hemFoldGuard
      (decide (inst.batchOracles.length = 1 ∧ inst.batchClaims.length = 1 ∧
        inst.initDomainPts = domPts ∧ inst.initDegBound = d₀ ∧
        inst.initMinAgree = A₀ ∧ inst.stages = stages))
      (.cur domPts (d₀ + 1) (A₀ + 1)
        (evalCascadeOracle domPts inst.batchOracles
          [(prodPool S).getD ch (CommRingOps.zero, CommRingOps.zero)])
        inst.initKernel
        (evalCascadeClaim inst.batchClaims [s₀]
          [(prodPool S).getD ch (CommRingOps.zero, CommRingOps.zero)]))
  | _, _ => .invalid

/-- `cross` round of the fold onto `st`: cross wires in, `φ` out. The verifier folds the kernel
    and fixes the two half-claims `w₀ + φ w₁` and `w₂ + φ (claim - w₀)`. -/
def hemFoldCrossStep (S curDom : List QuarticGoldilocks) (curDeg curAgree : Nat)
    (st : HemWhirStageSpec QuarticGoldilocks) (s : HemFoldIopState)
    (m : HemFoldIopMsg) (ch : Nat) : HemFoldIopState :=
  match s, m with
  | .cur dom deg agree oracle kernel claim, .cross w₀ w₁ w₂ =>
    hemFoldGuard
      (decide (dom = curDom ∧ deg = curDeg ∧ agree = curAgree ∧ kernel.length % 2 = 0))
      (.mid curDom st.domainPts (st.degBound - 1) (st.minAgree - 1) oracle
        (hemKernelFold (S.getD ch CommRingOps.zero) kernel)
        (CommRingOps.add w₀ (CommRingOps.mul (S.getD ch CommRingOps.zero) w₁))
        (CommRingOps.add w₂
          (CommRingOps.mul (S.getD ch CommRingOps.zero) (CommRingOps.sub claim w₀))))
  | _, _ => .invalid

/-- `shift` round of the fold onto `st`: shift wires in, `(θ, α, β)` out. The next oracle is the
    virtual fold of the current one and the next claim is `hemFoldClaimUpdate`, which is
    `hemBridgeFoldClaim` on the half-claims (`hemFoldClaimUpdate_eq_bridge`). -/
def hemFoldShiftStep (S curDom : List QuarticGoldilocks)
    (st : HemWhirStageSpec QuarticGoldilocks) (s : HemFoldIopState)
    (m : HemFoldIopMsg) (ch : Nat) : HemFoldIopState :=
  match s, m with
  | .mid dIn dOut d A oracle kernel e_f e_g, .shift c_F c_G =>
    hemFoldGuard
      (decide (dIn = curDom ∧ dOut = st.domainPts ∧ d = st.degBound - 1 ∧
        A = st.minAgree - 1))
      (.cur st.domainPts st.degBound st.minAgree
        (hemVirtualFoldOracle
          ((threePool S S).getD ch (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)).1
          ((threePool S S).getD ch (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)).2.1
          ((threePool S S).getD ch (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)).2.2
          curDom st.domainPts oracle)
        kernel
        (hemFoldClaimUpdate e_f e_g c_F c_G
          ((threePool S S).getD ch (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)).1
          ((threePool S S).getD ch (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)).2.1
          ((threePool S S).getD ch (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)).2.2))
  | _, _ => .invalid

/-- The cross-stage fold-consistency check: the committed table equals `oracle` at every index
    of a domain of size `n`. -/
@[expose] def hemTableMatchesOracle (n : Nat) (table : List QuarticGoldilocks)
    (oracle : Nat → QuarticGoldilocks) : Bool :=
  (List.range n).all (fun i => decide (tableToOracle table i = oracle i))

/-- `commit` round: the prover sends the table of the stage oracle; the verifier checks it
    against the virtual fold held in the state on the whole stage domain. -/
def hemFoldCommitStep (s : HemFoldIopState) (m : HemFoldIopMsg) : HemFoldIopState :=
  match s, m with
  | .cur dom deg agree oracle kernel claim, .commit table =>
    hemFoldGuard (hemTableMatchesOracle dom.length table oracle)
      (.cur dom deg agree (tableToOracle table) kernel claim)
  | _, _ => .invalid

/-- Final round: the verifier checks the final coefficients against the last oracle, kernel
    and claim. -/
def hemFoldFinalStep (s : HemFoldIopState) (m : HemFoldIopMsg) : HemFoldIopState :=
  match s, m with
  | .cur dom deg agree oracle kernel claim, .final coeffs =>
    hemFoldGuard (polyWitnessValid dom agree deg oracle kernel claim coeffs) .accepted
  | _, _ => .invalid

/-- The claim update of the `shift` round is `affine.rs::bridge_finish` on the running claim. -/
theorem hemFoldClaimUpdate_eq_bridge (claim w₀ w₁ w₂ c_F c_G φ θ α β : QuarticGoldilocks) :
    hemFoldClaimUpdate (CommRingOps.add w₀ (CommRingOps.mul φ w₁))
      (CommRingOps.add w₂ (CommRingOps.mul φ (CommRingOps.sub claim w₀))) c_F c_G θ α β =
    hemBridgeFoldClaim claim w₀ w₁ w₂ c_F c_G φ θ α β := by
  rw [hemFoldClaimUpdate_def, hemBridgeFoldClaim_def]

/-! ## §3. Per-round flip bounds -/

private theorem length_le_of_all_dead {n B : Nat} {P : Fin n → Prop} (L : List (Fin n))
    (hL : ∀ ch ∈ L, ¬¬ P ch) (hDead : ∀ ch, ¬ P ch) : L.length ≤ B := by
  cases L with
  | nil => exact Nat.zero_le _
  | cons ch _ => exact False.elim (hL ch (.head _) (hDead ch))

/-- List-size and decomposition budget of one fold stage. -/
structure HemFoldBudget where
  badMca : Nat
  listLo : Nat
  listHi : Nat
  deriving Repr

/-- Analytic certificate of one fold stage `st`: an affine fold decomposition bound at the
    stage degree and agreement, and decoding-list bounds one agreement step below. -/
structure HemStageFoldCert (S : List QuarticGoldilocks)
    (st : HemWhirStageSpec QuarticGoldilocks) (b : HemFoldBudget) : Prop where
  decomp_bound : AffineFoldDecompBound st.domainPts S st.degBound st.minAgree b.badMca
  list_lo_bound : ∀ word : QuarticGoldilocks → QuarticGoldilocks,
    (gsDecodeList (st.degBound - 1) (st.minAgree - 1) st.domainPts word).length ≤ b.listLo
  list_hi_bound : ∀ word : QuarticGoldilocks → QuarticGoldilocks,
    (gsDecodeList st.degBound (st.minAgree - 1) st.domainPts word).length ≤ b.listHi

/-- Certificate of the whole cascade: the Round-0 certificate, the stage geometry chain, and one
    `HemStageFoldCert` per stage with budget `bud st`. -/
structure HemMultistageRbrCert (S domPts : List QuarticGoldilocks) (d₀ A₀ badMca listG : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks))
    (bud : HemWhirStageSpec QuarticGoldilocks → HemFoldBudget) : Prop where
  cascade_cert : HemCascadeRbrCert S domPts d₀ A₀ badMca listG
  chain : HemStageChainWellFormed domPts (d₀ + 1) (A₀ + 1) stages
  stage_certs : ∀ st ∈ stages, HemStageFoldCert S st (bud st)

theorem hemFoldStageGeom_antipodal {curDom : List QuarticGoldilocks} {curDeg curAgree : Nat}
    {st : HemWhirStageSpec QuarticGoldilocks}
    (h : HemFoldStageGeom curDom curDeg curAgree st) :
    IsAntipodalDomainPair curDom st.domainPts where
  nodup_in := h.1
  nodup_out := h.2.1
  len_eq := h.2.2.1
  two_ne_zero := by decide +kernel
  even_nz := fun idx hIdx => (h.2.2.2.1 idx hIdx).1
  odd_neg := fun idx hIdx => (h.2.2.2.1 idx hIdx).2.1
  sq_eq := fun idx hIdx => (h.2.2.2.1 idx hIdx).2.2

private theorem hemFoldCascade_flip_bound
    (S domPts : List QuarticGoldilocks) (d₀ A₀ badMca listG : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks))
    (cert : HemCascadeRbrCert S domPts d₀ A₀ badMca listG)
    (hChain : HemStageChainWellFormed domPts (d₀ + 1) (A₀ + 1) stages)
    (inst : HemWhirInstance QuarticGoldilocks) (s : HemFoldIopState) (m : HemFoldIopMsg)
    (hDoomed : ¬ hemFoldIopLive domPts d₀ A₀ stages inst s)
    (L : List (Fin (prodPool S).length)) (hNd : L.Nodup)
    (hL : ∀ ch ∈ L, ¬¬ hemFoldIopLive domPts d₀ A₀ stages inst
      (hemFoldCascadeStep S domPts d₀ A₀ stages inst s m ch.1)) :
    L.length ≤ badMca + 1 * listG * S.length := by
  cases s with
  | cur _ _ _ _ _ _ => exact length_le_of_all_dead L hL (fun _ h => h)
  | mid _ _ _ _ _ _ _ _ => exact length_le_of_all_dead L hL (fun _ h => h)
  | accepted => exact length_le_of_all_dead L hL (fun _ h => h)
  | invalid => exact length_le_of_all_dead L hL (fun _ h => h)
  | init =>
    cases m with
    | cross _ _ _ => exact length_le_of_all_dead L hL (fun _ h => h)
    | shift _ _ => exact length_le_of_all_dead L hL (fun _ h => h)
    | commit _ => exact length_le_of_all_dead L hL (fun _ h => h)
    | final _ => exact length_le_of_all_dead L hL (fun _ h => h)
    | cascade shifts =>
      rcases shifts with _ | ⟨s₀, _ | ⟨s₁, more⟩⟩
      · exact length_le_of_all_dead L hL (fun _ h => h)
      · by_cases hWfDec : (inst.batchOracles.length = 1 ∧ inst.batchClaims.length = 1 ∧
            inst.initDomainPts = domPts ∧ inst.initDegBound = d₀ ∧
            inst.initMinAgree = A₀ ∧ inst.stages = stages)
        · have hStepEq : ∀ ch : Nat,
              hemFoldCascadeStep S domPts d₀ A₀ stages inst .init (.cascade [s₀]) ch =
                .cur domPts (d₀ + 1) (A₀ + 1)
                  (evalCascadeOracle domPts inst.batchOracles
                    [(prodPool S).getD ch (CommRingOps.zero, CommRingOps.zero)])
                  inst.initKernel
                  (evalCascadeClaim inst.batchClaims [s₀]
                    [(prodPool S).getD ch (CommRingOps.zero, CommRingOps.zero)]) := by
            intro ch
            show hemFoldGuard (decide _) _ = _
            rw [decide_eq_true hWfDec, hemFoldGuard_true]
          let inst' : HemWhirInstance QuarticGoldilocks :=
            { batchOracles := inst.batchOracles
              batchClaims := inst.batchClaims
              initDomainPts := inst.initDomainPts
              initDegBound := inst.initDegBound
              initMinAgree := inst.initMinAgree
              initKernel := inst.initKernel
              stages := [] }
          have hCoreDec : (inst'.batchOracles.length = 1 ∧ inst'.batchClaims.length = 1 ∧
              inst'.initDomainPts = domPts ∧ inst'.initDegBound = d₀ ∧
              inst'.initMinAgree = A₀ ∧ inst'.stages = []) :=
            ⟨hWfDec.1, hWfDec.2.1, hWfDec.2.2.1, hWfDec.2.2.2.1, hWfDec.2.2.2.2.1, rfl⟩
          have hChainInst : HemStageChainWellFormed domPts (d₀ + 1) (A₀ + 1) inst.stages := by
            rw [hWfDec.2.2.2.2.2]; exact hChain
          have hInvalid : ¬ HemStatementValid inst := fun hV =>
            hDoomed ⟨⟨⟨Nat.le_refl 1, by decide⟩, hWfDec.1, hWfDec.2.1, hWfDec.2.2.1,
              hWfDec.2.2.2.1, hWfDec.2.2.2.2.1, hChainInst⟩, hWfDec.2.2.2.2.2, hV⟩
          have hInvalid' : ¬ hemCoreLive 1 domPts d₀ A₀ inst' .init := fun h =>
            hInvalid ((HemStatementValid_iff inst).mpr ((HemStatementValid_iff inst').mp h.2))
          refine hemSingleCascade_flip_bound S domPts d₀ A₀ badMca listG cert inst' .init
            (.msgCascade [s₀]) hInvalid' L hNd ?_
          intro ch hch hNo
          refine hL ch hch (fun hLive => hNo ?_)
          rw [hStepEq] at hLive
          have hCoreStep :
              hemSingleCascadeStep S domPts d₀ A₀ inst' .init (.msgCascade [s₀]) ch.1 =
                .postCascade
                  (evalCascadeOracle domPts inst'.batchOracles
                    [(prodPool S).getD ch.1 (CommRingOps.zero, CommRingOps.zero)])
                  (evalCascadeClaim inst'.batchClaims [s₀]
                    [(prodPool S).getD ch.1 (CommRingOps.zero, CommRingOps.zero)]) := by
            unfold hemSingleCascadeStep
            rw [decide_eq_true hCoreDec]
            rfl
          rw [hCoreStep]
          exact hLive
        · refine length_le_of_all_dead L hL (fun ch h => ?_)
          have hStepEq :
              hemFoldCascadeStep S domPts d₀ A₀ stages inst .init (.cascade [s₀]) ch.1 =
                .invalid := by
            show hemFoldGuard (decide _) _ = _
            rw [decide_eq_false hWfDec, hemFoldGuard_false]
          rw [hStepEq] at h
          exact h
      · exact length_le_of_all_dead L hL (fun _ h => h)

private theorem hemFoldCross_flip_bound
    (S : List QuarticGoldilocks) (hS : S.Nodup)
    (domPts : List QuarticGoldilocks) (d₀ A₀ : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks))
    (curDom : List QuarticGoldilocks) (curDeg curAgree : Nat)
    (st : HemWhirStageSpec QuarticGoldilocks) (b : HemFoldBudget)
    (hGeom : HemFoldStageGeom curDom curDeg curAgree st)
    (hCert : HemStageFoldCert S st b)
    (inst : HemWhirInstance QuarticGoldilocks) (s : HemFoldIopState) (m : HemFoldIopMsg)
    (hDoomed : ¬ hemFoldIopLive domPts d₀ A₀ stages inst s)
    (L : List (Fin S.length)) (hNd : L.Nodup)
    (hL : ∀ ch ∈ L, ¬¬ hemFoldIopLive domPts d₀ A₀ stages inst
      (hemFoldCrossStep S curDom curDeg curAgree st s m ch.1)) :
    L.length ≤ b.listLo * b.listLo := by
  cases s with
  | init => exact length_le_of_all_dead L hL (fun _ h => h)
  | mid _ _ _ _ _ _ _ _ => exact length_le_of_all_dead L hL (fun _ h => h)
  | accepted => exact length_le_of_all_dead L hL (fun _ h => h)
  | invalid => exact length_le_of_all_dead L hL (fun _ h => h)
  | cur dom deg agree oracle kernel claim =>
    cases m with
    | cascade _ => exact length_le_of_all_dead L hL (fun _ h => h)
    | shift _ _ => exact length_le_of_all_dead L hL (fun _ h => h)
    | commit _ => exact length_le_of_all_dead L hL (fun _ h => h)
    | final _ => exact length_le_of_all_dead L hL (fun _ h => h)
    | cross w₀ w₁ w₂ =>
      by_cases hG : (dom = curDom ∧ deg = curDeg ∧ agree = curAgree ∧ kernel.length % 2 = 0)
      · have hStepEq : ∀ ch : Fin S.length,
            hemFoldCrossStep S curDom curDeg curAgree st
                (.cur dom deg agree oracle kernel claim) (.cross w₀ w₁ w₂) ch.1 =
              .mid curDom st.domainPts (st.degBound - 1) (st.minAgree - 1) oracle
                (hemKernelFold (S.get ch) kernel)
                (CommRingOps.add w₀ (CommRingOps.mul (S.get ch) w₁))
                (CommRingOps.add w₂
                  (CommRingOps.mul (S.get ch) (CommRingOps.sub claim w₀))) := by
          intro ch
          show hemFoldGuard (decide _) _ = _
          rw [decide_eq_true hG, hemFoldGuard_true, list_getD_eq_get S _ ch]
        obtain ⟨hDomEq, hDegEq, hAgEq, hPar⟩ := hG
        subst hDomEq; subst hDegEq; subst hAgEq
        have hPair := hemFoldStageGeom_antipodal hGeom
        obtain ⟨_, _, _, _, hDeg1, hDeg2, hAg1, _, hAg3⟩ := hGeom
        have hInvalidIn : ∀ Q : List QuarticGoldilocks,
            polyWitnessValid dom agree deg oracle kernel claim Q = false := by
          intro Q
          cases hV : polyWitnessValid dom agree deg oracle kernel claim Q
          · rfl
          · exact absurd ⟨Q, hV⟩ hDoomed
        have hBound := hemCrossRound_bad_phi_bound dom st.domainPts S kernel
          (st.degBound - 1) (st.minAgree - 1) (kernel.length / 2) deg agree oracle claim
          w₀ w₁ w₂ hPair hS (by omega) (by omega) (by omega) (by omega) hInvalidIn L hNd
          (fun i hi hNo => hL i hi (fun hLive => hNo (by
            rw [hStepEq] at hLive
            exact hLive)))
        exact Nat.le_trans hBound
          (Nat.mul_le_mul (hCert.list_lo_bound _) (hCert.list_lo_bound _))
      · refine length_le_of_all_dead L hL (fun ch h => ?_)
        have hStepEq :
            hemFoldCrossStep S curDom curDeg curAgree st
              (.cur dom deg agree oracle kernel claim) (.cross w₀ w₁ w₂) ch.1 = .invalid := by
          show hemFoldGuard (decide _) _ = _
          rw [decide_eq_false hG, hemFoldGuard_false]
        rw [hStepEq] at h
        exact h

private theorem hemFoldShift_flip_bound
    (S : List QuarticGoldilocks) (hS : S.Nodup)
    (domPts : List QuarticGoldilocks) (d₀ A₀ : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks))
    (curDom : List QuarticGoldilocks) (curDeg curAgree : Nat)
    (st : HemWhirStageSpec QuarticGoldilocks) (b : HemFoldBudget)
    (hGeom : HemFoldStageGeom curDom curDeg curAgree st)
    (hCert : HemStageFoldCert S st b)
    (inst : HemWhirInstance QuarticGoldilocks) (s : HemFoldIopState) (m : HemFoldIopMsg)
    (hDoomed : ¬ hemFoldIopLive domPts d₀ A₀ stages inst s)
    (L : List (Fin (threePool S S).length)) (hNd : L.Nodup)
    (hL : ∀ ch ∈ L, ¬¬ hemFoldIopLive domPts d₀ A₀ stages inst
      (hemFoldShiftStep S curDom st s m ch.1)) :
    L.length ≤ S.length * b.badMca + b.listLo * b.listLo * (S.length * S.length) +
      b.listHi * b.listHi * (S.length * S.length) := by
  cases s with
  | init => exact length_le_of_all_dead L hL (fun _ h => h)
  | cur _ _ _ _ _ _ => exact length_le_of_all_dead L hL (fun _ h => h)
  | accepted => exact length_le_of_all_dead L hL (fun _ h => h)
  | invalid => exact length_le_of_all_dead L hL (fun _ h => h)
  | mid dIn dOut d A oracle kernel e_f e_g =>
    cases m with
    | cascade _ => exact length_le_of_all_dead L hL (fun _ h => h)
    | cross _ _ _ => exact length_le_of_all_dead L hL (fun _ h => h)
    | commit _ => exact length_le_of_all_dead L hL (fun _ h => h)
    | final _ => exact length_le_of_all_dead L hL (fun _ h => h)
    | shift c_F c_G =>
      by_cases hG : (dIn = curDom ∧ dOut = st.domainPts ∧ d = st.degBound - 1 ∧
          A = st.minAgree - 1)
      · have hStepEq : ∀ ch : Fin (threePool S S).length,
            hemFoldShiftStep S curDom st (.mid dIn dOut d A oracle kernel e_f e_g)
                (.shift c_F c_G) ch.1 =
              .cur st.domainPts st.degBound st.minAgree
                (hemVirtualFoldOracle ((threePool S S).get ch).1 ((threePool S S).get ch).2.1
                  ((threePool S S).get ch).2.2 curDom st.domainPts oracle)
                kernel
                (hemFoldClaimUpdate e_f e_g c_F c_G ((threePool S S).get ch).1
                  ((threePool S S).get ch).2.1 ((threePool S S).get ch).2.2) := by
          intro ch
          show hemFoldGuard (decide _) _ = _
          rw [decide_eq_true hG, hemFoldGuard_true, list_getD_eq_get (threePool S S) _ ch]
        obtain ⟨hInEq, hOutEq, hdEq, hAEq⟩ := hG
        subst hInEq; subst hOutEq; subst hdEq; subst hAEq
        obtain ⟨_, hNdOut, _, _, hDeg1, _, hAg1, _, _⟩ := hGeom
        have hdSucc : st.degBound - 1 + 1 = st.degBound := by omega
        have hASucc : st.minAgree - 1 + 1 = st.minAgree := by omega
        have hDecomp : AffineFoldDecompBound st.domainPts S (st.degBound - 1 + 1)
            (st.minAgree - 1 + 1) b.badMca := by
          rw [hdSucc, hASucc]; exact hCert.decomp_bound
        have hBound := hemShiftRound_bad_triples_bound dIn st.domainPts S kernel
          (st.degBound - 1) (st.minAgree - 1) b.badMca oracle e_f e_g c_F c_G
          hNdOut hS (by omega) hDecomp hDoomed L hNd
          (fun ch hch hNo => hL ch hch (fun hLive => hNo (by
            rw [hStepEq] at hLive
            rw [hdSucc, hASucc]
            exact hLive)))
        rw [hdSucc] at hBound
        have hLo := Nat.mul_le_mul
          (hCert.list_lo_bound (lookupDomOracle st.domainPts (cosetEvenOracle oracle)))
          (hCert.list_lo_bound (lookupDomOracle st.domainPts (cosetOddOracle dIn oracle)))
        have hHi := Nat.mul_le_mul
          (hCert.list_hi_bound (lookupDomOracle st.domainPts (cosetEvenOracle oracle)))
          (hCert.list_hi_bound (lookupDomOracle st.domainPts (cosetOddOracle dIn oracle)))
        exact Nat.le_trans hBound
          (Nat.add_le_add
            (Nat.add_le_add_left (Nat.mul_le_mul_right _ hLo) _)
            (Nat.mul_le_mul_right _ hHi))
      · refine length_le_of_all_dead L hL (fun ch h => ?_)
        have hStepEq :
            hemFoldShiftStep S curDom st (.mid dIn dOut d A oracle kernel e_f e_g)
              (.shift c_F c_G) ch.1 = .invalid := by
          show hemFoldGuard (decide _) _ = _
          rw [decide_eq_false hG, hemFoldGuard_false]
        rw [hStepEq] at h
        exact h

private theorem polyWitnessValid_congr_oracle
    (dom : List QuarticGoldilocks) (A d : Nat) (O₁ O₂ : Nat → QuarticGoldilocks)
    (k : List QuarticGoldilocks) (c : QuarticGoldilocks) (P : List QuarticGoldilocks)
    (h : ∀ i : Nat, i < dom.length → O₁ i = O₂ i) :
    polyWitnessValid dom A d O₁ k c P = polyWitnessValid dom A d O₂ k c P := by
  simp only [polyWitnessValid_def]
  have hCount : hemCosetAgreeCount dom O₁ P = hemCosetAgreeCount dom O₂ P := by
    simp only [hemCosetAgreeCount_def]
    apply qsum_congr; intro idx
    rw [h idx.1 idx.2]
  rw [hCount]

theorem hemTableMatchesOracle_spec (n : Nat) (table : List QuarticGoldilocks)
    (oracle : Nat → QuarticGoldilocks) (h : hemTableMatchesOracle n table oracle = true)
    (i : Nat) (hi : i < n) : tableToOracle table i = oracle i :=
  of_decide_eq_true (List.all_eq_true.mp h i (List.mem_range.mpr hi))

private theorem hemFoldCommit_flip_bound
    (domPts : List QuarticGoldilocks) (d₀ A₀ : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks))
    (inst : HemWhirInstance QuarticGoldilocks) (s : HemFoldIopState) (m : HemFoldIopMsg)
    (hDoomed : ¬ hemFoldIopLive domPts d₀ A₀ stages inst s)
    (L : List (Fin 1)) (_hNd : L.Nodup)
    (hL : ∀ ch ∈ L, ¬¬ hemFoldIopLive domPts d₀ A₀ stages inst (hemFoldCommitStep s m)) :
    L.length ≤ 0 := by
  refine length_le_of_all_dead L hL (fun _ hLive => ?_)
  cases s with
  | init => exact hLive
  | mid _ _ _ _ _ _ _ _ => exact hLive
  | accepted => exact hLive
  | invalid => exact hLive
  | cur dom deg agree oracle kernel claim =>
    cases m with
    | cascade _ => exact hLive
    | cross _ _ _ => exact hLive
    | shift _ _ => exact hLive
    | final _ => exact hLive
    | commit table =>
      have hStep : hemFoldCommitStep (.cur dom deg agree oracle kernel claim) (.commit table) =
          hemFoldGuard (hemTableMatchesOracle dom.length table oracle)
            (.cur dom deg agree (tableToOracle table) kernel claim) := by rfl
      rw [hStep] at hLive
      cases hM : hemTableMatchesOracle dom.length table oracle
      · rw [hM, hemFoldGuard_false] at hLive
        exact hLive
      · rw [hM, hemFoldGuard_true] at hLive
        rcases hLive with ⟨P, hP⟩
        rw [polyWitnessValid_congr_oracle dom agree deg (tableToOracle table) oracle kernel
          claim P (hemTableMatchesOracle_spec dom.length table oracle hM)] at hP
        exact hDoomed ⟨P, hP⟩

private theorem hemFoldFinal_flip_bound
    (domPts : List QuarticGoldilocks) (d₀ A₀ : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks))
    (inst : HemWhirInstance QuarticGoldilocks) (s : HemFoldIopState) (m : HemFoldIopMsg)
    (hDoomed : ¬ hemFoldIopLive domPts d₀ A₀ stages inst s)
    (L : List (Fin 1)) (_hNd : L.Nodup)
    (hL : ∀ ch ∈ L, ¬¬ hemFoldIopLive domPts d₀ A₀ stages inst (hemFoldFinalStep s m)) :
    L.length ≤ 0 := by
  refine length_le_of_all_dead L hL (fun _ hLive => ?_)
  cases s with
  | init => exact hLive
  | mid _ _ _ _ _ _ _ _ => exact hLive
  | accepted => exact hLive
  | invalid => exact hLive
  | cur dom deg agree oracle kernel claim =>
    cases m with
    | cascade _ => exact hLive
    | cross _ _ _ => exact hLive
    | shift _ _ => exact hLive
    | commit _ => exact hLive
    | final coeffs =>
      have hStep : hemFoldFinalStep (.cur dom deg agree oracle kernel claim) (.final coeffs) =
          hemFoldGuard (polyWitnessValid dom agree deg oracle kernel claim coeffs)
            .accepted := by rfl
      rw [hStep] at hLive
      cases hV : polyWitnessValid dom agree deg oracle kernel claim coeffs
      · rw [hV, hemFoldGuard_false] at hLive
        exact hLive
      · exact hDoomed ⟨coeffs, hV⟩

/-! ## §4. Round specifications, the IOP and its `RbrStateFunction` -/

/-- Round specification type of the multi-stage IOP. -/
abbrev HemFoldRoundSpec (domPts : List QuarticGoldilocks) (d₀ A₀ : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks)) : Type :=
  SeqRoundSpec (HemWhirInstance QuarticGoldilocks) HemFoldIopState HemFoldIopMsg
    (hemFoldIopLive domPts d₀ A₀ stages)

/-- Round 0: flips on at most `badMca + listG * |S|` of the `|S|²` cascade challenges. -/
def hemFoldCascadeSpec (S : List QuarticGoldilocks) (hSpos : 0 < S.length)
    (domPts : List QuarticGoldilocks) (d₀ A₀ badMca listG : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks))
    (cert : HemCascadeRbrCert S domPts d₀ A₀ badMca listG)
    (hChain : HemStageChainWellFormed domPts (d₀ + 1) (A₀ + 1) stages) :
    HemFoldRoundSpec domPts d₀ A₀ stages where
  chalCard := (prodPool S).length
  h_pos := by rw [prodPool_length]; exact Nat.mul_pos hSpos hSpos
  bad := badMca + 1 * listG * S.length
  step := hemFoldCascadeStep S domPts d₀ A₀ stages
  flip_bound := hemFoldCascade_flip_bound S domPts d₀ A₀ badMca listG stages cert hChain

/-- `cross` round: flips on at most `listLo²` of the `|S|` challenges `φ`. -/
def hemFoldCrossSpec (S : List QuarticGoldilocks) (hS : S.Nodup) (hSpos : 0 < S.length)
    (domPts : List QuarticGoldilocks) (d₀ A₀ : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks))
    (curDom : List QuarticGoldilocks) (curDeg curAgree : Nat)
    (st : HemWhirStageSpec QuarticGoldilocks) (b : HemFoldBudget)
    (hGeom : HemFoldStageGeom curDom curDeg curAgree st)
    (hCert : HemStageFoldCert S st b) :
    HemFoldRoundSpec domPts d₀ A₀ stages where
  chalCard := S.length
  h_pos := hSpos
  bad := b.listLo * b.listLo
  step := fun _ => hemFoldCrossStep S curDom curDeg curAgree st
  flip_bound := hemFoldCross_flip_bound S hS domPts d₀ A₀ stages curDom curDeg curAgree st b
    hGeom hCert

/-- `shift` round: flips on at most
    `|S| * badMca + listLo² * |S|² + listHi² * |S|²` of the `|S|³` challenges `(θ, α, β)`. -/
def hemFoldShiftSpec (S : List QuarticGoldilocks) (hS : S.Nodup) (hSpos : 0 < S.length)
    (domPts : List QuarticGoldilocks) (d₀ A₀ : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks))
    (curDom : List QuarticGoldilocks) (curDeg curAgree : Nat)
    (st : HemWhirStageSpec QuarticGoldilocks) (b : HemFoldBudget)
    (hGeom : HemFoldStageGeom curDom curDeg curAgree st)
    (hCert : HemStageFoldCert S st b) :
    HemFoldRoundSpec domPts d₀ A₀ stages where
  chalCard := (threePool S S).length
  h_pos := by
    rw [threePool_length]
    exact Nat.mul_pos hSpos (Nat.mul_pos hSpos hSpos)
  bad := S.length * b.badMca + b.listLo * b.listLo * (S.length * S.length) +
    b.listHi * b.listHi * (S.length * S.length)
  step := fun _ => hemFoldShiftStep S curDom st
  flip_bound := hemFoldShift_flip_bound S hS domPts d₀ A₀ stages curDom curDeg curAgree st b
    hGeom hCert

/-- `commit` round: deterministic (`bad = 0`, one challenge). -/
def hemFoldCommitSpec (domPts : List QuarticGoldilocks) (d₀ A₀ : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks)) :
    HemFoldRoundSpec domPts d₀ A₀ stages where
  chalCard := 1
  h_pos := Nat.zero_lt_one
  bad := 0
  step := fun _ s m _ => hemFoldCommitStep s m
  flip_bound := hemFoldCommit_flip_bound domPts d₀ A₀ stages

/-- Final round: deterministic (`bad = 0`, one challenge). -/
def hemFoldFinalSpec (domPts : List QuarticGoldilocks) (d₀ A₀ : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks)) :
    HemFoldRoundSpec domPts d₀ A₀ stages where
  chalCard := 1
  h_pos := Nat.zero_lt_one
  bad := 0
  step := fun _ s m _ => hemFoldFinalStep s m
  flip_bound := hemFoldFinal_flip_bound domPts d₀ A₀ stages

/-- Round specifications of the fold stages `remStages` starting from the running geometry
    `(curDom, curDeg, curAgree)`, followed by the final round. -/
def hemFoldStageSpecs (S : List QuarticGoldilocks) (hS : S.Nodup) (hSpos : 0 < S.length)
    (domPts : List QuarticGoldilocks) (d₀ A₀ : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks))
    (bud : HemWhirStageSpec QuarticGoldilocks → HemFoldBudget) :
    (curDom : List QuarticGoldilocks) → (curDeg curAgree : Nat) →
    (remStages : List (HemWhirStageSpec QuarticGoldilocks)) →
    HemStageChainWellFormed curDom curDeg curAgree remStages →
    (∀ st ∈ remStages, HemStageFoldCert S st (bud st)) →
    List (HemFoldRoundSpec domPts d₀ A₀ stages)
  | _, _, _, [], _, _ => [hemFoldFinalSpec domPts d₀ A₀ stages]
  | curDom, curDeg, curAgree, st :: rest, hChain, hCerts =>
    hemFoldCrossSpec S hS hSpos domPts d₀ A₀ stages curDom curDeg curAgree st (bud st)
      ((hemStageChainWellFormed_cons_iff curDom curDeg curAgree st rest).mp hChain).1
      (hCerts st (.head rest)) ::
    hemFoldShiftSpec S hS hSpos domPts d₀ A₀ stages curDom curDeg curAgree st (bud st)
      ((hemStageChainWellFormed_cons_iff curDom curDeg curAgree st rest).mp hChain).1
      (hCerts st (.head rest)) ::
    hemFoldCommitSpec domPts d₀ A₀ stages ::
    hemFoldStageSpecs S hS hSpos domPts d₀ A₀ stages bud st.domainPts st.degBound st.minAgree
      rest ((hemStageChainWellFormed_cons_iff curDom curDeg curAgree st rest).mp hChain).2
      (fun s hs => hCerts s (.tail st hs))

/-- All `3 * stages.length + 2` round specifications: cascade, three rounds per stage, final. -/
def hemMultistageSpecs (S : List QuarticGoldilocks) (hSpos : 0 < S.length)
    (domPts : List QuarticGoldilocks) (d₀ A₀ badMca listG : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks))
    (bud : HemWhirStageSpec QuarticGoldilocks → HemFoldBudget)
    (cert : HemMultistageRbrCert S domPts d₀ A₀ badMca listG stages bud) :
    List (HemFoldRoundSpec domPts d₀ A₀ stages) :=
  hemFoldCascadeSpec S hSpos domPts d₀ A₀ badMca listG stages cert.cascade_cert cert.chain ::
  hemFoldStageSpecs S cert.cascade_cert.pool_nodup hSpos domPts d₀ A₀ stages bud
    domPts (d₀ + 1) (A₀ + 1) stages cert.chain cert.stage_certs

/-- Proof-free run of the stage rounds and the final round, with the `commit` step as a
    parameter. The verifier uses `hemFoldCommitStep`; the test module instantiates a mutant. -/
def hemFoldRunStagesWith (commitStep : HemFoldIopState → HemFoldIopMsg → HemFoldIopState)
    (S : List QuarticGoldilocks) :
    List QuarticGoldilocks → Nat → Nat → List (HemWhirStageSpec QuarticGoldilocks) →
    HemFoldIopState → List (HemFoldIopMsg × Nat) → HemFoldIopState
  | _, _, _, [], s, [] => s
  | _, _, _, [], s, (m, _) :: _ => hemFoldFinalStep s m
  | _, _, _, _ :: _, s, [] => s
  | curDom, curDeg, curAgree, st :: _, s, [(m₁, c₁)] =>
    hemFoldCrossStep S curDom curDeg curAgree st s m₁ c₁
  | curDom, curDeg, curAgree, st :: _, s, [(m₁, c₁), (m₂, c₂)] =>
    hemFoldShiftStep S curDom st (hemFoldCrossStep S curDom curDeg curAgree st s m₁ c₁) m₂ c₂
  | curDom, curDeg, curAgree, st :: rest, s, (m₁, c₁) :: (m₂, c₂) :: (m₃, _) :: tr =>
    hemFoldRunStagesWith commitStep S st.domainPts st.degBound st.minAgree rest
      (commitStep
        (hemFoldShiftStep S curDom st
          (hemFoldCrossStep S curDom curDeg curAgree st s m₁ c₁) m₂ c₂) m₃) tr

/-- Proof-free run of the whole IOP on a transcript prefix, with the `commit` step as a
    parameter. -/
def hemMultistageRunWith (commitStep : HemFoldIopState → HemFoldIopMsg → HemFoldIopState)
    (S domPts : List QuarticGoldilocks) (d₀ A₀ : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks))
    (inst : HemWhirInstance QuarticGoldilocks) :
    List (HemFoldIopMsg × Nat) → HemFoldIopState
  | [] => .init
  | (m, c) :: tr =>
    hemFoldRunStagesWith commitStep S domPts (d₀ + 1) (A₀ + 1) stages
      (hemFoldCascadeStep S domPts d₀ A₀ stages inst .init m c) tr

/-- The accepting state. -/
def hemFoldStateAccepted : HemFoldIopState → Bool
  | .accepted => true
  | _ => false

/-- Run of the stage rounds and the final round with the real `commit` step. -/
def hemFoldRunStages (S : List QuarticGoldilocks) :
    List QuarticGoldilocks → Nat → Nat → List (HemWhirStageSpec QuarticGoldilocks) →
    HemFoldIopState → List (HemFoldIopMsg × Nat) → HemFoldIopState :=
  hemFoldRunStagesWith hemFoldCommitStep S

/-- Run of the whole IOP with the real `commit` step. -/
def hemMultistageRun (S domPts : List QuarticGoldilocks) (d₀ A₀ : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks))
    (inst : HemWhirInstance QuarticGoldilocks) :
    List (HemFoldIopMsg × Nat) → HemFoldIopState :=
  hemMultistageRunWith hemFoldCommitStep S domPts d₀ A₀ stages inst

/-- Verifier of the multi-stage IOP: the run ends in the accepting state. It depends on no
    certificate. -/
def hemMultistageVerify (S domPts : List QuarticGoldilocks) (d₀ A₀ : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks))
    (inst : HemWhirInstance QuarticGoldilocks) (tr : List (HemFoldIopMsg × Nat)) : Bool :=
  hemFoldStateAccepted (hemMultistageRun S domPts d₀ A₀ stages inst tr)

private theorem hemFoldStageSpecs_run (S : List QuarticGoldilocks) (hS : S.Nodup)
    (hSpos : 0 < S.length) (domPts : List QuarticGoldilocks) (d₀ A₀ : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks))
    (bud : HemWhirStageSpec QuarticGoldilocks → HemFoldBudget)
    (inst : HemWhirInstance QuarticGoldilocks) :
    ∀ (remStages : List (HemWhirStageSpec QuarticGoldilocks))
      (curDom : List QuarticGoldilocks) (curDeg curAgree : Nat)
      (hChain : HemStageChainWellFormed curDom curDeg curAgree remStages)
      (hCerts : ∀ st ∈ remStages, HemStageFoldCert S st (bud st))
      (s : HemFoldIopState) (tr : List (HemFoldIopMsg × Nat)),
      runSeqSpecs
        (hemFoldStageSpecs S hS hSpos domPts d₀ A₀ stages bud curDom curDeg curAgree remStages
          hChain hCerts) inst s tr =
        hemFoldRunStages S curDom curDeg curAgree remStages s tr
  | [], _, _, _, _, _, _, [] => by rfl
  | [], _, _, _, _, _, _, (_, _) :: _ => by rfl
  | _ :: _, _, _, _, _, _, _, [] => by rfl
  | _ :: _, _, _, _, _, _, _, [(_, _)] => by rfl
  | _ :: _, _, _, _, _, _, _, [(_, _), (_, _)] => by rfl
  | st :: rest, curDom, curDeg, curAgree, hChain, hCerts, s,
      (m₁, c₁) :: (m₂, c₂) :: (m₃, _) :: tr =>
    hemFoldStageSpecs_run S hS hSpos domPts d₀ A₀ stages bud inst rest
      st.domainPts st.degBound st.minAgree
      ((hemStageChainWellFormed_cons_iff curDom curDeg curAgree st rest).mp hChain).2
      (fun s' hs => hCerts s' (.tail st hs))
      (hemFoldCommitStep
        (hemFoldShiftStep S curDom st
          (hemFoldCrossStep S curDom curDeg curAgree st s m₁ c₁) m₂ c₂) m₃) tr

private theorem hemMultistageSpecs_run (S : List QuarticGoldilocks) (hSpos : 0 < S.length)
    (domPts : List QuarticGoldilocks) (d₀ A₀ badMca listG : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks))
    (bud : HemWhirStageSpec QuarticGoldilocks → HemFoldBudget)
    (cert : HemMultistageRbrCert S domPts d₀ A₀ badMca listG stages bud)
    (inst : HemWhirInstance QuarticGoldilocks) (tr : List (HemFoldIopMsg × Nat)) :
    runSeqSpecs (hemMultistageSpecs S hSpos domPts d₀ A₀ badMca listG stages bud cert)
        inst .init tr =
      hemMultistageRun S domPts d₀ A₀ stages inst tr := by
  cases tr with
  | nil => rfl
  | cons mc tr =>
    exact hemFoldStageSpecs_run S cert.cascade_cert.pool_nodup hSpos domPts d₀ A₀ stages bud
      inst stages domPts (d₀ + 1) (A₀ + 1) cert.chain cert.stage_certs _ tr

/-- The multi-stage `Hem` affine-WHIR public-coin IOP: cascade, three rounds per fold stage,
    final opening. Its language is the set of well-formed instances with stage list `stages`
    whose statement holds. -/
def hemMultistageIop (S : List QuarticGoldilocks) (hSpos : 0 < S.length)
    (domPts : List QuarticGoldilocks) (d₀ A₀ badMca listG : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks))
    (bud : HemWhirStageSpec QuarticGoldilocks → HemFoldBudget)
    (cert : HemMultistageRbrCert S domPts d₀ A₀ badMca listG stages bud) :
    PublicCoinIop (HemWhirInstance QuarticGoldilocks) HemFoldIopMsg
      (hemMultistageSpecs S hSpos domPts d₀ A₀ badMca listG stages bud cert).length :=
  seqSpecsIop (hemMultistageSpecs S hSpos domPts d₀ A₀ badMca listG stages bud cert)
    (fun inst => WellFormedHemCascadeInstance 1 domPts d₀ A₀ inst ∧ inst.stages = stages ∧
      HemStatementValid inst)
    (hemMultistageVerify S domPts d₀ A₀ stages)

private theorem hemMultistageAccept_implies_live
    (S : List QuarticGoldilocks) (hSpos : 0 < S.length)
    (domPts : List QuarticGoldilocks) (d₀ A₀ badMca listG : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks))
    (bud : HemWhirStageSpec QuarticGoldilocks → HemFoldBudget)
    (cert : HemMultistageRbrCert S domPts d₀ A₀ badMca listG stages bud)
    (inst : HemWhirInstance QuarticGoldilocks) (tr : List (HemFoldIopMsg × Nat))
    (_hLen : tr.length =
      (hemMultistageSpecs S hSpos domPts d₀ A₀ badMca listG stages bud cert).length)
    (hVer : hemMultistageVerify S domPts d₀ A₀ stages inst tr = true) :
    hemFoldIopLive domPts d₀ A₀ stages inst
      (runSeqSpecs (hemMultistageSpecs S hSpos domPts d₀ A₀ badMca listG stages bud cert)
        inst .init tr) := by
  rw [hemMultistageSpecs_run]
  have hVer' : hemFoldStateAccepted (hemMultistageRun S domPts d₀ A₀ stages inst tr) = true :=
    hVer
  clear hVer
  generalize hemMultistageRun S domPts d₀ A₀ stages inst tr = sEnd at hVer'
  cases sEnd with
  | accepted => exact True.intro
  | init => exact Bool.noConfusion hVer'
  | cur _ _ _ _ _ _ => exact Bool.noConfusion hVer'
  | mid _ _ _ _ _ _ _ _ => exact Bool.noConfusion hVer'
  | invalid => exact Bool.noConfusion hVer'

/-- **`RbrStateFunction` of the multi-stage IOP.** Round 0 flips on at most
    `badMca + listG * |S|` of `|S|²` challenges; for each stage `st` the `cross` round flips on
    at most `listLo²` of `|S|`, the `shift` round on at most
    `|S| * badMca + (listLo² + listHi²) * |S|²` of `|S|³` (budget `bud st`), and the `commit`
    round on none; the final round flips on none. -/
def hemMultistageRbrOf (S : List QuarticGoldilocks) (hSpos : 0 < S.length)
    (domPts : List QuarticGoldilocks) (d₀ A₀ badMca listG : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks))
    (bud : HemWhirStageSpec QuarticGoldilocks → HemFoldBudget)
    (cert : HemMultistageRbrCert S domPts d₀ A₀ badMca listG stages bud) :
    RbrStateFunction (hemMultistageIop S hSpos domPts d₀ A₀ badMca listG stages bud cert) :=
  seqSpecsRbr (hemMultistageSpecs S hSpos domPts d₀ A₀ badMca listG stages bud cert)
    (fun _ => .init)
    (fun inst => WellFormedHemCascadeInstance 1 domPts d₀ A₀ inst ∧ inst.stages = stages ∧
      HemStatementValid inst)
    (hemMultistageVerify S domPts d₀ A₀ stages)
    (fun _ hNot hLive => hNot hLive)
    (hemMultistageAccept_implies_live S hSpos domPts d₀ A₀ badMca listG stages bud cert)

/-- **State-restoration soundness of the multi-stage cascade IOP.** For an arbitrary-length
    stage list `stages` with certificate `cert`, any instance whose statement is false, and any
    adaptive rewinding attack `tree` over a round schedule `sched`, the acceptance probability
    is at most the sum of the per-round flip ratios of `hemMultistageRbrOf` along `sched`. -/
theorem hemMultistage_state_restoration_soundness
    (S : List QuarticGoldilocks) (hSpos : 0 < S.length)
    (domPts : List QuarticGoldilocks) (d₀ A₀ badMca listG : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks))
    (bud : HemWhirStageSpec QuarticGoldilocks → HemFoldBudget)
    (cert : HemMultistageRbrCert S domPts d₀ A₀ badMca listG stages bud)
    (inst : HemWhirInstance QuarticGoldilocks)
    (hInvalid : ¬ HemStatementValid inst)
    (sched : List (Fin
      (hemMultistageSpecs S hSpos domPts d₀ A₀ badMca listG stages bud cert).length))
    (tree : SrScheduleTree
      (hemMultistageIop S hSpos domPts d₀ A₀ badMca listG stages bud cert) sched) :
    RatBound.le
      (srTreeAcceptProb (hemMultistageIop S hSpos domPts d₀ A₀ badMca listG stages bud cert)
        tree inst)
      (srScheduleErrorSum
        (hemMultistageRbrOf S hSpos domPts d₀ A₀ badMca listG stages bud cert) sched) :=
  rbr_implies_state_restoration_soundness
    (hemMultistageRbrOf S hSpos domPts d₀ A₀ badMca listG stages bud cert)
    inst (fun h => by
      simp only [hemMultistageIop, seqSpecsIop_inLang] at h
      exact hInvalid h.2.2) sched tree

/-! ## §5. Step equations and explicit round budgets -/

theorem hemFoldCascadeStep_init (S domPts : List QuarticGoldilocks) (d₀ A₀ : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks))
    (inst : HemWhirInstance QuarticGoldilocks) (s₀ : QuarticGoldilocks) (ch : Nat)
    (h : inst.batchOracles.length = 1 ∧ inst.batchClaims.length = 1 ∧
      inst.initDomainPts = domPts ∧ inst.initDegBound = d₀ ∧
      inst.initMinAgree = A₀ ∧ inst.stages = stages) :
    hemFoldCascadeStep S domPts d₀ A₀ stages inst .init (.cascade [s₀]) ch =
      .cur domPts (d₀ + 1) (A₀ + 1)
        (evalCascadeOracle domPts inst.batchOracles
          [(prodPool S).getD ch (CommRingOps.zero, CommRingOps.zero)])
        inst.initKernel
        (evalCascadeClaim inst.batchClaims [s₀]
          [(prodPool S).getD ch (CommRingOps.zero, CommRingOps.zero)]) := by
  show hemFoldGuard (decide _) _ = _
  rw [decide_eq_true h, hemFoldGuard_true]

theorem hemFoldCrossStep_cur (S curDom : List QuarticGoldilocks) (curDeg curAgree : Nat)
    (st : HemWhirStageSpec QuarticGoldilocks) (oracle : Nat → QuarticGoldilocks)
    (kernel : List QuarticGoldilocks) (claim w₀ w₁ w₂ : QuarticGoldilocks) (ch : Nat)
    (hPar : kernel.length % 2 = 0) :
    hemFoldCrossStep S curDom curDeg curAgree st
        (.cur curDom curDeg curAgree oracle kernel claim) (.cross w₀ w₁ w₂) ch =
      .mid curDom st.domainPts (st.degBound - 1) (st.minAgree - 1) oracle
        (hemKernelFold (S.getD ch CommRingOps.zero) kernel)
        (CommRingOps.add w₀ (CommRingOps.mul (S.getD ch CommRingOps.zero) w₁))
        (CommRingOps.add w₂
          (CommRingOps.mul (S.getD ch CommRingOps.zero) (CommRingOps.sub claim w₀))) := by
  show hemFoldGuard (decide _) _ = _
  rw [decide_eq_true (⟨rfl, rfl, rfl, hPar⟩ :
    curDom = curDom ∧ curDeg = curDeg ∧ curAgree = curAgree ∧ kernel.length % 2 = 0),
    hemFoldGuard_true]

theorem hemFoldShiftStep_mid (S curDom : List QuarticGoldilocks)
    (st : HemWhirStageSpec QuarticGoldilocks) (oracle : Nat → QuarticGoldilocks)
    (kernel : List QuarticGoldilocks) (e_f e_g c_F c_G : QuarticGoldilocks) (ch : Nat) :
    hemFoldShiftStep S curDom st
        (.mid curDom st.domainPts (st.degBound - 1) (st.minAgree - 1) oracle kernel e_f e_g)
        (.shift c_F c_G) ch =
      .cur st.domainPts st.degBound st.minAgree
        (hemVirtualFoldOracle
          ((threePool S S).getD ch (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)).1
          ((threePool S S).getD ch (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)).2.1
          ((threePool S S).getD ch (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)).2.2
          curDom st.domainPts oracle)
        kernel
        (hemFoldClaimUpdate e_f e_g c_F c_G
          ((threePool S S).getD ch (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)).1
          ((threePool S S).getD ch (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)).2.1
          ((threePool S S).getD ch (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)).2.2) := by
  show hemFoldGuard (decide _) _ = _
  rw [decide_eq_true (⟨rfl, rfl, rfl, rfl⟩ :
    curDom = curDom ∧ st.domainPts = st.domainPts ∧ st.degBound - 1 = st.degBound - 1 ∧
      st.minAgree - 1 = st.minAgree - 1), hemFoldGuard_true]

theorem hemFoldCommitStep_cur (dom : List QuarticGoldilocks) (deg agree : Nat)
    (oracle : Nat → QuarticGoldilocks) (kernel : List QuarticGoldilocks)
    (claim : QuarticGoldilocks) (table : List QuarticGoldilocks)
    (h : hemTableMatchesOracle dom.length table oracle = true) :
    hemFoldCommitStep (.cur dom deg agree oracle kernel claim) (.commit table) =
      .cur dom deg agree (tableToOracle table) kernel claim := by
  show hemFoldGuard (hemTableMatchesOracle dom.length table oracle) _ = _
  rw [h, hemFoldGuard_true]

theorem hemFoldFinalStep_cur (dom : List QuarticGoldilocks) (deg agree : Nat)
    (oracle : Nat → QuarticGoldilocks) (kernel : List QuarticGoldilocks)
    (claim : QuarticGoldilocks) (coeffs : List QuarticGoldilocks)
    (h : polyWitnessValid dom agree deg oracle kernel claim coeffs = true) :
    hemFoldFinalStep (.cur dom deg agree oracle kernel claim) (.final coeffs) = .accepted := by
  show hemFoldGuard (polyWitnessValid dom agree deg oracle kernel claim coeffs) _ = _
  rw [h, hemFoldGuard_true]

/-- `(bad, number of challenges)` of the three rounds of each stage followed by the final
    round. -/
def hemFoldStageRoundBudgets (S : List QuarticGoldilocks)
    (bud : HemWhirStageSpec QuarticGoldilocks → HemFoldBudget) :
    List (HemWhirStageSpec QuarticGoldilocks) → List (Nat × Nat)
  | [] => [(0, 1)]
  | st :: rest =>
    ((bud st).listLo * (bud st).listLo, S.length) ::
    (S.length * (bud st).badMca + (bud st).listLo * (bud st).listLo * (S.length * S.length) +
      (bud st).listHi * (bud st).listHi * (S.length * S.length), (threePool S S).length) ::
    (0, 1) :: hemFoldStageRoundBudgets S bud rest

private theorem hemFoldStageSpecs_budgets (S : List QuarticGoldilocks) (hS : S.Nodup)
    (hSpos : 0 < S.length) (domPts : List QuarticGoldilocks) (d₀ A₀ : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks))
    (bud : HemWhirStageSpec QuarticGoldilocks → HemFoldBudget) :
    ∀ (remStages : List (HemWhirStageSpec QuarticGoldilocks))
      (curDom : List QuarticGoldilocks) (curDeg curAgree : Nat)
      (hChain : HemStageChainWellFormed curDom curDeg curAgree remStages)
      (hCerts : ∀ st ∈ remStages, HemStageFoldCert S st (bud st)),
      (hemFoldStageSpecs S hS hSpos domPts d₀ A₀ stages bud curDom curDeg curAgree remStages
        hChain hCerts).map (fun sp => (sp.bad, sp.chalCard)) =
        hemFoldStageRoundBudgets S bud remStages
  | [], _, _, _, _, _ => by rfl
  | st :: rest, curDom, curDeg, curAgree, hChain, hCerts =>
    congrArg
      (fun l => ((bud st).listLo * (bud st).listLo, S.length) ::
        (S.length * (bud st).badMca + (bud st).listLo * (bud st).listLo * (S.length * S.length) +
          (bud st).listHi * (bud st).listHi * (S.length * S.length), (threePool S S).length) ::
        (0, 1) :: l)
      (hemFoldStageSpecs_budgets S hS hSpos domPts d₀ A₀ stages bud rest
        st.domainPts st.degBound st.minAgree
        ((hemStageChainWellFormed_cons_iff curDom curDeg curAgree st rest).mp hChain).2
        (fun s' hs => hCerts s' (.tail st hs)))

/-- **Explicit per-round budgets.** The list of `(badCard, challengeCard)` of the IOP rounds is
    the cascade pair `(badMca + listG * |S|, |S|²)` followed by `hemFoldStageRoundBudgets`. -/
theorem hemMultistageSpecs_budgets (S : List QuarticGoldilocks) (hSpos : 0 < S.length)
    (domPts : List QuarticGoldilocks) (d₀ A₀ badMca listG : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks))
    (bud : HemWhirStageSpec QuarticGoldilocks → HemFoldBudget)
    (cert : HemMultistageRbrCert S domPts d₀ A₀ badMca listG stages bud) :
    (hemMultistageSpecs S hSpos domPts d₀ A₀ badMca listG stages bud cert).map
        (fun sp => (sp.bad, sp.chalCard)) =
      (badMca + 1 * listG * S.length, (prodPool S).length) ::
        hemFoldStageRoundBudgets S bud stages :=
  congrArg (List.cons (badMca + 1 * listG * S.length, (prodPool S).length))
    (hemFoldStageSpecs_budgets S cert.cascade_cert.pool_nodup hSpos domPts d₀ A₀ stages bud
      stages domPts (d₀ + 1) (A₀ + 1) cert.chain cert.stage_certs)

theorem hemFoldStageRoundBudgets_length (S : List QuarticGoldilocks)
    (bud : HemWhirStageSpec QuarticGoldilocks → HemFoldBudget) :
    ∀ (stages : List (HemWhirStageSpec QuarticGoldilocks)),
      (hemFoldStageRoundBudgets S bud stages).length = 3 * stages.length + 1
  | [] => by rfl
  | _ :: rest => by
    show (hemFoldStageRoundBudgets S bud rest).length + 1 + 1 + 1 = 3 * (rest.length + 1) + 1
    rw [hemFoldStageRoundBudgets_length S bud rest, Nat.mul_succ]

/-- The IOP has `3 * stages.length + 2` rounds. -/
theorem hemMultistageSpecs_length (S : List QuarticGoldilocks) (hSpos : 0 < S.length)
    (domPts : List QuarticGoldilocks) (d₀ A₀ badMca listG : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks))
    (bud : HemWhirStageSpec QuarticGoldilocks → HemFoldBudget)
    (cert : HemMultistageRbrCert S domPts d₀ A₀ badMca listG stages bud) :
    (hemMultistageSpecs S hSpos domPts d₀ A₀ badMca listG stages bud cert).length =
      3 * stages.length + 2 := by
  have h := congrArg List.length
    (hemMultistageSpecs_budgets S hSpos domPts d₀ A₀ badMca listG stages bud cert)
  rw [List.length_map, List.length_cons, hemFoldStageRoundBudgets_length] at h
  exact h

/-- **Welch–Berlekamp stage certificate.** In the unique-decoding regime the stage certificate
    holds with `listLo = listHi = 1` and the Welch–Berlekamp exceptional count. -/
theorem hemWelchBerlekampStageCert (S : List QuarticGoldilocks)
    (st : HemWhirStageSpec QuarticGoldilocks)
    (hD : st.domainPts.Nodup) (hS : S.Nodup)
    (hdA : st.degBound + 2 ≤ st.minAgree) (hAD : st.minAgree ≤ st.domainPts.length)
    (hWB : 2 * st.domainPts.length + st.degBound + 1 < 3 * st.minAgree)
    (hUniq : st.domainPts.length + st.degBound + 2 < 2 * st.minAgree) :
    HemStageFoldCert S st
      ⟨Nat.max S.length (st.domainPts.length * (st.domainPts.length - 1) / 2), 1, 1⟩ where
  decomp_bound := affineFoldDecompBound_welch_berlekamp st.domainPts S st.degBound st.minAgree
    hD hS hAD hWB
  list_lo_bound := overlap_unique_decode_le_one st.domainPts (st.degBound - 1)
    (st.minAgree - 1) hD (by omega) (by omega)
  list_hi_bound := overlap_unique_decode_le_one st.domainPts st.degBound
    (st.minAgree - 1) hD (by omega) (by omega)

/-- **Johnson-radius stage certificate**, conditional on the same `NonExcludedDecompBound`
    hypothesis as `hemCwyz26JohnsonCert`; the list sizes are the Johnson bounds. -/
theorem hemCwyz26JohnsonStageCert (S : List QuarticGoldilocks)
    (st : HemWhirStageSpec QuarticGoldilocks) (m Wx Dy rest : Nat)
    (hD : st.domainPts.Nodup) (hS : S.Nodup)
    (hdA : st.degBound + 2 ≤ st.minAgree)
    (hCount : st.domainPts.length * Poly3.triCount 1 m Dy m <
      Poly3.triCount st.degBound Wx Dy (Dy + 1))
    (hWA : Wx + Dy ≤ m * st.minAgree)
    (hRest : NonExcludedDecompBound st.domainPts S st.degBound st.minAgree m Wx Dy rest)
    (hDen : st.domainPts.length * st.degBound < (st.minAgree - 1) * (st.minAgree - 1)) :
    HemStageFoldCert S st
      ⟨Dy + rest,
        JohnsonBound.johnsonBound st.domainPts.length (st.minAgree - 1) (st.degBound - 1),
        JohnsonBound.johnsonBound st.domainPts.length (st.minAgree - 1) st.degBound⟩ where
  decomp_bound := cwyz26_affineFoldDecompBound_of_nonExcluded st.domainPts S st.degBound
    st.minAgree m Wx Dy rest hRest hD hS hCount hWA
  list_lo_bound := fun word =>
    gsDecodeList_length_le_johnson st.domainPts word (st.degBound - 1) (st.minAgree - 1) hD
      (by omega)
      (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.sub_le st.degBound 1)) hDen)
  list_hi_bound := fun word =>
    gsDecodeList_length_le_johnson st.domainPts word st.degBound (st.minAgree - 1) hD
      (by omega) hDen

/-- The zero-stage case: a `HemCascadeRbrCert` is a multi-stage certificate for `stages = []`,
    and the IOP then has the two rounds (cascade, final) of `HemRbrSoundness`. -/
theorem hemMultistageRbrCert_nil (S domPts : List QuarticGoldilocks) (d₀ A₀ badMca listG : Nat)
    (bud : HemWhirStageSpec QuarticGoldilocks → HemFoldBudget)
    (cert : HemCascadeRbrCert S domPts d₀ A₀ badMca listG) :
    HemMultistageRbrCert S domPts d₀ A₀ badMca listG [] bud where
  cascade_cert := cert
  chain := hemStageChainWellFormed_nil domPts (d₀ + 1) (A₀ + 1)
  stage_certs := fun _ h => nomatch h

/-! ## §6. Acceptance bridge from the `verifyHemAffineWhir` checker -/

/-- One fold stage of an IOP transcript: the bridge wires, the committed stage table and the
    two challenge indices, together with the out-of-domain data and decoded-polynomial hints
    that only the `verifyHemAffineWhir` checker reads. -/
structure HemFoldStageTrace where
  w₀ : QuarticGoldilocks
  w₁ : QuarticGoldilocks
  w₂ : QuarticGoldilocks
  c_F : QuarticGoldilocks
  c_G : QuarticGoldilocks
  stageTable : List QuarticGoldilocks
  chPhi : Nat
  chTriple : Nat
  z₀ : QuarticGoldilocks
  z₁ : QuarticGoldilocks
  ood₀ : QuarticGoldilocks
  ood₁ : QuarticGoldilocks
  decoded : List (List QuarticGoldilocks)

/-- IOP transcript of the stage rounds and the final round. -/
def hemFoldIopRounds : List HemFoldStageTrace → List QuarticGoldilocks →
    List (HemFoldIopMsg × Nat)
  | [], coeffs => [(.final coeffs, 0)]
  | t :: ts, coeffs =>
    (.cross t.w₀ t.w₁ t.w₂, t.chPhi) :: (.shift t.c_F t.c_G, t.chTriple) ::
      (.commit t.stageTable, 0) :: hemFoldIopRounds ts coeffs

/-- The same rounds as a `verifyHemStages` checker transcript, with the challenges decoded
    from the pool `S`. -/
def hemFoldCheckerRounds (S : List QuarticGoldilocks) :
    List HemFoldStageTrace → List QuarticGoldilocks →
    List (HemTranscriptRound QuarticGoldilocks)
  | [], coeffs => [.finalQuery coeffs]
  | t :: ts, coeffs =>
    .stageFold (tableToOracle t.stageTable) t.w₀ t.w₁ t.w₂ t.c_F t.c_G
      (S.getD t.chPhi CommRingOps.zero)
      ((threePool S S).getD t.chTriple
        (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)).1
      ((threePool S S).getD t.chTriple
        (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)).2.1
      ((threePool S S).getD t.chTriple
        (CommRingOps.zero, CommRingOps.zero, CommRingOps.zero)).2.2
      t.z₀ t.z₁ t.ood₀ t.ood₁ t.decoded :: hemFoldCheckerRounds S ts coeffs

/-- The checks this IOP adds to `verifyHemStages`, on a checker transcript: at every stage the
    running kernel has even length and the stage oracle equals the virtual fold of the previous
    oracle on the whole stage domain. -/
def hemFoldStageChecks :
    (Nat → QuarticGoldilocks) → List QuarticGoldilocks → List QuarticGoldilocks →
    List (HemWhirStageSpec QuarticGoldilocks) →
    List (HemTranscriptRound QuarticGoldilocks) → Bool
  | _, _, _, [], _ => true
  | curOracle, curDom, curKernel, st :: remStages,
    .stageFold stageOracle _ _ _ _ _ φ θ α β _ _ _ _ _ :: restTr =>
    decide (curKernel.length % 2 = 0) &&
    (List.range st.domainPts.length).all (fun i =>
      decide (stageOracle i = hemVirtualFoldOracle θ α β curDom st.domainPts curOracle i)) &&
    hemFoldStageChecks stageOracle st.domainPts (hemKernelFold φ curKernel) remStages restTr
  | _, _, _, _ :: _, _ => false

private theorem checkQueriedCosets_spec (dom : List QuarticGoldilocks)
    (O : Nat → QuarticGoldilocks) (P : List QuarticGoldilocks) :
    ∀ (idxs : List Nat), checkQueriedCosets dom O P idxs = true →
      ∀ i ∈ idxs, i < dom.length ∧
        O i = RoundPoly.evalCoeffs P (dom.getD i CommRingOps.zero)
  | [], _, _, hi => nomatch hi
  | j :: rest, h, i, hi => by
    simp only [checkQueriedCosets_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.mp hi with hEq | hm
    · rw [hEq]; exact ⟨h.1.1, h.1.2⟩
    · exact checkQueriedCosets_spec dom O P rest h.2 i hm

private theorem qsum_prefix_indicator :
    ∀ (n k : Nat), k ≤ n → qsum n (fun i => if i.1 < k then 1 else 0) = k
  | n, 0, _ => by
    have hF : (fun i : Fin n => if i.1 < 0 then 1 else 0) = fun _ => 0 :=
      funext (fun i => ite_false_eq _ _ (Nat.not_lt_zero i.1))
    rw [hF, qsum_const, Nat.mul_zero]
  | 0, k + 1, h => absurd h (Nat.not_succ_le_zero k)
  | n + 1, k + 1, h => by
    show (if 0 < k + 1 then 1 else 0) +
      qsum n (fun i => if i.1 + 1 < k + 1 then 1 else 0) = k + 1
    have hc : (fun i : Fin n => if i.1 + 1 < k + 1 then 1 else 0) =
        fun i => if i.1 < k then 1 else 0 :=
      funext (fun i => by
        by_cases hi : i.1 < k
        · rw [ite_true_eq _ _ hi, ite_true_eq _ _ (Nat.succ_lt_succ hi)]
        · rw [ite_false_eq _ _ hi, ite_false_eq _ _ (fun h' => hi (Nat.lt_of_succ_lt_succ h'))])
    rw [hc, qsum_prefix_indicator n k (Nat.le_of_succ_le_succ h), ite_true_eq _ _ (Nat.succ_pos k),
      Nat.add_comm]

private theorem hemCosetAgreeCount_ge_of_prefix (dom : List QuarticGoldilocks)
    (O : Nat → QuarticGoldilocks) (P : List QuarticGoldilocks) (k : Nat)
    (hk : k ≤ dom.length)
    (h : checkQueriedCosets dom O P (List.range k) = true) :
    k ≤ hemCosetAgreeCount dom O P := by
  have hSpec := checkQueriedCosets_spec dom O P (List.range k) h
  have hLe : qsum dom.length (fun i => if i.1 < k then 1 else 0) ≤
      hemCosetAgreeCount dom O P := by
    rw [hemCosetAgreeCount_def]
    apply qsum_le_qsum; intro idx
    by_cases hi : idx.1 < k
    · have hEq := (hSpec idx.1 (List.mem_range.mpr hi)).2
      rw [list_getD_eq_get dom _ idx] at hEq
      rw [ite_true_eq _ _ hi, ite_true_eq _ _ hEq]
      exact Nat.le_refl 1
    · rw [ite_false_eq _ _ hi]
      exact Nat.zero_le _
  rw [qsum_prefix_indicator dom.length k hk] at hLe
  exact hLe

private theorem hemFoldRunStages_of_checker (S : List QuarticGoldilocks) :
    ∀ (stages : List (HemWhirStageSpec QuarticGoldilocks)) (ts : List HemFoldStageTrace)
      (coeffs : List QuarticGoldilocks) (curOracle : Nat → QuarticGoldilocks)
      (curDom : List QuarticGoldilocks) (curDeg curAgree : Nat)
      (curKernel : List QuarticGoldilocks) (curClaim : QuarticGoldilocks),
      curAgree ≤ curDom.length →
      (∀ st ∈ stages, st.minAgree ≤ st.domainPts.length) →
      verifyHemStages curOracle curDom curDeg curAgree curKernel curClaim stages
        (hemFoldCheckerRounds S ts coeffs) = true →
      hemFoldStageChecks curOracle curDom curKernel stages
        (hemFoldCheckerRounds S ts coeffs) = true →
      hemFoldRunStages S curDom curDeg curAgree stages
        (.cur curDom curDeg curAgree curOracle curKernel curClaim)
        (hemFoldIopRounds ts coeffs) = .accepted
  | [], [], coeffs, O, dom, deg, agree, k, c, hAg, _, hVer, _ => by
    simp only [hemFoldCheckerRounds, verifyHemStages, Bool.and_eq_true,
      decide_eq_true_eq] at hVer
    have hMin : Nat.min agree dom.length = agree := Nat.min_eq_left hAg
    rw [hMin] at hVer
    have hCount := hemCosetAgreeCount_ge_of_prefix dom O coeffs agree hAg hVer.2
    have hPW : polyWitnessValid dom agree deg O k c coeffs = true := by
      rw [polyWitnessValid_def]
      rw [decide_eq_true hVer.1.1, decide_eq_true hCount, decide_eq_true hVer.1.2]
      rfl
    exact hemFoldFinalStep_cur dom deg agree O k c coeffs hPW
  | [], _ :: _, _, _, _, _, _, _, _, _, _, hVer, _ => by
    simp only [hemFoldCheckerRounds, verifyHemStages] at hVer
    exact Bool.noConfusion hVer
  | _ :: _, [], _, _, _, _, _, _, _, _, _, hVer, _ => by
    simp only [hemFoldCheckerRounds, verifyHemStages] at hVer
    exact Bool.noConfusion hVer
  | st :: rem, t :: ts, coeffs, O, dom, deg, agree, k, c, _, hStAg, hVer, hChk => by
    simp only [hemFoldCheckerRounds, verifyHemStages, Bool.and_eq_true] at hVer
    simp only [hemFoldCheckerRounds, hemFoldStageChecks, Bool.and_eq_true,
      decide_eq_true_eq] at hChk
    have ih := hemFoldRunStages_of_checker S rem ts coeffs (tableToOracle t.stageTable)
      st.domainPts st.degBound st.minAgree _ _ (hStAg st (.head rem))
      (fun s' hs => hStAg s' (.tail st hs)) hVer.2 hChk.2
    show hemFoldRunStages S st.domainPts st.degBound st.minAgree rem
      (hemFoldCommitStep
        (hemFoldShiftStep S dom st
          (hemFoldCrossStep S dom deg agree st (.cur dom deg agree O k c)
            (.cross t.w₀ t.w₁ t.w₂) t.chPhi) (.shift t.c_F t.c_G) t.chTriple)
        (.commit t.stageTable)) (hemFoldIopRounds ts coeffs) = .accepted
    rw [hemFoldCrossStep_cur S dom deg agree st O k c t.w₀ t.w₁ t.w₂ t.chPhi hChk.1.1,
      hemFoldShiftStep_mid, hemFoldCommitStep_cur _ _ _ _ _ _ _ hChk.1.2,
      hemFoldClaimUpdate_eq_bridge]
    exact ih

/-- **Acceptance bridge from the stage checker.** Take an IOP transcript with stage data `ts`
    on a one-batch instance. If `verifyHemStages` accepts the corresponding checker rounds from
    the cascade output at degree `initDegBound + 1` and agreement `initMinAgree + 1`, and those
    rounds pass the fold checks `hemFoldStageChecks`, then the multi-stage IOP verifier (run
    with the instance's own parameters) accepts the IOP transcript. The hypothesis is the
    stage part of a `verifyHemAffineWhir` run whose post-cascade agreement threshold is
    `initMinAgree + 1`; the checker alone, without the fold checks, is not covered
    (`tooth_unconstrained_stageOracle_accepts_false_claim`). -/
theorem hemMultistageVerify_of_fold_checked_stages (S : List QuarticGoldilocks)
    (inst : HemWhirInstance QuarticGoldilocks) (s₀ : QuarticGoldilocks) (c₀ : Nat)
    (ts : List HemFoldStageTrace)
    (coeffs : List QuarticGoldilocks)
    (hOne : inst.batchOracles.length = 1)
    (hClaims : inst.batchClaims.length = 1)
    (hAgree : inst.initMinAgree < inst.initDomainPts.length)
    (hStageAgree : ∀ st ∈ inst.stages, st.minAgree ≤ st.domainPts.length)
    (hStages : verifyHemStages
      (evalCascadeOracle inst.initDomainPts inst.batchOracles
        [(prodPool S).getD c₀ (CommRingOps.zero, CommRingOps.zero)])
      inst.initDomainPts (inst.initDegBound + 1) (inst.initMinAgree + 1) inst.initKernel
      (evalCascadeClaim inst.batchClaims [s₀]
        [(prodPool S).getD c₀ (CommRingOps.zero, CommRingOps.zero)])
      inst.stages (hemFoldCheckerRounds S ts coeffs) = true)
    (hFold : hemFoldStageChecks
      (evalCascadeOracle inst.initDomainPts inst.batchOracles
        [(prodPool S).getD c₀ (CommRingOps.zero, CommRingOps.zero)])
      inst.initDomainPts inst.initKernel inst.stages
      (hemFoldCheckerRounds S ts coeffs) = true) :
    hemMultistageVerify S inst.initDomainPts inst.initDegBound inst.initMinAgree inst.stages
      inst ((.cascade [s₀], c₀) :: hemFoldIopRounds ts coeffs) = true := by
  have hRun := hemFoldRunStages_of_checker S inst.stages ts coeffs _ inst.initDomainPts
    (inst.initDegBound + 1) (inst.initMinAgree + 1) inst.initKernel _ hAgree hStageAgree
    hStages hFold
  have hRunEq : hemMultistageRun S inst.initDomainPts inst.initDegBound inst.initMinAgree
      inst.stages inst ((.cascade [s₀], c₀) :: hemFoldIopRounds ts coeffs) = .accepted := by
    show hemFoldRunStages S inst.initDomainPts (inst.initDegBound + 1) (inst.initMinAgree + 1)
      inst.stages
      (hemFoldCascadeStep S inst.initDomainPts inst.initDegBound inst.initMinAgree inst.stages
        inst .init (.cascade [s₀]) c₀) (hemFoldIopRounds ts coeffs) = .accepted
    rw [hemFoldCascadeStep_init S inst.initDomainPts inst.initDegBound inst.initMinAgree
      inst.stages inst s₀ c₀ ⟨hOne, hClaims, rfl, rfl, rfl, rfl⟩]
    exact hRun
  show hemFoldStateAccepted (hemMultistageRun S inst.initDomainPts inst.initDegBound
    inst.initMinAgree inst.stages inst ((.cascade [s₀], c₀) :: hemFoldIopRounds ts coeffs)) = true
  rw [hRunEq]
  rfl

/-! ## §7. Inhabited witness with two fold stages (64 → 32 → 16 points) -/

/-- Base-field element of `QuarticGoldilocks`. -/
@[expose] def hemFoldQg (n : Nat) : QuarticGoldilocks :=
  ⟨⟨Goldilocks.ofNat n, Goldilocks.ofNat 0⟩, ⟨Goldilocks.ofNat 0, Goldilocks.ofNat 0⟩⟩

/-- Bit-reversed exponents `0 .. 2^k - 1`: entries `2 i` and `2 i + 1` differ by `2^(k-1)`. -/
@[expose] def hemBitRevExponents : Nat → List Nat
  | 0 => [0]
  | k + 1 => (hemBitRevExponents k).flatMap (fun e => [e, e + 2 ^ k])

/-- The cyclic group generated by `g` of order `2^k`, in bit-reversed order, so that antipodal
    points are adjacent and the squares form the same list for `g²` and `k - 1`. -/
@[expose] def hemFoldDomain (g k : Nat) : List QuarticGoldilocks :=
  (hemBitRevExponents k).map (fun e => hemFoldQg (g ^ e))

/-- `8` has multiplicative order `64` in the Goldilocks field (`8^32 = 2^96 = -1`). -/
@[expose] def hemFoldDom64 : List QuarticGoldilocks := hemFoldDomain 8 6

theorem hemFoldDom64_head : hemFoldDom64 = hemFoldQg 1 :: hemFoldDom64.tail := by
  unfold hemFoldDom64 hemFoldDomain
  rfl

def hemFoldDom32 : List QuarticGoldilocks := hemFoldDomain 64 5

@[expose] def hemFoldDom16 : List QuarticGoldilocks := hemFoldDomain 4096 4

/-- First fold stage of the witness: 32 points, degree bound 1, agreement 28. -/
def hemFoldWitnessStage1 : HemWhirStageSpec QuarticGoldilocks :=
  { domainPts := hemFoldDom32, degBound := 1, minAgree := 28, listBound := 1,
    queriedCosets := [] }

/-- Second fold stage of the witness: 16 points, degree bound 1, agreement 16. -/
def hemFoldWitnessStage2 : HemWhirStageSpec QuarticGoldilocks :=
  { domainPts := hemFoldDom16, degBound := 1, minAgree := 16, listBound := 1,
    queriedCosets := [] }

def hemFoldWitnessStages : List (HemWhirStageSpec QuarticGoldilocks) :=
  [hemFoldWitnessStage1, hemFoldWitnessStage2]

/-- Welch–Berlekamp budget of a stage for the pool `S`. -/
def hemWelchBerlekampBudget (S : List QuarticGoldilocks)
    (st : HemWhirStageSpec QuarticGoldilocks) : HemFoldBudget :=
  ⟨Nat.max S.length (st.domainPts.length * (st.domainPts.length - 1) / 2), 1, 1⟩

set_option maxRecDepth 100000 in
theorem hemFoldDom64_nodup : hemFoldDom64.Nodup := by decide +kernel

set_option maxRecDepth 100000 in
theorem hemFoldWitnessGeom1 : HemFoldStageGeom hemFoldDom64 1 44 hemFoldWitnessStage1 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem hemFoldWitnessGeom2 :
    HemFoldStageGeom hemFoldDom32 1 28 hemFoldWitnessStage2 := by
  decide +kernel

theorem hemFoldWitnessChain :
    HemStageChainWellFormed hemFoldDom64 (0 + 1) (43 + 1) hemFoldWitnessStages :=
  (hemStageChainWellFormed_cons_iff _ _ _ _ _).mpr ⟨hemFoldWitnessGeom1,
    (hemStageChainWellFormed_cons_iff _ _ _ _ _).mpr ⟨hemFoldWitnessGeom2,
      hemStageChainWellFormed_nil _ _ _⟩⟩

set_option maxRecDepth 100000 in
/-- Certificate of the two-stage witness, with the challenge pool `S = hemFoldDom64`. Every
    field is discharged: the cascade by `hemWelchBerlekampCert`, both stages by
    `hemWelchBerlekampStageCert`. -/
theorem hemFoldWitnessCert :
    HemMultistageRbrCert hemFoldDom64 hemFoldDom64 0 43 2016 1 hemFoldWitnessStages
      (hemWelchBerlekampBudget hemFoldDom64) where
  cascade_cert := hemWelchBerlekampCert hemFoldDom64 hemFoldDom64 0 43
    hemFoldDom64_nodup hemFoldDom64_nodup (by decide) (by decide +kernel) (by decide +kernel)
  chain := hemFoldWitnessChain
  stage_certs := fun st hst => by
    rcases List.mem_cons.mp hst with hEq | h2
    · rw [hEq]
      exact hemWelchBerlekampStageCert hemFoldDom64 hemFoldWitnessStage1
        hemFoldWitnessGeom1.2.1 hemFoldDom64_nodup (by decide) (by decide +kernel)
        (by decide +kernel) (by decide +kernel)
    · rcases List.mem_cons.mp h2 with hEq | h3
      · rw [hEq]
        exact hemWelchBerlekampStageCert hemFoldDom64 hemFoldWitnessStage2
          hemFoldWitnessGeom2.2.1 hemFoldDom64_nodup (by decide) (by decide +kernel)
          (by decide +kernel) (by decide +kernel)
      · exact nomatch h3

/-- A false statement with two fold stages: the zero oracle with claim `1`. -/
def hemFoldFalseInst : HemWhirInstance QuarticGoldilocks :=
  { batchOracles := [fun _ => CommRingOps.zero]
    batchClaims := [CommRingOps.one]
    initDomainPts := hemFoldDom64
    initDegBound := 0
    initMinAgree := 43
    initKernel := [CommRingOps.one, CommRingOps.zero]
    stages := hemFoldWitnessStages }

theorem hemFoldFalseInst_invalid : ¬ HemStatementValid hemFoldFalseInst := by
  rw [HemStatementValid_iff]
  dsimp only [hemFoldFalseInst]
  rw [HemBatchValid_cons_cons_iff]
  rintro ⟨_, ⟨P, hP⟩, _⟩
  exact LawfulField.one_ne_zero
    (polyWitnessValid_zeroOracle_claim hemFoldDom64 0 43 [CommRingOps.one, CommRingOps.zero] P
      CommRingOps.one hemFoldDom64_nodup (by decide) hP)

theorem hemMultistageSpecs_one_lt_length (S : List QuarticGoldilocks) (hSpos : 0 < S.length)
    (domPts : List QuarticGoldilocks) (d₀ A₀ badMca listG : Nat)
    (stages : List (HemWhirStageSpec QuarticGoldilocks))
    (bud : HemWhirStageSpec QuarticGoldilocks → HemFoldBudget)
    (cert : HemMultistageRbrCert S domPts d₀ A₀ badMca listG stages bud) :
    1 < (hemMultistageSpecs S hSpos domPts d₀ A₀ badMca listG stages bud cert).length := by
  rw [hemMultistageSpecs_length]
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self 1) (Nat.le_add_left 2 _)

theorem hemFoldDom64_pos : 0 < hemFoldDom64.length := by decide

/-- An adaptive two-step attack on the witness IOP: a cascade message, then cross wires on the
    prefix just produced. -/
def hemFoldWitnessTree :
    SrScheduleTree
      (hemMultistageIop hemFoldDom64 hemFoldDom64_pos hemFoldDom64 0 43 2016 1
        hemFoldWitnessStages (hemWelchBerlekampBudget hemFoldDom64) hemFoldWitnessCert)
      [⟨0, Nat.lt_trans Nat.zero_lt_one
          (hemMultistageSpecs_one_lt_length hemFoldDom64 hemFoldDom64_pos hemFoldDom64 0 43 2016
            1 hemFoldWitnessStages (hemWelchBerlekampBudget hemFoldDom64) hemFoldWitnessCert)⟩,
       ⟨1, hemMultistageSpecs_one_lt_length hemFoldDom64 hemFoldDom64_pos hemFoldDom64 0 43 2016
            1 hemFoldWitnessStages (hemWelchBerlekampBudget hemFoldDom64) hemFoldWitnessCert⟩] :=
  .rewind (fun _ => []) (fun _ => .cascade [CommRingOps.zero])
    (fun _ => .rewind (fun hist => hist.headD [])
      (fun _ => .cross CommRingOps.zero CommRingOps.zero CommRingOps.zero)
      (fun _ => .done (fun hist => hist.headD [])))

/-- Inhabitedness witness for `hemMultistage_state_restoration_soundness` with two non-empty
    fold stages and a two-step attack schedule. -/
theorem inhabited_hemMultistage_state_restoration :
    ∃ (S : List QuarticGoldilocks) (hSpos : 0 < S.length)
      (domPts : List QuarticGoldilocks) (d₀ A₀ badMca listG : Nat)
      (stages : List (HemWhirStageSpec QuarticGoldilocks))
      (bud : HemWhirStageSpec QuarticGoldilocks → HemFoldBudget)
      (cert : HemMultistageRbrCert S domPts d₀ A₀ badMca listG stages bud)
      (inst : HemWhirInstance QuarticGoldilocks)
      (sched : List (Fin
        (hemMultistageSpecs S hSpos domPts d₀ A₀ badMca listG stages bud cert).length))
      (tree : SrScheduleTree
        (hemMultistageIop S hSpos domPts d₀ A₀ badMca listG stages bud cert) sched),
      ¬ HemStatementValid inst ∧ stages.length = 2 ∧ inst.stages = stages ∧ sched.length = 2 ∧
      RatBound.le
        (srTreeAcceptProb (hemMultistageIop S hSpos domPts d₀ A₀ badMca listG stages bud cert)
          tree inst)
        (srScheduleErrorSum
          (hemMultistageRbrOf S hSpos domPts d₀ A₀ badMca listG stages bud cert) sched) :=
  ⟨hemFoldDom64, hemFoldDom64_pos, hemFoldDom64, 0, 43, 2016, 1, hemFoldWitnessStages,
    hemWelchBerlekampBudget hemFoldDom64, hemFoldWitnessCert, hemFoldFalseInst, _,
    hemFoldWitnessTree, hemFoldFalseInst_invalid, rfl, rfl, rfl,
    hemMultistage_state_restoration_soundness hemFoldDom64 hemFoldDom64_pos hemFoldDom64 0 43
      2016 1 hemFoldWitnessStages (hemWelchBerlekampBudget hemFoldDom64) hemFoldWitnessCert
      hemFoldFalseInst hemFoldFalseInst_invalid _ hemFoldWitnessTree⟩

#verify_inhabited
  Qsag.hemMultistage_state_restoration_soundness
  Qsag.inhabited_hemMultistage_state_restoration

#verify_constructive
  Qsag.hemCrossRound_bad_phi_bound
  Qsag.hemShiftRound_bad_triples_bound
  Qsag.hemFoldStageGeom_antipodal
  Qsag.hemMultistageSpecs_budgets
  Qsag.hemMultistageSpecs_length
  Qsag.hemWelchBerlekampStageCert
  Qsag.hemCwyz26JohnsonStageCert
  Qsag.hemMultistageRbrCert_nil
  Qsag.hemMultistageVerify_of_fold_checked_stages
  Qsag.hemMultistage_state_restoration_soundness
  Qsag.hemFoldWitnessCert
  Qsag.inhabited_hemMultistage_state_restoration

end Qsag

namespace Qsag
#export_eqns hemMultistageRunWith hemFoldRunStagesWith hemFoldStateAccepted
  hemFoldGuard hemFoldCascadeStep hemFoldCrossStep hemFoldShiftStep
  hemTableMatchesOracle hemFoldCommitStep hemFoldFinalStep
end Qsag

namespace Qsag
open CommRingOps
def linearOracle {F : Type} [CommRingOps F] (D : List F) (a b : F) (i : Nat) : F :=
  add a (mul b (D.getD i zero))

theorem linearVirtualFold {F : Type} [LawfulField F] [DecidableEq F] (D E : List F)
    (hp : IsAntipodalDomainPair D E) (a b θ α β : F) (i : Nat) (hi : i < E.length) :
    hemVirtualFoldOracle θ α β D E (linearOracle D a b) i =
      linearOracle E (add b (mul α (add a (mul θ b)))) (mul β (add a (mul θ b))) i := by
  have hEven : 2 * i < D.length := by rw [hp.len_eq]; omega
  have hEvenGet : D.getD (2 * i) zero = D.getD (2 * i) one := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hEven, Option.getD_some]
  have hTwo := LawfulField.mul_inv_cancel hp.two_ne_zero
  have hn : mul (add (one : F) one) (D.getD (2 * i) one) ≠ zero := by
    intro h
    rcases LawfulField.mul_eq_zero h with h | h
    · exact hp.two_ne_zero h
    · exact hp.even_nz i hi h
  have hInv := LawfulField.mul_inv_cancel hn
  rw [hemVirtualFoldOracle_def]
  simp only [linearOracle, hp.odd_neg i hi, hEvenGet]
  generalize D.getD (2 * i) one = x at hTwo hInv ⊢
  generalize LawfulField.inv (add (one : F) one) = t at hTwo ⊢
  generalize LawfulField.inv (mul (add (one : F) one) x) = tx at hInv ⊢
  have hE : mul t (add (add a (mul b x)) (add a (mul b (neg x)))) = a := by
    calc
      _ = mul a (mul (add one one) t) := by constructive_ring
      _ = a := by rw [hTwo, LawfulCommRing.mul_one]
  have hO : mul tx (sub (add a (mul b x)) (add a (mul b (neg x)))) = b := by
    calc
      _ = mul b (mul (mul (add one one) x) tx) := by constructive_ring
      _ = b := by rw [hInv, LawfulCommRing.mul_one]
  rw [hE, hO]
  constructive_ring

theorem linearTable_toOracle {F : Type} [CommRingOps F] (D : List F) (a b : F) (i : Nat)
    (hi : i < D.length) :
    tableToOracle (D.map (fun x => add a (mul b x))) i = linearOracle D a b i := by
  simp only [tableToOracle_apply, linearOracle, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hi, Option.map_some, Option.getD_some]

theorem linearFoldTableCheck (D E : List QuarticGoldilocks)
    (hp : IsAntipodalDomainPair D E) (a b θ α β : QuarticGoldilocks) :
    hemTableMatchesOracle E.length
      (E.map (fun x => add (add b (mul α (add a (mul θ b))))
        (mul (mul β (add a (mul θ b))) x)))
      (hemVirtualFoldOracle θ α β D E (linearOracle D a b)) = true := by
  rw [hemTableMatchesOracle.public_eqs]
  apply List.all_eq_true.mpr
  intro i hi
  have hlt := List.mem_range.mp hi
  rw [linearTable_toOracle _ _ _ _ hlt, linearVirtualFold D E hp a b θ α β i hlt]
  exact decide_eq_true rfl

theorem linearVirtualFold_of (D E : List QuarticGoldilocks)
    (hp : IsAntipodalDomainPair D E) (O : Nat → QuarticGoldilocks) (a b θ α β : QuarticGoldilocks)
    (hO : ∀ i, i < D.length → O i = linearOracle D a b i) (i : Nat) (hi : i < E.length) :
    hemVirtualFoldOracle θ α β D E O i =
      linearOracle E (add b (mul α (add a (mul θ b)))) (mul β (add a (mul θ b))) i := by
  have hE : 2 * i < D.length := by rw [hp.len_eq]; omega
  have hO' : 2 * i + 1 < D.length := by rw [hp.len_eq]; omega
  have he : hemVirtualFoldOracle θ α β D E O i =
      hemVirtualFoldOracle θ α β D E (linearOracle D a b) i := by
    simp only [hemVirtualFoldOracle_def, hO (2 * i) hE, hO (2 * i + 1) hO']
  exact he.trans (linearVirtualFold D E hp a b θ α β i hi)

def linearNextA (a b θ α : QuarticGoldilocks) : QuarticGoldilocks :=
  add b (mul α (add a (mul θ b)))
def linearNextB (a b θ β : QuarticGoldilocks) : QuarticGoldilocks :=
  mul β (add a (mul θ b))
def linearTable (D : List QuarticGoldilocks) (a b : QuarticGoldilocks) :=
  D.map (fun x => add a (mul b x))

theorem linearStage_complete (S D : List QuarticGoldilocks) (st : HemWhirStageSpec QuarticGoldilocks)
    (hp : IsAntipodalDomainPair D st.domainPts) (hsd : st.degBound = 1)
    (A : Nat) (O : Nat → QuarticGoldilocks) (a b : QuarticGoldilocks)
    (hO : ∀ i, i < D.length → O i = linearOracle D a b i) (cp ct : Nat) :
    let t := (threePool S S).getD ct (zero, zero, zero)
    let na := linearNextA a b t.1 t.2.1
    let nb := linearNextB a b t.1 t.2.2
    hemFoldCommitStep
      (hemFoldShiftStep S D st
        (hemFoldCrossStep S D 1 A st (.cur D 1 A O [one, zero] a) (.cross a zero b) cp)
        (.shift zero zero) ct) (.commit (linearTable st.domainPts na nb)) =
      .cur st.domainPts 1 st.minAgree (tableToOracle (linearTable st.domainPts na nb)) [one, zero] na := by
  dsimp only
  rw [hemFoldCrossStep_cur _ _ _ _ _ _ _ _ _ _ _ _ (by rfl), hemFoldShiftStep_mid]
  simp only [hemKernelFold_pair, LawfulCommRing.mul_zero, LawfulCommRing.add_zero,
    LawfulCommRing.sub_self]
  have hcl : hemFoldClaimUpdate a b zero zero
      ((threePool S S).getD ct (zero, zero, zero)).1
      ((threePool S S).getD ct (zero, zero, zero)).2.1
      ((threePool S S).getD ct (zero, zero, zero)).2.2 =
      linearNextA a b ((threePool S S).getD ct (zero, zero, zero)).1
        ((threePool S S).getD ct (zero, zero, zero)).2.1 := by
    simp only [hemFoldClaimUpdate_def, linearNextA, LawfulCommRing.mul_zero,
      LawfulCommRing.add_zero]
  rw [hcl, hsd]
  apply hemFoldCommitStep_cur
  rw [hemTableMatchesOracle.public_eqs]
  apply List.all_eq_true.mpr
  intro i hi
  have hi' := List.mem_range.mp hi
  rw [show linearTable st.domainPts _ _ = st.domainPts.map (fun x => _) from rfl,
    linearTable_toOracle _ _ _ _ hi', linearVirtualFold_of D st.domainPts hp O a b _ _ _ hO i hi']
  exact decide_eq_true rfl

theorem linearTable_final_valid (D : List QuarticGoldilocks) (a b : QuarticGoldilocks)
    (A : Nat) (hA : A ≤ D.length) :
    polyWitnessValid D A 1 (tableToOracle (linearTable D a b)) [one, zero] a [a, b] = true := by
  have hEval (x : QuarticGoldilocks) : RoundPoly.evalCoeffs [a, b] x = add a (mul b x) := by
    simp only [RoundPoly.evalCoeffs_cons, RoundPoly.evalCoeffs_nil, LawfulCommRing.mul_zero,
      LawfulCommRing.add_zero]
    rw [LawfulCommRing.mul_comm x b]
  have hCount : hemCosetAgreeCount D (tableToOracle (linearTable D a b)) [a, b] = D.length := by
    rw [hemCosetAgreeCount_def]
    have he : (fun idx : Fin D.length =>
        if tableToOracle (linearTable D a b) idx.val = RoundPoly.evalCoeffs [a, b] (D.get idx)
          then 1 else 0) = fun _ => 1 := by
      funext idx
      simp only [linearTable, linearTable_toOracle _ _ _ _ idx.isLt, linearOracle, hEval,
        list_getD_eq_get D zero idx, ↓reduceIte]
    rw [he, qsum_const, Nat.mul_one]
  have hd : ringDot [a, b] [one, zero] = a := by
    simp only [ringDot_cons_cons, ringDot_nil_right, LawfulCommRing.mul_one,
      LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  rw [polyWitnessValid_def, hCount, hd, decide_eq_true hA]
  simp only [List.length_cons, List.length_nil, decide_eq_true (Nat.le_refl 2),
    decide_true, Bool.and_true]

#verify_constructive linearVirtualFold linearTable_toOracle linearFoldTableCheck
  linearVirtualFold_of linearStage_complete linearTable_final_valid

-- Equations for `Tests/HemMultistageCascadeTeeth` (no body exposed).
#export_eqns hemMultistageRun hemMultistageVerify linearOracle linearNextA linearNextB linearTable
  hemFoldWitnessStage1 hemFoldWitnessStage2 hemFoldWitnessStages hemFoldFalseInst hemFoldDom32
  hemFoldStageRoundBudgets hemWelchBerlekampBudget

end Qsag
