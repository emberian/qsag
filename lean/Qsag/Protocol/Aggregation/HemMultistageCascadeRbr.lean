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
