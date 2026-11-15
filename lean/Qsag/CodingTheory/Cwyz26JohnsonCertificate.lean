module
/-
# Qsag.CodingTheory.Cwyz26JohnsonCertificate — the non-excluded decomposition bound, discharged

`HemWhirRbrSoundness.NonExcludedDecompBound` is the candidate-specific form of the residual
count of `[CWYZ26]` Lemma 4.1: it counts non-excluded challenges whose accepted polynomial
does not decompose through a correlated pair. `HemFoldDecompositionBridge` identifies that
with `¬ HasPolynomialExplanation` for the selected polynomial, which is the hypothesis of
`Poly3.nonExcluded_pairs_card_le`.

* `nonExcludedDecompBound_sliced`: `NonExcludedDecompBound D S d A m Wx Dy rest` over any
  constructive field in which `1, …, Dy` are invertible, with
  `rest = ℓ·max{|S|, n(n-1)/2} + |S|·Dy·Dy·(n·Dy·2dDy/(A-B) + 1)`.
* `hemCwyz26JohnsonCert_sliced`: the cascade certificate `HemCascadeRbrCert` at the deployed
  field `QuarticGoldilocks` beyond the Welch–Berlekamp regime, with no residual hypothesis.
  The characteristic condition is `Dy < p`.
* `inhabited_johnsonCert_sliced`: the hypotheses hold together at `|D| = 11`, `d₀ = 0`,
  `A₀ = 7`, where `affineFoldDecompBound_welch_berlekamp` does not apply.
-/

public import Qsag.HemFoldDecompositionBridge
public import Qsag.CodingTheory.Cwyz26AffineGap
public import Qsag.CodingTheory.GoldilocksCharacteristic
import all Qsag.HemFoldDecompositionBridge
import all Qsag.HemWhirRbrSoundness
import all Qsag.CodingTheory.Cwyz26AffineGap
import all Qsag.CodingTheory.SlicedJetIncidence
import all Qsag.CodingTheory.PersistentPairsBound
import all Qsag.CodingTheory.GoldilocksCharacteristic
import all Qsag.CodingTheory.PolyMv3
import all Qsag.CodingTheory.TrivariateGsExplainer
import all Qsag.CodingTheory.SimpleRootStratification
import all Qsag.CodingTheory.AffineIncidenceBound
import all Qsag.ConcreteSecurityBudget
import all Qsag.AffineProximityGaps
import all Qsag.Goldilocks

public section
namespace Qsag

set_option autoImplicit false

open CommRingOps RoundPoly UPoly Poly3

/-- **`NonExcludedDecompBound`, proved.** For `d + 1 ≤ B < A`, `|D|·(d + 1) < B²`, the
    interpolation count (4.5) and `1, …, Dy` invertible, at most
    `ℓ·max{|S|, n(n-1)/2} + |S|·Dy·Dy·(n·Dy·2dDy/(A-B) + 1)` non-excluded challenges carry an
    accepted root of the explainer that does not decompose through a correlated pair. -/
theorem nonExcludedDecompBound_sliced {F : Type} [LawfulField F] [DecidableEq F]
    (D S : List F) (d A B m Wx Dy : Nat) (hD : D.Nodup) (hS : S.Nodup)
    (hcount : D.length * triCount 1 m Dy m < triCount d Wx Dy (Dy + 1))
    (hd : 1 ≤ d) (hDy : 1 ≤ Dy) (hB : d + 1 ≤ B) (hDen : D.length * (d + 1) < B * B)
    (hAB : B < A) (hchar : ∀ k, 1 ≤ k → k ≤ Dy → (CRing.natCast k : F) ≠ zero) :
    NonExcludedDecompBound D S d A m Wx Dy
      (((D.length * (B - (d + 1))) / (B * B - D.length * (d + 1))) *
          Nat.max S.length (D.length * (D.length - 1) / 2) +
        S.length * (Dy * (Dy * (D.length * (Dy * (2 * d * Dy)) / (A - B) + 1)))) := by
  intro x L hNd hL
  obtain ⟨_, hQdeg, _, _⟩ := explainer_spec x.1 x.2 D m d Wx Dy hcount
  have hZ : (explainer x.1 x.2 D m d Wx Dy).degZ ≤ Dy :=
    Nat.le_trans (degZ_le_degYZ _) hQdeg
  have h := nonExcluded_pairs_card_le x D S hD hS d A B Dy hd hDy hAB hB hDen
    (explainer x.1 x.2 D m d Wx Dy) hQdeg (fun k h1 h2 => hchar k h1 (Nat.le_trans h2 hZ))
    L hNd (fun p hp => by
      obtain ⟨h1, h2, P, hPlen, hPa, hroot, hNoDec⟩ := hL p hp
      have hdeg : (ofList P).natDeg ≤ d := by
        have h3 := natDeg_ofList_le P
        omega
      exact ⟨h1, h2, ofList P, hdeg, hPa, hroot, fun hE =>
        hNoDec ((hasPolynomialExplanation_iff_decomposes x D d (A - 1) p.1 p.2 P).mp hE)⟩)
  exact Nat.le_trans h (Nat.add_le_add_left
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hZ)) _)

/-- **The cascade certificate beyond unique decoding, without a residual hypothesis.**
    At `QuarticGoldilocks`, for `d₀ + 2 ≤ B < A₀ + 1` with `|D|·(d₀ + 2) < B²`, the
    interpolation count (4.5), `Wx + Dy ≤ m·(A₀ + 1)`, `1 ≤ Dy < p` and the
    Guruswami–Sudan dimension count. -/
theorem hemCwyz26JohnsonCert_sliced (S domPts : List QuarticGoldilocks)
    (d₀ A₀ B m Wx Dy m_gs listG : Nat) (hDom : domPts.Nodup) (hS : S.Nodup)
    (hCount : domPts.length * triCount 1 m Dy m < triCount (d₀ + 1) Wx Dy (Dy + 1))
    (hWA : Wx + Dy ≤ m * (A₀ + 1))
    (hdA : d₀ + 2 ≤ A₀) (hAgDom : A₀ + 1 ≤ domPts.length)
    (hB : d₀ + 1 + 1 ≤ B) (hDen : domPts.length * (d₀ + 1 + 1) < B * B) (hAB : B < A₀ + 1)
    (hDy : 1 ≤ Dy) (hDyP : Dy < goldilocksPrime)
    (hGsDim : domPts.length * (m_gs * (m_gs + 1) / 2) < gsMonomialCount (m_gs * A₀) d₀ listG) :
    HemCascadeRbrCert S domPts d₀ A₀
      (Dy + (((domPts.length * (B - (d₀ + 1 + 1))) / (B * B - domPts.length * (d₀ + 1 + 1))) *
          Nat.max S.length (domPts.length * (domPts.length - 1) / 2) +
        S.length * (Dy * (Dy * (domPts.length * (Dy * (2 * (d₀ + 1) * Dy)) / (A₀ + 1 - B) + 1)))))
      listG :=
  hemCwyz26JohnsonCert S domPts d₀ A₀ m Wx Dy _ m_gs listG hDom hS hdA hAgDom hCount hWA
    (nonExcludedDecompBound_sliced domPts S (d₀ + 1) (A₀ + 1) B m Wx Dy hDom hS hCount
      (Nat.succ_le_succ (Nat.zero_le _)) hDy hB hDen hAB
      (fun k h1 h2 => QuarticGoldilocks.natCast_ne_zero k h1 (Nat.lt_of_le_of_lt h2 hDyP)))
    hGsDim

namespace JohnsonCertTests

def q (n : Nat) : QuarticGoldilocks :=
  ⟨⟨Goldilocks.ofNat n, Goldilocks.ofNat 0⟩, ⟨Goldilocks.ofNat 0, Goldilocks.ofNat 0⟩⟩

def dom11 : List QuarticGoldilocks :=
  [q 0, q 1, q 2, q 3, q 4, q 5, q 6, q 7, q 8, q 9, q 10]

/-- The hypotheses of `hemCwyz26JohnsonCert_sliced` hold together, with the decomposition
    parameters `(d, A) = (1, 8)` on `|D| = 11` outside the regime `2|D| + d + 1 < 3A`. -/
theorem inhabited_johnsonCert_sliced :
    ∃ (S domPts : List QuarticGoldilocks) (d₀ A₀ B m Wx Dy m_gs listG : Nat),
      domPts.Nodup ∧ S.Nodup ∧
      domPts.length * triCount 1 m Dy m < triCount (d₀ + 1) Wx Dy (Dy + 1) ∧
      Wx + Dy ≤ m * (A₀ + 1) ∧ d₀ + 1 + 1 ≤ B ∧ d₀ + 2 ≤ A₀ ∧ A₀ + 1 ≤ domPts.length ∧
      domPts.length * (d₀ + 1 + 1) < B * B ∧ B < A₀ + 1 ∧ 1 ≤ Dy ∧ Dy < goldilocksPrime ∧
      domPts.length * (m_gs * (m_gs + 1) / 2) < gsMonomialCount (m_gs * A₀) d₀ listG ∧
      ¬ 2 * domPts.length + (d₀ + 1) + 1 < 3 * (A₀ + 1) :=
  ⟨dom11, dom11, 0, 7, 5, 2, 12, 4, 1, 1, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

#verify_constructive nonExcludedDecompBound_sliced hemCwyz26JohnsonCert_sliced
#verify_constructive inhabited_johnsonCert_sliced
#verify_inhabited hemCwyz26JohnsonCert_sliced inhabited_johnsonCert_sliced

end JohnsonCertTests

end Qsag
end
