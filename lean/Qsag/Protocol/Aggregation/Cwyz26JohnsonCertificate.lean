module
public import Qsag.Protocol.Aggregation.HemWhirRbrSoundness
public import Qsag.Coding.Cwyz26
import all Qsag.Protocol.Aggregation.HemWhirRbrSoundness
public section
namespace Qsag
open CommRingOps RoundPoly UPoly Poly3
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
        S.length * ((Nat.min Dy ((Wx + Dy - 1) / (d₀ + 1))) * (Dy * (domPts.length *
          ((Nat.min Dy ((Wx + Dy - 1) / (d₀ + 1))) * (2 * (d₀ + 1) * Dy)) / (A₀ + 1 - B) + 1)))))
      listG :=
  hemCwyz26JohnsonCert S domPts d₀ A₀ m Wx Dy _ m_gs listG hDom hS hdA hAgDom hCount hWA
    (nonExcludedDecompBound_sliced domPts S (d₀ + 1) (A₀ + 1) B m Wx Dy hDom hS hCount
      (Nat.succ_le_succ (Nat.zero_le _)) hDy hB hDen hAB
      (fun k h1 h2 => QuarticGoldilocks.natCast_ne_zero k h1 (Nat.lt_of_le_of_lt h2 hDyP)))
    hGsDim


end Qsag
