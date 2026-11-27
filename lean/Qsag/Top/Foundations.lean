module
public import Qsag.Tactic.CathedralKit
public import Qsag.Math.AlgebraicRepair
public import Qsag.Exec.SpecOracle
public import Qsag.Exec.Tactic.SimulationKit
/-
# Qsag.Top.Foundations — coding and oracle-model results at the deployed parameters

The Layer-1 modules `Coding.WelchBerlekampDecoder`, `Oracle.BlockCompressedOracle`,
`Oracle.PrefixMerkleExtraction`, `Oracle.TwoWayQipmCompression`, `Oracle.TwoWayQipmSwapAverage`
and `Oracle.ConstructiveQuantumHilbert` state their results for an arbitrary field, answer width
or amplitude ring. This module instantiates them at the parameters the deployment uses.

* `goldilocks_welch_berlekamp_eq_spec_decoder` relates unique-radius decoding to the specification.
* `block256_fourier_database_support`: for a `Qsag.QuantumAdv` with 256-bit oracle answers, the
  Fourier database component with more than `t` nonzero blocks vanishes after `t` queries.
* `block256_prefix_merkle_extraction_bound`: with 256-bit digests, the oracles under which an
  accepted Merkle opening differs from the one extracted from the Phase-1 query log number at
  most `(d + Q₂ + Q₁) (3 Q₁ + 1) / 2^256` of all oracles. This is a classical query bound.
* `two_way_transposition_average_o2h`: the averaged two-way transposition hybrid `8 q² n ‖ψ‖²`.
* `cliffordT_measure_reprogram_rbr_step`: the measure-and-reprogram round-by-round step for
  adversaries with amplitudes in `ℚ(√2, i)` (`CyclotomicEight`), the ring that holds the exact
  Hadamard and `T` gates.
-/

public import Qsag.Coding.WelchBerlekampDecoder
public import Qsag.Oracle.BlockCompressedOracle
public import Qsag.Oracle.PrefixMerkleExtraction
public import Qsag.Oracle.TwoWayQipmCompression
public import Qsag.Oracle.TwoWayQipmSwapAverage
public import Qsag.Oracle.ConstructiveQuantumHilbert
public import Qsag.Protocol.Threshold.MacBlind
public import Qsag.Protocol.Threshold.SacrificeFreezeSample
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Top.Foundations

set_option autoImplicit false
set_option exponentiation.threshold 2048

open Qsag.WelchBerlekamp in
/-- Inside the unique-decoding radius the Goldilocks Welch–Berlekamp decoder returns the list of
    the subset-enumeration specification decoder. -/
theorem goldilocks_welch_berlekamp_eq_spec_decoder (d e : Nat) (domain : List Goldilocks)
    (word : Goldilocks → Goldilocks) (hDom : domain.Nodup)
    (hRad : d + 1 + 2 * e ≤ domain.length) :
    gsDecodeList d (domain.length - e) domain word = wbDecodeList d e domain word :=
  wbDecode_eq_unique d e domain word hDom hRad

open Qsag.BlockCompressedOracle in
/-- **Fourier database support at the 256-bit answer width.** After `t` queries of a
    `QuantumAdv` to a 256-bit oracle, the component of the joint state on a Fourier database
    with more than `t` nonzero 256-bit blocks is zero. -/
theorem block256_fourier_database_support {n cardAnc Q : Nat} (A : QuantumAdv n 256 cardAnc Q)
    (t : Nat) (ht : t ≤ Q) (d : BlockTable 256 n) (hd : t < blockWeight 256 n d) :
    fourierBlockState (fun h => advStateAt A (blockOracle 256 n h) t ht) d =
      QVec.zero n 256 cardAnc :=
  quantumAdv_block256_fourier_coherent_support A t ht d hd

open Qsag.PrefixMerkleExtraction in
/-- **Prefix Merkle extraction with 256-bit digests.** For every two-phase classical adversary
    (`Q₁` queries before the challenge, `Q₂` after) and every fixed challenge, the number of
    oracles `Fin cardX → BitVec 256` under which the verifier accepts an opening of depth `d`
    other than the one extracted from the Phase-1 log is at most
    `(d + Q₂ + Q₁) (3 Q₁ + 1) / 2^256` of all `(2^256)^cardX` oracles. -/
theorem block256_prefix_merkle_extraction_bound {cardX Q₁ Q₂ : Nat} {St Chal : Type}
    (A : TwoPhaseAdversary cardX 256 Q₁ Q₂ St Chal) (L : MerkleAddressLayout cardX 256)
    (lvl d : Nat) (hLvl : lvl + d ≤ L.levels) (ch : Chal) :
    2 ^ 256 * uniformOracleSum 256 cardX
        (fun H => if prefixFailure A L lvl d H ch = true then 1 else 0) ≤
      ((d + Q₂ + Q₁) * (3 * Q₁ + 1)) * (2 ^ 256) ^ cardX :=
  prefix_extraction_failure_bound A L lvl d hLvl ch

/-- **Averaged two-way transposition hybrid.** For a `q`-query quantum adversary with
    superposition access to a permutation `π` of `n` points and its inverse `ρ`, the squared
    disturbance of composing `π` with the transposition `(a b)`, summed over all `n²` pairs, is
    at most `8 q² n` times the squared norm of the undisturbed final state. -/
theorem two_way_transposition_average_o2h {n w cardAnc q : Nat}
    (A : QuantumAdv (n + n) w cardAnc q) (π ρ : Fin n → Fin n)
    (hL : ∀ x, ρ (π x) = x) (hR : ∀ y, π (ρ y) = y) (enc : Fin n → BitVec w) :
    qsum n (fun a => qsum n (fun b =>
        QVec.stateNormSq
          ((runQuantumAdv A (qipmPermOracle (fun x => π (qipmFinSwap a b x))
            (fun y => qipmFinSwap a b (ρ y)) enc)).sub
            (runQuantumAdv A (qipmPermOracle π ρ enc))))) ≤
      8 * q ^ 2 * n * QVec.stateNormSq (runQuantumAdv A (qipmPermOracle π ρ enc)) :=
  qipm_two_way_swap_average_o2h A π ρ hL hR enc

open CommRingOps OrderedCommRing in
/-- **Measure-and-reprogram round-by-round step with exact Clifford+`T` amplitudes.** `Adv` is
    any adversary whose gates have entries in `ℚ(√2, i)`, making `Adv.steps.length`
    superposition queries through the response gate `G`. If every doomed point has at most
    `badCard` challenge indices that flip it to live, the Born mass of the outputs whose
    projected point is doomed and was reprogrammed to a flipping challenge, summed over points
    and challenge indices, is at most `(2 Q + 1)² · badCard · ‖ψ_final‖²` in the ordered ring
    `ℚ(√2)`. -/
theorem cliffordT_measure_reprogram_rbr_step {cardX cardY cardAnc : Nat} {Y : Type}
    (G : ResponseGate Y cardY)
    (Adv : QuantumAdvOver RatSqrt2 CyclotomicEight cardX cardY cardAnc) (H : Fin cardX → Y)
    (proj : Fin cardX → Fin cardX) {cardC : Nat} (chal : Fin cardC → Y)
    (isDoomed : Fin cardX → Bool) (flipsToLive : Fin cardX → Fin cardC → Bool) (badCard : Nat)
    (hRbr : ∀ x : Fin cardX, isDoomed x = true → finCountTrue cardC (flipsToLive x) ≤ badCard) :
    OrderedCommRing.le (ringSum (R := RatSqrt2) cardX (fun xStar =>
        if isDoomed xStar = true then
          ringSum (R := RatSqrt2) cardC (fun j =>
            if flipsToLive xStar j = true then
              queryMassOnOver (fun x => decide (xStar = proj x))
                (runQuantumAdvOver G Adv (pointUpdate H xStar (chal j)))
            else (zero : RatSqrt2))
        else zero))
      (CommRingOps.mul (natCastR ((2 * Adv.steps.length + 1) ^ 2 * badCard))
        (stateNormSqOver (runQuantumAdvOver G Adv H))) :=
  qrom_measure_reprogram_rbr_step_over G Adv H proj chal isDoomed flipsToLive badCard hRbr

#verify_constructive
  Qsag.Top.Foundations.goldilocks_welch_berlekamp_eq_spec_decoder
  Qsag.Top.Foundations.block256_fourier_database_support
  Qsag.Top.Foundations.block256_prefix_merkle_extraction_bound
  Qsag.Top.Foundations.two_way_transposition_average_o2h
  Qsag.Top.Foundations.cliffordT_measure_reprogram_rbr_step

/-- **Three-Projection Boolean MAC Blinding Bound (`L-Ex-14`)**:
    Over any field/ring projection modulus `q ≥ 2`, `(q² + q - 1)³ < q⁷`, i.e.,
    `(q⁻¹ + (1 - q⁻¹) q⁻²)³ < q⁻²`, and `Tower128` 2-round blinding has `2⁻²⁵⁶` soundness. -/
theorem threshold_three_projection_mac_blind_bound (q : Nat) (hq : 2 ≤ q) :
    (q ^ 2 + q - 1) ^ 3 < q ^ 7 :=
  Qsag.MacBlind.three_projection_mac_blind_bound q hq

end Qsag.Top.Foundations
