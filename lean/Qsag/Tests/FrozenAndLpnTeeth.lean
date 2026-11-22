module
/-
# Qsag.Tests.FrozenAndLpnTeeth — the four leaves used from outside

`#verify_constructive`, `#verify_inhabited` and `#tooth_pair` read proof bodies, and a module
does not export proof bodies, so those audits run at the end of each defining module. This
module checks the other side: that the exported statements are enough to work with. Every
proof below uses the imported theorems only as stated; nothing is unfolded. The
`#verify_constructive` lines at the end cover these local proofs only: imported proof bodies
are not visible from here.
-/
public import Qsag.Tactic.AssuranceKit
public import Qsag.Oracle.FrozenChallengeGame
public import Qsag.Protocol.Threshold.SacrificeFreezeSample
public import Qsag.Protocol.Threshold.MacBlind
public import Qsag.Protocol.Threshold.ThresholdMlDsaSecurity
public import Qsag.Protocol.Credentials.RepetitionCutAndChoose
public import Qsag.Math.TapRowParityBias

public section
namespace Qsag.FrozenAndLpnTeeth
open Qsag.FrozenChallenge Qsag.SacrificeFreeze Qsag.MacBlind Qsag.CutAndChoose Qsag.TapRowBias
set_option autoImplicit false

/-- The same wrong ML-DSA transcript in both orders at six challenges: frozen first it is
accepted on fewer than `q^6 / 2^137` challenge vectors, fitted afterwards on all `q^6`. -/
theorem mldsa_six_challenges_frozen_against_swapped :
    (∀ A : Adversary (List (Gate Fq204)) Fq204, Cheats (A.commit []) →
      countIf (frozenWins (sacConfig 6) A) (vectors fq204Elems 6) * 2 ^ 137 < mldsaQ ^ 6) ∧
    (∃ A : Adversary (List (Gate Fq204)) Fq204, (∀ chis, Cheats (A.commit chis)) ∧
      countIf (swappedWins (sacConfig 6) A) (vectors fq204Elems 6) = mldsaQ ^ 6) := by
  refine ⟨fun A hA => ?_, tooth_mldsa_swapped_order_cheat_always_accepted 6 (by decide)⟩
  have h := mldsa_sacrifice_frozen_soundness 6 (Nat.le_refl 6) A hA
  rw [h.2] at h
  exact h.1

/-- The empty challenge vector never produces a verdict, in any state of the sacrifice machine. -/
theorem sacrifice_empty_challenge_vector_rejected (reps : Nat)
    (s : State (List (Gate Fq204)) Fq204) :
    step (sacConfig reps) s (.sample []) = none :=
  step_empty_sample_rejected (sacConfig reps) s

/-- The 256-party theorems apply to an existing verifier, prover and challenge spaces. -/
theorem limbo256_bounds_are_instantiated :
    ∃ (K : Checker Unit Unit Unit Unit Unit Nat) (P : Prover Unit Unit Unit Unit Unit)
      (Gs Rs : List Unit) (Hs : List Nat),
      winCount K 33 P Gs Rs Hs * 2 ^ 263 < challengeCount 33 Gs Rs Hs ∧
      winCount K 17 P Gs Rs Hs * 2 ^ 135 < challengeCount 17 Gs Rs Hs := by
  obtain ⟨K, P, Gs, Rs, Hs, dG, hS, hH, hRs, hG, hGpos⟩ := inhabited_limbo256_soundness
  exact ⟨K, P, Gs, Rs, Hs, limbo256_tau33_soundness K P Gs Rs Hs dG hS hH hRs hG hGpos,
    limbo256_tau17_soundness K P Gs Rs Hs dG hS hH hRs hG hGpos⟩

/-- The balance premise fails on row 0, derived from the uniform theorem and the row's bias
instead of by inspecting the 64 weights. -/
theorem prodRow0_cannot_satisfy_balance_premise :
    ¬ (∀ w ∈ prodRow0Weights, imbalance 32768 w ≤ 2047) := fun hBal =>
  prodRow0_bias_not_lt_two_neg_256
    (balanced_blocks_special_case prodRow0Weights prodRow0Weights_length hBal)

/-- Row 0 of the deployed generator: the test bit's signed count over the `2^960` noise tuples
is above `2^842` and below `2^843`. -/
theorem prodRow0_signed_count_bracket :
    (noiseSignedSum 32768 (rowTestFns prodRow0Taps) false).natAbs * 2 ^ 117 < 32768 ^ 64 ∧
    32768 ^ 64 < (noiseSignedSum 32768 (rowTestFns prodRow0Taps) false).natAbs * 2 ^ 118 := by
  rw [prodRow0_bias_exact.2.1]
  exact prodRow0_bias_bracket

/-- Multiplicative SPDZ MAC-residual blinding (`L-Ex-14`): two-round `Tower128` blinding accepts a
nonzero defect on `1` out of `2^256` randomizer pairs and leaks `0` statistical bits on `α` across
non-guessed keys, whereas an unblinded residual distinguishes `α₁ ≠ α₂` in `1` query. -/
theorem macBlind_spdz_zero_leakage_against_unblinded_recovery :
    (∀ (rC₀ rC₁ d err₀ err₁ : Tower128), d ≠ CommRingOps.zero →
      qsum (2 ^ 256) (fun i =>
        let p := tower128PairEnum.toFun i
        if macBlindTwoRoundOpen p.1 p.2 rC₀ rC₁ d err₀ err₁ = CommRingOps.zero then 1 else 0) = 1) ∧
    (∀ (deltaX deltaM rCorrupt alpha₁ alpha₂ : Tower128),
      deltaX ≠ CommRingOps.zero →
      alpha₁ ≠ CommRingOps.mul deltaM (LawfulField.inv deltaX) →
      alpha₂ ≠ CommRingOps.mul deltaM (LawfulField.inv deltaX) →
      ∀ obs : Bool × Tower128 → Nat,
        qsum (2 ^ 128) (fun i =>
          let w := macBlindPure (tower128Enum.toFun i) rCorrupt (spdzMacDefect deltaX alpha₁ deltaM)
          obs (decide (w ≠ CommRingOps.zero), w)) =
        qsum (2 ^ 128) (fun i =>
          let w := macBlindPure (tower128Enum.toFun i) rCorrupt (spdzMacDefect deltaX alpha₂ deltaM)
          obs (decide (w ≠ CommRingOps.zero), w))) ∧
    (∀ (deltaX alpha₁ alpha₂ deltaM : Tower128),
      deltaX ≠ CommRingOps.zero → alpha₁ ≠ alpha₂ →
      ∃ invDx : Tower128,
        CommRingOps.mul (CommRingOps.add (spdzMacDefect deltaX alpha₁ deltaM) deltaM) invDx = alpha₁ ∧
        spdzMacDefect deltaX alpha₁ deltaM ≠ spdzMacDefect deltaX alpha₂ deltaM) :=
  ⟨fun rC₀ rC₁ d err₀ err₁ hd =>
     (macBlind_tower128_two_round_256bit_sound rC₀ rC₁ d err₀ err₁ hd).1,
   fun deltaX deltaM rCorrupt alpha₁ alpha₂ hDx hA1 hA2 obs =>
     macBlind_spdz_alpha_zero_leakage tower128Enum deltaX deltaM rCorrupt alpha₁ alpha₂ hDx hA1 hA2 obs,
   fun deltaX alpha₁ alpha₂ deltaM hDx hNe =>
     tooth_unblinded_mac_residual_recovers_alpha deltaX alpha₁ alpha₂ deltaM hDx hNe⟩

/-- Boolean triple 3-projection MAC blinding bound and adaptive `combineArity` (`L-Ex-14`):
3 projections beat `q^-2` for every `q ≥ 2`, `POOL_WORDS = 8192` (`524,288` bits) selects `f = 3`,
every `outBits ≥ 64` achieves `2^-40` within `2 ≤ f ≤ 7`, whereas hardcoding `f = 3` fails at `7,720` words. -/
theorem macBlind_boolean_projections_and_adaptive_arity_against_fixed3 :
    (((2 ^ 128) ^ 2 + 2 ^ 128 - 1) ^ 3 < (2 ^ 128) ^ 7 ∧ (2 ^ 128) ^ 2 = 2 ^ 256) ∧
    combineArity tripleF2PoolBits = 3 ∧
    (∀ outBits : Nat, 64 ≤ outBits → combineArityMeetsBound outBits (combineArity outBits) = true) ∧
    (∃ outBits : Nat, 64 ≤ outBits ∧ combineArityMeetsBound outBits 3 = false ∧ combineArity outBits ≠ 3) :=
  ⟨three_projection_mac_blind_bound_gf128,
   combineArity_pool_certificates.2.2.1,
   fun outBits hGe => (combineArity_valid_for_all_ge_64 outBits hGe).2.2,
   tooth_fixed_arity3_fails_at_7720_words⟩

/-- Dealerless FTS `(s, s², s³)` and 7-power Frobenius consistency (`L-Ex-15`):
frozen cheating tuples over `Tower8` (`GF(2^8)`) pass on `≤ 256` of `256^2` challenge pairs (and
over `Tower128` 7-power tuples on `≤ 3 * |xs|` of `|xs|^2`), whereas swapped order wins on all
`256^2` pairs and a degree-0 combiner `[1, s, s²]` lets a frozen invalid tuple pass every challenge. -/
theorem fts_frobenius_frozen_against_swapped_and_deg0 :
    (∀ A : Adversary (FtsPowerTriple Tower8) Tower8, FtsTripleCheats (A.commit []) →
      countIf (frozenWins ftsTripleConfig A) (vectors tower8Elems 2) ≤ 256 ∧
      (vectors tower8Elems 2).length = 256 ^ 2) ∧
    (∃ A : Adversary (FtsPowerTriple Tower8) Tower8,
      (∀ chis, FtsTripleCheats (A.commit chis)) ∧
      countIf (swappedWins ftsTripleConfig A) (vectors tower8Elems 2) = 256 ^ 2) ∧
    (∃ T : FtsPower7Tuple Tower128,
      ¬ FtsPower7ValidPowers T ∧
      (∀ s : Tower128, ftsBrokenDeg0ProdResidual T s = CommRingOps.zero) ∧
      (∀ theta : Tower128, ftsPower7Check T 1 theta = true)) := by
  refine ⟨ftsPowerTriple_tower8_frozen_soundness, ?_,
    tooth_ftsPower7_degree0_weight_cancels_error (towerElem_char2 7)⟩
  obtain ⟨A, hCheat, hWin⟩ :=
    tooth_ftsPowerTriple_swapped_order_always_accepted (towerElem_char2 3) tower8Elems
  exact ⟨A, hCheat, hWin.trans (by rw [tower8Elems_length])⟩

/-- Threshold ML-DSA `rssSacrificedSignStep` (`L-Ex-15`): frozen forged products pass on `≤ 1` of
`mldsaQ^6` challenges (`< 2^-137`) and `≤ 1` on any duplicate-free `Ext6Fq204` pool, whereas
sampling `chi` before freezing `(inp, T)` passes on all `chisExt.length` challenges. -/
theorem rss_sign_step_frozen_against_swapped
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (chisExt : List Ext6Fq204) (hNd : chisExt.Nodup) :
    (∀ A : Adversary (RssMlDsaAttemptInput × RssSacrificeTranscript204) Fq204,
      (A.commit []).1.products ≠
        rssComputeProducts chalHash sampleInBall st (A.commit []).1.mu (A.commit []).1.ySubsets →
      countIf
        (fun chis => rssSignStepAcceptsSacrifice chalHash sampleInBall st
          (A.commit []).1 (ext6OfList chis) (A.commit []).2)
        (vectors fq204Elems 6) * 2 ^ 137 < mldsaQ ^ 6) ∧
    (∀ A : Adversary (RssMlDsaAttemptInput × RssSacrificeTranscript204) Ext6Fq204,
      (A.commit []).1.products ≠
        rssComputeProducts chalHash sampleInBall st (A.commit []).1.mu (A.commit []).1.ySubsets →
      countIf (frozenWins (rssSignFreezeExt6Config chalHash sampleInBall st) A)
        (vectors chisExt 1) ≤ 1) ∧
    (∃ A : Adversary (RssMlDsaAttemptInput × RssSacrificeTranscript204) Ext6Fq204,
      (∀ chis, (A.commit chis).1.products ≠
        rssComputeProducts chalHash sampleInBall st (A.commit chis).1.mu (A.commit chis).1.ySubsets) ∧
      countIf (swappedWins (rssSignFreezeExt6Config chalHash sampleInBall st) A)
        (vectors chisExt 1) = chisExt.length) :=
  ⟨fun A hF => (rssSacrificedSignStep_mldsaQ6_frozen_soundness chalHash sampleInBall st A hF).2.1,
   fun A hF => (rssSacrificedSignStep_frozen_ext6_soundness chalHash sampleInBall st A chisExt hNd hF).1,
   tooth_rssSacrificedSignStep_swapped_order_forges chalHash sampleInBall st chisExt⟩

/-- Row 0 of the 11-tap balanced generator (`DENSE_PCG_TAPS_PER_TREE = 11`, `imbalance ≤ 7593`)
has bias strictly between `2^-220` and `2^-219` (`< 2^-135`), whereas an unfiltered degenerate
11-tap row fails `< 2^-135`. -/
theorem elevenTap_balanced_against_unfiltered :
    (∀ row : List (List Nat),
      row.length = 64 →
      (∀ ts ∈ row, ts.length = 11 ∧ (∀ a ∈ ts, a < 32768) ∧ imbalance 32768 (oddTapWeight ts) ≤ 7593) →
      (noiseSignedSum 32768 (row.map tapFn) false).natAbs * 2 ^ 135 < 32768 ^ 64) ∧
    (∃ row : List (List Nat),
      row.length = 64 ∧
      (∀ ts ∈ row, ts.length = 11 ∧ ∀ a ∈ ts, a < 32768) ∧
      ¬ ((noiseSignedSum 32768 (row.map tapFn) false).natAbs * 2 ^ 135 < 32768 ^ 64)) :=
  ⟨fun row hL hOk => (elevenTap_balanced_all_rows_bias_lt_two_neg_135 row hL hOk).1,
   tooth_elevenTap_unfiltered_tail_exceeds_two_neg_135⟩

#verify_constructive mldsa_six_challenges_frozen_against_swapped
#verify_constructive sacrifice_empty_challenge_vector_rejected
#verify_constructive limbo256_bounds_are_instantiated
#verify_constructive prodRow0_cannot_satisfy_balance_premise
#verify_constructive prodRow0_signed_count_bracket
#verify_constructive elevenTap_balanced_against_unfiltered
#verify_constructive macBlind_spdz_zero_leakage_against_unblinded_recovery
#verify_constructive macBlind_boolean_projections_and_adaptive_arity_against_fixed3
#verify_constructive fts_frobenius_frozen_against_swapped_and_deg0
#verify_constructive rss_sign_step_frozen_against_swapped

end Qsag.FrozenAndLpnTeeth
