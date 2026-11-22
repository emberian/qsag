module
/-
# Qsag.Protocol.Threshold.ComputationalMacBlind — PRG-Expanded SPDZ MAC-Residual Blinding

`Qsag.Protocol.Threshold.MacBlind` treats the honest randomizer of the blinded MAC-residual
opening `w = (r_honest + r_corrupt) · d`, `d = Δx · α − Δm`, as a uniform field element. In
production the randomizer is read from `PartyPrivateRng`, a stream expanded from a 32-byte seed.
This module replaces the uniform randomizer by `decodeMask (prg seed [])` and bounds, over
`Spec.GameBound`, the distance between the real blinded check and a simulator that never reads
the MAC key `α`:

1. **Coin space and engine** (sections 1, 2): games on `(seed × mask) × (α × adversary coin)`
   (`coordGame`), the fibrewise identical-until-bad bound `coordGame_advDist_le_inv_card`, and
   the reduction `coordGame_prf_hop` of one PRG call to the `Spec.PrfHard` experiment at input
   length `0` with one query.
2. **Blinded check** (section 3): `macCheckRealGame` (PRG-expanded randomizer),
   `macCheckIdealGame` (uniform randomizer), `macCheckSimGame` (opens `0` for an unshifted
   check and a uniform field element otherwise), and the bound `εPrf + 1 / |F|` between the
   first and the last, `computational_macBlind_spdz_security_bound`. The opening is
   `macBlindPure`; on fibres with nonzero defect its uniformity is
   `macBlind_uniform_of_nonzero_defect`, and the remaining fibres carry the single key
   `α = Δm · Δx⁻¹`.
3. **Teeth** (section 4): a seed-independent PRG gives an adversary advantage `1 − 1 / |F|`
   and is refuted as a `Spec.PrfHard` PRF through the bound.
4. **`Tower128`** (section 5): little-endian byte samplers and the bound `εPrf + 2⁻¹²⁸` for
   32-byte seeds and 16-byte masks.
5. **Pooled triples** (section 6): reconstruction algebra of `blind_open_pooled` and
   `blind_open_ext2_pooled` from per-party shares of a single-use triple `(r, a, c)`, and the
   opened value under a faulty correlation `c = r · (a + δ) + err`.
6. **General views** (section 7): the same bound for the direct opening with a post-OLE
   additive error, and for one pooled round, whose view is the pair `(e, w)` and whose honest
   mask and randomizer shares both come from the seeded stream.

Scope. Each game is one opening under a fresh MAC key; the two-round loop of
`blind_open_pooled` and repeated checks under one key are not composed here. The OLE that
produces `c` is an ideal multiplication with adversarial additive error; its realisation from
correlated OT is outside this module. `Spec.PrfSampleOk` has no exported defining equation,
so the uniformity of the PRF challenger sampler `prgPrfSampler` enters the bounds as the
premise `hU`; `uniformOn_prgPrfSampler` derives it from the defining equation of
`Spec.PrfSampleOk`.
-/

public import Qsag.Protocol.Threshold.MacBlind
public import Qsag.Spec.Assumptions
import Qsag.Tactic.AssuranceKit

public section

namespace Qsag.MacBlind

open Qsag.FrozenChallenge CommRingOps
open Qsag.Spec (Bytes Code byteOracleIface FinGame GameBound AdvDist CoinSplit UniformOn)

set_option autoImplicit false

/-! ## 1. Counting over the product coin space -/

private theorem iteOfPos {α : Type} {p : Prop} [Decidable p] (hp : p) (a b : α) :
    (if p then a else b) = a := by
  cases ‹Decidable p› with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn hp)

private theorem iteOfNeg {α : Type} {p : Prop} [Decidable p] (hnp : ¬ p) (a b : α) :
    (if p then a else b) = b := by
  cases ‹Decidable p› with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

theorem qsum_eq_sampleSum : ∀ (n : Nat) (f : Fin n → Nat), qsum n f = Spec.sampleSum n f
  | 0, _ => rfl
  | n + 1, f => by
    show f ⟨0, Nat.zero_lt_succ n⟩ + qsum n _ = f ⟨0, Nat.zero_lt_succ n⟩ + Spec.sampleSum n _
    rw [qsum_eq_sampleSum n]

/-- A sum over a split coin space is the iterated sum over its two coordinates. -/
theorem qsum_coinSplit {n nC nA : Nat} (π : CoinSplit n nC nA) (w : Fin n → Nat) :
    qsum n w = qsum nC (fun c => qsum nA (fun a => w (π.pair c a))) :=
  (qsum_eq_sampleSum n w).trans <|
    (π.sampleSum_eq w).trans <|
      (qsum_eq_sampleSum nC _).symm.trans <|
        qsum_congr (fun _ => (qsum_eq_sampleSum nA _).symm)

/-- Game on the coin space `(Fin cardK × Fin cardY) × (Fin cardF × Fin nA)` whose verdict is the
    function `W` of the four coordinates: challenger seed coin, challenger mask coin, MAC-key
    coin and adversary coin. The first pair is the challenger coordinate of the
    `Spec.PrfHard` experiment and the second pair its adversary coordinate. -/
@[expose] def coordGame {cardK cardY cardF nA : Nat} (hPos : 0 < (cardK * cardY) * (cardF * nA))
    (W : Fin cardK → Fin cardY → Fin cardF → Fin nA → Bool) :
    FinGame ((cardK * cardY) * (cardF * nA)) :=
  ⟨hPos, fun ω =>
    W ((CoinSplit.prod cardK cardY).chal ((CoinSplit.prod (cardK * cardY) (cardF * nA)).chal ω))
      ((CoinSplit.prod cardK cardY).advc ((CoinSplit.prod (cardK * cardY) (cardF * nA)).chal ω))
      ((CoinSplit.prod cardF nA).chal ((CoinSplit.prod (cardK * cardY) (cardF * nA)).advc ω))
      ((CoinSplit.prod cardF nA).advc ((CoinSplit.prod (cardK * cardY) (cardF * nA)).advc ω))⟩

theorem coordGame_win_pair {cardK cardY cardF nA : Nat}
    (hPos : 0 < (cardK * cardY) * (cardF * nA))
    (W : Fin cardK → Fin cardY → Fin cardF → Fin nA → Bool)
    (ck : Fin cardK) (cy : Fin cardY) (ca : Fin cardF) (a : Fin nA) :
    (coordGame hPos W).win
      ((CoinSplit.prod (cardK * cardY) (cardF * nA)).pair
        ((CoinSplit.prod cardK cardY).pair ck cy) ((CoinSplit.prod cardF nA).pair ca a)) =
      W ck cy ca a := by
  show W _ _ _ _ = W ck cy ca a
  simp only [CoinSplit.chal_pair, CoinSplit.advc_pair]

/-- Number of mask coins on which `W` accepts, for fixed seed, MAC-key and adversary coins. -/
def fibreWinCount {cardK cardY cardF nA : Nat}
    (W : Fin cardK → Fin cardY → Fin cardF → Fin nA → Bool)
    (ck : Fin cardK) (ca : Fin cardF) (a : Fin nA) : Nat :=
  qsum cardY (fun cy => if W ck cy ca a then 1 else 0)

theorem fibreWinCount_eq {cardK cardY cardF nA : Nat}
    (W : Fin cardK → Fin cardY → Fin cardF → Fin nA → Bool)
    (ck : Fin cardK) (ca : Fin cardF) (a : Fin nA) :
    fibreWinCount W ck ca a = qsum cardY (fun cy => if W ck cy ca a then 1 else 0) := by rfl

/-- The win count of a coordinate game, fibred over the seed, MAC-key and adversary coins. -/
theorem coordGame_winCount {cardK cardY cardF nA : Nat}
    (hPos : 0 < (cardK * cardY) * (cardF * nA))
    (W : Fin cardK → Fin cardY → Fin cardF → Fin nA → Bool) :
    (coordGame hPos W).winCount =
      qsum cardK (fun ck => qsum cardF (fun ca => qsum nA (fun a => fibreWinCount W ck ca a))) := by
  have h0 : (coordGame hPos W).winCount =
      qsum ((cardK * cardY) * (cardF * nA))
        (fun ω => if (coordGame hPos W).win ω then 1 else 0) :=
    (qsum_eq_sampleSum _ _).symm
  rw [h0, qsum_coinSplit (CoinSplit.prod (cardK * cardY) (cardF * nA)),
    qsum_coinSplit (CoinSplit.prod cardK cardY)]
  apply qsum_congr
  intro ck
  have h1 : ∀ cy : Fin cardY,
      qsum (cardF * nA) (fun b => if (coordGame hPos W).win
        ((CoinSplit.prod (cardK * cardY) (cardF * nA)).pair
          ((CoinSplit.prod cardK cardY).pair ck cy) b) then 1 else 0) =
      qsum cardF (fun ca => qsum nA (fun a => if W ck cy ca a then 1 else 0)) := by
    intro cy
    rw [qsum_coinSplit (CoinSplit.prod cardF nA)]
    exact qsum_congr (fun ca => qsum_congr (fun a => by rw [coordGame_win_pair]))
  refine (qsum_congr h1).trans ?_
  refine (qsum_comm cardY cardF (fun cy ca => qsum nA (fun a => if W ck cy ca a then 1 else 0))).trans ?_
  exact qsum_congr (fun ca => qsum_comm cardY nA (fun cy a => if W ck cy ca a then 1 else 0))

private theorem qsum_indicator_le_card {n : Nat} (p : Fin n → Bool) :
    qsum n (fun i => if p i then 1 else 0) ≤ n := by
  have h : qsum n (fun i => if p i then 1 else 0) ≤ qsum n (fun _ => 1) :=
    qsum_le_qsum (fun i => by cases p i <;> decide)
  rw [qsum_const, Nat.mul_one] at h
  exact h

private theorem natAbsDiff_le_of_le_add {a b c : Nat} (h₁ : a ≤ b + c) (h₂ : b ≤ a + c) :
    Spec.natAbsDiff a b ≤ c := by
  unfold Spec.natAbsDiff
  split <;> omega

private theorem coordGame_winCount_le_add {cardK cardY cardF nA : Nat}
    (hPos : 0 < (cardK * cardY) * (cardF * nA))
    (W₀ W₁ : Fin cardK → Fin cardY → Fin cardF → Fin nA → Bool)
    (bad : Fin cardF → Fin nA → Bool)
    (hGood : ∀ ck ca a, bad ca a = false → fibreWinCount W₀ ck ca a ≤ fibreWinCount W₁ ck ca a)
    (hBad : ∀ a : Fin nA, qsum cardF (fun ca => if bad ca a then 1 else 0) ≤ 1) :
    (coordGame hPos W₀).winCount ≤ (coordGame hPos W₁).winCount + cardK * (nA * cardY) := by
  rw [coordGame_winCount, coordGame_winCount]
  have hPt : ∀ (ck : Fin cardK) (ca : Fin cardF) (a : Fin nA),
      fibreWinCount W₀ ck ca a ≤
        fibreWinCount W₁ ck ca a + cardY * (if bad ca a then 1 else 0) := by
    intro ck ca a
    cases hb : bad ca a
    · exact Nat.le_trans (hGood ck ca a hb) (Nat.le_add_right _ _)
    · have h : fibreWinCount W₀ ck ca a ≤ cardY := qsum_indicator_le_card _
      show fibreWinCount W₀ ck ca a ≤ fibreWinCount W₁ ck ca a + cardY * 1
      omega
  have hBadSum : qsum cardF (fun ca => qsum nA (fun a => cardY * (if bad ca a then 1 else 0))) ≤
      nA * cardY := by
    rw [qsum_comm cardF nA (fun ca a => cardY * (if bad ca a then 1 else 0))]
    have h4 : ∀ a : Fin nA,
        qsum cardF (fun ca => cardY * (if bad ca a then 1 else 0)) ≤ cardY := by
      intro a
      rw [qsum_mul_left]
      exact Nat.le_trans (Nat.mul_le_mul_left cardY (hBad a)) (Nat.le_of_eq (Nat.mul_one cardY))
    have h5 : qsum nA (fun a => qsum cardF (fun ca => cardY * (if bad ca a then 1 else 0))) ≤
        qsum nA (fun _ => cardY) := qsum_le_qsum h4
    rw [qsum_const] at h5
    exact h5
  have hCk : ∀ ck : Fin cardK,
      qsum cardF (fun ca => qsum nA (fun a => fibreWinCount W₀ ck ca a)) ≤
        qsum cardF (fun ca => qsum nA (fun a => fibreWinCount W₁ ck ca a)) + nA * cardY := by
    intro ck
    have hLe : qsum cardF (fun ca => qsum nA (fun a => fibreWinCount W₀ ck ca a)) ≤
        qsum cardF (fun ca => qsum nA (fun a =>
          fibreWinCount W₁ ck ca a + cardY * (if bad ca a then 1 else 0))) :=
      qsum_le_qsum (fun ca => qsum_le_qsum (fun a => hPt ck ca a))
    have hSplit : qsum cardF (fun ca => qsum nA (fun a =>
          fibreWinCount W₁ ck ca a + cardY * (if bad ca a then 1 else 0))) =
        qsum cardF (fun ca => qsum nA (fun a => fibreWinCount W₁ ck ca a)) +
          qsum cardF (fun ca => qsum nA (fun a => cardY * (if bad ca a then 1 else 0))) :=
      (qsum_congr (fun ca => qsum_add (fun a => fibreWinCount W₁ ck ca a)
        (fun a => cardY * (if bad ca a then 1 else 0)))).trans
        (qsum_add (fun ca => qsum nA (fun a => fibreWinCount W₁ ck ca a))
          (fun ca => qsum nA (fun a => cardY * (if bad ca a then 1 else 0))))
    rw [hSplit] at hLe
    exact Nat.le_trans hLe (Nat.add_le_add_left hBadSum _)
  have hTot : qsum cardK (fun ck => qsum cardF (fun ca => qsum nA (fun a => fibreWinCount W₀ ck ca a))) ≤
      qsum cardK (fun ck =>
        qsum cardF (fun ca => qsum nA (fun a => fibreWinCount W₁ ck ca a)) + nA * cardY) :=
    qsum_le_qsum hCk
  rw [qsum_add (fun ck => qsum cardF (fun ca => qsum nA (fun a => fibreWinCount W₁ ck ca a)))
    (fun _ => nA * cardY), qsum_const] at hTot
  exact hTot

/-- **Fibrewise identical-until-bad bound.** If two coordinate games accept on the same number
    of mask coins for every seed, MAC-key and adversary coin outside `bad`, and every adversary
    coin has at most one bad MAC-key coin, their distinguishing advantage is at most `1 / cardF`. -/
theorem coordGame_advDist_le_inv_card {cardK cardY cardF nA : Nat}
    (hPos : 0 < (cardK * cardY) * (cardF * nA)) (hF : 0 < cardF)
    (W₀ W₁ : Fin cardK → Fin cardY → Fin cardF → Fin nA → Bool)
    (bad : Fin cardF → Fin nA → Bool)
    (hGood : ∀ ck ca a, bad ca a = false → fibreWinCount W₀ ck ca a = fibreWinCount W₁ ck ca a)
    (hBad : ∀ a : Fin nA, qsum cardF (fun ca => if bad ca a then 1 else 0) ≤ 1) :
    GameBound (AdvDist (coordGame hPos W₀) (coordGame hPos W₁)) ⟨1, cardF, hF⟩ := by
  have h01 := coordGame_winCount_le_add hPos W₀ W₁ bad
    (fun ck ca a hb => Nat.le_of_eq (hGood ck ca a hb)) hBad
  have h10 := coordGame_winCount_le_add hPos W₁ W₀ bad
    (fun ck ca a hb => Nat.le_of_eq (hGood ck ca a hb).symm) hBad
  have hAbs : Spec.natAbsDiff (coordGame hPos W₀).winCount (coordGame hPos W₁).winCount ≤
      cardK * (nA * cardY) := natAbsDiff_le_of_le_add h01 h10
  show Spec.natAbsDiff (coordGame hPos W₀).winCount (coordGame hPos W₁).winCount * cardF ≤
    1 * ((cardK * cardY) * (cardF * nA))
  have hEq : cardK * (nA * cardY) * cardF = 1 * ((cardK * cardY) * (cardF * nA)) := by
    rw [Nat.one_mul, Nat.mul_assoc cardK (nA * cardY) cardF, Nat.mul_comm nA cardY,
      Nat.mul_assoc cardY nA cardF, Nat.mul_comm nA cardF, Nat.mul_assoc cardK cardY (cardF * nA)]
  rw [← hEq]
  exact Nat.mul_le_mul_right cardF hAbs

/-! ## 2. The PRF reduction for one PRG call -/

/-- One-query distinguisher: query the empty input and apply `test` to the answer. -/
def prgOutputTest (test : Bytes → Bool) : Code byteOracleIface Bool :=
  .call ([] : Bytes) (fun (y : Bytes) => .ret (test y))

theorem prgOutputTest_within (test : Bytes → Bool) : Spec.Within 1 (prgOutputTest test) :=
  Spec.Within.call (b := 0) _ _ (fun _ => Spec.Within.ret 0 _)

theorem prgOutputTest_play (test : Bytes → Bool) (f : Bytes → Bytes) :
    (Code.play (Spec.budgetedFunOracle f 1) (prgOutputTest test) 0).1 = test (f []) := by
  have hEq : Spec.budgetedFunOracle f 1 0 ([] : Bytes) = (f [], 0 + 1) := by
    rw [Spec.budgetedFunOracle.public_eqs]
    exact iteOfPos Nat.one_pos _ _
  unfold prgOutputTest
  rw [Code.play_call, hEq, Code.play_ret]

/-- Challenger sampler of the PRF experiment at input length `0`: a seed and the function that
    answers the empty input with a mask and every other input with `[]`. -/
@[expose] def prgPrfSampler {cardK cardY : Nat} (keySampler : Fin cardK → Bytes)
    (maskSampler : Fin cardY → Bytes) (c : Fin (cardK * cardY)) : Bytes × (Bytes → Bytes) :=
  (keySampler ((CoinSplit.prod cardK cardY).chal c),
   fun inp => if inp = [] then maskSampler ((CoinSplit.prod cardK cardY).advc c) else [])

theorem prgPrfSampler_fst {cardK cardY : Nat} (keySampler : Fin cardK → Bytes)
    (maskSampler : Fin cardY → Bytes) (c : Fin (cardK * cardY)) :
    (prgPrfSampler keySampler maskSampler c).1 =
      keySampler ((CoinSplit.prod cardK cardY).chal c) := rfl

theorem prgPrfSampler_snd_nil {cardK cardY : Nat} (keySampler : Fin cardK → Bytes)
    (maskSampler : Fin cardY → Bytes) (c : Fin (cardK * cardY)) :
    (prgPrfSampler keySampler maskSampler c).2 [] =
      maskSampler ((CoinSplit.prod cardK cardY).advc c) := by
  show (if ([] : Bytes) = [] then maskSampler ((CoinSplit.prod cardK cardY).advc c)
    else ([] : Bytes)) = _
  exact iteOfPos rfl _ _

/-- `prgPrfSampler` is uniform on the sample set of the PRF challenger, at input length `0` given uniform seed and mask samplers. -/
theorem uniformOn_prgPrfSampler {cardK cardY keyLen outLen : Nat}
    {keySampler : Fin cardK → Bytes} {maskSampler : Fin cardY → Bytes}
    (hKey : UniformOn (fun s : Bytes => s.length = keyLen) keySampler)
    (hMask : UniformOn (fun s : Bytes => s.length = outLen) maskSampler) :
    UniformOn (Spec.PrfSampleOk keyLen 0 outLen) (prgPrfSampler keySampler maskSampler) where
  mem c := (Spec.prfSampleOk_iff keyLen 0 outLen _).mpr ⟨hKey.mem _, fun inp =>
    ⟨fun hLen => by
      have hNil : inp = [] := List.eq_nil_of_length_eq_zero hLen
      show (if inp = [] then maskSampler ((CoinSplit.prod cardK cardY).advc c)
        else ([] : Bytes)).length = outLen
      rw [iteOfPos hNil]
      exact hMask.mem _,
    fun hNe => by
      have hNe' : ¬ inp = [] := fun h => hNe (by rw [h]; rfl)
      show (if inp = [] then maskSampler ((CoinSplit.prod cardK cardY).advc c)
        else ([] : Bytes)) = []
      rw [iteOfNeg hNe']⟩⟩
  injective c c' h := by
    have hk : keySampler ((CoinSplit.prod cardK cardY).chal c) =
        keySampler ((CoinSplit.prod cardK cardY).chal c') := congrArg Prod.fst h
    have hy : maskSampler ((CoinSplit.prod cardK cardY).advc c) =
        maskSampler ((CoinSplit.prod cardK cardY).advc c') := by
      have hf := congrFun (congrArg Prod.snd h) ([] : Bytes)
      rw [prgPrfSampler_snd_nil, prgPrfSampler_snd_nil] at hf
      exact hf
    have h1 := hKey.injective _ _ hk
    have h2 := hMask.injective _ _ hy
    calc c = (CoinSplit.prod cardK cardY).pair ((CoinSplit.prod cardK cardY).chal c)
            ((CoinSplit.prod cardK cardY).advc c) := ((CoinSplit.prod cardK cardY).pair_eta c).symm
      _ = (CoinSplit.prod cardK cardY).pair ((CoinSplit.prod cardK cardY).chal c')
            ((CoinSplit.prod cardK cardY).advc c') := by rw [h1, h2]
      _ = c' := (CoinSplit.prod cardK cardY).pair_eta c'
  surjective x hx := by
    obtain ⟨hLen, hFun⟩ := (Spec.prfSampleOk_iff keyLen 0 outLen x).mp hx
    obtain ⟨ck, hck⟩ := hKey.surjective x.1 hLen
    obtain ⟨cy, hcy⟩ := hMask.surjective (x.2 []) ((hFun []).1 rfl)
    refine ⟨(CoinSplit.prod cardK cardY).pair ck cy, ?_⟩
    show (keySampler ((CoinSplit.prod cardK cardY).chal ((CoinSplit.prod cardK cardY).pair ck cy)),
      fun inp => if inp = [] then
        maskSampler ((CoinSplit.prod cardK cardY).advc ((CoinSplit.prod cardK cardY).pair ck cy))
        else ([] : Bytes)) = x
    rw [CoinSplit.chal_pair, CoinSplit.advc_pair, hck, hcy]
    refine Prod.ext rfl (funext fun inp => ?_)
    by_cases hNil : inp = []
    · subst hNil
      show (if ([] : Bytes) = [] then x.2 [] else ([] : Bytes)) = x.2 []
      exact iteOfPos rfl _ _
    · show (if inp = [] then x.2 [] else ([] : Bytes)) = x.2 inp
      rw [iteOfNeg hNil]
      exact ((hFun inp).2 (fun h0 => hNil (List.eq_nil_of_length_eq_zero h0))).symm

/-- **PRF hop for one PRG call.** Two coordinate games that apply the same test to the PRG
    output `prg seed []` and to a uniform mask are the real and the ideal `Spec.PrfHard`
    experiments of the one-query distinguishers `prgOutputTest (test ca a)`, whose own coin is
    the MAC-key coin and the adversary coin. -/
theorem coordGame_prf_hop {cardK cardY cardF nA : Nat}
    (hPos : 0 < (cardK * cardY) * (cardF * nA))
    (prg : Bytes → Bytes → Bytes) (keyLen outLen : Nat)
    (keySampler : Fin cardK → Bytes) (maskSampler : Fin cardY → Bytes)
    (hU : UniformOn (Spec.PrfSampleOk keyLen 0 outLen) (prgPrfSampler keySampler maskSampler))
    {𝒜 : Code byteOracleIface Bool → Prop} {εPrf : Spec.RatBound}
    (hPrf : Spec.PrfHard 𝒜 prg keyLen 0 outLen 1 εPrf)
    (test : Fin cardF → Fin nA → Bytes → Bool)
    (h𝒜 : ∀ (ca : Fin cardF) (a : Fin nA), 𝒜 (prgOutputTest (test ca a))) :
    GameBound
      (AdvDist
        (coordGame hPos (fun ck (_ : Fin cardY) ca a => test ca a (prg (keySampler ck) [])))
        (coordGame hPos (fun (_ : Fin cardK) cy ca a => test ca a (maskSampler cy)))) εPrf := by
  have hBound := hPrf ((cardK * cardY) * (cardF * nA)) (cardK * cardY) (cardF * nA) hPos
    (CoinSplit.prod (cardK * cardY) (cardF * nA)) (prgPrfSampler keySampler maskSampler) hU
    (fun b => prgOutputTest
      (test ((CoinSplit.prod cardF nA).chal b) ((CoinSplit.prod cardF nA).advc b)))
    (fun b => h𝒜 _ _)
  have hReal :
      coordGame hPos (fun ck (_ : Fin cardY) ca a => test ca a (prg (keySampler ck) [])) =
      Spec.prfRealGame hPos prg 1
        (fun ω => (prgPrfSampler keySampler maskSampler
          ((CoinSplit.prod (cardK * cardY) (cardF * nA)).chal ω)).1)
        (fun ω => prgOutputTest
          (test ((CoinSplit.prod cardF nA).chal ((CoinSplit.prod (cardK * cardY) (cardF * nA)).advc ω))
            ((CoinSplit.prod cardF nA).advc ((CoinSplit.prod (cardK * cardY) (cardF * nA)).advc ω)))) := by
    rw [Spec.prfRealGame.public_eqs]
    apply Spec.FinGame.ext_win
    intro ω
    show _ = (Code.play (Spec.budgetedFunOracle (prg (prgPrfSampler keySampler maskSampler _).1) 1)
      (prgOutputTest _) 0).1
    rw [prgOutputTest_play, prgPrfSampler_fst]
    rfl
  have hIdeal :
      coordGame hPos (fun (_ : Fin cardK) cy ca a => test ca a (maskSampler cy)) =
      Spec.prfIdealGame hPos 1
        (fun ω => (prgPrfSampler keySampler maskSampler
          ((CoinSplit.prod (cardK * cardY) (cardF * nA)).chal ω)).2)
        (fun ω => prgOutputTest
          (test ((CoinSplit.prod cardF nA).chal ((CoinSplit.prod (cardK * cardY) (cardF * nA)).advc ω))
            ((CoinSplit.prod cardF nA).advc ((CoinSplit.prod (cardK * cardY) (cardF * nA)).advc ω)))) := by
    rw [Spec.prfIdealGame.public_eqs]
    apply Spec.FinGame.ext_win
    intro ω
    show _ = (Code.play (Spec.budgetedFunOracle (prgPrfSampler keySampler maskSampler _).2 1)
      (prgOutputTest _) 0).1
    rw [prgOutputTest_play, prgPrfSampler_snd_nil]
    rfl
  rw [hReal, hIdeal]
  exact hBound

/-! ## 3. The blinded MAC check with a PRG-expanded honest randomizer -/

/-- MAC-check adversary corrupting every party but one. From its coin it fixes the additive
    shifts `Δx`, `Δm` of the opened value and of its MAC, and the randomizer shares of the
    corrupt parties (one list entry per corrupt party, any number of them); these are committed
    before the opening. It then sees the opened `w` and outputs a guess. -/
structure MacCheckAdv (F : Type) where
  deltaX : F
  deltaM : F
  corruptRandomizers : List F
  guess : F → Bool

/-- Sum of the corrupt parties' randomizer shares. -/
@[expose] def corruptSum {F : Type} [LawfulCommRing F] : List F → F
  | [] => zero
  | r :: rs => add r (corruptSum rs)

/-- The opened value of the blinded MAC check: `macBlindPure` at the honest randomizer, the sum
    of the corrupt randomizers, and the MAC defect `Δx · α − Δm` (the expression that
    `spdzMacDefect` names). -/
@[expose] def blindedCheckOpening {F : Type} [LawfulCommRing F] (A : MacCheckAdv F)
    (alpha rHonest : F) : F :=
  macBlindPure rHonest (corruptSum A.corruptRandomizers) (sub (mul A.deltaX alpha) A.deltaM)

/-- The simulated opened value. It is a function of the adversary's shifts and of one uniform
    field element `u`; the MAC key is not an argument. -/
@[expose] def simulatedOpening {F : Type} [LawfulCommRing F] [DecidableEq F] (A : MacCheckAdv F)
    (u : F) : F :=
  if A.deltaX = zero ∧ A.deltaM = zero then zero else u

/-- **Real game.** Uniform seed, uniform MAC key `α`, adversary coin `a`. The honest randomizer
    is `decodeMask (prg seed [])`; the adversary wins when it outputs `true` on the opened value. -/
@[expose] def macCheckRealGame {F : Type} [LawfulCommRing F] {cardK cardF nA : Nat}
    (hPos : 0 < (cardK * cardF) * (cardF * nA)) (enum : SimpleEquiv (Fin cardF) F)
    (prg : Bytes → Bytes → Bytes) (keySampler : Fin cardK → Bytes) (decodeMask : Bytes → F)
    (adv : Fin nA → MacCheckAdv F) : FinGame ((cardK * cardF) * (cardF * nA)) :=
  coordGame hPos (fun ck (_ : Fin cardF) ca a =>
    (adv a).guess (blindedCheckOpening (adv a) (enum.toFun ca)
      (decodeMask (prg (keySampler ck) []))))

/-- **Ideal game.** As the real game, with a uniform honest randomizer. -/
@[expose] def macCheckIdealGame {F : Type} [LawfulCommRing F] {cardK cardF nA : Nat}
    (hPos : 0 < (cardK * cardF) * (cardF * nA)) (enum : SimpleEquiv (Fin cardF) F)
    (adv : Fin nA → MacCheckAdv F) : FinGame ((cardK * cardF) * (cardF * nA)) :=
  coordGame hPos (fun (_ : Fin cardK) cy ca a =>
    (adv a).guess (blindedCheckOpening (adv a) (enum.toFun ca) (enum.toFun cy)))

/-- **Simulated game.** The adversary sees `simulatedOpening`; the MAC-key coin is not read. -/
@[expose] def macCheckSimGame {F : Type} [LawfulCommRing F] [DecidableEq F] {cardK cardF nA : Nat}
    (hPos : 0 < (cardK * cardF) * (cardF * nA)) (enum : SimpleEquiv (Fin cardF) F)
    (adv : Fin nA → MacCheckAdv F) : FinGame ((cardK * cardF) * (cardF * nA)) :=
  coordGame hPos (fun (_ : Fin cardK) cy (_ : Fin cardF) a =>
    (adv a).guess (simulatedOpening (adv a) (enum.toFun cy)))

/-- **Reduction distinguisher.** With the MAC key `alpha` and the MAC-check adversary `A` fixed
    by its own coin, it queries the oracle once on the empty input, decodes the answer as the
    honest randomizer, computes the opened value and returns the adversary's guess. -/
@[expose] def macBlindPrfDistinguisher {F : Type} [LawfulCommRing F] (decodeMask : Bytes → F)
    (alpha : F) (A : MacCheckAdv F) : Code byteOracleIface Bool :=
  .call ([] : Bytes) (fun (y : Bytes) =>
    .ret (A.guess (blindedCheckOpening A alpha (decodeMask y))))

theorem macBlindPrfDistinguisher_within {F : Type} [LawfulCommRing F] (decodeMask : Bytes → F)
    (alpha : F) (A : MacCheckAdv F) :
    Spec.Within 1 (macBlindPrfDistinguisher decodeMask alpha A) :=
  Spec.Within.call (b := 0) _ _ (fun _ => Spec.Within.ret 0 _)

theorem blindedCheckOpening_unshifted {F : Type} [LawfulCommRing F] (A : MacCheckAdv F)
    (hX : A.deltaX = zero) (hM : A.deltaM = zero) (alpha rHonest : F) :
    blindedCheckOpening A alpha rHonest = zero := by
  unfold blindedCheckOpening
  rw [hX, hM, LawfulCommRing.zero_mul, LawfulCommRing.sub_zero]
  exact macBlindPure_zero_defect_complete _ _

private theorem field_mul_left_cancel {F : Type} [LawfulField F] {a b c : F} (ha : a ≠ zero)
    (h : mul a b = mul a c) : b = c := by
  have h1 := congrArg (mul (LawfulField.inv a)) h
  rw [← LawfulCommRing.mul_assoc, ← LawfulCommRing.mul_assoc, LawfulField.inv_mul_cancel ha,
    LawfulCommRing.one_mul, LawfulCommRing.one_mul] at h1
  exact h1

/-- For shifts that are not both zero, at most one MAC key makes the defect `Δx · α − Δm` vanish. -/
theorem zero_defect_key_unique {F : Type} [LawfulField F] {cardF : Nat}
    (enum : SimpleEquiv (Fin cardF) F) (deltaX deltaM : F)
    (hShift : ¬ (deltaX = zero ∧ deltaM = zero)) (i j : Fin cardF)
    (hi : sub (mul deltaX (enum.toFun i)) deltaM = zero)
    (hj : sub (mul deltaX (enum.toFun j)) deltaM = zero) : i = j := by
  have hmi : mul deltaX (enum.toFun i) = deltaM := LawfulCommRing.sub_eq_zero_iff.mp hi
  have hmj : mul deltaX (enum.toFun j) = deltaM := LawfulCommRing.sub_eq_zero_iff.mp hj
  have hX : deltaX ≠ zero := by
    intro hX0
    apply hShift
    refine ⟨hX0, ?_⟩
    calc deltaM = mul deltaX (enum.toFun i) := hmi.symm
      _ = mul zero (enum.toFun i) := by rw [hX0]
      _ = zero := LawfulCommRing.zero_mul _
  have hEq : enum.toFun i = enum.toFun j := field_mul_left_cancel hX (hmi.trans hmj.symm)
  calc i = enum.invFun (enum.toFun i) := (enum.left_inv i).symm
    _ = enum.invFun (enum.toFun j) := by rw [hEq]
    _ = j := enum.left_inv j

/-- **PRF hop.** The real and ideal blinded checks differ by at most the PRF advantage of the
    reduction distinguishers. -/
theorem macCheck_real_ideal_prf_bound {F : Type} [LawfulCommRing F] {cardK cardF nA : Nat}
    (hPos : 0 < (cardK * cardF) * (cardF * nA)) (enum : SimpleEquiv (Fin cardF) F)
    (prg : Bytes → Bytes → Bytes) (keyLen outLen : Nat)
    (keySampler : Fin cardK → Bytes) (maskSampler : Fin cardF → Bytes) (decodeMask : Bytes → F)
    (hDecode : ∀ i : Fin cardF, decodeMask (maskSampler i) = enum.toFun i)
    (hU : UniformOn (Spec.PrfSampleOk keyLen 0 outLen) (prgPrfSampler keySampler maskSampler))
    {𝒜 : Code byteOracleIface Bool → Prop} {εPrf : Spec.RatBound}
    (hPrf : Spec.PrfHard 𝒜 prg keyLen 0 outLen 1 εPrf)
    (adv : Fin nA → MacCheckAdv F)
    (h𝒜 : ∀ (alpha : F) (a : Fin nA), 𝒜 (macBlindPrfDistinguisher decodeMask alpha (adv a))) :
    GameBound
      (AdvDist (macCheckRealGame hPos enum prg keySampler decodeMask adv)
        (macCheckIdealGame hPos enum adv)) εPrf := by
  have h := coordGame_prf_hop hPos prg keyLen outLen keySampler maskSampler hU hPrf
    (fun ca a y => (adv a).guess (blindedCheckOpening (adv a) (enum.toFun ca) (decodeMask y)))
    (fun ca a => h𝒜 (enum.toFun ca) a)
  have hFun :
      (fun (_ : Fin cardK) (cy : Fin cardF) (ca : Fin cardF) (a : Fin nA) =>
        (adv a).guess (blindedCheckOpening (adv a) (enum.toFun ca) (decodeMask (maskSampler cy)))) =
      (fun (_ : Fin cardK) (cy : Fin cardF) (ca : Fin cardF) (a : Fin nA) =>
        (adv a).guess (blindedCheckOpening (adv a) (enum.toFun ca) (enum.toFun cy))) := by
    funext _ cy ca a
    rw [hDecode]
  have hIdeal : coordGame hPos (fun (_ : Fin cardK) (cy : Fin cardF) (ca : Fin cardF) (a : Fin nA) =>
        (adv a).guess (blindedCheckOpening (adv a) (enum.toFun ca) (decodeMask (maskSampler cy)))) =
      macCheckIdealGame hPos enum adv := congrArg (coordGame hPos) hFun
  rw [← hIdeal]
  exact h

/-- **Statistical hop.** The ideal blinded check and the simulator differ by at most `1 / |F|`. -/
theorem macCheck_ideal_sim_bound {F : Type} [LawfulField F] [DecidableEq F] {cardK cardF nA : Nat}
    (hPos : 0 < (cardK * cardF) * (cardF * nA)) (hF : 0 < cardF)
    (enum : SimpleEquiv (Fin cardF) F) (adv : Fin nA → MacCheckAdv F) :
    GameBound
      (AdvDist (macCheckIdealGame (cardK := cardK) hPos enum adv) (macCheckSimGame hPos enum adv))
      ⟨1, cardF, hF⟩ := by
  unfold macCheckIdealGame macCheckSimGame
  refine coordGame_advDist_le_inv_card hPos hF _ _
    (fun ca a => decide (¬ ((adv a).deltaX = zero ∧ (adv a).deltaM = zero) ∧
      sub (mul (adv a).deltaX (enum.toFun ca)) (adv a).deltaM = zero)) ?_ ?_
  · intro ck ca a hb
    have hNot : ¬ (¬ ((adv a).deltaX = zero ∧ (adv a).deltaM = zero) ∧
        sub (mul (adv a).deltaX (enum.toFun ca)) (adv a).deltaM = zero) := of_decide_eq_false hb
    show qsum cardF (fun cy => if (adv a).guess
        (blindedCheckOpening (adv a) (enum.toFun ca) (enum.toFun cy)) then 1 else 0) =
      qsum cardF (fun cy => if (adv a).guess
        (simulatedOpening (adv a) (enum.toFun cy)) then 1 else 0)
    by_cases hHon : (adv a).deltaX = zero ∧ (adv a).deltaM = zero
    · apply qsum_congr
      intro cy
      have hI : blindedCheckOpening (adv a) (enum.toFun ca) (enum.toFun cy) = zero :=
        blindedCheckOpening_unshifted (adv a) hHon.1 hHon.2 _ _
      have hS : simulatedOpening (adv a) (enum.toFun cy) = zero := iteOfPos hHon _ _
      rw [hI, hS]
    · have hd : sub (mul (adv a).deltaX (enum.toFun ca)) (adv a).deltaM ≠ zero :=
        fun h0 => hNot ⟨hHon, h0⟩
      have hUnif := (macBlind_uniform_of_nonzero_defect enum
        (corruptSum (adv a).corruptRandomizers) _ zero hd).1
        (fun w => if (adv a).guess w then 1 else 0)
      refine Eq.trans (qsum_congr (fun cy => ?_)) (hUnif.trans (qsum_congr (fun cy => ?_)))
      · show (if (adv a).guess (macBlindPure (enum.toFun cy)
            (corruptSum (adv a).corruptRandomizers)
            (sub (mul (adv a).deltaX (enum.toFun ca)) (adv a).deltaM)) then 1 else 0) = _
        rw [macBlindPure_eq_open_zero]
      · have hS : simulatedOpening (adv a) (enum.toFun cy) = enum.toFun cy := iteOfNeg hHon _ _
        rw [hS]
  · intro a
    apply qsum_indicator_le_one_of_unique
    intro i j hi hj
    have hi' := of_decide_eq_true hi
    have hj' := of_decide_eq_true hj
    exact zero_defect_key_unique enum (adv a).deltaX (adv a).deltaM hi'.1 i j hi'.2 hj'.2

/-- **Computational blinded MAC check.** For every family of MAC-check adversaries `adv` whose
    reduction distinguishers lie in the class `𝒜`, and every PRG that is a `Spec.PrfHard`
    one-query PRF at input length `0` against `𝒜` with advantage `εPrf`, the real blinded check
    with honest randomizer `decodeMask (prg seed [])` is within `εPrf + 1 / |F|` of the
    simulator `simulatedOpening`, which does not read the MAC key. -/
theorem computational_macBlind_spdz_security_bound {F : Type} [LawfulField F] [DecidableEq F]
    {cardK cardF nA : Nat}
    (hPos : 0 < (cardK * cardF) * (cardF * nA)) (hF : 0 < cardF)
    (enum : SimpleEquiv (Fin cardF) F)
    (prg : Bytes → Bytes → Bytes) (keyLen outLen : Nat)
    (keySampler : Fin cardK → Bytes) (maskSampler : Fin cardF → Bytes) (decodeMask : Bytes → F)
    (hDecode : ∀ i : Fin cardF, decodeMask (maskSampler i) = enum.toFun i)
    (hU : UniformOn (Spec.PrfSampleOk keyLen 0 outLen) (prgPrfSampler keySampler maskSampler))
    {𝒜 : Code byteOracleIface Bool → Prop} {εPrf : Spec.RatBound}
    (hPrf : Spec.PrfHard 𝒜 prg keyLen 0 outLen 1 εPrf)
    (adv : Fin nA → MacCheckAdv F)
    (h𝒜 : ∀ (alpha : F) (a : Fin nA), 𝒜 (macBlindPrfDistinguisher decodeMask alpha (adv a))) :
    GameBound
      (AdvDist (macCheckRealGame hPos enum prg keySampler decodeMask adv)
        (macCheckSimGame hPos enum adv))
      (εPrf.add ⟨1, cardF, hF⟩) :=
  Spec.GameBound.trans
    (Spec.adv_triangle (macCheckRealGame hPos enum prg keySampler decodeMask adv)
      (macCheckIdealGame hPos enum adv) (macCheckSimGame hPos enum adv))
    (Spec.RatBound.add_le_add
      (macCheck_real_ideal_prf_bound hPos enum prg keyLen outLen keySampler maskSampler decodeMask
        hDecode hU hPrf adv h𝒜)
      (macCheck_ideal_sim_bound hPos hF enum adv))

/-! ## 4. Teeth: a predictable randomizer breaks the bound -/

/-- Adversary that knows the honest randomizer `r₀`: it shifts only the MAC (`Δx = 0`,
    `Δm = 1`, so the defect is `-1` for every key), lets one corrupt party contribute `-r₀`,
    and outputs whether the opened value is `0`. -/
def cancellingAdv {F : Type} [LawfulCommRing F] [DecidableEq F] (r₀ : F) : MacCheckAdv F where
  deltaX := zero
  deltaM := one
  corruptRandomizers := [neg r₀]
  guess := fun w => decide (w = zero)

theorem cancellingAdv_opening_zero {F : Type} [LawfulField F] [DecidableEq F] (r₀ alpha : F) :
    blindedCheckOpening (cancellingAdv r₀) alpha r₀ = zero := by
  have hd : sub (mul (zero : F) alpha) one ≠ zero := by
    intro h
    have h1 : mul (zero : F) alpha = one := LawfulCommRing.sub_eq_zero_iff.mp h
    rw [LawfulCommRing.zero_mul] at h1
    exact LawfulField.zero_ne_one h1
  show macBlindPure r₀ (add (neg r₀) zero) (sub (mul zero alpha) one) = zero
  rw [LawfulCommRing.add_zero]
  exact (macBlindPure_eq_zero_iff r₀ (neg r₀) _ hd).mpr (LawfulCommRing.neg_neg r₀).symm

/-- Against a PRG that ignores its seed, `cancellingAdv` wins the real game on every coin. -/
theorem tooth_constant_prg_real_always_wins {F : Type} [LawfulField F] [DecidableEq F]
    {cardK cardF nA : Nat} (hPos : 0 < (cardK * cardF) * (cardF * nA))
    (enum : SimpleEquiv (Fin cardF) F) (keySampler : Fin cardK → Bytes) (decodeMask : Bytes → F)
    (y₀ : Bytes) (ω : Fin ((cardK * cardF) * (cardF * nA))) :
    (macCheckRealGame hPos enum (fun _ _ => y₀) keySampler decodeMask
      (fun _ : Fin nA => cancellingAdv (decodeMask y₀))).win ω = true := by
  show decide (blindedCheckOpening (cancellingAdv (decodeMask y₀)) _ (decodeMask y₀) = zero) = true
  exact decide_eq_true (cancellingAdv_opening_zero _ _)

/-- Against the simulator, `cancellingAdv` wins on exactly one mask coin per fibre. -/
theorem cancellingAdv_sim_winCount {F : Type} [LawfulField F] [DecidableEq F]
    {cardK cardF nA : Nat} (hPos : 0 < (cardK * cardF) * (cardF * nA))
    (enum : SimpleEquiv (Fin cardF) F) (r₀ : F) :
    (macCheckSimGame hPos enum (fun _ : Fin nA => cancellingAdv r₀)).winCount =
      cardK * (cardF * (nA * 1)) := by
  unfold macCheckSimGame
  rw [coordGame_winCount]
  have hFibre : ∀ (ck : Fin cardK) (ca : Fin cardF) (a : Fin nA),
      fibreWinCount (fun (_ : Fin cardK) (cy : Fin cardF) (_ : Fin cardF) (_ : Fin nA) =>
        (cancellingAdv r₀).guess (simulatedOpening (cancellingAdv r₀) (enum.toFun cy))) ck ca a =
        1 := by
    intro ck ca a
    refine Eq.trans (qsum_congr (fun cy => ?_)) (qsum_enum_eq_target enum zero)
    have hS : simulatedOpening (cancellingAdv r₀) (enum.toFun cy) = enum.toFun cy :=
      iteOfNeg (fun h => LawfulField.zero_ne_one h.2.symm) _ _
    show (if decide (simulatedOpening (cancellingAdv r₀) (enum.toFun cy) = zero) = true
      then 1 else 0) = (if enum.toFun cy = zero then 1 else 0)
    rw [hS]
    by_cases h0 : enum.toFun cy = zero
    · rw [iteOfPos h0, iteOfPos (decide_eq_true h0)]
    · rw [iteOfNeg h0, iteOfNeg (fun h => h0 (of_decide_eq_true h))]
  refine Eq.trans (qsum_congr (fun ck => qsum_congr (fun ca => qsum_congr (fun a =>
    hFibre ck ca a)))) ?_
  rw [qsum_const, qsum_const, qsum_const]

private theorem tooth_arith {N m c en ed : Nat} (hN : N = m * c) (hNpos : 0 < N)
    (hε : en * c + 2 * ed < ed * c)
    (hB : Spec.natAbsDiff N m * (ed * c) ≤ (en * c + 1 * ed) * N) : False := by
  have hc : 0 < c := Nat.pos_of_ne_zero (fun h0 => by
    rw [hN, h0, Nat.mul_zero] at hNpos
    exact Nat.lt_irrefl 0 hNpos)
  have hmN : m ≤ N := by
    rw [hN]
    exact Nat.le_mul_of_pos_right m hc
  have hAbs : N - m ≤ Spec.natAbsDiff N m := by
    unfold Spec.natAbsDiff
    split <;> omega
  have h1 : (N - m) * (ed * c) ≤ (en * c + 1 * ed) * N :=
    Nat.le_trans (Nat.mul_le_mul_right _ hAbs) hB
  have h2 : (N - m) * (ed * c) + m * (ed * c) = N * (ed * c) := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hmN]
  have h3 : m * (ed * c) = ed * (m * c) := Nat.mul_left_comm m ed c
  rw [← hN] at h3
  have h4 : (en * c + 1 * ed + ed + 1) * N ≤ (ed * c) * N :=
    Nat.mul_le_mul_right N (by omega)
  have h5 : (en * c + 1 * ed + ed + 1) * N = (en * c + 1 * ed) * N + ed * N + N := by
    rw [Nat.add_mul, Nat.add_mul]
    omega
  have h6 : (ed * c) * N = N * (ed * c) := Nat.mul_comm _ _
  omega

/-- **Tooth: a seed-independent PRG violates the bound.** With `prg _ _ = y₀` the honest
    randomizer is the constant `decodeMask y₀`; `cancellingAdv` then has advantage
    `1 − 1 / |F|` against the simulator, which exceeds `ε + 1 / |F|` for every `ε < 1 − 2 / |F|`. -/
theorem tooth_constant_prg_breaks_blinding {F : Type} [LawfulField F] [DecidableEq F]
    {cardK cardF nA : Nat} (hPos : 0 < (cardK * cardF) * (cardF * nA)) (hF : 0 < cardF)
    (enum : SimpleEquiv (Fin cardF) F) (keySampler : Fin cardK → Bytes) (decodeMask : Bytes → F)
    (y₀ : Bytes) (ε : Spec.RatBound) (hε : ε.num * cardF + 2 * ε.den < ε.den * cardF) :
    ¬ GameBound
      (AdvDist
        (macCheckRealGame hPos enum (fun _ _ => y₀) keySampler decodeMask
          (fun _ : Fin nA => cancellingAdv (decodeMask y₀)))
        (macCheckSimGame hPos enum (fun _ : Fin nA => cancellingAdv (decodeMask y₀))))
      (ε.add ⟨1, cardF, hF⟩) := by
  intro hB
  have hReal := Spec.FinGame.winCount_of_forall_win _
    (tooth_constant_prg_real_always_wins (nA := nA) hPos enum keySampler decodeMask y₀)
  have hSim := cancellingAdv_sim_winCount (cardK := cardK) (nA := nA) hPos enum (decodeMask y₀)
  have hB' : Spec.natAbsDiff
      (macCheckRealGame hPos enum (fun _ _ => y₀) keySampler decodeMask
        (fun _ : Fin nA => cancellingAdv (decodeMask y₀))).winCount
      (macCheckSimGame hPos enum (fun _ : Fin nA => cancellingAdv (decodeMask y₀))).winCount *
        (ε.den * cardF) ≤
      (ε.num * cardF + 1 * ε.den) * ((cardK * cardF) * (cardF * nA)) := hB
  rw [hReal, hSim] at hB'
  have hN : (cardK * cardF) * (cardF * nA) = cardK * (cardF * (nA * 1)) * cardF := by
    rw [Nat.mul_one, Nat.mul_assoc cardK (cardF * nA) cardF, Nat.mul_comm (cardF * nA) cardF,
      Nat.mul_assoc cardK cardF (cardF * nA)]
  exact tooth_arith hN hPos hε hB'

/-- **Tooth: a seed-independent PRG is not `Spec.PrfHard`.** The bound of
    `computational_macBlind_spdz_security_bound` turns `cancellingAdv` into a refutation of
    the PRF assumption for every `ε < 1 − 2 / |F|`. -/
theorem tooth_constant_prg_not_prfHard {F : Type} [LawfulField F] [DecidableEq F]
    {cardK cardF : Nat} (hPos : 0 < (cardK * cardF) * (cardF * 1)) (hF : 0 < cardF)
    (enum : SimpleEquiv (Fin cardF) F) (keyLen outLen : Nat)
    (keySampler : Fin cardK → Bytes) (maskSampler : Fin cardF → Bytes) (decodeMask : Bytes → F)
    (hDecode : ∀ i : Fin cardF, decodeMask (maskSampler i) = enum.toFun i)
    (hU : UniformOn (Spec.PrfSampleOk keyLen 0 outLen) (prgPrfSampler keySampler maskSampler))
    (y₀ : Bytes) {𝒜 : Code byteOracleIface Bool → Prop}
    (h𝒜 : ∀ alpha : F,
      𝒜 (macBlindPrfDistinguisher decodeMask alpha (cancellingAdv (decodeMask y₀))))
    (ε : Spec.RatBound) (hε : ε.num * cardF + 2 * ε.den < ε.den * cardF) :
    ¬ Spec.PrfHard 𝒜 (fun _ _ => y₀) keyLen 0 outLen 1 ε :=
  fun hPrf => tooth_constant_prg_breaks_blinding hPos hF enum keySampler decodeMask y₀ ε hε
    (computational_macBlind_spdz_security_bound hPos hF enum (fun _ _ => y₀) keyLen outLen
      keySampler maskSampler decodeMask hDecode hU hPrf
      (fun _ : Fin 1 => cancellingAdv (decodeMask y₀)) (fun alpha _ => h𝒜 alpha))

/-- **Tooth: the unblinded residual determines the MAC key.** For `Δx ≠ 0` the defect
    `Δx · α − Δm`, opened without a randomizer, takes different values at different keys. -/
theorem tooth_unblinded_defect_separates_keys {F : Type} [LawfulField F]
    (deltaX deltaM alpha₁ alpha₂ : F) (hX : deltaX ≠ zero) (hNe : alpha₁ ≠ alpha₂) :
    sub (mul deltaX alpha₁) deltaM ≠ sub (mul deltaX alpha₂) deltaM := by
  intro hEq
  apply hNe
  have h1 := congrArg (fun z => add z deltaM) hEq
  rw [ring_sub_add_cancel_right, ring_sub_add_cancel_right] at h1
  exact field_mul_left_cancel hX h1

/-! ## 5. Byte samplers and the `Tower128` instance -/

/-- Little-endian `len`-byte encoding of `v`. -/
def leBytes : Nat → Nat → Bytes
  | 0, _ => []
  | len + 1, v => UInt8.ofNat (v % 256) :: leBytes len (v / 256)

/-- Little-endian value of a byte string. -/
def leValue : Bytes → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leValue bs

private theorem pow256_pos : ∀ len : Nat, 0 < 256 ^ len
  | 0 => Nat.one_pos
  | len + 1 => by
    rw [Nat.pow_succ]
    exact Nat.mul_pos (pow256_pos len) (by decide)

theorem leBytes_length : ∀ (len v : Nat), (leBytes len v).length = len
  | 0, _ => by rfl
  | len + 1, v => by
    show (leBytes len (v / 256)).length + 1 = len + 1
    rw [leBytes_length len]

theorem leValue_leBytes : ∀ (len v : Nat), v < 256 ^ len → leValue (leBytes len v) = v
  | 0, v, h => by
    have h0 : v = 0 := Nat.lt_one_iff.mp h
    subst h0
    rfl
  | len + 1, v, h => by
    have hDiv : v / 256 < 256 ^ len := by
      rw [Nat.pow_succ] at h
      exact (Nat.div_lt_iff_lt_mul (by decide)).mpr h
    have hb : (UInt8.ofNat (v % 256)).toNat = v % 256 := by
      rw [UInt8.toNat_ofNat']
      exact Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))
    show (UInt8.ofNat (v % 256)).toNat + 256 * leValue (leBytes len (v / 256)) = v
    rw [leValue_leBytes len _ hDiv, hb]
    omega

theorem leValue_lt : ∀ bs : Bytes, leValue bs < 256 ^ bs.length
  | [] => Nat.one_pos
  | b :: bs => by
    have ih := leValue_lt bs
    have hb : b.toNat < 256 := b.toNat_lt
    show b.toNat + 256 * leValue bs < 256 ^ (bs.length + 1)
    rw [Nat.pow_succ]
    omega

theorem leBytes_leValue : ∀ bs : Bytes, leBytes bs.length (leValue bs) = bs
  | [] => by rfl
  | b :: bs => by
    have hb : b.toNat < 256 := b.toNat_lt
    have hMod : (b.toNat + 256 * leValue bs) % 256 = b.toNat := by omega
    have hDiv : (b.toNat + 256 * leValue bs) / 256 = leValue bs := by omega
    show UInt8.ofNat ((b.toNat + 256 * leValue bs) % 256) ::
      leBytes bs.length ((b.toNat + 256 * leValue bs) / 256) = b :: bs
    rw [hMod, hDiv, leBytes_leValue bs, UInt8.ofNat_toNat]

/-- Uniform sampler of `len`-byte strings: the little-endian encoding of a coin in
    `Fin (256 ^ len)`. -/
def bytesSampler (len : Nat) (i : Fin (256 ^ len)) : Bytes := leBytes len i.1

