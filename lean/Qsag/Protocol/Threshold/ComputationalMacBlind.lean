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

theorem uniformOn_bytesSampler (len : Nat) :
    UniformOn (fun s : Bytes => s.length = len) (bytesSampler len) where
  mem i := leBytes_length len i.1
  injective i j h := by
    have h' : leValue (leBytes len i.1) = leValue (leBytes len j.1) := congrArg leValue h
    rw [leValue_leBytes len i.1 i.2, leValue_leBytes len j.1 j.2] at h'
    exact Fin.ext h'
  surjective s hs := by
    subst hs
    exact ⟨⟨leValue s, leValue_lt s⟩, leBytes_leValue s⟩

/-- Decode a byte string to the coin whose little-endian encoding it is. -/
def bytesToFin (len : Nat) (bs : Bytes) : Fin (256 ^ len) :=
  ⟨leValue bs % 256 ^ len, Nat.mod_lt _ (pow256_pos len)⟩

theorem bytesToFin_bytesSampler (len : Nat) (i : Fin (256 ^ len)) :
    bytesToFin len (bytesSampler len i) = i := by
  apply Fin.ext
  show leValue (leBytes len i.1) % 256 ^ len = i.1
  rw [leValue_leBytes len i.1 i.2, Nat.mod_eq_of_lt i.2]

/-- `tower128Enum` indexed by the 16-byte coin space `Fin (256 ^ 16)`. -/
def tower128ByteEnum : SimpleEquiv (Fin (256 ^ 16)) Tower128 :=
  SimpleEquiv.trans (finCastEquiv (by decide : 256 ^ 16 = 2 ^ 128)) tower128Enum

/-- Decode 16 little-endian bytes of the randomizer stream to a `Tower128` element, the shape
    of `next_tower128` on `PartyPrivateRng`. -/
def tower128DecodeMask (bs : Bytes) : Tower128 := tower128ByteEnum.toFun (bytesToFin 16 bs)

theorem tower128DecodeMask_bytesSampler (i : Fin (256 ^ 16)) :
    tower128DecodeMask (bytesSampler 16 i) = tower128ByteEnum.toFun i := by
  show tower128ByteEnum.toFun (bytesToFin 16 (bytesSampler 16 i)) = tower128ByteEnum.toFun i
  rw [bytesToFin_bytesSampler]

/-- Every keyed function is `Spec.PrfHard` with the trivial advantage bound `1`. -/
theorem prfHard_one (𝒜 : Code byteOracleIface Bool → Prop) (prf : Bytes → Bytes → Bytes)
    (keyLen inLen outLen q : Nat) :
    Spec.PrfHard 𝒜 prf keyLen inLen outLen q Spec.RatBound.one := by
  intro n nC nA hPos π sample _ adv _
  have h0 := Spec.FinGame.winProb_le_one
    (Spec.prfRealGame hPos prf q (fun ω => (sample (π.chal ω)).1) (fun ω => adv (π.advc ω)))
  have h1 := Spec.FinGame.winProb_le_one
    (Spec.prfIdealGame hPos q (fun ω => (sample (π.chal ω)).2) (fun ω => adv (π.advc ω)))
  have h0' : (Spec.prfRealGame hPos prf q (fun ω => (sample (π.chal ω)).1)
      (fun ω => adv (π.advc ω))).winCount * 1 ≤ 1 * n := h0
  have h1' : (Spec.prfIdealGame hPos q (fun ω => (sample (π.chal ω)).2)
      (fun ω => adv (π.advc ω))).winCount * 1 ≤ 1 * n := h1
  show Spec.natAbsDiff _ _ * 1 ≤ 1 * n
  unfold Spec.natAbsDiff
  split <;> omega

/-- **Blinded `Tower128` MAC check with a 32-byte seed.** The honest randomizer is the first
    16 bytes of the stream `prg seed []`, decoded by `tower128DecodeMask`. Against every family
    of MAC-check adversaries, if `prg` is a one-query PRF at input length `0` against all
    one-query distinguishers with advantage `εPrf`, the real check is within `εPrf + 2⁻¹²⁸` of
    the simulator. -/
theorem computational_macBlind_tower128_security_bound {nA : Nat}
    (hPos : 0 < (256 ^ 32 * 256 ^ 16) * (256 ^ 16 * nA))
    (prg : Bytes → Bytes → Bytes)
    {εPrf : Spec.RatBound}
    (hPrf : Spec.PrfHard (fun c => Spec.Within 1 c) prg 32 0 16 1 εPrf)
    (adv : Fin nA → MacCheckAdv Tower128) :
    GameBound
      (AdvDist (macCheckRealGame hPos tower128ByteEnum prg (bytesSampler 32) tower128DecodeMask adv)
        (macCheckSimGame hPos tower128ByteEnum adv))
      (εPrf.add (Spec.RatBound.invPow2 128)) :=
  Spec.GameBound.trans
    (computational_macBlind_spdz_security_bound hPos (pow256_pos 16) tower128ByteEnum prg 32 16
      (bytesSampler 32) (bytesSampler 16) tower128DecodeMask tower128DecodeMask_bytesSampler
      (uniformOn_prgPrfSampler (uniformOn_bytesSampler 32) (uniformOn_bytesSampler 16))
      hPrf adv (fun alpha a => macBlindPrfDistinguisher_within tower128DecodeMask alpha (adv a)))
    (Spec.RatBound.add_le_add (Spec.RatBound.le_refl εPrf)
      (by show 1 * 2 ^ 128 ≤ 1 * 256 ^ 16; decide))

theorem tower128_single_coin_space_pos : 0 < (256 ^ 32 * 256 ^ 16) * (256 ^ 16 * 1) := by
  decide

/-- **Tooth at `Tower128`.** With a seed-independent PRG, `cancellingAdv` separates the real
    blinded `Tower128` check from the simulator by more than `1/2 + 2⁻¹²⁸`. -/
theorem tooth_constant_prg_breaks_tower128_blinding (y₀ : Bytes) :
    ¬ GameBound
      (AdvDist
        (macCheckRealGame tower128_single_coin_space_pos tower128ByteEnum (fun _ _ => y₀)
          (bytesSampler 32) tower128DecodeMask
          (fun _ : Fin 1 => cancellingAdv (tower128DecodeMask y₀)))
        (macCheckSimGame tower128_single_coin_space_pos tower128ByteEnum
          (fun _ : Fin 1 => cancellingAdv (tower128DecodeMask y₀))))
      ((⟨1, 2, by decide⟩ : Spec.RatBound).add (Spec.RatBound.invPow2 128)) :=
  fun h => tooth_constant_prg_breaks_blinding tower128_single_coin_space_pos (pow256_pos 16)
    tower128ByteEnum (bytesSampler 32) tower128DecodeMask y₀ ⟨1, 2, by decide⟩
    (by show 1 * 256 ^ 16 + 2 * 2 < 2 * 256 ^ 16; decide)
    (Spec.GameBound.trans h (Spec.RatBound.add_le_add (Spec.RatBound.le_refl _)
      (by show 1 * 256 ^ 16 ≤ 1 * 2 ^ 128; decide)))

/-- The premises of `computational_macBlind_tower128_security_bound` are jointly satisfiable:
    the truncating PRG with the trivial advantage bound `1` of `prfHard_one`, one adversary
    coin and the adversary `cancellingAdv zero`. -/
theorem inhabited_computational_macBlind_tower128 :
    GameBound
      (AdvDist
        (macCheckRealGame tower128_single_coin_space_pos tower128ByteEnum
          (fun seed _ => seed.take 16) (bytesSampler 32) tower128DecodeMask
          (fun _ : Fin 1 => cancellingAdv (zero : Tower128)))
        (macCheckSimGame tower128_single_coin_space_pos tower128ByteEnum
          (fun _ : Fin 1 => cancellingAdv (zero : Tower128))))
      (Spec.RatBound.one.add (Spec.RatBound.invPow2 128)) :=
  computational_macBlind_tower128_security_bound tower128_single_coin_space_pos
    (fun seed _ => seed.take 16) (prfHard_one _ _ 32 0 16 1) _

/-! ## 6. Pooled single-use blinding triples

A retained `OtMesh` answers a blinded check from its pool of single-use triples: per-party
additive shares of a joint randomizer `r`, a one-time mask `a`, and `c`, the output of one
`pairwise_ole_tower128` / `ole_blind_ext2_batch` call on `(a, r)` (`refill_blind_pool`,
`refill_ext2_blind_pool`). `blind_open_ext2_pooled` commit-opens `e = Σ_p (d_p + a_p)` and
then `w = Σ_p (r_p · e − c_p)`; `blind_open_pooled` opens `w = Σ_p (r_p · e + c_p)` in
characteristic `2`. The pool has no sacrifice or consistency check on `c`: the lemmas below
give the opened value for a correct triple and for a triple whose correlation is off by an
input shift `δ` of the mask and an additive error `err`. -/

/-- Sum of the first `n` parties' additive shares. -/
@[expose] def partySum {F : Type} [LawfulCommRing F] : Nat → (Nat → F) → F
  | 0, _ => zero
  | n + 1, s => add (partySum n s) (s n)

theorem partySum_add {F : Type} [LawfulCommRing F] (s t : Nat → F) :
    ∀ n : Nat, partySum n (fun p => add (s p) (t p)) = add (partySum n s) (partySum n t)
  | 0 => (LawfulCommRing.add_zero (zero : F)).symm
  | n + 1 => by
    show add (partySum n (fun p => add (s p) (t p))) (add (s n) (t n)) =
      add (add (partySum n s) (s n)) (add (partySum n t) (t n))
    rw [partySum_add s t n]
    exact LawfulCommRing.add_add_add_comm _ _ _ _

theorem partySum_sub {F : Type} [LawfulCommRing F] (s t : Nat → F) :
    ∀ n : Nat, partySum n (fun p => sub (s p) (t p)) = sub (partySum n s) (partySum n t)
  | 0 => (LawfulCommRing.sub_self (zero : F)).symm
  | n + 1 => by
    show add (partySum n (fun p => sub (s p) (t p))) (sub (s n) (t n)) =
      sub (add (partySum n s) (s n)) (add (partySum n t) (t n))
    rw [partySum_sub s t n]
    constructive_ring

theorem partySum_mul_right {F : Type} [LawfulCommRing F] (s : Nat → F) (e : F) :
    ∀ n : Nat, partySum n (fun p => mul (s p) e) = mul (partySum n s) e
  | 0 => (LawfulCommRing.zero_mul e).symm
  | n + 1 => by
    show add (partySum n (fun p => mul (s p) e)) (mul (s n) e) = mul (add (partySum n s) (s n)) e
    rw [partySum_mul_right s e n]
    exact (LawfulCommRing.right_distrib _ _ _).symm

/-- The opened masked residual `e = Σ_p (d_p + a_p)`. -/
@[expose] def pooledMaskedOpen {F : Type} [LawfulCommRing F] (n : Nat) (dSh aSh : Nat → F) : F :=
  partySum n (fun p => add (dSh p) (aSh p))

/-- The opened product of `blind_open_ext2_pooled`: `w = Σ_p (r_p · e − c_p)`. -/
@[expose] def pooledBlindOpenSub {F : Type} [LawfulCommRing F] (n : Nat) (rSh cSh : Nat → F)
    (e : F) : F :=
  partySum n (fun p => sub (mul (rSh p) e) (cSh p))

/-- The opened product of `blind_open_pooled`: `w = Σ_p (r_p · e + c_p)`. -/
def pooledBlindOpenAdd {F : Type} [LawfulCommRing F] (n : Nat) (rSh cSh : Nat → F) (e : F) : F :=
  partySum n (fun p => add (mul (rSh p) e) (cSh p))

theorem pooledMaskedOpen_eq {F : Type} [LawfulCommRing F] (n : Nat) (dSh aSh : Nat → F) :
    pooledMaskedOpen n dSh aSh = add (partySum n dSh) (partySum n aSh) :=
  partySum_add dSh aSh n

theorem pooledBlindOpenSub_eq {F : Type} [LawfulCommRing F] (n : Nat) (rSh cSh : Nat → F)
    (e : F) :
    pooledBlindOpenSub n rSh cSh e = sub (mul (partySum n rSh) e) (partySum n cSh) :=
  (partySum_sub (fun p => mul (rSh p) e) cSh n).trans
    (congrArg (fun x => sub x (partySum n cSh)) (partySum_mul_right rSh e n))

theorem pooledBlindOpenAdd_eq {F : Type} [LawfulCommRing F] (n : Nat) (rSh cSh : Nat → F)
    (e : F) :
    pooledBlindOpenAdd n rSh cSh e = add (mul (partySum n rSh) e) (partySum n cSh) :=
  (partySum_add (fun p => mul (rSh p) e) cSh n).trans
    (congrArg (fun x => add x (partySum n cSh)) (partySum_mul_right rSh e n))

/-- **Pooled opening with a faulty triple (`blind_open_ext2_pooled`).** If the shares of `c`
    sum to `r · (a + δ) + err`, the opened value is `r · (d − δ) − err`. -/
theorem pooledBlindOpenSub_faulty {F : Type} [LawfulCommRing F] (n : Nat)
    (rSh aSh cSh dSh : Nat → F) (delta err : F)
    (hC : partySum n cSh = add (mul (partySum n rSh) (add (partySum n aSh) delta)) err) :
    pooledBlindOpenSub n rSh cSh (pooledMaskedOpen n dSh aSh) =
      sub (mul (partySum n rSh) (sub (partySum n dSh) delta)) err := by
  rw [pooledBlindOpenSub_eq, pooledMaskedOpen_eq, hC]
  constructive_ring

/-- **Pooled opening correctness (`blind_open_ext2_pooled`).** If the shares of `c` sum to
    `r · a`, the opened value is `r · d`. -/
theorem pooledBlindOpenSub_correct {F : Type} [LawfulCommRing F] (n : Nat)
    (rSh aSh cSh dSh : Nat → F)
    (hC : partySum n cSh = mul (partySum n rSh) (partySum n aSh)) :
    pooledBlindOpenSub n rSh cSh (pooledMaskedOpen n dSh aSh) =
      mul (partySum n rSh) (partySum n dSh) := by
  rw [pooledBlindOpenSub_eq, pooledMaskedOpen_eq, hC]
  constructive_ring

/-- **Pooled opening with a faulty triple in characteristic `2` (`blind_open_pooled`).** If the
    shares of `c` sum to `r · (a + δ) + err`, the opened value is `r · (d + δ) + err`. -/
theorem pooledBlindOpenAdd_faulty {F : Type} [LawfulCommRing F] (hChar : ∀ x : F, add x x = zero)
    (n : Nat) (rSh aSh cSh dSh : Nat → F) (delta err : F)
    (hC : partySum n cSh = add (mul (partySum n rSh) (add (partySum n aSh) delta)) err) :
    pooledBlindOpenAdd n rSh cSh (pooledMaskedOpen n dSh aSh) =
      add (mul (partySum n rSh) (add (partySum n dSh) delta)) err := by
  rw [pooledBlindOpenAdd_eq, pooledMaskedOpen_eq, hC]
  have h : add (mul (partySum n rSh) (add (partySum n dSh) (partySum n aSh)))
        (add (mul (partySum n rSh) (add (partySum n aSh) delta)) err) =
      add (add (mul (partySum n rSh) (add (partySum n dSh) delta)) err)
        (add (mul (partySum n rSh) (partySum n aSh)) (mul (partySum n rSh) (partySum n aSh))) := by
    constructive_ring
  rw [h, hChar, LawfulCommRing.add_zero]

theorem tower128_add_self (x : Tower128) : add x x = zero := towerAdd_self_zero 7 x

/-- **Pooled opening correctness over `Tower128` (`blind_open_pooled`).** If the shares of `c`
    sum to `r · a`, the opened value is `r · d`. -/
theorem pooledBlindOpenAdd_correct_tower128 (n : Nat) (rSh aSh cSh dSh : Nat → Tower128)
    (hC : partySum n cSh = mul (partySum n rSh) (partySum n aSh)) :
    pooledBlindOpenAdd n rSh cSh (pooledMaskedOpen n dSh aSh) =
      mul (partySum n rSh) (partySum n dSh) := by
  rw [pooledBlindOpenAdd_eq, pooledMaskedOpen_eq, hC]
  have h : add (mul (partySum n rSh) (add (partySum n dSh) (partySum n aSh)))
        (mul (partySum n rSh) (partySum n aSh)) =
      add (mul (partySum n rSh) (partySum n dSh))
        (add (mul (partySum n rSh) (partySum n aSh)) (mul (partySum n rSh) (partySum n aSh))) := by
    constructive_ring
  rw [h, tower128_add_self, LawfulCommRing.add_zero]

/-- The affine map `r ↦ (r + r_corrupt) · d + c` of the honest randomizer, a permutation of
    the field for `d ≠ 0`. -/
def affineBlindEquiv {F : Type} [LawfulField F] (rCorrupt d c : F) (hd : d ≠ zero) :
    SimpleEquiv F F where
  toFun r := add (mul (add r rCorrupt) d) c
  invFun w := sub (mul (sub w c) (LawfulField.inv d)) rCorrupt
  left_inv r := by
    show sub (mul (sub (add (mul (add r rCorrupt) d) c) c) (LawfulField.inv d)) rCorrupt = r
    rw [ring_add_sub_cancel_right, LawfulCommRing.mul_assoc, LawfulField.mul_inv_cancel hd,
      LawfulCommRing.mul_one, ring_add_sub_cancel_right]
  right_inv w := by
    show add (mul (add (sub (mul (sub w c) (LawfulField.inv d)) rCorrupt) rCorrupt) d) c = w
    rw [ring_sub_add_cancel_right, LawfulCommRing.mul_assoc,
      LawfulCommRing.mul_comm (LawfulField.inv d) d, LawfulField.mul_inv_cancel hd,
      LawfulCommRing.mul_one, ring_sub_add_cancel_right]

theorem affineBlindEquiv_toFun {F : Type} [LawfulField F] (rCorrupt d c : F) (hd : d ≠ zero)
    (r : F) : (affineBlindEquiv rCorrupt d c hd).toFun r = add (mul (add r rCorrupt) d) c := by
  rfl

/-- **A faulty triple does not bias a failing check.** With effective defect `d ≠ 0` and any
    additive correlation error `err` fixed before the honest randomizer is sampled, the opened
    value `(r + r_corrupt) · d − err` is uniform; in particular it is `0`, a false accept, for
    exactly one honest randomizer. -/
theorem faultyTriple_opening_uniform {F : Type} [LawfulField F] [DecidableEq F] {cardF : Nat}
    (enum : SimpleEquiv (Fin cardF) F) (rCorrupt d err : F) (hd : d ≠ zero) :
    (∀ g : F → Nat,
      qsum cardF (fun i => g (sub (mul (add (enum.toFun i) rCorrupt) d) err)) =
        qsum cardF (fun i => g (enum.toFun i))) ∧
    qsum cardF (fun i =>
      if sub (mul (add (enum.toFun i) rCorrupt) d) err = zero then 1 else 0) = 1 := by
  have hUnif : ∀ g : F → Nat,
      qsum cardF (fun i => g (sub (mul (add (enum.toFun i) rCorrupt) d) err)) =
        qsum cardF (fun i => g (enum.toFun i)) := by
    intro g
    refine Eq.trans (qsum_congr (fun i => ?_))
      (qsum_bijection_invariant enum (affineBlindEquiv rCorrupt d (neg err) hd) g)
    rw [affineBlindEquiv_toFun, LawfulCommRing.sub_eq_add_neg]
  exact ⟨hUnif, (hUnif (fun w => if w = zero then 1 else 0)).trans (qsum_enum_eq_target enum zero)⟩

/-- **A faulty triple makes an unshifted check abort.** With effective defect `0` and additive
    correlation error `err ≠ 0`, the opened value is nonzero for every randomizer. -/
theorem faultyTriple_unshifted_check_aborts {F : Type} [LawfulCommRing F] (r err : F)
    (hErr : err ≠ zero) : sub (mul r zero) err ≠ zero := by
  intro h
  rw [LawfulCommRing.mul_zero] at h
  exact hErr (LawfulCommRing.sub_eq_zero_iff.mp h).symm

/-! ## 7. PRG-expanded blinding with a general view

`coordGame_blinded_view_bound` packages the two hops for any real verdict that is a test of
the PRG output and any simulated verdict that reads only the mask coin and the adversary coin.
It is instantiated for the opening with a post-OLE additive error and for one round of the
pooled opening, whose view also contains the masked residual `e`. -/

/-- **PRG-expanded blinding, general view.** If outside the coins `bad` the real verdict on a
    uniform mask and the simulated verdict accept on the same number of mask coins, and every
    adversary coin has at most one bad MAC-key coin, then the real game on the PRG output is
    within `εPrf + 1 / cardF` of the simulated game. -/
theorem coordGame_blinded_view_bound {cardK cardY cardF nA : Nat}
    (hPos : 0 < (cardK * cardY) * (cardF * nA)) (hF : 0 < cardF)
    (prg : Bytes → Bytes → Bytes) (keyLen outLen : Nat)
    (keySampler : Fin cardK → Bytes) (maskSampler : Fin cardY → Bytes)
    (hU : UniformOn (Spec.PrfSampleOk keyLen 0 outLen) (prgPrfSampler keySampler maskSampler))
    {𝒜 : Code byteOracleIface Bool → Prop} {εPrf : Spec.RatBound}
    (hPrf : Spec.PrfHard 𝒜 prg keyLen 0 outLen 1 εPrf)
    (real : Fin cardF → Fin nA → Bytes → Bool) (sim : Fin cardY → Fin nA → Bool)
    (h𝒜 : ∀ (ca : Fin cardF) (a : Fin nA), 𝒜 (prgOutputTest (real ca a)))
    (bad : Fin cardF → Fin nA → Bool)
    (hGood : ∀ (ca : Fin cardF) (a : Fin nA), bad ca a = false →
      qsum cardY (fun cy => if real ca a (maskSampler cy) then 1 else 0) =
        qsum cardY (fun cy => if sim cy a then 1 else 0))
    (hBad : ∀ a : Fin nA, qsum cardF (fun ca => if bad ca a then 1 else 0) ≤ 1) :
    GameBound
      (AdvDist
        (coordGame hPos (fun ck (_ : Fin cardY) ca a => real ca a (prg (keySampler ck) [])))
        (coordGame hPos (fun (_ : Fin cardK) cy (_ : Fin cardF) a => sim cy a)))
      (εPrf.add ⟨1, cardF, hF⟩) :=
  Spec.GameBound.trans
    (Spec.adv_triangle _
      (coordGame hPos (fun (_ : Fin cardK) cy ca a => real ca a (maskSampler cy))) _)
    (Spec.RatBound.add_le_add
      (coordGame_prf_hop hPos prg keyLen outLen keySampler maskSampler hU hPrf real h𝒜)
      (coordGame_advDist_le_inv_card hPos hF _ _ bad (fun _ ca a hb => hGood ca a hb) hBad))

/-- For shifts that are not both zero, at most one MAC-key coin has zero defect. -/
theorem zero_defect_bad_coins_le_one {F : Type} [LawfulField F] [DecidableEq F] {cardF : Nat}
    (enum : SimpleEquiv (Fin cardF) F) (deltaX deltaM : F) :
    qsum cardF (fun ca => if decide (¬ (deltaX = zero ∧ deltaM = zero) ∧
      sub (mul deltaX (enum.toFun ca)) deltaM = zero) then 1 else 0) ≤ 1 := by
  apply qsum_indicator_le_one_of_unique
  intro i j hi hj
  have hi' := of_decide_eq_true hi
  have hj' := of_decide_eq_true hj
  exact zero_defect_key_unique enum deltaX deltaM hi'.1 i j hi'.2 hj'.2

/-! ### 7a. The direct opening with a post-OLE additive error -/

/-- The opened value `(r_honest + r_corrupt) · (Δx · α − Δm) + err` of the direct
    multiplication (`blind_open_ext2`, `blind_open_tower128` without a retained mesh) when the
    OLE output is off by an additive `err`; the expression that `macBlindOpen` names. -/
def oleBlindedOpening {F : Type} [LawfulCommRing F] (A : MacCheckAdv F) (err alpha rHonest : F) :
    F :=
  add (mul (add rHonest (corruptSum A.corruptRandomizers)) (sub (mul A.deltaX alpha) A.deltaM)) err

/-- The simulated opened value under an additive error: the error itself for an unshifted
    check, a uniform field element otherwise. The MAC key is not an argument. -/
def oleSimulatedOpening {F : Type} [LawfulCommRing F] [DecidableEq F] (A : MacCheckAdv F)
    (err u : F) : F :=
  if A.deltaX = zero ∧ A.deltaM = zero then err else u

theorem oleBlindedOpening_eq {F : Type} [LawfulCommRing F] (A : MacCheckAdv F)
    (err alpha rHonest : F) :
    oleBlindedOpening A err alpha rHonest =
      add (mul (add rHonest (corruptSum A.corruptRandomizers))
        (sub (mul A.deltaX alpha) A.deltaM)) err := by rfl

theorem oleSimulatedOpening_eq {F : Type} [LawfulCommRing F] [DecidableEq F] (A : MacCheckAdv F)
    (err u : F) :
    oleSimulatedOpening A err u = if A.deltaX = zero ∧ A.deltaM = zero then err else u := by rfl

theorem oleBlindedOpening_unshifted {F : Type} [LawfulCommRing F] (A : MacCheckAdv F)
    (hX : A.deltaX = zero) (hM : A.deltaM = zero) (err alpha rHonest : F) :
    oleBlindedOpening A err alpha rHonest = err := by
  unfold oleBlindedOpening
  rw [hX, hM, LawfulCommRing.zero_mul, LawfulCommRing.sub_zero, LawfulCommRing.mul_zero,
    LawfulCommRing.zero_add]

/-- Real game of the direct opening with additive error `oleErr a` chosen from the adversary coin. -/
def macCheckOleRealGame {F : Type} [LawfulCommRing F] {cardK cardF nA : Nat}
    (hPos : 0 < (cardK * cardF) * (cardF * nA)) (enum : SimpleEquiv (Fin cardF) F)
    (prg : Bytes → Bytes → Bytes) (keySampler : Fin cardK → Bytes) (decodeMask : Bytes → F)
    (adv : Fin nA → MacCheckAdv F) (oleErr : Fin nA → F) :
    FinGame ((cardK * cardF) * (cardF * nA)) :=
  coordGame hPos (fun ck (_ : Fin cardF) ca a =>
    (adv a).guess (oleBlindedOpening (adv a) (oleErr a) (enum.toFun ca)
      (decodeMask (prg (keySampler ck) []))))

/-- Simulated game of the direct opening with additive error; the MAC-key coin is not read. -/
def macCheckOleSimGame {F : Type} [LawfulCommRing F] [DecidableEq F] {cardK cardF nA : Nat}
    (hPos : 0 < (cardK * cardF) * (cardF * nA)) (enum : SimpleEquiv (Fin cardF) F)
    (adv : Fin nA → MacCheckAdv F) (oleErr : Fin nA → F) :
    FinGame ((cardK * cardF) * (cardF * nA)) :=
  coordGame hPos (fun (_ : Fin cardK) cy (_ : Fin cardF) a =>
    (adv a).guess (oleSimulatedOpening (adv a) (oleErr a) (enum.toFun cy)))

/-- Reduction distinguisher of the direct opening with additive error. -/
def macBlindOlePrfDistinguisher {F : Type} [LawfulCommRing F] (decodeMask : Bytes → F)
    (alpha : F) (A : MacCheckAdv F) (err : F) : Code byteOracleIface Bool :=
  prgOutputTest (fun y => A.guess (oleBlindedOpening A err alpha (decodeMask y)))

theorem macBlindOlePrfDistinguisher_within {F : Type} [LawfulCommRing F] (decodeMask : Bytes → F)
    (alpha : F) (A : MacCheckAdv F) (err : F) :
    Spec.Within 1 (macBlindOlePrfDistinguisher decodeMask alpha A err) :=
  prgOutputTest_within _

/-- **Computational blinded MAC check with a post-OLE additive error.** The real opening
    `(r_honest + r_corrupt) · d + err`, with PRG-expanded `r_honest` and `err` chosen by the
    adversary before the opening, is within `εPrf + 1 / |F|` of `oleSimulatedOpening`. -/
theorem computational_macBlind_ole_error_security_bound {F : Type} [LawfulField F]
    [DecidableEq F] {cardK cardF nA : Nat}
    (hPos : 0 < (cardK * cardF) * (cardF * nA)) (hF : 0 < cardF)
    (enum : SimpleEquiv (Fin cardF) F)
    (prg : Bytes → Bytes → Bytes) (keyLen outLen : Nat)
    (keySampler : Fin cardK → Bytes) (maskSampler : Fin cardF → Bytes) (decodeMask : Bytes → F)
    (hDecode : ∀ i : Fin cardF, decodeMask (maskSampler i) = enum.toFun i)
    (hU : UniformOn (Spec.PrfSampleOk keyLen 0 outLen) (prgPrfSampler keySampler maskSampler))
    {𝒜 : Code byteOracleIface Bool → Prop} {εPrf : Spec.RatBound}
    (hPrf : Spec.PrfHard 𝒜 prg keyLen 0 outLen 1 εPrf)
    (adv : Fin nA → MacCheckAdv F) (oleErr : Fin nA → F)
    (h𝒜 : ∀ (alpha : F) (a : Fin nA),
      𝒜 (macBlindOlePrfDistinguisher decodeMask alpha (adv a) (oleErr a))) :
    GameBound
      (AdvDist (macCheckOleRealGame hPos enum prg keySampler decodeMask adv oleErr)
        (macCheckOleSimGame hPos enum adv oleErr))
      (εPrf.add ⟨1, cardF, hF⟩) := by
  refine coordGame_blinded_view_bound hPos hF prg keyLen outLen keySampler maskSampler hU hPrf
    (fun ca a y =>
      (adv a).guess (oleBlindedOpening (adv a) (oleErr a) (enum.toFun ca) (decodeMask y)))
    (fun cy a => (adv a).guess (oleSimulatedOpening (adv a) (oleErr a) (enum.toFun cy)))
    (fun ca a => h𝒜 (enum.toFun ca) a)
    (fun ca a => decide (¬ ((adv a).deltaX = zero ∧ (adv a).deltaM = zero) ∧
      sub (mul (adv a).deltaX (enum.toFun ca)) (adv a).deltaM = zero))
    ?_ (fun a => zero_defect_bad_coins_le_one enum (adv a).deltaX (adv a).deltaM)
  intro ca a hb
  have hNot : ¬ (¬ ((adv a).deltaX = zero ∧ (adv a).deltaM = zero) ∧
      sub (mul (adv a).deltaX (enum.toFun ca)) (adv a).deltaM = zero) := of_decide_eq_false hb
  have hRw : ∀ cy : Fin cardF,
      (if (adv a).guess (oleBlindedOpening (adv a) (oleErr a) (enum.toFun ca)
        (decodeMask (maskSampler cy))) then 1 else 0) =
      (if (adv a).guess (oleBlindedOpening (adv a) (oleErr a) (enum.toFun ca)
        (enum.toFun cy)) then 1 else 0) := fun cy => by rw [hDecode]
  refine (qsum_congr hRw).trans ?_
  by_cases hHon : (adv a).deltaX = zero ∧ (adv a).deltaM = zero
  · apply qsum_congr
    intro cy
    have hS : oleSimulatedOpening (adv a) (oleErr a) (enum.toFun cy) = oleErr a :=
      iteOfPos hHon _ _
    rw [oleBlindedOpening_unshifted (adv a) hHon.1 hHon.2, hS]
  · have hd : sub (mul (adv a).deltaX (enum.toFun ca)) (adv a).deltaM ≠ zero :=
      fun h0 => hNot ⟨hHon, h0⟩
    refine Eq.trans (qsum_congr (fun cy => ?_))
      ((qsum_bijection_invariant enum
        (affineBlindEquiv (corruptSum (adv a).corruptRandomizers) _ (oleErr a) hd)
        (fun w => if (adv a).guess w then 1 else 0)).trans (qsum_congr (fun cy => ?_)))
    · rfl
    · have hS : oleSimulatedOpening (adv a) (oleErr a) (enum.toFun cy) = enum.toFun cy :=
        iteOfNeg hHon _ _
      rw [hS]

/-! ### 7b. One round of the pooled opening

The view of a pooled round is the pair `(e, w)`: the masked residual `e = d + a`, opened
first, and the product `w`. The honest party's mask share and randomizer share are both read
from its seeded stream, so one PRG output decodes to the pair `(a_honest, r_honest)`. -/

/-- Adversary against one pooled blinding round. It fixes the shifts `Δx`, `Δm`, the sums of the
    corrupt parties' mask and randomizer shares, and a deviation of the product opening that
    may depend on the opened `e` (it absorbs an additive error of the triple correlation and a
    shifted corrupt product share); it guesses from the pair `(e, w)`. -/
structure PooledCheckAdv (F : Type) where
  deltaX : F
  deltaM : F
  corruptMask : F
  corruptRandomizer : F
  productError : F → F
  guess : F × F → Bool

/-- The real view `(e, w)` of a pooled round at honest shares `h = (a_honest, r_honest)`:
    `e = a_honest + d + a_corrupt` and `w = (r_honest + r_corrupt) · d + productError e`,
    with `d = Δx · α − Δm`. -/
def pooledRealView {F : Type} [LawfulCommRing F] (A : PooledCheckAdv F) (alpha : F) (h : F × F) :
    F × F :=
  (add (add h.1 (sub (mul A.deltaX alpha) A.deltaM)) A.corruptMask,
   add (mul (add h.2 A.corruptRandomizer) (sub (mul A.deltaX alpha) A.deltaM))
     (A.productError (add (add h.1 (sub (mul A.deltaX alpha) A.deltaM)) A.corruptMask)))

/-- The simulated view from a uniform pair `u`: for an unshifted check a uniform `e` and the
    adversary's own deviation at `e`; otherwise a uniform pair. The MAC key is not an argument. -/
def pooledSimView {F : Type} [LawfulCommRing F] [DecidableEq F] (A : PooledCheckAdv F)
    (u : F × F) : F × F :=
  if A.deltaX = zero ∧ A.deltaM = zero then (u.1, A.productError u.1) else u

theorem pooledRealView_eq {F : Type} [LawfulCommRing F] (A : PooledCheckAdv F) (alpha : F)
    (h : F × F) :
    pooledRealView A alpha h =
      (add (add h.1 (sub (mul A.deltaX alpha) A.deltaM)) A.corruptMask,
       add (mul (add h.2 A.corruptRandomizer) (sub (mul A.deltaX alpha) A.deltaM))
         (A.productError (add (add h.1 (sub (mul A.deltaX alpha) A.deltaM)) A.corruptMask))) := by
  rfl

theorem pooledSimView_eq {F : Type} [LawfulCommRing F] [DecidableEq F] (A : PooledCheckAdv F)
    (u : F × F) :
    pooledSimView A u =
      if A.deltaX = zero ∧ A.deltaM = zero then (u.1, A.productError u.1) else u := by rfl

theorem pooledRealView_unshifted {F : Type} [LawfulCommRing F] (A : PooledCheckAdv F)
    (hX : A.deltaX = zero) (hM : A.deltaM = zero) (alpha : F) (h : F × F) :
    pooledRealView A alpha h =
      (add h.1 A.corruptMask, A.productError (add h.1 A.corruptMask)) := by
  unfold pooledRealView
  rw [hX, hM, LawfulCommRing.zero_mul, LawfulCommRing.sub_zero, LawfulCommRing.add_zero,
    LawfulCommRing.mul_zero, LawfulCommRing.zero_add]

/-- The map `(a, r) ↦ (a + d + a_corrupt, (r + r_corrupt) · d + errW e)` from the honest
    shares to the view of a pooled round, a permutation of `F × F` for `d ≠ 0`. -/
def pooledViewEquiv {F : Type} [LawfulField F] (aCorrupt rCorrupt d : F) (errW : F → F)
    (hd : d ≠ zero) : SimpleEquiv (F × F) (F × F) where
  toFun h := (add (add h.1 d) aCorrupt,
    add (mul (add h.2 rCorrupt) d) (errW (add (add h.1 d) aCorrupt)))
  invFun v := (sub (sub v.1 aCorrupt) d,
    sub (mul (sub v.2 (errW v.1)) (LawfulField.inv d)) rCorrupt)
  left_inv h := by
    have h1 : sub (sub (add (add h.1 d) aCorrupt) aCorrupt) d = h.1 := by
      rw [ring_add_sub_cancel_right, ring_add_sub_cancel_right]
    have h2 : sub (mul (sub (add (mul (add h.2 rCorrupt) d) (errW (add (add h.1 d) aCorrupt)))
        (errW (add (add h.1 d) aCorrupt))) (LawfulField.inv d)) rCorrupt = h.2 := by
      rw [ring_add_sub_cancel_right, LawfulCommRing.mul_assoc, LawfulField.mul_inv_cancel hd,
        LawfulCommRing.mul_one, ring_add_sub_cancel_right]
    exact Prod.ext h1 h2
  right_inv v := by
    have h1 : add (add (sub (sub v.1 aCorrupt) d) d) aCorrupt = v.1 := by
      rw [ring_sub_add_cancel_right, ring_sub_add_cancel_right]
    have h2 : add (mul (add (sub (mul (sub v.2 (errW v.1)) (LawfulField.inv d)) rCorrupt)
        rCorrupt) d) (errW (add (add (sub (sub v.1 aCorrupt) d) d) aCorrupt)) = v.2 := by
      rw [h1, ring_sub_add_cancel_right, LawfulCommRing.mul_assoc,
        LawfulCommRing.mul_comm (LawfulField.inv d) d, LawfulField.mul_inv_cancel hd,
        LawfulCommRing.mul_one, ring_sub_add_cancel_right]
    exact Prod.ext h1 h2

/-- Real game of one pooled round: uniform seed, uniform MAC key, adversary coin; the honest
    mask and randomizer shares are `decodePair (prg seed [])`. -/
def pooledCheckRealGame {F : Type} [LawfulCommRing F] {cardK cardY cardF nA : Nat}
    (hPos : 0 < (cardK * cardY) * (cardF * nA)) (enum : SimpleEquiv (Fin cardF) F)
    (prg : Bytes → Bytes → Bytes) (keySampler : Fin cardK → Bytes) (decodePair : Bytes → F × F)
    (adv : Fin nA → PooledCheckAdv F) : FinGame ((cardK * cardY) * (cardF * nA)) :=
  coordGame hPos (fun ck (_ : Fin cardY) ca a =>
    (adv a).guess (pooledRealView (adv a) (enum.toFun ca) (decodePair (prg (keySampler ck) []))))

/-- Simulated game of one pooled round; the MAC-key coin is not read. -/
def pooledCheckSimGame {F : Type} [LawfulCommRing F] [DecidableEq F] {cardK cardY cardF nA : Nat}
    (hPos : 0 < (cardK * cardY) * (cardF * nA)) (pairEnum : SimpleEquiv (Fin cardY) (F × F))
    (adv : Fin nA → PooledCheckAdv F) : FinGame ((cardK * cardY) * (cardF * nA)) :=
  coordGame hPos (fun (_ : Fin cardK) cy (_ : Fin cardF) a =>
    (adv a).guess (pooledSimView (adv a) (pairEnum.toFun cy)))

/-- Reduction distinguisher of one pooled round. -/
def pooledBlindPrfDistinguisher {F : Type} [LawfulCommRing F] (decodePair : Bytes → F × F)
    (alpha : F) (A : PooledCheckAdv F) : Code byteOracleIface Bool :=
  prgOutputTest (fun y => A.guess (pooledRealView A alpha (decodePair y)))

theorem pooledBlindPrfDistinguisher_within {F : Type} [LawfulCommRing F]
    (decodePair : Bytes → F × F) (alpha : F) (A : PooledCheckAdv F) :
    Spec.Within 1 (pooledBlindPrfDistinguisher decodePair alpha A) :=
  prgOutputTest_within _

/-- **Computational security of one pooled blinding round.** The view `(e, w)` of a pooled
    round whose honest mask and randomizer shares are expanded from a seed is within
    `εPrf + 1 / |F|` of `pooledSimView`, for every adversary family whose reduction
    distinguishers lie in `𝒜`. -/
theorem computational_pooledBlind_security_bound {F : Type} [LawfulField F] [DecidableEq F]
    {cardK cardY cardF nA : Nat}
    (hPos : 0 < (cardK * cardY) * (cardF * nA)) (hF : 0 < cardF)
    (enum : SimpleEquiv (Fin cardF) F) (pairEnum : SimpleEquiv (Fin cardY) (F × F))
    (prg : Bytes → Bytes → Bytes) (keyLen outLen : Nat)
    (keySampler : Fin cardK → Bytes) (maskSampler : Fin cardY → Bytes)
    (decodePair : Bytes → F × F)
    (hDecode : ∀ i : Fin cardY, decodePair (maskSampler i) = pairEnum.toFun i)
    (hU : UniformOn (Spec.PrfSampleOk keyLen 0 outLen) (prgPrfSampler keySampler maskSampler))
    {𝒜 : Code byteOracleIface Bool → Prop} {εPrf : Spec.RatBound}
    (hPrf : Spec.PrfHard 𝒜 prg keyLen 0 outLen 1 εPrf)
    (adv : Fin nA → PooledCheckAdv F)
    (h𝒜 : ∀ (alpha : F) (a : Fin nA), 𝒜 (pooledBlindPrfDistinguisher decodePair alpha (adv a))) :
    GameBound
      (AdvDist (pooledCheckRealGame hPos enum prg keySampler decodePair adv)
        (pooledCheckSimGame hPos pairEnum adv))
      (εPrf.add ⟨1, cardF, hF⟩) := by
  refine coordGame_blinded_view_bound hPos hF prg keyLen outLen keySampler maskSampler hU hPrf
    (fun ca a y => (adv a).guess (pooledRealView (adv a) (enum.toFun ca) (decodePair y)))
    (fun cy a => (adv a).guess (pooledSimView (adv a) (pairEnum.toFun cy)))
    (fun ca a => h𝒜 (enum.toFun ca) a)
    (fun ca a => decide (¬ ((adv a).deltaX = zero ∧ (adv a).deltaM = zero) ∧
      sub (mul (adv a).deltaX (enum.toFun ca)) (adv a).deltaM = zero))
    ?_ (fun a => zero_defect_bad_coins_le_one enum (adv a).deltaX (adv a).deltaM)
  intro ca a hb
  have hNot : ¬ (¬ ((adv a).deltaX = zero ∧ (adv a).deltaM = zero) ∧
      sub (mul (adv a).deltaX (enum.toFun ca)) (adv a).deltaM = zero) := of_decide_eq_false hb
  have hRw : ∀ cy : Fin cardY,
      (if (adv a).guess (pooledRealView (adv a) (enum.toFun ca)
        (decodePair (maskSampler cy))) then 1 else 0) =
      (if (adv a).guess (pooledRealView (adv a) (enum.toFun ca)
        (pairEnum.toFun cy)) then 1 else 0) := fun cy => by rw [hDecode]
  refine (qsum_congr hRw).trans ?_
  by_cases hHon : (adv a).deltaX = zero ∧ (adv a).deltaM = zero
  · refine Eq.trans (qsum_congr (fun cy => ?_))
      ((qsum_bijection_invariant pairEnum
        (SimpleEquiv.prodCongr (ringAddEquiv (adv a).corruptMask) (SimpleEquiv.refl F))
        (fun p => if (adv a).guess (p.1, (adv a).productError p.1) then 1 else 0)).trans
        (qsum_congr (fun cy => ?_)))
    · rw [pooledRealView_unshifted (adv a) hHon.1 hHon.2]
      rfl
    · have hS : pooledSimView (adv a) (pairEnum.toFun cy) =
          ((pairEnum.toFun cy).1, (adv a).productError (pairEnum.toFun cy).1) :=
        iteOfPos hHon _ _
      rw [hS]
  · have hd : sub (mul (adv a).deltaX (enum.toFun ca)) (adv a).deltaM ≠ zero :=
      fun h0 => hNot ⟨hHon, h0⟩
    refine Eq.trans (qsum_congr (fun cy => ?_))
      ((qsum_bijection_invariant pairEnum
        (pooledViewEquiv (adv a).corruptMask (adv a).corruptRandomizer _
          (adv a).productError hd)
        (fun v => if (adv a).guess v then 1 else 0)).trans (qsum_congr (fun cy => ?_)))
    · rfl
    · have hS : pooledSimView (adv a) (pairEnum.toFun cy) = pairEnum.toFun cy :=
        iteOfNeg hHon _ _
      rw [hS]

theorem partySum_succ {F : Type} [LawfulCommRing F] (n : Nat) (s : Nat → F) :
    partySum (n + 1) s = add (partySum n s) (s n) := by rfl

/-- **The pooled execution has the modelled view (`blind_open_ext2_pooled`).** Run the pooled
    round among `n + 1` parties, party `n` honest, on share vectors whose residual shares sum to
    `Δx · α − Δm` and whose triple correlation is off by an additive `err`; let the corrupt
    parties shift the product opening by `shift e` after seeing `e`. The opened pair is
    `pooledRealView` at the honest shares `(a_n, r_n)`, for the adversary whose corrupt sums
    are the first `n` parties' shares and whose deviation is `e ↦ shift e − err`. -/
theorem pooledSub_execution_view {F : Type} [LawfulCommRing F] (n : Nat)
    (rSh aSh cSh dSh : Nat → F) (deltaX deltaM alpha err : F) (shift : F → F)
    (guess : F × F → Bool)
    (hD : partySum (n + 1) dSh = sub (mul deltaX alpha) deltaM)
    (hC : partySum (n + 1) cSh =
      add (mul (partySum (n + 1) rSh) (partySum (n + 1) aSh)) err) :
    (pooledMaskedOpen (n + 1) dSh aSh,
      add (pooledBlindOpenSub (n + 1) rSh cSh (pooledMaskedOpen (n + 1) dSh aSh))
        (shift (pooledMaskedOpen (n + 1) dSh aSh))) =
    pooledRealView
      { deltaX := deltaX, deltaM := deltaM, corruptMask := partySum n aSh,
        corruptRandomizer := partySum n rSh, productError := fun e => sub (shift e) err,
        guess := guess } alpha (aSh n, rSh n) := by
  have hE : pooledMaskedOpen (n + 1) dSh aSh =
      add (add (aSh n) (sub (mul deltaX alpha) deltaM)) (partySum n aSh) := by
    rw [pooledMaskedOpen_eq, hD, partySum_succ]
    constructive_ring
  have hW : add (pooledBlindOpenSub (n + 1) rSh cSh (pooledMaskedOpen (n + 1) dSh aSh))
        (shift (pooledMaskedOpen (n + 1) dSh aSh)) =
      add (mul (add (rSh n) (partySum n rSh)) (sub (mul deltaX alpha) deltaM))
        (sub (shift (add (add (aSh n) (sub (mul deltaX alpha) deltaM)) (partySum n aSh))) err) := by
    rw [hE, pooledBlindOpenSub_eq, hC, partySum_succ n rSh, partySum_succ n aSh]
    constructive_ring
  exact Prod.ext hE hW

/-- **The pooled execution has the modelled view in characteristic `2` (`blind_open_pooled`).**
    As `pooledSub_execution_view` for the product opening `w = Σ_p (r_p · e + c_p)`; the
    deviation of the modelled adversary is `e ↦ shift e + err`. -/
theorem pooledAdd_execution_view {F : Type} [LawfulCommRing F] (hChar : ∀ x : F, add x x = zero)
    (n : Nat) (rSh aSh cSh dSh : Nat → F) (deltaX deltaM alpha err : F) (shift : F → F)
    (guess : F × F → Bool)
    (hD : partySum (n + 1) dSh = sub (mul deltaX alpha) deltaM)
    (hC : partySum (n + 1) cSh =
      add (mul (partySum (n + 1) rSh) (partySum (n + 1) aSh)) err) :
    (pooledMaskedOpen (n + 1) dSh aSh,
      add (pooledBlindOpenAdd (n + 1) rSh cSh (pooledMaskedOpen (n + 1) dSh aSh))
        (shift (pooledMaskedOpen (n + 1) dSh aSh))) =
    pooledRealView
      { deltaX := deltaX, deltaM := deltaM, corruptMask := partySum n aSh,
        corruptRandomizer := partySum n rSh, productError := fun e => add (shift e) err,
        guess := guess } alpha (aSh n, rSh n) := by
  have hE : pooledMaskedOpen (n + 1) dSh aSh =
      add (add (aSh n) (sub (mul deltaX alpha) deltaM)) (partySum n aSh) := by
    rw [pooledMaskedOpen_eq, hD, partySum_succ]
    constructive_ring
  have hW : add (pooledBlindOpenAdd (n + 1) rSh cSh (pooledMaskedOpen (n + 1) dSh aSh))
        (shift (pooledMaskedOpen (n + 1) dSh aSh)) =
      add (mul (add (rSh n) (partySum n rSh)) (sub (mul deltaX alpha) deltaM))
        (add (shift (add (add (aSh n) (sub (mul deltaX alpha) deltaM)) (partySum n aSh))) err) := by
    rw [hE, pooledBlindOpenAdd_eq, hC, partySum_succ n rSh, partySum_succ n aSh]
    have h : add (add (mul (add (partySum n rSh) (rSh n))
          (add (add (aSh n) (sub (mul deltaX alpha) deltaM)) (partySum n aSh)))
          (add (mul (add (partySum n rSh) (rSh n)) (add (partySum n aSh) (aSh n))) err))
          (shift (add (add (aSh n) (sub (mul deltaX alpha) deltaM)) (partySum n aSh))) =
        add (add (mul (add (rSh n) (partySum n rSh)) (sub (mul deltaX alpha) deltaM))
          (add (shift (add (add (aSh n) (sub (mul deltaX alpha) deltaM)) (partySum n aSh))) err))
          (add (mul (add (partySum n rSh) (rSh n)) (add (partySum n aSh) (aSh n)))
            (mul (add (partySum n rSh) (rSh n)) (add (partySum n aSh) (aSh n)))) := by
      constructive_ring
    rw [h, hChar, LawfulCommRing.add_zero]
  exact Prod.ext hE hW

/-- Pairs of `Tower128` elements indexed by the 32-byte coin space `Fin (256 ^ 32)`. -/
def tower128PairByteEnum : SimpleEquiv (Fin (256 ^ 32)) (Tower128 × Tower128) :=
  SimpleEquiv.trans (finCastEquiv (by decide : 256 ^ 32 = 256 ^ 16 * 256 ^ 16))
    (SimpleEquiv.trans (finMulProdEquiv (256 ^ 16) (256 ^ 16) (by decide))
      (SimpleEquiv.prodCongr tower128ByteEnum tower128ByteEnum))

/-- Decode 32 bytes of the honest party's stream to its mask share and randomizer share. -/
def tower128DecodePair (bs : Bytes) : Tower128 × Tower128 :=
  tower128PairByteEnum.toFun (bytesToFin 32 bs)

theorem tower128DecodePair_bytesSampler (i : Fin (256 ^ 32)) :
    tower128DecodePair (bytesSampler 32 i) = tower128PairByteEnum.toFun i := by
  show tower128PairByteEnum.toFun (bytesToFin 32 (bytesSampler 32 i)) =
    tower128PairByteEnum.toFun i
  rw [bytesToFin_bytesSampler]

/-- **One pooled `Tower128` blinding round with a 32-byte seed.** The honest mask and
    randomizer shares are 32 bytes of `prg seed []`. Against every family of pooled-round
    adversaries, if `prg` is a one-query PRF at input length `0` against all one-query
    distinguishers with advantage `εPrf`, the view `(e, w)` is within `εPrf + 2⁻¹²⁸` of the
    simulator. -/
theorem computational_pooledBlind_tower128_security_bound {nA : Nat}
    (hPos : 0 < (256 ^ 32 * 256 ^ 32) * (256 ^ 16 * nA))
    (prg : Bytes → Bytes → Bytes)
    {εPrf : Spec.RatBound}
    (hPrf : Spec.PrfHard (fun c => Spec.Within 1 c) prg 32 0 32 1 εPrf)
    (adv : Fin nA → PooledCheckAdv Tower128) :
    GameBound
      (AdvDist (pooledCheckRealGame hPos tower128ByteEnum prg (bytesSampler 32) tower128DecodePair adv)
        (pooledCheckSimGame hPos tower128PairByteEnum adv))
      (εPrf.add (Spec.RatBound.invPow2 128)) :=
  Spec.GameBound.trans
    (computational_pooledBlind_security_bound hPos (pow256_pos 16) tower128ByteEnum
      tower128PairByteEnum prg 32 32 (bytesSampler 32) (bytesSampler 32) tower128DecodePair
      tower128DecodePair_bytesSampler
      (uniformOn_prgPrfSampler (uniformOn_bytesSampler 32) (uniformOn_bytesSampler 32))
      hPrf adv (fun alpha a => pooledBlindPrfDistinguisher_within tower128DecodePair alpha (adv a)))
    (Spec.RatBound.add_le_add (Spec.RatBound.le_refl εPrf)
      (by show 1 * 2 ^ 128 ≤ 1 * 256 ^ 16; decide))

#verify_constructive
  Qsag.MacBlind.qsum_eq_sampleSum
  Qsag.MacBlind.qsum_coinSplit
  Qsag.MacBlind.coordGame_win_pair
  Qsag.MacBlind.fibreWinCount_eq
  Qsag.MacBlind.coordGame_winCount
  Qsag.MacBlind.coordGame_advDist_le_inv_card
  Qsag.MacBlind.prgOutputTest_within
  Qsag.MacBlind.prgOutputTest_play
  Qsag.MacBlind.prgPrfSampler_fst
  Qsag.MacBlind.prgPrfSampler_snd_nil
  Qsag.MacBlind.uniformOn_prgPrfSampler
  Qsag.MacBlind.coordGame_prf_hop
  Qsag.MacBlind.macBlindPrfDistinguisher_within
  Qsag.MacBlind.blindedCheckOpening_unshifted
  Qsag.MacBlind.zero_defect_key_unique
  Qsag.MacBlind.macCheck_real_ideal_prf_bound
  Qsag.MacBlind.macCheck_ideal_sim_bound
  Qsag.MacBlind.computational_macBlind_spdz_security_bound
  Qsag.MacBlind.cancellingAdv_opening_zero
  Qsag.MacBlind.tooth_constant_prg_real_always_wins
  Qsag.MacBlind.cancellingAdv_sim_winCount
  Qsag.MacBlind.tooth_constant_prg_breaks_blinding
  Qsag.MacBlind.tooth_constant_prg_not_prfHard
  Qsag.MacBlind.tooth_unblinded_defect_separates_keys
  Qsag.MacBlind.leBytes_length
  Qsag.MacBlind.leValue_leBytes
  Qsag.MacBlind.leValue_lt
  Qsag.MacBlind.leBytes_leValue
  Qsag.MacBlind.uniformOn_bytesSampler
  Qsag.MacBlind.bytesToFin_bytesSampler
  Qsag.MacBlind.tower128DecodeMask_bytesSampler
  Qsag.MacBlind.prfHard_one
  Qsag.MacBlind.computational_macBlind_tower128_security_bound
  Qsag.MacBlind.tower128_single_coin_space_pos
  Qsag.MacBlind.tooth_constant_prg_breaks_tower128_blinding
  Qsag.MacBlind.inhabited_computational_macBlind_tower128
  Qsag.MacBlind.partySum_add
  Qsag.MacBlind.partySum_sub
  Qsag.MacBlind.partySum_mul_right
  Qsag.MacBlind.pooledMaskedOpen_eq
  Qsag.MacBlind.pooledBlindOpenSub_eq
  Qsag.MacBlind.pooledBlindOpenAdd_eq
  Qsag.MacBlind.pooledBlindOpenSub_faulty
  Qsag.MacBlind.pooledBlindOpenSub_correct
  Qsag.MacBlind.pooledBlindOpenAdd_faulty
  Qsag.MacBlind.tower128_add_self
  Qsag.MacBlind.pooledBlindOpenAdd_correct_tower128
  Qsag.MacBlind.affineBlindEquiv_toFun
  Qsag.MacBlind.faultyTriple_opening_uniform
  Qsag.MacBlind.faultyTriple_unshifted_check_aborts
  Qsag.MacBlind.coordGame_blinded_view_bound
  Qsag.MacBlind.zero_defect_bad_coins_le_one
  Qsag.MacBlind.oleBlindedOpening_eq
  Qsag.MacBlind.oleSimulatedOpening_eq
  Qsag.MacBlind.oleBlindedOpening_unshifted
  Qsag.MacBlind.macBlindOlePrfDistinguisher_within
  Qsag.MacBlind.computational_macBlind_ole_error_security_bound
  Qsag.MacBlind.pooledRealView_eq
  Qsag.MacBlind.pooledSimView_eq
  Qsag.MacBlind.pooledRealView_unshifted
  Qsag.MacBlind.pooledBlindPrfDistinguisher_within
  Qsag.MacBlind.computational_pooledBlind_security_bound
  Qsag.MacBlind.partySum_succ
  Qsag.MacBlind.pooledSub_execution_view
  Qsag.MacBlind.pooledAdd_execution_view
  Qsag.MacBlind.tower128DecodePair_bytesSampler
  Qsag.MacBlind.computational_pooledBlind_tower128_security_bound

#tooth_pair computational_macBlind_spdz_security_bound vs tooth_constant_prg_breaks_blinding
#tooth_pair computational_macBlind_spdz_security_bound vs tooth_unblinded_mac_residual_recovers_alpha
#tooth_pair computational_macBlind_tower128_security_bound vs tooth_constant_prg_breaks_tower128_blinding

end Qsag.MacBlind
end
