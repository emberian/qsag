module
/-
# Qsag.Protocol.Threshold.MacBlind — Multiplicative SPDZ MAC-Residual Blinding (`L-Ex-14`)

Constructive field-permutation soundness, zero-leakage abort privacy, concrete field
instantiations (`GoldilocksExt2`, `Tower128`, `Gf2Pow128`), 3-projection Boolean MAC blinding,
and adaptive `combine_arity` hypergeometric bucket bounds for QSAG's preprocessing layer:

1. **Ideal-OLE Multiplicative MAC Blinding (`macBlind_uniform_of_nonzero_defect`):**
   Over any finite field `F` (`[LawfulField F]`), for nonzero MAC defect
   `d = Δ_x · α − Δ_m ≠ 0` and uniform honest randomizer `r_h ∈ F` independent of
   `(d, r_corrupt, err, α)`, the blinded opening `w = (r_h + r_corrupt) · d + err` is a
   constructive `SimpleEquiv F F` with explicit inverse `w ↦ (w − err) · d⁻¹ − r_corrupt`.
   Hence `w` is uniform over `F` and hits `0` on **exactly `1` out of `|F|`** honest randomizers.
2. **Exact Zero-Leakage Abort Across All `(t, n)` (`macBlind_abort_independent_of_alpha`):**
   In the pure multiplicative residual check `w = (r_h + r_corrupt) · d`, for any two nonzero
   defects `d₁, d₂ ≠ 0` (induced by any two candidate persistent MAC keys `α₁, α₂` consistent
   with an adversarial shift `Δ_x ≠ 0, Δ_m`), the rescaling bijection
   `r_h ↦ (r_h + r_corrupt) · (d₂ · d₁⁻¹) − r_corrupt` maps `-r_corrupt ↦ -r_corrupt` (`w = 0`)
   and bijects `F \ {-r_corrupt}` onto `F \ {-r_corrupt}` with identical nonzero output `w`.
   Every observable of `(abort?, w)` has **zero statistical distance** between `α₁` and `α₂`,
   including at unanimous dishonest majority `t = n`.
3. **Concrete Instantiations (`GoldilocksExt2`, `Tower128`, `Gf2Pow128`):**
   - `GoldilocksExt2` (`|F| = p^2 > 2^127`, 640-bit disposable choice LHL margin `384 ≥ 256`).
   - `Tower128` and polynomial-basis `Gf2Pow128` (`|F| = 2^128`), plus 2-round independent
     blinding (`macBlindTwoRoundOpen`) with exact false-accept count `1` out of `2^256` (`2^-256`).
4. **3-Projection Boolean MAC Blinding & Adaptive `combineArity` (`POOL_WORDS = 8192`):**
   - Constructive `Nat` proof that `(q ^ 2 + q - 1) ^ 3 < q ^ 7` for all `2 ≤ q`
     (`(1/q + (1 - 1/q)/q^2)^3 < 1/q^2`), instantiated at `q = 2^64` and `q = 2^128`.
   - Unconditional single-projection coin bound (`≤ q^2 + q - 1` out of `q^3` per active coordinate).
   - `tripleF2PoolWords = 8192` (`524288` bits) and `combineArity` hypergeometric bound
     `outBits * 2 ^ 40 ≤ chooseNat (f * (outBits + 1)) f`, proving `f = 3` at `8192` words,
     `f = 4` (with `f = 3` failing) at `7720` words, universal `2 ≤ combineArity outBits ≤ 7`
     for all `outBits ≥ 64`, and hypergeometric distinct-tuple soundness + discarded-bucket tooth.
-/

public import Qsag.Oracle.FrozenChallengeGame
public import Qsag.Math.Goldilocks
public import Qsag.Math.Gf2Pow128
public import Qsag.Math.Tactic.CommRing
public import Qsag.Math.Tactic.MaskBijection

public section

namespace Qsag.MacBlind

open Qsag.FrozenChallenge CommRingOps

set_option autoImplicit false

/-! ## 1. Ideal-OLE Multiplicative SPDZ MAC-Residual Blinding & Zero-Leakage Abort -/

/-- SPDZ MAC defect `d = Δ_x · α − Δ_m` induced by additive value shift `Δ_x` and MAC shift `Δ_m`
    against persistent global MAC key `α`. -/
def spdzMacDefect {F : Type} [LawfulCommRing F] (deltaX alpha deltaM : F) : F :=
  sub (mul deltaX alpha) deltaM

/-- Multiplicatively blinded MAC-residual opening `w = (r_honest + r_corrupt) · d + err`
    with honest randomizer `r_honest`, sum of corrupt randomizers `r_corrupt`, MAC defect `d`,
    and post-OLE additive offset `err`. -/
def macBlindOpen {F : Type} [LawfulCommRing F] (rHonest rCorrupt d err : F) : F :=
  add (mul (add rHonest rCorrupt) d) err

/-- Pure multiplicative MAC-residual opening `w = (r_honest + r_corrupt) · d` (`err = 0`). -/
def macBlindPure {F : Type} [LawfulCommRing F] (rHonest rCorrupt d : F) : F :=
  mul (add rHonest rCorrupt) d

theorem macBlindPure_eq_open_zero {F : Type} [LawfulCommRing F] (rHonest rCorrupt d : F) :
    macBlindPure rHonest rCorrupt d = macBlindOpen rHonest rCorrupt d zero := by
  unfold macBlindPure macBlindOpen
  exact (LawfulCommRing.add_zero _).symm

/-- Explicit inverse `w ↦ (w − err) · d⁻¹ − r_corrupt` of `macBlindOpen · rCorrupt d err`. -/
def macBlindInv {F : Type} [LawfulField F] (rCorrupt d err w : F) : F :=
  sub (mul (sub w err) (LawfulField.inv d)) rCorrupt

/-- **Constructive Field Permutation (`macBlindEquiv`)**:
    For any nonzero defect `d ≠ 0`, `r_h ↦ (r_h + r_corrupt) · d + err` is a constructive
    bijection `F ≃ F` (`0 Classical.choice`). -/
def macBlindEquiv {F : Type} [LawfulField F] (rCorrupt d err : F) (hd : d ≠ zero) :
    SimpleEquiv F F where
  toFun rH := macBlindOpen rH rCorrupt d err
  invFun w := macBlindInv rCorrupt d err w
  left_inv rH := by
    unfold macBlindOpen macBlindInv
    rw [ring_add_sub_cancel_right, LawfulCommRing.mul_assoc,
        LawfulField.mul_inv_cancel hd, LawfulCommRing.mul_one,
        ring_add_sub_cancel_right]
  right_inv w := by
    unfold macBlindOpen macBlindInv
    rw [ring_sub_add_cancel_right, LawfulCommRing.mul_assoc,
        LawfulCommRing.mul_comm (LawfulField.inv d) d,
        LawfulField.mul_inv_cancel hd, LawfulCommRing.mul_one,
        ring_sub_add_cancel_right]

theorem macBlindOpen_injective {F : Type} [LawfulField F] {rCorrupt d err : F} (hd : d ≠ zero)
    {r₁ r₂ : F} (hEq : macBlindOpen r₁ rCorrupt d err = macBlindOpen r₂ rCorrupt d err) :
    r₁ = r₂ := by
  let e := macBlindEquiv rCorrupt d err hd
  have hTo : e.toFun r₁ = e.toFun r₂ := hEq
  have hInv := congrArg e.invFun hTo
  rwa [e.left_inv, e.left_inv] at hInv

/-- Exact indicator sum over any finite carrier enumerated by `SimpleEquiv (Fin cardF) Ω`:
    every target element `target : Ω` is hit **exactly once**. -/
theorem qsum_enum_eq_target {Ω : Type} [DecidableEq Ω] {cardF : Nat}
    (enum : SimpleEquiv (Fin cardF) Ω) (target : Ω) :
    qsum cardF (fun i => if enum.toFun i = target then 1 else 0) = 1 := by
  have hCongr :
      qsum cardF (fun i => if enum.toFun i = target then 1 else 0) =
      qsum cardF (fun i => if i = enum.invFun target then 1 else 0) := by
    apply qsum_congr
    intro i
    by_cases h : i = enum.invFun target
    · subst h
      simp only [enum.right_inv, ↓reduceIte]
    · have ht : enum.toFun i ≠ target := fun he => h (by rw [← he, enum.left_inv])
      simp only [h, ht, ↓reduceIte]
  rw [hCongr]
  exact qsum_eq_indicator cardF (enum.invFun target)

/-- **Ideal-OLE Multiplicative MAC Blinding Uniformity & `1 / |F|` Soundness
    (`macBlind_uniform_of_nonzero_defect`)**:
    For any finite field `F` enumerated by `enum : SimpleEquiv (Fin cardF) F` and any nonzero
    MAC defect `d ≠ 0`:
    1. For every weight `g : F → Nat`, `macBlindOpen (enum.toFun i) rCorrupt d err` has the exact
       uniform expectation `qsum cardF (g ∘ enum.toFun)`.
    2. Every field element `target : F` occurs with exact multiplicity `1`.
    3. In particular, the false-acceptance event `w = 0` occurs on **exactly `1` out of `cardF`**
       honest randomizers (`Pr[w = 0] = 1 / |F|`). -/
theorem macBlind_uniform_of_nonzero_defect {F : Type} [LawfulField F] [DecidableEq F]
    {cardF : Nat} (enum : SimpleEquiv (Fin cardF) F)
    (rCorrupt d err : F) (hd : d ≠ zero) :
    (∀ g : F → Nat,
      qsum cardF (fun i => g (macBlindOpen (enum.toFun i) rCorrupt d err)) =
        qsum cardF (fun i => g (enum.toFun i))) ∧
    (∀ target : F,
      qsum cardF (fun i => if macBlindOpen (enum.toFun i) rCorrupt d err = target then 1 else 0) = 1) ∧
    qsum cardF (fun i => if macBlindOpen (enum.toFun i) rCorrupt d err = zero then 1 else 0) = 1 := by
  have hUnif : ∀ g : F → Nat,
      qsum cardF (fun i => g (macBlindOpen (enum.toFun i) rCorrupt d err)) =
        qsum cardF (fun i => g (enum.toFun i)) :=
    fun g => qsum_bijection_invariant enum (macBlindEquiv rCorrupt d err hd) g
  have hHit : ∀ target : F,
      qsum cardF (fun i => if macBlindOpen (enum.toFun i) rCorrupt d err = target then 1 else 0) = 1 := by
    intro target
    rw [hUnif (fun w => if w = target then 1 else 0)]
    exact qsum_enum_eq_target enum target
  exact ⟨hUnif, hHit, hHit zero⟩

/-- Over any duplicate-free list `xs : List F`, a nonzero defect `d ≠ 0` is falsely accepted by at
    most `1` honest randomizer in `xs`. -/
theorem macBlind_nodup_zero_count_le_one {F : Type} [LawfulField F] [DecidableEq F]
    (xs : List F) (hnd : xs.Nodup) (rCorrupt d err : F) (hd : d ≠ zero) :
    countIf (fun rH => decide (macBlindOpen rH rCorrupt d err = zero)) xs ≤ 1 := by
  apply countIf_le_one_of_unique hnd
  intro r₁ r₂ h₁ h₂
  exact macBlindOpen_injective hd ((of_decide_eq_true h₁).trans (of_decide_eq_true h₂).symm)

/-- Honest completeness of pure multiplicative blinding: when `d = 0`, `macBlindPure` opens `0`
    for every `(rHonest, rCorrupt)`. -/
theorem macBlindPure_zero_defect_complete {F : Type} [LawfulCommRing F] (rHonest rCorrupt : F) :
    macBlindPure rHonest rCorrupt zero = zero :=
  LawfulCommRing.mul_zero _

/-- Constructive randomizer-rescaling bijection `r_h ↦ (r_h + r_corrupt) · (d₂ · d₁⁻¹) − r_corrupt`
    transporting defect `d₁ ≠ 0` to `d₂ ≠ 0` while fixing the unique zero-opening point `-r_corrupt`. -/
def macBlindRescaleEquiv {F : Type} [LawfulField F] (rCorrupt d₁ d₂ : F)
    (hd₁ : d₁ ≠ zero) (hd₂ : d₂ ≠ zero) : SimpleEquiv F F :=
  SimpleEquiv.trans (macBlindEquiv rCorrupt d₂ zero hd₂)
    (SimpleEquiv.symm (macBlindEquiv rCorrupt d₁ zero hd₁))

theorem macBlindPure_rescale_eq {F : Type} [LawfulField F] (rCorrupt d₁ d₂ : F)
    (hd₁ : d₁ ≠ zero) (hd₂ : d₂ ≠ zero) (rH : F) :
    macBlindPure ((macBlindRescaleEquiv rCorrupt d₁ d₂ hd₁ hd₂).toFun rH) rCorrupt d₁ =
      macBlindPure rH rCorrupt d₂ := by
  rw [macBlindPure_eq_open_zero, macBlindPure_eq_open_zero]
  exact (macBlindEquiv rCorrupt d₁ zero hd₁).right_inv
    ((macBlindEquiv rCorrupt d₂ zero hd₂).toFun rH)

theorem macBlindPure_eq_zero_iff {F : Type} [LawfulField F] (rH rCorrupt d : F) (hd : d ≠ zero) :
    macBlindPure rH rCorrupt d = zero ↔ rH = neg rCorrupt := by
  unfold macBlindPure
  constructor
  · intro hZero
    have hAdd : add rH rCorrupt = zero := by
      calc add rH rCorrupt
          = mul (add rH rCorrupt) one := (LawfulCommRing.mul_one _).symm
        _ = mul (add rH rCorrupt) (mul d (LawfulField.inv d)) := by
            rw [LawfulField.mul_inv_cancel hd]
        _ = mul (mul (add rH rCorrupt) d) (LawfulField.inv d) := by
            rw [← LawfulCommRing.mul_assoc]
        _ = mul zero (LawfulField.inv d) := by rw [hZero]
        _ = zero := LawfulCommRing.zero_mul _
    exact LawfulCommRing.add_left_cancel
      ((LawfulCommRing.add_comm rCorrupt rH).trans
        (hAdd.trans (LawfulCommRing.add_right_neg rCorrupt).symm))
  · rintro rfl
    rw [LawfulCommRing.add_left_neg, LawfulCommRing.zero_mul]

/-- **Exact Zero-Leakage Abort Independence (`macBlind_abort_independent_of_alpha`)**:
    For ANY two nonzero defects `d₁, d₂ ≠ 0`:
    1. Every joint observable `obs : Bool × F → Nat` of `(decide (w ≠ 0), w)` (including both the
       abort indicator and the conditional distribution of `w` given abort `w ≠ 0`) has **identical**
       sum over uniform `r_h ∈ F`, hence `natAbsDiff = 0` (`0`-bit statistical leakage).
    2. The abort event `w ≠ 0` occurs on `cardF - 1` of the `cardF` honest randomizers, and on abort
       every nonzero `target ≠ 0` is hit **exactly once** (uniform on `F \ {0}`). -/
theorem macBlind_abort_independent_of_alpha {F : Type} [LawfulField F] [DecidableEq F]
    {cardF : Nat} (enum : SimpleEquiv (Fin cardF) F)
    (rCorrupt d₁ d₂ : F) (hd₁ : d₁ ≠ zero) (hd₂ : d₂ ≠ zero) :
    (∀ obs : Bool × F → Nat,
      qsum cardF (fun i =>
        let w := macBlindPure (enum.toFun i) rCorrupt d₁
        obs (decide (w ≠ zero), w)) =
      qsum cardF (fun i =>
        let w := macBlindPure (enum.toFun i) rCorrupt d₂
        obs (decide (w ≠ zero), w))) ∧
    (∀ obs : Bool × F → Nat,
      natAbsDiff
        (qsum cardF (fun i =>
          let w := macBlindPure (enum.toFun i) rCorrupt d₁
          obs (decide (w ≠ zero), w)))
        (qsum cardF (fun i =>
          let w := macBlindPure (enum.toFun i) rCorrupt d₂
          obs (decide (w ≠ zero), w))) = 0) ∧
    qsum cardF (fun i => if macBlindPure (enum.toFun i) rCorrupt d₁ ≠ zero then 1 else 0) + 1 =
      cardF ∧
    (∀ target : F, target ≠ zero →
      qsum cardF (fun i =>
        let w := macBlindPure (enum.toFun i) rCorrupt d₁
        if w ≠ zero ∧ w = target then 1 else 0) = 1) := by
  have hJoint : ∀ obs : Bool × F → Nat,
      qsum cardF (fun i =>
        let w := macBlindPure (enum.toFun i) rCorrupt d₁
        obs (decide (w ≠ zero), w)) =
      qsum cardF (fun i =>
        let w := macBlindPure (enum.toFun i) rCorrupt d₂
        obs (decide (w ≠ zero), w)) := by
    intro obs
    refine qsum_bijection_hop_eq enum (macBlindRescaleEquiv rCorrupt d₁ d₂ hd₁ hd₂)
      (fun rH => let w := macBlindPure rH rCorrupt d₁; obs (decide (w ≠ zero), w))
      (fun rH => let w := macBlindPure rH rCorrupt d₂; obs (decide (w ≠ zero), w)) ?_
    intro rH
    dsimp only
    rw [macBlindPure_rescale_eq rCorrupt d₁ d₂ hd₁ hd₂ rH]
  have hZeroDist : ∀ obs : Bool × F → Nat,
      natAbsDiff
        (qsum cardF (fun i =>
          let w := macBlindPure (enum.toFun i) rCorrupt d₁
          obs (decide (w ≠ zero), w)))
        (qsum cardF (fun i =>
          let w := macBlindPure (enum.toFun i) rCorrupt d₂
          obs (decide (w ≠ zero), w))) = 0 := by
    intro obs
    rw [hJoint obs, natAbsDiff_eq]
    simp
  have hSplit :
      qsum cardF (fun i => if macBlindPure (enum.toFun i) rCorrupt d₁ ≠ zero then 1 else 0) +
      qsum cardF (fun i => if macBlindPure (enum.toFun i) rCorrupt d₁ = zero then 1 else 0) =
      qsum cardF (fun _ => 1) := by
    rw [← qsum_add]
    apply qsum_congr
    intro i
    by_cases hz : macBlindPure (enum.toFun i) rCorrupt d₁ = zero <;> simp [hz]
  have hZeroHit :
      qsum cardF (fun i => if macBlindPure (enum.toFun i) rCorrupt d₁ = zero then 1 else 0) = 1 := by
    have hCongr :
        qsum cardF (fun i => if macBlindPure (enum.toFun i) rCorrupt d₁ = zero then 1 else 0) =
        qsum cardF (fun i => if macBlindOpen (enum.toFun i) rCorrupt d₁ zero = zero then 1 else 0) :=
      qsum_congr (fun i => by rw [macBlindPure_eq_open_zero])
    rw [hCongr]
    exact (macBlind_uniform_of_nonzero_defect enum rCorrupt d₁ zero hd₁).2.2
  rw [hZeroHit, qsum_const, Nat.mul_one] at hSplit
  refine ⟨hJoint, hZeroDist, hSplit, ?_⟩
  intro target hTargetNz
  have hTargetEq :
      qsum cardF (fun i =>
        let w := macBlindPure (enum.toFun i) rCorrupt d₁
        if w ≠ zero ∧ w = target then 1 else 0) =
      qsum cardF (fun i => if macBlindOpen (enum.toFun i) rCorrupt d₁ zero = target then 1 else 0) := by
    apply qsum_congr
    intro i
    dsimp only
    rw [macBlindPure_eq_open_zero]
    by_cases hw : macBlindOpen (enum.toFun i) rCorrupt d₁ zero = target
    · rw [hw]
      simp [hTargetNz]
    · simp [hw]
  rw [hTargetEq]
  exact (macBlind_uniform_of_nonzero_defect enum rCorrupt d₁ zero hd₁).2.1 target

theorem spdzMacDefect_ne_zero_of_key_ne {F : Type} [LawfulField F]
    {deltaX alpha deltaM : F} (hDx : deltaX ≠ zero)
    (hAlpha : alpha ≠ mul deltaM (LawfulField.inv deltaX)) :
    spdzMacDefect deltaX alpha deltaM ≠ zero := by
  intro hZero
  apply hAlpha
  have hEq : mul deltaX alpha = deltaM := LawfulCommRing.sub_eq_zero_iff.mp hZero
  calc alpha
      = mul alpha one := (LawfulCommRing.mul_one alpha).symm
    _ = mul alpha (mul deltaX (LawfulField.inv deltaX)) := by
        rw [LawfulField.mul_inv_cancel hDx]
    _ = mul (mul deltaX alpha) (LawfulField.inv deltaX) := by
        rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm alpha deltaX]
    _ = mul deltaM (LawfulField.inv deltaX) := by rw [hEq]

/-- **SPDZ Persistent MAC Key `α` Zero-Leakage Under Dishonest-Majority Abort (`macBlind_spdz_alpha_zero_leakage`)**:
    For any nonzero adversarial value shift `Δ_x ≠ 0`, any MAC shift `Δ_m`, any corrupt randomizer
    sum `r_corrupt` (even when `n - 1` of `n` parties are corrupt at `t = n`), and any two candidate
    persistent MAC keys `α₁, α₂` neither equal to the single guessed ratio `Δ_m · Δ_x⁻¹`,
    the blinded opening `(abort?, w)` has **identically equal distribution** under `α₁` and `α₂`. -/
theorem macBlind_spdz_alpha_zero_leakage {F : Type} [LawfulField F] [DecidableEq F]
    {cardF : Nat} (enum : SimpleEquiv (Fin cardF) F)
    (deltaX deltaM rCorrupt alpha₁ alpha₂ : F)
    (hDx : deltaX ≠ zero)
    (hAlpha₁ : alpha₁ ≠ mul deltaM (LawfulField.inv deltaX))
    (hAlpha₂ : alpha₂ ≠ mul deltaM (LawfulField.inv deltaX))
    (obs : Bool × F → Nat) :
    qsum cardF (fun i =>
      let w := macBlindPure (enum.toFun i) rCorrupt (spdzMacDefect deltaX alpha₁ deltaM)
      obs (decide (w ≠ zero), w)) =
    qsum cardF (fun i =>
      let w := macBlindPure (enum.toFun i) rCorrupt (spdzMacDefect deltaX alpha₂ deltaM)
      obs (decide (w ≠ zero), w)) :=
  (macBlind_abort_independent_of_alpha enum rCorrupt
    (spdzMacDefect deltaX alpha₁ deltaM)
    (spdzMacDefect deltaX alpha₂ deltaM)
    (spdzMacDefect_ne_zero_of_key_ne hDx hAlpha₁)
    (spdzMacDefect_ne_zero_of_key_ne hDx hAlpha₂)).1 obs

/-- **`#tooth` 1 (`tooth_unblinded_mac_residual_recovers_alpha`)**:
    Without multiplicative blinding (`macBlindPure` replaced by `spdzMacDefect`), an aborting
    shift `Δ_x ≠ 0` deterministically distinguishes any two candidate MAC keys `α₁ ≠ α₂`
    (`spdzMacDefect Δ_x α₁ Δ_m ≠ spdzMacDefect Δ_x α₂ Δ_m`) and recovers `α` in 1 query. -/
theorem tooth_unblinded_mac_residual_recovers_alpha {F : Type} [LawfulField F]
    (deltaX alpha₁ alpha₂ deltaM : F) (hDx : deltaX ≠ zero) (hNe : alpha₁ ≠ alpha₂) :
    ∃ invDx : F,
      mul (add (spdzMacDefect deltaX alpha₁ deltaM) deltaM) invDx = alpha₁ ∧
      spdzMacDefect deltaX alpha₁ deltaM ≠ spdzMacDefect deltaX alpha₂ deltaM := by
  refine ⟨LawfulField.inv deltaX, ?_, ?_⟩
  · unfold spdzMacDefect
    rw [ring_sub_add_cancel_right, LawfulCommRing.mul_comm deltaX alpha₁,
        LawfulCommRing.mul_assoc, LawfulField.mul_inv_cancel hDx, LawfulCommRing.mul_one]
  · intro hEq
    apply hNe
    unfold spdzMacDefect at hEq
    have hMulEq : mul deltaX alpha₁ = mul deltaX alpha₂ := by
      have hSub := congrArg (fun z => add z deltaM) hEq
      rwa [ring_sub_add_cancel_right, ring_sub_add_cancel_right] at hSub
    calc alpha₁
        = mul (LawfulField.inv deltaX) (mul deltaX alpha₁) := by
          rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm (LawfulField.inv deltaX) deltaX,
              LawfulField.mul_inv_cancel hDx, LawfulCommRing.one_mul]
      _ = mul (LawfulField.inv deltaX) (mul deltaX alpha₂) := by rw [hMulEq]
      _ = alpha₂ := by
          rw [← LawfulCommRing.mul_assoc, LawfulCommRing.mul_comm (LawfulField.inv deltaX) deltaX,
              LawfulField.mul_inv_cancel hDx, LawfulCommRing.one_mul]

/-- **`#tooth` 2 (`tooth_zero_randomizer_always_accepts_forged_mac`)**:
    If corrupt parties can cancel the honest randomizer (`r_honest = -r_corrupt`, e.g., when
    shares are opened sequentially without pre-open commitments), `macBlindPure` fails to abort
    (`decide (w ≠ 0) = false`) and accepts **every** forged MAC defect `d ≠ 0`. -/
theorem tooth_zero_randomizer_always_accepts_forged_mac {F : Type} [LawfulField F] [DecidableEq F]
    (rCorrupt d : F) (hd : d ≠ zero) :
    ∃ rH : F, d ≠ zero ∧ decide (macBlindPure rH rCorrupt d ≠ zero) = false := by
  refine ⟨neg rCorrupt, hd, ?_⟩
  have hz : macBlindPure (neg rCorrupt) rCorrupt d = zero :=
    (macBlindPure_eq_zero_iff (neg rCorrupt) rCorrupt d hd).mpr rfl
  simp [hz]

/-! ## 2. Concrete Field Enumerations (`GoldilocksExt2`, `Tower128`, `Gf2Pow128`) & 2-Round `2^-256` Bound -/

private theorem div_lt_of_lt_mul_constructive {n a b : Nat} (h : n < a * b) : n / b < a :=
  if hLt : n / b < a then hLt
  else False.elim <| Nat.lt_irrefl n <| calc
    n < a * b := h
    _ = b * a := Nat.mul_comm a b
    _ ≤ b * (n / b) := Nat.mul_le_mul_left b (Nat.le_of_not_lt hLt)
    _ ≤ b * (n / b) + n % b := Nat.le_add_right _ _
    _ = n := Nat.div_add_mod n b

/-- Constructive product enumeration `Fin (A * B) ≃ Fin A × Fin B` for `0 < B`. -/
def finMulProdEquiv (A B : Nat) (hB : 0 < B) : SimpleEquiv (Fin (A * B)) (Fin A × Fin B) where
  toFun i :=
    (⟨i.val / B, div_lt_of_lt_mul_constructive i.isLt⟩,
     ⟨i.val % B, Nat.mod_lt i.val hB⟩)
  invFun p :=
    ⟨p.2.val + B * p.1.val, by
      have h1 : p.1.val + 1 ≤ A := p.1.isLt
      have h2 : p.2.val < B := p.2.isLt
      calc p.2.val + B * p.1.val
          < B + B * p.1.val := Nat.add_lt_add_right h2 _
        _ = B * (p.1.val + 1) := by rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
        _ ≤ B * A := Nat.mul_le_mul_left B h1
        _ = A * B := Nat.mul_comm B A⟩
  left_inv i := Fin.ext (by
    dsimp only
    rw [Nat.add_comm, Nat.div_add_mod])
  right_inv := fun ⟨a, b⟩ => Prod.ext
    (Fin.ext (by
      dsimp only
      rw [Nat.add_mul_div_left b.val a.val hB, Nat.div_eq_of_lt b.isLt, Nat.zero_add]))
    (Fin.ext (by
      dsimp only
      rw [Nat.add_mul_mod_self_left b.val B a.val, Nat.mod_eq_of_lt b.isLt]))

def finCastEquiv {m n : Nat} (h : m = n) : SimpleEquiv (Fin m) (Fin n) where
  toFun i := ⟨i.val, h ▸ i.isLt⟩
  invFun j := ⟨j.val, h.symm ▸ j.isLt⟩
  left_inv _ := Fin.ext rfl
  right_inv _ := Fin.ext rfl

/-- Constructive enumeration `Fin goldilocksPrime ≃ Goldilocks`. -/
def goldilocksEnum : SimpleEquiv (Fin goldilocksPrime) Goldilocks where
  toFun i := ⟨i.val, i.isLt⟩
  invFun x := ⟨x.val, x.isLt⟩
  left_inv _ := Fin.ext rfl
  right_inv _ := Goldilocks.ext rfl

/-- Constructive enumeration `Fin (goldilocksPrime ^ 2) ≃ GoldilocksExt2` (`|F| = p^2 > 2^127`). -/
def goldilocksExt2Enum : SimpleEquiv (Fin (goldilocksPrime ^ 2)) GoldilocksExt2 :=
  SimpleEquiv.trans
    (finCastEquiv (by simp [Nat.pow_succ] : goldilocksPrime ^ 2 = goldilocksPrime * goldilocksPrime))
    (SimpleEquiv.trans
      (finMulProdEquiv goldilocksPrime goldilocksPrime (by decide))
      { toFun := fun p => ⟨goldilocksEnum.toFun p.1, goldilocksEnum.toFun p.2⟩
        invFun := fun z => (goldilocksEnum.invFun z.c0, goldilocksEnum.invFun z.c1)
        left_inv := fun ⟨a, b⟩ => Prod.ext (goldilocksEnum.left_inv a) (goldilocksEnum.left_inv b)
        right_inv := fun z => GoldilocksExt2.ext (goldilocksEnum.right_inv z.c0) (goldilocksEnum.right_inv z.c1) })

/-- Disposable-choice 640-bit OLE entropy budget for `GoldilocksExt2` (`10 × 64 = 640` random bits;
    after observing at most `128` bits of sender affine error and extracting `128` randomizer bits,
    `640 - 128 - 128 = 384 ≥ 256` residual min-entropy bits remain, giving `≤ 2^-192` LHL bias). -/
def goldilocksExt2OleChoiceWords : Nat := 10
def goldilocksExt2OleChoiceBits : Nat := 64 * goldilocksExt2OleChoiceWords

theorem goldilocksExt2_macBlind_soundness_and_lhl_budget
    (rCorrupt d err : GoldilocksExt2) (hd : d ≠ zero) :
    qsum (goldilocksPrime ^ 2)
      (fun i => if macBlindOpen (goldilocksExt2Enum.toFun i) rCorrupt d err = zero then 1 else 0) = 1 ∧
    2 ^ 127 < goldilocksPrime ^ 2 ∧
    goldilocksExt2OleChoiceBits - 128 - 128 = 384 :=
  ⟨(macBlind_uniform_of_nonzero_defect goldilocksExt2Enum rCorrupt d err hd).2.2,
   goldilocksExt2_card_gt_two_pow_126 127 (Nat.le_refl 127),
   rfl⟩

/-- Constructive enumeration `Fin (2 ^ (2 ^ k)) ≃ TowerElem k` via `unpackTower` / `packTower`. -/
def towerElemEnum (k : Nat) : SimpleEquiv (Fin (2 ^ (2 ^ k))) (TowerElem k) where
  toFun i := unpackTower k (BitVec.ofFin i)
  invFun x := (packTower k x).toFin
  left_inv i := by
    rw [packTower_unpackTower]
  right_inv x := by
    rw [BitVec.ofFin_toFin, unpackTower_packTower]

/-- Constructive enumeration `Fin (2 ^ 128) ≃ Tower128`. -/
def tower128Enum : SimpleEquiv (Fin (2 ^ 128)) Tower128 := towerElemEnum 7

/-- Constructive enumeration `Fin (2 ^ 128) ≃ Gf2Pow128` in polynomial basis. -/
def gf2Pow128Enum : SimpleEquiv (Fin (2 ^ 128)) Qsag.Math.Gf2Pow128 where
  toFun i := ⟨BitVec.ofFin i⟩
  invFun x := x.bits.toFin
  left_inv _ := rfl
  right_inv x := by cases x; rfl

/-- Constructive enumeration `Fin (2 ^ 256) ≃ Tower128 × Tower128` for 2-round `Tower128` blinding. -/
def tower128PairEnum : SimpleEquiv (Fin (2 ^ 256)) (Tower128 × Tower128) :=
  SimpleEquiv.trans
    (finCastEquiv (by decide : 2 ^ 256 = 2 ^ 128 * 2 ^ 128))
    (SimpleEquiv.trans
      (finMulProdEquiv (2 ^ 128) (2 ^ 128) (by decide))
      (SimpleEquiv.prodCongr tower128Enum tower128Enum))

/-- Exact 2-round multiplicative MAC-residual opening (`blind_open_tower128`):
    runs round 0 and returns immediately on nonzero opening `w₀ ≠ 0`; otherwise runs an
    independent round 1 and returns `w₁`. -/
def macBlindTwoRoundOpen {F : Type} [LawfulField F] [DecidableEq F]
    (rH₀ rH₁ rC₀ rC₁ d err₀ err₁ : F) : F :=
  let w₀ := macBlindOpen rH₀ rC₀ d err₀
  if w₀ ≠ zero then w₀ else macBlindOpen rH₁ rC₁ d err₁

theorem macBlindTwoRoundOpen_eq_zero_iff {F : Type} [LawfulField F] [DecidableEq F]
    (rH₀ rH₁ rC₀ rC₁ d err₀ err₁ : F) :
    macBlindTwoRoundOpen rH₀ rH₁ rC₀ rC₁ d err₀ err₁ = zero ↔
      macBlindOpen rH₀ rC₀ d err₀ = zero ∧ macBlindOpen rH₁ rC₁ d err₁ = zero := by
  unfold macBlindTwoRoundOpen
  dsimp only
  by_cases hw0 : macBlindOpen rH₀ rC₀ d err₀ = zero <;> simp [hw0]

private theorem ite_one_zero_true {P : Prop} [Decidable P] (h : P) : (if P then 1 else 0) = 1 := by
  simp [h]

private theorem ite_one_zero_false {P : Prop} [Decidable P] (h : ¬ P) : (if P then 1 else 0) = 0 := by
  simp [h]

theorem macBlindOpen_rescale_zero_eq {F : Type} [LawfulField F] (rCorrupt d₁ d₂ : F)
    (hd₁ : d₁ ≠ zero) (hd₂ : d₂ ≠ zero) (rH : F) :
    macBlindOpen ((macBlindRescaleEquiv rCorrupt d₁ d₂ hd₁ hd₂).toFun rH) rCorrupt d₁ zero =
      macBlindOpen rH rCorrupt d₂ zero := by
  rw [← macBlindPure_eq_open_zero, ← macBlindPure_eq_open_zero]
  exact macBlindPure_rescale_eq rCorrupt d₁ d₂ hd₁ hd₂ rH

/-- **Two-Round Independent Blinding Soundness (`macBlindTwoRound_zero_count_eq_one`)**:
    Over any finite field `F` with product enumeration `pairEnum : SimpleEquiv (Fin cardSq) (F × F)`,
    for any nonzero MAC defect `d ≠ 0`, `macBlindTwoRoundOpen` outputs `0` on **exactly `1`** out of
    `cardSq` honest randomizer pairs `(rH₀, rH₁)`. -/
