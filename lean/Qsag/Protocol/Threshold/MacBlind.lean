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
theorem macBlindTwoRound_zero_count_eq_one {F : Type} [LawfulField F] [DecidableEq F]
    {cardSq : Nat} (pairEnum : SimpleEquiv (Fin cardSq) (F × F))
    (rC₀ rC₁ d err₀ err₁ : F) (hd : d ≠ zero) :
    qsum cardSq (fun i =>
      let p := pairEnum.toFun i
      if macBlindTwoRoundOpen p.1 p.2 rC₀ rC₁ d err₀ err₁ = zero then 1 else 0) = 1 := by
  let pairPerm := SimpleEquiv.prodCongr
    (macBlindEquiv rC₀ d err₀ hd)
    (macBlindEquiv rC₁ d err₁ hd)
  have hCongr :
      qsum cardSq (fun i =>
        let p := pairEnum.toFun i
        if macBlindTwoRoundOpen p.1 p.2 rC₀ rC₁ d err₀ err₁ = zero then 1 else 0) =
      qsum cardSq (fun i =>
        if pairPerm.toFun (pairEnum.toFun i) = (zero, zero) then 1 else 0) := by
    apply qsum_congr
    intro i
    dsimp only [pairPerm]
    rw [SimpleEquiv.prodCongr_toFun]
    change (if macBlindTwoRoundOpen (pairEnum.toFun i).1 (pairEnum.toFun i).2 rC₀ rC₁ d err₀ err₁ = zero then 1 else 0) =
      (if (macBlindOpen (pairEnum.toFun i).1 rC₀ d err₀,
           macBlindOpen (pairEnum.toFun i).2 rC₁ d err₁) = (zero, zero) then 1 else 0)
    have hIff : macBlindTwoRoundOpen (pairEnum.toFun i).1 (pairEnum.toFun i).2 rC₀ rC₁ d err₀ err₁ = zero ↔
        (macBlindOpen (pairEnum.toFun i).1 rC₀ d err₀,
         macBlindOpen (pairEnum.toFun i).2 rC₁ d err₁) = (zero, zero) := by
      rw [macBlindTwoRoundOpen_eq_zero_iff, Prod.mk.injEq]
    by_cases h0 : (macBlindOpen (pairEnum.toFun i).1 rC₀ d err₀,
                   macBlindOpen (pairEnum.toFun i).2 rC₁ d err₁) = (zero, zero)
    · have hL : macBlindTwoRoundOpen (pairEnum.toFun i).1 (pairEnum.toFun i).2 rC₀ rC₁ d err₀ err₁ = zero :=
        hIff.mpr h0
      rw [ite_one_zero_true hL, ite_one_zero_true h0]
    · have hL : macBlindTwoRoundOpen (pairEnum.toFun i).1 (pairEnum.toFun i).2 rC₀ rC₁ d err₀ err₁ ≠ zero :=
        fun h => h0 (hIff.mp h)
      rw [ite_one_zero_false hL, ite_one_zero_false h0]
  rw [hCongr, qsum_bijection_invariant pairEnum pairPerm (fun q => if q = (zero, zero) then 1 else 0)]
  exact qsum_enum_eq_target pairEnum (zero, zero)

/-- **`Tower128` Two-Round Blinding `2^-256` Soundness & Zero-Leakage (`macBlind_tower128_two_round_256bit_sound`)**:
    For any nonzero defect `d ≠ 0` in `Tower128`, 2-round independent blinding accepts on
    **exactly `1` out of `2^256`** honest randomizer pairs (`Pr[accept] = 2^-256`), and in the pure
    check (`err₀ = err₁ = 0`) the 2-round output distribution is **independent** of which nonzero
    defect `d₁, d₂ ≠ 0` occurred! -/
theorem macBlind_tower128_two_round_256bit_sound
    (rC₀ rC₁ d err₀ err₁ : Tower128) (hd : d ≠ zero) :
    qsum (2 ^ 256) (fun i =>
      let p := tower128PairEnum.toFun i
      if macBlindTwoRoundOpen p.1 p.2 rC₀ rC₁ d err₀ err₁ = zero then 1 else 0) = 1 ∧
    (∀ (d₂ : Tower128), d₂ ≠ zero → ∀ (obs : Tower128 → Nat),
      qsum (2 ^ 256) (fun i =>
        let p := tower128PairEnum.toFun i
        obs (macBlindTwoRoundOpen p.1 p.2 rC₀ rC₁ d zero zero)) =
      qsum (2 ^ 256) (fun i =>
        let p := tower128PairEnum.toFun i
        obs (macBlindTwoRoundOpen p.1 p.2 rC₀ rC₁ d₂ zero zero))) := by
  refine ⟨macBlindTwoRound_zero_count_eq_one tower128PairEnum rC₀ rC₁ d err₀ err₁ hd, ?_⟩
  intro d₂ hd₂ obs
  let e2 := SimpleEquiv.prodCongr
    (macBlindRescaleEquiv rC₀ d d₂ hd hd₂)
    (macBlindRescaleEquiv rC₁ d d₂ hd hd₂)
  refine qsum_bijection_hop_eq tower128PairEnum e2
    (fun p => obs (macBlindTwoRoundOpen p.1 p.2 rC₀ rC₁ d zero zero))
    (fun p => obs (macBlindTwoRoundOpen p.1 p.2 rC₀ rC₁ d₂ zero zero)) ?_
  rintro ⟨r₀, r₁⟩
  dsimp only [e2]
  rw [SimpleEquiv.prodCongr_toFun]
  change obs (macBlindTwoRoundOpen
    ((macBlindRescaleEquiv rC₀ d d₂ hd hd₂).toFun r₀)
    ((macBlindRescaleEquiv rC₁ d d₂ hd hd₂).toFun r₁) rC₀ rC₁ d zero zero) =
    obs (macBlindTwoRoundOpen r₀ r₁ rC₀ rC₁ d₂ zero zero)
  unfold macBlindTwoRoundOpen
  simp only [macBlindOpen_rescale_zero_eq]

/-- Polynomial-basis `Gf2Pow128` MAC blinding via `isoTower128ToPoly` (`blind_open_additive_gf128_poly`)
    commutes with the canonical field isomorphism `Tower128 ≃+* Gf2Pow128`. -/
theorem macBlind_gf2Pow128_iso_commutes (rH rC d err : Tower128) :
    Qsag.Math.isoTower128ToPoly.toFun (macBlindOpen rH rC d err) =
      macBlindOpen
        (Qsag.Math.isoTower128ToPoly.toFun rH)
        (Qsag.Math.isoTower128ToPoly.toFun rC)
        (Qsag.Math.isoTower128ToPoly.toFun d)
        (Qsag.Math.isoTower128ToPoly.toFun err) := by
  unfold macBlindOpen
  rw [Qsag.Math.isoTower128ToPoly.map_add,
      Qsag.Math.isoTower128ToPoly.map_mul,
      Qsag.Math.isoTower128ToPoly.map_add]

/-! ## 3. 3-Projection Boolean MAC Blinding Bound (`(q^2 + q - 1)^3 < q^7`) -/

private theorem cube_mono {x y : Nat} (h : x ≤ y) : x ^ 3 ≤ y ^ 3 := by
  have h2 : x * x ≤ y * y := Nat.mul_le_mul h h
  have h3 : (x * x) * x ≤ (y * y) * y := Nat.mul_le_mul h2 h
  simpa [Nat.pow_succ] using h3

private theorem two_mul_cube (a : Nat) : (2 * a) ^ 3 = 8 * ((a * a) * a) := by
  have hPow : (2 * a) ^ 3 = ((2 * a) * (2 * a)) * (2 * a) := by simp [Nat.pow_succ]
  have h1 : (2 * a) * (2 * a) = 4 * (a * a) := by
    rw [Nat.mul_assoc 2 a (2 * a), ← Nat.mul_assoc a 2 a,
        Nat.mul_comm a 2, Nat.mul_assoc 2 a a, ← Nat.mul_assoc 2 2 (a * a)]
  have h2 : (4 * (a * a)) * (2 * a) = 8 * ((a * a) * a) := by
    rw [Nat.mul_assoc 4 (a * a) (2 * a), ← Nat.mul_assoc (a * a) 2 a,
        Nat.mul_comm (a * a) 2, Nat.mul_assoc 2 (a * a) a, ← Nat.mul_assoc 4 2 ((a * a) * a)]
  rw [hPow, h1, h2]

/-- **Constructive 3-Projection Boolean MAC Blinding Bound (`three_projection_mac_blind_bound`)**:
    For EVERY field size `2 ≤ q`, clearing denominators of
    `(1/q + (1 - 1/q)/q^2)^3 = ((q^2 + q - 1)/q^3)^3 < 1/q^2` yields
    `(q ^ 2 + q - 1) ^ 3 < q ^ 7`. -/
theorem three_projection_mac_blind_bound (q : Nat) (hq : 2 ≤ q) :
    (q ^ 2 + q - 1) ^ 3 < q ^ 7 := by
  match q with
  | 0 | 1 => omega
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | 5 => decide
  | 6 => decide
  | 7 => decide
  | 8 => decide
  | n + 9 =>
    let Q := n + 9
    have hQPos : 0 < Q := by omega
    have hQ2 : Q ^ 2 = Q * Q := by simp [Nat.pow_succ]
    have hQLeSq : Q ≤ Q ^ 2 := by
      rw [hQ2]
      exact Nat.le_mul_of_pos_left Q hQPos
    have hBaseLe : Q ^ 2 + Q - 1 ≤ 2 * Q ^ 2 := by omega
    have hCubeLe : (Q ^ 2 + Q - 1) ^ 3 ≤ (2 * Q ^ 2) ^ 3 := cube_mono hBaseLe
    have hEight : (2 * Q ^ 2) ^ 3 = 8 * Q ^ 6 := by
      rw [two_mul_cube (Q ^ 2), ← Nat.pow_add Q 2 2, ← Nat.pow_add Q 4 2]
    have hQ6Pos : 0 < Q ^ 6 := by
      have hSqPos : 0 < Q ^ 2 := by rw [hQ2]; exact Nat.mul_pos hQPos hQPos
      have hQ6Eq : Q ^ 6 = (Q ^ 2 * Q ^ 2) * Q ^ 2 := by
        rw [← Nat.pow_add Q 2 2, ← Nat.pow_add Q 4 2]
      rw [hQ6Eq]
      exact Nat.mul_pos (Nat.mul_pos hSqPos hSqPos) hSqPos
    have hStrict : 8 * Q ^ 6 < Q ^ 7 := by
      have hLt : 8 * Q ^ 6 < Q * Q ^ 6 := Nat.mul_lt_mul_of_pos_right (by omega : 8 < Q) hQ6Pos
      rwa [Nat.mul_comm Q (Q ^ 6), ← Nat.pow_succ] at hLt
    rw [hEight] at hCubeLe
    exact Nat.lt_of_le_of_lt hCubeLe hStrict

theorem three_projection_mac_blind_bound_u64 :
    ((2 ^ 64) ^ 2 + 2 ^ 64 - 1) ^ 3 < (2 ^ 64) ^ 7 :=
  three_projection_mac_blind_bound (2 ^ 64) (by decide)

theorem three_projection_mac_blind_bound_gf128 :
    ((2 ^ 128) ^ 2 + 2 ^ 128 - 1) ^ 3 < (2 ^ 128) ^ 7 ∧
    (2 ^ 128) ^ 2 = 2 ^ 256 :=
  ⟨three_projection_mac_blind_bound (2 ^ 128) (by decide), by decide⟩

/-- **Unconditional Single-Projection Two-Round False-Accept Bound (`single_projection_two_round_false_accept_count`)**:
    For any nonzero coordinate `v₀ ≠ 0`, any fixed linear combination `rest` of the remaining
    coordinates, and ANY post-OLE offsets `err₀, err₁ : F`, as `(wWeight, (rH₀, rH₁))` ranges
    uniformly over `F × (F × F)` (`q ^ 3` coins), `macBlindTwoRoundOpen` accepts on **at most
    `q ^ 2 + q - 1`** coins (matching `1/q + (1 - 1/q)/q^2 = (q^2 + q - 1)/q^3`). -/
theorem single_projection_two_round_false_accept_count {F : Type} [LawfulField F] [DecidableEq F]
    {q : Nat} (hq : 1 ≤ q)
    (enum : SimpleEquiv (Fin q) F)
    (pairEnum : SimpleEquiv (Fin (q ^ 2)) (F × F))
    (v₀ rest rC₀ rC₁ err₀ err₁ : F) (hv₀ : v₀ ≠ zero) :
    qsum q (fun iw =>
      let proj := macBlindOpen (enum.toFun iw) zero v₀ rest
      qsum (q ^ 2) (fun ir =>
        let p := pairEnum.toFun ir
        if macBlindTwoRoundOpen p.1 p.2 rC₀ rC₁ proj err₀ err₁ = zero then 1 else 0)) ≤
      q ^ 2 + q - 1 := by
  have hProjUnif := (macBlind_uniform_of_nonzero_defect enum zero v₀ rest hv₀).1
  let innerCount : F → Nat := fun proj =>
    qsum (q ^ 2) (fun ir =>
      let p := pairEnum.toFun ir
      if macBlindTwoRoundOpen p.1 p.2 rC₀ rC₁ proj err₀ err₁ = zero then 1 else 0)
  change qsum q (fun iw => innerCount (macBlindOpen (enum.toFun iw) zero v₀ rest)) ≤ q ^ 2 + q - 1
  rw [hProjUnif innerCount]
  have hSqGe1 : 1 ≤ q ^ 2 := by
    have hq2 : q ^ 2 = q * q := by simp [Nat.pow_succ]
    rw [hq2]
    exact Nat.mul_le_mul hq hq
  have hUpper : ∀ iw : Fin q,
      innerCount (enum.toFun iw) ≤
        1 + (if enum.toFun iw = zero then q ^ 2 - 1 else 0) := by
    intro iw
    dsimp only [innerCount]
    by_cases hp0 : enum.toFun iw = zero
    · simp only [hp0, ↓reduceIte]
      have hTriv :
          qsum (q ^ 2) (fun ir =>
            if macBlindTwoRoundOpen (pairEnum.toFun ir).1 (pairEnum.toFun ir).2 rC₀ rC₁ zero err₀ err₁ = zero
            then 1 else 0) ≤ qsum (q ^ 2) (fun _ => 1) :=
        qsum_le_qsum (fun ir => by split <;> omega)
      rw [qsum_const, Nat.mul_one] at hTriv
      omega
    · simp only [hp0, ↓reduceIte, Nat.add_zero]
      exact Nat.le_of_eq (macBlindTwoRound_zero_count_eq_one pairEnum rC₀ rC₁ (enum.toFun iw) err₀ err₁ hp0)
  have hSumLe := qsum_le_qsum hUpper
  rw [qsum_add, qsum_const, Nat.mul_one] at hSumLe
  have hFactor :
      qsum q (fun iw => if enum.toFun iw = zero then q ^ 2 - 1 else 0) =
      qsum q (fun iw => (q ^ 2 - 1) * (if enum.toFun iw = zero then 1 else 0)) := by
    apply qsum_congr
    intro iw
    by_cases hz : enum.toFun iw = zero <;> simp [hz]
  rw [hFactor, qsum_mul_left, qsum_enum_eq_target enum zero, Nat.mul_one] at hSumLe
  omega

/-! ## 4. `POOL_WORDS = 8192` & Adaptive `combineArity` Hypergeometric Criterion (`triple_f2.rs`) -/

/-- Default Boolean triple combine pool size in 64-bit words (`POOL_WORDS = 8192`). -/
def tripleF2PoolWords : Nat := 8192

/-- Output bits in one full `POOL_WORDS` combine pass (`64 * 8192 = 524,288`). -/
def tripleF2PoolBits : Nat := 64 * tripleF2PoolWords

/-- Statistical security parameter of one Boolean bucket-combine pass (`COMBINE_SECURITY_BITS = 40`). -/
def combineSecurityBits : Nat := 40

/-- Factorial `k!`. -/
def factNat : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * factNat k

theorem factNat_pos : ∀ k : Nat, 0 < factNat k
  | 0 => Nat.zero_lt_one
  | k + 1 => Nat.mul_pos (Nat.succ_pos k) (factNat_pos k)

/-- Pascal-triangle binomial coefficient `C(n, k)` (specification reference). -/
def choosePascal : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choosePascal n k + choosePascal n (k + 1)

/-- Fast falling-factorial binomial coefficient `C(n, k) = n^{\underline{k}} / k!`. -/
def chooseNat (n k : Nat) : Nat :=
  affineFallingFactorial n k / factNat k

private theorem affineFallingFactorial_eq_zero_of_lt (a : Nat) :
    ∀ {k : Nat}, a < k → affineFallingFactorial a k = 0
  | 0, h => by omega
  | k + 1, h => by
    show (a - k) * affineFallingFactorial a k = 0
    if hak : a = k then
      have hSub : a - k = 0 := by omega
      rw [hSub, Nat.zero_mul]
    else
      rw [affineFallingFactorial_eq_zero_of_lt a (k := k) (by omega), Nat.mul_zero]

private theorem mul_succ_affineFallingFactorial (n : Nat) :
    ∀ k : Nat, (n + 1) * affineFallingFactorial n k = affineFallingFactorial (n + 1) (k + 1)
  | 0 => by simp [affineFallingFactorial]
  | k + 1 => by
    show (n + 1) * ((n - k) * affineFallingFactorial n k) =
      (n + 1 - (k + 1)) * affineFallingFactorial (n + 1) (k + 1)
    have hs : n + 1 - (k + 1) = n - k := by omega
    rw [hs, ← Nat.mul_assoc, Nat.mul_comm (n + 1) (n - k), Nat.mul_assoc,
        mul_succ_affineFallingFactorial n k]

/-- Exact algebraic identity `choosePascal n k * k! = n^{\underline{k}}`. -/
theorem choosePascal_mul_factNat_eq :
    ∀ (n k : Nat), choosePascal n k * factNat k = affineFallingFactorial n k
  | _, 0 => by simp [choosePascal, factNat, affineFallingFactorial]
  | 0, k + 1 => by
    simp only [choosePascal, Nat.zero_mul]
    exact (affineFallingFactorial_eq_zero_of_lt 0 (Nat.zero_lt_succ k)).symm
  | n + 1, k + 1 => by
    simp only [choosePascal, factNat]
    have ih1 := choosePascal_mul_factNat_eq n k
    have ih2 := choosePascal_mul_factNat_eq n (k + 1)
    simp only [factNat] at ih2
    have hLhs :
        (choosePascal n k + choosePascal n (k + 1)) * ((k + 1) * factNat k) =
          (k + 1) * (choosePascal n k * factNat k) +
          choosePascal n (k + 1) * ((k + 1) * factNat k) := by
      rw [Nat.add_mul, ← Nat.mul_assoc (choosePascal n k) (k + 1) (factNat k),
          Nat.mul_comm (choosePascal n k) (k + 1), Nat.mul_assoc]
    rw [hLhs, ih1, ih2]
    show (k + 1) * affineFallingFactorial n k + (n - k) * affineFallingFactorial n k =
      affineFallingFactorial (n + 1) (k + 1)
    rw [← Nat.add_mul]
    if hkn : k ≤ n then
      have hSum : k + 1 + (n - k) = n + 1 := by omega
      rw [hSum]
      exact mul_succ_affineFallingFactorial n k
    else
      have hLt : n < k := by omega
      rw [affineFallingFactorial_eq_zero_of_lt n hLt, Nat.mul_zero]
      exact (affineFallingFactorial_eq_zero_of_lt (n + 1) (Nat.succ_lt_succ hLt)).symm

/-- `chooseNat n k` coincides identically with Pascal's `choosePascal n k`, and
    `chooseNat n k * factNat k = affineFallingFactorial n k`. -/
theorem chooseNat_eq_choosePascal (n k : Nat) :
    chooseNat n k = choosePascal n k ∧
    chooseNat n k * factNat k = affineFallingFactorial n k := by
  have hDiv : chooseNat n k = choosePascal n k := by
    unfold chooseNat
    rw [← choosePascal_mul_factNat_eq n k,
        Nat.mul_div_cancel (choosePascal n k) (factNat_pos k)]
  refine ⟨hDiv, ?_⟩
  rw [hDiv]
  exact choosePascal_mul_factNat_eq n k

/-- Hypergeometric single-bucket leakage criterion `out_bits * 2^40 ≤ C(f * (out_bits + 1), f)`. -/
def combineArityMeetsBound (outBits f : Nat) : Bool :=
  decide (outBits * 2 ^ combineSecurityBits ≤ chooseNat (f * (outBits + 1)) f)

/-- Search `f = 2, 3, ...` for the least bucket arity satisfying `combineArityMeetsBound`
    (with structural fuel `fuel`, where `fuel = 5` covers `f ∈ [2..7]` for all `outBits ≥ 64`). -/
def combineArityLoop (outBits f : Nat) : Nat → Nat
  | 0 => f
  | fuel + 1 =>
    if combineArityMeetsBound outBits f then f
    else combineArityLoop outBits (f + 1) fuel

/-- Adaptive bucket size `combine_arity(out_bits)` (`triple_f2.rs:2712-2730`). -/
def combineArity (outBits : Nat) : Nat :=
  combineArityLoop outBits 2 5

/-- Raw input 64-bit words required by `combine_input_words(out_words, arity)` (`triple_f2.rs:2733-2735`). -/
def combineInputWords (outWords arity : Nat) : Nat :=
  (arity * (64 * outWords + 1) + 63) / 64

/-- **Concrete `POOL_WORDS = 8192` & `7720`-Word Adaptive Arity Certificates (`combineArity_pool_certificates`)**:
    1. At `POOL_WORDS = 8192` (`outBits = 524,288`), `f = 2` fails and `combineArity 524288 = 3` passes.
    2. At `7720` words (`outBits = 494,080`), `f = 3` fails (`C(1482243, 3) < 494080 * 2^40`) and
       `combineArity 494080 = 4` passes.
    3. At `1` word (`outBits = 64`), `f = 6` fails and `combineArity 64 = 7` passes. -/
theorem combineArity_pool_certificates :
    combineArityMeetsBound tripleF2PoolBits 2 = false ∧
    combineArityMeetsBound tripleF2PoolBits 3 = true ∧
    combineArity tripleF2PoolBits = 3 ∧
    combineInputWords tripleF2PoolWords 3 = 24577 ∧
    combineArityMeetsBound (64 * 7720) 3 = false ∧
    combineArityMeetsBound (64 * 7720) 4 = true ∧
    combineArity (64 * 7720) = 4 ∧
    combineArityMeetsBound 64 6 = false ∧
    combineArityMeetsBound 64 7 = true ∧
    combineArity 64 = 7 := by
  decide

/-- **`#tooth` 3 (`tooth_fixed_arity3_fails_at_7720_words`)**:
    Hardcoding bucket size `f = 3` without `combineArity`'s adaptive check violates the `2^-40`
    bound on smaller pools such as `7,720` words (`494,080` bits). -/
theorem tooth_fixed_arity3_fails_at_7720_words :
    ∃ outBits : Nat,
      64 ≤ outBits ∧
      combineArityMeetsBound outBits 3 = false ∧
      combineArity outBits ≠ 3 :=
  ⟨64 * 7720, by decide, by decide, by decide⟩

/-- **Universal Arity-7 Ceiling for All `outBits ≥ 64` (`combineArity_valid_for_all_ge_64`)**:
    For EVERY `outBits ≥ 64`, `f = 7` satisfies `combineArityMeetsBound outBits 7 = true`, hence
    `2 ≤ combineArity outBits ≤ 7` and `combineArityMeetsBound outBits (combineArity outBits) = true`. -/
theorem combineArity_valid_for_all_ge_64 (outBits : Nat) (hGe : 64 ≤ outBits) :
    2 ≤ combineArity outBits ∧
    combineArity outBits ≤ 7 ∧
    combineArityMeetsBound outBits (combineArity outBits) = true := by
  have hArity7 : combineArityMeetsBound outBits 7 = true := by
    unfold combineArityMeetsBound combineSecurityBits
    apply decide_eq_true
    let m := 7 * (outBits + 1)
    have hm1 : 449 ≤ m - 6 := by dsimp only [m]; omega
    have hm0 : outBits ≤ m := by dsimp only [m]; omega
    have hFall :
        outBits * 449 ^ 6 ≤ affineFallingFactorial m 7 := by
      have hExpand :
          affineFallingFactorial m 7 =
            (m - 6) * ((m - 5) * ((m - 4) * ((m - 3) * ((m - 2) * ((m - 1) * m))))) := by
        simp [affineFallingFactorial]
      have hPow :
          outBits * 449 ^ 6 =
            449 * (449 * (449 * (449 * (449 * (449 * outBits))))) := by
        have h6 : (449 : Nat) ^ 6 = 449 * (449 * (449 * (449 * (449 * 449)))) := by decide
        rw [h6, Nat.mul_comm outBits]
        simp only [Nat.mul_assoc]
      rw [hExpand, hPow]
      exact Nat.mul_le_mul hm1
        (Nat.mul_le_mul (by omega)
          (Nat.mul_le_mul (by omega)
            (Nat.mul_le_mul (by omega)
              (Nat.mul_le_mul (by omega)
                (Nat.mul_le_mul (by omega) hm0)))))
    have hNum : factNat 7 * 2 ^ 40 ≤ 449 ^ 6 := by decide
    have hMul : (outBits * 2 ^ 40) * factNat 7 ≤ affineFallingFactorial m 7 := by
      calc (outBits * 2 ^ 40) * factNat 7
          = outBits * (factNat 7 * 2 ^ 40) := by
            rw [Nat.mul_assoc, Nat.mul_comm (2 ^ 40) (factNat 7)]
        _ ≤ outBits * 449 ^ 6 := Nat.mul_le_mul_left outBits hNum
        _ ≤ affineFallingFactorial m 7 := hFall
    rw [← (chooseNat_eq_choosePascal m 7).2] at hMul
    exact Nat.le_of_mul_le_mul_right hMul (factNat_pos 7)
  cases h2 : combineArityMeetsBound outBits 2
  · cases h3 : combineArityMeetsBound outBits 3
    · cases h4 : combineArityMeetsBound outBits 4
      · cases h5 : combineArityMeetsBound outBits 5
        · cases h6 : combineArityMeetsBound outBits 6
          · have hEq : combineArity outBits = 7 := by
              simp [combineArity, combineArityLoop, h2, h3, h4, h5, h6]
            rw [hEq]
            exact ⟨by decide, by decide, hArity7⟩
          · have hEq : combineArity outBits = 6 := by
              simp [combineArity, combineArityLoop, h2, h3, h4, h5, h6]
            rw [hEq]
            exact ⟨by decide, by decide, h6⟩
        · have hEq : combineArity outBits = 5 := by
            simp [combineArity, combineArityLoop, h2, h3, h4, h5]
          rw [hEq]
          exact ⟨by decide, by decide, h5⟩
      · have hEq : combineArity outBits = 4 := by
          simp [combineArity, combineArityLoop, h2, h3, h4]
        rw [hEq]
        exact ⟨by decide, by decide, h4⟩
    · have hEq : combineArity outBits = 3 := by
        simp [combineArity, combineArityLoop, h2, h3]
      rw [hEq]
      exact ⟨by decide, by decide, h3⟩
  · have hEq : combineArity outBits = 2 := by
      simp [combineArity, combineArityLoop, h2]
    rw [hEq]
    exact ⟨by decide, by decide, h2⟩

private theorem choosePascal_eq_zero_of_lt :
    ∀ {n k : Nat}, n < k → choosePascal n k = 0
  | _, 0, h => by omega
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    simp only [choosePascal,
      choosePascal_eq_zero_of_lt (n := n) (k := k) (by omega),
      choosePascal_eq_zero_of_lt (n := n) (k := k + 1) (by omega)]

/-- **Hypergeometric Single-Bucket Collision Bound (`combineBucket_hypergeometric_sound`)**:
    Over any duplicate-free raw bit pool `U` of size `f * (outBits + 1)` (`outBits` kept buckets
    plus `1` discarded bucket) where `combineArityMeetsBound outBits f = true`, and any adversarial
    weight-`f` parity support `good : α → Bool` (`(U.filter good).length ≤ f`), the union-bounded
    count over `outBits` kept buckets of ordered `f`-tuples landing wholly inside `good` satisfies
    `outBits * hitCount * 2 ^ 40 ≤ totalOrderedTuples` (`Pr[bad] ≤ 2^-40`)! -/
theorem combineBucket_hypergeometric_sound {α : Type} [DecidableEq α]
    (outBits f : Nat) (U : List α) (good : α → Bool)
    (hU : U.Nodup) (hLen : U.length = f * (outBits + 1))
    (hSupport : (U.filter good).length ≤ f)
    (hBound : combineArityMeetsBound outBits f = true) :
    outBits * ((affineDistinctTuples f U).filter (fun t => t.all good)).length *
        2 ^ combineSecurityBits ≤
      (affineDistinctTuples f U).length := by
  have hGoodLe : ((affineDistinctTuples f U).filter (fun t => t.all good)).length ≤ factNat f := by
    have h1 := affineDistinctTuples_all_good_le f f U good hU hSupport
    have hFactEq : affineFallingFactorial f f = factNat f := by
      have hC := (chooseNat_eq_choosePascal f f).2
      have hDiag : ∀ k : Nat, choosePascal k k = 1 := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih =>
          simp [choosePascal, ih, choosePascal_eq_zero_of_lt (Nat.lt_succ_self k)]
      rw [(chooseNat_eq_choosePascal f f).1, hDiag f, Nat.one_mul] at hC
      exact hC.symm
    rwa [hFactEq] at h1
  rw [affineDistinctTuples_length f hU, hLen,
      ← (chooseNat_eq_choosePascal (f * (outBits + 1)) f).2]
  have hArity : outBits * 2 ^ combineSecurityBits ≤ chooseNat (f * (outBits + 1)) f :=
    of_decide_eq_true hBound
  calc outBits * ((affineDistinctTuples f U).filter (fun t => t.all good)).length *
        2 ^ combineSecurityBits
      = (outBits * 2 ^ combineSecurityBits) *
          ((affineDistinctTuples f U).filter (fun t => t.all good)).length := by
        rw [Nat.mul_assoc, Nat.mul_comm _ (2 ^ combineSecurityBits), ← Nat.mul_assoc]
    _ ≤ chooseNat (f * (outBits + 1)) f * factNat f := Nat.mul_le_mul hArity hGoodLe

private theorem zero_one_two_nodup : ([0, 1, 2] : List Nat).Nodup :=
  .cons (fun x hx heq => by subst heq; revert hx; decide)
    (.cons (fun x hx heq => by subst heq; revert hx; decide)
      (.cons (fun _ h => nomatch h) .nil))

private theorem zero_one_nodup : ([0, 1] : List Nat).Nodup :=
  .cons (fun x hx heq => by subst heq; revert hx; decide)
    (.cons (fun _ h => nomatch h) .nil)

/-- **`#tooth` 4 (`tooth_no_discarded_bucket_all_parity_leaks`)**:
    Without the `+ 1` discarded bucket (`U.length = f`), the all-ones parity functional
    (`good := fun _ => true`) covers **every** `f`-tuple in `affineDistinctTuples f U`
    (`hitCount = totalOrderedTuples`), violating the `2^-combineSecurityBits` bound even when
    `combineArityMeetsBound outBits f = true`! -/
theorem tooth_no_discarded_bucket_all_parity_leaks :
    ∃ (outBits f : Nat) (U : List Nat),
      combineArityMeetsBound outBits f = true ∧
      U.Nodup ∧
      U.length = f ∧
      ¬ (outBits * ((affineDistinctTuples f U).filter (fun t => t.all (fun _ => true))).length *
          2 ^ combineSecurityBits ≤
        (affineDistinctTuples f U).length) := by
  refine ⟨tripleF2PoolBits, 3, [0, 1, 2], by decide, zero_one_two_nodup, rfl, ?_⟩
  have hAllTrue : ∀ t : List Nat, t.all (fun _ => true) = true := by
    intro t; induction t with | nil => rfl | cons _ _ ih => simp [ih]
  have hFilt : ∀ ts : List (List Nat), ts.filter (fun t => t.all (fun _ => true)) = ts := by
    intro ts; induction ts with | nil => rfl | cons t _ ih => simp [hAllTrue t, ih]
  rw [hFilt, affineDistinctTuples_length 3 zero_one_two_nodup]
  show ¬ (tripleF2PoolBits * affineFallingFactorial 3 3 * 2 ^ combineSecurityBits ≤
    affineFallingFactorial 3 3)
  decide

/-! ## 5. Non-Vacuity Witnesses & Constructive Kernel / Tooth-Pair Audits -/

theorem inhabited_goldilocksExt2_macBlind :
    ∃ (_rCorrupt d _err : GoldilocksExt2), d ≠ zero :=
  ⟨GoldilocksExt2.zero, GoldilocksExt2.one, GoldilocksExt2.zero, by decide⟩

theorem inhabited_tower128_two_round_macBlind :
    ∃ (_rC₀ _rC₁ d _err₀ _err₁ : Tower128), d ≠ zero :=
  ⟨towerZero 7, towerZero 7, towerOne 7, towerZero 7, towerZero 7, by decide⟩

theorem inhabited_combineBucket_hypergeometric :
    ∃ (outBits f : Nat) (U : List Nat) (good : Nat → Bool),
      U.Nodup ∧ U.length = f * (outBits + 1) ∧
      (U.filter good).length ≤ f ∧ combineArityMeetsBound outBits f = true :=
  ⟨0, 2, [0, 1], (fun _ => true), zero_one_nodup, rfl, by decide, by decide⟩

#verify_constructive
  macBlind_uniform_of_nonzero_defect
  macBlind_abort_independent_of_alpha
  macBlind_spdz_alpha_zero_leakage
  goldilocksExt2_macBlind_soundness_and_lhl_budget
  macBlind_tower128_two_round_256bit_sound
  macBlind_gf2Pow128_iso_commutes
  three_projection_mac_blind_bound
  three_projection_mac_blind_bound_gf128
  single_projection_two_round_false_accept_count
  combineArity_pool_certificates
  combineArity_valid_for_all_ge_64
  combineBucket_hypergeometric_sound

#tooth_pair macBlind_spdz_alpha_zero_leakage vs tooth_unblinded_mac_residual_recovers_alpha
#tooth_pair macBlind_abort_independent_of_alpha vs tooth_zero_randomizer_always_accepts_forged_mac
#tooth_pair combineArity_valid_for_all_ge_64 vs tooth_fixed_arity3_fails_at_7720_words
#tooth_pair combineBucket_hypergeometric_sound vs tooth_no_discarded_bucket_all_parity_leaks

#verify_inhabited goldilocksExt2_macBlind_soundness_and_lhl_budget inhabited_goldilocksExt2_macBlind
#verify_inhabited macBlind_tower128_two_round_256bit_sound inhabited_tower128_two_round_macBlind
#verify_inhabited combineBucket_hypergeometric_sound inhabited_combineBucket_hypergeometric

end Qsag.MacBlind
end
