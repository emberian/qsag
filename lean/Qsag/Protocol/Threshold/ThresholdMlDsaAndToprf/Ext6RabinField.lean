module

public import Qsag.Protocol.Threshold.MlDsa44Parameters
public import Qsag.Tactic.Prelude
public import Qsag.Spec.Refines
public import Qsag.Math.Goldilocks
public import Qsag.Math.Lattices
public import Qsag.Oracle.Poseidon2
public import Qsag.Protocol.Aggregation.UcGames
public import Qsag.Protocol.Credentials.AdvancedMpcAndCreds
public import Qsag.Coding.Cwyz26
public import Qsag.Tactic.AssuranceKit
import Qsag.Math.Primality

public section

namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
attribute [-instance] Fin.instLinearOrderPackage

set_option autoImplicit false

/-- Degree-6 verification extension field $\mathbb{F}_q[X]/(X^6 - 7)$ (`EXT_DEGREE = 6`, `EXT_NONRESIDUE = 7`,
    `rss_mpc.rs:52-56`) used by `rss_mpc::Engine` batch inner-product multiplication verification. -/
structure Ext6Fq204 where
  a0 : Fq204
  a1 : Fq204
  a2 : Fq204
  a3 : Fq204
  a4 : Fq204
  a5 : Fq204
  deriving DecidableEq, Repr

def ext6Zero : Ext6Fq204 := ⟨Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero⟩
def ext6Nonresidue : Fq204 := Fq204.ofNat 7

def ext6EmbedFq (x : Fq204) : Ext6Fq204 :=
  ⟨x, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero⟩

def ext6Add (x y : Ext6Fq204) : Ext6Fq204 :=
  ⟨Fq204.add x.a0 y.a0, Fq204.add x.a1 y.a1, Fq204.add x.a2 y.a2,
   Fq204.add x.a3 y.a3, Fq204.add x.a4 y.a4, Fq204.add x.a5 y.a5⟩

def ext6Sub (x y : Ext6Fq204) : Ext6Fq204 :=
  ⟨Fq204.sub x.a0 y.a0, Fq204.sub x.a1 y.a1, Fq204.sub x.a2 y.a2,
   Fq204.sub x.a3 y.a3, Fq204.sub x.a4 y.a4, Fq204.sub x.a5 y.a5⟩

/-- Base-field scalar multiplication `k_scale(x, s)` in $\mathbb{F}_q[X]/(X^6 - 7)$ (`rss_mpc.rs:336-338`). -/
def ext6Scale (x : Ext6Fq204) (s : Fq204) : Ext6Fq204 :=
  ⟨Fq204.mul x.a0 s, Fq204.mul x.a1 s, Fq204.mul x.a2 s,
   Fq204.mul x.a3 s, Fq204.mul x.a4 s, Fq204.mul x.a5 s⟩

/-- Multiplication in $\mathbb{F}_q[X]/(X^6 - 7)$ (`rss_mpc.rs:53-56`, reducing $X^{6+k} \mapsto 7 X^k$). -/
def ext6Mul (x y : Ext6Fq204) : Ext6Fq204 :=
  let nr := ext6Nonresidue
  let m (a b : Fq204) := Fq204.mul a b
  let ad (a b : Fq204) := Fq204.add a b
  let hi0 := ad (m x.a1 y.a5) (ad (m x.a2 y.a4) (ad (m x.a3 y.a3) (ad (m x.a4 y.a2) (m x.a5 y.a1))))
  let hi1 := ad (m x.a2 y.a5) (ad (m x.a3 y.a4) (ad (m x.a4 y.a3) (m x.a5 y.a2)))
  let hi2 := ad (m x.a3 y.a5) (ad (m x.a4 y.a4) (m x.a5 y.a3))
  let hi3 := ad (m x.a4 y.a5) (m x.a5 y.a4)
  let hi4 := m x.a5 y.a5
  ⟨ad (m x.a0 y.a0) (m nr hi0),
   ad (ad (m x.a0 y.a1) (m x.a1 y.a0)) (m nr hi1),
   ad (ad (m x.a0 y.a2) (ad (m x.a1 y.a1) (m x.a2 y.a0))) (m nr hi2),
   ad (ad (m x.a0 y.a3) (ad (m x.a1 y.a2) (ad (m x.a2 y.a1) (m x.a3 y.a0)))) (m nr hi3),
   ad (ad (m x.a0 y.a4) (ad (m x.a1 y.a3) (ad (m x.a2 y.a2) (ad (m x.a3 y.a1) (m x.a4 y.a0))))) (m nr hi4),
   ad (m x.a0 y.a5) (ad (m x.a1 y.a4) (ad (m x.a2 y.a3) (ad (m x.a3 y.a2) (ad (m x.a4 y.a1) (m x.a5 y.a0)))))⟩

private theorem fq204_add_sub_cancel_left (r v : Fq204) : Fq204.sub (Fq204.add r v) r = v := by
  rw [← Fq204.ofInt_nat r, ← Fq204.ofInt_nat v, Fq204.ofInt_add, Fq204.ofInt_sub]
  congr 1; omega

theorem fq204_sub_add_cancel_left (r y : Fq204) : Fq204.add r (Fq204.sub y r) = y := by
  rw [← Fq204.ofInt_nat r, ← Fq204.ofInt_nat y, Fq204.ofInt_sub, Fq204.ofInt_add]
  congr 1; omega

private theorem ext6Add_sub_cancel (rest v : Ext6Fq204) : ext6Sub (ext6Add rest v) rest = v := by
  rcases rest with ⟨r0, r1, r2, r3, r4, r5⟩
  rcases v with ⟨v0, v1, v2, v3, v4, v5⟩
  simp only [ext6Add, ext6Sub, fq204_add_sub_cancel_left]

private theorem ext6Sub_add_cancel (rest y : Ext6Fq204) : ext6Add rest (ext6Sub y rest) = y := by
  rcases rest with ⟨r0, r1, r2, r3, r4, r5⟩
  rcases y with ⟨y0, y1, y2, y3, y4, y5⟩
  simp only [ext6Add, ext6Sub, fq204_sub_add_cancel_left]

theorem ext6Scale_mul (x : Ext6Fq204) (a b : Fq204) :
    ext6Scale (ext6Scale x a) b = ext6Scale x (Fq204.mul a b) := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
  simp only [ext6Scale, Fq204.mul_assoc]

theorem ext6Scale_one (x : Ext6Fq204) : ext6Scale x Fq204.one = x := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
  simp only [ext6Scale, Fq204.mul_one]

/-- Constructive `Ext6Fq204` bijection `chi ↦ rest + k_scale(chi, delta)` for any nonzero gate error
    `delta ≠ 0` (`rss_mpc.rs:1066-1095`): proves that across all $q^6 = 8380417^6 > 2^{137}$ extension
    challenges `chi : Ext6Fq204`, **at most one** `chi` cancels `rest` to `ext6Zero`! -/
def ext6BatchChallengeEquiv (delta : Fq204) (hDelta : delta ≠ Fq204.zero) (rest : Ext6Fq204) :
    SimpleEquiv Ext6Fq204 Ext6Fq204 where
  toFun chi := ext6Add rest (ext6Scale chi delta)
  invFun out := ext6Scale (ext6Sub out rest) (Fq204.inv delta)
  left_inv chi := by
    rw [ext6Add_sub_cancel, ext6Scale_mul, Fq204.mul_inv_cancel hDelta, ext6Scale_one]
  right_inv out := by
    rw [ext6Scale_mul, Fq204.mul_comm (Fq204.inv delta) delta, Fq204.mul_inv_cancel hDelta,
        ext6Scale_one, ext6Sub_add_cancel]

private def fq204PowModAux (base : Nat) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | fuel + 1, exp, acc =>
    if exp = 0 then acc
    else
      let acc' := if exp % 2 = 1 then (acc * base) % mldsaQ else acc
      fq204PowModAux ((base * base) % mldsaQ) fuel (exp / 2) acc'

def fq204PowModNat (base exp : Nat) : Nat :=
  fq204PowModAux (base % mldsaQ) 28 exp 1

private theorem nodup_map_on_list_fq {α β : Type} (f : α → β) :
    ∀ {xs : List α}, xs.Nodup → (∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b) → (xs.map f).Nodup
  | [], _, _ => .nil
  | x :: xs, .cons hNotMem hTail, hInj => by
    simp only [List.map_cons]
    refine .cons ?_ (nodup_map_on_list_fq f hTail (fun a ha b hb => hInj a (.tail _ ha) b (.tail _ hb)))
    intro y hy hEq
    rcases List.mem_map.mp hy with ⟨z, hzMem, rfl⟩
    have hxz := hInj x (.head _) z (.tail _ hzMem) hEq
    exact hNotMem z hzMem hxz

private theorem exists_mem_of_filter_length_lt_fq {α : Type} (p : α → Bool) :
    ∀ (xs : List α), (xs.filter p).length < xs.length → ∃ x ∈ xs, p x = false
  | [], h => by simp at h
  | x :: xs, h => by
    cases hpx : p x
    · exact ⟨x, .head _, hpx⟩
    · simp only [List.filter_cons_of_pos hpx, List.length_cons] at h
      obtain ⟨y, hyMem, hyFalse⟩ := exists_mem_of_filter_length_lt_fq p xs (by omega)
      exact ⟨y, .tail _ hyMem, hyFalse⟩

private theorem exists_eval_nonzero_fq204 :
    ∀ (cs : List Fq204), cs.length < mldsaQ →
      (∃ c ∈ cs, c ≠ Fq204.zero) →
      ∃ x : Fq204, RoundPoly.evalCoeffs cs x ≠ CommRingOps.zero
  | [], _, ⟨_, hMem, _⟩ => by cases hMem
  | c₀ :: tail, hLen, ⟨c, hMem, hcNe⟩ => by
    if hc0Ne : c₀ ≠ Fq204.zero then
      refine ⟨Fq204.zero, ?_⟩
      change Fq204.add c₀ (Fq204.mul Fq204.zero (RoundPoly.evalCoeffs tail Fq204.zero)) ≠ Fq204.zero
      rw [Fq204.zero_mul, Fq204.add_zero]
      exact hc0Ne
    else
      have hc0Eq : c₀ = Fq204.zero := by
        cases decEq c₀ Fq204.zero with
        | isTrue h => exact h
        | isFalse h => exact False.elim (hc0Ne h)
      subst hc0Eq
      have hTailEx : ∃ c' ∈ tail, c' ≠ Fq204.zero := by
        rcases List.mem_cons.mp hMem with rfl | hInTail
        · exact False.elim (hcNe rfl)
        · exact ⟨c, hInTail, hcNe⟩
      have hTailPos : 1 ≤ tail.length := by
        rcases hTailEx with ⟨_, hm, _⟩
        cases tail with
        | nil => cases hm
        | cons _ _ => simp only [List.length_cons]; omega
      simp only [List.length_cons] at hLen
      obtain ⟨x₁, hx₁⟩ := exists_eval_nonzero_fq204 tail (by omega) hTailEx
      let d := tail.length - 1
      let grid : List Fq204 := (List.range (d + 1)).map (fun i => Fq204.ofNat (i + 1))
      have hGridLen : grid.length = d + 1 := by simp [grid]
      have hGridNodup : grid.Nodup := by
        apply nodup_map_on_list_fq _ (Qsag.Constructive.nodup_range (d + 1))
        intro a ha b hb hEq
        have haLt : a + 1 < mldsaQ := by have := List.mem_range.mp ha; omega
        have hbLt : b + 1 < mldsaQ := by have := List.mem_range.mp hb; omega
        have hVal := congrArg Fq204.val hEq
        simp only [Fq204.ofNat_val, Nat.mod_eq_of_lt haLt, Nat.mod_eq_of_lt hbLt] at hVal
        omega
      have hRootsLe :
          (grid.filter (fun r => decide (RoundPoly.evalCoeffs tail r = CommRingOps.zero))).length ≤ d :=
        RoundPoly.roots_nodup_length_le d tail grid hGridNodup (by omega) ⟨x₁, hx₁⟩
      have hFiltLt :
          (grid.filter (fun r => decide (RoundPoly.evalCoeffs tail r = CommRingOps.zero))).length < grid.length := by
        rw [hGridLen]; omega
      obtain ⟨x₀, hx₀Mem, hx₀False⟩ := exists_mem_of_filter_length_lt_fq
        (fun r => decide (RoundPoly.evalCoeffs tail r = CommRingOps.zero)) grid hFiltLt
      have hx₀NeZero : x₀ ≠ Fq204.zero := by
        rcases List.mem_map.mp hx₀Mem with ⟨idx, hIdxRange, rfl⟩
        have hIdxLt : idx + 1 < mldsaQ := by have := List.mem_range.mp hIdxRange; omega
        intro hZero
        have hv := congrArg Fq204.val hZero
        simp only [Fq204.ofNat_val, Nat.mod_eq_of_lt hIdxLt, Fq204.zero_val] at hv
        omega
      have hEvalTailNe : RoundPoly.evalCoeffs tail x₀ ≠ CommRingOps.zero := by
        intro hZero
        rw [decide_eq_true hZero] at hx₀False
        cases hx₀False
      refine ⟨x₀, ?_⟩
      change Fq204.add Fq204.zero (Fq204.mul x₀ (RoundPoly.evalCoeffs tail x₀)) ≠ Fq204.zero
      rw [Fq204.zero_add]
      intro hProdZero
      rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hProdZero with h1 | h2
      · exact hx₀NeZero h1
      · exact hEvalTailNe h2

/-- **Numeric Modulus Certificate & Base-Scalar Batch Bound for $\mathbb{F}_q[X]/(X^6 - 7)$ (`rss_mpc.rs:53-56, 1066-1206`)**:
    1. Serret–Kummer binomial irreducibility certificate for $X^6 - 7$ over $\mathbb{F}_{8380417}$:
       $6 \mid (q - 1)$, $7^{(q-1)/2} \equiv q - 1 \not\equiv 1 \pmod q$ ($7$ is a quadratic non-residue),
       $7^{(q-1)/3} \not\equiv 1 \pmod q$ ($7$ is a cubic non-residue), and $2^{137} < q^6$.
    2. Unique `Ext6Fq204` batch root: for any nonzero base-field gate error $\Delta \ne 0$ and arbitrary
       batch accumulator `rest`, `ext6Add rest (ext6Scale chi Δ) = ext6Zero` holds for **at most 1**
       challenge `chi : Ext6Fq204` (`(ext6BatchChallengeEquiv Δ hΔ rest).invFun ext6Zero`).
    3. Recursive polynomial folding bound (`rss_mpc.rs:1120-1171`, `FOLD = 8`): any degree-$\le D$
       ($D + 1 < q$) folding discrepancy polynomial with a nonzero coefficient has $\le D$ roots
       in any duplicate-free point set `S : List Fq204`. -/
theorem rss_ext6_modulus_certificate_and_batch_sacrifice_sound :
    ((mldsaQ - 1) % 6 = 0 ∧
     fq204PowModNat 7 ((mldsaQ - 1) / 2) = mldsaQ - 1 ∧
     fq204PowModNat 7 ((mldsaQ - 1) / 2) ≠ 1 ∧
     fq204PowModNat 7 ((mldsaQ - 1) / 3) ≠ 1 ∧
     2 ^ 137 < mldsaQ ^ 6) ∧
    (∀ (delta : Fq204) (_hDelta : delta ≠ Fq204.zero) (rest chi₁ chi₂ : Ext6Fq204),
      ext6Add rest (ext6Scale chi₁ delta) = ext6Zero →
      ext6Add rest (ext6Scale chi₂ delta) = ext6Zero →
      chi₁ = chi₂) ∧
    (∀ (D : Nat) (cs S : List Fq204),
      D + 1 < mldsaQ →
      cs.length ≤ D + 1 →
      S.Nodup →
      (∃ c ∈ cs, c ≠ Fq204.zero) →
      (S.filter (fun r => decide (RoundPoly.evalCoeffs cs r = CommRingOps.zero))).length ≤ D) := by
  refine ⟨by decide, ?_, ?_⟩
  · intro delta hDelta rest chi₁ chi₂ h1 h2
    let eqv := ext6BatchChallengeEquiv delta hDelta rest
    have hEq : eqv.toFun chi₁ = eqv.toFun chi₂ := h1.trans h2.symm
    have hInv := congrArg eqv.invFun hEq
    rwa [eqv.left_inv, eqv.left_inv] at hInv
  · intro D cs S hDLt hLen hNodup hNz
    obtain ⟨x₀, hx₀⟩ := exists_eval_nonzero_fq204 cs (by omega) hNz
    exact RoundPoly.roots_nodup_length_le D cs S hNodup hLen ⟨x₀, hx₀⟩

/-! ## Binary modular powers and Rabin unit certificates for the extension

The normal form of `X^n` modulo `X^6 - 7` is `7^(n/6) X^(n%6)`.
The certificates below provide quotient-ring inverses of `X^(q^2)-X` and
`X^(q^3)-X`, and the sixth Frobenius identity. The section after them turns the same
Frobenius scalars into an inverse for every nonzero element.
-/

def ext6Monomial204 (degree : Nat) (coefficient : Fq204) : Ext6Fq204 :=
  match degree with
  | 0 => ⟨coefficient, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero⟩
  | 1 => ⟨Fq204.zero, coefficient, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero⟩
  | 2 => ⟨Fq204.zero, Fq204.zero, coefficient, Fq204.zero, Fq204.zero, Fq204.zero⟩
  | 3 => ⟨Fq204.zero, Fq204.zero, Fq204.zero, coefficient, Fq204.zero, Fq204.zero⟩
  | 4 => ⟨Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero, coefficient, Fq204.zero⟩
  | _ => ⟨Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero, coefficient⟩

def ext6XPower204 (n : Nat) : Ext6Fq204 :=
  ext6Monomial204 (n % 6) (Fq204.pow (Fq204.ofNat 7) (n / 6))

/-- Logarithmic coefficient exponentiation for the binomial normal form. -/
def ext6XPowerFast204 (fuel n : Nat) : Ext6Fq204 :=
  ext6Monomial204 (n % 6) (Fq204.ofNat (modPowFuel fuel 7 (n / 6) mldsaQ))

theorem ext6XPowerFast204_correct (fuel n : Nat) (h : n / 6 < 2 ^ fuel) :
    ext6XPowerFast204 fuel n = ext6XPower204 n := by
  unfold ext6XPowerFast204 ext6XPower204
  congr 1
  apply Fq204.ext
  rw [Fq204.ofNat_val, modPowFuel_eq_pow_mod fuel 7 (n / 6) mldsaQ h,
    Nat.mod_mod, Fq204.pow_val]
  rfl

theorem ext6XPower204_succ (n : Nat) :
    ext6Mul (ext6XPower204 n) (ext6Monomial204 1 Fq204.one) = ext6XPower204 (n + 1) := by
  have hr : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega
  rcases hr with h | h | h | h | h | h
  · have hd : (n + 1) / 6 = n / 6 := by omega
    have hm : (n + 1) % 6 = 1 := by omega
    simp only [ext6XPower204, h, hd, hm, ext6Monomial204, ext6Mul,
      Fq204.mul_zero, Fq204.mul_one, Fq204.add_zero]
  · have hd : (n + 1) / 6 = n / 6 := by omega
    have hm : (n + 1) % 6 = 2 := by omega
    simp only [ext6XPower204, h, hd, hm, ext6Monomial204, ext6Mul,
      Fq204.mul_zero, Fq204.mul_one, Fq204.add_zero, Fq204.zero_add]
  · have hd : (n + 1) / 6 = n / 6 := by omega
    have hm : (n + 1) % 6 = 3 := by omega
    simp only [ext6XPower204, h, hd, hm, ext6Monomial204, ext6Mul,
      Fq204.mul_zero, Fq204.mul_one, Fq204.add_zero, Fq204.zero_add]
  · have hd : (n + 1) / 6 = n / 6 := by omega
    have hm : (n + 1) % 6 = 4 := by omega
    simp only [ext6XPower204, h, hd, hm, ext6Monomial204, ext6Mul,
      Fq204.mul_zero, Fq204.mul_one, Fq204.add_zero, Fq204.zero_add]
  · have hd : (n + 1) / 6 = n / 6 := by omega
    have hm : (n + 1) % 6 = 5 := by omega
    simp only [ext6XPower204, h, hd, hm, ext6Monomial204, ext6Mul,
      Fq204.mul_zero, Fq204.mul_one, Fq204.add_zero, Fq204.zero_add]
  · have hd : (n + 1) / 6 = n / 6 + 1 := by omega
    have hm : (n + 1) % 6 = 0 := by omega
    simp only [ext6XPower204, h, hd, hm, ext6Monomial204, ext6Mul,
      Fq204.mul_zero, Fq204.mul_one, Fq204.add_zero, Fq204.zero_add]
    rw [Fq204.pow, Fq204.mul_comm]
    rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- Explicit units modulo the actual multiplication law; these are the two
coprimality certificates required for degree six. -/
theorem ext6RabinUnits204 :
    ext6Mul (ext6Sub (ext6XPowerFast204 160 (mldsaQ ^ 2)) (ext6Monomial204 1 Fq204.one))
      (ext6Monomial204 5 (Fq204.ofNat 2748270)) = ext6EmbedFq Fq204.one ∧
    ext6Mul (ext6Sub (ext6XPowerFast204 160 (mldsaQ ^ 3)) (ext6Monomial204 1 Fq204.one))
      (ext6Monomial204 5 (Fq204.ofNat 2993006)) = ext6EmbedFq Fq204.one ∧
    ext6XPowerFast204 160 (mldsaQ ^ 6) = ext6Monomial204 1 Fq204.one := by
  have h2 : ext6XPowerFast204 160 (mldsaQ ^ 2) = ext6Monomial204 1 (Fq204.ofNat 949247) := by decide
  have h3 : ext6XPowerFast204 160 (mldsaQ ^ 3) = ext6Monomial204 1 (Fq204.ofNat 8380416) := by decide
  have h6 : ext6XPowerFast204 160 (mldsaQ ^ 6) = ext6Monomial204 1 Fq204.one := by decide
  rw [h2, h3, h6]
  decide


/-- The same certificates for powers characterized by the multiplication
recurrence, rather than just for the fast evaluator. -/
theorem ext6RabinCertificate204 :
    ext6Mul (ext6Sub (ext6XPower204 (mldsaQ ^ 2)) (ext6Monomial204 1 Fq204.one))
      (ext6Monomial204 5 (Fq204.ofNat 2748270)) = ext6EmbedFq Fq204.one ∧
    ext6Mul (ext6Sub (ext6XPower204 (mldsaQ ^ 3)) (ext6Monomial204 1 Fq204.one))
      (ext6Monomial204 5 (Fq204.ofNat 2993006)) = ext6EmbedFq Fq204.one ∧
    ext6XPower204 (mldsaQ ^ 6) = ext6Monomial204 1 Fq204.one := by
  rw [← ext6XPowerFast204_correct 160 (mldsaQ ^ 2) (by decide),
    ← ext6XPowerFast204_correct 160 (mldsaQ ^ 3) (by decide),
    ← ext6XPowerFast204_correct 160 (mldsaQ ^ 6) (by decide)]
  exact ext6RabinUnits204


/-! ## The extension ring is a field

`Ext6Fq204` is `F_q[X]/(X^6 - 7)`. The `q`-th power map is a ring endomorphism in
characteristic `q` (`ext6Pow_add_frobenius`), fixes the base field
(`ext6Pow_embed_frobenius`), and sends `X` to `ζ X` with `ζ = 7^((q-1)/6)`, so it acts on
coordinates by `a_i ↦ ζ^i a_i` (`ext6Pow_frobenius`). The Rabin conditions say that
`X^(q^2) ≠ X` and `X^(q^3) ≠ X` while `X^(q^6) = X`; in coordinates, an element fixed by
the second and third Frobenius iterates is a base-field constant
(`ext6_rabin_fixed_is_constant`). The norm `a · a^q ⋯ a^(q^5)` is such an element and is
nonzero when `a` is, which gives an explicit inverse (`ext6Inv`, `ext6Mul_inv_cancel`),
zero-divisor freedom (`ext6Mul_eq_zero`) and irreducibility of the modulus
(`ext6Modulus_irreducible`).
-/

section Ext6Field

local instance : Std.Associative Fq204.add := ⟨Fq204.add_assoc⟩
local instance : Std.Commutative Fq204.add := ⟨Fq204.add_comm⟩
local instance : Std.Associative Fq204.mul := ⟨Fq204.mul_assoc⟩
local instance : Std.Commutative Fq204.mul := ⟨Fq204.mul_comm⟩

def ext6One : Ext6Fq204 := ext6EmbedFq Fq204.one

theorem ext6Add_assoc (x y z : Ext6Fq204) :
    ext6Add (ext6Add x y) z = ext6Add x (ext6Add y z) := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
  rcases y with ⟨y0, y1, y2, y3, y4, y5⟩
  rcases z with ⟨z0, z1, z2, z3, z4, z5⟩
  simp only [ext6Add, Fq204.add_assoc]

theorem ext6Add_comm (x y : Ext6Fq204) : ext6Add x y = ext6Add y x := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
  rcases y with ⟨y0, y1, y2, y3, y4, y5⟩
  simp only [ext6Add, Ext6Fq204.mk.injEq]
  exact ⟨Fq204.add_comm _ _, Fq204.add_comm _ _, Fq204.add_comm _ _, Fq204.add_comm _ _,
    Fq204.add_comm _ _, Fq204.add_comm _ _⟩

theorem ext6Add_zero (x : Ext6Fq204) : ext6Add x ext6Zero = x := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
  simp only [ext6Add, ext6Zero, Fq204.add_zero]

theorem ext6Zero_add (x : Ext6Fq204) : ext6Add ext6Zero x = x := by
  rw [ext6Add_comm, ext6Add_zero]

theorem ext6Add_add_add_comm (a b c d : Ext6Fq204) :
    ext6Add (ext6Add a b) (ext6Add c d) = ext6Add (ext6Add a c) (ext6Add b d) := by
  rw [ext6Add_assoc, ext6Add_assoc, ← ext6Add_assoc b c d, ext6Add_comm b c,
    ext6Add_assoc c b d]

local instance : Std.Associative ext6Add := ⟨ext6Add_assoc⟩
local instance : Std.Commutative ext6Add := ⟨ext6Add_comm⟩

theorem ext6Mul_comm (x y : Ext6Fq204) : ext6Mul x y = ext6Mul y x := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
  rcases y with ⟨y0, y1, y2, y3, y4, y5⟩
  simp only [ext6Mul, Ext6Fq204.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ac_rfl

set_option maxHeartbeats 4000000 in
theorem ext6Mul_assoc (x y z : Ext6Fq204) :
    ext6Mul (ext6Mul x y) z = ext6Mul x (ext6Mul y z) := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
  rcases y with ⟨y0, y1, y2, y3, y4, y5⟩
  rcases z with ⟨z0, z1, z2, z3, z4, z5⟩
  simp only [ext6Mul, Ext6Fq204.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [Fq204.left_distrib, Fq204.right_distrib]; ac_rfl)

theorem ext6Mul_add (x y z : Ext6Fq204) :
    ext6Mul x (ext6Add y z) = ext6Add (ext6Mul x y) (ext6Mul x z) := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
  rcases y with ⟨y0, y1, y2, y3, y4, y5⟩
  rcases z with ⟨z0, z1, z2, z3, z4, z5⟩
  simp only [ext6Mul, ext6Add, Ext6Fq204.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (simp only [Fq204.left_distrib]; ac_rfl)

theorem ext6Add_mul (x y z : Ext6Fq204) :
    ext6Mul (ext6Add x y) z = ext6Add (ext6Mul x z) (ext6Mul y z) := by
  rw [ext6Mul_comm, ext6Mul_add, ext6Mul_comm z x, ext6Mul_comm z y]

theorem ext6Mul_one (x : Ext6Fq204) : ext6Mul x ext6One = x := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
  simp only [ext6Mul, ext6One, ext6EmbedFq, Fq204.mul_zero, Fq204.mul_one, Fq204.add_zero,
    Fq204.zero_add]

theorem ext6One_mul (x : Ext6Fq204) : ext6Mul ext6One x = x := by
  rw [ext6Mul_comm, ext6Mul_one]

theorem ext6Mul_zero (x : Ext6Fq204) : ext6Mul x ext6Zero = ext6Zero := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
  simp only [ext6Mul, ext6Zero, Fq204.mul_zero, Fq204.add_zero]

theorem ext6Zero_mul (x : Ext6Fq204) : ext6Mul ext6Zero x = ext6Zero := by
  rw [ext6Mul_comm, ext6Mul_zero]

local instance : Std.Associative ext6Mul := ⟨ext6Mul_assoc⟩
local instance : Std.Commutative ext6Mul := ⟨ext6Mul_comm⟩

theorem ext6Scale_eq_mul_embed (x : Ext6Fq204) (s : Fq204) :
    ext6Scale x s = ext6Mul x (ext6EmbedFq s) := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
  simp only [ext6Mul, ext6Scale, ext6EmbedFq, Fq204.mul_zero, Fq204.add_zero, Fq204.zero_add]

theorem ext6Mul_scale_right (x y : Ext6Fq204) (s : Fq204) :
    ext6Mul x (ext6Scale y s) = ext6Scale (ext6Mul x y) s := by
  rw [ext6Scale_eq_mul_embed, ext6Scale_eq_mul_embed, ext6Mul_assoc]

theorem ext6Mul_scale_left (x y : Ext6Fq204) (s : Fq204) :
    ext6Mul (ext6Scale x s) y = ext6Scale (ext6Mul x y) s := by
  rw [ext6Mul_comm, ext6Mul_scale_right, ext6Mul_comm]

theorem ext6Scale_zero (x : Ext6Fq204) : ext6Scale x Fq204.zero = ext6Zero := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
  simp only [ext6Scale, ext6Zero, Fq204.mul_zero]

theorem ext6Scale_add_scalar (x : Ext6Fq204) (s t : Fq204) :
    ext6Scale x (Fq204.add s t) = ext6Add (ext6Scale x s) (ext6Scale x t) := by
  rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
  simp only [ext6Scale, ext6Add, Fq204.left_distrib]

theorem ext6Scale_embed (c s : Fq204) :
    ext6Scale (ext6EmbedFq c) s = ext6EmbedFq (Fq204.mul c s) := by
  simp only [ext6Scale, ext6EmbedFq, Fq204.zero_mul]

theorem ext6Embed_add (a b : Fq204) :
    ext6EmbedFq (Fq204.add a b) = ext6Add (ext6EmbedFq a) (ext6EmbedFq b) := by
  simp only [ext6EmbedFq, ext6Add, Fq204.add_zero]

/-- Powers under the extension multiplication. -/
def ext6Pow (a : Ext6Fq204) : Nat → Ext6Fq204
  | 0 => ext6One
  | n + 1 => ext6Mul (ext6Pow a n) a

theorem ext6Pow_zero (a : Ext6Fq204) : ext6Pow a 0 = ext6One := by rfl

theorem ext6Pow_succ (a : Ext6Fq204) (n : Nat) :
    ext6Pow a (n + 1) = ext6Mul (ext6Pow a n) a := by rfl

theorem ext6Pow_one (a : Ext6Fq204) : ext6Pow a 1 = a := by
  rw [ext6Pow_succ, ext6Pow_zero, ext6One_mul]

theorem ext6Pow_add (a : Ext6Fq204) (m n : Nat) :
    ext6Pow a (m + n) = ext6Mul (ext6Pow a m) (ext6Pow a n) := by
  induction n with
  | zero => rw [Nat.add_zero, ext6Pow_zero, ext6Mul_one]
  | succ n ih => rw [← Nat.add_assoc, ext6Pow_succ, ext6Pow_succ, ih, ext6Mul_assoc]

theorem ext6Pow_mul (a : Ext6Fq204) (m n : Nat) :
    ext6Pow a (m * n) = ext6Pow (ext6Pow a m) n := by
  induction n with
  | zero => rw [Nat.mul_zero, ext6Pow_zero, ext6Pow_zero]
  | succ n ih => rw [Nat.mul_succ, ext6Pow_add, ih, ext6Pow_succ]

theorem ext6Mul_pow (a b : Ext6Fq204) (n : Nat) :
    ext6Pow (ext6Mul a b) n = ext6Mul (ext6Pow a n) (ext6Pow b n) := by
  induction n with
  | zero => rw [ext6Pow_zero, ext6Pow_zero, ext6Pow_zero, ext6Mul_one]
  | succ n ih =>
    rw [ext6Pow_succ, ext6Pow_succ, ext6Pow_succ, ih]
    ac_rfl

theorem ext6Pow_one_base (n : Nat) : ext6Pow ext6One n = ext6One := by
  induction n with
  | zero => rfl
  | succ n ih => rw [ext6Pow_succ, ih, ext6Mul_one]

theorem ext6Pow_zero_base {n : Nat} (hn : 0 < n) : ext6Pow ext6Zero n = ext6Zero := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [ext6Pow_succ, ext6Mul_zero]

theorem ext6Pow_scale (a : Ext6Fq204) (s : Fq204) (n : Nat) :
    ext6Pow (ext6Scale a s) n = ext6Scale (ext6Pow a n) (Fq204.pow s n) := by
  induction n with
  | zero =>
    rw [ext6Pow_zero, ext6Pow_zero]
    exact (ext6Scale_one _).symm
  | succ n ih =>
    rw [ext6Pow_succ, ext6Pow_succ, ih, ext6Mul_scale_right, ext6Mul_scale_left, ext6Scale_mul]
    rfl

