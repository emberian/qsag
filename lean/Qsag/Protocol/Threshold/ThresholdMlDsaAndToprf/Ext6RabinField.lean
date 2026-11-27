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

/-! ### Binomial coefficients and the characteristic-`q` power of a sum -/

private def choose204 : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose204 n k + choose204 n (k + 1)

private theorem choose204_zero_right (n : Nat) : choose204 n 0 = 1 := by
  cases n <;> rfl

private theorem choose204_succ_succ (n k : Nat) :
    choose204 (n + 1) (k + 1) = choose204 n k + choose204 n (k + 1) := rfl

private theorem choose204_eq_zero_of_lt : ∀ (n k : Nat), n < k → choose204 n k = 0
  | _, 0, h => by omega
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    rw [choose204_succ_succ, choose204_eq_zero_of_lt n k (by omega),
      choose204_eq_zero_of_lt n (k + 1) (by omega)]

private theorem choose204_self : ∀ n : Nat, choose204 n n = 1
  | 0 => rfl
  | n + 1 => by
    rw [choose204_succ_succ, choose204_self n, choose204_eq_zero_of_lt n (n + 1) (by omega)]

private theorem choose204_one_right : ∀ n : Nat, choose204 n 1 = n
  | 0 => rfl
  | n + 1 => by
    rw [choose204_succ_succ, choose204_zero_right, choose204_one_right n]
    omega

private theorem succ_mul_choose204 :
    ∀ n k : Nat, (k + 1) * choose204 (n + 1) (k + 1) = (n + 1) * choose204 n k
  | 0, 0 => by decide
  | 0, k + 1 => by
    rw [choose204_succ_succ, choose204_eq_zero_of_lt 0 (k + 1) (by omega),
      choose204_eq_zero_of_lt 0 (k + 1 + 1) (by omega)]
    omega
  | n + 1, 0 => by
    rw [choose204_one_right, choose204_zero_right]
    omega
  | n + 1, k + 1 => by
    have h1 := succ_mul_choose204 n k
    have h2 := succ_mul_choose204 n (k + 1)
    rw [choose204_succ_succ (n + 1) (k + 1)]
    rw [choose204_succ_succ n k] at h1 ⊢
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul] at h1 h2 ⊢
    omega

private theorem mldsaQ_dvd_choose204 {k : Nat} (hk0 : 0 < k) (hk : k < mldsaQ) :
    mldsaQ ∣ choose204 mldsaQ k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have h := succ_mul_choose204 (mldsaQ - 1) j
  have hq : mldsaQ - 1 + 1 = mldsaQ := by decide
  rw [hq] at h
  have hdvd : mldsaQ ∣ (j + 1) * choose204 mldsaQ (j + 1) := ⟨_, h⟩
  exact mldsaQ_isPrime.dvd_mul hdvd (fun hd => by
    have := Nat.le_of_dvd (by omega) hd
    omega)

private theorem fq204_ofNat_add (a b : Nat) :
    Fq204.ofNat (a + b) = Fq204.add (Fq204.ofNat a) (Fq204.ofNat b) := by
  apply Fq204.ext
  rw [Fq204.add_val, Fq204.ofNat_val, Fq204.ofNat_val, Fq204.ofNat_val, ← Nat.add_mod]

private theorem fq204_ofNat_one : Fq204.ofNat 1 = Fq204.one := by decide

private theorem fq204_ofNat_zero : Fq204.ofNat 0 = Fq204.zero := by decide

private theorem fq204_ofNat_eq_zero_of_dvd {n : Nat} (h : mldsaQ ∣ n) :
    Fq204.ofNat n = Fq204.zero := by
  apply Fq204.ext
  rw [Fq204.ofNat_val, Nat.mod_eq_zero_of_dvd h]
  rfl

/-- `ext6Binom x y n k` is the degree-`k` term of `(x + y)^n`, built by Pascal's rule. -/
private def ext6Binom (x y : Ext6Fq204) : Nat → Nat → Ext6Fq204
  | 0, 0 => ext6One
  | 0, _ + 1 => ext6Zero
  | n + 1, 0 => ext6Mul (ext6Binom x y n 0) y
  | n + 1, k + 1 =>
    ext6Add (ext6Mul (ext6Binom x y n (k + 1)) y) (ext6Mul (ext6Binom x y n k) x)

private def ext6BinomSum (x y : Ext6Fq204) (n : Nat) : Nat → Ext6Fq204
  | 0 => ext6Zero
  | m + 1 => ext6Add (ext6BinomSum x y n m) (ext6Binom x y n m)

private theorem ext6BinomSum_succ (x y : Ext6Fq204) (n m : Nat) :
    ext6BinomSum x y n (m + 1) = ext6Add (ext6BinomSum x y n m) (ext6Binom x y n m) := rfl

private theorem ext6Binom_zero_succ (x y : Ext6Fq204) (k : Nat) :
    ext6Binom x y 0 (k + 1) = ext6Zero := rfl

private theorem ext6Binom_zero_zero (x y : Ext6Fq204) : ext6Binom x y 0 0 = ext6One := rfl

private theorem ext6BinomSum_zero (x y : Ext6Fq204) (n : Nat) :
    ext6BinomSum x y n 0 = ext6Zero := rfl

private theorem ext6Binom_succ_zero (x y : Ext6Fq204) (n : Nat) :
    ext6Binom x y (n + 1) 0 = ext6Mul (ext6Binom x y n 0) y := rfl

private theorem ext6Binom_succ_succ (x y : Ext6Fq204) (n k : Nat) :
    ext6Binom x y (n + 1) (k + 1) =
      ext6Add (ext6Mul (ext6Binom x y n (k + 1)) y) (ext6Mul (ext6Binom x y n k) x) := rfl

private theorem ext6BinomSum_succ_row (x y : Ext6Fq204) (n m : Nat) :
    ext6BinomSum x y (n + 1) (m + 1) =
      ext6Add (ext6Mul (ext6BinomSum x y n (m + 1)) y) (ext6Mul (ext6BinomSum x y n m) x) := by
  induction m with
  | zero =>
    rw [ext6BinomSum_succ, ext6BinomSum_succ, ext6Binom_succ_zero, ext6BinomSum_zero,
      ext6BinomSum_zero, ext6Zero_add, ext6Zero_add, ext6Zero_mul, ext6Add_zero]
  | succ m ih =>
    have hx : ext6Mul (ext6BinomSum x y n (m + 1)) x =
        ext6Add (ext6Mul (ext6BinomSum x y n m) x) (ext6Mul (ext6Binom x y n m) x) := by
      rw [ext6BinomSum_succ, ext6Add_mul]
    rw [ext6BinomSum_succ x y (n + 1), ih, ext6Binom_succ_succ,
      ext6BinomSum_succ x y n (m + 1), ext6Add_mul, hx]
    exact ext6Add_add_add_comm _ _ _ _

private theorem ext6Binom_closed (x y : Ext6Fq204) (n : Nat) :
    (∀ k, n < k → ext6Binom x y n k = ext6Zero) ∧
    (∀ k j, k + j = n → ext6Binom x y n k =
      ext6Scale (ext6Mul (ext6Pow x k) (ext6Pow y j)) (Fq204.ofNat (choose204 n k))) := by
  induction n with
  | zero =>
    refine ⟨fun k hk => ?_, fun k j h => ?_⟩
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact ext6Binom_zero_succ x y k'
    · have hk0 : k = 0 := by omega
      have hj0 : j = 0 := by omega
      subst hk0
      subst hj0
      rw [ext6Pow_zero, ext6Pow_zero, ext6Mul_one, choose204_zero_right, fq204_ofNat_one,
        ext6Scale_one, ext6Binom_zero_zero]
  | succ n ih =>
    obtain ⟨ihZ, ihC⟩ := ih
    refine ⟨fun k hk => ?_, fun k j h => ?_⟩
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [ext6Binom_succ_succ, ihZ (k' + 1) (by omega), ihZ k' (by omega), ext6Zero_mul,
        ext6Zero_mul, ext6Add_zero]
    · cases k with
      | zero =>
        have hj : j = n + 1 := by omega
        subst hj
        rw [ext6Binom_succ_zero, ihC 0 n (by omega), choose204_zero_right, choose204_zero_right,
          fq204_ofNat_one, ext6Scale_one, ext6Scale_one, ext6Pow_zero, ext6One_mul, ext6One_mul,
          ext6Pow_succ]
      | succ k' =>
        have hkj : k' + j = n := by omega
        have hSecond : ext6Mul (ext6Mul (ext6Pow x k') (ext6Pow y j)) x =
            ext6Mul (ext6Pow x (k' + 1)) (ext6Pow y j) := by
          rw [ext6Pow_succ, ext6Mul_assoc, ext6Mul_comm (ext6Pow y j) x, ← ext6Mul_assoc]
        have hFirst : ext6Mul (ext6Binom x y n (k' + 1)) y =
            ext6Scale (ext6Mul (ext6Pow x (k' + 1)) (ext6Pow y j))
              (Fq204.ofNat (choose204 n (k' + 1))) := by
          cases j with
          | zero =>
            rw [ihZ (k' + 1) (by omega), choose204_eq_zero_of_lt n (k' + 1) (by omega),
              fq204_ofNat_zero, ext6Scale_zero, ext6Zero_mul]
          | succ j' =>
            rw [ihC (k' + 1) j' (by omega), ext6Mul_scale_left, ext6Pow_succ y j',
              ext6Mul_assoc]
        rw [ext6Binom_succ_succ, hFirst, ihC k' j hkj, ext6Mul_scale_left, hSecond,
          choose204_succ_succ, fq204_ofNat_add, ext6Scale_add_scalar, ext6Add_comm]

private theorem ext6Pow_add_base (x y : Ext6Fq204) (n : Nat) :
    ext6Pow (ext6Add x y) n = ext6BinomSum x y n (n + 1) := by
  induction n with
  | zero =>
    rw [ext6Pow_zero, ext6BinomSum_succ, ext6BinomSum_zero, ext6Binom_zero_zero, ext6Zero_add]
  | succ n ih =>
    have hz : ext6BinomSum x y n (n + 1 + 1) = ext6BinomSum x y n (n + 1) := by
      rw [ext6BinomSum_succ x y n (n + 1), (ext6Binom_closed x y n).1 (n + 1) (by omega),
        ext6Add_zero]
    rw [ext6Pow_succ, ext6BinomSum_succ_row, ih, hz, ext6Mul_add, ext6Add_comm]

private theorem ext6BinomSum_of_middle_zero (x y : Ext6Fq204) (n m : Nat)
    (h : ∀ k, 0 < k → k < m + 1 → ext6Binom x y n k = ext6Zero) :
    ext6BinomSum x y n (m + 1) = ext6Binom x y n 0 := by
  induction m with
  | zero => rw [ext6BinomSum_succ, ext6BinomSum_zero, ext6Zero_add]
  | succ m ih =>
    rw [ext6BinomSum_succ, ih (fun k h0 hk => h k h0 (by omega)),
      h (m + 1) (by omega) (by omega), ext6Add_zero]

/-- The `q`-th power map is additive on the extension. -/
theorem ext6Pow_add_frobenius (x y : Ext6Fq204) :
    ext6Pow (ext6Add x y) mldsaQ = ext6Add (ext6Pow x mldsaQ) (ext6Pow y mldsaQ) := by
  obtain ⟨hZero, hClosed⟩ := ext6Binom_closed x y mldsaQ
  have hMid : ∀ k, 0 < k → k < (mldsaQ - 1) + 1 → ext6Binom x y mldsaQ k = ext6Zero := by
    intro k hk0 hk
    have hkq : k < mldsaQ := by
      have hq : mldsaQ - 1 + 1 = mldsaQ := by decide
      omega
    rw [hClosed k (mldsaQ - k) (by omega),
      fq204_ofNat_eq_zero_of_dvd (mldsaQ_dvd_choose204 hk0 hkq), ext6Scale_zero]
  have hSum := ext6BinomSum_of_middle_zero x y mldsaQ (mldsaQ - 1) hMid
  have hq : mldsaQ - 1 + 1 = mldsaQ := by decide
  rw [hq] at hSum
  rw [ext6Pow_add_base, ext6BinomSum_succ, hSum, hClosed 0 mldsaQ (Nat.zero_add _),
    hClosed mldsaQ 0 (Nat.add_zero _), choose204_zero_right, choose204_self, fq204_ofNat_one,
    ext6Scale_one, ext6Scale_one, ext6Pow_zero, ext6Pow_zero, ext6One_mul, ext6Mul_one,
    ext6Add_comm]

/-- Fermat's little theorem for base-field constants, inside the extension. -/
theorem ext6Pow_embed_frobenius (c : Fq204) :
    ext6Pow (ext6EmbedFq c) mldsaQ = ext6EmbedFq c := by
  have h : ∀ n : Nat,
      ext6Pow (ext6EmbedFq (Fq204.ofNat n)) mldsaQ = ext6EmbedFq (Fq204.ofNat n) := by
    intro n
    induction n with
    | zero =>
      have hz : ext6EmbedFq (Fq204.ofNat 0) = ext6Zero := by decide
      rw [hz]
      exact ext6Pow_zero_base (by decide)
    | succ n ih =>
      rw [fq204_ofNat_add, ext6Embed_add, ext6Pow_add_frobenius, ih, fq204_ofNat_one]
      show ext6Add _ (ext6Pow ext6One mldsaQ) = _
      rw [ext6Pow_one_base]
      rfl
  have hc : Fq204.ofNat c.val = c :=
    Fq204.ext (by rw [Fq204.ofNat_val]; exact Nat.mod_eq_of_lt c.isLt)
  rw [← hc]
  exact h c.val

/-! ### Frobenius in coordinates -/

/-- `ζ = 7^((q-1)/6)`, the scalar with `X^q = ζ X`. It has multiplicative order six. -/
def ext6FrobeniusZeta : Fq204 := Fq204.ofNat 949248

/-- Coordinate action `a_i ↦ c^i a_i`, the substitution `X ↦ c X`. -/
def ext6Twist (c : Fq204) (a : Ext6Fq204) : Ext6Fq204 :=
  let c2 := Fq204.mul c c
  let c3 := Fq204.mul c2 c
  let c4 := Fq204.mul c3 c
  let c5 := Fq204.mul c4 c
  ⟨a.a0, Fq204.mul a.a1 c, Fq204.mul a.a2 c2, Fq204.mul a.a3 c3, Fq204.mul a.a4 c4,
    Fq204.mul a.a5 c5⟩

theorem ext6Twist_twist (c d : Fq204) (a : Ext6Fq204) :
    ext6Twist c (ext6Twist d a) = ext6Twist (Fq204.mul d c) a := by
  rcases a with ⟨a0, a1, a2, a3, a4, a5⟩
  simp only [ext6Twist, Ext6Fq204.mk.injEq]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_⟩ <;> ac_rfl

theorem ext6Twist_one (a : Ext6Fq204) : ext6Twist Fq204.one a = a := by
  rcases a with ⟨a0, a1, a2, a3, a4, a5⟩
  simp only [ext6Twist, Fq204.mul_one]

theorem ext6Pow_X (n : Nat) :
    ext6Pow (ext6Monomial204 1 Fq204.one) n = ext6XPower204 n := by
  induction n with
  | zero => decide
  | succ n ih => rw [ext6Pow_succ, ih, ext6XPower204_succ]

set_option maxRecDepth 8192 in
theorem ext6XPower204_q :
    ext6XPower204 mldsaQ = ext6Scale (ext6Monomial204 1 Fq204.one) ext6FrobeniusZeta := by
  rw [← ext6XPowerFast204_correct 24 mldsaQ (by decide)]
  decide

private def ext6Term (i : Nat) (c : Fq204) : Ext6Fq204 :=
  ext6Mul (ext6EmbedFq c) (ext6Pow (ext6Monomial204 1 Fq204.one) i)

private theorem ext6Term_frobenius (i : Nat) (c : Fq204) :
    ext6Pow (ext6Term i c) mldsaQ =
      ext6Mul (ext6EmbedFq c)
        (ext6Scale (ext6Pow (ext6Monomial204 1 Fq204.one) i) (Fq204.pow ext6FrobeniusZeta i)) := by
  rw [ext6Term, ext6Mul_pow, ext6Pow_embed_frobenius, ← ext6Pow_mul, Nat.mul_comm, ext6Pow_mul,
    ext6Pow_X mldsaQ, ext6XPower204_q, ext6Pow_scale]

private theorem ext6Pow_X_small :
    ext6Pow (ext6Monomial204 1 Fq204.one) 0 = ext6Monomial204 0 Fq204.one ∧
    ext6Pow (ext6Monomial204 1 Fq204.one) 1 = ext6Monomial204 1 Fq204.one ∧
    ext6Pow (ext6Monomial204 1 Fq204.one) 2 = ext6Monomial204 2 Fq204.one ∧
    ext6Pow (ext6Monomial204 1 Fq204.one) 3 = ext6Monomial204 3 Fq204.one ∧
    ext6Pow (ext6Monomial204 1 Fq204.one) 4 = ext6Monomial204 4 Fq204.one ∧
    ext6Pow (ext6Monomial204 1 Fq204.one) 5 = ext6Monomial204 5 Fq204.one := by
  decide

/-- **Frobenius in coordinates.** `a^q = (a_0, ζ a_1, ζ^2 a_2, …, ζ^5 a_5)`. -/
theorem ext6Pow_frobenius (a : Ext6Fq204) :
    ext6Pow a mldsaQ = ext6Twist ext6FrobeniusZeta a := by
  rcases a with ⟨a0, a1, a2, a3, a4, a5⟩
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := ext6Pow_X_small
  have hdecomp : (⟨a0, a1, a2, a3, a4, a5⟩ : Ext6Fq204) =
      ext6Add (ext6Term 0 a0) (ext6Add (ext6Term 1 a1) (ext6Add (ext6Term 2 a2)
        (ext6Add (ext6Term 3 a3) (ext6Add (ext6Term 4 a4) (ext6Term 5 a5))))) := by
    simp only [ext6Term, h0, h1, h2, h3, h4, h5]
    simp only [ext6Monomial204, ext6Mul, ext6EmbedFq, ext6Add,
      Fq204.mul_zero, Fq204.mul_one, Fq204.add_zero, Fq204.zero_add]
  rw [congrArg (fun t => ext6Pow t mldsaQ) hdecomp]
  simp only [ext6Pow_add_frobenius, ext6Term_frobenius]
  simp only [h0, h1, h2, h3, h4, h5]
  simp only [ext6Monomial204, ext6Mul, ext6EmbedFq, ext6Add, ext6Scale,
    ext6Twist, Fq204.pow,
    Fq204.mul_zero, Fq204.zero_mul, Fq204.mul_one, Fq204.one_mul, Fq204.add_zero,
    Fq204.zero_add]

private theorem ext6Zeta_powers :
    Fq204.mul ext6FrobeniusZeta ext6FrobeniusZeta = Fq204.ofNat 949247 ∧
    Fq204.mul (Fq204.ofNat 949247) ext6FrobeniusZeta = Fq204.ofNat 8380416 ∧
    Fq204.mul (Fq204.ofNat 8380416) ext6FrobeniusZeta = Fq204.ofNat 7431169 ∧
    Fq204.mul (Fq204.ofNat 7431169) ext6FrobeniusZeta = Fq204.ofNat 7431170 ∧
    Fq204.mul (Fq204.ofNat 7431170) ext6FrobeniusZeta = Fq204.one := by
  decide

/-- Frobenius iterates in coordinates. The scalars `949247` and `8380416` of the second
and third iterate are the ones in `ext6RabinUnits204`; the sixth iterate is the identity. -/
theorem ext6Pow_frobenius_iterates (a : Ext6Fq204) :
    ext6Pow a (mldsaQ * mldsaQ) = ext6Twist (Fq204.ofNat 949247) a ∧
    ext6Pow a (mldsaQ * mldsaQ * mldsaQ) = ext6Twist (Fq204.ofNat 8380416) a ∧
    ext6Pow a (mldsaQ * mldsaQ * mldsaQ * mldsaQ) = ext6Twist (Fq204.ofNat 7431169) a ∧
    ext6Pow a (mldsaQ * mldsaQ * mldsaQ * mldsaQ * mldsaQ) =
      ext6Twist (Fq204.ofNat 7431170) a ∧
    ext6Pow a (mldsaQ * mldsaQ * mldsaQ * mldsaQ * mldsaQ * mldsaQ) = a := by
  obtain ⟨z2, z3, z4, z5, z6⟩ := ext6Zeta_powers
  have e2 : ext6Pow a (mldsaQ * mldsaQ) = ext6Twist (Fq204.ofNat 949247) a := by
    rw [ext6Pow_mul, ext6Pow_frobenius, ext6Pow_frobenius, ext6Twist_twist, z2]
  have e3 : ext6Pow a (mldsaQ * mldsaQ * mldsaQ) = ext6Twist (Fq204.ofNat 8380416) a := by
    rw [ext6Pow_mul, e2, ext6Pow_frobenius, ext6Twist_twist, z3]
  have e4 : ext6Pow a (mldsaQ * mldsaQ * mldsaQ * mldsaQ) =
      ext6Twist (Fq204.ofNat 7431169) a := by
    rw [ext6Pow_mul, e3, ext6Pow_frobenius, ext6Twist_twist, z4]
  have e5 : ext6Pow a (mldsaQ * mldsaQ * mldsaQ * mldsaQ * mldsaQ) =
      ext6Twist (Fq204.ofNat 7431170) a := by
    rw [ext6Pow_mul, e4, ext6Pow_frobenius, ext6Twist_twist, z5]
  refine ⟨e2, e3, e4, e5, ?_⟩
  rw [ext6Pow_mul, e5, ext6Pow_frobenius, ext6Twist_twist, z6, ext6Twist_one]

private theorem fq204_eq_zero_of_mul_fixed {x c : Fq204} (hc : c ≠ Fq204.one)
    (h : Fq204.mul x c = x) : x = Fq204.zero := by
  if hx : x = Fq204.zero then exact hx
  else
    exfalso
    apply hc
    have h1 := congrArg (Fq204.mul (Fq204.inv x)) h
    rwa [← Fq204.mul_assoc, Fq204.inv_mul_cancel hx, Fq204.one_mul] at h1

/-- **Rabin's criterion in coordinates.** An element fixed by the second and the third
Frobenius iterate lies in the base field: the second iterate kills the coordinates of
degree `1, 2, 4, 5` and the third those of degree `1, 3, 5`. -/
theorem ext6_rabin_fixed_is_constant (n : Ext6Fq204)
    (h2 : ext6Pow n (mldsaQ * mldsaQ) = n)
    (h3 : ext6Pow n (mldsaQ * mldsaQ * mldsaQ) = n) :
    n = ext6EmbedFq n.a0 := by
  obtain ⟨e2, e3, _⟩ := ext6Pow_frobenius_iterates n
  rw [e2] at h2
  rw [e3] at h3
  rcases n with ⟨n0, n1, n2, n3, n4, n5⟩
  simp only [ext6Twist, Ext6Fq204.mk.injEq] at h2 h3
  obtain ⟨_, h21, h22, _, h24, h25⟩ := h2
  obtain ⟨_, _, _, h33, _, _⟩ := h3
  have z1 := fq204_eq_zero_of_mul_fixed (by decide) h21
  have z2 := fq204_eq_zero_of_mul_fixed (by decide) h22
  have z3 := fq204_eq_zero_of_mul_fixed (by decide) h33
  have z4 := fq204_eq_zero_of_mul_fixed (by decide) h24
  have z5 := fq204_eq_zero_of_mul_fixed (by decide) h25
  simp only [ext6EmbedFq, z1, z2, z3, z4, z5]

/-! ### Inverse, zero-divisor freedom, irreducibility -/

/-- Product of the five nontrivial Frobenius conjugates of `a`. -/
def ext6ConjProduct (a : Ext6Fq204) : Ext6Fq204 :=
  ext6Mul (ext6Twist ext6FrobeniusZeta a)
    (ext6Mul (ext6Twist (Fq204.ofNat 949247) a)
      (ext6Mul (ext6Twist (Fq204.ofNat 8380416) a)
        (ext6Mul (ext6Twist (Fq204.ofNat 7431169) a) (ext6Twist (Fq204.ofNat 7431170) a))))

/-- Field norm `a · a^q ⋯ a^(q^5)`. -/
def ext6Norm (a : Ext6Fq204) : Ext6Fq204 := ext6Mul a (ext6ConjProduct a)

theorem ext6Norm_def (a : Ext6Fq204) : ext6Mul a (ext6ConjProduct a) = ext6Norm a := by rfl

/-- Executable inverse: conjugate product divided by the base-field norm. -/
def ext6Inv (a : Ext6Fq204) : Ext6Fq204 :=
  ext6Scale (ext6ConjProduct a) (Fq204.inv (ext6Norm a).a0)

private def ext6NormExponent : Nat :=
  1 + (mldsaQ + (mldsaQ * mldsaQ + (mldsaQ * mldsaQ * mldsaQ +
    (mldsaQ * mldsaQ * mldsaQ * mldsaQ + mldsaQ * mldsaQ * mldsaQ * mldsaQ * mldsaQ))))

private theorem ext6Norm_eq_pow (a : Ext6Fq204) : ext6Norm a = ext6Pow a ext6NormExponent := by
  obtain ⟨e2, e3, e4, e5, _⟩ := ext6Pow_frobenius_iterates a
  rw [ext6NormExponent, ext6Pow_add, ext6Pow_add, ext6Pow_add, ext6Pow_add, ext6Pow_add,
    ext6Pow_one, ext6Pow_frobenius, e2, e3, e4, e5]
  rfl

theorem ext6Norm_frobenius_fixed (a : Ext6Fq204) :
    ext6Pow (ext6Norm a) mldsaQ = ext6Norm a := by
  obtain ⟨z2, z3, z4, z5, z6⟩ := ext6Zeta_powers
  simp only [ext6Norm, ext6ConjProduct, ext6Mul_pow]
  simp only [ext6Pow_frobenius, ext6Twist_twist, z2, z3, z4, z5, z6, ext6Twist_one]
  ac_rfl

theorem ext6Norm_is_constant (a : Ext6Fq204) :
    ext6Norm a = ext6EmbedFq (ext6Norm a).a0 := by
  have h1 := ext6Norm_frobenius_fixed a
  apply ext6_rabin_fixed_is_constant
  · rw [ext6Pow_mul, h1, h1]
  · rw [ext6Pow_mul, ext6Pow_mul, h1, h1, h1]

theorem ext6Norm_ne_zero {a : Ext6Fq204} (ha : a ≠ ext6Zero) : ext6Norm a ≠ ext6Zero := by
  intro hN
  apply ha
  have h6 := (ext6Pow_frobenius_iterates a).2.2.2.2
  have hE : mldsaQ * mldsaQ * mldsaQ * mldsaQ * mldsaQ * mldsaQ =
      ext6NormExponent * (mldsaQ - 1) + 1 := by decide
  rw [hE, ext6Pow_succ, ext6Pow_mul, ← ext6Norm_eq_pow, hN,
    ext6Pow_zero_base (by decide), ext6Zero_mul] at h6
  exact h6.symm

/-- **Every nonzero element of the extension is invertible.** -/
theorem ext6Mul_inv_cancel {a : Ext6Fq204} (ha : a ≠ ext6Zero) :
    ext6Mul a (ext6Inv a) = ext6One := by
  have hConst := ext6Norm_is_constant a
  have hN0 : (ext6Norm a).a0 ≠ Fq204.zero := fun h0 =>
    ext6Norm_ne_zero ha (hConst.trans (by rw [h0]; rfl))
  have hKey : ext6Mul a (ext6Inv a) =
      ext6Scale (ext6Norm a) (Fq204.inv (ext6Norm a).a0) := by
    rw [ext6Inv, ext6Mul_scale_right, ext6Norm_def]
  have hS : ext6Scale (ext6Norm a) (Fq204.inv (ext6Norm a).a0) =
      ext6Scale (ext6EmbedFq (ext6Norm a).a0) (Fq204.inv (ext6Norm a).a0) :=
    congrArg (fun t => ext6Scale t (Fq204.inv (ext6Norm a).a0)) hConst
  rw [hKey, hS, ext6Scale_embed, Fq204.mul_inv_cancel hN0]
  rfl

/-- **Zero-divisor freedom of `F_q[X]/(X^6 - 7)`.** -/
theorem ext6Mul_eq_zero {a b : Ext6Fq204} (h : ext6Mul a b = ext6Zero) :
    a = ext6Zero ∨ b = ext6Zero := by
  if ha : a = ext6Zero then exact .inl ha
  else
    right
    have h1 := congrArg (ext6Mul (ext6Inv a)) h
    rwa [← ext6Mul_assoc, ext6Mul_comm (ext6Inv a) a, ext6Mul_inv_cancel ha, ext6One_mul,
      ext6Mul_zero] at h1

/-- The eleven coefficients of the unreduced product of two polynomials of degree at most
five; `ext6Mul` is this product with `X^(6+k)` replaced by `7 X^k`. -/
def ext6ProductCoeffs (x y : Ext6Fq204) : List Fq204 :=
  let m (a b : Fq204) := Fq204.mul a b
  let ad (a b : Fq204) := Fq204.add a b
  [m x.a0 y.a0,
   ad (m x.a0 y.a1) (m x.a1 y.a0),
   ad (m x.a0 y.a2) (ad (m x.a1 y.a1) (m x.a2 y.a0)),
   ad (m x.a0 y.a3) (ad (m x.a1 y.a2) (ad (m x.a2 y.a1) (m x.a3 y.a0))),
   ad (m x.a0 y.a4) (ad (m x.a1 y.a3) (ad (m x.a2 y.a2) (ad (m x.a3 y.a1) (m x.a4 y.a0)))),
   ad (m x.a0 y.a5) (ad (m x.a1 y.a4) (ad (m x.a2 y.a3) (ad (m x.a3 y.a2)
     (ad (m x.a4 y.a1) (m x.a5 y.a0))))),
   ad (m x.a1 y.a5) (ad (m x.a2 y.a4) (ad (m x.a3 y.a3) (ad (m x.a4 y.a2) (m x.a5 y.a1)))),
   ad (m x.a2 y.a5) (ad (m x.a3 y.a4) (ad (m x.a4 y.a3) (m x.a5 y.a2))),
   ad (m x.a3 y.a5) (ad (m x.a4 y.a4) (m x.a5 y.a3)),
   ad (m x.a4 y.a5) (m x.a5 y.a4),
   m x.a5 y.a5]

/-- **Irreducibility of `X^6 - 7` over `F_q`.** No two polynomials of degree at most five
multiply to `X^6 - 7`; a proper factorization of a degree-six polynomial has both factors
of degree at most five. -/
theorem ext6Modulus_irreducible (g h : Ext6Fq204) :
    ext6ProductCoeffs g h ≠
      [Fq204.neg ext6Nonresidue, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero,
       Fq204.one, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero] := by
  intro hEq
  have hMul : ext6Mul g h = ext6Zero := by
    rcases g with ⟨g0, g1, g2, g3, g4, g5⟩
    rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
    simp only [ext6ProductCoeffs, List.cons.injEq, and_true] at hEq
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hEq
    simp only [ext6Mul, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10]
    decide
  have hOne : (ext6ProductCoeffs g h).getD 6 Fq204.zero = Fq204.one := by rw [hEq]; rfl
  rcases ext6Mul_eq_zero hMul with hz | hz
  · subst hz
    simp only [ext6ProductCoeffs, ext6Zero, Fq204.zero_mul, Fq204.add_zero] at hOne
    exact absurd hOne (by decide)
  · subst hz
    simp only [ext6ProductCoeffs, ext6Zero, Fq204.mul_zero, Fq204.add_zero] at hOne
    exact absurd hOne (by decide)

def ext6Neg (x : Ext6Fq204) : Ext6Fq204 :=
  ⟨Fq204.neg x.a0, Fq204.neg x.a1, Fq204.neg x.a2, Fq204.neg x.a3, Fq204.neg x.a4,
    Fq204.neg x.a5⟩

instance : CommRingOps Ext6Fq204 where
  zero := ext6Zero
  one := ext6One
  add := ext6Add
  mul := ext6Mul
  neg := ext6Neg
  sub := ext6Sub

instance : LawfulCommRing Ext6Fq204 where
  add_assoc := ext6Add_assoc
  add_comm := ext6Add_comm
  zero_add := ext6Zero_add
  add_zero := ext6Add_zero
  add_left_neg := fun x => by
    rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
    show ext6Add (ext6Neg _) _ = ext6Zero
    simp only [ext6Add, ext6Neg, ext6Zero, Fq204.add_left_neg]
  sub_eq_add_neg := fun x y => by
    rcases x with ⟨x0, x1, x2, x3, x4, x5⟩
    rcases y with ⟨y0, y1, y2, y3, y4, y5⟩
    show ext6Sub _ _ = ext6Add _ (ext6Neg _)
    simp only [ext6Add, ext6Neg, ext6Sub, Fq204.sub_eq_add_neg]
  mul_assoc := ext6Mul_assoc
  mul_comm := ext6Mul_comm
  one_mul := ext6One_mul
  mul_one := ext6Mul_one
  left_distrib := ext6Mul_add
  right_distrib := ext6Add_mul

instance : NoZeroDivisors Ext6Fq204 where
  eq_zero_or_eq_zero_of_mul_eq_zero := ext6Mul_eq_zero

theorem ext6Inv_zero : ext6Inv ext6Zero = ext6Zero := by
  have hTwist : ∀ c : Fq204, ext6Twist c ext6Zero = ext6Zero := fun c => by
    unfold ext6Twist ext6Zero
    dsimp only
    simp only [Fq204.zero_mul]
  have hConj : ext6ConjProduct ext6Zero = ext6Zero := by
    unfold ext6ConjProduct
    rw [hTwist, ext6Zero_mul]
  unfold ext6Inv
  rw [hConj]
  unfold ext6Scale ext6Zero
  dsimp only
  simp only [Fq204.zero_mul]

/-- The verification extension as a field, with the executable inverse `ext6Inv`. -/
instance : LawfulField Ext6Fq204 where
  inv := ext6Inv
  zero_ne_one := by decide
  inv_zero := ext6Inv_zero
  mul_inv_cancel := ext6Mul_inv_cancel

end Ext6Field

/-! ### Root counting over the extension challenge space

`rss_mpc.rs` draws the batching coin `lambda` and every folding coin `xi` from the
extension. With the field structure above, a discrepancy polynomial with extension
coefficients has no more roots than its degree, so a wrong multiplication triple
survives batching with at most `gates` values of `lambda` and a wrong folding round with
at most `2 (FOLD - 1) = 14` values of `xi`.
-/

private theorem exists_eval_nonzero_ext6 :
    ∀ (cs : List Ext6Fq204), cs.length < mldsaQ →
      (∃ c ∈ cs, c ≠ ext6Zero) →
      ∃ x : Ext6Fq204, RoundPoly.evalCoeffs cs x ≠ ext6Zero
  | [], _, ⟨_, hMem, _⟩ => by cases hMem
  | c₀ :: tail, hLen, ⟨c, hMem, hcNe⟩ => by
    if hc0Ne : c₀ ≠ ext6Zero then
      refine ⟨ext6Zero, ?_⟩
      change ext6Add c₀ (ext6Mul ext6Zero (RoundPoly.evalCoeffs tail ext6Zero)) ≠ ext6Zero
      rw [ext6Zero_mul, ext6Add_zero]
      exact hc0Ne
    else
      have hc0Eq : c₀ = ext6Zero := by
        cases decEq c₀ ext6Zero with
        | isTrue h => exact h
        | isFalse h => exact False.elim (hc0Ne h)
      subst hc0Eq
      have hTailEx : ∃ c' ∈ tail, c' ≠ ext6Zero := by
        rcases List.mem_cons.mp hMem with rfl | hInTail
        · exact False.elim (hcNe rfl)
        · exact ⟨c, hInTail, hcNe⟩
      have hTailPos : 1 ≤ tail.length := by
        rcases hTailEx with ⟨_, hm, _⟩
        cases tail with
        | nil => cases hm
        | cons _ _ => simp only [List.length_cons]; omega
      simp only [List.length_cons] at hLen
      obtain ⟨x₁, hx₁⟩ := exists_eval_nonzero_ext6 tail (by omega) hTailEx
      let d := tail.length - 1
      let grid : List Ext6Fq204 :=
        (List.range (d + 1)).map (fun i => ext6EmbedFq (Fq204.ofNat (i + 1)))
      have hGridLen : grid.length = d + 1 := by simp [grid]
      have hGridNodup : grid.Nodup := by
        apply nodup_map_on_list_fq _ (Qsag.Constructive.nodup_range (d + 1))
        intro a ha b hb hEq
        have haLt : a + 1 < mldsaQ := by have := List.mem_range.mp ha; omega
        have hbLt : b + 1 < mldsaQ := by have := List.mem_range.mp hb; omega
        have hVal := congrArg (fun e : Ext6Fq204 => e.a0.val) hEq
        simp only [ext6EmbedFq, Fq204.ofNat_val, Nat.mod_eq_of_lt haLt,
          Nat.mod_eq_of_lt hbLt] at hVal
        omega
      have hRootsLe :
          (grid.filter (fun r => decide (RoundPoly.evalCoeffs tail r = ext6Zero))).length ≤ d :=
        RoundPoly.roots_nodup_length_le d tail grid hGridNodup (by omega) ⟨x₁, hx₁⟩
      have hFiltLt :
          (grid.filter (fun r => decide (RoundPoly.evalCoeffs tail r = ext6Zero))).length <
            grid.length := by
        rw [hGridLen]; omega
      obtain ⟨x₀, hx₀Mem, hx₀False⟩ := exists_mem_of_filter_length_lt_fq
        (fun r => decide (RoundPoly.evalCoeffs tail r = ext6Zero)) grid hFiltLt
      have hx₀NeZero : x₀ ≠ ext6Zero := by
        rcases List.mem_map.mp hx₀Mem with ⟨idx, hIdxRange, rfl⟩
        have hIdxLt : idx + 1 < mldsaQ := by have := List.mem_range.mp hIdxRange; omega
        intro hZero
        have hv := congrArg (fun e : Ext6Fq204 => e.a0.val) hZero
        simp only [ext6EmbedFq, ext6Zero, Fq204.ofNat_val, Nat.mod_eq_of_lt hIdxLt,
          Fq204.zero_val] at hv
        omega
      have hEvalTailNe : RoundPoly.evalCoeffs tail x₀ ≠ ext6Zero := by
        intro hZero
        rw [decide_eq_true hZero] at hx₀False
        cases hx₀False
      refine ⟨x₀, ?_⟩
      change ext6Add ext6Zero (ext6Mul x₀ (RoundPoly.evalCoeffs tail x₀)) ≠ ext6Zero
      rw [ext6Zero_add]
      intro hProdZero
      rcases ext6Mul_eq_zero hProdZero with h1 | h2
      · exact hx₀NeZero h1
      · exact hEvalTailNe h2

/-- **Batching and folding coins are drawn from a field.** A polynomial over the
extension of formal degree at most `D` with a nonzero coefficient vanishes on at most `D`
points of any duplicate-free list of extension challenges. -/
theorem rss_ext6_discrepancy_roots_le (D : Nat) (cs S : List Ext6Fq204)
    (hD : D + 1 < mldsaQ) (hLen : cs.length ≤ D + 1) (hNodup : S.Nodup)
    (hNz : ∃ c ∈ cs, c ≠ ext6Zero) :
    (S.filter (fun xi => decide (RoundPoly.evalCoeffs cs xi = ext6Zero))).length ≤ D := by
  obtain ⟨x₀, hx₀⟩ := exists_eval_nonzero_ext6 cs (by omega) hNz
  exact RoundPoly.roots_nodup_length_le D cs S hNodup hLen ⟨x₀, hx₀⟩

/-- One folding round of `Engine::verify` (`FOLD = 8`): the round polynomial has degree
at most fourteen, so at most fourteen folding coins hide a wrong round. -/
theorem rss_ext6_fold_round_roots_le (cs S : List Ext6Fq204)
    (hLen : cs.length ≤ 15) (hNodup : S.Nodup) (hNz : ∃ c ∈ cs, c ≠ ext6Zero) :
    (S.filter (fun xi => decide (RoundPoly.evalCoeffs cs xi = ext6Zero))).length ≤ 14 :=
  rss_ext6_discrepancy_roots_le 14 cs S (by decide) hLen hNodup hNz

/-- The nonzero-coefficient premise is needed: the zero polynomial vanishes everywhere. -/
theorem tooth_rss_ext6_zero_discrepancy_all_roots :
    ∃ S : List Ext6Fq204, S.Nodup ∧
      (S.filter (fun xi => decide (RoundPoly.evalCoeffs [ext6Zero] xi = ext6Zero))).length = 2 :=
  ⟨[ext6Zero, ext6One], by decide, by decide⟩

/-- The inverse is specific to nonzero elements. -/
theorem tooth_ext6Inv_zero_not_inverse :
    ext6Mul ext6Zero (ext6Inv ext6Zero) ≠ ext6One := by
  rw [ext6Zero_mul]
  decide

/-- The third Frobenius iterate alone does not cut out the base field: `X^2` is fixed by
it and is not a constant, so the second-iterate condition of the criterion is needed. -/
theorem tooth_ext6_third_iterate_fixes_nonconstant :
    ∃ n : Ext6Fq204, ext6Pow n (mldsaQ * mldsaQ * mldsaQ) = n ∧ n ≠ ext6EmbedFq n.a0 := by
  refine ⟨ext6Monomial204 2 Fq204.one, ?_, by decide⟩
  rw [(ext6Pow_frobenius_iterates _).2.1]
  decide

/-- A reducible modulus is rejected by the same coefficient test: `X^6 - 1` factors. -/
theorem tooth_ext6_unit_modulus_factors :
    ∃ g h : Ext6Fq204, ext6ProductCoeffs g h =
      [Fq204.neg Fq204.one, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero,
       Fq204.one, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero] :=
  ⟨⟨Fq204.neg Fq204.one, Fq204.zero, Fq204.zero, Fq204.one, Fq204.zero, Fq204.zero⟩,
   ⟨Fq204.one, Fq204.zero, Fq204.zero, Fq204.one, Fq204.zero, Fq204.zero⟩, by decide⟩

theorem ext6Inv_inhabited :
    ∃ a : Ext6Fq204, a ≠ ext6Zero ∧ ext6Mul a (ext6Inv a) = ext6One :=
  ⟨ext6Monomial204 1 Fq204.one, by decide, ext6Mul_inv_cancel (by decide)⟩

theorem ext6Zero_eq : ext6Zero =
    ⟨Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero, Fq204.zero⟩ := by
  unfold ext6Zero; rfl

theorem ext6Sub_eq (x y : Ext6Fq204) : ext6Sub x y =
    ⟨Fq204.sub x.a0 y.a0, Fq204.sub x.a1 y.a1, Fq204.sub x.a2 y.a2,
     Fq204.sub x.a3 y.a3, Fq204.sub x.a4 y.a4, Fq204.sub x.a5 y.a5⟩ := by
  unfold ext6Sub; rfl

theorem ext6Scale_eq (x : Ext6Fq204) (s : Fq204) : ext6Scale x s =
    ⟨Fq204.mul x.a0 s, Fq204.mul x.a1 s, Fq204.mul x.a2 s,
     Fq204.mul x.a3 s, Fq204.mul x.a4 s, Fq204.mul x.a5 s⟩ := by
  unfold ext6Scale; rfl

#tooth_pair ext6Mul_inv_cancel vs tooth_ext6Inv_zero_not_inverse
#tooth_pair ext6_rabin_fixed_is_constant vs tooth_ext6_third_iterate_fixes_nonconstant
#tooth_pair ext6Modulus_irreducible vs tooth_ext6_unit_modulus_factors
#tooth_pair rss_ext6_discrepancy_roots_le vs tooth_rss_ext6_zero_discrepancy_all_roots
#verify_inhabited ext6Mul_inv_cancel ext6Inv_inhabited

#export_eqns ext6EmbedFq ext6Add

end Qsag
end
