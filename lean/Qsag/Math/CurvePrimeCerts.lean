module
/-
# Qsag.Math.CurvePrimeCerts — Constructive Prime Certificates & Prime-Order Curve Subgroups

Constructive (`0 sorry`, `0 axiom`, `0 Classical.choice`, `0 native_decide`) primality
certification, prime residue fields, and binary projective/twisted-Edwards generator order
verification for all deployed QSAG ownership-migration curves:

1. **`secp256k1`** (`SECP256K1_FIELD_P`, `SECP256K1_ORDER_N`, `y² = x³ + 7`),
2. **`Ed25519` / `Curve25519`** (`P_ED25519 = 2^255 - 19`, `R_ED25519 = ED25519_ORDER_L`,
   complete twisted-Edwards `-x² + y² = 1 + d x² y²`),
3. **Zcash Pasta Cycle — `Pallas` & `Vesta`** (`p_pallas`, `q_pallas`, `p_vesta = q_pallas`,
   `q_vesta = p_pallas`, `y² = x³ + 5`, Ironwood `ZIP-2005` `0x03` & Orchard),
4. **Zcash Sapling — `Jubjub`** (`q_jubjub = r_bls381`, `R_JUBJUB`, complete twisted-Edwards
   `-u² + v² = 1 + d_J u² v²` with `G^Sapling`),
5. **`BLS12-381` `G_1`** (`p_bls381`, `r_bls381`, `y² = x³ + 4`).

Also constructs a total constructive `LawfulField (PrimeMod p)` instance for every certified prime
`[CurveFactPrime p]` via `extGcd` Bézout inversion (`extGcd_bezout`, `extGcd_dvd`), and bundles all six
production curves into `CertifiedPrimeScalarCurve` records replacing toy `secp7Mod43`.
-/

public import Qsag.Math.Primality
public import Qsag.Math.EllipticCurves
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false
set_option exponentiation.threshold 512

/-! ## §1. Self-Contained Kernel-Reducible Pocklington Certifier & Deployed Curve Moduli -/

/-- `secp256k1` base field prime `2^256 - 2^32 - 977`. -/
abbrev SECP256K1_FIELD_P : Nat :=
  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

/-- `Ed25519` / `Curve25519` base field prime `2^255 - 19`. -/
abbrev P_ED25519 : Nat :=
  0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFED

/-- `Ed25519` prime-order subgroup scalar modulus `2^252 + 27742317777372353535851937790883648493`. -/
abbrev R_ED25519 : Nat := ED25519_ORDER_L

/-- `Vesta` base field prime (`= q_pallas` in the Zcash Pasta 2-cycle). -/
abbrev p_vesta : Nat := q_pallas

/-- `Vesta` scalar field prime (`= p_pallas` in the Zcash Pasta 2-cycle). -/
abbrev q_vesta : Nat := p_pallas

/-- `Jubjub` base coordinate field prime (`= r_bls381`, Zcash Sapling). -/
abbrev q_jubjub : Nat := r_bls381

/-- `Jubjub` prime-order SpendAuth scalar subgroup modulus `r_J` (Zcash Sapling). -/
abbrev R_JUBJUB : Nat :=
  0x0e7db4ea6533afa906673b0101343b00a6682093ccc81082d0970e5ed6f72cb7

/-- `IsPrimeMod` and `IsPrimeNat` are definitionally equivalent. -/
theorem isPrimeMod_iff_isPrimeNat (p : Nat) : IsPrimeMod p ↔ IsPrimeNat p :=
  Iff.rfl

private def strictEvalCert (n : Nat) (k : Nat → Nat) : Nat :=
  match n with | 0 => k 0 | m + 1 => k (m + 1)

/-- Tail-recursive binary square-and-multiply modular exponentiation (`< 1s` in Lean's kernel). -/
def certPowMod : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, m => 1 % m
  | fuel + 1, b, e, m =>
    if e = 0 then 1 % m
    else
      strictEvalCert (certPowMod fuel ((b * b) % m) (e / 2) m) fun sub =>
        if e % 2 = 1 then (b * sub) % m else sub

private theorem certPowMod_eq_pow_mod :
    ∀ (fuel b e m : Nat), e < 2 ^ fuel → certPowMod fuel b e m = (b ^ e) % m
  | 0, b, e, m, hLt => by
    have he0 : e = 0 := by omega
    subst he0; unfold certPowMod; rw [Nat.pow_zero]
  | fuel + 1, b, e, m, hLt => by
    unfold certPowMod
    if he0 : e = 0 then
      simp only [he0, ↓reduceIte, Nat.pow_zero]
    else
      simp only [he0, ↓reduceIte]
      have hStrict : ∀ x (f : Nat → Nat), strictEvalCert x f = f x := by
        intro x f; cases x <;> rfl
      rw [hStrict]
      have hHalfLt : e / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at hLt; omega
      rw [certPowMod_eq_pow_mod fuel ((b * b) % m) (e / 2) m hHalfLt]
      have hSqPow : (((b * b) % m) ^ (e / 2)) % m = ((b * b) ^ (e / 2)) % m := by
        clear hLt he0 hHalfLt
        induction (e / 2) with
        | zero => rfl
        | succ k ih =>
          rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, ih, Nat.mod_mod, ← Nat.mul_mod]
      rw [hSqPow]
      have hSqEq : (b * b) ^ (e / 2) = b ^ (2 * (e / 2)) := by
        rw [← Nat.pow_two, ← Nat.pow_mul]
      rw [hSqEq]
      have hDivMod : 2 * (e / 2) + e % 2 = e := Nat.div_add_mod e 2
      if hOdd : e % 2 = 1 then
        simp only [hOdd, ↓reduceIte]
        rw [Nat.mul_mod_mod]
        have heEq : e = 2 * (e / 2) + 1 := by omega
        conv => rhs; rw [heEq, Nat.pow_add, Nat.pow_one, Nat.mul_comm]
      else
        simp only [hOdd, ↓reduceIte]
        have heEq : e = 2 * (e / 2) := by omega
        conv => rhs; rw [heEq]

/-- Fuelled Euclidean GCD for kernel-evaluated coprimality checks. -/
def certGcd : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | fuel + 1, a, b => if b = 0 then a else certGcd fuel b (a % b)

private theorem dvd_certGcd : ∀ (fuel a b d : Nat), d ∣ a → d ∣ b → d ∣ certGcd fuel a b
  | 0, _, _, _, hda, _ => hda
  | fuel + 1, a, b, d, hda, hdb => by
    unfold certGcd
    if hb0 : b = 0 then
      simp only [hb0, ↓reduceIte]; exact hda
    else
      simp only [hb0, ↓reduceIte]
      exact dvd_certGcd fuel b (a % b) d hdb ((Nat.dvd_mod_iff hdb).2 hda)

def certDistinct : List (Nat × Nat) → Bool
  | [] => true
  | (q, _) :: rest => rest.all (fun p => q != p.1) && certDistinct rest

def certFactorsProd : List (Nat × Nat) → Nat
  | [] => 1
  | (q, e) :: rest => (q ^ e) * certFactorsProd rest

def certCheckFactor (known : List Nat) (n g : Nat) (qe : Nat × Nat) : Bool :=
  let q := qe.1
  let e := qe.2
  known.contains q &&
  decide (1 ≤ e) &&
  decide ((n - 1) % (q ^ e) = 0) &&
  let r := certPowMod 256 g ((n - 1) / q) n
  decide (1 < r) && decide (certGcd 512 (r - 1) n = 1)

def certCheckStep (known : List Nat) (s : PocklingtonStep) : Bool :=
  decide (3 ≤ s.n) &&
  decide (s.n < 2 ^ 256) &&
  decide (certPowMod 256 s.g (s.n - 1) s.n = 1) &&
  certDistinct s.factors &&
  s.factors.all (certCheckFactor known s.n s.g) &&
  let F := certFactorsProd s.factors
  decide (s.n < F * F)

def certVerifyChainAux : List Nat → List PocklingtonStep → Option (List Nat)
  | known, [] => some known
  | known, s :: rest =>
    if certCheckStep known s then certVerifyChainAux (s.n :: known) rest else none

def certVerifyPrime (chain : List PocklingtonStep) (target : Nat) : Bool :=
  match certVerifyChainAux [2] chain with
  | some known => known.contains target
  | none => false

private def cMinDivAux (n d : Nat) : Nat → Nat
  | 0 => n
  | fuel + 1 => if n % d = 0 then d else cMinDivAux n (d + 1) fuel

private theorem cMinDivAux_spec :
    ∀ (fuel n d : Nat),
      2 ≤ n → 2 ≤ d → n ≤ d + fuel →
      (∀ k : Nat, 2 ≤ k → k < d → ¬ (k ∣ n)) →
      let p := cMinDivAux n d fuel
      2 ≤ p ∧ p ∣ n ∧ (∀ k : Nat, 2 ≤ k → k < p → ¬ (k ∣ n))
  | 0, n, _, hn2, _, _, hno => by
    dsimp only [cMinDivAux]
    exact ⟨hn2, Nat.dvd_refl n, fun k hk2 hklt => hno k hk2 (by omega)⟩
  | fuel + 1, n, d, hn2, hd, hle, hno => by
    dsimp only [cMinDivAux]
    if hmod : n % d = 0 then
      simp only [hmod, ↓reduceIte]
      exact ⟨hd, Nat.dvd_of_mod_eq_zero hmod, hno⟩
    else
      simp only [hmod, ↓reduceIte]
      refine cMinDivAux_spec fuel n (d + 1) hn2 (by omega) (by omega) (fun k hk2 hklt => ?_)
      if hkd : k = d then
        subst hkd; exact fun hdvd => hmod (Nat.mod_eq_zero_of_dvd hdvd)
      else
        exact hno k hk2 (by omega)

private theorem cMinDiv_prime_and_sq {n : Nat} (hn : 2 ≤ n) :
    ∃ p : Nat, IsPrimeNat p ∧ p ∣ n ∧ (p = n ∨ p * p ≤ n) := by
  obtain ⟨hp2, hpdvd, hpmin⟩ :=
    cMinDivAux_spec n n 2 hn (by decide) (by omega) (by intros; omega)
  have hple : cMinDivAux n 2 n ≤ n := Nat.le_of_dvd (by omega) hpdvd
  have hPrime : IsPrimeNat (cMinDivAux n 2 n) := by
    refine ⟨hp2, fun d hd => ?_⟩
    if hd1 : d = 1 then exact .inl hd1
    else if hdp : d = cMinDivAux n 2 n then exact .inr hdp
    else
      have hdpos := Nat.pos_of_dvd_of_pos hd (by omega)
      have hdle := Nat.le_of_dvd (by omega) hd
      exact False.elim (hpmin d (by omega) (by omega) (Nat.dvd_trans hd hpdvd))
  refine ⟨cMinDivAux n 2 n, hPrime, hpdvd, ?_⟩
  if hEq : cMinDivAux n 2 n = n then exact .inl hEq
  else
    obtain ⟨k, hk⟩ := hpdvd
    have hk2 : 2 ≤ k := by
      if hk01 : k ≤ 1 then
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk01 with rfl | rfl <;> omega
      else omega
    have hpk : cMinDivAux n 2 n ≤ k := by
      if hlt : k < cMinDivAux n 2 n then
        exact False.elim (hpmin k hk2 hlt ⟨cMinDivAux n 2 n, Nat.mul_comm _ _ ▸ hk⟩)
      else omega
    have hmul : cMinDivAux n 2 n * cMinDivAux n 2 n ≤ cMinDivAux n 2 n * k :=
      Nat.mul_le_mul_left (cMinDivAux n 2 n) hpk
    rw [← hk] at hmul
    exact .inr hmul

private theorem cPow_mod_one {p x : Nat} (hp : 2 ≤ p) (hx : x % p = 1) :
    ∀ k : Nat, (x ^ k) % p = 1
  | 0 => Nat.mod_eq_of_lt hp
  | k + 1 => by
    rw [Nat.pow_succ, Nat.mul_mod, cPow_mod_one hp hx k, hx]
    exact Nat.mod_eq_of_lt hp

private theorem cExists_gcd_ord {p g : Nat} (hp : 2 ≤ p) :
    ∀ (b a : Nat), (g ^ a) % p = 1 → (g ^ b) % p = 1 →
      ∃ d : Nat, d ∣ a ∧ d ∣ b ∧ (g ^ d) % p = 1
  | b, a, ha, hb => by
    if h0 : b = 0 then
      subst h0; exact ⟨a, Nat.dvd_refl a, Nat.dvd_zero a, ha⟩
    else
      have hRem : (g ^ (a % b)) % p = 1 := by
        have hdiv : b * (a / b) + a % b = a := Nat.div_add_mod a b
        have hpow : g ^ a = (g ^ b) ^ (a / b) * g ^ (a % b) := by
          conv => lhs; rw [← hdiv]
          rw [Nat.pow_add, Nat.pow_mul]
        have h1 : ((g ^ b) ^ (a / b)) % p = 1 := cPow_mod_one hp hb (a / b)
        rw [hpow, Nat.mul_mod, h1, Nat.one_mul, Nat.mod_mod] at ha
        exact ha
      obtain ⟨d, hdB, hdRem, hgd⟩ := cExists_gcd_ord hp (a % b) b hb hRem
      have hdiv : b * (a / b) + a % b = a := Nat.div_add_mod a b
      have hdA : d ∣ a := by
        rw [← hdiv]
        exact Nat.dvd_add (Nat.dvd_trans hdB (Nat.dvd_mul_right b (a / b))) hdRem
      exact ⟨d, hdA, hdB, hgd⟩
termination_by b _ => b
decreasing_by exact Nat.mod_lt a (Nat.pos_of_ne_zero h0)

private theorem cPrime_dvd_of_not_dvd {q m d : Nat}
    (hq : IsPrimeNat q) (hd : d ∣ q * m) (hnd : ¬ (d ∣ m)) : q ∣ d := by
  obtain ⟨hdd, hdq⟩ := extGcd_dvd d q
  rcases hq.2 _ hdq with hg1 | hgq
  · exfalso
    have hbez := extGcd_bezout d q
    rw [hg1] at hbez
    obtain ⟨k, hk⟩ := hd
    have hmul : ((d : Int) * (extGcd d q).2.1 + (q : Int) * (extGcd d q).2.2) * (m : Int) =
        1 * (m : Int) := congrArg (· * (m : Int)) hbez
    rw [Int.add_mul, Int.one_mul] at hmul
    have hqm : (q : Int) * (extGcd d q).2.2 * (m : Int) =
        (d : Int) * ((k : Int) * (extGcd d q).2.2) := by
      have hkInt : (q : Int) * (m : Int) = (d : Int) * (k : Int) := by exact_mod_cast hk
      rw [Int.mul_right_comm (q : Int), hkInt, Int.mul_assoc]
    rw [hqm, Int.mul_assoc (d : Int), ← Int.mul_add] at hmul
    exact hnd (Int.ofNat_dvd.1 ⟨(extGcd d q).2.1 * (m : Int) + (k : Int) * (extGcd d q).2.2, hmul.symm⟩)
  · rw [hgq] at hdd; exact hdd

private theorem cPrime_pow_dvd {q m : Nat} (hq : IsPrimeNat q) :
    ∀ (e : Nat) {d : Nat}, 1 ≤ e → d ∣ q ^ e * m → ¬ (d ∣ q ^ (e - 1) * m) → q ^ e ∣ d
  | 0, _, he, _, _ => by omega
  | 1, d, _, hd, hnd => by
    simpa using cPrime_dvd_of_not_dvd hq (by simpa using hd) (by simpa using hnd)
  | e + 2, d, _, hd, hnd => by
    have hqPos : 0 < q := by have := hq.1; omega
    have hPow : q ^ (e + 2) * m = q * (q ^ (e + 1) * m) := by
      rw [Nat.pow_succ, Nat.mul_comm (q ^ (e + 1)) q, Nat.mul_assoc]
    rw [hPow] at hd
    have hndE1 : ¬ (d ∣ q ^ (e + 1) * m) := by simpa using hnd
    obtain ⟨d', rfl⟩ := cPrime_dvd_of_not_dvd hq hd hndE1
    have hd' : d' ∣ q ^ (e + 1) * m := by
      obtain ⟨k, hk⟩ := hd
      rw [Nat.mul_assoc] at hk
      exact ⟨k, Nat.eq_of_mul_eq_mul_left hqPos hk⟩
    have hnd' : ¬ (d' ∣ q ^ e * m) := fun hc => hndE1 (by
      rw [Nat.pow_succ, Nat.mul_comm (q ^ e) q, Nat.mul_assoc]
      exact Nat.mul_dvd_mul_left q hc)
    have ih := cPrime_pow_dvd hq (e + 1) (by omega) hd' hnd'
    rw [Nat.pow_succ, Nat.mul_comm]
    exact Nat.mul_dvd_mul_left q ih

private theorem cPrime_dvd_mul {q a b : Nat} (hq : IsPrimeNat q) (hd : q ∣ a * b) :
    q ∣ a ∨ q ∣ b :=
  if ha : a % q = 0 then .inl (Nat.dvd_of_mod_eq_zero ha)
  else .inr (IsPrimeMod.dvd_mul hq hd (fun h => ha (Nat.mod_eq_zero_of_dvd h)))

private theorem cNot_dvd_pow {q p : Nat} (hq : IsPrimeNat q) (hp : IsPrimeNat p) (hne : q ≠ p) :
    ∀ e : Nat, ¬ (q ∣ p ^ e)
  | 0 => fun hd => by simp only [Nat.pow_zero] at hd; have := Nat.le_of_dvd (by decide) hd; have := hq.1; omega
  | e + 1 => fun hd => by
    rw [Nat.pow_succ] at hd
    rcases cPrime_dvd_mul hq hd with h1 | hqp
    · exact cNot_dvd_pow hq hp hne e h1
    · rcases hp.2 q hqp with hq1 | hqq
      · have := hq.1; omega
      · exact hne hqq

private theorem cNot_dvd_prod {q : Nat} (hq : IsPrimeNat q) :
    ∀ (fs : List (Nat × Nat)),
      (∀ p ∈ fs, IsPrimeNat p.1 ∧ q ≠ p.1) → ¬ (q ∣ certFactorsProd fs)
  | [], _ => fun hd => by dsimp only [certFactorsProd] at hd; have := Nat.le_of_dvd (by decide) hd; have := hq.1; omega
  | (p, e) :: rest, hall => fun hd => by
    dsimp only [certFactorsProd] at hd
    obtain ⟨hpPrime, hne⟩ := hall (p, e) (.head _)
    rcases cPrime_dvd_mul hq hd with hPow | hdRest
    · exact cNot_dvd_pow hq hpPrime hne e hPow
    · exact cNot_dvd_prod hq rest (fun z hz => hall z (.tail _ hz)) hdRest

private theorem cPrime_pow_pos {q : Nat} (hq : IsPrimeNat q) : ∀ e : Nat, 0 < q ^ e
  | 0 => Nat.one_pos
  | e + 1 => Nat.pow_succ q e ▸ Nat.mul_pos (cPrime_pow_pos hq e) (by have := hq.1; omega)

private theorem cPrime_pow_mul_dvd {q B d : Nat}
    (hq : IsPrimeNat q) (hnotB : ¬ (q ∣ B)) :
    ∀ (e : Nat), q ^ e ∣ d → B ∣ d → (q ^ e * B) ∣ d
  | 0, _, hB => by simp only [Nat.pow_zero, Nat.one_mul]; exact hB
  | e + 1, hqe1, hB => by
    have hqe : q ^ e ∣ d := Nat.dvd_trans ⟨q, rfl⟩ (Nat.pow_succ q e ▸ hqe1)
    obtain ⟨k, hk⟩ := cPrime_pow_mul_dvd hq hnotB e hqe hB
    obtain ⟨m, hm⟩ := hqe1
    have hEq : B * k = q * m := Nat.eq_of_mul_eq_mul_left (cPrime_pow_pos hq e) (by
      calc q ^ e * (B * k) = q ^ e * B * k := (Nat.mul_assoc _ _ _).symm
        _ = q ^ e * (q * m) := by rw [← hk, hm, Nat.pow_succ, Nat.mul_assoc])
    rcases cPrime_dvd_mul hq ⟨m, hEq⟩ with hqB | ⟨k', rfl⟩
    · exact False.elim (hnotB hqB)
    · refine ⟨k', ?_⟩
      calc d = (q ^ e * B) * (q * k') := hk
        _ = (q ^ (e + 1) * B) * k' := by
          rw [Nat.pow_succ]; simp only [Nat.mul_assoc]; rw [Nat.mul_left_comm B q k']

private theorem cMod_mod_dvd {x n p : Nat} (hpn : p ∣ n) : (x % n) % p = x % p := by
  obtain ⟨k, rfl⟩ := hpn
  have hdiv : p * k * (x / (p * k)) + x % (p * k) = x := Nat.div_add_mod x (p * k)
  conv => rhs; rw [← hdiv]
  rw [Nat.mul_assoc p k _, Nat.mul_add_mod]

private theorem cFactor_dvd {known : List Nat}
    (hKnown : ∀ q ∈ known, IsPrimeNat q)
    {n g p d : Nat} (hn3 : 3 ≤ n) (hn256 : n < 2 ^ 256)
    (hpPrime : IsPrimeNat p) (hpn : p ∣ n)
    (hdn1 : d ∣ (n - 1)) (hgd : (g ^ d) % p = 1)
    {qe : Nat × Nat} (hchk : certCheckFactor known n g qe = true) :
    IsPrimeNat qe.1 ∧ (qe.1 ^ qe.2) ∣ d := by
  unfold certCheckFactor at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hchk
  rcases hchk with ⟨⟨⟨hqMem, he1⟩, hqeMod⟩, hrGt1, hgcd1⟩
  have hqPrime : IsPrimeNat qe.1 := hKnown qe.1 hqMem
  refine ⟨hqPrime, ?_⟩
  obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero hqeMod
  have hqPos : 0 < qe.1 := by have := hqPrime.1; omega
  have hDivQ : (n - 1) / qe.1 = qe.1 ^ (qe.2 - 1) * m := by
    have hSplit : qe.1 ^ qe.2 = qe.1 * qe.1 ^ (qe.2 - 1) := by
      conv => lhs; rw [← Nat.sub_add_cancel he1, Nat.pow_succ, Nat.mul_comm]
    have hEq : n - 1 = qe.1 * (qe.1 ^ (qe.2 - 1) * m) := by
      rw [hm, hSplit, Nat.mul_assoc]
    rw [hEq, Nat.mul_div_right _ hqPos]
  have hNotDvdPred : ¬ (d ∣ qe.1 ^ (qe.2 - 1) * m) := by
    intro hdPred
    rw [← hDivQ] at hdPred
    obtain ⟨k, hk⟩ := hdPred
    have hgDivQ : (g ^ ((n - 1) / qe.1)) % p = 1 := by
      rw [hk, Nat.pow_mul]; exact cPow_mod_one hpPrime.1 hgd k
    have hExpLt : (n - 1) / qe.1 < 2 ^ 256 :=
      Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    have hrEq := certPowMod_eq_pow_mod 256 g ((n - 1) / qe.1) n hExpLt
    let r := certPowMod 256 g ((n - 1) / qe.1) n
    have hrModP : r % p = 1 := by
      dsimp only [r]; rw [hrEq, cMod_mod_dvd hpn, hgDivQ]
    have hpDvdR1 : p ∣ (r - 1) := by
      have hdiv : p * (r / p) + r % p = r := Nat.div_add_mod r p
      rw [hrModP] at hdiv
      have : 1 < r := hrGt1
      exact ⟨r / p, by omega⟩
    have hpDvd1 : p ∣ 1 := by
      have hdvdG := dvd_certGcd 512 (r - 1) n p hpDvdR1 hpn
      have hgEq : certGcd 512 (r - 1) n = 1 := hgcd1
      rwa [hgEq] at hdvdG
    have := Nat.le_of_dvd (by decide) hpDvd1
    have := hpPrime.1
    omega
  exact cPrime_pow_dvd hqPrime qe.2 he1 (hm ▸ hdn1) hNotDvdPred

private theorem cFactorsProd_dvd {known : List Nat}
    (hKnown : ∀ q ∈ known, IsPrimeNat q)
    {n g p d : Nat} (hn3 : 3 ≤ n) (hn256 : n < 2 ^ 256)
    (hpPrime : IsPrimeNat p) (hpn : p ∣ n)
    (hdn1 : d ∣ (n - 1)) (hgd : (g ^ d) % p = 1) :
    ∀ (fs : List (Nat × Nat)),
      certDistinct fs = true →
      fs.all (certCheckFactor known n g) = true →
      certFactorsProd fs ∣ d
  | [], _, _ => ⟨d, (Nat.one_mul d).symm⟩
  | (q, e) :: rest, hdist, hall => by
    simp only [certDistinct, List.all_cons, Bool.and_eq_true] at hdist hall
    obtain ⟨hNotInRest, hdistRest⟩ := hdist
    obtain ⟨hHead, hallRest⟩ := hall
    obtain ⟨hqPrime, hqeDvd⟩ :=
      cFactor_dvd hKnown hn3 hn256 hpPrime hpn hdn1 hgd hHead
    have hRestDvd :=
      cFactorsProd_dvd hKnown hn3 hn256 hpPrime hpn hdn1 hgd rest hdistRest hallRest
    have hRestProps : ∀ z ∈ rest, IsPrimeNat z.1 ∧ q ≠ z.1 := fun z hz => by
      have hzChk := List.all_eq_true.1 hallRest z hz
      obtain ⟨hzPrime, _⟩ := cFactor_dvd hKnown hn3 hn256 hpPrime hpn hdn1 hgd hzChk
      exact ⟨hzPrime, bne_iff_ne.1 (List.all_eq_true.1 hNotInRest z hz)⟩
    exact cPrime_pow_mul_dvd hqPrime (cNot_dvd_prod hqPrime rest hRestProps) e hqeDvd hRestDvd

theorem certCheckStep_sound {known : List Nat}
    (hKnown : ∀ q ∈ known, IsPrimeNat q) {s : PocklingtonStep}
    (hStep : certCheckStep known s = true) : IsPrimeNat s.n := by
  unfold certCheckStep at hStep
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hStep
  rcases hStep with ⟨⟨⟨⟨⟨hn3, hn256⟩, hFermatN⟩, hDist⟩, hFactors⟩, hFsq⟩
  obtain ⟨p, hpPrime, hpn, hpCases⟩ := cMinDiv_prime_and_sq (by omega : 2 ≤ s.n)
  rcases hpCases with hpEq | hpSqLe
  · rwa [← hpEq]
  · exfalso
    have hp2 : 2 ≤ p := hpPrime.1
    have hgPowN : (s.g ^ (s.n - 1)) % s.n = 1 := by
      rw [← certPowMod_eq_pow_mod 256 s.g (s.n - 1) s.n (by omega)]
      exact hFermatN
    have hgPowP : (s.g ^ (s.n - 1)) % p = 1 := by
      rw [← cMod_mod_dvd hpn, hgPowN]; exact Nat.mod_eq_of_lt hp2
    have hNotPg : ¬ (p ∣ s.g) := by
      intro ⟨k, hk⟩
      have hSplit : s.n - 1 = (s.n - 2) + 1 := by omega
      have hModG : s.g % p = 0 := by rw [hk, Nat.mul_mod_right]
      have hZero : (s.g ^ (s.n - 1)) % p = 0 := by
        rw [hSplit, Nat.pow_succ, Nat.mul_mod, hModG, Nat.mul_zero, Nat.zero_mod]
      omega
    have hgFermatP : (s.g ^ (p - 1)) % p = 1 := hpPrime.pow_sub_one_mod hNotPg
    obtain ⟨d, hdn1, hdp1, hgd⟩ := cExists_gcd_ord hp2 (p - 1) (s.n - 1) hgPowP hgFermatP
    have hFDvdD := cFactorsProd_dvd hKnown hn3 hn256 hpPrime hpn hdn1 hgd s.factors hDist hFactors
    have hFLeP1 : certFactorsProd s.factors ≤ p - 1 :=
      Nat.le_of_dvd (by omega) (Nat.dvd_trans hFDvdD hdp1)
    have hFLtP : certFactorsProd s.factors < p := by omega
    exact Nat.lt_asymm hFsq (Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_lt hFLtP hFLtP) hpSqLe)

private theorem certVerifyChainAux_sound :
    ∀ (known : List Nat) (chain : List PocklingtonStep) (out : List Nat),
      (∀ q ∈ known, IsPrimeNat q) →
      certVerifyChainAux known chain = some out →
      ∀ q ∈ out, IsPrimeNat q
  | known, [], out, hKnown, hEq => by injection hEq with hOut; subst hOut; exact hKnown
  | known, s :: rest, out, hKnown, hEq => by
    unfold certVerifyChainAux at hEq
    split at hEq
    · rename_i hStep
      have hsPrime := certCheckStep_sound hKnown hStep
      refine certVerifyChainAux_sound (s.n :: known) rest out (fun q hq => ?_) hEq
      rcases List.mem_cons.1 hq with rfl | hqOld
      · exact hsPrime
      · exact hKnown q hqOld
    · cases hEq

/-- **Top-level Pocklington Certificate Soundness (`certVerifyPrime_sound`)**:
    whenever `certVerifyPrime chain target = true`, `IsPrimeNat target` holds constructively. -/
theorem certVerifyPrime_sound {chain : List PocklingtonStep} {target : Nat}
    (hCert : certVerifyPrime chain target = true) : IsPrimeNat target := by
  unfold certVerifyPrime at hCert
  cases hChain : certVerifyChainAux [2] chain with
  | none => simp only [hChain] at hCert; cases hCert
  | some out =>
    simp only [hChain] at hCert
    exact certVerifyChainAux_sound [2] chain out
      (fun q hq => by rcases List.mem_singleton.1 hq with rfl; exact isPrimeNat_2)
      hChain target (List.contains_iff_mem.1 hCert)

/-- Shared 54-step Pocklington certificate DAG certifying `P_ED25519`, `R_ED25519`, and
    `R_JUBJUB` from `[2]` in `< 0.5s` kernel reduction. -/
def ed25519AndJubjubPrimeChain : List PocklingtonStep := [
  ⟨5, 2, [(2, 2)]⟩,
  ⟨11, 2, [(5, 1)]⟩,
  ⟨991, 2, [(11, 1), (5, 1)]⟩,
  ⟨17, 3, [(2, 4)]⟩,
  ⟨103, 2, [(17, 1)]⟩,
  ⟨8574133, 2, [(991, 1), (103, 1)]⟩,
  ⟨3, 2, [(2, 1)]⟩,
  ⟨7, 2, [(3, 1)]⟩,
  ⟨127, 3, [(7, 1), (3, 2)]⟩,
  ⟨1919519569386763, 2, [(8574133, 1), (127, 1)]⟩,
  ⟨19, 2, [(3, 2)]⟩,
  ⟨419, 2, [(19, 1), (11, 1)]⟩,
  ⟨97, 5, [(3, 1), (2, 5)]⟩,
  ⟨569003, 2, [(419, 1), (97, 1)]⟩,
  ⟨2773320623, 2, [(569003, 1)]⟩,
  ⟨72106336199, 2, [(2773320623, 1)]⟩,
  ⟨75445702479781427272750846543864801, 2, [(1919519569386763, 1), (72106336199, 1)]⟩,
  ⟨41, 6, [(5, 1), (2, 3)]⟩,
  ⟨1723, 2, [(41, 1), (7, 1)]⟩,
  ⟨430751, 2, [(1723, 1)]⟩,
  ⟨43, 2, [(7, 1)]⟩,
  ⟨173, 2, [(43, 1)]⟩,
  ⟨4153, 2, [(173, 1)]⟩,
  ⟨31757755568855353, 2, [(430751, 1), (4153, 1)]⟩,
  ⟨74058212732561358302231226437062788676166966415465897661863160754340907, 2,
    [(75445702479781427272750846543864801, 1), (31757755568855353, 1)]⟩,
  ⟨57896044618658097711785492504343953926634992332820282019728792003956564819949, 2,
    [(74058212732561358302231226437062788676166966415465897661863160754340907, 1)]⟩,
  ⟨2551, 2, [(17, 1), (5, 2)]⟩,
  ⟨1224481, 2, [(2551, 1)]⟩,
  ⟨73, 2, [(3, 2)]⟩,
  ⟨3797, 2, [(73, 1)]⟩,
  ⟨531581, 2, [(3797, 1)]⟩,
  ⟨1257559732178653, 2, [(1224481, 1), (531581, 1)]⟩,
  ⟨4434155615661930479, 2, [(1257559732178653, 1)]⟩,
  ⟨172054593956031949258510691, 2, [(4434155615661930479, 1)]⟩,
  ⟨19757330305831588566944191468367130476339, 2, [(172054593956031949258510691, 1)]⟩,
  ⟨276602624281642239937218680557139826668747, 2,
    [(19757330305831588566944191468367130476339, 1)]⟩,
  ⟨7237005577332262213973186563042994240857116359379907606001950938285454250989, 2,
    [(276602624281642239937218680557139826668747, 1)]⟩,
  ⟨89, 2, [(11, 1)]⟩,
  ⟨179, 2, [(89, 1)]⟩,
  ⟨23629, 2, [(179, 1)]⟩,
  ⟨567097, 2, [(23629, 1)]⟩,
  ⟨62701, 2, [(19, 1), (11, 1), (5, 2)]⟩,
  ⟨16356472538621, 2, [(567097, 1), (62701, 1)]⟩,
  ⟨623312455501769069, 2, [(16356472538621, 1)]⟩,
  ⟨255074062430788457494141376149, 2, [(623312455501769069, 1)]⟩,
  ⟨13, 2, [(3, 1), (2, 2)]⟩,
  ⟨157, 2, [(13, 1)]⟩,
  ⟨1571, 2, [(157, 1)]⟩,
  ⟨2837227, 2, [(1571, 1), (43, 1)]⟩,
  ⟨187256983, 2, [(2837227, 1)]⟩,
  ⟨2567293236931, 2, [(187256983, 1)]⟩,
  ⟨431305263804409, 2, [(2567293236931, 1)]⟩,
  ⟨203928654140967434528233, 2, [(431305263804409, 1)]⟩,
  ⟨6554484396890773809930967563523245729705921265872317281365359162392183254199, 2,
    [(255074062430788457494141376149, 1), (203928654140967434528233, 1)]⟩
]

/-- Kernel-certified primality of `P_ED25519 = 2^255 - 19`. -/
theorem p_ed25519_isPrime : IsPrimeNat P_ED25519 :=
  certVerifyPrime_sound (chain := ed25519AndJubjubPrimeChain) (by decide +kernel)

/-- Kernel-certified primality of `R_ED25519 = ED25519_ORDER_L`. -/
theorem r_ed25519_isPrime : IsPrimeNat R_ED25519 :=
  certVerifyPrime_sound (chain := ed25519AndJubjubPrimeChain) (by decide +kernel)

/-- Kernel-certified primality of `R_JUBJUB` (Zcash Sapling scalar subgroup order). -/
theorem r_jubjub_isPrime : IsPrimeNat R_JUBJUB :=
  certVerifyPrime_sound (chain := ed25519AndJubjubPrimeChain) (by decide +kernel)

/-- Kernel-certified primality of `SECP256K1_FIELD_P`. -/
theorem p_secp256k1_isPrime : IsPrimeNat SECP256K1_FIELD_P :=
  secp256k1FieldPrime_isPrime

/-- Kernel-certified primality of `SECP256K1_ORDER_N`. -/
theorem n_secp256k1_isPrime : IsPrimeNat SECP256K1_ORDER_N :=
  secp256k1OrderPrime_isPrime

/-- Kernel-certified primality of `p_pallas` (`= q_vesta`). -/
theorem p_pallas_isPrimeNat : IsPrimeNat p_pallas := p_pallas_isPrime

/-- Kernel-certified primality of `q_pallas` (`= p_vesta`). -/
theorem q_pallas_isPrimeNat : IsPrimeNat q_pallas := q_pallas_isPrime

/-- Kernel-certified primality of `p_bls381`. -/
theorem p_bls381_isPrimeNat : IsPrimeNat p_bls381 := p_bls381_isPrime

/-- Kernel-certified primality of `r_bls381` (`= q_jubjub`). -/
theorem r_bls381_isPrimeNat : IsPrimeNat r_bls381 := r_bls381_isPrime

/-- **Master Production Curve Primality Certificate**:
    Every deployed migration base field and prime-order scalar subgroup modulus across
    `secp256k1`, `Ed25519`, `Pallas`/`Vesta`, `Jubjub`, and `BLS12-381` is certified prime. -/
theorem all_production_curve_moduli_prime :
    IsPrimeNat SECP256K1_FIELD_P ∧
    IsPrimeNat SECP256K1_ORDER_N ∧
    IsPrimeNat P_ED25519 ∧
    IsPrimeNat R_ED25519 ∧
    IsPrimeNat p_pallas ∧
    IsPrimeNat q_pallas ∧
    IsPrimeNat p_vesta ∧
    IsPrimeNat q_vesta ∧
    IsPrimeNat q_jubjub ∧
    IsPrimeNat R_JUBJUB ∧
    IsPrimeNat p_bls381 ∧
    IsPrimeNat r_bls381 :=
  ⟨p_secp256k1_isPrime, n_secp256k1_isPrime, p_ed25519_isPrime, r_ed25519_isPrime,
   p_pallas_isPrimeNat, q_pallas_isPrimeNat, q_pallas_isPrimeNat, p_pallas_isPrimeNat,
   r_bls381_isPrimeNat, r_jubjub_isPrime, p_bls381_isPrimeNat, r_bls381_isPrimeNat⟩

/-- `#tooth` Cofactor-8 full twisted-Edwards curve orders `8 * R_ED25519` and `8 * R_JUBJUB`
    are composite and rejected by `certVerifyPrime` and `IsPrimeNat`. -/
theorem tooth_cofactor8_edwards_orders_not_prime :
    ¬ (IsPrimeNat (8 * R_ED25519) ∨
       IsPrimeNat (8 * R_JUBJUB) ∨
       certVerifyPrime ed25519AndJubjubPrimeChain (8 * R_ED25519) = true) := by
  rintro (hP | hJ | hCert)
  · rcases hP.2 2 ⟨4 * R_ED25519, by omega⟩ with h1 | hEq
    · omega
    · have := r_ed25519_isPrime.1; omega
  · rcases hJ.2 2 ⟨4 * R_JUBJUB, by omega⟩ with h1 | hEq
    · omega
    · have := r_jubjub_isPrime.1; omega
  · revert hCert; decide +kernel

/-! ## §2. Constructive `PrimeMod p` Residue Field (`LawfulField` via `extGcd`) -/

/-- Typeclass carrying a constructive proof `IsPrimeNat p`. -/
class CurveFactPrime (p : Nat) : Prop where
  isPrime : IsPrimeNat p

instance : CurveFactPrime SECP256K1_FIELD_P := ⟨p_secp256k1_isPrime⟩
instance : CurveFactPrime SECP256K1_ORDER_N := ⟨n_secp256k1_isPrime⟩
instance : CurveFactPrime P_ED25519 := ⟨p_ed25519_isPrime⟩
instance : CurveFactPrime R_ED25519 := ⟨r_ed25519_isPrime⟩
instance : CurveFactPrime p_pallas := ⟨p_pallas_isPrimeNat⟩
instance : CurveFactPrime q_pallas := ⟨q_pallas_isPrimeNat⟩
instance : CurveFactPrime R_JUBJUB := ⟨r_jubjub_isPrime⟩
instance : CurveFactPrime p_bls381 := ⟨p_bls381_isPrimeNat⟩
instance : CurveFactPrime r_bls381 := ⟨r_bls381_isPrimeNat⟩

/-- Canonical prime-field element mod `p`: natural residue `val < p`. -/
