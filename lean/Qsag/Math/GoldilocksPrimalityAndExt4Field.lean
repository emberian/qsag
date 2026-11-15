module
/-
# Qsag.Math.GoldilocksPrimalityAndExt4Field — Constructive Primality, Universal Inversion & Quartic Field

Self-contained Lean 4.35 algebraic foundation closing universal primality, inversion, and quartic
irreducibility obligations over `Qsag.Goldilocks` (`0 sorry`, `0 Classical.choice`, `0 native_decide`):
1. **Lucas–BLS $N - 1$ Primality & Fermat-Totient Certification (`checkLucasBlsCert_sound`)**:
   Constructive primality and primitive-root order over $p - 1 = 2^{32} \cdot 3 \cdot 5 \cdot 17 \cdot 257 \cdot 65537$,
   establishing `goldilocksPrime_is_prime`, `goldilocks_lucas_fermat_witnesses`, and `goldilocks_seven_primitive_root`.
2. **Universal `Goldilocks` Multiplicative Inverse & Bezout Equivalence
   (`goldilocks_universal_mul_inv_cancel`, `goldilocks_invBezout_eq_inv`, `goldilocks_mul_eq_zero_iff`)**.
3. **Constructive Irreducibility of $v^4 - 7 \in \mathbb{F}_p[v]$ & Universal `GoldilocksExt4`
   Division (`v_pow4_sub_seven_irreducible`, `ext4_mul_inv_cancel`, `towerToPoly_mul_hom`)**.
-/

public import Qsag.Math.Goldilocks
import all Qsag.Math.Goldilocks
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-- Canonical alias `Goldilocks.p = 2^64 - 2^32 + 1 = 18446744069414584321`. -/
abbrev Goldilocks.p : Nat := goldilocksPrime

/-! ## 1. Constructive Lucas–BLS $N - 1$ Primality & Fermat-Prime Factorization of $p - 1$ -/

/-- Fast 64-bit binary modular exponentiation (`O(log e)` kernel reductions, `0 native_decide`). -/
@[expose] def powMod (base exp m : Nat) : Nat := modPowFuel 64 base exp m

theorem powMod_eq_pow_mod {base exp m : Nat} (hLt : exp < 2 ^ 64) :
    powMod base exp m = (base ^ exp) % m := modPowFuel_eq_pow_mod 64 base exp m hLt

/-- Product $\prod_{(q, e)} q^e$ of prime-power factors of $N - 1$. -/
@[expose] def facPowProd : List (Nat × Nat) → Nat
  | [] => 1
  | (q, e) :: rest => q ^ e * facPowProd rest

/-- Executable Lucas–Brillhart–Lehmer–Selfridge $N - 1$ primality & primitive-root checker. -/
@[expose] def checkLucasBlsCert (N g : Nat) (facs : List (Nat × Nat)) : Bool :=
  decide (2 ≤ N) && decide (facPowProd facs = N - 1) &&
  facs.all (fun qe => decide (0 < qe.2)) && decide (powMod g (N - 1) N = 1) &&
  facs.all (fun qe =>
    let rem := powMod g ((N - 1) / qe.1) N
    decide (rem ≠ 1) && decide (Nat.gcd (rem - 1) N = 1))

private theorem prime_dvd_pow {r q : Nat} (hr : IsPrimeNat r) :
    ∀ {e : Nat}, r ∣ q ^ e → r ∣ q
  | 0, hd => by
    rw [Nat.pow_zero] at hd; have := Nat.le_of_dvd (by decide) hd; have := hr.1; omega
  | _ + 1, hd => by
    rw [Nat.pow_succ] at hd
    if hrq : r ∣ q then exact hrq
    else exact prime_dvd_pow hr (hr.dvd_mul (Nat.mul_comm _ q ▸ hd) hrq)

private theorem prime_mem_of_dvd_facPowProd {r : Nat} (hr : IsPrimeNat r) :
    ∀ {facs : List (Nat × Nat)},
      (∀ qe ∈ facs, IsPrimeNat qe.1) → r ∣ facPowProd facs → ∃ qe ∈ facs, r = qe.1
  | [], _, hd => by
    dsimp only [facPowProd] at hd; have := Nat.le_of_dvd (by decide) hd; have := hr.1; omega
  | (q, e) :: rest, hPrimes, hd => by
    dsimp only [facPowProd] at hd
    if hrPow : r ∣ q ^ e then
      rcases (hPrimes (q, e) (.head _)).2 r (prime_dvd_pow hr hrPow) with h1 | hEq
      · have := hr.1; omega
      · exact ⟨(q, e), .head _, hEq⟩
    else
      obtain ⟨qe, hMem, hEq⟩ :=
        prime_mem_of_dvd_facPowProd hr (fun x hx => hPrimes x (.tail _ hx)) (hr.dvd_mul hd hrPow)
      exact ⟨qe, .tail _ hMem, hEq⟩

private theorem dvd_totient_prime_step {N d : Nat} {facs : List (Nat × Nat)}
    (hFac : facPowProd facs = N - 1) (hPrimes : ∀ qe ∈ facs, IsPrimeNat qe.1)
    (hdDvd : d ∣ (N - 1)) (hdLt : d < N - 1) :
    ∃ qe ∈ facs, ∃ u : Nat, (N - 1) / qe.1 = d * u := by
  obtain ⟨m, hmEq⟩ := hdDvd
  have hmGe2 : 2 ≤ m := by
    if hm0 : m = 0 then subst hm0; omega else if hm1 : m = 1 then subst hm1; omega else omega
  obtain ⟨hQPrime, hQDvdM, _⟩ := minDivisor_isPrime hmGe2
  let q := minDivisor m
  have hQDvdFac : q ∣ facPowProd facs := by
    rw [hFac, hmEq]; exact Nat.dvd_trans hQDvdM (Nat.dvd_mul_left m d)
  obtain ⟨qe, hQeMem, hQEq⟩ := prime_mem_of_dvd_facPowProd hQPrime hPrimes hQDvdFac
  obtain ⟨u, huEq⟩ := hQDvdM
  refine ⟨qe, hQeMem, u, ?_⟩
  have hNm1 : N - 1 = qe.1 * (d * u) := by
    rw [hmEq, huEq, ← hQEq, ← Nat.mul_assoc, Nat.mul_comm d q, Nat.mul_assoc]
  have hqPos : 0 < qe.1 := by have := hQPrime.1; omega
  rw [hNm1, Nat.mul_div_right _ hqPos]

/-- **Constructive Lucas–BLS $N - 1$ Primality & Primitive-Root Theorem (`checkLucasBlsCert_sound`)**:
    Whenever every factor base `qe.1` in `facs` is prime, `N - 1 < 2 ^ 64`, and
    `checkLucasBlsCert N g facs = true`, `N` is prime AND `g` has exact order `N - 1` mod `N`. -/
theorem checkLucasBlsCert_sound {N g : Nat} {facs : List (Nat × Nat)}
    (hBound : N - 1 < 2 ^ 64) (hPrimes : ∀ qe ∈ facs, IsPrimeNat qe.1)
    (hCert : checkLucasBlsCert N g facs = true) :
    IsPrimeNat N ∧ (∀ k : Nat, 1 ≤ k → k < N - 1 → (g ^ k) % N ≠ 1) := by
  simp only [checkLucasBlsCert, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hCert
  rcases hCert with ⟨⟨⟨⟨hN2, hFac⟩, _⟩, hFermatPow⟩, hFactors⟩
  have hFermat : (g ^ (N - 1)) % N = 1 := by rwa [powMod_eq_pow_mod hBound] at hFermatPow
  have hPrimeN : IsPrimeNat N := by
    refine ⟨hN2, fun d hd => ?_⟩
    if hd1 : d = 1 then exact .inl hd1
    else if hdN : d = N then exact .inr hdN
    else
      exfalso
      have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
      have hdLe : d ≤ N := Nat.le_of_dvd (by omega) hd
      obtain ⟨hrPrime, hrDvdD, hrLeD⟩ := minDivisor_isPrime (n := d) (by omega)
      let r := minDivisor d
      have hrDvdN : r ∣ N := Nat.dvd_trans hrDvdD hd
      have hr2 : 2 ≤ r := hrPrime.1
      have hModR : (g ^ (N - 1)) % r = 1 := by
        rw [← Nat.mod_mod_of_dvd (g ^ (N - 1)) hrDvdN, hFermat]; exact Nat.mod_eq_of_lt hr2
      have hNotDvdG : ¬ (r ∣ g) := by
        rintro ⟨c, rfl⟩
        have hPowSplit : N - 1 = (N - 2) + 1 := by omega
        rw [hPowSplit, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm _ r, Nat.mul_assoc,
            Nat.mul_mod_right] at hModR; cases hModR
      let k := Nat.gcd (N - 1) (r - 1)
      have hkPow : (g ^ k) % r = 1 :=
        pow_gcd_mod_eq_one hr2 (N - 1) (r - 1) hModR (hrPrime.pow_sub_one_mod hNotDvdG)
      have hkLeRm1 : k ≤ r - 1 := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right (N - 1) (r - 1))
      obtain ⟨qe, hQeMem, u, hDivEq⟩ :=
        dvd_totient_prime_step hFac hPrimes (Nat.gcd_dvd_left (N - 1) (r - 1)) (by omega)
      have hStepBound : (N - 1) / qe.1 < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hBound
      obtain ⟨_, hGcd1⟩ := hFactors qe hQeMem
      rw [powMod_eq_pow_mod hStepBound] at hGcd1
      let rem := (g ^ ((N - 1) / qe.1)) % N
      have hRemModR : rem % r = 1 := by
        dsimp only [rem]; rw [Nat.mod_mod_of_dvd _ hrDvdN, hDivEq, Nat.pow_mul]
        exact pow_mod_eq_one_of_eq_one hr2 hkPow u
      have hRemSub : r ∣ (rem - 1) := by
        have hdiv := Nat.div_add_mod rem r
        have hRemGe1 : 1 ≤ rem := by
          if hz : rem = 0 then rw [hz, Nat.zero_mod] at hRemModR; cases hRemModR else omega
        rw [hRemModR] at hdiv; exact ⟨rem / r, by omega⟩
      have hrDvdGcd : r ∣ Nat.gcd (rem - 1) N := Nat.dvd_gcd hRemSub hrDvdN
      rw [hGcd1] at hrDvdGcd; have := Nat.le_of_dvd (by decide) hrDvdGcd; omega
  refine ⟨hPrimeN, fun k hk1 hkLt hgk => ?_⟩
  let d := Nat.gcd (N - 1) k
  have hdPow : (g ^ d) % N = 1 := pow_gcd_mod_eq_one hN2 (N - 1) k hFermat hgk
  have hdLeK : d ≤ k := Nat.le_of_dvd hk1 (Nat.gcd_dvd_right (N - 1) k)
  obtain ⟨qe, hQeMem, u, hDivEq⟩ :=
    dvd_totient_prime_step hFac hPrimes (Nat.gcd_dvd_left (N - 1) k) (by omega)
  have hStepBound : (N - 1) / qe.1 < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hBound
  obtain ⟨hRemNe1, _⟩ := hFactors qe hQeMem
  rw [powMod_eq_pow_mod hStepBound, hDivEq, Nat.pow_mul,
      pow_mod_eq_one_of_eq_one hN2 hdPow u] at hRemNe1
  exact hRemNe1 rfl

theorem isPrimeNat_2 : IsPrimeNat 2 :=
  ⟨by decide, fun _ hd => by
    have := Nat.pos_of_dvd_of_pos hd (by decide); have := Nat.le_of_dvd (by decide) hd; omega⟩
theorem isPrimeNat_3 : IsPrimeNat 3 :=
  (checkLucasBlsCert_sound (N := 3) (g := 2) (facs := [(2, 1)]) (by decide)
    (fun _ h => List.mem_singleton.mp h ▸ isPrimeNat_2) (by decide)).1
theorem isPrimeNat_5 : IsPrimeNat 5 :=
  (checkLucasBlsCert_sound (N := 5) (g := 3) (facs := [(2, 2)]) (by decide)
    (fun _ h => List.mem_singleton.mp h ▸ isPrimeNat_2) (by decide)).1
theorem isPrimeNat_17 : IsPrimeNat 17 :=
  (checkLucasBlsCert_sound (N := 17) (g := 3) (facs := [(2, 4)]) (by decide)
    (fun _ h => List.mem_singleton.mp h ▸ isPrimeNat_2) (by decide)).1
theorem isPrimeNat_257 : IsPrimeNat 257 :=
  (checkLucasBlsCert_sound (N := 257) (g := 3) (facs := [(2, 8)]) (by decide)
    (fun _ h => List.mem_singleton.mp h ▸ isPrimeNat_2) (by decide)).1
theorem isPrimeNat_65537 : IsPrimeNat 65537 :=
  (checkLucasBlsCert_sound (N := 65537) (g := 3) (facs := [(2, 16)]) (by decide)
    (fun _ h => List.mem_singleton.mp h ▸ isPrimeNat_2) (by decide)).1

/-- Complete prime-power factorization of $p - 1 = 2^{32} \cdot 3 \cdot 5 \cdot 17 \cdot 257 \cdot 65537$. -/
def goldilocksTotientFactors : List (Nat × Nat) :=
  [(2, 32), (3, 1), (5, 1), (17, 1), (257, 1), (65537, 1)]

theorem goldilocks_totient_fermat_factorization :
    Goldilocks.p - 1 = 2 ^ 32 * 3 * 5 * 17 * 257 * 65537 ∧
    facPowProd goldilocksTotientFactors = Goldilocks.p - 1 := ⟨by decide, by decide⟩

private theorem goldilocksTotientFactors_all_prime :
    ∀ qe ∈ goldilocksTotientFactors, IsPrimeNat qe.1 := by
  intro qe hMem
  simp only [goldilocksTotientFactors, List.mem_cons, List.not_mem_nil, or_false] at hMem
  rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact isPrimeNat_2
  · exact isPrimeNat_3
  · exact isPrimeNat_5
  · exact isPrimeNat_17
  · exact isPrimeNat_257
  · exact isPrimeNat_65537

theorem goldilocks_lucas_cert_valid :
    checkLucasBlsCert Goldilocks.p 7 goldilocksTotientFactors = true := by decide

/-- **Constructive Primality of Goldilocks $p = 2^{64} - 2^{32} + 1$ (`goldilocksPrime_is_prime`)**. -/
theorem goldilocksPrime_is_prime : IsPrimeNat Goldilocks.p :=
  (checkLucasBlsCert_sound (by decide) goldilocksTotientFactors_all_prime goldilocks_lucas_cert_valid).1

/-- Explicit Lucas–Fermat witnesses at $g = 7$ for all 6 prime factors of $p - 1$. -/
theorem goldilocks_lucas_fermat_witnesses :
    powMod 7 (Goldilocks.p - 1) Goldilocks.p = 1 ∧
    ∀ q ∈ ([2, 3, 5, 17, 257, 65537] : List Nat),
      powMod 7 ((Goldilocks.p - 1) / q) Goldilocks.p ≠ 1 := by
  refine ⟨by decide, fun q hq => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- **Primitive-Root Theorem (`goldilocks_seven_primitive_root`)**:
    $g = 7$ generates $\mathbb{F}_p^\times$ with exact multiplicative order $p - 1$. -/
theorem goldilocks_seven_primitive_root :
    powMod 7 (Goldilocks.p - 1) Goldilocks.p = 1 ∧
    ∀ k : Nat, 1 ≤ k → k < Goldilocks.p - 1 → (7 ^ k) % Goldilocks.p ≠ 1 :=
  ⟨by decide,
   (checkLucasBlsCert_sound (by decide) goldilocksTotientFactors_all_prime goldilocks_lucas_cert_valid).2⟩

/-- **`#tooth` Proth-Shaped Composite Counterexample (`tooth_proth16_65281_not_prime`)**. -/
theorem tooth_proth16_65281_not_prime :
    ∃ N : Nat, N = 2 ^ 16 - 2 ^ 8 + 1 ∧ N = 97 * 673 ∧
      checkLucasBlsCert N 7 [(2, 8), (3, 1), (5, 1), (17, 1)] = false ∧ ¬ IsPrimeNat N :=
  ⟨65281, by decide, by decide, by decide, fun hp => by
    rcases hp.2 97 ⟨673, by decide⟩ with h1 | h2 <;> omega⟩

/-- **`#tooth` Carmichael Pseudoprime Refusal (`tooth_carmichael_561_rejected`)**. -/
theorem tooth_carmichael_561_rejected :
    ∃ N : Nat, N = 561 ∧ powMod 2 (N - 1) N = 1 ∧
      checkLucasBlsCert N 2 [(2, 4), (5, 1), (7, 1)] = false ∧ ¬ IsPrimeNat N :=
  ⟨561, rfl, by decide, by decide, fun hp => by
    rcases hp.2 3 ⟨187, by decide⟩ with h1 | h2 <;> omega⟩

/-! ## 2. Universal Two-Sided Multiplicative Inverse & Bezout Equivalence on `Goldilocks` -/

/-- Constructive extended-Euclidean Bezout field inverse on `Goldilocks` (`invBezout 0 = 0`). -/
def Goldilocks.invBezout (x : Goldilocks) : Goldilocks :=
  if x.val = 0 then Goldilocks.zero else goldOfInt (extGcd x.val Goldilocks.p).2.1

/-- **Universal Two-Sided `Goldilocks` Inverse Law (`goldilocks_universal_mul_inv_cancel`)**. -/
theorem goldilocks_universal_mul_inv_cancel (x : Goldilocks) (hx : x ≠ Goldilocks.zero) :
    CommRingOps.mul x (Goldilocks.inv x) = CommRingOps.one ∧
    CommRingOps.mul (Goldilocks.inv x) x = CommRingOps.one :=
  let hR := Goldilocks.mul_inv_cancel hx
  ⟨hR, (LawfulCommRing.mul_comm _ _).trans hR⟩

/-- **Universal Bezout Inverse Soundness (`goldilocks_mul_invBezout_cancel`)**. -/
theorem goldilocks_mul_invBezout_cancel (x : Goldilocks) (hx : x ≠ Goldilocks.zero) :
    CommRingOps.mul x (Goldilocks.invBezout x) = CommRingOps.one ∧
    CommRingOps.mul (Goldilocks.invBezout x) x = CommRingOps.one := by
  have hxValNe : x.val ≠ 0 := fun h0 => hx (Goldilocks.ext h0)
  obtain ⟨hdx, hdp⟩ := extGcd_dvd x.val Goldilocks.p
  have hg1 : (extGcd x.val Goldilocks.p).1 = 1 := by
    rcases goldilocksPrime_is_prime.2 _ hdp with h1 | hpEq
    · exact h1
    · rw [hpEq] at hdx
      have hle := Nat.le_of_dvd (by omega) hdx; have := x.isLt; unfold Goldilocks.p at hle; omega
  have hbez := extGcd_bezout x.val Goldilocks.p; rw [hg1] at hbez
  have hRight : CommRingOps.mul x (Goldilocks.invBezout x) = CommRingOps.one := by
    unfold Goldilocks.invBezout; simp only [hxValNe, ↓reduceIte]
    change Goldilocks.mul x (goldOfInt (extGcd x.val Goldilocks.p).2.1) = Goldilocks.one
    have hMulInt : Goldilocks.mul x (goldOfInt (extGcd x.val Goldilocks.p).2.1) =
        goldOfInt ((x.val : Int) * (extGcd x.val Goldilocks.p).2.1) := by
      have h := goldOfInt_mul x.val (extGcd x.val Goldilocks.p).2.1; rwa [goldOfInt_nat] at h
    rw [hMulInt]; apply Goldilocks.ext; apply Int.ofNat_inj.mp; rw [goldOfInt_val]
    have hMod : ((x.val : Int) * (extGcd x.val Goldilocks.p).2.1) % goldP = 1 := by
      have hEq : (x.val : Int) * (extGcd x.val Goldilocks.p).2.1 =
          1 + goldP * (-(extGcd x.val Goldilocks.p).2.2) := by
        dsimp only [goldP, Goldilocks.p] at hbez ⊢; rw [Int.mul_neg]; omega
      rw [hEq, Int.add_mul_emod_self_left]; decide
    rw [hMod]; rfl
  exact ⟨hRight, (LawfulCommRing.mul_comm _ _).trans hRight⟩

/-- Exact agreement of Fermat exponentiation inverse and Euclidean Bezout inverse for ALL `x`. -/
theorem goldilocks_invBezout_eq_inv (x : Goldilocks) :
    Goldilocks.invBezout x = Goldilocks.inv x := by
  if hx : x = Goldilocks.zero then subst hx; rfl
  else
    have hB := (goldilocks_mul_invBezout_cancel x hx).1
    have hF := (goldilocks_universal_mul_inv_cancel x hx).2
    calc Goldilocks.invBezout x
        = CommRingOps.mul CommRingOps.one (Goldilocks.invBezout x) := (LawfulCommRing.one_mul _).symm
      _ = CommRingOps.mul (CommRingOps.mul (Goldilocks.inv x) x) (Goldilocks.invBezout x) := by rw [hF]
      _ = CommRingOps.mul (Goldilocks.inv x) (CommRingOps.mul x (Goldilocks.invBezout x)) :=
            LawfulCommRing.mul_assoc _ _ _
      _ = CommRingOps.mul (Goldilocks.inv x) CommRingOps.one := by rw [hB]
      _ = Goldilocks.inv x := LawfulCommRing.mul_one _

/-- **Integral-Domain Zero-Product Characterization (`goldilocks_mul_eq_zero_iff`)**. -/
theorem goldilocks_mul_eq_zero_iff (x y : Goldilocks) :
    CommRingOps.mul x y = Goldilocks.zero ↔ x = Goldilocks.zero ∨ y = Goldilocks.zero := by
  constructor
  · exact NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero
  · rintro (rfl | rfl)
    · exact LawfulCommRing.zero_mul y
    · exact LawfulCommRing.mul_zero x

/-! ## 3. Irreducibility of $v^4 - 7 \in \mathbb{F}_p[v]$ & Universal `GoldilocksExt4` Division -/

private theorem sq_mul_sq_eq {R : Type} [LawfulCommRing R] (a b : R) :
    CommRingOps.mul (CommRingOps.mul a b) (CommRingOps.mul a b) =
      CommRingOps.mul (CommRingOps.mul a a) (CommRingOps.mul b b) := by
  rw [LawfulCommRing.mul_assoc a b _, ← LawfulCommRing.mul_assoc b a _,
      LawfulCommRing.mul_comm b a, LawfulCommRing.mul_assoc a b _, ← LawfulCommRing.mul_assoc a a _]

/-- Exact norm characterization on `GoldilocksExt2`: $a^2 - 7 b^2 = 0 \iff a = 0 \land b = 0$. -/
theorem norm_ext2_eq_zero_iff (z : GoldilocksExt2) :
    GoldilocksExt2.norm z = Goldilocks.zero ↔ z = GoldilocksExt2.zero := by
  constructor
  · intro hN
    if hz : z = GoldilocksExt2.zero then exact hz
    else exact False.elim (GoldilocksExt2.norm_ne_zero hz hN)
  · rintro rfl
    change CommRingOps.sub (CommRingOps.mul CommRingOps.zero CommRingOps.zero)
      (CommRingOps.mul GoldilocksExt2.nonResidue (CommRingOps.mul CommRingOps.zero CommRingOps.zero)) =
      CommRingOps.zero
    rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_zero, LawfulCommRing.sub_self]

/-- Parametric modular quadratic-extension multiplication $(a_0 + a_1 u)(b_0 + b_1 u) \bmod (m, u^2 - r)$. -/
@[expose] def quadExtMulMod (m r : Nat) (x y : Nat × Nat) : Nat × Nat :=
  ((x.1 * y.1 + r * (x.2 * y.2)) % m, (x.1 * y.2 + x.2 * y.1) % m)

theorem goldilocksExt2_mul_coords_eq_quadExtMulMod (x y : GoldilocksExt2) :
    ((GoldilocksExt2.mul x y).c0.val, (GoldilocksExt2.mul x y).c1.val) =
      quadExtMulMod Goldilocks.p 7 (x.c0.val, x.c1.val) (y.c0.val, y.c1.val) := by
  unfold GoldilocksExt2.mul quadExtMulMod
  dsimp only [CommRingOps.add, CommRingOps.mul, GoldilocksExt2.nonResidue, Goldilocks.p]
  apply Prod.ext <;> dsimp only
  · rw [Goldilocks.add_val, Goldilocks.mul_val, Goldilocks.mul_val, Goldilocks.mul_val,
        Nat.mul_mod_mod, Nat.add_mod_mod, Nat.mod_add_mod]
  · rw [Goldilocks.add_val, Goldilocks.mul_val, Goldilocks.mul_val, Nat.mod_add_mod, Nat.add_mod_mod]

/-- **Universal Integral-Domain Law via `quadExtMulMod` at `(Goldilocks.p, 7)`**. -/
theorem goldilocks_quadExtMulMod_no_zero_divisors (x y : GoldilocksExt2) :
    quadExtMulMod Goldilocks.p 7 (x.c0.val, x.c1.val) (y.c0.val, y.c1.val) = (0, 0) ↔
      x = GoldilocksExt2.zero ∨ y = GoldilocksExt2.zero := by
  rw [← goldilocksExt2_mul_coords_eq_quadExtMulMod]
  constructor
  · intro hPair
    exact NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero
      (GoldilocksExt2.ext (Goldilocks.ext (Prod.mk.inj hPair).1) (Goldilocks.ext (Prod.mk.inj hPair).2))
  · rintro (rfl | rfl)
    · rw [show GoldilocksExt2.mul GoldilocksExt2.zero y = GoldilocksExt2.zero from LawfulCommRing.zero_mul y]; rfl
    · rw [show GoldilocksExt2.mul x GoldilocksExt2.zero = GoldilocksExt2.zero from LawfulCommRing.mul_zero x]; rfl

/-- **`#tooth` Non-Trivial Zero-Divisor Modulo $29$ (`tooth_mod29_seven_residue_zero_divisor`)**:
    Modulo $29$, $7 \equiv 6^2 \pmod{29}$, so $(6 - u)(6 + u) = 0$ in $(\mathbb{Z}/29\mathbb{Z})[u]/(u^2 - 7)$. -/
theorem tooth_mod29_seven_residue_zero_divisor :
    ∃ x y : Nat × Nat, x = (6, 28) ∧ y = (6, 1) ∧ x ≠ (0, 0) ∧ y ≠ (0, 0) ∧
      quadExtMulMod 29 7 x y = (0, 0) :=
  ⟨(6, 28), (6, 1), rfl, rfl, by decide, by decide, by decide⟩

/-- Square root of $-1$ in `Goldilocks`: $\iota = 2^{48}$ satisfies $\iota^2 = 2^{96} \equiv -1 \pmod p$. -/
def goldilocksSqrtNegOne : Goldilocks := ⟨2 ^ 48, by decide⟩

theorem goldilocksSqrtNegOne_sq :
    CommRingOps.mul goldilocksSqrtNegOne goldilocksSqrtNegOne = CommRingOps.neg CommRingOps.one := by
  apply Goldilocks.ext
  change (Goldilocks.mul goldilocksSqrtNegOne goldilocksSqrtNegOne).val = (Goldilocks.neg Goldilocks.one).val
  rw [Goldilocks.mul_val, Goldilocks.neg_val]; decide

/-- $-7$ is ALSO a quadratic non-residue in `Goldilocks`. -/
theorem neg_seven_not_square_in_goldilocks (x : Goldilocks) :
    CommRingOps.mul x x ≠ CommRingOps.neg GoldilocksExt2.nonResidue := by
  intro hSq
  have hwSq : CommRingOps.mul (CommRingOps.mul x goldilocksSqrtNegOne)
      (CommRingOps.mul x goldilocksSqrtNegOne) = GoldilocksExt2.nonResidue := by
    rw [sq_mul_sq_eq, hSq, goldilocksSqrtNegOne_sq, LawfulCommRing.neg_mul,
        LawfulCommRing.mul_neg, LawfulCommRing.neg_neg, LawfulCommRing.mul_one]
  exact GoldilocksExt2.nonResidue_not_square _ hwSq

/-- Predicate stating $(v^2 + a_1 v + a_0)(v^2 + b_1 v + b_0) = v^4 - 7$ in $\mathbb{F}_p[v]$. -/
@[expose] def IsMonicQuadFactorOfV4Sub7 (a1 a0 b1 b0 : Goldilocks) : Prop :=
  CommRingOps.add a1 b1 = Goldilocks.zero ∧
  CommRingOps.add (CommRingOps.add a0 b0) (CommRingOps.mul a1 b1) = Goldilocks.zero ∧
  CommRingOps.add (CommRingOps.mul a1 b0) (CommRingOps.mul b1 a0) = Goldilocks.zero ∧
  CommRingOps.mul a0 b0 = CommRingOps.neg GoldilocksExt2.nonResidue

/-- **Complete Polynomial Irreducibility of $v^4 - 7 \in \mathbb{F}_p[v]$ (`v_pow4_sub_seven_irreducible`)**. -/
theorem v_pow4_sub_seven_irreducible :
    (∀ r : Goldilocks,
      CommRingOps.mul (CommRingOps.mul r r) (CommRingOps.mul r r) ≠ GoldilocksExt2.nonResidue) ∧
    (∀ a1 a0 b1 b0 : Goldilocks, ¬ IsMonicQuadFactorOfV4Sub7 a1 a0 b1 b0) := by
  refine ⟨fun r h4 => GoldilocksExt2.nonResidue_not_square (CommRingOps.mul r r) h4, ?_⟩
  intro a1 a0 b1 b0 ⟨hDeg3, hDeg2, hDeg1, hConst⟩
  have hb1 : b1 = CommRingOps.neg a1 :=
    LawfulCommRing.add_left_cancel (hDeg3.trans (LawfulCommRing.add_right_neg a1).symm)
  if ha1Zero : a1 = Goldilocks.zero then
    subst ha1Zero
    have ha1b1 : CommRingOps.mul Goldilocks.zero b1 = CommRingOps.zero := LawfulCommRing.zero_mul b1
    rw [ha1b1, LawfulCommRing.add_zero] at hDeg2
    have hb0 : b0 = CommRingOps.neg a0 :=
      LawfulCommRing.add_left_cancel (hDeg2.trans (LawfulCommRing.add_right_neg a0).symm)
    rw [hb0, LawfulCommRing.mul_neg] at hConst
    have hNeg := congrArg CommRingOps.neg hConst
    rw [LawfulCommRing.neg_neg, LawfulCommRing.neg_neg] at hNeg
    exact GoldilocksExt2.nonResidue_not_square a0 hNeg
  else
    rw [hb1, LawfulCommRing.neg_mul, ← LawfulCommRing.sub_eq_add_neg, ← LawfulCommRing.mul_sub] at hDeg1
    rcases (goldilocks_mul_eq_zero_iff a1 (CommRingOps.sub b0 a0)).mp hDeg1 with hBad | hSub0
    · exact ha1Zero hBad
    · rw [LawfulCommRing.sub_eq_zero_iff.mp hSub0] at hConst
      exact neg_seven_not_square_in_goldilocks a0 hConst

namespace GoldilocksField

/-- Quartic extension field $\mathbb{F}_{p^4} = \mathbb{F}_{p^2}[v]/(v^2 - u)$ ($u^2 = 7, v^4 = 7$). -/
structure GoldilocksExt4 where
  c0 : GoldilocksExt2
  c1 : GoldilocksExt2
  deriving DecidableEq, Repr

namespace GoldilocksExt4

def nonResidue : GoldilocksExt2 := GoldilocksExt2.uBasis

theorem ext {x y : GoldilocksExt4} (h0 : x.c0 = y.c0) (h1 : x.c1 = y.c1) : x = y := by
  cases x; cases y; simp only at h0 h1; subst h0 h1; rfl

@[expose] def zero : GoldilocksExt4 := ⟨CommRingOps.zero, CommRingOps.zero⟩
@[expose] def one : GoldilocksExt4 := ⟨CommRingOps.one, CommRingOps.zero⟩
def vBasis : GoldilocksExt4 := ⟨CommRingOps.zero, CommRingOps.one⟩
def ofExt2 (a : GoldilocksExt2) : GoldilocksExt4 := ⟨a, CommRingOps.zero⟩
def embedBase (a : Goldilocks) : GoldilocksExt4 := ⟨GoldilocksExt2.ofBase a, CommRingOps.zero⟩

instance : Inhabited GoldilocksExt4 := ⟨zero⟩

def add (x y : GoldilocksExt4) : GoldilocksExt4 := ⟨CommRingOps.add x.c0 y.c0, CommRingOps.add x.c1 y.c1⟩
def neg (x : GoldilocksExt4) : GoldilocksExt4 := ⟨CommRingOps.neg x.c0, CommRingOps.neg x.c1⟩
def sub (x y : GoldilocksExt4) : GoldilocksExt4 := ⟨CommRingOps.sub x.c0 y.c0, CommRingOps.sub x.c1 y.c1⟩
@[expose] def mul (x y : GoldilocksExt4) : GoldilocksExt4 :=
  ⟨CommRingOps.add (CommRingOps.mul x.c0 y.c0) (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1)),
   CommRingOps.add (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c1 y.c0)⟩

instance : CommRingOps GoldilocksExt4 where
  zero := zero; one := one; add := add; mul := mul; neg := neg; sub := sub

instance : LawfulCommRing GoldilocksExt4 where
  add_assoc x y z := by exact ext (LawfulCommRing.add_assoc x.c0 y.c0 z.c0) (LawfulCommRing.add_assoc x.c1 y.c1 z.c1)
  add_comm x y := by exact ext (LawfulCommRing.add_comm x.c0 y.c0) (LawfulCommRing.add_comm x.c1 y.c1)
  zero_add x := by exact ext (LawfulCommRing.zero_add x.c0) (LawfulCommRing.zero_add x.c1)
  add_zero x := by exact ext (LawfulCommRing.add_zero x.c0) (LawfulCommRing.add_zero x.c1)
  add_left_neg x := by exact ext (LawfulCommRing.add_left_neg x.c0) (LawfulCommRing.add_left_neg x.c1)
  sub_eq_add_neg x y := by exact ext (LawfulCommRing.sub_eq_add_neg x.c0 y.c0) (LawfulCommRing.sub_eq_add_neg x.c1 y.c1)
  mul_comm x y := by
    apply ext
    · change CommRingOps.add (CommRingOps.mul x.c0 y.c0) (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1)) =
        CommRingOps.add (CommRingOps.mul y.c0 x.c0) (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 x.c1))
      rw [LawfulCommRing.mul_comm x.c0 y.c0, LawfulCommRing.mul_comm x.c1 y.c1]
    · change CommRingOps.add (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c1 y.c0) =
        CommRingOps.add (CommRingOps.mul y.c0 x.c1) (CommRingOps.mul y.c1 x.c0)
      rw [LawfulCommRing.mul_comm x.c0 y.c1, LawfulCommRing.mul_comm x.c1 y.c0, LawfulCommRing.add_comm]
  one_mul x := by
    apply ext
    · change CommRingOps.add (CommRingOps.mul CommRingOps.one x.c0)
        (CommRingOps.mul nonResidue (CommRingOps.mul CommRingOps.zero x.c1)) = x.c0
      rw [LawfulCommRing.one_mul, LawfulCommRing.zero_mul, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    · change CommRingOps.add (CommRingOps.mul CommRingOps.one x.c1) (CommRingOps.mul CommRingOps.zero x.c0) = x.c1
      rw [LawfulCommRing.one_mul, LawfulCommRing.zero_mul, LawfulCommRing.add_zero]
  mul_one x := by
    apply ext
    · change CommRingOps.add (CommRingOps.mul x.c0 CommRingOps.one)
        (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 CommRingOps.zero)) = x.c0
      rw [LawfulCommRing.mul_one, LawfulCommRing.mul_zero, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
    · change CommRingOps.add (CommRingOps.mul x.c0 CommRingOps.zero) (CommRingOps.mul x.c1 CommRingOps.one) = x.c1
      rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_one, LawfulCommRing.zero_add]
  left_distrib x y z := by
    apply ext
    · change CommRingOps.add (CommRingOps.mul x.c0 (CommRingOps.add y.c0 z.c0))
        (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 (CommRingOps.add y.c1 z.c1))) =
        CommRingOps.add
          (CommRingOps.add (CommRingOps.mul x.c0 y.c0) (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1)))
          (CommRingOps.add (CommRingOps.mul x.c0 z.c0) (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 z.c1)))
      rw [LawfulCommRing.left_distrib x.c0 y.c0 z.c0, LawfulCommRing.left_distrib x.c1 y.c1 z.c1,
          LawfulCommRing.left_distrib nonResidue (CommRingOps.mul x.c1 y.c1) (CommRingOps.mul x.c1 z.c1),
          LawfulCommRing.add_add_add_comm (CommRingOps.mul x.c0 y.c0) (CommRingOps.mul x.c0 z.c0)]
    · change CommRingOps.add (CommRingOps.mul x.c0 (CommRingOps.add y.c1 z.c1))
        (CommRingOps.mul x.c1 (CommRingOps.add y.c0 z.c0)) =
        CommRingOps.add
          (CommRingOps.add (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c1 y.c0))
          (CommRingOps.add (CommRingOps.mul x.c0 z.c1) (CommRingOps.mul x.c1 z.c0))
      rw [LawfulCommRing.left_distrib x.c0 y.c1 z.c1, LawfulCommRing.left_distrib x.c1 y.c0 z.c0,
          LawfulCommRing.add_add_add_comm (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c0 z.c1)]
  right_distrib x y z := by
    apply ext
    · change CommRingOps.add (CommRingOps.mul (CommRingOps.add x.c0 y.c0) z.c0)
        (CommRingOps.mul nonResidue (CommRingOps.mul (CommRingOps.add x.c1 y.c1) z.c1)) =
        CommRingOps.add
          (CommRingOps.add (CommRingOps.mul x.c0 z.c0) (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 z.c1)))
          (CommRingOps.add (CommRingOps.mul y.c0 z.c0) (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 z.c1)))
      rw [LawfulCommRing.right_distrib x.c0 y.c0 z.c0, LawfulCommRing.right_distrib x.c1 y.c1 z.c1,
          LawfulCommRing.left_distrib nonResidue (CommRingOps.mul x.c1 z.c1) (CommRingOps.mul y.c1 z.c1),
          LawfulCommRing.add_add_add_comm (CommRingOps.mul x.c0 z.c0) (CommRingOps.mul y.c0 z.c0)]
    · change CommRingOps.add (CommRingOps.mul (CommRingOps.add x.c0 y.c0) z.c1)
        (CommRingOps.mul (CommRingOps.add x.c1 y.c1) z.c0) =
        CommRingOps.add
          (CommRingOps.add (CommRingOps.mul x.c0 z.c1) (CommRingOps.mul x.c1 z.c0))
          (CommRingOps.add (CommRingOps.mul y.c0 z.c1) (CommRingOps.mul y.c1 z.c0))
      rw [LawfulCommRing.right_distrib x.c0 y.c0 z.c1, LawfulCommRing.right_distrib x.c1 y.c1 z.c0,
          LawfulCommRing.add_add_add_comm (CommRingOps.mul x.c0 z.c1) (CommRingOps.mul y.c0 z.c1)]
  mul_assoc x y z := by
    apply ext
    · change CommRingOps.add
          (CommRingOps.mul (CommRingOps.add (CommRingOps.mul x.c0 y.c0)
            (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1))) z.c0)
          (CommRingOps.mul nonResidue (CommRingOps.mul
            (CommRingOps.add (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c1 y.c0)) z.c1)) =
        CommRingOps.add
          (CommRingOps.mul x.c0 (CommRingOps.add (CommRingOps.mul y.c0 z.c0)
            (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 z.c1))))
          (CommRingOps.mul nonResidue (CommRingOps.mul x.c1
            (CommRingOps.add (CommRingOps.mul y.c0 z.c1) (CommRingOps.mul y.c1 z.c0))))
      rw [LawfulCommRing.right_distrib (CommRingOps.mul x.c0 y.c0)
            (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1)) z.c0,
          LawfulCommRing.right_distrib (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c1 y.c0) z.c1,
          LawfulCommRing.left_distrib nonResidue
            (CommRingOps.mul (CommRingOps.mul x.c0 y.c1) z.c1) (CommRingOps.mul (CommRingOps.mul x.c1 y.c0) z.c1),
          LawfulCommRing.left_distrib x.c0 (CommRingOps.mul y.c0 z.c0)
            (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 z.c1)),
          LawfulCommRing.left_distrib x.c1 (CommRingOps.mul y.c0 z.c1) (CommRingOps.mul y.c1 z.c0),
          LawfulCommRing.left_distrib nonResidue
            (CommRingOps.mul x.c1 (CommRingOps.mul y.c0 z.c1)) (CommRingOps.mul x.c1 (CommRingOps.mul y.c1 z.c0))]
      have t3 : CommRingOps.mul nonResidue (CommRingOps.mul (CommRingOps.mul x.c0 y.c1) z.c1) =
          CommRingOps.mul x.c0 (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 z.c1)) := by
        rw [LawfulCommRing.mul_assoc x.c0 y.c1 z.c1, ← LawfulCommRing.mul_assoc nonResidue x.c0 (CommRingOps.mul y.c1 z.c1),
            LawfulCommRing.mul_comm nonResidue x.c0, LawfulCommRing.mul_assoc x.c0 nonResidue (CommRingOps.mul y.c1 z.c1)]
      rw [LawfulCommRing.mul_assoc x.c0 y.c0 z.c0, LawfulCommRing.mul_assoc nonResidue (CommRingOps.mul x.c1 y.c1) z.c0,
          LawfulCommRing.mul_assoc x.c1 y.c1 z.c0, t3, LawfulCommRing.mul_assoc x.c1 y.c0 z.c1,
          LawfulCommRing.add_add_add_comm (CommRingOps.mul x.c0 (CommRingOps.mul y.c0 z.c0))
            (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 (CommRingOps.mul y.c1 z.c0))),
          LawfulCommRing.add_comm (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 (CommRingOps.mul y.c1 z.c0)))
            (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 (CommRingOps.mul y.c0 z.c1)))]
    · change CommRingOps.add
          (CommRingOps.mul (CommRingOps.add (CommRingOps.mul x.c0 y.c0)
            (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1))) z.c1)
          (CommRingOps.mul (CommRingOps.add (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c1 y.c0)) z.c0) =
        CommRingOps.add
          (CommRingOps.mul x.c0 (CommRingOps.add (CommRingOps.mul y.c0 z.c1) (CommRingOps.mul y.c1 z.c0)))
          (CommRingOps.mul x.c1 (CommRingOps.add (CommRingOps.mul y.c0 z.c0)
            (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 z.c1))))
      rw [LawfulCommRing.right_distrib (CommRingOps.mul x.c0 y.c0)
            (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1)) z.c1,
          LawfulCommRing.right_distrib (CommRingOps.mul x.c0 y.c1) (CommRingOps.mul x.c1 y.c0) z.c0,
          LawfulCommRing.left_distrib x.c0 (CommRingOps.mul y.c0 z.c1) (CommRingOps.mul y.c1 z.c0),
          LawfulCommRing.left_distrib x.c1 (CommRingOps.mul y.c0 z.c0)
            (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 z.c1))]
      have s2 : CommRingOps.mul (CommRingOps.mul nonResidue (CommRingOps.mul x.c1 y.c1)) z.c1 =
          CommRingOps.mul x.c1 (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 z.c1)) := by
        rw [LawfulCommRing.mul_assoc nonResidue (CommRingOps.mul x.c1 y.c1) z.c1,
            LawfulCommRing.mul_assoc x.c1 y.c1 z.c1,
            ← LawfulCommRing.mul_assoc nonResidue x.c1 (CommRingOps.mul y.c1 z.c1),
            LawfulCommRing.mul_comm nonResidue x.c1,
            LawfulCommRing.mul_assoc x.c1 nonResidue (CommRingOps.mul y.c1 z.c1)]
      rw [LawfulCommRing.mul_assoc x.c0 y.c0 z.c1, s2, LawfulCommRing.mul_assoc x.c0 y.c1 z.c0,
          LawfulCommRing.mul_assoc x.c1 y.c0 z.c0,
          LawfulCommRing.add_add_add_comm (CommRingOps.mul x.c0 (CommRingOps.mul y.c0 z.c1))
            (CommRingOps.mul x.c1 (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 z.c1))),
          LawfulCommRing.add_comm (CommRingOps.mul x.c1 (CommRingOps.mul nonResidue (CommRingOps.mul y.c1 z.c1)))
            (CommRingOps.mul x.c1 (CommRingOps.mul y.c0 z.c0))]

/-- Quadratic non-residue theorem in $\mathbb{F}_{p^2}$: $u = (0, 1)$ has no square root in `GoldilocksExt2`. -/
theorem uBasis_not_square (z : GoldilocksExt2) : CommRingOps.mul z z ≠ nonResidue := by
  intro hsq
  have hc0 : CommRingOps.add (CommRingOps.mul z.c0 z.c0)
      (CommRingOps.mul GoldilocksExt2.nonResidue (CommRingOps.mul z.c1 z.c1)) =
      CommRingOps.zero := congrArg GoldilocksExt2.c0 hsq
  have hc1 : CommRingOps.add (CommRingOps.mul z.c0 z.c1) (CommRingOps.mul z.c1 z.c0) =
      Goldilocks.one := congrArg GoldilocksExt2.c1 hsq
  have hbNe : z.c1 ≠ Goldilocks.zero := fun hb0 => by
    rw [hb0] at hc1
    change CommRingOps.add (CommRingOps.mul z.c0 CommRingOps.zero)
      (CommRingOps.mul CommRingOps.zero z.c0) = Goldilocks.one at hc1
    rw [LawfulCommRing.mul_zero, LawfulCommRing.zero_mul, LawfulCommRing.add_zero] at hc1
    exact absurd hc1 (by decide)
  have haSqEq : CommRingOps.mul z.c0 z.c0 =
      CommRingOps.neg (CommRingOps.mul GoldilocksExt2.nonResidue (CommRingOps.mul z.c1 z.c1)) := by
    apply LawfulCommRing.add_left_cancel
      (a := CommRingOps.mul GoldilocksExt2.nonResidue (CommRingOps.mul z.c1 z.c1))
    rw [LawfulCommRing.add_comm _ (CommRingOps.mul z.c0 z.c0), hc0, LawfulCommRing.add_right_neg]
  let q := CommRingOps.mul z.c0 (Goldilocks.inv z.c1)
  have hqSq : CommRingOps.mul q q = CommRingOps.neg GoldilocksExt2.nonResidue := by
    dsimp only [q]
    have hcancel : CommRingOps.mul (CommRingOps.mul z.c1 z.c1)
        (CommRingOps.mul (Goldilocks.inv z.c1) (Goldilocks.inv z.c1)) = CommRingOps.one := by
      rw [← sq_mul_sq_eq, Goldilocks.mul_inv_cancel hbNe, LawfulCommRing.mul_one]
    rw [sq_mul_sq_eq, haSqEq, LawfulCommRing.neg_mul,
        LawfulCommRing.mul_assoc GoldilocksExt2.nonResidue, hcancel, LawfulCommRing.mul_one]
  exact neg_seven_not_square_in_goldilocks q hqSq

/-- Relative norm $N_{\mathbb{F}_{p^4}/\mathbb{F}_{p^2}}(A + B v) = A^2 - u B^2 \in \mathbb{F}_{p^2}$. -/
def norm (z : GoldilocksExt4) : GoldilocksExt2 :=
  CommRingOps.sub (CommRingOps.mul z.c0 z.c0) (CommRingOps.mul nonResidue (CommRingOps.mul z.c1 z.c1))

theorem norm_ne_zero {z : GoldilocksExt4} (hz : z ≠ zero) : norm z ≠ GoldilocksExt2.zero := by
  intro hnorm
  have hEq : CommRingOps.mul z.c0 z.c0 = CommRingOps.mul nonResidue (CommRingOps.mul z.c1 z.c1) :=
    LawfulCommRing.sub_eq_zero_iff.mp hnorm
  if hc1 : z.c1 = GoldilocksExt2.zero then
    have hrhs : CommRingOps.mul nonResidue (CommRingOps.mul z.c1 z.c1) = GoldilocksExt2.zero := by
      rw [hc1]
      change CommRingOps.mul nonResidue (CommRingOps.mul CommRingOps.zero CommRingOps.zero) = CommRingOps.zero
      rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_zero]
    rw [hrhs] at hEq
    rcases NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero hEq with hc0 | hc0 <;> exact hz (ext hc0 hc1)
  else
    let q := CommRingOps.mul z.c0 (GoldilocksExt2.inv z.c1)
    have hqSq : CommRingOps.mul q q = nonResidue := by
      dsimp only [q]
      have hcancel : CommRingOps.mul (CommRingOps.mul z.c1 z.c1)
          (CommRingOps.mul (GoldilocksExt2.inv z.c1) (GoldilocksExt2.inv z.c1)) = CommRingOps.one := by
        rw [← sq_mul_sq_eq, GoldilocksExt2.mul_inv_cancel hc1, LawfulCommRing.mul_one]
      rw [sq_mul_sq_eq, hEq, LawfulCommRing.mul_assoc nonResidue, hcancel, LawfulCommRing.mul_one]
    exact uBasis_not_square q hqSq

/-- Constructive closed-form quartic field inverse $(A - B v)(A^2 - u B^2)^{-1}$ (`inv 0 = 0`). -/
@[expose] def inv (z : GoldilocksExt4) : GoldilocksExt4 :=
  let invN := GoldilocksExt2.inv (norm z)
  ⟨CommRingOps.mul z.c0 invN, CommRingOps.neg (CommRingOps.mul z.c1 invN)⟩

instance : Mul GoldilocksExt4 := ⟨mul⟩
instance : Inv GoldilocksExt4 := ⟨inv⟩

/-- **Universal Two-Sided `GoldilocksExt4` Division (`ext4_mul_inv_cancel`)**:
    Every nonzero `z : GoldilocksExt4` satisfies `z * z⁻¹ = 1` and `z⁻¹ * z = 1`. -/
theorem ext4_mul_inv_cancel {z : GoldilocksExt4} (hz : z ≠ zero) :
    z * z⁻¹ = one ∧ z⁻¹ * z = one := by
  have hnormNe := norm_ne_zero hz
  let invN := GoldilocksExt2.inv (norm z)
  have hRight : mul z (inv z) = one := by
    apply ext
    · change CommRingOps.add (CommRingOps.mul z.c0 (CommRingOps.mul z.c0 invN))
          (CommRingOps.mul nonResidue (CommRingOps.mul z.c1 (CommRingOps.neg (CommRingOps.mul z.c1 invN)))) =
        CommRingOps.one
      rw [← LawfulCommRing.mul_assoc z.c0 z.c0 invN, LawfulCommRing.mul_neg z.c1, LawfulCommRing.mul_neg nonResidue,
          ← LawfulCommRing.mul_assoc z.c1 z.c1 invN, ← LawfulCommRing.mul_assoc nonResidue _ invN,
          ← LawfulCommRing.sub_eq_add_neg, ← LawfulCommRing.sub_mul]
      exact GoldilocksExt2.mul_inv_cancel hnormNe
    · change CommRingOps.add (CommRingOps.mul z.c0 (CommRingOps.neg (CommRingOps.mul z.c1 invN)))
          (CommRingOps.mul z.c1 (CommRingOps.mul z.c0 invN)) = CommRingOps.zero
      rw [LawfulCommRing.mul_neg, ← LawfulCommRing.mul_assoc z.c0 z.c1 invN,
          ← LawfulCommRing.mul_assoc z.c1 z.c0 invN, LawfulCommRing.mul_comm z.c1 z.c0,
          LawfulCommRing.add_left_neg]
  exact ⟨hRight, (LawfulCommRing.mul_comm (inv z) z).trans hRight⟩

instance : NoZeroDivisors GoldilocksExt4 where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    if ha : a = zero then exact .inl ha
    else
      right
      have hmul := congrArg (CommRingOps.mul (inv a)) h
      rw [LawfulCommRing.mul_zero, ← LawfulCommRing.mul_assoc,
          show CommRingOps.mul (inv a) a = CommRingOps.one from (ext4_mul_inv_cancel ha).2,
          LawfulCommRing.one_mul] at hmul
      exact hmul

/-- **Absence of Non-Trivial Zero Divisors in `GoldilocksExt4` (`ext4_mul_eq_zero_iff`)**. -/
theorem ext4_mul_eq_zero_iff (z w : GoldilocksExt4) : z * w = zero ↔ z = zero ∨ w = zero := by
  constructor
  · exact NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero
  · rintro (rfl | rfl)
    · exact LawfulCommRing.zero_mul w
    · exact LawfulCommRing.mul_zero z

/-- Defining polynomial relation $v^4 = 7$ inside `GoldilocksExt4`. -/
theorem vBasis_pow4_eq_seven :
    (vBasis * vBasis) * (vBasis * vBasis) = embedBase GoldilocksExt2.nonResidue := by
  have hSq : vBasis * vBasis = ofExt2 GoldilocksExt2.uBasis := by
    apply ext <;> apply GoldilocksExt2.ext <;> apply Goldilocks.ext <;>
      (dsimp only [HMul.hMul, Mul.mul, mul, vBasis, ofExt2, nonResidue, GoldilocksExt2.uBasis,
        CommRingOps.add, CommRingOps.mul, CommRingOps.zero, CommRingOps.one,
        GoldilocksExt2.add, GoldilocksExt2.mul, GoldilocksExt2.zero, GoldilocksExt2.one]
       simp only [Goldilocks.add_val, Goldilocks.mul_val, Goldilocks.zero, Goldilocks.one,
         GoldilocksExt2.nonResidue]; decide)
  rw [hSq]
  apply ext <;> apply GoldilocksExt2.ext <;> apply Goldilocks.ext <;>
    (dsimp only [HMul.hMul, Mul.mul, mul, ofExt2, embedBase, nonResidue, GoldilocksExt2.uBasis,
      GoldilocksExt2.ofBase, CommRingOps.add, CommRingOps.mul, CommRingOps.zero, CommRingOps.one,
      GoldilocksExt2.add, GoldilocksExt2.mul, GoldilocksExt2.zero, GoldilocksExt2.one]
     simp only [Goldilocks.add_val, Goldilocks.mul_val, Goldilocks.zero, Goldilocks.one,
       GoldilocksExt2.nonResidue]; decide)

/-- Direct polynomial-basis carrier $a_0 + a_1 v + a_2 v^2 + a_3 v^3 \in \mathbb{F}_p[v]/(v^4 - 7)$. -/
structure Ext4Poly where
  a0 : Goldilocks
  a1 : Goldilocks
  a2 : Goldilocks
  a3 : Goldilocks
  deriving DecidableEq, Repr

/-- Multiplication directly in polynomial basis $[1, v, v^2, v^3]$ modulo $v^4 - 7$. -/
@[expose] def Ext4Poly.mul (x y : Ext4Poly) : Ext4Poly :=
  let s := GoldilocksExt2.nonResidue
  { a0 := CommRingOps.add (CommRingOps.mul x.a0 y.a0)
            (CommRingOps.mul s (CommRingOps.add (CommRingOps.add (CommRingOps.mul x.a1 y.a3)
              (CommRingOps.mul x.a2 y.a2)) (CommRingOps.mul x.a3 y.a1)))
    a1 := CommRingOps.add (CommRingOps.add (CommRingOps.mul x.a0 y.a1) (CommRingOps.mul x.a1 y.a0))
            (CommRingOps.mul s (CommRingOps.add (CommRingOps.mul x.a2 y.a3) (CommRingOps.mul x.a3 y.a2)))
    a2 := CommRingOps.add (CommRingOps.add (CommRingOps.add (CommRingOps.mul x.a0 y.a2)
            (CommRingOps.mul x.a1 y.a1)) (CommRingOps.mul x.a2 y.a0))
            (CommRingOps.mul s (CommRingOps.mul x.a3 y.a3))
    a3 := CommRingOps.add (CommRingOps.add (CommRingOps.mul x.a0 y.a3) (CommRingOps.mul x.a1 y.a2))
            (CommRingOps.add (CommRingOps.mul x.a2 y.a1) (CommRingOps.mul x.a3 y.a0)) }

/-- `[0, 2, 1, 3]` basis bijection mapping `(A0 + A1 u) + (B0 + B1 u) v` to `A0 + B0 v + A1 v^2 + B1 v^3`. -/
@[expose] def towerToPoly (z : GoldilocksExt4) : Ext4Poly := ⟨z.c0.c0, z.c1.c0, z.c0.c1, z.c1.c1⟩
def polyToTower (p : Ext4Poly) : GoldilocksExt4 := ⟨⟨p.a0, p.a2⟩, ⟨p.a1, p.a3⟩⟩

theorem polyToTower_towerToPoly (z : GoldilocksExt4) : polyToTower (towerToPoly z) = z := by
  cases z with | mk c0 c1 => cases c0; cases c1; rfl
theorem towerToPoly_polyToTower (p : Ext4Poly) : towerToPoly (polyToTower p) = p := by
  cases p; rfl

/-- Ring-multiplication homomorphism between quadratic tower `GoldilocksExt4` and $\mathbb{F}_p[v]/(v^4 - 7)$. -/
theorem towerToPoly_mul_hom (x y : GoldilocksExt4) :
    towerToPoly (x * y) = Ext4Poly.mul (towerToPoly x) (towerToPoly y) := by
  unfold towerToPoly Ext4Poly.mul
  change Ext4Poly.mk ((mul x y).c0.c0) ((mul x y).c1.c0) ((mul x y).c0.c1) ((mul x y).c1.c1) = _
  unfold mul nonResidue GoldilocksExt2.uBasis
  dsimp only [CommRingOps.add, CommRingOps.mul, CommRingOps.zero, CommRingOps.one,
    GoldilocksExt2.add, GoldilocksExt2.mul, GoldilocksExt2.zero, GoldilocksExt2.one,
    Goldilocks.zero, Goldilocks.one]
  congr 1
  · apply Goldilocks.ext
    simp only [Goldilocks.add_val, Goldilocks.mul_val, GoldilocksExt2.nonResidue,
      Nat.zero_mul, Nat.zero_add, Nat.one_mul, Nat.mod_mod,
      Nat.mul_mod_mod, Nat.add_mod_mod, Nat.mod_add_mod, Nat.left_distrib]
    congr 1; omega
  · apply Goldilocks.ext
    simp only [Goldilocks.add_val, Goldilocks.mul_val, GoldilocksExt2.nonResidue,
      Nat.mul_mod_mod, Nat.add_mod_mod, Nat.mod_add_mod, Nat.left_distrib]
    congr 1; omega
  · apply Goldilocks.ext
    simp only [Goldilocks.add_val, Goldilocks.mul_val, GoldilocksExt2.nonResidue,
      Nat.zero_mul, Nat.one_mul, Nat.mod_mod,
      Nat.mul_mod_mod, Nat.add_mod_mod, Nat.mod_add_mod]
    congr 1; omega
  · apply Goldilocks.ext
    simp only [Goldilocks.add_val, Goldilocks.mul_val, Nat.add_mod_mod, Nat.mod_add_mod]
    congr 1; omega

/-- **`#tooth` Zero-Element Inversion Boundary (`tooth_ext4_zero_has_no_inverse`)**. -/
theorem tooth_ext4_zero_has_no_inverse : zero * zero⁻¹ ≠ one := by
  intro hEq
  have hZero : zero * zero⁻¹ = zero := LawfulCommRing.zero_mul (zero⁻¹)
  rw [hZero] at hEq; exact absurd hEq (by decide)

end GoldilocksExt4
end GoldilocksField

/-! ## 4. Inhabitedness Witnesses & `#tooth_pair` / `#verify_constructive` Assurance Gates -/

theorem witness_lucas_bls_goldilocks :
    ∃ (N g : Nat) (facs : List (Nat × Nat)),
      N - 1 < 2 ^ 64 ∧ (∀ qe ∈ facs, IsPrimeNat qe.1) ∧ checkLucasBlsCert N g facs = true :=
  ⟨Goldilocks.p, 7, goldilocksTotientFactors, by decide,
   goldilocksTotientFactors_all_prime, goldilocks_lucas_cert_valid⟩

theorem witness_goldilocks_nonzero_element :
    ∃ x : Goldilocks, x ≠ Goldilocks.zero ∧ Goldilocks.inv x ≠ Goldilocks.zero :=
  ⟨⟨7, by decide⟩, by decide, by decide⟩

theorem witness_goldilocks_bezout_nonzero :
    ∃ x : Goldilocks, x ≠ Goldilocks.zero ∧ Goldilocks.invBezout x ≠ Goldilocks.zero :=
  ⟨⟨7, by decide⟩, by decide, by rw [goldilocks_invBezout_eq_inv]; decide⟩

theorem witness_ext4_nontrivial_element :
    ∃ z : GoldilocksField.GoldilocksExt4, z ≠ GoldilocksField.GoldilocksExt4.zero ∧
      z⁻¹ ≠ GoldilocksField.GoldilocksExt4.zero :=
  ⟨⟨⟨⟨3, by decide⟩, ⟨0, by decide⟩⟩, ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩⟩, by decide, by decide⟩

theorem tooth_goldilocks_zero_has_no_inverse :
    CommRingOps.mul Goldilocks.zero (Goldilocks.inv Goldilocks.zero) ≠ CommRingOps.one := by
  rw [show CommRingOps.mul Goldilocks.zero (Goldilocks.inv Goldilocks.zero) = Goldilocks.zero from
        LawfulCommRing.zero_mul _]
  decide

theorem tooth_monic_quad_factor_zero_at_origin :
    ¬ IsMonicQuadFactorOfV4Sub7 Goldilocks.zero Goldilocks.zero Goldilocks.zero Goldilocks.zero :=
  v_pow4_sub_seven_irreducible.2 _ _ _ _

#verify_constructive Qsag.goldilocksPrime_is_prime Qsag.goldilocks_lucas_fermat_witnesses
  Qsag.goldilocks_seven_primitive_root Qsag.goldilocks_universal_mul_inv_cancel
  Qsag.goldilocks_invBezout_eq_inv Qsag.v_pow4_sub_seven_irreducible
  Qsag.GoldilocksField.GoldilocksExt4.ext4_mul_inv_cancel
  Qsag.GoldilocksField.GoldilocksExt4.towerToPoly_mul_hom

#verify_inhabited Qsag.checkLucasBlsCert_sound Qsag.witness_lucas_bls_goldilocks
#verify_inhabited Qsag.goldilocks_universal_mul_inv_cancel Qsag.witness_goldilocks_nonzero_element
#verify_inhabited Qsag.goldilocks_mul_invBezout_cancel Qsag.witness_goldilocks_bezout_nonzero
#verify_inhabited Qsag.GoldilocksField.GoldilocksExt4.ext4_mul_inv_cancel Qsag.witness_ext4_nontrivial_element

#tooth_pair Qsag.checkLucasBlsCert_sound vs Qsag.tooth_proth16_65281_not_prime
#tooth_pair Qsag.checkLucasBlsCert_sound vs Qsag.tooth_carmichael_561_rejected
#tooth_pair Qsag.goldilocks_universal_mul_inv_cancel vs Qsag.tooth_goldilocks_zero_has_no_inverse
#tooth_pair Qsag.goldilocks_quadExtMulMod_no_zero_divisors vs Qsag.tooth_mod29_seven_residue_zero_divisor
#tooth_pair Qsag.v_pow4_sub_seven_irreducible vs Qsag.tooth_monic_quad_factor_zero_at_origin
#tooth_pair Qsag.GoldilocksField.GoldilocksExt4.ext4_mul_inv_cancel vs Qsag.GoldilocksField.GoldilocksExt4.tooth_ext4_zero_has_no_inverse

end Qsag
end
