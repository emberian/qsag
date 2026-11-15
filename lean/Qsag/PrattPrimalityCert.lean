module
/-
# Qsag.PrattPrimalityCert — Kernel-Checked Pocklington–Pratt Primality Certificates

Constructive (`0 sorry`, `0 axiom`, `0 Classical.choice`, `0 native_decide`) primality
certificate verifier over `Nat` using fueled binary modular exponentiation (`powModFuel`)
and fueled Euclidean GCD (`gcdFuel`).

Given a topological chain of `PocklingtonStep` witnesses starting from base prime `2`:
1. Each step `(n, g, factors)` checks `3 ≤ n < 2 ^ 256`, Fermat witness
   `g ^ (n - 1) ≡ 1 (mod n)`, pairwise distinct previously certified prime divisors `q_i`
   with `(n - 1) % (q_i ^ e_i) = 0`, `r_i = g ^ ((n - 1) / q_i) mod n > 1`,
   `gcd(r_i - 1, n) = 1`, and partial factored part `F = ∏ q_i ^ e_i` satisfying `F * F > n`.
2. Soundness (`verifyPrimeCert_sound`) proves `Weierstrass.IsPrime n` for every certified
   integer in the chain via Fermat's Little Theorem (`Weierstrass.IsPrime.pow_sub_one_mod`)
   and Pocklington's prime-divisor lower bound `F < p`.
3. Instantiates kernel-checked certificates for both the `secp256k1` base-field prime
   `SECP256K1_FIELD_P = 2^256 - 2^32 - 977` and scalar subgroup order `SECP256K1_ORDER_N`.
-/

public import Qsag.Goldilocks
public import Qsag.ActiveMigrationZeroTest
import all Qsag.ActiveMigrationZeroTest
public import Qsag.Tactic.AssuranceKit

public section

namespace Qsag

set_option autoImplicit false

namespace Weierstrass

/- `Weierstrass.IsPrime` and Euclid's lemma `IsPrime.dvd_mul` are the declarations of
   `ActiveMigrationZeroTest.lean`; this module certifies primes for that same predicate. -/

private theorem dvd_mul_not_left {q a b : Nat} (hq : IsPrime q)
    (hdvd : q ∣ a * b) (hna : ¬ (q ∣ a)) : q ∣ b := by
  obtain ⟨hda, hdq⟩ := extGcd_dvd a q
  have hg1 : (extGcd a q).1 = 1 := by
    rcases hq.2 _ hdq with h1 | hqq
    · exact h1
    · rw [hqq] at hda
      exact False.elim (hna hda)
  have hbez := extGcd_bezout a q
  rw [hg1] at hbez
  obtain ⟨k, hk⟩ := hdvd
  have hmul : ((a : Int) * (extGcd a q).2.1 + (q : Int) * (extGcd a q).2.2) * (b : Int) =
      1 * (b : Int) := congrArg (· * (b : Int)) hbez
  rw [Int.add_mul, Int.one_mul] at hmul
  have hab : (a : Int) * (extGcd a q).2.1 * (b : Int) =
      (q : Int) * ((k : Int) * (extGcd a q).2.1) := by
    have hkInt : (a : Int) * (b : Int) = (q : Int) * (k : Int) := by exact_mod_cast hk
    rw [Int.mul_right_comm (a : Int), hkInt, Int.mul_assoc]
  rw [hab, Int.mul_assoc (q : Int), ← Int.mul_add] at hmul
  exact Int.ofNat_dvd.1 ⟨(k : Int) * (extGcd a q).2.1 + (extGcd a q).2.2 * (b : Int), hmul.symm⟩

/-! ### Constructive Proof of Fermat's Little Theorem for `Weierstrass.IsPrime` -/

private def posRange : Nat → List Nat
  | 0 => []
  | n + 1 => (n + 1) :: posRange n

private theorem mem_posRange_iff (x : Nat) : ∀ (n : Nat), x ∈ posRange n ↔ 1 ≤ x ∧ x ≤ n
  | 0 => Iff.intro (fun h => by cases h) (fun ⟨_, _⟩ => by omega)
  | n + 1 => by
    simp only [posRange, List.mem_cons, mem_posRange_iff x n]
    refine ⟨?_, fun ⟨hLo, hHi⟩ => if hEq : x = n + 1 then .inl hEq else .inr ⟨hLo, by omega⟩⟩
    rintro (rfl | ⟨hLo, hHi⟩)
    · exact ⟨Nat.succ_pos n, Nat.le_refl _⟩
    · exact ⟨hLo, Nat.le_trans hHi (Nat.le_succ n)⟩

private theorem posRange_nodup : ∀ (n : Nat), (posRange n).Nodup
  | 0 => .nil
  | n + 1 => .cons (fun b hb heq => by have := ((mem_posRange_iff b n).1 hb).2; omega) (posRange_nodup n)

private def listProd : List Nat → Nat
  | [] => 1
  | x :: xs => x * listProd xs

private def eraseFirst (v : Nat) : List Nat → List Nat
  | [] => []
  | y :: ys => if y = v then ys else y :: eraseFirst v ys

private theorem mem_of_mem_eraseFirst {v z : Nat} :
    ∀ {ys : List Nat}, z ∈ eraseFirst v ys → z ∈ ys
  | [], h => by cases h
  | y :: ys, h => by
    simp only [eraseFirst] at h
    split at h
    · exact .tail _ h
    · cases h with
      | head => exact .head _
      | tail _ ht => exact .tail _ (mem_of_mem_eraseFirst ht)

private theorem eraseFirst_spec {v : Nat} :
    ∀ {ys : List Nat}, ys.Nodup → v ∈ ys →
      listProd ys = v * listProd (eraseFirst v ys) ∧ (eraseFirst v ys).length + 1 = ys.length ∧
      (eraseFirst v ys).Nodup ∧ (∀ z : Nat, z ≠ v → z ∈ ys → z ∈ eraseFirst v ys)
  | [], _, hmem => by cases hmem
  | y :: ys, .cons hrel hnd, hmem => by
    dsimp only [eraseFirst]
    if hy : y = v then
      subst hy; simp only [↓reduceIte, listProd, List.length_cons]
      refine ⟨trivial, trivial, hnd, fun z hzne hzmem => ?_⟩
      cases hzmem with | head => exact False.elim (hzne rfl) | tail _ htail => exact htail
    else
      simp only [hy, ↓reduceIte, listProd, List.length_cons]
      have hvTail : v ∈ ys := by
        cases hmem with | head => exact False.elim (hy rfl) | tail _ ht => exact ht
      obtain ⟨hprod, hlen, hnd', hsub⟩ := eraseFirst_spec hnd hvTail
      refine ⟨by rw [hprod, ← Nat.mul_assoc, Nat.mul_comm y v, Nat.mul_assoc], by omega,
        .cons (fun b hb heq => hrel b (mem_of_mem_eraseFirst hb) heq) hnd', fun z hzne hzmem => ?_⟩
      cases hzmem with | head => exact .head _ | tail _ ht => exact .tail _ (hsub z hzne ht)

private theorem listProd_eq_of_nodup_subset :
    ∀ {xs ys : List Nat},
      xs.Nodup → ys.Nodup → xs.length = ys.length →
      (∀ x ∈ xs, x ∈ ys) → listProd xs = listProd ys
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, hlen, _ => by cases hlen
  | x :: xs, ys, .cons hrel hndX, hndY, hlen, hsub => by
    obtain ⟨hprodY, hlenE, hndE, hmemE⟩ := eraseFirst_spec hndY (hsub x (.head _))
    simp only [List.length_cons] at hlen
    have ih := listProd_eq_of_nodup_subset hndX hndE (by omega) (fun z hz =>
      hmemE z (fun heq => hrel z hz heq.symm) (hsub z (.tail _ hz)))
    simp only [listProd, ih, hprodY]

private theorem listProd_map_mul_mod (a q : Nat) :
    ∀ (n : Nat),
      listProd ((posRange n).map (fun i => (a * i) % q)) % q =
      (a ^ n * listProd (posRange n)) % q
  | 0 => by simp [posRange, listProd]
  | n + 1 => by
    simp only [posRange, List.map_cons, listProd]
    rw [Nat.mul_mod ((a * (n + 1)) % q), Nat.mod_mod, listProd_map_mul_mod a q n, ← Nat.mul_mod]
    have hcomm : a * (n + 1) * (a ^ n * listProd (posRange n)) =
        a ^ (n + 1) * ((n + 1) * listProd (posRange n)) := by
      rw [Nat.pow_succ, Nat.mul_comm (a ^ n) a]
      rw [Nat.mul_assoc a (n + 1) (a ^ n * listProd (posRange n)),
          ← Nat.mul_assoc (n + 1) (a ^ n) (listProd (posRange n)),
          Nat.mul_comm (n + 1) (a ^ n),
          Nat.mul_assoc (a ^ n) (n + 1) (listProd (posRange n)),
          ← Nat.mul_assoc a (a ^ n) _]
    rw [hcomm]

private theorem not_dvd_listProd_posRange {q : Nat} (hq : IsPrime q) :
    ∀ {n : Nat}, n < q → ¬ (q ∣ listProd (posRange n))
  | 0, _, hdvd => by dsimp only [posRange, listProd] at hdvd; have := Nat.le_of_dvd (by decide) hdvd; have := hq.1; omega
  | n + 1, hlt, hdvd => by
    simp only [posRange, listProd] at hdvd
    exact not_dvd_listProd_posRange hq (by omega)
      (dvd_mul_not_left hq hdvd (fun h1 => by have := Nat.le_of_dvd (by omega) h1; omega))

private theorem sub_dvd_of_mod_eq {x y q : Nat} (hle : y ≤ x) (hmod : x % q = y % q) :
    q ∣ (x - y) := by
  have hx := Nat.div_add_mod x q; have hy := Nat.div_add_mod y q
  have hdivLe := Nat.div_le_div_right (c := q) hle
  refine ⟨x / q - y / q, ?_⟩; rw [Nat.mul_sub]; omega

private theorem one_le_pow_of_pos {a : Nat} (ha : 1 ≤ a) : ∀ k : Nat, 1 ≤ a ^ k
  | 0 => Nat.le_refl 1
  | k + 1 => Nat.pow_succ a k ▸ Nat.le_trans (one_le_pow_of_pos ha k) (Nat.le_mul_of_pos_right _ ha)

/-- Fermat's Little Theorem: `a ^ (q - 1) ≡ 1 (mod q)` for prime `q` and `¬ (q ∣ a)`. -/
theorem IsPrime.pow_sub_one_mod {q a : Nat} (hq : IsPrime q) (hna : ¬ (q ∣ a)) :
    (a ^ (q - 1)) % q = 1 := by
  let L := posRange (q - 1)
  let f := fun i : Nat => (a * i) % q
  have hMem : ∀ x ∈ L.map f, x ∈ L := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hi1, hi2⟩ := (mem_posRange_iff i (q - 1)).1 hi
    have hni : ¬ (q ∣ i) := fun hd => by have := Nat.le_of_dvd (by omega) hd; have := hq.1; omega
    have hnai : ¬ (q ∣ a * i) := fun hd => hni (dvd_mul_not_left hq (Nat.mul_comm a i ▸ hd) hna)
    have hmodPos : 0 < (a * i) % q :=
      if hz : (a * i) % q = 0 then False.elim (hnai (Nat.dvd_of_mod_eq_zero hz)) else by omega
    have hmodLt : (a * i) % q < q := Nat.mod_lt _ (by have := hq.1; omega)
    dsimp only [f]; exact (mem_posRange_iff _ (q - 1)).2 ⟨hmodPos, by omega⟩
  have hInjLe : ∀ u v : Nat, u ≤ v → v ≤ q - 1 → (a * u) % q = (a * v) % q → u = v := by
    intro u v huv hv hij
    have hdvd : q ∣ a * (v - u) :=
      (Nat.mul_sub a v u) ▸ sub_dvd_of_mod_eq (Nat.mul_le_mul_left a huv) hij.symm
    have hdvdDiff : q ∣ (v - u) := dvd_mul_not_left hq hdvd hna
    have hq2 := hq.1
    if hdiff0 : v - u = 0 then omega else have := Nat.le_of_dvd (by omega) hdvdDiff; omega
  have hInjOn : ∀ i j : Nat, i ∈ L → j ∈ L → f i = f j → i = j := by
    intro i j hi hj hij; dsimp only [f] at hij
    obtain ⟨_, hi2⟩ := (mem_posRange_iff i (q - 1)).1 hi
    obtain ⟨_, hj2⟩ := (mem_posRange_iff j (q - 1)).1 hj
    exact if hijLe : i ≤ j then hInjLe i j hijLe hj2 hij else (hInjLe j i (by omega) hi2 hij.symm).symm
  have hNodupMap : (L.map f).Nodup := by
    have hsubNd : ∀ {xs : List Nat}, xs.Nodup → (∀ z ∈ xs, z ∈ L) → (xs.map f).Nodup := by
      intro xs hnd hxs; induction hnd with
      | nil => exact .nil
      | @cons x rest hrel _ ih =>
        refine .cons (fun b hb heq => ?_) (ih (fun z hz => hxs z (.tail _ hz)))
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
        exact hrel y hy (hInjOn x y (hxs x (.head _)) (hxs y (.tail _ hy)) heq)
    exact hsubNd (posRange_nodup (q - 1)) (fun z hz => hz)
  have hProdEq : listProd (L.map f) = listProd L :=
    listProd_eq_of_nodup_subset hNodupMap (posRange_nodup (q - 1)) (by simp) hMem
  have hModEq : (a ^ (q - 1) * listProd L) % q = (listProd L) % q := by
    rw [← listProd_map_mul_mod a q (q - 1), hProdEq]
  have haPos : 1 ≤ a := if ha0 : a = 0 then by subst ha0; exact False.elim (hna (Nat.dvd_zero q)) else by omega
  have hpowPos : 1 ≤ a ^ (q - 1) := one_le_pow_of_pos haPos (q - 1)
  have hdvdMul : q ∣ (a ^ (q - 1) - 1) * listProd L := by
    have hsub : a ^ (q - 1) * listProd L - listProd L = (a ^ (q - 1) - 1) * listProd L := by
      rw [Nat.sub_mul, Nat.one_mul]
    exact hsub ▸ sub_dvd_of_mod_eq (Nat.le_mul_of_pos_left _ hpowPos) hModEq
  have hnotF : ¬ (q ∣ listProd L) := not_dvd_listProd_posRange hq (by have := hq.1; omega)
  obtain ⟨k, hk⟩ := dvd_mul_not_left hq (Nat.mul_comm (a ^ (q - 1) - 1) (listProd L) ▸ hdvdMul) hnotF
  have hEq : a ^ (q - 1) = q * k + 1 := by omega
  rw [hEq, Nat.mul_add_mod, Nat.mod_eq_of_lt hq.1]

end Weierstrass

/-! ## Kernel-Reducible Fueled Modular Power & Euclidean GCD -/

@[expose] def strictEval (n : Nat) (k : Nat → Nat) : Nat :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)

private theorem strictEval_eq (n : Nat) (k : Nat → Nat) : strictEval n k = k n := by
  cases n <;> rfl

/-- Fueled binary modular exponentiation (`O(fuel)` squarings in `decide +kernel`). -/
@[expose] def powModFuel : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, m => 1 % m
  | fuel + 1, base, exp, m =>
    if exp = 0 then 1 % m
    else
      strictEval (powModFuel fuel base (exp / 2) m) fun half =>
        strictEval ((half * half) % m) fun sq =>
          if exp % 2 = 1 then (sq * (base % m)) % m else sq

private theorem pow_two_mul_cert (b k : Nat) : b ^ (2 * k) = (b ^ k) * (b ^ k) := by
  rw [Nat.mul_comm 2 k, Nat.pow_mul, Nat.pow_succ, Nat.pow_one]

theorem powModFuel_eq_pow_mod :
    ∀ (fuel base exp m : Nat), exp < 2 ^ fuel → powModFuel fuel base exp m = (base ^ exp) % m
  | 0, _, exp, m, hlt => by
    have he0 : exp = 0 := by simp at hlt; omega
    subst he0; simp [powModFuel]
  | fuel + 1, base, exp, m, hlt => by
    simp only [powModFuel]
    if h0 : exp = 0 then
      subst h0; simp
    else
      simp only [h0, ↓reduceIte, strictEval_eq]
      have hexpHalf : exp / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at hlt; omega
      have ih := powModFuel_eq_pow_mod fuel base (exp / 2) m hexpHalf
      have hsq : ((powModFuel fuel base (exp / 2) m) * (powModFuel fuel base (exp / 2) m)) % m =
          (base ^ (2 * (exp / 2))) % m := by
        rw [ih, ← Nat.mul_mod, ← pow_two_mul_cert]
      have hmod2 : exp % 2 = 0 ∨ exp % 2 = 1 := by omega
      rcases hmod2 with hr0 | hr1
      · simp only [hr0, show ¬ (0 = 1) by decide, ↓reduceIte]
        rw [hsq, show 2 * (exp / 2) = exp by omega]
      · simp only [hr1, ↓reduceIte]
        have hexp : exp = 2 * (exp / 2) + 1 := by omega
        conv => rhs; rw [hexp, Nat.pow_add, Nat.pow_one, Nat.mul_mod]
        rw [hsq]

/-- Fueled Euclidean GCD avoiding `WellFounded.fix` inside kernel reduction (`decide +kernel`). -/
@[expose] def gcdFuel : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, a, b => if b = 0 then a else gcdFuel fuel b (a % b)

theorem dvd_gcdFuel : ∀ (fuel a b d : Nat), d ∣ a → d ∣ b → d ∣ gcdFuel fuel a b
  | 0, _, _, d, _, _ => Nat.dvd_zero d
  | fuel + 1, a, b, d, hda, hdb => by
    unfold gcdFuel
    if hb : b = 0 then
      simp only [hb, ↓reduceIte]
      exact hda
    else
      simp only [hb, ↓reduceIte]
      exact dvd_gcdFuel fuel b (a % b) d hdb ((Nat.dvd_mod_iff hdb).2 hda)

/-- Single Pocklington–Lucas primality certificate node for `n` using witness base `g`
    and prime-power factors `(q, e)` of `n - 1` drawn from already certified primes. -/
structure PocklingtonStep where
  n : Nat
  g : Nat
  factors : List (Nat × Nat)
  deriving Repr, DecidableEq

/-- Product `∏ q_i ^ e_i` of the certified prime-power factors of `n - 1`. -/
@[expose] def factorsProd : List (Nat × Nat) → Nat
  | [] => 1
  | (q, e) :: rest => (q ^ e) * factorsProd rest

/-- Boolean check that all first projections `q` in `factors` are pairwise distinct. -/
@[expose] def allDistinctPrimes : List (Nat × Nat) → Bool
  | [] => true
  | (q, _) :: rest => rest.all (fun p => q != p.1) && allDistinctPrimes rest

/-- Check one prime-power factor `(q, e)` of `n - 1` under Pocklington witness `g`. -/
@[expose] def checkPocklingtonFactor (known : List Nat) (n g : Nat) (qe : Nat × Nat) : Bool :=
  let q := qe.1
  let e := qe.2
  known.contains q &&
  decide (1 ≤ e) &&
  decide ((n - 1) % (q ^ e) = 0) &&
  let r := powModFuel 256 g ((n - 1) / q) n
  decide (1 < r) && decide (gcdFuel 512 (r - 1) n = 1)

/-- Kernel-reducible Pocklington certificate step checker for `3 ≤ n < 2^256`. -/
@[expose] def checkPocklingtonStep (known : List Nat) (s : PocklingtonStep) : Bool :=
  decide (3 ≤ s.n) &&
  decide (s.n < 2 ^ 256) &&
  decide (powModFuel 256 s.g (s.n - 1) s.n = 1) &&
  allDistinctPrimes s.factors &&
  s.factors.all (checkPocklingtonFactor known s.n s.g) &&
  let F := factorsProd s.factors
  decide (s.n < F * F)

/-- Verify a topological sequence of Pocklington steps starting from `known = [2]`. -/
@[expose] def verifyPrimeChainAux : List Nat → List PocklingtonStep → Option (List Nat)
  | known, [] => some known
  | known, s :: rest =>
    if checkPocklingtonStep known s then
      verifyPrimeChainAux (s.n :: known) rest
    else
      none

/-- Boolean check that `chain` is valid and certifies `target` as prime. -/
@[expose] def verifyPrimeCert (chain : List PocklingtonStep) (target : Nat) : Bool :=
  match verifyPrimeChainAux [2] chain with
  | some known => known.contains target
  | none => false

/-! ## Pocklington Certificate Soundness Proof -/

private def minDivAux (n d : Nat) : Nat → Nat
  | 0 => n
  | fuel + 1 => if n % d = 0 then d else minDivAux n (d + 1) fuel

private def minDiv (n : Nat) : Nat :=
  if n < 2 then n else minDivAux n 2 n

private theorem minDivAux_spec :
    ∀ (fuel n d : Nat),
      2 ≤ n → 2 ≤ d → n ≤ d + fuel →
      (∀ k : Nat, 2 ≤ k → k < d → ¬ (k ∣ n)) →
      let p := minDivAux n d fuel
      2 ≤ p ∧ p ∣ n ∧ (∀ k : Nat, 2 ≤ k → k < p → ¬ (k ∣ n))
  | 0, n, _, hn2, _, _, hno => by
    dsimp only [minDivAux]
    exact ⟨hn2, Nat.dvd_refl n, fun k hk2 hklt => hno k hk2 (by omega)⟩
  | fuel + 1, n, d, hn2, hd, hle, hno => by
    dsimp only [minDivAux]
    if hmod : n % d = 0 then
      simp only [hmod, ↓reduceIte]
      exact ⟨hd, Nat.dvd_of_mod_eq_zero hmod, hno⟩
    else
      simp only [hmod, ↓reduceIte]
      apply minDivAux_spec fuel n (d + 1) hn2 (by omega) (by omega)
      intro k hk2 hklt
      if hkd : k = d then
        subst hkd
        exact fun hdvd => hmod (Nat.mod_eq_zero_of_dvd hdvd)
      else
        exact hno k hk2 (by omega)

private theorem minDiv_prime_and_sq {n : Nat} (hn : 2 ≤ n) :
    Weierstrass.IsPrime (minDiv n) ∧ minDiv n ∣ n ∧
    (minDiv n = n ∨ minDiv n * minDiv n ≤ n) := by
  unfold minDiv
  simp only [show ¬ n < 2 by omega, ↓reduceIte]
  obtain ⟨hp2, hpdvd, hpmin⟩ :=
    minDivAux_spec n n 2 hn (by decide) (by omega) (by intros; omega)
  have hple : minDivAux n 2 n ≤ n := Nat.le_of_dvd (by omega) hpdvd
  have hPrime : Weierstrass.IsPrime (minDivAux n 2 n) := by
    refine ⟨hp2, fun d hd => ?_⟩
    if hd1 : d = 1 then exact .inl hd1
    else if hdp : d = minDivAux n 2 n then exact .inr hdp
    else
      have hdpos := Nat.pos_of_dvd_of_pos hd (by omega); have hdle := Nat.le_of_dvd (by omega) hd
      exact False.elim (hpmin d (by omega) (by omega) (Nat.dvd_trans hd hpdvd))
  refine ⟨hPrime, hpdvd, ?_⟩
  if hEq : minDivAux n 2 n = n then exact .inl hEq
  else
    obtain ⟨k, hk⟩ := hpdvd
    have hk2 : 2 ≤ k := if hk01 : k ≤ 1 then by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk01 with rfl | rfl <;> omega else by omega
    have hpk : minDivAux n 2 n ≤ k := if hlt : k < minDivAux n 2 n then
      False.elim (hpmin k hk2 hlt ⟨minDivAux n 2 n, Nat.mul_comm _ _ ▸ hk⟩) else by omega
    have hmul := Nat.mul_le_mul_left (minDivAux n 2 n) hpk; exact .inr (by omega)

private theorem pow_mod_eq_one_of_mod_eq_one {p x : Nat} (hp : 2 ≤ p) (hx : x % p = 1) :
    ∀ k : Nat, (x ^ k) % p = 1
  | 0 => Nat.mod_eq_of_lt hp
  | k + 1 => by
    rw [Nat.pow_succ, Nat.mul_mod, pow_mod_eq_one_of_mod_eq_one hp hx k, hx]
    exact Nat.mod_eq_of_lt hp

private theorem pow_mod_rem_eq_one {p g a b : Nat} (hp : 2 ≤ p)
    (ha : (g ^ a) % p = 1) (hb : (g ^ b) % p = 1) :
    (g ^ (a % b)) % p = 1 := by
  have hdiv : b * (a / b) + a % b = a := Nat.div_add_mod a b
  have hpow : g ^ a = (g ^ b) ^ (a / b) * g ^ (a % b) := by
    conv => lhs; rw [← hdiv]
    rw [Nat.pow_add, Nat.pow_mul]
  have h1 : ((g ^ b) ^ (a / b)) % p = 1 := pow_mod_eq_one_of_mod_eq_one hp hb (a / b)
  rw [hpow, Nat.mul_mod, h1, Nat.one_mul, Nat.mod_mod] at ha
  exact ha

private theorem exists_common_div_pow_one {p g : Nat} (hp : 2 ≤ p) :
    ∀ (b a : Nat), (g ^ a) % p = 1 → (g ^ b) % p = 1 →
      ∃ d : Nat, d ∣ a ∧ d ∣ b ∧ (g ^ d) % p = 1
  | b, a, ha, hb => by
    if h0 : b = 0 then
      subst h0
      exact ⟨a, Nat.dvd_refl a, Nat.dvd_zero a, ha⟩
    else
      obtain ⟨d, hdB, hdRem, hgd⟩ :=
        exists_common_div_pow_one hp (a % b) b hb (pow_mod_rem_eq_one hp ha hb)
      have hdiv : b * (a / b) + a % b = a := Nat.div_add_mod a b
      have hdMul : d ∣ b * (a / b) := Nat.dvd_trans hdB (Nat.dvd_mul_right b (a / b))
      have hdA : d ∣ a := by rw [← hdiv]; exact Nat.dvd_add hdMul hdRem
      exact ⟨d, hdA, hdB, hgd⟩
termination_by b _ => b
decreasing_by exact Nat.mod_lt a (Nat.pos_of_ne_zero h0)

private theorem prime_dvd_of_dvd_mul_of_not_dvd {q m d : Nat}
    (hq : Weierstrass.IsPrime q) (hd : d ∣ q * m) (hnd : ¬ (d ∣ m)) : q ∣ d := by
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
    have hdvdM : d ∣ m :=
      Int.ofNat_dvd.1 ⟨(extGcd d q).2.1 * (m : Int) + (k : Int) * (extGcd d q).2.2, hmul.symm⟩
    exact hnd hdvdM
  · rw [hgq] at hdd
    exact hdd

private theorem prime_pow_dvd_of_not_dvd_pred {q m : Nat} (hq : Weierstrass.IsPrime q) :
    ∀ (e : Nat) {d : Nat}, 1 ≤ e → d ∣ q ^ e * m → ¬ (d ∣ q ^ (e - 1) * m) → q ^ e ∣ d
  | 0, _, he, _, _ => by omega
  | 1, d, _, hd, hnd => by
    have hd1 : d ∣ q * m := by simpa using hd
    have hnd1 : ¬ (d ∣ m) := by simpa using hnd
    simpa using prime_dvd_of_dvd_mul_of_not_dvd hq hd1 hnd1
  | e + 2, d, _, hd, hnd => by
    have hqPos : 0 < q := by have := hq.1; omega
    have hPow : q ^ (e + 2) * m = q * (q ^ (e + 1) * m) := by
      rw [Nat.pow_succ, Nat.mul_comm (q ^ (e + 1)) q, Nat.mul_assoc]
    rw [hPow] at hd
    have hndE1 : ¬ (d ∣ q ^ (e + 1) * m) := by simpa using hnd
    have hqd : q ∣ d := prime_dvd_of_dvd_mul_of_not_dvd hq hd hndE1
    obtain ⟨d', rfl⟩ := hqd
    have hd' : d' ∣ q ^ (e + 1) * m := by
      obtain ⟨k, hk⟩ := hd
      rw [Nat.mul_assoc] at hk
      exact ⟨k, Nat.eq_of_mul_eq_mul_left hqPos hk⟩
    have hnd' : ¬ (d' ∣ q ^ e * m) := by
      intro hc
      apply hndE1
      have hPow1 : q ^ (e + 1) * m = q * (q ^ e * m) := by
        rw [Nat.pow_succ, Nat.mul_comm (q ^ e) q, Nat.mul_assoc]
      rw [hPow1]
      exact Nat.mul_dvd_mul_left q hc
    have ih := prime_pow_dvd_of_not_dvd_pred hq (e + 1) (by omega) hd' hnd'
    have hPow2 : q ^ (e + 2) = q * q ^ (e + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [hPow2]
    exact Nat.mul_dvd_mul_left q ih

private theorem not_prime_dvd_pow_of_ne {q p : Nat}
    (hq : Weierstrass.IsPrime q) (hp : Weierstrass.IsPrime p) (hne : q ≠ p) :
    ∀ e : Nat, ¬ (q ∣ p ^ e)
  | 0 => fun hd => by simp only [Nat.pow_zero] at hd; have := Nat.le_of_dvd (by decide) hd; have := hq.1; omega
  | e + 1 => fun hd => by
    rw [Nat.pow_succ] at hd
    rcases hq.dvd_mul hd with h1 | hqp
    · exact not_prime_dvd_pow_of_ne hq hp hne e h1
    · rcases hp.2 q hqp with hq1 | hqq
      · have := hq.1; omega
      · exact hne hqq

private theorem not_prime_dvd_factorsProd {q : Nat} (hq : Weierstrass.IsPrime q) :
    ∀ (fs : List (Nat × Nat)),
      (∀ p ∈ fs, Weierstrass.IsPrime p.1 ∧ q ≠ p.1) → ¬ (q ∣ factorsProd fs)
  | [], _ => fun hd => by dsimp only [factorsProd] at hd; have := Nat.le_of_dvd (by decide) hd; have := hq.1; omega
  | (p, e) :: rest, hall => fun hd => by
    dsimp only [factorsProd] at hd
    obtain ⟨hpPrime, hne⟩ := hall (p, e) (.head _)
    rcases hq.dvd_mul hd with hPow | hdRest
    · exact not_prime_dvd_pow_of_ne hq hpPrime hne e hPow
    · exact not_prime_dvd_factorsProd hq rest (fun z hz => hall z (.tail _ hz)) hdRest

private theorem prime_pow_pos {q : Nat} (hq : Weierstrass.IsPrime q) : ∀ e : Nat, 0 < q ^ e
  | 0 => Nat.one_pos
  | e + 1 => Nat.pow_succ q e ▸ Nat.mul_pos (prime_pow_pos hq e) (by have := hq.1; omega)

private theorem prime_pow_mul_dvd {q B d : Nat}
    (hq : Weierstrass.IsPrime q) (hnotB : ¬ (q ∣ B)) :
    ∀ (e : Nat), q ^ e ∣ d → B ∣ d → (q ^ e * B) ∣ d
  | 0, _, hB => by simp only [Nat.pow_zero, Nat.one_mul]; exact hB
  | e + 1, hqe1, hB => by
    have hqe : q ^ e ∣ d := Nat.dvd_trans ⟨q, rfl⟩ (Nat.pow_succ q e ▸ hqe1)
    obtain ⟨k, hk⟩ := prime_pow_mul_dvd hq hnotB e hqe hB
    obtain ⟨m, hm⟩ := hqe1
    have hEq : B * k = q * m := Nat.eq_of_mul_eq_mul_left (prime_pow_pos hq e) (by
      calc q ^ e * (B * k) = q ^ e * B * k := (Nat.mul_assoc _ _ _).symm
        _ = q ^ e * (q * m) := by rw [← hk, hm, Nat.pow_succ, Nat.mul_assoc])
    rcases hq.dvd_mul ⟨m, hEq⟩ with hqB | ⟨k', rfl⟩
    · exact False.elim (hnotB hqB)
    · refine ⟨k', ?_⟩
      calc d = (q ^ e * B) * (q * k') := hk
        _ = (q ^ (e + 1) * B) * k' := by
          rw [Nat.pow_succ]; simp only [Nat.mul_assoc]; rw [Nat.mul_left_comm B q k']

private theorem mod_mod_of_dvd {x n p : Nat} (hpn : p ∣ n) : (x % n) % p = x % p := by
  obtain ⟨k, rfl⟩ := hpn
  have hdiv : p * k * (x / (p * k)) + x % (p * k) = x := Nat.div_add_mod x (p * k)
  conv => rhs; rw [← hdiv]
  rw [Nat.mul_assoc p k _, Nat.mul_add_mod]

private theorem checkFactor_implies_pow_dvd {known : List Nat}
    (hKnown : ∀ q ∈ known, Weierstrass.IsPrime q)
    {n g p : Nat} (hn3 : 3 ≤ n) (hn256 : n < 2 ^ 256)
    (hpPrime : Weierstrass.IsPrime p) (hpn : p ∣ n)
    {d : Nat} (hdn1 : d ∣ (n - 1)) (hgd : (g ^ d) % p = 1)
    {qe : Nat × Nat} (hchk : checkPocklingtonFactor known n g qe = true) :
    Weierstrass.IsPrime qe.1 ∧ (qe.1 ^ qe.2) ∣ d := by
  unfold checkPocklingtonFactor at hchk
  dsimp only at hchk
  have h1 := Eq.mp (Bool.and_eq_true _ _) hchk
  have h2 := Eq.mp (Bool.and_eq_true _ _) h1.1
  have h3 := Eq.mp (Bool.and_eq_true _ _) h2.1
  have h4 := Eq.mp (Bool.and_eq_true _ _) h1.2
  have hqMem : qe.1 ∈ known := List.contains_iff_mem.1 h3.1
  have he1 : 1 ≤ qe.2 := of_decide_eq_true h3.2
  have hqeMod : (n - 1) % (qe.1 ^ qe.2) = 0 := of_decide_eq_true h2.2
  have hrGt1 : 1 < powModFuel 256 g ((n - 1) / qe.1) n := of_decide_eq_true h4.1
  have hgcd1 : gcdFuel 512 (powModFuel 256 g ((n - 1) / qe.1) n - 1) n = 1 :=
    of_decide_eq_true h4.2
  have hqPrime : Weierstrass.IsPrime qe.1 := hKnown qe.1 hqMem
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
      rw [hk, Nat.pow_mul]
      exact pow_mod_eq_one_of_mod_eq_one hpPrime.1 hgd k
    have hExpLt : (n - 1) / qe.1 < 2 ^ 256 := by
      have hle : (n - 1) / qe.1 ≤ n - 1 := Nat.div_le_self _ _
      omega
    have hrEq : powModFuel 256 g ((n - 1) / qe.1) n = (g ^ ((n - 1) / qe.1)) % n :=
      powModFuel_eq_pow_mod 256 g ((n - 1) / qe.1) n hExpLt
    let r := powModFuel 256 g ((n - 1) / qe.1) n
    have hrModP : r % p = 1 := by
      dsimp only [r]
      rw [hrEq, mod_mod_of_dvd hpn, hgDivQ]
    have hpDvdR1 : p ∣ (r - 1) := by
      have hdiv : p * (r / p) + r % p = r := Nat.div_add_mod r p
      rw [hrModP] at hdiv
      have hrGt1' : 1 < r := hrGt1
      exact ⟨r / p, by omega⟩
    have hpDvd1 : p ∣ 1 := by
      have hdvdG := dvd_gcdFuel 512 (r - 1) n p hpDvdR1 hpn
      have hgcd1' : gcdFuel 512 (r - 1) n = 1 := hgcd1
      rwa [hgcd1'] at hdvdG
    have hle1 : p ≤ 1 := Nat.le_of_dvd (by decide) hpDvd1
    have hp2 := hpPrime.1
    omega
  have hdQeM : d ∣ qe.1 ^ qe.2 * m := by rwa [← hm]
  exact prime_pow_dvd_of_not_dvd_pred hqPrime qe.2 he1 hdQeM hNotDvdPred

private theorem factorsProd_dvd_of_checks {known : List Nat}
    (hKnown : ∀ q ∈ known, Weierstrass.IsPrime q)
    {n g p d : Nat} (hn3 : 3 ≤ n) (hn256 : n < 2 ^ 256)
    (hpPrime : Weierstrass.IsPrime p) (hpn : p ∣ n)
    (hdn1 : d ∣ (n - 1)) (hgd : (g ^ d) % p = 1) :
    ∀ (fs : List (Nat × Nat)),
      allDistinctPrimes fs = true →
      fs.all (checkPocklingtonFactor known n g) = true →
      factorsProd fs ∣ d
  | [], _, _ => ⟨d, (Nat.one_mul d).symm⟩
  | (q, e) :: rest, hdist, hall => by
    simp only [allDistinctPrimes, List.all_cons, Bool.and_eq_true] at hdist hall
    obtain ⟨hNotInRest, hdistRest⟩ := hdist
    obtain ⟨hHead, hallRest⟩ := hall
    obtain ⟨hqPrime, hqeDvd⟩ :=
      checkFactor_implies_pow_dvd hKnown hn3 hn256 hpPrime hpn hdn1 hgd hHead
    have hRestDvd : factorsProd rest ∣ d :=
      factorsProd_dvd_of_checks hKnown hn3 hn256 hpPrime hpn hdn1 hgd rest hdistRest hallRest
    have hRestProps : ∀ z ∈ rest, Weierstrass.IsPrime z.1 ∧ q ≠ z.1 := by
      intro z hz
      have hzChk : checkPocklingtonFactor known n g z = true := List.all_eq_true.1 hallRest z hz
      obtain ⟨hzPrime, _⟩ :=
        checkFactor_implies_pow_dvd hKnown hn3 hn256 hpPrime hpn hdn1 hgd hzChk
      have hneB : (q != z.1) = true := List.all_eq_true.1 hNotInRest z hz
      exact ⟨hzPrime, bne_iff_ne.1 hneB⟩
    have hNotQRest : ¬ (q ∣ factorsProd rest) :=
      not_prime_dvd_factorsProd hqPrime rest hRestProps
    exact prime_pow_mul_dvd hqPrime hNotQRest e hqeDvd hRestDvd

/-- **Soundness of a single Pocklington step (`checkPocklingtonStep_sound`)**:
    if every integer in `known` is prime and `checkPocklingtonStep known s = true`,
    then `Weierstrass.IsPrime s.n`. -/
theorem checkPocklingtonStep_sound {known : List Nat}
    (hKnown : ∀ q ∈ known, Weierstrass.IsPrime q) {s : PocklingtonStep}
    (hStep : checkPocklingtonStep known s = true) : Weierstrass.IsPrime s.n := by
  unfold checkPocklingtonStep at hStep
  dsimp only at hStep
  have a1 := Eq.mp (Bool.and_eq_true _ _) hStep
  have a2 := Eq.mp (Bool.and_eq_true _ _) a1.1
  have a3 := Eq.mp (Bool.and_eq_true _ _) a2.1
  have a4 := Eq.mp (Bool.and_eq_true _ _) a3.1
  have a5 := Eq.mp (Bool.and_eq_true _ _) a4.1
  have hn3 : 3 ≤ s.n := of_decide_eq_true a5.1
  have hn256 : s.n < 2 ^ 256 := of_decide_eq_true a5.2
  have hFermatN : powModFuel 256 s.g (s.n - 1) s.n = 1 := of_decide_eq_true a4.2
  have hDist : allDistinctPrimes s.factors = true := a3.2
  have hFactors : s.factors.all (checkPocklingtonFactor known s.n s.g) = true := a2.2
  have hFsq : s.n < factorsProd s.factors * factorsProd s.factors := of_decide_eq_true a1.2
  obtain ⟨hpPrime, hpn, hpCases⟩ := minDiv_prime_and_sq (by omega : 2 ≤ s.n)
  rcases hpCases with hpEq | hpSqLe
  · rwa [← hpEq]
  · exfalso
    have hp2 : 2 ≤ minDiv s.n := hpPrime.1
    have hExpLt : s.n - 1 < 2 ^ 256 := by omega
    have hgPowN : (s.g ^ (s.n - 1)) % s.n = 1 := by
      rw [← powModFuel_eq_pow_mod 256 s.g (s.n - 1) s.n hExpLt]
      exact hFermatN
    have hgPowP : (s.g ^ (s.n - 1)) % (minDiv s.n) = 1 := by
      rw [← mod_mod_of_dvd hpn, hgPowN]
      exact Nat.mod_eq_of_lt hp2
    have hNotPg : ¬ (minDiv s.n ∣ s.g) := by
      intro ⟨k, hk⟩
      have hSplit : s.n - 1 = (s.n - 2) + 1 := by omega
      have hModG : s.g % (minDiv s.n) = 0 := by rw [hk, Nat.mul_mod_right]
      have hZero : (s.g ^ (s.n - 1)) % (minDiv s.n) = 0 := by
        rw [hSplit, Nat.pow_succ, Nat.mul_mod, hModG, Nat.mul_zero, Nat.zero_mod]
      omega
    have hgFermatP : (s.g ^ (minDiv s.n - 1)) % (minDiv s.n) = 1 :=
      hpPrime.pow_sub_one_mod hNotPg
    obtain ⟨d, hdn1, hdp1, hgd⟩ :=
      exists_common_div_pow_one hp2 (minDiv s.n - 1) (s.n - 1) hgPowP hgFermatP
    have hFDvdD : factorsProd s.factors ∣ d :=
      factorsProd_dvd_of_checks hKnown hn3 hn256 hpPrime hpn hdn1 hgd s.factors hDist hFactors
    have hFDvdP1 : factorsProd s.factors ∣ (minDiv s.n - 1) := Nat.dvd_trans hFDvdD hdp1
    have hFLeP1 : factorsProd s.factors ≤ minDiv s.n - 1 := Nat.le_of_dvd (by omega) hFDvdP1
    have hFLtP : factorsProd s.factors < minDiv s.n := by omega
    have hSqLt : factorsProd s.factors * factorsProd s.factors < minDiv s.n * minDiv s.n :=
      Nat.mul_lt_mul_of_lt_of_lt hFLtP hFLtP
    exact Nat.lt_asymm hFsq (Nat.lt_of_lt_of_le hSqLt hpSqLe)

private theorem primeTwo : Weierstrass.IsPrime 2 := by
  refine ⟨by decide, fun d hd => ?_⟩
  have hle : d ≤ 2 := Nat.le_of_dvd (by decide) hd
  have hpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by decide)
  omega

private theorem verifyPrimeChainAux_sound :
    ∀ (known : List Nat) (chain : List PocklingtonStep) (out : List Nat),
      (∀ q ∈ known, Weierstrass.IsPrime q) →
      verifyPrimeChainAux known chain = some out →
      ∀ q ∈ out, Weierstrass.IsPrime q
  | known, [], out, hKnown, hEq => by
    injection hEq with hOut
    subst hOut
    exact hKnown
  | known, s :: rest, out, hKnown, hEq => by
    unfold verifyPrimeChainAux at hEq
    split at hEq
    · rename_i hStep
      have hsPrime : Weierstrass.IsPrime s.n := checkPocklingtonStep_sound hKnown hStep
      have hKnown' : ∀ q ∈ s.n :: known, Weierstrass.IsPrime q := by
        intro q hq
        rcases List.mem_cons.1 hq with rfl | hqOld
        · exact hsPrime
        · exact hKnown q hqOld
      exact verifyPrimeChainAux_sound (s.n :: known) rest out hKnown' hEq
    · cases hEq

/-- **Top-level Pocklington certificate chain soundness (`verifyPrimeCert_sound`)**:
    whenever `verifyPrimeCert chain target = true`, `Weierstrass.IsPrime target` holds unconditionally. -/
theorem verifyPrimeCert_sound {chain : List PocklingtonStep} {target : Nat}
    (hCert : verifyPrimeCert chain target = true) : Weierstrass.IsPrime target := by
  unfold verifyPrimeCert at hCert
  cases hChain : verifyPrimeChainAux [2] chain with
  | none => simp only [hChain] at hCert; cases hCert
  | some out =>
    simp only [hChain] at hCert
    have hMem : target ∈ out := List.contains_iff_mem.1 hCert
    have hInit : ∀ q ∈ ([2] : List Nat), Weierstrass.IsPrime q := by
      intro q hq
      rcases List.mem_singleton.1 hq with rfl
      exact primeTwo
    exact verifyPrimeChainAux_sound [2] chain out hInit hChain target hMem

/-! ## Certified `secp256k1` Base Field & Subgroup Order Primality (`0 native_decide`) -/

/-- Shared 35-step Pocklington certificate DAG certifying both
    `SECP256K1_FIELD_P = 2^256 - 2^32 - 977` and `SECP256K1_ORDER_N`. -/
def secp256k1PrimeChain : List PocklingtonStep := [
  ⟨3, 2, [(2, 1)]⟩, ⟨13, 2, [(3, 1), (2, 2)]⟩, ⟨53, 2, [(13, 1)]⟩,
  ⟨7, 2, [(3, 1)]⟩, ⟨29, 2, [(7, 1)]⟩, ⟨107590001, 2, [(53, 1), (29, 1), (7, 1)]⟩,
  ⟨19, 2, [(3, 2)]⟩, ⟨5, 2, [(2, 2)]⟩, ⟨11, 2, [(5, 1)]⟩, ⟨419, 2, [(19, 1), (11, 1)]⟩,
  ⟨20113, 2, [(419, 1)]⟩, ⟨1206781, 2, [(20113, 1)]⟩, ⟨7240687, 2, [(1206781, 1)]⟩,
  ⟨17, 3, [(2, 4)]⟩, ⟨239, 2, [(17, 1)]⟩, ⟨101, 2, [(5, 2)]⟩, ⟨96557, 2, [(239, 1), (101, 1)]⟩,
  ⟨255515944373312847190720520512484175977, 2, [(107590001, 1), (7240687, 1), (96557, 1)]⟩,
  ⟨205115282021455665897114700593932402728804164701536103180137503955397371, 2,
    [(255515944373312847190720520512484175977, 1)]⟩,
  ⟨115792089237316195423570985008687907853269984665640564039457584007908834671663, 2,
    [(205115282021455665897114700593932402728804164701536103180137503955397371, 1)]⟩,
  ⟨1871, 2, [(17, 1), (11, 1)]⟩, ⟨1627771, 2, [(1871, 1)]⟩, ⟨297159362677, 2, [(1627771, 1)]⟩,
  ⟨1409, 3, [(11, 1), (2, 7)]⟩, ⟨28181, 2, [(1409, 1)]⟩, ⟨545358713, 2, [(28181, 1)]⟩,
  ⟨29047611873442575647497758179, 2, [(297159362677, 1), (545358713, 1)]⟩,
  ⟨341948486974166000522343609283189, 2, [(29047611873442575647497758179, 1)]⟩,
  ⟨41, 6, [(5, 1), (2, 3)]⟩, ⟨9349, 2, [(41, 1), (19, 1)]⟩, ⟨44706919, 2, [(9349, 1)]⟩,
  ⟨113, 3, [(7, 1), (2, 4)]⟩, ⟨120233, 2, [(113, 1), (19, 1)]⟩,
  ⟨174723607534414371449, 2, [(44706919, 1), (120233, 1)]⟩,
  ⟨115792089237316195423570985008687907852837564279074904382605163141518161494337, 2,
    [(341948486974166000522343609283189, 1), (174723607534414371449, 1)]⟩
]

/-- Kernel-checked primality of `SECP256K1_FIELD_P = 2^256 - 2^32 - 977`. -/
theorem secp256k1FieldPrime_isPrime :
    Weierstrass.IsPrime 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F :=
  verifyPrimeCert_sound (chain := secp256k1PrimeChain) (by decide +kernel)

/-- Kernel-checked primality of `SECP256K1_ORDER_N`. -/
theorem secp256k1OrderPrime_isPrime :
    Weierstrass.IsPrime 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141 :=
  verifyPrimeCert_sound (chain := secp256k1PrimeChain) (by decide +kernel)

/-- Mutation-sensitivity witness: the Carmichael number `561 = 3 · 11 · 17` passes the naive
    base-2 Fermat pseudoprime test `2^560 ≡ 1 (mod 561)`, yet `checkPocklingtonStep` rejects it
    because `gcd(2^(560 / 17) - 1, 561) ≠ 1`. -/
theorem tooth_carmichael_561_rejected_by_pocklington :
    ∃ (chain : List PocklingtonStep) (target : Nat),
      powModFuel 256 2 (target - 1) target = 1 ∧
      verifyPrimeCert chain target = false ∧
      ¬ Weierstrass.IsPrime target := by
  refine ⟨[⟨3, 2, [(2, 1)]⟩, ⟨11, 2, [(2, 1), (5, 1)]⟩, ⟨561, 2, [(17, 1), (11, 1)]⟩],
    561, by decide +kernel, by decide +kernel, fun ⟨_, hdiv⟩ => ?_⟩
  rcases hdiv 3 ⟨187, by decide⟩ with h1 | h561 <;> omega

theorem inhabited_verifyPrimeCert :
    ∃ (chain : List PocklingtonStep) (target : Nat),
      verifyPrimeCert chain target = true ∧ Weierstrass.IsPrime target :=
  ⟨[⟨3, 2, [(2, 1)]⟩], 3, by decide +kernel,
    verifyPrimeCert_sound (chain := [⟨3, 2, [(2, 1)]⟩]) (by decide +kernel)⟩

#tooth_pair
  Qsag.verifyPrimeCert_sound
  vs
  Qsag.tooth_carmichael_561_rejected_by_pocklington

#verify_inhabited
  Qsag.verifyPrimeCert_sound
  Qsag.inhabited_verifyPrimeCert

#verify_constructive
  Qsag.verifyPrimeCert_sound
  Qsag.secp256k1FieldPrime_isPrime
  Qsag.secp256k1OrderPrime_isPrime
  Qsag.tooth_carmichael_561_rejected_by_pocklington

end Qsag
