module
public import Qsag.Tactic.Prelude

public section
namespace Qsag
/-- The Goldilocks prime $p = 2^{64} - 2^{32} + 1 = 18446744069414584321$. -/
@[expose] def goldilocksPrime : Nat := 18446744069414584321

private def strictNat (n : Nat) (k : Nat → Nat) : Nat :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)

private theorem strictNat_eq (n : Nat) (k : Nat → Nat) : strictNat n k = k n := by
  cases n <;> rfl

def modPowFuel : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, m => 1 % m
  | fuel + 1, base, exp, m =>
    if exp = 0 then 1 % m
    else
      strictNat (modPowFuel fuel base (exp / 2) m) fun half =>
        strictNat ((half * half) % m) fun sq =>
          if exp % 2 = 1 then (sq * (base % m)) % m else sq

private theorem pow_two_mul (b k : Nat) : b ^ (2 * k) = (b ^ k) * (b ^ k) := by
  rw [Nat.mul_comm 2 k, Nat.pow_mul, Nat.pow_succ, Nat.pow_one]

theorem modPowFuel_eq_pow_mod :
    ∀ (fuel base exp m : Nat), exp < 2 ^ fuel → modPowFuel fuel base exp m = (base ^ exp) % m
  | 0, _, exp, m, hlt => by
    have he0 : exp = 0 := by simp at hlt; omega
    subst he0; simp [modPowFuel]
  | fuel + 1, base, exp, m, hlt => by
    simp only [modPowFuel]
    if h0 : exp = 0 then
      subst h0; simp
    else
      simp only [h0, ↓reduceIte, strictNat_eq]
      have hexpHalf : exp / 2 < 2 ^ fuel := by
        rw [Nat.pow_succ] at hlt; omega
      have ih := modPowFuel_eq_pow_mod fuel base (exp / 2) m hexpHalf
      have hsq : ((modPowFuel fuel base (exp / 2) m) * (modPowFuel fuel base (exp / 2) m)) % m =
          (base ^ (2 * (exp / 2))) % m := by
        rw [ih, ← Nat.mul_mod, ← pow_two_mul]
      have hmod2 : exp % 2 = 0 ∨ exp % 2 = 1 := by omega
      rcases hmod2 with hr0 | hr1
      · simp only [hr0, show ¬ (0 = 1) by decide, ↓reduceIte]
        have hexp : 2 * (exp / 2) = exp := by omega
        rw [hsq, hexp]
      · simp only [hr1, ↓reduceIte]
        have hexp : exp = 2 * (exp / 2) + 1 := by omega
        conv => rhs; rw [hexp, Nat.pow_add, Nat.pow_one, Nat.mul_mod]
        rw [hsq]

/-- Elementary primality predicate on `Nat`. -/
@[expose] def IsPrimeNat (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

private def minDivisorAux (n d : Nat) : Nat → Nat
  | 0 => n
  | fuel + 1 => if n % d = 0 then d else minDivisorAux n (d + 1) fuel

private def minDivisor (n : Nat) : Nat :=
  if n < 2 then n else minDivisorAux n 2 n

private theorem minDivisorAux_spec :
    ∀ (fuel n d : Nat),
      2 ≤ n → 2 ≤ d → n ≤ d + fuel →
      (∀ k : Nat, 2 ≤ k → k < d → ¬ (k ∣ n)) →
      let q := minDivisorAux n d fuel
      2 ≤ q ∧ q ∣ n ∧ (∀ k : Nat, 2 ≤ k → k < q → ¬ (k ∣ n))
  | 0, n, d, hn2, _, _, hno => by
    dsimp only [minDivisorAux]
    refine ⟨hn2, Nat.dvd_refl n, ?_⟩
    intro k hk2 hklt
    exact hno k hk2 (by omega)
  | fuel + 1, n, d, hn2, hd, hle, hno => by
    dsimp only [minDivisorAux]
    if hmod : n % d = 0 then
      simp only [hmod, ↓reduceIte]
      exact ⟨hd, Nat.dvd_of_mod_eq_zero hmod, hno⟩
    else
      simp only [hmod, ↓reduceIte]
      apply minDivisorAux_spec fuel n (d + 1) hn2 (by omega) (by omega)
      intro k hk2 hklt
      if hkd : k = d then
        subst hkd
        intro hdvd
        exact hmod (Nat.mod_eq_zero_of_dvd hdvd)
      else
        exact hno k hk2 (by omega)

private theorem minDivisor_isPrime {n : Nat} (hn : 2 ≤ n) :
    IsPrimeNat (minDivisor n) ∧ minDivisor n ∣ n ∧ minDivisor n ≤ n := by
  unfold minDivisor
  have hnot : ¬ n < 2 := by omega
  simp only [hnot, ↓reduceIte]
  obtain ⟨hq2, hqdvd, hqmin⟩ := minDivisorAux_spec n n 2 hn (by decide) (by omega) (by intros; omega)
  have hqle : minDivisorAux n 2 n ≤ n := Nat.le_of_dvd (by omega) hqdvd
  refine ⟨⟨hq2, ?_⟩, hqdvd, hqle⟩
  intro d hd
  if hd1 : d = 1 then exact .inl hd1
  else if hdq : d = minDivisorAux n 2 n then exact .inr hdq
  else
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
    have hdle : d ≤ minDivisorAux n 2 n := Nat.le_of_dvd (by omega) hd
    exact False.elim (hqmin d (by omega) (by omega) (Nat.dvd_trans hd hqdvd))

def extGcd (a b : Nat) : Nat × Int × Int :=
  if _hb : b = 0 then (a, 1, 0)
  else
    let r := extGcd b (a % b)
    (r.1, r.2.2, r.2.1 - ((a / b : Nat) : Int) * r.2.2)
termination_by b
decreasing_by exact Nat.mod_lt a (Nat.pos_of_ne_zero _hb)

theorem extGcd_dvd (a b : Nat) : (extGcd a b).1 ∣ a ∧ (extGcd a b).1 ∣ b := by
  if hb : b = 0 then
    subst hb
    rw [extGcd]
    simp only [↓reduceDIte]
    exact ⟨Nat.dvd_refl a, Nat.dvd_zero a⟩
  else
    obtain ⟨hdb, hdmod⟩ := extGcd_dvd b (a % b)
    have heq : (extGcd a b).1 = (extGcd b (a % b)).1 := by
      conv => lhs; rw [extGcd]
      simp [hb]
    rw [heq]
    refine ⟨?_, hdb⟩
    have hdiv : b * (a / b) + a % b = a := Nat.div_add_mod a b
    have hmul : (extGcd b (a % b)).1 ∣ b * (a / b) := Nat.dvd_trans hdb (Nat.dvd_mul_right b (a / b))
    have hsum := Nat.dvd_add hmul hdmod
    rwa [hdiv] at hsum
termination_by b
decreasing_by exact Nat.mod_lt a (Nat.pos_of_ne_zero hb)

theorem extGcd_bezout (a b : Nat) :
    (a : Int) * (extGcd a b).2.1 + (b : Int) * (extGcd a b).2.2 = ((extGcd a b).1 : Int) := by
  if hb : b = 0 then
    subst hb
    rw [extGcd]
    simp
  else
    have ih := extGcd_bezout b (a % b)
    have hstep : extGcd a b =
        ((extGcd b (a % b)).1,
         (extGcd b (a % b)).2.2,
         (extGcd b (a % b)).2.1 - ((a / b : Nat) : Int) * (extGcd b (a % b)).2.2) := by
      conv => lhs; rw [extGcd]
      simp [hb]
    rw [hstep]
    dsimp only
    have hdivInt : (b : Int) * ((a / b : Nat) : Int) + ((a % b : Nat) : Int) = (a : Int) := by
      exact_mod_cast Nat.div_add_mod a b
    have h1 : (b : Int) * ((extGcd b (a % b)).2.1 - ((a / b : Nat) : Int) * (extGcd b (a % b)).2.2) =
        (b : Int) * (extGcd b (a % b)).2.1 - ((b : Int) * ((a / b : Nat) : Int)) * (extGcd b (a % b)).2.2 := by
      rw [Int.mul_sub, Int.mul_assoc]
    have h2 : ((a : Int) - (b : Int) * ((a / b : Nat) : Int)) * (extGcd b (a % b)).2.2 =
        (a : Int) * (extGcd b (a % b)).2.2 - ((b : Int) * ((a / b : Nat) : Int)) * (extGcd b (a % b)).2.2 :=
      Int.sub_mul _ _ _
    have h3 : ((a % b : Nat) : Int) = (a : Int) - (b : Int) * ((a / b : Nat) : Int) := by omega
    rw [h3, h2] at ih
    rw [h1]
    omega
termination_by b
decreasing_by exact Nat.mod_lt a (Nat.pos_of_ne_zero hb)

theorem IsPrimeNat.dvd_mul {q a b : Nat} (hq : IsPrimeNat q)
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

private def posRange : Nat → List Nat
  | 0 => []
  | n + 1 => (n + 1) :: posRange n

private theorem mem_posRange_iff {x : Nat} : ∀ {n : Nat}, x ∈ posRange n ↔ 1 ≤ x ∧ x ≤ n
  | 0 => by
    constructor
    · intro h; cases h
    · rintro ⟨hLo, hHi⟩; omega
  | n + 1 => by
    simp only [posRange, List.mem_cons, mem_posRange_iff]
    constructor
    · intro h
      rcases h with hEq | ⟨hLo, hHi⟩
      · subst hEq; exact ⟨Nat.succ_pos n, Nat.le_refl _⟩
      · exact ⟨hLo, Nat.le_trans hHi (Nat.le_succ n)⟩
    · rintro ⟨hLo, hHi⟩
      by_cases hEq : x = n + 1
      · exact .inl hEq
      · exact .inr ⟨hLo, by omega⟩

private theorem posRange_nodup : ∀ (n : Nat), (posRange n).Nodup
  | 0 => .nil
  | n + 1 =>
    .cons
      (fun b hb heq => by
        have hle := (mem_posRange_iff.1 hb).2
        omega)
      (posRange_nodup n)

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
    ∀ {ys : List Nat},
      ys.Nodup → v ∈ ys →
      listProd ys = v * listProd (eraseFirst v ys) ∧
      (eraseFirst v ys).length + 1 = ys.length ∧
      (eraseFirst v ys).Nodup ∧
      (∀ z : Nat, z ≠ v → z ∈ ys → z ∈ eraseFirst v ys)
  | [], _, hmem => by cases hmem
  | y :: ys, .cons hrel hnd, hmem => by
    dsimp only [eraseFirst]
    if hy : y = v then
      subst hy
      simp only [↓reduceIte, listProd, List.length_cons]
      refine ⟨trivial, trivial, hnd, ?_⟩
      intro z hzne hzmem
      cases hzmem with
      | head => exact False.elim (hzne rfl)
      | tail _ htail => exact htail
    else
      simp only [hy, ↓reduceIte, listProd, List.length_cons]
      have hvTail : v ∈ ys := by
        cases hmem with
        | head => exact False.elim (hy rfl)
        | tail _ ht => exact ht
      obtain ⟨hprod, hlen, hnd', hsub⟩ := eraseFirst_spec hnd hvTail
      refine ⟨?_, by omega, .cons (fun b hb heq => hrel b (mem_of_mem_eraseFirst hb) heq) hnd', ?_⟩
      · rw [hprod, ← Nat.mul_assoc, Nat.mul_comm y v, Nat.mul_assoc]
      · intro z hzne hzmem
        cases hzmem with
        | head => exact .head _
        | tail _ ht => exact .tail _ (hsub z hzne ht)

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

private theorem not_dvd_listProd_posRange {q : Nat} (hq : IsPrimeNat q) :
    ∀ {n : Nat}, n < q → ¬ (q ∣ listProd (posRange n))
  | 0, _, hdvd => by
    dsimp only [posRange, listProd] at hdvd
    have hle := Nat.le_of_dvd (by decide) hdvd
    have hq2 := hq.1
    omega
  | n + 1, hlt, hdvd => by
    simp only [posRange, listProd] at hdvd
    have hnot1 : ¬ (q ∣ (n + 1)) := by
      intro h1
      have hle := Nat.le_of_dvd (by omega) h1
      omega
    exact not_dvd_listProd_posRange hq (by omega) (hq.dvd_mul hdvd hnot1)

private theorem sub_dvd_of_mod_eq {x y q : Nat} (hle : y ≤ x) (hmod : x % q = y % q) :
    q ∣ (x - y) := by
  have hx : q * (x / q) + x % q = x := Nat.div_add_mod x q
  have hy : q * (y / q) + y % q = y := Nat.div_add_mod y q
  have hdivLe : y / q ≤ x / q := Nat.div_le_div_right hle
  refine ⟨x / q - y / q, ?_⟩
  rw [Nat.mul_sub]
  omega

private theorem one_le_pow_of_pos {a : Nat} (ha : 1 ≤ a) : ∀ k : Nat, 1 ≤ a ^ k
  | 0 => Nat.le_refl 1
  | k + 1 => by
    rw [Nat.pow_succ]
    exact Nat.le_trans (one_le_pow_of_pos ha k) (Nat.le_mul_of_pos_right _ ha)

/-- **Fermat's Little Theorem (`IsPrimeNat.pow_sub_one_mod`)**. -/
theorem IsPrimeNat.pow_sub_one_mod {q a : Nat} (hq : IsPrimeNat q) (hna : ¬ (q ∣ a)) :
    (a ^ (q - 1)) % q = 1 := by
  let L := posRange (q - 1)
  let f := fun i : Nat => (a * i) % q
  have hMem : ∀ x ∈ L.map f, x ∈ L := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hi1, hi2⟩ := mem_posRange_iff.1 hi
    have hni : ¬ (q ∣ i) := fun hd => by
      have hle := Nat.le_of_dvd (by omega) hd
      have hq2 := hq.1
      omega
    have hnai : ¬ (q ∣ a * i) := fun hd => hni (hq.dvd_mul (Nat.mul_comm a i ▸ hd) hna)
    have hmodPos : 0 < (a * i) % q := by
      if hz : (a * i) % q = 0 then
        exact False.elim (hnai (Nat.dvd_of_mod_eq_zero hz))
      else omega
    have hmodLt : (a * i) % q < q := Nat.mod_lt _ (by have := hq.1; omega)
    dsimp only [f]
    exact mem_posRange_iff.2 ⟨hmodPos, by omega⟩
  have hInjOn : ∀ i j : Nat, i ∈ L → j ∈ L → f i = f j → i = j := by
    intro i j hi hj hij
    obtain ⟨hi1, hi2⟩ := mem_posRange_iff.1 hi
    obtain ⟨hj1, hj2⟩ := mem_posRange_iff.1 hj
    have hq2 := hq.1
    if hijLe : i ≤ j then
      have hdvd : q ∣ a * (j - i) := by
        have hmul : a * j - a * i = a * (j - i) := (Nat.mul_sub a j i).symm
        rw [← hmul]
        exact sub_dvd_of_mod_eq (Nat.mul_le_mul_left a hijLe) hij.symm
      have hdvdDiff : q ∣ (j - i) := hq.dvd_mul hdvd hna
      if hdiff0 : j - i = 0 then omega
      else
        have hle := Nat.le_of_dvd (by omega) hdvdDiff
        omega
    else
      have hjiLe : j ≤ i := by omega
      have hdvd : q ∣ a * (i - j) := by
        have hmul : a * i - a * j = a * (i - j) := (Nat.mul_sub a i j).symm
        rw [← hmul]
        exact sub_dvd_of_mod_eq (Nat.mul_le_mul_left a hjiLe) hij
      have hdvdDiff : q ∣ (i - j) := hq.dvd_mul hdvd hna
      if hdiff0 : i - j = 0 then omega
      else
        have hle := Nat.le_of_dvd (by omega) hdvdDiff
        omega
  have hNodupMap : (L.map f).Nodup := by
    have hsubNd : ∀ {xs : List Nat}, xs.Nodup → (∀ z ∈ xs, z ∈ L) → (xs.map f).Nodup := by
      intro xs hnd hxs
      induction hnd with
      | nil => exact .nil
      | @cons x rest hrel hndRest ih =>
        refine .cons (fun b hb heq => ?_) (ih (fun z hz => hxs z (.tail _ hz)))
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
        have hxy := hInjOn x y (hxs x (.head _)) (hxs y (.tail _ hy)) heq
        exact hrel y hy hxy
    exact hsubNd (posRange_nodup (q - 1)) (fun z hz => hz)
  have hProdEq : listProd (L.map f) = listProd L :=
    listProd_eq_of_nodup_subset hNodupMap (posRange_nodup (q - 1)) (by simp) hMem
  have hModEq : (a ^ (q - 1) * listProd L) % q = (listProd L) % q := by
    rw [← listProd_map_mul_mod a q (q - 1), hProdEq]
  have haPos : 1 ≤ a := by
    if ha0 : a = 0 then subst ha0; exact False.elim (hna (Nat.dvd_zero q))
    else omega
  have hpowPos : 1 ≤ a ^ (q - 1) := one_le_pow_of_pos haPos (q - 1)
  have hdvdMul : q ∣ (a ^ (q - 1) - 1) * listProd L := by
    have hsub : a ^ (q - 1) * listProd L - listProd L = (a ^ (q - 1) - 1) * listProd L := by
      rw [Nat.sub_mul, Nat.one_mul]
    rw [← hsub]
    exact sub_dvd_of_mod_eq (Nat.le_mul_of_pos_left _ hpowPos) hModEq
  have hnotF : ¬ (q ∣ listProd L) :=
    not_dvd_listProd_posRange hq (by have := hq.1; omega)
  have hdvdPow : q ∣ (a ^ (q - 1) - 1) :=
    hq.dvd_mul (Nat.mul_comm (a ^ (q - 1) - 1) (listProd L) ▸ hdvdMul) hnotF
  obtain ⟨k, hk⟩ := hdvdPow
  have hEq : a ^ (q - 1) = q * k + 1 := by omega
  rw [hEq, Nat.mul_add_mod, Nat.mod_eq_of_lt hq.1]

private theorem pow_mod_eq_one_of_eq_one {a q : Nat} (hq : 2 ≤ q) (ha : a % q = 1) :
    ∀ k : Nat, (a ^ k) % q = 1
  | 0 => Nat.mod_eq_of_lt hq
  | k + 1 => by
    rw [Nat.pow_succ, Nat.mul_mod, pow_mod_eq_one_of_eq_one hq ha k, ha]
    exact Nat.mod_eq_of_lt hq

private theorem pow_gcd_mod_eq_one {a q : Nat} (hq : 2 ≤ q) :
    ∀ (m n : Nat), (a ^ m) % q = 1 → (a ^ n) % q = 1 → (a ^ (Nat.gcd m n)) % q = 1
  | 0, n, _, hn => by simpa [Nat.gcd_zero_left] using hn
  | m + 1, n, hm, hn => by
    have hdiv : (m + 1) * (n / (m + 1)) + n % (m + 1) = n := Nat.div_add_mod n (m + 1)
    have hrem : (a ^ (n % (m + 1))) % q = 1 := by
      have hn' : (a ^ ((m + 1) * (n / (m + 1)) + n % (m + 1))) % q = 1 := hdiv.symm ▸ hn
      rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod,
          pow_mod_eq_one_of_eq_one hq hm (n / (m + 1)), Nat.one_mul, Nat.mod_mod] at hn'
      exact hn'
    rw [Nat.gcd_rec (m + 1) n]
    exact pow_gcd_mod_eq_one hq (n % (m + 1)) (m + 1) hrem hm
termination_by m _ => m
decreasing_by exact Nat.mod_lt n (Nat.succ_pos m)

private theorem dvd_of_two_pow_dvd_mul_odd :
    ∀ (k g c : Nat), c % 2 = 1 → 2 ^ k ∣ g * c → 2 ^ k ∣ g
  | 0, g, _, _, _ => Nat.one_dvd g
  | k + 1, g, c, hodd, hdvd => by
    have h2prime : IsPrimeNat 2 := ⟨by decide, fun d hd => by
      have hpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by decide)
      have hle : d ≤ 2 := Nat.le_of_dvd (by decide) hd
      omega⟩
    have hnc : ¬ (2 ∣ c) := fun hc => by obtain ⟨t, rfl⟩ := hc; omega
    have h2dvd : 2 ∣ g * c := by
      rw [Nat.pow_succ] at hdvd
      exact Nat.dvd_trans (Nat.dvd_mul_left 2 (2 ^ k)) hdvd
    obtain ⟨g', rfl⟩ := h2prime.dvd_mul (Nat.mul_comm g c ▸ h2dvd) hnc
    have hdvd' : 2 ^ k ∣ g' * c := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc 2 g' c] at hdvd
      exact Nat.dvd_of_mul_dvd_mul_left (by decide) hdvd
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2]
    exact Nat.mul_dvd_mul_left 2 (dvd_of_two_pow_dvd_mul_odd k g' c hodd hdvd')

private theorem goldilocksEuler_modPow_abstract (e : Nat)
    (hLt : e < 2 ^ 64)
    (hEval : modPowFuel 64 7 e goldilocksPrime = goldilocksPrime - 1) :
    (7 ^ e) % goldilocksPrime = goldilocksPrime - 1 := by
  rw [← modPowFuel_eq_pow_mod 64 7 e goldilocksPrime hLt]
  exact hEval

/-- Euler witness `7 ^ ((p - 1) / 2) ≡ -1 (mod p)` via verified 64-step modular exponentiation. -/
theorem goldilocksEuler_modPow :
    ∀ u : Unit, u = () →
      (7 ^ ((goldilocksPrime - 1) / 2)) % goldilocksPrime = goldilocksPrime - 1 :=
  fun _ _ => goldilocksEuler_modPow_abstract ((goldilocksPrime - 1) / 2) (by decide) (by decide)

/-- Proth-style divisor argument with the modulus and the half-exponent abstract: the kernel never
    meets a closed power with a 63-bit exponent while checking it. -/
private theorem dvd_cases_of_euler_certificate (p half : Nat)
    (hpPos : 1 ≤ p) (hpLt : p < (2 ^ 32) * (2 ^ 32)) (hodd : p % 2 = 1)
    (hrem : p % 3 ≠ 0 ∧ p % 5 ≠ 0 ∧ p % 7 ≠ 0)
    (hEuler : 7 ^ half % p = p - 1) (h2half : p - 1 = 2 * half)
    (h2pow32 : 2 ^ 32 ∣ (p - 1)) (d : Nat) (hd : d ∣ p) :
    d = 1 ∨ d = p := by
  if hd1 : d = 1 then exact .inl hd1
  else if hdp : d = p then exact .inr hdp
  else
    exfalso
    obtain ⟨e, he⟩ := hd
    have hdPos : 2 ≤ d := by
      if hd0 : d = 0 then subst hd0; rw [Nat.zero_mul] at he; omega
      else omega
    have hePos : 2 ≤ e := by
      if he0 : e = 0 then subst he0; rw [Nat.mul_zero] at he; omega
      else if he1 : e = 1 then subst he1; rw [Nat.mul_one] at he; exact False.elim (hdp he.symm)
      else omega
    let m := if d ≤ e then d else e
    have hm2 : 2 ≤ m := by dsimp [m]; split <;> omega
    have hmDvd : m ∣ p := by
      dsimp [m]; split
      · exact ⟨e, he⟩
      · exact ⟨d, Nat.mul_comm d e ▸ he⟩
    have hmSq : m * m ≤ p := by
      dsimp [m]; split
      · rename_i hle; rw [he]; exact Nat.mul_le_mul_left d hle
      · rename_i hgt; rw [he, Nat.mul_comm d e]; exact Nat.mul_le_mul_left e (by omega)
    obtain ⟨q, hqDef⟩ : ∃ q, minDivisor m = q := ⟨minDivisor m, rfl⟩
    obtain ⟨hqPrime, hqDvdM, hqLeM⟩ := minDivisor_isPrime hm2
    rw [hqDef] at hqPrime hqDvdM hqLeM
    have hqDvdP : q ∣ p := Nat.dvd_trans hqDvdM hmDvd
    have hqSq : q * q < (2 ^ 32) * (2 ^ 32) := by
      exact Nat.lt_of_le_of_lt (Nat.le_trans (Nat.mul_le_mul hqLeM hqLeM) hmSq) hpLt
    have hqLt32 : q < 2 ^ 32 := by
      if hge : 2 ^ 32 ≤ q then
        have hsqGe := Nat.mul_le_mul hge hge
        omega
      else omega
    have hqGe3 : 3 ≤ q := by
      have hq2 := hqPrime.1
      if hqEq2 : q = 2 then
        obtain ⟨k, hk⟩ := hqDvdP
        rw [hqEq2] at hk
        omega
      else omega
    have hqNotDvd7 : ¬ (q ∣ 7) := by
      intro hd7
      have hle7 : q ≤ 7 := Nat.le_of_dvd (by decide) hd7
      obtain ⟨k, hk⟩ := hqDvdP
      have hcases : q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 ∨ q = 7 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl
      · exact hrem.1 (by omega)
      · rcases hqPrime.2 2 ⟨2, rfl⟩ with h | h <;> omega
      · exact hrem.2.1 (by omega)
      · rcases hqPrime.2 2 ⟨3, rfl⟩ with h | h <;> omega
      · exact hrem.2.2 (by omega)
    have hHalfPlusOneDvdP : p ∣ (7 ^ half + 1) := by
      have hdiv := Nat.div_add_mod (7 ^ half) p
      rw [hEuler] at hdiv
      refine ⟨(7 ^ half) / p + 1, ?_⟩
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have hHalfPlusOneDvdQ : q ∣ (7 ^ half + 1) := Nat.dvd_trans hqDvdP hHalfPlusOneDvdP
    have hHalfModQ : (7 ^ half) % q = q - 1 := by
      obtain ⟨t, ht⟩ := hHalfPlusOneDvdQ
      have htPos : 1 ≤ t := by
        if ht0 : t = 0 then
          rw [ht0, Nat.mul_zero] at ht
          exact False.elim (Nat.succ_ne_zero (7 ^ half) ht)
        else omega
      have hEq : 7 ^ half = q * (t - 1) + (q - 1) := by
        rw [Nat.mul_sub, Nat.mul_one]
        have hq1 : q ≤ q * t := by
          have h := Nat.mul_le_mul_left q htPos
          rwa [Nat.mul_one] at h
        omega
      rw [hEq, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    have hPm1ModQ : (7 ^ (p - 1)) % q = 1 := by
      rw [h2half, pow_two_mul, Nat.mul_mod, hHalfModQ]
      obtain ⟨q2, hq2Eq⟩ : ∃ q2, q = q2 + 3 := ⟨q - 3, by omega⟩
      have hsq : (q - 1) * (q - 1) = q * (q - 2) + 1 := by
        rw [hq2Eq]
        have ha : q2 + 3 - 1 = q2 + 2 := by omega
        have hb : q2 + 3 - 2 = q2 + 1 := by omega
        rw [ha, hb]
        simp only [Nat.mul_add, Nat.add_mul]
        omega
      rw [hsq, Nat.mul_add_mod, Nat.mod_eq_of_lt hqPrime.1]
    have hQm1ModQ : (7 ^ (q - 1)) % q = 1 := hqPrime.pow_sub_one_mod hqNotDvd7
    obtain ⟨g, hgDef⟩ : ∃ g, Nat.gcd (p - 1) (q - 1) = g := ⟨_, rfl⟩
    have hgPow : (7 ^ g) % q = 1 := by
      rw [← hgDef]
      exact pow_gcd_mod_eq_one hqPrime.1 (p - 1) (q - 1) hPm1ModQ hQm1ModQ
    have hgNotDvdHalf : ¬ (g ∣ half) := by
      rintro ⟨u, hu⟩
      have h1 : (7 ^ half) % q = 1 := by
        rw [hu, Nat.pow_mul]
        exact pow_mod_eq_one_of_eq_one hqPrime.1 hgPow u
      rw [hHalfModQ] at h1
      omega
    obtain ⟨c, hc⟩ := hgDef ▸ Nat.gcd_dvd_left (p - 1) (q - 1)
    have hcOdd : c % 2 = 1 := by
      if hce : c % 2 = 0 then
        obtain ⟨c', hc'⟩ : ∃ c', c = 2 * c' := ⟨c / 2, by omega⟩
        have hmul : 2 * half = 2 * (g * c') := by
          rw [← h2half, hc, hc', ← Nat.mul_assoc, Nat.mul_comm g 2, Nat.mul_assoc]
        have hhalfEq : half = g * c' := by omega
        exact False.elim (hgNotDvdHalf ⟨c', hhalfEq⟩)
      else omega
    have h2pow32DvdPm1 : 2 ^ 32 ∣ (p - 1) := h2pow32
    rw [hc] at h2pow32DvdPm1
    have h2pow32DvdG : 2 ^ 32 ∣ g := dvd_of_two_pow_dvd_mul_odd 32 g c hcOdd h2pow32DvdPm1
    have h2pow32DvdQm1 : 2 ^ 32 ∣ (q - 1) :=
      Nat.dvd_trans h2pow32DvdG (hgDef ▸ Nat.gcd_dvd_right (p - 1) (q - 1))
    have hge : 2 ^ 32 ≤ q - 1 := Nat.le_of_dvd (by omega) h2pow32DvdQm1
    omega

/-- **Zero-Axiom Proth Primality Theorem for `goldilocksPrime` ($p = 2^{64} - 2^{32} + 1$)**. -/
theorem goldilocksPrime_dvd_cases (d : Nat) (hd : d ∣ goldilocksPrime) :
    d = 1 ∨ d = goldilocksPrime :=
  dvd_cases_of_euler_certificate goldilocksPrime ((goldilocksPrime - 1) / 2)
    (by decide) (by decide) (by decide) (by decide) (goldilocksEuler_modPow () rfl) (by decide)
    ⟨2 ^ 32 - 1, by decide⟩ d hd

theorem goldilocksPrime_isPrime (u : Unit) : IsPrimeNat goldilocksPrime :=
  ⟨by decide, fun _ => (let _ := u; goldilocksPrime_dvd_cases _)⟩

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
