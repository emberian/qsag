module
public import Qsag.Tactic.Prelude

public section
namespace Qsag
/-- The Goldilocks prime $p = 2^{64} - 2^{32} + 1 = 18446744069414584321$. -/
@[expose] def goldilocksPrime : Nat := 18446744069414584321

abbrev primalityStrictNat (n : Nat) (k : Nat → Nat) : Nat :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)

private theorem strictNat_eq (n : Nat) (k : Nat → Nat) : primalityStrictNat n k = k n := by
  cases n <;> rfl

@[expose] def modPowFuel : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, m => 1 % m
  | fuel + 1, base, exp, m =>
    if exp = 0 then 1 % m
    else
      primalityStrictNat (modPowFuel fuel base (exp / 2) m) fun half =>
        primalityStrictNat ((half * half) % m) fun sq =>
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

/-- The list `[n, n - 1, …, 1]` of positive naturals up to `n`; the index set shared by the
    Fermat little theorem here and the cyclic-order argument in `Qsag.Math.EllipticCurves`. -/
def posRange : Nat → List Nat
  | 0 => []
  | n + 1 => (n + 1) :: posRange n

theorem mem_posRange_iff {x : Nat} : ∀ {n : Nat}, x ∈ posRange n ↔ 1 ≤ x ∧ x ≤ n
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

theorem posRange_nodup : ∀ (n : Nat), (posRange n).Nodup
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


end Qsag
namespace Qsag
set_option autoImplicit false
namespace Weierstrass
abbrev IsPrime := IsPrimeNat
/-- Euclid's lemma (*Elements* VII.30). -/
theorem IsPrime.dvd_mul {p a b : Nat} (hp : IsPrime p) (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  rcases hp.2 (Nat.gcd p a) (Nat.gcd_dvd_left p a) with h1 | hpg
  · exact Or.inr (Nat.Coprime.dvd_of_dvd_mul_left h1 h)
  · have hd := Nat.gcd_dvd_right p a
    rw [hpg] at hd
    exact Or.inl hd

end Weierstrass

end Qsag

namespace Qsag

set_option autoImplicit false

namespace Weierstrass

/- `Weierstrass.IsPrime` and Euclid's lemma `IsPrime.dvd_mul` are the declarations of
   `ActiveMigrationZeroTest.lean`; this module certifies primes for that same predicate. -/

/-! ### Fermat's Little Theorem for `Weierstrass.IsPrime` -/

/-- Fermat's Little Theorem: `a ^ (q - 1) ≡ 1 (mod q)` for prime `q` and `¬ (q ∣ a)`.
    `Weierstrass.IsPrime` abbreviates `IsPrimeNat`, so this is `IsPrimeNat.pow_sub_one_mod`. -/
theorem IsPrime.pow_sub_one_mod {q a : Nat} (hq : IsPrime q) (hna : ¬ (q ∣ a)) :
    (a ^ (q - 1)) % q = 1 :=
  IsPrimeNat.pow_sub_one_mod hq hna

end Weierstrass

/-! ## Kernel-Reducible Fueled Modular Power & Euclidean GCD -/

abbrev strictEval := primalityStrictNat

private theorem strictEval_eq (n : Nat) (k : Nat → Nat) : strictEval n k = k n := by
  cases n <;> rfl

/-- Fueled binary modular exponentiation (`O(fuel)` squarings in `decide +kernel`). -/
abbrev powModFuel := modPowFuel

private theorem pow_two_mul_cert (b k : Nat) : b ^ (2 * k) = (b ^ k) * (b ^ k) := by
  rw [Nat.mul_comm 2 k, Nat.pow_mul, Nat.pow_succ, Nat.pow_one]

theorem powModFuel_eq_pow_mod :
    ∀ (fuel base exp m : Nat), exp < 2 ^ fuel → powModFuel fuel base exp m = (base ^ exp) % m := modPowFuel_eq_pow_mod

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
def allDistinctPrimes : List (Nat × Nat) → Bool
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


end Qsag
