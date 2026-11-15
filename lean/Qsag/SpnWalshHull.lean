module
/-
# Qsag.SpnWalshHull — linear trails are signed Fourier terms, the hull is their sum

Differential trail products are probabilities only in an explicit experiment
(`Qsag.SpnRoundConstantExperiment`). Linear trail products are different objects: they are
terms of an exact Fourier expansion, multiply without any independence assumption, and are
not events. This module proves that expansion for an explicit character pairing and applies
it to the actual two-lane round function.

Setting: a finite type listed once (`elems`), a symmetric bilinear pairing `dot` into `Bool`,
the character `wsgn (dot u x) = ±1`, and the unnormalized Walsh coefficient
`walsh f u w = Σ_x (-1)^(u·f(x) + w·x)` (correlation is `walsh / N`).

* `walsh_comp`: `Σ_v walsh g u v · walsh f v w = N · walsh (g ∘ f) u w`.
* `walshTrailSum_eq`: for a list of rounds, the sum over ALL intermediate mask sequences of
  the products of one-round coefficients equals `N^rounds` times the coefficient of the
  composition. One mask sequence is one trail; its product is a contribution, not a bound.
* `walsh_input_translate`: adding a constant before a map multiplies its coefficient by a
  sign. `spnRound128_walsh_constant_sign` is this for the actual `spnRound128`: the public
  round constants change only the signs with which trails add up, never the size of a
  single trail's contribution.
* `walsh_parseval`, `walsh_uniform_bound_ge_card`: `Σ_w walsh f u w ^ 2 = N^2` for every map,
  so no bound below `N` holds for all input masks. On the 256-bit state every uniform bound
  on the squared coefficient is at least `2^256` (squared correlation `2^-256`):
  `spn_state_walsh_uniform_bound_ge_2_256`. A single-trail product such as `(36/2^128)^72`
  is below this floor (`walsh_trail_product_below_parseval_floor`), so it cannot be a bound
  on the hull for all masks. This is forced by Parseval and is not an attack.
* `tooth_walsh_single_trail_is_not_the_hull`: a two-round example over `Bool` where one trail
  contributes `4` and the hull is `0`.

Not proved: any bound on the Walsh coefficients of `x^7` over `Tower128` (the Weil bound
`6·2^64` is a theorem of algebraic geometry, not derived here), hence no numeric bound on any
trail contribution or on the hull of the 48-round permutation.
-/
public import Qsag.SpnFixedConstantTrail
import all Qsag.SpnFixedConstantTrail
import all Qsag.SpnRoundConstantExperiment
import all Qsag.ParallelSeededSpnSecurity

public section
namespace Qsag
set_option autoImplicit false

/-! ## §1. Integer sums over lists -/

/-- The character value `(-1)^b`. -/
def wsgn (b : Bool) : Int := if b then -1 else 1

theorem wsgn_xor (a b : Bool) : wsgn (a ^^ b) = wsgn a * wsgn b := by
  cases a <;> cases b <;> rfl

theorem wsgn_mul_self (a : Bool) : wsgn a * wsgn a = 1 := by cases a <;> rfl

/-- Sum of an integer-valued function over a list. -/
def isum {α : Type} (f : α → Int) : List α → Int
  | [] => 0
  | x :: xs => f x + isum f xs

theorem isum_congr {α : Type} (f g : α → Int) :
    ∀ l : List α, (∀ x ∈ l, f x = g x) → isum f l = isum g l
  | [], _ => rfl
  | x :: xs, h => by
    show f x + isum f xs = g x + isum g xs
    rw [h x List.mem_cons_self, isum_congr f g xs fun y hy => h y (List.mem_cons_of_mem _ hy)]

theorem isum_eq_zero {α : Type} (f : α → Int) :
    ∀ l : List α, (∀ x ∈ l, f x = 0) → isum f l = 0
  | [], _ => rfl
  | x :: xs, h => by
    show f x + isum f xs = 0
    rw [h x List.mem_cons_self, isum_eq_zero f xs fun y hy => h y (List.mem_cons_of_mem _ hy)]
    rfl

theorem isum_add {α : Type} (f g : α → Int) :
    ∀ l : List α, isum (fun x => f x + g x) l = isum f l + isum g l
  | [] => rfl
  | x :: xs => by
    show f x + g x + isum (fun x => f x + g x) xs = f x + isum f xs + (g x + isum g xs)
    rw [isum_add f g xs, Int.add_assoc, Int.add_assoc, Int.add_left_comm (g x)]

theorem isum_mul_left {α : Type} (c : Int) (f : α → Int) :
    ∀ l : List α, isum (fun x => c * f x) l = c * isum f l
  | [] => (Int.mul_zero c).symm
  | x :: xs => by
    show c * f x + isum (fun x => c * f x) xs = c * (f x + isum f xs)
    rw [isum_mul_left c f xs, Int.mul_add]

theorem isum_mul_right {α : Type} (c : Int) (f : α → Int) :
    ∀ l : List α, isum (fun x => f x * c) l = isum f l * c
  | [] => (Int.zero_mul c).symm
  | x :: xs => by
    show f x * c + isum (fun x => f x * c) xs = (f x + isum f xs) * c
    rw [isum_mul_right c f xs, Int.add_mul]

theorem isum_swap {α β : Type} (F : α → β → Int) (l2 : List β) :
    ∀ l1 : List α, isum (fun x => isum (fun y => F x y) l2) l1 =
      isum (fun y => isum (fun x => F x y) l1) l2
  | [] => (isum_eq_zero _ l2 fun _ _ => rfl).symm
  | x :: xs => by
    show isum (fun y => F x y) l2 + isum (fun x => isum (fun y => F x y) l2) xs = _
    rw [isum_swap F l2 xs, ← isum_add]
    rfl

theorem isum_mul_isum {α β : Type} (A : α → Int) (B : β → Int) (l1 : List α) (l2 : List β) :
    isum A l1 * isum B l2 = isum (fun x => isum (fun y => A y * B x) l1) l2 := by
  rw [← isum_mul_left]
  exact isum_congr _ _ l2 fun x _ => (isum_mul_right (B x) A l1).symm

/-- A sum against the indicator of one listed point picks out that point's term. -/
theorem isum_indicator {α : Type} [DecidableEq α] (F : α → Int) (c : α) :
    ∀ l : List α, l.Nodup → c ∈ l → isum (fun y => if y = c then F y else 0) l = F c
  | [], _, h => absurd h List.not_mem_nil
  | y :: ys, hNd, hMem => by
    have hy := List.nodup_cons.mp hNd
    show (if y = c then F y else 0) + isum (fun y => if y = c then F y else 0) ys = F c
    by_cases hc : y = c
    · have hRest : isum (fun y => if y = c then F y else 0) ys = 0 :=
        isum_eq_zero _ ys fun z hz => ite_eq_right fun (hzc : z = c) =>
          hy.1 ((Eq.trans hzc hc.symm) ▸ hz)
      rw [ite_eq_left hc, hRest, hc, Int.add_zero]
    · have hIn : c ∈ ys := (List.mem_cons.mp hMem).resolve_left fun h => hc h.symm
      rw [ite_eq_right hc, isum_indicator F c ys hy.2 hIn, Int.zero_add]

theorem isum_const {α : Type} (c : Int) :
    ∀ l : List α, isum (fun _ => c) l = (l.length : Int) * c
  | [] => (Int.zero_mul c).symm
  | x :: xs => by
    show c + isum (fun _ => c) xs = ((xs.length + 1 : Nat) : Int) * c
    rw [isum_const c xs, Int.natCast_succ, Int.add_mul, Int.one_mul, Int.add_comm]

theorem isum_le {α : Type} (f g : α → Int) :
    ∀ l : List α, (∀ x ∈ l, f x ≤ g x) → isum f l ≤ isum g l
  | [], _ => Int.le_refl 0
  | x :: xs, h =>
    Int.add_le_add (h x List.mem_cons_self)
      (isum_le f g xs fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem isum_append {α : Type} (f : α → Int) (l2 : List α) :
    ∀ l1 : List α, isum f (l1 ++ l2) = isum f l1 + isum f l2
  | [] => (Int.zero_add _).symm
  | x :: xs => by
    show f x + isum f (xs ++ l2) = f x + isum f xs + isum f l2
    rw [isum_append f l2 xs, Int.add_assoc]

theorem isum_map {α β : Type} (f : β → Int) (g : α → β) :
    ∀ l : List α, isum f (l.map g) = isum (fun x => f (g x)) l
  | [] => rfl
  | x :: xs => by
    show f (g x) + isum f (xs.map g) = f (g x) + isum (fun x => f (g x)) xs
    rw [isum_map f g xs]

theorem isum_pairList {α : Type} (F : α × α → Int) (l2 : List α) :
    ∀ l1 : List α, isum F (l1.flatMap fun a => l2.map fun b => (a, b)) =
      isum (fun a => isum (fun b => F (a, b)) l2) l1
  | [] => rfl
  | x :: xs => by
    rw [List.flatMap_cons, isum_append, isum_map, isum_pairList F l2 xs]
    rfl

theorem int_mul_rearr (a s1 s2 b : Int) : (a * s1) * (s2 * b) = (a * b) * (s1 * s2) := by
  rw [Int.mul_assoc, Int.mul_assoc a b, ← Int.mul_assoc s1 s2 b, Int.mul_comm (s1 * s2) b]

theorem int_mul_rearr2 (a s1 b s2 : Int) : (a * s1) * (b * s2) = (a * b) * (s1 * s2) := by
  rw [Int.mul_assoc, Int.mul_left_comm s1 b s2, ← Int.mul_assoc]

/-! ## §2. Walsh coefficients, composition and the trail expansion -/

/-- A finite set of masks/points with a symmetric bilinear `Bool` pairing whose characters
    are orthogonal. `add` is the group law the pairing is linear in. -/
structure WalshSpace (α : Type) [DecidableEq α] where
  elems : List α
  dot : α → α → Bool
  add : α → α → α
  nodup : elems.Nodup
  complete : ∀ x : α, x ∈ elems
  dot_symm : ∀ a b : α, dot a b = dot b a
  dot_add : ∀ u a b : α, dot u (add a b) = (dot u a ^^ dot u b)
  orth : ∀ y y' : α, isum (fun v => wsgn (dot v y) * wsgn (dot v y')) elems =
    if y = y' then (elems.length : Int) else 0

/-- Unnormalized Walsh coefficient `Σ_x (-1)^(u·f(x) + w·x)`; the correlation of the output
    mask `u` with the input mask `w` is this divided by the number of points. -/
def walsh {α : Type} [DecidableEq α] (W : WalshSpace α) (f : α → α) (u w : α) : Int :=
  isum (fun x => wsgn (W.dot u (f x)) * wsgn (W.dot w x)) W.elems

/-- **Composition.** Summing the products of coefficients over the intermediate mask gives
    `N` times the coefficient of the composition. No probability is involved. -/
theorem walsh_comp {α : Type} [DecidableEq α] (W : WalshSpace α) (f g : α → α) (u w : α) :
    isum (fun v => walsh W g u v * walsh W f v w) W.elems =
      (W.elems.length : Int) * walsh W (fun x => g (f x)) u w := by
  have h1 : isum (fun v => walsh W g u v * walsh W f v w) W.elems =
      isum (fun v => isum (fun x => isum (fun y =>
        (wsgn (W.dot u (g y)) * wsgn (W.dot v y)) *
          (wsgn (W.dot v (f x)) * wsgn (W.dot w x))) W.elems) W.elems) W.elems :=
    isum_congr _ _ _ fun v _ => isum_mul_isum _ _ _ _
  have h2 := isum_swap (fun v x => isum (fun y =>
      (wsgn (W.dot u (g y)) * wsgn (W.dot v y)) *
        (wsgn (W.dot v (f x)) * wsgn (W.dot w x))) W.elems) W.elems W.elems
  have h3 : isum (fun x => isum (fun v => isum (fun y =>
        (wsgn (W.dot u (g y)) * wsgn (W.dot v y)) *
          (wsgn (W.dot v (f x)) * wsgn (W.dot w x))) W.elems) W.elems) W.elems =
      isum (fun x => (wsgn (W.dot u (g (f x))) * wsgn (W.dot w x)) *
        (W.elems.length : Int)) W.elems := by
    apply isum_congr
    intro x _
    rw [isum_swap (fun v y => (wsgn (W.dot u (g y)) * wsgn (W.dot v y)) *
      (wsgn (W.dot v (f x)) * wsgn (W.dot w x))) W.elems W.elems]
    have hInner : isum (fun y => isum (fun v =>
          (wsgn (W.dot u (g y)) * wsgn (W.dot v y)) *
            (wsgn (W.dot v (f x)) * wsgn (W.dot w x))) W.elems) W.elems =
        isum (fun y => if y = f x then
          (wsgn (W.dot u (g y)) * wsgn (W.dot w x)) * (W.elems.length : Int) else 0) W.elems := by
      apply isum_congr
      intro y _
      have hO := W.orth y (f x)
      have hT : isum (fun v => (wsgn (W.dot u (g y)) * wsgn (W.dot v y)) *
            (wsgn (W.dot v (f x)) * wsgn (W.dot w x))) W.elems =
          (wsgn (W.dot u (g y)) * wsgn (W.dot w x)) *
            isum (fun v => wsgn (W.dot v y) * wsgn (W.dot v (f x))) W.elems := by
        rw [← isum_mul_left]
        exact isum_congr _ _ _ fun v _ => int_mul_rearr _ _ _ _
      rw [hT, hO]
      by_cases hy : y = f x
      · rw [ite_eq_left hy, ite_eq_left hy]
      · rw [ite_eq_right hy, ite_eq_right hy, Int.mul_zero]
    rw [hInner]
    exact isum_indicator (fun y => (wsgn (W.dot u (g y)) * wsgn (W.dot w x)) *
      (W.elems.length : Int)) (f x) W.elems W.nodup (W.complete (f x))
  rw [h1, h2, h3, isum_mul_right, Int.mul_comm]
  rfl

/-- The identity map has coefficient `N` on the diagonal and `0` elsewhere. -/
theorem walsh_id {α : Type} [DecidableEq α] (W : WalshSpace α) (u w : α) :
    walsh W (fun x => x) u w = if u = w then (W.elems.length : Int) else 0 := by
  rw [← W.orth u w]
  exact isum_congr _ _ _ fun x _ => by rw [W.dot_symm u x, W.dot_symm w x]

/-- Rounds applied in list order (head first). -/
def composeRounds {α : Type} : List (α → α) → α → α
  | [], x => x
  | f :: fs, x => composeRounds fs (f x)

/-- Sum over every sequence of intermediate masks (every linear trail) of the product of the
    one-round coefficients along it. -/
def walshTrailSum {α : Type} [DecidableEq α] (W : WalshSpace α) : List (α → α) → α → α → Int
  | [], u, w => if u = w then (W.elems.length : Int) else 0
  | f :: fs, u, w => isum (fun v => walshTrailSum W fs u v * walsh W f v w) W.elems

/-- **Linear hull = signed sum of trail contributions**, exactly, for any list of rounds. -/
theorem walshTrailSum_eq {α : Type} [DecidableEq α] (W : WalshSpace α) :
    ∀ (fs : List (α → α)) (u w : α),
      walshTrailSum W fs u w =
        (W.elems.length : Int) ^ fs.length * walsh W (composeRounds fs) u w
  | [], u, w => by
    show (if u = w then (W.elems.length : Int) else 0) = _
    rw [← walsh_id W u w, List.length_nil, Int.pow_zero, Int.one_mul]
    rfl
  | f :: fs, u, w => by
    show isum (fun v => walshTrailSum W fs u v * walsh W f v w) W.elems = _
    have hStep : isum (fun v => walshTrailSum W fs u v * walsh W f v w) W.elems =
        (W.elems.length : Int) ^ fs.length *
          isum (fun v => walsh W (composeRounds fs) u v * walsh W f v w) W.elems := by
      rw [← isum_mul_left]
      exact isum_congr _ _ _ fun v _ => by rw [walshTrailSum_eq W fs u v, Int.mul_assoc]
    rw [hStep, walsh_comp, ← Int.mul_assoc, List.length_cons, Int.pow_succ]
    rfl

/-- Adding a constant after a map multiplies the coefficient by a sign. -/
theorem walsh_output_translate {α : Type} [DecidableEq α] (W : WalshSpace α) (f : α → α)
    (k u w : α) :
    walsh W (fun x => W.add (f x) k) u w = wsgn (W.dot u k) * walsh W f u w := by
  unfold walsh
  rw [← isum_mul_left]
  apply isum_congr
  intro x _
  rw [W.dot_add, wsgn_xor, Int.mul_comm (wsgn (W.dot u (f x))), Int.mul_assoc]

/-- Adding a constant before a map multiplies the coefficient by a sign (of the input mask).
    Derived from `walsh_comp` and orthogonality; no reindexing of the sum is used. -/
theorem walsh_input_translate {α : Type} [DecidableEq α] (W : WalshSpace α) (f : α → α)
    (k u w : α) :
    walsh W (fun x => f (W.add x k)) u w = wsgn (W.dot w k) * walsh W f u w := by
  have hPos : (W.elems.length : Int) ≠ 0 := by
    cases hE : W.elems with
    | nil => exact absurd (hE ▸ W.complete k) List.not_mem_nil
    | cons x xs =>
      have hp : (0 : Int) < ((x :: xs).length : Int) := Int.natCast_pos.mpr (Nat.succ_pos _)
      exact fun h0 => Int.lt_irrefl 0 (h0 ▸ hp)
  have hShift : ∀ v : α, walsh W (fun x => W.add x k) v w =
      wsgn (W.dot v k) * (if v = w then (W.elems.length : Int) else 0) := by
    intro v
    have h := walsh_output_translate W (fun x => x) k v w
    rw [walsh_id] at h
    exact h
  have hC := walsh_comp W (fun x => W.add x k) f u w
  have hSum : isum (fun v => walsh W f u v * walsh W (fun x => W.add x k) v w) W.elems =
      walsh W f u w * (wsgn (W.dot w k) * (W.elems.length : Int)) := by
    have hI := isum_indicator (fun v => walsh W f u v * (wsgn (W.dot v k) * (W.elems.length : Int)))
      w W.elems W.nodup (W.complete w)
    rw [← hI]
    apply isum_congr
    intro v _
    rw [hShift v]
    by_cases hv : v = w
    · rw [ite_eq_left hv, ite_eq_left hv]
    · rw [ite_eq_right hv, ite_eq_right hv, Int.mul_zero, Int.mul_zero]
  rw [hSum] at hC
  apply Int.eq_of_mul_eq_mul_left hPos
  rw [← hC, Int.mul_left_comm, Int.mul_comm (walsh W f u w)]
  exact Int.mul_left_comm _ _ _

/-! ## §3. Parseval and the floor for uniform bounds -/

/-- **Parseval.** For every map and every output mask, the squared coefficients over all
    input masks sum to `N²`. -/
theorem walsh_parseval {α : Type} [DecidableEq α] (W : WalshSpace α) (f : α → α) (u : α) :
    isum (fun w => walsh W f u w * walsh W f u w) W.elems =
      (W.elems.length : Int) * (W.elems.length : Int) := by
  have h1 : isum (fun w => walsh W f u w * walsh W f u w) W.elems =
      isum (fun w => isum (fun x => isum (fun y =>
        (wsgn (W.dot u (f y)) * wsgn (W.dot w y)) *
          (wsgn (W.dot u (f x)) * wsgn (W.dot w x))) W.elems) W.elems) W.elems :=
    isum_congr _ _ _ fun w _ => isum_mul_isum _ _ _ _
  have h2 := isum_swap (fun w x => isum (fun y =>
      (wsgn (W.dot u (f y)) * wsgn (W.dot w y)) *
        (wsgn (W.dot u (f x)) * wsgn (W.dot w x))) W.elems) W.elems W.elems
  have h3 : isum (fun x => isum (fun w => isum (fun y =>
        (wsgn (W.dot u (f y)) * wsgn (W.dot w y)) *
          (wsgn (W.dot u (f x)) * wsgn (W.dot w x))) W.elems) W.elems) W.elems =
      isum (fun _ => (W.elems.length : Int)) W.elems := by
    apply isum_congr
    intro x _
    rw [isum_swap (fun w y => (wsgn (W.dot u (f y)) * wsgn (W.dot w y)) *
      (wsgn (W.dot u (f x)) * wsgn (W.dot w x))) W.elems W.elems]
    have hInner : isum (fun y => isum (fun w =>
          (wsgn (W.dot u (f y)) * wsgn (W.dot w y)) *
            (wsgn (W.dot u (f x)) * wsgn (W.dot w x))) W.elems) W.elems =
        isum (fun y => if y = x then
          (wsgn (W.dot u (f y)) * wsgn (W.dot u (f x))) * (W.elems.length : Int) else 0) W.elems := by
      apply isum_congr
      intro y _
      have hO := W.orth y x
      have hT : isum (fun w => (wsgn (W.dot u (f y)) * wsgn (W.dot w y)) *
            (wsgn (W.dot u (f x)) * wsgn (W.dot w x))) W.elems =
          (wsgn (W.dot u (f y)) * wsgn (W.dot u (f x))) *
            isum (fun w => wsgn (W.dot w y) * wsgn (W.dot w x)) W.elems := by
        rw [← isum_mul_left]
        exact isum_congr _ _ _ fun w _ => int_mul_rearr2 _ _ _ _
      rw [hT, hO]
      by_cases hy : y = x
      · rw [ite_eq_left hy, ite_eq_left hy]
      · rw [ite_eq_right hy, ite_eq_right hy, Int.mul_zero]
    rw [hInner, isum_indicator (fun y => (wsgn (W.dot u (f y)) * wsgn (W.dot u (f x))) *
      (W.elems.length : Int)) x W.elems W.nodup (W.complete x), wsgn_mul_self, Int.one_mul]
  rw [h1, h2, h3, isum_const]

/-- **Floor.** If `B` bounds the squared coefficient for every input mask, then `B ≥ N`:
    some input mask has squared correlation at least `1/N` with any given output mask. -/
theorem walsh_uniform_bound_ge_card {α : Type} [DecidableEq α] (W : WalshSpace α)
    (f : α → α) (u : α) (B : Int)
    (hB : ∀ w ∈ W.elems, walsh W f u w * walsh W f u w ≤ B) :
    (W.elems.length : Int) ≤ B := by
  have hPos : (0 : Int) < (W.elems.length : Int) := by
    cases hE : W.elems with
    | nil => exact absurd (hE ▸ W.complete u) List.not_mem_nil
    | cons x xs => exact Int.natCast_pos.mpr (Nat.succ_pos _)
  have hSum := isum_le _ (fun _ => B) W.elems hB
  rw [walsh_parseval, isum_const] at hSum
  exact Int.le_of_mul_le_mul_left hSum hPos

/-! ## §4. The bit pairing on the Wiedemann tower and the actual round function -/

/-- Coordinatewise inner product of tower elements (all `2^k` bit coordinates). -/
def towerDot : (k : Nat) → TowerElem k → TowerElem k → Bool
  | 0, a, b => a && b
  | k + 1, a, b => towerDot k a.1 b.1 ^^ towerDot k a.2 b.2

theorem towerDot_symm : ∀ (k : Nat) (a b : TowerElem k), towerDot k a b = towerDot k b a
  | 0, a, b => Bool.and_comm a b
  | k + 1, a, b => by
    show (towerDot k a.1 b.1 ^^ towerDot k a.2 b.2) = (towerDot k b.1 a.1 ^^ towerDot k b.2 a.2)
    rw [towerDot_symm k a.1 b.1, towerDot_symm k a.2 b.2]

theorem bxor_swap (p q r s : Bool) : ((p ^^ q) ^^ (r ^^ s)) = ((p ^^ r) ^^ (q ^^ s)) := by
  cases p <;> cases q <;> cases r <;> cases s <;> rfl

theorem towerDot_add : ∀ (k : Nat) (u a b : TowerElem k),
    towerDot k u (towerAdd k a b) = (towerDot k u a ^^ towerDot k u b)
  | 0, u, a, b => by cases u <;> cases a <;> cases b <;> rfl
  | k + 1, u, a, b => by
    show (towerDot k u.1 (towerAdd k a.1 b.1) ^^ towerDot k u.2 (towerAdd k a.2 b.2)) =
      ((towerDot k u.1 a.1 ^^ towerDot k u.2 a.2) ^^ (towerDot k u.1 b.1 ^^ towerDot k u.2 b.2))
    rw [towerDot_add k u.1, towerDot_add k u.2, bxor_swap]

theorem towerDot_orth : ∀ (k : Nat) (y y' : TowerElem k),
    isum (fun v => wsgn (towerDot k v y) * wsgn (towerDot k v y')) (towerAll k) =
      if y = y' then ((towerAll k).length : Int) else 0
  | 0, y, y' => by cases y <;> cases y' <;> rfl
  | k + 1, y, y' => by
    show isum (fun v => wsgn (towerDot k v.1 y.1 ^^ towerDot k v.2 y.2) *
        wsgn (towerDot k v.1 y'.1 ^^ towerDot k v.2 y'.2)) (rcPairs (towerAll k)) =
      if y = y' then ((rcPairs (towerAll k)).length : Int) else 0
    have hSplit : isum (fun v => wsgn (towerDot k v.1 y.1 ^^ towerDot k v.2 y.2) *
        wsgn (towerDot k v.1 y'.1 ^^ towerDot k v.2 y'.2)) (rcPairs (towerAll k)) =
        isum (fun a => wsgn (towerDot k a y.1) * wsgn (towerDot k a y'.1)) (towerAll k) *
          isum (fun b => wsgn (towerDot k b y.2) * wsgn (towerDot k b y'.2)) (towerAll k) := by
      unfold rcPairs
      rw [isum_pairList, ← isum_mul_right]
      apply isum_congr
      intro a _
      rw [← isum_mul_left]
      apply isum_congr
      intro b _
      show wsgn (towerDot k a y.1 ^^ towerDot k b y.2) *
        wsgn (towerDot k a y'.1 ^^ towerDot k b y'.2) = _
      rw [wsgn_xor, wsgn_xor, int_mul_rearr2]
    rw [hSplit, towerDot_orth k y.1 y'.1, towerDot_orth k y.2 y'.2, rcPairs_length,
      Int.natCast_mul]
    by_cases h : y = y'
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right h]
      by_cases h1 : y.1 = y'.1
      · have h2 : ¬ y.2 = y'.2 := fun h2 => h (Prod.ext h1 h2)
        rw [ite_eq_right h2, Int.mul_zero]
      · rw [ite_eq_right h1, Int.zero_mul]

/-- The tower with its bit pairing is a `WalshSpace` (level 7: one lane; level 8: the
    256-bit two-lane state, since `TowerElem 8 = Tower128 × Tower128`). -/
def towerWalsh (k : Nat) : WalshSpace (TowerElem k) where
  elems := towerAll k
  dot := towerDot k
  add := towerAdd k
  nodup := towerAll_nodup k
  complete := towerAll_complete k
  dot_symm := towerDot_symm k
  dot_add := towerDot_add k
  orth := towerDot_orth k

/-- **Round constants change only signs.** The Walsh coefficient of the actual round with
    constant `rc` is the coefficient of the constant-free round times `(-1)^(w·rc)`. Hence
    every one-round coefficient, and every product of them along a trail, has a magnitude
    that does not depend on the public constants; the constants decide how trails cancel. -/
theorem spnRound128_walsh_constant_sign (mdsA mdsB : Tower128) (rc u w : TowerElem 8) :
    walsh (towerWalsh 8) (spnRound128 mdsA mdsB rc) u w =
      wsgn (towerDot 8 w rc) *
        walsh (towerWalsh 8) (spnRound128 mdsA mdsB (towerZero 7, towerZero 7)) u w := by
  refine Eq.trans ?_ (walsh_input_translate (towerWalsh 8)
    (spnRound128 mdsA mdsB (towerZero 7, towerZero 7)) rc u w)
  apply congrArg (fun f => walsh (towerWalsh 8) f u w)
  funext x
  show spnRound128 mdsA mdsB rc x =
    spnRound128 mdsA mdsB (towerZero 7, towerZero 7) (towerAdd 7 x.1 rc.1, towerAdd 7 x.2 rc.2)
  unfold spnRound128
  rw [towerAdd_zero, towerAdd_zero]

/-- The exact trail expansion for the actual rounds: for any constant list, the sum over all
    intermediate 256-bit mask sequences of the products of one-round coefficients is
    `N^rounds` times the coefficient of the composed permutation. -/
theorem spn_walsh_hull_expansion (mdsA mdsB : Tower128) (ks : List (TowerElem 8))
    (u w : TowerElem 8) :
    walshTrailSum (towerWalsh 8) (ks.map fun rc => spnRound128 mdsA mdsB rc) u w =
      ((towerWalsh 8).elems.length : Int) ^ ks.length *
        walsh (towerWalsh 8)
          (composeRounds (ks.map fun rc => spnRound128 mdsA mdsB rc)) u w := by
  exact (walshTrailSum_eq (towerWalsh 8) _ u w).trans
    (congrArg (fun n => ((towerWalsh 8).elems.length : Int) ^ n *
      walsh (towerWalsh 8) (composeRounds (ks.map fun rc => spnRound128 mdsA mdsB rc)) u w)
      (List.length_map _))

/-- `composeRounds` over the mapped constant list is the permutation `spnRunList`. -/
theorem composeRounds_spnRound128 (mdsA mdsB : Tower128) :
    ∀ (ks : List (Tower128 × Tower128)) (x : Tower128 × Tower128),
      composeRounds (ks.map fun rc => spnRound128 mdsA mdsB rc) x = spnRunList mdsA mdsB ks x
  | [], _ => rfl
  | rc :: rest, x => composeRounds_spnRound128 mdsA mdsB rest (spnRound128 mdsA mdsB rc x)

/-- **Parseval floor on the 256-bit state.** For every map of the two-lane state (in
    particular the 48-round permutation under any constants) and every output mask, a bound
    valid for all input masks on the squared Walsh coefficient is at least `2^256`. -/
theorem spn_state_walsh_uniform_bound_ge_2_256 (f : TowerElem 8 → TowerElem 8)
    (u : TowerElem 8) (B : Int)
    (hB : ∀ w : TowerElem 8, walsh (towerWalsh 8) f u w * walsh (towerWalsh 8) f u w ≤ B) :
    ((2 ^ 2 ^ 8 : Nat) : Int) ≤ B := by
  have h := walsh_uniform_bound_ge_card (towerWalsh 8) f u B fun w _ => hB w
  rw [show (towerWalsh 8).elems.length = 2 ^ 2 ^ 8 from towerAll_length 8] at h
  exact h

/-- A product of 72 per-box squared-correlation bounds `36/2^128` is below the `2^-256`
    Parseval floor of the 256-bit state. Such a product can bound one trail's contribution
    (given a per-box Walsh bound), never the hull for all masks. -/
theorem walsh_trail_product_below_parseval_floor : 36 ^ 72 * 2 ^ 256 < (2 ^ 128) ^ 72 := by
  decide

/-! ## §5. One trail is not the hull -/

/-- `Bool` with `&&` as pairing and `^^` as addition. -/
def boolWalsh : WalshSpace Bool where
  elems := [false, true]
  dot := fun a b => a && b
  add := fun a b => a ^^ b
  nodup := by decide
  complete := fun x => by cases x <;> decide
  dot_symm := fun a b => by cases a <;> cases b <;> rfl
  dot_add := fun u a b => by cases u <;> cases a <;> cases b <;> rfl
  orth := fun y y' => by cases y <;> cases y' <;> rfl

/-- Two rounds over `Bool`: the identity, then the constant map. With output and input mask
    `true`, the trail through the intermediate mask `false` contributes `2 · 2 = 4`, the trail
    through `true` contributes `-2 · 2 = -4`, and the hull (their sum) is `0`. A single
    trail's size says nothing about the hull, in either direction. -/
theorem tooth_walsh_single_trail_is_not_the_hull :
    walsh boolWalsh (fun _ => true) true false * walsh boolWalsh (fun x => x) false true = 0 ∧
    walsh boolWalsh (fun _ => true) true true * walsh boolWalsh (fun x => x) true true = 0 ∧
    walsh boolWalsh (fun x => !x) true true * walsh boolWalsh (fun x => x) true true = -4 ∧
    walsh boolWalsh (fun x => x) true true * walsh boolWalsh (fun x => x) true true = 4 ∧
    walshTrailSum boolWalsh [fun x => x, fun _ => true] true true = 0 := by
  decide

end Qsag
end

#verify_constructive
  Qsag.walsh_comp
  Qsag.walshTrailSum_eq
  Qsag.walsh_input_translate
  Qsag.walsh_parseval
  Qsag.walsh_uniform_bound_ge_card
  Qsag.towerDot_orth
  Qsag.spnRound128_walsh_constant_sign
  Qsag.spn_walsh_hull_expansion
  Qsag.spn_state_walsh_uniform_bound_ge_2_256
  Qsag.walsh_trail_product_below_parseval_floor
  Qsag.tooth_walsh_single_trail_is_not_the_hull
