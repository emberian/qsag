module
/-
# Qsag.Poseidon2 — Algebraic Width-12 Goldilocks `Poseidon2` Permutation & 256-Bit Sponge

Self-contained Lean 4.35 algebraic sponge specification (`Init` + `Qsag.Goldilocks` + `Qsag.Keccak`):
1. Degree-7 S-box bijection (`sbox7_bijective`) via $d_{\text{inv}} = \frac{4(p - 1) + 1}{7}$
   and Fermat's Little Theorem (`IsPrimeNat.pow_sub_one_mod`).
2. Full Width-12 (`rate = 8, capacity = 4` = 256-bit capacity) `Poseidon2` permutation (`poseidon2Perm12`)
   with proved invertible Grassi et al. external block-circulant diffusion $M_E = \text{circ}(2 M_4, M_4, M_4)$
   ($4 \times 4$ MDS $M_4$ of branch number $5$, external branch number $10$; `applyMEInv_applyME`,
   `applyME_applyMEInv`), Sherman–Morrison invertible internal $M_I = \mathbf{1}\mathbf{1}^T + \text{diag}(v)$
   (`applyMIInv_applyMI`, `applyMI_applyMIInv`), non-affine round constants
   (`poseidon2ConstAt_not_affine`), and full permutation bijection (`poseidon2Perm12_bijective`).
3. Canonical `< 2^56` limb framing (`bytesToLimbs56_injective`), multi-rate `10*1` sponge padding
   (`poseidon2Pad_injective`, `poseidon2PadBytes_injective`), and 32-byte `poseidon2Hash32` with
   build-time conformance vectors matching `crates/qsag-core/src/sponge/poseidon2.rs`.
-/

public import Qsag.Goldilocks
public import Qsag.Keccak

public section
namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd

set_option autoImplicit false

/-! ## 1. Goldilocks Power Map $x \mapsto x^7 \pmod p$ & Exact Inverse $d_{\text{inv}}$ (`sbox7_bijective`) -/

def poseidon2DInv : Nat := 10540996611094048183

theorem goldilocksPred_coprime_seven (x : Goldilocks) :
    7 * poseidon2DInv = 4 * (goldilocksPrime - 1) + 1 ∧
    Nat.gcd 7 (goldilocksPrime - 1) = 1 ∧
    goldilocksPrime - 1 = (2 ^ 32) * 3 * 5 * 17 * 257 * 65537 ∧
    x.val < goldilocksPrime := by
  have hBez : 7 * poseidon2DInv = 4 * (goldilocksPrime - 1) + 1 := rfl
  refine ⟨hBez, ?_, rfl, x.isLt⟩
  obtain ⟨k1, hk1⟩ := Nat.gcd_dvd_left 7 (goldilocksPrime - 1)
  obtain ⟨k2, hk2⟩ := Nat.gcd_dvd_right 7 (goldilocksPrime - 1)
  let g := Nat.gcd 7 (goldilocksPrime - 1)
  have h1 : g ∣ 1 := ⟨k1 * poseidon2DInv - 4 * k2, by
    have h7 : 7 * poseidon2DInv = g * (k1 * poseidon2DInv) := by
      calc 7 * poseidon2DInv = (g * k1) * poseidon2DInv := by rw [← hk1]
      _ = g * (k1 * poseidon2DInv) := Nat.mul_assoc _ _ _
    have h4 : 4 * (goldilocksPrime - 1) = g * (4 * k2) := by
      calc 4 * (goldilocksPrime - 1) = 4 * (g * k2) := by rw [← hk2]
      _ = g * (4 * k2) := by rw [← Nat.mul_assoc, Nat.mul_comm 4 g, Nat.mul_assoc]
    rw [Nat.mul_sub_left_distrib, ← h7, ← h4]
    omega⟩
  exact Nat.eq_one_of_dvd_one h1

/-- Degree-7 algebraic S-box $x \mapsto x^7$ over `Goldilocks` (depth-3 multiplication tree). -/
@[expose] def sbox7 (x : Goldilocks) : Goldilocks :=
  let x2 := Goldilocks.mul x x
  let x3 := Goldilocks.mul x2 x
  let x4 := Goldilocks.mul x2 x2
  Goldilocks.mul x3 x4

theorem sbox7_val (x : Goldilocks) :
    (sbox7 x).val = (x.val ^ 7) % goldilocksPrime := by
  have hx2 : (Goldilocks.mul x x).val = (x.val * x.val) % goldilocksPrime := Goldilocks.mul_val x x
  have hx3 : (Goldilocks.mul (Goldilocks.mul x x) x).val = (x.val * x.val * x.val) % goldilocksPrime := by
    rw [Goldilocks.mul_val, hx2, Nat.mod_mul_mod]
  have hx4 : (Goldilocks.mul (Goldilocks.mul x x) (Goldilocks.mul x x)).val =
      ((x.val * x.val) * (x.val * x.val)) % goldilocksPrime := by
    rw [Goldilocks.mul_val, hx2, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
  unfold sbox7
  dsimp only
  rw [Goldilocks.mul_val, hx3, hx4, Nat.mul_mod, Nat.mod_mod, Nat.mod_mod, ← Nat.mul_mod]
  congr 1
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_assoc]

def goldilocksPowAux : Nat → Goldilocks → Nat → Goldilocks
  | 0, _, _ => Goldilocks.one
  | fuel + 1, base, exp =>
    if exp = 0 then Goldilocks.one
    else
      let half := goldilocksPowAux fuel base (exp / 2)
      let sq := Goldilocks.mul half half
      if exp % 2 = 1 then Goldilocks.mul sq base else sq

def goldilocksPow (x : Goldilocks) (exp : Nat) : Goldilocks :=
  if x.val == 0 then
    if exp == 0 then Goldilocks.one else Goldilocks.zero
  else
    goldilocksPowAux (Nat.log2 exp + 1) x exp

@[expose] def sbox7Inv (x : Goldilocks) : Goldilocks :=
  goldilocksPow x poseidon2DInv

private theorem pow_two_mul_nat (b k : Nat) : b ^ (2 * k) = (b ^ k) * (b ^ k) := by
  rw [Nat.mul_comm 2 k, Nat.pow_mul, Nat.pow_succ, Nat.pow_one]

theorem goldilocksPowAux_val (fuel : Nat) (base : Goldilocks) :
    ∀ (exp : Nat), exp < 2 ^ fuel →
      (goldilocksPowAux fuel base exp).val = (base.val ^ exp) % goldilocksPrime := by
  induction fuel with
  | zero =>
    intro exp hlt
    have he0 : exp = 0 := by simp at hlt; omega
    subst he0
    rfl
  | succ fuel ih =>
    intro exp hlt
    simp only [goldilocksPowAux]
    if h0 : exp = 0 then
      subst h0
      rfl
    else
      simp only [h0, ↓reduceIte]
      have hexpHalf : exp / 2 < 2 ^ fuel := by
        rw [Nat.pow_succ] at hlt
        omega
      have ihHalf := ih (exp / 2) hexpHalf
      let half := goldilocksPowAux fuel base (exp / 2)
      have hsq : (Goldilocks.mul half half).val = (base.val ^ (2 * (exp / 2))) % goldilocksPrime := by
        rw [Goldilocks.mul_val, ihHalf, ← Nat.mul_mod, ← pow_two_mul_nat]
      have hmod2 : exp % 2 = 0 ∨ exp % 2 = 1 := by omega
      rcases hmod2 with hr0 | hr1
      · simp only [hr0, show ¬ (0 = 1) by decide, ↓reduceIte]
        have hexp : 2 * (exp / 2) = exp := by omega
        rw [hsq, hexp]
      · simp only [hr1, ↓reduceIte]
        have hexp : exp = 2 * (exp / 2) + 1 := by omega
        change (Goldilocks.mul (Goldilocks.mul half half) base).val = _
        rw [Goldilocks.mul_val, hsq, Nat.mod_mul_mod]
        conv => rhs; rw [hexp, Nat.pow_add, Nat.pow_one]

theorem goldilocksPow_val (x : Goldilocks) (exp : Nat) :
    (goldilocksPow x exp).val = (x.val ^ exp) % goldilocksPrime := by
  unfold goldilocksPow
  cases hx0 : (x.val == 0)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hFuel : exp < 2 ^ (Nat.log2 exp + 1) := by
      by_cases he : exp = 0
      · subst he; decide
      · exact Nat.lt_log2_self
    exact goldilocksPowAux_val (Nat.log2 exp + 1) x exp hFuel
  · simp only [↓reduceIte]
    have hxEq : x.val = 0 := eq_of_beq hx0
    rw [hxEq]
    cases he0 : (exp == 0)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have heNe : exp ≠ 0 := by intro h; subst h; simp at he0
      rw [Nat.zero_pow (Nat.pos_of_ne_zero heNe), Nat.zero_mod]
      rfl
    · simp only [↓reduceIte]
      have heEq : exp = 0 := eq_of_beq he0
      rw [heEq, Nat.pow_zero]
      rfl

theorem sbox7Inv_val (x : Goldilocks) :
    (sbox7Inv x).val = (x.val ^ poseidon2DInv) % goldilocksPrime :=
  goldilocksPow_val x poseidon2DInv

private theorem pow_mod_congr_nat {x y m : Nat} (h : x % m = y % m) (k : Nat) :
    (x ^ k) % m = (y ^ k) % m := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, ih, h, ← Nat.mul_mod]

private theorem pow4_mod_one {u p : Nat} (hp : 1 < p) (hu : u % p = 1) :
    (u ^ 4) % p = 1 := by
  have h2 : u ^ 2 = u * u := by
    rw [show (2 : Nat) = 1 + 1 from rfl, Nat.pow_add, Nat.pow_one]
  have h4 : u ^ 4 = (u * u) * (u * u) := by
    rw [show (4 : Nat) = 2 + 2 from rfl, Nat.pow_add, h2]
  have hu2 : (u * u) % p = 1 := by
    rw [Nat.mul_mod, hu, Nat.one_mul, Nat.mod_eq_of_lt hp]
  rw [h4, Nat.mul_mod, hu2, Nat.one_mul, Nat.mod_eq_of_lt hp]

private theorem pow_seven_dInv_mod (a : Goldilocks) :
    (a.val ^ (7 * poseidon2DInv)) % goldilocksPrime = a.val := by
  if ha0 : a.val = 0 then
    have hexp0 : 7 * poseidon2DInv = (4 * (goldilocksPrime - 1)) + 1 := rfl
    rw [ha0, hexp0, Nat.zero_pow (by omega), Nat.zero_mod]
  else
    have hndvd : ¬ (goldilocksPrime ∣ a.val) := fun hd => by
      have hle := Nat.le_of_dvd (by omega) hd
      have hlt := a.isLt
      omega
    have hflt : (a.val ^ (goldilocksPrime - 1)) % goldilocksPrime = 1 :=
      (goldilocksPrime_isPrime ()).pow_sub_one_mod hndvd
    have hexp : 7 * poseidon2DInv = (goldilocksPrime - 1) * 4 + 1 := rfl
    have hp1 : 1 < goldilocksPrime := by decide
    have hu4 : ((a.val ^ (goldilocksPrime - 1)) ^ 4) % goldilocksPrime = 1 :=
      pow4_mod_one hp1 hflt
    rw [hexp, Nat.pow_add, Nat.pow_mul, Nat.pow_one, Nat.mul_mod, hu4,
        Nat.one_mul, Nat.mod_mod, Nat.mod_eq_of_lt a.isLt]

theorem sbox7Inv_sbox7 (x : Goldilocks) : sbox7Inv (sbox7 x) = x := by
  apply Goldilocks.ext
  have hCongr : (sbox7 x).val % goldilocksPrime = (x.val ^ 7) % goldilocksPrime := by
    rw [sbox7_val, Nat.mod_mod]
  rw [sbox7Inv_val, pow_mod_congr_nat hCongr poseidon2DInv, ← Nat.pow_mul, pow_seven_dInv_mod]

theorem sbox7_sbox7Inv (x : Goldilocks) : sbox7 (sbox7Inv x) = x := by
  apply Goldilocks.ext
  have hCongr : (sbox7Inv x).val % goldilocksPrime = (x.val ^ poseidon2DInv) % goldilocksPrime := by
    rw [sbox7Inv_val, Nat.mod_mod]
  rw [sbox7_val, pow_mod_congr_nat hCongr 7, ← Nat.pow_mul, Nat.mul_comm poseidon2DInv 7, pow_seven_dInv_mod]

/-- **Goldilocks Degree-7 S-Box Bijection Theorem (`sbox7_bijective`)**. -/
theorem sbox7_bijective (x y : Goldilocks) :
    sbox7Inv (sbox7 x) = x ∧
    sbox7 (sbox7Inv y) = y ∧
    (sbox7 x = sbox7 y ↔ x = y) ∧
    (∃ z : Goldilocks, sbox7 z = y) := by
  refine ⟨sbox7Inv_sbox7 x, sbox7_sbox7Inv y, ?_, ⟨sbox7Inv y, sbox7_sbox7Inv y⟩⟩
  constructor
  · intro h
    have hInv := congrArg sbox7Inv h
    rwa [sbox7Inv_sbox7, sbox7Inv_sbox7] at hInv
  · intro h
    subst h
    rfl

/-! ## 2. Width-12 State (`rate = 8, capacity = 4`) & Invertible Linear Layers $M_E, M_I$ -/

structure Lane4 where
  x0 : Goldilocks
  x1 : Goldilocks
  x2 : Goldilocks
  x3 : Goldilocks
  deriving DecidableEq, Repr

theorem Lane4.ext {a b : Lane4}
    (h0 : a.x0 = b.x0) (h1 : a.x1 = b.x1) (h2 : a.x2 = b.x2) (h3 : a.x3 = b.x3) : a = b := by
  cases a; cases b; simp only at *; subst h0 h1 h2 h3; rfl

structure Poseidon2State12 where
  b0 : Lane4
  b1 : Lane4
  b2 : Lane4
  deriving DecidableEq, Repr

theorem Poseidon2State12.ext {s t : Poseidon2State12}
    (h0 : s.b0 = t.b0) (h1 : s.b1 = t.b1) (h2 : s.b2 = t.b2) : s = t := by
  cases s; cases t; simp only at *; subst h0 h1 h2; rfl

def Poseidon2State12.toList (s : Poseidon2State12) : List Goldilocks :=
  [s.b0.x0, s.b0.x1, s.b0.x2, s.b0.x3,
   s.b1.x0, s.b1.x1, s.b1.x2, s.b1.x3,
   s.b2.x0, s.b2.x1, s.b2.x2, s.b2.x3]

def lane4Zero : Lane4 := ⟨Goldilocks.zero, Goldilocks.zero, Goldilocks.zero, Goldilocks.zero⟩

def lane4Add (a b : Lane4) : Lane4 :=
  ⟨Goldilocks.add a.x0 b.x0, Goldilocks.add a.x1 b.x1,
   Goldilocks.add a.x2 b.x2, Goldilocks.add a.x3 b.x3⟩

def lane4Sub (a b : Lane4) : Lane4 :=
  ⟨Goldilocks.sub a.x0 b.x0, Goldilocks.sub a.x1 b.x1,
   Goldilocks.sub a.x2 b.x2, Goldilocks.sub a.x3 b.x3⟩

def lane4Scale (c : Goldilocks) (a : Lane4) : Lane4 :=
  ⟨Goldilocks.mul c a.x0, Goldilocks.mul c a.x1,
   Goldilocks.mul c a.x2, Goldilocks.mul c a.x3⟩

def lane4Sum (a : Lane4) : Goldilocks :=
  Goldilocks.add (Goldilocks.add a.x0 a.x1) (Goldilocks.add a.x2 a.x3)

private def inv4G : Goldilocks := ⟨13835058052060938241, by decide⟩
private def inv7G : Goldilocks := ⟨2635249152773512046, by decide⟩
private def inv15G : Goldilocks := ⟨17216961131453612033, by decide⟩
private def inv1024G : Goldilocks := ⟨18428729670909296641, by decide⟩
private def inv2559G : Goldilocks := ⟨16817606062502628066, by decide⟩

private theorem ofNat_eq_goldOfInt (k : Nat) : Goldilocks.ofNat k = goldOfInt (k : Int) := by
  apply Goldilocks.ext
  apply Int.ofNat_inj.mp
  rw [goldOfInt_val]
  simp [Goldilocks.ofNat, goldP, Int.natCast_emod]

private theorem mul_cancel_of_prod_one {u k : Goldilocks} (h : Goldilocks.mul u k = Goldilocks.one)
    (x : Goldilocks) :
    Goldilocks.mul u (Goldilocks.mul k x) = x := by
  change CommRingOps.mul u (CommRingOps.mul k x) = x
  rw [← LawfulCommRing.mul_assoc]
  change CommRingOps.mul (Goldilocks.mul u k) x = x
  rw [h]
  exact LawfulCommRing.one_mul x

private theorem inv4G_mul_cancel (x : Goldilocks) :
    Goldilocks.mul inv4G (Goldilocks.mul (Goldilocks.ofNat 4) x) = x :=
  mul_cancel_of_prod_one (Goldilocks.ext (by rw [Goldilocks.mul_val]; rfl)) x

private theorem mul_inv4G_cancel (x : Goldilocks) :
    Goldilocks.mul (Goldilocks.ofNat 4) (Goldilocks.mul inv4G x) = x :=
  mul_cancel_of_prod_one (Goldilocks.ext (by rw [Goldilocks.mul_val]; rfl)) x

private theorem inv7G_mul_cancel (x : Goldilocks) :
    Goldilocks.mul inv7G (Goldilocks.mul (Goldilocks.ofNat 7) x) = x :=
  mul_cancel_of_prod_one (Goldilocks.ext (by rw [Goldilocks.mul_val]; rfl)) x

private theorem mul_inv7G_cancel (x : Goldilocks) :
    Goldilocks.mul (Goldilocks.ofNat 7) (Goldilocks.mul inv7G x) = x :=
  mul_cancel_of_prod_one (Goldilocks.ext (by rw [Goldilocks.mul_val]; rfl)) x

private theorem inv15G_mul_cancel (x : Goldilocks) :
    Goldilocks.mul inv15G (Goldilocks.mul (Goldilocks.ofNat 15) x) = x :=
  mul_cancel_of_prod_one (Goldilocks.ext (by rw [Goldilocks.mul_val]; rfl)) x

private theorem inv1024G_mul_cancel (x : Goldilocks) :
    Goldilocks.mul inv1024G (Goldilocks.mul (Goldilocks.ofNat 1024) x) = x :=
  mul_cancel_of_prod_one (Goldilocks.ext (by rw [Goldilocks.mul_val]; rfl)) x

private theorem inv2559G_mul_cancel (x : Goldilocks) :
    Goldilocks.mul inv2559G (Goldilocks.mul (Goldilocks.ofNat 2559) x) = x :=
  mul_cancel_of_prod_one (Goldilocks.ext (by rw [Goldilocks.mul_val]; rfl)) x

private theorem mul_inv2559G_cancel (x : Goldilocks) :
    Goldilocks.mul (Goldilocks.ofNat 2559) (Goldilocks.mul inv2559G x) = x :=
  mul_cancel_of_prod_one (Goldilocks.ext (by rw [Goldilocks.mul_val]; rfl)) x

def applyM4 (b : Lane4) : Lane4 :=
  let s := lane4Sum b
  let c2 := Goldilocks.ofNat 2
  ⟨Goldilocks.add s (Goldilocks.add b.x0 (Goldilocks.mul c2 b.x1)),
   Goldilocks.add s (Goldilocks.add b.x1 (Goldilocks.mul c2 b.x2)),
   Goldilocks.add s (Goldilocks.add b.x2 (Goldilocks.mul c2 b.x3)),
   Goldilocks.add s (Goldilocks.add b.x3 (Goldilocks.mul c2 b.x0))⟩

private def makeM4InvRaw (y : Lane4) (s : Goldilocks) : Lane4 :=
  let u0 := Goldilocks.sub y.x0 s
  let u1 := Goldilocks.sub y.x1 s
  let u2 := Goldilocks.sub y.x2 s
  let u3 := Goldilocks.sub y.x3 s
  let c2 := Goldilocks.ofNat 2
  let c4 := Goldilocks.ofNat 4
  let c8 := Goldilocks.ofNat 8
  ⟨Goldilocks.sub (Goldilocks.add (Goldilocks.sub (Goldilocks.mul c8 u3) (Goldilocks.mul c4 u2)) (Goldilocks.mul c2 u1)) u0,
   Goldilocks.sub (Goldilocks.add (Goldilocks.sub (Goldilocks.mul c8 u0) (Goldilocks.mul c4 u3)) (Goldilocks.mul c2 u2)) u1,
   Goldilocks.sub (Goldilocks.add (Goldilocks.sub (Goldilocks.mul c8 u1) (Goldilocks.mul c4 u0)) (Goldilocks.mul c2 u3)) u2,
   Goldilocks.sub (Goldilocks.add (Goldilocks.sub (Goldilocks.mul c8 u2) (Goldilocks.mul c4 u1)) (Goldilocks.mul c2 u0)) u3⟩

def applyM4Inv (y : Lane4) : Lane4 :=
  lane4Scale inv15G (makeM4InvRaw y (Goldilocks.mul inv7G (lane4Sum y)))

private theorem lane4Sum_applyM4 (b : Lane4) :
    lane4Sum (applyM4 b) = Goldilocks.mul (Goldilocks.ofNat 7) (lane4Sum b) := by
  unfold applyM4 lane4Sum
  dsimp only
  rw [← goldOfInt_nat b.x0, ← goldOfInt_nat b.x1, ← goldOfInt_nat b.x2, ← goldOfInt_nat b.x3,
      ofNat_eq_goldOfInt, ofNat_eq_goldOfInt]
  simp only [goldOfInt_add, goldOfInt_mul]
  congr 1
  omega

private theorem makeM4InvRaw_applyM4 (b : Lane4) :
    makeM4InvRaw (applyM4 b) (lane4Sum b) = lane4Scale (Goldilocks.ofNat 15) b := by
  unfold makeM4InvRaw applyM4 lane4Sum lane4Scale
  dsimp only
  apply Lane4.ext <;>
    (rw [← goldOfInt_nat b.x0, ← goldOfInt_nat b.x1, ← goldOfInt_nat b.x2, ← goldOfInt_nat b.x3];
     simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_sub, goldOfInt_mul];
     congr 1; omega)

theorem applyM4Inv_applyM4 (b : Lane4) : applyM4Inv (applyM4 b) = b := by
  unfold applyM4Inv
  rw [lane4Sum_applyM4, inv7G_mul_cancel, makeM4InvRaw_applyM4]
  unfold lane4Scale
  exact Lane4.ext
    (inv15G_mul_cancel b.x0)
    (inv15G_mul_cancel b.x1)
    (inv15G_mul_cancel b.x2)
    (inv15G_mul_cancel b.x3)

private theorem applyM4_scale (c : Goldilocks) (b : Lane4) :
    applyM4 (lane4Scale c b) = lane4Scale c (applyM4 b) := by
  have h2 : ∀ x : Int, (c.val : Int) * (((2 : Nat) : Int) * x) =
      ((2 : Nat) : Int) * ((c.val : Int) * x) := fun x => by
    rw [← Int.mul_assoc, Int.mul_comm (c.val : Int) ((2 : Nat) : Int), Int.mul_assoc]
  unfold applyM4 lane4Scale lane4Sum
  dsimp only
  apply Lane4.ext <;>
    (rw [← goldOfInt_nat c, ← goldOfInt_nat b.x0, ← goldOfInt_nat b.x1,
         ← goldOfInt_nat b.x2, ← goldOfInt_nat b.x3];
     simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul, Int.mul_add, h2])

private theorem applyM4_makeM4InvRaw (y : Lane4) (s : Goldilocks) :
    applyM4 (makeM4InvRaw y s) =
      let rem := Goldilocks.mul (Goldilocks.ofNat 5)
        (Goldilocks.sub (lane4Sum y) (Goldilocks.mul (Goldilocks.ofNat 7) s))
      ⟨Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 15) y.x0) rem,
       Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 15) y.x1) rem,
       Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 15) y.x2) rem,
       Goldilocks.add (Goldilocks.mul (Goldilocks.ofNat 15) y.x3) rem⟩ := by
  unfold applyM4 makeM4InvRaw lane4Sum
  dsimp only
  apply Lane4.ext <;>
    (rw [← goldOfInt_nat y.x0, ← goldOfInt_nat y.x1, ← goldOfInt_nat y.x2,
         ← goldOfInt_nat y.x3, ← goldOfInt_nat s];
     simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_sub, goldOfInt_mul];
     congr 1; omega)

theorem applyM4_applyM4Inv (y : Lane4) : applyM4 (applyM4Inv y) = y := by
  unfold applyM4Inv
  rw [applyM4_scale, applyM4_makeM4InvRaw]
  have hs7 : Goldilocks.mul (Goldilocks.ofNat 7) (Goldilocks.mul inv7G (lane4Sum y)) = lane4Sum y :=
    mul_inv7G_cancel (lane4Sum y)
  have hRemZero : Goldilocks.mul (Goldilocks.ofNat 5)
      (Goldilocks.sub (lane4Sum y) (Goldilocks.mul (Goldilocks.ofNat 7) (Goldilocks.mul inv7G (lane4Sum y)))) =
      Goldilocks.zero := by
    rw [hs7]
    have hz : Goldilocks.sub (lane4Sum y) (lane4Sum y) = Goldilocks.zero := by
      change CommRingOps.sub (lane4Sum y) (lane4Sum y) = CommRingOps.zero
      exact LawfulCommRing.sub_self _
    rw [hz]
    change CommRingOps.mul (Goldilocks.ofNat 5) CommRingOps.zero = CommRingOps.zero
    exact LawfulCommRing.mul_zero _
  unfold lane4Scale
  dsimp only at *
  rw [hRemZero]
  have hAddZero : ∀ a : Goldilocks, Goldilocks.add a Goldilocks.zero = a := fun a => by
    change CommRingOps.add a CommRingOps.zero = a
    exact LawfulCommRing.add_zero a
  rw [hAddZero, hAddZero, hAddZero, hAddZero]
  exact Lane4.ext
    (inv15G_mul_cancel y.x0)
    (inv15G_mul_cancel y.x1)
    (inv15G_mul_cancel y.x2)
    (inv15G_mul_cancel y.x3)

@[expose] def applyME (st : Poseidon2State12) : Poseidon2State12 :=
  let y0 := applyM4 st.b0
  let y1 := applyM4 st.b1
  let y2 := applyM4 st.b2
  let s := lane4Add (lane4Add y0 y1) y2
  ⟨lane4Add y0 s, lane4Add y1 s, lane4Add y2 s⟩

def applyMEInv (st : Poseidon2State12) : Poseidon2State12 :=
  let sumAll := lane4Add (lane4Add st.b0 st.b1) st.b2
  let s := lane4Scale inv4G sumAll
  ⟨applyM4Inv (lane4Sub st.b0 s),
   applyM4Inv (lane4Sub st.b1 s),
   applyM4Inv (lane4Sub st.b2 s)⟩

private theorem scalar_sum_four_cancel (a b c : Goldilocks) :
    Goldilocks.mul inv4G (Goldilocks.add (Goldilocks.add
      (Goldilocks.add a (Goldilocks.add (Goldilocks.add a b) c))
      (Goldilocks.add b (Goldilocks.add (Goldilocks.add a b) c)))
      (Goldilocks.add c (Goldilocks.add (Goldilocks.add a b) c))) =
      Goldilocks.add (Goldilocks.add a b) c := by
  have h : Goldilocks.add (Goldilocks.add
      (Goldilocks.add a (Goldilocks.add (Goldilocks.add a b) c))
      (Goldilocks.add b (Goldilocks.add (Goldilocks.add a b) c)))
      (Goldilocks.add c (Goldilocks.add (Goldilocks.add a b) c)) =
      Goldilocks.mul (Goldilocks.ofNat 4) (Goldilocks.add (Goldilocks.add a b) c) := by
    rw [← goldOfInt_nat a, ← goldOfInt_nat b, ← goldOfInt_nat c]
    simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
    congr 1; omega
  rw [h, inv4G_mul_cancel]

private theorem lane4_sum_four_cancel (y0 y1 y2 : Lane4) :
    lane4Scale inv4G (lane4Add (lane4Add (lane4Add y0 (lane4Add (lane4Add y0 y1) y2))
      (lane4Add y1 (lane4Add (lane4Add y0 y1) y2)))
      (lane4Add y2 (lane4Add (lane4Add y0 y1) y2))) =
    lane4Add (lane4Add y0 y1) y2 := by
  unfold lane4Scale lane4Add
  exact Lane4.ext
    (scalar_sum_four_cancel y0.x0 y1.x0 y2.x0)
    (scalar_sum_four_cancel y0.x1 y1.x1 y2.x1)
    (scalar_sum_four_cancel y0.x2 y1.x2 y2.x2)
    (scalar_sum_four_cancel y0.x3 y1.x3 y2.x3)

private theorem lane4Sub_add_right (a s : Lane4) : lane4Sub (lane4Add a s) s = a := by
  unfold lane4Sub lane4Add
  apply Lane4.ext <;>
    (change CommRingOps.sub (CommRingOps.add _ _) _ = _;
     rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
         LawfulCommRing.add_right_neg, LawfulCommRing.add_zero])

theorem applyMEInv_applyME (st : Poseidon2State12) : applyMEInv (applyME st) = st := by
  unfold applyMEInv applyME
  dsimp only
  rw [lane4_sum_four_cancel]
  rw [lane4Sub_add_right, lane4Sub_add_right, lane4Sub_add_right]
  rw [applyM4Inv_applyM4, applyM4Inv_applyM4, applyM4Inv_applyM4]

private theorem lane4SubSumId (b0 b1 b2 s : Lane4) :
    lane4Add (lane4Add (lane4Sub b0 s) (lane4Sub b1 s)) (lane4Sub b2 s) =
      lane4Add s (lane4Sub (lane4Add (lane4Add b0 b1) b2) (lane4Scale (Goldilocks.ofNat 4) s)) := by
  unfold lane4Add lane4Sub lane4Scale
  apply Lane4.ext <;>
    (rw [← goldOfInt_nat b0.x0, ← goldOfInt_nat b0.x1, ← goldOfInt_nat b0.x2, ← goldOfInt_nat b0.x3,
         ← goldOfInt_nat b1.x0, ← goldOfInt_nat b1.x1, ← goldOfInt_nat b1.x2, ← goldOfInt_nat b1.x3,
         ← goldOfInt_nat b2.x0, ← goldOfInt_nat b2.x1, ← goldOfInt_nat b2.x2, ← goldOfInt_nat b2.x3,
         ← goldOfInt_nat s.x0, ← goldOfInt_nat s.x1, ← goldOfInt_nat s.x2, ← goldOfInt_nat s.x3];
     simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_sub, goldOfInt_mul];
     congr 1; omega)

theorem applyME_applyMEInv (st : Poseidon2State12) : applyME (applyMEInv st) = st := by
  unfold applyME applyMEInv
  dsimp only
  rw [applyM4_applyM4Inv, applyM4_applyM4Inv, applyM4_applyM4Inv]
  let sumAll := lane4Add (lane4Add st.b0 st.b1) st.b2
  have h4 : lane4Scale (Goldilocks.ofNat 4) (lane4Scale inv4G sumAll) = sumAll := by
    unfold lane4Scale
    exact Lane4.ext
      (mul_inv4G_cancel sumAll.x0)
      (mul_inv4G_cancel sumAll.x1)
      (mul_inv4G_cancel sumAll.x2)
      (mul_inv4G_cancel sumAll.x3)
  have hSumSub : lane4Add (lane4Add (lane4Sub st.b0 (lane4Scale inv4G sumAll))
      (lane4Sub st.b1 (lane4Scale inv4G sumAll))) (lane4Sub st.b2 (lane4Scale inv4G sumAll)) =
      lane4Scale inv4G sumAll := by
    rw [lane4SubSumId st.b0 st.b1 st.b2 (lane4Scale inv4G sumAll), h4]
    have hZero : lane4Sub sumAll sumAll = lane4Zero := by
      unfold lane4Sub lane4Zero
      apply Lane4.ext <;> exact LawfulCommRing.sub_self _
    rw [hZero]
    unfold lane4Add lane4Zero
    apply Lane4.ext <;> exact LawfulCommRing.add_zero _
  change Poseidon2State12.mk
    (lane4Add (lane4Sub st.b0 (lane4Scale inv4G sumAll))
      (lane4Add (lane4Add (lane4Sub st.b0 (lane4Scale inv4G sumAll))
        (lane4Sub st.b1 (lane4Scale inv4G sumAll))) (lane4Sub st.b2 (lane4Scale inv4G sumAll))))
    (lane4Add (lane4Sub st.b1 (lane4Scale inv4G sumAll))
      (lane4Add (lane4Add (lane4Sub st.b0 (lane4Scale inv4G sumAll))
        (lane4Sub st.b1 (lane4Scale inv4G sumAll))) (lane4Sub st.b2 (lane4Scale inv4G sumAll))))
    (lane4Add (lane4Sub st.b2 (lane4Scale inv4G sumAll))
      (lane4Add (lane4Add (lane4Sub st.b0 (lane4Scale inv4G sumAll))
        (lane4Sub st.b1 (lane4Scale inv4G sumAll))) (lane4Sub st.b2 (lane4Scale inv4G sumAll)))) = st
  rw [hSumSub]
  have hAddSub : ∀ a b : Lane4, lane4Add (lane4Sub a b) b = a := fun a b => by
    unfold lane4Add lane4Sub
    apply Lane4.ext <;>
      (change CommRingOps.add (CommRingOps.sub _ _) _ = _;
       rw [LawfulCommRing.add_comm, LawfulCommRing.add_sub_cancel_left])
  rw [hAddSub, hAddSub, hAddSub]

def state12Sum (st : Poseidon2State12) : Goldilocks :=
  Goldilocks.add (Goldilocks.add (lane4Sum st.b0) (lane4Sum st.b1)) (lane4Sum st.b2)

@[expose] def applyMI (st : Poseidon2State12) : Poseidon2State12 :=
  let s := state12Sum st
  let b0 := st.b0
  let b1 := st.b1
  let b2 := st.b2
  ⟨⟨Goldilocks.add (Goldilocks.mul (goldOfInt (-2)) b0.x0) s,
    Goldilocks.add b0.x1 s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 2) b0.x2) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 4) b0.x3) s⟩,
   ⟨Goldilocks.add (Goldilocks.mul (goldOfInt 8) b1.x0) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 16) b1.x1) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 32) b1.x2) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 64) b1.x3) s⟩,
   ⟨Goldilocks.add (Goldilocks.mul (goldOfInt 128) b2.x0) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 256) b2.x1) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 512) b2.x2) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 1024) b2.x3) s⟩⟩

private def weightedSumMI (y : Poseidon2State12) : Goldilocks :=
  let t0 := Goldilocks.add
    (Goldilocks.add (Goldilocks.mul (goldOfInt (-512)) y.b0.x0) (Goldilocks.mul (goldOfInt 1024) y.b0.x1))
    (Goldilocks.add (Goldilocks.mul (goldOfInt 512) y.b0.x2) (Goldilocks.mul (goldOfInt 256) y.b0.x3))
  let t1 := Goldilocks.add
    (Goldilocks.add (Goldilocks.mul (goldOfInt 128) y.b1.x0) (Goldilocks.mul (goldOfInt 64) y.b1.x1))
    (Goldilocks.add (Goldilocks.mul (goldOfInt 32) y.b1.x2) (Goldilocks.mul (goldOfInt 16) y.b1.x3))
  let t2 := Goldilocks.add
    (Goldilocks.add (Goldilocks.mul (goldOfInt 8) y.b2.x0) (Goldilocks.mul (goldOfInt 4) y.b2.x1))
    (Goldilocks.add (Goldilocks.mul (goldOfInt 2) y.b2.x2) y.b2.x3)
  Goldilocks.add (Goldilocks.add t0 t1) t2

private def makeMIInvRaw (y : Poseidon2State12) (inv1024 s : Goldilocks) : Poseidon2State12 :=
  let scale (w : Int) (yi : Goldilocks) : Goldilocks :=
    Goldilocks.mul inv1024 (Goldilocks.mul (goldOfInt w) (Goldilocks.sub yi s))
  ⟨⟨scale (-512) y.b0.x0, scale 1024 y.b0.x1, scale 512 y.b0.x2, scale 256 y.b0.x3⟩,
   ⟨scale 128 y.b1.x0, scale 64 y.b1.x1, scale 32 y.b1.x2, scale 16 y.b1.x3⟩,
   ⟨scale 8 y.b2.x0, scale 4 y.b2.x1, scale 2 y.b2.x2, scale 1 y.b2.x3⟩⟩

def applyMIInv (y : Poseidon2State12) : Poseidon2State12 :=
  makeMIInvRaw y inv1024G (Goldilocks.mul inv2559G (weightedSumMI y))

private theorem weightedSumMI_applyMI (st : Poseidon2State12) :
    weightedSumMI (applyMI st) = Goldilocks.mul (Goldilocks.ofNat 2559) (state12Sum st) := by
  unfold weightedSumMI applyMI state12Sum lane4Sum
  dsimp only
  rw [← goldOfInt_nat st.b0.x0, ← goldOfInt_nat st.b0.x1, ← goldOfInt_nat st.b0.x2, ← goldOfInt_nat st.b0.x3,
      ← goldOfInt_nat st.b1.x0, ← goldOfInt_nat st.b1.x1, ← goldOfInt_nat st.b1.x2, ← goldOfInt_nat st.b1.x3,
      ← goldOfInt_nat st.b2.x0, ← goldOfInt_nat st.b2.x1, ← goldOfInt_nat st.b2.x2, ← goldOfInt_nat st.b2.x3]
  simp only [ofNat_eq_goldOfInt, goldOfInt_add, goldOfInt_mul]
  congr 1; omega

private theorem mi_lane_recover (v w : Int) (hv : v * w = 1024) (x s : Goldilocks) :
    Goldilocks.mul inv1024G (Goldilocks.mul (goldOfInt w)
      (Goldilocks.sub (Goldilocks.add (Goldilocks.mul (goldOfInt v) x) s) s)) = x := by
  have hProd : Goldilocks.mul (goldOfInt w)
      (Goldilocks.sub (Goldilocks.add (Goldilocks.mul (goldOfInt v) x) s) s) =
      Goldilocks.mul (Goldilocks.ofNat 1024) x := by
    rw [← goldOfInt_nat x, ← goldOfInt_nat s, ofNat_eq_goldOfInt]
    simp only [goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
    congr 1
    have hEq : w * (v * (x.val : Int) + (s.val : Int) - (s.val : Int)) = (v * w) * (x.val : Int) := by
      rw [Int.add_sub_cancel, ← Int.mul_assoc, Int.mul_comm w v]
    rw [hEq, hv]
    omega
  rw [hProd, inv1024G_mul_cancel x]

theorem applyMIInv_applyMI (st : Poseidon2State12) : applyMIInv (applyMI st) = st := by
  unfold applyMIInv
  rw [weightedSumMI_applyMI, inv2559G_mul_cancel (state12Sum st)]
  unfold makeMIInvRaw applyMI
  dsimp only
  have h1 : Goldilocks.add st.b0.x1 (state12Sum st) =
      Goldilocks.add (Goldilocks.mul (goldOfInt 1) st.b0.x1) (state12Sum st) := by
    have hone : goldOfInt 1 = CommRingOps.one := rfl
    change _ = Goldilocks.add (CommRingOps.mul (goldOfInt 1) st.b0.x1) _
    rw [hone, LawfulCommRing.one_mul]
  apply Poseidon2State12.ext
  · apply Lane4.ext
    · exact mi_lane_recover (-2) (-512) rfl st.b0.x0 (state12Sum st)
    · rw [h1]; exact mi_lane_recover 1 1024 rfl st.b0.x1 (state12Sum st)
    · exact mi_lane_recover 2 512 rfl st.b0.x2 (state12Sum st)
    · exact mi_lane_recover 4 256 rfl st.b0.x3 (state12Sum st)
  · apply Lane4.ext
    · exact mi_lane_recover 8 128 rfl st.b1.x0 (state12Sum st)
    · exact mi_lane_recover 16 64 rfl st.b1.x1 (state12Sum st)
    · exact mi_lane_recover 32 32 rfl st.b1.x2 (state12Sum st)
    · exact mi_lane_recover 64 16 rfl st.b1.x3 (state12Sum st)
  · apply Lane4.ext
    · exact mi_lane_recover 128 8 rfl st.b2.x0 (state12Sum st)
    · exact mi_lane_recover 256 4 rfl st.b2.x1 (state12Sum st)
    · exact mi_lane_recover 512 2 rfl st.b2.x2 (state12Sum st)
    · exact mi_lane_recover 1024 1 rfl st.b2.x3 (state12Sum st)

private theorem mi_lane_assoc_aux (v w : Int) (hv : v * w = 1024) (inv1024 yi s : Goldilocks) :
    Goldilocks.mul (goldOfInt v)
      (Goldilocks.mul inv1024 (Goldilocks.mul (goldOfInt w) (Goldilocks.sub yi s))) =
      Goldilocks.mul inv1024 (Goldilocks.mul (Goldilocks.ofNat 1024) (Goldilocks.sub yi s)) := by
  rw [← goldOfInt_nat inv1024, ← goldOfInt_nat yi, ← goldOfInt_nat s, ofNat_eq_goldOfInt]
  simp only [goldOfInt_sub, goldOfInt_mul]
  congr 1
  have hEq : v * ((inv1024.val : Int) * (w * ((yi.val : Int) - (s.val : Int)))) =
      (inv1024.val : Int) * ((v * w) * ((yi.val : Int) - (s.val : Int))) := by
    rw [← Int.mul_assoc, ← Int.mul_assoc, Int.mul_comm v (inv1024.val : Int),
        Int.mul_assoc (inv1024.val : Int) v w, Int.mul_assoc]
  rw [hEq, hv]
  rfl

private theorem mi_lane_forward (v w : Int) (hv : v * w = 1024) (yi s : Goldilocks) :
    Goldilocks.add (Goldilocks.mul (goldOfInt v)
      (Goldilocks.mul inv1024G (Goldilocks.mul (goldOfInt w) (Goldilocks.sub yi s)))) s = yi := by
  rw [mi_lane_assoc_aux v w hv inv1024G yi s, inv1024G_mul_cancel (Goldilocks.sub yi s)]
  change CommRingOps.add (CommRingOps.sub yi s) s = yi
  rw [LawfulCommRing.add_comm, LawfulCommRing.add_sub_cancel_left]

private theorem state12Sum_makeMIInvRaw (y : Poseidon2State12) (inv1024 s : Goldilocks) :
    state12Sum (makeMIInvRaw y inv1024 s) =
      Goldilocks.mul inv1024 (Goldilocks.sub (weightedSumMI y) (Goldilocks.mul (goldOfInt 1535) s)) := by
  unfold state12Sum makeMIInvRaw lane4Sum weightedSumMI
  dsimp only
  rw [← goldOfInt_nat inv1024, ← goldOfInt_nat s,
      ← goldOfInt_nat y.b0.x0, ← goldOfInt_nat y.b0.x1, ← goldOfInt_nat y.b0.x2, ← goldOfInt_nat y.b0.x3,
      ← goldOfInt_nat y.b1.x0, ← goldOfInt_nat y.b1.x1, ← goldOfInt_nat y.b1.x2, ← goldOfInt_nat y.b1.x3,
      ← goldOfInt_nat y.b2.x0, ← goldOfInt_nat y.b2.x1, ← goldOfInt_nat y.b2.x2, ← goldOfInt_nat y.b2.x3]
  simp only [goldOfInt_add, goldOfInt_sub, goldOfInt_mul, ← Int.mul_add]
  congr 1
  congr 1
  omega

private theorem mi_2559_sub_1535 (s : Goldilocks) :
    Goldilocks.sub (Goldilocks.mul (Goldilocks.ofNat 2559) s) (Goldilocks.mul (goldOfInt 1535) s) =
      Goldilocks.mul (Goldilocks.ofNat 1024) s := by
  rw [← goldOfInt_nat s, ofNat_eq_goldOfInt, ofNat_eq_goldOfInt]
  simp only [goldOfInt_sub, goldOfInt_mul]
  congr 1; omega

private theorem applyMI_makeMIInvRaw_helper (y : Poseidon2State12) (s : Goldilocks)
    (hSum : state12Sum (makeMIInvRaw y inv1024G s) = s) :
    applyMI (makeMIInvRaw y inv1024G s) = y := by
  unfold applyMI
  rw [hSum]
  unfold makeMIInvRaw
  dsimp only
  have h1 : ∀ a : Goldilocks, a = Goldilocks.mul (goldOfInt 1) a := fun a => by
    rw [← goldOfInt_nat a, goldOfInt_mul, Int.one_mul]
  apply Poseidon2State12.ext
  · apply Lane4.ext
    · exact mi_lane_forward (-2) (-512) rfl y.b0.x0 s
    · rw [h1 (Goldilocks.mul inv1024G (Goldilocks.mul (goldOfInt 1024) (Goldilocks.sub y.b0.x1 s)))]
      exact mi_lane_forward 1 1024 rfl y.b0.x1 s
    · exact mi_lane_forward 2 512 rfl y.b0.x2 s
    · exact mi_lane_forward 4 256 rfl y.b0.x3 s
  · apply Lane4.ext
    · exact mi_lane_forward 8 128 rfl y.b1.x0 s
    · exact mi_lane_forward 16 64 rfl y.b1.x1 s
    · exact mi_lane_forward 32 32 rfl y.b1.x2 s
    · exact mi_lane_forward 64 16 rfl y.b1.x3 s
  · apply Lane4.ext
    · exact mi_lane_forward 128 8 rfl y.b2.x0 s
    · exact mi_lane_forward 256 4 rfl y.b2.x1 s
    · exact mi_lane_forward 512 2 rfl y.b2.x2 s
    · exact mi_lane_forward 1024 1 rfl y.b2.x3 s

