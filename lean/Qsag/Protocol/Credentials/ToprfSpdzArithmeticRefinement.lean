module
/-
# Qsag.Protocol.Credentials.ToprfSpdzArithmeticRefinement — Share-Level SPDZ Arithmetic of the TOPRF

Model of `crates/qsag-cred/src/voprf_spdz.rs` (`evaluate_inner`, `SpdzPreparedSession::sbox`)
below the gate layer of `piToprfCredService`. The servers hold Lagrange shares of the PRF key and
of the `GF(p²)` MAC key, evaluate `Poseidon2` on authenticated shares with one `Π_pow7` tuple per
S-box round against an adversary that adds an error to every opened value and every MAC
residual, open the blinded residuals (`MacBlind.macBlindPure`), and release the value
reconstructed from the opened output shares.

## Scope

Proved:
* `spdzEval_sound_or_mac_forgery`, `piToprfRealSpdz_sound_or_mac_forgery`: an accepted evaluation
  reconstructs `evalAlgebraicOprf k x`, or an error lane of the adversary satisfies
  `d ≠ 0 ∧ m = α · d`, or a corrupt randomizer cancels an honest blinding randomizer.
* `evalFooled_macKey_unique`, `spdz_mac_forgery_game_bound`, `goldilocksExt2_card_bits`: for one
  evaluation and an adversary fixed before the MAC key is sampled (its errors are functions of
  the values opened so far), at most one of the `p²` keys is fooled, and `2^127.99 < p² < 2^128`.
* `spdzEval_macKey_zero_leakage`, `piToprfRealSpdz_macKey_zero_leakage`: for an adversary none of
  whose nonzero error lanes is a forgery point of either of two MAC keys, the transcript of one
  evaluation has the same distribution over the honest blinding randomizers under both keys.
* `piToprfRealSpdzGuarded_dataRefines`: outside the bad event `realSpdzBad` the machine refines
  `Spec.idealCredMachine` when `cfg.oprf pt = evalAlgebraicOprf k (enc pt)`.
* Issuance: `piToprfRealSpdz_issue_accept_checks`, `piToprfRealSpdz_issue_binding_or_collision`.

Not proved:
* A bound on the probability that a corrupt randomizer cancels an honest one, and the composition
  of the one-evaluation key bound over several evaluations under one MAC key.
* The preprocessing: `ServersValid` and `SessionValid` are hypotheses. The corrupt randomizers
  are functions of the lane index only, which is what commit-before-open provides.
* Hiding or collision resistance of `RealSpdzParams.commit`, what `LimboSdOpeningWire.verify33`
  certifies about the issuance proof, and pseudorandomness of `evalAlgebraicOprf`.
-/
public import Qsag.Protocol.Credentials.ToprfMachine
public import Qsag.Protocol.Threshold.MacBlind
public import Qsag.Oracle.Poseidon2
public import Qsag.Oracle.ProbPkgBridge
public import Qsag.Math.Tactic.CommRing
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.SpdzToprf

open CommRingOps
open CRing (natCast npow)

set_option autoImplicit false

/-! ## 1. Linear reconstruction and authenticated shares over a commutative ring -/

section Generic
variable {M : Type} [LawfulCommRing M]

/-- `Σ_{i<n} f i` in the ring. -/
def linSum : (n : Nat) → (Fin n → M) → M
  | 0, _ => zero
  | n + 1, f => add (f ⟨0, Nat.zero_lt_succ n⟩)
      (linSum n (fun i => f ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩))

theorem linSum_congr {n : Nat} {f g : Fin n → M} (h : ∀ i, f i = g i) :
    linSum n f = linSum n g := by
  rw [show f = g from funext h]

theorem linSum_add : ∀ (n : Nat) (f g : Fin n → M),
    linSum n (fun i => add (f i) (g i)) = add (linSum n f) (linSum n g)
  | 0, _, _ => (LawfulCommRing.zero_add (zero : M)).symm
  | n + 1, f, g => by
    unfold linSum
    dsimp only
    rw [linSum_add n]
    constructive_ring

theorem linSum_mul_left (c : M) : ∀ (n : Nat) (f : Fin n → M),
    linSum n (fun i => mul c (f i)) = mul c (linSum n f)
  | 0, _ => (LawfulCommRing.mul_zero c).symm
  | n + 1, f => by
    unfold linSum
    dsimp only
    rw [linSum_mul_left c n]
    constructive_ring

theorem additive_zero {L : M → M} (hAdd : ∀ x y, L (add x y) = add (L x) (L y)) :
    L zero = zero := by
  have h := hAdd zero zero
  rw [LawfulCommRing.zero_add] at h
  exact (LawfulCommRing.add_left_cancel
    ((LawfulCommRing.add_zero (L zero)).trans h)).symm

theorem linSum_map {L : M → M} (hAdd : ∀ x y, L (add x y) = add (L x) (L y)) :
    ∀ (n : Nat) (f : Fin n → M), linSum n (fun i => L (f i)) = L (linSum n f)
  | 0, _ => (additive_zero hAdd).symm
  | n + 1, f => by
    unfold linSum
    dsimp only
    rw [linSum_map hAdd n, hAdd]

/-- Lagrange reconstruction `Σ_i λ_i · f_i` of a value from its `n` server shares. -/
def recSum {n : Nat} (lam f : Fin n → M) : M :=
  linSum n (fun i => mul (lam i) (f i))

theorem recSum_add {n : Nat} (lam f g : Fin n → M) :
    recSum lam (fun i => add (f i) (g i)) = add (recSum lam f) (recSum lam g) := by
  unfold recSum
  rw [← linSum_add]
  exact linSum_congr (fun i => LawfulCommRing.left_distrib _ _ _)

theorem recSum_sub {n : Nat} (lam f g : Fin n → M) :
    recSum lam (fun i => sub (f i) (g i)) = sub (recSum lam f) (recSum lam g) := by
  have hNeg : recSum lam (fun i => mul (neg one) (g i)) = mul (neg one) (recSum lam g) := by
    unfold recSum
    rw [← linSum_mul_left]
    exact linSum_congr (fun i => by dsimp only; constructive_ring)
  have hSplit : recSum lam (fun i => sub (f i) (g i)) =
      recSum lam (fun i => add (f i) (mul (neg one) (g i))) := by
    unfold recSum
    exact linSum_congr (fun i => by dsimp only; constructive_ring)
  rw [hSplit, recSum_add, hNeg]
  constructive_ring

theorem recSum_scale {n : Nat} (lam : Fin n → M) (c : M) (f : Fin n → M) :
    recSum lam (fun i => mul c (f i)) = mul c (recSum lam f) := by
  unfold recSum
  rw [← linSum_mul_left]
  exact linSum_congr (fun i => by dsimp only; constructive_ring)

theorem recSum_mul_const {n : Nat} (lam a : Fin n → M) (c : M) :
    recSum lam (fun i => mul (a i) c) = mul (recSum lam a) c := by
  have h := recSum_scale lam c a
  rw [LawfulCommRing.mul_comm c (recSum lam a)] at h
  rw [← h]
  unfold recSum
  exact linSum_congr (fun i => by dsimp only; constructive_ring)

theorem recSum_const {n : Nat} (lam : Fin n → M) (hOne : linSum n lam = one) (c : M) :
    recSum lam (fun _ => c) = c := by
  have h : recSum lam (fun _ => c) = mul c (linSum n lam) := by
    unfold recSum
    rw [← linSum_mul_left]
    exact linSum_congr (fun i => LawfulCommRing.mul_comm _ _)
  rw [h, hOne, LawfulCommRing.mul_one]

theorem recSum_map {n : Nat} (lam : Fin n → M) {L : M → M}
    (hAdd : ∀ x y, L (add x y) = add (L x) (L y))
    (hLam : ∀ i x, L (mul (lam i) x) = mul (lam i) (L x)) (f : Fin n → M) :
    recSum lam (fun i => L (f i)) = L (recSum lam f) := by
  unfold recSum
  rw [← linSum_map hAdd]
  exact linSum_congr (fun i => (hLam i (f i)).symm)

end Generic

/-- One server's authenticated share of a ring element: the value share and the two coordinates
    of its MAC share. The same record holds a Lagrange-reconstructed aggregate. -/
structure AShare (M : Type) where
  v : M
  m0 : M
  m1 : M

/-- One server's share of a preprocessed `Π_pow7` tuple: authenticated shares of
    `r, r², …, r⁷` (`r_pows`, `r_macs` in `voprf_spdz.rs`). -/
structure Pow7Share (M : Type) where
  r1 : AShare M
  r2 : AShare M
  r3 : AShare M
  r4 : AShare M
  r5 : AShare M
  r6 : AShare M
  r7 : AShare M

section Shares
variable {M : Type} [LawfulCommRing M]

def AShare.add (s t : AShare M) : AShare M :=
  ⟨CommRingOps.add s.v t.v, CommRingOps.add s.m0 t.m0, CommRingOps.add s.m1 t.m1⟩
def AShare.sub (s t : AShare M) : AShare M :=
  ⟨CommRingOps.sub s.v t.v, CommRingOps.sub s.m0 t.m0, CommRingOps.sub s.m1 t.m1⟩
/-- Multiplication of a share by a public ring element. -/
def AShare.scale (c : M) (s : AShare M) : AShare M := ⟨mul c s.v, mul c s.m0, mul c s.m1⟩
/-- A server's share of the public constant `c`: the constant itself, and its MAC share under
    the server's share `(a0, a1)` of the MAC key (`Wire::public`). -/
def AShare.pub (a0 a1 c : M) : AShare M := ⟨c, mul a0 c, mul a1 c⟩
/-- A public linear layer applied to every component of a share. -/
def AShare.map (L : M → M) (s : AShare M) : AShare M := ⟨L s.v, L s.m0, L s.m1⟩

/-- Lagrange reconstruction of an authenticated sharing, component by component. -/
def aggShare {n : Nat} (lam : Fin n → M) (s : Fin n → AShare M) : AShare M :=
  ⟨recSum lam (fun i => (s i).v), recSum lam (fun i => (s i).m0), recSum lam (fun i => (s i).m1)⟩

def aggPow7 {n : Nat} (lam : Fin n → M) (t : Fin n → Pow7Share M) : Pow7Share M :=
  ⟨aggShare lam (fun i => (t i).r1), aggShare lam (fun i => (t i).r2),
   aggShare lam (fun i => (t i).r3), aggShare lam (fun i => (t i).r4),
   aggShare lam (fun i => (t i).r5), aggShare lam (fun i => (t i).r6),
   aggShare lam (fun i => (t i).r7)⟩

theorem aggShare_add {n : Nat} (lam : Fin n → M) (s t : Fin n → AShare M) :
    aggShare lam (fun i => (s i).add (t i)) = (aggShare lam s).add (aggShare lam t) := by
  unfold aggShare AShare.add
  dsimp only
  rw [recSum_add, recSum_add, recSum_add]

theorem aggShare_sub {n : Nat} (lam : Fin n → M) (s t : Fin n → AShare M) :
    aggShare lam (fun i => (s i).sub (t i)) = (aggShare lam s).sub (aggShare lam t) := by
  unfold aggShare AShare.sub
  dsimp only
  rw [recSum_sub, recSum_sub, recSum_sub]

theorem aggShare_scale {n : Nat} (lam : Fin n → M) (c : M) (s : Fin n → AShare M) :
    aggShare lam (fun i => AShare.scale c (s i)) = AShare.scale c (aggShare lam s) := by
  unfold aggShare AShare.scale
  dsimp only
  rw [recSum_scale, recSum_scale, recSum_scale]

theorem aggShare_pub {n : Nat} (lam : Fin n → M) (hOne : linSum n lam = one)
    (a0 a1 : Fin n → M) (c : M) :
    aggShare lam (fun i => AShare.pub (a0 i) (a1 i) c) =
      AShare.pub (recSum lam a0) (recSum lam a1) c := by
  unfold aggShare AShare.pub
  dsimp only
  rw [recSum_const lam hOne, recSum_mul_const, recSum_mul_const]

theorem aggShare_map {n : Nat} (lam : Fin n → M) {L : M → M}
    (hAdd : ∀ x y, L (add x y) = add (L x) (L y))
    (hLam : ∀ i x, L (mul (lam i) x) = mul (lam i) (L x)) (s : Fin n → AShare M) :
    aggShare lam (fun i => (s i).map L) = (aggShare lam s).map L := by
  unfold aggShare AShare.map
  dsimp only
  rw [recSum_map lam hAdd hLam, recSum_map lam hAdd hLam, recSum_map lam hAdd hLam]

/-- The SPDZ MAC relation on a reconstructed wire: `mac = α · value`, coordinate by coordinate
    (`A0`, `A1` are the two coordinates of the MAC key). -/
def Authentic (A0 A1 : M) (s : AShare M) : Prop :=
  s.m0 = mul A0 s.v ∧ s.m1 = mul A1 s.v

theorem Authentic.add {A0 A1 : M} {s t : AShare M} (hs : Authentic A0 A1 s)
    (ht : Authentic A0 A1 t) : Authentic A0 A1 (s.add t) := by
  unfold Authentic AShare.add at *
  dsimp only
  rw [hs.1, hs.2, ht.1, ht.2]
  exact ⟨by constructive_ring, by constructive_ring⟩

theorem Authentic.sub {A0 A1 : M} {s t : AShare M} (hs : Authentic A0 A1 s)
    (ht : Authentic A0 A1 t) : Authentic A0 A1 (s.sub t) := by
  unfold Authentic AShare.sub at *
  dsimp only
  rw [hs.1, hs.2, ht.1, ht.2]
  exact ⟨by constructive_ring, by constructive_ring⟩

theorem Authentic.scale {A0 A1 : M} (c : M) {s : AShare M} (hs : Authentic A0 A1 s) :
    Authentic A0 A1 (AShare.scale c s) := by
  unfold Authentic AShare.scale at *
  dsimp only
  rw [hs.1, hs.2]
  exact ⟨by constructive_ring, by constructive_ring⟩

theorem Authentic.pub (A0 A1 c : M) : Authentic A0 A1 (AShare.pub A0 A1 c) := ⟨rfl, rfl⟩

theorem Authentic.map {A0 A1 : M} {L : M → M}
    (h0 : ∀ x, L (mul A0 x) = mul A0 (L x)) (h1 : ∀ x, L (mul A1 x) = mul A1 (L x))
    {s : AShare M} (hs : Authentic A0 A1 s) : Authentic A0 A1 (s.map L) := by
  unfold Authentic AShare.map at *
  dsimp only
  rw [hs.1, hs.2]
  exact ⟨h0 _, h1 _⟩

/-- A reconstructed tuple is valid: authenticated sharings of the powers `r, r², …, r⁷`. -/
structure Pow7Valid (A0 A1 : M) (t : Pow7Share M) : Prop where
  auth1 : Authentic A0 A1 t.r1
  auth2 : Authentic A0 A1 t.r2
  auth3 : Authentic A0 A1 t.r3
  auth4 : Authentic A0 A1 t.r4
  auth5 : Authentic A0 A1 t.r5
  auth6 : Authentic A0 A1 t.r6
  auth7 : Authentic A0 A1 t.r7
  pow2 : t.r2.v = npow t.r1.v 2
  pow3 : t.r3.v = npow t.r1.v 3
  pow4 : t.r4.v = npow t.r1.v 4
  pow5 : t.r5.v = npow t.r1.v 5
  pow6 : t.r6.v = npow t.r1.v 6
  pow7 : t.r7.v = npow t.r1.v 7

/-! ### The one-round `x ↦ x⁷` gate on shares (`SpdzPreparedSession::sbox`) -/

/-- A server's share of the masked S-box input `sel · (x + C + r)`; `sel` is the public
    idempotent selecting the lanes that carry an S-box in this round. -/
def sboxMasked (sel a0 a1 C : M) (x : AShare M) (t : Pow7Share M) : AShare M :=
  AShare.scale sel ((x.add (AShare.pub a0 a1 C)).add t.r1)

/-- A server's share of `(y - r)⁷`, expanded on its shares of the powers of `r` with the public
    opened value `y`: `y⁷ - 7y⁶r + 21y⁵r² - 35y⁴r³ + 35y³r⁴ - 21y²r⁵ + 7yr⁶ - r⁷`. -/
def sboxExpand (a0 a1 y : M) (t : Pow7Share M) : AShare M :=
  (((((((AShare.pub a0 a1 (npow y 7)).sub
    (AShare.scale (mul (natCast 7) (npow y 6)) t.r1)).add
    (AShare.scale (mul (natCast 21) (npow y 5)) t.r2)).sub
    (AShare.scale (mul (natCast 35) (npow y 4)) t.r3)).add
    (AShare.scale (mul (natCast 35) (npow y 3)) t.r4)).sub
    (AShare.scale (mul (natCast 21) (npow y 2)) t.r5)).add
    (AShare.scale (mul (natCast 7) y) t.r6)).sub t.r7

/-- A server's output share of the round's S-box layer: unselected lanes keep `x + C`, selected
    lanes take the expansion of `(y - r)⁷`. -/
def sboxOut (sel a0 a1 C y : M) (x : AShare M) (t : Pow7Share M) : AShare M :=
  (AShare.scale (sub one sel) (x.add (AShare.pub a0 a1 C))).add
    (AShare.scale sel (sboxExpand a0 a1 y t))

theorem aggShare_sboxMasked {n : Nat} (lam : Fin n → M) (hOne : linSum n lam = one)
    (sel C : M) (a0 a1 : Fin n → M) (x : Fin n → AShare M) (t : Fin n → Pow7Share M) :
    aggShare lam (fun i => sboxMasked sel (a0 i) (a1 i) C (x i) (t i)) =
      sboxMasked sel (recSum lam a0) (recSum lam a1) C (aggShare lam x) (aggPow7 lam t) := by
  unfold sboxMasked
  rw [aggShare_scale, aggShare_add, aggShare_add, aggShare_pub lam hOne]
  rfl

theorem aggShare_sboxOut {n : Nat} (lam : Fin n → M) (hOne : linSum n lam = one)
    (sel C y : M) (a0 a1 : Fin n → M) (x : Fin n → AShare M) (t : Fin n → Pow7Share M) :
    aggShare lam (fun i => sboxOut sel (a0 i) (a1 i) C y (x i) (t i)) =
      sboxOut sel (recSum lam a0) (recSum lam a1) C y (aggShare lam x) (aggPow7 lam t) := by
  unfold sboxOut sboxExpand
  simp only [aggShare_add, aggShare_sub, aggShare_scale, aggShare_pub lam hOne]
  rfl

theorem npow_seven_of_idem {s : M} (hs : mul s s = s) : npow s 7 = s := by
  have h : npow s 7 = mul (mul (mul (mul (mul (mul s s) s) s) s) s) s := by constructive_ring
  rw [h]
  simp only [hs]

/-- On an idempotent `s`, `s · (s·z)⁷ = s · z⁷`. -/
theorem idem_mul_pow7 {s : M} (hs : mul s s = s) (z : M) :
    mul s (npow (mul s z) 7) = mul s (npow z 7) := by
  have h : mul s (npow (mul s z) 7) = mul (mul s (npow s 7)) (npow z 7) := by constructive_ring
  rw [h, npow_seven_of_idem hs, hs]

theorem sboxExpand_v (a0 a1 y : M) (t : Pow7Share M)
    (h2 : t.r2.v = npow t.r1.v 2) (h3 : t.r3.v = npow t.r1.v 3) (h4 : t.r4.v = npow t.r1.v 4)
    (h5 : t.r5.v = npow t.r1.v 5) (h6 : t.r6.v = npow t.r1.v 6) (h7 : t.r7.v = npow t.r1.v 7) :
    (sboxExpand a0 a1 y t).v = npow (sub y t.r1.v) 7 := by
  unfold sboxExpand AShare.sub AShare.add AShare.scale AShare.pub
  dsimp only
  rw [h2, h3, h4, h5, h6, h7]
  constructive_ring

/-- Value of the S-box layer when the opened value carries the additive error `sel · E`:
    the selected lanes compute `(x + C + E)⁷`. -/
theorem sboxOut_v {sel : M} (hs : mul sel sel = sel) (a0 a1 C E : M) (x : AShare M)
    (t : Pow7Share M)
    (h2 : t.r2.v = npow t.r1.v 2) (h3 : t.r3.v = npow t.r1.v 3) (h4 : t.r4.v = npow t.r1.v 4)
    (h5 : t.r5.v = npow t.r1.v 5) (h6 : t.r6.v = npow t.r1.v 6) (h7 : t.r7.v = npow t.r1.v 7) :
    (sboxOut sel a0 a1 C (add (sboxMasked sel a0 a1 C x t).v (mul sel E)) x t).v =
      add (mul (sub one sel) (add x.v C)) (mul sel (npow (add (add x.v C) E) 7)) := by
  have hExp := sboxExpand_v a0 a1 (add (sboxMasked sel a0 a1 C x t).v (mul sel E)) t
    h2 h3 h4 h5 h6 h7
  have hMv : (sboxMasked sel a0 a1 C x t).v = mul sel (add (add x.v C) t.r1.v) := rfl
  have hLhs : (sboxOut sel a0 a1 C (add (sboxMasked sel a0 a1 C x t).v (mul sel E)) x t).v =
      add (mul (sub one sel) (add x.v C))
        (mul sel (sboxExpand a0 a1 (add (sboxMasked sel a0 a1 C x t).v (mul sel E)) t).v) := rfl
  rw [hLhs, hExp, hMv]
  have hInner : mul sel (sub (add (mul sel (add (add x.v C) t.r1.v)) (mul sel E)) t.r1.v) =
      mul sel (add (add x.v C) E) := by
    have h1 : mul sel (sub (add (mul sel (add (add x.v C) t.r1.v)) (mul sel E)) t.r1.v) =
        sub (mul (mul sel sel) (add (add (add x.v C) t.r1.v) E)) (mul sel t.r1.v) := by
      constructive_ring
    rw [h1, hs]
    constructive_ring
  rw [← idem_mul_pow7 hs (sub (add (mul sel (add (add x.v C) t.r1.v)) (mul sel E)) t.r1.v),
      hInner, idem_mul_pow7 hs]

theorem sboxMasked_authentic {A0 A1 : M} (sel C : M) {x : AShare M} {t : Pow7Share M}
    (hx : Authentic A0 A1 x) (ht : Authentic A0 A1 t.r1) :
    Authentic A0 A1 (sboxMasked sel A0 A1 C x t) :=
  Authentic.scale sel ((hx.add (Authentic.pub A0 A1 C)).add ht)

theorem sboxExpand_authentic {A0 A1 : M} (y : M) {t : Pow7Share M} (ht : Pow7Valid A0 A1 t) :
    Authentic A0 A1 (sboxExpand A0 A1 y t) := by
  have h0 := Authentic.pub A0 A1 (npow y 7)
  have h1 := h0.sub (Authentic.scale (mul (natCast 7) (npow y 6)) ht.auth1)
  have h2 := h1.add (Authentic.scale (mul (natCast 21) (npow y 5)) ht.auth2)
  have h3 := h2.sub (Authentic.scale (mul (natCast 35) (npow y 4)) ht.auth3)
  have h4 := h3.add (Authentic.scale (mul (natCast 35) (npow y 3)) ht.auth4)
  have h5 := h4.sub (Authentic.scale (mul (natCast 21) (npow y 2)) ht.auth5)
  have h6 := h5.add (Authentic.scale (mul (natCast 7) y) ht.auth6)
  exact h6.sub ht.auth7

theorem sboxOut_authentic {A0 A1 : M} (sel C y : M) {x : AShare M} {t : Pow7Share M}
    (hx : Authentic A0 A1 x) (ht : Pow7Valid A0 A1 t) :
    Authentic A0 A1 (sboxOut sel A0 A1 C y x t) :=
  (Authentic.scale _ (hx.add (Authentic.pub A0 A1 C))).add
    (Authentic.scale sel (sboxExpand_authentic y ht))

end Shares

/-! ## 2. Share-level evaluation of a substitution-permutation network, with an active adversary -/

/-- One round `x ↦ L ((1 - sel)·(x + C) + sel·(x + C)⁷)`: add the round constant, raise the
    lanes selected by the idempotent `sel` to the seventh power, apply the linear layer. -/
structure SpnRound (M : Type) where
  sel : M
  C : M
  L : M → M

/-- The active adversary of one evaluation. `valErr` is the additive error it puts on the next
    opened value, `macShift` the additive error on the two coordinates of the MAC residual of an
    opening; both are functions of every value opened so far (most recent first). -/
structure SpnTamper (M : Type) where
  valErr : List M → M
  macShift : List M → M × M

/-- State of a share-level evaluation: every server's share of the current state, the values
    opened so far and the MAC residual of each opening (most recent first). -/
structure SpnRun (n : Nat) (M : Type) where
  shares : Fin n → AShare M
  opened : List M
  resid : List (M × M)

/-- What the evaluation means on reconstructed values: the current value, the opened values, and
    for each opening the effective value error and MAC-residual error. It mentions no MAC key
    and no MAC share. -/
structure SpnValRun (M : Type) where
  x : M
  opened : List M
  trace : List (M × M × M)

section Spn
variable {M : Type} [LawfulCommRing M]

/-- Honest value of one round. -/
def SpnRound.eval (rd : SpnRound M) (x : M) : M :=
  rd.L (add (mul (sub one rd.sel) (add x rd.C)) (mul rd.sel (npow (add x rd.C) 7)))

/-- The function computed by a list of rounds. -/
def spnPlain : List (SpnRound M) → M → M
  | [], x => x
  | rd :: rest, x => spnPlain rest (rd.eval x)

/-- One round on shares: every server masks its share with its tuple share, the masked value is
    opened (the adversary adds `sel · valErr`), every server expands `(y - r)⁷` locally and
    applies the linear layer; the MAC residual `Σλᵢ(mᵢ - αᵢ·y)` of the opening is recorded with
    the adversary's shift. -/
def spnStep {n : Nat} (lam a0 a1 : Fin n → M) (adv : SpnTamper M) (rd : SpnRound M)
    (tup : Fin n → Pow7Share M) (run : SpnRun n M) : SpnRun n M :=
  let masked := aggShare lam (fun i => sboxMasked rd.sel (a0 i) (a1 i) rd.C (run.shares i) (tup i))
  let y := add masked.v (mul rd.sel (adv.valErr run.opened))
  let sh := adv.macShift (y :: run.opened)
  { shares := fun i => (sboxOut rd.sel (a0 i) (a1 i) rd.C y (run.shares i) (tup i)).map rd.L
    opened := y :: run.opened
    resid := (sub (add masked.m0 (mul rd.sel sh.1)) (mul (recSum lam a0) y),
              sub (add masked.m1 (mul rd.sel sh.2)) (mul (recSum lam a1) y)) :: run.resid }

def spnRun {n : Nat} (lam a0 a1 : Fin n → M) (adv : SpnTamper M) :
    List (SpnRound M × (Fin n → Pow7Share M)) → SpnRun n M → SpnRun n M
  | [], run => run
  | p :: rest, run => spnRun lam a0 a1 adv rest (spnStep lam a0 a1 adv p.1 p.2 run)

/-- Open the lanes selected by `sel` of the current state, with its MAC residual. -/
def spnOpen {n : Nat} (lam a0 a1 : Fin n → M) (adv : SpnTamper M) (sel : M)
    (run : SpnRun n M) : SpnRun n M :=
  let masked := aggShare lam (fun i => AShare.scale sel (run.shares i))
  let y := add masked.v (mul sel (adv.valErr run.opened))
  let sh := adv.macShift (y :: run.opened)
  { shares := run.shares
    opened := y :: run.opened
    resid := (sub (add masked.m0 (mul sel sh.1)) (mul (recSum lam a0) y),
              sub (add masked.m1 (mul sel sh.2)) (mul (recSum lam a1) y)) :: run.resid }

def spnValStep (adv : SpnTamper M) (rd : SpnRound M) (r : M) (vr : SpnValRun M) : SpnValRun M :=
  let y := add (mul rd.sel (add (add vr.x rd.C) r)) (mul rd.sel (adv.valErr vr.opened))
  let sh := adv.macShift (y :: vr.opened)
  { x := rd.L (add (mul (sub one rd.sel) (add vr.x rd.C))
        (mul rd.sel (npow (add (add vr.x rd.C) (adv.valErr vr.opened)) 7)))
    opened := y :: vr.opened
    trace := (mul rd.sel (adv.valErr vr.opened), mul rd.sel sh.1, mul rd.sel sh.2) :: vr.trace }

def spnValRun (adv : SpnTamper M) : List (SpnRound M × M) → SpnValRun M → SpnValRun M
  | [], vr => vr
  | p :: rest, vr => spnValRun adv rest (spnValStep adv p.1 p.2 vr)

def spnValOpen (adv : SpnTamper M) (sel : M) (vr : SpnValRun M) : SpnValRun M :=
  let y := add (mul sel vr.x) (mul sel (adv.valErr vr.opened))
  let sh := adv.macShift (y :: vr.opened)
  { x := vr.x
    opened := y :: vr.opened
    trace := (mul sel (adv.valErr vr.opened), mul sel sh.1, mul sel sh.2) :: vr.trace }

/-- MAC residual of an opening with value error `e` and residual error `(d0, d1)` under the MAC
    key `(A0, A1)`: `d - α·e`. -/
def residOf (A0 A1 : M) (t : M × M × M) : M × M :=
  (sub t.2.1 (mul A0 t.1), sub t.2.2 (mul A1 t.1))

/-- The share-level run and the value-level run agree: the reconstructed state is authentic and
    has the value-level value, the openings coincide, and every recorded residual is `d - α·e`
    for the value-level error entry. -/
structure SpnSim {n : Nat} (lam : Fin n → M) (A0 A1 : M) (run : SpnRun n M)
    (vr : SpnValRun M) : Prop where
  auth : Authentic A0 A1 (aggShare lam run.shares)
  value : (aggShare lam run.shares).v = vr.x
  opened : run.opened = vr.opened
  resid : run.resid = vr.trace.map (residOf A0 A1)

/-- Hypotheses on one round and its tuple under which the round preserves `SpnSim`. -/
structure RoundOk {n : Nat} (lam : Fin n → M) (A0 A1 : M)
    (p : SpnRound M × (Fin n → Pow7Share M)) : Prop where
  idem : mul p.1.sel p.1.sel = p.1.sel
  additive : ∀ x y, p.1.L (add x y) = add (p.1.L x) (p.1.L y)
  central : ∀ i x, p.1.L (mul (lam i) x) = mul (lam i) (p.1.L x)
  central0 : ∀ x, p.1.L (mul A0 x) = mul A0 (p.1.L x)
  central1 : ∀ x, p.1.L (mul A1 x) = mul A1 (p.1.L x)
  tuple : Pow7Valid A0 A1 (aggPow7 lam p.2)

theorem spnStep_sim {n : Nat} (lam a0 a1 : Fin n → M) (hOne : linSum n lam = one)
    (adv : SpnTamper M) (p : SpnRound M × (Fin n → Pow7Share M))
    (hp : RoundOk lam (recSum lam a0) (recSum lam a1) p)
    {run : SpnRun n M} {vr : SpnValRun M}
    (h : SpnSim lam (recSum lam a0) (recSum lam a1) run vr) :
    SpnSim lam (recSum lam a0) (recSum lam a1) (spnStep lam a0 a1 adv p.1 p.2 run)
      (spnValStep adv p.1 (aggPow7 lam p.2).r1.v vr) := by
  have hT := hp.tuple
  have hMaskedEq := aggShare_sboxMasked lam hOne p.1.sel p.1.C a0 a1 run.shares p.2
  have hMaskedAuth := sboxMasked_authentic p.1.sel p.1.C h.auth hT.auth1
  have hMv : (sboxMasked p.1.sel (recSum lam a0) (recSum lam a1) p.1.C (aggShare lam run.shares)
      (aggPow7 lam p.2)).v =
      mul p.1.sel (add (add vr.x p.1.C) (aggPow7 lam p.2).r1.v) := by
    rw [← h.value]; rfl
  have hY : add (aggShare lam (fun i => sboxMasked p.1.sel (a0 i) (a1 i) p.1.C (run.shares i)
      (p.2 i))).v (mul p.1.sel (adv.valErr run.opened)) =
      add (mul p.1.sel (add (add vr.x p.1.C) (aggPow7 lam p.2).r1.v))
        (mul p.1.sel (adv.valErr vr.opened)) := by
    rw [hMaskedEq, hMv, h.opened]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show Authentic _ _ (aggShare lam (fun i => (sboxOut p.1.sel (a0 i) (a1 i) p.1.C _
      (run.shares i) (p.2 i)).map p.1.L))
    rw [aggShare_map lam hp.additive hp.central, aggShare_sboxOut lam hOne]
    exact Authentic.map hp.central0 hp.central1 (sboxOut_authentic _ _ _ h.auth hT)
  · show (aggShare lam (fun i => (sboxOut p.1.sel (a0 i) (a1 i) p.1.C _
      (run.shares i) (p.2 i)).map p.1.L)).v = _
    rw [aggShare_map lam hp.additive hp.central, aggShare_sboxOut lam hOne, hMaskedEq]
    show p.1.L (sboxOut p.1.sel (recSum lam a0) (recSum lam a1) p.1.C _ (aggShare lam run.shares)
      (aggPow7 lam p.2)).v = _
    rw [sboxOut_v hp.idem _ _ _ _ _ _ hT.pow2 hT.pow3 hT.pow4 hT.pow5 hT.pow6 hT.pow7,
        h.value, h.opened]
    rfl
  · show _ :: run.opened = _ :: vr.opened
    rw [hY, h.opened]
  · show _ :: run.resid = _ :: vr.trace.map (residOf (recSum lam a0) (recSum lam a1))
    rw [h.resid, hY]
    congr 1
    rw [hMaskedEq, hMaskedAuth.1, hMaskedAuth.2, hMv, h.opened]
    unfold residOf
    dsimp only
    congr 1 <;> constructive_ring

theorem spnRun_sim {n : Nat} (lam a0 a1 : Fin n → M) (hOne : linSum n lam = one)
    (adv : SpnTamper M) :
    ∀ (l : List (SpnRound M × (Fin n → Pow7Share M))),
      (∀ p ∈ l, RoundOk lam (recSum lam a0) (recSum lam a1) p) →
      ∀ {run : SpnRun n M} {vr : SpnValRun M},
        SpnSim lam (recSum lam a0) (recSum lam a1) run vr →
        SpnSim lam (recSum lam a0) (recSum lam a1) (spnRun lam a0 a1 adv l run)
          (spnValRun adv (l.map (fun p => (p.1, (aggPow7 lam p.2).r1.v))) vr)
  | [], _, _, _, h => h
  | p :: rest, hOk, _, _, h =>
    spnRun_sim lam a0 a1 hOne adv rest (fun q hq => hOk q (List.mem_cons_of_mem p hq))
      (spnStep_sim lam a0 a1 hOne adv p (hOk p (List.mem_cons_self ..)) h)

theorem spnOpen_sim {n : Nat} (lam a0 a1 : Fin n → M) (adv : SpnTamper M) (sel : M)
    {run : SpnRun n M} {vr : SpnValRun M}
    (h : SpnSim lam (recSum lam a0) (recSum lam a1) run vr) :
    SpnSim lam (recSum lam a0) (recSum lam a1) (spnOpen lam a0 a1 adv sel run)
      (spnValOpen adv sel vr) := by
  have hAuth := Authentic.scale sel h.auth
  have hV : (AShare.scale sel (aggShare lam run.shares)).v = mul sel vr.x := by
    rw [← h.value]; rfl
  have hY : add (aggShare lam (fun i => AShare.scale sel (run.shares i))).v
      (mul sel (adv.valErr run.opened)) =
      add (mul sel vr.x) (mul sel (adv.valErr vr.opened)) := by
    rw [aggShare_scale, hV, h.opened]
  refine ⟨h.auth, h.value, ?_, ?_⟩
  · show _ :: run.opened = _ :: vr.opened
    rw [hY, h.opened]
  · show _ :: run.resid = _ :: vr.trace.map (residOf (recSum lam a0) (recSum lam a1))
    rw [h.resid, hY]
    congr 1
    rw [aggShare_scale, hAuth.1, hAuth.2, hV, h.opened]
    unfold residOf
    dsimp only
    congr 1 <;> constructive_ring

/-- The value opened by `spnValOpen`. -/
def spnValOut (adv : SpnTamper M) (sel : M) (vr : SpnValRun M) : M :=
  add (mul sel vr.x) (mul sel (adv.valErr vr.opened))

theorem spnValRun_trace_mem (adv : SpnTamper M) :
    ∀ (l : List (SpnRound M × M)) (vr : SpnValRun M) (t : M × M × M),
      t ∈ vr.trace → t ∈ (spnValRun adv l vr).trace
  | [], _, _, h => h
  | p :: rest, vr, t, h =>
    spnValRun_trace_mem adv rest (spnValStep adv p.1 p.2 vr) t (List.mem_cons_of_mem _ h)

/-- A round whose effective opening error `sel · valErr` is zero computes the honest round. -/
theorem spnValStep_clean (adv : SpnTamper M) (rd : SpnRound M) (r : M) (vr : SpnValRun M)
    (hs : mul rd.sel rd.sel = rd.sel) (hE : mul rd.sel (adv.valErr vr.opened) = zero) :
    (spnValStep adv rd r vr).x = rd.eval vr.x := by
  have hInner : mul rd.sel (add (add vr.x rd.C) (adv.valErr vr.opened)) =
      mul rd.sel (add vr.x rd.C) := by
    rw [LawfulCommRing.left_distrib, hE, LawfulCommRing.add_zero]
  show rd.L (add (mul (sub one rd.sel) (add vr.x rd.C))
      (mul rd.sel (npow (add (add vr.x rd.C) (adv.valErr vr.opened)) 7))) = rd.eval vr.x
  rw [← idem_mul_pow7 hs (add (add vr.x rd.C) (adv.valErr vr.opened)), hInner, idem_mul_pow7 hs]
  rfl

/-- An evaluation whose trace has no value error computes `spnPlain`. -/
theorem spnValRun_clean (adv : SpnTamper M) :
    ∀ (l : List (SpnRound M × M)) (vr : SpnValRun M),
      (∀ p ∈ l, mul p.1.sel p.1.sel = p.1.sel) →
      (∀ t ∈ (spnValRun adv l vr).trace, t.1 = zero) →
      (spnValRun adv l vr).x = spnPlain (l.map Prod.fst) vr.x
  | [], _, _, _ => rfl
  | p :: rest, vr, hIdem, hZero => by
    have hHead : mul p.1.sel (adv.valErr vr.opened) = zero :=
      hZero _ (spnValRun_trace_mem adv rest (spnValStep adv p.1 p.2 vr) _ (List.mem_cons_self ..))
    have ih := spnValRun_clean adv rest (spnValStep adv p.1 p.2 vr)
      (fun q hq => hIdem q (List.mem_cons_of_mem p hq)) hZero
    have hStep := spnValStep_clean adv p.1 p.2 vr (hIdem p (List.mem_cons_self ..)) hHead
    show (spnValRun adv rest (spnValStep adv p.1 p.2 vr)).x =
      spnPlain (rest.map Prod.fst) (p.1.eval vr.x)
    rw [ih, hStep]

/-- **Value-level soundness of the MAC check.** If every recorded residual `d - α·e` of an
    evaluation followed by an output opening is zero, then either the opened output is the
    selected lanes of the honest function value, or some opening carries a nonzero value error
    `e` together with the matching MAC error `d = α·e`. -/
theorem spnVal_sound_or_forgery [DecidableEq M] (adv : SpnTamper M)
    (l : List (SpnRound M × M)) (selOut x0 A0 A1 : M)
    (hIdem : ∀ p ∈ l, mul p.1.sel p.1.sel = p.1.sel)
    (hRes : ∀ t ∈ (spnValOpen adv selOut (spnValRun adv l ⟨x0, [], []⟩)).trace,
      residOf A0 A1 t = (zero, zero)) :
    spnValOut adv selOut (spnValRun adv l ⟨x0, [], []⟩) =
        mul selOut (spnPlain (l.map Prod.fst) x0) ∨
    ∃ t ∈ (spnValOpen adv selOut (spnValRun adv l ⟨x0, [], []⟩)).trace,
      t.1 ≠ zero ∧ t.2.1 = mul A0 t.1 ∧ t.2.2 = mul A1 t.1 := by
  cases hFind : (spnValOpen adv selOut (spnValRun adv l ⟨x0, [], []⟩)).trace.find?
      (fun t => !decide (t.1 = zero)) with
  | some t =>
    have hMem := List.mem_of_find?_eq_some hFind
    have hP : (!decide (t.1 = zero)) = true :=
      List.find?_some (p := fun t : M × M × M => !decide (t.1 = zero)) hFind
    have hNe : t.1 ≠ zero := fun h0 => by
      rw [decide_eq_true h0] at hP
      cases hP
    have hR := hRes t hMem
    unfold residOf at hR
    obtain ⟨h0, h1⟩ := Prod.mk.inj hR
    exact Or.inr ⟨t, hMem, hNe, LawfulCommRing.sub_eq_zero_iff.mp h0,
      LawfulCommRing.sub_eq_zero_iff.mp h1⟩
  | none =>
    have hAll : ∀ t ∈ (spnValOpen adv selOut (spnValRun adv l ⟨x0, [], []⟩)).trace,
        t.1 = zero := by
      intro t ht
      have hNot := List.find?_eq_none.mp hFind t ht
      cases hD : decide (t.1 = zero) with
      | true => exact of_decide_eq_true hD
      | false =>
        rw [hD] at hNot
        exact absurd rfl hNot
    have hOutErr : mul selOut (adv.valErr (spnValRun adv l ⟨x0, [], []⟩).opened) = zero :=
      hAll _ (List.mem_cons_self ..)
    have hClean := spnValRun_clean adv l ⟨x0, [], []⟩ hIdem
      (fun t ht => hAll t (List.mem_cons_of_mem _ ht))
    refine Or.inl ?_
    unfold spnValOut
    rw [hOutErr, LawfulCommRing.add_zero, hClean]

end Spn

/-! ## 3. The lane-wise ring on `Poseidon2State12` and `Poseidon2` as a list of rounds -/

/-- Lane-wise binary operation on a width-12 state. -/
def stMap2 (f : Goldilocks → Goldilocks → Goldilocks) (a b : Poseidon2State12) :
    Poseidon2State12 :=
  ⟨⟨f a.b0.x0 b.b0.x0, f a.b0.x1 b.b0.x1, f a.b0.x2 b.b0.x2, f a.b0.x3 b.b0.x3⟩,
   ⟨f a.b1.x0 b.b1.x0, f a.b1.x1 b.b1.x1, f a.b1.x2 b.b1.x2, f a.b1.x3 b.b1.x3⟩,
   ⟨f a.b2.x0 b.b2.x0, f a.b2.x1 b.b2.x1, f a.b2.x2 b.b2.x2, f a.b2.x3 b.b2.x3⟩⟩

/-- The state all of whose lanes are `c`: the embedding of a base-field scalar. -/
def stConst (c : Goldilocks) : Poseidon2State12 :=
  ⟨⟨c, c, c, c⟩, ⟨c, c, c, c⟩, ⟨c, c, c, c⟩⟩

/-- The product ring `Goldilocks¹²` on width-12 states: every operation acts lane by lane. -/
@[reducible] def stRing : LawfulCommRing Poseidon2State12 where
  zero := stConst zero
  one := stConst one
  add := stMap2 add
  mul := stMap2 mul
  neg := fun a => stMap2 (fun x _ => neg x) a a
  sub := stMap2 sub
  add_assoc a b c := by
    apply Poseidon2State12.ext <;> apply Lane4.ext <;> exact LawfulCommRing.add_assoc _ _ _
  add_comm a b := by
    apply Poseidon2State12.ext <;> apply Lane4.ext <;> exact LawfulCommRing.add_comm _ _
  zero_add a := by
    apply Poseidon2State12.ext <;> apply Lane4.ext <;> exact LawfulCommRing.zero_add _
  add_zero a := by
    apply Poseidon2State12.ext <;> apply Lane4.ext <;> exact LawfulCommRing.add_zero _
  add_left_neg a := by
    apply Poseidon2State12.ext <;> apply Lane4.ext <;> exact LawfulCommRing.add_left_neg _
  sub_eq_add_neg a b := by
    apply Poseidon2State12.ext <;> apply Lane4.ext <;> exact LawfulCommRing.sub_eq_add_neg _ _
  mul_assoc a b c := by
    apply Poseidon2State12.ext <;> apply Lane4.ext <;> exact LawfulCommRing.mul_assoc _ _ _
  mul_comm a b := by
    apply Poseidon2State12.ext <;> apply Lane4.ext <;> exact LawfulCommRing.mul_comm _ _
  one_mul a := by
    apply Poseidon2State12.ext <;> apply Lane4.ext <;> exact LawfulCommRing.one_mul _
  mul_one a := by
    apply Poseidon2State12.ext <;> apply Lane4.ext <;> exact LawfulCommRing.mul_one _
  left_distrib a b c := by
    apply Poseidon2State12.ext <;> apply Lane4.ext <;> exact LawfulCommRing.left_distrib _ _ _
  right_distrib a b c := by
    apply Poseidon2State12.ext <;> apply Lane4.ext <;> exact LawfulCommRing.right_distrib _ _ _

attribute [scoped instance] stRing

theorem st_add_eq (a b : Poseidon2State12) : add a b = stMap2 add a b := by rfl
theorem st_mul_eq (a b : Poseidon2State12) : mul a b = stMap2 mul a b := by rfl
theorem st_sub_eq (a b : Poseidon2State12) : sub a b = stMap2 sub a b := by rfl
theorem st_one_eq : (one : Poseidon2State12) = stConst one := by rfl
theorem st_zero_eq : (zero : Poseidon2State12) = stConst zero := by rfl

theorem stConst_add (a b : Goldilocks) : stConst (add a b) = add (stConst a) (stConst b) := by rfl
theorem stConst_mul (a b : Goldilocks) : stConst (mul a b) = mul (stConst a) (stConst b) := by rfl

theorem stConst_linSum : ∀ (n : Nat) (f : Fin n → Goldilocks),
    linSum n (fun i => stConst (f i)) = stConst (linSum n f)
  | 0, _ => rfl
  | n + 1, f => by
    unfold linSum
    dsimp only
    rw [stConst_linSum n, stConst_add]

theorem stConst_recSum {n : Nat} (lam f : Fin n → Goldilocks) :
    recSum (fun i => stConst (lam i)) (fun i => stConst (f i)) = stConst (recSum lam f) := by
  unfold recSum
  rw [← stConst_linSum]
  rfl

theorem state12Add_eq_add (a b : Poseidon2State12) : state12Add a b = add a b := by
  rw [state12Add_eq, lane4Add_eq, lane4Add_eq, lane4Add_eq]
  rfl

theorem state12Scale_eq_mul (c : Goldilocks) (a : Poseidon2State12) :
    state12Scale c a = mul (stConst c) a := by
  rw [state12Scale_eq, lane4Scale_eq, lane4Scale_eq, lane4Scale_eq]
  rfl

theorem sbox7_eq_npow (x : Goldilocks) : sbox7 x = npow x 7 := by
  show mul (mul (mul x x) x) (mul (mul x x) (mul x x)) = npow x 7
  constructive_ring

theorem st_npow7_eq (a : Poseidon2State12) :
    npow a 7 = ⟨⟨npow a.b0.x0 7, npow a.b0.x1 7, npow a.b0.x2 7, npow a.b0.x3 7⟩,
                ⟨npow a.b1.x0 7, npow a.b1.x1 7, npow a.b1.x2 7, npow a.b1.x3 7⟩,
                ⟨npow a.b2.x0 7, npow a.b2.x1 7, npow a.b2.x2 7, npow a.b2.x3 7⟩⟩ := by
  apply Poseidon2State12.ext <;> apply Lane4.ext <;> rfl

theorem sboxState12_eq_npow (a : Poseidon2State12) : sboxState12 a = npow a 7 := by
  rw [sboxState12_eq, st_npow7_eq]
  simp only [sbox7_eq_npow]

/-- The state with `c` on lane 0 and zero elsewhere; `stLane0 one` is the idempotent selecting
    the single S-box lane of an internal round. -/
def stLane0 (c : Goldilocks) : Poseidon2State12 :=
  ⟨⟨c, zero, zero, zero⟩, ⟨zero, zero, zero, zero⟩, ⟨zero, zero, zero, zero⟩⟩

/-- The idempotent selecting the four output lanes. -/
def selOut : Poseidon2State12 :=
  ⟨⟨one, one, one, one⟩, ⟨zero, zero, zero, zero⟩, ⟨zero, zero, zero, zero⟩⟩

/-- An external round: constant on all lanes, S-box on all lanes, `applyME`. -/
def extRound (rc : Poseidon2State12) : SpnRound Poseidon2State12 := ⟨one, rc, applyME⟩

/-- An internal round: constant and S-box on lane 0 only, `applyMI`. -/
def intRound (rc : Goldilocks) : SpnRound Poseidon2State12 := ⟨stLane0 one, stLane0 rc, applyMI⟩

theorem extRound_eval (rc st : Poseidon2State12) :
    (extRound rc).eval st = externalRound rc st := by
  rw [externalRound_eq, sboxState12_eq_npow, state12Add_eq_add]
  show applyME (add (mul (sub one one) (add st rc)) (mul one (npow (add st rc) 7))) = _
  congr 1
  constructive_ring

private theorem lane_keep (x : Goldilocks) :
    add (mul (sub one zero) (add x zero)) (mul zero (npow (add x zero) 7)) = x := by
  constructive_ring

private theorem lane_sbox (x rc : Goldilocks) :
    add (mul (sub one one) (add x rc)) (mul one (npow (add x rc) 7)) =
      sbox7 (Goldilocks.add x rc) := by
  rw [sbox7_eq_npow]
  show _ = npow (add x rc) 7
  constructive_ring

theorem intRound_eval (rc : Goldilocks) (st : Poseidon2State12) :
    (intRound rc).eval st = internalRound rc st := by
  rw [internalRound_eq]
  show applyMI (add (mul (sub one (stLane0 one)) (add st (stLane0 rc)))
    (mul (stLane0 one) (npow (add st (stLane0 rc)) 7))) = _
  rw [st_npow7_eq]
  congr 1
  exact Poseidon2State12.ext
    (Lane4.ext (lane_sbox st.b0.x0 rc) (lane_keep st.b0.x1) (lane_keep st.b0.x2)
      (lane_keep st.b0.x3))
    (Lane4.ext (lane_keep st.b1.x0) (lane_keep st.b1.x1) (lane_keep st.b1.x2)
      (lane_keep st.b1.x3))
    (Lane4.ext (lane_keep st.b2.x0) (lane_keep st.b2.x1) (lane_keep st.b2.x2)
      (lane_keep st.b2.x3))

/-- The 30 rounds of the width-12 `Poseidon2` permutation after its initial linear layer. -/
def poseidonRounds : List (SpnRound Poseidon2State12) :=
  poseidon2InitialExtConsts.map extRound ++
    (poseidon2InternalConsts.map intRound ++ poseidon2TerminalExtConsts.map extRound)

theorem spnPlain_append {M : Type} [LawfulCommRing M] :
    ∀ (l₁ l₂ : List (SpnRound M)) (x : M),
      spnPlain (l₁ ++ l₂) x = spnPlain l₂ (spnPlain l₁ x)
  | [], _, _ => rfl
  | rd :: rest, l₂, x => spnPlain_append rest l₂ (rd.eval x)

theorem runRounds_ext_eq : ∀ (cs : List Poseidon2State12) (s : Poseidon2State12),
    runRounds externalRound cs s = spnPlain (cs.map extRound) s
  | [], s => runRounds_nil externalRound s
  | c :: cs, s => by
    rw [runRounds_cons, runRounds_ext_eq cs, ← extRound_eval]
    rfl

theorem runRounds_int_eq : ∀ (cs : List Goldilocks) (s : Poseidon2State12),
    runRounds internalRound cs s = spnPlain (cs.map intRound) s
  | [], s => runRounds_nil internalRound s
  | c :: cs, s => by
    rw [runRounds_cons, runRounds_int_eq cs, ← intRound_eval]
    rfl

/-- `poseidon2Perm12` is the initial linear layer followed by `poseidonRounds`. -/
theorem poseidon2Perm12_eq_spnPlain (st : Poseidon2State12) :
    poseidon2Perm12 st = spnPlain poseidonRounds (applyME st) := by
  unfold poseidon2Perm12 poseidonRounds
  dsimp only
  rw [spnPlain_append, spnPlain_append, runRounds_ext_eq, runRounds_int_eq, runRounds_ext_eq]

theorem applyME_additive (x y : Poseidon2State12) :
    applyME (add x y) = add (applyME x) (applyME y) := by
  rw [← state12Add_eq_add, applyME_add, state12Add_eq_add]

theorem applyME_central (c : Goldilocks) (x : Poseidon2State12) :
    applyME (mul (stConst c) x) = mul (stConst c) (applyME x) := by
  rw [← state12Scale_eq_mul, applyME_scale, state12Scale_eq_mul]

theorem applyMI_additive (x y : Poseidon2State12) :
    applyMI (add x y) = add (applyMI x) (applyMI y) := by
  rw [← state12Add_eq_add, applyMI_add, state12Add_eq_add]

theorem applyMI_central (c : Goldilocks) (x : Poseidon2State12) :
    applyMI (mul (stConst c) x) = mul (stConst c) (applyMI x) := by
  rw [← state12Scale_eq_mul, applyMI_scale, state12Scale_eq_mul]

theorem stLane0_one_idem : mul (stLane0 one) (stLane0 one) = stLane0 one :=
  Poseidon2State12.ext
    (Lane4.ext (LawfulCommRing.mul_one one) (LawfulCommRing.mul_zero zero)
      (LawfulCommRing.mul_zero zero) (LawfulCommRing.mul_zero zero))
    (Lane4.ext (LawfulCommRing.mul_zero zero) (LawfulCommRing.mul_zero zero)
      (LawfulCommRing.mul_zero zero) (LawfulCommRing.mul_zero zero))
    (Lane4.ext (LawfulCommRing.mul_zero zero) (LawfulCommRing.mul_zero zero)
      (LawfulCommRing.mul_zero zero) (LawfulCommRing.mul_zero zero))

theorem selOut_idem : mul selOut selOut = selOut :=
  Poseidon2State12.ext
    (Lane4.ext (LawfulCommRing.mul_one one) (LawfulCommRing.mul_one one)
      (LawfulCommRing.mul_one one) (LawfulCommRing.mul_one one))
    (Lane4.ext (LawfulCommRing.mul_zero zero) (LawfulCommRing.mul_zero zero)
      (LawfulCommRing.mul_zero zero) (LawfulCommRing.mul_zero zero))
    (Lane4.ext (LawfulCommRing.mul_zero zero) (LawfulCommRing.mul_zero zero)
      (LawfulCommRing.mul_zero zero) (LawfulCommRing.mul_zero zero))

/-- Every `Poseidon2` round has an idempotent selector and a linear layer that is additive and
    commutes with multiplication by base-field scalars. -/
theorem poseidonRounds_ok {rd : SpnRound Poseidon2State12} (h : rd ∈ poseidonRounds) :
    mul rd.sel rd.sel = rd.sel ∧ (∀ x y, rd.L (add x y) = add (rd.L x) (rd.L y)) ∧
      ∀ (c : Goldilocks) x, rd.L (mul (stConst c) x) = mul (stConst c) (rd.L x) := by
  unfold poseidonRounds at h
  rcases List.mem_append.mp h with h | h
  · obtain ⟨rc, _, rfl⟩ := List.mem_map.mp h
    exact ⟨LawfulCommRing.mul_one _, applyME_additive, applyME_central⟩
  · rcases List.mem_append.mp h with h | h
    · obtain ⟨rc, _, rfl⟩ := List.mem_map.mp h
      exact ⟨stLane0_one_idem, applyMI_additive, applyMI_central⟩
    · obtain ⟨rc, _, rfl⟩ := List.mem_map.mp h
      exact ⟨LawfulCommRing.mul_one _, applyME_additive, applyME_central⟩

/-! ## 4. The algebraic PRF and its evaluation from server shares -/

/-- `SPONGE_DOMAIN` of `voprf.rs`. -/
def toprfDomain : Goldilocks := Goldilocks.ofNat 0x544f50524631

/-- The public part of the TOPRF input state: the four input lanes, `1` on lane 4 and the
    domain constant on lane 7 (`voprf_spdz.rs`, `evaluate_inner`). -/
def toprfInput (x : Lane4) : Poseidon2State12 :=
  ⟨x, ⟨one, zero, zero, toprfDomain⟩, ⟨zero, zero, zero, zero⟩⟩

/-- The key on lanes 8 to 11. -/
def keyState (k : Lane4) : Poseidon2State12 :=
  ⟨⟨zero, zero, zero, zero⟩, ⟨zero, zero, zero, zero⟩, k⟩

def toprfState (k x : Lane4) : Poseidon2State12 :=
  ⟨x, ⟨one, zero, zero, toprfDomain⟩, k⟩

/-- The algebraic PRF computed by the SPDZ TOPRF of `voprf_spdz.rs`: the first four lanes of
    `poseidon2Perm12` on the state holding the input, the two domain constants and the key. -/
def evalAlgebraicOprf (k x : Lane4) : Lane4 := (poseidon2Perm12 (toprfState k x)).b0

theorem toprfInput_add_keyState (k x : Lane4) :
    add (toprfInput x) (keyState k) = toprfState k x :=
  Poseidon2State12.ext
    (Lane4.ext (LawfulCommRing.add_zero x.x0) (LawfulCommRing.add_zero x.x1)
      (LawfulCommRing.add_zero x.x2) (LawfulCommRing.add_zero x.x3))
    (Lane4.ext (LawfulCommRing.add_zero one) (LawfulCommRing.add_zero zero)
      (LawfulCommRing.add_zero zero) (LawfulCommRing.add_zero toprfDomain))
    (Lane4.ext (LawfulCommRing.zero_add k.x0) (LawfulCommRing.zero_add k.x1)
      (LawfulCommRing.zero_add k.x2) (LawfulCommRing.zero_add k.x3))

theorem selOut_mul_b0 (a : Poseidon2State12) : (mul selOut a).b0 = a.b0 :=
  Lane4.ext (LawfulCommRing.one_mul a.b0.x0) (LawfulCommRing.one_mul a.b0.x1)
    (LawfulCommRing.one_mul a.b0.x2) (LawfulCommRing.one_mul a.b0.x3)

/-! ### Lanes of a state and of a MAC residual -/

def stLane (a : Poseidon2State12) : Fin 12 → Goldilocks
  | ⟨0, _⟩ => a.b0.x0 | ⟨1, _⟩ => a.b0.x1 | ⟨2, _⟩ => a.b0.x2 | ⟨3, _⟩ => a.b0.x3
  | ⟨4, _⟩ => a.b1.x0 | ⟨5, _⟩ => a.b1.x1 | ⟨6, _⟩ => a.b1.x2 | ⟨7, _⟩ => a.b1.x3
  | ⟨8, _⟩ => a.b2.x0 | ⟨9, _⟩ => a.b2.x1 | ⟨10, _⟩ => a.b2.x2 | ⟨_ + 11, _⟩ => a.b2.x3

theorem st_ext_lane {a b : Poseidon2State12} (h : ∀ ℓ, stLane a ℓ = stLane b ℓ) : a = b :=
  Poseidon2State12.ext
    (Lane4.ext (h ⟨0, by decide⟩) (h ⟨1, by decide⟩) (h ⟨2, by decide⟩) (h ⟨3, by decide⟩))
    (Lane4.ext (h ⟨4, by decide⟩) (h ⟨5, by decide⟩) (h ⟨6, by decide⟩) (h ⟨7, by decide⟩))
    (Lane4.ext (h ⟨8, by decide⟩) (h ⟨9, by decide⟩) (h ⟨10, by decide⟩) (h ⟨11, by decide⟩))

theorem stLane_zero : ∀ ℓ : Fin 12, stLane zero ℓ = zero
  | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl | ⟨5, _⟩ => rfl | ⟨6, _⟩ => rfl | ⟨7, _⟩ => rfl
  | ⟨8, _⟩ => rfl | ⟨9, _⟩ => rfl | ⟨10, _⟩ => rfl | ⟨_ + 11, _⟩ => rfl

theorem stLane_mul_const (c : Goldilocks) (a : Poseidon2State12) :
    ∀ ℓ : Fin 12, stLane (mul (stConst c) a) ℓ = mul c (stLane a ℓ)
  | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl | ⟨2, _⟩ => rfl | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl | ⟨5, _⟩ => rfl | ⟨6, _⟩ => rfl | ⟨7, _⟩ => rfl
  | ⟨8, _⟩ => rfl | ⟨9, _⟩ => rfl | ⟨10, _⟩ => rfl | ⟨_ + 11, _⟩ => rfl

theorem exists_lane_ne_zero {e : Poseidon2State12} (h : e ≠ zero) :
    ∃ ℓ, stLane e ℓ ≠ zero := by
  cases hF : (List.finRange 12).find? (fun ℓ => !decide (stLane e ℓ = zero)) with
  | some ℓ =>
    have hP : (!decide (stLane e ℓ = zero)) = true :=
      List.find?_some (p := fun ℓ : Fin 12 => !decide (stLane e ℓ = zero)) hF
    refine ⟨ℓ, fun h0 => ?_⟩
    rw [decide_eq_true h0] at hP
    cases hP
  | none =>
    refine absurd (st_ext_lane (fun ℓ => ?_)) h
    have hNot := List.find?_eq_none.mp hF ℓ (List.mem_finRange ℓ)
    rw [stLane_zero]
    cases hD : decide (stLane e ℓ = zero) with
    | true => exact of_decide_eq_true hD
    | false =>
      rw [hD] at hNot
      exact absurd rfl hNot

/-- The twelve `GoldilocksExt2` lanes of a pair of coordinate states. -/
def ext2Lanes (p : Poseidon2State12 × Poseidon2State12) : List GoldilocksExt2 :=
  (List.finRange 12).map (fun ℓ => ⟨stLane p.1 ℓ, stLane p.2 ℓ⟩)

theorem ext2Lanes_zero {p : Poseidon2State12 × Poseidon2State12}
    (h : ∀ d ∈ ext2Lanes p, d = zero) : p = (zero, zero) := by
  have hl : ∀ ℓ, stLane p.1 ℓ = zero ∧ stLane p.2 ℓ = zero := fun ℓ => by
    have hd := h ⟨stLane p.1 ℓ, stLane p.2 ℓ⟩
      (List.mem_map.mpr ⟨ℓ, List.mem_finRange ℓ, rfl⟩)
    exact ⟨(congrArg GoldilocksExt2.c0 hd).trans GoldilocksExt2.ringZero_c0,
      (congrArg GoldilocksExt2.c1 hd).trans GoldilocksExt2.ringZero_c1⟩
  exact Prod.ext (st_ext_lane fun ℓ => (hl ℓ).1.trans (stLane_zero ℓ).symm)
    (st_ext_lane fun ℓ => (hl ℓ).2.trans (stLane_zero ℓ).symm)

theorem ext2_mul_ofBase (a : GoldilocksExt2) (v : Goldilocks) :
    mul a (GoldilocksExt2.ofBase v) = ⟨mul a.c0 v, mul a.c1 v⟩ := by
  apply GoldilocksExt2.ext
  · rw [GoldilocksExt2.mul_c0]
    show add (mul a.c0 v) (mul GoldilocksExt2.nonResidue (mul a.c1 zero)) = mul a.c0 v
    rw [LawfulCommRing.mul_zero, LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  · rw [GoldilocksExt2.mul_c1]
    show add (mul a.c0 zero) (mul a.c1 v) = mul a.c1 v
    rw [LawfulCommRing.mul_zero, LawfulCommRing.zero_add]

/-! ### Blinded opening of the residual lanes (`MacBlind.macBlindPure`) -/

/-- The blinded residual openings `w = (r_honest + r_corrupt) · σ`, one per residual lane. -/
def blindList (rC : Nat → GoldilocksExt2) :
    Nat → List GoldilocksExt2 → List GoldilocksExt2 → List GoldilocksExt2
  | j, r :: rs, d :: ds => MacBlind.macBlindPure r (rC j) d :: blindList rC (j + 1) rs ds
  | _, _, _ => []

/-- Some honest blinding randomizer is cancelled by the corrupt one (`r_honest + r_corrupt = 0`):
    that lane's blinded opening is zero whatever its residual. -/
@[expose] def blindDegenerate (rC : Nat → GoldilocksExt2) : Nat → List GoldilocksExt2 → Bool
  | _, [] => false
  | j, r :: rs => decide (add r (rC j) = zero) || blindDegenerate rC (j + 1) rs

