module
/- Canonical decoded x86-64 and AArch64 state, instruction, and step semantics.
Byte decoders and execution share these exact instruction constructors. -/
public import Qsag.Machine.IsaFetch
public import Qsag.Spec.Refines
public import Qsag.Math.Goldilocks
public import Qsag.Oracle.Keccak
public import Qsag.Math.Gf2Pow128
import Qsag.Tactic.AssuranceKit
public section
namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe
set_option autoImplicit false
set_option maxRecDepth 65536
/-! ## §3. Constant-Depth Register Banks & `x86_64` Machine-Code Decoder + Semantics -/

/-- Flat 16-slot register bank (`O(1)` WHNF depth, zero `Array` bounds proof obligations). -/


private theorem fin16_elim {P : Nat → Prop} {i : Nat} (hi : i < 16)
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3)
    (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7)
    (h8 : P 8) (h9 : P 9) (h10 : P 10) (h11 : P 11)
    (h12 : P 12) (h13 : P 13) (h14 : P 14) (h15 : P 15) : P i := by
  match i with
  | 0 => exact h0 | 1 => exact h1 | 2 => exact h2 | 3 => exact h3
  | 4 => exact h4 | 5 => exact h5 | 6 => exact h6 | 7 => exact h7
  | 8 => exact h8 | 9 => exact h9 | 10 => exact h10 | 11 => exact h11
  | 12 => exact h12 | 13 => exact h13 | 14 => exact h14 | 15 => exact h15
  | _ + 16 => exact False.elim (by omega)

theorem Bank16.get_const {α : Type} (v : α) (i : Nat) :
    (Bank16.const v).get i = v := by
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 => rfl
  | _ + 15 => rfl

theorem Bank16.get_ofFn {α : Type} (f : Nat → α) {i : Nat} (hi : i < 16) :
    (Bank16.ofFn f).get i = f i :=
  fin16_elim (P := fun i => (Bank16.ofFn f).get i = f i)
    hi rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem Bank16.get_set_eq {α : Type} (b : Bank16 α) (i : Nat) (v : α) :
    (b.set i v).get i = v := by
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 => rfl
  | _ + 15 => rfl

theorem Bank16.get_set_ne {α : Type} (b : Bank16 α) {i j : Nat} (v : α)
    (hi : i < 16) (hj : j < 16) (hne : i ≠ j) :
    (b.set i v).get j = b.get j := by
  revert hne
  refine fin16_elim (P := fun i => i ≠ j → (b.set i v).get j = b.get j) hi
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    (refine fin16_elim (P := fun j => _ ≠ j → (b.set _ v).get j = b.get j) hj
       ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      (intro hne; first | exact absurd rfl hne | rfl))

theorem Bank16.allIdx_get {α : Type} {p : Nat → α → Bool} {b : Bank16 α}
    (h : b.allIdx p = true) {i : Nat} (hi : i < 16) :
    p i (b.get i) = true := by
  unfold Bank16.allIdx at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩,
    h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩
  exact fin16_elim (P := fun i => p i (b.get i) = true)
    hi h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15

theorem Bank32.get_const {α : Type} (v : α) (i : Nat) :
    (Bank32.const v).get i = v := by
  unfold Bank32.const Bank32.get
  split <;> exact Bank16.get_const v _

theorem Bank32.get_ofFn {α : Type} (f : Nat → α) {i : Nat} (hi : i < 32) :
    (Bank32.ofFn f).get i = f i := by
  unfold Bank32.ofFn Bank32.get
  split
  · rename_i hlt
    exact Bank16.get_ofFn f hlt
  · rename_i hge
    rw [Bank16.get_ofFn (fun k => f (k + 16)) (by omega)]
    exact congrArg f (by omega)

theorem Bank32.get_set_eq {α : Type} (b : Bank32 α) (i : Nat) (v : α) :
    (b.set i v).get i = v := by
  unfold Bank32.set Bank32.get
  split <;> simp [*, Bank16.get_set_eq]

theorem Bank32.get_set_ne {α : Type} (b : Bank32 α) {i j : Nat} (v : α)
    (hi : i < 32) (hj : j < 32) (hne : i ≠ j) :
    (b.set i v).get j = b.get j := by
  unfold Bank32.set Bank32.get
  by_cases hi16 : i < 16 <;> by_cases hj16 : j < 16 <;> simp only [hi16, hj16, ↓reduceIte]
  · exact Bank16.get_set_ne b.lo v hi16 hj16 hne
  · exact Bank16.get_set_ne b.hi v (by omega) (by omega) (by omega)

theorem Bank32.allIdx_get {α : Type} {p : Nat → α → Bool} {b : Bank32 α}
    (h : b.allIdx p = true) {i : Nat} (hi : i < 32) :
    p i (b.get i) = true := by
  unfold Bank32.allIdx at h
  rw [Bool.and_eq_true] at h
  unfold Bank32.get
  split
  · rename_i hlt
    exact Bank16.allIdx_get h.1 hlt
  · rename_i hge
    have hHi := Bank16.allIdx_get h.2 (i := i - 16) (by omega)
    have hEq : i - 16 + 16 = i := by omega
    simpa only [hEq] using hHi


/-! #### Memory Read-Over-Write & Disjointness Lemmas -/

theorem writeMem8_eq (mem : UInt64 → UInt8) (addr : UInt64) (b : UInt8) :
    writeMem8 mem addr b addr = b := by
  change (if addr == addr then b else mem addr) = b
  have h : (addr == addr) = true := by
    change (addr.toBitVec == addr.toBitVec) = true
    exact beq_self_eq_true _
  rw [h]
  rfl

theorem writeMem8_ne (mem : UInt64 → UInt8) {addr q : UInt64} (b : UInt8) (hne : q ≠ addr) :
    writeMem8 mem addr b q = mem q := by
  unfold writeMem8
  have hbf : (q == addr) = false := beq_false_of_ne hne
  rw [hbf]
  rfl

theorem writeMem64_ne (mem : UInt64 → UInt8) {addr q : UInt64} (v : UInt64)
    (hDisj : ∀ j : Nat, j < 8 → q ≠ addr + UInt64.ofNat j) :
    writeMem64 mem addr v q = mem q := by
  unfold writeMem64
  have h0 : q ≠ addr := by simpa using hDisj 0 (by omega)
  have h1 : q ≠ addr + 1 := hDisj 1 (by omega)
  have h2 : q ≠ addr + 2 := hDisj 2 (by omega)
  have h3 : q ≠ addr + 3 := hDisj 3 (by omega)
  have h4 : q ≠ addr + 4 := hDisj 4 (by omega)
  have h5 : q ≠ addr + 5 := hDisj 5 (by omega)
  have h6 : q ≠ addr + 6 := hDisj 6 (by omega)
  have h7 : q ≠ addr + 7 := hDisj 7 (by omega)
  simp only [writeMem8_ne _ _ h7, writeMem8_ne _ _ h6, writeMem8_ne _ _ h5, writeMem8_ne _ _ h4,
    writeMem8_ne _ _ h3, writeMem8_ne _ _ h2, writeMem8_ne _ _ h1, writeMem8_ne _ _ h0]

theorem uint64_eq_of_toNat_eq {a b : UInt64} (h : a.toNat = b.toNat) : a = b :=
  UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

theorem writeMem128_ne (mem : UInt64 → UInt8) {addr q : UInt64} (v : Vec128)
    (hDisj : ∀ j : Nat, j < 16 → q ≠ addr + UInt64.ofNat j) :
    writeMem128 mem addr v q = mem q := by
  unfold writeMem128
  rw [writeMem64_ne _ _ (fun j hj => by
        have := hDisj (8 + j) (by omega)
        have hAdd : addr + 8 + UInt64.ofNat j = addr + UInt64.ofNat (8 + j) := by
          apply uint64_eq_of_toNat_eq
          have h8 : (8 : UInt64).toNat = 8 := rfl
          simp only [UInt64.toNat_add, UInt64.toNat_ofNat', h8, Nat.add_mod_mod, Nat.mod_add_mod]
          congr 1; omega
        rwa [hAdd]),
      writeMem64_ne _ _ (fun j hj => hDisj j (by omega))]

theorem writeMem256_ne (mem : UInt64 → UInt8) {addr q : UInt64} (v : Vec256)
    (hDisj : ∀ j : Nat, j < 32 → q ≠ addr + UInt64.ofNat j) :
    writeMem256 mem addr v q = mem q := by
  unfold writeMem256
  have hOff (base : Nat) (hbase : base + 8 ≤ 32) :
      ∀ j : Nat, j < 8 → q ≠ addr + UInt64.ofNat base + UInt64.ofNat j := by
    intro j hj
    have hEq : addr + UInt64.ofNat base + UInt64.ofNat j = addr + UInt64.ofNat (base + j) := by
      apply uint64_eq_of_toNat_eq
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.add_mod_mod, Nat.mod_add_mod]
      congr 1; omega
    rw [hEq]
    exact hDisj (base + j) (by omega)
  have h8 : ∀ j : Nat, j < 8 → q ≠ addr + 8 + UInt64.ofNat j := hOff 8 (by omega)
  have h16 : ∀ j : Nat, j < 8 → q ≠ addr + 16 + UInt64.ofNat j := hOff 16 (by omega)
  have h24 : ∀ j : Nat, j < 8 → q ≠ addr + 24 + UInt64.ofNat j := hOff 24 (by omega)
  rw [writeMem64_ne _ _ h24,
      writeMem64_ne _ _ h16,
      writeMem64_ne _ _ h8,
      writeMem64_ne _ _ (fun j hj => hDisj j (by omega))]

theorem readMem64_congr {m1 m2 : UInt64 → UInt8} {addr : UInt64}
    (h : ∀ j : Nat, j < 8 → m1 (addr + UInt64.ofNat j) = m2 (addr + UInt64.ofNat j)) :
    readMem64 m1 addr = readMem64 m2 addr := by
  have h0 : m1 addr = m2 addr := by simpa using h 0 (by omega)
  have h1 : m1 (addr + 1) = m2 (addr + 1) := h 1 (by omega)
  have h2 : m1 (addr + 2) = m2 (addr + 2) := h 2 (by omega)
  have h3 : m1 (addr + 3) = m2 (addr + 3) := h 3 (by omega)
  have h4 : m1 (addr + 4) = m2 (addr + 4) := h 4 (by omega)
  have h5 : m1 (addr + 5) = m2 (addr + 5) := h 5 (by omega)
  have h6 : m1 (addr + 6) = m2 (addr + 6) := h 6 (by omega)
  have h7 : m1 (addr + 7) = m2 (addr + 7) := h 7 (by omega)
  unfold readMem64
  rw [h0, h1, h2, h3, h4, h5, h6, h7]

theorem addr_off_ne (addr a b : UInt64) (hne : a ≠ b) :
    addr + a ≠ addr + b := by
  intro hEq
  have hSub : (addr + a) - addr = (addr + b) - addr := congrArg (· - addr) hEq
  have hCancel (x : UInt64) : (addr + x) - addr = x := by
    apply uint64_eq_of_toNat_eq
    have hx := x.toNat_lt
    have hd := addr.toNat_lt
    have h64 : (2 : Nat) ^ 64 = 0x10000000000000000 := rfl
    simp only [UInt64.toNat_sub, UInt64.toNat_add, h64]
    omega
  rw [hCancel a, hCancel b] at hSub
  exact hne hSub

theorem addr_ne_add_pos (addr b : UInt64) (hb : (0 : UInt64) ≠ b) :
    addr ≠ addr + b := by
  have h0 : addr + 0 = addr := by
    apply uint64_eq_of_toNat_eq
    have hd := addr.toNat_lt
    have hZ : (0 : UInt64).toNat = 0 := rfl
    have h64 : (2 : Nat) ^ 64 = 0x10000000000000000 := rfl
    simp only [UInt64.toNat_add, hZ, h64]
    omega
  intro hEq
  exact addr_off_ne addr 0 b hb (h0.trans hEq)

theorem toUInt8_toUInt64_eq_and (w : UInt64) :
    w.toUInt8.toUInt64 = (w &&& (0xFF : UInt64)) := by
  apply uint64_eq_of_toNat_eq
  have h1 : w.toUInt8.toUInt64.toNat = w.toNat % 256 := by
    change (UInt8.ofNat w.toNat).toNat = w.toNat % 256
    exact UInt8.toNat_ofNat'
  have h2 : (w &&& (0xFF : UInt64)).toNat = w.toNat % 256 := by
    rw [UInt64.toNat_and]
    change w.toNat &&& (2 ^ 8 - 1) = w.toNat % 256
    exact Constructive.and_mask w.toNat 8
  exact h1.trans h2.symm

def checkMaskFFBits : Bool :=
  (List.range 64).all (fun i => (0xFF : UInt64).toBitVec.getLsbD i == decide (i < 8))

theorem checkMaskFFBits_true : checkMaskFFBits = true := by decide

theorem mask_ff_getLsbD_lt (k : Nat) (hk : k < 64) :
    (0xFF : UInt64).toBitVec.getLsbD k = decide (k < 8) := by
  have h := List.all_eq_true.mp checkMaskFFBits_true k (List.mem_range.mpr hk)
  exact beq_iff_eq.mp h

theorem uint64_shiftRight_getLsbD (v sh : UInt64) (k : Nat) :
    (v >>> sh).toBitVec.getLsbD k = v.toBitVec.getLsbD (sh.toNat % 64 + k) := by
  simp only [BitVec.getLsbD, show (v >>> sh).toBitVec.toNat = (v >>> sh).toNat from rfl,
    show v.toBitVec.toNat = v.toNat from rfl, UInt64.toNat_shiftRight,
    Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem byte_slot_getLsbD (v sh : UInt64) (i : Nat) (hi : i < 64) (hsh : sh.toNat ≤ 56) :
    (((v >>> sh).toUInt8.toUInt64) <<< sh).toBitVec.getLsbD i =
      if sh.toNat ≤ i ∧ i < sh.toNat + 8 then v.toBitVec.getLsbD i else false := by
  have hMod : sh.toNat % 64 = sh.toNat := Nat.mod_eq_of_lt (by omega)
  have h64Nat : (64 : BitVec 64).toNat = 64 := rfl
  have hShNat : (sh.toBitVec % 64).toNat = sh.toNat := by
    rw [BitVec.toNat_umod, h64Nat]
    exact hMod
  rw [toUInt8_toUInt64_eq_and, UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq', hShNat,
      BitVec.getLsbD_shiftLeft]
  simp only [hi, decide_true, Bool.true_and, UInt64.toBitVec_and, BitVec.getLsbD_and,
    uint64_shiftRight_getLsbD, hMod]
  have hSub64 : i - sh.toNat < 64 := by omega
  rw [mask_ff_getLsbD_lt (i - sh.toNat) hSub64]
  if hLow : i < sh.toNat then
    have hNot : ¬(sh.toNat ≤ i ∧ i < sh.toNat + 8) := by intro h; omega
    simp only [decide_eq_true hLow, hNot, ↓reduceIte]
    rfl
  else if hHigh : i < sh.toNat + 8 then
    have hSub : i - sh.toNat < 8 := by omega
    have hYes : sh.toNat ≤ i ∧ i < sh.toNat + 8 := ⟨by omega, hHigh⟩
    have hAdd : sh.toNat + (i - sh.toNat) = i := by omega
    simp only [decide_eq_false hLow, decide_eq_true hSub, hYes, and_self, hAdd, ↓reduceIte]
    cases v.toBitVec.getLsbD i <;> rfl
  else
    have hSub : ¬(i - sh.toNat < 8) := by intro h; omega
    have hNot : ¬(sh.toNat ≤ i ∧ i < sh.toNat + 8) := by intro h; omega
    simp only [decide_eq_false hLow, decide_eq_false hSub, hNot, ↓reduceIte]
    cases v.toBitVec.getLsbD (sh.toNat + (i - sh.toNat)) <;> rfl

theorem byte_reassemble_u64 (v : UInt64) :
    v.toUInt8.toUInt64 |||
    ((v >>> 8).toUInt8.toUInt64 <<< 8) |||
    ((v >>> 16).toUInt8.toUInt64 <<< 16) |||
    ((v >>> 24).toUInt8.toUInt64 <<< 24) |||
    ((v >>> 32).toUInt8.toUInt64 <<< 32) |||
    ((v >>> 40).toUInt8.toUInt64 <<< 40) |||
    ((v >>> 48).toUInt8.toUInt64 <<< 48) |||
    ((v >>> 56).toUInt8.toUInt64 <<< 56) = v := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt64.toBitVec_or, BitVec.getLsbD_or]
  rw [byte_slot_getLsbD v 8 i hi (by decide),
      byte_slot_getLsbD v 16 i hi (by decide),
      byte_slot_getLsbD v 24 i hi (by decide),
      byte_slot_getLsbD v 32 i hi (by decide),
      byte_slot_getLsbD v 40 i hi (by decide),
      byte_slot_getLsbD v 48 i hi (by decide),
      byte_slot_getLsbD v 56 i hi (by decide),
      toUInt8_toUInt64_eq_and v]
  simp only [UInt64.toBitVec_and, BitVec.getLsbD_and, mask_ff_getLsbD_lt i hi,
    show (8 : UInt64).toNat = 8 from rfl, show (16 : UInt64).toNat = 16 from rfl,
    show (24 : UInt64).toNat = 24 from rfl, show (32 : UInt64).toNat = 32 from rfl,
    show (40 : UInt64).toNat = 40 from rfl, show (48 : UInt64).toNat = 48 from rfl,
    show (56 : UInt64).toNat = 56 from rfl]
  if c0 : i < 8 then
    have n1 : ¬(8 ≤ i ∧ i < 16) := by intro h; omega
    have n2 : ¬(16 ≤ i ∧ i < 24) := by intro h; omega
    have n3 : ¬(24 ≤ i ∧ i < 32) := by intro h; omega
    have n4 : ¬(32 ≤ i ∧ i < 40) := by intro h; omega
    have n5 : ¬(40 ≤ i ∧ i < 48) := by intro h; omega
    have n6 : ¬(48 ≤ i ∧ i < 56) := by intro h; omega
    have n7 : ¬(56 ≤ i ∧ i < 64) := by intro h; omega
    simp only [decide_eq_true c0, n1, n2, n3, n4, n5, n6, n7, ↓reduceIte]
    cases v.toBitVec.getLsbD i <;> rfl
  else if c1 : i < 16 then
    have y1 : 8 ≤ i ∧ i < 16 := by constructor <;> omega
    have n2 : ¬(16 ≤ i ∧ i < 24) := by intro h; omega
    have n3 : ¬(24 ≤ i ∧ i < 32) := by intro h; omega
    have n4 : ¬(32 ≤ i ∧ i < 40) := by intro h; omega
    have n5 : ¬(40 ≤ i ∧ i < 48) := by intro h; omega
    have n6 : ¬(48 ≤ i ∧ i < 56) := by intro h; omega
    have n7 : ¬(56 ≤ i ∧ i < 64) := by intro h; omega
    simp only [decide_eq_false c0, y1, n2, n3, n4, n5, n6, n7, and_self, ↓reduceIte]
    cases v.toBitVec.getLsbD i <;> rfl
  else if c2 : i < 24 then
    have n1 : ¬(8 ≤ i ∧ i < 16) := by intro h; omega
    have y2 : 16 ≤ i ∧ i < 24 := by constructor <;> omega
    have n3 : ¬(24 ≤ i ∧ i < 32) := by intro h; omega
    have n4 : ¬(32 ≤ i ∧ i < 40) := by intro h; omega
    have n5 : ¬(40 ≤ i ∧ i < 48) := by intro h; omega
    have n6 : ¬(48 ≤ i ∧ i < 56) := by intro h; omega
    have n7 : ¬(56 ≤ i ∧ i < 64) := by intro h; omega
    simp only [decide_eq_false c0, n1, y2, n3, n4, n5, n6, n7, and_self, ↓reduceIte]
    cases v.toBitVec.getLsbD i <;> rfl
  else if c3 : i < 32 then
    have n1 : ¬(8 ≤ i ∧ i < 16) := by intro h; omega
    have n2 : ¬(16 ≤ i ∧ i < 24) := by intro h; omega
    have y3 : 24 ≤ i ∧ i < 32 := by constructor <;> omega
    have n4 : ¬(32 ≤ i ∧ i < 40) := by intro h; omega
    have n5 : ¬(40 ≤ i ∧ i < 48) := by intro h; omega
    have n6 : ¬(48 ≤ i ∧ i < 56) := by intro h; omega
    have n7 : ¬(56 ≤ i ∧ i < 64) := by intro h; omega
    simp only [decide_eq_false c0, n1, n2, y3, n4, n5, n6, n7, and_self, ↓reduceIte]
    cases v.toBitVec.getLsbD i <;> rfl
  else if c4 : i < 40 then
    have n1 : ¬(8 ≤ i ∧ i < 16) := by intro h; omega
    have n2 : ¬(16 ≤ i ∧ i < 24) := by intro h; omega
    have n3 : ¬(24 ≤ i ∧ i < 32) := by intro h; omega
    have y4 : 32 ≤ i ∧ i < 40 := by constructor <;> omega
    have n5 : ¬(40 ≤ i ∧ i < 48) := by intro h; omega
    have n6 : ¬(48 ≤ i ∧ i < 56) := by intro h; omega
    have n7 : ¬(56 ≤ i ∧ i < 64) := by intro h; omega
    simp only [decide_eq_false c0, n1, n2, n3, y4, n5, n6, n7, and_self, ↓reduceIte]
    cases v.toBitVec.getLsbD i <;> rfl
  else if c5 : i < 48 then
    have n1 : ¬(8 ≤ i ∧ i < 16) := by intro h; omega
    have n2 : ¬(16 ≤ i ∧ i < 24) := by intro h; omega
    have n3 : ¬(24 ≤ i ∧ i < 32) := by intro h; omega
    have n4 : ¬(32 ≤ i ∧ i < 40) := by intro h; omega
    have y5 : 40 ≤ i ∧ i < 48 := by constructor <;> omega
    have n6 : ¬(48 ≤ i ∧ i < 56) := by intro h; omega
    have n7 : ¬(56 ≤ i ∧ i < 64) := by intro h; omega
    simp only [decide_eq_false c0, n1, n2, n3, n4, y5, n6, n7, and_self, ↓reduceIte]
    cases v.toBitVec.getLsbD i <;> rfl
  else if c6 : i < 56 then
    have n1 : ¬(8 ≤ i ∧ i < 16) := by intro h; omega
    have n2 : ¬(16 ≤ i ∧ i < 24) := by intro h; omega
    have n3 : ¬(24 ≤ i ∧ i < 32) := by intro h; omega
    have n4 : ¬(32 ≤ i ∧ i < 40) := by intro h; omega
    have n5 : ¬(40 ≤ i ∧ i < 48) := by intro h; omega
    have y6 : 48 ≤ i ∧ i < 56 := by constructor <;> omega
    have n7 : ¬(56 ≤ i ∧ i < 64) := by intro h; omega
    simp only [decide_eq_false c0, n1, n2, n3, n4, n5, y6, n7, and_self, ↓reduceIte]
    cases v.toBitVec.getLsbD i <;> rfl
  else
    have n1 : ¬(8 ≤ i ∧ i < 16) := by intro h; omega
    have n2 : ¬(16 ≤ i ∧ i < 24) := by intro h; omega
    have n3 : ¬(24 ≤ i ∧ i < 32) := by intro h; omega
    have n4 : ¬(32 ≤ i ∧ i < 40) := by intro h; omega
    have n5 : ¬(40 ≤ i ∧ i < 48) := by intro h; omega
    have n6 : ¬(48 ≤ i ∧ i < 56) := by intro h; omega
    have y7 : 56 ≤ i ∧ i < 64 := by constructor <;> omega
    simp only [decide_eq_false c0, n1, n2, n3, n4, n5, n6, y7, and_self, ↓reduceIte]
    cases v.toBitVec.getLsbD i <;> rfl

theorem readMem64_writeMem64_self (mem : UInt64 → UInt8) (addr v : UInt64) :
    readMem64 (writeMem64 mem addr v) addr = v := by
  let m0 := writeMem8 mem addr v.toUInt8
  let m1 := writeMem8 m0 (addr + 1) (v >>> 8).toUInt8
  let m2 := writeMem8 m1 (addr + 2) (v >>> 16).toUInt8
  let m3 := writeMem8 m2 (addr + 3) (v >>> 24).toUInt8
  let m4 := writeMem8 m3 (addr + 4) (v >>> 32).toUInt8
  let m5 := writeMem8 m4 (addr + 5) (v >>> 40).toUInt8
  let m6 := writeMem8 m5 (addr + 6) (v >>> 48).toUInt8
  let m7 := writeMem8 m6 (addr + 7) (v >>> 56).toUInt8
  change readMem64 m7 addr = v
  have b7 : m7 (addr + 7) = (v >>> 56).toUInt8 := writeMem8_eq _ _ _
  have b6 : m7 (addr + 6) = (v >>> 48).toUInt8 := by
    dsimp only [m7, m6]
    rw [writeMem8_ne _ _ (addr_off_ne addr 6 7 (by decide))]; exact writeMem8_eq _ _ _
  have b5 : m7 (addr + 5) = (v >>> 40).toUInt8 := by
    dsimp only [m7, m6, m5]
    rw [writeMem8_ne _ _ (addr_off_ne addr 5 7 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 5 6 (by decide))]; exact writeMem8_eq _ _ _
  have b4 : m7 (addr + 4) = (v >>> 32).toUInt8 := by
    dsimp only [m7, m6, m5, m4]
    rw [writeMem8_ne _ _ (addr_off_ne addr 4 7 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 4 6 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 4 5 (by decide))]; exact writeMem8_eq _ _ _
  have b3 : m7 (addr + 3) = (v >>> 24).toUInt8 := by
    dsimp only [m7, m6, m5, m4, m3]
    rw [writeMem8_ne _ _ (addr_off_ne addr 3 7 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 3 6 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 3 5 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 3 4 (by decide))]; exact writeMem8_eq _ _ _
  have b2 : m7 (addr + 2) = (v >>> 16).toUInt8 := by
    dsimp only [m7, m6, m5, m4, m3, m2]
    rw [writeMem8_ne _ _ (addr_off_ne addr 2 7 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 2 6 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 2 5 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 2 4 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 2 3 (by decide))]; exact writeMem8_eq _ _ _
  have b1 : m7 (addr + 1) = (v >>> 8).toUInt8 := by
    dsimp only [m7, m6, m5, m4, m3, m2, m1]
    rw [writeMem8_ne _ _ (addr_off_ne addr 1 7 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 1 6 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 1 5 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 1 4 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 1 3 (by decide)),
        writeMem8_ne _ _ (addr_off_ne addr 1 2 (by decide))]; exact writeMem8_eq _ _ _
  have b0 : m7 addr = v.toUInt8 := by
    dsimp only [m7, m6, m5, m4, m3, m2, m1, m0]
    rw [writeMem8_ne _ _ (addr_ne_add_pos addr 7 (by decide)),
        writeMem8_ne _ _ (addr_ne_add_pos addr 6 (by decide)),
        writeMem8_ne _ _ (addr_ne_add_pos addr 5 (by decide)),
        writeMem8_ne _ _ (addr_ne_add_pos addr 4 (by decide)),
        writeMem8_ne _ _ (addr_ne_add_pos addr 3 (by decide)),
        writeMem8_ne _ _ (addr_ne_add_pos addr 2 (by decide)),
        writeMem8_ne _ _ (addr_ne_add_pos addr 1 (by decide))]; exact writeMem8_eq _ _ _
  unfold readMem64
  rw [b0, b1, b2, b3, b4, b5, b6, b7]
  exact byte_reassemble_u64 v

def checkAlign32MaskBits : Bool :=
  (List.range 64).all (fun i =>
    (0xFFFFFFFFFFFFFFE0 : UInt64).toBitVec.getLsbD i == decide (5 ≤ i))

theorem checkAlign32MaskBits_true : checkAlign32MaskBits = true := by decide

theorem align32_eq_shift (x : UInt64) :
    (x &&& (0xFFFFFFFFFFFFFFE0 : UInt64)) = (x >>> 5) <<< 5 := by
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h5 : (5 : UInt64).toBitVec % 64 = BitVec.ofNat 64 5 := by decide
  have hMaskBit : (0xFFFFFFFFFFFFFFE0 : UInt64).toBitVec.getLsbD i = decide (5 ≤ i) :=
    beq_iff_eq.mp (List.all_eq_true.mp checkAlign32MaskBits_true i (List.mem_range.mpr hi))
  rw [UInt64.toBitVec_and, BitVec.getLsbD_and, hMaskBit,
      UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq', h5, BitVec.toNat_ofNat]
  simp only [show 5 % 64 = 5 from rfl, BitVec.getLsbD_shiftLeft, hi, decide_true, Bool.true_and,
    uint64_shiftRight_getLsbD, show (5 : UInt64).toNat % 64 = 5 from rfl]
  if hlt : i < 5 then
    have hge : ¬(5 ≤ i) := by intro h; omega
    rw [decide_eq_true hlt, decide_eq_false hge]
    cases x.toBitVec.getLsbD i <;> rfl
  else
    have hge : 5 ≤ i := by omega
    have hAdd : 5 + (i - 5) = i := by omega
    rw [decide_eq_false hlt, decide_eq_true hge, hAdd]
    cases x.toBitVec.getLsbD i <;> rfl

theorem align32_toNat (x : UInt64) :
    (x &&& (0xFFFFFFFFFFFFFFE0 : UInt64)).toNat = (x.toNat / 32) * 32 := by
  rw [align32_eq_shift]
  have hlt : (x.toNat / 32) * 32 < 2 ^ 64 := by have := x.toNat_lt; omega
  simp [UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hlt]

theorem uint64_evalAdd_eq (a b : UInt64) :
    UInt64.ofNat ((a.toNat + b.toNat) % 0x10000000000000000) = a + b := by
  apply uint64_eq_of_toNat_eq
  have h64 : (2 : Nat) ^ 64 = 0x10000000000000000 := rfl
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat', h64, Nat.mod_mod]

theorem uint64_evalSub_eq (a b : UInt64) :
    UInt64.ofNat ((a.toNat + 0x10000000000000000 - b.toNat) % 0x10000000000000000) = a - b := by
  apply uint64_eq_of_toNat_eq
  have ha := a.toNat_lt; have hb := b.toNat_lt
  have h64 : (2 : Nat) ^ 64 = 0x10000000000000000 := rfl
  simp only [UInt64.toNat_sub, UInt64.toNat_ofNat', h64]; omega


/-! ## §5. 3-Way Hardware Constant-Time Noninterference & ABI Hygiene Verifier -/


theorem PcMap.empty_get {α : Type} (pc : Nat) :
    (PcMap.empty : PcMap α).get pc = none := by
  unfold PcMap.empty PcMap.get
  split
  · rfl
  · rw [Bank32.get_const]

theorem PcMap.get_some_lt {α : Type} {m : PcMap α} {pc : Nat} {v : α}
    (h : m.get pc = some v) : pc < 8192 := by
  unfold PcMap.get at h
  split at h
  · cases h
  · omega

theorem PcMap.get_set_eq {α : Type} (m : PcMap α) {pc : Nat} (v : α) (hpc : pc < 8192) :
    (m.set pc v).get pc = some v := by
  have hge : ¬(pc ≥ 8192) := by intro h; omega
  unfold PcMap.set PcMap.get
  simp only [hge, ↓reduceIte, Bank32.get_set_eq, Bank16.get_set_eq]

theorem PcMap.get_set_ne {α : Type} (m : PcMap α) {pc q : Nat} (v : α)
    (hq : q < 8192) (hne : pc ≠ q) :
    (m.set pc v).get q = m.get q := by
  have hqge : ¬(q ≥ 8192) := by intro h; omega
  by_cases hpc : pc ≥ 8192
  · unfold PcMap.set; simp [hpc]
  · unfold PcMap.set PcMap.get
    simp only [hpc, hqge, ↓reduceIte]
    have hi2p : pc / 256 < 32 := by omega
    have hi2q : q / 256 < 32 := by omega
    have hi1p : (pc / 16) % 16 < 16 := by omega
    have hi1q : (q / 16) % 16 < 16 := by omega
    have hi0p : pc % 16 < 16 := by omega
    have hi0q : q % 16 < 16 := by omega
    by_cases h2 : pc / 256 = q / 256
    · rw [← h2, Bank32.get_set_eq]
      dsimp only
      by_cases h1 : (pc / 16) % 16 = (q / 16) % 16
      · have h0ne : pc % 16 ≠ q % 16 := by omega
        rw [← h1, Bank16.get_set_eq]
        dsimp only
        rw [Bank16.get_set_ne _ _ hi0p hi0q h0ne]
        cases hm2 : m.root.get (pc / 256) with
        | none => simp [Bank16.get_const]
        | some b1 =>
          dsimp only
          cases hm1 : b1.get ((pc / 16) % 16) with
          | none => simp [Bank16.get_const]
          | some b0 => rfl
      · rw [Bank16.get_set_ne _ _ hi1p hi1q h1]
        cases hm2 : m.root.get (pc / 256) with
        | none => simp [Bank16.get_const]
        | some b1 => rfl
    · rw [Bank32.get_set_ne _ _ hi2p hi2q h2]

theorem PcMap.all_get {α : Type} {pred : Nat → α → Bool} {m : PcMap α}
    (hAll : m.all pred = true) {pc : Nat} {v : α} (hGet : m.get pc = some v) :
    pred pc v = true := by
  have hlt : pc < 8192 := PcMap.get_some_lt hGet
  have hge : ¬(pc ≥ 8192) := by intro h; omega
  unfold PcMap.get at hGet
  simp only [hge, ↓reduceIte] at hGet
  unfold PcMap.all at hAll
  have h2 := Bank32.allIdx_get hAll (i := pc / 256) (by omega)
  cases hm2 : Bank32.get m.root (pc / 256) with
  | none => simp [hm2] at hGet
  | some p1 =>
    simp only [hm2] at hGet h2
    have h1 := Bank16.allIdx_get h2 (i := (pc / 16) % 16) (by omega)
    cases hm1 : Bank16.get p1 ((pc / 16) % 16) with
    | none => simp [hm1] at hGet
    | some p0 =>
      simp only [hm1] at hGet h1
      have h0 := Bank16.allIdx_get h1 (i := pc % 16) (by omega)
      simp only [hGet] at h0
      have hIdx : (pc / 256) * 256 + ((pc / 16) % 16) * 16 + (pc % 16) = pc := by omega
      simpa only [hIdx] using h0

theorem buildProgMap_get_eq {Instr : Type} (prog : List (DecodedInstr Instr))
    {pc : Nat} (hpc : pc < 8192) :
    (buildProgMap prog).get pc = findInstrAtPc pc prog := by
  induction prog with
  | nil => exact PcMap.empty_get pc
  | cons d ds ih =>
    unfold buildProgMap findInstrAtPc
    by_cases heq : d.offset = pc
    · subst heq
      simp [PcMap.get_set_eq _ _ hpc]
    · have hbeq : (d.offset == pc) = false := beq_false_of_ne heq
      rw [PcMap.get_set_ne _ _ hpc heq, hbeq]
      simp [ih]

/-! #### `x86_64` & `AArch64` Relational Contracts, Hygiene Postconditions & Inhabitedness Witnesses -/

/-- Well-formed frame non-aliasing precondition when `c.usesRbpFrame = true`:
    `rsp` has `0x400` bytes of downward stack headroom and the caller's output buffer
    `[outPtr .. outPtr + outBytes)` does not overlap the callee's saved-`rbp` slot `[rsp - 8 .. rsp)`. -/
def X86FramePrecond (c : FuncContract) (s₀ : X86State) : Prop :=
  c.usesRbpFrame = false ∨
  (c.outPtrReg < 16 ∧
   0x400 ≤ (s₀.gpr.get 4).toNat ∧
   ∀ j k : Nat, j < c.outBytes → k < 8 →
     s₀.gpr.get c.outPtrReg + UInt64.ofNat j ≠ (s₀.gpr.get 4 - 8) + UInt64.ofNat k)

/-- Initial `x86_64` relational contract $\Gamma(s_1, s_2)$:
    both executions start at `pc = 0` with clean upper `YMM` state, agree on public GPRs (`len`, pointers, `rsp`)
    and static public LUT regions (`pubMemRegions`), while secret memory and secret GPRs are arbitrary. -/
def X86ContractInit (c : FuncContract) (s₁ s₂ : X86State) : Prop :=
  s₁.pc = 0 ∧ s₂.pc = 0 ∧
  s₁.halted = false ∧ s₂.halted = false ∧
  s₁.ymmDirty = false ∧ s₂.ymmDirty = false ∧
  (∀ r ∈ c.pubGprs, r < 16 ∧ s₁.gpr.get r = s₂.gpr.get r) ∧
  (∀ regLen ∈ c.pubMemRegions,
     regLen.1 < 16 ∧
     ∀ off : Nat, off < regLen.2 →
       s₁.mem (s₁.gpr.get regLen.1 + UInt64.ofNat off) =
       s₂.mem (s₂.gpr.get regLen.1 + UInt64.ofNat off)) ∧
  X86FramePrecond c s₁ ∧ X86FramePrecond c s₂

/-- Base of the 32-byte-aligned `0x340`-byte frame that a `usesRbpFrame` kernel allocates with
    `push rbp; mov rbp, rsp; and rsp, -32; sub rsp, 0x340`, as a function of the entry `rsp`. -/
def x86FrameSpVal (rsp₀ : UInt64) : UInt64 :=
  ((rsp₀ - 8) &&& 0xFFFFFFFFFFFFFFE0) - 0x340

/-- System V AMD64 ABI & Epilogue Zeroization postcondition upon `ret`. A `usesRbpFrame`
    kernel additionally leaves its 800-byte (25 × 32) stack spill area zeroed. -/
def X86ExitHygiene (c : FuncContract) (s₁₀ s₂₀ s₁ s₂ : X86State) : Prop :=
  (s₁.gpr.get 4 = s₁₀.gpr.get 4 + 8 ∧ s₂.gpr.get 4 = s₂₀.gpr.get 4 + 8) ∧
  (∀ r ∈ [3, 5, 12, 13, 14, 15],
     s₁.gpr.get r = s₁₀.gpr.get r ∧ s₂.gpr.get r = s₂₀.gpr.get r) ∧
  (s₁.ymmDirty = false ∧ s₂.ymmDirty = false) ∧
  (∀ i : Nat, i < 16 →
     (s₁.ymm.get i = Vec256.zero ∧ s₂.ymm.get i = Vec256.zero) ∨
     (∃ r : Nat, r < 16 ∧
       ((s₁.ymm.get i = s₁₀.ymm.get r ∧ s₂.ymm.get i = s₂₀.ymm.get r) ∨
        (s₁.ymm.get i = ⟨(s₁₀.ymm.get r).w0, (s₁₀.ymm.get r).w1, 0, 0⟩ ∧
         s₂.ymm.get i = ⟨(s₂₀.ymm.get r).w0, (s₂₀.ymm.get r).w1, 0, 0⟩)))) ∧
  (∀ r ∈ c.wipedScratchGprs, s₁.gpr.get r = 0 ∧ s₂.gpr.get r = 0) ∧
  (c.usesRbpFrame = true →
     ∀ j : Nat, j < 800 →
       s₁.mem (x86FrameSpVal (s₁₀.gpr.get 4) + UInt64.ofNat j) = 0 ∧
       s₂.mem (x86FrameSpVal (s₂₀.gpr.get 4) + UInt64.ofNat j) = 0)

/-- Initial `AArch64` relational contract $\Gamma(s_1, s_2)$:
    both executions start at `pc = 0`, agree on public GPRs (`x0..x3` pointers / lengths),
    while secret memory, secret GPRs, and caller NEON contents are completely arbitrary. -/
def Arm64ContractInit (c : FuncContract) (s₁ s₂ : Arm64State) : Prop :=
  s₁.pc = 0 ∧ s₂.pc = 0 ∧
  s₁.halted = false ∧ s₂.halted = false ∧
  s₁.dit = c.doitEnabled ∧ s₂.dit = c.doitEnabled ∧
  (∀ r ∈ c.pubGprs, r < 31 ∧ s₁.gpr.get r = s₂.gpr.get r)

/-- AAPCS64 ABI & NEON Epilogue Zeroization postcondition upon `ret`. -/
def Arm64ExitHygiene (c : FuncContract) (s₁₀ s₂₀ s₁ s₂ : Arm64State) : Prop :=
  (∀ r ∈ [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30],
     s₁.gpr.get r = s₁₀.gpr.get r ∧ s₂.gpr.get r = s₂₀.gpr.get r) ∧
  (∀ v ∈ [8, 9, 10, 11, 12, 13, 14, 15],
     s₁.vec.get v = s₁₀.vec.get v ∧ s₂.vec.get v = s₂₀.vec.get v) ∧
  (∀ v : Nat, v < 32 →
     (s₁.vec.get v = Vec128.zero ∧ s₂.vec.get v = Vec128.zero) ∨
     (∃ r : Nat, r < 32 ∧ s₁.vec.get v = s₁₀.vec.get r ∧ s₂.vec.get v = s₂₀.vec.get r)) ∧
  (∀ r ∈ c.wipedScratchGprs, getArmGpr s₁ r = 0 ∧ getArmGpr s₂ r = 0)

/-- **Anti-Vacuity / Inhabitedness Witness (`lean/uninhabited-premise-risk`) for `X86ContractInit`:**
    Every well-indexed `FuncContract` (including all 16 `x86SymbolContracts`) admits concrete
    pairs of initial states `(s₁, s₂)` with distinct secret memory (`0xAA ≠ 0x55` above `0x200000`)
    satisfying `X86ContractInit c s₁ s₂`. -/
theorem x86_contract_init_inhabited (c : FuncContract)
    (hPubLt : ∀ r ∈ c.pubGprs, r < 16)
    (hMemLt : ∀ regLen ∈ c.pubMemRegions, regLen.1 < 16 ∧ regLen.2 ≤ 0x10000)
    (hOutLt : c.outPtrReg < 16)
    (hOutSz : c.outBytes ≤ 0x10000) :
    ∃ s₁ s₂ : X86State,
      s₁.mem 0x200000 ≠ s₂.mem 0x200000 ∧ X86ContractInit c s₁ s₂ := by
  let gpr0 : Bank16 UInt64 := Bank16.ofFn (fun r => if r == 4 then 0x80000 else 0x10000)
  let s₁ : X86State := {
    pc := 0, gpr := gpr0, ymm := Bank16.const Vec256.zero,
    cf := false, ofFlag := false, zf := false, ymmDirty := false, halted := false,
    mem := fun a => if a.toNat < 0x100000 then 0x11 else 0xAA
  }
  let s₂ : X86State := { s₁ with
    mem := fun a => if a.toNat < 0x100000 then 0x11 else 0x55
  }
  refine ⟨s₁, s₂, by decide, ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩⟩
  · intro r hr; exact ⟨hPubLt r hr, rfl⟩
  · intro regLen hrl
    rcases hMemLt regLen hrl with ⟨hr16, hlen⟩
    refine ⟨hr16, fun off hoff => ?_⟩
    have hBase : (gpr0.get regLen.1).toNat ≤ 0x80000 := by
      rw [Bank16.get_ofFn _ hr16]; split <;> decide
    have hAddrLt : (gpr0.get regLen.1 + UInt64.ofNat off).toNat < 0x100000 := by
      have hSumLt : (gpr0.get regLen.1).toNat + off < 2 ^ 64 := by omega
      simp [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hSumLt]; omega
    dsimp only [s₁, s₂]
    simp only [hAddrLt, ↓reduceIte]
  · by_cases hUse : c.usesRbpFrame = false
    · exact Or.inl hUse
    · right
      have h4 : 0x400 ≤ (s₁.gpr.get 4).toNat := by decide
      refine ⟨hOutLt, h4, fun j k hj hk => ?_⟩
      intro hEq
      have hNat := congrArg UInt64.toNat hEq
      have hOutVal : (s₁.gpr.get c.outPtrReg).toNat = 0x10000 ∨ (s₁.gpr.get c.outPtrReg).toNat = 0x80000 := by
        change (gpr0.get c.outPtrReg).toNat = 0x10000 ∨ (gpr0.get c.outPtrReg).toNat = 0x80000
        rw [Bank16.get_ofFn _ hOutLt]
        split
        · exact Or.inr (by decide)
        · exact Or.inl (by decide)
      have hSpSub : (s₁.gpr.get 4 - 8).toNat = 0x7FFF8 := by decide
      have hRhs : ((s₁.gpr.get 4 - 8) + UInt64.ofNat k).toNat = 0x7FFF8 + k := by
        have hlt : 0x7FFF8 + k < 2 ^ 64 := by omega
        simp [UInt64.toNat_add, hSpSub, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]
      rcases hOutVal with h10 | h80
      · have hLhs : (s₁.gpr.get c.outPtrReg + UInt64.ofNat j).toNat = 0x10000 + j := by
          have hlt : 0x10000 + j < 2 ^ 64 := by omega
          simp [UInt64.toNat_add, h10, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]
        rw [hLhs, hRhs] at hNat; omega
      · have hLhs : (s₁.gpr.get c.outPtrReg + UInt64.ofNat j).toNat = 0x80000 + j := by
          have hlt : 0x80000 + j < 2 ^ 64 := by omega
          simp [UInt64.toNat_add, h80, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]
        rw [hLhs, hRhs] at hNat; omega
  · by_cases hUse : c.usesRbpFrame = false
    · exact Or.inl hUse
    · right
      have h4 : 0x400 ≤ (s₂.gpr.get 4).toNat := by decide
      refine ⟨hOutLt, h4, fun j k hj hk => ?_⟩
      intro hEq
      have hNat := congrArg UInt64.toNat hEq
      have hOutVal : (s₂.gpr.get c.outPtrReg).toNat = 0x10000 ∨ (s₂.gpr.get c.outPtrReg).toNat = 0x80000 := by
        change (gpr0.get c.outPtrReg).toNat = 0x10000 ∨ (gpr0.get c.outPtrReg).toNat = 0x80000
        rw [Bank16.get_ofFn _ hOutLt]
        split
        · exact Or.inr (by decide)
        · exact Or.inl (by decide)
      have hSpSub : (s₂.gpr.get 4 - 8).toNat = 0x7FFF8 := by decide
      have hRhs : ((s₂.gpr.get 4 - 8) + UInt64.ofNat k).toNat = 0x7FFF8 + k := by
        have hlt : 0x7FFF8 + k < 2 ^ 64 := by omega
        simp [UInt64.toNat_add, hSpSub, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]
      rcases hOutVal with h10 | h80
      · have hLhs : (s₂.gpr.get c.outPtrReg + UInt64.ofNat j).toNat = 0x10000 + j := by
          have hlt : 0x10000 + j < 2 ^ 64 := by omega
          simp [UInt64.toNat_add, h10, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]
        rw [hLhs, hRhs] at hNat; omega
      · have hLhs : (s₂.gpr.get c.outPtrReg + UInt64.ofNat j).toNat = 0x80000 + j := by
          have hlt : 0x80000 + j < 2 ^ 64 := by omega
          simp [UInt64.toNat_add, h80, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]
        rw [hLhs, hRhs] at hNat; omega

/-- **Anti-Vacuity / Inhabitedness Witness (`lean/uninhabited-premise-risk`) for `Arm64ContractInit`:**
    Every `AArch64` `FuncContract` with `pubGprs ⊆ 0..30` admits concrete pairs `(s₁, s₂)`
    with distinct secret memory (`0xAA ≠ 0x55`) satisfying `Arm64ContractInit c s₁ s₂`. -/
theorem aarch64_contract_init_inhabited (c : FuncContract)
    (hPubLt : ∀ r ∈ c.pubGprs, r < 31) :
    ∃ s₁ s₂ : Arm64State,
      s₁.mem 0x10000 ≠ s₂.mem 0x10000 ∧ Arm64ContractInit c s₁ s₂ := by
  let s₁ : Arm64State := {
    pc := 0, gpr := Bank32.const 0x4000, vec := Bank32.const Vec128.zero,
    cf := false, zf := false, dit := c.doitEnabled, halted := false,
    mem := fun _ => 0xAA
  }
  let s₂ : Arm64State := { s₁ with mem := fun _ => 0x55 }
  exact ⟨s₁, s₂, show (0xAA : UInt8) ≠ 0x55 by decide,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun r hr => ⟨hPubLt r hr, rfl⟩⟩⟩

/-! #### Inductive Relational Invariant & Step Soundness for `x86_64` -/

private def RelX86Gpr (s₁₀ s₂₀ : X86State) (orig : RegOrigin) (v₁ v₂ : UInt64) : Prop :=
  match orig with
  | .initSame r => r < 16 ∧ v₁ = s₁₀.gpr.get r ∧ v₂ = s₂₀.gpr.get r ∧ v₁ = v₂
  | .initOwn r => r < 16 ∧ v₁ = s₁₀.gpr.get r ∧ v₂ = s₂₀.gpr.get r
  | .spMinus8 => v₁ = s₁₀.gpr.get 4 - 8 ∧ v₂ = s₂₀.gpr.get 4 - 8 ∧ v₁ = v₂
  | .spAligned32 =>
      v₁ = (s₁₀.gpr.get 4 - 8) &&& 0xFFFFFFFFFFFFFFE0 ∧
      v₂ = (s₂₀.gpr.get 4 - 8) &&& 0xFFFFFFFFFFFFFFE0 ∧ v₁ = v₂
  | .frameSp =>
      v₁ = x86FrameSpVal (s₁₀.gpr.get 4) ∧
      v₂ = x86FrameSpVal (s₂₀.gpr.get 4) ∧ v₁ = v₂
  | .zeroConst => v₁ = 0 ∧ v₂ = 0
  | .constVal k => v₁ = k ∧ v₂ = k
  | .pubVal => v₁ = v₂
  | .secretVal => True

private theorem RelX86Gpr_public_eq {s₁₀ s₂₀ : X86State} {orig : RegOrigin} {v₁ v₂ : UInt64}
    (hRel : RelX86Gpr s₁₀ s₂₀ orig v₁ v₂) (hPub : orig.isPublic = true) :
    v₁ = v₂ := by
  cases orig with
  | initSame _ => exact hRel.2.2.2
  | initOwn _ => cases hPub
  | spMinus8 => exact hRel.2.2
  | spAligned32 => exact hRel.2.2
  | frameSp => exact hRel.2.2
  | zeroConst => exact hRel.1.trans hRel.2.symm
  | constVal _ => exact hRel.1.trans hRel.2.symm
  | pubVal => exact hRel
  | secretVal => cases hPub

private theorem RelX86Gpr_mono {s₁₀ s₂₀ : X86State} {a b : RegOrigin} {v₁ v₂ : UInt64}
    (hRel : RelX86Gpr s₁₀ s₂₀ a v₁ v₂) (hle : a.le b = true) :
    RelX86Gpr s₁₀ s₂₀ b v₁ v₂ := by
  unfold RegOrigin.le at hle
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hle
  rcases hle with (rfl | rfl) | ⟨rfl, hPub⟩
  · exact hRel
  · trivial
  · exact RelX86Gpr_public_eq hRel hPub

private def RelX86Vec (s₁₀ s₂₀ : X86State) (vo : VecOrigin) (v₁ v₂ : Vec256) : Prop :=
  match vo with
  | .initVec r =>
      r < 16 ∧
      ((v₁ = s₁₀.ymm.get r ∧ v₂ = s₂₀.ymm.get r) ∨
       (v₁ = ⟨(s₁₀.ymm.get r).w0, (s₁₀.ymm.get r).w1, 0, 0⟩ ∧
        v₂ = ⟨(s₂₀.ymm.get r).w0, (s₂₀.ymm.get r).w1, 0, 0⟩))
  | .zeroConst => v₁ = Vec256.zero ∧ v₂ = Vec256.zero
  | .pubVal => v₁ = v₂
  | .secretVal => True

private theorem RelX86Vec_public_eq {s₁₀ s₂₀ : X86State} {vo : VecOrigin} {v₁ v₂ : Vec256}
    (hRel : RelX86Vec s₁₀ s₂₀ vo v₁ v₂) (hPub : vo.isPublic = true) :
    v₁ = v₂ := by
  cases vo <;> simp [VecOrigin.isPublic, RelX86Vec] at hPub hRel
  · rw [hRel.1, hRel.2]
  · exact hRel

private theorem RelX86Vec_mono {s₁₀ s₂₀ : X86State} {a b : VecOrigin} {v₁ v₂ : Vec256}
    (hRel : RelX86Vec s₁₀ s₂₀ a v₁ v₂) (hle : a.le b = true) :
    RelX86Vec s₁₀ s₂₀ b v₁ v₂ := by
  unfold VecOrigin.le at hle
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hle
  rcases hle with (rfl | rfl) | ⟨rfl, hPub⟩
  · exact hRel
  · trivial
  · exact RelX86Vec_public_eq hRel hPub

private theorem writeMem8_zero_keep (m : UInt64 → UInt8) (a q : UInt64) (h : m q = 0 ∨ q = a) :
    writeMem8 m a 0 q = 0 := by
  unfold writeMem8
  by_cases hq : q = a
  · simp [hq]
  · rcases h with h | h
    · simp [hq, h]
    · exact absurd h hq

private theorem writeMem64_zero_keep (m : UInt64 → UInt8) (a q : UInt64)
    (h : m q = 0 ∨ q = a ∨ q = a + 1 ∨ q = a + 2 ∨ q = a + 3 ∨ q = a + 4 ∨ q = a + 5 ∨ q = a + 6 ∨ q = a + 7) :
    writeMem64 m a 0 q = 0 := by
  have z0 : (0 : UInt64).toUInt8 = 0 := by decide
  have z1 : ((0 : UInt64) >>> 8).toUInt8 = 0 := by decide
  have z2 : ((0 : UInt64) >>> 16).toUInt8 = 0 := by decide
  have z3 : ((0 : UInt64) >>> 24).toUInt8 = 0 := by decide
  have z4 : ((0 : UInt64) >>> 32).toUInt8 = 0 := by decide
  have z5 : ((0 : UInt64) >>> 40).toUInt8 = 0 := by decide
  have z6 : ((0 : UInt64) >>> 48).toUInt8 = 0 := by decide
  have z7 : ((0 : UInt64) >>> 56).toUInt8 = 0 := by decide
  unfold writeMem64
  simp only [z0, z1, z2, z3, z4, z5, z6, z7]
  rcases h with h | h | h | h | h | h | h | h | h
  · exact writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inl h)))))))))))))))
  · exact writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inr h)))))))))))))))
  · exact writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inr h)))))))))))))
  · exact writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inr h)))))))))))
  · exact writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inr h)))))))))
  · exact writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inr h)))))))
  · exact writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inr h)))))
  · exact writeMem8_zero_keep _ _ _ (Or.inl (writeMem8_zero_keep _ _ _ (Or.inr h)))
  · exact writeMem8_zero_keep _ _ _ (Or.inr h)

private theorem writeMem256_zero_keep (m : UInt64 → UInt8) (a q : UInt64)
    (h : m q = 0 ∨ ∃ i : Nat, i < 32 ∧ q = a + UInt64.ofNat i) :
    writeMem256 m a Vec256.zero q = 0 := by
  show writeMem64 (writeMem64 (writeMem64 (writeMem64 m a 0) (a + 8) 0) (a + 16) 0) (a + 24) 0 q = 0
  by_cases h0 : m q = 0
  · exact writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inl
      (writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inl h0)))))))
  · rcases h with h | ⟨i, hi, rfl⟩
    · exact absurd h h0
    match i, hi with
    | 0, _ => exact writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inr (Or.inl (UInt64.add_zero a)))))))))
    | 1, _ => exact writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inr (Or.inr (Or.inl (rfl))))))))))
    | 2, _ => exact writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl (rfl)))))))))))
    | 3, _ => exact writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (rfl))))))))))))
    | 4, _ => exact writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (rfl)))))))))))))
    | 5, _ => exact writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (rfl))))))))))))))
    | 6, _ => exact writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (rfl)))))))))))))))
    | 7, _ => exact writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (rfl)))))))))))))))
    | 8, _ => exact writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inr (Or.inl (rfl)))))))
    | 9, _ => exact writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inr (Or.inr (Or.inl ((UInt64.add_assoc a 8 1).symm))))))))
    | 10, _ => exact writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl ((UInt64.add_assoc a 8 2).symm)))))))))
    | 11, _ => exact writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((UInt64.add_assoc a 8 3).symm))))))))))
    | 12, _ => exact writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((UInt64.add_assoc a 8 4).symm)))))))))))
    | 13, _ => exact writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((UInt64.add_assoc a 8 5).symm))))))))))))
    | 14, _ => exact writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((UInt64.add_assoc a 8 6).symm)))))))))))))
    | 15, _ => exact writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((UInt64.add_assoc a 8 7).symm)))))))))))))
    | 16, _ => exact writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inr (Or.inl (rfl)))))
    | 17, _ => exact writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inr (Or.inr (Or.inl ((UInt64.add_assoc a 16 1).symm))))))
    | 18, _ => exact writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl ((UInt64.add_assoc a 16 2).symm)))))))
    | 19, _ => exact writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((UInt64.add_assoc a 16 3).symm))))))))
    | 20, _ => exact writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((UInt64.add_assoc a 16 4).symm)))))))))
    | 21, _ => exact writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((UInt64.add_assoc a 16 5).symm))))))))))
    | 22, _ => exact writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((UInt64.add_assoc a 16 6).symm)))))))))))
    | 23, _ => exact writeMem64_zero_keep _ _ _ (Or.inl (writeMem64_zero_keep _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((UInt64.add_assoc a 16 7).symm)))))))))))
    | 24, _ => exact writeMem64_zero_keep _ _ _ (Or.inr (Or.inl (rfl)))
    | 25, _ => exact writeMem64_zero_keep _ _ _ (Or.inr (Or.inr (Or.inl ((UInt64.add_assoc a 24 1).symm))))
    | 26, _ => exact writeMem64_zero_keep _ _ _ (Or.inr (Or.inr (Or.inr (Or.inl ((UInt64.add_assoc a 24 2).symm)))))
    | 27, _ => exact writeMem64_zero_keep _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((UInt64.add_assoc a 24 3).symm))))))
    | 28, _ => exact writeMem64_zero_keep _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((UInt64.add_assoc a 24 4).symm)))))))
    | 29, _ => exact writeMem64_zero_keep _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((UInt64.add_assoc a 24 5).symm))))))))
    | 30, _ => exact writeMem64_zero_keep _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ((UInt64.add_assoc a 24 6).symm)))))))))
    | 31, _ => exact writeMem64_zero_keep _ _ _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((UInt64.add_assoc a 24 7).symm)))))))))
    | n + 32, hn => exact absurd hn (by omega)

private theorem frame_addr_split (a : UInt64) (y z : Nat) :
    a + UInt64.ofNat (y + z) = a + UInt64.ofNat y + UInt64.ofNat z := by
  apply uint64_eq_of_toNat_eq
  have h64 : (2 : Nat) ^ 64 = 0x10000000000000000 := rfl
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat', h64]
  omega

/-- One iteration of the frame wipe: storing 32 zero bytes at `base + (25 - k) * 32` extends a
    zeroed prefix of `(25 - k) * 32` bytes to `(26 - k) * 32` bytes. -/
private theorem frame_store_zero_step (k : Nat) (m : UInt64 → UInt8) (base : UInt64)
    (hz : ∀ j : Nat, j < (25 - k) * 32 → m (base + UInt64.ofNat j) = 0)
    (j : Nat) (hj : j < (26 - k) * 32) (hk : k ≤ 25) :
    writeMem256 m (base + UInt64.ofNat ((25 - k) * 32)) Vec256.zero (base + UInt64.ofNat j) = 0 := by
  apply writeMem256_zero_keep
  by_cases hlt : j < (25 - k) * 32
  · exact Or.inl (hz j hlt)
  · refine Or.inr ⟨j - (25 - k) * 32, by omega, ?_⟩
    have hsplit : j = (25 - k) * 32 + (j - (25 - k) * 32) := by omega
    rw [← frame_addr_split, ← hsplit]

/-- Both executions hold zero bytes on the first `n` bytes of their aligned spill frame. -/
@[reducible] private def FrameZeroed (s₁₀ s₂₀ s₁ s₂ : X86State) (n : Nat) : Prop :=
  ∀ j : Nat, j < n →
    s₁.mem (x86FrameSpVal (s₁₀.gpr.get 4) + UInt64.ofNat j) = 0 ∧
    s₂.mem (x86FrameSpVal (s₂₀.gpr.get 4) + UInt64.ofNat j) = 0

/-- Frame-wipe loop phases (`mov ecx, 25; mov rax, rsp; L: vmovdqa [rax], ymm0; add rax, 32;
    dec ecx; jne L`): `1` at the store, `5` after it, `2` after the pointer bump, `3` after the
    decrement, `4` once the loop has exited with all 800 bytes zeroed. Every phase carries the
    zeroed prefix written so far. -/
private def RelX86Loop (s₁₀ s₂₀ s₁ s₂ : X86State) (loopSt : Nat) : Prop :=
  if loopSt == 0 then True
  else if loopSt == 1 then
    x86FrameSpVal (s₁₀.gpr.get 4) = x86FrameSpVal (s₂₀.gpr.get 4) ∧
    ∃ k : Nat, 1 ≤ k ∧ k ≤ 25 ∧
      s₁.gpr.get 1 = UInt64.ofNat k ∧ s₂.gpr.get 1 = UInt64.ofNat k ∧
      s₁.gpr.get 0 = x86FrameSpVal (s₁₀.gpr.get 4) + UInt64.ofNat ((25 - k) * 32) ∧
      s₂.gpr.get 0 = x86FrameSpVal (s₂₀.gpr.get 4) + UInt64.ofNat ((25 - k) * 32) ∧
      FrameZeroed s₁₀ s₂₀ s₁ s₂ ((25 - k) * 32)
  else if loopSt == 2 then
    x86FrameSpVal (s₁₀.gpr.get 4) = x86FrameSpVal (s₂₀.gpr.get 4) ∧
    ∃ k : Nat, 1 ≤ k ∧ k ≤ 25 ∧
      s₁.gpr.get 1 = UInt64.ofNat k ∧ s₂.gpr.get 1 = UInt64.ofNat k ∧
      s₁.gpr.get 0 = x86FrameSpVal (s₁₀.gpr.get 4) + UInt64.ofNat ((26 - k) * 32) ∧
      s₂.gpr.get 0 = x86FrameSpVal (s₂₀.gpr.get 4) + UInt64.ofNat ((26 - k) * 32) ∧
      FrameZeroed s₁₀ s₂₀ s₁ s₂ ((26 - k) * 32)
  else if loopSt == 3 then
    x86FrameSpVal (s₁₀.gpr.get 4) = x86FrameSpVal (s₂₀.gpr.get 4) ∧
    ∃ k' : Nat, k' ≤ 24 ∧
      s₁.gpr.get 1 = UInt64.ofNat k' ∧ s₂.gpr.get 1 = UInt64.ofNat k' ∧
      s₁.gpr.get 0 = x86FrameSpVal (s₁₀.gpr.get 4) + UInt64.ofNat ((25 - k') * 32) ∧
      s₂.gpr.get 0 = x86FrameSpVal (s₂₀.gpr.get 4) + UInt64.ofNat ((25 - k') * 32) ∧
      s₁.zf = (k' == 0) ∧ s₂.zf = (k' == 0) ∧
      FrameZeroed s₁₀ s₂₀ s₁ s₂ ((25 - k') * 32)
  else if loopSt == 4 then FrameZeroed s₁₀ s₂₀ s₁ s₂ 800
  else if loopSt == 5 then
    x86FrameSpVal (s₁₀.gpr.get 4) = x86FrameSpVal (s₂₀.gpr.get 4) ∧
    ∃ k : Nat, 1 ≤ k ∧ k ≤ 25 ∧
      s₁.gpr.get 1 = UInt64.ofNat k ∧ s₂.gpr.get 1 = UInt64.ofNat k ∧
      s₁.gpr.get 0 = x86FrameSpVal (s₁₀.gpr.get 4) + UInt64.ofNat ((25 - k) * 32) ∧
      s₂.gpr.get 0 = x86FrameSpVal (s₂₀.gpr.get 4) + UInt64.ofNat ((25 - k) * 32) ∧
      FrameZeroed s₁₀ s₂₀ s₁ s₂ ((26 - k) * 32)
  else False

/-- The wiped phase survives any step that leaves memory untouched; every other phase resets. -/
private theorem RelX86Loop_keep4 {s₁₀ s₂₀ s₁ s₂ s₁' s₂' : X86State} {n : Nat}
    (h : RelX86Loop s₁₀ s₂₀ s₁ s₂ n) (hm1 : s₁'.mem = s₁.mem) (hm2 : s₂'.mem = s₂.mem) :
    RelX86Loop s₁₀ s₂₀ s₁' s₂' (if n == 4 then 4 else 0) := by
  by_cases h4 : (n == 4) = true
  · have hn : n = 4 := beq_iff_eq.mp h4
    subst hn
    unfold RelX86Loop at h ⊢
    simp only [show (4 == 0) = false from rfl, show (4 == 1) = false from rfl, show (4 == 2) = false from rfl, show (4 == 3) = false from rfl, beq_self_eq_true, ↓reduceIte] at h ⊢
    intro j hj
    rw [hm1, hm2]
    exact h j hj
  · simp [h4, RelX86Loop]

private def RelX86 (s₁₀ s₂₀ : X86State) (st : X86AbsState) (s₁ s₂ : X86State) : Prop :=
  s₁.pc = s₂.pc ∧
  s₁.halted = false ∧ s₂.halted = false ∧
  (∀ r : Nat, r < 16 → RelX86Gpr s₁₀ s₂₀ (st.gpr.get r) (s₁.gpr.get r) (s₂.gpr.get r)) ∧
  (∀ i : Nat, i < 16 → RelX86Vec s₁₀ s₂₀ (st.ymm.get i) (s₁.ymm.get i) (s₂.ymm.get i)) ∧
  (st.cfPub = true → s₁.cf = s₂.cf) ∧
  (st.ofPub = true → s₁.ofFlag = s₂.ofFlag) ∧
  (st.zfPub = true → s₁.zf = s₂.zf) ∧
  (st.ymmDirty = false → s₁.ymmDirty = false ∧ s₂.ymmDirty = false) ∧
  (st.memUnmodified = true → s₁.mem = s₁₀.mem ∧ s₂.mem = s₂₀.mem) ∧
  (st.rbpSaved = true →
     s₁₀.gpr.get 4 = s₂₀.gpr.get 4 ∧
     readMem64 s₁.mem (s₁₀.gpr.get 4 - 8) = s₁₀.gpr.get 5 ∧
     readMem64 s₂.mem (s₂₀.gpr.get 4 - 8) = s₂₀.gpr.get 5) ∧
  RelX86Loop s₁₀ s₂₀ s₁ s₂ st.stackZeroLoop

private theorem RelX86_mono {s₁₀ s₂₀ s₁ s₂ : X86State} {a b : X86AbsState}
    (hRel : RelX86 s₁₀ s₂₀ a s₁ s₂) (hle : a.le b = true) :
    RelX86 s₁₀ s₂₀ b s₁ s₂ := by
  unfold X86AbsState.le at hle
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hle
  rcases hle with ⟨⟨⟨⟨⟨⟨⟨⟨hGpr, hYmm⟩, hCf⟩, hOf⟩, hZf⟩, hDirty⟩, hMem⟩, hRbp⟩, hLoop⟩
  rcases hRel with ⟨hPc, hH1, hH2, rGpr, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp, rLoop⟩
  refine ⟨hPc, hH1, hH2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr; exact RelX86Gpr_mono (rGpr r hr) (Bank16.allIdx_get hGpr hr)
  · intro i hi; exact RelX86Vec_mono (rYmm i hi) (Bank16.allIdx_get hYmm hi)
  · intro hb; exact hCf.elim (fun hbf => nomatch hbf.symm.trans hb) (fun ha => rCf ha)
  · intro hb; exact hOf.elim (fun hbf => nomatch hbf.symm.trans hb) (fun ha => rOf ha)
  · intro hb; exact hZf.elim (fun hbf => nomatch hbf.symm.trans hb) (fun ha => rZf ha)
  · intro hb; exact hDirty.elim (fun hbt => nomatch hbt.symm.trans hb) (fun ha => rDirty ha)
  · intro hb; exact hMem.elim (fun hbf => nomatch hbf.symm.trans hb) (fun ha => rMem ha)
  · intro hb; exact hRbp.elim (fun hbf => nomatch hbf.symm.trans hb) (fun ha => rRbp ha)
  · rcases hLoop with hb0 | heq
    · simp [RelX86Loop, hb0]
    · rwa [← heq]

private theorem RelX86_init {c : FuncContract} {s₁ s₂ : X86State}
    (hInit : X86ContractInit c s₁ s₂) :
    RelX86 s₁ s₂ (initX86AbsState c) s₁ s₂ := by
  rcases hInit with ⟨hpc1, hpc2, hh1, hh2, hd1, hd2, hPubGprs, _, _, _⟩
  refine ⟨by omega, hh1, hh2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    unfold initX86AbsState
    rw [Bank16.get_ofFn _ hr]
    split
    · rename_i hMemPub
      exact ⟨hr, rfl, rfl, (hPubGprs r hMemPub).2⟩
    · split
      · exact ⟨hr, rfl, rfl⟩
      · trivial
  · intro i hi
    unfold initX86AbsState
    rw [Bank16.get_ofFn _ hi]
    exact ⟨hi, Or.inl ⟨rfl, rfl⟩⟩
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · intro _; exact ⟨hd1, hd2⟩
  · intro _; exact ⟨rfl, rfl⟩
  · intro h; cases h
  · simp [initX86AbsState, RelX86Loop]

private theorem evalX86Alu_congr (op : X86AluOp) (is64 : Bool)
    {a₁ a₂ b₁ b₂ : UInt64} {cf₁ cf₂ : Bool}
    (ha : a₁ = a₂) (hb : b₁ = b₂)
    (hcf : (if op == .adc || op == .sbb then true else false) = true → cf₁ = cf₂) :
    evalX86Alu op is64 a₁ b₁ cf₁ = evalX86Alu op is64 a₂ b₂ cf₂ := by
  subst ha hb
  cases op <;> simp_all [evalX86Alu]

private theorem evalX86AluOf_congr (op : X86AluOp) (is64 : Bool)
    {a₁ a₂ b₁ b₂ : UInt64} {cf₁ cf₂ : Bool}
    (ha : a₁ = a₂) (hb : b₁ = b₂)
    (hcf : (if op == .adc || op == .sbb then true else false) = true → cf₁ = cf₂) :
    evalX86AluOf op is64 a₁ b₁ cf₁ = evalX86AluOf op is64 a₂ b₂ cf₂ := by
  subst ha hb
  cases op <;> simp_all [evalX86AluOf]

private theorem evalX86AluOf_sbb_self (is64 : Bool) (v : UInt64) (cf : Bool) :
    evalX86AluOf .sbb is64 v v cf = false := by
  dsimp only [evalX86AluOf, signedOutOfBounds]
  rw [Int.sub_self]
  cases is64 <;> cases cf <;> decide

private theorem evalX86Shift_fst_congr (sk : X86ShiftKind) (is64 : Bool) {v₁ v₂ : UInt64} (cnt : Nat)
    (cf₁ of₁ zf₁ cf₂ of₂ zf₂ : Bool) (hv : v₁ = v₂) :
    (evalX86Shift sk is64 v₁ cnt cf₁ of₁ zf₁).1 = (evalX86Shift sk is64 v₂ cnt cf₂ of₂ zf₂).1 := by
  subst hv
  cases is64
  · cases hc : (cnt % 32 == 0) <;> cases sk <;> simp [evalX86Shift, hc]
  · cases hc : (cnt % 64 == 0) <;> cases sk <;> simp [evalX86Shift, hc]

private theorem evalX86Shift_zf (sk : X86ShiftKind) (is64 : Bool) (v : UInt64) (cnt : Nat)
    (cf of_ zf : Bool) :
    (evalX86Shift sk is64 v cnt cf of_ zf).2.2.2 =
      if x86ShiftPreservesZf sk is64 cnt then zf
      else (evalX86Shift sk is64 v cnt cf of_ zf).1 == 0 := by
  cases is64
  · cases hc : (cnt % 32 == 0) <;> cases sk <;> simp [evalX86Shift, x86ShiftPreservesZf, hc]
  · cases hc : (cnt % 64 == 0) <;> cases sk <;> simp [evalX86Shift, x86ShiftPreservesZf, hc]

private theorem evalX86Addr_public_eq {s₁₀ s₂₀ s₁ s₂ : X86State} {st : X86AbsState}
    {addr : X86MemAddr} (nextPc : Nat)
    (hAddrOk : x86AddrIsPublic st addr = true)
    (hRegsOk : x86AddrRegsValid addr = true)
    (hGpr : ∀ r < 16, RelX86Gpr s₁₀ s₂₀ (st.gpr.get r) (s₁.gpr.get r) (s₂.gpr.get r)) :
    evalX86Addr s₁ nextPc addr = evalX86Addr s₂ nextPc addr := by
  cases addr with
  | baseDisp base disp =>
    simp only [x86AddrIsPublic, x86AddrRegsValid, decide_eq_true_eq] at hAddrOk hRegsOk
    rw [evalX86Addr, evalX86Addr, RelX86Gpr_public_eq (hGpr base hRegsOk) hAddrOk]
  | ripDisp disp => rfl
  | absDisp disp => rfl
  | indexedSib baseOpt idx scale disp =>
    cases baseOpt with
    | none =>
      simp only [x86AddrIsPublic, x86AddrRegsValid, Bool.and_true, decide_eq_true_eq] at hAddrOk hRegsOk
      have hIdx := RelX86Gpr_public_eq (hGpr idx hRegsOk) hAddrOk
      simp [evalX86Addr, hIdx]
    | some b =>
      simp only [x86AddrIsPublic, x86AddrRegsValid, Bool.and_eq_true, decide_eq_true_eq] at hAddrOk hRegsOk
      have hIdx := RelX86Gpr_public_eq (hGpr idx hRegsOk.1) hAddrOk.1
      have hBase := RelX86Gpr_public_eq (hGpr b hRegsOk.2) hAddrOk.2
      simp [evalX86Addr, hIdx, hBase]

private theorem isInPubMemRegion_bytes_eq {c : FuncContract} {s₁₀ s₂₀ s₁ s₂ : X86State}
    {st : X86AbsState} {addr : X86MemAddr} {wBytes : Nat} (nextPc : Nat)
    (hInit : X86ContractInit c s₁₀ s₂₀)
    (hRel : RelX86 s₁₀ s₂₀ st s₁ s₂)
    (hRegsOk : x86AddrRegsValid addr = true)
    (hIn : isInPubMemRegion c st addr wBytes = true) :
    ∀ j : Nat, j < wBytes →
      s₁.mem (evalX86Addr s₁ nextPc addr + UInt64.ofNat j) =
      s₂.mem (evalX86Addr s₂ nextPc addr + UInt64.ofNat j) := by
  rcases hRel with ⟨_, _, _, rGpr, _, _, _, _, _, rMem, _, _⟩
  unfold isInPubMemRegion at hIn
  cases hMemUnmod : st.memUnmodified
  · simp [hMemUnmod] at hIn
  · simp only [hMemUnmod, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hIn
    cases addr with
    | ripDisp _ => cases hIn
    | absDisp _ => cases hIn
    | indexedSib _ _ _ _ => cases hIn
    | baseDisp base disp =>
      simp only [x86AddrRegsValid, decide_eq_true_eq] at hRegsOk
      cases hOrig : st.gpr.get base <;> simp only [hOrig] at hIn <;> try contradiction
      case initSame r =>
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, beq_iff_eq] at hIn
        rcases hIn with ⟨hrPub, ⟨⟨ptrReg, regionLen⟩, hRegMem, hPtrEq, hBound⟩⟩
        subst hPtrEq
        rcases rMem hMemUnmod with ⟨hm1, hm2⟩
        have hBaseRel := rGpr base hRegsOk
        rw [hOrig] at hBaseRel
        rcases hBaseRel with ⟨_, hb1, hb2, _⟩
        rcases hInit with ⟨_, _, _, _, _, _, _, hPubMem, _, _⟩
        have hByte := (hPubMem (ptrReg, regionLen) hRegMem).2
        intro j hj
        have hAdd (x : UInt64) :
            x + disp + UInt64.ofNat j = x + UInt64.ofNat (disp.toNat + j) := by
          apply uint64_eq_of_toNat_eq
          simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.add_mod_mod, Nat.mod_add_mod]
          congr 1; omega
        rw [hm1, hm2, evalX86Addr, evalX86Addr, hb1, hb2, hAdd, hAdd]
        exact hByte (disp.toNat + j) (by omega)

private theorem frameSp_store_disjoint_spSlot {rsp₀ disp : UInt64} {wBytes : Nat}
    (hHeadroom : 0x400 ≤ rsp₀.toNat)
    (hDispBound : disp.toNat + wBytes ≤ 0x320) :
    ∀ j k : Nat, j < wBytes → k < 8 →
      (rsp₀ - 8) + UInt64.ofNat k ≠ x86FrameSpVal rsp₀ + disp + UInt64.ofNat j := by
  intro j k hj hk hEq
  have hRspLt := rsp₀.toNat_lt
  have hPow : (2 : Nat) ^ 64 = 0x10000000000000000 := rfl
  have hSpSlot : (rsp₀ - 8).toNat = rsp₀.toNat - 8 := by
    have h8 : (8 : UInt64).toNat = 8 := rfl
    simp only [UInt64.toNat_sub, h8, hPow]; omega
  have hAlign : ((rsp₀ - 8) &&& (0xFFFFFFFFFFFFFFE0 : UInt64)).toNat = ((rsp₀.toNat - 8) / 32) * 32 := by
    rw [align32_toNat, hSpSlot]
  have hFsp : (x86FrameSpVal rsp₀).toNat = ((rsp₀.toNat - 8) / 32) * 32 - 0x340 := by
    unfold x86FrameSpVal
    have h340 : (0x340 : UInt64).toNat = 0x340 := rfl
    simp only [UInt64.toNat_sub, hAlign, h340, hPow]; omega
  have hLhs : ((rsp₀ - 8) + UInt64.ofNat k).toNat = rsp₀.toNat - 8 + k := by
    simp only [UInt64.toNat_add, hSpSlot, UInt64.toNat_ofNat', hPow]; omega
  have hAdd1 : (x86FrameSpVal rsp₀ + disp).toNat = (x86FrameSpVal rsp₀).toNat + disp.toNat := by
    simp only [UInt64.toNat_add, hFsp, hPow]; omega
  have hRhs : (x86FrameSpVal rsp₀ + disp + UInt64.ofNat j).toNat =
      (x86FrameSpVal rsp₀).toNat + disp.toNat + j := by
    simp only [UInt64.toNat_add, UInt64.toNat_ofNat', hAdd1, hFsp, hPow]; omega
  have hNat := congrArg UInt64.toNat hEq
  rw [hLhs, hRhs, hFsp] at hNat
  omega

private theorem storePreservesSavedRbp_disjoint {c : FuncContract} {s₁₀ s₂₀ s₁ s₂ : X86State}
    {st : X86AbsState} {addr : X86MemAddr} {wBytes : Nat} (nextPc : Nat)
    (hInit : X86ContractInit c s₁₀ s₂₀)
    (hRel : RelX86 s₁₀ s₂₀ st s₁ s₂)
    (hRegsOk : x86AddrRegsValid addr = true)
    (hKeep : storePreservesSavedRbp c st addr wBytes = true) :
    (∀ j k : Nat, j < wBytes → k < 8 →
       (s₁₀.gpr.get 4 - 8) + UInt64.ofNat k ≠ evalX86Addr s₁ nextPc addr + UInt64.ofNat j) ∧
    (∀ j k : Nat, j < wBytes → k < 8 →
       (s₂₀.gpr.get 4 - 8) + UInt64.ofNat k ≠ evalX86Addr s₂ nextPc addr + UInt64.ofNat j) := by
  rcases hRel with ⟨_, _, _, rGpr, _, _, _, _, _, _, _, rLoop⟩
  unfold storePreservesSavedRbp at hKeep
  cases hRbp : st.rbpSaved
  · simp [hRbp] at hKeep
  · cases hUse : c.usesRbpFrame
    · simp [hRbp, hUse] at hKeep
    · simp only [hRbp, hUse, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hKeep
      rcases hInit with ⟨_, _, _, _, _, _, _, _, hFp1, hFp2⟩
      have hFp1' : c.outPtrReg < 16 ∧ 0x400 ≤ (s₁₀.gpr.get 4).toNat ∧
          ∀ j k : Nat, j < c.outBytes → k < 8 →
            s₁₀.gpr.get c.outPtrReg + UInt64.ofNat j ≠ (s₁₀.gpr.get 4 - 8) + UInt64.ofNat k :=
        hFp1.elim (fun hFalse => nomatch hUse.symm.trans hFalse) id
      have hFp2' : c.outPtrReg < 16 ∧ 0x400 ≤ (s₂₀.gpr.get 4).toNat ∧
          ∀ j k : Nat, j < c.outBytes → k < 8 →
            s₂₀.gpr.get c.outPtrReg + UInt64.ofNat j ≠ (s₂₀.gpr.get 4 - 8) + UInt64.ofNat k :=
        hFp2.elim (fun hFalse => nomatch hUse.symm.trans hFalse) id
      cases addr with
      | ripDisp _ => cases hKeep
      | absDisp _ => cases hKeep
      | indexedSib _ _ _ _ => cases hKeep
      | baseDisp base disp =>
        simp only [x86AddrRegsValid, decide_eq_true_eq] at hRegsOk
        by_cases hc1 : (st.gpr.get base == .frameSp && decide (disp.toNat + wBytes ≤ 0x320)) = true
        · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc1
          have hBRel := rGpr base hRegsOk
          rw [hc1.1] at hBRel
          rcases hBRel with ⟨hb1, hb2, _⟩
          refine ⟨fun j k hj hk => ?_, fun j k hj hk => ?_⟩
          · rw [evalX86Addr, hb1]
            exact frameSp_store_disjoint_spSlot hFp1'.2.1 hc1.2 j k hj hk
          · rw [evalX86Addr, hb2]
            exact frameSp_store_disjoint_spSlot hFp2'.2.1 hc1.2 j k hj hk
        · simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hKeep
          by_cases hc2 : (st.gpr.get base == .initSame c.outPtrReg &&
              c.outBytes == 0x320 && decide (disp.toNat + wBytes ≤ 0x320)) = true
          · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc2
            rcases hc2 with ⟨⟨hOrig, hOutSz⟩, hDisp⟩
            have hBRel := rGpr base hRegsOk
            rw [hOrig] at hBRel
            rcases hBRel with ⟨_, hb1, hb2, _⟩
            have hAdd (x : UInt64) (j : Nat) :
                x + disp + UInt64.ofNat j = x + UInt64.ofNat (disp.toNat + j) := by
              apply uint64_eq_of_toNat_eq
              simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.add_mod_mod, Nat.mod_add_mod]
              congr 1; omega
            refine ⟨fun j k hj hk hEq => ?_, fun j k hj hk hEq => ?_⟩
            · rw [evalX86Addr, hb1, hAdd] at hEq
              exact hFp1'.2.2 (disp.toNat + j) k (by omega) hk hEq.symm
            · rw [evalX86Addr, hb2, hAdd] at hEq
              exact hFp2'.2.2 (disp.toNat + j) k (by omega) hk hEq.symm
          · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hKeep
            by_cases hc3 : (base == 0 && disp == 0 && wBytes == 32 && st.stackZeroLoop == 1) = true
            · simp only [Bool.and_eq_true, beq_iff_eq] at hc3
              rcases hc3 with ⟨⟨⟨rfl, rfl⟩, rfl⟩, hLoop1⟩
              unfold RelX86Loop at rLoop
              simp only [hLoop1, show (1 == 0) = false from rfl, beq_self_eq_true, ↓reduceIte] at rLoop
              rcases rLoop with ⟨_, ⟨m, hm1, hm25, _, _, ha1, ha2, _⟩⟩
              have hAdd0 (x : UInt64) : x + 0 = x := by
                apply UInt64.eq_of_toBitVec_eq; simp
              have hDispM : (UInt64.ofNat ((25 - m) * 32)).toNat + 32 ≤ 0x320 := by
                have hlt : (25 - m) * 32 < 2 ^ 64 := by omega
                simp [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hlt]; omega
              refine ⟨fun j k hj hk => ?_, fun j k hj hk => ?_⟩
              · rw [evalX86Addr, ha1, hAdd0]
                exact frameSp_store_disjoint_spSlot hFp1'.2.1 hDispM j k hj hk
              · rw [evalX86Addr, ha2, hAdd0]
                exact frameSp_store_disjoint_spSlot hFp2'.2.1 hDispM j k hj hk
            · simp [hc3] at hKeep

private def checkLoopDecHelper : Bool :=
  (List.range 26).all (fun k =>
    if k == 0 then true
    else
      let res := maskGprWidth false (maskGprWidth false (UInt64.ofNat k) + (0 - 1))
      let ofFlag := evalX86IncDecOf false false (UInt64.ofNat k)
      (res == UInt64.ofNat (k - 1)) && ((res == 0) == (k - 1 == 0)) && !ofFlag)

private theorem checkLoopDecHelper_true : checkLoopDecHelper = true := by decide

private theorem loop_dec_ecx_step {k : Nat} (hk1 : 1 ≤ k) (hk25 : k ≤ 25) :
    let res := maskGprWidth false (maskGprWidth false (UInt64.ofNat k) + (0 - 1))
    res = UInt64.ofNat (k - 1) ∧ (res == 0) = (k - 1 == 0) ∧
      evalX86IncDecOf false false (UInt64.ofNat k) = false := by
  have hHelper := checkLoopDecHelper_true
  unfold checkLoopDecHelper at hHelper
  have hMem : k ∈ List.range 26 := List.mem_range.mpr (by omega)
  have hAll := List.all_eq_true.mp hHelper k hMem
  have hk0 : (k == 0) = false := beq_false_of_ne (by omega)
  simp only [hk0, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hAll
  exact ⟨hAll.1.1, hAll.1.2, hAll.2⟩

private theorem RelX86Gpr_set {s₁₀ s₂₀ : X86State} {g : Bank16 RegOrigin} {b₁ b₂ : Bank16 UInt64}
    {dst : Nat} {orig : RegOrigin} {v₁ v₂ : UInt64}
    (hd : dst < 16)
    (hOld : ∀ r < 16, RelX86Gpr s₁₀ s₂₀ (g.get r) (b₁.get r) (b₂.get r))
    (hNew : RelX86Gpr s₁₀ s₂₀ orig v₁ v₂) :
    ∀ r < 16, RelX86Gpr s₁₀ s₂₀ ((g.set dst orig).get r) ((b₁.set dst v₁).get r) ((b₂.set dst v₂).get r) := by
  intro r hr
  by_cases heq : r = dst
  · subst heq; simp only [Bank16.get_set_eq]; exact hNew
  · rw [Bank16.get_set_ne _ _ hd hr (Ne.symm heq),
        Bank16.get_set_ne _ _ hd hr (Ne.symm heq),
        Bank16.get_set_ne _ _ hd hr (Ne.symm heq)]
    exact hOld r hr

private theorem RelX86Vec_set {s₁₀ s₂₀ : X86State} {ym : Bank16 VecOrigin} {b₁ b₂ : Bank16 Vec256}
    {dst : Nat} {vo : VecOrigin} {v₁ v₂ : Vec256}
    (hd : dst < 16)
    (hOld : ∀ i < 16, RelX86Vec s₁₀ s₂₀ (ym.get i) (b₁.get i) (b₂.get i))
    (hNew : RelX86Vec s₁₀ s₂₀ vo v₁ v₂) :
    ∀ i < 16, RelX86Vec s₁₀ s₂₀ ((ym.set dst vo).get i) ((b₁.set dst v₁).get i) ((b₂.set dst v₂).get i) := by
  intro i hi
  by_cases heq : i = dst
  · subst heq; simp only [Bank16.get_set_eq]; exact hNew
  · rw [Bank16.get_set_ne _ _ hd hi (Ne.symm heq),
        Bank16.get_set_ne _ _ hd hi (Ne.symm heq),
        Bank16.get_set_ne _ _ hd hi (Ne.symm heq)]
    exact hOld i hi

private theorem readMem128_congr {m1 m2 : UInt64 → UInt8} {addr : UInt64}
    (h : ∀ j : Nat, j < 16 → m1 (addr + UInt64.ofNat j) = m2 (addr + UInt64.ofNat j)) :
    readMem128 m1 addr = readMem128 m2 addr := by
  have h8 : readMem64 m1 (addr + 8) = readMem64 m2 (addr + 8) := by
    apply readMem64_congr; intro j hj
    have hAdd : addr + 8 + UInt64.ofNat j = addr + UInt64.ofNat (8 + j) := by
      apply uint64_eq_of_toNat_eq
      have h8v : (8 : UInt64).toNat = 8 := rfl
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat', h8v, Nat.add_mod_mod, Nat.mod_add_mod]
      congr 1; omega
    rw [hAdd]; exact h (8 + j) (by omega)
  unfold readMem128
  rw [readMem64_congr (fun j hj => h j (by omega)), h8]

private theorem readMem256_congr {m1 m2 : UInt64 → UInt8} {addr : UInt64}
    (h : ∀ j : Nat, j < 32 → m1 (addr + UInt64.ofNat j) = m2 (addr + UInt64.ofNat j)) :
    readMem256 m1 addr = readMem256 m2 addr := by
  have hSlot (base : Nat) (hb : base + 8 ≤ 32) :
      readMem64 m1 (addr + UInt64.ofNat base) = readMem64 m2 (addr + UInt64.ofNat base) := by
    apply readMem64_congr; intro j hj
    have hAdd : addr + UInt64.ofNat base + UInt64.ofNat j = addr + UInt64.ofNat (base + j) := by
      apply uint64_eq_of_toNat_eq
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.add_mod_mod, Nat.mod_add_mod]
      congr 1; omega
    rw [hAdd]; exact h (base + j) (by omega)
  have h0 := readMem64_congr (fun j hj => h j (by omega))
  have h8 : readMem64 m1 (addr + 8) = readMem64 m2 (addr + 8) := hSlot 8 (by omega)
  have h16 : readMem64 m1 (addr + 16) = readMem64 m2 (addr + 16) := hSlot 16 (by omega)
  have h24 : readMem64 m1 (addr + 24) = readMem64 m2 (addr + 24) := hSlot 24 (by omega)
  unfold readMem256
  rw [h0, h8, h16, h24]

private theorem evalX86Cond_public_eq {st : X86AbsState} {s₁ s₂ : X86State} {cc : Nat}
    (hPub : x86CondIsPublic cc st = true)
    (rCf : st.cfPub = true → s₁.cf = s₂.cf)
    (rZf : st.zfPub = true → s₁.zf = s₂.zf) :
    evalX86Cond cc s₁ = evalX86Cond cc s₂ := by
  unfold x86CondIsPublic at hPub
  unfold evalX86Cond
  by_cases c2 : cc == 2
  · simp [c2] at hPub ⊢; exact rCf hPub
  · by_cases c3 : cc == 3
    · simp [c2, c3] at hPub ⊢; exact rCf hPub
    · by_cases c4 : cc == 4
      · simp [c2, c3, c4] at hPub ⊢; exact rZf hPub
      · by_cases c5 : cc == 5
        · simp [c2, c3, c4, c5] at hPub ⊢; exact rZf hPub
        · simp [c2, c3, c4, c5] at hPub

private theorem evalX86Alu_xor_self (is64 : Bool) (v : UInt64) (cf : Bool) :
    evalX86Alu .xorOp is64 v v cf = (0, false, true) := by
  unfold evalX86Alu maskGprWidth
  have hxor : v ^^^ v = 0 := by apply UInt64.eq_of_toBitVec_eq; simp
  cases is64 <;> simp only [hxor] <;> rfl

private theorem maskGprWidth_toNat_lt (is64 : Bool) (v : UInt64) :
    (maskGprWidth is64 v).toNat < (if is64 then 0x10000000000000000 else 0x100000000) := by
  cases is64
  · unfold maskGprWidth
    simp only [Bool.false_eq_true, ↓reduceIte, UInt64.toNat_and]
    have h32 : (0xFFFFFFFF : UInt64).toNat = 0xFFFFFFFF := rfl
    rw [h32]
    have := @Nat.and_le_right v.toNat 0xFFFFFFFF
    omega
  · unfold maskGprWidth
    simpa using v.toNat_lt

theorem evalX86Alu_sbb_self_congr (is64 : Bool) (v₁ v₂ : UInt64) (cf : Bool) :
    evalX86Alu .sbb is64 v₁ v₁ cf = evalX86Alu .sbb is64 v₂ v₂ cf := by
  have h1 := maskGprWidth_toNat_lt is64 v₁
  have h2 := maskGprWidth_toNat_lt is64 v₂
  unfold evalX86Alu
  cases cf <;> cases is64 <;> simp only [↓reduceIte, Bool.false_eq_true, Nat.add_zero, Nat.sub_zero] at h1 h2 ⊢
  · have e1 : (maskGprWidth false v₁).toNat + 0x100000000 * 2 - (maskGprWidth false v₁).toNat =
        0x100000000 * 2 := by omega
    have e2 : (maskGprWidth false v₂).toNat + 0x100000000 * 2 - (maskGprWidth false v₂).toNat =
        0x100000000 * 2 := by omega
    have l1 : decide ((maskGprWidth false v₁).toNat < (maskGprWidth false v₁).toNat) = false :=
      decide_eq_false (by omega)
    have l2 : decide ((maskGprWidth false v₂).toNat < (maskGprWidth false v₂).toNat) = false :=
      decide_eq_false (by omega)
    rw [l1, l2, e1, e2]
  · unfold maskGprWidth at h1 h2 ⊢
    simp only [↓reduceIte] at h1 h2 ⊢
    have e1 : v₁.toNat + 0x10000000000000000 * 2 - v₁.toNat = 0x10000000000000000 * 2 := by omega
    have e2 : v₂.toNat + 0x10000000000000000 * 2 - v₂.toNat = 0x10000000000000000 * 2 := by omega
    have l1 : decide (v₁.toNat < v₁.toNat) = false := decide_eq_false (by omega)
    have l2 : decide (v₂.toNat < v₂.toNat) = false := decide_eq_false (by omega)
    rw [l1, l2, e1, e2]
  · have l1 : decide ((maskGprWidth false v₁).toNat < (maskGprWidth false v₁).toNat + 1) = true :=
      decide_eq_true (by omega)
    have l2 : decide ((maskGprWidth false v₂).toNat < (maskGprWidth false v₂).toNat + 1) = true :=
      decide_eq_true (by omega)
    have e1 : (maskGprWidth false v₁).toNat + 0x100000000 * 2 - (maskGprWidth false v₁).toNat - 1 =
        0x100000000 * 2 - 1 := by omega
    have e2 : (maskGprWidth false v₂).toNat + 0x100000000 * 2 - (maskGprWidth false v₂).toNat - 1 =
        0x100000000 * 2 - 1 := by omega
    rw [l1, l2, e1, e2]
  · unfold maskGprWidth at h1 h2 ⊢
    simp only [↓reduceIte] at h1 h2 ⊢
    have l1 : decide (v₁.toNat < v₁.toNat + 1) = true := decide_eq_true (by omega)
    have l2 : decide (v₂.toNat < v₂.toNat + 1) = true := decide_eq_true (by omega)
    have e1 : v₁.toNat + 0x10000000000000000 * 2 - v₁.toNat - 1 = 0x10000000000000000 * 2 - 1 := by omega
    have e2 : v₂.toNat + 0x10000000000000000 * 2 - v₂.toNat - 1 = 0x10000000000000000 * 2 - 1 := by omega
    rw [l1, l2, e1, e2]

private theorem evalVecShift256_zero (sk : X86VecShiftKind) (is256 : Bool) (imm : Nat) :
    clampVecWidth is256 (evalVecShift256 sk Vec256.zero imm) = Vec256.zero := by
  have hzL (c : UInt64) : (0 : UInt64) <<< c = 0 := by apply UInt64.eq_of_toBitVec_eq; simp
  have hzR (c : UInt64) : (0 : UInt64) >>> c = 0 := by apply UInt64.eq_of_toBitVec_eq; simp
  have hzA (m : UInt64) : (0 : UInt64) &&& m = 0 := by apply UInt64.eq_of_toBitVec_eq; simp
  unfold evalVecShift256 clampVecWidth Vec256.zero
  cases sk <;> cases is256 <;> simp [hzL, hzR, hzA] <;>
    repeat' split <;> simp_all [hzL, hzR, hzA]

private theorem uint64_add_zero (x : UInt64) : x + 0 = x := by
  apply UInt64.eq_of_toBitVec_eq; simp

private theorem findInstrAtPc_offset {Instr : Type} {pc : Nat} {prog : List (DecodedInstr Instr)}
    {d : DecodedInstr Instr} (h : findInstrAtPc pc prog = some d) :
    d.offset = pc := by
  induction prog with
  | nil => cases h
  | cons x xs ih =>
    unfold findInstrAtPc at h
    by_cases heq : x.offset == pc
    · simp [heq] at h; subst h; exact beq_iff_eq.mp heq
    · simp [heq] at h; exact ih h

private theorem transferX86Instr_step_sound {c : FuncContract}
    {s₁₀ s₂₀ s₁ s₂ : X86State} {d : DecodedInstr X86Instr}
    {st : X86AbsState} {succs : List (Nat × X86AbsState)}
    (hInit : X86ContractInit c s₁₀ s₂₀)
    (hRel : RelX86 s₁₀ s₂₀ st s₁ s₂)
    (_hPcEq : s₁.pc = d.offset)
    (hTr : transferX86Instr c d st = some succs) :
    let (s₁', obs₁) := stepX86 d s₁
    let (s₂', obs₂) := stepX86 d s₂
    obs₁ = obs₂ ∧
    obs₁.isDoitSafe = true ∧
    ((s₁'.halted = true ∧ s₂'.halted = true ∧ X86ExitHygiene c s₁₀ s₂₀ s₁' s₂') ∨
     (∃ nst : X86AbsState, (s₁'.pc, nst) ∈ succs ∧ RelX86 s₁₀ s₂₀ nst s₁' s₂')) := by
  have hPolicy : x86ViolatesPolicy c d.instr st = false := by
    cases hp : x86ViolatesPolicy c d.instr st with
    | false => rfl
    | true => simp [transferX86Instr, hp] at hTr
  cases hValid : x86InstrRegsValid d.instr
  · unfold transferX86Instr at hTr; simp [hPolicy, hValid] at hTr
  · rcases hRel with ⟨hPc12, hH1, hH2, rGpr, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp, rLoop⟩
    have hRelFull : RelX86 s₁₀ s₂₀ st s₁ s₂ :=
      ⟨hPc12, hH1, hH2, rGpr, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp, rLoop⟩
    cases hIns : d.instr <;>
      unfold transferX86Instr at hTr <;>
      rw [hPolicy, hIns] at hTr <;>
      rw [hIns] at hValid <;>
      simp only [hValid, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr <;>
      simp only [x86InstrRegsValid, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hValid
    case nop =>
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp,
        by simp [RelX86Loop]⟩
    case mfence =>
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp,
        by simp [RelX86Loop]⟩
    case pushReg reg =>
      by_cases hPushOk : (c.usesRbpFrame && reg == 5 && st.gpr.get 4 == .initSame 4 &&
          st.gpr.get 5 == .initOwn 5 && decide (4 ∈ c.pubGprs) && !st.rbpSaved) = true
      · simp only [hPushOk, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at hPushOk
        rcases hPushOk with ⟨⟨⟨⟨⟨_, rfl⟩, hSp4⟩, hBp5⟩, _⟩, _⟩
        have r4 := rGpr 4 (by omega); rw [hSp4] at r4; rcases r4 with ⟨_, hs1_4, hs2_4, h4eq⟩
        have r5 := rGpr 5 (by omega); rw [hBp5] at r5; rcases r5 with ⟨_, hs1_5, hs2_5⟩
        have hSpEq0 : s₁₀.gpr.get 4 = s₂₀.gpr.get 4 := by rw [← hs1_4, ← hs2_4, h4eq]
        simp only [stepX86, hIns, hs1_4, hs2_4, hs1_5, hs2_5, ← hSpEq0, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2,
          RelX86Gpr_set (by omega) rGpr ⟨rfl, hSpEq0 ▸ rfl, rfl⟩,
          rYmm, rCf, rOf, rZf, rDirty, (fun h => nomatch h), ?_, by simp [RelX86Loop]⟩
        intro _
        exact ⟨hSpEq0, readMem64_writeMem64_self _ _ _, hSpEq0 ▸ readMem64_writeMem64_self _ _ _⟩
      · have hF : (c.usesRbpFrame && reg == 5 && st.gpr.get 4 == .initSame 4 &&
            st.gpr.get 5 == .initOwn 5 && decide (4 ∈ c.pubGprs) && !st.rbpSaved) = false :=
          Bool.eq_false_iff.mpr hPushOk
        simp only [hF, Bool.false_eq_true, ↓reduceIte] at hTr; cases hTr
    case popReg reg =>
      by_cases hPopOk : (c.usesRbpFrame && reg == 5 && st.gpr.get 4 == .spMinus8 && st.rbpSaved) = true
      · simp only [hPopOk, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [Bool.and_eq_true, beq_iff_eq] at hPopOk
        rcases hPopOk with ⟨⟨⟨_, rfl⟩, hSp4⟩, hRbpSaved⟩
        have r4 := rGpr 4 (by omega); rw [hSp4] at r4; rcases r4 with ⟨hs1_4, hs2_4, h4eq⟩
        rcases rRbp hRbpSaved with ⟨hSp0Eq, hMem5_1, hMem5_2⟩
        have hAdd8 (x : UInt64) : (x - 8) + 8 = x := by
          apply UInt64.eq_of_toBitVec_eq; simp
        simp only [stepX86, hIns, hs1_4, hs2_4, ← hSp0Eq, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, rCf, rOf, rZf, rDirty, rMem,
          fun _ => ⟨hSp0Eq, hMem5_1, hSp0Eq ▸ hMem5_2⟩, RelX86Loop_keep4 rLoop rfl rfl⟩
        refine RelX86Gpr_set (by omega)
          (RelX86Gpr_set (by omega) rGpr ⟨by omega, hAdd8 _, hSp0Eq ▸ hAdd8 _, rfl⟩)
          ⟨by omega, hMem5_1, by rwa [hSp0Eq]⟩
      · have hF : (c.usesRbpFrame && reg == 5 && st.gpr.get 4 == .spMinus8 && st.rbpSaved) = false :=
          Bool.eq_false_iff.mpr hPopOk
        simp only [hF, Bool.false_eq_true, ↓reduceIte] at hTr; cases hTr
    case ret =>
      by_cases hRetOk : ((st.gpr.get 4 == .initSame 4 && decide (4 ∈ c.pubGprs)) &&
          (((st.gpr.get 3).le (.initOwn 3) || st.gpr.get 3 == .initSame 3) &&
           [3, 5, 12, 13, 14, 15].all (fun r => st.gpr.get r == .initOwn r || st.gpr.get r == .initSame r)) &&
          !st.ymmDirty &&
          st.ymm.allIdx (fun _ vo => vo != .secretVal && vo != .pubVal) &&
          c.wipedScratchGprs.all (fun r => st.gpr.get r == .zeroConst) &&
          (!c.usesRbpFrame || st.stackZeroLoop == 4)) = true
      · simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq,
          List.all_eq_true] at hRetOk
        rcases hRetOk with ⟨⟨⟨⟨⟨⟨hSp4, _⟩, ⟨_, hCallee⟩⟩, hClean⟩, hVecWiped⟩, hGprWiped⟩, hFrame⟩
        have r4 := rGpr 4 (by omega)
        rw [hSp4] at r4
        have hSpEq : s₁.gpr.get 4 = s₂.gpr.get 4 := r4.2.2.2
        simp only [stepX86, hIns, hSpEq, true_and]
        left
        refine ⟨?_, ?_, rDirty hClean, ?_, ?_, ?_⟩
        · simp only [Bank16.get_set_eq]
          exact ⟨congrArg (· + 8) (hSpEq.symm.trans r4.2.1), congrArg (· + 8) r4.2.2.1⟩
        · intro r hr
          have hcr := hCallee r hr
          have hr16 : r < 16 := by simp at hr; omega
          have hne : 4 ≠ r := by intro he; subst r; simp at hr
          simp only [Bank16.get_set_ne _ _ (by omega) hr16 hne]
          have rr := rGpr r hr16
          rcases hcr with hOwn | hSame
          · rw [hOwn] at rr; exact rr.2
          · rw [hSame] at rr; exact ⟨rr.2.1, rr.2.2.1⟩
        · intro i hi
          have hNotSec := Bank16.allIdx_get hVecWiped hi
          simp only [Bool.and_eq_true, bne_iff_ne] at hNotSec
          have rv := rYmm i hi
          cases hVo : st.ymm.get i <;> rw [hVo] at rv hNotSec
          · exact Or.inr ⟨_, rv.1, rv.2⟩
          · exact Or.inl rv
          · exact absurd rfl hNotSec.2
          · exact absurd rfl hNotSec.1
        · intro r hr
          have hZ := hGprWiped r hr
          have hne : 4 ≠ r := by
            intro he; subst r; rw [hSp4] at hZ; cases hZ
          have hkeep (g : Bank16 UInt64) (v : UInt64) : (g.set 4 v).get r = g.get r := by
            by_cases hlt : r < 16
            · exact Bank16.get_set_ne _ _ (by omega) hlt hne
            · match r with
              | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 => omega
              | _ + 15 => rfl
          simp only [hkeep]
          by_cases hr16 : r < 16
          · have rr := rGpr r hr16; rw [hZ] at rr; exact rr
          · have h15 : ∀ {α : Type} (b : Bank16 α), b.get r = b.get 15 := fun b => by
              match r with
              | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 => exact False.elim (by omega)
              | _ + 15 => rfl
            have rr := rGpr 15 (by omega)
            rw [h15 st.gpr] at hZ; rw [hZ] at rr
            rw [h15 s₁.gpr, h15 s₂.gpr]; exact rr
        · intro hFr
          rcases hFrame with hNo | h4
          · rw [hNo] at hFr; cases hFr
          · unfold RelX86Loop at rLoop
            simp only [h4, show (4 == 0) = false from rfl, show (4 == 1) = false from rfl, show (4 == 2) = false from rfl, show (4 == 3) = false from rfl, beq_self_eq_true, ↓reduceIte] at rLoop
            exact rLoop
      · have hF : ((st.gpr.get 4 == .initSame 4 && decide (4 ∈ c.pubGprs)) &&
            (((st.gpr.get 3).le (.initOwn 3) || st.gpr.get 3 == .initSame 3) &&
             [3, 5, 12, 13, 14, 15].all (fun r => st.gpr.get r == .initOwn r || st.gpr.get r == .initSame r)) &&
            !st.ymmDirty &&
            st.ymm.allIdx (fun _ vo => vo != .secretVal && vo != .pubVal) &&
            c.wipedScratchGprs.all (fun r => st.gpr.get r == .zeroConst) &&
            (!c.usesRbpFrame || st.stackZeroLoop == 4)) = false :=
          Bool.eq_false_iff.mpr hRetOk
        simp only [hF, Bool.false_eq_true, ↓reduceIte] at hTr; cases hTr
    case movRegReg is64 dst src =>
      rcases hValid with ⟨hd16, hs16⟩
      by_cases hInitLoop : (is64 && dst == 0 && src == 4 && st.gpr.get 4 == .frameSp &&
          st.gpr.get 1 == .constVal 25) = true
      · simp only [hInitLoop, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [Bool.and_eq_true, beq_iff_eq] at hInitLoop
        rcases hInitLoop with ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, hSpFsp⟩, hRcx25⟩
        have r4 := rGpr 4 (by omega); rw [hSpFsp] at r4; rcases r4 with ⟨h4_1, h4_2, h4eq⟩
        have r1 := rGpr 1 (by omega); rw [hRcx25] at r1; rcases r1 with ⟨h1_1, h1_2⟩
        simp only [stepX86, hIns, maskGprWidth, ↓reduceIte, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp, ?_⟩
        · intro r hr
          by_cases hr1 : r = 1
          · subst hr1
            rw [Bank16.get_set_eq, Bank16.get_set_ne _ _ (by omega) (by omega) (by omega),
                Bank16.get_set_ne _ _ (by omega) (by omega) (by omega)]
            simp [RelX86Gpr, h1_1, h1_2]
          · rw [Bank16.get_set_ne _ _ (by omega) hr (Ne.symm hr1)]
            exact RelX86Gpr_set (by omega) rGpr (by simp [RelX86Gpr, h4eq]) r hr
        · unfold RelX86Loop
          simp only [show (1 == 0) = false from rfl, beq_self_eq_true, ↓reduceIte]
          have hFspEq : x86FrameSpVal (s₁₀.gpr.get 4) = x86FrameSpVal (s₂₀.gpr.get 4) := by
            rw [← h4_1, ← h4_2, h4eq]
          refine ⟨hFspEq, 25, by omega, by omega, ?_, ?_, ?_, ?_, fun j hj => absurd hj (by omega)⟩
          · rw [Bank16.get_set_ne _ _ (by omega) (by omega) (by omega)]; exact h1_1
          · rw [Bank16.get_set_ne _ _ (by omega) (by omega) (by omega)]; exact h1_2
          · simp only [Bank16.get_set_eq, Nat.sub_self, Nat.zero_mul]
            exact h4_1.trans (uint64_add_zero _).symm
          · simp only [Bank16.get_set_eq, Nat.sub_self, Nat.zero_mul]
            exact h4_2.trans (uint64_add_zero _).symm
      · simp only [hInitLoop, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [stepX86, hIns, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp,
          RelX86Loop_keep4 rLoop rfl rfl⟩
        apply RelX86Gpr_set hd16 rGpr
        cases is64
        · simp only [Bool.false_eq_true, ↓reduceIte]
          by_cases hPub : (st.gpr.get src).isPublic = true
          · simp only [hPub, ↓reduceIte, RelX86Gpr]
            rw [RelX86Gpr_public_eq (rGpr src hs16) hPub]
          · simp [hPub, RelX86Gpr]
        · simp only [↓reduceIte, maskGprWidth]
          exact rGpr src hs16
    case movImm is64 dst imm =>
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp,
        by simp [RelX86Loop]⟩
      apply RelX86Gpr_set hValid rGpr
      by_cases hz : (maskGprWidth is64 imm == 0) = true
      · simp only [hz, ↓reduceIte, RelX86Gpr]; exact ⟨beq_iff_eq.mp hz, beq_iff_eq.mp hz⟩
      · simp [hz, RelX86Gpr]
    case loadGpr wBytes is64 dst addr =>
      rcases hValid with ⟨⟨hw18, hd16⟩, hAddrReg⟩
      cases hAddrPub : x86AddrIsPublic st addr
      · simp [hAddrPub] at hTr
      · simp only [hAddrPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hEaEq := evalX86Addr_public_eq (d.offset + d.byteLen) hAddrPub hAddrReg rGpr
        simp only [stepX86, hIns, hEaEq, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp,
          by simp [RelX86Loop]⟩
        apply RelX86Gpr_set hd16 rGpr
        by_cases hIn : isInPubMemRegion c st addr wBytes = true
        · simp only [hIn, ↓reduceIte, RelX86Gpr]
          have hBytes := isInPubMemRegion_bytes_eq (d.offset + d.byteLen) hInit hRelFull hAddrReg hIn
          rcases hw18 with rfl | rfl
          · have hb0 := hBytes 0 (by omega)
            rw [hEaEq] at hb0
            have h0 : (evalX86Addr s₂ (d.offset + d.byteLen) addr + UInt64.ofNat 0) =
                evalX86Addr s₂ (d.offset + d.byteLen) addr := uint64_add_zero _
            rw [h0] at hb0
            simp [hb0]
          · have hR64 : readMem64 s₁.mem (evalX86Addr s₂ (d.offset + d.byteLen) addr) =
                readMem64 s₂.mem (evalX86Addr s₂ (d.offset + d.byteLen) addr) := by
              apply readMem64_congr; intro j hj
              simpa only [← hEaEq] using hBytes j hj
            simp [show (8 == 1) = false from rfl, hR64]
        · simp [hIn, RelX86Gpr]
    case storeGpr wBytes src addr =>
      rcases hValid with ⟨⟨hw18, hs16⟩, hAddrReg⟩
      cases hAddrPub : x86AddrIsPublic st addr
      · simp [hAddrPub] at hTr
      · simp only [hAddrPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hEaEq := evalX86Addr_public_eq (d.offset + d.byteLen) hAddrPub hAddrReg rGpr
        simp only [stepX86, hIns, hEaEq, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, rYmm, rCf, rOf, rZf, rDirty,
          (fun h => nomatch h), ?_, by simp [RelX86Loop]⟩
        intro hRbpOk
        cases hRbpB : st.rbpSaved
        · simp [hRbpB] at hRbpOk
        · simp only [hRbpB, ↓reduceIte] at hRbpOk
          rcases rRbp hRbpB with ⟨hSp0Eq, hM1, hM2⟩
          rcases storePreservesSavedRbp_disjoint (d.offset + d.byteLen) hInit hRelFull hAddrReg hRbpOk
            with ⟨hDisj1, hDisj2⟩
          refine ⟨hSp0Eq, ?_, ?_⟩
          · rw [hEaEq] at hDisj1
            rcases hw18 with rfl | rfl
            · simp only [beq_self_eq_true, ↓reduceIte]
              rw [readMem64_congr (fun k hk =>
                writeMem8_ne _ _ (by simpa [uint64_add_zero] using hDisj1 0 k (by omega) hk))]
              exact hM1
            · simp only [show (8 == 1) = false from rfl, Bool.false_eq_true, ↓reduceIte]
              rw [readMem64_congr (fun k hk => writeMem64_ne _ _ (fun j hj => hDisj1 j k hj hk))]
              exact hM1
          · rcases hw18 with rfl | rfl
            · simp only [beq_self_eq_true, ↓reduceIte]
              rw [readMem64_congr (fun k hk =>
                writeMem8_ne _ _ (by simpa [uint64_add_zero] using hDisj2 0 k (by omega) hk))]
              exact hM2
            · simp only [show (8 == 1) = false from rfl, Bool.false_eq_true, ↓reduceIte]
              rw [readMem64_congr (fun k hk => writeMem64_ne _ _ (fun j hj => hDisj2 j k hj hk))]
              exact hM2
    case aluRegReg op is64 dst src =>
      rcases hValid with ⟨hd16, hs16⟩
      by_cases hXorSelf : (op == .xorOp && dst == src) = true
      · simp only [hXorSelf, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [Bool.and_eq_true, beq_iff_eq] at hXorSelf
        rcases hXorSelf with ⟨rfl, rfl⟩
        simp only [stepX86, hIns, evalX86Alu_xor_self, evalX86AluOf, true_and]
        exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2,
          RelX86Gpr_set hd16 rGpr ⟨rfl, rfl⟩,
          rYmm, fun _ => rfl, fun _ => rfl, fun _ => rfl, rDirty, rMem, rRbp, RelX86Loop_keep4 rLoop rfl rfl⟩
      · simp only [hXorSelf, Bool.false_eq_true, ↓reduceIte] at hTr
        by_cases hSbbSelf : (op == .sbb && dst == src) = true
        · simp only [hSbbSelf, ↓reduceIte] at hTr
          injection hTr with hS; subst hS
          simp only [Bool.and_eq_true, beq_iff_eq] at hSbbSelf
          rcases hSbbSelf with ⟨rfl, rfl⟩
          simp only [stepX86, hIns, evalX86AluOf_sbb_self, true_and]
          refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, ?_, (fun _ => rfl), ?_, rDirty, rMem, rRbp,
            by simp [RelX86Loop]⟩
          · apply RelX86Gpr_set hd16 rGpr
            by_cases hCfB : st.cfPub = true
            · simp only [hCfB, ↓reduceIte, RelX86Gpr]
              rw [rCf hCfB, evalX86Alu_sbb_self_congr]
            · simp [hCfB, RelX86Gpr]
          · intro hCfB
            rw [rCf hCfB, evalX86Alu_sbb_self_congr]
          · intro hCfB
            rw [rCf hCfB, evalX86Alu_sbb_self_congr]
        · simp only [hSbbSelf, Bool.false_eq_true, ↓reduceIte] at hTr
          injection hTr with hS; subst hS
          simp only [stepX86, hIns, true_and]
          have hAluEq : ((st.gpr.get dst).isPublic && (st.gpr.get src).isPublic &&
              (if op == .adc || op == .sbb then st.cfPub else true)) = true →
              evalX86Alu op is64 (s₁.gpr.get dst) (s₁.gpr.get src) s₁.cf =
              evalX86Alu op is64 (s₂.gpr.get dst) (s₂.gpr.get src) s₂.cf := by
            intro hBoth
            simp only [Bool.and_eq_true] at hBoth
            exact evalX86Alu_congr op is64
              (RelX86Gpr_public_eq (rGpr dst hd16) hBoth.1.1)
              (RelX86Gpr_public_eq (rGpr src hs16) hBoth.1.2)
              (fun hNeed => rCf (by
                by_cases hc : (op == .adc || op == .sbb) = true
                · simpa [hc] using hBoth.2
                · simp [hc] at hNeed))
          refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm,
            (fun hb => congrArg (fun t => t.2.1) (hAluEq hb)),
            (fun hOfB => by
              cases op <;> simp [evalX86AluOf] at hOfB ⊢),
            (fun hb => congrArg (fun t => t.2.2) (hAluEq hb)),
            rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
          apply RelX86Gpr_set hd16 rGpr
          by_cases hb : ((st.gpr.get dst).isPublic && (st.gpr.get src).isPublic &&
              (if op == .adc || op == .sbb then st.cfPub else true)) = true
          · simp only [hb, ↓reduceIte, RelX86Gpr]
            exact congrArg Prod.fst (hAluEq hb)
          · simp only [hb, Bool.false_eq_true, ↓reduceIte, RelX86Gpr]
    case aluLoad64 op dst addr =>
      rcases hValid with ⟨hd16, hAddrReg⟩
      cases hAddrPub : x86AddrIsPublic st addr
      · simp [hAddrPub] at hTr
      · simp only [hAddrPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hEaEq := evalX86Addr_public_eq (d.offset + d.byteLen) hAddrPub hAddrReg rGpr
        simp only [stepX86, hIns, hEaEq, true_and]
        have hAluEq : ((st.gpr.get dst).isPublic && isInPubMemRegion c st addr 8 &&
            (if op == .adc || op == .sbb then st.cfPub else true)) = true →
            evalX86Alu op true (s₁.gpr.get dst) (readMem64 s₁.mem (evalX86Addr s₂ (d.offset + d.byteLen) addr)) s₁.cf =
            evalX86Alu op true (s₂.gpr.get dst) (readMem64 s₂.mem (evalX86Addr s₂ (d.offset + d.byteLen) addr)) s₂.cf := by
          intro hBoth
          simp only [Bool.and_eq_true] at hBoth
          have hBytes := isInPubMemRegion_bytes_eq (d.offset + d.byteLen) hInit hRelFull hAddrReg hBoth.1.2
          have hMemEq : readMem64 s₁.mem (evalX86Addr s₂ (d.offset + d.byteLen) addr) =
              readMem64 s₂.mem (evalX86Addr s₂ (d.offset + d.byteLen) addr) :=
            readMem64_congr (fun j hj => by simpa only [← hEaEq] using hBytes j hj)
          exact evalX86Alu_congr op true
            (RelX86Gpr_public_eq (rGpr dst hd16) hBoth.1.1) hMemEq
            (fun hNeed => rCf (by
              by_cases hc : (op == .adc || op == .sbb) = true
              · simpa [hc] using hBoth.2
              · simp [hc] at hNeed))
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm,
          (fun hb => congrArg (fun t => t.2.1) (hAluEq hb)),
          (fun hOfB => by
            cases op <;> simp [evalX86AluOf] at hOfB ⊢),
          (fun hb => congrArg (fun t => t.2.2) (hAluEq hb)),
          rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
        apply RelX86Gpr_set hd16 rGpr
        by_cases hb : ((st.gpr.get dst).isPublic && isInPubMemRegion c st addr 8 &&
            (if op == .adc || op == .sbb then st.cfPub else true)) = true
        · simp only [hb, ↓reduceIte, RelX86Gpr]
          exact congrArg Prod.fst (hAluEq hb)
        · simp only [hb, Bool.false_eq_true, ↓reduceIte, RelX86Gpr]
    case aluImm op is64 dst imm =>
      by_cases hc1 : (is64 && op == .andOp && dst == 4 && imm == 0xFFFFFFFFFFFFFFE0 && st.gpr.get 4 == .spMinus8) = true
      · simp only [hc1, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [Bool.and_eq_true, beq_iff_eq] at hc1
        rcases hc1 with ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hSp4⟩
        have r4 := rGpr 4 (by omega); rw [hSp4] at r4; rcases r4 with ⟨h4_1, h4_2, h4eq⟩
        simp only [stepX86, hIns, evalX86Alu, evalX86AluOf, maskGprWidth, ↓reduceIte, true_and]
        exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2,
          RelX86Gpr_set (by omega) rGpr ⟨congrArg (· &&& 0xFFFFFFFFFFFFFFE0) h4_1,
            congrArg (· &&& 0xFFFFFFFFFFFFFFE0) h4_2, congrArg (· &&& 0xFFFFFFFFFFFFFFE0) h4eq⟩,
          rYmm, (fun _ => rfl), (fun _ => rfl), (fun _ => by rw [h4eq]), rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
      · simp only [hc1, Bool.false_eq_true, ↓reduceIte] at hTr
        by_cases hc2 : (is64 && op == .sub && dst == 4 && imm == 0x340 && st.gpr.get 4 == .spAligned32) = true
        · simp only [hc2, ↓reduceIte] at hTr
          injection hTr with hS; subst hS
          simp only [Bool.and_eq_true, beq_iff_eq] at hc2
          rcases hc2 with ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hSp4⟩
          have r4 := rGpr 4 (by omega); rw [hSp4] at r4; rcases r4 with ⟨h4_1, h4_2, h4eq⟩
          simp only [stepX86, hIns, evalX86Alu, maskGprWidth, ↓reduceIte, uint64_evalSub_eq, true_and]
          exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2,
            RelX86Gpr_set (by omega) rGpr ⟨by rw [x86FrameSpVal, ← h4_1], by rw [x86FrameSpVal, ← h4_2],
              congrArg (· - 0x340) h4eq⟩,
            rYmm, (fun _ => by rw [h4eq]), (fun h => nomatch h), (fun _ => by rw [h4eq]),
            rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
        · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hTr
          by_cases hc3 : (is64 && op == .add && dst == 0 && imm == 0x20 && st.stackZeroLoop == 5) = true
          · simp only [hc3, ↓reduceIte] at hTr
            injection hTr with hS; subst hS
            simp only [Bool.and_eq_true, beq_iff_eq] at hc3
            rcases hc3 with ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hLoop1⟩
            unfold RelX86Loop at rLoop
            simp only [hLoop1, show (5 == 0) = false from rfl, show (5 == 1) = false from rfl, show (5 == 2) = false from rfl, show (5 == 3) = false from rfl, show (5 == 4) = false from rfl, beq_self_eq_true, ↓reduceIte] at rLoop
            rcases rLoop with ⟨hFspEq, k, hk1, hk25, hk1_1, hk1_2, ha0_1, ha0_2, hZ⟩
            have h0eq : s₁.gpr.get 0 = s₂.gpr.get 0 := by rw [ha0_1, ha0_2, hFspEq]
            simp only [stepX86, hIns, evalX86Alu, maskGprWidth, ↓reduceIte, uint64_evalAdd_eq, true_and]
            refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2,
              RelX86Gpr_set (by omega) rGpr (congrArg (· + 0x20) h0eq),
              rYmm, (fun _ => by rw [h0eq]), (fun h => nomatch h), (fun _ => by rw [h0eq]), rDirty, rMem, rRbp, ?_⟩
            unfold RelX86Loop
            simp only [show (2 == 0) = false from rfl, show (2 == 1) = false from rfl, beq_self_eq_true, ↓reduceIte]
            have hStep32 (base : UInt64) :
                (base + UInt64.ofNat ((25 - k) * 32)) + 0x20 = base + UInt64.ofNat ((26 - k) * 32) := by
              apply uint64_eq_of_toNat_eq
              have h20 : (0x20 : UInt64).toNat = 32 := rfl
              have hMul : (25 - k) * 32 + 32 = (26 - k) * 32 := by omega
              simp only [UInt64.toNat_add, UInt64.toNat_ofNat', h20, Nat.add_mod_mod, Nat.mod_add_mod,
                Nat.add_assoc, hMul]
            refine ⟨hFspEq, k, hk1, hk25, ?_, ?_, ?_, ?_, hZ⟩
            · rw [Bank16.get_set_ne _ _ (by omega) (by omega) (by omega)]; exact hk1_1
            · rw [Bank16.get_set_ne _ _ (by omega) (by omega) (by omega)]; exact hk1_2
            · simp only [Bank16.get_set_eq, ha0_1, hStep32]
            · simp only [Bank16.get_set_eq, ha0_2, hStep32]
          · simp only [hc3, Bool.false_eq_true, ↓reduceIte] at hTr
            injection hTr with hS; subst hS
            simp only [stepX86, hIns, true_and]
            have hAluEq : ((st.gpr.get dst).isPublic &&
                (if op == .adc || op == .sbb then st.cfPub else true)) = true →
                evalX86Alu op is64 (s₁.gpr.get dst) imm s₁.cf =
                evalX86Alu op is64 (s₂.gpr.get dst) imm s₂.cf := by
              intro hBoth
              simp only [Bool.and_eq_true] at hBoth
              exact evalX86Alu_congr op is64
                (RelX86Gpr_public_eq (rGpr dst hValid) hBoth.1) rfl
                (fun hNeed => rCf (by
                  by_cases hc : (op == .adc || op == .sbb) = true
                  · simpa [hc] using hBoth.2
                  · simp [hc] at hNeed))
            refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm,
              (fun hb => congrArg (fun t => t.2.1) (hAluEq hb)),
              (fun hOfB => by
                cases op <;> simp [evalX86AluOf] at hOfB ⊢),
              (fun hb => congrArg (fun t => t.2.2) (hAluEq hb)),
              rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
            apply RelX86Gpr_set hValid rGpr
            by_cases hb : ((st.gpr.get dst).isPublic &&
                (if op == .adc || op == .sbb then st.cfPub else true)) = true
            · simp only [hb, ↓reduceIte, RelX86Gpr]
              exact congrArg Prod.fst (hAluEq hb)
            · simp only [hb, Bool.false_eq_true, ↓reduceIte, RelX86Gpr]
    case incDec isInc is64 dst =>
      by_cases hcLoop : (!isInc && !is64 && dst == 1 && st.stackZeroLoop == 2) = true
      · simp only [hcLoop, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hcLoop
        rcases hcLoop with ⟨⟨⟨rfl, rfl⟩, rfl⟩, hLoop2⟩
        unfold RelX86Loop at rLoop
        simp only [hLoop2, show (2 == 0) = false from rfl, show (2 == 1) = false from rfl,
          beq_self_eq_true, ↓reduceIte] at rLoop
        rcases rLoop with ⟨hFspEq, k, hk1, hk25, hk1_1, hk1_2, ha0_1, ha0_2, hZ⟩
        rcases loop_dec_ecx_step hk1 hk25 with ⟨hDecVal, hDecZf, hDecOf⟩
        simp only [stepX86, hIns, Bool.false_eq_true, ↓reduceIte, hk1_1, hk1_2, hDecVal, hDecOf, true_and]
        have hZfEq : (UInt64.ofNat (k - 1) == (0 : UInt64)) = (k - 1 == 0) := by
          simpa only [hDecVal] using hDecZf
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2,
          RelX86Gpr_set (by omega) rGpr rfl,
          rYmm, rCf, fun _ => rfl, fun _ => rfl, rDirty, rMem, rRbp, ?_⟩
        unfold RelX86Loop
        simp only [show (3 == 0) = false from rfl, show (3 == 1) = false from rfl,
          show (3 == 2) = false from rfl, beq_self_eq_true, ↓reduceIte]
        have hSubEq : 26 - k = 25 - (k - 1) := by omega
        refine ⟨hFspEq, k - 1, by omega,
          by simp [Bank16.get_set_eq], by simp [Bank16.get_set_eq], ?_, ?_, hZfEq, hZfEq,
          by rw [← hSubEq]; exact hZ⟩
        · rw [Bank16.get_set_ne _ _ (by omega) (by omega) (by omega), ha0_1, hSubEq]
        · rw [Bank16.get_set_ne _ _ (by omega) (by omega) (by omega), ha0_2, hSubEq]
      · simp only [hcLoop, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [stepX86, hIns, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, rCf,
          (fun hp => by rw [RelX86Gpr_public_eq (rGpr dst hValid) hp]),
          (fun hp => by rw [RelX86Gpr_public_eq (rGpr dst hValid) hp]),
          rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
        apply RelX86Gpr_set hValid rGpr
        by_cases hp : (st.gpr.get dst).isPublic = true
        · simp only [hp, ↓reduceIte, RelX86Gpr]; rw [RelX86Gpr_public_eq (rGpr dst hValid) hp]
        · simp [hp, RelX86Gpr]
    case negReg is64 dst =>
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm,
        (fun hp => by rw [RelX86Gpr_public_eq (rGpr dst hValid) hp]),
        (fun hp => by rw [RelX86Gpr_public_eq (rGpr dst hValid) hp]),
        (fun hp => by rw [RelX86Gpr_public_eq (rGpr dst hValid) hp]),
        rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
      apply RelX86Gpr_set hValid rGpr
      by_cases hp : (st.gpr.get dst).isPublic = true
      · simp only [hp, ↓reduceIte, RelX86Gpr]; rw [RelX86Gpr_public_eq (rGpr dst hValid) hp]
      · simp [hp, RelX86Gpr]
    case mulOneOp isSigned is64 src =>
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      have hBothEq : ((st.gpr.get 0).isPublic && (st.gpr.get src).isPublic) = true →
          s₁.gpr.get 0 = s₂.gpr.get 0 ∧ s₁.gpr.get src = s₂.gpr.get src := by
        intro hp; simp only [Bool.and_eq_true] at hp
        exact ⟨RelX86Gpr_public_eq (rGpr 0 (by omega)) hp.1, RelX86Gpr_public_eq (rGpr src hValid) hp.2⟩
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm,
        (fun h => nomatch h), (fun h => nomatch h), (fun h => nomatch h),
        rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
      apply RelX86Gpr_set (by omega)
      · apply RelX86Gpr_set (by omega) rGpr
        by_cases hp : ((st.gpr.get 0).isPublic && (st.gpr.get src).isPublic) = true
        · simp only [hp, ↓reduceIte, RelX86Gpr]; rcases hBothEq hp with ⟨e0, es⟩; simp [e0, es]
        · simp [hp, RelX86Gpr]
      · by_cases hp : ((st.gpr.get 0).isPublic && (st.gpr.get src).isPublic) = true
        · simp only [hp, ↓reduceIte, RelX86Gpr]; rcases hBothEq hp with ⟨e0, es⟩; simp [e0, es]
        · simp [hp, RelX86Gpr]
    case shiftImm sk is64 dst cnt =>
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm,
        (fun h => nomatch h), (fun h => nomatch h),
        (fun hp => by
          rw [evalX86Shift_zf, evalX86Shift_zf]
          by_cases hPres : x86ShiftPreservesZf sk is64 cnt = true
          · simp only [hPres, ↓reduceIte] at hp ⊢
            exact rZf hp
          · simp only [hPres, Bool.false_eq_true, ↓reduceIte] at hp ⊢
            rw [evalX86Shift_fst_congr sk is64 cnt _ _ _ _ _ _
              (RelX86Gpr_public_eq (rGpr dst hValid) hp)]),
        rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
      apply RelX86Gpr_set hValid rGpr
      by_cases hp : (st.gpr.get dst).isPublic = true
      · simp only [hp, ↓reduceIte, RelX86Gpr]
        exact evalX86Shift_fst_congr sk is64 cnt _ _ _ _ _ _
          (RelX86Gpr_public_eq (rGpr dst hValid) hp)
      · simp [hp, RelX86Gpr]
    case cmovcc cc is64 dst src =>
      rcases hValid with ⟨hd16, hs16⟩
      have hGate : ¬ ((!x86CondSupported cc || !c.doitEnabled) = true) := by
        intro hG; simp [hG] at hTr
      simp only [hGate] at hTr
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp,
        by simp [RelX86Loop]⟩
      apply RelX86Gpr_set hd16 rGpr
      by_cases hp : (x86CondIsPublic cc st && (st.gpr.get dst).isPublic && (st.gpr.get src).isPublic) = true
      · simp only [hp, ↓reduceIte, RelX86Gpr]
        simp only [Bool.and_eq_true] at hp
        rw [evalX86Cond_public_eq hp.1.1 rCf rZf,
            RelX86Gpr_public_eq (rGpr src hs16) hp.2,
            RelX86Gpr_public_eq (rGpr dst hd16) hp.1.2]
      · simp [hp, RelX86Gpr]
    case testRegReg is64 r1 r2 =>
      rcases hValid with ⟨hr1, hr2⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, rYmm,
        (fun _ => rfl), (fun _ => rfl),
        (fun hp => by
          simp only [Bool.and_eq_true] at hp
          rw [RelX86Gpr_public_eq (rGpr r1 hr1) hp.1, RelX86Gpr_public_eq (rGpr r2 hr2) hp.2]),
        rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
    case cmpRegReg is64 dst src =>
      rcases hValid with ⟨hd16, hs16⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      have hBoth : ((st.gpr.get dst).isPublic && (st.gpr.get src).isPublic) = true →
          s₁.gpr.get dst = s₂.gpr.get dst ∧ s₁.gpr.get src = s₂.gpr.get src := by
        intro hp; simp only [Bool.and_eq_true] at hp
        exact ⟨RelX86Gpr_public_eq (rGpr dst hd16) hp.1, RelX86Gpr_public_eq (rGpr src hs16) hp.2⟩
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, rYmm,
        (fun hp => by rcases hBoth hp with ⟨e1, e2⟩; rw [e1, e2]),
        (fun hp => by rcases hBoth hp with ⟨e1, e2⟩; rw [e1, e2]),
        (fun hp => by rcases hBoth hp with ⟨e1, e2⟩; rw [e1, e2]),
        rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
    case cmpImm is64 dst imm =>
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, rYmm,
        (fun hp => by rw [RelX86Gpr_public_eq (rGpr dst hValid) hp]),
        (fun hp => by rw [RelX86Gpr_public_eq (rGpr dst hValid) hp]),
        (fun hp => by rw [RelX86Gpr_public_eq (rGpr dst hValid) hp]),
        rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
    case lea is64 dst addr =>
      rcases hValid with ⟨hd16, hAddrReg⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp,
        by simp [RelX86Loop]⟩
      apply RelX86Gpr_set hd16 rGpr
      by_cases hp : x86AddrIsPublic st addr = true
      · simp only [hp, ↓reduceIte, RelX86Gpr]
        rw [evalX86Addr_public_eq (d.offset + d.byteLen) hp hAddrReg rGpr]
      · simp [hp, RelX86Gpr]
    case storeImm8 addr imm =>
      cases hAddrPub : x86AddrIsPublic st addr
      · simp [hAddrPub] at hTr
      · simp only [hAddrPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hEaEq := evalX86Addr_public_eq (d.offset + d.byteLen) hAddrPub hValid rGpr
        simp only [stepX86, hIns, hEaEq, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, rYmm, rCf, rOf, rZf, rDirty,
          (fun h => nomatch h), ?_, by simp [RelX86Loop]⟩
        intro hRbpOk
        cases hRbpB : st.rbpSaved
        · simp [hRbpB] at hRbpOk
        · simp only [hRbpB, ↓reduceIte] at hRbpOk
          rcases rRbp hRbpB with ⟨hSp0Eq, hM1, hM2⟩
          rcases storePreservesSavedRbp_disjoint (d.offset + d.byteLen) hInit hRelFull hValid hRbpOk
            with ⟨hDisj1, hDisj2⟩
          refine ⟨hSp0Eq, ?_, ?_⟩
          · rw [hEaEq] at hDisj1
            rw [readMem64_congr (fun k hk =>
              writeMem8_ne _ _ (by simpa [uint64_add_zero] using hDisj1 0 k (by omega) hk))]
            exact hM1
          · rw [readMem64_congr (fun k hk =>
              writeMem8_ne _ _ (by simpa [uint64_add_zero] using hDisj2 0 k (by omega) hk))]
            exact hM2
    case notReg is64 dst =>
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp,
        by simp [RelX86Loop]⟩
      apply RelX86Gpr_set hValid rGpr
      by_cases hp : (st.gpr.get dst).isPublic = true
      · simp only [hp, ↓reduceIte, RelX86Gpr]; rw [RelX86Gpr_public_eq (rGpr dst hValid) hp]
      · simp [hp, RelX86Gpr]
    case setcc cc dst =>
      cases hSup : x86CondSupported cc
      · simp [hSup] at hTr
      · simp only [hSup, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [stepX86, hIns, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp,
          by simp [RelX86Loop]⟩
        apply RelX86Gpr_set hValid rGpr
        by_cases hp : (x86CondIsPublic cc st && (st.gpr.get dst).isPublic) = true
        · simp only [hp, ↓reduceIte, RelX86Gpr]
          simp only [Bool.and_eq_true] at hp
          rw [evalX86Cond_public_eq hp.1 rCf rZf, RelX86Gpr_public_eq (rGpr dst hValid) hp.2]
        · simp [hp, RelX86Gpr]
    case bswap is64 dst =>
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp,
        by simp [RelX86Loop]⟩
      apply RelX86Gpr_set hValid rGpr
      by_cases hp : (st.gpr.get dst).isPublic = true
      · simp only [hp, ↓reduceIte, RelX86Gpr]; rw [RelX86Gpr_public_eq (rGpr dst hValid) hp]
      · simp [hp, RelX86Gpr]
    case sseMovdquLoad dst addr =>
      rcases hValid with ⟨hd16, hAddrReg⟩
      cases hAddrPub : x86AddrIsPublic st addr
      · simp [hAddrPub] at hTr
      · simp only [hAddrPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hEaEq := evalX86Addr_public_eq (d.offset + d.byteLen) hAddrPub hAddrReg rGpr
        simp only [stepX86, hIns, hEaEq, true_and]
        exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr,
          RelX86Vec_set hd16 rYmm trivial, rCf, rOf, rZf, rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
    case ssePcmpeqb dst src =>
      rcases hValid with ⟨hd16, _⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr,
        RelX86Vec_set hd16 rYmm trivial, rCf, rOf, rZf, rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
    case ssePand dst src =>
      rcases hValid with ⟨hd16, _⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr,
        RelX86Vec_set hd16 rYmm trivial, rCf, rOf, rZf, rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
    case ssePmovmskb dst src =>
      rcases hValid with ⟨hd16, hs16⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp,
        by simp [RelX86Loop]⟩
      apply RelX86Gpr_set hd16 rGpr
      by_cases hp : (st.ymm.get src).isPublic = true
      · simp only [hp, ↓reduceIte, RelX86Gpr]; rw [RelX86Vec_public_eq (rYmm src hs16) hp]
      · simp [hp, RelX86Gpr]
    case mulx hiDst loDst src =>
      rcases hValid with ⟨⟨hhi16, hlo16⟩, hs16⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      have hBothEq : ((st.gpr.get 2).isPublic && (st.gpr.get src).isPublic) = true →
          s₁.gpr.get 2 = s₂.gpr.get 2 ∧ s₁.gpr.get src = s₂.gpr.get src := by
        intro hp; simp only [Bool.and_eq_true] at hp
        exact ⟨RelX86Gpr_public_eq (rGpr 2 (by omega)) hp.1, RelX86Gpr_public_eq (rGpr src hs16) hp.2⟩
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp,
        by simp [RelX86Loop]⟩
      apply RelX86Gpr_set hhi16
      · apply RelX86Gpr_set hlo16 rGpr
        by_cases hp : ((st.gpr.get 2).isPublic && (st.gpr.get src).isPublic) = true
        · simp only [hp, ↓reduceIte, RelX86Gpr]; rcases hBothEq hp with ⟨e2, es⟩; simp [e2, es]
        · simp [hp, RelX86Gpr]
      · by_cases hp : ((st.gpr.get 2).isPublic && (st.gpr.get src).isPublic) = true
        · simp only [hp, ↓reduceIte, RelX86Gpr]; rcases hBothEq hp with ⟨e2, es⟩; simp [e2, es]
        · simp [hp, RelX86Gpr]
    case adcx dst src =>
      rcases hValid with ⟨hd16, hs16⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      have hEq : ((st.gpr.get dst).isPublic && (st.gpr.get src).isPublic && st.cfPub) = true →
          s₁.gpr.get dst = s₂.gpr.get dst ∧ s₁.gpr.get src = s₂.gpr.get src ∧ s₁.cf = s₂.cf := by
        intro hp; simp only [Bool.and_eq_true] at hp
        exact ⟨RelX86Gpr_public_eq (rGpr dst hd16) hp.1.1,
               RelX86Gpr_public_eq (rGpr src hs16) hp.1.2, rCf hp.2⟩
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm,
        (fun hp => by rcases hEq hp with ⟨ed, es, ec⟩; simp [ed, es, ec]),
        rOf, rZf, rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
      apply RelX86Gpr_set hd16 rGpr
      by_cases hp : ((st.gpr.get dst).isPublic && (st.gpr.get src).isPublic && st.cfPub) = true
      · simp only [hp, ↓reduceIte, RelX86Gpr]; rcases hEq hp with ⟨ed, es, ec⟩; simp [ed, es, ec]
      · simp [hp, RelX86Gpr]
    case adox dst src =>
      rcases hValid with ⟨hd16, hs16⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      have hEq : ((st.gpr.get dst).isPublic && (st.gpr.get src).isPublic && st.ofPub) = true →
          s₁.gpr.get dst = s₂.gpr.get dst ∧ s₁.gpr.get src = s₂.gpr.get src ∧ s₁.ofFlag = s₂.ofFlag := by
        intro hp; simp only [Bool.and_eq_true] at hp
        exact ⟨RelX86Gpr_public_eq (rGpr dst hd16) hp.1.1,
               RelX86Gpr_public_eq (rGpr src hs16) hp.1.2, rOf hp.2⟩
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, ?_, rYmm, rCf,
        (fun hp => by rcases hEq hp with ⟨ed, es, eo⟩; simp [ed, es, eo]),
        rZf, rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
      apply RelX86Gpr_set hd16 rGpr
      by_cases hp : ((st.gpr.get dst).isPublic && (st.gpr.get src).isPublic && st.ofPub) = true
      · simp only [hp, ↓reduceIte, RelX86Gpr]; rcases hEq hp with ⟨ed, es, eo⟩; simp [ed, es, eo]
      · simp [hp, RelX86Gpr]
    case jcc cc targetPc =>
      by_cases hBad : (!x86CondIsPublic cc st || decide (targetPc < 0) || decide (targetPc.toNat ≥ 8192)) = true
      · simp [hBad] at hTr
      · simp only [hBad, Bool.false_eq_true, ↓reduceIte] at hTr
        simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, not_or, Bool.not_eq_false] at hBad
        rcases hBad with ⟨⟨hCondPub, hNotNeg⟩, _⟩
        have hGe0 : targetPc ≥ 0 := by omega
        have hCondEq := evalX86Cond_public_eq hCondPub rCf rZf
        by_cases hLoop3 : (st.stackZeroLoop == 3 && cc == 5) = true
        · simp only [hLoop3, ↓reduceIte] at hTr
          injection hTr with hS; subst hS
          simp only [Bool.and_eq_true, beq_iff_eq] at hLoop3
          rcases hLoop3 with ⟨hSt3, rfl⟩
          unfold RelX86Loop at rLoop
          simp only [hSt3, show (3 == 0) = false from rfl, show (3 == 1) = false from rfl,
            show (3 == 2) = false from rfl, beq_self_eq_true, ↓reduceIte] at rLoop
          rcases rLoop with ⟨hFspEq, k', hk'24, hk1, hk2, ha1, ha2, hzf1, hzf2, hZ⟩
          simp only [stepX86, hIns, decide_eq_true hGe0, Bool.and_true, true_and]
          by_cases hTaken : evalX86Cond 5 s₁ = true
          · have hTaken2 : evalX86Cond 5 s₂ = true := hCondEq ▸ hTaken
            simp only [hTaken, hTaken2, ↓reduceIte]
            have hk'Pos : 1 ≤ k' := by
              unfold evalX86Cond at hTaken
              simp only [show (5 == 2) = false from rfl, show (5 == 3) = false from rfl,
                show (5 == 4) = false from rfl, Bool.false_eq_true, beq_self_eq_true, ↓reduceIte, hzf1,
                Bool.not_eq_true', beq_eq_false_iff_ne] at hTaken
              omega
            refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp, ?_⟩
            unfold RelX86Loop
            simp only [show (1 == 0) = false from rfl, beq_self_eq_true, ↓reduceIte]
            exact ⟨hFspEq, k', hk'Pos, by omega, hk1, hk2, ha1, ha2, hZ⟩
          · have hTakenF1 : evalX86Cond 5 s₁ = false := Bool.eq_false_iff.mpr hTaken
            have hTakenF2 : evalX86Cond 5 s₂ = false := hCondEq ▸ hTakenF1
            have hk'Z : k' = 0 := by
              by_cases h0 : k' = 0
              · exact h0
              · exact absurd (by simp [evalX86Cond, hzf1, h0]) hTaken
            simp only [hTakenF1, hTakenF2, Bool.false_eq_true, ↓reduceIte]
            refine Or.inr ⟨_, List.Mem.tail _ (List.Mem.head _), rfl, hH1, hH2, rGpr, rYmm, rCf, rOf, rZf,
              rDirty, rMem, rRbp, ?_⟩
            unfold RelX86Loop
            simp only [show (4 == 0) = false from rfl, show (4 == 1) = false from rfl, show (4 == 2) = false from rfl, show (4 == 3) = false from rfl, beq_self_eq_true, ↓reduceIte]
            intro j hj
            exact hZ j (by omega)
        · simp only [hLoop3, Bool.false_eq_true, ↓reduceIte] at hTr
          injection hTr with hS; subst hS
          simp only [stepX86, hIns, decide_eq_true hGe0, Bool.and_true, true_and]
          by_cases hTaken : evalX86Cond cc s₁ = true
          · have hTaken2 : evalX86Cond cc s₂ = true := hCondEq ▸ hTaken
            simp only [hTaken, hTaken2, ↓reduceIte]
            exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp,
              by simp [RelX86Loop]⟩
          · have hTakenF1 : evalX86Cond cc s₁ = false := Bool.eq_false_iff.mpr hTaken
            have hTakenF2 : evalX86Cond cc s₂ = false := hCondEq ▸ hTakenF1
            simp only [hTakenF1, hTakenF2, Bool.false_eq_true, ↓reduceIte]
            exact Or.inr ⟨_, List.Mem.tail _ (List.Mem.head _), rfl, hH1, hH2, rGpr, rYmm, rCf, rOf, rZf,
              rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
    case jmpRel targetPc =>
      by_cases hBad : (decide (targetPc < 0) || decide (targetPc.toNat ≥ 8192)) = true
      · simp [hBad] at hTr
      · simp only [hBad, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hBad
        have hGe0 : targetPc ≥ 0 := by omega
        simp only [stepX86, hIns, hGe0, ↓reduceIte, true_and]
        exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, rYmm, rCf, rOf, rZf, rDirty, rMem, rRbp,
          by simp [RelX86Loop]⟩
    case indirectBr _ => cases hTr
    case divRem _ => cases hTr
    case varShiftCl _ _ => cases hTr
    case vpgather _ _ => cases hTr
    case vzeroall =>
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, ?_, rCf, rOf, rZf,
        fun _ => ⟨rfl, rfl⟩, rMem, rRbp, RelX86Loop_keep4 rLoop rfl rfl⟩
      intro i hi
      rw [Bank16.get_ofFn _ hi, Bank16.get_ofFn _ hi]
      exact ⟨rfl, rfl⟩
    case vzeroupper =>
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, ?_, rCf, rOf, rZf,
        fun _ => ⟨rfl, rfl⟩, rMem, rRbp, RelX86Loop_keep4 rLoop rfl rfl⟩
      intro i hi
      rw [Bank16.get_ofFn _ hi, Bank16.get_ofFn _ hi, Bank16.get_ofFn _ hi]
      have rv := rYmm i hi
      cases hVo : st.ymm.get i <;> rw [hVo] at rv
      · rcases rv with ⟨hr, (⟨e1, e2⟩ | ⟨e1, e2⟩)⟩
        · exact ⟨hr, Or.inr ⟨by rw [e1], by rw [e2]⟩⟩
        · exact ⟨hr, Or.inr ⟨by rw [e1], by rw [e2]⟩⟩
      · rcases rv with ⟨e1, e2⟩
        simp [e1, e2, Vec256.zero, RelX86Vec]
      · simp only [RelX86Vec] at rv ⊢; rw [rv]
      · trivial
    case vload is256 dst addr =>
      rcases hValid with ⟨hd16, hAddrReg⟩
      cases hAddrPub : x86AddrIsPublic st addr
      · simp [hAddrPub] at hTr
      · simp only [hAddrPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hEaEq := evalX86Addr_public_eq (d.offset + d.byteLen) hAddrPub hAddrReg rGpr
        simp only [stepX86, hIns, hEaEq, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, ?_, rCf, rOf, rZf, ?_, rMem, rRbp,
          by simp [RelX86Loop]⟩
        · apply RelX86Vec_set hd16 rYmm
          by_cases hIn : isInPubMemRegion c st addr (if is256 then 32 else 16) = true
          · simp only [hIn, ↓reduceIte, RelX86Vec]
            have hBytes := isInPubMemRegion_bytes_eq (d.offset + d.byteLen) hInit hRelFull hAddrReg hIn
            cases is256
            · simp only [Bool.false_eq_true, ↓reduceIte] at hBytes ⊢
              rw [readMem128_congr (fun j hj => by simpa only [← hEaEq] using hBytes j hj)]
            · simp only [↓reduceIte] at hBytes ⊢
              exact readMem256_congr (fun j hj => by simpa only [← hEaEq] using hBytes j hj)
          · simp [hIn, RelX86Vec]
        · intro hClean
          simp only [Bool.or_eq_false_iff] at hClean
          rcases rDirty hClean.1 with ⟨d1, d2⟩
          simp [d1, d2, hClean.2]
    case vstore is256 src addr =>
      rcases hValid with ⟨hs16, hAddrReg⟩
      cases hAddrPub : x86AddrIsPublic st addr
      · simp [hAddrPub] at hTr
      · simp only [hAddrPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hEaEq := evalX86Addr_public_eq (d.offset + d.byteLen) hAddrPub hAddrReg rGpr
        simp only [stepX86, hIns, hEaEq, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, rYmm, rCf, rOf, rZf, rDirty,
          (fun h => nomatch h), ?_, ?_⟩
        · intro hRbpOk
          cases hRbpB : st.rbpSaved
          · simp [hRbpB] at hRbpOk
          · simp only [hRbpB, ↓reduceIte] at hRbpOk
            rcases rRbp hRbpB with ⟨hSp0Eq, hM1, hM2⟩
            rcases storePreservesSavedRbp_disjoint (d.offset + d.byteLen) hInit hRelFull hAddrReg hRbpOk
              with ⟨hDisj1, hDisj2⟩
            refine ⟨hSp0Eq, ?_, ?_⟩
            · rw [hEaEq] at hDisj1
              cases is256
              · simp only [Bool.false_eq_true, ↓reduceIte] at hDisj1 ⊢
                rw [readMem64_congr (fun k hk => writeMem128_ne _ _ (fun j hj => hDisj1 j k hj hk))]
                exact hM1
              · simp only [↓reduceIte] at hDisj1 ⊢
                rw [readMem64_congr (fun k hk => writeMem256_ne _ _ (fun j hj => hDisj1 j k hj hk))]
                exact hM1
            · cases is256
              · simp only [Bool.false_eq_true, ↓reduceIte] at hDisj2 ⊢
                rw [readMem64_congr (fun k hk => writeMem128_ne _ _ (fun j hj => hDisj2 j k hj hk))]
                exact hM2
              · simp only [↓reduceIte] at hDisj2 ⊢
                rw [readMem64_congr (fun k hk => writeMem256_ne _ _ (fun j hj => hDisj2 j k hj hk))]
                exact hM2
        · by_cases hKeepLoop : (st.stackZeroLoop == 1 && addr == .baseDisp 0 0 && is256 &&
              st.ymm.get src == .zeroConst) = true
          · simp only [hKeepLoop, ↓reduceIte]
            simp only [Bool.and_eq_true, beq_iff_eq] at hKeepLoop
            rcases hKeepLoop with ⟨⟨⟨hL1, rfl⟩, rfl⟩, hSrcZ⟩
            have rv := rYmm src hs16
            rw [hSrcZ] at rv
            rcases rv with ⟨hv1, hv2⟩
            unfold RelX86Loop at rLoop ⊢
            simp only [hL1, show (1 == 0) = false from rfl, beq_self_eq_true, ↓reduceIte] at rLoop
            simp only [show (5 == 0) = false from rfl, show (5 == 1) = false from rfl, show (5 == 2) = false from rfl, show (5 == 3) = false from rfl, show (5 == 4) = false from rfl, beq_self_eq_true, ↓reduceIte]
            rcases rLoop with ⟨hFspEq, k, hk1, hk25, hc1, hc2, ha1, ha2, hZ⟩
            have hEa2 (n : Nat) : evalX86Addr s₂ n (.baseDisp 0 0) =
                x86FrameSpVal (s₂₀.gpr.get 4) + UInt64.ofNat ((25 - k) * 32) := by
              show s₂.gpr.get 0 + 0 = _
              rw [UInt64.add_zero, ha2]
            refine ⟨hFspEq, k, hk1, hk25, hc1, hc2, ha1, ha2, ?_⟩
            intro j hj
            refine ⟨?_, ?_⟩
            · show writeMem256 s₁.mem (evalX86Addr s₂ _ (.baseDisp 0 0)) (s₁.ymm.get src)
                (x86FrameSpVal (s₁₀.gpr.get 4) + UInt64.ofNat j) = 0
              rw [hEa2, hv1, ← hFspEq]
              exact frame_store_zero_step k s₁.mem _ (fun j hj => (hZ j hj).1) j hj hk25
            · show writeMem256 s₂.mem (evalX86Addr s₂ _ (.baseDisp 0 0)) (s₂.ymm.get src)
                (x86FrameSpVal (s₂₀.gpr.get 4) + UInt64.ofNat j) = 0
              rw [hEa2, hv2]
              exact frame_store_zero_step k s₂.mem _ (fun j hj => (hZ j hj).2) j hj hk25
          · simp [hKeepLoop, RelX86Loop]
    case vmovGprToXmm is64 dstVec srcGpr =>
      rcases hValid with ⟨hd16, hs16⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, ?_, rCf, rOf, rZf, rDirty, rMem, rRbp,
        by simp [RelX86Loop]⟩
      apply RelX86Vec_set hd16 rYmm
      by_cases hz : (st.gpr.get srcGpr == .zeroConst) = true
      · simp only [hz, ↓reduceIte, RelX86Vec]
        have rs := rGpr srcGpr hs16
        rw [beq_iff_eq.mp hz] at rs
        rcases rs with ⟨r1, r2⟩
        have hm0 : maskGprWidth is64 0 = 0 := by cases is64 <;> rfl
        simp [r1, r2, hm0, Vec256.zero]
      · simp only [hz, Bool.false_eq_true, ↓reduceIte]
        by_cases hp : (st.gpr.get srcGpr).isPublic = true
        · simp only [hp, ↓reduceIte, RelX86Vec]
          rw [RelX86Gpr_public_eq (rGpr srcGpr hs16) hp]
        · simp [hp, RelX86Vec]
    case vpbroadcast isQword is256 dst srcVec =>
      rcases hValid with ⟨hd16, hs16⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, ?_, rCf, rOf, rZf,
        ?_, rMem, rRbp, by simp [RelX86Loop]⟩
      · apply RelX86Vec_set hd16 rYmm
        by_cases hz : (st.ymm.get srcVec == .zeroConst) = true
        · simp only [hz, ↓reduceIte, RelX86Vec]
          have rv := rYmm srcVec hs16
          rw [beq_iff_eq.mp hz] at rv
          rcases rv with ⟨r1, r2⟩
          have hmb0 : mapBytes64 (fun _ => 0) = 0 := by decide
          cases isQword <;> cases is256 <;> simp [r1, r2, Vec256.zero, hmb0, clampVecWidth]
        · simp only [hz, Bool.false_eq_true, ↓reduceIte]
          by_cases hp : (st.ymm.get srcVec).isPublic = true
          · simp only [hp, ↓reduceIte, RelX86Vec]
            rw [RelX86Vec_public_eq (rYmm srcVec hs16) hp]
          · simp [hp, RelX86Vec]
      · intro hClean
        simp only [Bool.or_eq_false_iff] at hClean
        rcases rDirty hClean.1 with ⟨d1, d2⟩
        simp [d1, d2, hClean.2]
    case vpbroadcastLoad64 dst addr =>
      rcases hValid with ⟨hd16, hAddrReg⟩
      cases hAddrPub : x86AddrIsPublic st addr
      · simp [hAddrPub] at hTr
      · simp only [hAddrPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hEaEq := evalX86Addr_public_eq (d.offset + d.byteLen) hAddrPub hAddrReg rGpr
        simp only [stepX86, hIns, hEaEq, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, ?_, rCf, rOf, rZf,
          (fun h => nomatch h), rMem, rRbp, by simp [RelX86Loop]⟩
        apply RelX86Vec_set hd16 rYmm
        by_cases hIn : isInPubMemRegion c st addr 8 = true
        · simp only [hIn, ↓reduceIte, RelX86Vec]
          have hBytes := isInPubMemRegion_bytes_eq (d.offset + d.byteLen) hInit hRelFull hAddrReg hIn
          rw [readMem64_congr (fun j hj => by simpa only [← hEaEq] using hBytes j hj)]
        · simp [hIn, RelX86Vec]
    case vbinOp op is256 dst src1 src2 =>
      rcases hValid with ⟨⟨hd16, hs1⟩, hs2⟩
      by_cases hSelf : (op == .vpxor && src1 == src2) = true
      · simp only [hSelf, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [Bool.and_eq_true, beq_iff_eq] at hSelf
        rcases hSelf with ⟨rfl, rfl⟩
        have hXorZ (v : Vec256) : clampVecWidth is256 (evalVecBin256 .vpxor v v) = Vec256.zero := by
          have hx (w : UInt64) : w ^^^ w = 0 := by apply UInt64.eq_of_toBitVec_eq; simp
          cases is256 <;> simp [evalVecBin256, clampVecWidth, Vec256.zero, hx]
        simp only [stepX86, hIns, hXorZ, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr,
          RelX86Vec_set hd16 rYmm ⟨rfl, rfl⟩,
          rCf, rOf, rZf, ?_, rMem, rRbp, RelX86Loop_keep4 rLoop rfl rfl⟩
        intro hClean
        simp only [Bool.or_eq_false_iff] at hClean
        rcases rDirty hClean.1 with ⟨d1, d2⟩
        simp [d1, d2, hClean.2]
      · simp only [hSelf, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [stepX86, hIns, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, ?_, rCf, rOf, rZf, ?_, rMem, rRbp,
          RelX86Loop_keep4 rLoop rfl rfl⟩
        · apply RelX86Vec_set hd16 rYmm
          by_cases hp : ((st.ymm.get src1).isPublic && (st.ymm.get src2).isPublic) = true
          · simp only [hp, ↓reduceIte, RelX86Vec]
            simp only [Bool.and_eq_true] at hp
            rw [RelX86Vec_public_eq (rYmm src1 hs1) hp.1, RelX86Vec_public_eq (rYmm src2 hs2) hp.2]
          · simp [hp, RelX86Vec]
        · intro hClean
          simp only [Bool.or_eq_false_iff] at hClean
          rcases rDirty hClean.1 with ⟨d1, d2⟩
          simp [d1, d2, hClean.2]
    case vpxorLoad128 dst src1 addr =>
      rcases hValid with ⟨⟨hd16, hs1⟩, hAddrReg⟩
      cases hAddrPub : x86AddrIsPublic st addr
      · simp [hAddrPub] at hTr
      · simp only [hAddrPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hEaEq := evalX86Addr_public_eq (d.offset + d.byteLen) hAddrPub hAddrReg rGpr
        simp only [stepX86, hIns, hEaEq, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, ?_, rCf, rOf, rZf,
          rDirty, rMem, rRbp, by simp [RelX86Loop]⟩
        apply RelX86Vec_set hd16 rYmm
        by_cases hp : ((st.ymm.get src1).isPublic && isInPubMemRegion c st addr 16) = true
        · simp only [hp, ↓reduceIte, RelX86Vec]
          simp only [Bool.and_eq_true] at hp
          have hBytes := isInPubMemRegion_bytes_eq (d.offset + d.byteLen) hInit hRelFull hAddrReg hp.2
          rw [RelX86Vec_public_eq (rYmm src1 hs1) hp.1,
              readMem128_congr (fun j hj => by simpa only [← hEaEq] using hBytes j hj)]
        · simp [hp, RelX86Vec]
    case vpxorLoad256 dst src1 addr =>
      rcases hValid with ⟨⟨hd16, hs1⟩, hAddrReg⟩
      cases hAddrPub : x86AddrIsPublic st addr
      · simp [hAddrPub] at hTr
      · simp only [hAddrPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hEaEq := evalX86Addr_public_eq (d.offset + d.byteLen) hAddrPub hAddrReg rGpr
        simp only [stepX86, hIns, hEaEq, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, ?_, rCf, rOf, rZf,
          (fun h => nomatch h), rMem, rRbp, by simp [RelX86Loop]⟩
        apply RelX86Vec_set hd16 rYmm
        by_cases hp : ((st.ymm.get src1).isPublic && isInPubMemRegion c st addr 32) = true
        · simp only [hp, ↓reduceIte, RelX86Vec]
          simp only [Bool.and_eq_true] at hp
          have hBytes := isInPubMemRegion_bytes_eq (d.offset + d.byteLen) hInit hRelFull hAddrReg hp.2
          rw [RelX86Vec_public_eq (rYmm src1 hs1) hp.1,
              readMem256_congr (fun j hj => by simpa only [← hEaEq] using hBytes j hj)]
        · simp [hp, RelX86Vec]
    case vshiftImm sk is256 dst src imm =>
      rcases hValid with ⟨hd16, hs16⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, ?_, rCf, rOf, rZf, ?_, rMem, rRbp,
        by simp [RelX86Loop]⟩
      · apply RelX86Vec_set hd16 rYmm
        by_cases hz : (st.ymm.get src == .zeroConst) = true
        · simp only [hz, ↓reduceIte, RelX86Vec]
          have rv := rYmm src hs16
          rw [beq_iff_eq.mp hz] at rv
          rcases rv with ⟨r1, r2⟩
          rw [r1, r2, evalVecShift256_zero]
          exact ⟨rfl, rfl⟩
        · simp only [hz, Bool.false_eq_true, ↓reduceIte]
          by_cases hp : (st.ymm.get src).isPublic = true
          · simp only [hp, ↓reduceIte, RelX86Vec]
            rw [RelX86Vec_public_eq (rYmm src hs16) hp]
          · simp [hp, RelX86Vec]
      · intro hClean
        simp only [Bool.or_eq_false_iff] at hClean
        rcases rDirty hClean.1 with ⟨d1, d2⟩
        simp [d1, d2, hClean.2]
    case vpclmulqdq is256 dst src1 src2 imm =>
      rcases hValid with ⟨⟨hd16, hs1⟩, hs2⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, ?_, rCf, rOf, rZf, ?_, rMem, rRbp,
        by simp [RelX86Loop]⟩
      · apply RelX86Vec_set hd16 rYmm
        by_cases hp : ((st.ymm.get src1).isPublic && (st.ymm.get src2).isPublic) = true
        · simp only [hp, ↓reduceIte, RelX86Vec]
          simp only [Bool.and_eq_true] at hp
          rw [RelX86Vec_public_eq (rYmm src1 hs1) hp.1, RelX86Vec_public_eq (rYmm src2 hs2) hp.2]
        · simp [hp, RelX86Vec]
      · intro hClean
        simp only [Bool.or_eq_false_iff] at hClean
        rcases rDirty hClean.1 with ⟨d1, d2⟩
        simp [d1, d2, hClean.2]
    case vgf2p8affineqb is256 dst src1 src2 imm =>
      rcases hValid with ⟨⟨hd16, hs1⟩, hs2⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, ?_, rCf, rOf, rZf, ?_, rMem, rRbp,
        by simp [RelX86Loop]⟩
      · apply RelX86Vec_set hd16 rYmm
        by_cases hp : ((st.ymm.get src1).isPublic && (st.ymm.get src2).isPublic) = true
        · simp only [hp, ↓reduceIte, RelX86Vec]
          simp only [Bool.and_eq_true] at hp
          rw [RelX86Vec_public_eq (rYmm src1 hs1) hp.1, RelX86Vec_public_eq (rYmm src2 hs2) hp.2]
        · simp [hp, RelX86Vec]
      · intro hClean
        simp only [Bool.or_eq_false_iff] at hClean
        rcases rDirty hClean.1 with ⟨d1, d2⟩
        simp [d1, d2, hClean.2]
    case vperm2i128 dst src1 src2 imm =>
      rcases hValid with ⟨⟨hd16, hs1⟩, hs2⟩
      injection hTr with hS; subst hS
      simp only [stepX86, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rGpr, ?_, rCf, rOf, rZf,
        (fun h => nomatch h), rMem, rRbp, by simp [RelX86Loop]⟩
      apply RelX86Vec_set hd16 rYmm
      by_cases hp : ((st.ymm.get src1).isPublic && (st.ymm.get src2).isPublic) = true
      · simp only [hp, ↓reduceIte, RelX86Vec]
        simp only [Bool.and_eq_true] at hp
        rw [RelX86Vec_public_eq (rYmm src1 hs1) hp.1, RelX86Vec_public_eq (rYmm src2 hs2) hp.2]
      · simp [hp, RelX86Vec]

private theorem runX86_of_halted (prog : List (DecodedInstr X86Instr)) (fuel : Nat)
    {s : X86State} (hHalt : s.halted = true) :
    runX86 prog fuel s = (s, []) := by
  cases fuel with
  | zero => rfl
  | succ k => simp [runX86, hHalt]

private theorem runX86_invariant_sound {c : FuncContract}
    {prog : List (DecodedInstr X86Instr)} {inv : PcMap X86AbsState}
    {s₁₀ s₂₀ : X86State}
    (hInit : X86ContractInit c s₁₀ s₂₀)
    (hAll : inv.all (fun pc st =>
      match (buildProgMap prog).get pc with
      | none => false
      | some d =>
        match transferX86Instr c d st with
        | none => false
        | some succs =>
          succs.all (fun (npc, nst) =>
            match inv.get npc with
            | none => false
            | some dstSt => nst.le dstSt)) = true) :
    ∀ (fuel : Nat) {s₁ s₂ : X86State} {st : X86AbsState},
      inv.get s₁.pc = some st →
      RelX86 s₁₀ s₂₀ st s₁ s₂ →
      let (s₁f, tr₁) := runX86 prog fuel s₁
      let (s₂f, tr₂) := runX86 prog fuel s₂
      tr₁ = tr₂ ∧
      (∀ obs ∈ tr₁, obs.isDoitSafe = true) ∧
      ((s₁f.halted = true ∧ s₂f.halted = true ∧ X86ExitHygiene c s₁₀ s₂₀ s₁f s₂f) ∨
       (s₁f.halted = false ∧ s₂f.halted = false))
  | 0, s₁, s₂, st, _, hRel =>
    ⟨rfl, (fun _ h => nomatch h), Or.inr ⟨hRel.2.1, hRel.2.2.1⟩⟩
  | fuel + 1, s₁, s₂, st, hInvPc, hRel => by
    have hPcLt : s₁.pc < 8192 := PcMap.get_some_lt hInvPc
    have hPred := PcMap.all_get hAll hInvPc
    rw [buildProgMap_get_eq prog hPcLt] at hPred
    cases hFind : findInstrAtPc s₁.pc prog with
    | none => simp [hFind] at hPred
    | some d =>
      simp only [hFind] at hPred
      cases hTr : transferX86Instr c d st with
      | none => simp [hTr] at hPred
      | some succs =>
        simp only [hTr, List.all_eq_true] at hPred
        have hFind2 : findInstrAtPc s₂.pc prog = some d := hRel.1 ▸ hFind
        have hOffEq : s₁.pc = d.offset := (findInstrAtPc_offset hFind).symm
        have hStep := transferX86Instr_step_sound hInit hRel hOffEq hTr
        rcases stp1 : stepX86 d s₁ with ⟨s₁', obs₁⟩
        rcases stp2 : stepX86 d s₂ with ⟨s₂', obs₂⟩
        simp only [stp1, stp2] at hStep
        rcases hStep with ⟨hObsEq, hDoit, hExitOrCont⟩
        simp only [runX86, hRel.2.1, hRel.2.2.1, Bool.false_eq_true, ↓reduceIte, hFind, hFind2, stp1, stp2]
        rcases hExitOrCont with ⟨hh1', hh2', hHyg⟩ | ⟨nst, hMemSucc, hRel'⟩
        · rw [runX86_of_halted prog fuel hh1', runX86_of_halted prog fuel hh2']
          refine ⟨congrArg (· :: []) hObsEq, ?_, Or.inl ⟨hh1', hh2', hHyg⟩⟩
          intro o ho; simp at ho; subst ho; exact hDoit
        · have hSuccOk := hPred (s₁'.pc, nst) hMemSucc
          cases hInvNext : inv.get s₁'.pc with
          | none => simp [hInvNext] at hSuccOk
          | some dstSt =>
            simp only [hInvNext] at hSuccOk
            have hRelDst := RelX86_mono hRel' hSuccOk
            have ih := runX86_invariant_sound hInit hAll fuel hInvNext hRelDst
            rcases hr1 : runX86 prog fuel s₁' with ⟨s₁f, tr₁⟩
            rcases hr2 : runX86 prog fuel s₂' with ⟨s₂f, tr₂⟩
            simp only [hr1, hr2] at ih
            rcases ih with ⟨hTrEq, hTrDoit, hPost⟩
            refine ⟨by rw [hObsEq, hTrEq], ?_, hPost⟩
            intro o ho
            rcases List.mem_cons.mp ho with rfl | hRest
            · exact hDoit
            · exact hTrDoit o hRest

/-- **3-Way Hardware Constant-Time Noninterference + System V ABI Hygiene Soundness (`x86_64`):**
    Whenever `checkX86ThreeWayNI code c = true`, for ANY two initial machine states `(s₁, s₂)`
    satisfying `X86ContractInit c s₁ s₂` (with arbitrary secret memory & secret registers) and
    ANY execution fuel `fuel`:
    1. **`PC-NI` & `Mem-NI`:** `tr₁ = tr₂` (every executed PC and `(addr, width)` memory access matches),
    2. **`DOIT-NI`:** Every executed instruction has `obs.isDoitSafe = true`. For `cmovcc` this
       flag means "data-operand-independent when `DOITM` is set": `X86State` carries no `DOITM`
       bit, and the checker accepts `cmovcc` only under a contract with `c.doitEnabled = true`
       (`tooth_x86_cmovcc_rejected_without_doit`). The guarantee for such a stream is therefore
       conditional on the processor running it in that mode,
    3. **`ABI & Epilogue Zeroization`:** If execution halts (`ret`), both states halt together and
       satisfy `X86ExitHygiene c s₁ s₂ s₁f s₂f` (`rsp` & `rbx, rbp, r12..r15` preserved,
       `ymmDirty = false` via `vzeroupper`, scratch `ymm` secrets wiped, scratch GPRs wiped). -/
theorem checkX86ThreeWayNI_sound {code : List UInt8} {c : FuncContract}
    (hCheck : checkX86ThreeWayNI code c = true)
    {s₁ s₂ : X86State} (hInit : X86ContractInit c s₁ s₂) (fuel : Nat) :
    ∃ prog : List (DecodedInstr X86Instr),
      decodeX86Stream code = some prog ∧
      let (s₁f, tr₁) := runX86 prog fuel s₁
      let (s₂f, tr₂) := runX86 prog fuel s₂
      tr₁ = tr₂ ∧
      (∀ obs ∈ tr₁, obs.isDoitSafe = true) ∧
      ((s₁f.halted = true ∧ s₂f.halted = true ∧ X86ExitHygiene c s₁ s₂ s₁f s₂f) ∨
       (s₁f.halted = false ∧ s₂f.halted = false)) := by
  unfold checkX86ThreeWayNI at hCheck
  cases hDec : decodeX86Stream code with
  | none => simp [hDec] at hCheck
  | some prog =>
    simp only [hDec] at hCheck
    cases prog with
    | nil => simp at hCheck
    | cons d0 ds =>
      cases hInf : inferX86Invariant (d0 :: ds) c with
      | none => simp [hInf] at hCheck
      | some inv =>
        simp only [hInf, verifyX86Invariant, Bool.and_eq_true] at hCheck
        rcases hCheck with ⟨hEntry, hAll⟩
        cases hInv0 : inv.get 0 with
        | none => simp [hInv0] at hEntry
        | some st0 =>
          simp only [hInv0] at hEntry
          have hRel0 := RelX86_mono (RelX86_init hInit) hEntry
          have hInvS1 : inv.get s₁.pc = some st0 := hInit.1 ▸ hInv0
          exact ⟨d0 :: ds, rfl, runX86_invariant_sound hInit hAll fuel hInvS1 hRel0⟩


/-! #### Inductive Relational Invariant & Step Soundness for `AArch64` -/

private def RelArmGpr (s₁₀ s₂₀ : Arm64State) (orig : ArmRegOrigin) (v₁ v₂ : UInt64) : Prop :=
  match orig with
  | .initSame r => r < 31 ∧ v₁ = s₁₀.gpr.get r ∧ v₂ = s₂₀.gpr.get r ∧ v₁ = v₂
  | .initOwn r => r < 31 ∧ v₁ = s₁₀.gpr.get r ∧ v₂ = s₂₀.gpr.get r
  | .zeroConst => v₁ = 0 ∧ v₂ = 0
  | .pubVal => v₁ = v₂
  | .secretVal => True

private theorem RelArmGpr_public_eq {s₁₀ s₂₀ : Arm64State} {orig : ArmRegOrigin} {v₁ v₂ : UInt64}
    (hRel : RelArmGpr s₁₀ s₂₀ orig v₁ v₂) (hPub : orig.isPublic = true) :
    v₁ = v₂ := by
  cases orig with
  | initSame _ => exact hRel.2.2.2
  | initOwn _ => cases hPub
  | zeroConst => exact hRel.1.trans hRel.2.symm
  | pubVal => exact hRel
  | secretVal => cases hPub

private theorem RelArmGpr_mono {s₁₀ s₂₀ : Arm64State} {a b : ArmRegOrigin} {v₁ v₂ : UInt64}
    (hRel : RelArmGpr s₁₀ s₂₀ a v₁ v₂) (hle : a.le b = true) :
    RelArmGpr s₁₀ s₂₀ b v₁ v₂ := by
  unfold ArmRegOrigin.le at hle
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hle
  rcases hle with (rfl | rfl) | ⟨rfl, hPub⟩
  · exact hRel
  · trivial
  · exact RelArmGpr_public_eq hRel hPub

private def RelArmVec (s₁₀ s₂₀ : Arm64State) (vo : VecOrigin) (v₁ v₂ : Vec128) : Prop :=
  match vo with
  | .initVec r => r < 32 ∧ v₁ = s₁₀.vec.get r ∧ v₂ = s₂₀.vec.get r
  | .zeroConst => v₁ = Vec128.zero ∧ v₂ = Vec128.zero
  | .pubVal => v₁ = v₂
  | .secretVal => True

private theorem RelArmVec_public_eq {s₁₀ s₂₀ : Arm64State} {vo : VecOrigin} {v₁ v₂ : Vec128}
    (hRel : RelArmVec s₁₀ s₂₀ vo v₁ v₂) (hPub : vo.isPublic = true) :
    v₁ = v₂ := by
  cases vo <;> simp [VecOrigin.isPublic, RelArmVec] at hPub hRel
  · rw [hRel.1, hRel.2]
  · exact hRel

private theorem RelArmVec_mono {s₁₀ s₂₀ : Arm64State} {a b : VecOrigin} {v₁ v₂ : Vec128}
    (hRel : RelArmVec s₁₀ s₂₀ a v₁ v₂) (hle : a.le b = true) :
    RelArmVec s₁₀ s₂₀ b v₁ v₂ := by
  unfold VecOrigin.le at hle
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hle
  rcases hle with (rfl | rfl) | ⟨rfl, hPub⟩
  · exact hRel
  · trivial
  · exact RelArmVec_public_eq hRel hPub

private def RelArm64 (s₁₀ s₂₀ : Arm64State) (st : Arm64AbsState) (s₁ s₂ : Arm64State) : Prop :=
  s₁.pc = s₂.pc ∧
  s₁.halted = false ∧ s₂.halted = false ∧
  s₁.dit = st.dit ∧ s₂.dit = st.dit ∧
  (∀ r : Nat, r < 31 → RelArmGpr s₁₀ s₂₀ (st.gpr.get r) (s₁.gpr.get r) (s₂.gpr.get r)) ∧
  (∀ v : Nat, v < 32 → RelArmVec s₁₀ s₂₀ (st.vec.get v) (s₁.vec.get v) (s₂.vec.get v)) ∧
  (st.cfPub = true → s₁.cf = s₂.cf) ∧
  (st.zfPub = true → s₁.zf = s₂.zf)

private theorem RelArm64_mono {s₁₀ s₂₀ s₁ s₂ : Arm64State} {a b : Arm64AbsState}
    (hRel : RelArm64 s₁₀ s₂₀ a s₁ s₂) (hle : a.le b = true) :
    RelArm64 s₁₀ s₂₀ b s₁ s₂ := by
  unfold Arm64AbsState.le at hle
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hle
  rcases hle with ⟨⟨⟨⟨hDit, hGpr⟩, hVec⟩, hCf⟩, hZf⟩
  rcases hRel with ⟨hPc, hH1, hH2, rDit1, rDit2, rGpr, rVec, rCf, rZf⟩
  refine ⟨hPc, hH1, hH2, rDit1.trans (beq_iff_eq.mp hDit), rDit2.trans (beq_iff_eq.mp hDit), ?_, ?_, ?_, ?_⟩
  · intro r hr; exact RelArmGpr_mono (rGpr r hr) (Bank32.allIdx_get hGpr (by omega))
  · intro v hv; exact RelArmVec_mono (rVec v hv) (Bank32.allIdx_get hVec hv)
  · intro hb; exact hCf.elim (fun hbf => nomatch hbf.symm.trans hb) (fun ha => rCf ha)
  · intro hb; exact hZf.elim (fun hbf => nomatch hbf.symm.trans hb) (fun ha => rZf ha)

private theorem RelArm64_init {c : FuncContract} {s₁ s₂ : Arm64State}
    (hInit : Arm64ContractInit c s₁ s₂) :
    RelArm64 s₁ s₂ (initArm64AbsState c) s₁ s₂ := by
  rcases hInit with ⟨hpc1, hpc2, hh1, hh2, hd1, hd2, hPubGprs⟩
  refine ⟨by omega, hh1, hh2, hd1, hd2, ?_, ?_, (fun h => nomatch h), (fun h => nomatch h)⟩
  · intro r hr
    unfold initArm64AbsState
    rw [Bank32.get_ofFn _ (by omega)]
    have hne31 : (r == 31) = false := beq_false_of_ne (by omega)
    simp only [hne31, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i hMem
      exact ⟨hr, rfl, rfl, (hPubGprs r hMem).2⟩
    · split
      · exact ⟨hr, rfl, rfl⟩
      · trivial
  · intro v hv
    unfold initArm64AbsState
    rw [Bank32.get_ofFn _ hv]
    exact ⟨hv, rfl, rfl⟩

private theorem getArmGpr_rel {s₁₀ s₂₀ s₁ s₂ : Arm64State} {st : Arm64AbsState} {r : Nat}
    (hr : r < 32)
    (rGpr : ∀ i < 31, RelArmGpr s₁₀ s₂₀ (st.gpr.get i) (s₁.gpr.get i) (s₂.gpr.get i)) :
    RelArmGpr s₁₀ s₂₀ (getArmAbsGpr st r) (getArmGpr s₁ r) (getArmGpr s₂ r) := by
  unfold getArmAbsGpr getArmGpr
  by_cases h31 : r == 31
  · simp [h31, RelArmGpr]
  · simp only [h31, Bool.false_eq_true, ↓reduceIte]
    have hne : r ≠ 31 := fun h => h31 (beq_iff_eq.mpr h)
    exact rGpr r (by omega)

private theorem setArmGpr_rel {s₁₀ s₂₀ s₁ s₂ : Arm64State} {st : Arm64AbsState}
    {rd : Nat} {orig : ArmRegOrigin} {v₁ v₂ : UInt64}
    (_hrd : rd < 32)
    (rGpr : ∀ i < 31, RelArmGpr s₁₀ s₂₀ (st.gpr.get i) (s₁.gpr.get i) (s₂.gpr.get i))
    (hNew : RelArmGpr s₁₀ s₂₀ orig v₁ v₂) :
    ∀ i < 31, RelArmGpr s₁₀ s₂₀ ((setArmAbsGpr st rd orig).get i)
      ((setArmGpr s₁ rd v₁).get i) ((setArmGpr s₂ rd v₂).get i) := by
  intro i hi
  unfold setArmAbsGpr setArmGpr
  by_cases h31 : rd == 31
  · simp only [h31, ↓reduceIte]; exact rGpr i hi
  · simp only [h31, Bool.false_eq_true, ↓reduceIte]
    have hrd31 : rd < 31 := by
      have hne : rd ≠ 31 := fun h => h31 (beq_iff_eq.mpr h)
      omega
    by_cases heq : i = rd
    · subst heq; simp only [Bank32.get_set_eq]; exact hNew
    · rw [Bank32.get_set_ne _ _ (by omega) (by omega) (Ne.symm heq),
          Bank32.get_set_ne _ _ (by omega) (by omega) (Ne.symm heq),
          Bank32.get_set_ne _ _ (by omega) (by omega) (Ne.symm heq)]
      exact rGpr i hi

private theorem RelArmVec_set {s₁₀ s₂₀ : Arm64State} {vc : Bank32 VecOrigin} {b₁ b₂ : Bank32 Vec128}
    {vd : Nat} {vo : VecOrigin} {v₁ v₂ : Vec128}
    (hvd : vd < 32)
    (hOld : ∀ i < 32, RelArmVec s₁₀ s₂₀ (vc.get i) (b₁.get i) (b₂.get i))
    (hNew : RelArmVec s₁₀ s₂₀ vo v₁ v₂) :
    ∀ i < 32, RelArmVec s₁₀ s₂₀ ((vc.set vd vo).get i) ((b₁.set vd v₁).get i) ((b₂.set vd v₂).get i) := by
  intro i hi
  by_cases heq : i = vd
  · subst heq; simp only [Bank32.get_set_eq]; exact hNew
  · rw [Bank32.get_set_ne _ _ hvd hi (Ne.symm heq),
        Bank32.get_set_ne _ _ hvd hi (Ne.symm heq),
        Bank32.get_set_ne _ _ hvd hi (Ne.symm heq)]
    exact hOld i hi

private theorem evalArmCond_public_eq {st : Arm64AbsState} {s₁ s₂ : Arm64State} {cond : Nat}
    (hPub : armCondIsPublic cond st = true)
    (rCf : st.cfPub = true → s₁.cf = s₂.cf)
    (rZf : st.zfPub = true → s₁.zf = s₂.zf) :
    evalArmCond cond s₁ = evalArmCond cond s₂ := by
  unfold armCondIsPublic at hPub
  unfold evalArmCond
  by_cases c0 : cond == 0
  · simp [c0] at hPub ⊢; exact rZf hPub
  · by_cases c1 : cond == 1
    · simp [c0, c1] at hPub ⊢; exact rZf hPub
    · by_cases c2 : cond == 2
      · simp [c0, c1, c2] at hPub ⊢; exact rCf hPub
      · by_cases c3 : cond == 3
        · simp [c0, c1, c2, c3] at hPub ⊢; exact rCf hPub
        · simp [c0, c1, c2, c3] at hPub ⊢; exact rCf hPub

private theorem arm_eor_self_zero (is64 : Bool) (v : UInt64) (sk : Nat) (cf zf : Bool) :
    evalArmAlu .eor is64 v (applyArmShift is64 v sk 0) cf zf = (0, cf, zf) := by
  unfold applyArmShift evalArmAlu maskGprWidth
  cases is64
  · simp only [Bool.false_eq_true, ↓reduceIte, show 0 % 32 = 0 from rfl, beq_self_eq_true]
    have hz : (v ^^^ (v &&& 0xFFFFFFFF)) &&& 0xFFFFFFFF = 0 := by
      apply UInt64.eq_of_toBitVec_eq
      rw [UInt64.toBitVec_and, UInt64.toBitVec_xor, UInt64.toBitVec_and]
      apply BitVec.eq_of_getLsbD_eq; intro i _hi
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor]
      rw [show (0 : UInt64).toBitVec = 0#64 from rfl, BitVec.getLsbD_zero]
      cases v.toBitVec.getLsbD i <;>
        cases (0xFFFFFFFF : UInt64).toBitVec.getLsbD i <;> rfl
    simp [hz]
  · simp only [↓reduceIte, show 0 % 64 = 0 from rfl, beq_self_eq_true]
    have hz : v ^^^ v = 0 := by apply UInt64.eq_of_toBitVec_eq; simp
    simp [hz]

private theorem evalArmAlu_res_flags {op : Arm64AluOp} {is64 : Bool}
    {a₁ b₁ : UInt64} {cf₁ zf₁ : Bool} :
    (evalArmAlu op is64 a₁ b₁ cf₁ zf₁).2 =
      (if op == .adds || op == .subs then
         ((evalArmAlu op is64 a₁ b₁ cf₁ zf₁).2.1, (evalArmAlu op is64 a₁ b₁ cf₁ zf₁).2.2)
       else (cf₁, zf₁)) := by
  cases op <;> rfl

private theorem evalArmAlu_pub_congr (op : Arm64AluOp) (is64 : Bool)
    {a₁ a₂ b₁ b₂ : UInt64} {cf₁ cf₂ zf₁ zf₂ : Bool}
    (ha : a₁ = a₂) (hb : b₁ = b₂)
    (hcf : (if op == .adc || op == .sbc then true else false) = true → cf₁ = cf₂) :
    (evalArmAlu op is64 a₁ b₁ cf₁ zf₁).1 = (evalArmAlu op is64 a₂ b₂ cf₂ zf₂).1 ∧
    ((op == .adds || op == .subs) = true →
      (evalArmAlu op is64 a₁ b₁ cf₁ zf₁).2.1 = (evalArmAlu op is64 a₂ b₂ cf₂ zf₂).2.1 ∧
      (evalArmAlu op is64 a₁ b₁ cf₁ zf₁).2.2 = (evalArmAlu op is64 a₂ b₂ cf₂ zf₂).2.2) := by
  subst ha hb
  cases op <;> simp_all [evalArmAlu]

private theorem transferArm64Instr_step_sound {c : FuncContract}
    {s₁₀ s₂₀ s₁ s₂ : Arm64State} {d : DecodedInstr Arm64Instr}
    {st : Arm64AbsState} {succs : List (Nat × Arm64AbsState)}
    (hRel : RelArm64 s₁₀ s₂₀ st s₁ s₂)
    (_hPcEq : s₁.pc = d.offset)
    (hTr : transferArm64Instr c d st = some succs) :
    let (s₁', obs₁) := stepArm64 d s₁
    let (s₂', obs₂) := stepArm64 d s₂
    obs₁ = obs₂ ∧
    obs₁.isDoitSafe = true ∧
    ((s₁'.halted = true ∧ s₂'.halted = true ∧ Arm64ExitHygiene c s₁₀ s₂₀ s₁' s₂') ∨
     (∃ nst : Arm64AbsState, (s₁'.pc, nst) ∈ succs ∧ RelArm64 s₁₀ s₂₀ nst s₁' s₂')) := by
  by_cases hGate : (armRequiresDit d.instr && !st.dit) = true
  · simp [transferArm64Instr, hGate] at hTr
  have hAllowed : armRequiresDit d.instr = true → st.dit = true := by
    intro h
    cases hd : st.dit
    · simp [h, hd] at hGate
    · rfl
  cases hValid : arm64InstrRegsValid d.instr
  · unfold transferArm64Instr at hTr; simp [hGate, hValid] at hTr
  · rcases hRel with ⟨hPc12, hH1, hH2, rDit1, rDit2, rGpr, rVec, rCf, rZf⟩
    cases hIns : d.instr <;>
      unfold transferArm64Instr at hTr <;>
      simp only [hGate, Bool.false_eq_true, ↓reduceIte] at hTr <;>
      rw [hIns] at hTr hValid <;>
      simp only [hValid, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr <;>
      simp only [arm64InstrRegsValid, Bool.and_eq_true, decide_eq_true_eq] at hValid
    case nop =>
      injection hTr with hS; subst hS; simp only [stepArm64, hIns, true_and]
      exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, rVec, rCf, rZf⟩
    case msrDit imm =>
      injection hTr with hS; subst hS; simp only [stepArm64, hIns, true_and]
      exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rfl, rfl, rGpr, rVec, rCf, rZf⟩
    case isb =>
      injection hTr with hS; subst hS; simp only [stepArm64, hIns, true_and]
      exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, rVec, rCf, rZf⟩
    case dmbIsh =>
      injection hTr with hS; subst hS; simp only [stepArm64, hIns, true_and]
      exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, rVec, rCf, rZf⟩
    case ret =>
      by_cases hRetOk : (([19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30].all (fun r =>
            st.gpr.get r == .initOwn r || st.gpr.get r == .initSame r)) &&
          ([8, 9, 10, 11, 12, 13, 14, 15].all (fun v => st.vec.get v == .initVec v)) &&
          st.vec.allIdx (fun _ vo => vo != .secretVal && vo != .pubVal) &&
          c.wipedScratchGprs.all (fun r => decide (r < 32) && getArmAbsGpr st r == .zeroConst)) = true
      · simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq,
          List.all_eq_true] at hRetOk
        rcases hRetOk with ⟨⟨⟨hCalleeGpr, hCalleeVec⟩, hVecWiped⟩, hGprWiped⟩
        simp only [stepArm64, hIns, true_and]
        left
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro r hr
          have hcr := hCalleeGpr r hr
          have hr31 : r < 31 := by simp at hr; omega
          have rr := rGpr r hr31
          rcases hcr with hOwn | hSame
          · rw [hOwn] at rr; exact rr.2
          · rw [hSame] at rr; exact ⟨rr.2.1, rr.2.2.1⟩
        · intro v hv
          have hcv := hCalleeVec v hv
          have hv32 : v < 32 := by simp at hv; omega
          have rv := rVec v hv32
          rw [hcv] at rv
          exact rv.2
        · intro v hv
          have hNotSec := Bank32.allIdx_get hVecWiped hv
          simp only [Bool.and_eq_true, bne_iff_ne] at hNotSec
          have rv := rVec v hv
          cases hVo : st.vec.get v <;> rw [hVo] at rv hNotSec
          · exact Or.inr ⟨_, rv.1, rv.2⟩
          · exact Or.inl rv
          · exact absurd rfl hNotSec.2
          · exact absurd rfl hNotSec.1
        · intro r hr
          rcases hGprWiped r hr with ⟨hr32, hZ⟩
          have rr := getArmGpr_rel hr32 rGpr
          rw [hZ] at rr
          exact rr
      · have hF : (([19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30].all (fun r =>
              st.gpr.get r == .initOwn r || st.gpr.get r == .initSame r)) &&
            ([8, 9, 10, 11, 12, 13, 14, 15].all (fun v => st.vec.get v == .initVec v)) &&
            st.vec.allIdx (fun _ vo => vo != .secretVal && vo != .pubVal) &&
            c.wipedScratchGprs.all (fun r => decide (r < 32) && getArmAbsGpr st r == .zeroConst)) = false :=
          Bool.eq_false_iff.mpr hRetOk
        simp only [hF, Bool.false_eq_true, ↓reduceIte] at hTr; cases hTr
    case aluReg op is64 rd rn rm sk sa =>
      rcases hValid with ⟨⟨hd32, hn32⟩, hm32⟩
      by_cases hEorSelf : (op == .eor && rn == rm && sa == 0) = true
      · simp only [hEorSelf, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [Bool.and_eq_true, beq_iff_eq] at hEorSelf
        rcases hEorSelf with ⟨⟨rfl, rfl⟩, rfl⟩
        simp only [stepArm64, hIns, arm_eor_self_zero, true_and]
        exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2,
          setArmGpr_rel hd32 rGpr ⟨rfl, rfl⟩, rVec, rCf, rZf⟩
      · simp only [hEorSelf, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [stepArm64, hIns, true_and]
        have hCongr : ((getArmAbsGpr st rn).isPublic && (getArmAbsGpr st rm).isPublic &&
            (if op == .adc || op == .sbc then st.cfPub else true)) = true →
            (evalArmAlu op is64 (getArmGpr s₁ rn) (applyArmShift is64 (getArmGpr s₁ rm) sk sa) s₁.cf s₁.zf).1 =
            (evalArmAlu op is64 (getArmGpr s₂ rn) (applyArmShift is64 (getArmGpr s₂ rm) sk sa) s₂.cf s₂.zf).1 ∧
            ((op == .adds || op == .subs) = true →
              (evalArmAlu op is64 (getArmGpr s₁ rn) (applyArmShift is64 (getArmGpr s₁ rm) sk sa) s₁.cf s₁.zf).2.1 =
              (evalArmAlu op is64 (getArmGpr s₂ rn) (applyArmShift is64 (getArmGpr s₂ rm) sk sa) s₂.cf s₂.zf).2.1 ∧
              (evalArmAlu op is64 (getArmGpr s₁ rn) (applyArmShift is64 (getArmGpr s₁ rm) sk sa) s₁.cf s₁.zf).2.2 =
              (evalArmAlu op is64 (getArmGpr s₂ rn) (applyArmShift is64 (getArmGpr s₂ rm) sk sa) s₂.cf s₂.zf).2.2) := by
          intro hp; simp only [Bool.and_eq_true] at hp
          have en := RelArmGpr_public_eq (getArmGpr_rel hn32 rGpr) hp.1.1
          have em := RelArmGpr_public_eq (getArmGpr_rel hm32 rGpr) hp.1.2
          exact evalArmAlu_pub_congr op is64 en (congrArg (fun x => applyArmShift is64 x sk sa) em)
            (fun hNeed => rCf (by
              by_cases hc : (op == .adc || op == .sbc) = true
              · simpa [hc] using hp.2
              · simp [hc] at hNeed))
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, ?_, rVec, ?_, ?_⟩
        · apply setArmGpr_rel hd32 rGpr
          by_cases hp : ((getArmAbsGpr st rn).isPublic && (getArmAbsGpr st rm).isPublic &&
              (if op == .adc || op == .sbc then st.cfPub else true)) = true
          · simp only [hp, ↓reduceIte, RelArmGpr]; exact (hCongr hp).1
          · simp only [hp, Bool.false_eq_true, ↓reduceIte, RelArmGpr]
        · by_cases hSf : (op == .adds || op == .subs) = true
          · simp only [hSf, ↓reduceIte]; intro hp; exact ((hCongr hp).2 hSf).1
          · simp only [hSf, Bool.false_eq_true, ↓reduceIte]
            intro hCfB
            have hKeep1 := @evalArmAlu_res_flags op is64 (getArmGpr s₁ rn)
              (applyArmShift is64 (getArmGpr s₁ rm) sk sa) s₁.cf s₁.zf
            have hKeep2 := @evalArmAlu_res_flags op is64 (getArmGpr s₂ rn)
              (applyArmShift is64 (getArmGpr s₂ rm) sk sa) s₂.cf s₂.zf
            simp only [hSf, Bool.false_eq_true, ↓reduceIte] at hKeep1 hKeep2
            rw [congrArg Prod.fst hKeep1, congrArg Prod.fst hKeep2, rCf hCfB]
        · by_cases hSf : (op == .adds || op == .subs) = true
          · simp only [hSf, ↓reduceIte]; intro hp; exact ((hCongr hp).2 hSf).2
          · simp only [hSf, Bool.false_eq_true, ↓reduceIte]
            intro hZfB
            have hKeep1 := @evalArmAlu_res_flags op is64 (getArmGpr s₁ rn)
              (applyArmShift is64 (getArmGpr s₁ rm) sk sa) s₁.cf s₁.zf
            have hKeep2 := @evalArmAlu_res_flags op is64 (getArmGpr s₂ rn)
              (applyArmShift is64 (getArmGpr s₂ rm) sk sa) s₂.cf s₂.zf
            simp only [hSf, Bool.false_eq_true, ↓reduceIte] at hKeep1 hKeep2
            rw [congrArg Prod.snd hKeep1, congrArg Prod.snd hKeep2, rZf hZfB]
    case aluImm op is64 rd rn imm =>
      rcases hValid with ⟨hd32, hn32⟩
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, true_and]
      have hCongr : ((getArmAbsGpr st rn).isPublic &&
          (if op == .adc || op == .sbc then st.cfPub else true)) = true →
          (evalArmAlu op is64 (getArmGpr s₁ rn) imm s₁.cf s₁.zf).1 =
          (evalArmAlu op is64 (getArmGpr s₂ rn) imm s₂.cf s₂.zf).1 ∧
          ((op == .adds || op == .subs) = true →
            (evalArmAlu op is64 (getArmGpr s₁ rn) imm s₁.cf s₁.zf).2.1 =
            (evalArmAlu op is64 (getArmGpr s₂ rn) imm s₂.cf s₂.zf).2.1 ∧
            (evalArmAlu op is64 (getArmGpr s₁ rn) imm s₁.cf s₁.zf).2.2 =
            (evalArmAlu op is64 (getArmGpr s₂ rn) imm s₂.cf s₂.zf).2.2) := by
        intro hp; simp only [Bool.and_eq_true] at hp
        exact evalArmAlu_pub_congr op is64 (RelArmGpr_public_eq (getArmGpr_rel hn32 rGpr) hp.1) rfl
          (fun hNeed => rCf (by
            by_cases hc : (op == .adc || op == .sbc) = true
            · simpa [hc] using hp.2
            · simp [hc] at hNeed))
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, ?_, rVec, ?_, ?_⟩
      · apply setArmGpr_rel hd32 rGpr
        by_cases hp : ((getArmAbsGpr st rn).isPublic &&
            (if op == .adc || op == .sbc then st.cfPub else true)) = true
        · simp only [hp, ↓reduceIte, RelArmGpr]; exact (hCongr hp).1
        · simp only [hp, Bool.false_eq_true, ↓reduceIte, RelArmGpr]
      · by_cases hSf : (op == .adds || op == .subs) = true
        · simp only [hSf, ↓reduceIte]; intro hp; exact ((hCongr hp).2 hSf).1
        · simp only [hSf, Bool.false_eq_true, ↓reduceIte]
          intro hCfB
          have hKeep1 := @evalArmAlu_res_flags op is64 (getArmGpr s₁ rn) imm s₁.cf s₁.zf
          have hKeep2 := @evalArmAlu_res_flags op is64 (getArmGpr s₂ rn) imm s₂.cf s₂.zf
          simp only [hSf, Bool.false_eq_true, ↓reduceIte] at hKeep1 hKeep2
          rw [congrArg Prod.fst hKeep1, congrArg Prod.fst hKeep2, rCf hCfB]
      · by_cases hSf : (op == .adds || op == .subs) = true
        · simp only [hSf, ↓reduceIte]; intro hp; exact ((hCongr hp).2 hSf).2
        · simp only [hSf, Bool.false_eq_true, ↓reduceIte]
          intro hZfB
          have hKeep1 := @evalArmAlu_res_flags op is64 (getArmGpr s₁ rn) imm s₁.cf s₁.zf
          have hKeep2 := @evalArmAlu_res_flags op is64 (getArmGpr s₂ rn) imm s₂.cf s₂.zf
          simp only [hSf, Bool.false_eq_true, ↓reduceIte] at hKeep1 hKeep2
          rw [congrArg Prod.snd hKeep1, congrArg Prod.snd hKeep2, rZf hZfB]
    case movWide isMovn is64 rd imm16 sh =>
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, ?_, rVec, rCf, rZf⟩
      apply setArmGpr_rel hValid rGpr
      by_cases hz : (!isMovn && imm16 == 0) = true
      · simp only [hz, ↓reduceIte, RelArmGpr]
        simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hz
        rcases hz with ⟨rfl, rfl⟩
        have hSh0 : (0 : UInt64) <<< UInt64.ofNat sh = 0 := by apply UInt64.eq_of_toBitVec_eq; simp
        have hm0 : maskGprWidth is64 0 = 0 := by cases is64 <;> rfl
        simp [hSh0, hm0]
      · simp [hz, RelArmGpr]
    case ubfm is64 rd rn immr imms =>
      rcases hValid with ⟨hd32, hn32⟩
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, ?_, rVec, rCf, rZf⟩
      apply setArmGpr_rel hd32 rGpr
      by_cases hp : (getArmAbsGpr st rn).isPublic = true
      · simp only [hp, ↓reduceIte, RelArmGpr]; rw [RelArmGpr_public_eq (getArmGpr_rel hn32 rGpr) hp]
      · simp [hp, RelArmGpr]
    case mulOp isUmulh rd rn rm =>
      have hd : st.dit = true := hAllowed (by simp [hIns, armRequiresDit])
      rcases hValid with ⟨⟨hd32, hn32⟩, hm32⟩
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, rDit1, rDit2, hd, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rfl, rfl, ?_, rVec, rCf, rZf⟩
      apply setArmGpr_rel hd32 rGpr
      by_cases hp : ((getArmAbsGpr st rn).isPublic && (getArmAbsGpr st rm).isPublic) = true
      · simp only [hp, ↓reduceIte, RelArmGpr]
        simp only [Bool.and_eq_true] at hp
        rw [RelArmGpr_public_eq (getArmGpr_rel hn32 rGpr) hp.1,
            RelArmGpr_public_eq (getArmGpr_rel hm32 rGpr) hp.2]
      · simp [hp, RelArmGpr]
    case csel cond isInv is64 rd rn rm =>
      have hd : st.dit = true := hAllowed (by simp [hIns, armRequiresDit])
      rcases hValid with ⟨⟨hd32, hn32⟩, hm32⟩
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, rDit1, rDit2, hd, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rfl, rfl, ?_, rVec, rCf, rZf⟩
      apply setArmGpr_rel hd32 rGpr
      by_cases hp : (armCondIsPublic cond st && (getArmAbsGpr st rn).isPublic && (getArmAbsGpr st rm).isPublic) = true
      · simp only [hp, ↓reduceIte, RelArmGpr]
        simp only [Bool.and_eq_true] at hp
        rw [evalArmCond_public_eq hp.1.1 rCf rZf,
            RelArmGpr_public_eq (getArmGpr_rel hn32 rGpr) hp.1.2,
            RelArmGpr_public_eq (getArmGpr_rel hm32 rGpr) hp.2]
      · simp [hp, RelArmGpr]
    case ldp64 rt1 rt2 rn off =>
      rcases hValid with ⟨⟨ht1, ht2⟩, hn32⟩
      cases hPub : (getArmAbsGpr st rn).isPublic
      · simp [hPub] at hTr
      · simp only [hPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hRnEq := RelArmGpr_public_eq (getArmGpr_rel hn32 rGpr) hPub
        simp only [stepArm64, hIns, hRnEq, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, ?_, rVec, rCf, rZf⟩
        have r1 := setArmGpr_rel ht1 rGpr (orig := .secretVal)
          (v₁ := readMem64 s₁.mem (getArmGpr s₂ rn + off))
          (v₂ := readMem64 s₂.mem (getArmGpr s₂ rn + off)) trivial
        exact setArmGpr_rel (st := { st with gpr := setArmAbsGpr st rt1 .secretVal })
          (s₁ := { s₁ with gpr := setArmGpr s₁ rt1 (readMem64 s₁.mem (getArmGpr s₂ rn + off)) })
          (s₂ := { s₂ with gpr := setArmGpr s₂ rt1 (readMem64 s₂.mem (getArmGpr s₂ rn + off)) })
          ht2 r1 trivial
    case stp64 rt1 rt2 rn off =>
      rcases hValid with ⟨⟨_, _⟩, hn32⟩
      cases hPub : (getArmAbsGpr st rn).isPublic
      · simp [hPub] at hTr
      · simp only [hPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hRnEq := RelArmGpr_public_eq (getArmGpr_rel hn32 rGpr) hPub
        simp only [stepArm64, hIns, hRnEq, true_and]
        exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, rVec, rCf, rZf⟩
    case strbPost rt rn postOff =>
      rcases hValid with ⟨_, hn32⟩
      cases hPub : (getArmAbsGpr st rn).isPublic
      · simp [hPub] at hTr
      · simp only [hPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hRnEq := RelArmGpr_public_eq (getArmGpr_rel hn32 rGpr) hPub
        simp only [stepArm64, hIns, hRnEq, true_and]
        exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, setArmGpr_rel hn32 rGpr rfl, rVec, rCf, rZf⟩
    case ldrQ rt rn off =>
      rcases hValid with ⟨ht32, hn32⟩
      cases hPub : (getArmAbsGpr st rn).isPublic
      · simp [hPub] at hTr
      · simp only [hPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hRnEq := RelArmGpr_public_eq (getArmGpr_rel hn32 rGpr) hPub
        simp only [stepArm64, hIns, hRnEq, true_and]
        exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, RelArmVec_set ht32 rVec trivial, rCf, rZf⟩
    case strQ rt rn off =>
      rcases hValid with ⟨_, hn32⟩
      cases hPub : (getArmAbsGpr st rn).isPublic
      · simp [hPub] at hTr
      · simp only [hPub, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hRnEq := RelArmGpr_public_eq (getArmGpr_rel hn32 rGpr) hPub
        simp only [stepArm64, hIns, hRnEq, true_and]
        exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, rVec, rCf, rZf⟩
    case fmovDFromX vd xn =>
      rcases hValid with ⟨hvd, hxn⟩
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, ?_, rCf, rZf⟩
      apply RelArmVec_set hvd rVec
      by_cases hz : (getArmAbsGpr st xn == .zeroConst) = true
      · simp only [hz, ↓reduceIte, RelArmVec]
        have rx := getArmGpr_rel hxn rGpr
        rw [beq_iff_eq.mp hz] at rx
        rcases rx with ⟨x1, x2⟩
        simp [x1, x2, Vec128.zero]
      · simp only [hz, Bool.false_eq_true, ↓reduceIte]
        by_cases hp : (getArmAbsGpr st xn).isPublic = true
        · simp only [hp, ↓reduceIte, RelArmVec]
          rw [RelArmGpr_public_eq (getArmGpr_rel hxn rGpr) hp]
        · simp [hp, RelArmVec]
    case veor16b vd vn vm =>
      rcases hValid with ⟨⟨hvd, hvn⟩, hvm⟩
      by_cases hSelf : (vn == vm) = true
      · simp only [hSelf, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have hEq := beq_iff_eq.mp hSelf; subst hEq
        have hx (w : UInt64) : w ^^^ w = 0 := by apply UInt64.eq_of_toBitVec_eq; simp
        simp only [stepArm64, hIns, hx, true_and]
        exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr,
          RelArmVec_set hvd rVec ⟨rfl, rfl⟩, rCf, rZf⟩
      · simp only [hSelf, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [stepArm64, hIns, true_and]
        refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, ?_, rCf, rZf⟩
        apply RelArmVec_set hvd rVec
        by_cases hp : ((st.vec.get vn).isPublic && (st.vec.get vm).isPublic) = true
        · simp only [hp, ↓reduceIte, RelArmVec]
          simp only [Bool.and_eq_true] at hp
          rw [RelArmVec_public_eq (rVec vn hvn) hp.1, RelArmVec_public_eq (rVec vm hvm) hp.2]
        · simp [hp, RelArmVec]
    case vbcax16b vd vn vm va =>
      rcases hValid with ⟨⟨⟨hvd, hvn⟩, hvm⟩, hva⟩
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, ?_, rCf, rZf⟩
      apply RelArmVec_set hvd rVec
      by_cases hp : ((st.vec.get vn).isPublic && (st.vec.get vm).isPublic && (st.vec.get va).isPublic) = true
      · simp only [hp, ↓reduceIte, RelArmVec]
        simp only [Bool.and_eq_true] at hp
        rw [RelArmVec_public_eq (rVec vn hvn) hp.1.1,
            RelArmVec_public_eq (rVec vm hvm) hp.1.2,
            RelArmVec_public_eq (rVec va hva) hp.2]
      · simp [hp, RelArmVec]
    case veor3_16b vd vn vm va =>
      rcases hValid with ⟨⟨⟨hvd, hvn⟩, hvm⟩, hva⟩
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, ?_, rCf, rZf⟩
      apply RelArmVec_set hvd rVec
      by_cases hp : ((st.vec.get vn).isPublic && (st.vec.get vm).isPublic && (st.vec.get va).isPublic) = true
      · simp only [hp, ↓reduceIte, RelArmVec]
        simp only [Bool.and_eq_true] at hp
        rw [RelArmVec_public_eq (rVec vn hvn) hp.1.1,
            RelArmVec_public_eq (rVec vm hvm) hp.1.2,
            RelArmVec_public_eq (rVec va hva) hp.2]
      · simp [hp, RelArmVec]
    case vrax1_2d vd vn vm =>
      rcases hValid with ⟨⟨hvd, hvn⟩, hvm⟩
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, ?_, rCf, rZf⟩
      apply RelArmVec_set hvd rVec
      by_cases hp : ((st.vec.get vn).isPublic && (st.vec.get vm).isPublic) = true
      · simp only [hp, ↓reduceIte, RelArmVec]
        simp only [Bool.and_eq_true] at hp
        rw [RelArmVec_public_eq (rVec vn hvn) hp.1, RelArmVec_public_eq (rVec vm hvm) hp.2]
      · simp [hp, RelArmVec]
    case vxar_2d vd vn vm imm6 =>
      rcases hValid with ⟨⟨hvd, hvn⟩, hvm⟩
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, ?_, rCf, rZf⟩
      apply RelArmVec_set hvd rVec
      by_cases hp : ((st.vec.get vn).isPublic && (st.vec.get vm).isPublic) = true
      · simp only [hp, ↓reduceIte, RelArmVec]
        simp only [Bool.and_eq_true] at hp
        rw [RelArmVec_public_eq (rVec vn hvn) hp.1, RelArmVec_public_eq (rVec vm hvm) hp.2]
      · simp [hp, RelArmVec]
    case vpmull isHigh vd vn vm =>
      have hd : st.dit = true := hAllowed (by simp [hIns, armRequiresDit])
      rcases hValid with ⟨⟨hvd, hvn⟩, hvm⟩
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, rDit1, rDit2, hd, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rfl, rfl, rGpr, ?_, rCf, rZf⟩
      apply RelArmVec_set hvd rVec
      by_cases hp : ((st.vec.get vn).isPublic && (st.vec.get vm).isPublic) = true
      · simp only [hp, ↓reduceIte, RelArmVec]
        simp only [Bool.and_eq_true] at hp
        rw [RelArmVec_public_eq (rVec vn hvn) hp.1, RelArmVec_public_eq (rVec vm hvm) hp.2]
      · simp [hp, RelArmVec]
    case vtrn is128 second elementBytes vd vn vm =>
      rcases hValid with ⟨⟨hvd, hvn⟩, hvm⟩
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, ?_, rCf, rZf⟩
      apply RelArmVec_set hvd rVec
      by_cases hp : ((st.vec.get vn).isPublic && (st.vec.get vm).isPublic) = true
      · simp only [hp, ↓reduceIte, RelArmVec]
        simp only [Bool.and_eq_true] at hp
        rw [RelArmVec_public_eq (rVec vn hvn) hp.1, RelArmVec_public_eq (rVec vm hvm) hp.2]
      · simp [hp, RelArmVec]
    case vext16b vd vn vm imm4 =>
      rcases hValid with ⟨⟨hvd, hvn⟩, hvm⟩
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, ?_, rCf, rZf⟩
      apply RelArmVec_set hvd rVec
      by_cases hp : ((st.vec.get vn).isPublic && (st.vec.get vm).isPublic) = true
      · simp only [hp, ↓reduceIte, RelArmVec]
        simp only [Bool.and_eq_true] at hp
        rw [RelArmVec_public_eq (rVec vn hvn) hp.1, RelArmVec_public_eq (rVec vm hvm) hp.2]
      · simp [hp, RelArmVec]
    case vdup2d vd xn =>
      rcases hValid with ⟨hvd, hxn⟩
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, ?_, rCf, rZf⟩
      apply RelArmVec_set hvd rVec
      by_cases hz : (getArmAbsGpr st xn == .zeroConst) = true
      · simp only [hz, ↓reduceIte, RelArmVec]
        have rx := getArmGpr_rel hxn rGpr
        rw [beq_iff_eq.mp hz] at rx
        rcases rx with ⟨x1, x2⟩
        simp [x1, x2, Vec128.zero]
      · simp only [hz, Bool.false_eq_true, ↓reduceIte]
        by_cases hp : (getArmAbsGpr st xn).isPublic = true
        · simp only [hp, ↓reduceIte, RelArmVec]
          rw [RelArmGpr_public_eq (getArmGpr_rel hxn rGpr) hp]
        · simp [hp, RelArmVec]
    case vand16b vd vn vm =>
      rcases hValid with ⟨⟨hvd, hvn⟩, hvm⟩
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, ?_, rCf, rZf⟩
      apply RelArmVec_set hvd rVec
      by_cases hp : ((st.vec.get vn).isPublic && (st.vec.get vm).isPublic) = true
      · simp only [hp, ↓reduceIte, RelArmVec]
        simp only [Bool.and_eq_true] at hp
        rw [RelArmVec_public_eq (rVec vn hvn) hp.1, RelArmVec_public_eq (rVec vm hvm) hp.2]
      · simp [hp, RelArmVec]
    case vshift2d left vd vn amount =>
      rcases hValid with ⟨hvd, hvn⟩
      injection hTr with hS; subst hS
      simp only [stepArm64, hIns, true_and]
      refine Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, ?_, rCf, rZf⟩
      apply RelArmVec_set hvd rVec
      by_cases hp : (st.vec.get vn).isPublic = true
      · simp only [hp, ↓reduceIte, RelArmVec]
        rw [RelArmVec_public_eq (rVec vn hvn) hp]
      · simp [hp, RelArmVec]
    case ldpQ rt1 rt2 rn off =>
      rcases hValid with ⟨⟨ht1, ht2⟩, hn⟩
      cases hp : (getArmAbsGpr st rn).isPublic
      · simp [hp] at hTr
      · simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have he := RelArmGpr_public_eq (getArmGpr_rel hn rGpr) hp
        simp only [stepArm64, hIns, he, true_and]
        exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr,
          RelArmVec_set ht2 (RelArmVec_set ht1 rVec trivial) trivial, rCf, rZf⟩
    case stpQ rt1 rt2 rn off =>
      rcases hValid with ⟨⟨_, _⟩, hn⟩
      cases hp : (getArmAbsGpr st rn).isPublic
      · simp [hp] at hTr
      · simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        have he := RelArmGpr_public_eq (getArmGpr_rel hn rGpr) hp
        simp only [stepArm64, hIns, he, true_and]
        exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, rVec, rCf, rZf⟩
    case bCond cond targetPc =>
      by_cases hBad : (!armCondIsPublic cond st || decide (targetPc < 0) || decide (targetPc.toNat ≥ 8192)) = true
      · simp [hBad] at hTr
      · simp only [hBad, Bool.false_eq_true, ↓reduceIte] at hTr
        injection hTr with hS; subst hS
        simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, not_or, Bool.not_eq_false] at hBad
        rcases hBad with ⟨⟨hCondPub, hNotNeg⟩, _⟩
        have hGe0 : targetPc ≥ 0 := by omega
        have hCondEq := evalArmCond_public_eq hCondPub rCf rZf
        simp only [stepArm64, hIns, decide_eq_true hGe0, Bool.and_true, true_and]
        by_cases hTaken : evalArmCond cond s₁ = true
        · have hTaken2 : evalArmCond cond s₂ = true := hCondEq ▸ hTaken
          simp only [hTaken, hTaken2, ↓reduceIte]
          exact Or.inr ⟨_, List.Mem.head _, rfl, hH1, hH2, rDit1, rDit2, rGpr, rVec, rCf, rZf⟩
        · have hTakenF1 : evalArmCond cond s₁ = false := Bool.eq_false_iff.mpr hTaken
          have hTakenF2 : evalArmCond cond s₂ = false := hCondEq ▸ hTakenF1
          simp only [hTakenF1, hTakenF2, Bool.false_eq_true, ↓reduceIte]
          exact Or.inr ⟨_, List.Mem.tail _ (List.Mem.head _), rfl, hH1, hH2, rDit1, rDit2, rGpr, rVec, rCf, rZf⟩
    case cbzOrTbz _ => cases hTr
    case udivOrSdiv _ => cases hTr
    case varShiftReg _ => cases hTr
    case regOffsetMem _ => cases hTr

private theorem runArm64_of_halted (prog : List (DecodedInstr Arm64Instr)) (fuel : Nat)
    {s : Arm64State} (hHalt : s.halted = true) :
    runArm64 prog fuel s = (s, []) := by
  cases fuel with
  | zero => rfl
  | succ k => simp [runArm64, hHalt]

private theorem runArm64_invariant_sound {c : FuncContract}
    {prog : List (DecodedInstr Arm64Instr)} {inv : PcMap Arm64AbsState}
    {s₁₀ s₂₀ : Arm64State}
    (hAll : inv.all (fun pc st =>
      match (buildProgMap prog).get pc with
      | none => false
      | some d =>
        match transferArm64Instr c d st with
        | none => false
        | some succs =>
          succs.all (fun (npc, nst) =>
            match inv.get npc with
            | none => false
            | some dstSt => nst.le dstSt)) = true) :
    ∀ (fuel : Nat) {s₁ s₂ : Arm64State} {st : Arm64AbsState},
      inv.get s₁.pc = some st →
      RelArm64 s₁₀ s₂₀ st s₁ s₂ →
      let (s₁f, tr₁) := runArm64 prog fuel s₁
      let (s₂f, tr₂) := runArm64 prog fuel s₂
      tr₁ = tr₂ ∧
      (∀ obs ∈ tr₁, obs.isDoitSafe = true) ∧
      ((s₁f.halted = true ∧ s₂f.halted = true ∧ Arm64ExitHygiene c s₁₀ s₂₀ s₁f s₂f) ∨
       (s₁f.halted = false ∧ s₂f.halted = false))
  | 0, s₁, s₂, st, _, hRel =>
    ⟨rfl, (fun _ h => nomatch h), Or.inr ⟨hRel.2.1, hRel.2.2.1⟩⟩
  | fuel + 1, s₁, s₂, st, hInvPc, hRel => by
    have hPcLt : s₁.pc < 8192 := PcMap.get_some_lt hInvPc
    have hPred := PcMap.all_get hAll hInvPc
    rw [buildProgMap_get_eq prog hPcLt] at hPred
    cases hFind : findInstrAtPc s₁.pc prog with
    | none => simp [hFind] at hPred
    | some d =>
      simp only [hFind] at hPred
      cases hTr : transferArm64Instr c d st with
      | none => simp [hTr] at hPred
      | some succs =>
        simp only [hTr, List.all_eq_true] at hPred
        have hFind2 : findInstrAtPc s₂.pc prog = some d := hRel.1 ▸ hFind
        have hOffEq : s₁.pc = d.offset := (findInstrAtPc_offset hFind).symm
        have hStep := transferArm64Instr_step_sound hRel hOffEq hTr
        rcases stp1 : stepArm64 d s₁ with ⟨s₁', obs₁⟩
        rcases stp2 : stepArm64 d s₂ with ⟨s₂', obs₂⟩
        simp only [stp1, stp2] at hStep
        rcases hStep with ⟨hObsEq, hDoit, hExitOrCont⟩
        simp only [runArm64, hRel.2.1, hRel.2.2.1, Bool.false_eq_true, ↓reduceIte, hFind, hFind2, stp1, stp2]
        rcases hExitOrCont with ⟨hh1', hh2', hHyg⟩ | ⟨nst, hMemSucc, hRel'⟩
        · rw [runArm64_of_halted prog fuel hh1', runArm64_of_halted prog fuel hh2']
          refine ⟨congrArg (· :: []) hObsEq, ?_, Or.inl ⟨hh1', hh2', hHyg⟩⟩
          intro o ho; simp at ho; subst ho; exact hDoit
        · have hSuccOk := hPred (s₁'.pc, nst) hMemSucc
          cases hInvNext : inv.get s₁'.pc with
          | none => simp [hInvNext] at hSuccOk
          | some dstSt =>
            simp only [hInvNext] at hSuccOk
            have hRelDst := RelArm64_mono hRel' hSuccOk
            have ih := runArm64_invariant_sound hAll fuel hInvNext hRelDst
            rcases hr1 : runArm64 prog fuel s₁' with ⟨s₁f, tr₁⟩
            rcases hr2 : runArm64 prog fuel s₂' with ⟨s₂f, tr₂⟩
            simp only [hr1, hr2] at ih
            rcases ih with ⟨hTrEq, hTrDoit, hPost⟩
            refine ⟨by rw [hObsEq, hTrEq], ?_, hPost⟩
            intro o ho
            rcases List.mem_cons.mp ho with rfl | hRest
            · exact hDoit
            · exact hTrDoit o hRest

/-- **3-Way Hardware Constant-Time Noninterference + AAPCS64 ABI Hygiene Soundness (`AArch64`):**
    Whenever `checkArm64ThreeWayNI code c = true`, for ANY two initial machine states `(s₁, s₂)`
    satisfying `Arm64ContractInit c s₁ s₂` and ANY execution fuel `fuel`:
    1. **`PC-NI` & `Mem-NI`:** `tr₁ = tr₂` (every executed PC and `(addr, width)` memory access matches),
    2. **`DOIT-NI`:** Every executed instruction has `obs.isDoitSafe = true`,
    3. **`ABI & Epilogue Zeroization`:** If execution halts (`ret`), both states halt together and
       satisfy `Arm64ExitHygiene c s₁ s₂ s₁f s₂f` (`x19..x30` & `v8..v15` preserved, scratch NEON
       `v0..v7, v16..v31` secret registers wiped, scratch GPRs wiped). -/
theorem checkArm64ThreeWayNI_sound {code : List UInt8} {c : FuncContract}
    (hCheck : checkArm64ThreeWayNI code c = true)
    {s₁ s₂ : Arm64State} (hInit : Arm64ContractInit c s₁ s₂) (fuel : Nat) :
    ∃ prog : List (DecodedInstr Arm64Instr),
      decodeArm64Stream code = some prog ∧
      let (s₁f, tr₁) := runArm64 prog fuel s₁
      let (s₂f, tr₂) := runArm64 prog fuel s₂
      tr₁ = tr₂ ∧
      (∀ obs ∈ tr₁, obs.isDoitSafe = true) ∧
      ((s₁f.halted = true ∧ s₂f.halted = true ∧ Arm64ExitHygiene c s₁ s₂ s₁f s₂f) ∨
       (s₁f.halted = false ∧ s₂f.halted = false)) := by
  unfold checkArm64ThreeWayNI at hCheck
  cases hDec : decodeArm64Stream code with
  | none => simp [hDec] at hCheck
  | some prog =>
    simp only [hDec] at hCheck
    cases prog with
    | nil => simp at hCheck
    | cons d0 ds =>
      cases hInf : inferArm64Invariant (d0 :: ds) c with
      | none => simp [hInf] at hCheck
      | some inv =>
        simp only [hInf, verifyArm64Invariant, Bool.and_eq_true] at hCheck
        rcases hCheck with ⟨hEntry, hAll⟩
        cases hInv0 : inv.get 0 with
        | none => simp [hInv0] at hEntry
        | some st0 =>
          simp only [hInv0] at hEntry
          have hRel0 := RelArm64_mono (RelArm64_init hInit) hEntry
          have hInvS1 : inv.get s₁.pc = some st0 := hInit.1 ▸ hInv0
          exact ⟨d0 :: ds, rfl, runArm64_invariant_sound hAll fuel hInvS1 hRel0⟩


/-! ### Certificate-checked verification: the invariant is supplied, never inferred in the kernel -/

/- `x86_64` check against a supplied invariant: decode, then verify inductiveness. Inference is
    not on the trusted path; `verifyX86Invariant` alone carries soundness. -/


/-- `AArch64` check against a supplied invariant. -/


theorem checkX86WithInv_sound {code : List UInt8} {c : FuncContract} {inv : PcMap X86AbsState}
    (hCheck : checkX86WithInv code c inv = true)
    {s₁ s₂ : X86State} (hInit : X86ContractInit c s₁ s₂) (fuel : Nat) :
    ∃ prog : List (DecodedInstr X86Instr),
      decodeX86Stream code = some prog ∧
      let (s₁f, tr₁) := runX86 prog fuel s₁
      let (s₂f, tr₂) := runX86 prog fuel s₂
      tr₁ = tr₂ ∧
      (∀ obs ∈ tr₁, obs.isDoitSafe = true) ∧
      ((s₁f.halted = true ∧ s₂f.halted = true ∧ X86ExitHygiene c s₁ s₂ s₁f s₂f) ∨
       (s₁f.halted = false ∧ s₂f.halted = false)) := by
  unfold checkX86WithInv at hCheck
  cases hDec : decodeX86Stream code with
  | none => simp [hDec] at hCheck
  | some prog =>
    simp only [hDec] at hCheck
    cases prog with
    | nil => simp at hCheck
    | cons d0 ds =>
      simp only [verifyX86Invariant, Bool.and_eq_true] at hCheck
      rcases hCheck with ⟨hEntry, hAll⟩
      cases hInv0 : inv.get 0 with
      | none => simp [hInv0] at hEntry
      | some st0 =>
        simp only [hInv0] at hEntry
        have hRel0 := RelX86_mono (RelX86_init hInit) hEntry
        have hInvS1 : inv.get s₁.pc = some st0 := hInit.1 ▸ hInv0
        exact ⟨d0 :: ds, rfl, runX86_invariant_sound hInit hAll fuel hInvS1 hRel0⟩

theorem checkArm64WithInv_sound {code : List UInt8} {c : FuncContract} {inv : PcMap Arm64AbsState}
    (hCheck : checkArm64WithInv code c inv = true)
    {s₁ s₂ : Arm64State} (hInit : Arm64ContractInit c s₁ s₂) (fuel : Nat) :
    ∃ prog : List (DecodedInstr Arm64Instr),
      decodeArm64Stream code = some prog ∧
      let (s₁f, tr₁) := runArm64 prog fuel s₁
      let (s₂f, tr₂) := runArm64 prog fuel s₂
      tr₁ = tr₂ ∧
      (∀ obs ∈ tr₁, obs.isDoitSafe = true) ∧
      ((s₁f.halted = true ∧ s₂f.halted = true ∧ Arm64ExitHygiene c s₁ s₂ s₁f s₂f) ∨
       (s₁f.halted = false ∧ s₂f.halted = false)) := by
  unfold checkArm64WithInv at hCheck
  cases hDec : decodeArm64Stream code with
  | none => simp [hDec] at hCheck
  | some prog =>
    simp only [hDec] at hCheck
    cases prog with
    | nil => simp at hCheck
    | cons d0 ds =>
      simp only [verifyArm64Invariant, Bool.and_eq_true] at hCheck
      rcases hCheck with ⟨hEntry, hAll⟩
      cases hInv0 : inv.get 0 with
      | none => simp [hInv0] at hEntry
      | some st0 =>
        simp only [hInv0] at hEntry
        have hRel0 := RelArm64_mono (RelArm64_init hInit) hEntry
        have hInvS1 : inv.get s₁.pc = some st0 := hInit.1 ▸ hInv0
        exact ⟨d0 :: ds, rfl, runArm64_invariant_sound hAll fuel hInvS1 hRel0⟩


/-- Every instruction the decoder returns is at most 15 bytes long. -/
theorem decodeX86InstrAt_byteLen_le (pc : Nat) (bs : List UInt8) (d : DecodedInstr X86Instr)
    (h : decodeX86InstrAt pc bs = some d) : d.byteLen ≤ 15 := by
  unfold decodeX86InstrAt at h
  cases hU : decodeX86InstrAtUncapped pc bs with
  | none => rw [hU] at h; cases h
  | some d' =>
    rw [hU] at h
    by_cases hLe : d'.byteLen ≤ 15
    · simp only [Option.bind_some, hLe, ↓reduceIte] at h
      cases h; exact hLe
    · simp only [Option.bind_some, hLe, ↓reduceIte] at h
      cases h

/-! ## §1. Run laws: one-step unfolding and halting -/

theorem runX86_halted_fst (prog : List (DecodedInstr X86Instr)) (fuel : Nat) (s : X86State)
    (h : s.halted = true) : (runX86 prog fuel s).1 = s := by
  cases fuel with
  | zero => rfl
  | succ k =>
    have e : runX86 prog (k + 1) s = (if s.halted then (s, []) else
        match findInstrAtPc s.pc prog with
        | none => ({ s with halted := true }, [])
        | some d =>
          let (s', obs) := stepX86 d s
          let (sFinal, restObs) := runX86 prog k s'
          (sFinal, obs :: restObs)) := by rfl
    rw [e, h]
    rfl

theorem runX86_step_fst (prog : List (DecodedInstr X86Instr)) (fuel : Nat) (s : X86State)
    (d : DecodedInstr X86Instr) (hh : s.halted = false) (hf : findInstrAtPc s.pc prog = some d) :
    (runX86 prog (fuel + 1) s).1 = (runX86 prog fuel (stepX86 d s).1).1 := by
  have e : runX86 prog (fuel + 1) s = (if s.halted then (s, []) else
      match findInstrAtPc s.pc prog with
      | none => ({ s with halted := true }, [])
      | some d =>
        let (s', obs) := stepX86 d s
        let (sFinal, restObs) := runX86 prog fuel s'
        (sFinal, obs :: restObs)) := by rfl
  rw [e, hh, hf]
  rfl

theorem runArm64_halted_fst (prog : List (DecodedInstr Arm64Instr)) (fuel : Nat) (s : Arm64State)
    (h : s.halted = true) : (runArm64 prog fuel s).1 = s := by
  cases fuel with
  | zero => rfl
  | succ k =>
    have e : runArm64 prog (k + 1) s = (if s.halted then (s, []) else
        match findInstrAtPc s.pc prog with
        | none => ({ s with halted := true }, [])
        | some d =>
          let (s', obs) := stepArm64 d s
          let (sFinal, restObs) := runArm64 prog k s'
          (sFinal, obs :: restObs)) := by rfl
    rw [e, h]
    rfl

theorem runArm64_step_fst (prog : List (DecodedInstr Arm64Instr)) (fuel : Nat) (s : Arm64State)
    (d : DecodedInstr Arm64Instr) (hh : s.halted = false) (hf : findInstrAtPc s.pc prog = some d) :
    (runArm64 prog (fuel + 1) s).1 = (runArm64 prog fuel (stepArm64 d s).1).1 := by
  have e : runArm64 prog (fuel + 1) s = (if s.halted then (s, []) else
      match findInstrAtPc s.pc prog with
      | none => ({ s with halted := true }, [])
      | some d =>
        let (s', obs) := stepArm64 d s
        let (sFinal, restObs) := runArm64 prog fuel s'
        (sFinal, obs :: restObs)) := by rfl
  rw [e, hh, hf]
  rfl

/-! ## §2. Register-bank literals -/

section BankLits
variable {α : Type} (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 v : α)

theorem b16get_0 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 0 = r0 := by rfl
theorem b16get_1 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 1 = r1 := by rfl
theorem b16get_2 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 2 = r2 := by rfl
theorem b16get_3 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 3 = r3 := by rfl
theorem b16get_4 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 4 = r4 := by rfl
theorem b16get_5 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 5 = r5 := by rfl
theorem b16get_6 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 6 = r6 := by rfl
theorem b16get_7 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 7 = r7 := by rfl
theorem b16get_8 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 8 = r8 := by rfl
theorem b16get_9 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 9 = r9 := by rfl
theorem b16get_10 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 10 = r10 := by rfl
theorem b16get_11 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 11 = r11 := by rfl
theorem b16get_12 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 12 = r12 := by rfl
theorem b16get_13 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 13 = r13 := by rfl
theorem b16get_14 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 14 = r14 := by rfl
theorem b16get_15 : Bank16.get (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 15 = r15 := by rfl
theorem b16set_0 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 0 v = Bank16.mk v r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 := by rfl
theorem b16set_1 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 1 v = Bank16.mk r0 v r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 := by rfl
theorem b16set_2 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 2 v = Bank16.mk r0 r1 v r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 := by rfl
theorem b16set_3 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 3 v = Bank16.mk r0 r1 r2 v r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 := by rfl
theorem b16set_4 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 4 v = Bank16.mk r0 r1 r2 r3 v r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 := by rfl
theorem b16set_5 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 5 v = Bank16.mk r0 r1 r2 r3 r4 v r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 := by rfl
theorem b16set_6 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 6 v = Bank16.mk r0 r1 r2 r3 r4 r5 v r7 r8 r9 r10 r11 r12 r13 r14 r15 := by rfl
theorem b16set_7 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 7 v = Bank16.mk r0 r1 r2 r3 r4 r5 r6 v r8 r9 r10 r11 r12 r13 r14 r15 := by rfl
theorem b16set_8 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 8 v = Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 v r9 r10 r11 r12 r13 r14 r15 := by rfl
theorem b16set_9 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 9 v = Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 v r10 r11 r12 r13 r14 r15 := by rfl
theorem b16set_10 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 10 v = Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 v r11 r12 r13 r14 r15 := by rfl
theorem b16set_11 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 11 v = Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 v r12 r13 r14 r15 := by rfl
theorem b16set_12 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 12 v = Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 v r13 r14 r15 := by rfl
theorem b16set_13 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 13 v = Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 v r14 r15 := by rfl
theorem b16set_14 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 14 v = Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 v r15 := by rfl
theorem b16set_15 : Bank16.set (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) 15 v = Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 v := by rfl
end BankLits

/- AArch64 register read with `x31` as the zero register (the bank-level form of `getArmGpr`). -/


/-- AArch64 register write discarding writes to `x31` (the bank-level form of `setArmGpr`). -/


theorem armGet_31 (g : Bank32 UInt64) : armGet g 31 = 0 := by rfl
theorem armSet_31 (g : Bank32 UInt64) (v : UInt64) : armSet g 31 v = g := by rfl

section ArmBankLits
variable (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 v : UInt64) (hi : Bank16 UInt64)

theorem armGet_0 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 0 = r0 := by rfl
theorem armGet_1 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 1 = r1 := by rfl
theorem armGet_2 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 2 = r2 := by rfl
theorem armGet_3 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 3 = r3 := by rfl
theorem armGet_4 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 4 = r4 := by rfl
theorem armGet_5 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 5 = r5 := by rfl
theorem armGet_6 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 6 = r6 := by rfl
theorem armGet_7 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 7 = r7 := by rfl
theorem armGet_8 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 8 = r8 := by rfl
theorem armGet_9 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 9 = r9 := by rfl
theorem armGet_10 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 10 = r10 := by rfl
theorem armGet_11 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 11 = r11 := by rfl
theorem armGet_12 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 12 = r12 := by rfl
theorem armGet_13 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 13 = r13 := by rfl
theorem armGet_14 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 14 = r14 := by rfl
theorem armGet_15 : armGet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 15 = r15 := by rfl
theorem armSet_0 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 0 v = Bank32.mk (Bank16.mk v r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi := by rfl
theorem armSet_1 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 1 v = Bank32.mk (Bank16.mk r0 v r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi := by rfl
theorem armSet_2 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 2 v = Bank32.mk (Bank16.mk r0 r1 v r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi := by rfl
theorem armSet_3 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 3 v = Bank32.mk (Bank16.mk r0 r1 r2 v r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi := by rfl
theorem armSet_4 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 4 v = Bank32.mk (Bank16.mk r0 r1 r2 r3 v r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi := by rfl
theorem armSet_5 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 5 v = Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 v r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi := by rfl
theorem armSet_6 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 6 v = Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 v r7 r8 r9 r10 r11 r12 r13 r14 r15) hi := by rfl
theorem armSet_7 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 7 v = Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 v r8 r9 r10 r11 r12 r13 r14 r15) hi := by rfl
theorem armSet_8 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 8 v = Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 v r9 r10 r11 r12 r13 r14 r15) hi := by rfl
theorem armSet_9 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 9 v = Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 v r10 r11 r12 r13 r14 r15) hi := by rfl
theorem armSet_10 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 10 v = Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 v r11 r12 r13 r14 r15) hi := by rfl
theorem armSet_11 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 11 v = Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 v r12 r13 r14 r15) hi := by rfl
theorem armSet_12 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 12 v = Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 v r13 r14 r15) hi := by rfl
theorem armSet_13 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 13 v = Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 v r14 r15) hi := by rfl
theorem armSet_14 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 14 v = Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 v r15) hi := by rfl
theorem armSet_15 : armSet (Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15) hi) 15 v = Bank32.mk (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 v) hi := by rfl
end ArmBankLits

/-! ## §3. `x86_64` step lemmas, one per instruction form, on a state given by its fields -/

/-- Program counter after a conditional jump. -/


theorem jccPc_false (tgt : Int) (next : Nat) : jccPc false tgt next = next := by rfl
theorem jccPc_true_5 (next : Nat) : jccPc true 5 next = 5 := by rfl
theorem jccPc_true_0 (next : Nat) : jccPc true 0 next = 0 := by rfl
theorem maskGprWidth_true (v : UInt64) : maskGprWidth true v = v := by rfl

section X86Steps
variable (off len pc : Nat) (g : Bank16 UInt64) (y : Bank16 Vec256) (cf o zf dy : Bool)
  (m : UInt64 → UInt8)

theorem stepX86_load64 (dst base : Nat) (disp : UInt64) :
    (stepX86 ⟨off, len, .loadGpr 8 true dst (.baseDisp base disp)⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (readMem64 m (g.get base + disp)), y, cf, o, zf, dy, false, m⟩ := by rfl

theorem stepX86_load8 (dst base : Nat) (disp : UInt64) :
    (stepX86 ⟨off, len, .loadGpr 1 false dst (.baseDisp base disp)⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (maskGprWidth false (m (g.get base + disp)).toUInt64), y, cf, o, zf, dy, false, m⟩ := by
  rfl

theorem stepX86_store8 (src base : Nat) (disp : UInt64) :
    (stepX86 ⟨off, len, .storeGpr 1 src (.baseDisp base disp)⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g, y, cf, o, zf, dy, false, writeMem8 m (g.get base + disp) (g.get src).toUInt8⟩ := by rfl

theorem stepX86_xorLoad64 (dst base : Nat) (disp : UInt64) :
    (stepX86 ⟨off, len, .aluLoad64 .xorOp dst (.baseDisp base disp)⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (g.get dst ^^^ readMem64 m (g.get base + disp)), y, false, false,
        (g.get dst ^^^ readMem64 m (g.get base + disp)) == 0, dy, false, m⟩ := by rfl

theorem stepX86_xorRR (is64 : Bool) (dst src : Nat) :
    (stepX86 ⟨off, len, .aluRegReg .xorOp is64 dst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (maskGprWidth is64 (g.get dst ^^^ g.get src)), y, false, false,
        maskGprWidth is64 (g.get dst ^^^ g.get src) == 0, dy, false, m⟩ := by rfl

theorem stepX86_orRR (is64 : Bool) (dst src : Nat) :
    (stepX86 ⟨off, len, .aluRegReg .orOp is64 dst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (maskGprWidth is64 (g.get dst ||| g.get src)), y, false, false,
        maskGprWidth is64 (g.get dst ||| g.get src) == 0, dy, false, m⟩ := by rfl

theorem stepX86_xorImm (is64 : Bool) (dst : Nat) (imm : UInt64) :
    (stepX86 ⟨off, len, .aluImm .xorOp is64 dst imm⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (maskGprWidth is64 (g.get dst ^^^ imm)), y, false, false,
        maskGprWidth is64 (g.get dst ^^^ imm) == 0, dy, false, m⟩ := by rfl

theorem stepX86_subImm32 (dst : Nat) (imm : UInt64) :
    (stepX86 ⟨off, len, .aluImm .sub false dst imm⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len,
        g.set dst (maskGprWidth false (UInt64.ofNat (((maskGprWidth false (g.get dst)).toNat + 0x100000000 -
          (maskGprWidth false imm).toNat) % 0x100000000))), y,
        decide ((maskGprWidth false (g.get dst)).toNat < (maskGprWidth false imm).toNat),
        evalX86AluOf .sub false (g.get dst) imm cf,
        maskGprWidth false (UInt64.ofNat (((maskGprWidth false (g.get dst)).toNat + 0x100000000 -
          (maskGprWidth false imm).toNat) % 0x100000000)) == 0, dy, false, m⟩ := by rfl

theorem stepX86_addRR64 (dst src : Nat) :
    (stepX86 ⟨off, len, .aluRegReg .add true dst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len,
        g.set dst (UInt64.ofNat (((g.get dst).toNat + (g.get src).toNat) % 0x10000000000000000)), y,
        decide ((g.get dst).toNat + (g.get src).toNat ≥ 0x10000000000000000),
        evalX86AluOf .add true (g.get dst) (g.get src) cf,
        UInt64.ofNat (((g.get dst).toNat + (g.get src).toNat) % 0x10000000000000000) == 0,
        dy, false, m⟩ := by rfl

theorem stepX86_subRR64 (dst src : Nat) :
    (stepX86 ⟨off, len, .aluRegReg .sub true dst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len,
        g.set dst (UInt64.ofNat (((g.get dst).toNat + 0x10000000000000000 - (g.get src).toNat) %
          0x10000000000000000)), y,
        decide ((g.get dst).toNat < (g.get src).toNat),
        evalX86AluOf .sub true (g.get dst) (g.get src) cf,
        UInt64.ofNat (((g.get dst).toNat + 0x10000000000000000 - (g.get src).toNat) %
          0x10000000000000000) == 0, dy, false, m⟩ := by rfl

theorem stepX86_sbbRR (is64 : Bool) (dst src : Nat) :
    (stepX86 ⟨off, len, .aluRegReg .sbb is64 dst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (evalX86Alu .sbb is64 (g.get dst) (g.get src) cf).1, y,
        (evalX86Alu .sbb is64 (g.get dst) (g.get src) cf).2.1,
        evalX86AluOf .sbb is64 (g.get dst) (g.get src) cf,
        (evalX86Alu .sbb is64 (g.get dst) (g.get src) cf).2.2, dy, false, m⟩ := by rfl

theorem stepX86_andRR (is64 : Bool) (dst src : Nat) :
    (stepX86 ⟨off, len, .aluRegReg .andOp is64 dst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (maskGprWidth is64 (g.get dst &&& g.get src)), y, false, false,
        maskGprWidth is64 (g.get dst &&& g.get src) == 0, dy, false, m⟩ := by rfl

theorem stepX86_movImm (is64 : Bool) (dst : Nat) (imm : UInt64) :
    (stepX86 ⟨off, len, .movImm is64 dst imm⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (maskGprWidth is64 imm), y, cf, o, zf, dy, false, m⟩ := by rfl

theorem stepX86_mulx (hiDst loDst src : Nat) :
    (stepX86 ⟨off, len, .mulx hiDst loDst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len,
        (g.set loDst (UInt64.ofNat (((g.get 2).toNat * (g.get src).toNat) % 0x10000000000000000))).set hiDst
          (UInt64.ofNat (((g.get 2).toNat * (g.get src).toNat) / 0x10000000000000000)),
        y, cf, o, zf, dy, false, m⟩ := by rfl

theorem stepX86_shl64 (dst cnt : Nat) :
    (stepX86 ⟨off, len, .shiftImm .shl true dst cnt⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (evalX86Shift .shl true (g.get dst) cnt cf o zf).1, y,
        (evalX86Shift .shl true (g.get dst) cnt cf o zf).2.1,
        (evalX86Shift .shl true (g.get dst) cnt cf o zf).2.2.1,
        (evalX86Shift .shl true (g.get dst) cnt cf o zf).2.2.2,
        dy, false, m⟩ := by rfl

theorem stepX86_movRR (is64 : Bool) (dst src : Nat) :
    (stepX86 ⟨off, len, .movRegReg is64 dst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (maskGprWidth is64 (g.get src)), y, cf, o, zf, dy, false, m⟩ := by rfl

theorem stepX86_neg (is64 : Bool) (dst : Nat) :
    (stepX86 ⟨off, len, .negReg is64 dst⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (maskGprWidth is64 (0 - maskGprWidth is64 (g.get dst))), y,
        maskGprWidth is64 (g.get dst) != 0,
        maskGprWidth is64 (g.get dst) == (if is64 then 0x8000000000000000 else 0x80000000),
        maskGprWidth is64 (0 - maskGprWidth is64 (g.get dst)) == 0, dy, false, m⟩ := by rfl

theorem stepX86_shr64 (dst cnt : Nat) :
    (stepX86 ⟨off, len, .shiftImm .shr true dst cnt⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (evalX86Shift .shr true (g.get dst) cnt cf o zf).1, y,
        (evalX86Shift .shr true (g.get dst) cnt cf o zf).2.1,
        (evalX86Shift .shr true (g.get dst) cnt cf o zf).2.2.1,
        (evalX86Shift .shr true (g.get dst) cnt cf o zf).2.2.2,
        dy, false, m⟩ := by rfl

theorem stepX86_shr32 (dst cnt : Nat) :
    (stepX86 ⟨off, len, .shiftImm .shr false dst cnt⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (evalX86Shift .shr false (g.get dst) cnt cf o zf).1, y,
        (evalX86Shift .shr false (g.get dst) cnt cf o zf).2.1,
        (evalX86Shift .shr false (g.get dst) cnt cf o zf).2.2.1,
        (evalX86Shift .shr false (g.get dst) cnt cf o zf).2.2.2,
        dy, false, m⟩ := by rfl

theorem stepX86_inc (is64 : Bool) (dst : Nat) :
    (stepX86 ⟨off, len, .incDec true is64 dst⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (maskGprWidth is64 (maskGprWidth is64 (g.get dst) + 1)), y, cf,
        evalX86IncDecOf true is64 (g.get dst),
        maskGprWidth is64 (maskGprWidth is64 (g.get dst) + 1) == 0, dy, false, m⟩ := by rfl

theorem stepX86_dec (is64 : Bool) (dst : Nat) :
    (stepX86 ⟨off, len, .incDec false is64 dst⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (maskGprWidth is64 (maskGprWidth is64 (g.get dst) + (0 - 1))), y, cf,
        evalX86IncDecOf false is64 (g.get dst),
        maskGprWidth is64 (maskGprWidth is64 (g.get dst) + (0 - 1)) == 0, dy, false, m⟩ := by rfl

theorem stepX86_jnz (tgt : Int) :
    (stepX86 ⟨off, len, .jcc 5 tgt⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨jccPc (!zf) tgt (off + len), g, y, cf, o, zf, dy, false, m⟩ := by rfl

theorem stepX86_mfence :
    (stepX86 ⟨off, len, .mfence⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g, y, cf, o, zf, dy, false, m⟩ := by rfl

theorem stepX86_ret :
    (stepX86 ⟨off, len, .ret⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨(readMem64 m (g.get 4)).toNat, g.set 4 (g.get 4 + 8), y, cf, o, zf, dy, true, m⟩ := by rfl

end X86Steps

/-! ## §4. `AArch64` step lemmas -/

section Arm64Steps
variable (off len pc : Nat) (g : Bank32 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool)
  (m : UInt64 → UInt8)

theorem stepArm64_ldp (rt1 rt2 rn : Nat) (disp : UInt64) :
    (stepArm64 ⟨off, len, .ldp64 rt1 rt2 rn disp⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet (armSet g rt1 (readMem64 m (armGet g rn + disp))) rt2
        (readMem64 m (armGet g rn + disp + 8)), v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_eorRR (rd rn rm : Nat) :
    (stepArm64 ⟨off, len, .aluReg .eor true rd rn rm 0 0⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (armGet g rn ^^^ armGet g rm), v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_orrRR (rd rn rm : Nat) :
    (stepArm64 ⟨off, len, .aluReg .orr true rd rn rm 0 0⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (armGet g rn ||| armGet g rm), v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_subRR (rd rn rm : Nat) :
    (stepArm64 ⟨off, len, .aluReg .sub true rd rn rm 0 0⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (UInt64.ofNat (((armGet g rn).toNat + 0x10000000000000000 - (armGet g rm).toNat) %
        0x10000000000000000)), v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_lsr64 (rd rn immr : Nat) :
    (stepArm64 ⟨off, len, .ubfm true rd rn immr 63⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (armGet g rn >>> UInt64.ofNat immr), v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_eorImm (rd rn : Nat) (imm : UInt64) :
    (stepArm64 ⟨off, len, .aluImm .eor true rd rn imm⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (armGet g rn ^^^ imm), v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_subsImm (rd rn : Nat) (imm : UInt64) :
    (stepArm64 ⟨off, len, .aluImm .subs true rd rn imm⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (UInt64.ofNat (((armGet g rn).toNat + 0x10000000000000000 - imm.toNat) %
          0x10000000000000000)), v, decide ((armGet g rn).toNat ≥ imm.toNat),
        UInt64.ofNat (((armGet g rn).toNat + 0x10000000000000000 - imm.toNat) % 0x10000000000000000) == 0,
        dit, false, m⟩ := by rfl

theorem stepArm64_mul (rd rn rm : Nat) :
    (stepArm64 ⟨off, len, .mulOp false rd rn rm⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (UInt64.ofNat (((armGet g rn).toNat * (armGet g rm).toNat) %
        0x10000000000000000)), v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_umulh (rd rn rm : Nat) :
    (stepArm64 ⟨off, len, .mulOp true rd rn rm⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (UInt64.ofNat (((armGet g rn).toNat * (armGet g rm).toNat) /
        0x10000000000000000)), v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_lsl32 (rd rn : Nat) :
    (stepArm64 ⟨off, len, .ubfm true rd rn 32 31⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (armGet g rn <<< UInt64.ofNat (64 - 32)), v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_andImm (rd rn : Nat) (imm : UInt64) :
    (stepArm64 ⟨off, len, .aluImm .andOp true rd rn imm⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (armGet g rn &&& imm), v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_andRR (rd rn rm : Nat) :
    (stepArm64 ⟨off, len, .aluReg .andOp true rd rn rm 0 0⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (armGet g rn &&& armGet g rm), v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_movn32 (rd imm16 sh : Nat) :
    (stepArm64 ⟨off, len, .movWide true false rd imm16 sh⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (maskGprWidth false (~~~(UInt64.ofNat imm16 <<< UInt64.ofNat sh))),
        v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_addRR (rd rn rm : Nat) :
    (stepArm64 ⟨off, len, .aluReg .add true rd rn rm 0 0⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (UInt64.ofNat (((armGet g rn).toNat + (armGet g rm).toNat) %
        0x10000000000000000)), v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_addsRR (rd rn rm : Nat) :
    (stepArm64 ⟨off, len, .aluReg .adds true rd rn rm 0 0⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (UInt64.ofNat (((armGet g rn).toNat + (armGet g rm).toNat) %
          0x10000000000000000)), v,
        decide ((armGet g rn).toNat + (armGet g rm).toNat ≥ 0x10000000000000000),
        UInt64.ofNat (((armGet g rn).toNat + (armGet g rm).toNat) % 0x10000000000000000) == 0,
        dit, false, m⟩ := by rfl

theorem stepArm64_subsRR (rd rn rm : Nat) :
    (stepArm64 ⟨off, len, .aluReg .subs true rd rn rm 0 0⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (UInt64.ofNat (((armGet g rn).toNat + 0x10000000000000000 -
          (armGet g rm).toNat) % 0x10000000000000000)), v,
        decide ((armGet g rn).toNat ≥ (armGet g rm).toNat),
        UInt64.ofNat (((armGet g rn).toNat + 0x10000000000000000 - (armGet g rm).toNat) %
          0x10000000000000000) == 0, dit, false, m⟩ := by rfl

theorem stepArm64_adcRR (rd rn rm : Nat) :
    (stepArm64 ⟨off, len, .aluReg .adc true rd rn rm 0 0⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (UInt64.ofNat (((armGet g rn).toNat + (armGet g rm).toNat +
        (if cf then 1 else 0)) % 0x10000000000000000)), v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_sbcRR (rd rn rm : Nat) :
    (stepArm64 ⟨off, len, .aluReg .sbc true rd rn rm 0 0⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (UInt64.ofNat (((armGet g rn).toNat + 0x10000000000000000 * 2 -
        (armGet g rm).toNat - (if cf then 0 else 1)) % 0x10000000000000000)),
        v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_movz (rd imm16 sh : Nat) :
    (stepArm64 ⟨off, len, .movWide false true rd imm16 sh⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rd (UInt64.ofNat imm16 <<< UInt64.ofNat sh), v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_strbPost (rt rn : Nat) (post : UInt64) :
    (stepArm64 ⟨off, len, .strbPost rt rn post⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, armSet g rn (armGet g rn + post), v, cf, zf, dit, false,
        writeMem8 m (armGet g rn) (armGet g rt).toUInt8⟩ := by rfl

theorem stepArm64_bne (tgt : Int) :
    (stepArm64 ⟨off, len, .bCond 1 tgt⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨jccPc (!zf) tgt (off + 4), g, v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_dmb :
    (stepArm64 ⟨off, len, .dmbIsh⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨off + 4, g, v, cf, zf, dit, false, m⟩ := by rfl

theorem stepArm64_ret :
    (stepArm64 ⟨off, len, .ret⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩).1 =
      ⟨pc, g, v, cf, zf, dit, true, m⟩ := by rfl

end Arm64Steps

/-! ## §5. Word and byte arithmetic used by the specifications -/

theorem u64_eq_of_toNat {a b : UInt64} (h : a.toNat = b.toNat) : a = b :=
  UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

theorem u8_eq_of_toNat {a b : UInt8} (h : a.toNat = b.toNat) : a = b :=
  UInt8.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq h)

theorem mask32_xor_self (x : UInt64) : maskGprWidth false (x ^^^ x) = 0 := by
  rw [UInt64.xor_self]; decide

theorem u64_zero_beq_zero : ((0 : UInt64) == 0) = true := by decide

theorem u64_shl_zero_zero : UInt64.ofNat 0 <<< UInt64.ofNat 0 = 0 := by decide

theorem u64_zero_toUInt8 : (0 : UInt64).toUInt8 = 0 := by decide

/-- `((x | -x) >> 63) ^ 1` is the zero test of a 64-bit word. -/
theorem zeroTest64 (x : UInt64) :
    ((x ||| (0 - x)) >>> UInt64.ofNat 63) ^^^ 1 = if x = 0 then 1 else 0 := by
  if hx : x = 0 then
    subst hx; rw [ite_eq_left rfl]; decide
  else
    rw [ite_eq_right hx]
    have hpos : 0 < x.toNat := Nat.pos_of_ne_zero (fun h => hx (u64_eq_of_toNat h))
    have hlt : x.toNat < 18446744073709551616 := x.toNat_lt
    have hneg : (0 - x).toNat = 18446744073709551616 - x.toNat := by
      have h0 : (0 : UInt64).toNat = 0 := rfl
      have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
      rw [UInt64.toNat_sub, h0, h64]
      omega
    have hl : x.toNat ≤ x.toNat ||| (0 - x).toNat := Nat.left_le_or
    have hr : (0 - x).toNat ≤ x.toNat ||| (0 - x).toNat := Nat.right_le_or
    have hor : (x ||| (0 - x)).toNat = x.toNat ||| (0 - x).toNat := UInt64.toNat_or _ _
    have horLt : (x ||| (0 - x)).toNat < 18446744073709551616 := (x ||| (0 - x)).toNat_lt
    have hsh : (x ||| (0 - x)) >>> UInt64.ofNat 63 = 1 := by
      apply u64_eq_of_toNat
      have h63 : (UInt64.ofNat 63).toNat % 64 = 63 := rfl
      rw [UInt64.toNat_shiftRight, h63, Nat.shiftRight_eq_div_pow]
      show (x ||| (0 - x)).toNat / 9223372036854775808 = 1
      omega
    rw [hsh]; decide

theorem zeroTest64_masked (x : UInt64) :
    maskGprWidth false (((x ||| (0 - x)) >>> UInt64.ofNat 63) ^^^ 1) = if x = 0 then 1 else 0 := by
  rw [zeroTest64]
  if hx : x = 0 then rw [ite_eq_left hx]; decide else rw [ite_eq_right hx]; decide

theorem or_shl_eq_add (x y i : Nat) (hx : x < 2 ^ i) : x ||| y <<< i = x + y * 2 ^ i := by
  rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq, Nat.add_comm]

theorem byte_shl_toNat (b : UInt8) (c : UInt64) (n : Nat) (hc : c.toNat = n) (hn : n ≤ 56) :
    (b.toUInt64 <<< c).toNat = b.toNat <<< n := by
  have hb := b.toNat_lt
  have hlt : b.toNat <<< n < 2 ^ 64 := by
    rw [Nat.shiftLeft_eq]
    calc b.toNat * 2 ^ n < 2 ^ 8 * 2 ^ n := Nat.mul_lt_mul_of_pos_right hb (Nat.two_pow_pos n)
      _ = 2 ^ (8 + n) := (Nat.pow_add 2 8 n).symm
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  rw [UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, hc, Nat.mod_eq_of_lt (show n < 64 by omega),
    Nat.mod_eq_of_lt hlt]

/-- Little-endian value of the eight bytes read by `readMem64`. -/
theorem readMem64_toNat (m : UInt64 → UInt8) (a : UInt64) :
    (readMem64 m a).toNat =
      (m a).toNat + (m (a + 1)).toNat * 256 + (m (a + 2)).toNat * 65536 +
      (m (a + 3)).toNat * 16777216 + (m (a + 4)).toNat * 4294967296 +
      (m (a + 5)).toNat * 1099511627776 + (m (a + 6)).toNat * 281474976710656 +
      (m (a + 7)).toNat * 72057594037927936 := by
  have b0 : (m a).toNat < 256 := (m a).toNat_lt
  have b1 : (m (a + 1)).toNat < 256 := (m (a + 1)).toNat_lt
  have b2 : (m (a + 2)).toNat < 256 := (m (a + 2)).toNat_lt
  have b3 : (m (a + 3)).toNat < 256 := (m (a + 3)).toNat_lt
  have b4 : (m (a + 4)).toNat < 256 := (m (a + 4)).toNat_lt
  have b5 : (m (a + 5)).toNat < 256 := (m (a + 5)).toNat_lt
  have b6 : (m (a + 6)).toNat < 256 := (m (a + 6)).toNat_lt
  unfold readMem64
  rw [UInt64.toNat_or, UInt64.toNat_or, UInt64.toNat_or, UInt64.toNat_or, UInt64.toNat_or,
    UInt64.toNat_or, UInt64.toNat_or, UInt8.toNat_toUInt64,
    byte_shl_toNat _ 8 8 rfl (by decide), byte_shl_toNat _ 16 16 rfl (by decide),
    byte_shl_toNat _ 24 24 rfl (by decide), byte_shl_toNat _ 32 32 rfl (by decide),
    byte_shl_toNat _ 40 40 rfl (by decide), byte_shl_toNat _ 48 48 rfl (by decide),
    byte_shl_toNat _ 56 56 rfl (by decide)]
  have e1 := or_shl_eq_add (m a).toNat (m (a + 1)).toNat 8 b0
  rw [e1]
  have e2 := or_shl_eq_add ((m a).toNat + (m (a + 1)).toNat * 2 ^ 8) (m (a + 2)).toNat 16
    (by show _ < 65536; omega)
  rw [e2]
  have e3 := or_shl_eq_add ((m a).toNat + (m (a + 1)).toNat * 2 ^ 8 + (m (a + 2)).toNat * 2 ^ 16)
    (m (a + 3)).toNat 24 (by show _ + _ * 256 + _ * 65536 < 16777216; omega)
  rw [e3]
  have e4 := or_shl_eq_add ((m a).toNat + (m (a + 1)).toNat * 2 ^ 8 + (m (a + 2)).toNat * 2 ^ 16 +
    (m (a + 3)).toNat * 2 ^ 24) (m (a + 4)).toNat 32
    (by show _ + _ * 256 + _ * 65536 + _ * 16777216 < 4294967296; omega)
  rw [e4]
  have e5 := or_shl_eq_add ((m a).toNat + (m (a + 1)).toNat * 2 ^ 8 + (m (a + 2)).toNat * 2 ^ 16 +
    (m (a + 3)).toNat * 2 ^ 24 + (m (a + 4)).toNat * 2 ^ 32) (m (a + 5)).toNat 40
    (by show _ + _ * 256 + _ * 65536 + _ * 16777216 + _ * 4294967296 < 1099511627776; omega)
  rw [e5]
  have e6 := or_shl_eq_add ((m a).toNat + (m (a + 1)).toNat * 2 ^ 8 + (m (a + 2)).toNat * 2 ^ 16 +
    (m (a + 3)).toNat * 2 ^ 24 + (m (a + 4)).toNat * 2 ^ 32 + (m (a + 5)).toNat * 2 ^ 40)
    (m (a + 6)).toNat 48
    (by show _ + _ * 256 + _ * 65536 + _ * 16777216 + _ * 4294967296 + _ * 1099511627776 <
          281474976710656; omega)
  rw [e6]
  have e7 := or_shl_eq_add ((m a).toNat + (m (a + 1)).toNat * 2 ^ 8 + (m (a + 2)).toNat * 2 ^ 16 +
    (m (a + 3)).toNat * 2 ^ 24 + (m (a + 4)).toNat * 2 ^ 32 + (m (a + 5)).toNat * 2 ^ 40 +
    (m (a + 6)).toNat * 2 ^ 48) (m (a + 7)).toNat 56
    (by show _ + _ * 256 + _ * 65536 + _ * 16777216 + _ * 4294967296 + _ * 1099511627776 +
          _ * 281474976710656 < 72057594037927936; omega)
  rw [e7]

/-- `readMem64` is injective on the eight bytes it reads. -/
theorem readMem64_inj {m m' : UInt64 → UInt8} {a b : UInt64} (h : readMem64 m a = readMem64 m' b) :
    m a = m' b ∧ m (a + 1) = m' (b + 1) ∧ m (a + 2) = m' (b + 2) ∧ m (a + 3) = m' (b + 3) ∧
    m (a + 4) = m' (b + 4) ∧ m (a + 5) = m' (b + 5) ∧ m (a + 6) = m' (b + 6) ∧
    m (a + 7) = m' (b + 7) := by
  have hn := congrArg UInt64.toNat h
  rw [readMem64_toNat, readMem64_toNat] at hn
  have a0 : (m a).toNat < 256 := (m a).toNat_lt
  have a1 : (m (a + 1)).toNat < 256 := (m (a + 1)).toNat_lt
  have a2 : (m (a + 2)).toNat < 256 := (m (a + 2)).toNat_lt
  have a3 : (m (a + 3)).toNat < 256 := (m (a + 3)).toNat_lt
  have a4 : (m (a + 4)).toNat < 256 := (m (a + 4)).toNat_lt
  have a5 : (m (a + 5)).toNat < 256 := (m (a + 5)).toNat_lt
  have a6 : (m (a + 6)).toNat < 256 := (m (a + 6)).toNat_lt
  have a7 : (m (a + 7)).toNat < 256 := (m (a + 7)).toNat_lt
  have c0 : (m' b).toNat < 256 := (m' b).toNat_lt
  have c1 : (m' (b + 1)).toNat < 256 := (m' (b + 1)).toNat_lt
  have c2 : (m' (b + 2)).toNat < 256 := (m' (b + 2)).toNat_lt
  have c3 : (m' (b + 3)).toNat < 256 := (m' (b + 3)).toNat_lt
  have c4 : (m' (b + 4)).toNat < 256 := (m' (b + 4)).toNat_lt
  have c5 : (m' (b + 5)).toNat < 256 := (m' (b + 5)).toNat_lt
  have c6 : (m' (b + 6)).toNat < 256 := (m' (b + 6)).toNat_lt
  have c7 : (m' (b + 7)).toNat < 256 := (m' (b + 7)).toNat_lt
  exact ⟨u8_eq_of_toNat (by omega), u8_eq_of_toNat (by omega), u8_eq_of_toNat (by omega),
    u8_eq_of_toNat (by omega), u8_eq_of_toNat (by omega), u8_eq_of_toNat (by omega),
    u8_eq_of_toNat (by omega), u8_eq_of_toNat (by omega)⟩

theorem addr_split (a : UInt64) (d j : Nat) :
    a + UInt64.ofNat d + UInt64.ofNat j = a + UInt64.ofNat (d + j) := by
  rw [UInt64.add_assoc, ← UInt64.ofNat_add]

theorem readMem64_eq_iff (m : UInt64 → UInt8) (a b : UInt64) :
    readMem64 m a = readMem64 m b ↔
      ∀ j : Nat, j < 8 → m (a + UInt64.ofNat j) = m (b + UInt64.ofNat j) := by
  have e0 : ∀ x : UInt64, x + UInt64.ofNat 0 = x := fun x => UInt64.add_zero x
  constructor
  · intro h
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := readMem64_inj h
    intro j hj
    match j, hj with
    | 0, _ => rw [e0, e0]; exact h0
    | 1, _ => exact h1
    | 2, _ => exact h2
    | 3, _ => exact h3
    | 4, _ => exact h4
    | 5, _ => exact h5
    | 6, _ => exact h6
    | 7, _ => exact h7
    | n + 8, hn => exact absurd hn (by omega)
  · intro h
    have h0 : m a = m b := by
      have := h 0 (by decide)
      rw [e0, e0] at this
      exact this
    have h1 : m (a + 1) = m (b + 1) := h 1 (by decide)
    have h2 : m (a + 2) = m (b + 2) := h 2 (by decide)
    have h3 : m (a + 3) = m (b + 3) := h 3 (by decide)
    have h4 : m (a + 4) = m (b + 4) := h 4 (by decide)
    have h5 : m (a + 5) = m (b + 5) := h 5 (by decide)
    have h6 : m (a + 6) = m (b + 6) := h 6 (by decide)
    have h7 : m (a + 7) = m (b + 7) := h 7 (by decide)
    unfold readMem64
    rw [h0, h1, h2, h3, h4, h5, h6, h7]

theorem block_of_bytes (m : UInt64 → UInt8) (a b : UInt64) (n d : Nat)
    (h : ∀ i : Nat, i < n → m (a + UInt64.ofNat i) = m (b + UInt64.ofNat i)) (hd : d + 8 ≤ n) :
    readMem64 m (a + UInt64.ofNat d) = readMem64 m (b + UInt64.ofNat d) :=
  (readMem64_eq_iff _ _ _).mpr (fun j hj => by
    rw [addr_split, addr_split]; exact h (d + j) (by omega))

theorem bytes_of_block (m : UInt64 → UInt8) (a b : UInt64) (d : Nat)
    (h : readMem64 m (a + UInt64.ofNat d) = readMem64 m (b + UInt64.ofNat d))
    (i : Nat) (h1 : d ≤ i) (h2 : i < d + 8) :
    m (a + UInt64.ofNat i) = m (b + UInt64.ofNat i) := by
  have := (readMem64_eq_iff _ _ _).mp h (i - d) (by omega)
  rw [addr_split, addr_split, show d + (i - d) = i from by omega] at this
  exact this

/-- The OR of the four XOR-ed 64-bit words vanishes exactly when the two 32-byte buffers agree. -/
theorem xorOr4_eq_zero_iff (m : UInt64 → UInt8) (a b a0 a1 a2 a3 b0 b1 b2 b3 : UInt64)
    (ha0 : a0 = a + UInt64.ofNat 0) (ha1 : a1 = a + UInt64.ofNat 8)
    (ha2 : a2 = a + UInt64.ofNat 16) (ha3 : a3 = a + UInt64.ofNat 24)
    (hb0 : b0 = b + UInt64.ofNat 0) (hb1 : b1 = b + UInt64.ofNat 8)
    (hb2 : b2 = b + UInt64.ofNat 16) (hb3 : b3 = b + UInt64.ofNat 24) :
    (readMem64 m a0 ^^^ readMem64 m b0 ||| readMem64 m a1 ^^^ readMem64 m b1) |||
      (readMem64 m a2 ^^^ readMem64 m b2 ||| readMem64 m a3 ^^^ readMem64 m b3) = 0 ↔
    ∀ i : Nat, i < 32 → m (a + UInt64.ofNat i) = m (b + UInt64.ofNat i) := by
  subst ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
  rw [UInt64.or_eq_zero_iff, UInt64.or_eq_zero_iff, UInt64.or_eq_zero_iff,
    UInt64.xor_eq_zero_iff, UInt64.xor_eq_zero_iff, UInt64.xor_eq_zero_iff, UInt64.xor_eq_zero_iff]
  constructor
  · intro ⟨⟨h0, h1⟩, h2, h3⟩ i hi
    if c1 : i < 8 then exact bytes_of_block m a b 0 h0 i (by omega) (by omega)
    else if c2 : i < 16 then exact bytes_of_block m a b 8 h1 i (by omega) (by omega)
    else if c3 : i < 24 then exact bytes_of_block m a b 16 h2 i (by omega) (by omega)
    else exact bytes_of_block m a b 24 h3 i (by omega) (by omega)
  · intro h
    exact ⟨⟨block_of_bytes m a b 32 0 h (by decide), block_of_bytes m a b 32 8 h (by decide)⟩,
      block_of_bytes m a b 32 16 h (by decide), block_of_bytes m a b 32 24 h (by decide)⟩


theorem u64_add_neg_one (x : UInt64) : x + (0 - 1) = x - 1 := by
  apply u64_eq_of_toNat
  have h0 : (0 : UInt64).toNat = 0 := rfl
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  have hx : x.toNat < 18446744073709551616 := x.toNat_lt
  rw [UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_sub, h0, h1, h64]
  omega

end Qsag

namespace Qsag.Machine
/-- CPU leakage contract uses the same `StepObs` emitted by the decoded instruction runner.
Hardware mode and public-state hypotheses are supplied by the verified caller. -/
def x86LeakageContract (lowEq : Qsag.X86State → Qsag.X86State → Prop)
    (hardware : Spec.ExecMode → Qsag.X86State → Prop) :
    Spec.LeakageContract Qsag.X86State (List (Qsag.DecodedInstr Qsag.X86Instr) × Nat) Qsag.StepObs where
  publicEq := lowEq
  admissible := hardware
  observe _ s request := (Qsag.runX86 request.1 request.2 s).2

def arm64LeakageContract (lowEq : Qsag.Arm64State → Qsag.Arm64State → Prop)
    (hardware : Spec.ExecMode → Qsag.Arm64State → Prop) :
    Spec.LeakageContract Qsag.Arm64State (List (Qsag.DecodedInstr Qsag.Arm64Instr) × Nat) Qsag.StepObs where
  publicEq := lowEq
  admissible := hardware
  observe _ s request := (Qsag.runArm64 request.1 request.2 s).2
end Qsag.Machine

namespace Qsag.SydTv
open Qsag
abbrev Word := BitVec 64
abbrev Env := Nat → Word
abbrev Observation := Qsag.StepObs
/- Single-instruction `x86_64` byte decoder at offset `pc` wrapping `ElfBinaryVerify.decodeX86InstrAt`. -/


/- Single-instruction `AArch64` byte decoder at 4-byte-aligned offset `pc` wrapping `ElfBinaryVerify.decodeArm64Word`. -/


/- Generic `x86_64` fetch-step runner parameterized by instruction fetch (`decodeX86One` or `findInstrAtPc`). -/


/-- Live byte-decoded `x86_64` execution fetching each instruction directly via `decodeX86One`. -/


theorem runX86_eq_runX86Fetch (prog : List (DecodedInstr X86Instr)) (fuel : Nat) (s : X86State) :
    runX86 prog fuel s = runX86Fetch (fun pc => findInstrAtPc pc prog) fuel s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ k ih =>
    change (if s.halted then (s, []) else _) = (if s.halted then (s, []) else _)
    cases s.halted
    · dsimp only
      cases hfind : findInstrAtPc s.pc prog with
      | none => rfl
      | some d =>
        dsimp only
        rw [ih (stepX86 d s).1]
    · rfl

theorem runX86Fetch_halted (fetch : Nat → Option (DecodedInstr X86Instr)) (fuel : Nat)
    (s : X86State) (h : s.halted = true) :
    runX86Fetch fetch fuel s = (s, []) := by
  cases fuel with
  | zero => rfl
  | succ k =>
    change (if s.halted then (s, []) else _) = (s, [])
    rw [h]; rfl

theorem runX86Fetch_step (fetch : Nat → Option (DecodedInstr X86Instr)) (fuel : Nat)
    (s : X86State) (d : DecodedInstr X86Instr) (hh : s.halted = false) (hf : fetch s.pc = some d) :
    runX86Fetch fetch (fuel + 1) s =
      let r := stepX86 d s
      let u := runX86Fetch fetch fuel r.1
      (u.1, r.2 :: u.2) := by
  change (if s.halted then (s, []) else _) = _
  rw [hh, hf]; rfl

theorem findInstrAtPc_some_mem {Instr : Type} (pc : Nat) :
    ∀ (prog : List (DecodedInstr Instr)) (d : DecodedInstr Instr),
      findInstrAtPc pc prog = some d → d ∈ prog ∧ d.offset = pc := by
  intro prog
  induction prog with
  | nil => intro d h; exact absurd h (by simp [findInstrAtPc])
  | cons x xs ih =>
    intro d h
    simp only [findInstrAtPc] at h
    split at h
    · rename_i hx
      have hxd : x = d := Option.some.inj h
      subst hxd
      exact ⟨List.mem_cons_self, by simpa using hx⟩
    · obtain ⟨hm, ho⟩ := ih d h
      exact ⟨List.mem_cons_of_mem _ hm, ho⟩

/-- One fetch-step where the instruction is located by evaluating `findInstrAtPc` on the decoded
program (`hfind` is closed by `rfl` once the state's `pc` is a literal). -/
theorem runX86Fetch_step_prog (fetch : Nat → Option (DecodedInstr X86Instr))
    (prog : List (DecodedInstr X86Instr)) (hf : ∀ d ∈ prog, fetch d.offset = some d)
    (fuel : Nat) (s : X86State) (d : DecodedInstr X86Instr) (hh : s.halted = false)
    (hfind : findInstrAtPc s.pc prog = some d) :
    runX86Fetch fetch (fuel + 1) s =
      let r := stepX86 d s
      let u := runX86Fetch fetch fuel r.1
      (u.1, r.2 :: u.2) := by
  obtain ⟨hm, ho⟩ := findInstrAtPc_some_mem _ _ _ hfind
  exact runX86Fetch_step fetch fuel s d hh (by rw [← ho]; exact hf d hm)

/- Generic `AArch64` fetch-step runner parameterized by instruction fetch (`decodeArm64One` or `findInstrAtPc`). -/


/-- Live byte-decoded `AArch64` execution fetching each instruction directly via `decodeArm64One`. -/


theorem runArm64_eq_runArm64Fetch (prog : List (DecodedInstr Arm64Instr)) (fuel : Nat) (s : Arm64State) :
    runArm64 prog fuel s = runArm64Fetch (fun pc => findInstrAtPc pc prog) fuel s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ k ih =>
    change (if s.halted then (s, []) else _) = (if s.halted then (s, []) else _)
    cases s.halted
    · dsimp only
      cases hfind : findInstrAtPc s.pc prog with
      | none => rfl
      | some d =>
        dsimp only
        rw [ih (stepArm64 d s).1]
    · rfl

theorem runArm64Fetch_halted (fetch : Nat → Option (DecodedInstr Arm64Instr)) (fuel : Nat)
    (s : Arm64State) (h : s.halted = true) :
    runArm64Fetch fetch fuel s = (s, []) := by
  cases fuel with
  | zero => rfl
  | succ k =>
    change (if s.halted then (s, []) else _) = (s, [])
    rw [h]; rfl

theorem runArm64Fetch_step (fetch : Nat → Option (DecodedInstr Arm64Instr)) (fuel : Nat)
    (s : Arm64State) (d : DecodedInstr Arm64Instr) (hh : s.halted = false) (hf : fetch s.pc = some d) :
    runArm64Fetch fetch (fuel + 1) s =
      let r := stepArm64 d s
      let u := runArm64Fetch fetch fuel r.1
      (u.1, r.2 :: u.2) := by
  change (if s.halted then (s, []) else _) = _
  rw [hh, hf]; rfl

/-! ## §3. Full State+Trace Step Equations & Arithmetic / SIMD Helpers -/

theorem u64_eq_of_toNat_eq {a b : UInt64} (h : a.toNat = b.toNat) : a = b := by
  cases a; cases b; congr; exact BitVec.eq_of_toNat_eq h

theorem bv64_ne_zero_iff_u64_ne_zero (n : Word) :
    n ≠ 0 ↔ UInt64.ofBitVec n ≠ 0 := by
  constructor
  · intro hn h0
    apply hn
    apply BitVec.eq_of_toNat_eq
    have := congrArg UInt64.toNat h0
    simpa using this
  · intro hu hn
    subst hn
    exact hu rfl

theorem bv64_pos_of_ne_zero (n : Word) (hn : n ≠ 0) : 0 < n.toNat := by
  rcases Nat.eq_zero_or_pos n.toNat with hz | hp
  · exfalso
    apply hn
    apply BitVec.eq_of_toNat_eq
    simpa using hz
  · exact hp

theorem u64_evalAdd64_val (a b : UInt64) (cf : Bool) :
    (evalX86Alu .add true a b cf).1 = a + b := by
  apply u64_eq_of_toNat_eq
  change (UInt64.ofNat ((a.toNat + b.toNat) % 0x10000000000000000)).toNat = (a + b).toNat
  rw [UInt64.toNat_ofNat', UInt64.toNat_add]
  have h64 : (2 : Nat) ^ 64 = 0x10000000000000000 := rfl
  omega

theorem vpxor_self (v : Vec256) : evalVecBin256 .vpxor v v = Vec256.zero := by
  cases v
  simp [evalVecBin256, Vec256.zero]









theorem zeroUpperVec256_zero : zeroUpperVec256 Vec256.zero = Vec256.zero := by rfl

theorem vzeroupper_bank16 (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Vec256) :
    Bank16.ofFn (fun i =>
      let v := (Bank16.mk y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).get i
      ⟨v.w0, v.w1, 0, 0⟩) =
    Bank16.mk (zeroUpperVec256 y0) (zeroUpperVec256 y1) (zeroUpperVec256 y2) (zeroUpperVec256 y3)
      (zeroUpperVec256 y4) (zeroUpperVec256 y5) (zeroUpperVec256 y6) (zeroUpperVec256 y7)
      (zeroUpperVec256 y8) (zeroUpperVec256 y9) (zeroUpperVec256 y10) (zeroUpperVec256 y11)
      (zeroUpperVec256 y12) (zeroUpperVec256 y13) (zeroUpperVec256 y14) (zeroUpperVec256 y15) := by rfl

section FullSteps
variable (off len pc : Nat) (g : Bank16 UInt64) (y : Bank16 Vec256) (cf o zf dy : Bool)
  (m : UInt64 → UInt8)

theorem stepX86Full_movRR (is64 : Bool) (dst src : Nat) :
    stepX86 ⟨off, len, .movRegReg is64 dst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g.set dst (maskGprWidth is64 (g.get src)), y, cf, o, zf, dy, false, m⟩,
       ⟨off, [], true⟩) := by rfl

theorem stepX86Full_movImm (is64 : Bool) (dst : Nat) (imm : UInt64) :
    stepX86 ⟨off, len, .movImm is64 dst imm⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g.set dst (maskGprWidth is64 imm), y, cf, o, zf, dy, false, m⟩,
       ⟨off, [], true⟩) := by rfl

theorem stepX86Full_load8 (dst base : Nat) :
    stepX86 ⟨off, len, .loadGpr 1 false dst (.baseDisp base 0)⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g.set dst (maskGprWidth false (m (g.get base)).toUInt64), y, cf, o, zf, dy, false, m⟩,
       ⟨off, [(g.get base, 1)], true⟩) := by
  simp only [stepX86, evalX86Addr, UInt64.add_zero]
  rfl

theorem stepX86Full_store8 (src base : Nat) :
    stepX86 ⟨off, len, .storeGpr 1 src (.baseDisp base 0)⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g, y, cf, o, zf, dy, false, writeMem8 m (g.get base) (g.get src).toUInt8⟩,
       ⟨off, [(g.get base, 1)], true⟩) := by
  simp only [stepX86, evalX86Addr, UInt64.add_zero]
  rfl

theorem stepX86Full_xorRR (is64 : Bool) (dst src : Nat) :
    stepX86 ⟨off, len, .aluRegReg .xorOp is64 dst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g.set dst (maskGprWidth is64 (g.get dst ^^^ g.get src)), y, false, false,
        maskGprWidth is64 (g.get dst ^^^ g.get src) == 0, dy, false, m⟩,
       ⟨off, [], true⟩) := by rfl

theorem stepX86Full_orRR (is64 : Bool) (dst src : Nat) :
    stepX86 ⟨off, len, .aluRegReg .orOp is64 dst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g.set dst (maskGprWidth is64 (g.get dst ||| g.get src)), y, false, false,
        maskGprWidth is64 (g.get dst ||| g.get src) == 0, dy, false, m⟩,
       ⟨off, [], true⟩) := by rfl

theorem stepX86Full_subImm32 (dst : Nat) (imm : UInt64) :
    stepX86 ⟨off, len, .aluImm .sub false dst imm⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len,
        g.set dst (maskGprWidth false (UInt64.ofNat (((maskGprWidth false (g.get dst)).toNat + 0x100000000 -
          (maskGprWidth false imm).toNat) % 0x100000000))), y,
        decide ((maskGprWidth false (g.get dst)).toNat < (maskGprWidth false imm).toNat),
        evalX86AluOf .sub false (g.get dst) imm cf,
        maskGprWidth false (UInt64.ofNat (((maskGprWidth false (g.get dst)).toNat + 0x100000000 -
          (maskGprWidth false imm).toNat) % 0x100000000)) == 0, dy, false, m⟩,
       ⟨off, [], true⟩) := by rfl

theorem stepX86Full_shr32_31 (dst : Nat) :
    stepX86 ⟨off, len, .shiftImm .shr false dst 31⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len,
        g.set dst (maskGprWidth false (maskGprWidth false (g.get dst) >>> UInt64.ofNat (31 % 32))), y,
        ((maskGprWidth false (g.get dst) >>> UInt64.ofNat (31 % 32 - 1)) &&& 1) != 0,
        (maskGprWidth false (g.get dst) &&& 0x80000000) != 0,
        maskGprWidth false (maskGprWidth false (g.get dst) >>> UInt64.ofNat (31 % 32)) == 0, dy, false, m⟩,
       ⟨off, [], true⟩) := by rfl

theorem stepX86Full_addImm64 (dst : Nat) (imm : UInt64) :
    stepX86 ⟨off, len, .aluImm .add true dst imm⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g.set dst (g.get dst + imm), y,
        (evalX86Alu .add true (g.get dst) imm cf).2.1,
        evalX86AluOf .add true (g.get dst) imm cf,
        (evalX86Alu .add true (g.get dst) imm cf).2.2, dy, false, m⟩,
       ⟨off, [], true⟩) := by
  simp only [stepX86, u64_evalAdd64_val]

theorem stepX86Full_inc64 (dst : Nat) :
    stepX86 ⟨off, len, .incDec true true dst⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g.set dst (g.get dst + 1), y, cf, evalX86IncDecOf true true (g.get dst),
        g.get dst + 1 == 0, dy, false, m⟩,
       ⟨off, [], true⟩) := by rfl

theorem stepX86Full_dec64 (dst : Nat) :
    stepX86 ⟨off, len, .incDec false true dst⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g.set dst (g.get dst - 1), y, cf, evalX86IncDecOf false true (g.get dst),
        g.get dst - 1 == 0, dy, false, m⟩,
       ⟨off, [], true⟩) := by
  have h : stepX86 ⟨off, len, .incDec false true dst⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g.set dst (g.get dst + (0 - 1)), y, cf, evalX86IncDecOf false true (g.get dst),
        g.get dst + (0 - 1) == 0, dy, false, m⟩, ⟨off, [], true⟩) := rfl
  rw [h, u64_add_neg_one]

theorem stepX86Full_jnz (tgt : Int) :
    stepX86 ⟨off, len, .jcc 5 tgt⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨jccPc (!zf) tgt (off + len), g, y, cf, o, zf, dy, false, m⟩,
       ⟨off, [], true⟩) := by rfl

theorem stepX86Full_mfence :
    stepX86 ⟨off, len, .mfence⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g, y, cf, o, zf, dy, false, m⟩, ⟨off, [], true⟩) := by rfl

theorem stepX86Full_ret :
    stepX86 ⟨off, len, .ret⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨(readMem64 m (g.get 4)).toNat, g.set 4 (g.get 4 + 8), y, cf, o, zf, dy, true, m⟩,
       ⟨off, [(g.get 4, 8)], true⟩) := by rfl

theorem stepX86Full_vload256 (dst base : Nat) :
    stepX86 ⟨off, len, .vload true dst (.baseDisp base 0)⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g, y.set dst (readMem256 m (g.get base)), cf, o, zf, true, false, m⟩,
       ⟨off, [(g.get base, 32)], true⟩) := by
  simp only [stepX86, evalX86Addr, UInt64.add_zero, Bool.or_true]
  rfl

theorem stepX86Full_vstore256 (src base : Nat) :
    stepX86 ⟨off, len, .vstore true src (.baseDisp base 0)⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g, y, cf, o, zf, dy, false, writeMem256 m (g.get base) (y.get src)⟩,
       ⟨off, [(g.get base, 32)], true⟩) := by
  simp only [stepX86, evalX86Addr, UInt64.add_zero]
  rfl

theorem stepX86Full_vmovGprToXmm (is64 : Bool) (dstVec srcGpr : Nat) :
    stepX86 ⟨off, len, .vmovGprToXmm is64 dstVec srcGpr⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g, y.set dstVec ⟨maskGprWidth is64 (g.get srcGpr), 0, 0, 0⟩, cf, o, zf, dy, false, m⟩,
       ⟨off, [], true⟩) := by rfl

theorem stepX86Full_vpbroadcastQ (dst src : Nat) :
    stepX86 ⟨off, len, .vpbroadcast true true dst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g, y.set dst (bcastQword256 (y.get src).w0), cf, o, zf, true, false, m⟩,
       ⟨off, [], true⟩) := by cases dy <;> rfl

theorem stepX86Full_vpbroadcastB (dst src : Nat) :
    stepX86 ⟨off, len, .vpbroadcast false true dst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g, y.set dst (bcastByte256 (y.get src).w0.toUInt8), cf, o, zf, true, false, m⟩,
       ⟨off, [], true⟩) := by cases dy <;> rfl

theorem stepX86Full_vgf2p8affine256 (dst s1 s2 : Nat) (imm : UInt8) :
    stepX86 ⟨off, len, .vgf2p8affineqb true dst s1 s2 imm⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g, y.set dst (gfniAffineVec256 (y.get s1) (y.get s2) imm), cf, o, zf, true, false, m⟩,
       ⟨off, [], true⟩) := by
  simp only [stepX86, clampVecWidth, Bool.or_true]
  rfl

theorem stepX86Full_vbinOp256 (op : X86VecBinOp) (dst s1 s2 : Nat) :
    stepX86 ⟨off, len, .vbinOp op true dst s1 s2⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g, y.set dst (evalVecBin256 op (y.get s1) (y.get s2)), cf, o, zf, true, false, m⟩,
       ⟨off, [], true⟩) := by
  simp only [stepX86, clampVecWidth, Bool.or_true]
  rfl

theorem stepX86Full_vshift256 (sk : X86VecShiftKind) (dst src imm : Nat) :
    stepX86 ⟨off, len, .vshiftImm sk true dst src imm⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g, y.set dst (evalVecShift256 sk (y.get src) imm), cf, o, zf, true, false, m⟩,
       ⟨off, [], true⟩) := by
  simp only [stepX86, clampVecWidth, Bool.or_true]
  rfl

theorem stepX86Full_vpclmul256 (dst s1 s2 : Nat) (imm : UInt8) :
    stepX86 ⟨off, len, .vpclmulqdq true dst s1 s2 imm⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g, y.set dst (clmul256 (y.get s1) (y.get s2) imm), cf, o, zf, true, false, m⟩,
       ⟨off, [], true⟩) := by
  simp only [stepX86, clmul256, Bool.or_true]
  rfl

theorem stepX86Full_vzeroupper :
    stepX86 ⟨off, len, .vzeroupper⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g, Bank16.ofFn (fun i => let v := y.get i; ⟨v.w0, v.w1, 0, 0⟩), cf, o, zf, false, false, m⟩,
       ⟨off, [], true⟩) := by rfl

end FullSteps

section ArmFullSteps
variable (off len pc : Nat) (g : Bank32 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool)
  (m : UInt64 → UInt8)

theorem stepArm64Full_strbPost31_0 :
    stepArm64 ⟨off, len, .strbPost 31 0 1⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩ =
      (⟨off + 4, armSet g 0 (armGet g 0 + 1), v, cf, zf, dit, false, writeMem8 m (armGet g 0) 0⟩,
       ⟨off, [(armGet g 0, 1)], true⟩) := by rfl

theorem stepArm64Full_subsImm1_1 :
    stepArm64 ⟨off, len, .aluImm .subs true 1 1 1⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩ =
      (⟨off + 4, armSet g 1 (armGet g 1 - 1), v, decide ((armGet g 1).toNat ≥ 1),
        armGet g 1 - 1 == 0, dit, false, m⟩,
       ⟨off, [], true⟩) := by
  have hsub : UInt64.ofNat (((armGet g 1).toNat + 0x10000000000000000 - 1) %
      0x10000000000000000) = armGet g 1 - 1 := by
    apply u64_eq_of_toNat_eq
    have hlt : (armGet g 1).toNat < 18446744073709551616 := (armGet g 1).toNat_lt
    have h1 : (1 : UInt64).toNat = 1 := rfl
    have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
    rw [UInt64.toNat_ofNat', UInt64.toNat_sub, h1, h64]
    omega
  have h : stepArm64 ⟨off, len, .aluImm .subs true 1 1 1⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩ =
      ((⟨off + 4,
        armSet g 1 (UInt64.ofNat (((armGet g 1).toNat + 0x10000000000000000 - 1) % 0x10000000000000000)),
        v, decide ((armGet g 1).toNat ≥ 1),
        UInt64.ofNat (((armGet g 1).toNat + 0x10000000000000000 - 1) % 0x10000000000000000) == 0,
        dit, false, m⟩ : Arm64State), (⟨off, [], true⟩ : StepObs)) := rfl
  rw [h, hsub]

theorem stepArm64Full_bne0 :
    stepArm64 ⟨off, len, .bCond 1 0⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩ =
      (⟨jccPc (!zf) 0 (off + 4), g, v, cf, zf, dit, false, m⟩,
       ⟨off, [], true⟩) := by rfl

theorem stepArm64Full_dmbIsh :
    stepArm64 ⟨off, len, .dmbIsh⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩ =
      (⟨off + 4, g, v, cf, zf, dit, false, m⟩, ⟨off, [], true⟩) := by rfl

theorem stepArm64Full_ret :
    stepArm64 ⟨off, len, .ret⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩ =
      (⟨pc, g, v, cf, zf, dit, true, m⟩, ⟨off, [], true⟩) := by rfl

end ArmFullSteps

theorem mask32_xor_self_eq (x : UInt64) : maskGprWidth false (x ^^^ x) = 0 := by
  rw [UInt64.xor_self]; rfl

theorem u64_zero_beq_true : ((0 : UInt64) == 0) = true := by rfl


end Qsag.SydTv

namespace Qsag.Machine
/-- Byte-selected x86 contract. The checker's `FuncContract` carries its hardware and
initial-state assumptions; this view records exactly the runner's `StepObs` trace. -/
def x86CodeLeakageContract (code : List UInt8) (c : Qsag.FuncContract) :
    Spec.LeakageContract Qsag.X86State Nat Qsag.StepObs where
  publicEq := Qsag.X86ContractInit c
  admissible mode _ := mode = Spec.ExecMode.constantTimeSafe
  observe _ s fuel := match Qsag.decodeX86Stream code with
    | none => []
    | some prog => (Qsag.runX86 prog fuel s).2

theorem checkX86_refines_leakage_contract {code : List UInt8} {c : Qsag.FuncContract}
    (h : Qsag.checkX86ThreeWayNI code c = true) :
    (x86CodeLeakageContract code c).ConstTimeUnder := by
  intro mode s₁ s₂ fuel _ _ hi
  obtain ⟨prog, hd, heq, _⟩ := Qsag.checkX86ThreeWayNI_sound h hi fuel
  simpa only [x86CodeLeakageContract, hd] using heq

/-- AArch64 counterpart; DIT entry-state obligations remain explicit in `FuncContract`. -/
def arm64CodeLeakageContract (code : List UInt8) (c : Qsag.FuncContract) :
    Spec.LeakageContract Qsag.Arm64State Nat Qsag.StepObs where
  publicEq := Qsag.Arm64ContractInit c
  admissible mode _ := mode = Spec.ExecMode.constantTimeSafe
  observe _ s fuel := match Qsag.decodeArm64Stream code with
    | none => []
    | some prog => (Qsag.runArm64 prog fuel s).2

theorem checkArm64_refines_leakage_contract {code : List UInt8} {c : Qsag.FuncContract}
    (h : Qsag.checkArm64ThreeWayNI code c = true) :
    (arm64CodeLeakageContract code c).ConstTimeUnder := by
  intro mode s₁ s₂ fuel _ _ hi
  obtain ⟨prog, hd, heq, _⟩ := Qsag.checkArm64ThreeWayNI_sound h hi fuel
  simpa only [arm64CodeLeakageContract, hd] using heq
end Qsag.Machine

public section
namespace Qsag.SydTv
@[simp] theorem runX86One_eq (code : List UInt8) :
    runX86One code = runX86Fetch (decodeX86One code) := by rfl
@[simp] theorem runArm64One_eq (code : List UInt8) :
    runArm64One code = runArm64Fetch (decodeArm64One code) := by rfl
end Qsag.SydTv

public section
namespace Qsag
@[simp] theorem armSet_hi0 (g : Bank32 UInt64) (v : UInt64) : (armSet g 0 v).hi = g.hi := by rfl
@[simp] theorem armSet_hi1 (g : Bank32 UInt64) (v : UInt64) : (armSet g 1 v).hi = g.hi := by rfl
theorem evalVecBin256_xor_eq (a b : Vec256) : evalVecBin256 .vpxor a b =
    ⟨a.w0 ^^^ b.w0, a.w1 ^^^ b.w1, a.w2 ^^^ b.w2, a.w3 ^^^ b.w3⟩ := by rfl
theorem evalVecShift256_left8 (v : Vec256) : evalVecShift256 .vpslldq v 8 =
    ⟨0, v.w0 <<< 0, 0, v.w2 <<< 0⟩ := by rfl
theorem evalVecShift256_right8 (v : Vec256) : evalVecShift256 .vpsrldq v 8 =
    ⟨v.w1 >>> 0, 0, v.w3 >>> 0, 0⟩ := by rfl
end Qsag
namespace Qsag.SydTv
open Qsag
theorem bcastQword256_eq (w : UInt64) : bcastQword256 w = ⟨w, w, w, w⟩ := by rfl
theorem clmul256_eq_0 (a b : Vec256) : clmul256 a b 0 =
    ⟨(clmul64 a.w0 b.w0).w0, (clmul64 a.w0 b.w0).w1,
      (clmul64 a.w2 b.w2).w0, (clmul64 a.w2 b.w2).w1⟩ := by rfl
theorem clmul256_eq_1 (a b : Vec256) : clmul256 a b 1 =
    ⟨(clmul64 a.w1 b.w0).w0, (clmul64 a.w1 b.w0).w1,
      (clmul64 a.w3 b.w2).w0, (clmul64 a.w3 b.w2).w1⟩ := by rfl
theorem clmul256_eq_16 (a b : Vec256) : clmul256 a b 16 =
    ⟨(clmul64 a.w0 b.w1).w0, (clmul64 a.w0 b.w1).w1,
      (clmul64 a.w2 b.w3).w0, (clmul64 a.w2 b.w3).w1⟩ := by rfl
theorem clmul256_eq_17 (a b : Vec256) : clmul256 a b 17 =
    ⟨(clmul64 a.w1 b.w1).w0, (clmul64 a.w1 b.w1).w1,
      (clmul64 a.w3 b.w3).w0, (clmul64 a.w3 b.w3).w1⟩ := by rfl
end Qsag.SydTv
