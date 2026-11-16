module

public import Qsag.Tactic.Prelude
import Qsag.Tactic.AssuranceKit

/-!
# Qsag.Exec.TwoSlotHwmCrashModel — sector-level crash model of the two-slot high-water mark

Models `qsag_asm::durable::TwoSlotHwm` (`crates/qsag-asm/src/durable.rs`) and its caller
`DurableBurnJournal::reserve` / `load_guarded` (`crates/qsag-fts/src/wal.rs`, format `QSBURN05`)
on a byte-addressed file stored in fixed-size sectors.

## Device

* `Disk`: the durable image, bytes by offset plus the file length.
* `Dev`: a durable image and the writes issued since the last `fsync` (`Op.pwrite`, `Op.fsync`).
* `CrashImage`: what a power loss can leave. Outside one sector touched by an unsynced write,
  every byte holds the value of some prefix of the unsynced writes (so any byte-granular mix of
  old and new, including short-write prefixes). Inside that one sector every byte is arbitrary,
  including bytes of the sector the write never addressed. The file length ends anywhere between
  the old and the fully written length.
* `NoForge`: the one assumption about the garbage. A slot or chain read back after the crash
  either fails to authenticate or decodes to its value before or after the unsynced writes.
  This is MAC unforgeability stated for the storage medium; it does not restrict where the
  garbage lands.

## Protocol

`Codec` abstracts the two authenticated formats (the 80-byte slot and the record chain) by
their laws (`Codec.Lawful`). `recoverWrites` is `recover_with_outcome` /
`recover_from_lone_slot`, case for case, returning the slot writes that the Rust performs.
`reserveOps` is `reserve`: record, `fsync`, slot A, `fsync`, slot B, `fsync`.
`Step` is the system: reserve, recover, shutdown, each either completing or crashing at any
operation boundary.

## Results

* `distinct_pages_safe`: with the slots and the record area on pairwise sector-disjoint ranges
  (`Layout.Separated`; `Layout.paged_separated` proves it for `TwoSlotHwm::paged`), in every
  reachable state (a) a recovery that returns never returns a counter below the highest
  acknowledged one, (b) recovery succeeds whenever the record chain itself parses, (c) a live
  handle is at or above every acknowledged counter.
* `shared_sector_single_tear_loses_state`: with both slots inside one sector (`QSBURN04`,
  `qsag-hd/src/budget.rs` offsets `32..112` and `112..192`), an acknowledged commit followed by
  one torn sector during the next slot write leaves no valid slot; recovery refuses.
* `append_tear_fails_closed`: a tear inside the record being appended leaves a chain that does
  not parse. `load_guarded` has no repair for that state, so (b) cannot be strengthened to
  unconditional success. Slots are intact and nothing is rolled back.

`Slot` classification keeps only "authenticates or not": the Rust distinguishes
`Uninitialized` from `Corrupt` but `recover_with_outcome` matches on `Valid` alone.
Counters are `Nat`; `Codec.bound` carries the `u64` range, and `reserve` is guarded by it.
Journal creation (one write of the three header pages) is outside the model: `Init` starts from
a steady image.
-/

public section

namespace Qsag.Exec.TwoSlotHwmCrashModel

set_option autoImplicit false

/-! ## 1. Bytes, sectors and unsynced writes -/

/-- Durable image of one regular file. -/
structure Disk where
  bytes : Nat → UInt8
  len : Nat

/-- `bs` laid over `f` starting at `off`. -/
@[expose] def overlay : List UInt8 → Nat → (Nat → UInt8) → Nat → UInt8
  | [], _, f => f
  | b :: rest, off, f => fun x => if x = off then b else overlay rest (off + 1) f x

/-- The `n` bytes of `f` starting at `off`. -/
@[expose] def readAt (f : Nat → UInt8) : Nat → Nat → List UInt8
  | _, 0 => []
  | off, n + 1 => f off :: readAt f (off + 1) n

/-- `pwrite(bs, off)` applied in full; the file grows when the write ends past its length. -/
@[expose] def Disk.write (d : Disk) (off : Nat) (bs : List UInt8) : Disk :=
  ⟨overlay bs off d.bytes, max d.len (off + bs.length)⟩

theorem overlay_outside (bs : List UInt8) (f : Nat → UInt8) (x : Nat) :
    ∀ off, (x < off ∨ off + bs.length ≤ x) → overlay bs off f x = f x := by
  induction bs with
  | nil => intro off _; rfl
  | cons b rest ih =>
    intro off h
    have hlen : (b :: rest).length = rest.length + 1 := rfl
    rw [hlen] at h
    have hne : ¬ x = off := by omega
    have hrest := ih (off + 1) (by omega)
    show (if x = off then b else overlay rest (off + 1) f x) = f x
    rw [ite_eq_right hne]
    exact hrest

theorem readAt_congr {f g : Nat → UInt8} :
    ∀ (n off : Nat), (∀ x, off ≤ x → x < off + n → f x = g x) → readAt f off n = readAt g off n := by
  intro n
  induction n with
  | zero => intro off _; rfl
  | succ n ih =>
    intro off h
    show f off :: readAt f (off + 1) n = g off :: readAt g (off + 1) n
    rw [h off (Nat.le_refl off) (by omega), ih (off + 1) (fun x h1 h2 => h x (by omega) (by omega))]

theorem readAt_overlay (f : Nat → UInt8) :
    ∀ (bs : List UInt8) (off : Nat), readAt (overlay bs off f) off bs.length = bs := by
  intro bs
  induction bs with
  | nil => intro off; rfl
  | cons b rest ih =>
    intro off
    show overlay (b :: rest) off f off :: readAt (overlay (b :: rest) off f) (off + 1) rest.length
      = b :: rest
    have hhead : overlay (b :: rest) off f off = b := by
      show (if off = off then b else overlay rest (off + 1) f off) = b
      rw [ite_eq_left rfl]
    have htail : readAt (overlay (b :: rest) off f) (off + 1) rest.length
        = readAt (overlay rest (off + 1) f) (off + 1) rest.length := by
      apply readAt_congr
      intro x hx _
      have hne : ¬ x = off := by omega
      show (if x = off then b else overlay rest (off + 1) f x) = overlay rest (off + 1) f x
      rw [ite_eq_right hne]
    rw [hhead, htail, ih (off + 1)]

theorem Disk.write_bytes_outside (d : Disk) (off : Nat) (bs : List UInt8) {x : Nat}
    (h : x < off ∨ off + bs.length ≤ x) : (d.write off bs).bytes x = d.bytes x :=
  overlay_outside bs d.bytes x off h

theorem Disk.write_len (d : Disk) (off : Nat) (bs : List UInt8) :
    (d.write off bs).len = max d.len (off + bs.length) := by rfl

theorem Disk.len_le_write_len (d : Disk) (off : Nat) (bs : List UInt8) :
    d.len ≤ (d.write off bs).len := Nat.le_max_left _ _

theorem Disk.readAt_write (d : Disk) (off : Nat) (bs : List UInt8) :
    readAt (d.write off bs).bytes off bs.length = bs :=
  readAt_overlay d.bytes bs off

/-- One `pwrite`. -/
structure PWrite where
  off : Nat
  data : List UInt8

def Disk.apply (d : Disk) (w : PWrite) : Disk := d.write w.off w.data

def Disk.applyAll (d : Disk) (ws : List PWrite) : Disk := ws.foldl Disk.apply d

/-- The durable image and the writes not yet covered by an `fsync`. -/
structure Dev where
  durable : Disk
  pending : List PWrite

inductive Op where
  | pwrite (w : PWrite)
  | fsync

@[expose] def Dev.run (v : Dev) : Op → Dev
  | .pwrite w => ⟨v.durable, v.pending ++ [w]⟩
  | .fsync => ⟨v.durable.applyAll v.pending, []⟩

/-- Images a power loss can leave on a device with sector size `S`. With nothing unsynced the
    image is the durable one. Otherwise one sector `x₀ / S` touched by an unsynced write is
    arbitrary; every other byte holds its value after some prefix of the unsynced writes. -/
@[expose] def CrashImage (S : Nat) (v : Dev) (d' : Disk) : Prop :=
  (v.pending = [] ∧ d' = v.durable) ∨
  ∃ w x₀, w ∈ v.pending ∧ w.off ≤ x₀ ∧ x₀ < w.off + w.data.length ∧
    (∀ x, x / S ≠ x₀ / S →
      ∃ k, d'.bytes x = (v.durable.applyAll (v.pending.take k)).bytes x) ∧
    v.durable.len ≤ d'.len ∧ d'.len ≤ (v.durable.applyAll v.pending).len

theorem crashImage_nil {S : Nat} {d d' : Disk} (h : CrashImage S ⟨d, []⟩ d') : d' = d := by
  rcases h with ⟨_, h⟩ | ⟨w, _, hw, _⟩
  · exact h
  · exact absurd hw List.not_mem_nil

theorem crashImage_single {S : Nat} {d d' : Disk} {w : PWrite}
    (h : CrashImage S ⟨d, [w]⟩ d') :
    ∃ x₀, w.off ≤ x₀ ∧ x₀ < w.off + w.data.length ∧
      (∀ x, x / S ≠ x₀ / S →
        d'.bytes x = d.bytes x ∨ d'.bytes x = (d.write w.off w.data).bytes x) ∧
      d.len ≤ d'.len ∧ d'.len ≤ (d.write w.off w.data).len := by
  rcases h with ⟨hnil, _⟩ | ⟨w', x₀, hw, h1, h2, hB, hl1, hl2⟩
  · exact absurd hnil (List.cons_ne_nil _ _)
  · have hw' : w' = w := List.mem_singleton.mp hw
    subst hw'
    refine ⟨x₀, h1, h2, ?_, hl1, hl2⟩
    intro x hx
    obtain ⟨k, hk⟩ := hB x hx
    cases k with
    | zero => exact Or.inl hk
    | succ k =>
      have e : List.take (k + 1) [w'] = [w'] := by rw [List.take_succ_cons, List.take_nil]
      have hk' : d'.bytes x = (d.applyAll (List.take (k + 1) [w'])).bytes x := hk
      rw [e] at hk'
      exact Or.inr hk'

/-- Bytes that share no sector with the write keep their value across a torn write. -/
theorem torn_frame {S off : Nat} {bs : List UInt8} {d d' : Disk} {x₀ : Nat}
    (hTorn : ∀ x, x / S ≠ x₀ / S →
      d'.bytes x = d.bytes x ∨ d'.bytes x = (d.write off bs).bytes x)
    (h1 : off ≤ x₀) (h2 : x₀ < off + bs.length) {x : Nat}
    (hx : ∀ y, off ≤ y → y < off + bs.length → x / S ≠ y / S) : d'.bytes x = d.bytes x := by
  rcases hTorn x (hx x₀ h1 h2) with h | h
  · exact h
  · rw [h]
    apply Disk.write_bytes_outside
    rcases Nat.lt_or_ge x off with a | a
    · exact Or.inl a
    · rcases Nat.lt_or_ge x (off + bs.length) with b | b
      · exact absurd rfl (hx x a b)
      · exact Or.inr b

/-! ## 2. Layout and codec -/

inductive Slot where
  | a
  | b
  deriving DecidableEq

/-- `ChainHead`: record count, tag of the last record, tag of the one before it. -/
structure Head (Tip : Type) where
  len : Nat
  tip : Tip
  prev : Tip

/-- Sector size and the three offsets a journal format fixes. -/
structure Layout where
  sector : Nat
  offA : Nat
  offB : Nat
  chainOff : Nat

@[expose] def Layout.off (L : Layout) : Slot → Nat
  | .a => L.offA
  | .b => L.offB

/-- No byte of slot A shares a sector with a byte of slot B, no slot byte shares a sector with
    the record area, and both slots end before the record area. `n` is the slot length. -/
structure Layout.Separated (L : Layout) (n : Nat) : Prop where
  ab : ∀ x y, L.offA ≤ x → x < L.offA + n → L.offB ≤ y → y < L.offB + n →
    x / L.sector ≠ y / L.sector
  chain : ∀ s x y, L.off s ≤ x → x < L.off s + n → L.chainOff ≤ y →
    x / L.sector ≠ y / L.sector
  below : ∀ s, L.off s + n ≤ L.chainOff

/-- `TwoSlotHwm::paged`: slot A at the start of page `first`, slot B at the start of the next
    page, records from the page after. -/
@[expose] def Layout.paged (sector page first : Nat) : Layout :=
  ⟨sector, first * page, (first + 1) * page, (first + 2) * page⟩

private theorem div_ne_of_boundary {S x y m : Nat} (hS : 0 < S) (hx : x < m * S)
    (hy : m * S ≤ y) : x / S ≠ y / S := by
  have h1 : x / S < m :=
    Nat.lt_of_not_ge fun h => absurd ((Nat.le_div_iff_mul_le hS).1 h) (Nat.not_le_of_lt hx)
  have h2 : m ≤ y / S := (Nat.le_div_iff_mul_le hS).2 hy
  omega

/-- A slot that fits one page, on a device whose sector size divides the page size, is
    separated under the paged layout. Covers 512-byte and 4096-byte sectors for 4096-byte pages. -/
theorem Layout.paged_separated {sector page first n : Nat} (hS : 0 < sector)
    (hDiv : sector ∣ page) (hFit : n ≤ page) :
    (Layout.paged sector page first).Separated n := by
  obtain ⟨k, hk⟩ := hDiv
  have e1 : (first + 1) * page = first * page + page := Nat.succ_mul first page
  have e2 : (first + 2) * page = first * page + page + page := by
    rw [show first + 2 = (first + 1) + 1 from rfl, Nat.succ_mul, Nat.succ_mul]
  have b1 : (first + 1) * page = ((first + 1) * k) * sector := by
    rw [hk, Nat.mul_comm sector k, Nat.mul_assoc]
  have b2 : (first + 2) * page = ((first + 2) * k) * sector := by
    rw [hk, Nat.mul_comm sector k, Nat.mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · intro x y _ hx2 hy1 _
    have hx2 : x < first * page + n := hx2
    have hy1 : (first + 1) * page ≤ y := hy1
    show x / sector ≠ y / sector
    exact div_ne_of_boundary hS (m := (first + 1) * k) (by omega) (by omega)
  · intro s x y hx1 hx2 hy
    have hy : (first + 2) * page ≤ y := hy
    show x / sector ≠ y / sector
    cases s with
    | a =>
      have hx2 : x < first * page + n := hx2
      exact div_ne_of_boundary hS (m := (first + 2) * k) (by omega) (by omega)
    | b =>
      have hx2 : x < (first + 1) * page + n := hx2
      exact div_ne_of_boundary hS (m := (first + 2) * k) (by omega) (by omega)
  · intro s
    cases s with
    | a => show first * page + n ≤ (first + 2) * page; omega
    | b => show (first + 1) * page + n ≤ (first + 2) * page; omega

/-- The two authenticated on-disk formats. `verify` is `TwoSlotHwm::verify` (slot index, MAC,
    reserved bytes); `parse` is the record loop of `load_guarded` (length check, every record
    tag), reading the file from `chainOff` up to its length. -/
structure Codec (Tip Rec : Type) where
  slotLen : Nat
  bound : Nat
  encSlot : Slot → Nat → Tip → List UInt8
  verify : Slot → List UInt8 → Option (Nat × Tip)
  recLen : Nat
  encRec : Tip → Rec → List UInt8
  tag : Tip → Rec → Tip
  parse : Nat → Disk → Option (Head Tip)

structure Codec.Lawful {Tip Rec : Type} (C : Codec Tip Rec) (chainOff : Nat) : Prop where
  encSlot_length : ∀ s c t, (C.encSlot s c t).length = C.slotLen
  verify_encSlot : ∀ s c t, c < C.bound → C.verify s (C.encSlot s c t) = some (c, t)
  parse_local : ∀ d d' : Disk, (∀ x, chainOff ≤ x → d.bytes x = d'.bytes x) → d.len = d'.len →
    C.parse chainOff d = C.parse chainOff d'
  parse_append : ∀ (d : Disk) (h : Head Tip) (r : Rec), C.parse chainOff d = some h →
    C.parse chainOff (d.write (chainOff + C.recLen * h.len) (C.encRec h.tip r))
      = some ⟨h.len + 1, C.tag h.tip r, h.tip⟩

/-- What recovery sees: each slot authenticated or not, and the parsed chain. -/
structure View (Tip : Type) where
  a : Option (Nat × Tip)
  b : Option (Nat × Tip)
  chain : Option (Head Tip)

def View.get {Tip : Type} (v : View Tip) : Slot → Option (Nat × Tip)
  | .a => v.a
  | .b => v.b

def View.set {Tip : Type} (v : View Tip) : Slot → Option (Nat × Tip) → View Tip
  | .a, x => ⟨x, v.b, v.chain⟩
  | .b, x => ⟨v.a, x, v.chain⟩

theorem View.ext' {Tip : Type} {v w : View Tip} (ha : v.a = w.a) (hb : v.b = w.b)
    (hc : v.chain = w.chain) : v = w := by
  cases v; cases w
  cases ha; cases hb; cases hc
  rfl

theorem View.set_get_self {Tip : Type} (v : View Tip) (s : Slot) : v.set s (v.get s) = v := by
  cases s <;> rfl

theorem View.set_chain {Tip : Type} (v : View Tip) (s : Slot) (x : Option (Nat × Tip)) :
    (v.set s x).chain = v.chain := by
  cases s <;> rfl

section Protocol

variable {Tip Rec : Type}

def readSlot (C : Codec Tip Rec) (L : Layout) (d : Disk) (s : Slot) : List UInt8 :=
  readAt d.bytes (L.off s) C.slotLen

@[expose] def view (C : Codec Tip Rec) (L : Layout) (d : Disk) : View Tip :=
  ⟨C.verify .a (readSlot C L d .a), C.verify .b (readSlot C L d .b), C.parse L.chainOff d⟩

theorem view_get (C : Codec Tip Rec) (L : Layout) (d : Disk) (s : Slot) :
    (view C L d).get s = C.verify s (readSlot C L d s) := by
  cases s <;> rfl

/-- Unforgeability on the medium: after a crash each slot and the chain either fail to
    authenticate or decode as before or as after the unsynced writes. -/
@[expose] def NoForge (C : Codec Tip Rec) (L : Layout) (v : Dev) (d' : Disk) : Prop :=
  (∀ s, (view C L d').get s = none ∨ (view C L d').get s = (view C L v.durable).get s ∨
      (view C L d').get s = (view C L (v.durable.applyAll v.pending)).get s) ∧
  ((view C L d').chain = none ∨ (view C L d').chain = (view C L v.durable).chain ∨
      (view C L d').chain = (view C L (v.durable.applyAll v.pending)).chain)

/-- One `write_slot` without its `sync_all`. -/
structure SlotWrite (Tip : Type) where
  slot : Slot
  ctr : Nat
  tip : Tip

/-- `TwoSlotHwm::commit`: slot A, then slot B. -/
@[expose] def commitWrites (c : Nat) (t : Tip) : List (SlotWrite Tip) := [⟨.a, c, t⟩, ⟨.b, c, t⟩]

/-- `recover_from_lone_slot`. -/
@[expose] def loneSlot [DecidableEq Tip] (damaged : Slot) (c : Nat) (t : Tip) (h : Head Tip) :
    Option (List (SlotWrite Tip)) :=
  if h.len = c then (if h.tip = t then some [⟨damaged, c, h.tip⟩] else none)
  else if c + 1 = h.len then (if h.prev = t then some (commitWrites h.len h.tip) else none)
  else none

/-- `recover_with_outcome`: `none` is `Err(invalid())`, `some ws` the slot writes performed
    before `Ok` (`[]` for `Steady`). -/
@[expose] def recoverWrites [DecidableEq Tip] :
    Option (Nat × Tip) → Option (Nat × Tip) → Head Tip → Option (List (SlotWrite Tip))
  | some (a, ta), some (b, tb), h =>
    if a < b ∨ 1 < a - b then none
    else if h.len = a then
      (if h.tip = ta then (if b = a ∧ tb = ta then some [] else some [⟨.b, a, h.tip⟩]) else none)
    else if a + 1 = h.len then
      (if a = b ∧ ta = tb ∧ h.prev = ta then some (commitWrites h.len h.tip) else none)
    else none
  | some (c, t), none, h => loneSlot .b c t h
  | none, some (c, t), h => loneSlot .a c t h
  | none, none, _ => none

def slotPWrite (C : Codec Tip Rec) (L : Layout) (w : SlotWrite Tip) : PWrite :=
  ⟨L.off w.slot, C.encSlot w.slot w.ctr w.tip⟩

/-- Each slot write is followed by its own `fsync`. -/
def slotOps (C : Codec Tip Rec) (L : Layout) : List (SlotWrite Tip) → List Op
  | [] => []
  | w :: rest => .pwrite (slotPWrite C L w) :: .fsync :: slotOps C L rest

/-- `DurableBurnJournal::reserve` on a handle holding `n` records ending at `t`. -/
def reserveOps (C : Codec Tip Rec) (L : Layout) (n : Nat) (t : Tip) (r : Rec) : List Op :=
  .pwrite ⟨L.chainOff + C.recLen * n, C.encRec t r⟩ :: .fsync ::
    slotOps C L (commitWrites (n + 1) (C.tag t r))

/-- Run a list of operations; power may fail before any of them or after the last.
    The flag is `true` when every operation ran. -/
inductive Exec (C : Codec Tip Rec) (L : Layout) : Dev → List Op → Bool → Disk → Prop where
  | done (v : Dev) : v.pending = [] → Exec C L v [] true v.durable
  | op {v : Dev} {o : Op} {rest : List Op} {fin : Bool} {d' : Disk} :
      Exec C L (v.run o) rest fin d' → Exec C L v (o :: rest) fin d'
  | crash {v : Dev} {ops : List Op} {d' : Disk} :
      CrashImage L.sector v d' → NoForge C L v d' → Exec C L v ops false d'

/-- Strict-parser decision core: parse the whole chain, classify the slots, decide.
Production first attempts this path, then applies `recoverTruncatedAppendPlan` below to a
one-record uncommitted tail; the legacy append-tear counterexample concerns only this core. -/
def recoverPlan [DecidableEq Tip] (C : Codec Tip Rec) (L : Layout) (d : Disk) :
    Option (Head Tip × List (SlotWrite Tip)) :=
  match (view C L d).chain with
  | none => none
  | some h =>
    match recoverWrites (view C L d).a (view C L d).b h with
    | none => none
    | some ws => some (h, ws)

theorem recoverPlan_eq_some [DecidableEq Tip] {C : Codec Tip Rec} {L : Layout} {d : Disk}
    {h : Head Tip} {ws : List (SlotWrite Tip)} (hp : recoverPlan C L d = some (h, ws)) :
    (view C L d).chain = some h ∧ recoverWrites (view C L d).a (view C L d).b h = some ws := by
  unfold recoverPlan at hp
  cases hc : (view C L d).chain with
  | none => rw [hc] at hp; cases hp
  | some h' =>
    rw [hc] at hp
    have hp : (match recoverWrites (view C L d).a (view C L d).b h' with
      | none => none
      | some ws => some (h', ws)) = some (h, ws) := hp
    cases hw : recoverWrites (view C L d).a (view C L d).b h' with
    | none => rw [hw] at hp; cases hp
    | some ws' =>
      rw [hw] at hp
      cases hp
      exact ⟨rfl, hw⟩

theorem recoverPlan_of [DecidableEq Tip] {C : Codec Tip Rec} {L : Layout} {d : Disk}
    {h : Head Tip} {ws : List (SlotWrite Tip)} (hc : (view C L d).chain = some h)
    (hw : recoverWrites (view C L d).a (view C L d).b h = some ws) :
    recoverPlan C L d = some (h, ws) := by
  unfold recoverPlan
  rw [hc]
  show (match recoverWrites (view C L d).a (view C L d).b h with
    | none => none
    | some ws => some (h, ws)) = some (h, ws)
  rw [hw]

/-! ## 3. From bytes to views -/

/-- Slots read the same when their bytes agree. -/
theorem view_slots_congr (C : Codec Tip Rec) (L : Layout) {d d' : Disk}
    (h : ∀ s x, L.off s ≤ x → x < L.off s + C.slotLen → d'.bytes x = d.bytes x) :
    (view C L d').a = (view C L d).a ∧ (view C L d').b = (view C L d).b := by
  constructor
  · show C.verify .a (readAt d'.bytes (L.off .a) C.slotLen)
      = C.verify .a (readAt d.bytes (L.off .a) C.slotLen)
    rw [readAt_congr C.slotLen (L.off .a) (h .a)]
  · show C.verify .b (readAt d'.bytes (L.off .b) C.slotLen)
      = C.verify .b (readAt d.bytes (L.off .b) C.slotLen)
    rw [readAt_congr C.slotLen (L.off .b) (h .b)]

/-- A change confined to the sectors of slot `s` moves only that slot's entry of the view. -/
theorem view_slot_frame {C : Codec Tip Rec} {L : Layout} (hLaw : C.Lawful L.chainOff)
    (hSep : L.Separated C.slotLen) {d d' : Disk} (s : Slot)
    (hFar : ∀ x, (∀ y, L.off s ≤ y → y < L.off s + C.slotLen → x / L.sector ≠ y / L.sector) →
      d'.bytes x = d.bytes x)
    (hLen : d'.len = d.len) :
    view C L d' = (view C L d).set s ((view C L d').get s) := by
  have hChain : (view C L d').chain = (view C L d).chain :=
    hLaw.parse_local d' d
      (fun x hx => hFar x (fun y hy1 hy2 => Ne.symm (hSep.chain s y x hy1 hy2 hx))) hLen
  cases s with
  | a =>
    have hb : (view C L d').b = (view C L d).b := by
      show C.verify .b (readAt d'.bytes L.offB C.slotLen)
        = C.verify .b (readAt d.bytes L.offB C.slotLen)
      rw [readAt_congr C.slotLen L.offB
        (fun x hx1 hx2 => hFar x (fun y hy1 hy2 => Ne.symm (hSep.ab y x hy1 hy2 hx1 hx2)))]
    exact View.ext' (w := (view C L d).set .a ((view C L d').get .a)) rfl hb hChain
  | b =>
    have ha : (view C L d').a = (view C L d).a := by
      show C.verify .a (readAt d'.bytes L.offA C.slotLen)
        = C.verify .a (readAt d.bytes L.offA C.slotLen)
      rw [readAt_congr C.slotLen L.offA
        (fun x hx1 hx2 => hFar x (fun y hy1 hy2 => hSep.ab x y hx1 hx2 hy1 hy2))]
    exact View.ext' (w := (view C L d).set .b ((view C L d').get .b)) ha rfl hChain

private theorem sector_far_outside {S off n x : Nat}
    (hx : ∀ y, off ≤ y → y < off + n → x / S ≠ y / S) : x < off ∨ off + n ≤ x := by
  rcases Nat.lt_or_ge x off with a | a
  · exact Or.inl a
  · rcases Nat.lt_or_ge x (off + n) with b | b
    · exact absurd rfl (hx x a b)
    · exact Or.inr b

/-- A completed slot write. -/
theorem view_write_slot {C : Codec Tip Rec} {L : Layout} (hLaw : C.Lawful L.chainOff)
    (hSep : L.Separated C.slotLen) {d : Disk} (w : SlotWrite Tip)
    (hLen : L.chainOff ≤ d.len) (hB : w.ctr < C.bound) :
    view C L (d.write (L.off w.slot) (C.encSlot w.slot w.ctr w.tip))
      = (view C L d).set w.slot (some (w.ctr, w.tip)) := by
  have hEnc := hLaw.encSlot_length w.slot w.ctr w.tip
  have hBelow := hSep.below w.slot
  have hGet : (view C L (d.write (L.off w.slot) (C.encSlot w.slot w.ctr w.tip))).get w.slot
      = some (w.ctr, w.tip) := by
    rw [view_get]
    have hRead := Disk.readAt_write d (L.off w.slot) (C.encSlot w.slot w.ctr w.tip)
    rw [hEnc] at hRead
    show C.verify w.slot (readAt _ (L.off w.slot) C.slotLen) = _
    rw [hRead]
    exact hLaw.verify_encSlot w.slot w.ctr w.tip hB
  have hFrame := view_slot_frame hLaw hSep (d := d)
    (d' := d.write (L.off w.slot) (C.encSlot w.slot w.ctr w.tip)) w.slot
    (fun x hx => Disk.write_bytes_outside d _ _ (by rw [hEnc]; exact sector_far_outside hx))
    (by rw [Disk.write_len, hEnc]; omega)
  rw [hFrame, hGet]

/-- A slot write interrupted by a crash: the other slot and the chain are untouched; the slot
    being written reads as invalid, as before, or as intended. -/
theorem torn_slot_view {C : Codec Tip Rec} {L : Layout} (hLaw : C.Lawful L.chainOff)
    (hSep : L.Separated C.slotLen) {d d' : Disk} {w : SlotWrite Tip}
    (hLen : L.chainOff ≤ d.len) (hB : w.ctr < C.bound)
    (hC : CrashImage L.sector ⟨d, [slotPWrite C L w]⟩ d')
    (hN : NoForge C L ⟨d, [slotPWrite C L w]⟩ d') :
    L.chainOff ≤ d'.len ∧
      ∃ x, (x = none ∨ x = (view C L d).get w.slot ∨ x = some (w.ctr, w.tip)) ∧
        view C L d' = (view C L d).set w.slot x := by
  obtain ⟨x₀, h1, h2, hT, hl1, hl2⟩ := crashImage_single hC
  have hEnc := hLaw.encSlot_length w.slot w.ctr w.tip
  have hBelow := hSep.below w.slot
  have h2' : x₀ < L.off w.slot + (C.encSlot w.slot w.ctr w.tip).length := h2
  have hl2' : d'.len ≤ max d.len (L.off w.slot + (C.encSlot w.slot w.ctr w.tip).length) := hl2
  rw [hEnc] at hl2'
  have hLenEq : d'.len = d.len := by omega
  have hFrame := view_slot_frame hLaw hSep (d := d) (d' := d') w.slot
    (fun x hx => torn_frame (off := L.off w.slot) (bs := C.encSlot w.slot w.ctr w.tip) hT h1 h2'
      (fun y hy1 hy2 => hx y hy1 (by rw [hEnc] at hy2; exact hy2))) hLenEq
  refine ⟨by omega, (view C L d').get w.slot, ?_, hFrame⟩
  rcases hN.1 w.slot with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ?_)
    rw [h]
    have hW := view_write_slot hLaw hSep w hLen hB
    have hW' : view C L (Disk.applyAll d [slotPWrite C L w])
        = (view C L d).set w.slot (some (w.ctr, w.tip)) := hW
    rw [hW']
    cases w.slot <;> rfl

/-! ## 4. Recovery on views -/

/-- Slot-level effect of running `slotOps`, with a crash at any point. -/
inductive ViewExec : View Tip → List (SlotWrite Tip) → Bool → View Tip → Prop where
  | done (v : View Tip) : ViewExec v [] true v
  | step {v : View Tip} {w : SlotWrite Tip} {rest : List (SlotWrite Tip)} {fin : Bool}
      {v' : View Tip} :
      ViewExec (v.set w.slot (some (w.ctr, w.tip))) rest fin v' → ViewExec v (w :: rest) fin v'
  | stay {v : View Tip} {ws : List (SlotWrite Tip)} : ViewExec v ws false v
  | torn {v : View Tip} {w : SlotWrite Tip} {rest : List (SlotWrite Tip)}
      {x : Option (Nat × Tip)} :
      (x = none ∨ x = some (w.ctr, w.tip)) → ViewExec v (w :: rest) false (v.set w.slot x)

theorem ViewExec.chain_eq {v v' : View Tip} {ws : List (SlotWrite Tip)} {fin : Bool}
    (h : ViewExec v ws fin v') : v'.chain = v.chain := by
  induction h with
  | done _ => rfl
  | step _ ih => rw [ih, View.set_chain]
  | stay => rfl
  | torn _ => rw [View.set_chain]

theorem exec_slotOps {C : Codec Tip Rec} {L : Layout} (hLaw : C.Lawful L.chainOff)
    (hSep : L.Separated C.slotLen) :
    ∀ (ws : List (SlotWrite Tip)) (d : Disk) (fin : Bool) (d' : Disk),
      L.chainOff ≤ d.len → (∀ w ∈ ws, w.ctr < C.bound) →
      Exec C L ⟨d, []⟩ (slotOps C L ws) fin d' →
      ViewExec (view C L d) ws fin (view C L d') ∧ L.chainOff ≤ d'.len := by
  intro ws
  induction ws with
  | nil =>
    intro d fin d' hLen _ hE
    have hE : Exec C L ⟨d, []⟩ [] fin d' := hE
    cases hE with
    | done _ => exact ⟨.done _, hLen⟩
    | crash hC _ => rw [crashImage_nil hC]; exact ⟨.stay, hLen⟩
  | cons w rest ih =>
    intro d fin d' hLen hB hE
    have hE : Exec C L ⟨d, []⟩ (.pwrite (slotPWrite C L w) :: .fsync :: slotOps C L rest) fin d' :=
      hE
    cases hE with
    | crash hC _ => rw [crashImage_nil hC]; exact ⟨.stay, hLen⟩
    | op hE1 =>
      cases hE1 with
      | crash hC hN =>
        obtain ⟨hl, x, hx, hv⟩ :=
          torn_slot_view hLaw hSep hLen (hB w List.mem_cons_self) hC hN
        refine ⟨?_, hl⟩
        rw [hv]
        rcases hx with rfl | rfl | rfl
        · exact .torn (Or.inl rfl)
        · rw [View.set_get_self]; exact .stay
        · exact .torn (Or.inr rfl)
      | op hE2 =>
        have hE2 : Exec C L ⟨d.write (L.off w.slot) (C.encSlot w.slot w.ctr w.tip), []⟩
            (slotOps C L rest) fin d' := hE2
        have hLen1 : L.chainOff ≤ (d.write (L.off w.slot) (C.encSlot w.slot w.ctr w.tip)).len :=
          Nat.le_trans hLen (Disk.len_le_write_len _ _ _)
        obtain ⟨hV, hl⟩ := ih _ fin d' hLen1 (fun w' hw' => hB w' (List.mem_cons_of_mem _ hw')) hE2
        rw [view_write_slot hLaw hSep w hLen (hB w List.mem_cons_self)] at hV
        exact ⟨.step hV, hl⟩

/-- Both slots and the chain agree on `n` records ending at `t`. -/
def Steady (v : View Tip) (n : Nat) (t : Tip) : Prop :=
  v.a = some (n, t) ∧ v.b = some (n, t) ∧ ∃ p, v.chain = some ⟨n, t, p⟩

/-- Every image a crash can leave when the highest acknowledged counter is `G`: a base
    `(n, t)` with `G ≤ n` held by both slots (chain at `n`, or torn), or the chain one record
    ahead with the slots between the base and the new record. -/
def Fam (v : View Tip) (G : Nat) : Prop :=
  ∃ n t, G ≤ n ∧
    ((v.a = some (n, t) ∧ v.b = some (n, t) ∧ (v.chain = none ∨ ∃ p, v.chain = some ⟨n, t, p⟩)) ∨
     (∃ t', v.chain = some ⟨n + 1, t', t⟩ ∧
        ((v.b = some (n, t) ∧ (v.a = none ∨ v.a = some (n, t) ∨ v.a = some (n + 1, t'))) ∨
         (v.a = some (n + 1, t') ∧ v.b = none))))

theorem fam_of_steady {v : View Tip} {n G : Nat} {t : Tip} (h : Steady v n t) (hG : G ≤ n) :
    Fam v G :=
  ⟨n, t, hG, Or.inl ⟨h.1, h.2.1, Or.inr h.2.2⟩⟩

private theorem steady_mk (n : Nat) (t p : Tip) :
    Steady (⟨some (n, t), some (n, t), some ⟨n, t, p⟩⟩ : View Tip) n t :=
  ⟨rfl, rfl, p, rfl⟩

private theorem false_ne_true_imp {P : Prop} : (false = true → P) := fun h => by cases h

/-- Rewriting slot B onto the record that slot A already holds. -/
theorem repairB_view {G n : Nat} {t t' : Tip} {b : Option (Nat × Tip)} (hG : G ≤ n)
    (hb : b = none ∨ b = some (n, t)) {fin : Bool} {v' : View Tip}
    (h : ViewExec ⟨some (n + 1, t'), b, some ⟨n + 1, t', t⟩⟩ [⟨.b, n + 1, t'⟩] fin v') :
    Fam v' G ∧ (fin = true → Steady v' (n + 1) t') := by
  have hOrig : Fam (⟨some (n + 1, t'), b, some ⟨n + 1, t', t⟩⟩ : View Tip) G := by
    rcases hb with rfl | rfl
    · exact ⟨n, t, hG, Or.inr ⟨t', rfl, Or.inr ⟨rfl, rfl⟩⟩⟩
    · exact ⟨n, t, hG, Or.inr ⟨t', rfl, Or.inl ⟨rfl, Or.inr (Or.inr rfl)⟩⟩⟩
  have hNew : Steady (⟨some (n + 1, t'), some (n + 1, t'), some ⟨n + 1, t', t⟩⟩ : View Tip)
      (n + 1) t' := steady_mk _ _ _
  cases h with
  | step h1 =>
    cases h1 with
    | done _ => exact ⟨fam_of_steady hNew (by omega), fun _ => hNew⟩
    | stay => exact ⟨fam_of_steady hNew (by omega), false_ne_true_imp⟩
  | stay => exact ⟨hOrig, false_ne_true_imp⟩
  | torn hx =>
    refine ⟨?_, false_ne_true_imp⟩
    rcases hx with rfl | rfl
    · exact ⟨n, t, hG, Or.inr ⟨t', rfl, Or.inr ⟨rfl, rfl⟩⟩⟩
    · exact fam_of_steady hNew (by omega)

/-- `commit` onto a record the chain already holds, from any slot A the family allows. -/
theorem commit_view {G n : Nat} {t t' : Tip} {a : Option (Nat × Tip)} (hG : G ≤ n)
    (ha : a = none ∨ a = some (n, t) ∨ a = some (n + 1, t')) {fin : Bool} {v' : View Tip}
    (h : ViewExec ⟨a, some (n, t), some ⟨n + 1, t', t⟩⟩ (commitWrites (n + 1) t') fin v') :
    Fam v' G ∧ (fin = true → Steady v' (n + 1) t') := by
  have h : ViewExec ⟨a, some (n, t), some ⟨n + 1, t', t⟩⟩
      [⟨.a, n + 1, t'⟩, ⟨.b, n + 1, t'⟩] fin v' := h
  cases h with
  | step h1 => exact repairB_view hG (Or.inr rfl) h1
  | stay => exact ⟨⟨n, t, hG, Or.inr ⟨t', rfl, Or.inl ⟨rfl, ha⟩⟩⟩, false_ne_true_imp⟩
  | torn hx =>
    refine ⟨⟨n, t, hG, Or.inr ⟨t', rfl, Or.inl ⟨rfl, ?_⟩⟩⟩, false_ne_true_imp⟩
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)

private theorem ctr_commit {n : Nat} {t' : Tip} :
    ∀ w ∈ commitWrites (n + 1) t', w.ctr = n + 1 := by
  intro w hw
  have hw : w ∈ [(⟨.a, n + 1, t'⟩ : SlotWrite Tip), ⟨.b, n + 1, t'⟩] := hw
  rcases List.mem_cons.mp hw with rfl | hw
  · rfl
  · rcases List.mem_cons.mp hw with rfl | hw
    · rfl
    · exact absurd hw List.not_mem_nil

private theorem ctr_single {n : Nat} {t' : Tip} :
    ∀ w ∈ [(⟨.b, n + 1, t'⟩ : SlotWrite Tip)], w.ctr = n + 1 := by
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hw
  · rfl
  · exact absurd hw List.not_mem_nil

section Decide

variable [DecidableEq Tip]

private theorem rw_steady (n : Nat) (t p : Tip) :
    recoverWrites (some (n, t)) (some (n, t)) (⟨n, t, p⟩ : Head Tip) = some [] := by
  simp only [recoverWrites, ↓reduceIte, and_self]
  rw [ite_eq_right (by omega)]

private theorem rw_adv_both (n : Nat) (t t' : Tip) :
    recoverWrites (some (n, t)) (some (n, t)) (⟨n + 1, t', t⟩ : Head Tip)
      = some (commitWrites (n + 1) t') := by
  simp only [recoverWrites, ↓reduceIte, and_self]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

private theorem rw_adv_lone (n : Nat) (t t' : Tip) :
    recoverWrites none (some (n, t)) (⟨n + 1, t', t⟩ : Head Tip)
      = some (commitWrites (n + 1) t') := by
  simp only [recoverWrites, loneSlot, ↓reduceIte]
  rw [ite_eq_right (by omega)]

private theorem rw_repair (n : Nat) (t t' : Tip) :
    recoverWrites (some (n + 1, t')) (some (n, t)) (⟨n + 1, t', t⟩ : Head Tip)
      = some [⟨.b, n + 1, t'⟩] := by
  simp only [recoverWrites, ↓reduceIte]
  rw [ite_eq_right (by omega), ite_eq_right (fun h => by have := h.1; omega)]

private theorem rw_lone_b (n : Nat) (t t' : Tip) :
    recoverWrites (some (n + 1, t')) none (⟨n + 1, t', t⟩ : Head Tip)
      = some [⟨.b, n + 1, t'⟩] := by
  simp only [recoverWrites, loneSlot, ↓reduceIte]

/-- In every image of the family whose chain parses, recovery decides to proceed, returns a
    counter at or above `G`, and stays inside the family however its own writes are cut. -/
