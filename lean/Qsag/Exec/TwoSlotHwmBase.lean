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

@[expose] def Disk.apply (d : Disk) (w : PWrite) : Disk := d.write w.off w.data

@[expose] def Disk.applyAll (d : Disk) (ws : List PWrite) : Disk := ws.foldl Disk.apply d

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


@[expose] def Disk.truncate (d : Disk) (n : Nat) : Disk := ⟨d.bytes, n⟩

@[simp] theorem Disk.truncate_bytes (d : Disk) (n x : Nat) : (d.truncate n).bytes x = d.bytes x := by rfl
@[simp] theorem Disk.truncate_len (d : Disk) (n : Nat) : (d.truncate n).len = n := by rfl

#verify_constructive overlay_outside readAt_congr readAt_overlay crashImage_single torn_frame Layout.paged_separated

end Qsag.Exec.TwoSlotHwmCrashModel
end
