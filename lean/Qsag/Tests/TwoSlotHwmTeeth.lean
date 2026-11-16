module

public import Qsag.Exec.TwoSlotHwmCrashModel
import Qsag.Tactic.AssuranceKit

/-!
# Qsag.Tests.TwoSlotHwmTeeth — a concrete codec for the two-slot crash model

`toyCodec` is a lawful `Codec` with 80-byte slots and 2-byte records, small enough to compute
with: a slot is `counter byte, tip byte, slot marker, 77 zero bytes`; the chain is any even
number of bytes after `chainOff`, its tip the parity of the record count. It has no secret, so
it says nothing about forgery; it shows that the hypotheses of the theorems in
`Qsag.Exec.TwoSlotHwmCrashModel` are jointly satisfiable and that their teeth bite on bytes.

* `toy_qsburn05_safe` with `toy_trace_witness`: a provisioned `QSBURN05` image on 512-byte
  sectors, recovered, with one acknowledged `reserve`.
* `toy_qsburn04_single_tear`: the shared-sector layout loses both slots to one torn sector.
* `toy_append_tear_fails_closed`: one junk byte where a record was being appended leaves an
  odd-length chain; recovery refuses.
-/

public section

namespace Qsag.Tests.TwoSlotHwmTeeth

open Qsag.Exec.TwoSlotHwmCrashModel

set_option autoImplicit false

def par : Nat → Bool
  | 0 => false
  | n + 1 => !par n

def marker : Slot → UInt8
  | .a => 0xA1
  | .b => 0xB2

def toyEnc (s : Slot) (c : Nat) (t : Bool) : List UInt8 :=
  UInt8.ofNat c :: (if t then 1 else 0) :: marker s :: List.replicate 77 0

def toyVerify : Slot → List UInt8 → Option (Nat × Bool)
  | s, x :: y :: m :: rest =>
    if m = marker s ∧ rest.length = 77 then some (x.toNat, y != 0) else none
  | _, _ => none

def toyParse (off : Nat) (d : Disk) : Option (Head Bool) :=
  if off ≤ d.len ∧ (d.len - off) % 2 = 0 then
    some ⟨(d.len - off) / 2, par ((d.len - off) / 2), !par ((d.len - off) / 2)⟩
  else none

def toyCodec : Codec Bool Unit where
  slotLen := 80
  bound := 256
  encSlot := toyEnc
  verify := toyVerify
  recLen := 2
  encRec _ _ := [0x7E, 0x7E]
  tag t _ := !t
  parse := toyParse

theorem toyVerify_enc (s : Slot) (c : Nat) (t : Bool) (hc : c < 256) :
    toyVerify s (toyEnc s c t) = some (c, t) := by
  show (if marker s = marker s ∧ (List.replicate 77 (0 : UInt8)).length = 77 then
    some ((UInt8.ofNat c).toNat, (if t then (1 : UInt8) else 0) != 0) else none) = some (c, t)
  rw [ite_eq_left ⟨rfl, List.length_replicate⟩, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hc]
  cases t <;> rfl

theorem toyLawful (off : Nat) : toyCodec.Lawful off where
  encSlot_length s c t := by
    show (UInt8.ofNat c :: (if t then 1 else 0) :: marker s :: List.replicate 77 0).length = 80
    rw [List.length_cons, List.length_cons, List.length_cons, List.length_replicate]
  verify_encSlot s c t hc := toyVerify_enc s c t hc
  parse_local d d' _ hLen := by
    show toyParse off d = toyParse off d'
    unfold toyParse
    rw [hLen]
  parse_append d h r hp := by
    have hp : toyParse off d = some h := hp
    unfold toyParse at hp
    rcases Nat.lt_or_ge d.len off with hlt | hge
    · rw [ite_eq_right (fun hh => absurd hh.1 (Nat.not_le_of_lt hlt))] at hp
      cases hp
    · rcases Nat.mod_two_eq_zero_or_one (d.len - off) with hm | hm
      · rw [ite_eq_left ⟨hge, hm⟩] at hp
        cases hp
        show toyParse off (d.write (off + 2 * ((d.len - off) / 2)) [0x7E, 0x7E]) = _
        have hl : (d.write (off + 2 * ((d.len - off) / 2)) [0x7E, 0x7E]).len
            = off + 2 * ((d.len - off) / 2 + 1) := by
          rw [Disk.write_len]
          show max d.len (off + 2 * ((d.len - off) / 2) + 2) = _
          omega
        unfold toyParse
        rw [hl, Nat.add_sub_cancel_left, ite_eq_left ⟨Nat.le_add_right _ _, by omega⟩]
        have hd : 2 * ((d.len - off) / 2 + 1) / 2 = (d.len - off) / 2 + 1 := by omega
        rw [hd]
        show some (⟨_, !par ((d.len - off) / 2), !!par ((d.len - off) / 2)⟩ : Head Bool) = _
        rw [Bool.not_not]
        rfl
      · rw [ite_eq_right (fun hh => by have := hh.2; omega)] at hp
        cases hp

/-- A zero-filled header with both slots written at `(0, false)` and no records. -/
def toyImage : Disk :=
  ((⟨fun _ => 0, (qsburn05 512).chainOff⟩ : Disk).write ((qsburn05 512).off .a)
    (toyCodec.encSlot .a 0 false)).write ((qsburn05 512).off .b) (toyCodec.encSlot .b 0 false)

theorem toy_provisioned : Init toyCodec (qsburn05 512) ⟨toyImage, 0, none⟩ := by
  have hSep : (qsburn05 512).Separated toyCodec.slotLen :=
    qsburn05_separated (by decide) ⟨8, by decide⟩
  have hc : (view toyCodec (qsburn05 512) ⟨fun _ => 0, (qsburn05 512).chainOff⟩).chain
      = some ⟨0, false, true⟩ := by
    show toyParse (qsburn05 512).chainOff ⟨fun _ => 0, (qsburn05 512).chainOff⟩ = _
    unfold toyParse
    rw [ite_eq_left ⟨Nat.le_refl _, by rw [Nat.sub_self]⟩, Nat.sub_self]
    rfl
  have hS := provisioned_steady (toyLawful _) hSep (Nat.le_refl _) (by decide) hc
  refine Init.intro rfl ?_ (Nat.le_refl 0) (by decide) hS
  exact Nat.le_trans
    (Disk.len_le_write_len ⟨fun _ => 0, (qsburn05 512).chainOff⟩ ((qsburn05 512).off .a)
      (toyCodec.encSlot .a 0 false)) (Disk.len_le_write_len _ _ _)

/-- `qsburn05_safe` on 512-byte sectors for the concrete codec. -/
theorem toy_qsburn05_safe {s₀ s : Sys Bool} (hInit : Init toyCodec (qsburn05 512) s₀)
    (hReach : Reach toyCodec (qsburn05 512) s₀ s) :
    (∀ h ws, recoverPlan toyCodec (qsburn05 512) s.disk = some (h, ws) → s.acked ≤ h.len) ∧
    (∀ h, (view toyCodec (qsburn05 512) s.disk).chain = some h →
      ∃ ws, recoverPlan toyCodec (qsburn05 512) s.disk = some (h, ws)) ∧
    (∀ n t, s.live = some (n, t) → s.acked ≤ n) :=
  qsburn05_safe (by decide) ⟨8, by decide⟩ rfl (toyLawful _) hInit hReach

/-- A provisioned image, recovered, with one `reserve` acknowledged. -/
theorem toy_trace_witness : ∃ s₀ s : Sys Bool,
    Init toyCodec (qsburn05 512) s₀ ∧ Reach toyCodec (qsburn05 512) s₀ s := by
  have hInit := toy_provisioned
  obtain ⟨s, hReach, _⟩ := init_can_commit hInit ()
    (fun h hc => by
      have hc : toyParse (qsburn05 512).chainOff toyImage = some h := hc
      unfold toyParse at hc
      have hl : toyImage.len = (qsburn05 512).chainOff := by
        show max (max (qsburn05 512).chainOff ((qsburn05 512).off .a + 80))
          ((qsburn05 512).off .b + 80) = (qsburn05 512).chainOff
        have ho := qsburn05_offsets 512
        have ha : (qsburn05 512).off .a = 4096 := ho.1
        have hb : (qsburn05 512).off .b = 8192 := ho.2.1
        rw [ha, hb, ho.2.2]
        decide
      rw [hl, Nat.sub_self, ite_eq_left ⟨Nat.le_refl _, rfl⟩] at hc
      cases hc
      decide)
  exact ⟨_, s, hInit, hReach⟩

/-- Both slots in sector 0: an acknowledged commit, then one torn sector, then nothing to
    recover from. The junk is 80 zero bytes over each slot. -/
theorem toy_qsburn04_single_tear {s : Sys Bool} {n : Nat} {t : Bool}
    (hLive : s.live = some (n, t)) (hAck : s.acked ≤ n) (hBound : n + 2 < 256) :
    ∃ s₁ s₂, Step toyCodec sharedSectorLayout s s₁ ∧ s₁.acked = n + 1 ∧
      Step toyCodec sharedSectorLayout s₁ s₂ ∧ s₂.acked = n + 1 ∧
      (view toyCodec sharedSectorLayout s₂.disk).a = none ∧
      (view toyCodec sharedSectorLayout s₂.disk).b = none ∧
      recoverPlan toyCodec sharedSectorLayout s₂.disk = none :=
  qsburn04_single_tear_loses_state (C := toyCodec) rfl (toyLawful _)
    (jA := List.replicate 80 0) (jB := List.replicate 80 0) List.length_replicate
    List.length_replicate (by decide) (by decide) hLive hAck hBound () ()

/-- One junk byte in place of a 2-byte record: the chain has odd length and recovery refuses,
    with both slots intact. -/
theorem toy_append_tear_fails_closed {s : Sys Bool} {n : Nat} {t : Bool}
    (hLive : s.live = some (n, t)) (hBound : n + 1 < 256)
    (hLen : s.disk.len = (qsburn05 512).chainOff + 2 * n) :
    ∃ s', Step toyCodec (qsburn05 512) s s' ∧ s'.acked = s.acked ∧
      (view toyCodec (qsburn05 512) s'.disk).a = (view toyCodec (qsburn05 512) s.disk).a ∧
      (view toyCodec (qsburn05 512) s'.disk).b = (view toyCodec (qsburn05 512) s.disk).b ∧
      recoverPlan toyCodec (qsburn05 512) s'.disk = none := by
  have hSep : (qsburn05 512).Separated toyCodec.slotLen :=
    qsburn05_separated (by decide) ⟨8, by decide⟩
  refine append_tear_fails_closed (C := toyCodec) hSep.below hLive hBound () (j := [0])
    (by decide) (by show 1 ≤ 2; omega) ?_ ?_
  · intro x h1 h2
    have h2 : x < (qsburn05 512).chainOff + 2 * n + 1 := h2
    have h1 : (qsburn05 512).chainOff + 2 * n ≤ x := h1
    have hx : x = (qsburn05 512).chainOff + 2 * n := by omega
    rw [hx]
    rfl
  · show toyParse (qsburn05 512).chainOff
      (s.disk.write ((qsburn05 512).chainOff + 2 * n) [0]) = none
    unfold toyParse
    have hl : (s.disk.write ((qsburn05 512).chainOff + 2 * n) [0]).len
        = (qsburn05 512).chainOff + (2 * n + 1) := by
      rw [Disk.write_len, hLen]
      show max _ ((qsburn05 512).chainOff + 2 * n + 1) = _
      omega
    rw [hl, Nat.add_sub_cancel_left, ite_eq_right (fun hh => by have := hh.2; omega)]

/-- Byte-level torn append on `toyImage` (`Slot A = 0, Slot B = 0`, 1-byte torn tail):
    `recoverPlan` fails closed, while `recoverTruncatedAppendPlan` truncates back to `chainOff`
    and recovers counter `0`. -/
def toyTornSteady : Disk :=
  toyImage.write (qsburn05 512).chainOff [0xEE]

/-- Byte-level torn append after record `0` reached disk before HWM updated (`Slot A = 0, Slot B = 0`,
    `committed = 1 = hwm + 1`, plus 1-byte torn tail of record `1`):
    `recoverTruncatedAppendPlan` keeps committed record `0` and converges slots to `1`. -/
def toyTornCommittedPlusOne : Disk :=
  (toyImage.write (qsburn05 512).chainOff [0x7E, 0x7E]).write ((qsburn05 512).chainOff + 2) [0xEE]

/-- Byte-level torn append with staggered HWM slots (`Slot A = 1, Slot B = 0`, `committed = 1`,
    plus 1-byte torn tail of record `1`): `slotsPermitTailTruncation` accepts `(1, 0)` at `1`. -/
def toyTornStaggeredSlots : Disk :=
  (((toyImage.write (qsburn05 512).chainOff [0x7E, 0x7E]).write ((qsburn05 512).off .a)
      (toyCodec.encSlot .a 1 true)).write ((qsburn05 512).chainOff + 2) [0xEE])

/-- Byte-level gap violation (`Slot A = 0, Slot B = 0`, two records + 1-byte torn tail so
    `committed = 2 > 0 + 1`): `recoverTruncatedAppendPlan` fails closed. -/
def toyTornGapTwo : Disk :=
  (((toyImage.write (qsburn05 512).chainOff [0x7E, 0x7E]).write ((qsburn05 512).chainOff + 2)
      [0x7E, 0x7E]).write ((qsburn05 512).chainOff + 4) [0xEE])

theorem toy_append_tear_truncate_recovers_all_modes :
    recoverPlan toyCodec (qsburn05 512) toyTornSteady = none ∧
    (recoverTruncatedAppendPlan toyCodec (qsburn05 512) toyTornSteady).map (fun r => (r.1.len, r.2.1.len)) =
      some ((qsburn05 512).chainOff, 0) ∧
    (recoverTruncatedAppendPlan toyCodec (qsburn05 512) toyTornCommittedPlusOne).map (fun r => (r.1.len, r.2.1.len)) =
      some ((qsburn05 512).chainOff + 2, 1) ∧
    (recoverTruncatedAppendPlan toyCodec (qsburn05 512) toyTornStaggeredSlots).map (fun r => (r.1.len, r.2.1.len)) =
      some ((qsburn05 512).chainOff + 2, 1) := by
  decide +kernel

theorem tooth_toy_slot_gap_two_rejected :
    recoverTruncatedAppendPlan toyCodec (qsburn05 512) toyTornGapTwo = none := by
  decide +kernel

theorem witness_append_tear_truncate_recovers :
    ∃ (Tip Rec : Type) (_ : DecidableEq Tip) (C : Codec Tip Rec) (L : Layout) (d : Disk)
      (committed : Nat) (h : Head Tip) (ws : List (SlotWrite Tip)),
      0 < C.recLen ∧
      recoverPlan C L d = none ∧
      (L.chainOff + C.recLen * committed < d.len ∧
        d.len - (L.chainOff + C.recLen * committed) ≤ C.recLen) ∧
      slotsPermitTailTruncation C L d committed = true ∧
      recoverPlan C L (d.truncate (L.chainOff + C.recLen * committed)) = some (h, ws) := by
  refine ⟨Bool, Unit, inferInstance, toyCodec, qsburn05 512, toyTornCommittedPlusOne,
    1, ⟨1, true, false⟩, commitWrites 1 true, by decide, by decide +kernel,
    ⟨by decide +kernel, by decide +kernel⟩, by decide +kernel, by decide +kernel⟩

#verify_constructive toyLawful toy_provisioned toy_qsburn05_safe toy_trace_witness
#verify_constructive toy_qsburn04_single_tear toy_append_tear_fails_closed
#verify_inhabited toy_qsburn05_safe toy_trace_witness
#tooth_pair toy_qsburn05_safe vs toy_qsburn04_single_tear
#tooth_pair toy_qsburn05_safe vs toy_append_tear_fails_closed
#verify_constructive toy_append_tear_truncate_recovers_all_modes tooth_toy_slot_gap_two_rejected witness_append_tear_truncate_recovers
#verify_inhabited Qsag.Exec.TwoSlotHwmCrashModel.append_tear_truncate_recovers witness_append_tear_truncate_recovers
#tooth_pair toy_append_tear_truncate_recovers_all_modes vs tooth_toy_slot_gap_two_rejected

end Qsag.Tests.TwoSlotHwmTeeth
