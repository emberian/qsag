module

public import Qsag.Exec.TwoSlotHwmCrashModel
public import Qsag.Oracle.Sponge
import Qsag.Tactic.AssuranceKit

/-!
# Qsag.Tests.TwoSlotHwmTeeth — Keyed `cSHAKE256` MAC Codec for the Two-Slot Crash Model

`cshakeWalCodec` instantiates `TwoSlotHwmCrashModel.Codec` with real 24-round `keccakF1600`
NIST SP 800-185 `cSHAKE256` (`"QSAG.WAL.HWM.MAC/v1"`) authentication over a 32-byte secret key:
* **80-byte HWM slots (`Slot.a`, `Slot.b`)**: `[ctrByte, slotMarker] ++ tip256 (32B) ++ slotMac256 (32B) ++ zeros (14B)`,
  authenticated under `(walKey, slotMarker, ctrByte, tip256)`.
* **34-byte append-only journal records**: `[recByte, 0x5A] ++ chainMac256 (32B)`, chaining
  `nextTip := cSHAKE256(walKey, 0x11 || prevTip256 || recByte)` from `genesisTip := cSHAKE256(walKey, 0x10)`.

Verified properties and teeth:
* `cshakeWal_qsburn05_safe` with `cshakeWal_trace_witness`: provisioned `QSBURN05` image on 512-byte
  sectors, recovered, with one acknowledged `reserve`.
* `cshakeWal_qsburn04_single_tear`: shared-sector layout loses both slots to one torn sector.
* `cshakeWal_append_tear_fails_closed`: partial record tear fails closed in `recoverPlan`.
* `cshakeWal_append_tear_truncate_recovers_all_modes` & `tooth_cshakeWal_slot_gap_two_rejected`:
  1-record uncommitted tail truncates cleanly while a 2-record gap fails closed.
* `tooth_cshakeWal_wrong_key_rejected`: forging a slot or record under a distinct key `altWalKey ≠ testWalKey`
  is rejected by both `verify` and `recoverTruncatedAppendPlan`!
-/

public section

namespace Qsag.Tests.TwoSlotHwmTeeth

open Qsag
open Qsag.Exec.TwoSlotHwmCrashModel

set_option autoImplicit false

private def kZeroState : KState :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

private def kLoadLe64 (block : List UInt8) (laneIdx : Nat) : UInt64 :=
  let base := 8 * laneIdx
  (block.getD base 0).toUInt64 |||
  ((block.getD (base + 1) 0).toUInt64 <<< 8) |||
  ((block.getD (base + 2) 0).toUInt64 <<< 16) |||
  ((block.getD (base + 3) 0).toUInt64 <<< 24) |||
  ((block.getD (base + 4) 0).toUInt64 <<< 32) |||
  ((block.getD (base + 5) 0).toUInt64 <<< 40) |||
  ((block.getD (base + 6) 0).toUInt64 <<< 48) |||
  ((block.getD (base + 7) 0).toUInt64 <<< 56)

private def kXorRate136 (s : KState) (block : List UInt8) : KState :=
  { s with
    a0  := s.a0  ^^^ kLoadLe64 block 0,  a1  := s.a1  ^^^ kLoadLe64 block 1,
    a2  := s.a2  ^^^ kLoadLe64 block 2,  a3  := s.a3  ^^^ kLoadLe64 block 3,
    a4  := s.a4  ^^^ kLoadLe64 block 4,  a5  := s.a5  ^^^ kLoadLe64 block 5,
    a6  := s.a6  ^^^ kLoadLe64 block 6,  a7  := s.a7  ^^^ kLoadLe64 block 7,
    a8  := s.a8  ^^^ kLoadLe64 block 8,  a9  := s.a9  ^^^ kLoadLe64 block 9,
    a10 := s.a10 ^^^ kLoadLe64 block 10, a11 := s.a11 ^^^ kLoadLe64 block 11,
    a12 := s.a12 ^^^ kLoadLe64 block 12, a13 := s.a13 ^^^ kLoadLe64 block 13,
    a14 := s.a14 ^^^ kLoadLe64 block 14, a15 := s.a15 ^^^ kLoadLe64 block 15,
    a16 := s.a16 ^^^ kLoadLe64 block 16 }

private def kLaneBytesLE (w : UInt64) : List UInt8 :=
  [UInt8.ofNat (w.toNat % 256),
   UInt8.ofNat ((w.toNat / 256) % 256),
   UInt8.ofNat ((w.toNat / 65536) % 256),
   UInt8.ofNat ((w.toNat / 16777216) % 256),
   UInt8.ofNat ((w.toNat / 4294967296) % 256),
   UInt8.ofNat ((w.toNat / 1099511627776) % 256),
   UInt8.ofNat ((w.toNat / 281474976710656) % 256),
   UInt8.ofNat ((w.toNat / 72057594037927936) % 256)]

private def kRateBlockBytes (s : KState) : List UInt8 :=
  kLaneBytesLE s.a0 ++ kLaneBytesLE s.a1 ++ kLaneBytesLE s.a2 ++ kLaneBytesLE s.a3 ++
  kLaneBytesLE s.a4 ++ kLaneBytesLE s.a5 ++ kLaneBytesLE s.a6 ++ kLaneBytesLE s.a7 ++
  kLaneBytesLE s.a8 ++ kLaneBytesLE s.a9 ++ kLaneBytesLE s.a10 ++ kLaneBytesLE s.a11 ++
  kLaneBytesLE s.a12 ++ kLaneBytesLE s.a13 ++ kLaneBytesLE s.a14 ++ kLaneBytesLE s.a15 ++
  kLaneBytesLE s.a16

/-- Precomputed 136-byte SP 800-185 `bytepad(encodeString("") || encodeString("QSAG.WAL.HWM.MAC/v1"), 136)`. -/
private def walMacPrefix136 : List UInt8 :=
  [
   0x01, 0x88, 0x01, 0x00, 0x01, 0x98, 0x51, 0x53, 0x41, 0x47, 0x2E, 0x57, 0x41, 0x4C, 0x2E, 0x48, 0x57,
   0x4D, 0x2E, 0x4D, 0x41, 0x43, 0x2F, 0x76, 0x31, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
   0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

/-- Keyed 256-bit NIST SP 800-185 `cSHAKE256` (`keccakF1600`, domain `0x04`) authenticator. -/
def cshakeWalMac256 (role : UInt8) (walKey payload : List UInt8) : BitVec 256 :=
  let framed := walMacPrefix136 ++ (role :: (be 8 walKey.length ++ walKey ++ payload))
  BitVec.ofNat 256 (ofBE (evalSponge 136 0x04 keccakF1600 kZeroState kXorRate136 kRateBlockBytes framed 32))

def marker : Slot → UInt8
  | .a => 0xA1
  | .b => 0xB2

/-- Genesis chain accumulator `cSHAKE256(walKey, 0x10)` for an empty 0-record journal. -/
def walGenesisTip (walKey : List UInt8) : BitVec 256 :=
  cshakeWalMac256 0x10 walKey []

/-- Rolling chain tag `cSHAKE256(walKey, 0x11 || prevTip || recByte)`. -/
def walChainTag (walKey : List UInt8) (prevTip : BitVec 256) (r : UInt8) : BitVec 256 :=
  cshakeWalMac256 0x11 walKey (be 32 prevTip.toNat ++ [r])

/-- Slot MAC `cSHAKE256(walKey, 0x20 || marker(s) || ctrByte || tip)`. -/
def walSlotMac (walKey : List UInt8) (s : Slot) (ctrByte : UInt8) (tip : BitVec 256) : BitVec 256 :=
  cshakeWalMac256 0x20 walKey (marker s :: ctrByte :: be 32 tip.toNat)

/-- Encode an 80-byte `QSBURN05` HWM slot: `ctr (1B) || marker (1B) || tip (32B) || mac (32B) || zeros (14B)`. -/
def walEncSlot (walKey : List UInt8) (s : Slot) (c : Nat) (t : BitVec 256) : List UInt8 :=
  let cb := UInt8.ofNat c
  let mac := walSlotMac walKey s cb t
  cb :: marker s :: (be 32 t.toNat ++ (be 32 mac.toNat ++ List.replicate 14 0))

/-- Verify an 80-byte `QSBURN05` HWM slot: check length, slot marker, reserved zero tail, and 32-byte `cSHAKE256` MAC. -/
def walVerifySlot (walKey : List UInt8) (s : Slot) (bs : List UInt8) : Option (Nat × BitVec 256) :=
  match bs with
  | cb :: m :: rest =>
    if m = marker s ∧ rest.length = 78 ∧ rest.drop 64 = List.replicate 14 0 then
      let tip := BitVec.ofNat 256 (ofBE (rest.take 32))
      let macBytes := (rest.drop 32).take 32
      if macBytes = be 32 (walSlotMac walKey s cb tip).toNat then
        some (cb.toNat, tip)
      else none
    else none
  | _ => none

/-- Encode a 34-byte authenticated WAL record: `recByte (1B) || 0x5A (1B) || chainMac (32B)`. -/
def walEncRec (walKey : List UInt8) (prevTip : BitVec 256) (r : UInt8) : List UInt8 :=
  r :: (0x5A : UInt8) :: be 32 (walChainTag walKey prevTip r).toNat

/-- Verify `k` consecutive 34-byte MAC-chained records starting at `off`. -/
def walParseRecords (walKey : List UInt8) (off : Nat) (d : Disk) : Nat → Option (Head (BitVec 256))
  | 0 => some ⟨0, walGenesisTip walKey, 0#256⟩
  | k + 1 =>
    match walParseRecords walKey off d k with
    | none => none
    | some h =>
      let recBytes := readAt d.bytes (off + 34 * k) 34
      let r := recBytes.getD 0 0
      let nextTip := walChainTag walKey h.tip r
      if recBytes.getD 1 0 = 0x5A ∧ recBytes.drop 2 = be 32 nextTip.toNat then
        some ⟨k + 1, nextTip, h.tip⟩
      else none

def walParse (walKey : List UInt8) (off : Nat) (d : Disk) : Option (Head (BitVec 256)) :=
  if off ≤ d.len ∧ (d.len - off) % 34 = 0 then
    walParseRecords walKey off d ((d.len - off) / 34)
  else none

/-- Keyed `cSHAKE256` MAC `Codec` with 80-byte slots and 34-byte authenticated records. -/
def cshakeWalCodec (walKey : List UInt8) : Codec (BitVec 256) UInt8 where
  slotLen := 80
  bound := 256
  encSlot := walEncSlot walKey
  verify := walVerifySlot walKey
  recLen := 34
  encRec := walEncRec walKey
  tag := walChainTag walKey
  parse := walParse walKey

section SymbolicWalProofs
attribute [local irreducible] cshakeWalMac256

private theorem bv256_lt_pow : ∀ (v : BitVec 256), v.toNat < 256 ^ 32 := fun v => by
  have hPow : (2 : Nat) ^ 256 = 256 ^ 32 := by decide
  rw [← hPow]; exact v.isLt

private theorem bv256_roundtrip (v : BitVec 256) : BitVec.ofNat 256 (ofBE (be 32 v.toNat)) = v := by
  rw [ofBE_be (bv256_lt_pow v)]
  exact BitVec.eq_of_toNat_eq (Nat.mod_eq_of_lt v.isLt)

theorem walVerifySlot_enc (walKey : List UInt8) (s : Slot) (c : Nat) (t : BitVec 256) (hc : c < 256) :
    walVerifySlot walKey s (walEncSlot walKey s c t) = some (c, t) := by
  unfold walEncSlot walVerifySlot
  dsimp only
  let cb := UInt8.ofNat c
  let mac := walSlotMac walKey s cb t
  let tail := be 32 mac.toNat ++ List.replicate 14 (0 : UInt8)
  have h32t : (be 32 t.toNat).length = 32 := length_be 32 _
  have h32m : (be 32 mac.toNat).length = 32 := length_be 32 _
  have hRestLen : (be 32 t.toNat ++ tail).length = 78 := by
    simp only [tail, List.length_append, h32t, h32m, List.length_replicate]
  have hDrop64 : (be 32 t.toNat ++ tail).drop 64 = List.replicate 14 0 := by
    have hd : ((be 32 t.toNat ++ tail).drop 32).drop 32 = (be 32 t.toNat ++ tail).drop 64 := by
      rw [List.drop_drop]
    rw [← hd, drop_append_of_len_eq h32t, drop_append_of_len_eq h32m]
  rw [ite_eq_left ⟨rfl, hRestLen, hDrop64⟩,
      take_append_of_len_eq h32t, bv256_roundtrip t, drop_append_of_len_eq h32t,
      take_append_of_len_eq h32m, ite_eq_left rfl, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hc]

private theorem walParseRecords_congr (walKey : List UInt8) (off : Nat) :
    ∀ (k : Nat) (d d' : Disk),
      (∀ x, off ≤ x → x < off + 34 * k → d.bytes x = d'.bytes x) →
      walParseRecords walKey off d k = walParseRecords walKey off d' k
  | 0, _, _, _ => rfl
  | k + 1, d, d', hEq => by
    unfold walParseRecords
    rw [walParseRecords_congr walKey off k d d' (fun x hx1 hx2 => hEq x hx1 (by omega))]
    cases walParseRecords walKey off d' k with
    | none => rfl
    | some h =>
      dsimp only
      have hRead : readAt d.bytes (off + 34 * k) 34 = readAt d'.bytes (off + 34 * k) 34 :=
        readAt_congr 34 (off + 34 * k) (fun x hx1 hx2 => hEq x (by omega) (by omega))
      rw [hRead]

private theorem walParseRecords_len (walKey : List UInt8) (off : Nat) (d : Disk) :
    ∀ (k : Nat) {h : Head (BitVec 256)}, walParseRecords walKey off d k = some h → h.len = k
  | 0, _, hEq => by injection hEq with h'; rw [← h']
  | k + 1, _, hEq => by
    unfold walParseRecords at hEq
    cases hPrev : walParseRecords walKey off d k with
    | none => rw [hPrev] at hEq; cases hEq
    | some hp =>
      rw [hPrev] at hEq
      dsimp only at hEq
      split at hEq
      · injection hEq with h'; rw [← h']
      · cases hEq

theorem cshakeWalLawful (walKey : List UInt8) (off : Nat) : (cshakeWalCodec walKey).Lawful off where
  encSlot_length s c t := by
    show (walEncSlot walKey s c t).length = 80
    unfold walEncSlot
    simp only [List.length_cons, List.length_append, length_be, List.length_replicate]
  verify_encSlot s c t hc := walVerifySlot_enc walKey s c t hc
  parse_local d d' hBytes hLen := by
    show walParse walKey off d = walParse walKey off d'
    unfold walParse
    rw [hLen]
    split
    · exact walParseRecords_congr walKey off _ d d' (fun x hx _ => hBytes x hx)
    · rfl
  parse_append d h r hp := by
    have hp' : walParse walKey off d = some h := hp
    unfold walParse at hp'
    by_cases hCond : off ≤ d.len ∧ (d.len - off) % 34 = 0
    · rw [ite_eq_left hCond] at hp'
      let k := (d.len - off) / 34
      have hkEq : h.len = k := walParseRecords_len walKey off d k hp'
      have hdLen : d.len = off + 34 * k := by
        have hDiv := Nat.div_add_mod (d.len - off) 34
        rw [hCond.2, Nat.add_zero] at hDiv
        omega
      let recBs := walEncRec walKey h.tip r
      have hRecLen : recBs.length = 34 := by
        unfold recBs walEncRec
        simp only [List.length_cons, length_be]
      let d1 := d.write (off + 34 * h.len) recBs
      show walParse walKey off d1 = some ⟨h.len + 1, walChainTag walKey h.tip r, h.tip⟩
      have hd1Len : d1.len = off + 34 * (k + 1) := by
        dsimp only [d1]
        rw [Disk.write_len, hkEq, hdLen, hRecLen]
        omega
      unfold walParse
      rw [hd1Len, Nat.add_sub_cancel_left, ite_eq_left ⟨Nat.le_add_right _ _, by omega⟩]
      have hDivK : 34 * (k + 1) / 34 = k + 1 := by omega
      rw [hDivK]
      unfold walParseRecords
      have hPre : walParseRecords walKey off d1 k = walParseRecords walKey off d k :=
        walParseRecords_congr walKey off k d1 d (fun x _ hx2 => by
          dsimp only [d1]
          rw [hkEq]
          exact Disk.write_bytes_outside d (off + 34 * k) recBs (.inl hx2))
      rw [hPre, hp']
      dsimp only
      have hRead0 := Disk.readAt_write d (off + 34 * k) recBs
      rw [hRecLen] at hRead0
      have hRead : readAt d1.bytes (off + 34 * k) 34 = recBs := by
        dsimp only [d1]
        rw [hkEq]
        exact hRead0
      rw [hRead]
      have hGet0 : recBs.getD 0 0 = r := rfl
      have hGet1 : recBs.getD 1 0 = 0x5A := rfl
      have hDrop2 : recBs.drop 2 = be 32 (walChainTag walKey h.tip r).toNat := rfl
      rw [hGet0, hGet1, hDrop2, ite_eq_left ⟨rfl, rfl⟩, hkEq]
    · rw [ite_eq_right hCond] at hp'; cases hp'

/-- Canonical 32-byte custodian WAL MAC key for concrete crash-recovery verification. -/
def testWalKey : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x57, 0x41, 0x4C, 0x30,
   0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80,
   0x91, 0xA2, 0xB3, 0xC4, 0xD5, 0xE6, 0xF7, 0x08,
   0x19, 0x2A, 0x3B, 0x4C, 0x5D, 0x6E, 0x7F, 0x81]

/-- Distinct wrong 32-byte key (single bit flipped in last byte: `0x81 → 0x80`). -/
def wrongWalKey : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x57, 0x41, 0x4C, 0x30,
   0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80,
   0x91, 0xA2, 0xB3, 0xC4, 0xD5, 0xE6, 0xF7, 0x08,
   0x19, 0x2A, 0x3B, 0x4C, 0x5D, 0x6E, 0x7F, 0x80]

abbrev keyedWalCodec : Codec (BitVec 256) UInt8 := cshakeWalCodec testWalKey

def testGenesisTip : BitVec 256 := walGenesisTip testWalKey
def testTip1 : BitVec 256 := walChainTag testWalKey testGenesisTip 0x01
def testTip2 : BitVec 256 := walChainTag testWalKey testTip1 0x02

/-- Provisioned `QSBURN05` header with both 80-byte slots MAC-authenticated at `(0, testGenesisTip)`. -/
def walProvisionedImage : Disk :=
  ((⟨fun _ => 0, (qsburn05 512).chainOff⟩ : Disk).write ((qsburn05 512).off .a)
    (keyedWalCodec.encSlot .a 0 testGenesisTip)).write ((qsburn05 512).off .b)
    (keyedWalCodec.encSlot .b 0 testGenesisTip)

theorem cshakeWal_provisioned : Init keyedWalCodec (qsburn05 512) ⟨walProvisionedImage, 0, none⟩ := by
  have hSep : (qsburn05 512).Separated keyedWalCodec.slotLen :=
    qsburn05_separated (by decide) ⟨8, by decide⟩
  have hc : (view keyedWalCodec (qsburn05 512) ⟨fun _ => 0, (qsburn05 512).chainOff⟩).chain
      = some ⟨0, testGenesisTip, 0#256⟩ := by
    show walParse testWalKey (qsburn05 512).chainOff ⟨fun _ => 0, (qsburn05 512).chainOff⟩ = _
    unfold walParse
    rw [ite_eq_left ⟨Nat.le_refl _, by rw [Nat.sub_self]⟩, Nat.sub_self]
    rfl
  have hS := provisioned_steady (cshakeWalLawful testWalKey _) hSep (Nat.le_refl _) (by decide) hc
  refine Init.intro rfl ?_ (Nat.le_refl 0) (by decide) hS
  exact Nat.le_trans
    (Disk.len_le_write_len ⟨fun _ => 0, (qsburn05 512).chainOff⟩ ((qsburn05 512).off .a)
      (keyedWalCodec.encSlot .a 0 testGenesisTip)) (Disk.len_le_write_len _ _ _)

/-- `qsburn05_safe` on 512-byte sectors for the keyed `cSHAKE256` MAC codec. -/
theorem cshakeWal_qsburn05_safe {s₀ s : Sys (BitVec 256)}
    (hInit : Init keyedWalCodec (qsburn05 512) s₀)
    (hReach : Reach keyedWalCodec (qsburn05 512) s₀ s) :
    (∀ h ws, recoverPlan keyedWalCodec (qsburn05 512) s.disk = some (h, ws) → s.acked ≤ h.len) ∧
    (∀ h, (view keyedWalCodec (qsburn05 512) s.disk).chain = some h →
      ∃ ws, recoverPlan keyedWalCodec (qsburn05 512) s.disk = some (h, ws)) ∧
    (∀ n t, s.live = some (n, t) → s.acked ≤ n) :=
  qsburn05_safe (by decide) ⟨8, by decide⟩ rfl (cshakeWalLawful testWalKey _) hInit hReach

/-- Provisioned keyed-MAC image, recovered, with one `reserve` acknowledged. -/
theorem cshakeWal_trace_witness : ∃ s₀ s : Sys (BitVec 256),
    Init keyedWalCodec (qsburn05 512) s₀ ∧ Reach keyedWalCodec (qsburn05 512) s₀ s := by
  have hInit := cshakeWal_provisioned
  obtain ⟨s, hReach, _⟩ := init_can_commit hInit 0x01
    (fun h hc => by
      have hc' : walParse testWalKey (qsburn05 512).chainOff walProvisionedImage = some h := hc
      unfold walParse at hc'
      have hl : walProvisionedImage.len = (qsburn05 512).chainOff := by
        show max (max (qsburn05 512).chainOff ((qsburn05 512).off .a + _))
          ((qsburn05 512).off .b + _) = (qsburn05 512).chainOff
        have hL80a : (keyedWalCodec.encSlot .a 0 testGenesisTip).length = 80 :=
          (cshakeWalLawful testWalKey 0).encSlot_length .a 0 testGenesisTip
        have hL80b : (keyedWalCodec.encSlot .b 0 testGenesisTip).length = 80 :=
          (cshakeWalLawful testWalKey 0).encSlot_length .b 0 testGenesisTip
        rw [hL80a, hL80b]
        dsimp only [Layout.off]
        have ho := qsburn05_offsets 512
        rw [ho.1, ho.2.1, ho.2.2]
        decide
      rw [hl, Nat.sub_self, ite_eq_left ⟨Nat.le_refl _, rfl⟩] at hc'
      injection hc' with hEq
      rw [← hEq]
      decide)
  exact ⟨_, s, hInit, hReach⟩

/-- Both slots in sector 0: an acknowledged commit, then one torn sector, then nothing to recover from. -/
theorem cshakeWal_qsburn04_single_tear {s : Sys (BitVec 256)} {n : Nat} {t : BitVec 256}
    (hLive : s.live = some (n, t)) (hAck : s.acked ≤ n) (hBound : n + 2 < 256) :
    ∃ s₁ s₂, Step keyedWalCodec sharedSectorLayout s s₁ ∧ s₁.acked = n + 1 ∧
      Step keyedWalCodec sharedSectorLayout s₁ s₂ ∧ s₂.acked = n + 1 ∧
      (view keyedWalCodec sharedSectorLayout s₂.disk).a = none ∧
      (view keyedWalCodec sharedSectorLayout s₂.disk).b = none ∧
      recoverPlan keyedWalCodec sharedSectorLayout s₂.disk = none :=
  qsburn04_single_tear_loses_state (C := keyedWalCodec) rfl (cshakeWalLawful testWalKey _)
    (jA := List.replicate 80 0) (jB := List.replicate 80 0) List.length_replicate
    List.length_replicate (by decide) (by decide) hLive hAck hBound 0x01 0x02

/-- 1-byte torn append in place of a 34-byte MAC-authenticated record: `recoverPlan` fails closed
    with both 80-byte MAC slots intact. -/
theorem cshakeWal_append_tear_fails_closed {s : Sys (BitVec 256)} {n : Nat} {t : BitVec 256}
    (hLive : s.live = some (n, t)) (hBound : n + 1 < 256)
    (hLen : s.disk.len = (qsburn05 512).chainOff + 34 * n) :
    ∃ s', Step keyedWalCodec (qsburn05 512) s s' ∧ s'.acked = s.acked ∧
      (view keyedWalCodec (qsburn05 512) s'.disk).a = (view keyedWalCodec (qsburn05 512) s.disk).a ∧
      (view keyedWalCodec (qsburn05 512) s'.disk).b = (view keyedWalCodec (qsburn05 512) s.disk).b ∧
      recoverPlan keyedWalCodec (qsburn05 512) s'.disk = none := by
  have hSep : (qsburn05 512).Separated keyedWalCodec.slotLen :=
    qsburn05_separated (by decide) ⟨8, by decide⟩
  have hEncLen : [0x01].length ≤ (keyedWalCodec.encRec t 0x01).length := by
    show 1 ≤ (walEncRec testWalKey t 0x01).length
    unfold walEncRec
    simp only [List.length_cons, length_be]
    decide
  refine append_tear_fails_closed (C := keyedWalCodec) hSep.below hLive hBound 0x01
    (j := [0x01]) (by decide) hEncLen ?_ ?_
  · intro x h1 h2
    have h2' : x < (qsburn05 512).chainOff + 34 * n + 1 := h2
    have h1' : (qsburn05 512).chainOff + 34 * n ≤ x := h1
    have hx : x = (qsburn05 512).chainOff + 34 * n := by omega
    rw [hx]; rfl
  · show walParse testWalKey (qsburn05 512).chainOff
      (s.disk.write ((qsburn05 512).chainOff + 34 * n) [0x01]) = none
    unfold walParse
    have hl : (s.disk.write ((qsburn05 512).chainOff + 34 * n) [0x01]).len
        = (qsburn05 512).chainOff + (34 * n + 1) := by
      rw [Disk.write_len, hLen]
      show max _ ((qsburn05 512).chainOff + 34 * n + 1) = _
      omega
    rw [hl, Nat.add_sub_cancel_left, ite_eq_right (fun hh => by have := hh.2; omega)]

end SymbolicWalProofs

set_option maxRecDepth 65536

/-- Steady image with 1-byte torn tail at `chainOff`. -/
def walTornSteady : Disk :=
  walProvisionedImage.write (qsburn05 512).chainOff [0xEE]

/-- Record `0` (`walEncRec testWalKey testGenesisTip 0x01`, 34B) reached disk before HWM updated,
    followed by a 1-byte torn tail of record `1` at `chainOff + 34`. -/
def walTornCommittedPlusOne : Disk :=
  (walProvisionedImage.write (qsburn05 512).chainOff
    (walEncRec testWalKey testGenesisTip 0x01)).write ((qsburn05 512).chainOff + 34) [0xEE]

/-- Staggered HWM slots (`Slot A = (1, testTip1)`, `Slot B = (0, testGenesisTip)`), committed record `0`,
    plus 1-byte torn tail of record `1`. -/
def walTornStaggeredSlots : Disk :=
  (((walProvisionedImage.write (qsburn05 512).chainOff
      (walEncRec testWalKey testGenesisTip 0x01)).write ((qsburn05 512).off .a)
      (keyedWalCodec.encSlot .a 1 testTip1)).write ((qsburn05 512).chainOff + 34) [0xEE])

/-- Gap-2 violation (`Slot A = 0, Slot B = 0`, two MAC-valid records `0` and `1` + 1-byte torn tail
    so `committed = 2 > 0 + 1`): `recoverTruncatedAppendPlan` fails closed. -/
def walTornGapTwo : Disk :=
  (((walProvisionedImage.write (qsburn05 512).chainOff
      (walEncRec testWalKey testGenesisTip 0x01)).write ((qsburn05 512).chainOff + 34)
      (walEncRec testWalKey testTip1 0x02)).write ((qsburn05 512).chainOff + 68) [0xEE])

/-- Forged record written under `wrongWalKey` (single bit flipped in key) + 1-byte torn tail. -/
def walForgedWrongKeyRecord : Disk :=
  walProvisionedImage.write (qsburn05 512).chainOff
    (walEncRec wrongWalKey (walGenesisTip wrongWalKey) 0x01)

theorem cshakeWal_append_tear_truncate_recovers_all_modes :
    recoverPlan keyedWalCodec (qsburn05 512) walTornSteady = none ∧
    (recoverTruncatedAppendPlan keyedWalCodec (qsburn05 512) walTornSteady).map
      (fun r => (r.1.len, r.2.1.len)) = some ((qsburn05 512).chainOff, 0) ∧
    (recoverTruncatedAppendPlan keyedWalCodec (qsburn05 512) walTornCommittedPlusOne).map
      (fun r => (r.1.len, r.2.1.len)) = some ((qsburn05 512).chainOff + 34, 1) ∧
    (recoverTruncatedAppendPlan keyedWalCodec (qsburn05 512) walTornStaggeredSlots).map
      (fun r => (r.1.len, r.2.1.len)) = some ((qsburn05 512).chainOff + 34, 1) := by
  decide +kernel

theorem tooth_cshakeWal_slot_gap_two_rejected :
    ¬ ∃ r, recoverTruncatedAppendPlan keyedWalCodec (qsburn05 512) walTornGapTwo = some r := by
  have h : recoverTruncatedAppendPlan keyedWalCodec (qsburn05 512) walTornGapTwo = none := by
    decide +kernel
  rw [h]
  simp

private theorem wrongKey_slot_and_record_rejected :
    keyedWalCodec.verify .a ((cshakeWalCodec wrongWalKey).encSlot .a 0 (walGenesisTip wrongWalKey)) = none ∧
    recoverPlan keyedWalCodec (qsburn05 512) walForgedWrongKeyRecord = none := by
  decide +kernel

/-- `#tooth`: Single-bit key mismatch (`wrongWalKey ≠ testWalKey`) is rejected on both 80-byte slots
    and 34-byte journal records! -/
theorem tooth_cshakeWal_wrong_key_rejected :
    ¬ ∃ out,
      keyedWalCodec.verify .a ((cshakeWalCodec wrongWalKey).encSlot .a 0 (walGenesisTip wrongWalKey)) = some out ∨
      ∃ plan, recoverPlan keyedWalCodec (qsburn05 512) walForgedWrongKeyRecord = some plan := by
  rintro ⟨out, hSlot | ⟨plan, hPlan⟩⟩
  · rw [wrongKey_slot_and_record_rejected.1] at hSlot; cases hSlot
  · rw [wrongKey_slot_and_record_rejected.2] at hPlan; cases hPlan

private def walTruncPrefix : Disk :=
  walTornCommittedPlusOne.truncate ((qsburn05 512).chainOff + keyedWalCodec.recLen * 1)

private theorem walTruncPrefix_viewA :
    (view keyedWalCodec (qsburn05 512) walTruncPrefix).a = some (0, testGenesisTip) := by
  decide +kernel

private theorem walTruncPrefix_viewB :
    (view keyedWalCodec (qsburn05 512) walTruncPrefix).b = some (0, testGenesisTip) := by
  decide +kernel

private theorem walTruncPrefix_chainMap :
    ((view keyedWalCodec (qsburn05 512) walTruncPrefix).chain.map
      fun h => (h.len, h.tip, h.prev)) = some (1, testTip1, testGenesisTip) := by
  decide +kernel

private theorem walTornCommittedPlusOne_chainNone :
    (view keyedWalCodec (qsburn05 512) walTornCommittedPlusOne).chain.isSome = false := by
  decide +kernel

private theorem walTornCommittedPlusOne_tailBounds :
    (qsburn05 512).chainOff + keyedWalCodec.recLen * 1 < walTornCommittedPlusOne.len ∧
      walTornCommittedPlusOne.len - ((qsburn05 512).chainOff + keyedWalCodec.recLen * 1) ≤
        keyedWalCodec.recLen := by
  decide +kernel

private theorem walTornCommittedPlusOne_slotsPermit :
    slotsPermitTailTruncation keyedWalCodec (qsburn05 512) walTornCommittedPlusOne 1 = true := by
  decide +kernel

section SymbolicWalWitnessAndAudit
attribute [local irreducible] cshakeWalMac256

private theorem walTornCommittedPlusOne_recoverNone :
    recoverPlan keyedWalCodec (qsburn05 512) walTornCommittedPlusOne = none := by
  have hcNone := walTornCommittedPlusOne_chainNone
  unfold recoverPlan
  cases hc : (view keyedWalCodec (qsburn05 512) walTornCommittedPlusOne).chain with
  | none => rfl
  | some _ => rw [hc] at hcNone; cases hcNone

private theorem walTruncPrefix_recoverPlan :
    recoverPlan keyedWalCodec (qsburn05 512) walTruncPrefix =
      some (⟨1, testTip1, testGenesisTip⟩, commitWrites 1 testTip1) := by
  have hcMap := walTruncPrefix_chainMap
  have hc : (view keyedWalCodec (qsburn05 512) walTruncPrefix).chain =
      some ⟨1, testTip1, testGenesisTip⟩ := by
    cases hCh : (view keyedWalCodec (qsburn05 512) walTruncPrefix).chain with
    | none => rw [hCh] at hcMap; cases hcMap
    | some hd =>
      rw [hCh] at hcMap
      cases hd with
      | mk l tp pv =>
        injection hcMap with hTuple
        have h1 : l = 1 := (Prod.mk.inj hTuple).1
        have h23 := (Prod.mk.inj hTuple).2
        have h2 : tp = testTip1 := (Prod.mk.inj h23).1
        have h3 : pv = testGenesisTip := (Prod.mk.inj h23).2
        rw [h1, h2, h3]
  apply recoverPlan_of hc
  rw [walTruncPrefix_viewA, walTruncPrefix_viewB]
  unfold recoverWrites
  dsimp only
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl,
      ite_eq_left ⟨rfl, rfl, rfl⟩]

theorem witness_append_tear_truncate_recovers :
    ∃ (Tip Rec : Type) (_ : DecidableEq Tip) (C : Codec Tip Rec) (L : Layout) (d : Disk)
      (committed : Nat) (h : Head Tip) (ws : List (SlotWrite Tip)),
      0 < C.recLen ∧
      recoverPlan C L d = none ∧
      (L.chainOff + C.recLen * committed < d.len ∧
        d.len - (L.chainOff + C.recLen * committed) ≤ C.recLen) ∧
      slotsPermitTailTruncation C L d committed = true ∧
      recoverPlan C L (d.truncate (L.chainOff + C.recLen * committed)) = some (h, ws) :=
  ⟨BitVec 256, UInt8, inferInstance, keyedWalCodec, qsburn05 512, walTornCommittedPlusOne,
    1, ⟨1, testTip1, testGenesisTip⟩, commitWrites 1 testTip1,
    by decide, walTornCommittedPlusOne_recoverNone, walTornCommittedPlusOne_tailBounds,
    walTornCommittedPlusOne_slotsPermit, walTruncPrefix_recoverPlan⟩

#verify_constructive cshakeWalLawful cshakeWal_provisioned cshakeWal_qsburn05_safe cshakeWal_trace_witness
#verify_constructive cshakeWal_qsburn04_single_tear cshakeWal_append_tear_fails_closed
#verify_inhabited cshakeWal_qsburn05_safe cshakeWal_trace_witness
#tooth_pair cshakeWal_qsburn05_safe vs cshakeWal_qsburn04_single_tear
#tooth_pair cshakeWal_qsburn05_safe vs cshakeWal_append_tear_fails_closed
#tooth_pair cshakeWal_qsburn05_safe vs tooth_cshakeWal_wrong_key_rejected
#verify_constructive cshakeWal_append_tear_truncate_recovers_all_modes tooth_cshakeWal_slot_gap_two_rejected
  tooth_cshakeWal_wrong_key_rejected witness_append_tear_truncate_recovers
#tooth_pair cshakeWal_append_tear_truncate_recovers_all_modes vs tooth_cshakeWal_slot_gap_two_rejected

end SymbolicWalWitnessAndAudit

end Qsag.Tests.TwoSlotHwmTeeth
end
