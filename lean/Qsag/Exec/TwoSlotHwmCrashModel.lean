module

public import Qsag.Exec.TwoSlotHwmBase
import Qsag.Tactic.AssuranceKit

public section

namespace Qsag.Exec.TwoSlotHwmCrashModel

set_option autoImplicit false

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

@[expose] def readSlot (C : Codec Tip Rec) (L : Layout) (d : Disk) (s : Slot) : List UInt8 :=
  readAt d.bytes (L.off s) C.slotLen

@[expose] def view (C : Codec Tip Rec) (L : Layout) (d : Disk) : View Tip :=
  ⟨C.verify .a (readSlot C L d .a), C.verify .b (readSlot C L d .b), C.parse L.chainOff d⟩

theorem view_get (C : Codec Tip Rec) (L : Layout) (d : Disk) (s : Slot) :
    (view C L d).get s = C.verify s (readSlot C L d s) := by
  cases s <;> rfl

/-- Unforgeability on the medium: after a crash each slot and the chain either fail to
    authenticate or decode as before or as after the unsynced writes. -/
def NoForge (C : Codec Tip Rec) (L : Layout) (v : Dev) (d' : Disk) : Prop :=
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
@[expose] def recoverPlan [DecidableEq Tip] (C : Codec Tip Rec) (L : Layout) (d : Disk) :
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
theorem recover_view {v : View Tip} {G : Nat} {h : Head Tip} (hFam : Fam v G)
    (hc : v.chain = some h) :
    ∃ ws, recoverWrites v.a v.b h = some ws ∧ G ≤ h.len ∧ (∀ w ∈ ws, w.ctr = h.len) ∧
      ∀ (fin : Bool) (v' : View Tip), ViewExec v ws fin v' →
        Fam v' G ∧ (fin = true → Steady v' h.len h.tip) := by
  obtain ⟨a, b, c⟩ := v
  obtain ⟨n, t, hG, hCase⟩ := hFam
  have hc : c = some h := hc
  rcases hCase with ⟨ha, hb, hch⟩ | ⟨t', hch, hCase⟩
  · have ha : a = some (n, t) := ha
    have hb : b = some (n, t) := hb
    rcases hch with hch | ⟨p, hch⟩
    · have hch : c = none := hch
      rw [hch] at hc; cases hc
    · have hch : c = some ⟨n, t, p⟩ := hch
      subst ha hb hch
      cases hc
      refine ⟨[], rw_steady n t p, hG, fun w hw => absurd hw List.not_mem_nil, ?_⟩
      intro fin v' hE
      have hS := steady_mk n t p
      cases hE with
      | done _ => exact ⟨fam_of_steady hS hG, fun _ => hS⟩
      | stay => exact ⟨fam_of_steady hS hG, false_ne_true_imp⟩
  · have hch : c = some ⟨n + 1, t', t⟩ := hch
    rw [hch] at hc; cases hc
    subst hch
    rcases hCase with ⟨hb, ha⟩ | ⟨ha, hb⟩
    · have hb : b = some (n, t) := hb
      subst hb
      rcases ha with ha | ha | ha
      · have ha : a = none := ha
        subst ha
        exact ⟨_, rw_adv_lone n t t', by show G ≤ n + 1; omega, ctr_commit,
          fun fin v' hE => commit_view hG (Or.inl rfl) hE⟩
      · have ha : a = some (n, t) := ha
        subst ha
        exact ⟨_, rw_adv_both n t t', by show G ≤ n + 1; omega, ctr_commit,
          fun fin v' hE => commit_view hG (Or.inr (Or.inl rfl)) hE⟩
      · have ha : a = some (n + 1, t') := ha
        subst ha
        exact ⟨_, rw_repair n t t', by show G ≤ n + 1; omega, ctr_single,
          fun fin v' hE => repairB_view hG (Or.inr rfl) hE⟩
    · have ha : a = some (n + 1, t') := ha
      have hb : b = none := hb
      subst ha hb
      exact ⟨_, rw_lone_b n t t', by show G ≤ n + 1; omega, ctr_single,
        fun fin v' hE => repairB_view hG (Or.inl rfl) hE⟩

end Decide

/-! ## 5. The system: reserve, recover, shutdown, crash -/

/-- The journal file, the highest counter ever reported to the caller (a completed `reserve`
    or a returned recovery), and the open handle `(records, tip)` if a process holds one. -/
structure Sys (Tip : Type) where
  disk : Disk
  acked : Nat
  live : Option (Nat × Tip)

inductive Step [DecidableEq Tip] (C : Codec Tip Rec) (L : Layout) : Sys Tip → Sys Tip → Prop where
  | reserveAck {s : Sys Tip} {n : Nat} {t : Tip} {r : Rec} {d' : Disk} :
      s.live = some (n, t) → n + 1 < C.bound →
      Exec C L ⟨s.disk, []⟩ (reserveOps C L n t r) true d' →
      Step C L s ⟨d', max s.acked (n + 1), some (n + 1, C.tag t r)⟩
  | reserveCrash {s : Sys Tip} {n : Nat} {t : Tip} {r : Rec} {d' : Disk} :
      s.live = some (n, t) → n + 1 < C.bound →
      Exec C L ⟨s.disk, []⟩ (reserveOps C L n t r) false d' →
      Step C L s ⟨d', s.acked, none⟩
  | recoverOk {s : Sys Tip} {h : Head Tip} {ws : List (SlotWrite Tip)} {d' : Disk} :
      s.live = none → recoverPlan C L s.disk = some (h, ws) →
      Exec C L ⟨s.disk, []⟩ (slotOps C L ws) true d' →
      Step C L s ⟨d', max s.acked h.len, some (h.len, h.tip)⟩
  | recoverCrash {s : Sys Tip} {h : Head Tip} {ws : List (SlotWrite Tip)} {d' : Disk} :
      s.live = none → recoverPlan C L s.disk = some (h, ws) →
      Exec C L ⟨s.disk, []⟩ (slotOps C L ws) false d' →
      Step C L s ⟨d', s.acked, none⟩
  | shutdown {s : Sys Tip} : Step C L s ⟨s.disk, s.acked, none⟩

inductive Reach [DecidableEq Tip] (C : Codec Tip Rec) (L : Layout) : Sys Tip → Sys Tip → Prop where
  | refl (s : Sys Tip) : Reach C L s s
  | tail {s s' s'' : Sys Tip} : Reach C L s s' → Step C L s' s'' → Reach C L s s''

/-- A provisioned journal with no process attached. -/
def Init (C : Codec Tip Rec) (L : Layout) (s : Sys Tip) : Prop :=
  s.live = none ∧ L.chainOff ≤ s.disk.len ∧
    ∃ n t, s.acked ≤ n ∧ n < C.bound ∧ Steady (view C L s.disk) n t

structure SysInv (C : Codec Tip Rec) (L : Layout) (s : Sys Tip) : Prop where
  len : L.chainOff ≤ s.disk.len
  fam : Fam (view C L s.disk) s.acked
  bound : ∀ h, (view C L s.disk).chain = some h → h.len < C.bound
  live : ∀ n t, s.live = some (n, t) → Steady (view C L s.disk) n t ∧ s.acked ≤ n

theorem SysInv.of_init {C : Codec Tip Rec} {L : Layout} {s : Sys Tip} (h : Init C L s) :
    SysInv C L s := by
  obtain ⟨hLive, hLen, n, t, hG, hB, hS⟩ := h
  refine ⟨hLen, fam_of_steady hS hG, ?_, ?_⟩
  · intro h hc
    obtain ⟨p, hp⟩ := hS.2.2
    rw [hp] at hc; cases hc
    exact hB
  · intro n' t' hl
    rw [hLive] at hl; cases hl

/-- `reserve`, cut anywhere or run to the end. -/
theorem reserve_exec {C : Codec Tip Rec} {L : Layout} (hLaw : C.Lawful L.chainOff)
    (hSep : L.Separated C.slotLen) {d d' : Disk} {G n : Nat} {t : Tip} {r : Rec} {fin : Bool}
    (hLen : L.chainOff ≤ d.len) (hS : Steady (view C L d) n t) (hG : G ≤ n)
    (hB : n + 1 < C.bound) (hE : Exec C L ⟨d, []⟩ (reserveOps C L n t r) fin d') :
    L.chainOff ≤ d'.len ∧ Fam (view C L d') G ∧
      (∀ h, (view C L d').chain = some h → h.len < C.bound) ∧
      (fin = true → Steady (view C L d') (n + 1) (C.tag t r)) := by
  obtain ⟨va, vb, p, vc⟩ := hS
  have hS : Steady (view C L d) n t := ⟨va, vb, p, vc⟩
  have hOldB : ∀ h, (view C L d).chain = some h → h.len < C.bound := by
    intro h hc; rw [vc] at hc; cases hc; show n < C.bound; omega
  have hApp : (view C L (d.write (L.chainOff + C.recLen * n) (C.encRec t r))).chain
      = some ⟨n + 1, C.tag t r, t⟩ := hLaw.parse_append d ⟨n, t, p⟩ r vc
  have hE : Exec C L ⟨d, []⟩ (.pwrite ⟨L.chainOff + C.recLen * n, C.encRec t r⟩ :: .fsync ::
      slotOps C L (commitWrites (n + 1) (C.tag t r))) fin d' := hE
  cases hE with
  | crash hC _ =>
    rw [crashImage_nil hC]
    exact ⟨hLen, fam_of_steady hS hG, hOldB, false_ne_true_imp⟩
  | op hE1 =>
    cases hE1 with
    | crash hC hN =>
      obtain ⟨x₀, h1, h2, hT, hl1, _⟩ := crashImage_single hC
      have hSlots := view_slots_congr C L (d := d) (d' := d')
        (fun s x hx1 hx2 => torn_frame hT h1 h2
          (fun y hy1 _ => hSep.chain s x y hx1 hx2 (by
            have hy1 : L.chainOff + C.recLen * n ≤ y := hy1
            omega)))
      have ha : (view C L d').a = some (n, t) := hSlots.1.trans va
      have hb : (view C L d').b = some (n, t) := hSlots.2.trans vb
      refine ⟨Nat.le_trans hLen hl1, ?_, ?_, false_ne_true_imp⟩
      · rcases hN.2 with h | h | h
        · exact ⟨n, t, hG, Or.inl ⟨ha, hb, Or.inl h⟩⟩
        · exact ⟨n, t, hG, Or.inl ⟨ha, hb, Or.inr ⟨p, h.trans vc⟩⟩⟩
        · exact ⟨n, t, hG, Or.inr ⟨C.tag t r, h.trans hApp, Or.inl ⟨hb, Or.inr (Or.inl ha)⟩⟩⟩
      · intro h hc
        rcases hN.2 with e | e | e
        · rw [e] at hc; cases hc
        · exact hOldB h (e.symm.trans hc)
        · have e' := (e.trans hApp).symm.trans hc
          cases e'
          exact hB
    | op hE2 =>
      have hLen1 : L.chainOff ≤ (d.write (L.chainOff + C.recLen * n) (C.encRec t r)).len :=
        Nat.le_trans hLen (Disk.len_le_write_len _ _ _)
      have hSlots := view_slots_congr C L (d := d)
        (d' := d.write (L.chainOff + C.recLen * n) (C.encRec t r))
        (fun s x _ hx2 => Disk.write_bytes_outside d _ _ (Or.inl (by
          have := hSep.below s
          omega)))
      have hView : view C L (d.write (L.chainOff + C.recLen * n) (C.encRec t r))
          = ⟨some (n, t), some (n, t), some ⟨n + 1, C.tag t r, t⟩⟩ :=
        View.ext' (hSlots.1.trans va) (hSlots.2.trans vb) hApp
      have hE2 : Exec C L ⟨d.write (L.chainOff + C.recLen * n) (C.encRec t r), []⟩
          (slotOps C L (commitWrites (n + 1) (C.tag t r))) fin d' := hE2
      obtain ⟨hV, hl⟩ := exec_slotOps hLaw hSep _ _ fin d' hLen1
        (fun w hw => by
          have hw : w ∈ [(⟨.a, n + 1, C.tag t r⟩ : SlotWrite Tip), ⟨.b, n + 1, C.tag t r⟩] := hw
          rcases List.mem_cons.mp hw with rfl | hw
          · exact hB
          · rcases List.mem_cons.mp hw with rfl | hw
            · exact hB
            · exact absurd hw List.not_mem_nil) hE2
      rw [hView] at hV
      obtain ⟨hF, hSt⟩ := commit_view hG (Or.inr (Or.inl rfl)) hV
      refine ⟨hl, hF, ?_, hSt⟩
      intro h hc
      have e := hV.chain_eq.symm.trans hc
      cases e
      exact hB

theorem SysInv.step [DecidableEq Tip] {C : Codec Tip Rec} {L : Layout}
    (hLaw : C.Lawful L.chainOff) (hSep : L.Separated C.slotLen) {s s' : Sys Tip}
    (hInv : SysInv C L s) (hStep : Step C L s s') : SysInv C L s' := by
  cases hStep with
  | shutdown => exact ⟨hInv.len, hInv.fam, hInv.bound, fun n t h => by cases h⟩
  | @reserveAck n t r d' hLive hB hE =>
    obtain ⟨hS, hG⟩ := hInv.live n t hLive
    obtain ⟨hl, _, hb, hSt⟩ := reserve_exec hLaw hSep hInv.len hS hG hB hE
    have hSt := hSt rfl
    have hMax : max s.acked (n + 1) ≤ n + 1 := by omega
    refine ⟨hl, fam_of_steady hSt hMax, hb, ?_⟩
    intro n' t' hl'
    cases hl'
    exact ⟨hSt, hMax⟩
  | @reserveCrash n t r d' hLive hB hE =>
    obtain ⟨hS, hG⟩ := hInv.live n t hLive
    obtain ⟨hl, hF, hb, _⟩ := reserve_exec hLaw hSep hInv.len hS hG hB hE
    exact ⟨hl, hF, hb, fun n t h => by cases h⟩
  | @recoverOk h ws d' hLive hPlan hE =>
    obtain ⟨hc, hw⟩ := recoverPlan_eq_some hPlan
    obtain ⟨ws', hw', hG, hctr, hpost⟩ := recover_view hInv.fam hc
    have hEq : ws' = ws := Option.some.inj (hw'.symm.trans hw)
    subst hEq
    have hbound := hInv.bound h hc
    obtain ⟨hV, hl⟩ := exec_slotOps hLaw hSep ws' s.disk true d' hInv.len
      (fun w hw => by rw [hctr w hw]; exact hbound) hE
    obtain ⟨_, hSt⟩ := hpost _ _ hV
    have hSt := hSt rfl
    have hMax : max s.acked h.len ≤ h.len := by omega
    refine ⟨hl, fam_of_steady hSt hMax, ?_, ?_⟩
    · intro h' hc'
      obtain ⟨p, hp⟩ := hSt.2.2
      rw [hp] at hc'; cases hc'
      exact hbound
    · intro n' t' hl'
      cases hl'
      exact ⟨hSt, hMax⟩
  | @recoverCrash h ws d' hLive hPlan hE =>
    obtain ⟨hc, hw⟩ := recoverPlan_eq_some hPlan
    obtain ⟨ws', hw', hG, hctr, hpost⟩ := recover_view hInv.fam hc
    have hEq : ws' = ws := Option.some.inj (hw'.symm.trans hw)
    subst hEq
    have hbound := hInv.bound h hc
    obtain ⟨hV, hl⟩ := exec_slotOps hLaw hSep ws' s.disk false d' hInv.len
      (fun w hw => by rw [hctr w hw]; exact hbound) hE
    obtain ⟨hF, _⟩ := hpost _ _ hV
    refine ⟨hl, hF, ?_, fun n t h => by cases h⟩
    intro h' hc'
    exact hInv.bound h' (hV.chain_eq.symm.trans hc')

theorem SysInv.reach [DecidableEq Tip] {C : Codec Tip Rec} {L : Layout}
    (hLaw : C.Lawful L.chainOff) (hSep : L.Separated C.slotLen) {s₀ s : Sys Tip}
    (hInv : SysInv C L s₀) (hReach : Reach C L s₀ s) : SysInv C L s := by
  induction hReach with
  | refl => exact hInv
  | tail _ hStep ih => exact ih.step hLaw hSep hStep

/-- **Crash safety with sector-disjoint slots (`distinct_pages_safe`).**
    From a provisioned journal, after any sequence of reserves, recoveries, shutdowns and
    crashes (each crash tearing any one sector under an unsynced write):
    1. a recovery that decides to proceed returns a counter at or above every acknowledged one;
    2. recovery decides to proceed whenever the record chain parses;
    3. an open handle is at or above every acknowledged counter. -/
theorem distinct_pages_safe [DecidableEq Tip] {C : Codec Tip Rec} {L : Layout}
    (hLaw : C.Lawful L.chainOff) (hSep : L.Separated C.slotLen) {s₀ s : Sys Tip}
    (hInit : Init C L s₀) (hReach : Reach C L s₀ s) :
    (∀ h ws, recoverPlan C L s.disk = some (h, ws) → s.acked ≤ h.len) ∧
    (∀ h, (view C L s.disk).chain = some h → ∃ ws, recoverPlan C L s.disk = some (h, ws)) ∧
    (∀ n t, s.live = some (n, t) → s.acked ≤ n) := by
  have hInv := (SysInv.of_init hInit).reach hLaw hSep hReach
  refine ⟨?_, ?_, fun n t hl => (hInv.live n t hl).2⟩
  · intro h ws hPlan
    obtain ⟨hc, _⟩ := recoverPlan_eq_some hPlan
    obtain ⟨_, _, hG, _⟩ := recover_view hInv.fam hc
    exact hG
  · intro h hc
    obtain ⟨ws, hw, _⟩ := recover_view hInv.fam hc
    exact ⟨ws, recoverPlan_of hc hw⟩

/-- `distinct_pages_safe` for `TwoSlotHwm::paged` on any sector size dividing the page size. -/
theorem paged_layout_safe [DecidableEq Tip] {C : Codec Tip Rec} {sector page first : Nat}
    (hS : 0 < sector) (hDiv : sector ∣ page) (hFit : C.slotLen ≤ page)
    (hLaw : C.Lawful (Layout.paged sector page first).chainOff) {s₀ s : Sys Tip}
    (hInit : Init C (Layout.paged sector page first) s₀)
    (hReach : Reach C (Layout.paged sector page first) s₀ s) :
    (∀ h ws, recoverPlan C (Layout.paged sector page first) s.disk = some (h, ws) →
      s.acked ≤ h.len) ∧
    (∀ h, (view C (Layout.paged sector page first) s.disk).chain = some h →
      ∃ ws, recoverPlan C (Layout.paged sector page first) s.disk = some (h, ws)) ∧
    (∀ n t, s.live = some (n, t) → s.acked ≤ n) :=
  distinct_pages_safe hLaw (Layout.paged_separated hS hDiv hFit) hInit hReach

/-! ## 6. Progress: operations can complete -/

theorem slotOps_completes (C : Codec Tip Rec) (L : Layout) :
    ∀ (ws : List (SlotWrite Tip)) (d : Disk), ∃ d', Exec C L ⟨d, []⟩ (slotOps C L ws) true d' := by
  intro ws
  induction ws with
  | nil => intro d; exact ⟨d, Exec.done ⟨d, []⟩ rfl⟩
  | cons w rest ih =>
    intro d
    obtain ⟨d', h⟩ := ih (d.write (L.off w.slot) (C.encSlot w.slot w.ctr w.tip))
    exact ⟨d', Exec.op (Exec.op h)⟩

theorem reserveOps_completes (C : Codec Tip Rec) (L : Layout) (d : Disk) (n : Nat) (t : Tip)
    (r : Rec) : ∃ d', Exec C L ⟨d, []⟩ (reserveOps C L n t r) true d' ∧ d.len ≤ d'.len := by
  refine ⟨_, Exec.op (Exec.op (Exec.op (Exec.op (Exec.op (Exec.op (Exec.done _ rfl)))))), ?_⟩
  exact Nat.le_trans (Disk.len_le_write_len _ _ _)
    (Nat.le_trans (Disk.len_le_write_len _ _ _) (Disk.len_le_write_len _ _ _))

theorem Init.intro {C : Codec Tip Rec} {L : Layout} {s : Sys Tip} {n : Nat} {t : Tip}
    (hLive : s.live = none) (hLen : L.chainOff ≤ s.disk.len) (hG : s.acked ≤ n)
    (hB : n < C.bound) (hS : Steady (view C L s.disk) n t) : Init C L s :=
  ⟨hLive, hLen, n, t, hG, hB, hS⟩

/-- Writing both slots for the record the chain already ends at gives a steady image. -/
theorem provisioned_steady {C : Codec Tip Rec} {L : Layout} (hLaw : C.Lawful L.chainOff)
    (hSep : L.Separated C.slotLen) {d : Disk} {n : Nat} {t p : Tip} (hLen : L.chainOff ≤ d.len)
    (hB : n < C.bound) (hc : (view C L d).chain = some ⟨n, t, p⟩) :
    Steady (view C L ((d.write (L.off .a) (C.encSlot .a n t)).write (L.off .b)
      (C.encSlot .b n t))) n t := by
  have h1 : view C L (d.write (L.off .a) (C.encSlot .a n t))
      = (view C L d).set .a (some (n, t)) := view_write_slot hLaw hSep ⟨.a, n, t⟩ hLen hB
  have h2 : view C L ((d.write (L.off .a) (C.encSlot .a n t)).write (L.off .b)
      (C.encSlot .b n t)) = (view C L (d.write (L.off .a) (C.encSlot .a n t))).set .b
        (some (n, t)) :=
    view_write_slot hLaw hSep ⟨.b, n, t⟩ (Nat.le_trans hLen (Disk.len_le_write_len _ _ _)) hB
  rw [h2, h1]
  exact ⟨rfl, rfl, p, hc⟩

/-- From a provisioned journal with room for one more record, a recovery followed by a
    `reserve` can run to completion and be acknowledged. -/
theorem init_can_commit [DecidableEq Tip] {C : Codec Tip Rec} {L : Layout} {s₀ : Sys Tip}
    (hInit : Init C L s₀) (r : Rec)
    (hRoom : ∀ h, (view C L s₀.disk).chain = some h → h.len + 1 < C.bound) :
    ∃ s, Reach C L s₀ s ∧ ∃ n t, s.live = some (n + 1, t) ∧ s.acked = n + 1 := by
  obtain ⟨hLive, _, n, t, hG, _, hS⟩ := hInit
  obtain ⟨p, hc⟩ := hS.2.2
  obtain ⟨ws, hw, _⟩ := recover_view (fam_of_steady hS hG) hc
  obtain ⟨d₁, hE₁⟩ := slotOps_completes C L ws s₀.disk
  obtain ⟨d₂, hE₂, _⟩ := reserveOps_completes C L d₁ n t r
  have hB : n + 1 < C.bound := hRoom _ hc
  have st₁ : Step C L s₀ ⟨d₁, max s₀.acked n, some (n, t)⟩ :=
    Step.recoverOk (h := ⟨n, t, p⟩) hLive (recoverPlan_of hc hw) hE₁
  have st₂ : Step C L ⟨d₁, max s₀.acked n, some (n, t)⟩
      ⟨d₂, max (max s₀.acked n) (n + 1), some (n + 1, C.tag t r)⟩ :=
    Step.reserveAck (s := ⟨d₁, max s₀.acked n, some (n, t)⟩) rfl hB hE₂
  refine ⟨_, Reach.tail (Reach.tail (Reach.refl _) st₁) st₂, n, C.tag t r, rfl, ?_⟩
  show max (max s₀.acked n) (n + 1) = n + 1
  omega

/-! ## 7. Shared sector: one tear takes both slots -/

/-- **One sector holding both slots (`shared_sector_single_tear_loses_state`).**
    Slot A, slot B and nothing else of theirs lie in one sector (`hShared`). From an open handle,
    one `reserve` completes and is acknowledged at `n + 1`; the next `reserve` crashes while
    writing slot A, tearing that single sector. The crash satisfies `CrashImage` and `NoForge`
    exactly as in `distinct_pages_safe`. Afterwards neither slot authenticates and recovery
    refuses, with the acknowledged counter still `n + 1`.
    `jA`, `jB` are any slot-sized byte strings that do not authenticate. -/
theorem shared_sector_single_tear_loses_state [DecidableEq Tip] {C : Codec Tip Rec} {L : Layout}
    (hLaw : C.Lawful L.chainOff)
    (hShared : ∀ x, L.offA ≤ x → x < L.offB + C.slotLen → x / L.sector = L.offA / L.sector)
    (hAB : L.offA + C.slotLen ≤ L.offB) (hBC : L.offB + C.slotLen ≤ L.chainOff)
    (hPos : 0 < C.slotLen)
    {jA jB : List UInt8} (hjA : jA.length = C.slotLen) (hjB : jB.length = C.slotLen)
    (hvA : C.verify .a jA = none) (hvB : C.verify .b jB = none)
    {s : Sys Tip} {n : Nat} {t : Tip} (hLive : s.live = some (n, t)) (hAck : s.acked ≤ n)
    (hBound : n + 2 < C.bound) (r₁ r₂ : Rec) :
    ∃ s₁ s₂, Step C L s s₁ ∧ s₁.acked = n + 1 ∧ Step C L s₁ s₂ ∧ s₂.acked = n + 1 ∧
      (view C L s₂.disk).a = none ∧ (view C L s₂.disk).b = none ∧
      recoverPlan C L s₂.disk = none := by
  obtain ⟨d₁, hE₁, _⟩ := reserveOps_completes C L s.disk n t r₁
  have hAcked : max s.acked (n + 1) = n + 1 := by omega
  -- the second reserve: record appended and synced, slot A write torn
  let dR := d₁.write (L.chainOff + C.recLen * (n + 1)) (C.encRec (C.tag t r₁) r₂)
  let d₂ : Disk := ⟨overlay jB L.offB (overlay jA L.offA dR.bytes), dR.len⟩
  have hOut : ∀ x, (x < L.offA ∨ L.offB + C.slotLen ≤ x) → d₂.bytes x = dR.bytes x := by
    intro x hx
    show overlay jB L.offB (overlay jA L.offA dR.bytes) x = dR.bytes x
    rw [overlay_outside jB _ x L.offB (by rw [hjB]; omega),
      overlay_outside jA _ x L.offA (by rw [hjA]; omega)]
  have hA : (view C L d₂).a = none := by
    show C.verify .a (readAt (overlay jB L.offB (overlay jA L.offA dR.bytes)) L.offA C.slotLen)
      = none
    have e : readAt (overlay jB L.offB (overlay jA L.offA dR.bytes)) L.offA C.slotLen
        = readAt (overlay jA L.offA dR.bytes) L.offA C.slotLen :=
      readAt_congr _ _ (fun x _ hx2 => overlay_outside jB _ x L.offB (Or.inl (by omega)))
    rw [e, ← hjA, readAt_overlay]
    exact hvA
  have hB : (view C L d₂).b = none := by
    show C.verify .b (readAt (overlay jB L.offB (overlay jA L.offA dR.bytes)) L.offB C.slotLen)
      = none
    rw [← hjB, readAt_overlay]
    exact hvB
  have hChain : (view C L d₂).chain = (view C L dR).chain :=
    hLaw.parse_local d₂ dR (fun x hx => hOut x (Or.inr (by omega))) rfl
  have hCrash : CrashImage L.sector
      ⟨dR, [slotPWrite C L ⟨.a, n + 2, C.tag (C.tag t r₁) r₂⟩]⟩ d₂ := by
    refine Or.inr ⟨_, L.offA, List.mem_cons_self, Nat.le_refl _, ?_, ?_, Nat.le_refl _,
      Disk.len_le_write_len _ _ _⟩
    · show L.offA < L.offA + (C.encSlot .a (n + 2) (C.tag (C.tag t r₁) r₂)).length
      rw [hLaw.encSlot_length]; omega
    · intro x hx
      refine ⟨0, hOut x ?_⟩
      rcases Nat.lt_or_ge x L.offA with a | a
      · exact Or.inl a
      · rcases Nat.lt_or_ge x (L.offB + C.slotLen) with b | b
        · exact absurd (hShared x a b) hx
        · exact Or.inr b
  have hNoForge : NoForge C L ⟨dR, [slotPWrite C L ⟨.a, n + 2, C.tag (C.tag t r₁) r₂⟩]⟩ d₂ := by
    refine ⟨fun sl => Or.inl ?_, Or.inr (Or.inl hChain)⟩
    cases sl with
    | a => exact hA
    | b => exact hB
  have hE₂ : Exec C L ⟨d₁, []⟩ (reserveOps C L (n + 1) (C.tag t r₁) r₂) false d₂ :=
    Exec.op (Exec.op (Exec.op (Exec.crash hCrash hNoForge)))
  refine ⟨⟨d₁, max s.acked (n + 1), some (n + 1, C.tag t r₁)⟩, ⟨d₂, max s.acked (n + 1), none⟩,
    Step.reserveAck hLive (by omega) hE₁, hAcked, Step.reserveCrash rfl hBound hE₂, hAcked,
    hA, hB, ?_⟩
  unfold recoverPlan
  cases hc : (view C L d₂).chain with
  | none => rfl
  | some h =>
    show (match recoverWrites (view C L d₂).a (view C L d₂).b h with
      | none => none
      | some ws => some (h, ws)) = none
    rw [hA, hB]
    rfl

/-! ## 8. A torn record append fails closed -/

/-- **Legacy strict-parser counterexample (`append_tear_fails_closed`).** `reserve` crashes inside its record write;
    the junk `j` stays within one sector of the record area and the chain no longer parses
    (`hJunk`: a bad tag, or a length that is not a whole number of records). Both slots are
    intact and the acknowledged counter is unchanged, yet recovery returns no plan: the
    journal is refused until repaired by hand. This holds under `Layout.Separated` as well. -/
theorem append_tear_fails_closed [DecidableEq Tip] {C : Codec Tip Rec} {L : Layout}
    (hBelow : ∀ sl, L.off sl + C.slotLen ≤ L.chainOff)
    {s : Sys Tip} {n : Nat} {t : Tip} (hLive : s.live = some (n, t)) (hBound : n + 1 < C.bound)
    (r : Rec) {j : List UInt8} (hjPos : 0 < j.length)
    (hjLen : j.length ≤ (C.encRec t r).length)
    (hjSector : ∀ x, L.chainOff + C.recLen * n ≤ x → x < L.chainOff + C.recLen * n + j.length →
      x / L.sector = (L.chainOff + C.recLen * n) / L.sector)
    (hJunk : (view C L (s.disk.write (L.chainOff + C.recLen * n) j)).chain = none) :
    ∃ s', Step C L s s' ∧ s'.acked = s.acked ∧
      (view C L s'.disk).a = (view C L s.disk).a ∧ (view C L s'.disk).b = (view C L s.disk).b ∧
      recoverPlan C L s'.disk = none := by
  let off := L.chainOff + C.recLen * n
  let d' := s.disk.write off j
  have hSlots := view_slots_congr C L (d := s.disk) (d' := d')
    (fun sl x _ hx2 => Disk.write_bytes_outside s.disk off j (Or.inl (by
      have := hBelow sl
      show x < L.chainOff + C.recLen * n
      omega)))
  have hCrash : CrashImage L.sector ⟨s.disk, [⟨off, C.encRec t r⟩]⟩ d' := by
    refine Or.inr ⟨_, off, List.mem_cons_self, Nat.le_refl _, ?_, ?_,
      Disk.len_le_write_len _ _ _, ?_⟩
    · show off < off + (C.encRec t r).length; omega
    · intro x hx
      refine ⟨0, Disk.write_bytes_outside s.disk off j ?_⟩
      rcases Nat.lt_or_ge x off with a | a
      · exact Or.inl a
      · rcases Nat.lt_or_ge x (off + j.length) with b | b
        · exact absurd (hjSector x a b) hx
        · exact Or.inr b
    · show max s.disk.len (off + j.length) ≤ max s.disk.len (off + (C.encRec t r).length)
      omega
  have hNoForge : NoForge C L ⟨s.disk, [⟨off, C.encRec t r⟩]⟩ d' := by
    refine ⟨fun sl => Or.inr (Or.inl ?_), Or.inl hJunk⟩
    cases sl with
    | a => exact hSlots.1
    | b => exact hSlots.2
  have hE : Exec C L ⟨s.disk, []⟩ (reserveOps C L n t r) false d' :=
    Exec.op (Exec.crash hCrash hNoForge)
  refine ⟨⟨d', s.acked, none⟩, Step.reserveCrash hLive hBound hE, rfl, hSlots.1, hSlots.2, ?_⟩
  unfold recoverPlan
  show (match (view C L d').chain with
    | none => none
    | some h =>
      match recoverWrites (view C L d').a (view C L d').b h with
      | none => none
      | some ws => some (h, ws)) = none
  rw [hJunk]

end Protocol

/-! ## 9. The two layouts in the tree -/

/-- `QSBURN05` (`crates/qsag-fts/src/wal.rs`): slot A at 4096, slot B at 8192, records from 12288. -/
@[expose] def qsburn05 (sector : Nat) : Layout := Layout.paged sector 4096 1

theorem qsburn05_offsets (sector : Nat) :
    (qsburn05 sector).offA = 4096 ∧ (qsburn05 sector).offB = 8192 ∧
      (qsburn05 sector).chainOff = 12288 := by
  refine ⟨by rfl, by rfl, by rfl⟩

/-- 80-byte slots under `QSBURN05` are separated on every sector size dividing 4096. -/
theorem qsburn05_separated {sector : Nat} (hS : 0 < sector) (hDiv : sector ∣ 4096) :
    (qsburn05 sector).Separated 80 :=
  Layout.paged_separated hS hDiv (by omega)

/-- `distinct_pages_safe` for `QSBURN05` with its 80-byte slots. -/
theorem qsburn05_safe {Tip Rec : Type} [DecidableEq Tip] {C : Codec Tip Rec} {sector : Nat}
    (hS : 0 < sector) (hDiv : sector ∣ 4096) (hSlot : C.slotLen = 80)
    (hLaw : C.Lawful (qsburn05 sector).chainOff) {s₀ s : Sys Tip}
    (hInit : Init C (qsburn05 sector) s₀) (hReach : Reach C (qsburn05 sector) s₀ s) :
    (∀ h ws, recoverPlan C (qsburn05 sector) s.disk = some (h, ws) → s.acked ≤ h.len) ∧
    (∀ h, (view C (qsburn05 sector) s.disk).chain = some h →
      ∃ ws, recoverPlan C (qsburn05 sector) s.disk = some (h, ws)) ∧
    (∀ n t, s.live = some (n, t) → s.acked ≤ n) :=
  distinct_pages_safe hLaw (by rw [hSlot]; exact qsburn05_separated hS hDiv) hInit hReach

/-- `QSBURN04` and `qsag-hd/src/budget.rs`: slot A at `32..112`, slot B at `112..192`, records
    from 192, on 512-byte sectors. -/
@[expose] def sharedSectorLayout : Layout := ⟨512, 32, 112, 192⟩

/-- Every byte of both 80-byte slots lies in sector 0. -/
theorem sharedSectorLayout_shared :
    ∀ x, sharedSectorLayout.offA ≤ x → x < sharedSectorLayout.offB + 80 →
      x / sharedSectorLayout.sector = sharedSectorLayout.offA / sharedSectorLayout.sector := by
  intro x _ hx
  have hx : x < 112 + 80 := hx
  show x / 512 = 32 / 512
  omega

/-- `shared_sector_single_tear_loses_state` for the shared-sector layout with 80-byte slots. -/
theorem qsburn04_single_tear_loses_state {Tip Rec : Type} [DecidableEq Tip] {C : Codec Tip Rec}
    (hSlot : C.slotLen = 80) (hLaw : C.Lawful sharedSectorLayout.chainOff)
    {jA jB : List UInt8} (hjA : jA.length = 80) (hjB : jB.length = 80)
    (hvA : C.verify .a jA = none) (hvB : C.verify .b jB = none)
    {s : Sys Tip} {n : Nat} {t : Tip} (hLive : s.live = some (n, t)) (hAck : s.acked ≤ n)
    (hBound : n + 2 < C.bound) (r₁ r₂ : Rec) :
    ∃ s₁ s₂, Step C sharedSectorLayout s s₁ ∧ s₁.acked = n + 1 ∧
      Step C sharedSectorLayout s₁ s₂ ∧ s₂.acked = n + 1 ∧
      (view C sharedSectorLayout s₂.disk).a = none ∧
      (view C sharedSectorLayout s₂.disk).b = none ∧
      recoverPlan C sharedSectorLayout s₂.disk = none :=
  shared_sector_single_tear_loses_state hLaw (by rw [hSlot]; exact sharedSectorLayout_shared)
    (by rw [hSlot]; show 32 + 80 ≤ 112; omega) (by rw [hSlot]; show 112 + 80 ≤ 192; omega)
    (by rw [hSlot]; omega) (hjA.trans hSlot.symm) (hjB.trans hSlot.symm) hvA hvB hLive hAck
    hBound r₁ r₂

#verify_constructive view_slot_frame view_write_slot torn_slot_view
#verify_constructive exec_slotOps repairB_view commit_view recover_view reserve_exec
#verify_constructive SysInv.step distinct_pages_safe paged_layout_safe
#verify_constructive shared_sector_single_tear_loses_state append_tear_fails_closed
#verify_constructive qsburn05_separated sharedSectorLayout_shared
#tooth_pair distinct_pages_safe vs shared_sector_single_tear_loses_state
#tooth_pair distinct_pages_safe vs append_tear_fails_closed
#verify_constructive provisioned_steady init_can_commit qsburn05_safe
#verify_constructive qsburn04_single_tear_loses_state
#tooth_pair qsburn05_safe vs qsburn04_single_tear_loses_state

end Qsag.Exec.TwoSlotHwmCrashModel

public section
namespace Qsag.Exec.TwoSlotHwmCrashModel
set_option autoImplicit false

/-- `QSHDQB04` HD query-budget two-slot HWM paged layout (`budget.rs:108`):
    page 1 (`4096`) holds slot A, page 2 (`8192`) holds slot B, and records start at page 3 (`12288`). -/
@[expose] def qshdqb04 (sector : Nat) : Layout := Layout.paged sector 4096 1

theorem qshdqb04_eq (sector : Nat) : qshdqb04 sector = Layout.paged sector 4096 1 := by rfl

theorem qshdqb04_separated {sector : Nat} (hS : 0 < sector) (hDiv : sector ∣ 4096) :
    (qshdqb04 sector).Separated 80 :=
  Layout.paged_separated hS hDiv (by decide)



/-- `slots_permit_tail_truncation` (`wal.rs:353`, `budget.rs:117-133`):
    true iff at least one HWM slot authenticates AND every authenticating HWM slot `counter`
    satisfies `counter ≤ committed ∧ committed ≤ counter + 1`.
    This permits torn-tail truncation both when `Slot A = c, Slot B = c - 1` (crash between
    the two slot syncs) and when `committed = c + 1` (record `c` synced before HWM updated,
    followed by a torn append of record `c + 1`), while rejecting `committed < counter`
    (prefix truncation) and `committed > counter + 1` (unexplained multi-record gap). -/
@[expose] def slotsPermitTailTruncation {Tip Rec : Type}
    (C : Codec Tip Rec) (L : Layout) (d : Disk) (committed : Nat) : Bool :=
  let okSlot : Option (Nat × Tip) → Bool
    | none => true
    | some (ctr, _) => decide (ctr ≤ committed) && decide (committed ≤ ctr + 1)
  (((view C L d).a).isSome || ((view C L d).b).isSome) &&
  okSlot (view C L d).a && okSlot (view C L d).b

/-- Unique committed-record prefix count implied by a file length with `1..recLen` trailing
    unauthenticated bytes (`wal.rs:320-345`): both partial-record tears (`1 ≤ tail < recLen`)
    and full-length corrupt-MAC last-record tears (`tail = recLen`) map to the same prefix count. -/
@[expose] def committedPrefixCount {Tip Rec : Type} (C : Codec Tip Rec) (L : Layout) (d : Disk) : Nat :=
  (d.len - 1 - L.chainOff) / C.recLen

theorem committedPrefixCount_of_tail {Tip Rec : Type}
    (C : Codec Tip Rec) (L : Layout) (d : Disk) (committed : Nat)
    (hRecPos : 0 < C.recLen)
    (hTail : L.chainOff + C.recLen * committed < d.len ∧
      d.len - (L.chainOff + C.recLen * committed) ≤ C.recLen) :
    committedPrefixCount C L d = committed := by
  unfold committedPrefixCount
  have hEq : d.len - 1 - L.chainOff = C.recLen * committed + (d.len - (L.chainOff + C.recLen * committed) - 1) := by
    omega
  have hRem : d.len - (L.chainOff + C.recLen * committed) - 1 < C.recLen := by
    omega
  rw [hEq, Nat.mul_add_div hRecPos, Nat.div_eq_of_lt hRem, Nat.add_zero]

/-- Production recovery with uncommitted-tail truncation (`wal.rs:load_guarded` & `budget.rs:open_guarded`).
    The caller supplies NO counter, program, or authentication verdict:
    1. First try `recoverPlan C L d` (whole file parses with `tail_len = 0`).
    2. Otherwise require `0 < C.recLen` and `L.chainOff < d.len`, derive `committed` uniquely from
       `committedPrefixCount`, check `1 ≤ tail_len ≤ C.recLen` and `slotsPermitTailTruncation`
       (`hwm_counter ≤ committed ≤ hwm_counter + 1`), verify the entire truncated prefix via
       `recoverPlan C L (d.truncate stop)` BEFORE accepting truncation, and converge both HWM
       slots onto `(h.len, h.tip)` (`commitWrites h.len h.tip`). -/
@[expose] def recoverTruncatedAppendPlan {Tip Rec : Type} [DecidableEq Tip]
    (C : Codec Tip Rec) (L : Layout) (d : Disk) :
    Option (Disk × Head Tip × List (SlotWrite Tip)) :=
  match recoverPlan C L d with
  | some (h, ws) => some (d, h, ws)
  | none =>
    if decide (0 < C.recLen) && decide (L.chainOff < d.len) then
      let committed := committedPrefixCount C L d
      let stop := L.chainOff + C.recLen * committed
      if decide (stop < d.len) && decide (d.len - stop ≤ C.recLen) &&
         slotsPermitTailTruncation C L d committed then
        let prefixDisk := d.truncate stop
        match recoverPlan C L prefixDisk with
        | some (h, _ws) => some (prefixDisk, h, commitWrites h.len h.tip)
        | none => none
      else none
    else none

/-- **Liveness & Safety of Uncommitted-Tail Truncation (`append_tear_truncate_recovers`)**:
    When a crash during `append` leaves `1 ≤ tail_len ≤ C.recLen` unauthenticated trailing bytes
    (`recoverPlan C L d = none`), every authenticating HWM slot satisfies
    `hwm_counter ≤ committed ≤ hwm_counter + 1` (`slotsPermitTailTruncation C L d committed = true`),
    and the truncated prefix `d.truncate (L.chainOff + C.recLen * committed)` passes full chain MAC
    and two-slot HWM verification (`recoverPlan`), recovery succeeds by truncating to
    `L.chainOff + C.recLen * committed`, preserving every committed byte and converging both slots. -/
theorem append_tear_truncate_recovers {Tip Rec : Type} [DecidableEq Tip]
    {C : Codec Tip Rec} {L : Layout} {d : Disk} {committed : Nat}
    {h : Head Tip} {ws : List (SlotWrite Tip)}
    (hRecPos : 0 < C.recLen)
    (hTorn : recoverPlan C L d = none)
    (hTail : L.chainOff + C.recLen * committed < d.len ∧
      d.len - (L.chainOff + C.recLen * committed) ≤ C.recLen)
    (hSlots : slotsPermitTailTruncation C L d committed = true)
    (hCommitted : recoverPlan C L (d.truncate (L.chainOff + C.recLen * committed)) = some (h, ws)) :
    recoverTruncatedAppendPlan C L d =
      some (d.truncate (L.chainOff + C.recLen * committed), h, commitWrites h.len h.tip) ∧
    (d.truncate (L.chainOff + C.recLen * committed)).len = L.chainOff + C.recLen * committed ∧
    (∀ x, x < L.chainOff + C.recLen * committed →
      (d.truncate (L.chainOff + C.recLen * committed)).bytes x = d.bytes x) := by
  have hChainLt : L.chainOff < d.len := by omega
  have hCnt : committedPrefixCount C L d = committed :=
    committedPrefixCount_of_tail C L d committed hRecPos hTail
  refine ⟨?_, Disk.truncate_len _ _, fun _ _ => Disk.truncate_bytes _ _ _⟩
  unfold recoverTruncatedAppendPlan
  rw [hTorn]
  dsimp only
  have hb1 : (decide (0 < C.recLen) && decide (L.chainOff < d.len)) = true := by
    rw [decide_eq_true hRecPos, decide_eq_true hChainLt]; rfl
  rw [hb1]
  simp only [↓reduceIte]
  rw [hCnt]
  have hb2 : (decide (L.chainOff + C.recLen * committed < d.len) &&
      decide (d.len - (L.chainOff + C.recLen * committed) ≤ C.recLen) &&
      slotsPermitTailTruncation C L d committed) = true := by
    rw [decide_eq_true hTail.1, decide_eq_true hTail.2, hSlots]; rfl
  rw [hb2]
  simp only [↓reduceIte, hCommitted]

/-- Both staggered HWM slots `(c, c - 1)` at `committed = c` AND steady slots `(c, c)` at
    `committed = c + 1` satisfy `slotsPermitTailTruncation`. -/
theorem slotsPermitTailTruncation_staggered_and_plus_one {Tip Rec : Type}
    {C : Codec Tip Rec} {L : Layout} {d₁ d₂ : Disk} (c : Nat) (ta tb : Tip)
    (hc : 1 ≤ c)
    (hA₁ : (view C L d₁).a = some (c, ta))
    (hB₁ : (view C L d₁).b = some (c - 1, tb))
    (hA₂ : (view C L d₂).a = some (c, ta))
    (hB₂ : (view C L d₂).b = some (c, tb)) :
    slotsPermitTailTruncation C L d₁ c = true ∧
    slotsPermitTailTruncation C L d₂ (c + 1) = true := by
  unfold slotsPermitTailTruncation
  rw [hA₁, hB₁, hA₂, hB₂]
  dsimp only
  rw [decide_eq_true (Nat.le_refl c), decide_eq_true (Nat.le_add_right c 1),
      decide_eq_true (by omega : c - 1 ≤ c), decide_eq_true (by omega : c ≤ c - 1 + 1),
      decide_eq_true (Nat.le_refl (c + 1))]
  exact ⟨rfl, rfl⟩

/-- Any authenticating HWM slot outside `ctr ≤ committed ≤ ctr + 1` causes `slotsPermitTailTruncation`
    and `recoverTruncatedAppendPlan` to fail closed. -/
theorem slot_gap_exceeding_one_rejected {Tip Rec : Type} [DecidableEq Tip]
    {C : Codec Tip Rec} {L : Layout} {d : Disk} {ctr : Nat} {t : Tip}
    (hTorn : recoverPlan C L d = none)
    (hSlotA : (view C L d).a = some (ctr, t))
    (hGap : committedPrefixCount C L d < ctr ∨ ctr + 1 < committedPrefixCount C L d) :
    recoverTruncatedAppendPlan C L d = none := by
  have hFalse : slotsPermitTailTruncation C L d (committedPrefixCount C L d) = false := by
    have hRangeF : (decide (ctr ≤ committedPrefixCount C L d) &&
        decide (committedPrefixCount C L d ≤ ctr + 1)) = false := by
      rcases hGap with hLt | hGt
      · rw [decide_eq_false (Nat.not_le_of_gt hLt), Bool.false_and]
      · rw [decide_eq_false (Nat.not_le_of_gt hGt), Bool.and_false]
    unfold slotsPermitTailTruncation
    rw [hSlotA]
    simp only [Option.isSome_some, Bool.true_or, hRangeF, Bool.false_and, Bool.true_and]
  unfold recoverTruncatedAppendPlan
  rw [hTorn]
  cases hb1 : (decide (0 < C.recLen) && decide (L.chainOff < d.len))
  · rfl
  · dsimp only [↓reduceIte]
    rw [hFalse, Bool.and_false]
    rfl

/-- Neither a zero-length chain nor a shortened/empty file beyond `chainOff` authorizes truncation. -/
theorem truncated_or_oversized_tail_rejected {Tip Rec : Type} [DecidableEq Tip]
    {C : Codec Tip Rec} {L : Layout} {d : Disk}
    (hTorn : recoverPlan C L d = none)
    (hBad : d.len ≤ L.chainOff ∨ C.recLen = 0) :
    recoverTruncatedAppendPlan C L d = none := by
  have hb1 : (decide (0 < C.recLen) && decide (L.chainOff < d.len)) = false := by
    rcases hBad with hLe | hZ
    · have hf : decide (L.chainOff < d.len) = false := decide_eq_false (Nat.not_lt_of_ge hLe)
      rw [hf, Bool.and_false]
    · have hf : decide (0 < C.recLen) = false := decide_eq_false (by omega)
      rw [hf, Bool.false_and]
  unfold recoverTruncatedAppendPlan
  rw [hTorn, hb1]
  rfl

/-- A corrupt committed prefix is refused even when the tail length and HWM slots pass. -/
theorem corrupt_committed_record_rejected {Tip Rec : Type} [DecidableEq Tip]
    {C : Codec Tip Rec} {L : Layout} {d : Disk}
    (hTorn : recoverPlan C L d = none)
    (hCorrupt : recoverPlan C L (d.truncate (L.chainOff + C.recLen * committedPrefixCount C L d)) = none) :
    recoverTruncatedAppendPlan C L d = none := by
  unfold recoverTruncatedAppendPlan
  rw [hTorn]
  cases hb1 : (decide (0 < C.recLen) && decide (L.chainOff < d.len))
  · rfl
  · dsimp only [↓reduceIte]
    cases hb2 : (decide (L.chainOff + C.recLen * committedPrefixCount C L d < d.len) &&
        decide (d.len - (L.chainOff + C.recLen * committedPrefixCount C L d) ≤ C.recLen) &&
        slotsPermitTailTruncation C L d (committedPrefixCount C L d))
    · rfl
    · simp only [↓reduceIte, hCorrupt]

#verify_constructive qshdqb04_separated committedPrefixCount_of_tail
  append_tear_truncate_recovers slotsPermitTailTruncation_staggered_and_plus_one
  slot_gap_exceeding_one_rejected truncated_or_oversized_tail_rejected
  corrupt_committed_record_rejected
#tooth_pair append_tear_truncate_recovers vs corrupt_committed_record_rejected
#tooth_pair append_tear_truncate_recovers vs slot_gap_exceeding_one_rejected
end Qsag.Exec.TwoSlotHwmCrashModel
end
