module
/-
# Qsag.Machine.Ass2DitNoninterference — data-independent timing of `ASS2 / Dregg-64`

Noninterference of the `ASS2 / Dregg-64` step function (`Qsag.Machine.Ass2Dregg64Isa`) for the
observation an enclave adversary has of a run: the `PC` trace, the trace of data addresses, and
the `CYCLES` and `INSTRET` counters.

* `PubCfg`: which registers, sponge lanes and memory bytes are public. `Ass2PubEquiv cfg s₁ s₂`:
  the two states agree on `PC`, on every control register and on the public registers, lanes and
  bytes.
* `ditOk cfg i`: the side conditions on one instruction. The base register of `LOAD`, `STORE`,
  `SLD64`, `SST64` and `JALR`, the condition register of `BR` and the source of `CSRW` are public.
  Every other instruction is accepted on secret operands.
* `ditPost cfg i s`: the labels after the instruction. A result is public when all of its inputs
  are; a store labels the bytes it writes with the label of the stored value.
* `exec_noninterference`, `ass2_dit_step_noninterference`, `ass2_dit_run_trace_noninterference`:
  equivalent states take the same step observations and stay equivalent.
* `ass2DitContract`: the `Spec.DitHardwareContract` of the leakage function `ass2Leakage`.
* `ditSafeRun_straight`: a loaded straight-line program with public code is safe from every
  state, whatever its registers and lanes hold.
* `ass2_zkhem_v2_fp5_horner_and_turboshake_leaf_verified`: a 25-word program computing a
  degree-2 Horner evaluation in `QuinticGoldilocks` and one `TurboSHAKE256` block of a Merkle
  parent, with its result and its secret-independent trace.

The code bytes at `PC` have to be public: the instruction word is an input of the step.
-/

public import Qsag.Machine.Ass2Dregg64Isa
public import Qsag.Spec.Assumptions
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Ass2

set_option autoImplicit false

/-! ## 1. Public / secret partition -/

/-- The public registers, lanes and memory bytes. -/
structure PubCfg where
  reg : Reg → Bool
  lane : Fin 25 → Bool
  mem : UInt64 → Bool

namespace PubCfg

/-- `R0` is public under every configuration. -/
abbrev regPub (cfg : PubCfg) (r : Reg) : Bool := if r = 0 then true else cfg.reg r

/-- A lane index `≥ 25` reads as `0` and is public. -/
abbrev lanePub (cfg : PubCfg) (k : Nat) : Bool := if h : k < 25 then cfg.lane ⟨k, h⟩ else true

/-- Relabel one register. -/
abbrev setReg (cfg : PubCfg) (rd : Reg) (b : Bool) : PubCfg :=
  { cfg with reg := fun r => if r = rd then b else cfg.reg r }

/-- Relabel the lanes. -/
abbrev setLanes (cfg : PubCfg) (f : Fin 25 → Bool) : PubCfg := { cfg with lane := f }

/-- Relabel the memory. -/
abbrev setMem (cfg : PubCfg) (f : UInt64 → Bool) : PubCfg := { cfg with mem := f }

end PubCfg

/-- `f k` holds for every `k < n`. -/
def allBelow : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, f => f n && allBelow n f

theorem band_split {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> first | exact ⟨rfl, rfl⟩ | cases h

theorem allBelow_spec {n : Nat} {f : Nat → Bool} (h : allBelow n f = true) :
    ∀ k, k < n → f k = true := by
  induction n with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    intro k hk
    have h' : (f n && allBelow n f) = true := h
    obtain ⟨h1, h2⟩ := band_split h'
    by_cases hkn : k = n
    · rw [hkn]; exact h1
    · exact ih h2 k (by omega)

theorem allBelow_of {n : Nat} {f : Nat → Bool} (h : ∀ k, k < n → f k = true) :
    allBelow n f = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (f n && allBelow n f) = true
    rw [h n (Nat.lt_succ_self n), ih (fun k hk => h k (Nat.lt_succ_of_lt hk))]
    rfl

/-- The `n` bytes at `a` are public. -/
abbrev memPub (lab : UInt64 → Bool) (a : UInt64) (n : Nat) : Bool :=
  allBelow n (fun k => lab (a + UInt64.ofNat k))

/-- The `n` lanes from `base` are public. -/
abbrev lanesPub (cfg : PubCfg) (base n : Nat) : Bool :=
  allBelow n (fun t => cfg.lanePub (base + t))

/-- Lanes `0 .. n - 1` are public. -/
abbrev allLanesPub (cfg : PubCfg) (n : Nat) : Bool := allBelow n cfg.lanePub

/-- Two states agree on everything public: `PC`, the control registers and counters, the debug
    stream, and the registers, lanes and bytes that `cfg` marks public. -/
structure Ass2PubEquiv (cfg : PubCfg) (s₁ s₂ : Ass2State) : Prop where
  pc : s₁.pc = s₂.pc
  evec : s₁.evec = s₂.evec
  epc : s₁.epc = s₂.epc
  ecause : s₁.ecause = s₂.ecause
  excEn : s₁.excEn = s₂.excEn
  halted : s₁.halted = s₂.halted
  instret : s₁.instret = s₂.instret
  cycles : s₁.cycles = s₂.cycles
  dbgOut : s₁.dbgOut = s₂.dbgOut
  dbgIn : s₁.dbgIn = s₂.dbgIn
  regs : ∀ r, cfg.regPub r = true → s₁.rget r = s₂.rget r
  spg : ∀ k, cfg.lane k = true → s₁.spg k = s₂.spg k
  mem : ∀ a, cfg.mem a = true → s₁.mem a = s₂.mem a

/-! ## 2. Side conditions and label transfer -/

/-- The side conditions of one instruction: address bases, branch conditions, jump bases and
    control-register sources are public. -/
@[expose] def ditOk (cfg : PubCfg) : Ass2Insn → Bool
  | .csrw ra _ => cfg.regPub ra
  | .ld64 _ ra _ => cfg.regPub ra
  | .ldbu _ ra _ => cfg.regPub ra
  | .st64 _ ra _ => cfg.regPub ra
  | .stb _ ra _ => cfg.regPub ra
  | .br _ rc _ => cfg.regPub rc
  | .jalr _ ra _ => cfg.regPub ra
  | .sld64 _ ra _ => cfg.regPub ra
  | .sst64 _ ra _ => cfg.regPub ra
  | _ => true

/-- The labels after `i` executes in `s`. The state enters through public values only: the
    alignment of an address and the address a store writes. -/
@[expose] def ditPost (cfg : PubCfg) (i : Ass2Insn) (s : Ass2State) : PubCfg :=
  match i with
  | .exc => cfg
  | .eret => cfg
  | .csrr rd a =>
    match csrReadAddr s.dbgIn a.toNat with
    | some _ => cfg.setReg rd true
    | none => cfg
  | .csrw _ _ => cfg
  | .zeroize => { reg := fun _ => true, lane := fun _ => true, mem := cfg.mem }
  | .halt => cfg
  | .nop => cfg
  | .lut4 _ rd ra rb => cfg.setReg rd (cfg.regPub ra && cfg.regPub rb)
  | .alu _ rd ra rb => cfg.setReg rd (cfg.regPub ra && cfg.regPub rb)
  | .alui _ rd ra _ => cfg.setReg rd (cfg.regPub ra)
  | .movz20 rd _ => cfg.setReg rd true
  | .movs20 rd _ => cfg.setReg rd true
  | .auipc rd _ => cfg.setReg rd true
  | .cmp _ rd ra rb => cfg.setReg rd (cfg.regPub ra && cfg.regPub rb)
  | .sel rd ra rb rc => cfg.setReg rd (cfg.regPub ra && cfg.regPub rb && cfg.regPub rc)
  | .bextu rd ra _ _ => cfg.setReg rd (cfg.regPub ra)
  | .bexts rd ra _ _ => cfg.setReg rd (cfg.regPub ra)
  | .bswap64 rd ra => cfg.setReg rd (cfg.regPub ra)
  | .ld64 rd ra off =>
    if (s.rget ra + (sext off <<< (3 : UInt64))).toNat % 8 = 0 then
      cfg.setReg rd (memPub cfg.mem (s.rget ra + (sext off <<< (3 : UInt64))) 8)
    else cfg
  | .ldbu rd ra off => cfg.setReg rd (cfg.mem (s.rget ra + sext off))
  | .st64 rv ra off =>
    if (s.rget ra + (sext off <<< (3 : UInt64))).toNat % 8 = 0 then
      cfg.setMem (fun x =>
        if (x - (s.rget ra + (sext off <<< (3 : UInt64)))).toNat < 8 then cfg.regPub rv
        else cfg.mem x)
    else cfg
  | .stb rv ra off =>
    cfg.setMem (fun x => if x = s.rget ra + sext off then cfg.regPub rv else cfg.mem x)
  | .br _ _ _ => cfg
  | .jal rd _ => cfg.setReg rd true
  | .jalr rd ra off =>
    if (s.rget ra + (sext off <<< (2 : UInt64))).toNat % 4 = 0 then cfg.setReg rd true else cfg
  | .sget rd k => cfg.setReg rd (cfg.lanePub k.toNat)
  | .sput k ra => cfg.setLanes (fun j => if j.val = k.toNat then cfg.regPub ra else cfg.lane j)
  | .sxor k ra =>
    cfg.setLanes (fun j =>
      if j.val = k.toNat then cfg.lanePub k.toNat && cfg.regPub ra else cfg.lane j)
  | .szero => cfg.setLanes (fun _ => true)
  | .sld64 k ra off =>
    if (s.rget ra + (sext off <<< (3 : UInt64))).toNat % 8 = 0 then
      cfg.setLanes (fun j =>
        if j.val = k.toNat then memPub cfg.mem (s.rget ra + (sext off <<< (3 : UInt64))) 8
        else cfg.lane j)
    else cfg
  | .sst64 k ra off =>
    if (s.rget ra + (sext off <<< (3 : UInt64))).toNat % 8 = 0 then
      cfg.setMem (fun x =>
        if (x - (s.rget ra + (sext off <<< (3 : UInt64)))).toNat < 8 then cfg.lanePub k.toNat
        else cfg.mem x)
    else cfg
  | .glMac rd ra rb rc => cfg.setReg rd (cfg.regPub ra && cfg.regPub rb && cfg.regPub rc)
  | .glAdd rd ra rb => cfg.setReg rd (cfg.regPub ra && cfg.regPub rb)
  | .glSub rd ra rb => cfg.setReg rd (cfg.regPub ra && cfg.regPub rb)
  | .glSbox7 rd ra => cfg.setReg rd (cfg.regPub ra)
  | .fp5Mul ed ea eb =>
    cfg.setLanes (fun j =>
      if j.val / 5 = ed.val then lanesPub cfg (5 * ea.val) 5 && lanesPub cfg (5 * eb.val) 5
      else cfg.lane j)
  | .fp5Add ed ea eb =>
    cfg.setLanes (fun j =>
      if j.val / 5 = ed.val then lanesPub cfg (5 * ea.val) 5 && lanesPub cfg (5 * eb.val) 5
      else cfg.lane j)
  | .fp5Sub ed ea eb =>
    cfg.setLanes (fun j =>
      if j.val / 5 = ed.val then lanesPub cfg (5 * ea.val) 5 && lanesPub cfg (5 * eb.val) 5
      else cfg.lane j)
  | .gf128Mul pd pa pb =>
    cfg.setLanes (fun j =>
      if j.val / 2 = pd.val then lanesPub cfg (2 * pa.val) 2 && lanesPub cfg (2 * pb.val) 2
      else cfg.lane j)
  | .gf128Xor pd pa pb =>
    cfg.setLanes (fun j =>
      if j.val / 2 = pd.val then lanesPub cfg (2 * pa.val) 2 && lanesPub cfg (2 * pb.val) 2
      else cfg.lane j)
  | .keccak _ => cfg.setLanes (fun _ => allLanesPub cfg 25)
  | .poseidon2Gl24 => cfg.setLanes (fun j => if j.val < 24 then allLanesPub cfg 24 else cfg.lane j)
  | .poseidon2Gl12 => cfg.setLanes (fun j => if j.val < 12 then allLanesPub cfg 12 else cfg.lane j)

/-! ## 3. Equivalence is preserved by the state updates -/

section Updates
variable {cfg : PubCfg} {s₁ s₂ : Ass2State}

theorem lane_eq (heq : Ass2PubEquiv cfg s₁ s₂) (k : Nat) (h : cfg.lanePub k = true) :
    lane s₁.spg k = lane s₂.spg k := by
  have h' : (if hk : k < 25 then cfg.lane ⟨k, hk⟩ else true) = true := h
  show (if hk : k < 25 then s₁.spg ⟨k, hk⟩ else 0) = (if hk : k < 25 then s₂.spg ⟨k, hk⟩ else 0)
  by_cases hk : k < 25
  · rw [dite_eq_left hk] at h'
    rw [dite_eq_left hk, dite_eq_left hk]
    exact heq.spg _ h'
  · rw [dite_eq_right hk, dite_eq_right hk]

/-- Retirement with new registers, lanes and memory that agree where the new labels are public. -/
theorem equiv_update (heq : Ass2PubEquiv cfg s₁ s₂) {cfg' : PubCfg}
    {r₁ r₂ : Reg → UInt64} {σ₁ σ₂ : Fin 25 → UInt64} {m₁ m₂ : UInt64 → UInt8}
    {npc₁ npc₂ : UInt64} (c : UInt64) (hpc : npc₁ = npc₂)
    (hr : ∀ r, cfg'.regPub r = true →
      (if r = 0 then (0 : UInt64) else r₁ r) = (if r = 0 then (0 : UInt64) else r₂ r))
    (hσ : ∀ k, cfg'.lane k = true → σ₁ k = σ₂ k)
    (hm : ∀ a, cfg'.mem a = true → m₁ a = m₂ a) :
    Ass2PubEquiv cfg'
      { s₁ with pc := npc₁, regs := r₁, spg := σ₁, mem := m₁, instret := s₁.instret + 1,
                cycles := s₁.cycles + c }
      { s₂ with pc := npc₂, regs := r₂, spg := σ₂, mem := m₂, instret := s₂.instret + 1,
                cycles := s₂.cycles + c } :=
  ⟨hpc, heq.evec, heq.epc, heq.ecause, heq.excEn, heq.halted,
    congrArg (fun x => x + 1) heq.instret, congrArg (fun x => x + c) heq.cycles, heq.dbgOut, heq.dbgIn,
    hr, hσ, hm⟩

theorem regs_setReg (heq : Ass2PubEquiv cfg s₁ s₂) (rd : Reg) {lab : Bool} {v₁ v₂ : UInt64}
    (hv : lab = true → v₁ = v₂) :
    ∀ r, (cfg.setReg rd lab).regPub r = true →
      (if r = 0 then (0 : UInt64) else (if r = rd ∧ rd ≠ 0 then v₁ else s₁.regs r)) =
      (if r = 0 then (0 : UInt64) else (if r = rd ∧ rd ≠ 0 then v₂ else s₂.regs r)) := by
  intro r hr
  have hr' : (if r = 0 then true else (if r = rd then lab else cfg.reg r)) = true := hr
  by_cases h0 : r = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
  · rw [ite_eq_right h0] at hr'
    rw [ite_eq_right h0, ite_eq_right h0]
    by_cases hrd : r = rd
    · rw [ite_eq_left hrd] at hr'
      have hc : r = rd ∧ rd ≠ 0 := ⟨hrd, fun e => h0 (hrd.trans e)⟩
      rw [ite_eq_left hc, ite_eq_left hc]
      exact hv hr'
    · rw [ite_eq_right hrd] at hr'
      have hc : ¬ (r = rd ∧ rd ≠ 0) := fun e => hrd e.1
      rw [ite_eq_right hc, ite_eq_right hc]
      have hp : (if r = 0 then true else cfg.reg r) = true := by rw [ite_eq_right h0]; exact hr'
      have h2 : (if r = 0 then (0 : UInt64) else s₁.regs r) =
          (if r = 0 then (0 : UInt64) else s₂.regs r) := heq.regs r hp
      rw [ite_eq_right h0, ite_eq_right h0] at h2
      exact h2

/-- A register write that retires to `npc`. -/
theorem equiv_setRegTo (heq : Ass2PubEquiv cfg s₁ s₂) (rd : Reg) {lab : Bool} {v₁ v₂ : UInt64}
    {npc₁ npc₂ : UInt64} (c : UInt64) (hpc : npc₁ = npc₂) (hv : lab = true → v₁ = v₂) :
    Ass2PubEquiv (cfg.setReg rd lab) ((s₁.setReg rd v₁).retireTo npc₁ c)
      ((s₂.setReg rd v₂).retireTo npc₂ c) :=
  equiv_update heq c hpc (regs_setReg heq rd hv) heq.spg heq.mem

/-- A register write that retires to `PC + 4`. -/
theorem equiv_setReg (heq : Ass2PubEquiv cfg s₁ s₂) (rd : Reg) {lab : Bool} {v₁ v₂ : UInt64}
    (c : UInt64) (hv : lab = true → v₁ = v₂) :
    Ass2PubEquiv (cfg.setReg rd lab) ((s₁.setReg rd v₁).retire c) ((s₂.setReg rd v₂).retire c) :=
  equiv_setRegTo heq rd c (congrArg (fun x => x + 4) heq.pc) hv

theorem equiv_setSpg (heq : Ass2PubEquiv cfg s₁ s₂) {lab : Fin 25 → Bool}
    {σ₁ σ₂ : Fin 25 → UInt64} (c : UInt64) (hσ : ∀ k, lab k = true → σ₁ k = σ₂ k) :
    Ass2PubEquiv (cfg.setLanes lab) ((s₁.setSpg σ₁).retire c) ((s₂.setSpg σ₂).retire c) :=
  equiv_update heq c (congrArg (fun x => x + 4) heq.pc) heq.regs hσ heq.mem

theorem equiv_setMem (heq : Ass2PubEquiv cfg s₁ s₂) {lab : UInt64 → Bool}
    {m₁ m₂ : UInt64 → UInt8} (c : UInt64) (hm : ∀ a, lab a = true → m₁ a = m₂ a) :
    Ass2PubEquiv (cfg.setMem lab) ((s₁.setMem m₁).retire c) ((s₂.setMem m₂).retire c) :=
  equiv_update heq c (congrArg (fun x => x + 4) heq.pc) heq.regs heq.spg hm

theorem equiv_retireTo (heq : Ass2PubEquiv cfg s₁ s₂) {npc₁ npc₂ : UInt64} (c : UInt64)
    (hpc : npc₁ = npc₂) : Ass2PubEquiv cfg (s₁.retireTo npc₁ c) (s₂.retireTo npc₂ c) :=
  equiv_update heq c hpc heq.regs heq.spg heq.mem

theorem equiv_trap (heq : Ass2PubEquiv cfg s₁ s₂) (c : UInt64) :
    Ass2PubEquiv cfg (s₁.trap c) (s₂.trap c) := by
  unfold Ass2State.trap
  by_cases h : s₁.excEn = true
  · have h₂ : s₂.excEn = true := by rw [← heq.excEn]; exact h
    rw [ite_eq_left h, ite_eq_left h₂]
    exact ⟨heq.evec, heq.evec, heq.pc, rfl, rfl, heq.halted, heq.instret, congrArg (· + 1) heq.cycles,
      heq.dbgOut, heq.dbgIn, heq.regs, heq.spg, heq.mem⟩
  · have h₂ : ¬ s₂.excEn = true := by rw [← heq.excEn]; exact h
    rw [ite_eq_right h, ite_eq_right h₂]
    exact ⟨heq.pc, heq.evec, heq.epc, rfl, heq.excEn, rfl, heq.instret, congrArg (· + 1) heq.cycles,
      heq.dbgOut, heq.dbgIn, heq.regs, heq.spg, heq.mem⟩

theorem equiv_ite {c₁ c₂ : Prop} [Decidable c₁] [Decidable c₂] (hc : c₁ ↔ c₂)
    {cfgA cfgB : PubCfg} {a₁ b₁ a₂ b₂ : Ass2State}
    (hA : c₁ → Ass2PubEquiv cfgA a₁ a₂) (hB : ¬ c₁ → Ass2PubEquiv cfgB b₁ b₂) :
    Ass2PubEquiv (if c₁ then cfgA else cfgB) (if c₁ then a₁ else b₁) (if c₂ then a₂ else b₂) := by
  by_cases h : c₁
  · rw [ite_eq_left h, ite_eq_left h, ite_eq_left (hc.mp h)]
    exact hA h
  · rw [ite_eq_right h, ite_eq_right h, ite_eq_right (fun h₂ => h (hc.mpr h₂))]
    exact hB h

theorem equiv_ite_same {c₁ c₂ : Prop} [Decidable c₁] [Decidable c₂] (hc : c₁ ↔ c₂)
    {cfg' : PubCfg} {a₁ b₁ a₂ b₂ : Ass2State}
    (hA : c₁ → Ass2PubEquiv cfg' a₁ a₂) (hB : ¬ c₁ → Ass2PubEquiv cfg' b₁ b₂) :
    Ass2PubEquiv cfg' (if c₁ then a₁ else b₁) (if c₂ then a₂ else b₂) := by
  by_cases h : c₁
  · rw [ite_eq_left h, ite_eq_left (hc.mp h)]
    exact hA h
  · rw [ite_eq_right h, ite_eq_right (fun h₂ => h (hc.mpr h₂))]
    exact hB h

end Updates

/-! ### Pointwise agreement of the written views -/

theorem write64_pub {m₁ m₂ : UInt64 → UInt8} {lab : UInt64 → Bool} {b : Bool}
    {v₁ v₂ a : UInt64} (hv : b = true → v₁ = v₂) (hm : ∀ x, lab x = true → m₁ x = m₂ x) :
    ∀ x, (if (x - a).toNat < 8 then b else lab x) = true →
      write64 m₁ a v₁ x = write64 m₂ a v₂ x := by
  intro x hx
  show (if (x - a).toNat < 8 then (v₁ >>> UInt64.ofNat (8 * (x - a).toNat)).toUInt8 else m₁ x) =
    (if (x - a).toNat < 8 then (v₂ >>> UInt64.ofNat (8 * (x - a).toNat)).toUInt8 else m₂ x)
  by_cases h : (x - a).toNat < 8
  · rw [ite_eq_left h] at hx
    rw [ite_eq_left h, ite_eq_left h, hv hx]
  · rw [ite_eq_right h] at hx
    rw [ite_eq_right h, ite_eq_right h]
    exact hm x hx

theorem store8_pub {m₁ m₂ : UInt64 → UInt8} {lab : UInt64 → Bool} {b : Bool}
    {v₁ v₂ a : UInt64} (hv : b = true → v₁ = v₂) (hm : ∀ x, lab x = true → m₁ x = m₂ x) :
    ∀ x, (if x = a then b else lab x) = true →
      (if x = a then v₁.toUInt8 else m₁ x) = (if x = a then v₂.toUInt8 else m₂ x) := by
  intro x hx
  by_cases h : x = a
  · rw [ite_eq_left h] at hx
    rw [ite_eq_left h, ite_eq_left h, hv hx]
  · rw [ite_eq_right h] at hx
    rw [ite_eq_right h, ite_eq_right h]
    exact hm x hx

theorem setLane_pub {σ₁ σ₂ : Fin 25 → UInt64} {lab : Fin 25 → Bool} {b : Bool}
    {v₁ v₂ : UInt64} {k : Nat} (hv : b = true → v₁ = v₂)
    (hσ : ∀ j, lab j = true → σ₁ j = σ₂ j) :
    ∀ j : Fin 25, (if j.val = k then b else lab j) = true →
      setLane σ₁ k v₁ j = setLane σ₂ k v₂ j := by
  intro j hj
  show (if j.val = k then v₁ else σ₁ j) = (if j.val = k then v₂ else σ₂ j)
  by_cases h : j.val = k
  · rw [ite_eq_left h] at hj
    rw [ite_eq_left h, ite_eq_left h]
    exact hv hj
  · rw [ite_eq_right h] at hj
    rw [ite_eq_right h, ite_eq_right h]
    exact hσ j hj

theorem fp5Write_pub {σ₁ σ₂ : Fin 25 → UInt64} {lab : Fin 25 → Bool} {b : Bool}
    {q₁ q₂ : QuinticGoldilocks} {d : Nat} (hq : b = true → q₁ = q₂)
    (hσ : ∀ j, lab j = true → σ₁ j = σ₂ j) :
    ∀ j : Fin 25, (if j.val / 5 = d then b else lab j) = true →
      fp5Write σ₁ d q₁ j = fp5Write σ₂ d q₂ j := by
  intro j hj
  by_cases h : j.val / 5 = d
  · rw [ite_eq_left h] at hj
    rw [fp5Write_in σ₁ d q₁ j h, fp5Write_in σ₂ d q₂ j h, hq hj]
  · rw [ite_eq_right h] at hj
    rw [fp5Write_out σ₁ d q₁ j h, fp5Write_out σ₂ d q₂ j h]
    exact hσ j hj

theorem gfWrite_pub {σ₁ σ₂ : Fin 25 → UInt64} {lab : Fin 25 → Bool} {b : Bool}
    {x₁ x₂ : Math.Gf2Pow128} {d : Nat} (hx : b = true → x₁ = x₂)
    (hσ : ∀ j, lab j = true → σ₁ j = σ₂ j) :
    ∀ j : Fin 25, (if j.val / 2 = d then b else lab j) = true →
      gfWrite σ₁ d x₁ j = gfWrite σ₂ d x₂ j := by
  intro j hj
  by_cases h : j.val / 2 = d
  · rw [ite_eq_left h] at hj
    rw [gfWrite_in σ₁ d x₁ j h, gfWrite_in σ₂ d x₂ j h, hx hj]
  · rw [ite_eq_right h] at hj
    rw [gfWrite_out σ₁ d x₁ j h, gfWrite_out σ₂ d x₂ j h]
    exact hσ j hj

theorem prefix_pub {σ₁ σ₂ : Fin 25 → UInt64} {lab : Fin 25 → Bool} {b : Bool} (n : Nat)
    (f₁ f₂ : Nat → UInt64) (hf : b = true → f₁ = f₂) (hσ : ∀ j, lab j = true → σ₁ j = σ₂ j) :
    ∀ j : Fin 25, (if j.val < n then b else lab j) = true →
      (if j.val < n then f₁ j.val else σ₁ j) = (if j.val < n then f₂ j.val else σ₂ j) := by
  intro j hj
  by_cases h : j.val < n
  · rw [ite_eq_left h] at hj
    rw [ite_eq_left h, ite_eq_left h, hf hj]
  · rw [ite_eq_right h] at hj
    rw [ite_eq_right h, ite_eq_right h]
    exact hσ j hj

/-! ## 4. One instruction -/

section Exec
variable {cfg : PubCfg} {s₁ s₂ : Ass2State}

theorem csrGet_equiv (heq : Ass2PubEquiv cfg s₁ s₂) (c : CsrR) : csrGet s₁ c = csrGet s₂ c := by
  cases c
  case evec => exact heq.evec
  case instret => exact heq.instret
  case cycles => exact heq.cycles
  case epc => exact heq.epc
  case ecause => exact heq.ecause
  case dbgIn => exact congrArg debugInputValue heq.dbgIn
  case excEn =>
    show (if s₁.excEn = true then (1 : UInt64) else 0) = (if s₂.excEn = true then (1 : UInt64) else 0)
    rw [heq.excEn]
  all_goals rfl

theorem csrApply_equiv (heq : Ass2PubEquiv cfg s₁ s₂) (c : CsrW) (v : UInt64) :
    Ass2PubEquiv cfg (csrApply s₁ c v) (csrApply s₂ c v) := by
  have pc4 : s₁.pc + 4 = s₂.pc + 4 := congrArg (fun x => x + 4) heq.pc
  have ir1 : s₁.instret + 1 = s₂.instret + 1 := congrArg (fun x => x + 1) heq.instret
  have cy1 : s₁.cycles + 1 = s₂.cycles + 1 := congrArg (fun x => x + 1) heq.cycles
  cases c
  case evec =>
    exact ⟨pc4, rfl, heq.epc, heq.ecause, heq.excEn, heq.halted, ir1, cy1, heq.dbgOut, heq.dbgIn, heq.regs,
      heq.spg, heq.mem⟩
  case power =>
    exact ⟨pc4, heq.evec, heq.epc, heq.ecause, heq.excEn,
      congrArg (fun x => x || decide (v.toNat % 2 = 1)) heq.halted, ir1, cy1, heq.dbgOut, heq.dbgIn,
      heq.regs, heq.spg, heq.mem⟩
  case instret =>
    exact ⟨pc4, heq.evec, heq.epc, heq.ecause, heq.excEn, heq.halted, rfl, cy1, heq.dbgOut, heq.dbgIn,
      heq.regs, heq.spg, heq.mem⟩
  case cycles =>
    exact ⟨pc4, heq.evec, heq.epc, heq.ecause, heq.excEn, heq.halted, ir1, rfl, heq.dbgOut, heq.dbgIn,
      heq.regs, heq.spg, heq.mem⟩
  case epc =>
    exact ⟨pc4, heq.evec, rfl, heq.ecause, heq.excEn, heq.halted, ir1, cy1, heq.dbgOut, heq.dbgIn,
      heq.regs, heq.spg, heq.mem⟩
  case ecause =>
    exact ⟨pc4, heq.evec, heq.epc, rfl, heq.excEn, heq.halted, ir1, cy1, heq.dbgOut, heq.dbgIn,
      heq.regs, heq.spg, heq.mem⟩
  case dbgOut =>
    exact ⟨pc4, heq.evec, heq.epc, heq.ecause, heq.excEn, heq.halted, ir1, cy1,
      congrArg (fun x => x ++ [v.toUInt8]) heq.dbgOut, heq.dbgIn, heq.regs, heq.spg, heq.mem⟩
  case excEn =>
    exact ⟨pc4, heq.evec, heq.epc, heq.ecause, rfl, heq.halted, ir1, cy1, heq.dbgOut, heq.dbgIn,
      heq.regs, heq.spg, heq.mem⟩
  case zeroize =>
    show Ass2PubEquiv cfg (Ass2State.retire (if v.toNat % 2 = 1 then s₁.wipe else s₁) 1)
      (Ass2State.retire (if v.toNat % 2 = 1 then s₂.wipe else s₂) 1)
    by_cases hb : v.toNat % 2 = 1
    · rw [ite_eq_left hb, ite_eq_left hb]
      exact ⟨pc4, heq.evec, heq.epc, heq.ecause, heq.excEn, heq.halted, ir1, cy1, heq.dbgOut, heq.dbgIn,
        fun _ _ => rfl, fun _ _ => rfl, heq.mem⟩
    · rw [ite_eq_right hb, ite_eq_right hb]
      exact equiv_retireTo heq 1 pc4

theorem fp5Read_pub (heq : Ass2PubEquiv cfg s₁ s₂) {e : Nat}
    (h : lanesPub cfg (5 * e) 5 = true) : fp5Read s₁.spg e = fp5Read s₂.spg e :=
  fp5Read_congr fun t ht => lane_eq heq _ (allBelow_spec h t ht)

theorem gfRead_pub (heq : Ass2PubEquiv cfg s₁ s₂) {k : Nat}
    (h : lanesPub cfg (2 * k) 2 = true) : gfRead s₁.spg k = gfRead s₂.spg k :=
  gfRead_congr fun t ht => lane_eq heq _ (allBelow_spec h t ht)

/-- A result register computed from one source register. -/
theorem equiv_reg1 (heq : Ass2PubEquiv cfg s₁ s₂) (f : UInt64 → UInt64) (rd ra : Reg)
    (c : UInt64) :
    Ass2PubEquiv (cfg.setReg rd (cfg.regPub ra)) ((s₁.setReg rd (f (s₁.rget ra))).retire c)
      ((s₂.setReg rd (f (s₂.rget ra))).retire c) :=
  equiv_setReg heq rd c fun h => congrArg f (heq.regs ra h)

/-- A result register computed from two source registers. -/
theorem equiv_reg2 (heq : Ass2PubEquiv cfg s₁ s₂) (f : UInt64 → UInt64 → UInt64)
    (rd ra rb : Reg) (c : UInt64) :
    Ass2PubEquiv (cfg.setReg rd (cfg.regPub ra && cfg.regPub rb))
      ((s₁.setReg rd (f (s₁.rget ra) (s₁.rget rb))).retire c)
      ((s₂.setReg rd (f (s₂.rget ra) (s₂.rget rb))).retire c) :=
  equiv_setReg heq rd c fun h => by
    obtain ⟨ha, hb⟩ := band_split h
    rw [heq.regs ra ha, heq.regs rb hb]

/-- A result register computed from three source registers. -/
theorem equiv_reg3 (heq : Ass2PubEquiv cfg s₁ s₂) (f : UInt64 → UInt64 → UInt64 → UInt64)
    (rd ra rb rc : Reg) (c : UInt64) :
    Ass2PubEquiv (cfg.setReg rd (cfg.regPub ra && cfg.regPub rb && cfg.regPub rc))
      ((s₁.setReg rd (f (s₁.rget ra) (s₁.rget rb) (s₁.rget rc))).retire c)
      ((s₂.setReg rd (f (s₂.rget ra) (s₂.rget rb) (s₂.rget rc))).retire c) :=
  equiv_setReg heq rd c fun h => by
    obtain ⟨hab, hc⟩ := band_split h
    obtain ⟨ha, hb⟩ := band_split hab
    rw [heq.regs ra ha, heq.regs rb hb, heq.regs rc hc]

/-- **One instruction.** Equivalent states executing the same instruction under its side
    conditions access the same data address and end equivalent under the transferred labels.
    Operands of the data path may be secret. -/
theorem exec_noninterference (heq : Ass2PubEquiv cfg s₁ s₂) (i : Ass2Insn)
    (hok : ditOk cfg i = true) :
    effAddr i s₁ = effAddr i s₂ ∧
    Ass2PubEquiv (ditPost cfg i s₁) (execAss2 i s₁) (execAss2 i s₂) := by
  have pc4 : s₁.pc + 4 = s₂.pc + 4 := congrArg (fun x => x + 4) heq.pc
  cases i
  case exc =>
    refine ⟨rfl, ?_⟩
    exact equiv_ite_same (by rw [heq.excEn])
      (fun _ => ⟨heq.evec, heq.evec, pc4, rfl, rfl, heq.halted, heq.instret,
        congrArg (fun x => x + 1) heq.cycles, heq.dbgOut, heq.dbgIn, heq.regs, heq.spg, heq.mem⟩)
      (fun _ => equiv_retireTo heq 1 pc4)
  case eret =>
    exact ⟨rfl, congrArg (fun x => x &&& ~~~3) heq.epc, heq.evec, heq.epc, heq.ecause, rfl,
      heq.halted, congrArg (fun x => x + 1) heq.instret, congrArg (fun x => x + 1) heq.cycles,
      heq.dbgOut, heq.dbgIn, heq.regs, heq.spg, heq.mem⟩
  case csrr rd a =>
    refine ⟨rfl, ?_⟩
    show Ass2PubEquiv
      (match csrReadAddr s₁.dbgIn a.toNat with
        | some _ => cfg.setReg rd true
        | none => cfg)
      (match csrReadAddr s₁.dbgIn a.toNat with
        | some c => ((afterCsrRead s₁ c).setReg rd (csrGet s₁ c)).retire 1
        | none => s₁.trap 1)
      (match csrReadAddr s₂.dbgIn a.toNat with
        | some c => ((afterCsrRead s₂ c).setReg rd (csrGet s₂ c)).retire 1
        | none => s₂.trap 1)
    rw [← heq.dbgIn]
    cases csrReadAddr s₁.dbgIn a.toNat with
    | none => exact equiv_trap heq 1
    | some c =>
      have post : Ass2PubEquiv cfg (afterCsrRead s₁ c) (afterCsrRead s₂ c) := by
        refine ⟨heq.pc, heq.evec, heq.epc, heq.ecause, heq.excEn, heq.halted, heq.instret,
          heq.cycles, heq.dbgOut, ?_, heq.regs, heq.spg, heq.mem⟩
        show (match c with | .dbgIn => s₁.dbgIn.map List.tail | _ => s₁.dbgIn) = _
        rw [heq.dbgIn]
        rfl
      exact equiv_setReg post rd 1 (fun _ => csrGet_equiv heq c)
  case csrw ra a =>
    have hra : s₁.rget ra = s₂.rget ra := heq.regs ra hok
    refine ⟨rfl, ?_⟩
    show Ass2PubEquiv cfg
      (match csrWOf a.toNat with
        | some c => csrApply s₁ c (s₁.rget ra)
        | none => s₁.trap 1)
      (match csrWOf a.toNat with
        | some c => csrApply s₂ c (s₂.rget ra)
        | none => s₂.trap 1)
    rw [hra]
    cases csrWOf a.toNat
    · exact equiv_trap heq 1
    · exact csrApply_equiv heq _ _
  case zeroize =>
    exact ⟨rfl, equiv_update heq 1 pc4 (fun _ _ => rfl) (fun _ _ => rfl) heq.mem⟩
  case halt =>
    exact ⟨rfl, pc4, heq.evec, heq.epc, heq.ecause, heq.excEn, rfl,
      congrArg (fun x => x + 1) heq.instret, congrArg (fun x => x + 1) heq.cycles, heq.dbgOut, heq.dbgIn,
      heq.regs, heq.spg, heq.mem⟩
  case nop => exact ⟨rfl, equiv_retireTo heq 1 pc4⟩
  case lut4 m rd ra rb => exact ⟨rfl, equiv_reg2 heq (lut4Eval m) rd ra rb _⟩
  case alu op rd ra rb => exact ⟨rfl, equiv_reg2 heq (aluEval op) rd ra rb _⟩
  case alui op rd ra imm => exact ⟨rfl, equiv_reg1 heq (fun a => aluiEval op a imm) rd ra _⟩
  case movz20 rd imm => exact ⟨rfl, equiv_setReg heq rd _ (fun _ => rfl)⟩
  case movs20 rd imm => exact ⟨rfl, equiv_setReg heq rd _ (fun _ => rfl)⟩
  case auipc rd imm =>
    exact ⟨rfl, equiv_setReg heq rd _
      (fun _ => congrArg (fun x => x + (sext imm <<< (2 : UInt64))) heq.pc)⟩
  case cmp flags rd ra rb => exact ⟨rfl, equiv_reg2 heq (cmpEval flags) rd ra rb _⟩
  case sel rd ra rb rc =>
    exact ⟨rfl, equiv_reg3 heq (fun a b c => if c = 0 then a else b) rd ra rb rc _⟩
  case bextu rd ra idx len =>
    exact ⟨rfl, equiv_reg1 heq (fun a => bextuEval a idx.val len.val) rd ra _⟩
  case bexts rd ra idx len =>
    exact ⟨rfl, equiv_reg1 heq (fun a => bextsEval a idx.val len.val) rd ra _⟩
  case bswap64 rd ra => exact ⟨rfl, equiv_reg1 heq bswap64Eval rd ra _⟩
  case ld64 rd ra off =>
    have hra : s₁.rget ra = s₂.rget ra := heq.regs ra hok
    refine ⟨congrArg (fun x => some (x + (sext off <<< (3 : UInt64)))) hra, ?_⟩
    exact equiv_ite (by rw [hra])
      (fun _ => equiv_setReg heq rd _ (fun h => by
        rw [← hra]
        exact read64_congr (fun k hk => heq.mem _ (allBelow_spec h k hk))))
      (fun _ => equiv_trap heq 4)
  case ldbu rd ra off =>
    have hra : s₁.rget ra = s₂.rget ra := heq.regs ra hok
    refine ⟨congrArg (fun x => some (x + sext off)) hra, ?_⟩
    exact equiv_setReg heq rd _ (fun h => by
      rw [← hra]
      exact congrArg UInt8.toUInt64 (heq.mem _ h))
  case st64 rv ra off =>
    have hra : s₁.rget ra = s₂.rget ra := heq.regs ra hok
    refine ⟨congrArg (fun x => some (x + (sext off <<< (3 : UInt64)))) hra, ?_⟩
    exact equiv_ite (by rw [hra])
      (fun _ => equiv_setMem heq _ (by
        rw [← hra]
        exact write64_pub (heq.regs rv) heq.mem))
      (fun _ => equiv_trap heq 4)
  case stb rv ra off =>
    have hra : s₁.rget ra = s₂.rget ra := heq.regs ra hok
    refine ⟨congrArg (fun x => some (x + sext off)) hra, ?_⟩
    exact equiv_setMem heq _ (by
      rw [← hra]
      exact store8_pub (heq.regs rv) heq.mem)
  case br op rc off =>
    have hrc : s₁.rget rc = s₂.rget rc := heq.regs rc hok
    refine ⟨rfl, equiv_retireTo heq 1 ?_⟩
    rw [hrc, heq.pc]
  case jal rd off =>
    exact ⟨rfl, equiv_setRegTo heq rd _
      (congrArg (fun x => x + 4 + (sext off <<< (2 : UInt64))) heq.pc) (fun _ => pc4)⟩
  case jalr rd ra off =>
    have hra : s₁.rget ra = s₂.rget ra := heq.regs ra hok
    refine ⟨rfl, ?_⟩
    exact equiv_ite (by rw [hra])
      (fun _ => equiv_setRegTo heq rd _ (by rw [hra]) (fun _ => pc4))
      (fun _ => equiv_trap heq 3)
  case sget rd k => exact ⟨rfl, equiv_setReg heq rd _ (lane_eq heq k.toNat)⟩
  case sput k ra => exact ⟨rfl, equiv_setSpg heq _ (setLane_pub (heq.regs ra) heq.spg)⟩
  case sxor k ra =>
    exact ⟨rfl, equiv_setSpg heq _ (setLane_pub (fun h => by
      obtain ⟨h1, h2⟩ := band_split h
      rw [lane_eq heq _ h1, heq.regs ra h2]) heq.spg)⟩
  case szero => exact ⟨rfl, equiv_setSpg heq _ (fun _ _ => rfl)⟩
  case sld64 k ra off =>
    have hra : s₁.rget ra = s₂.rget ra := heq.regs ra hok
    refine ⟨congrArg (fun x => some (x + (sext off <<< (3 : UInt64)))) hra, ?_⟩
    exact equiv_ite (by rw [hra])
      (fun _ => equiv_setSpg heq _ (setLane_pub (fun h => by
        rw [← hra]
        exact read64_congr (fun k hk => heq.mem _ (allBelow_spec h k hk))) heq.spg))
      (fun _ => equiv_trap heq 4)
  case sst64 k ra off =>
    have hra : s₁.rget ra = s₂.rget ra := heq.regs ra hok
    refine ⟨congrArg (fun x => some (x + (sext off <<< (3 : UInt64)))) hra, ?_⟩
    exact equiv_ite (by rw [hra])
      (fun _ => equiv_setMem heq _ (by
        rw [← hra]
        exact write64_pub (lane_eq heq k.toNat) heq.mem))
      (fun _ => equiv_trap heq 4)
  case glMac rd ra rb rc => exact ⟨rfl, equiv_reg3 heq glMac rd ra rb rc _⟩
  case glAdd rd ra rb => exact ⟨rfl, equiv_reg2 heq glAdd rd ra rb _⟩
  case glSub rd ra rb => exact ⟨rfl, equiv_reg2 heq glSub rd ra rb _⟩
  case glSbox7 rd ra => exact ⟨rfl, equiv_reg1 heq glSbox7 rd ra _⟩
  case fp5Mul ed ea eb =>
    exact ⟨rfl, equiv_setSpg heq _ (fp5Write_pub (fun h => by
      obtain ⟨h1, h2⟩ := band_split h
      rw [fp5Read_pub heq h1, fp5Read_pub heq h2]) heq.spg)⟩
  case fp5Add ed ea eb =>
    exact ⟨rfl, equiv_setSpg heq _ (fp5Write_pub (fun h => by
      obtain ⟨h1, h2⟩ := band_split h
      rw [fp5Read_pub heq h1, fp5Read_pub heq h2]) heq.spg)⟩
  case fp5Sub ed ea eb =>
    exact ⟨rfl, equiv_setSpg heq _ (fp5Write_pub (fun h => by
      obtain ⟨h1, h2⟩ := band_split h
      rw [fp5Read_pub heq h1, fp5Read_pub heq h2]) heq.spg)⟩
  case gf128Mul pd pa pb =>
    exact ⟨rfl, equiv_setSpg heq _ (gfWrite_pub (fun h => by
      obtain ⟨h1, h2⟩ := band_split h
      rw [gfRead_pub heq h1, gfRead_pub heq h2]) heq.spg)⟩
  case gf128Xor pd pa pb =>
    exact ⟨rfl, equiv_setSpg heq _ (gfWrite_pub (fun h => by
      obtain ⟨h1, h2⟩ := band_split h
      rw [gfRead_pub heq h1, gfRead_pub heq h2]) heq.spg)⟩
  case keccak rounds =>
    exact ⟨rfl, equiv_setSpg heq _ (fun j h => by
      rw [kRead_congr (fun k hk => lane_eq heq k (allBelow_spec h k hk))])⟩
  case poseidon2Gl24 =>
    exact ⟨rfl, equiv_setSpg heq _
      (prefix_pub 24 (p24Lane (Poseidon2Gl24.poseidon2Gl24Perm (p24Read s₁.spg)))
        (p24Lane (Poseidon2Gl24.poseidon2Gl24Perm (p24Read s₂.spg)))
        (fun h => by rw [p24Read_congr (fun k hk => lane_eq heq k (allBelow_spec h k hk))])
        heq.spg)⟩
  case poseidon2Gl12 =>
    exact ⟨rfl, equiv_setSpg heq _
      (prefix_pub 12 (p12Lane (poseidon2Perm12 (p12Read s₁.spg)))
        (p12Lane (poseidon2Perm12 (p12Read s₂.spg)))
        (fun h => by rw [p12Read_congr (fun k hk => lane_eq heq k (allBelow_spec h k hk))])
        heq.spg)⟩

end Exec

