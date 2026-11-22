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

/-! ## 5. One step and a run -/

/-- What one step shows the adversary: the `PC` it starts at, the data address it accesses, and
    the two counters. -/
structure Ass2Obs where
  pc : UInt64
  addr : Option UInt64
  cycles : UInt64
  instret : UInt64
  deriving DecidableEq, Repr

/-- The data address of the next step. -/
def stepAddr (s : Ass2State) : Option UInt64 :=
  match currentInsn s with
  | some i => effAddr i s
  | none => none

/-- The observation of the next step. -/
def obsAss2 (s : Ass2State) : Ass2Obs := ⟨s.pc, stepAddr s, s.cycles, s.instret⟩

/-- The labels after the next step. -/
def ditStepCfg (cfg : PubCfg) (s : Ass2State) : PubCfg :=
  match currentInsn s with
  | some i => ditPost cfg i s
  | none => cfg

/-- The next step is safe: the four code bytes at `PC` are public and the instruction, if one
    executes, meets its side conditions. -/
@[expose] def DitSafeStep (cfg : PubCfg) (s : Ass2State) : Prop :=
  (s.halted = false → s.pc.toNat % 4 = 0 → memPub cfg.mem s.pc 4 = true) ∧
  (∀ i, currentInsn s = some i → ditOk cfg i = true)

/-- The observations of `n` steps. -/
@[expose] def traceAss2 : Nat → Ass2State → List Ass2Obs
  | 0, _ => []
  | n + 1, s => obsAss2 s :: traceAss2 n (stepAss2 s)

/-- The labels after `n` steps. -/
@[expose] def cfgRun : Nat → PubCfg → Ass2State → PubCfg
  | 0, cfg, _ => cfg
  | n + 1, cfg, s => cfgRun n (ditStepCfg cfg s) (stepAss2 s)

/-- Each of the next `n` steps is safe under the labels transferred up to it. -/
@[expose] def DitSafeRun : Nat → PubCfg → Ass2State → Prop
  | 0, _, _ => True
  | n + 1, cfg, s => DitSafeStep cfg s ∧ DitSafeRun n (ditStepCfg cfg s) (stepAss2 s)

theorem currentInsn_equiv {cfg : PubCfg} {s₁ s₂ : Ass2State} (heq : Ass2PubEquiv cfg s₁ s₂)
    (hcode : s₁.halted = false → s₁.pc.toNat % 4 = 0 → memPub cfg.mem s₁.pc 4 = true) :
    currentInsn s₁ = currentInsn s₂ := by
  rw [currentInsn_eq, currentInsn_eq, ← heq.halted, ← heq.pc]
  by_cases hh : s₁.halted = true
  · rw [ite_eq_left hh, ite_eq_left hh]
  · rw [ite_eq_right hh, ite_eq_right hh]
    by_cases hpc : s₁.pc.toNat % 4 = 0
    · have hb : s₁.halted = false := by
        cases hx : s₁.halted with
        | false => rfl
        | true => exact absurd hx hh
      rw [ite_eq_left hpc, ite_eq_left hpc,
        fetch32_congr (fun k hk => heq.mem _ (allBelow_spec (hcode hb hpc) k hk))]
    · rw [ite_eq_right hpc, ite_eq_right hpc]

/-- **Step noninterference.** Two states that agree on everything public take a safe step to
    the same `PC`, the same data address, the same `CYCLES` and the same `INSTRET`, and agree on
    everything the transferred labels mark public. -/
theorem ass2_dit_step_noninterference (cfg : PubCfg) (s₁ s₂ : Ass2State)
    (heq : Ass2PubEquiv cfg s₁ s₂) (hsafe : DitSafeStep cfg s₁) :
    (stepAss2 s₁).pc = (stepAss2 s₂).pc ∧ stepAddr s₁ = stepAddr s₂ ∧
    (stepAss2 s₁).cycles = (stepAss2 s₂).cycles ∧
    (stepAss2 s₁).instret = (stepAss2 s₂).instret ∧
    Ass2PubEquiv (ditStepCfg cfg s₁) (stepAss2 s₁) (stepAss2 s₂) := by
  have hcur := currentInsn_equiv heq hsafe.1
  have key : stepAddr s₁ = stepAddr s₂ ∧
      Ass2PubEquiv (ditStepCfg cfg s₁) (stepAss2 s₁) (stepAss2 s₂) := by
    cases hc : currentInsn s₁ with
    | none =>
      have hc₂ : currentInsn s₂ = none := by rw [← hcur]; exact hc
      rw [stepAss2_of_currentInsn_none hc, stepAss2_of_currentInsn_none hc₂]
      unfold stepAddr ditStepCfg
      rw [hc, hc₂]
      refine ⟨rfl, ?_⟩
      exact equiv_ite_same (by rw [heq.halted]) (fun _ => heq)
        (fun _ => by rw [heq.pc]; exact equiv_trap heq _)
    | some i =>
      have hc₂ : currentInsn s₂ = some i := by rw [← hcur]; exact hc
      rw [stepAss2_of_currentInsn_some hc, stepAss2_of_currentInsn_some hc₂]
      unfold stepAddr ditStepCfg
      rw [hc, hc₂]
      exact exec_noninterference heq i (hsafe.2 i hc)
  exact ⟨key.2.pc, key.1, key.2.cycles, key.2.instret, key.2⟩

/-- **Trace noninterference.** Two states that agree on everything public produce, over a safe
    run of `n` steps, the same sequence of `PC`s, data addresses, `CYCLES` and `INSTRET`, and end
    agreeing on everything the transferred labels mark public. Safety is assumed of the first run
    only. -/
theorem ass2_dit_run_trace_noninterference (n : Nat) :
    ∀ (cfg : PubCfg) (s₁ s₂ : Ass2State), Ass2PubEquiv cfg s₁ s₂ → DitSafeRun n cfg s₁ →
      traceAss2 n s₁ = traceAss2 n s₂ ∧
      Ass2PubEquiv (cfgRun n cfg s₁) (runAss2 n s₁) (runAss2 n s₂) := by
  induction n with
  | zero => intro cfg s₁ s₂ heq _; exact ⟨rfl, heq⟩
  | succ n ih =>
    intro cfg s₁ s₂ heq hsafe
    obtain ⟨hstep, hrest⟩ := hsafe
    obtain ⟨_, haddr, _, _, heq'⟩ := ass2_dit_step_noninterference cfg s₁ s₂ heq hstep
    obtain ⟨htr, hfin⟩ := ih _ _ _ heq' hrest
    refine ⟨?_, hfin⟩
    have hobs : obsAss2 s₁ = obsAss2 s₂ := by
      show (⟨s₁.pc, stepAddr s₁, s₁.cycles, s₁.instret⟩ : Ass2Obs) =
        ⟨s₂.pc, stepAddr s₂, s₂.cycles, s₂.instret⟩
      rw [heq.pc, haddr, heq.cycles, heq.instret]
    show obsAss2 s₁ :: traceAss2 n (stepAss2 s₁) = obsAss2 s₂ :: traceAss2 n (stepAss2 s₂)
    rw [htr, hobs]

/-- A finite RAM exposes an attempted data address only after a successful fetch. -/
abbrev obsInRam (size : Nat) (s : Ass2State) : Ass2Obs :=
  ⟨s.pc, if fetchFault size s then none else stepAddr s, s.cycles, s.instret⟩

/-- A memory fault preserves the labels of every data byte, lane and register. -/
abbrev cfgInRam (size : Nat) (cfg : PubCfg) (s : Ass2State) : PubCfg :=
  if ramFault size s then cfg else ditStepCfg cfg s

/-- Successful fetches obey the usual code and operand label conditions. Out-of-range
    fetches have a public outcome before the contents of any RAM byte can matter. -/
abbrev safeInRam (size : Nat) (cfg : PubCfg) (s : Ass2State) : Prop :=
  fetchFault size s = false → DitSafeStep cfg s

theorem stepInRam_noninterference (size : Nat) (cfg : PubCfg) (s₁ s₂ : Ass2State)
    (heq : Ass2PubEquiv cfg s₁ s₂) (hs : safeInRam size cfg s₁) :
    obsInRam size s₁ = obsInRam size s₂ ∧
    Ass2PubEquiv (cfgInRam size cfg s₁) (stepAss2InRam size s₁) (stepAss2InRam size s₂) := by
  have hf : fetchFault size s₁ = fetchFault size s₂ := by
    simp only [fetchFault, heq.halted, heq.pc]
  cases h : fetchFault size s₁ with
  | true =>
    have h₂ := hf.symm.trans h
    simp only [obsInRam, h, h₂, ↓reduceIte, heq.pc, heq.cycles, heq.instret,
      stepAss2InRam_eq, cfgInRam, ramFault, Bool.true_or]
    exact ⟨trivial, equiv_trap heq 5⟩
  | false =>
    have h₂ := hf.symm.trans h
    have safe := hs h
    have hc := currentInsn_equiv heq safe.1
    obtain ⟨_, ha, _, _, post⟩ := ass2_dit_step_noninterference cfg s₁ s₂ heq safe
    have hr : ramFault size s₁ = ramFault size s₂ := by
      unfold ramFault
      rw [hf, ← hc]
      cases hi : currentInsn s₁ with
      | none => rfl
      | some i =>
        have hi₂ := hc.symm.trans hi
        unfold stepAddr at ha
        rw [hi, hi₂] at ha
        change effAddr i s₁ = effAddr i s₂ at ha
        simp only [ha]
    constructor
    · simp only [obsInRam, h, h₂, Bool.false_eq_true, ↓reduceIte, heq.pc, ha, heq.cycles, heq.instret]
    · rw [stepAss2InRam_eq, stepAss2InRam_eq]
      unfold cfgInRam
      rw [← hr]
      split
      · exact equiv_trap heq 5
      · exact post

/-- Predict labels and require safety along the first bounded-RAM execution only. -/
def DitSafeRamRun (size : Nat) : Nat → PubCfg → Ass2State → Prop
  | 0, _, _ => True
  | n + 1, cfg, s => safeInRam size cfg s ∧
      DitSafeRamRun size n (cfgInRam size cfg s) (stepAss2InRam size s)

/-- Observation trace over the same bounded-RAM steps used by the lockstep checker. -/
def traceInRam (size : Nat) : Nat → Ass2State → List Ass2Obs
  | 0, _ => []
  | n + 1, s => obsInRam size s :: traceInRam size n (stepAss2InRam size s)

theorem traceInRam_noninterference (size n : Nat) (cfg : PubCfg) (s₁ s₂ : Ass2State)
    (heq : Ass2PubEquiv cfg s₁ s₂) (hs : DitSafeRamRun size n cfg s₁) :
    traceInRam size n s₁ = traceInRam size n s₂ := by
  induction n generalizing cfg s₁ s₂ with
  | zero => rfl
  | succ n ih =>
    obtain ⟨obs, post⟩ := stepInRam_noninterference size cfg s₁ s₂ heq hs.1
    simp only [traceInRam, obs, ih _ _ _ post hs.2]

/-! ## 6. The `DitHardwareContract` of the ISA -/

theorem memPub_four (lab : UInt64 → Bool) (a : UInt64) :
    memPub lab a 4 = (lab (a + 3) && (lab (a + 2) && (lab (a + 1) && (lab (a + 0) && true)))) := by
  simp only [memPub, allBelow]
  rfl

/-- The state with the public part of `pub` and the secret registers, lanes and bytes of `d`. -/
def injectSecrets (cfg : PubCfg) (pub d : Ass2State) : Ass2State :=
  { pub with regs := fun r => if cfg.regPub r then pub.regs r else d.regs r,
             spg := fun k => if cfg.lane k then pub.spg k else d.spg k,
             mem := fun a => if cfg.mem a then pub.mem a else d.mem a }

theorem injectSecrets_secret_reg (cfg : PubCfg) (pub d : Ass2State) (r : Reg)
    (h : cfg.regPub r = false) : (injectSecrets cfg pub d).rget r = d.rget r := by
  unfold injectSecrets Ass2State.rget
  simp only [h, Bool.false_eq_true, ↓reduceIte]

theorem injectSecrets_equiv (cfg : PubCfg) (pub d₁ d₂ : Ass2State) :
    Ass2PubEquiv cfg (injectSecrets cfg pub d₁) (injectSecrets cfg pub d₂) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun r hr => ?_, fun k hk => ?_,
    fun a ha => ?_⟩
  · show (if r = 0 then (0 : UInt64)
        else (if cfg.regPub r = true then pub.regs r else d₁.regs r)) =
      (if r = 0 then (0 : UInt64) else (if cfg.regPub r = true then pub.regs r else d₂.regs r))
    rw [ite_eq_left hr, ite_eq_left hr]
  · show (if cfg.lane k = true then pub.spg k else d₁.spg k) =
      (if cfg.lane k = true then pub.spg k else d₂.spg k)
    rw [ite_eq_left hk, ite_eq_left hk]
  · show (if cfg.mem a = true then pub.mem a else d₁.mem a) =
      (if cfg.mem a = true then pub.mem a else d₂.mem a)
    rw [ite_eq_left ha, ite_eq_left ha]

/-- An enclave entry: a public initial state, the labels of its secrets, a step count, and
    safety of the run for every value of the secrets. -/
structure Ass2CtEntry where
  cfg : PubCfg
  steps : Nat
  pub : Ass2State
  safe : ∀ d : Ass2State, DitSafeRun steps cfg (injectSecrets cfg pub d)

/-- The leakage of an entry on secrets `d`: the observation trace of its run. The execution mode
    does not enter: the `DIT` control register is hardwired to `1` and no instruction has an
    operand-dependent latency. -/
def ass2Leakage (_mode : Spec.ExecMode) (e : Ass2CtEntry) (d : Ass2State) : List Ass2Obs :=
  traceAss2 e.steps (injectSecrets e.cfg e.pub d)

/-- The leakage of a safe entry does not depend on its secrets. -/
def ass2DitContract : Spec.DitHardwareContract Ass2CtEntry Ass2State (List Ass2Obs) where
  observe := ass2Leakage
  dataIndependent e d₁ d₂ :=
    (ass2_dit_run_trace_noninterference e.steps e.cfg _ _
      (injectSecrets_equiv e.cfg e.pub d₁ d₂) (e.safe d₁)).1

/-- The contract's observation is the trace of the run from the injected state. -/
theorem ass2DitContract_observe (mode : Spec.ExecMode) (e : Ass2CtEntry) (d : Ass2State) :
    ass2DitContract.observe mode e d = traceAss2 e.steps (injectSecrets e.cfg e.pub d) := by
  rfl

/-! ## 7. Straight-line programs are safe -/

/-- The `4 * n` code bytes from `a` are public. -/
@[expose] def CodePub (lab : UInt64 → Bool) : UInt64 → Nat → Prop
  | _, 0 => True
  | a, n + 1 => memPub lab a 4 = true ∧ CodePub lab (a + 4) n

theorem ditOk_straight (cfg : PubCfg) {i : Ass2Insn} (h : i.isStraight = true) :
    ditOk cfg i = true := by
  cases i <;> first | rfl | exact absurd h Bool.false_ne_true

theorem ditPost_mem_straight (cfg : PubCfg) {i : Ass2Insn} (h : i.isStraight = true)
    (s : Ass2State) : (ditPost cfg i s).mem = cfg.mem := by
  cases i <;> first | rfl | exact absurd h Bool.false_ne_true

/-- A loaded program of well-formed straight instructions with public code is safe from every
    state: no condition is placed on the registers or lanes. -/
theorem ditSafeRun_straight (prog : List Ass2Insn) :
    ∀ (cfg : PubCfg) (s : Ass2State), s.halted = false → s.pc.toNat % 4 = 0 →
      LoadedAt s.mem s.pc prog → CodePub cfg.mem s.pc prog.length →
      (∀ i, i ∈ prog → i.WellFormed ∧ i.isStraight = true) →
      DitSafeRun prog.length cfg s := by
  induction prog with
  | nil => intro _ _ _ _ _ _ _; exact True.intro
  | cons i rest ih =>
    intro cfg s hh hpc hl hcode hs
    obtain ⟨hwf, hst⟩ := hs i (List.mem_cons_self ..)
    obtain ⟨hf, hrest⟩ := hl
    obtain ⟨hc4, hcrest⟩ := hcode
    have hcur : currentInsn s = some i :=
      currentInsn_of_fetch hh hpc (by rw [hf]; exact decodeAss2_encodeAss2 i hwf)
    obtain ⟨epc, emem, ehalt⟩ := execAss2_straight hst s
    have hstep : stepAss2 s = execAss2 i s := stepAss2_of_currentInsn_some hcur
    have hcfg : ditStepCfg cfg s = ditPost cfg i s := by unfold ditStepCfg; rw [hcur]
    show DitSafeStep cfg s ∧ DitSafeRun rest.length (ditStepCfg cfg s) (stepAss2 s)
    refine ⟨⟨fun _ _ => hc4, fun j hj => ?_⟩, ?_⟩
    · rw [hcur] at hj
      cases hj
      exact ditOk_straight cfg hst
    · rw [hstep, hcfg]
      exact ih _ _ (by rw [ehalt]; exact hh) (by rw [epc]; exact aligned_add4 _ hpc)
        (by rw [epc, emem]; exact hrest)
        (by rw [ditPost_mem_straight cfg hst, epc]; exact hcrest)
        (fun j hj => hs j (List.mem_cons_of_mem _ hj))

/-! ## 8. Verified enclave microcode: `zk-Hem v2` Horner step and `TurboSHAKE256` leaf block

Register roles: `E0 = x`, `E1 = c2` (and the result), `E2 = c1`, `E3 = c0`; `R4 = left`,
`R5 = right`, `R6 = direction bit` of the Merkle path; `R7 .. R14` are scratch. -/

/-- `E1 := (E1 * E0 + E2) * E0 + E3`. -/
@[expose] def zkhemHornerProg : List Ass2Insn :=
  [.fp5Mul 1 1 0, .fp5Add 1 1 2, .fp5Mul 1 1 0, .fp5Add 1 1 3]

/-- Order `(left, right)` by the direction bit without branching, move `E1` out of the bank,
    load the 56-byte message `first ‖ second ‖ E1` with the `TurboSHAKE256` domain byte `0x1F`
    and the final rate bit, and permute. -/
@[expose] def zkhemHashProg : List Ass2Insn :=
  [.sel 7 4 5 6, .sel 8 5 4 6,
   .sget 9 5, .sget 10 6, .sget 11 7, .sget 12 8, .sget 13 9,
   .szero,
   .sput 0 7, .sput 1 8, .sput 2 9, .sput 3 10, .sput 4 11, .sput 5 12, .sput 6 13,
   .movz20 14 0x1F, .sxor 7 14,
   .movz20 14 0x80, .alui .shli 14 14 56, .sxor 16 14,
   .keccak 12]

/-- The kernel: Horner evaluation, then the leaf block. -/
@[expose] def zkhemLeafProg : List Ass2Insn := zkhemHornerProg ++ zkhemHashProg

/-- The kernel as 25 instruction words. -/
@[expose] def zkhemLeafWords : List UInt32 :=
  [0xD0040011, 0xD0050211, 0xD0040011, 0xD0050311,
   0x60006547, 0x60006458,
   0xC0005009, 0xC000600A, 0xC000700B, 0xC000800C, 0xC000900D,
   0xC0000300,
   0xC0000170, 0xC0001180, 0xC0002190, 0xC00031A0, 0xC00041B0, 0xC00051C0, 0xC00061D0,
   0x40001F0E, 0xC00072E0,
   0x4000800E, 0x300385EE, 0xC00102E0,
   0xF0C00000]

/-- The degree-2 Horner value `(c2 * x + c1) * x + c0` of the quintic registers
    `x = E0`, `c2 = E1`, `c1 = E2`, `c0 = E3`. -/
@[expose] def zkhemHorner (σ : Fin 25 → UInt64) : QuinticGoldilocks :=
  QuinticGoldilocks.add
    (QuinticGoldilocks.mul
      (QuinticGoldilocks.add (QuinticGoldilocks.mul (fp5Read σ 1) (fp5Read σ 0)) (fp5Read σ 2))
      (fp5Read σ 0))
    (fp5Read σ 3)

/-- The `TurboSHAKE256` input block of a 56-byte message `m0 ‖ .. ‖ m6` (little-endian lanes)
    with domain byte `0x1F`: the message in lanes `0..6`, the domain byte at byte 56, and bit 7 of
    byte 135, the last byte of the 136-byte rate. -/
abbrev zkhemLeafBlock (m0 m1 m2 m3 m4 m5 m6 : UInt64) : KState :=
  ⟨m0, m1, m2, m3, m4, m5, m6, 0x1F, 0, 0, 0, 0, 0, 0, 0, 0, 0x8000000000000000,
    0, 0, 0, 0, 0, 0, 0, 0⟩

/-- `E1 := E_a * E_b`. -/
private def bankMul (σ : Fin 25 → UInt64) (a b : Nat) : Fin 25 → UInt64 :=
  fp5Write σ 1 (QuinticGoldilocks.mul (fp5Read σ a) (fp5Read σ b))

/-- `E1 := E_a + E_b`. -/
private def bankAdd (σ : Fin 25 → UInt64) (a b : Nat) : Fin 25 → UInt64 :=
  fp5Write σ 1 (QuinticGoldilocks.add (fp5Read σ a) (fp5Read σ b))

private theorem bankMul_same (σ : Fin 25 → UInt64) (a b : Nat) :
    fp5Read (bankMul σ a b) 1 = QuinticGoldilocks.mul (fp5Read σ a) (fp5Read σ b) :=
  fp5Read_fp5Write_same σ (by decide) _

private theorem bankMul_other (σ : Fin 25 → UInt64) (a b e : Nat) (he : e ≠ 1) :
    fp5Read (bankMul σ a b) e = fp5Read σ e :=
  fp5Read_fp5Write_other σ he _

private theorem bankAdd_same (σ : Fin 25 → UInt64) (a b : Nat) :
    fp5Read (bankAdd σ a b) 1 = QuinticGoldilocks.add (fp5Read σ a) (fp5Read σ b) :=
  fp5Read_fp5Write_same σ (by decide) _

private theorem bankAdd_other (σ : Fin 25 → UInt64) (a b e : Nat) (he : e ≠ 1) :
    fp5Read (bankAdd σ a b) e = fp5Read σ e :=
  fp5Read_fp5Write_other σ he _

/-- The bank after the Horner program. -/
private def hornerBank (σ : Fin 25 → UInt64) : Fin 25 → UInt64 :=
  bankAdd (bankMul (bankAdd (bankMul σ 1 0) 1 2) 1 0) 1 3

private theorem hornerBank_eq (σ : Fin 25 → UInt64) :
    hornerBank σ = fp5Write (bankMul (bankAdd (bankMul σ 1 0) 1 2) 1 0) 1 (zkhemHorner σ) := by
  have a1 := bankMul_same σ 1 0
  have a1_0 := bankMul_other σ 1 0 0 (by decide)
  have a1_2 := bankMul_other σ 1 0 2 (by decide)
  have a1_3 := bankMul_other σ 1 0 3 (by decide)
  have a2 := bankAdd_same (bankMul σ 1 0) 1 2
  have a2_0 := bankAdd_other (bankMul σ 1 0) 1 2 0 (by decide)
  have a2_3 := bankAdd_other (bankMul σ 1 0) 1 2 3 (by decide)
  have a3 := bankMul_same (bankAdd (bankMul σ 1 0) 1 2) 1 0
  have a3_3 := bankMul_other (bankAdd (bankMul σ 1 0) 1 2) 1 0 3 (by decide)
  rw [a1, a1_2] at a2
  rw [a2, a2_0, a1_0] at a3
  rw [a2_3, a1_3] at a3_3
  show fp5Write (bankMul (bankAdd (bankMul σ 1 0) 1 2) 1 0) 1
      (QuinticGoldilocks.add (fp5Read (bankMul (bankAdd (bankMul σ 1 0) 1 2) 1 0) 1)
        (fp5Read (bankMul (bankAdd (bankMul σ 1 0) 1 2) 1 0) 3)) = _
  rw [a3, a3_3]
  rfl

/-- The Horner program leaves `zkhemHorner` in `E1` and the registers unchanged. -/
theorem zkhemHorner_exec (s : Ass2State) :
    fp5Read (zkhemHornerProg.foldl (fun t i => execAss2 i t) s).spg 1 = zkhemHorner s.spg ∧
    (zkhemHornerProg.foldl (fun t i => execAss2 i t) s).regs = s.regs := by
  refine ⟨?_, rfl⟩
  show fp5Read (hornerBank s.spg) 1 = zkhemHorner s.spg
  rw [hornerBank_eq]
  exact fp5Read_fp5Write_same _ (by decide) _

private theorem hornerBank_lanes (σ : Fin 25 → UInt64) :
    lane (hornerBank σ) 5 = glTo (zkhemHorner σ).c0 ∧
    lane (hornerBank σ) 6 = glTo (zkhemHorner σ).c1 ∧
    lane (hornerBank σ) 7 = glTo (zkhemHorner σ).c2 ∧
    lane (hornerBank σ) 8 = glTo (zkhemHorner σ).c3 ∧
    lane (hornerBank σ) 9 = glTo (zkhemHorner σ).c4 := by
  rw [hornerBank_eq]
  have hl := fp5Limb_eq (zkhemHorner σ)
  exact ⟨(lane_fp5Write_same _ (by decide) _ (by decide : 0 < 5)).trans hl.1,
    (lane_fp5Write_same _ (by decide) _ (by decide : 1 < 5)).trans hl.2.1,
    (lane_fp5Write_same _ (by decide) _ (by decide : 2 < 5)).trans hl.2.2.1,
    (lane_fp5Write_same _ (by decide) _ (by decide : 3 < 5)).trans hl.2.2.2.1,
    (lane_fp5Write_same _ (by decide) _ (by decide : 4 < 5)).trans hl.2.2.2.2⟩

/-- The hash program leaves in the bank the 12-round permutation of the leaf block built from
    the two ordered children and lanes `5..9`. -/
theorem zkhemHash_exec (t : Ass2State) :
    (zkhemHashProg.foldl (fun u i => execAss2 i u) t).spg =
      kLane (keccakRounds 12
        (zkhemLeafBlock (if t.rget 6 = 0 then t.rget 4 else t.rget 5)
          (if t.rget 6 = 0 then t.rget 5 else t.rget 4)
          (lane t.spg 5) (lane t.spg 6) (lane t.spg 7) (lane t.spg 8) (lane t.spg 9))) := by
  have h7 : (0 : UInt64) ^^^ zext (0x1F : BitVec 20) = 0x1F := by decide
  have h16 : (0 : UInt64) ^^^ aluiEval .shli (zext (0x80 : BitVec 20)) (56 : BitVec 16) =
      0x8000000000000000 := by
    rw [(aluiEval_eq _ _).1]
    decide
  refine congrArg (fun K => kLane (keccakRounds 12 K))
    (kRead_eq_mk _ _ rfl rfl rfl rfl rfl rfl rfl h7 rfl rfl rfl rfl rfl rfl rfl rfl h16
      rfl rfl rfl rfl rfl rfl rfl rfl)

theorem zkhemLeafProg_straight :
    ∀ i, i ∈ zkhemLeafProg → i.WellFormed ∧ i.isStraight = true := by
  decide

/-- **The `zk-Hem v2` Horner and `TurboSHAKE256` leaf kernel.**

    1. `zkhemLeafWords` is the encoding of `zkhemLeafProg`, word for word.
    2. Run for 25 steps from any state it is loaded in, the kernel leaves in the bank the
       12-round `Keccak-f[1600]` permutation of the `TurboSHAKE256` block whose message is the
       two children, ordered by the direction bit `R6`, followed by the five limbs of the Horner
       value `(E1 * E0 + E2) * E0 + E3` in `QuinticGoldilocks`. Memory is unchanged and `PC`
       advances by 100.
    3. If the code is public, two runs from states that agree on everything public produce the
       same `PC`, address, `CYCLES` and `INSTRET` trace. The children, the direction bit and
       every lane may be secret: no register or lane is required to be public. -/
theorem ass2_zkhem_v2_fp5_horner_and_turboshake_leaf_verified :
    zkhemLeafWords = zkhemLeafProg.map encodeAss2 ∧
    (∀ s : Ass2State, s.halted = false → s.pc.toNat % 4 = 0 →
      LoadedAt s.mem s.pc zkhemLeafProg →
      (runAss2 25 s).spg =
        kLane (keccakRounds 12
          (zkhemLeafBlock (if s.rget 6 = 0 then s.rget 4 else s.rget 5)
            (if s.rget 6 = 0 then s.rget 5 else s.rget 4)
            (glTo (zkhemHorner s.spg).c0) (glTo (zkhemHorner s.spg).c1)
            (glTo (zkhemHorner s.spg).c2) (glTo (zkhemHorner s.spg).c3)
            (glTo (zkhemHorner s.spg).c4))) ∧
      (runAss2 25 s).mem = s.mem ∧ (runAss2 25 s).pc = s.pc + 100 ∧
      (runAss2 25 s).halted = false) ∧
    (∀ (cfg : PubCfg) (s₁ s₂ : Ass2State), Ass2PubEquiv cfg s₁ s₂ → s₁.halted = false →
      s₁.pc.toNat % 4 = 0 → LoadedAt s₁.mem s₁.pc zkhemLeafProg → CodePub cfg.mem s₁.pc 25 →
      traceAss2 25 s₁ = traceAss2 25 s₂ ∧
      Ass2PubEquiv (cfgRun 25 cfg s₁) (runAss2 25 s₁) (runAss2 25 s₂)) := by
  refine ⟨by decide, fun s hh hpc hl => ?_, fun cfg s₁ s₂ heq hh hpc hl hcode => ?_⟩
  · have hrun : runAss2 25 s = zkhemLeafProg.foldl (fun t i => execAss2 i t) s :=
      runAss2_straight zkhemLeafProg s hh hpc hl zkhemLeafProg_straight
    obtain ⟨fpc, fmem, fhalt⟩ :=
      foldl_straight_frame zkhemLeafProg s (fun i hi => (zkhemLeafProg_straight i hi).2)
    rw [hrun]
    refine ⟨?_, fmem, fpc, fhalt.trans hh⟩
    have hsplit : zkhemLeafProg.foldl (fun t i => execAss2 i t) s =
        zkhemHashProg.foldl (fun t i => execAss2 i t)
          (zkhemHornerProg.foldl (fun t i => execAss2 i t) s) := List.foldl_append
    rw [hsplit, zkhemHash_exec]
    obtain ⟨l0, l1, l2, l3, l4⟩ := hornerBank_lanes s.spg
    show kLane (keccakRounds 12
        (zkhemLeafBlock (if s.rget 6 = 0 then s.rget 4 else s.rget 5)
          (if s.rget 6 = 0 then s.rget 5 else s.rget 4)
          (lane (hornerBank s.spg) 5) (lane (hornerBank s.spg) 6) (lane (hornerBank s.spg) 7)
          (lane (hornerBank s.spg) 8) (lane (hornerBank s.spg) 9))) = _
    rw [l0, l1, l2, l3, l4]
  · exact ass2_dit_run_trace_noninterference 25 cfg s₁ s₂ heq
      (ditSafeRun_straight zkhemLeafProg cfg s₁ hh hpc hl hcode zkhemLeafProg_straight)

/-- Substituting the secret bytes preserves a program whose instruction bytes are public. -/
theorem loadedAt_injectSecrets (cfg : PubCfg) (pub d : Ass2State) (prog : List Ass2Insn)
    (a : UInt64) (hl : LoadedAt pub.mem a prog) (hc : CodePub cfg.mem a prog.length) :
    LoadedAt (injectSecrets cfg pub d).mem a prog := by
  induction prog generalizing a with
  | nil => trivial
  | cons i rest ih =>
    obtain ⟨hf, ht⟩ := hl
    obtain ⟨hp, hc⟩ := hc
    refine ⟨Eq.trans (fetch32_congr (fun k hk => ?_)) hf, ih _ ht hc⟩
    exact ite_eq_left (allBelow_spec hp k hk)

/-- The 25-word kernel is a hardware-contract entry for arbitrary secret registers, lanes
    and private data bytes. Its caller supplies the loaded public code and the entry PC. -/
def zkhemLeafEntry (cfg : PubCfg) (pub : Ass2State) (hh : pub.halted = false)
    (ha : pub.pc.toNat % 4 = 0) (hl : LoadedAt pub.mem pub.pc zkhemLeafProg)
    (hc : CodePub cfg.mem pub.pc 25) : Ass2CtEntry where
  cfg := cfg
  steps := 25
  pub := pub
  safe d := ditSafeRun_straight zkhemLeafProg cfg (injectSecrets cfg pub d) hh ha
    (loadedAt_injectSecrets cfg pub d zkhemLeafProg pub.pc hl hc) hc zkhemLeafProg_straight

/-- The hardware contract compares the actual kernel traces after secret injection. -/
theorem zkhemLeafEntry_trace (cfg : PubCfg) (pub d₁ d₂ : Ass2State) (hh : pub.halted = false)
    (ha : pub.pc.toNat % 4 = 0) (hl : LoadedAt pub.mem pub.pc zkhemLeafProg)
    (hc : CodePub cfg.mem pub.pc 25) :
    traceAss2 25 (injectSecrets cfg pub d₁) = traceAss2 25 (injectSecrets cfg pub d₂) :=
  ass2DitContract.dataIndependent (zkhemLeafEntry cfg pub hh ha hl hc) d₁ d₂

#verify_constructive
  Qsag.Ass2.loadedAt_injectSecrets
  Qsag.Ass2.zkhemLeafEntry_trace
  Qsag.Ass2.band_split
  Qsag.Ass2.allBelow_spec
  Qsag.Ass2.allBelow_of
  Qsag.Ass2.lane_eq
  Qsag.Ass2.equiv_update
  Qsag.Ass2.regs_setReg
  Qsag.Ass2.equiv_setRegTo
  Qsag.Ass2.equiv_setReg
  Qsag.Ass2.equiv_setSpg
  Qsag.Ass2.equiv_setMem
  Qsag.Ass2.equiv_retireTo
  Qsag.Ass2.equiv_trap
  Qsag.Ass2.equiv_ite
  Qsag.Ass2.equiv_ite_same
  Qsag.Ass2.write64_pub
  Qsag.Ass2.store8_pub
  Qsag.Ass2.setLane_pub
  Qsag.Ass2.fp5Write_pub
  Qsag.Ass2.gfWrite_pub
  Qsag.Ass2.prefix_pub
  Qsag.Ass2.csrGet_equiv
  Qsag.Ass2.csrApply_equiv
  Qsag.Ass2.fp5Read_pub
  Qsag.Ass2.gfRead_pub
  Qsag.Ass2.equiv_reg1
  Qsag.Ass2.equiv_reg2
  Qsag.Ass2.equiv_reg3
  Qsag.Ass2.exec_noninterference
  Qsag.Ass2.currentInsn_equiv
  Qsag.Ass2.ass2_dit_step_noninterference
  Qsag.Ass2.ass2_dit_run_trace_noninterference
  Qsag.Ass2.injectSecrets_equiv
  Qsag.Ass2.ass2DitContract_observe
  Qsag.Ass2.ditOk_straight
  Qsag.Ass2.ditPost_mem_straight
  Qsag.Ass2.ditSafeRun_straight
  Qsag.Ass2.zkhemHorner_exec
  Qsag.Ass2.zkhemHash_exec
  Qsag.Ass2.zkhemLeafProg_straight
  Qsag.Ass2.ass2_zkhem_v2_fp5_horner_and_turboshake_leaf_verified

end Qsag.Ass2
