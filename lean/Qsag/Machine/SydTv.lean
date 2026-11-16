module
public import Qsag.Machine.ElfVerify
public import Qsag.Machine.McRefine
public import Qsag.Machine.ElfParse
import Qsag.Tactic.AssuranceKit
import Qsag.Tactic.Prelude
import Qsag.Machine.ElfVerify
import Qsag.Machine.McRefine
import Qsag.Machine.ElfFixtures
public section

/-!
# `Qsag.Machine.SydTv` — Sewell–Myreen–Klein Cut-Point Translation Validation

Untrusted search / certificate checking over **real byte-decoded `Qsag.Machine.IsaCt` instructions**
(`decodeX86One` / `decodeArm64One`, `stepX86` / `runX86`, `stepArm64` / `runArm64`, `StepObs`)
extracted from the production `qsag_asm` `.rlib` archives (`Qsag.Machine.ElfFixtures` /
`Qsag.Machine.ElfParse`; the symbol bytes and their decode certificates are in
`Qsag.Machine.McRefine`):

1. **Trip counts (`n : BitVec 64`)**:
   - `n ≠ 0`: the theorems `*_sydtv_refines_pos` are about `runX86One` / `runArm64One` on the
     symbol bytes themselves: entry prologue, `n.toNat` trips of the Sewell loop relation
     (`LoopRelationCert`) and exit epilogue, with functional postcondition and equal `StepObs`
     traces for two runs that agree on the public pointers and count.
   - `n = 0`: the symbols are bottom-tested and their Rust wrappers return before calling them
     on empty input (`ct_memzero`, `ct_eq_bytes`, `gf256_shamir_mac_with_backend`,
     `tower128_bdoz_2lane_poly_mac_with_backend` in `crates/qsag-asm/src/lib.rs`). The
     `*GuardedRun` runners add that early return as a hand-written branch; it is a model of the
     wrapper, it is not decoded machine code, and it has not been validated against the compiled
     wrapper. `UnrestrictedLoopCert` and the `*_sydtv_refines_all_n` theorems are statements
     about these guarded runners. `tooth_unguarded_zero_count_wraps_counter` shows what the raw
     memzero symbol does when entered with a zero count.
2. **Real Byte-Decoded ISA Welding (`decodeX86One` & `decodeArm64One`)**:
   Every cut replays as concrete multi-instruction runs of `stepX86` / `stepArm64`
   fetched live from `.rlib` symbol bytes via `decodeX86One` / `decodeArm64One` AND via
   `runX86` / `runArm64` over `decodeX86Stream` / `decodeArm64Stream`.
3. **Five Certified Looping `.rlib` Kernels (Scalar, Multi-Pointer, Accumulator, GFNI & VPCLMUL SIMD)**:
   - `qsag_asm_ct_memzero_x86_64` (`currentX86ExtractedSlices[15]`, 41 B): 1-pointer affine + byte zeroing.
   - `qsag_asm_ct_memzero_aarch64` (`currentAarch64ExtractedSlices[6]`, 20 B): AArch64 post-index affine + byte zeroing.
   - `qsag_asm_ct_eq_bytes_x86_64` (`currentX86ExtractedSlices[14]`, 63 B): 2-pointer affine + OR-of-XOR accumulator.
   - `qsag_asm_gf256_shamir_mac_gfni` (`currentX86ExtractedSlices[3]`, 160 B): 2-pointer 32B stride + GFNI Wiedemann `T₃` SIMD MAC.
   - `qsag_asm_tower128_bdoz_mac_vpclmul` (`currentX86ExtractedSlices[6]`, 204 B): 2-pointer 32B stride + dual-256b Karatsuba carryless XOR accumulators + `0x87` reduction.
   The four `x86_64` symbols end in a scratch-wipe epilogue (`xor` of `rdi`, `rsi`, `rdx`, `rcx`,
   `r8`–`r11`; the SIMD ones also `vzeroall`); the postconditions state the wiped registers.
-/

namespace Qsag.SydTv

open Qsag

set_option autoImplicit false

-- These instances are proved classically; without them `simp` discharges `UInt64` equality
-- tests through the decidable-equality instance instead.
attribute [-instance] UInt64.instLawfulEqOrd UInt64.instLawfulOrderOrd

/-! ## §1. Cut-Point DAG Representation, Symbolic Flattening & Unrestricted Loop Certificates -/


inductive Expr where
  | var : Nat → Expr
  | lit : Word → Expr
  | add : Expr → Expr → Expr
  | sub : Expr → Expr → Expr
  | xor : Expr → Expr → Expr
  | orOp : Expr → Expr → Expr
  deriving DecidableEq, Repr

def Expr.eval : Expr → Env → Word
  | .var r, e => e r
  | .lit w, _ => w
  | .add a b, e => a.eval e + b.eval e
  | .sub a b, e => a.eval e - b.eval e
  | .xor a b, e => a.eval e ^^^ b.eval e
  | .orOp a b, e => a.eval e ||| b.eval e

def put (e : Env) (r : Nat) (w : Word) : Env := fun k => if k = r then w else e k

inductive TvNode (S : Type) where
  | Assign : (S → S) → Nat → TvNode S
  | Cond : (S → Bool) → Nat → Nat → TvNode S
  | CallBlackBox : Nat → Nat → TvNode S
  | Ret : (S → Word) → TvNode S
  | Err : TvNode S

structure TvGraph (S : Type) where
  node : Nat → TvNode S
  entry : Nat
  loopHeads : List Nat
  fuel : Nat

inductive DagResult (S : Type) where
  | ret : Word → S → DagResult S
  | err : DagResult S
  | cut : Nat → S → DagResult S

abbrev Boxes (S : Type) := Nat → S → S

def exprAssign (r : Nat) (x : Expr) (next : Nat) : TvNode Env :=
  .Assign (fun e => put e r (x.eval e)) next

def execFrom {S : Type} (g : TvGraph S) (boxes : Boxes S) : Nat → Nat → S → DagResult S
  | 0, pc, e => .cut pc e
  | n + 1, pc, e =>
    if pc ∈ g.loopHeads then .cut pc e else
    match g.node pc with
    | .Assign f next => execFrom g boxes n next (f e)
    | .Cond p yes no => execFrom g boxes n (if p e then yes else no) e
    | .CallBlackBox b next => execFrom g boxes n next (boxes b e)
    | .Ret x => .ret (x e) e
    | .Err => .err

inductive Flattened (S : Type) where
  | leaf : (S → DagResult S) → Flattened S
  | branch : (S → Bool) → Flattened S → Flattened S → Flattened S

def evalFlattened {S : Type} : Flattened S → S → DagResult S
  | .leaf k, e => k e
  | .branch p yes no, e => if p e then evalFlattened yes e else evalFlattened no e

def flattenFrom {S : Type} (g : TvGraph S) (boxes : Boxes S) :
    Nat → Nat → (S → S) → Flattened S
  | 0, pc, σ => .leaf (fun e => .cut pc (σ e))
  | n + 1, pc, σ =>
    if pc ∈ g.loopHeads then .leaf (fun e => .cut pc (σ e)) else
    match g.node pc with
    | .Assign f next => flattenFrom g boxes n next (fun e => f (σ e))
    | .Cond p yes no => .branch (fun e => p (σ e))
        (flattenFrom g boxes n yes σ) (flattenFrom g boxes n no σ)
    | .CallBlackBox b next => flattenFrom g boxes n next (fun e => boxes b (σ e))
    | .Ret x => .leaf (fun e => .ret (x (σ e)) (σ e))
    | .Err => .leaf (fun _ => .err)

theorem flattenFrom_sound {S : Type} (g : TvGraph S) (boxes : Boxes S) (n pc : Nat)
    (σ : S → S) (e : S) :
    evalFlattened (flattenFrom g boxes n pc σ) e = execFrom g boxes n pc (σ e) := by
  induction n generalizing pc σ with
  | zero => rfl
  | succ n ih =>
    simp only [flattenFrom, execFrom]
    split
    · rfl
    · cases g.node pc <;> simp only [evalFlattened]
      · exact ih _ _
      · split <;> simp_all
      · exact ih _ _

def flattenDag {S : Type} (g : TvGraph S) (boxes : Boxes S) : Flattened S :=
  flattenFrom g boxes g.fuel g.entry id

def execGraphDag {S : Type} (g : TvGraph S) (boxes : Boxes S) : S → DagResult S :=
  execFrom g boxes g.fuel g.entry

theorem flattenDag_sound {S : Type} (g : TvGraph S) (boxes : Boxes S) (env : S) :
    evalFlattened (flattenDag g boxes) env = execGraphDag g boxes env :=
  flattenFrom_sound g boxes g.fuel g.entry id env

/-- Counted sequence of DAG cuts emitting `StepObs` leakage traces. -/
def runCuts {S : Type} (step : S → S × List StepObs) : Nat → S → S × List StepObs
  | 0, s => (s, [])
  | n + 1, s =>
    let t := step s
    let u := runCuts step n t.1
    (u.1, t.2 ++ u.2)

/-- Positive-count Sewell loop-relation certificate with public `StepObs` schedule. -/
structure LoopRelationCert (A M : Type) (bound : Nat)
    (asmStep : A → A × List StepObs) (asmFfiStep : M → M × List StepObs)
    (asmHead : A) (asmFfiInit : M) (Post : A → M → Prop) where
  LoopRel : Nat → A → M → Prop
  schedule : Nat → List StepObs
  entry : LoopRel 0 asmHead asmFfiInit
  body : ∀ v a m, v < bound → LoopRel v a m →
    LoopRel (v + 1) (asmStep a).1 (asmFfiStep m).1 ∧
    (asmStep a).2 = schedule v ∧ (asmFfiStep m).2 = schedule v
  exit : ∀ a m, LoopRel bound a m → Post a m

abbrev LoopRefinementCert := LoopRelationCert

def scheduleTrace (schedule : Nat → List StepObs) : Nat → Nat → List StepObs
  | 0, _ => []
  | n + 1, v => schedule v ++ scheduleTrace schedule n (v + 1)

theorem remaining_sound {A M : Type} {bound : Nat}
    {as : A → A × List StepObs} {ms : M → M × List StepObs}
    {a₀ : A} {m₀ : M} {P : A → M → Prop}
    (c : LoopRelationCert A M bound as ms a₀ m₀ P) (remaining : Nat) :
    ∀ v a m, v + remaining = bound → c.LoopRel v a m →
    P (runCuts as remaining a).1 (runCuts ms remaining m).1 ∧
    (runCuts as remaining a).2 = scheduleTrace c.schedule remaining v ∧
    (runCuts ms remaining m).2 = scheduleTrace c.schedule remaining v := by
  induction remaining with
  | zero =>
    intro v a m hv h
    simp only [Nat.add_zero] at hv
    subst v
    exact ⟨c.exit a m h, rfl, rfl⟩
  | succ n ih =>
    intro v a m hv h
    obtain ⟨hr, ha, hm⟩ := c.body v a m (by omega) h
    obtain ⟨hp, hat, hmt⟩ := ih (v + 1) (as a).1 (ms m).1 (by omega) hr
    exact ⟨hp,
      by simpa [runCuts, scheduleTrace, ha] using congrArg (List.append (c.schedule v)) hat,
      by simpa [runCuts, scheduleTrace, hm] using congrArg (List.append (c.schedule v)) hmt⟩

theorem sewell_loop_relation_refinement_sound {A M : Type} {bound : Nat}
    {as : A → A × List StepObs} {ms : M → M × List StepObs}
    {a : A} {m : M} {P : A → M → Prop}
    (c : LoopRelationCert A M bound as ms a m P) :
    P (runCuts as bound a).1 (runCuts ms bound m).1 ∧
    (runCuts as bound a).2 = scheduleTrace c.schedule bound 0 ∧
    (runCuts ms bound m).2 = scheduleTrace c.schedule bound 0 :=
  remaining_sound c bound 0 a m (by omega) c.entry

theorem three_way_noninterference {A M : Type} {n : Nat}
    {as : A → A × List StepObs} {ms : M → M × List StepObs}
    {a b : A} {m k : M} {P : A → M → Prop}
    (c : LoopRelationCert A M n as ms a m P)
    (d : LoopRelationCert A M n as ms b k P) (h : c.schedule = d.schedule) :
    (runCuts as n a).2 = (runCuts as n b).2 ∧
    (runCuts as n a).2 = (runCuts ms n m).2 := by
  obtain ⟨_, ha, hm⟩ := sewell_loop_relation_refinement_sound c
  obtain ⟨_, hb, _⟩ := sewell_loop_relation_refinement_sound d
  exact ⟨ha.trans ((congrArg (fun s => scheduleTrace s n 0) h).trans hb.symm), ha.trans hm.symm⟩

/-- Full-function Sewell cut-point certificate over an **unrestricted 64-bit trip count**
`n : Word` (`BitVec 64`), unifying:
- `zero_cut`: the `n = 0` zero-trip entry-to-exit cut and its public `zeroSchedule`, and
- `pos_cert` + `pos_replay`: the `n ≠ 0` entry prologue, `n.toNat`-trip `LoopRelationCert`,
  and exit epilogue replayed against the byte-decoded machine semantics. -/
structure UnrestrictedLoopCert (A M : Type) (n : Word)
    (asmExec : A → A × List StepObs) (asmFfiExec : M → M × List StepObs)
    (asmBody : A → A × List StepObs) (asmFfiBody : M → M × List StepObs)
    (asmInit : A) (asmFfiInit : M)
    (asmHead : A) (asmFfiHead : M)
    (LoopPost : A → M → Prop) (Post : A → M → Prop) where
  zeroSchedule : List StepObs
  entrySchedule : List StepObs
  bodySchedule : Nat → List StepObs
  exitSchedule : List StepObs
  zero_cut : n = 0 →
    Post (asmExec asmInit).1 (asmFfiExec asmFfiInit).1 ∧
    (asmExec asmInit).2 = zeroSchedule ∧
    (asmFfiExec asmFfiInit).2 = zeroSchedule
  pos_cert : n ≠ 0 →
    LoopRelationCert A M n.toNat asmBody asmFfiBody asmHead asmFfiHead LoopPost
  pos_sched : ∀ hn : n ≠ 0, (pos_cert hn).schedule = bodySchedule
  pos_replay : ∀ _hn : n ≠ 0,
    LoopPost (runCuts asmBody n.toNat asmHead).1 (runCuts asmFfiBody n.toNat asmFfiHead).1 →
    (runCuts asmBody n.toNat asmHead).2 = scheduleTrace bodySchedule n.toNat 0 →
    (runCuts asmFfiBody n.toNat asmFfiHead).2 = scheduleTrace bodySchedule n.toNat 0 →
    Post (asmExec asmInit).1 (asmFfiExec asmFfiInit).1 ∧
    (asmExec asmInit).2 = entrySchedule ++ (runCuts asmBody n.toNat asmHead).2 ++ exitSchedule ∧
    (asmFfiExec asmFfiInit).2 = entrySchedule ++ (runCuts asmFfiBody n.toNat asmFfiHead).2 ++ exitSchedule

def fullSchedule (n : Word) (zeroSched entrySched : List StepObs)
    (bodySched : Nat → List StepObs) (exitSched : List StepObs) : List StepObs :=
  if n = 0 then zeroSched else entrySched ++ scheduleTrace bodySched n.toNat 0 ++ exitSched

/-- Constructive (`0 Classical.choice`) soundness for unrestricted `n : BitVec 64` (`n = 0` and `n > 0`). -/
theorem unrestricted_loop_refinement_sound {A M : Type} {n : Word}
    {asmExec : A → A × List StepObs} {asmFfiExec : M → M × List StepObs}
    {asmBody : A → A × List StepObs} {asmFfiBody : M → M × List StepObs}
    {asmInit : A} {asmFfiInit : M} {asmHead : A} {asmFfiHead : M}
    {LP P : A → M → Prop}
    (c : UnrestrictedLoopCert A M n asmExec asmFfiExec asmBody asmFfiBody
      asmInit asmFfiInit asmHead asmFfiHead LP P) :
    P (asmExec asmInit).1 (asmFfiExec asmFfiInit).1 ∧
    (asmExec asmInit).2 =
      fullSchedule n c.zeroSchedule c.entrySchedule c.bodySchedule c.exitSchedule ∧
    (asmFfiExec asmFfiInit).2 =
      fullSchedule n c.zeroSchedule c.entrySchedule c.bodySchedule c.exitSchedule := by
  if hn : n = 0 then
    obtain ⟨hp, ha, hm⟩ := c.zero_cut hn
    simp only [fullSchedule, hn, ↓reduceIte]
    exact ⟨hp, ha, hm⟩
  else
    obtain ⟨hlp, hal, hml⟩ := sewell_loop_relation_refinement_sound (c.pos_cert hn)
    rw [c.pos_sched hn] at hal hml
    obtain ⟨hp, ha, hm⟩ := c.pos_replay hn hlp hal hml
    simp only [fullSchedule, hn, ↓reduceIte]
    rw [hal] at ha
    rw [hml] at hm
    exact ⟨hp, ha, hm⟩

/-- Constructive 3-way `StepObs` noninterference across all `n : BitVec 64` (`n = 0` and `n > 0`). -/
theorem unrestricted_three_way_noninterference {A M : Type} {n : Word}
    {asmExec : A → A × List StepObs} {asmFfiExec asmFfiExec₂ : M → M × List StepObs}
    {asmBody : A → A × List StepObs} {asmFfiBody : M → M × List StepObs}
    {a₁ a₂ : A} {m₁ m₂ : M} {ah₁ ah₂ : A} {mh₁ mh₂ : M}
    {LP₁ LP₂ P₁ P₂ : A → M → Prop}
    (c₁ : UnrestrictedLoopCert A M n asmExec asmFfiExec asmBody asmFfiBody a₁ m₁ ah₁ mh₁ LP₁ P₁)
    (c₂ : UnrestrictedLoopCert A M n asmExec asmFfiExec₂ asmBody asmFfiBody a₂ m₂ ah₂ mh₂ LP₂ P₂)
    (hz : c₁.zeroSchedule = c₂.zeroSchedule)
    (he : c₁.entrySchedule = c₂.entrySchedule)
    (hb : c₁.bodySchedule = c₂.bodySchedule)
    (hx : c₁.exitSchedule = c₂.exitSchedule) :
    (asmExec a₁).2 = (asmExec a₂).2 ∧
    (asmExec a₁).2 = (asmFfiExec m₁).2 := by
  obtain ⟨_, ha₁, hm₁⟩ := unrestricted_loop_refinement_sound c₁
  obtain ⟨_, ha₂, _⟩ := unrestricted_loop_refinement_sound c₂
  have hsched : fullSchedule n c₁.zeroSchedule c₁.entrySchedule c₁.bodySchedule c₁.exitSchedule =
      fullSchedule n c₂.zeroSchedule c₂.entrySchedule c₂.bodySchedule c₂.exitSchedule := by
    rw [hz, he, hb, hx]
  exact ⟨ha₁.trans (hsched.trans ha₂.symm), ha₁.trans hm₁.symm⟩

/-! ## §2. Single-Instruction Byte Decoders & `TvGraph` Welding -/

/-- Embed real `decodeX86One` + `stepX86` byte semantics into `TvGraph X86State` with an optional
entry zero-trip guard on register `countReg` (`label = 0` tests `s.gpr.get countReg == 0`;
labels `2 * pc + 2` execute instruction at `pc`; labels `2 * pc + 3` dispatch `jcc` / `ret`). -/

def x86GuardedBytesToGraph (code : List UInt8) (countReg entryPc fuel : Nat)
    (heads : List Nat) : TvGraph X86State where
  entry := 0
  fuel := fuel
  loopHeads := heads.map (fun h => 2 * h + 2)
  node := fun label =>
    if label == 0 then
      .Cond (fun s => s.gpr.get countReg == 0) 1 (2 * entryPc + 2)
    else if label == 1 then
      .Ret (fun s => BitVec.ofNat 64 (s.gpr.get 0).toNat)
    else
      let rem := label - 2
      let pc := rem / 2
      match decodeX86One code pc with
      | none => .Err
      | some d =>
        if rem % 2 == 0 then
          match d.instr with
          | .jcc _ _ | .ret => .Assign (fun s => (stepX86 d s).1) (label + 1)
          | .jmpRel tgt =>
            if tgt ≥ 0 then .Assign (fun s => (stepX86 d s).1) (2 * tgt.toNat + 2) else .Err
          | _ => .Assign (fun s => (stepX86 d s).1) (2 * (d.offset + d.byteLen) + 2)
        else
          match d.instr with
          | .jcc _ tgt =>
            if tgt ≥ 0 then
              .Cond (fun s => s.pc == tgt.toNat) (2 * tgt.toNat + 2) (2 * (d.offset + d.byteLen) + 2)
            else .Err
          | .ret => .Ret (fun s => BitVec.ofNat 64 (s.gpr.get 0).toNat)
          | _ => .Err

/-- Embed real `decodeArm64One` + `stepArm64` byte semantics into `TvGraph Arm64State` with
entry zero-trip guard on register `countReg`. -/
def arm64GuardedBytesToGraph (code : List UInt8) (countReg entryPc fuel : Nat)
    (heads : List Nat) : TvGraph Arm64State where
  entry := 0
  fuel := fuel
  loopHeads := heads.map (fun h => 2 * h + 2)
  node := fun label =>
    if label == 0 then
      .Cond (fun s => getArmGpr s countReg == 0) 1 (2 * entryPc + 2)
    else if label == 1 then
      .Ret (fun s => BitVec.ofNat 64 (getArmGpr s 0).toNat)
    else
      let rem := label - 2
      let pc := rem / 2
      match decodeArm64One code pc with
      | none => .Err
      | some d =>
        if rem % 2 == 0 then
          match d.instr with
          | .bCond _ _ | .ret => .Assign (fun s => (stepArm64 d s).1) (label + 1)
          | _ => .Assign (fun s => (stepArm64 d s).1) (2 * (d.offset + d.byteLen) + 2)
        else
          match d.instr with
          | .bCond _ tgt =>
            if tgt ≥ 0 then
              .Cond (fun s => s.pc == tgt.toNat) (2 * tgt.toNat + 2) (2 * (d.offset + d.byteLen) + 2)
            else .Err
          | .ret => .Ret (fun s => BitVec.ofNat 64 (getArmGpr s 0).toNat)
          | _ => .Err

/-- Zero-trip entry-to-exit cut theorem on `x86GuardedBytesToGraph`: when `s.gpr.get countReg = 0`,
symbolic flattening takes the zero-trip branch directly to `.ret` without entering the loop body. -/
theorem x86GuardedGraph_zero_trip_cut (code : List UInt8) (countReg entryPc k : Nat)
    (heads : List Nat) (h0 : 0 ∉ heads.map (fun h => 2 * h + 2))
    (h1 : 1 ∉ heads.map (fun h => 2 * h + 2))
    (s : X86State) (hz : s.gpr.get countReg = 0) :
    evalFlattened (flattenDag (x86GuardedBytesToGraph code countReg entryPc (k + 2) heads) (fun _ => id)) s =
      .ret (BitVec.ofNat 64 (s.gpr.get 0).toNat) s := by
  rw [flattenDag_sound]
  simp [execGraphDag, execFrom, x86GuardedBytesToGraph, h0, h1, hz]

/-- Positive-count entry-to-head cut theorem on `x86GuardedBytesToGraph`: when `s.gpr.get countReg ≠ 0`
and `entryPc ∈ heads`, symbolic flattening cuts at the loop head `2 * entryPc + 2`. -/
theorem x86GuardedGraph_pos_head_cut (code : List UInt8) (countReg entryPc k : Nat)
    (heads : List Nat) (h0 : 0 ∉ heads.map (fun h => 2 * h + 2))
    (hhead : entryPc ∈ heads)
    (s : X86State) (hnz : s.gpr.get countReg ≠ 0) :
    evalFlattened (flattenDag (x86GuardedBytesToGraph code countReg entryPc (k + 2) heads) (fun _ => id)) s =
      .cut (2 * entryPc + 2) s := by
  rw [flattenDag_sound]
  have hmem : (2 * entryPc + 2) ∈ heads.map (fun h => 2 * h + 2) := List.mem_map_of_mem hhead
  simp [execGraphDag, execFrom, x86GuardedBytesToGraph, h0, beq_false_of_ne hnz, hmem]

theorem arm64GuardedGraph_zero_trip_cut (code : List UInt8) (countReg entryPc k : Nat)
    (heads : List Nat) (h0 : 0 ∉ heads.map (fun h => 2 * h + 2))
    (h1 : 1 ∉ heads.map (fun h => 2 * h + 2))
    (s : Arm64State) (hz : getArmGpr s countReg = 0) :
    evalFlattened (flattenDag (arm64GuardedBytesToGraph code countReg entryPc (k + 2) heads) (fun _ => id)) s =
      .ret (BitVec.ofNat 64 (getArmGpr s 0).toNat) s := by
  rw [flattenDag_sound]
  simp [execGraphDag, execFrom, arm64GuardedBytesToGraph, h0, h1, hz]

theorem arm64GuardedGraph_pos_head_cut (code : List UInt8) (countReg entryPc k : Nat)
    (heads : List Nat) (h0 : 0 ∉ heads.map (fun h => 2 * h + 2))
    (hhead : entryPc ∈ heads)
    (s : Arm64State) (hnz : getArmGpr s countReg ≠ 0) :
    evalFlattened (flattenDag (arm64GuardedBytesToGraph code countReg entryPc (k + 2) heads) (fun _ => id)) s =
      .cut (2 * entryPc + 2) s := by
  rw [flattenDag_sound]
  have hmem : (2 * entryPc + 2) ∈ heads.map (fun h => 2 * h + 2) := List.mem_map_of_mem hhead
  simp [execGraphDag, execFrom, arm64GuardedBytesToGraph, h0, beq_false_of_ne hnz, hmem]

/-- Generic pointer recurrence with arbitrary byte stride `stride` (wrapping mod `2^64`). -/
def ptrStride (base : UInt64) (stride : UInt64) : Nat → UInt64
  | 0 => base
  | v + 1 => ptrStride base stride v + stride

theorem ptrStride_one_eq (base : UInt64) (v : Nat) :
    ptrStride base 1 v = base + UInt64.ofNat v := by
  induction v with
  | zero => simp [ptrStride]
  | succ v ih =>
    simp only [ptrStride, ih]
    apply u64_eq_of_toNat_eq
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
    have h1 : (1 : UInt64).toNat = 1 := rfl
    have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
    rw [h1]
    omega

theorem ptrStride_32_eq (base : UInt64) (v : Nat) :
    ptrStride base 32 v = base + UInt64.ofNat (32 * v) := by
  induction v with
  | zero => simp [ptrStride]
  | succ v ih =>
    simp only [ptrStride, ih]
    apply u64_eq_of_toNat_eq
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
    have h32 : (32 : UInt64).toNat = 32 := rfl
    have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
    rw [h32]
    omega

/-! ## §4. Kernel 1 — `qsag_asm_ct_memzero_x86_64` (1-Pointer Affine, Unrestricted `∀ n : Word`) -/

structure AsmFfiMemzero where
  ptr : UInt64
  remaining : Nat
  mem : UInt64 → UInt8

def memzeroX86EntryObs : List StepObs := [⟨0, [], true⟩, ⟨3, [], true⟩]

def memzeroX86BodyObs (p : UInt64) : List StepObs :=
  [⟨5, [(p, 1)], true⟩, ⟨7, [], true⟩, ⟨10, [], true⟩, ⟨13, [], true⟩]

def memzeroX86ExitObs (rsp : UInt64) : List StepObs :=
  [⟨15, [], true⟩, ⟨18, [], true⟩, ⟨20, [], true⟩, ⟨22, [], true⟩, ⟨24, [], true⟩, ⟨26, [], true⟩,
   ⟨29, [], true⟩, ⟨32, [], true⟩, ⟨35, [], true⟩, ⟨38, [], true⟩, ⟨40, [(rsp, 8)], true⟩]

/-- The caller-saved scratch registers `rcx`, `rdx`, `rsi`, `rdi`, `r8`–`r11` set to zero, in the
order the production epilogue clears them. -/
def wipeScratch (g : Bank16 UInt64) : Bank16 UInt64 :=
  g.set 7 0 |>.set 6 0 |>.set 2 0 |>.set 1 0 |>.set 8 0 |>.set 9 0 |>.set 10 0 |>.set 11 0

def memzeroX86BodyStep (s : X86State) : X86State × List StepObs :=
  let p := s.gpr.get 7
  let c := s.gpr.get 1
  ({ s with
      pc := jccPc (!(c - 1 == 0)) 5 15
      gpr := (s.gpr.set 7 (p + 1)).set 1 (c - 1)
      ofFlag := evalX86IncDecOf false true c
      zf := c - 1 == 0
      mem := writeMem8 s.mem p 0 },
   memzeroX86BodyObs p)

def asmFfiMemzeroX86BodyStep (m : AsmFfiMemzero) : AsmFfiMemzero × List StepObs :=
  (⟨m.ptr + 1, m.remaining - 1, writeMem8 m.mem m.ptr 0⟩, memzeroX86BodyObs m.ptr)

theorem asmFfiMemzero_cuts_mem (k : Nat) (p : UInt64) (rem : Nat) (mem : UInt64 → UInt8) :
    (runCuts asmFfiMemzeroX86BodyStep k ⟨p, rem, mem⟩).1.mem = zeroRange k mem p := by
  induction k generalizing p rem mem with
  | zero => simp [runCuts]
  | succ k ih =>
    simpa [runCuts, asmFfiMemzeroX86BodyStep, zeroRange_zero, zeroRange_succ] using ih (p + 1) (rem - 1) (writeMem8 mem p 0)

/-- Symbol execution behind a zero-count guard on `rsi`. The guard branch is a hand-written
model of the Rust wrapper's early return on empty input, not decoded machine code. -/
def ctMemzeroX86GuardedRun (fetch : Nat → Option (DecodedInstr X86Instr))
    (fuel : Nat) (s : X86State) : X86State × List StepObs :=
  if s.gpr.get 6 == 0 then ({ s with halted := true }, [⟨0, [], true⟩])
  else runX86Fetch fetch fuel s

def asmFfiMemzeroX86Run (rsp : UInt64) (n : Word) (base : UInt64) (mem : UInt64 → UInt8) : AsmFfiMemzero × List StepObs :=
  if n = 0 then (⟨base, 0, mem⟩, [⟨0, [], true⟩])
  else
    let loop := runCuts asmFfiMemzeroX86BodyStep n.toNat ⟨base, n.toNat, mem⟩
    (loop.1, memzeroX86EntryObs ++ loop.2 ++ (memzeroX86ExitObs rsp))

section MemzeroX86Fetch
variable (fetch : Nat → Option (DecodedInstr X86Instr))
  (hf0 : fetch 0 = some ⟨0, 3, .movRegReg true 1 6⟩)
  (hf3 : fetch 3 = some ⟨3, 2, .aluRegReg .xorOp false 0 0⟩)
  (hf5 : fetch 5 = some ⟨5, 2, .storeGpr 1 0 (.baseDisp 7 0)⟩)
  (hf7 : fetch 7 = some ⟨7, 3, .incDec true true 7⟩)
  (hf10 : fetch 10 = some ⟨10, 3, .incDec false true 1⟩)
  (hf13 : fetch 13 = some ⟨13, 2, .jcc 5 5⟩)
  (hf15 : fetch 15 = some ⟨15, 3, .mfence⟩)
  (hf18 : fetch 18 = some ⟨18, 2, .aluRegReg .xorOp false 7 7⟩)
  (hf20 : fetch 20 = some ⟨20, 2, .aluRegReg .xorOp false 6 6⟩)
  (hf22 : fetch 22 = some ⟨22, 2, .aluRegReg .xorOp false 2 2⟩)
  (hf24 : fetch 24 = some ⟨24, 2, .aluRegReg .xorOp false 1 1⟩)
  (hf26 : fetch 26 = some ⟨26, 3, .aluRegReg .xorOp false 8 8⟩)
  (hf29 : fetch 29 = some ⟨29, 3, .aluRegReg .xorOp false 9 9⟩)
  (hf32 : fetch 32 = some ⟨32, 3, .aluRegReg .xorOp false 10 10⟩)
  (hf35 : fetch 35 = some ⟨35, 3, .aluRegReg .xorOp false 11 11⟩)
  (hf38 : fetch 38 = some ⟨38, 2, .aluRegReg .xorOp false 0 0⟩)
  (hf40 : fetch 40 = some ⟨40, 1, .ret⟩)

include hf0 hf3 in
theorem ctMemzeroX86_entry_full (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) (fuel : Nat) :
    runX86Fetch fetch (2 + fuel)
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, m⟩ =
      let u := runX86Fetch fetch fuel
        ⟨5, ⟨0, r6, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, false, false, true, dy, false, m⟩
      (u.1, memzeroX86EntryObs ++ u.2) := by
  rw [show 2 + fuel = (fuel + 1) + 1 from by omega]
  rw [runX86Fetch_step fetch (fuel + 1) _ _ rfl hf0]
  simp only [stepX86Full_movRR, maskGprWidth_true, b16get_6, b16set_1]
  rw [runX86Fetch_step fetch fuel _ _ rfl hf3]
  simp only [stepX86Full_xorRR, b16get_0, mask32_xor_self_eq, u64_zero_beq_true, b16set_0, memzeroX86EntryObs]
  rfl

include hf5 hf7 hf10 hf13 in
theorem ctMemzeroX86_body_full (c p r2 r3 r4 r5 r6 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) (fuel : Nat) :
    let s : X86State := ⟨5, ⟨0, c, r2, r3, r4, r5, r6, p, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, m⟩
    runX86Fetch fetch (4 + fuel) s =
      ((runX86Fetch fetch fuel (memzeroX86BodyStep s).1).1,
       (memzeroX86BodyStep s).2 ++ (runX86Fetch fetch fuel (memzeroX86BodyStep s).1).2) := by
  dsimp only
  rw [show 4 + fuel = (((fuel + 1) + 1) + 1) + 1 from by omega]
  rw [runX86Fetch_step fetch _ _ _ rfl hf5]
  simp only [stepX86Full_store8, b16get_7, b16get_0]
  rw [runX86Fetch_step fetch _ _ _ rfl hf7]
  simp only [stepX86Full_inc64, b16get_7, b16set_7]
  rw [runX86Fetch_step fetch _ _ _ rfl hf10]
  simp only [stepX86Full_dec64, b16get_1, b16set_1]
  rw [runX86Fetch_step fetch _ _ _ rfl hf13]
  simp only [stepX86Full_jnz, memzeroX86BodyStep, memzeroX86BodyObs, b16get_7, b16get_1, b16set_7, b16set_1]
  rfl

include hf15 hf18 hf20 hf22 hf24 hf26 hf29 hf32 hf35 hf38 hf40 in
theorem ctMemzeroX86_exit_full (g : Bank16 UInt64) (y : Bank16 Vec256) (cf o zf dy : Bool)
    (m : UInt64 → UInt8) (extra : Nat) :
    runX86Fetch fetch (11 + extra) ⟨15, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨(readMem64 m (g.get 4)).toNat, ((wipeScratch g).set 0 0).set 4 (g.get 4 + 8), y, false, false, true, dy, true, m⟩, (memzeroX86ExitObs (g.get 4))) := by
  rw [show 11 + extra = ((((((((((extra + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 from by omega]
  rw [runX86Fetch_step fetch _ _ _ rfl hf15]
  simp only [stepX86Full_mfence]
  rw [runX86Fetch_step fetch _ _ _ rfl hf18]
  simp only [stepX86Full_xorRR, mask32_xor_self_eq, u64_zero_beq_true]
  rw [runX86Fetch_step fetch _ _ _ rfl hf20]
  simp only [stepX86Full_xorRR, mask32_xor_self_eq, u64_zero_beq_true]
  rw [runX86Fetch_step fetch _ _ _ rfl hf22]
  simp only [stepX86Full_xorRR, mask32_xor_self_eq, u64_zero_beq_true]
  rw [runX86Fetch_step fetch _ _ _ rfl hf24]
  simp only [stepX86Full_xorRR, mask32_xor_self_eq, u64_zero_beq_true]
  rw [runX86Fetch_step fetch _ _ _ rfl hf26]
  simp only [stepX86Full_xorRR, mask32_xor_self_eq, u64_zero_beq_true]
  rw [runX86Fetch_step fetch _ _ _ rfl hf29]
  simp only [stepX86Full_xorRR, mask32_xor_self_eq, u64_zero_beq_true]
  rw [runX86Fetch_step fetch _ _ _ rfl hf32]
  simp only [stepX86Full_xorRR, mask32_xor_self_eq, u64_zero_beq_true]
  rw [runX86Fetch_step fetch _ _ _ rfl hf35]
  simp only [stepX86Full_xorRR, mask32_xor_self_eq, u64_zero_beq_true]
  rw [runX86Fetch_step fetch _ _ _ rfl hf38]
  simp only [stepX86Full_xorRR, mask32_xor_self_eq, u64_zero_beq_true]
  rw [runX86Fetch_step fetch _ _ _ rfl hf40]
  simp only [stepX86Full_ret, memzeroX86ExitObs, wipeScratch]
  rw [runX86Fetch_halted _ _ _ rfl]
  cases g
  rfl

end MemzeroX86Fetch

def MemzeroX86Rel (s₀ : X86State) (n v : Nat) (a : X86State) (m : AsmFfiMemzero) : Prop :=
  ∃ o zf : Bool,
    a = ⟨if v = n then 15 else 5,
          (s₀.gpr.set 0 0 |>.set 1 (UInt64.ofNat (n - v)) |>.set 7 (ptrStride (s₀.gpr.get 7) 1 v)),
          s₀.ymm, false, o, zf, s₀.ymmDirty, false, m.mem⟩ ∧
    m.ptr = ptrStride (s₀.gpr.get 7) 1 v ∧
    m.remaining = n - v

def MemzeroX86LoopPost (s₀ : X86State) (n : Nat) (a : X86State) (m : AsmFfiMemzero) : Prop :=
  ∃ o zf : Bool,
    a = ⟨15, (s₀.gpr.set 0 0 |>.set 1 0 |>.set 7 (ptrStride (s₀.gpr.get 7) 1 n)),
          s₀.ymm, false, o, zf, s₀.ymmDirty, false, m.mem⟩ ∧
    m.remaining = 0

def MemzeroX86Post (s₀ : X86State) (n : Word) (out : X86State) (m : AsmFfiMemzero) : Prop :=
  out.halted = true ∧
  out.mem = m.mem ∧
  out.mem = zeroRange n.toNat s₀.mem (s₀.gpr.get 7) ∧
  (∀ i < n.toNat, out.mem (s₀.gpr.get 7 + UInt64.ofNat i) = 0) ∧
  (∀ addr, (∀ i < n.toNat, addr ≠ s₀.gpr.get 7 + UInt64.ofNat i) → out.mem addr = s₀.mem addr) ∧
  out.gpr.get 4 = (if n = 0 then s₀.gpr.get 4 else s₀.gpr.get 4 + 8) ∧
  out.gpr.get 3 = s₀.gpr.get 3 ∧
  out.gpr.get 5 = s₀.gpr.get 5 ∧
  (∀ r, 12 ≤ r → r < 16 → out.gpr.get r = s₀.gpr.get r) ∧
  (n ≠ 0 → out.gpr.get 0 = 0 ∧ out.gpr.get 1 = 0 ∧ out.gpr.get 2 = 0 ∧ out.gpr.get 6 = 0 ∧
    out.gpr.get 7 = 0 ∧ out.gpr.get 8 = 0 ∧ out.gpr.get 9 = 0 ∧ out.gpr.get 10 = 0 ∧
    out.gpr.get 11 = 0)

theorem u64_ofNat_sub_one {k : Nat} (hk : 0 < k) (hbound : k < 2 ^ 64) :
    UInt64.ofNat k - 1 = UInt64.ofNat (k - 1) := by
  apply u64_eq_of_toNat_eq
  have h1 : (1 : UInt64).toNat = 1 := rfl
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  rw [UInt64.toNat_sub, UInt64.toNat_ofNat', UInt64.toNat_ofNat', h1]
  rw [h64] at hbound ⊢
  omega

theorem u64_ofNat_eq_zero_iff {k : Nat} (hbound : k < 2 ^ 64) :
    (UInt64.ofNat k == 0) = decide (k = 0) := by
  cases k with
  | zero => rfl
  | succ j =>
    have hne : UInt64.ofNat (j + 1) ≠ 0 := by
      intro h
      have := congrArg UInt64.toNat h
      have h0 : (0 : UInt64).toNat = 0 := rfl
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hbound, h0] at this
      omega
    simp only [beq_false_of_ne hne]
    rfl

def ctMemzeroX86PosCert (s₀ : X86State) (n : Nat) (hn : 0 < n) (hbound : n < 2 ^ 64) :
    LoopRelationCert X86State AsmFfiMemzero n memzeroX86BodyStep asmFfiMemzeroX86BodyStep
      ⟨5, (s₀.gpr.set 0 0 |>.set 1 (UInt64.ofNat n)), s₀.ymm, false, false, true, s₀.ymmDirty, false, s₀.mem⟩
      ⟨s₀.gpr.get 7, n, s₀.mem⟩
      (MemzeroX86LoopPost s₀ n) where
  LoopRel := MemzeroX86Rel s₀ n
  schedule := fun v => memzeroX86BodyObs (ptrStride (s₀.gpr.get 7) 1 v)
  entry := by
    refine ⟨false, true, ?_, rfl, by dsimp only; omega⟩
    obtain ⟨_, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, _, _, _, _, _, _, _⟩ := s₀
    simp [ptrStride, Nat.ne_of_lt hn, b16get_7, b16set_0, b16set_1, b16set_7]
  body := by
    intro v a m hv ⟨o, zf, ha, hmp, hmr⟩
    subst ha
    obtain ⟨_, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, _, _, _, dy, _, _⟩ := s₀
    have hvn : v ≠ n := Nat.ne_of_lt hv
    have hpos : 0 < n - v := by omega
    have hlt : n - v < 2 ^ 64 := by omega
    have hdec := u64_ofNat_sub_one hpos hlt
    have hsub : n - v - 1 = n - (v + 1) := by omega
    have hzf : (UInt64.ofNat (n - (v + 1)) == 0) = decide (v + 1 = n) := by
      rw [u64_ofNat_eq_zero_iff (by omega)]
      by_cases heq : v + 1 = n <;> simp [heq] <;> omega
    have hjcc : jccPc (!(UInt64.ofNat (n - (v + 1)) == 0)) 5 15 = (if v + 1 = n then 15 else 5) := by
      rw [hzf]
      by_cases heq : v + 1 = n <;> simp [heq, jccPc]
    refine ⟨⟨evalX86IncDecOf false true (UInt64.ofNat (n - v)), UInt64.ofNat (n - (v + 1)) == 0,
      ?_, ?_, ?_⟩, ?_, ?_⟩
    · simp only [memzeroX86BodyStep, asmFfiMemzeroX86BodyStep, b16get_7, b16get_1,
        b16set_0, b16set_1, b16set_7, hdec, hsub, hjcc, ptrStride, hmp]
    · simp [asmFfiMemzeroX86BodyStep, hmp, ptrStride]
    · simp [asmFfiMemzeroX86BodyStep, hmr]; omega
    · simp [memzeroX86BodyStep, b16get_7, b16set_0, b16set_1, b16set_7]
    · simp [asmFfiMemzeroX86BodyStep, hmp, b16get_7]
  exit := by
    intro a m ⟨o, zf, ha, _, hmr⟩
    exact ⟨o, zf, by simpa using ha, by omega⟩

theorem ctMemzeroX86_replay_loop (fetch : Nat → Option (DecodedInstr X86Instr))
    (hf5 : fetch 5 = some ⟨5, 2, .storeGpr 1 0 (.baseDisp 7 0)⟩)
    (hf7 : fetch 7 = some ⟨7, 3, .incDec true true 7⟩)
    (hf10 : fetch 10 = some ⟨10, 3, .incDec false true 1⟩)
    (hf13 : fetch 13 = some ⟨13, 2, .jcc 5 5⟩)
    (s₀ : X86State) (n : Nat) (hn : 0 < n) (hbound : n < 2 ^ 64) (rem : Nat) :
    ∀ v a m fuel, v + rem = n → MemzeroX86Rel s₀ n v a m →
      runX86Fetch fetch (4 * rem + fuel) a =
        let loop := runCuts memzeroX86BodyStep rem a
        let u := runX86Fetch fetch fuel loop.1
        (u.1, loop.2 ++ u.2) := by
  induction rem with
  | zero =>
    intro v a m fuel _ _
    simp [runCuts]
  | succ k ih =>
    intro v a m fuel hv hrel
    have hvn : v < n := by omega
    rcases hrel with ⟨o, zf, ha, hmp, hmr⟩
    have hrel' : MemzeroX86Rel s₀ n v a m := ⟨o, zf, ha, hmp, hmr⟩
    have hbody := (ctMemzeroX86PosCert s₀ n hn hbound).body v a m hvn hrel'
    obtain ⟨_, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, _, _, _, dy, _, _⟩ := s₀
    have ha5 : a = ⟨5, ⟨0, UInt64.ofNat (n - v), r2, r3, r4, r5, r6, ptrStride r7 1 v,
        r8, r9, r10, r11, r12, r13, r14, r15⟩, y, false, o, zf, dy, false, m.mem⟩ := by
      simpa [Nat.ne_of_lt hvn, b16get_7, b16set_0, b16set_1, b16set_7] using ha
    rw [show 4 * (k + 1) + fuel = 4 + (4 * k + fuel) from by omega, ha5]
    rw [ctMemzeroX86_body_full fetch hf5 hf7 hf10 hf13]
    rw [← ha5]
    rw [ih (v + 1) (memzeroX86BodyStep a).1 (asmFfiMemzeroX86BodyStep m).1 fuel (by omega) hbody.1]
    simp [runCuts, List.append_assoc]

/-- Complete `UnrestrictedLoopCert` for `qsag_asm_ct_memzero_x86_64` over **all `n : BitVec 64`**
(`n = 0` zero-trip cut + `n ≠ 0` byte-decoded `.rlib` execution). -/
def ctMemzeroX86UnrestrictedCert (fetch : Nat → Option (DecodedInstr X86Instr))
    (hf : ∀ d ∈ ctCurrentMemzeroX86Prog, fetch d.offset = some d)
    (s₀ : X86State) (fuel : Nat) (hpc : s₀.pc = 0) (hh : s₀.halted = false)
    (n : Word) (hcount : s₀.gpr.get 6 = UInt64.ofBitVec n)
    (hfuel : 4 * n.toNat + 13 ≤ fuel) :
    UnrestrictedLoopCert X86State AsmFfiMemzero n
      (ctMemzeroX86GuardedRun fetch fuel)
      (fun m => asmFfiMemzeroX86Run (s₀.gpr.get 4) n m.ptr m.mem)
      memzeroX86BodyStep asmFfiMemzeroX86BodyStep
      s₀ ⟨s₀.gpr.get 7, n.toNat, s₀.mem⟩
      ⟨5, (s₀.gpr.set 0 0 |>.set 1 (UInt64.ofNat n.toNat)), s₀.ymm, false, false, true, s₀.ymmDirty, false, s₀.mem⟩
      ⟨s₀.gpr.get 7, n.toNat, s₀.mem⟩
      (MemzeroX86LoopPost s₀ n.toNat)
      (MemzeroX86Post s₀ n) where
  zeroSchedule := [⟨0, [], true⟩]
  entrySchedule := memzeroX86EntryObs
  bodySchedule := fun v => memzeroX86BodyObs (ptrStride (s₀.gpr.get 7) 1 v)
  exitSchedule := (memzeroX86ExitObs (s₀.gpr.get 4))
  zero_cut := by
    intro hz
    subst hz
    have hg0 : (s₀.gpr.get 6 == 0) = true := by simp [hcount]
    dsimp only [ctMemzeroX86GuardedRun, asmFfiMemzeroX86Run]
    rw [ite_eq_left hg0, ite_eq_left rfl]
    refine ⟨⟨rfl, rfl, by simp, ?_, ?_, rfl, rfl, rfl, fun _ _ _ => rfl, fun h => absurd rfl h⟩, rfl, rfl⟩
    · intro i hi; exact absurd hi (Nat.not_lt_zero i)
    · intro _ _; rfl
  pos_cert := fun hn =>
    ctMemzeroX86PosCert s₀ n.toNat (bv64_pos_of_ne_zero n hn) n.isLt
  pos_sched := fun _ => rfl
  pos_replay := by
    intro hn hlp hal hml
    have hg0 : ¬ ((s₀.gpr.get 6 == 0) = true) := by
      rw [beq_false_of_ne (hcount ▸ (bv64_ne_zero_iff_u64_ne_zero n).mp hn)]; decide
    dsimp only [ctMemzeroX86GuardedRun, asmFfiMemzeroX86Run]
    rw [ite_eq_right hg0, ite_eq_right hn]
    have hf0 := hf ⟨0, 3, .movRegReg true 1 6⟩ (by simp only [ctCurrentMemzeroX86Prog_eq]; simp)
    have hf3 := hf ⟨3, 2, .aluRegReg .xorOp false 0 0⟩ (by simp only [ctCurrentMemzeroX86Prog_eq]; simp)
    have hf5 := hf ⟨5, 2, .storeGpr 1 0 (.baseDisp 7 0)⟩ (by simp only [ctCurrentMemzeroX86Prog_eq]; simp)
    have hf7 := hf ⟨7, 3, .incDec true true 7⟩ (by simp only [ctCurrentMemzeroX86Prog_eq]; simp)
    have hf10 := hf ⟨10, 3, .incDec false true 1⟩ (by simp only [ctCurrentMemzeroX86Prog_eq]; simp)
    have hf13 := hf ⟨13, 2, .jcc 5 5⟩ (by simp only [ctCurrentMemzeroX86Prog_eq]; simp)
    have hf15 := hf ⟨15, 3, .mfence⟩ (by simp only [ctCurrentMemzeroX86Prog_eq]; simp)
    have hf18 := hf ⟨18, 2, .aluRegReg .xorOp false 7 7⟩ (by simp only [ctCurrentMemzeroX86Prog_eq]; simp)
    have hf20 := hf ⟨20, 2, .aluRegReg .xorOp false 6 6⟩ (by simp only [ctCurrentMemzeroX86Prog_eq]; simp)
    have hf22 := hf ⟨22, 2, .aluRegReg .xorOp false 2 2⟩ (by simp only [ctCurrentMemzeroX86Prog_eq]; simp)
    have hf24 := hf ⟨24, 2, .aluRegReg .xorOp false 1 1⟩ (by simp only [ctCurrentMemzeroX86Prog_eq]; simp)
    have hf26 := hf ⟨26, 3, .aluRegReg .xorOp false 8 8⟩ (by simp only [ctCurrentMemzeroX86Prog_eq]; simp)
    have hf29 := hf ⟨29, 3, .aluRegReg .xorOp false 9 9⟩ (by simp only [ctCurrentMemzeroX86Prog_eq]; simp)
    have hf32 := hf ⟨32, 3, .aluRegReg .xorOp false 10 10⟩ (by simp only [ctCurrentMemzeroX86Prog_eq]; simp)
    have hf35 := hf ⟨35, 3, .aluRegReg .xorOp false 11 11⟩ (by simp only [ctCurrentMemzeroX86Prog_eq]; simp)
    have hf38 := hf ⟨38, 2, .aluRegReg .xorOp false 0 0⟩ (by simp only [ctCurrentMemzeroX86Prog_eq]; simp)
    have hf40 := hf ⟨40, 1, .ret⟩ (by simp only [ctCurrentMemzeroX86Prog_eq]; simp)
    obtain ⟨extra, hextra⟩ : ∃ extra, fuel = 2 + (4 * n.toNat + (11 + extra)) :=
      ⟨fuel - (4 * n.toNat + 13), by omega⟩
    rw [hextra]
    obtain ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
      y, cf, o, zf, dy, hlt, m⟩ := s₀
    cases hpc; cases hh
    have hr6 : r6 = UInt64.ofNat n.toNat := by
      apply u64_eq_of_toNat_eq
      have : r6 = UInt64.ofBitVec n := hcount
      rw [this, UInt64.toNat_ofNat', Nat.mod_eq_of_lt n.isLt]
      rfl
    rw [ctMemzeroX86_entry_full fetch hf0 hf3]
    have headEq : (⟨5, ⟨0, r6, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        y, false, false, true, dy, false, m⟩ : X86State) =
      ⟨5, ((Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15).set 0 0 |>.set 1 (UInt64.ofNat n.toNat)),
        y, false, false, true, dy, false, m⟩ := by
      simp [hr6, b16set_0, b16set_1]
    rw [headEq]
    have hpos := bv64_pos_of_ne_zero n hn
    have hrep := ctMemzeroX86_replay_loop fetch hf5 hf7 hf10 hf13
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, m⟩
      n.toNat hpos n.isLt n.toNat 0 _ ⟨r7, n.toNat, m⟩ (11 + extra) (by omega)
      (ctMemzeroX86PosCert _ n.toNat hpos n.isLt).entry
    dsimp only at hrep ⊢
    rw [hrep]
    rcases hlp with ⟨oL, zfL, haL, _⟩
    rw [haL, ctMemzeroX86_exit_full fetch hf15 hf18 hf20 hf22 hf24 hf26 hf29 hf32 hf35 hf38 hf40]
    have hzr := asmFfiMemzero_cuts_mem n.toNat r7 n.toNat m
    refine ⟨?_, by simp only [List.append_assoc]; rfl, rfl⟩
    dsimp only [MemzeroX86Post]
    rw [ite_eq_right hn]
    refine ⟨rfl, rfl, hzr, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    · intro i hi
      have h := zeroRange_inside n.toNat m r7 i hi
      rw [← hzr] at h; exact h
    · intro addr haddr
      have h := zeroRange_outside n.toNat m r7 addr haddr
      rw [← hzr] at h; exact h
    · rfl
    · rfl
    · rfl
    · intro r h12 h16
      match r, h12, h16 with
      | 12, _, _ => rfl | 13, _, _ => rfl | 14, _, _ => rfl | 15, _, _ => rfl
      | r + 16, _, h => exact absurd h (by omega)

theorem ctMemzeroX86_fetch_decodeOne :
    ∀ d ∈ ctCurrentMemzeroX86Prog, decodeX86One zeroCode d.offset = some d := by
  intro d hd
  have hall := ctMemzeroX86_decodeOne_all.2
  rw [List.all_eq_true] at hall
  have h := hall d hd
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

/-- Refinement and `StepObs` noninterference for the guarded runner of `qsag_asm_ct_memzero_x86_64` at every
`n : BitVec 64`. For `n ≠ 0` the runner is byte-decoded execution of the symbol
(`ct_memzero_x86_64_sydtv_refines_pos`); for `n = 0` it is the modelled wrapper early return. -/
theorem ct_memzero_x86_64_sydtv_refines_all_n (s₁ s₂ : X86State) (fuel : Nat) (n : Word)
    (hpc₁ : s₁.pc = 0) (hh₁ : s₁.halted = false) (hc₁ : s₁.gpr.get 6 = UInt64.ofBitVec n)
    (hpc₂ : s₂.pc = 0) (hh₂ : s₂.halted = false) (hc₂ : s₂.gpr.get 6 = UInt64.ofBitVec n)
    (hptr : s₁.gpr.get 7 = s₂.gpr.get 7)
    (hfuel : 4 * n.toNat + 13 ≤ fuel)
    (hsp : s₁.gpr.get 4 = s₂.gpr.get 4) :
    let c₁ := ctMemzeroX86UnrestrictedCert (decodeX86One zeroCode) ctMemzeroX86_fetch_decodeOne
      s₁ fuel hpc₁ hh₁ n hc₁ hfuel
    let out₁ := ctMemzeroX86GuardedRun (decodeX86One zeroCode) fuel s₁
    let out₂ := ctMemzeroX86GuardedRun (decodeX86One zeroCode) fuel s₂
    let ffi₁ := asmFfiMemzeroX86Run (s₁.gpr.get 4) n (s₁.gpr.get 7) s₁.mem
    MemzeroX86Post s₁ n out₁.1 ffi₁.1 ∧
    out₁.2 = out₂.2 ∧
    out₁.2 = ffi₁.2 ∧
    out₁.2 = fullSchedule n c₁.zeroSchedule c₁.entrySchedule c₁.bodySchedule c₁.exitSchedule := by
  dsimp only
  let c₁ := ctMemzeroX86UnrestrictedCert (decodeX86One zeroCode) ctMemzeroX86_fetch_decodeOne
    s₁ fuel hpc₁ hh₁ n hc₁ hfuel
  let c₂ := ctMemzeroX86UnrestrictedCert (decodeX86One zeroCode) ctMemzeroX86_fetch_decodeOne
    s₂ fuel hpc₂ hh₂ n hc₂ hfuel
  obtain ⟨hp, ha₁, _⟩ := unrestricted_loop_refinement_sound c₁
  have hni : (ctMemzeroX86GuardedRun (decodeX86One zeroCode) fuel s₁).2 =
      (ctMemzeroX86GuardedRun (decodeX86One zeroCode) fuel s₂).2 ∧
      (ctMemzeroX86GuardedRun (decodeX86One zeroCode) fuel s₁).2 =
      (asmFfiMemzeroX86Run (s₁.gpr.get 4) n (s₁.gpr.get 7) s₁.mem).2 := by
    obtain ⟨_, hb₁, hm₁⟩ := unrestricted_loop_refinement_sound c₁
    obtain ⟨_, hb₂, _⟩ := unrestricted_loop_refinement_sound c₂
    have hsched : c₁.bodySchedule = c₂.bodySchedule := by
      funext v; simp [c₁, c₂, ctMemzeroX86UnrestrictedCert, hptr]
    exact ⟨hb₁.trans ((congrArg (fun bs => fullSchedule n [⟨0, [], true⟩] memzeroX86EntryObs bs (memzeroX86ExitObs (s₁.gpr.get 4))) hsched).trans (by simpa only [c₂, ctMemzeroX86UnrestrictedCert, ← hsp] using hb₂.symm)),
      hb₁.trans hm₁.symm⟩
  exact ⟨hp, hni.1, hni.2, ha₁⟩

theorem ctMemzeroX86GuardedRun_pos (fetch : Nat → Option (DecodedInstr X86Instr)) (fuel : Nat)
    (s : X86State) (n : Word) (hn : n ≠ 0) (hc : s.gpr.get 6 = UInt64.ofBitVec n) :
    ctMemzeroX86GuardedRun fetch fuel s = runX86Fetch fetch fuel s := by
  have hg0 : ¬ ((s.gpr.get 6 == 0) = true) := by
    rw [beq_false_of_ne (hc ▸ (bv64_ne_zero_iff_u64_ne_zero n).mp hn)]; decide
  unfold ctMemzeroX86GuardedRun
  rw [ite_eq_right hg0]

/-- `qsag_asm_ct_memzero_x86_64`, raw symbol bytes, nonzero count: `runX86One zeroCode` halts
with the `n` bytes at `rdi` zeroed, and two runs with the same `rdi` and count emit the same
`StepObs` trace, equal to the trace of the FFI-wrapper-level loop. -/
theorem ct_memzero_x86_64_sydtv_refines_pos (s₁ s₂ : X86State) (fuel : Nat) (n : Word) (hn : n ≠ 0)
    (hpc₁ : s₁.pc = 0) (hh₁ : s₁.halted = false) (hc₁ : s₁.gpr.get 6 = UInt64.ofBitVec n)
    (hpc₂ : s₂.pc = 0) (hh₂ : s₂.halted = false) (hc₂ : s₂.gpr.get 6 = UInt64.ofBitVec n)
    (hptr : s₁.gpr.get 7 = s₂.gpr.get 7)
    (hfuel : 4 * n.toNat + 13 ≤ fuel)
    (hsp : s₁.gpr.get 4 = s₂.gpr.get 4) :
    MemzeroX86Post s₁ n (runX86One zeroCode fuel s₁).1 (asmFfiMemzeroX86Run (s₁.gpr.get 4) n (s₁.gpr.get 7) s₁.mem).1 ∧
    (runX86One zeroCode fuel s₁).2 = (runX86One zeroCode fuel s₂).2 ∧
    (runX86One zeroCode fuel s₁).2 = (asmFfiMemzeroX86Run (s₁.gpr.get 4) n (s₁.gpr.get 7) s₁.mem).2 := by
  have h := ct_memzero_x86_64_sydtv_refines_all_n s₁ s₂ fuel n hpc₁ hh₁ hc₁ hpc₂ hh₂ hc₂ hptr hfuel hsp
  dsimp only at h
  rw [ctMemzeroX86GuardedRun_pos _ fuel s₁ n hn hc₁, ctMemzeroX86GuardedRun_pos _ fuel s₂ n hn hc₂] at h
  simpa only [runX86One_eq, runArm64One_eq] using And.intro h.1 (And.intro h.2.1 h.2.2.1)

/-! ## §5. Kernel 2 — `qsag_asm_ct_memzero_aarch64` (AArch64 Post-Index Affine, Unrestricted `∀ n : Word`) -/

theorem ctMemzeroArm_fetch_decodeOne :
    ∀ d ∈ ctMemzeroArmProg, decodeArm64One armZeroCode d.offset = some d := by
  intro d hd
  have hall := ctMemzeroArm_decodeOne_all.2
  rw [List.all_eq_true] at hall
  have h := hall d hd
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

def memzeroArmBodyObs (p : UInt64) : List StepObs :=
  [⟨0, [(p, 1)], true⟩, ⟨4, [], true⟩, ⟨8, [], true⟩]

def memzeroArmExitObs : List StepObs := [⟨12, [], true⟩, ⟨16, [], true⟩]

def memzeroArmBodyStep (s : Arm64State) : Arm64State × List StepObs :=
  let p := armGet s.gpr 0
  let c := armGet s.gpr 1
  ({ s with
      pc := jccPc (!(c - 1 == 0)) 0 12
      gpr := armSet (armSet s.gpr 0 (p + 1)) 1 (c - 1)
      cf := decide (c.toNat ≥ 1)
      zf := c - 1 == 0
      mem := writeMem8 s.mem p 0 },
   memzeroArmBodyObs p)

def asmFfiMemzeroArmBodyStep (m : AsmFfiMemzero) : AsmFfiMemzero × List StepObs :=
  (⟨m.ptr + 1, m.remaining - 1, writeMem8 m.mem m.ptr 0⟩, memzeroArmBodyObs m.ptr)

theorem asmFfiMemzeroArm_cuts_mem (k : Nat) (p : UInt64) (rem : Nat) (mem : UInt64 → UInt8) :
    (runCuts asmFfiMemzeroArmBodyStep k ⟨p, rem, mem⟩).1.mem = zeroRange k mem p := by
  induction k generalizing p rem mem with
  | zero => simp [runCuts]
  | succ k ih =>
    simpa [runCuts, asmFfiMemzeroArmBodyStep, zeroRange_zero, zeroRange_succ] using ih (p + 1) (rem - 1) (writeMem8 mem p 0)

/-- Symbol execution behind a zero-count guard on `x1`. The guard branch is a hand-written
model of the Rust wrapper's early return on empty input, not decoded machine code. -/
def ctMemzeroArmGuardedRun (fetch : Nat → Option (DecodedInstr Arm64Instr))
    (fuel : Nat) (s : Arm64State) : Arm64State × List StepObs :=
  if armGet s.gpr 1 == 0 then ({ s with halted := true }, [⟨0, [], true⟩])
  else runArm64Fetch fetch fuel s

def asmFfiMemzeroArmRun (n : Word) (base : UInt64) (mem : UInt64 → UInt8) : AsmFfiMemzero × List StepObs :=
  if n = 0 then (⟨base, 0, mem⟩, [⟨0, [], true⟩])
  else
    let loop := runCuts asmFfiMemzeroArmBodyStep n.toNat ⟨base, n.toNat, mem⟩
    (loop.1, [] ++ loop.2 ++ memzeroArmExitObs)

theorem ctMemzeroArm_body_full (fetch : Nat → Option (DecodedInstr Arm64Instr))
    (hf0 : fetch 0 = some ⟨0, 4, .strbPost 31 0 1⟩)
    (hf4 : fetch 4 = some ⟨4, 4, .aluImm .subs true 1 1 1⟩)
    (hf8 : fetch 8 = some ⟨8, 4, .bCond 1 0⟩)
    (p c r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64) (hi : Bank16 UInt64)
    (v : Bank32 Vec128) (cf zf dit : Bool) (m : UInt64 → UInt8) (fuel : Nat) :
    let s : Arm64State := ⟨0, ⟨⟨p, c, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
      v, cf, zf, dit, false, m⟩
    runArm64Fetch fetch (3 + fuel) s =
      ((runArm64Fetch fetch fuel (memzeroArmBodyStep s).1).1,
       (memzeroArmBodyStep s).2 ++ (runArm64Fetch fetch fuel (memzeroArmBodyStep s).1).2) := by
  dsimp only
  rw [show 3 + fuel = ((fuel + 1) + 1) + 1 from by omega]
  rw [runArm64Fetch_step fetch _ _ _ rfl hf0]
  simp only [stepArm64Full_strbPost31_0, armGet_0, armSet_0]
  rw [runArm64Fetch_step fetch _ _ _ rfl hf4]
  simp only [stepArm64Full_subsImm1_1, armGet_1, armSet_1]
  rw [runArm64Fetch_step fetch _ _ _ rfl hf8]
  simp only [stepArm64Full_bne0, memzeroArmBodyStep, memzeroArmBodyObs, armGet_0, armGet_1, armSet_0, armSet_1]
  rfl

theorem ctMemzeroArm_exit_full (fetch : Nat → Option (DecodedInstr Arm64Instr))
    (hf12 : fetch 12 = some ⟨12, 4, .dmbIsh⟩)
    (hf16 : fetch 16 = some ⟨16, 4, .ret⟩)
    (g : Bank32 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool) (m : UInt64 → UInt8) (extra : Nat) :
    runArm64Fetch fetch (2 + extra) ⟨12, g, v, cf, zf, dit, false, m⟩ =
      (⟨16, g, v, cf, zf, dit, true, m⟩, memzeroArmExitObs) := by
  rw [show 2 + extra = (extra + 1) + 1 from by omega]
  rw [runArm64Fetch_step fetch _ _ _ rfl hf12]
  simp only [stepArm64Full_dmbIsh]
  rw [runArm64Fetch_step fetch _ _ _ rfl hf16]
  simp only [stepArm64Full_ret, memzeroArmExitObs]
  rw [runArm64Fetch_halted _ _ _ rfl]

def MemzeroArmRel (s₀ : Arm64State) (n v : Nat) (a : Arm64State) (m : AsmFfiMemzero) : Prop :=
  ∃ cf zf : Bool,
    a = ⟨if v = n then 12 else 0,
          armSet (armSet s₀.gpr 0 (ptrStride (armGet s₀.gpr 0) 1 v)) 1 (UInt64.ofNat (n - v)),
          s₀.vec, cf, zf, s₀.dit, false, m.mem⟩ ∧
    m.ptr = ptrStride (armGet s₀.gpr 0) 1 v ∧
    m.remaining = n - v

def MemzeroArmLoopPost (s₀ : Arm64State) (n : Nat) (a : Arm64State) (m : AsmFfiMemzero) : Prop :=
  ∃ cf zf : Bool,
    a = ⟨12, armSet (armSet s₀.gpr 0 (ptrStride (armGet s₀.gpr 0) 1 n)) 1 0,
          s₀.vec, cf, zf, s₀.dit, false, m.mem⟩ ∧
    m.remaining = 0

def MemzeroArmPost (s₀ : Arm64State) (n : Word) (out : Arm64State) (m : AsmFfiMemzero) : Prop :=
  out.halted = true ∧
  out.mem = m.mem ∧
  out.mem = zeroRange n.toNat s₀.mem (armGet s₀.gpr 0) ∧
  (∀ i < n.toNat, out.mem (armGet s₀.gpr 0 + UInt64.ofNat i) = 0) ∧
  (∀ addr, (∀ i < n.toNat, addr ≠ armGet s₀.gpr 0 + UInt64.ofNat i) → out.mem addr = s₀.mem addr) ∧
  out.vec = s₀.vec ∧
  out.dit = s₀.dit ∧
  out.gpr.hi = s₀.gpr.hi

def ctMemzeroArmPosCert (s₀ : Arm64State) (n : Nat) (hn : 0 < n) (hbound : n < 2 ^ 64)
    (h1 : armGet s₀.gpr 1 = UInt64.ofNat n) (hpc : s₀.pc = 0) (hh : s₀.halted = false) :
    LoopRelationCert Arm64State AsmFfiMemzero n memzeroArmBodyStep asmFfiMemzeroArmBodyStep
      s₀ ⟨armGet s₀.gpr 0, n, s₀.mem⟩ (MemzeroArmLoopPost s₀ n) where
  LoopRel := MemzeroArmRel s₀ n
  schedule := fun v => memzeroArmBodyObs (ptrStride (armGet s₀.gpr 0) 1 v)
  entry := by
    obtain ⟨pc, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
      v, cf, zf, dit, hlt, m⟩ := s₀
    cases hpc; cases hh
    refine ⟨cf, zf, ?_, rfl, by dsimp only; omega⟩
    have h1' : r1 = UInt64.ofNat n := h1
    subst h1'
    simp [ptrStride, Nat.ne_of_lt hn, armGet_0, armSet_0, armSet_1]
  body := by
    intro v a m hv ⟨cf, zf, ha, hmp, hmr⟩
    subst ha
    obtain ⟨_, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
      vec, _, _, dit, _, _⟩ := s₀
    have hpos : 0 < n - v := by omega
    have hlt : n - v < 2 ^ 64 := by omega
    have hdec := u64_ofNat_sub_one hpos hlt
    have hsub : n - v - 1 = n - (v + 1) := by omega
    have hzf : (UInt64.ofNat (n - (v + 1)) == 0) = decide (v + 1 = n) := by
      rw [u64_ofNat_eq_zero_iff (by omega)]
      by_cases heq : v + 1 = n <;> simp [heq] <;> omega
    have hjcc : jccPc (!(UInt64.ofNat (n - (v + 1)) == 0)) 0 12 = (if v + 1 = n then 12 else 0) := by
      rw [hzf]
      by_cases heq : v + 1 = n
      · rw [ite_eq_left heq, decide_eq_true heq]; rfl
      · rw [ite_eq_right heq, decide_eq_false heq]; rfl
    refine ⟨⟨decide ((UInt64.ofNat (n - v)).toNat ≥ 1), UInt64.ofNat (n - (v + 1)) == 0, ?_, ?_, ?_⟩, ?_, ?_⟩
    · simp only [memzeroArmBodyStep, asmFfiMemzeroArmBodyStep, armGet_0, armGet_1, armSet_0, armSet_1,
        hdec, hsub, hjcc, ptrStride, hmp]
    · simp [asmFfiMemzeroArmBodyStep, hmp, ptrStride]
    · simp [asmFfiMemzeroArmBodyStep, hmr]; omega
    · simp [memzeroArmBodyStep, armGet_0, armSet_0, armSet_1]
    · simp [asmFfiMemzeroArmBodyStep, hmp, armGet_0]
  exit := by
    intro a m ⟨cf, zf, ha, _, hmr⟩
    exact ⟨cf, zf, by simpa using ha, by omega⟩

theorem ctMemzeroArm_replay_loop (fetch : Nat → Option (DecodedInstr Arm64Instr))
    (hf0 : fetch 0 = some ⟨0, 4, .strbPost 31 0 1⟩)
    (hf4 : fetch 4 = some ⟨4, 4, .aluImm .subs true 1 1 1⟩)
    (hf8 : fetch 8 = some ⟨8, 4, .bCond 1 0⟩)
    (s₀ : Arm64State) (n : Nat) (hn : 0 < n) (hbound : n < 2 ^ 64)
    (h1 : armGet s₀.gpr 1 = UInt64.ofNat n) (hpc : s₀.pc = 0) (hh : s₀.halted = false)
    (rem : Nat) :
    ∀ v a m fuel, v + rem = n → MemzeroArmRel s₀ n v a m →
      runArm64Fetch fetch (3 * rem + fuel) a =
        let loop := runCuts memzeroArmBodyStep rem a
        let u := runArm64Fetch fetch fuel loop.1
        (u.1, loop.2 ++ u.2) := by
  induction rem with
  | zero => intro v a m fuel _ _; simp [runCuts]
  | succ k ih =>
    intro v a m fuel hv hrel
    have hvn : v < n := by omega
    rcases hrel with ⟨cf, zf, ha, hmp, hmr⟩
    have hrel' : MemzeroArmRel s₀ n v a m := ⟨cf, zf, ha, hmp, hmr⟩
    have hbody := (ctMemzeroArmPosCert s₀ n hn hbound h1 hpc hh).body v a m hvn hrel'
    obtain ⟨_, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
      vec, _, _, dit, _, _⟩ := s₀
    have ha0 : a = ⟨0, ⟨⟨ptrStride r0 1 v, UInt64.ofNat (n - v), r2, r3, r4, r5, r6, r7,
        r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩, vec, cf, zf, dit, false, m.mem⟩ := by
      simpa [Nat.ne_of_lt hvn, armGet_0, armSet_0, armSet_1] using ha
    rw [show 3 * (k + 1) + fuel = 3 + (3 * k + fuel) from by omega, ha0]
    rw [ctMemzeroArm_body_full fetch hf0 hf4 hf8]
    rw [← ha0]
    rw [ih (v + 1) (memzeroArmBodyStep a).1 (asmFfiMemzeroArmBodyStep m).1 fuel (by omega) hbody.1]
    simp [runCuts, List.append_assoc]

/-- Complete `UnrestrictedLoopCert` for `qsag_asm_ct_memzero_aarch64` over **all `n : BitVec 64`**. -/
def ctMemzeroArmUnrestrictedCert (fetch : Nat → Option (DecodedInstr Arm64Instr))
    (hf : ∀ d ∈ ctMemzeroArmProg, fetch d.offset = some d)
    (s₀ : Arm64State) (fuel : Nat) (hpc : s₀.pc = 0) (hh : s₀.halted = false)
    (n : Word) (hcount : armGet s₀.gpr 1 = UInt64.ofBitVec n)
    (hfuel : 3 * n.toNat + 2 ≤ fuel) :
    UnrestrictedLoopCert Arm64State AsmFfiMemzero n
      (ctMemzeroArmGuardedRun fetch fuel)
      (fun m => asmFfiMemzeroArmRun n m.ptr m.mem)
      memzeroArmBodyStep asmFfiMemzeroArmBodyStep
      s₀ ⟨armGet s₀.gpr 0, n.toNat, s₀.mem⟩
      s₀ ⟨armGet s₀.gpr 0, n.toNat, s₀.mem⟩
      (MemzeroArmLoopPost s₀ n.toNat)
      (MemzeroArmPost s₀ n) where
  zeroSchedule := [⟨0, [], true⟩]
  entrySchedule := []
  bodySchedule := fun v => memzeroArmBodyObs (ptrStride (armGet s₀.gpr 0) 1 v)
  exitSchedule := memzeroArmExitObs
  zero_cut := by
    intro hz; subst hz
    have hg0 : (armGet s₀.gpr 1 == 0) = true := by simp [hcount]
    dsimp only [ctMemzeroArmGuardedRun, asmFfiMemzeroArmRun]
    rw [ite_eq_left hg0, ite_eq_left rfl]
    refine ⟨⟨rfl, rfl, by simp, ?_, ?_, rfl, rfl, rfl⟩, rfl, rfl⟩
    · intro i hi; exact absurd hi (Nat.not_lt_zero i)
    · intro _ _; rfl
  pos_cert := by
    intro hn
    have h1 : armGet s₀.gpr 1 = UInt64.ofNat n.toNat := by
      apply u64_eq_of_toNat_eq
      rw [hcount, UInt64.toNat_ofNat', Nat.mod_eq_of_lt n.isLt]; rfl
    exact ctMemzeroArmPosCert s₀ n.toNat (bv64_pos_of_ne_zero n hn) n.isLt h1 hpc hh
  pos_sched := fun _ => rfl
  pos_replay := by
    intro hn hlp hal hml
    have hg0 : ¬ ((armGet s₀.gpr 1 == 0) = true) := by
      rw [beq_false_of_ne (hcount ▸ (bv64_ne_zero_iff_u64_ne_zero n).mp hn)]; decide
    dsimp only [ctMemzeroArmGuardedRun, asmFfiMemzeroArmRun]
    rw [ite_eq_right hg0, ite_eq_right hn]
    have hf0 := hf ⟨0, 4, .strbPost 31 0 1⟩ (by simp only [ctMemzeroArmProg_eq]; simp)
    have hf4 := hf ⟨4, 4, .aluImm .subs true 1 1 1⟩ (by simp only [ctMemzeroArmProg_eq]; simp)
    have hf8 := hf ⟨8, 4, .bCond 1 0⟩ (by simp only [ctMemzeroArmProg_eq]; simp)
    have hf12 := hf ⟨12, 4, .dmbIsh⟩ (by simp only [ctMemzeroArmProg_eq]; simp)
    have hf16 := hf ⟨16, 4, .ret⟩ (by simp only [ctMemzeroArmProg_eq]; simp)
    have h1 : armGet s₀.gpr 1 = UInt64.ofNat n.toNat := by
      apply u64_eq_of_toNat_eq
      rw [hcount, UInt64.toNat_ofNat', Nat.mod_eq_of_lt n.isLt]; rfl
    obtain ⟨extra, hextra⟩ : ∃ extra, fuel = 3 * n.toNat + (2 + extra) :=
      ⟨fuel - (3 * n.toNat + 2), by omega⟩
    rw [hextra]
    have hpos := bv64_pos_of_ne_zero n hn
    have hrep := ctMemzeroArm_replay_loop fetch hf0 hf4 hf8 s₀ n.toNat hpos n.isLt h1 hpc hh
      n.toNat 0 s₀ ⟨armGet s₀.gpr 0, n.toNat, s₀.mem⟩ (2 + extra) (by omega)
      (ctMemzeroArmPosCert s₀ n.toNat hpos n.isLt h1 hpc hh).entry
    dsimp only at hrep ⊢
    rw [hrep]
    rcases hlp with ⟨cfL, zfL, haL, _⟩
    rw [haL, ctMemzeroArm_exit_full fetch hf12 hf16]
    have hzr := asmFfiMemzeroArm_cuts_mem n.toNat (armGet s₀.gpr 0) n.toNat s₀.mem
    have hhi : (armSet (armSet s₀.gpr 0 (ptrStride (armGet s₀.gpr 0) 1 n.toNat)) 1 0).hi = s₀.gpr.hi := by
      obtain ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩ := s₀.gpr
      simp only [armSet_hi0, armSet_hi1]
    refine ⟨⟨rfl, rfl, hzr, ?_, ?_, rfl, rfl, hhi⟩, by simp, by simp⟩
    · intro i hi
      have h := zeroRange_inside n.toNat s₀.mem (armGet s₀.gpr 0) i hi
      rw [← hzr] at h; exact h
    · intro addr haddr
      have h := zeroRange_outside n.toNat s₀.mem (armGet s₀.gpr 0) addr haddr
      rw [← hzr] at h; exact h

/-- Refinement and `StepObs` noninterference for the guarded runner of `qsag_asm_ct_memzero_aarch64` at every
`n : BitVec 64`. For `n ≠ 0` the runner is byte-decoded execution of the symbol
(`ct_memzero_aarch64_sydtv_refines_pos`); for `n = 0` it is the modelled wrapper early return. -/
theorem ct_memzero_aarch64_sydtv_refines_all_n (s₁ s₂ : Arm64State) (fuel : Nat) (n : Word)
    (hpc₁ : s₁.pc = 0) (hh₁ : s₁.halted = false) (hc₁ : armGet s₁.gpr 1 = UInt64.ofBitVec n)
    (hpc₂ : s₂.pc = 0) (hh₂ : s₂.halted = false) (hc₂ : armGet s₂.gpr 1 = UInt64.ofBitVec n)
    (hptr : armGet s₁.gpr 0 = armGet s₂.gpr 0)
    (hfuel : 3 * n.toNat + 2 ≤ fuel) :
    let out₁ := ctMemzeroArmGuardedRun (decodeArm64One armZeroCode) fuel s₁
    let out₂ := ctMemzeroArmGuardedRun (decodeArm64One armZeroCode) fuel s₂
    let ffi₁ := asmFfiMemzeroArmRun n (armGet s₁.gpr 0) s₁.mem
    MemzeroArmPost s₁ n out₁.1 ffi₁.1 ∧ out₁.2 = out₂.2 ∧ out₁.2 = ffi₁.2 := by
  dsimp only
  let c₁ := ctMemzeroArmUnrestrictedCert (decodeArm64One armZeroCode) ctMemzeroArm_fetch_decodeOne
    s₁ fuel hpc₁ hh₁ n hc₁ hfuel
  let c₂ := ctMemzeroArmUnrestrictedCert (decodeArm64One armZeroCode) ctMemzeroArm_fetch_decodeOne
    s₂ fuel hpc₂ hh₂ n hc₂ hfuel
  obtain ⟨hp, _, _⟩ := unrestricted_loop_refinement_sound c₁
  have hsched : c₁.bodySchedule = c₂.bodySchedule := by
    funext v; simp [c₁, c₂, ctMemzeroArmUnrestrictedCert, hptr]
  obtain ⟨hni1, hni2⟩ := unrestricted_three_way_noninterference c₁ c₂ (by rfl) (by rfl) hsched (by rfl)
  exact ⟨hp, hni1, hni2⟩

theorem ctMemzeroArmGuardedRun_pos (fetch : Nat → Option (DecodedInstr Arm64Instr)) (fuel : Nat)
    (s : Arm64State) (n : Word) (hn : n ≠ 0) (hc : armGet s.gpr 1 = UInt64.ofBitVec n) :
    ctMemzeroArmGuardedRun fetch fuel s = runArm64Fetch fetch fuel s := by
  have hg0 : ¬ ((armGet s.gpr 1 == 0) = true) := by
    rw [beq_false_of_ne (hc ▸ (bv64_ne_zero_iff_u64_ne_zero n).mp hn)]; decide
  unfold ctMemzeroArmGuardedRun
  rw [ite_eq_right hg0]

/-- `qsag_asm_ct_memzero_aarch64`, raw symbol bytes, nonzero count. -/
theorem ct_memzero_aarch64_sydtv_refines_pos (s₁ s₂ : Arm64State) (fuel : Nat) (n : Word) (hn : n ≠ 0)
    (hpc₁ : s₁.pc = 0) (hh₁ : s₁.halted = false) (hc₁ : armGet s₁.gpr 1 = UInt64.ofBitVec n)
    (hpc₂ : s₂.pc = 0) (hh₂ : s₂.halted = false) (hc₂ : armGet s₂.gpr 1 = UInt64.ofBitVec n)
    (hptr : armGet s₁.gpr 0 = armGet s₂.gpr 0)
    (hfuel : 3 * n.toNat + 2 ≤ fuel) :
    MemzeroArmPost s₁ n (runArm64One armZeroCode fuel s₁).1
      (asmFfiMemzeroArmRun n (armGet s₁.gpr 0) s₁.mem).1 ∧
    (runArm64One armZeroCode fuel s₁).2 = (runArm64One armZeroCode fuel s₂).2 ∧
    (runArm64One armZeroCode fuel s₁).2 = (asmFfiMemzeroArmRun n (armGet s₁.gpr 0) s₁.mem).2 := by
  have h := ct_memzero_aarch64_sydtv_refines_all_n s₁ s₂ fuel n hpc₁ hh₁ hc₁ hpc₂ hh₂ hc₂ hptr hfuel
  dsimp only at h
  rw [ctMemzeroArmGuardedRun_pos _ fuel s₁ n hn hc₁, ctMemzeroArmGuardedRun_pos _ fuel s₂ n hn hc₂] at h
  simpa only [runX86One_eq, runArm64One_eq] using h

/-! ## §6. Kernel 3 — `qsag_asm_ct_eq_bytes_x86_64` (2-Pointer Affine + OR-of-XOR Accumulator, `∀ n : Word`) -/

theorem ctEqBytesX86_fetch_decodeOne :
    ∀ d ∈ ctCurrentEqBytesX86Prog, decodeX86One eqBytesCode d.offset = some d := by
  intro d hd
  have hall := ctEqBytesX86_decodeOne_all.2
  rw [List.all_eq_true] at hall
  have h := hall d hd
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

structure AsmFfiEqBytes where
  ptrA : UInt64
  ptrB : UInt64
  acc : UInt64
  remaining : Nat
  mem : UInt64 → UInt8
  result : UInt64 := 0

def eqBytesEntryObs : List StepObs := [⟨0, [], true⟩, ⟨2, [], true⟩]

def eqBytesBodyObs (pA pB : UInt64) : List StepObs :=
  [⟨5, [(pA, 1)], true⟩, ⟨9, [(pB, 1)], true⟩, ⟨13, [], true⟩, ⟨16, [], true⟩,
   ⟨19, [], true⟩, ⟨22, [], true⟩, ⟨25, [], true⟩, ⟨28, [], true⟩]

def eqBytesExitObs (rsp : UInt64) : List StepObs :=
  [⟨30, [], true⟩, ⟨33, [], true⟩, ⟨36, [], true⟩, ⟨39, [], true⟩, ⟨42, [], true⟩, ⟨44, [], true⟩,
   ⟨46, [], true⟩, ⟨48, [], true⟩, ⟨50, [], true⟩, ⟨53, [], true⟩, ⟨56, [], true⟩, ⟨59, [], true⟩,
   ⟨62, [(rsp, 8)], true⟩]

def eqAccStepVal (acc : UInt64) (x y : UInt8) : UInt64 :=
  maskGprWidth false (acc ||| byteDiff x y)

theorem eqAcc_snoc (k : Nat) (m : UInt64 → UInt8) (pA pB acc : UInt64) :
    eqAccStepVal (eqAcc k m pA pB acc) (m (ptrStride pA 1 k)) (m (ptrStride pB 1 k)) =
      eqAcc (k + 1) m pA pB acc := by
  induction k generalizing pA pB acc with
  | zero => rfl
  | succ k ih =>
    simp only [eqAcc, ptrStride_one_eq] at ih ⊢
    have hA : pA + UInt64.ofNat (k + 1) = pA + 1 + UInt64.ofNat k := (addr_succ pA k).symm
    have hB : pB + UInt64.ofNat (k + 1) = pB + 1 + UInt64.ofNat k := (addr_succ pB k).symm
    rw [hA, hB]
    exact ih (pA + 1) (pB + 1) (maskGprWidth false (acc ||| byteDiff (m pA) (m pB)))

def eqBytesBodyStep (s : X86State) : X86State × List StepObs :=
  let pA := s.gpr.get 7
  let pB := s.gpr.get 6
  let c := s.gpr.get 1
  let bA := maskGprWidth false (s.mem pA).toUInt64
  let bB := maskGprWidth false (s.mem pB).toUInt64
  let xr := maskGprWidth false (bA ^^^ bB)
  let acc' := maskGprWidth false (s.gpr.get 0 ||| xr)
  ({ s with
      pc := jccPc (!(c - 1 == 0)) 5 30
      gpr := (s.gpr.set 8 xr |>.set 9 bB |>.set 0 acc' |>.set 7 (pA + 1) |>.set 6 (pB + 1) |>.set 1 (c - 1))
      cf := false
      ofFlag := evalX86IncDecOf false true c
      zf := c - 1 == 0 },
   eqBytesBodyObs pA pB)

def asmFfiEqBytesBodyStep (m : AsmFfiEqBytes) : AsmFfiEqBytes × List StepObs :=
  (⟨m.ptrA + 1, m.ptrB + 1, eqAccStepVal m.acc (m.mem m.ptrA) (m.mem m.ptrB),
    m.remaining - 1, m.mem, 0⟩,
   eqBytesBodyObs m.ptrA m.ptrB)

/-- Symbol execution behind a zero-count guard on `rdx`. The guard branch is a hand-written
model of the Rust wrapper's early return on empty input, not decoded machine code. -/
def ctEqBytesGuardedRun (fetch : Nat → Option (DecodedInstr X86Instr))
    (fuel : Nat) (s : X86State) : X86State × List StepObs :=
  if s.gpr.get 2 == 0 then
    ({ s with pc := 62, gpr := (s.gpr.set 0 1 |>.set 1 0 |>.set 8 0 |>.set 9 0), halted := true },
     [⟨0, [], true⟩])
  else runX86Fetch fetch fuel s

def asmFfiEqBytesRun (rsp : UInt64) (n : Word) (baseA baseB : UInt64) (mem : UInt64 → UInt8) : AsmFfiEqBytes × List StepObs :=
  if n = 0 then
    (⟨baseA, baseB, 0, 0, mem, 1⟩, [⟨0, [], true⟩])
  else
    let loop := runCuts asmFfiEqBytesBodyStep n.toNat ⟨baseA, baseB, 0, n.toNat, mem, 0⟩
    let res : UInt64 := if loop.1.acc = 0 then 1 else 0
    ({ loop.1 with result := res }, eqBytesEntryObs ++ loop.2 ++ (eqBytesExitObs rsp))

section EqBytesFetch
variable (fetch : Nat → Option (DecodedInstr X86Instr))
  (hf0 : fetch 0 = some ⟨0, 2, .aluRegReg .xorOp false 0 0⟩)
  (hf2 : fetch 2 = some ⟨2, 3, .movRegReg true 1 2⟩)
  (hf5 : fetch 5 = some ⟨5, 4, .loadGpr 1 false 8 (.baseDisp 7 0)⟩)
  (hf9 : fetch 9 = some ⟨9, 4, .loadGpr 1 false 9 (.baseDisp 6 0)⟩)
  (hf13 : fetch 13 = some ⟨13, 3, .aluRegReg .xorOp false 8 9⟩)
  (hf16 : fetch 16 = some ⟨16, 3, .aluRegReg .orOp false 0 8⟩)
  (hf19 : fetch 19 = some ⟨19, 3, .incDec true true 7⟩)
  (hf22 : fetch 22 = some ⟨22, 3, .incDec true true 6⟩)
  (hf25 : fetch 25 = some ⟨25, 3, .incDec false true 1⟩)
  (hf28 : fetch 28 = some ⟨28, 2, .jcc 5 5⟩)
  (hf30 : fetch 30 = some ⟨30, 3, .aluImm .sub false 0 1⟩)
  (hf33 : fetch 33 = some ⟨33, 3, .shiftImm .shr false 0 31⟩)
  (hf36 : fetch 36 = some ⟨36, 3, .aluRegReg .xorOp false 8 8⟩)
  (hf39 : fetch 39 = some ⟨39, 3, .aluRegReg .xorOp false 9 9⟩)
  (hf42 : fetch 42 = some ⟨42, 2, .aluRegReg .xorOp false 7 7⟩)
  (hf44 : fetch 44 = some ⟨44, 2, .aluRegReg .xorOp false 6 6⟩)
  (hf46 : fetch 46 = some ⟨46, 2, .aluRegReg .xorOp false 2 2⟩)
  (hf48 : fetch 48 = some ⟨48, 2, .aluRegReg .xorOp false 1 1⟩)
  (hf50 : fetch 50 = some ⟨50, 3, .aluRegReg .xorOp false 8 8⟩)
  (hf53 : fetch 53 = some ⟨53, 3, .aluRegReg .xorOp false 9 9⟩)
  (hf56 : fetch 56 = some ⟨56, 3, .aluRegReg .xorOp false 10 10⟩)
  (hf59 : fetch 59 = some ⟨59, 3, .aluRegReg .xorOp false 11 11⟩)
  (hf62 : fetch 62 = some ⟨62, 1, .ret⟩)

include hf0 hf2 in
theorem ctEqBytes_entry_full (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) (fuel : Nat) :
    runX86Fetch fetch (2 + fuel)
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, m⟩ =
      let u := runX86Fetch fetch fuel
        ⟨5, ⟨0, r2, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, false, false, true, dy, false, m⟩
      (u.1, eqBytesEntryObs ++ u.2) := by
  rw [show 2 + fuel = (fuel + 1) + 1 from by omega]
  rw [runX86Fetch_step fetch _ _ _ rfl hf0]
  simp only [stepX86Full_xorRR, b16get_0, mask32_xor_self_eq, u64_zero_beq_true, b16set_0]
  rw [runX86Fetch_step fetch _ _ _ rfl hf2]
  simp only [stepX86Full_movRR, maskGprWidth_true, b16get_2, b16set_1, eqBytesEntryObs]
  rfl

include hf5 hf9 hf13 hf16 hf19 hf22 hf25 hf28 in
theorem ctEqBytes_body_full (acc c r2 r3 r4 r5 pB pA r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) (fuel : Nat) :
    let s : X86State := ⟨5, ⟨acc, c, r2, r3, r4, r5, pB, pA, r8, r9, r10, r11, r12, r13, r14, r15⟩,
      y, cf, o, zf, dy, false, m⟩
    runX86Fetch fetch (8 + fuel) s =
      ((runX86Fetch fetch fuel (eqBytesBodyStep s).1).1,
       (eqBytesBodyStep s).2 ++ (runX86Fetch fetch fuel (eqBytesBodyStep s).1).2) := by
  dsimp only
  rw [show 8 + fuel = (((((((fuel + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 from by omega]
  rw [runX86Fetch_step fetch _ _ _ rfl hf5]
  simp only [stepX86Full_load8, b16get_7, b16set_8]
  rw [runX86Fetch_step fetch _ _ _ rfl hf9]
  simp only [stepX86Full_load8, b16get_6, b16set_9]
  rw [runX86Fetch_step fetch _ _ _ rfl hf13]
  simp only [stepX86Full_xorRR, b16get_8, b16get_9, b16set_8]
  rw [runX86Fetch_step fetch _ _ _ rfl hf16]
  simp only [stepX86Full_orRR, b16get_0, b16get_8, b16set_0]
  rw [runX86Fetch_step fetch _ _ _ rfl hf19]
  simp only [stepX86Full_inc64, b16get_7, b16set_7]
  rw [runX86Fetch_step fetch _ _ _ rfl hf22]
  simp only [stepX86Full_inc64, b16get_6, b16set_6]
  rw [runX86Fetch_step fetch _ _ _ rfl hf25]
  simp only [stepX86Full_dec64, b16get_1, b16set_1]
  rw [runX86Fetch_step fetch _ _ _ rfl hf28]
  simp only [stepX86Full_jnz, eqBytesBodyStep, eqBytesBodyObs,
    b16get_0, b16get_1, b16get_6, b16get_7, b16set_0, b16set_1, b16set_6, b16set_7, b16set_8, b16set_9]
  rfl

include hf30 hf33 hf36 hf39 hf42 hf44 hf46 hf48 hf50 hf53 hf56 hf59 hf62 in
theorem ctEqBytes_exit_full (acc r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) (hA : acc.toNat < 256) (extra : Nat) :
    runX86Fetch fetch (13 + extra)
      ⟨30, ⟨acc, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, m⟩ =
      (⟨(readMem64 m r4).toNat, ⟨if acc = 0 then 1 else 0, 0, 0, r3, r4 + 8, r5, 0, 0, 0, 0, 0, 0, r12, r13, r14, r15⟩,
        y, false, false, true, dy, true, m⟩,
       (eqBytesExitObs r4)) := by
  rw [show 13 + extra = ((((((((((((extra + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 from by omega]
  rw [runX86Fetch_step fetch _ _ _ rfl hf30]
  simp only [stepX86Full_subImm32, b16get_0, b16set_0]
  rw [runX86Fetch_step fetch _ _ _ rfl hf33]
  simp only [stepX86Full_shr32_31, b16get_0, b16set_0, eqTail_spec acc hA]
  rw [runX86Fetch_step fetch _ _ _ rfl hf36]
  simp only [stepX86Full_xorRR, b16get_8, mask32_xor_self_eq, u64_zero_beq_true, b16set_8]
  rw [runX86Fetch_step fetch _ _ _ rfl hf39]
  simp only [stepX86Full_xorRR, b16get_9, mask32_xor_self_eq, u64_zero_beq_true, b16set_9]
  rw [runX86Fetch_step fetch _ _ _ rfl hf42]
  simp only [stepX86Full_xorRR, b16get_7, mask32_xor_self_eq, u64_zero_beq_true, b16set_7]
  rw [runX86Fetch_step fetch _ _ _ rfl hf44]
  simp only [stepX86Full_xorRR, b16get_6, mask32_xor_self_eq, u64_zero_beq_true, b16set_6]
  rw [runX86Fetch_step fetch _ _ _ rfl hf46]
  simp only [stepX86Full_xorRR, b16get_2, mask32_xor_self_eq, u64_zero_beq_true, b16set_2]
  rw [runX86Fetch_step fetch _ _ _ rfl hf48]
  simp only [stepX86Full_xorRR, b16get_1, mask32_xor_self_eq, u64_zero_beq_true, b16set_1]
  rw [runX86Fetch_step fetch _ _ _ rfl hf50]
  simp only [stepX86Full_xorRR, b16get_8, mask32_xor_self_eq, u64_zero_beq_true, b16set_8]
  rw [runX86Fetch_step fetch _ _ _ rfl hf53]
  simp only [stepX86Full_xorRR, b16get_9, mask32_xor_self_eq, u64_zero_beq_true, b16set_9]
  rw [runX86Fetch_step fetch _ _ _ rfl hf56]
  simp only [stepX86Full_xorRR, b16get_10, mask32_xor_self_eq, u64_zero_beq_true, b16set_10]
  rw [runX86Fetch_step fetch _ _ _ rfl hf59]
  simp only [stepX86Full_xorRR, b16get_11, mask32_xor_self_eq, u64_zero_beq_true, b16set_11]
  rw [runX86Fetch_step fetch _ _ _ rfl hf62]
  simp only [stepX86Full_ret, b16get_4, b16set_4, eqBytesExitObs]
  rw [runX86Fetch_halted _ _ _ rfl]

end EqBytesFetch

def EqBytesRel (s₀ : X86State) (n v : Nat) (a : X86State) (m : AsmFfiEqBytes) : Prop :=
  let baseA := s₀.gpr.get 7
  let baseB := s₀.gpr.get 6
  ∃ cf o zf : Bool, ∃ x8 x9 : UInt64,
    a = ⟨if v = n then 30 else 5,
          (s₀.gpr.set 8 x8 |>.set 9 x9 |>.set 0 (eqAcc v s₀.mem baseA baseB 0)
            |>.set 7 (ptrStride baseA 1 v) |>.set 6 (ptrStride baseB 1 v)
            |>.set 1 (UInt64.ofNat (n - v))),
          s₀.ymm, cf, o, zf, s₀.ymmDirty, false, s₀.mem⟩ ∧
    m.ptrA = ptrStride baseA 1 v ∧
    m.ptrB = ptrStride baseB 1 v ∧
    m.acc = eqAcc v s₀.mem baseA baseB 0 ∧
    m.remaining = n - v ∧
    m.mem = s₀.mem

def EqBytesLoopPost (s₀ : X86State) (n : Nat) (a : X86State) (m : AsmFfiEqBytes) : Prop :=
  let baseA := s₀.gpr.get 7
  let baseB := s₀.gpr.get 6
  ∃ cf o zf : Bool, ∃ x8 x9 : UInt64,
    a = ⟨30,
          (s₀.gpr.set 8 x8 |>.set 9 x9 |>.set 0 (eqAcc n s₀.mem baseA baseB 0)
            |>.set 7 (ptrStride baseA 1 n) |>.set 6 (ptrStride baseB 1 n) |>.set 1 0),
          s₀.ymm, cf, o, zf, s₀.ymmDirty, false, s₀.mem⟩ ∧
    m.acc = eqAcc n s₀.mem baseA baseB 0 ∧
    m.remaining = 0

def EqBytesPost (s₀ : X86State) (n : Word) (out : X86State) (m : AsmFfiEqBytes) : Prop :=
  let baseA := s₀.gpr.get 7
  let baseB := s₀.gpr.get 6
  out.halted = true ∧
  out.mem = s₀.mem ∧
  out.gpr.get 0 = m.result ∧
  out.gpr.get 0 = (if ∀ i < n.toNat, s₀.mem (baseA + UInt64.ofNat i) = s₀.mem (baseB + UInt64.ofNat i) then 1 else 0) ∧
  out.gpr.get 1 = 0 ∧ out.gpr.get 8 = 0 ∧ out.gpr.get 9 = 0 ∧
  out.gpr.get 4 = (if n = 0 then s₀.gpr.get 4 else s₀.gpr.get 4 + 8) ∧ out.gpr.get 3 = s₀.gpr.get 3 ∧ out.gpr.get 5 = s₀.gpr.get 5 ∧
  (∀ r, 12 ≤ r → r < 16 → out.gpr.get r = s₀.gpr.get r) ∧
  (n ≠ 0 → out.gpr.get 2 = 0 ∧ out.gpr.get 6 = 0 ∧ out.gpr.get 7 = 0 ∧ out.gpr.get 10 = 0 ∧
    out.gpr.get 11 = 0)

def ctEqBytesPosCert (s₀ : X86State) (n : Nat) (hn : 0 < n) (hbound : n < 2 ^ 64) :
    LoopRelationCert X86State AsmFfiEqBytes n eqBytesBodyStep asmFfiEqBytesBodyStep
      ⟨5, (s₀.gpr.set 0 0 |>.set 1 (UInt64.ofNat n)), s₀.ymm, false, false, true, s₀.ymmDirty, false, s₀.mem⟩
      ⟨s₀.gpr.get 7, s₀.gpr.get 6, 0, n, s₀.mem, 0⟩
      (EqBytesLoopPost s₀ n) where
  LoopRel := EqBytesRel s₀ n
  schedule := fun v => eqBytesBodyObs (ptrStride (s₀.gpr.get 7) 1 v) (ptrStride (s₀.gpr.get 6) 1 v)
  entry := by
    obtain ⟨_, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, _, _, _, dy, _, m⟩ := s₀
    refine ⟨false, false, true, r8, r9, ?_, rfl, rfl, rfl, by dsimp only; omega, rfl⟩
    simp [ptrStride, eqAcc, Nat.ne_of_lt hn, b16get_6, b16get_7, b16set_0, b16set_1, b16set_6, b16set_7, b16set_8, b16set_9]
  body := by
    intro v a m hv ⟨cf, o, zf, x8, x9, ha, hpA, hpB, hacc, hmr, hmem⟩
    subst ha
    obtain ⟨_, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, _, _, _, dy, _, mem⟩ := s₀
    have hpos : 0 < n - v := by omega
    have hlt : n - v < 2 ^ 64 := by omega
    have hdec := u64_ofNat_sub_one hpos hlt
    have hsub : n - v - 1 = n - (v + 1) := by omega
    have hzf : (UInt64.ofNat (n - (v + 1)) == 0) = decide (v + 1 = n) := by
      rw [u64_ofNat_eq_zero_iff (by omega)]
      by_cases heq : v + 1 = n <;> simp [heq] <;> omega
    have hjcc : jccPc (!(UInt64.ofNat (n - (v + 1)) == 0)) 5 30 = (if v + 1 = n then 30 else 5) := by
      rw [hzf]
      by_cases heq : v + 1 = n <;> simp [heq, jccPc]
    have hsnoc := eqAcc_snoc v mem r7 r6 0
    refine ⟨⟨false, evalX86IncDecOf false true (UInt64.ofNat (n - v)), UInt64.ofNat (n - (v + 1)) == 0,
      byteDiff (mem (ptrStride r7 1 v)) (mem (ptrStride r6 1 v)),
      maskGprWidth false (mem (ptrStride r6 1 v)).toUInt64,
      ?_, ?_, ?_, ?_, ?_, hmem⟩, ?_, ?_⟩
    · simp only [eqBytesBodyStep, b16get_0, b16get_1, b16get_6, b16get_7,
        b16set_0, b16set_1, b16set_6, b16set_7, b16set_8, b16set_9,
        hdec, hsub, hjcc, ptrStride]
      change _ = _
      rw [← hsnoc]
      simp only [eqAccStepVal, byteDiff_unfold]
    · simp [asmFfiEqBytesBodyStep, hpA, ptrStride, b16get_7]
    · simp [asmFfiEqBytesBodyStep, hpB, ptrStride, b16get_6]
    · simp only [asmFfiEqBytesBodyStep, hacc, hpA, hpB, hmem, b16get_6, b16get_7, hsnoc]
    · simp [asmFfiEqBytesBodyStep, hmr]; omega
    · simp [eqBytesBodyStep, b16get_6, b16get_7, b16set_0, b16set_1, b16set_6, b16set_7, b16set_8, b16set_9]
    · simp [asmFfiEqBytesBodyStep, hpA, hpB, b16get_6, b16get_7]
  exit := by
    intro a m ⟨cf, o, zf, x8, x9, ha, _, _, hacc, hmr, _⟩
    exact ⟨cf, o, zf, x8, x9, by simpa using ha, hacc, by omega⟩

theorem ctEqBytes_replay_loop (fetch : Nat → Option (DecodedInstr X86Instr))
    (hf5 : fetch 5 = some ⟨5, 4, .loadGpr 1 false 8 (.baseDisp 7 0)⟩)
    (hf9 : fetch 9 = some ⟨9, 4, .loadGpr 1 false 9 (.baseDisp 6 0)⟩)
    (hf13 : fetch 13 = some ⟨13, 3, .aluRegReg .xorOp false 8 9⟩)
    (hf16 : fetch 16 = some ⟨16, 3, .aluRegReg .orOp false 0 8⟩)
    (hf19 : fetch 19 = some ⟨19, 3, .incDec true true 7⟩)
    (hf22 : fetch 22 = some ⟨22, 3, .incDec true true 6⟩)
    (hf25 : fetch 25 = some ⟨25, 3, .incDec false true 1⟩)
    (hf28 : fetch 28 = some ⟨28, 2, .jcc 5 5⟩)
    (s₀ : X86State) (n : Nat) (hn : 0 < n) (hbound : n < 2 ^ 64) (rem : Nat) :
    ∀ v a m fuel, v + rem = n → EqBytesRel s₀ n v a m →
      runX86Fetch fetch (8 * rem + fuel) a =
        let loop := runCuts eqBytesBodyStep rem a
        let u := runX86Fetch fetch fuel loop.1
        (u.1, loop.2 ++ u.2) := by
  induction rem with
  | zero => intro v a m fuel _ _; simp [runCuts]
  | succ k ih =>
    intro v a m fuel hv hrel
    have hvn : v < n := by omega
    rcases hrel with ⟨cf, o, zf, x8, x9, ha, hpA, hpB, hacc, hmr, hmem⟩
    have hrel' : EqBytesRel s₀ n v a m := ⟨cf, o, zf, x8, x9, ha, hpA, hpB, hacc, hmr, hmem⟩
    have hbody := (ctEqBytesPosCert s₀ n hn hbound).body v a m hvn hrel'
    obtain ⟨_, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, _, _, _, dy, _, mem⟩ := s₀
    have ha5 : a = ⟨5, ⟨eqAcc v mem r7 r6 0, UInt64.ofNat (n - v), r2, r3, r4, r5,
        ptrStride r6 1 v, ptrStride r7 1 v, x8, x9, r10, r11, r12, r13, r14, r15⟩,
        y, cf, o, zf, dy, false, mem⟩ := by
      simpa [Nat.ne_of_lt hvn, b16get_6, b16get_7, b16set_0, b16set_1, b16set_6, b16set_7, b16set_8, b16set_9] using ha
    rw [show 8 * (k + 1) + fuel = 8 + (8 * k + fuel) from by omega, ha5]
    rw [ctEqBytes_body_full fetch hf5 hf9 hf13 hf16 hf19 hf22 hf25 hf28]
    rw [← ha5]
    rw [ih (v + 1) (eqBytesBodyStep a).1 (asmFfiEqBytesBodyStep m).1 fuel (by omega) hbody.1]
    simp [runCuts, List.append_assoc]

/-- Complete `UnrestrictedLoopCert` for `qsag_asm_ct_eq_bytes_x86_64` over **all `n : BitVec 64`**. -/
def ctEqBytesX86UnrestrictedCert (fetch : Nat → Option (DecodedInstr X86Instr))
    (hf : ∀ d ∈ ctCurrentEqBytesX86Prog, fetch d.offset = some d)
    (s₀ : X86State) (fuel : Nat) (hpc : s₀.pc = 0) (hh : s₀.halted = false)
    (n : Word) (hcount : s₀.gpr.get 2 = UInt64.ofBitVec n)
    (hfuel : 8 * n.toNat + 15 ≤ fuel) :
    UnrestrictedLoopCert X86State AsmFfiEqBytes n
      (ctEqBytesGuardedRun fetch fuel)
      (fun m => asmFfiEqBytesRun (s₀.gpr.get 4) n m.ptrA m.ptrB m.mem)
      eqBytesBodyStep asmFfiEqBytesBodyStep
      s₀ ⟨s₀.gpr.get 7, s₀.gpr.get 6, 0, n.toNat, s₀.mem, 0⟩
      ⟨5, (s₀.gpr.set 0 0 |>.set 1 (UInt64.ofNat n.toNat)), s₀.ymm, false, false, true, s₀.ymmDirty, false, s₀.mem⟩
      ⟨s₀.gpr.get 7, s₀.gpr.get 6, 0, n.toNat, s₀.mem, 0⟩
      (EqBytesLoopPost s₀ n.toNat)
      (EqBytesPost s₀ n) where
  zeroSchedule := [⟨0, [], true⟩]
  entrySchedule := eqBytesEntryObs
  bodySchedule := fun v => eqBytesBodyObs (ptrStride (s₀.gpr.get 7) 1 v) (ptrStride (s₀.gpr.get 6) 1 v)
  exitSchedule := (eqBytesExitObs (s₀.gpr.get 4))
  zero_cut := by
    intro hz; subst hz
    have hg0 : (s₀.gpr.get 2 == 0) = true := by simp [hcount]
    dsimp only [ctEqBytesGuardedRun, asmFfiEqBytesRun]
    rw [ite_eq_left hg0, ite_eq_left rfl]
    obtain ⟨_, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, _, _, _, _, _, _, mem⟩ := s₀
    have hvac : (∀ i < (0 : Word).toNat, mem (r7 + UInt64.ofNat i) = mem (r6 + UInt64.ofNat i)) := by
      intro i hi; exact absurd hi (Nat.not_lt_zero i)
    refine ⟨?_, rfl, rfl⟩
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun h => absurd rfl h⟩
    · rfl
    · exact (ite_eq_left hvac).symm
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · intro r h12 h16
      match r, h12, h16 with
      | 12, _, _ => rfl | 13, _, _ => rfl | 14, _, _ => rfl | 15, _, _ => rfl
      | r + 16, _, h => exact absurd h (by omega)
  pos_cert := fun hn =>
    ctEqBytesPosCert s₀ n.toNat (bv64_pos_of_ne_zero n hn) n.isLt
  pos_sched := fun _ => rfl
  pos_replay := by
    intro hn hlp hal hml
    have hg0 : ¬ ((s₀.gpr.get 2 == 0) = true) := by
      rw [beq_false_of_ne (hcount ▸ (bv64_ne_zero_iff_u64_ne_zero n).mp hn)]; decide
    dsimp only [ctEqBytesGuardedRun, asmFfiEqBytesRun]
    rw [ite_eq_right hg0, ite_eq_right hn]
    have hf0 := hf ⟨0, 2, .aluRegReg .xorOp false 0 0⟩ (by simp only [ctCurrentEqBytesX86Prog_eq]; simp)
    have hf2 := hf ⟨2, 3, .movRegReg true 1 2⟩ (by simp only [ctCurrentEqBytesX86Prog_eq]; simp)
    have hf5 := hf ⟨5, 4, .loadGpr 1 false 8 (.baseDisp 7 0)⟩ (by simp only [ctCurrentEqBytesX86Prog_eq]; simp)
    have hf9 := hf ⟨9, 4, .loadGpr 1 false 9 (.baseDisp 6 0)⟩ (by simp only [ctCurrentEqBytesX86Prog_eq]; simp)
    have hf13 := hf ⟨13, 3, .aluRegReg .xorOp false 8 9⟩ (by simp only [ctCurrentEqBytesX86Prog_eq]; simp)
    have hf16 := hf ⟨16, 3, .aluRegReg .orOp false 0 8⟩ (by simp only [ctCurrentEqBytesX86Prog_eq]; simp)
    have hf19 := hf ⟨19, 3, .incDec true true 7⟩ (by simp only [ctCurrentEqBytesX86Prog_eq]; simp)
    have hf22 := hf ⟨22, 3, .incDec true true 6⟩ (by simp only [ctCurrentEqBytesX86Prog_eq]; simp)
    have hf25 := hf ⟨25, 3, .incDec false true 1⟩ (by simp only [ctCurrentEqBytesX86Prog_eq]; simp)
    have hf28 := hf ⟨28, 2, .jcc 5 5⟩ (by simp only [ctCurrentEqBytesX86Prog_eq]; simp)
    have hf30 := hf ⟨30, 3, .aluImm .sub false 0 1⟩ (by simp only [ctCurrentEqBytesX86Prog_eq]; simp)
    have hf33 := hf ⟨33, 3, .shiftImm .shr false 0 31⟩ (by simp only [ctCurrentEqBytesX86Prog_eq]; simp)
    have hf36 := hf ⟨36, 3, .aluRegReg .xorOp false 8 8⟩ (by simp only [ctCurrentEqBytesX86Prog_eq]; simp)
    have hf39 := hf ⟨39, 3, .aluRegReg .xorOp false 9 9⟩ (by simp only [ctCurrentEqBytesX86Prog_eq]; simp)
    have hf42 := hf ⟨42, 2, .aluRegReg .xorOp false 7 7⟩ (by simp only [ctCurrentEqBytesX86Prog_eq]; simp)
    have hf44 := hf ⟨44, 2, .aluRegReg .xorOp false 6 6⟩ (by simp only [ctCurrentEqBytesX86Prog_eq]; simp)
    have hf46 := hf ⟨46, 2, .aluRegReg .xorOp false 2 2⟩ (by simp only [ctCurrentEqBytesX86Prog_eq]; simp)
    have hf48 := hf ⟨48, 2, .aluRegReg .xorOp false 1 1⟩ (by simp only [ctCurrentEqBytesX86Prog_eq]; simp)
    have hf50 := hf ⟨50, 3, .aluRegReg .xorOp false 8 8⟩ (by simp only [ctCurrentEqBytesX86Prog_eq]; simp)
    have hf53 := hf ⟨53, 3, .aluRegReg .xorOp false 9 9⟩ (by simp only [ctCurrentEqBytesX86Prog_eq]; simp)
    have hf56 := hf ⟨56, 3, .aluRegReg .xorOp false 10 10⟩ (by simp only [ctCurrentEqBytesX86Prog_eq]; simp)
    have hf59 := hf ⟨59, 3, .aluRegReg .xorOp false 11 11⟩ (by simp only [ctCurrentEqBytesX86Prog_eq]; simp)
    have hf62 := hf ⟨62, 1, .ret⟩ (by simp only [ctCurrentEqBytesX86Prog_eq]; simp)
    obtain ⟨extra, hextra⟩ : ∃ extra, fuel = 2 + (8 * n.toNat + (13 + extra)) :=
      ⟨fuel - (8 * n.toNat + 15), by omega⟩
    rw [hextra]
    obtain ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
      y, cf, o, zf, dy, hlt, m⟩ := s₀
    cases hpc; cases hh
    have hr2 : r2 = UInt64.ofNat n.toNat := by
      apply u64_eq_of_toNat_eq
      have : r2 = UInt64.ofBitVec n := hcount
      rw [this, UInt64.toNat_ofNat', Nat.mod_eq_of_lt n.isLt]; rfl
    rw [ctEqBytes_entry_full fetch hf0 hf2]
    have headEq : (⟨5, ⟨0, r2, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        y, false, false, true, dy, false, m⟩ : X86State) =
      ⟨5, ((Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15).set 0 0 |>.set 1 (UInt64.ofNat n.toNat)),
        y, false, false, true, dy, false, m⟩ := by
      simp [hr2, b16set_0, b16set_1]
    rw [headEq]
    have hpos := bv64_pos_of_ne_zero n hn
    have hrep := ctEqBytes_replay_loop fetch hf5 hf9 hf13 hf16 hf19 hf22 hf25 hf28
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, m⟩
      n.toNat hpos n.isLt n.toNat 0 _ ⟨r7, r6, 0, n.toNat, m, 0⟩ (13 + extra) (by omega)
      (ctEqBytesPosCert _ n.toNat hpos n.isLt).entry
    dsimp only at hrep ⊢
    rw [hrep]
    rcases hlp with ⟨cfL, oL, zfL, x8L, x9L, haL, haccL, _⟩
    have hspec := eqAcc_spec m n.toNat r7 r6 0 (by decide)
    have ha30 : (runCuts eqBytesBodyStep n.toNat
        ⟨5, ((Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15).set 0 0 |>.set 1 (UInt64.ofNat n.toNat)),
          y, false, false, true, dy, false, m⟩).1 =
      ⟨30, ⟨eqAcc n.toNat m r7 r6 0, 0, r2, r3, r4, r5, ptrStride r6 1 n.toNat, ptrStride r7 1 n.toNat,
        x8L, x9L, r10, r11, r12, r13, r14, r15⟩, y, cfL, oL, zfL, dy, false, m⟩ := by
      simpa [b16get_6, b16get_7, b16set_0, b16set_1, b16set_6, b16set_7, b16set_8, b16set_9] using haL
    rw [ha30, ctEqBytes_exit_full fetch hf30 hf33 hf36 hf39 hf42 hf44 hf46 hf48 hf50 hf53 hf56 hf59 hf62 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hspec.1]
    have hiff : (eqAcc n.toNat m r7 r6 0 = 0) ↔
        (∀ i < n.toNat, m (r7 + UInt64.ofNat i) = m (r6 + UInt64.ofNat i)) := by
      constructor
      · intro h0; exact (hspec.2.mp h0).2
      · intro hall; exact hspec.2.mpr ⟨rfl, hall⟩
    have hres : (if eqAcc n.toNat m r7 r6 0 = 0 then (1 : UInt64) else 0) =
        (if ∀ i < n.toNat, m (r7 + UInt64.ofNat i) = m (r6 + UInt64.ofNat i) then 1 else 0) := by
      by_cases h0 : eqAcc n.toNat m r7 r6 0 = 0
      · rw [ite_eq_left h0, ite_eq_left (hiff.mp h0)]
      · rw [ite_eq_right h0, ite_eq_right (fun hall => h0 (hiff.mpr hall))]
    refine ⟨?_, by simp only [List.append_assoc]; rfl, rfl⟩
    dsimp only [EqBytesPost]
    rw [ite_eq_right hn]
    refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_, fun _ => ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
    · simp [b16get_0, b16get_6, b16get_7] at haccL ⊢; rw [haccL]
    · simp [b16get_0, b16get_6, b16get_7, hres]
    · intro r h12 h16
      match r, h12, h16 with
      | 12, _, _ => rfl | 13, _, _ => rfl | 14, _, _ => rfl | 15, _, _ => rfl
      | r + 16, _, h => exact absurd h (by omega)

/-- Refinement and `StepObs` noninterference for the guarded runner of `qsag_asm_ct_eq_bytes_x86_64` at every
`n : BitVec 64`. For `n ≠ 0` the runner is byte-decoded execution of the symbol
(`ct_eq_bytes_x86_64_sydtv_refines_pos`); for `n = 0` it is the modelled wrapper early return. -/
theorem ct_eq_bytes_x86_64_sydtv_refines_all_n (s₁ s₂ : X86State) (fuel : Nat) (n : Word)
    (hpc₁ : s₁.pc = 0) (hh₁ : s₁.halted = false) (hc₁ : s₁.gpr.get 2 = UInt64.ofBitVec n)
    (hpc₂ : s₂.pc = 0) (hh₂ : s₂.halted = false) (hc₂ : s₂.gpr.get 2 = UInt64.ofBitVec n)
    (hpA : s₁.gpr.get 7 = s₂.gpr.get 7) (hpB : s₁.gpr.get 6 = s₂.gpr.get 6)
    (hfuel : 8 * n.toNat + 15 ≤ fuel)
    (hsp : s₁.gpr.get 4 = s₂.gpr.get 4) :
    let out₁ := ctEqBytesGuardedRun (decodeX86One eqBytesCode) fuel s₁
    let out₂ := ctEqBytesGuardedRun (decodeX86One eqBytesCode) fuel s₂
    let ffi₁ := asmFfiEqBytesRun (s₁.gpr.get 4) n (s₁.gpr.get 7) (s₁.gpr.get 6) s₁.mem
    EqBytesPost s₁ n out₁.1 ffi₁.1 ∧ out₁.2 = out₂.2 ∧ out₁.2 = ffi₁.2 := by
  dsimp only
  let c₁ := ctEqBytesX86UnrestrictedCert (decodeX86One eqBytesCode) ctEqBytesX86_fetch_decodeOne
    s₁ fuel hpc₁ hh₁ n hc₁ hfuel
  let c₂ := ctEqBytesX86UnrestrictedCert (decodeX86One eqBytesCode) ctEqBytesX86_fetch_decodeOne
    s₂ fuel hpc₂ hh₂ n hc₂ hfuel
  obtain ⟨hp, _, _⟩ := unrestricted_loop_refinement_sound c₁
  have hsched : c₁.bodySchedule = c₂.bodySchedule := by
    funext v; simp [c₁, c₂, ctEqBytesX86UnrestrictedCert, hpA, hpB]
  obtain ⟨hni1, hni2⟩ := unrestricted_three_way_noninterference c₁ c₂ rfl rfl hsched (by simp [c₁, c₂, ctEqBytesX86UnrestrictedCert, hsp])
  exact ⟨hp, hni1, hni2⟩

theorem ctEqBytesGuardedRun_pos (fetch : Nat → Option (DecodedInstr X86Instr)) (fuel : Nat)
    (s : X86State) (n : Word) (hn : n ≠ 0) (hc : s.gpr.get 2 = UInt64.ofBitVec n) :
    ctEqBytesGuardedRun fetch fuel s = runX86Fetch fetch fuel s := by
  have hg0 : ¬ ((s.gpr.get 2 == 0) = true) := by
    rw [beq_false_of_ne (hc ▸ (bv64_ne_zero_iff_u64_ne_zero n).mp hn)]; decide
  unfold ctEqBytesGuardedRun
  rw [ite_eq_right hg0]

/-- `qsag_asm_ct_eq_bytes_x86_64`, raw symbol bytes, nonzero count. -/
theorem ct_eq_bytes_x86_64_sydtv_refines_pos (s₁ s₂ : X86State) (fuel : Nat) (n : Word) (hn : n ≠ 0)
    (hpc₁ : s₁.pc = 0) (hh₁ : s₁.halted = false) (hc₁ : s₁.gpr.get 2 = UInt64.ofBitVec n)
    (hpc₂ : s₂.pc = 0) (hh₂ : s₂.halted = false) (hc₂ : s₂.gpr.get 2 = UInt64.ofBitVec n)
    (hpA : s₁.gpr.get 7 = s₂.gpr.get 7) (hpB : s₁.gpr.get 6 = s₂.gpr.get 6)
    (hfuel : 8 * n.toNat + 15 ≤ fuel)
    (hsp : s₁.gpr.get 4 = s₂.gpr.get 4) :
    EqBytesPost s₁ n (runX86One eqBytesCode fuel s₁).1
      (asmFfiEqBytesRun (s₁.gpr.get 4) n (s₁.gpr.get 7) (s₁.gpr.get 6) s₁.mem).1 ∧
    (runX86One eqBytesCode fuel s₁).2 = (runX86One eqBytesCode fuel s₂).2 ∧
    (runX86One eqBytesCode fuel s₁).2 = (asmFfiEqBytesRun (s₁.gpr.get 4) n (s₁.gpr.get 7) (s₁.gpr.get 6) s₁.mem).2 := by
  have h := ct_eq_bytes_x86_64_sydtv_refines_all_n s₁ s₂ fuel n hpc₁ hh₁ hc₁ hpc₂ hh₂ hc₂ hpA hpB hfuel hsp
  dsimp only at h
  rw [ctEqBytesGuardedRun_pos _ fuel s₁ n hn hc₁, ctEqBytesGuardedRun_pos _ fuel s₂ n hn hc₂] at h
  simpa only [runX86One_eq, runArm64One_eq] using h

/-! ## §7. Kernel 4 — `qsag_asm_gf256_shamir_mac_gfni` (2-Pointer 32B Affine + GFNI SIMD MAC, `∀ n : Word`) -/

theorem gfniShamirMac_fetch_decodeOne :
    ∀ d ∈ gfniShamirMacProg, decodeX86One gfniShamirMacCode d.offset = some d := by
  intro d hd
  have hall := gfniShamirMac_decodeOne_all.2
  rw [List.all_eq_true] at hall
  have h := hall d hd
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

def t3MatVec : Vec256 := bcastQword256 0x71500a8a86be78ce
def t3InvMatVec : Vec256 := bcastQword256 0xa1e4f8e072a2700c

def gfniScaledCoeff (scalar : UInt64) : Vec256 :=
  gfniAffineVec256 (bcastByte256 (maskGprWidth false scalar).toUInt8) t3MatVec 0

def gfniShamirMacBlock (coeff shareVec accVec : Vec256) : Vec256 :=
  let sT3 := gfniAffineVec256 shareVec t3MatVec 0
  let prodT3 := evalVecBin256 .vgf2p8mulb sT3 coeff
  let prod := gfniAffineVec256 prodT3 t3InvMatVec 0
  evalVecBin256 .vpxor accVec prod

def shamirMacRange : Nat → Vec256 → (UInt64 → UInt8) → UInt64 → UInt64 → (UInt64 → UInt8)
  | 0, _, mem, _, _ => mem
  | k + 1, coeff, mem, pS, pA =>
    let updated := writeMem256 mem pA (gfniShamirMacBlock coeff (readMem256 mem pS) (readMem256 mem pA))
    shamirMacRange k coeff updated (pS + 32) (pA + 32)

structure AsmFfiShamirMac where
  sharesPtr : UInt64
  accPtr : UInt64
  coeff : Vec256
  remaining : Nat
  mem : UInt64 → UInt8

def gfniEntryObs : List StepObs :=
  [⟨0, [], true⟩, ⟨10, [], true⟩, ⟨15, [], true⟩, ⟨20, [], true⟩, ⟨30, [], true⟩,
   ⟨35, [], true⟩, ⟨40, [], true⟩, ⟨44, [], true⟩, ⟨49, [], true⟩]

def gfniBodyObs (pS pA : UInt64) : List StepObs :=
  [⟨55, [(pS, 32)], true⟩, ⟨59, [(pA, 32)], true⟩, ⟨63, [], true⟩, ⟨69, [], true⟩,
   ⟨74, [], true⟩, ⟨80, [], true⟩, ⟨84, [(pA, 32)], true⟩, ⟨88, [], true⟩,
   ⟨92, [], true⟩, ⟨96, [], true⟩, ⟨99, [], true⟩]

def gfniExitObs (rsp : UInt64) : List StepObs :=
  [⟨101, [], true⟩, ⟨105, [], true⟩, ⟨109, [], true⟩, ⟨113, [], true⟩, ⟨117, [], true⟩,
   ⟨122, [], true⟩, ⟨127, [], true⟩, ⟨129, [], true⟩, ⟨131, [], true⟩, ⟨134, [], true⟩,
   ⟨137, [], true⟩, ⟨139, [], true⟩, ⟨141, [], true⟩, ⟨143, [], true⟩, ⟨145, [], true⟩,
   ⟨148, [], true⟩, ⟨151, [], true⟩, ⟨154, [], true⟩, ⟨157, [], true⟩, ⟨159, [(rsp, 8)], true⟩]

def gfniBodyStep (s : X86State) : X86State × List StepObs :=
  let pS := s.gpr.get 6
  let pA := s.gpr.get 7
  let c := s.gpr.get 1
  let shareV := readMem256 s.mem pS
  let accV := readMem256 s.mem pA
  let y0' := gfniAffineVec256 shareV (s.ymm.get 14) 0
  let pT3 := evalVecBin256 .vgf2p8mulb y0' (s.ymm.get 3)
  let y2' := gfniAffineVec256 pT3 (s.ymm.get 15) 0
  let y1' := evalVecBin256 .vpxor accV y2'
  let cf1 := (evalX86Alu .add true pS 32 s.cf).2.1
  let cf2 := (evalX86Alu .add true pA 32 cf1).2.1
  ({ s with
      pc := jccPc (!(c - 1 == 0)) 55 101
      gpr := (s.gpr.set 6 (pS + 32) |>.set 7 (pA + 32) |>.set 1 (c - 1))
      ymm := (s.ymm.set 0 y0' |>.set 1 y1' |>.set 2 y2')
      cf := cf2
      ofFlag := evalX86IncDecOf false true c
      zf := c - 1 == 0
      ymmDirty := true
      mem := writeMem256 s.mem pA y1' },
   gfniBodyObs pS pA)

def asmFfiGfniBodyStep (m : AsmFfiShamirMac) : AsmFfiShamirMac × List StepObs :=
  let nextMem := writeMem256 m.mem m.accPtr
    (gfniShamirMacBlock m.coeff (readMem256 m.mem m.sharesPtr) (readMem256 m.mem m.accPtr))
  (⟨m.sharesPtr + 32, m.accPtr + 32, m.coeff, m.remaining - 1, nextMem⟩,
   gfniBodyObs m.sharesPtr m.accPtr)

theorem asmFfiGfni_cuts_mem (k : Nat) (pS pA : UInt64) (coeff : Vec256) (rem : Nat) (mem : UInt64 → UInt8) :
    (runCuts asmFfiGfniBodyStep k ⟨pS, pA, coeff, rem, mem⟩).1.mem = shamirMacRange k coeff mem pS pA := by
  induction k generalizing pS pA rem mem with
  | zero => rfl
  | succ k ih =>
    simpa [runCuts, asmFfiGfniBodyStep, shamirMacRange] using
      ih (pS + 32) (pA + 32) (rem - 1)
        (writeMem256 mem pA (gfniShamirMacBlock coeff (readMem256 mem pS) (readMem256 mem pA)))

/-- Symbol execution behind a zero-count guard on `rcx`. The guard branch is a hand-written
model of the Rust wrapper's early return on empty input, not decoded machine code. -/
def gfniShamirMacGuardedRun (fetch : Nat → Option (DecodedInstr X86Instr))
    (fuel : Nat) (s : X86State) : X86State × List StepObs :=
  if s.gpr.get 1 == 0 then
    ({ s with pc := 159, gpr := (s.gpr.set 0 0 |>.set 2 0), ymmDirty := false, halted := true },
     [⟨0, [], true⟩])
  else runX86Fetch fetch fuel s

def asmFfiGfniRun (rsp : UInt64) (n : Word) (baseS baseA scalar : UInt64) (mem : UInt64 → UInt8) :
    AsmFfiShamirMac × List StepObs :=
  let coeff := gfniScaledCoeff scalar
  if n = 0 then (⟨baseS, baseA, coeff, 0, mem⟩, [⟨0, [], true⟩])
  else
    let loop := runCuts asmFfiGfniBodyStep n.toNat ⟨baseS, baseA, coeff, n.toNat, mem⟩
    (loop.1, gfniEntryObs ++ loop.2 ++ (gfniExitObs rsp))

theorem gfni_entry_full (fetch : Nat → Option (DecodedInstr X86Instr))
    (hf : ∀ d ∈ gfniShamirMacProg, fetch d.offset = some d)
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Vec256)
    (cf o zf dy : Bool) (m : UInt64 → UInt8) (fuel : Nat) :
    runX86Fetch fetch (9 + fuel)
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
        cf, o, zf, dy, false, m⟩ =
      let u := runX86Fetch fetch fuel
        ⟨55, ⟨0xa1e4f8e072a2700c, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
          ⟨y0, y1, y2, gfniScaledCoeff r2, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, t3MatVec, t3InvMatVec⟩,
          cf, o, zf, true, false, m⟩
      (u.1, gfniEntryObs ++ u.2) := by
  rw [show 9 + fuel = ((((((((fuel + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 from by omega]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_movImm, maskGprWidth_true, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_vmovGprToXmm, maskGprWidth_true, b16get_0, b16set_14]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_vpbroadcastQ, b16get_14, b16set_14]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_movImm, maskGprWidth_true, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_vmovGprToXmm, maskGprWidth_true, b16get_0, b16set_15]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_vpbroadcastQ, b16get_15, b16set_15]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_vmovGprToXmm, b16get_2, b16set_3]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_vpbroadcastB, b16get_3, b16set_3]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]
  simp only [stepX86Full_vgf2p8affine256, b16get_3, b16get_14, b16set_3, gfniScaledCoeff, t3MatVec, t3InvMatVec, gfniEntryObs]
  rfl

theorem gfni_body_full (fetch : Nat → Option (DecodedInstr X86Instr))
    (hf : ∀ d ∈ gfniShamirMacProg, fetch d.offset = some d)
    (r0 c r2 r3 r4 r5 pS pA r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y0 y1 y2 coeff y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 m14 m15 : Vec256)
    (cf o zf dy : Bool) (m : UInt64 → UInt8) (fuel : Nat) :
    let s : X86State := ⟨55, ⟨r0, c, r2, r3, r4, r5, pS, pA, r8, r9, r10, r11, r12, r13, r14, r15⟩,
      ⟨y0, y1, y2, coeff, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, m14, m15⟩,
      cf, o, zf, dy, false, m⟩
    runX86Fetch fetch (11 + fuel) s =
      ((runX86Fetch fetch fuel (gfniBodyStep s).1).1,
       (gfniBodyStep s).2 ++ (runX86Fetch fetch fuel (gfniBodyStep s).1).2) := by
  dsimp only
  rw [show 11 + fuel = ((((((((((fuel + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 from by omega]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_vload256, b16get_6, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_vload256, b16get_7, b16set_1]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_vgf2p8affine256, b16get_0, b16get_14, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_vbinOp256, b16get_0, b16get_3, b16set_2]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_vgf2p8affine256, b16get_2, b16get_15, b16set_2]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_vbinOp256, b16get_1, b16get_2, b16set_1]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_vstore256, b16get_7, b16get_1]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_addImm64, b16get_6, b16set_6]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_addImm64, b16get_7, b16set_7]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_dec64, b16get_1, b16set_1]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]
  simp only [stepX86Full_jnz, gfniBodyStep, gfniBodyObs,
    b16get_1, b16get_3, b16get_6, b16get_7, b16get_14, b16get_15,
    b16set_0, b16set_1, b16set_2, b16set_6, b16set_7]
  rfl

theorem gfni_exit_full (fetch : Nat → Option (DecodedInstr X86Instr))
    (hf : ∀ d ∈ gfniShamirMacProg, fetch d.offset = some d)
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Vec256)
    (cf o zf dy : Bool) (m : UInt64 → UInt8) (extra : Nat) :
    runX86Fetch fetch (20 + extra)
      ⟨101, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
        cf, o, zf, dy, false, m⟩ =
      (⟨(readMem64 m r4).toNat, ⟨0, 0, 0, r3, r4 + 8, r5, 0, 0, 0, 0, 0, 0, r12, r13, r14, r15⟩,
        ⟨Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero,
          Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero⟩,
        false, false, true, false, true, m⟩,
       (gfniExitObs r4)) := by
  rw [show 20 + extra = (((((((((((((((((((extra + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 from by omega]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_vbinOp256, b16get_0, vpxor_self, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_vbinOp256, b16get_1, vpxor_self, b16set_1]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_vbinOp256, b16get_2, vpxor_self, b16set_2]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_vbinOp256, b16get_3, vpxor_self, b16set_3]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_vbinOp256, b16get_14, vpxor_self, b16set_14]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_vbinOp256, b16get_15, vpxor_self, b16set_15]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_xorRR, b16get_0, mask32_xor_self_eq, u64_zero_beq_true, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_xorRR, b16get_2, mask32_xor_self_eq, u64_zero_beq_true, b16set_2]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_vzeroall]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_vzeroupper, vzeroupper_bank16, zeroUpperVec256_zero]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_xorRR, b16get_7, mask32_xor_self_eq, u64_zero_beq_true, b16set_7]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_xorRR, b16get_6, mask32_xor_self_eq, u64_zero_beq_true, b16set_6]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_xorRR, b16get_2, mask32_xor_self_eq, u64_zero_beq_true, b16set_2]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_xorRR, b16get_1, mask32_xor_self_eq, u64_zero_beq_true, b16set_1]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_xorRR, b16get_8, mask32_xor_self_eq, u64_zero_beq_true, b16set_8]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_xorRR, b16get_9, mask32_xor_self_eq, u64_zero_beq_true, b16set_9]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_xorRR, b16get_10, mask32_xor_self_eq, u64_zero_beq_true, b16set_10]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_xorRR, b16get_11, mask32_xor_self_eq, u64_zero_beq_true, b16set_11]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]; simp only [stepX86Full_xorRR, b16get_0, mask32_xor_self_eq, u64_zero_beq_true, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [gfniShamirMacProg_eq]; rfl)]
  simp only [stepX86Full_ret, b16get_4, b16set_4, gfniExitObs]
  rw [runX86Fetch_halted _ _ _ rfl]

def GfniMacRel (s₀ : X86State) (n v : Nat) (a : X86State) (m : AsmFfiShamirMac) : Prop :=
  let baseS := s₀.gpr.get 6
  let baseA := s₀.gpr.get 7
  let coeff := gfniScaledCoeff (s₀.gpr.get 2)
  ∃ cf o zf : Bool, ∃ y0 y1 y2 : Vec256,
    a = ⟨if v = n then 101 else 55,
          (s₀.gpr.set 0 0xa1e4f8e072a2700c |>.set 6 (ptrStride baseS 32 v)
            |>.set 7 (ptrStride baseA 32 v) |>.set 1 (UInt64.ofNat (n - v))),
          (s₀.ymm.set 0 y0 |>.set 1 y1 |>.set 2 y2 |>.set 3 coeff
            |>.set 14 t3MatVec |>.set 15 t3InvMatVec),
          cf, o, zf, true, false, m.mem⟩ ∧
    m.sharesPtr = ptrStride baseS 32 v ∧
    m.accPtr = ptrStride baseA 32 v ∧
    m.coeff = coeff ∧
    m.remaining = n - v

def GfniMacLoopPost (s₀ : X86State) (n : Nat) (a : X86State) (m : AsmFfiShamirMac) : Prop :=
  let baseS := s₀.gpr.get 6
  let baseA := s₀.gpr.get 7
  let coeff := gfniScaledCoeff (s₀.gpr.get 2)
  ∃ cf o zf : Bool, ∃ y0 y1 y2 : Vec256,
    a = ⟨101,
          (s₀.gpr.set 0 0xa1e4f8e072a2700c |>.set 6 (ptrStride baseS 32 n)
            |>.set 7 (ptrStride baseA 32 n) |>.set 1 0),
          (s₀.ymm.set 0 y0 |>.set 1 y1 |>.set 2 y2 |>.set 3 coeff
            |>.set 14 t3MatVec |>.set 15 t3InvMatVec),
          cf, o, zf, true, false, m.mem⟩ ∧
    m.remaining = 0

def GfniMacPost (s₀ : X86State) (n : Word) (out : X86State) (m : AsmFfiShamirMac) : Prop :=
  out.halted = true ∧
  out.mem = m.mem ∧
  out.mem = shamirMacRange n.toNat (gfniScaledCoeff (s₀.gpr.get 2)) s₀.mem (s₀.gpr.get 6) (s₀.gpr.get 7) ∧
  out.gpr.get 0 = 0 ∧ out.gpr.get 1 = 0 ∧ out.gpr.get 2 = 0 ∧
  out.ymmDirty = false ∧
  (n ≠ 0 → out.ymm.get 0 = Vec256.zero ∧ out.ymm.get 1 = Vec256.zero ∧
    out.ymm.get 2 = Vec256.zero ∧ out.ymm.get 3 = Vec256.zero ∧
    out.ymm.get 14 = Vec256.zero ∧ out.ymm.get 15 = Vec256.zero) ∧
  out.gpr.get 4 = (if n = 0 then s₀.gpr.get 4 else s₀.gpr.get 4 + 8) ∧ out.gpr.get 3 = s₀.gpr.get 3 ∧ out.gpr.get 5 = s₀.gpr.get 5 ∧
  out.gpr.get 12 = s₀.gpr.get 12 ∧ out.gpr.get 13 = s₀.gpr.get 13 ∧
  out.gpr.get 14 = s₀.gpr.get 14 ∧ out.gpr.get 15 = s₀.gpr.get 15 ∧
  (n ≠ 0 → (∀ i, i < 16 → out.ymm.get i = Vec256.zero) ∧
    out.gpr.get 6 = 0 ∧ out.gpr.get 7 = 0 ∧ out.gpr.get 8 = 0 ∧ out.gpr.get 9 = 0 ∧
    out.gpr.get 10 = 0 ∧ out.gpr.get 11 = 0)

def gfniShamirMacPosCert (s₀ : X86State) (n : Nat) (hn : 0 < n) (hbound : n < 2 ^ 64) :
    LoopRelationCert X86State AsmFfiShamirMac n gfniBodyStep asmFfiGfniBodyStep
      ⟨55, (s₀.gpr.set 0 0xa1e4f8e072a2700c |>.set 1 (UInt64.ofNat n)),
        (s₀.ymm.set 3 (gfniScaledCoeff (s₀.gpr.get 2)) |>.set 14 t3MatVec |>.set 15 t3InvMatVec),
        s₀.cf, s₀.ofFlag, s₀.zf, true, false, s₀.mem⟩
      ⟨s₀.gpr.get 6, s₀.gpr.get 7, gfniScaledCoeff (s₀.gpr.get 2), n, s₀.mem⟩
      (GfniMacLoopPost s₀ n) where
  LoopRel := GfniMacRel s₀ n
  schedule := fun v => gfniBodyObs (ptrStride (s₀.gpr.get 6) 32 v) (ptrStride (s₀.gpr.get 7) 32 v)
  entry := by
    obtain ⟨_, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
      ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
      cf, o, zf, dy, _, m⟩ := s₀
    refine ⟨cf, o, zf, y0, y1, y2, ?_, rfl, rfl, rfl, by dsimp only; omega⟩
    simp [ptrStride, Nat.ne_of_lt hn, b16get_2, b16get_6, b16get_7,
      b16set_0, b16set_1, b16set_2, b16set_3, b16set_6, b16set_7, b16set_14, b16set_15]
  body := by
    intro v a m hv ⟨cf, o, zf, y0, y1, y2, ha, hpS, hpA, hcoeff, hmr⟩
    subst ha
    obtain ⟨_, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
      ⟨oy0, oy1, oy2, oy3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, oy14, oy15⟩,
      _, _, _, _, _, _⟩ := s₀
    have hpos : 0 < n - v := by omega
    have hlt : n - v < 2 ^ 64 := by omega
    have hdec := u64_ofNat_sub_one hpos hlt
    have hsub : n - v - 1 = n - (v + 1) := by omega
    have hzf : (UInt64.ofNat (n - (v + 1)) == 0) = decide (v + 1 = n) := by
      rw [u64_ofNat_eq_zero_iff (by omega)]
      by_cases heq : v + 1 = n <;> simp [heq] <;> omega
    have hjcc : jccPc (!(UInt64.ofNat (n - (v + 1)) == 0)) 55 101 = (if v + 1 = n then 101 else 55) := by
      rw [hzf]
      by_cases heq : v + 1 = n <;> simp [heq, jccPc]
    let pS := ptrStride r6 32 v
    let pA := ptrStride r7 32 v
    let cf1 := (evalX86Alu .add true pS 32 cf).2.1
    let cf2 := (evalX86Alu .add true pA 32 cf1).2.1
    let y0' := gfniAffineVec256 (readMem256 m.mem pS) t3MatVec 0
    let y2' := gfniAffineVec256 (evalVecBin256 .vgf2p8mulb y0' (gfniScaledCoeff r2)) t3InvMatVec 0
    let y1' := evalVecBin256 .vpxor (readMem256 m.mem pA) y2'
    refine ⟨⟨cf2, evalX86IncDecOf false true (UInt64.ofNat (n - v)), UInt64.ofNat (n - (v + 1)) == 0,
      y0', y1', y2', ?_, ?_, ?_, hcoeff, ?_⟩, ?_, ?_⟩
    · simp only [gfniBodyStep, asmFfiGfniBodyStep, gfniShamirMacBlock,
        b16get_1, b16get_2, b16get_3, b16get_6, b16get_7, b16get_14, b16get_15,
        b16set_0, b16set_1, b16set_2, b16set_3, b16set_6, b16set_7, b16set_14, b16set_15,
        hdec, hsub, hjcc, ptrStride, hpS, hpA, hcoeff]
      rfl
    · simp [asmFfiGfniBodyStep, hpS, ptrStride, b16get_6]
    · simp [asmFfiGfniBodyStep, hpA, ptrStride, b16get_7]
    · simp [asmFfiGfniBodyStep, hmr]; omega
    · simp [gfniBodyStep, b16get_6, b16get_7, b16set_0, b16set_1, b16set_6, b16set_7]
    · simp [asmFfiGfniBodyStep, hpS, hpA, b16get_6, b16get_7]
  exit := by
    intro a m ⟨cf, o, zf, y0, y1, y2, ha, _, _, _, hmr⟩
    exact ⟨cf, o, zf, y0, y1, y2, by simpa using ha, by omega⟩

theorem gfni_replay_loop (fetch : Nat → Option (DecodedInstr X86Instr))
    (hf : ∀ d ∈ gfniShamirMacProg, fetch d.offset = some d)
    (s₀ : X86State) (n : Nat) (hn : 0 < n) (hbound : n < 2 ^ 64) (rem : Nat) :
    ∀ v a m fuel, v + rem = n → GfniMacRel s₀ n v a m →
      runX86Fetch fetch (11 * rem + fuel) a =
        let loop := runCuts gfniBodyStep rem a
        let u := runX86Fetch fetch fuel loop.1
        (u.1, loop.2 ++ u.2) := by
  induction rem with
  | zero => intro v a m fuel _ _; simp [runCuts]
  | succ k ih =>
    intro v a m fuel hv hrel
    have hvn : v < n := by omega
    rcases hrel with ⟨cf, o, zf, y0, y1, y2, ha, hpS, hpA, hcoeff, hmr⟩
    have hrel' : GfniMacRel s₀ n v a m := ⟨cf, o, zf, y0, y1, y2, ha, hpS, hpA, hcoeff, hmr⟩
    have hbody := (gfniShamirMacPosCert s₀ n hn hbound).body v a m hvn hrel'
    obtain ⟨_, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
      ⟨oy0, oy1, oy2, oy3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, oy14, oy15⟩,
      _, _, _, _, _, _⟩ := s₀
    have ha55 : a = ⟨55, ⟨0xa1e4f8e072a2700c, UInt64.ofNat (n - v), r2, r3, r4, r5,
        ptrStride r6 32 v, ptrStride r7 32 v, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨y0, y1, y2, gfniScaledCoeff r2, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, t3MatVec, t3InvMatVec⟩,
        cf, o, zf, true, false, m.mem⟩ := by
      simpa [Nat.ne_of_lt hvn, b16get_2, b16get_6, b16get_7,
        b16set_0, b16set_1, b16set_2, b16set_3, b16set_6, b16set_7, b16set_14, b16set_15] using ha
    rw [show 11 * (k + 1) + fuel = 11 + (11 * k + fuel) from by omega, ha55]
    rw [gfni_body_full fetch hf]
    rw [← ha55]
    rw [ih (v + 1) (gfniBodyStep a).1 (asmFfiGfniBodyStep m).1 fuel (by omega) hbody.1]
    simp [runCuts, List.append_assoc]

/-- Complete `UnrestrictedLoopCert` for `qsag_asm_gf256_shamir_mac_gfni` over **all `n : BitVec 64`**. -/
def gfniShamirMacUnrestrictedCert (fetch : Nat → Option (DecodedInstr X86Instr))
    (hf : ∀ d ∈ gfniShamirMacProg, fetch d.offset = some d)
    (s₀ : X86State) (fuel : Nat) (hpc : s₀.pc = 0) (hh : s₀.halted = false)
    (n : Word) (hcount : s₀.gpr.get 1 = UInt64.ofBitVec n)
    (hfuel : 11 * n.toNat + 29 ≤ fuel) :
    UnrestrictedLoopCert X86State AsmFfiShamirMac n
      (gfniShamirMacGuardedRun fetch fuel)
      (fun m => asmFfiGfniRun (s₀.gpr.get 4) n m.sharesPtr m.accPtr (s₀.gpr.get 2) m.mem)
      gfniBodyStep asmFfiGfniBodyStep
      s₀ ⟨s₀.gpr.get 6, s₀.gpr.get 7, gfniScaledCoeff (s₀.gpr.get 2), n.toNat, s₀.mem⟩
      ⟨55, (s₀.gpr.set 0 0xa1e4f8e072a2700c |>.set 1 (UInt64.ofNat n.toNat)),
        (s₀.ymm.set 3 (gfniScaledCoeff (s₀.gpr.get 2)) |>.set 14 t3MatVec |>.set 15 t3InvMatVec),
        s₀.cf, s₀.ofFlag, s₀.zf, true, false, s₀.mem⟩
      ⟨s₀.gpr.get 6, s₀.gpr.get 7, gfniScaledCoeff (s₀.gpr.get 2), n.toNat, s₀.mem⟩
      (GfniMacLoopPost s₀ n.toNat)
      (GfniMacPost s₀ n) where
  zeroSchedule := [⟨0, [], true⟩]
  entrySchedule := gfniEntryObs
  bodySchedule := fun v => gfniBodyObs (ptrStride (s₀.gpr.get 6) 32 v) (ptrStride (s₀.gpr.get 7) 32 v)
  exitSchedule := (gfniExitObs (s₀.gpr.get 4))
  zero_cut := by
    intro hz; subst hz
    have hg0 : (s₀.gpr.get 1 == 0) = true := by simp [hcount]
    dsimp only [gfniShamirMacGuardedRun, asmFfiGfniRun]
    rw [ite_eq_left hg0, ite_eq_left rfl]
    obtain ⟨_, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, _, _, _, _, _, _, _⟩ := s₀
    have hr1 : r1 = 0 := hcount
    refine ⟨⟨rfl, rfl, rfl, rfl, hr1, rfl, rfl, fun h => absurd rfl h, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      fun h => absurd rfl h⟩, rfl, rfl⟩
  pos_cert := fun hn =>
    gfniShamirMacPosCert s₀ n.toNat (bv64_pos_of_ne_zero n hn) n.isLt
  pos_sched := fun _ => rfl
  pos_replay := by
    intro hn hlp hal hml
    have hg0 : ¬ ((s₀.gpr.get 1 == 0) = true) := by
      rw [beq_false_of_ne (hcount ▸ (bv64_ne_zero_iff_u64_ne_zero n).mp hn)]; decide
    dsimp only [gfniShamirMacGuardedRun, asmFfiGfniRun]
    rw [ite_eq_right hg0, ite_eq_right hn]
    obtain ⟨extra, hextra⟩ : ∃ extra, fuel = 9 + (11 * n.toNat + (20 + extra)) :=
      ⟨fuel - (11 * n.toNat + 29), by omega⟩
    rw [hextra]
    obtain ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
      ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
      cf, o, zf, dy, hlt, m⟩ := s₀
    cases hpc; cases hh
    have hr1 : r1 = UInt64.ofNat n.toNat := by
      apply u64_eq_of_toNat_eq
      have : r1 = UInt64.ofBitVec n := hcount
      rw [this, UInt64.toNat_ofNat', Nat.mod_eq_of_lt n.isLt]; rfl
    rw [gfni_entry_full fetch hf]
    have headEq : (⟨55, ⟨0xa1e4f8e072a2700c, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨y0, y1, y2, gfniScaledCoeff r2, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, t3MatVec, t3InvMatVec⟩,
        cf, o, zf, true, false, m⟩ : X86State) =
      ⟨55, ((Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15).set 0 0xa1e4f8e072a2700c
            |>.set 1 (UInt64.ofNat n.toNat)),
        ((Bank16.mk y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).set 3 (gfniScaledCoeff r2)
          |>.set 14 t3MatVec |>.set 15 t3InvMatVec),
        cf, o, zf, true, false, m⟩ := by
      simp [hr1, b16set_0, b16set_1, b16set_3, b16set_14, b16set_15]
    rw [headEq]
    have hpos := bv64_pos_of_ne_zero n hn
    have hrep := gfni_replay_loop fetch hf
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩, cf, o, zf, dy, false, m⟩
      n.toNat hpos n.isLt n.toNat 0 _ ⟨r6, r7, gfniScaledCoeff r2, n.toNat, m⟩ (20 + extra) (by omega)
      (gfniShamirMacPosCert _ n.toNat hpos n.isLt).entry
    dsimp only at hrep ⊢
    simp only [b16get_2] at hrep
    rw [hrep]
    rcases hlp with ⟨cfL, oL, zfL, y0L, y1L, y2L, haL, _⟩
    have ha101 : (runCuts gfniBodyStep n.toNat
        ⟨55, ((Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15).set 0 0xa1e4f8e072a2700c
              |>.set 1 (UInt64.ofNat n.toNat)),
          ((Bank16.mk y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).set 3 (gfniScaledCoeff r2)
            |>.set 14 t3MatVec |>.set 15 t3InvMatVec),
          cf, o, zf, true, false, m⟩).1 =
      ⟨101, ⟨0xa1e4f8e072a2700c, 0, r2, r3, r4, r5, ptrStride r6 32 n.toNat, ptrStride r7 32 n.toNat,
        r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨y0L, y1L, y2L, gfniScaledCoeff r2, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, t3MatVec, t3InvMatVec⟩,
        cfL, oL, zfL, true, false,
        (runCuts asmFfiGfniBodyStep n.toNat ⟨r6, r7, gfniScaledCoeff r2, n.toNat, m⟩).1.mem⟩ := by
      simpa [b16get_2, b16get_6, b16get_7,
        b16set_0, b16set_1, b16set_2, b16set_3, b16set_6, b16set_7, b16set_14, b16set_15] using haL
    rw [ha101, gfni_exit_full fetch hf]
    have hmr := asmFfiGfni_cuts_mem n.toNat r6 r7 (gfniScaledCoeff r2) n.toNat m
    refine ⟨?_, by simp only [List.append_assoc, b16get_2]; rfl, rfl⟩
    dsimp only [GfniMacPost]
    rw [ite_eq_right hn]
    refine ⟨rfl, rfl, hmr, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    · intro _
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · intro _
      exact ⟨fun i hi => match i, hi with
        | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl
        | 6, _ => rfl | 7, _ => rfl | 8, _ => rfl | 9, _ => rfl | 10, _ => rfl | 11, _ => rfl
        | 12, _ => rfl | 13, _ => rfl | 14, _ => rfl | 15, _ => rfl
        | i + 16, h => absurd h (by omega), rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Refinement and `StepObs` noninterference for the guarded runner of `qsag_asm_gf256_shamir_mac_gfni` at every
`n : BitVec 64`. For `n ≠ 0` the runner is byte-decoded execution of the symbol
(`gf256_shamir_mac_gfni_sydtv_refines_pos`); for `n = 0` it is the modelled wrapper early return. -/
theorem gf256_shamir_mac_gfni_sydtv_refines_all_n (s₁ s₂ : X86State) (fuel : Nat) (n : Word)
    (hpc₁ : s₁.pc = 0) (hh₁ : s₁.halted = false) (hc₁ : s₁.gpr.get 1 = UInt64.ofBitVec n)
    (hpc₂ : s₂.pc = 0) (hh₂ : s₂.halted = false) (hc₂ : s₂.gpr.get 1 = UInt64.ofBitVec n)
    (hpS : s₁.gpr.get 6 = s₂.gpr.get 6) (hpA : s₁.gpr.get 7 = s₂.gpr.get 7)
    (hfuel : 11 * n.toNat + 29 ≤ fuel)
    (hsp : s₁.gpr.get 4 = s₂.gpr.get 4) :
    let out₁ := gfniShamirMacGuardedRun (decodeX86One gfniShamirMacCode) fuel s₁
    let out₂ := gfniShamirMacGuardedRun (decodeX86One gfniShamirMacCode) fuel s₂
    let ffi₁ := asmFfiGfniRun (s₁.gpr.get 4) n (s₁.gpr.get 6) (s₁.gpr.get 7) (s₁.gpr.get 2) s₁.mem
    GfniMacPost s₁ n out₁.1 ffi₁.1 ∧ out₁.2 = out₂.2 ∧ out₁.2 = ffi₁.2 := by
  dsimp only
  let c₁ := gfniShamirMacUnrestrictedCert (decodeX86One gfniShamirMacCode) gfniShamirMac_fetch_decodeOne
    s₁ fuel hpc₁ hh₁ n hc₁ hfuel
  let c₂ := gfniShamirMacUnrestrictedCert (decodeX86One gfniShamirMacCode) gfniShamirMac_fetch_decodeOne
    s₂ fuel hpc₂ hh₂ n hc₂ hfuel
  obtain ⟨hp, _, _⟩ := unrestricted_loop_refinement_sound c₁
  have hsched : c₁.bodySchedule = c₂.bodySchedule := by
    funext v; simp [c₁, c₂, gfniShamirMacUnrestrictedCert, hpS, hpA]
  have hz : c₁.zeroSchedule = c₂.zeroSchedule := by
    simp [c₁, c₂, gfniShamirMacUnrestrictedCert]
  have he : c₁.entrySchedule = c₂.entrySchedule := by
    simp [c₁, c₂, gfniShamirMacUnrestrictedCert]
  have hx : c₁.exitSchedule = c₂.exitSchedule := by
    simp [c₁, c₂, gfniShamirMacUnrestrictedCert, hsp]
  obtain ⟨hni1, hni2⟩ := unrestricted_three_way_noninterference c₁ c₂ hz he hsched hx
  exact ⟨hp, hni1, hni2⟩

theorem gfniShamirMacGuardedRun_pos (fetch : Nat → Option (DecodedInstr X86Instr)) (fuel : Nat)
    (s : X86State) (n : Word) (hn : n ≠ 0) (hc : s.gpr.get 1 = UInt64.ofBitVec n) :
    gfniShamirMacGuardedRun fetch fuel s = runX86Fetch fetch fuel s := by
  have hg0 : ¬ ((s.gpr.get 1 == 0) = true) := by
    rw [beq_false_of_ne (hc ▸ (bv64_ne_zero_iff_u64_ne_zero n).mp hn)]; decide
  unfold gfniShamirMacGuardedRun
  rw [ite_eq_right hg0]

/-- `qsag_asm_gf256_shamir_mac_gfni`, raw symbol bytes, nonzero block count. The scalar in `rdx`
may differ between the two runs. -/
theorem gf256_shamir_mac_gfni_sydtv_refines_pos (s₁ s₂ : X86State) (fuel : Nat) (n : Word) (hn : n ≠ 0)
    (hpc₁ : s₁.pc = 0) (hh₁ : s₁.halted = false) (hc₁ : s₁.gpr.get 1 = UInt64.ofBitVec n)
    (hpc₂ : s₂.pc = 0) (hh₂ : s₂.halted = false) (hc₂ : s₂.gpr.get 1 = UInt64.ofBitVec n)
    (hpS : s₁.gpr.get 6 = s₂.gpr.get 6) (hpA : s₁.gpr.get 7 = s₂.gpr.get 7)
    (hfuel : 11 * n.toNat + 29 ≤ fuel)
    (hsp : s₁.gpr.get 4 = s₂.gpr.get 4) :
    GfniMacPost s₁ n (runX86One gfniShamirMacCode fuel s₁).1
      (asmFfiGfniRun (s₁.gpr.get 4) n (s₁.gpr.get 6) (s₁.gpr.get 7) (s₁.gpr.get 2) s₁.mem).1 ∧
    (runX86One gfniShamirMacCode fuel s₁).2 = (runX86One gfniShamirMacCode fuel s₂).2 ∧
    (runX86One gfniShamirMacCode fuel s₁).2 =
      (asmFfiGfniRun (s₁.gpr.get 4) n (s₁.gpr.get 6) (s₁.gpr.get 7) (s₁.gpr.get 2) s₁.mem).2 := by
  have h := gf256_shamir_mac_gfni_sydtv_refines_all_n s₁ s₂ fuel n hpc₁ hh₁ hc₁ hpc₂ hh₂ hc₂ hpS hpA hfuel hsp
  dsimp only at h
  rw [gfniShamirMacGuardedRun_pos _ fuel s₁ n hn hc₁, gfniShamirMacGuardedRun_pos _ fuel s₂ n hn hc₂] at h
  simpa only [runX86One_eq, runArm64One_eq] using h

/-! ## §8. Kernel 5 — `qsag_asm_tower128_bdoz_mac_vpclmul` (2-Pointer 32B Affine + Dual-256b Karatsuba XOR Accumulators, `∀ n : Word`) -/

theorem vpclmulBdozMac_fetch_decodeOne :
    ∀ d ∈ vpclmulBdozMacProg, decodeX86One vpclmulBdozMacCode d.offset = some d := by
  intro d hd
  have hall := vpclmulBdozMac_decodeOne_all.2
  rw [List.all_eq_true] at hall
  have h := hall d hd
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

def karatsubaStepLo (accLo a b : Vec256) : Vec256 :=
  let mid := evalVecBin256 .vpxor (clmul256 a b 0x01) (clmul256 a b 0x10)
  let prodLo := evalVecBin256 .vpxor (clmul256 a b 0x00) (evalVecShift256 .vpslldq mid 8)
  evalVecBin256 .vpxor accLo prodLo

def karatsubaStepHi (accHi a b : Vec256) : Vec256 :=
  let mid := evalVecBin256 .vpxor (clmul256 a b 0x01) (clmul256 a b 0x10)
  let prodHi := evalVecBin256 .vpxor (clmul256 a b 0x11) (evalVecShift256 .vpsrldq mid 8)
  evalVecBin256 .vpxor accHi prodHi

def poly87Reduce256 (accLo accHi : Vec256) : Vec256 :=
  let c87 := bcastQword256 0x87
  let r1 := clmul256 accHi c87 0x01
  let lo1 := evalVecBin256 .vpxor accLo (evalVecShift256 .vpslldq r1 8)
  let hi1 := evalVecBin256 .vpxor accHi (evalVecShift256 .vpsrldq r1 8)
  let r0 := clmul256 hi1 c87 0x00
  evalVecBin256 .vpxor lo1 r0

def bdozMacAccum : Nat → (UInt64 → UInt8) → UInt64 → UInt64 → Vec256 → Vec256 → Vec256 × Vec256
  | 0, _, _, _, lo, hi => (lo, hi)
  | k + 1, mem, pL, pR, lo, hi =>
    let a := readMem256 mem pL
    let b := readMem256 mem pR
    bdozMacAccum k mem (pL + 32) (pR + 32) (karatsubaStepLo lo a b) (karatsubaStepHi hi a b)

section Gf128MacAlgebra
-- clmul64 is opaque across the public ISA interface.
attribute [-instance] UInt8.instLawfulEqOrd BitVec.instLawfulEqOrd

/-- Select either independent 128-bit SIMD lane in polynomial bit order. -/
def gf128Lane (v : Vec256) (lane : Fin 2) : BitVec 128 :=
  if lane.val = 0 then gf128Words v.w0 v.w1 else gf128Words v.w2 v.w3

/-- Interpret the pair of unreduced SIMD accumulators as a polynomial. -/
def gf128AccumLane (lo hi : Vec256) (lane : Fin 2) : BitVec 256 :=
  gf128Lane hi lane ++ gf128Lane lo lane

/-- XOR of unreduced polynomial products in the selected lane of n blocks.
Pointer arithmetic is the machine's UInt64 arithmetic, including wrapping. -/
def gf128BdozPolySum : Nat → (UInt64 → UInt8) → UInt64 → UInt64 → Fin 2 → BitVec 256
  | 0, _, _, _, _ => 0
  | n+1, mem, pL, pR, lane =>
      gf128PolyMul ((gf128Lane (readMem256 mem pL) lane).setWidth 256)
        (gf128Lane (readMem256 mem pR) lane) ^^^
      gf128BdozPolySum n mem (pL+32) (pR+32) lane

/-- XOR of the mathematical GF(2^128) products in the selected lane of n blocks. -/
def gf128BdozFieldSum : Nat → (UInt64 → UInt8) → UInt64 → UInt64 → Fin 2 → BitVec 128
  | 0, _, _, _, _ => 0
  | n+1, mem, pL, pR, lane =>
      gf128FieldMul (gf128Lane (readMem256 mem pL) lane)
        (gf128Lane (readMem256 mem pR) lane) ^^^
      gf128BdozFieldSum n mem (pL+32) (pR+32) lane

theorem gf128BdozPolySum_reduce (n : Nat) (mem : UInt64 → UInt8)
    (pL pR : UInt64) (lane : Fin 2) :
    gf128Reduce (gf128BdozPolySum n mem pL pR lane) =
      gf128BdozFieldSum n mem pL pR lane := by
  induction n generalizing pL pR with
  | zero => exact gf128Reduce_zero_eq
  | succ n ih =>
    simp only [gf128BdozPolySum, gf128BdozFieldSum, gf128Reduce_xor, ih, gf128FieldMul_eq]

private theorem gf128AccWords_product (l0 l1 h0 h1 : UInt64) (p00 p01 p10 p11 : Vec128) :
    gf128Words (h0 ^^^ (p11.w0 ^^^ ((p10.w1 ^^^ p01.w1) >>> 0)))
      (h1 ^^^ (p11.w1 ^^^ 0)) ++
      gf128Words (l0 ^^^ (p00.w0 ^^^ 0))
        (l1 ^^^ (p00.w1 ^^^ ((p10.w0 ^^^ p01.w0) <<< 0))) =
    (gf128Words h0 h1 ++ gf128Words l0 l1) ^^^
      (gf128Words (p11.w0 ^^^ p01.w1 ^^^ p10.w1) p11.w1 ++
        gf128Words p00.w0 (p00.w1 ^^^ p01.w0 ^^^ p10.w0)) := by
  simp only [UInt64.shiftLeft_zero, UInt64.shiftRight_zero, UInt64.xor_zero]
  apply BitVec.eq_of_getLsbD_eq
  intro i hbound
  simp only [gf128Words_eq, BitVec.getLsbD_append, UInt64.toBitVec_xor, BitVec.getLsbD_xor]
  by_cases h0 : i < 128 <;> by_cases h1 : i < 64 <;> by_cases h2 : i - 128 < 64 <;>
    simp_all only [↓reduceIte, Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]

private theorem gf128KaratsubaStep_lane (lo hi a b : Vec256) (lane : Fin 2) :
    gf128AccumLane (karatsubaStepLo lo a b) (karatsubaStepHi hi a b) lane =
      gf128AccumLane lo hi lane ^^^
        gf128PolyMul ((gf128Lane a lane).setWidth 256) (gf128Lane b lane) := by
  by_cases hl : lane.val = 0
  · simp only [gf128AccumLane, gf128Lane, hl, ↓reduceIte]
    rw [← gf128_clmul_four_words]
    simp only [karatsubaStepLo, karatsubaStepHi, evalVecBin256_xor_eq, evalVecShift256_left8, evalVecShift256_right8, clmul256_eq_0, clmul256_eq_1, clmul256_eq_16, clmul256_eq_17]
    exact gf128AccWords_product lo.w0 lo.w1 hi.w0 hi.w1
      (clmul64 a.w0 b.w0) (clmul64 a.w0 b.w1) (clmul64 a.w1 b.w0) (clmul64 a.w1 b.w1)
  · simp only [gf128AccumLane, gf128Lane, hl, ↓reduceIte]
    rw [← gf128_clmul_four_words]
    simp only [karatsubaStepLo, karatsubaStepHi, evalVecBin256_xor_eq, evalVecShift256_left8, evalVecShift256_right8, clmul256_eq_0, clmul256_eq_1, clmul256_eq_16, clmul256_eq_17]
    exact gf128AccWords_product lo.w2 lo.w3 hi.w2 hi.w3
      (clmul64 a.w2 b.w2) (clmul64 a.w2 b.w3) (clmul64 a.w3 b.w2) (clmul64 a.w3 b.w3)

theorem gf128BdozAccum_polynomial (n : Nat) (mem : UInt64 → UInt8)
    (pL pR : UInt64) (lo hi : Vec256) (lane : Fin 2) :
    gf128AccumLane (bdozMacAccum n mem pL pR lo hi).1
      (bdozMacAccum n mem pL pR lo hi).2 lane =
      gf128AccumLane lo hi lane ^^^ gf128BdozPolySum n mem pL pR lane := by
  induction n generalizing pL pR lo hi with
  | zero => simp [bdozMacAccum, gf128BdozPolySum]
  | succ n ih =>
    simp only [bdozMacAccum, ih, gf128KaratsubaStep_lane, gf128BdozPolySum,
      BitVec.xor_assoc]

private theorem gf128ReduceWords (lo0 lo1 hi0 hi1 : UInt64) :
    gf128Words
      ((lo0 ^^^ (0 : UInt64)) ^^^ (clmul64 (hi0 ^^^ ((clmul64 hi1 0x87).w1 >>> (0 : UInt64))) 0x87).w0)
      ((lo1 ^^^ ((clmul64 hi1 0x87).w0 <<< (0 : UInt64))) ^^^
        (clmul64 (hi0 ^^^ ((clmul64 hi1 0x87).w1 >>> (0 : UInt64))) 0x87).w1) =
      gf128WordReduce lo0 lo1 hi0 hi1 := by
  simp only [UInt64.xor_zero, UInt64.shiftLeft_zero, UInt64.shiftRight_zero, gf128WordReduce_eq]

private theorem gf128Poly87Reduce_lane (lo hi : Vec256) (lane : Fin 2) :
    gf128Lane (poly87Reduce256 lo hi) lane = gf128Reduce (gf128AccumLane lo hi lane) := by
  by_cases hl : lane.val = 0
  · simp only [gf128AccumLane, gf128Lane, hl, ↓reduceIte]
    rw [← gf128WordReduce_eq_reduce]
    simp only [poly87Reduce256, bcastQword256_eq, evalVecBin256_xor_eq, evalVecShift256_left8, evalVecShift256_right8, clmul256_eq_0, clmul256_eq_1]
    exact gf128ReduceWords lo.w0 lo.w1 hi.w0 hi.w1
  · simp only [gf128AccumLane, gf128Lane, hl, ↓reduceIte]
    rw [← gf128WordReduce_eq_reduce]
    simp only [poly87Reduce256, bcastQword256_eq, evalVecBin256_xor_eq, evalVecShift256_left8, evalVecShift256_right8, clmul256_eq_0, clmul256_eq_1]
    exact gf128ReduceWords lo.w2 lo.w3 hi.w2 hi.w3

/-- Each valid 128-bit lane of the reduced machine accumulator is the XOR
of the n mathematical field products read from the corresponding input lane.
The count-zero case is an algebraic identity, not execution of a zero-trip ABI call. -/
theorem gf128_bdozMacAccum_field (n : Nat) (mem : UInt64 → UInt8)
    (pL pR : UInt64) (lane : Nat) (hLane : lane < 2) :
    gf128Lane
      (poly87Reduce256 (bdozMacAccum n mem pL pR Vec256.zero Vec256.zero).1
        (bdozMacAccum n mem pL pR Vec256.zero Vec256.zero).2) ⟨lane, hLane⟩ =
      gf128BdozFieldSum n mem pL pR ⟨lane, hLane⟩ := by
  rw [gf128Poly87Reduce_lane, gf128BdozAccum_polynomial]
  have hz : gf128AccumLane Vec256.zero Vec256.zero ⟨lane, hLane⟩ = 0 := by
    simp [gf128AccumLane, gf128Lane, Vec256.zero, gf128Words_eq]
  rw [hz]
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.zero_xor] using
    gf128BdozPolySum_reduce n mem pL pR ⟨lane, hLane⟩


end Gf128MacAlgebra

structure AsmFfiBdozMac where
  lhsPtr : UInt64
  rhsPtr : UInt64
  outPtr : UInt64
  accLo : Vec256
  accHi : Vec256
  remaining : Nat
  mem : UInt64 → UInt8

def vpclmulEntryObs : List StepObs := [⟨0, [], true⟩, ⟨4, [], true⟩]

def vpclmulBodyObs (pL pR : UInt64) : List StepObs :=
  [⟨8, [(pL, 32)], true⟩, ⟨12, [(pR, 32)], true⟩, ⟨16, [], true⟩, ⟨22, [], true⟩,
   ⟨28, [], true⟩, ⟨34, [], true⟩, ⟨40, [], true⟩, ⟨44, [], true⟩, ⟨49, [], true⟩,
   ⟨54, [], true⟩, ⟨58, [], true⟩, ⟨62, [], true⟩, ⟨66, [], true⟩, ⟨70, [], true⟩,
   ⟨74, [], true⟩, ⟨78, [], true⟩, ⟨81, [], true⟩]

def vpclmulExitObs (rsp : UInt64) (outPtr : UInt64) : List StepObs :=
  [⟨83, [], true⟩, ⟨88, [], true⟩, ⟨93, [], true⟩, ⟨98, [], true⟩, ⟨104, [], true⟩,
   ⟨109, [], true⟩, ⟨114, [], true⟩, ⟨118, [], true⟩, ⟨122, [], true⟩, ⟨128, [], true⟩,
   ⟨132, [(outPtr, 32)], true⟩, ⟨136, [], true⟩, ⟨140, [], true⟩, ⟨144, [], true⟩,
   ⟨148, [], true⟩, ⟨152, [], true⟩, ⟨156, [], true⟩, ⟨160, [], true⟩, ⟨164, [], true⟩,
   ⟨168, [], true⟩, ⟨173, [], true⟩, ⟨175, [], true⟩, ⟨178, [], true⟩, ⟨181, [], true⟩,
   ⟨183, [], true⟩, ⟨185, [], true⟩, ⟨187, [], true⟩, ⟨189, [], true⟩, ⟨192, [], true⟩,
   ⟨195, [], true⟩, ⟨198, [], true⟩, ⟨201, [], true⟩, ⟨203, [(rsp, 8)], true⟩]

def vpclmulBodyStep (s : X86State) : X86State × List StepObs :=
  let pL := s.gpr.get 6
  let pR := s.gpr.get 2
  let c := s.gpr.get 1
  let a := readMem256 s.mem pL
  let b := readMem256 s.mem pR
  let mid := evalVecBin256 .vpxor (clmul256 a b 0x01) (clmul256 a b 0x10)
  let shL := evalVecShift256 .vpslldq mid 8
  let shH := evalVecShift256 .vpsrldq mid 8
  let pLo := evalVecBin256 .vpxor (clmul256 a b 0x00) shL
  let pHi := evalVecBin256 .vpxor (clmul256 a b 0x11) shH
  let lo' := evalVecBin256 .vpxor (s.ymm.get 0) pLo
  let hi' := evalVecBin256 .vpxor (s.ymm.get 1) pHi
  let cf1 := (evalX86Alu .add true pL 32 s.cf).2.1
  let cf2 := (evalX86Alu .add true pR 32 cf1).2.1
  ({ s with
      pc := jccPc (!(c - 1 == 0)) 8 83
      gpr := (s.gpr.set 6 (pL + 32) |>.set 2 (pR + 32) |>.set 1 (c - 1))
      ymm := (s.ymm.set 2 a |>.set 3 b |>.set 4 pLo |>.set 5 pHi |>.set 6 shH |>.set 7 shL |>.set 0 lo' |>.set 1 hi')
      cf := cf2
      ofFlag := evalX86IncDecOf false true c
      zf := c - 1 == 0
      ymmDirty := true },
   vpclmulBodyObs pL pR)

def asmFfiVpclmulBodyStep (m : AsmFfiBdozMac) : AsmFfiBdozMac × List StepObs :=
  let a := readMem256 m.mem m.lhsPtr
  let b := readMem256 m.mem m.rhsPtr
  (⟨m.lhsPtr + 32, m.rhsPtr + 32, m.outPtr,
    karatsubaStepLo m.accLo a b, karatsubaStepHi m.accHi a b, m.remaining - 1, m.mem⟩,
   vpclmulBodyObs m.lhsPtr m.rhsPtr)

theorem asmFfiVpclmul_cuts_accum (k : Nat) (pL pR outP : UInt64) (lo hi : Vec256) (rem : Nat) (mem : UInt64 → UInt8) :
    let final := (runCuts asmFfiVpclmulBodyStep k ⟨pL, pR, outP, lo, hi, rem, mem⟩).1
    (final.accLo, final.accHi) = bdozMacAccum k mem pL pR lo hi ∧ final.mem = mem ∧ final.outPtr = outP := by
  induction k generalizing pL pR lo hi rem with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ k ih =>
    simpa [runCuts, asmFfiVpclmulBodyStep, bdozMacAccum] using
      ih (pL + 32) (pR + 32) (karatsubaStepLo lo (readMem256 mem pL) (readMem256 mem pR))
        (karatsubaStepHi hi (readMem256 mem pL) (readMem256 mem pR)) (rem - 1)

/-- Symbol execution behind a zero-count guard on `rcx`. The guard branch is a hand-written
model of the Rust wrapper's early return on empty input, not decoded machine code. -/
def vpclmulGuardedRun (fetch : Nat → Option (DecodedInstr X86Instr))
    (fuel : Nat) (s : X86State) : X86State × List StepObs :=
  if s.gpr.get 1 == 0 then
    ({ s with
        pc := 203
        gpr := s.gpr.set 0 0
        ymmDirty := false
        halted := true },
     [⟨0, [], true⟩])
  else runX86Fetch fetch fuel s

def asmFfiVpclmulRun (rsp : UInt64) (n : Word) (baseL baseR outP : UInt64) (mem : UInt64 → UInt8) :
    AsmFfiBdozMac × List StepObs :=
  if n = 0 then
    (⟨baseL, baseR, outP, Vec256.zero, Vec256.zero, 0, mem⟩,
     [⟨0, [], true⟩])
  else
    let loop := runCuts asmFfiVpclmulBodyStep n.toNat ⟨baseL, baseR, outP, Vec256.zero, Vec256.zero, n.toNat, mem⟩
    let red := poly87Reduce256 loop.1.accLo loop.1.accHi
    ({ loop.1 with mem := writeMem256 mem outP red },
     vpclmulEntryObs ++ loop.2 ++ (vpclmulExitObs rsp) outP)

theorem vpclmul_entry_full (fetch : Nat → Option (DecodedInstr X86Instr))
    (hf : ∀ d ∈ vpclmulBdozMacProg, fetch d.offset = some d)
    (g : Bank16 UInt64) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Vec256)
    (cf o zf dy : Bool) (m : UInt64 → UInt8) (fuel : Nat) :
    runX86Fetch fetch (2 + fuel)
      ⟨0, g, ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
        cf, o, zf, dy, false, m⟩ =
      let u := runX86Fetch fetch fuel
        ⟨8, g, ⟨Vec256.zero, Vec256.zero, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
          cf, o, zf, true, false, m⟩
      (u.1, vpclmulEntryObs ++ u.2) := by
  rw [show 2 + fuel = (fuel + 1) + 1 from by omega]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vbinOp256, b16get_0, vpxor_self, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vbinOp256, b16get_1, vpxor_self, b16set_1, vpclmulEntryObs]
  rfl

theorem vpclmul_body_full (fetch : Nat → Option (DecodedInstr X86Instr))
    (hf : ∀ d ∈ vpclmulBdozMacProg, fetch d.offset = some d)
    (r0 c pR r3 r4 r5 pL r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (lo hi y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Vec256)
    (cf o zf dy : Bool) (m : UInt64 → UInt8) (fuel : Nat) :
    let s : X86State := ⟨8, ⟨r0, c, pR, r3, r4, r5, pL, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
      ⟨lo, hi, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
      cf, o, zf, dy, false, m⟩
    runX86Fetch fetch (17 + fuel) s =
      ((runX86Fetch fetch fuel (vpclmulBodyStep s).1).1,
       (vpclmulBodyStep s).2 ++ (runX86Fetch fetch fuel (vpclmulBodyStep s).1).2) := by
  dsimp only
  rw [show 17 + fuel = ((((((((((((((((fuel + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 from by omega]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vload256, b16get_6, b16set_2]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vload256, b16get_2, b16set_3]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vpclmul256, b16get_2, b16get_3, b16set_4]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vpclmul256, b16get_2, b16get_3, b16set_5]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vpclmul256, b16get_2, b16get_3, b16set_6]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vpclmul256, b16get_2, b16get_3, b16set_7]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vbinOp256, b16get_6, b16get_7, b16set_6]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vshift256, b16get_6, b16set_7]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vshift256, b16get_6, b16set_6]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vbinOp256, b16get_4, b16get_7, b16set_4]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vbinOp256, b16get_5, b16get_6, b16set_5]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vbinOp256, b16get_0, b16get_4, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vbinOp256, b16get_1, b16get_5, b16set_1]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_addImm64, b16get_6, b16set_6]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_addImm64, b16get_2, b16set_2]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_dec64, b16get_1, b16set_1]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]
  simp only [stepX86Full_jnz, vpclmulBodyStep, vpclmulBodyObs,
    b16get_0, b16get_1, b16get_2, b16get_6,
    b16set_0, b16set_1, b16set_2, b16set_3, b16set_4, b16set_5, b16set_6, b16set_7]
  rfl

theorem vpclmul_exit_full (fetch : Nat → Option (DecodedInstr X86Instr))
    (hf : ∀ d ∈ vpclmulBdozMacProg, fetch d.offset = some d)
    (r0 r1 r2 r3 r4 r5 r6 outP r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (lo hi y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Vec256)
    (cf o zf dy : Bool) (m : UInt64 → UInt8) (extra : Nat) :
    runX86Fetch fetch (33 + extra)
      ⟨83, ⟨r0, r1, r2, r3, r4, r5, r6, outP, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨lo, hi, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
        cf, o, zf, dy, false, m⟩ =
      (⟨(readMem64 (writeMem256 m outP (poly87Reduce256 lo hi)) r4).toNat, ⟨0, 0, 0, r3, r4 + 8, r5, 0, 0, 0, 0, 0, 0, r12, r13, r14, r15⟩,
        ⟨Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero,
          Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero⟩,
        false, false, true, false, true, writeMem256 m outP (poly87Reduce256 lo hi)⟩,
       (vpclmulExitObs r4) outP) := by
  have h87 : maskGprWidth false 0x87 = 0x87 := rfl
  rw [show 33 + extra = ((((((((((((((((((((((((((((((((extra + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 from by omega]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_movImm, h87, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vmovGprToXmm, maskGprWidth_true, b16get_0, b16set_8]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vpbroadcastQ, b16get_8, b16set_8]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vpclmul256, b16get_1, b16get_8, b16set_4]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vshift256, b16get_4, b16set_5]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vshift256, b16get_4, b16set_6]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vbinOp256, b16get_0, b16get_5, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vbinOp256, b16get_1, b16get_6, b16set_1]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vpclmul256, b16get_1, b16get_8, b16set_4]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vbinOp256, b16get_0, b16get_4, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vstore256, b16get_7, b16get_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vbinOp256, b16get_0, vpxor_self, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vbinOp256, b16get_1, vpxor_self, b16set_1]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vbinOp256, b16get_2, vpxor_self, b16set_2]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vbinOp256, b16get_3, vpxor_self, b16set_3]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vbinOp256, b16get_4, vpxor_self, b16set_4]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vbinOp256, b16get_5, vpxor_self, b16set_5]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vbinOp256, b16get_6, vpxor_self, b16set_6]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vbinOp256, b16get_7, vpxor_self, b16set_7]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vbinOp256, b16get_8, vpxor_self, b16set_8]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_xorRR, b16get_0, mask32_xor_self_eq, u64_zero_beq_true, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vzeroall]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_vzeroupper, vzeroupper_bank16, zeroUpperVec256_zero]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_xorRR, b16get_7, mask32_xor_self_eq, u64_zero_beq_true, b16set_7]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_xorRR, b16get_6, mask32_xor_self_eq, u64_zero_beq_true, b16set_6]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_xorRR, b16get_2, mask32_xor_self_eq, u64_zero_beq_true, b16set_2]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_xorRR, b16get_1, mask32_xor_self_eq, u64_zero_beq_true, b16set_1]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_xorRR, b16get_8, mask32_xor_self_eq, u64_zero_beq_true, b16set_8]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_xorRR, b16get_9, mask32_xor_self_eq, u64_zero_beq_true, b16set_9]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_xorRR, b16get_10, mask32_xor_self_eq, u64_zero_beq_true, b16set_10]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_xorRR, b16get_11, mask32_xor_self_eq, u64_zero_beq_true, b16set_11]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]; simp only [stepX86Full_xorRR, b16get_0, mask32_xor_self_eq, u64_zero_beq_true, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl (by simp only [vpclmulBdozMacProg_eq]; rfl)]
  simp only [stepX86Full_ret, b16get_4, b16set_4, poly87Reduce256, vpclmulExitObs]
  rw [runX86Fetch_halted _ _ _ rfl]

def VpclmulRel (s₀ : X86State) (n v : Nat) (a : X86State) (m : AsmFfiBdozMac) : Prop :=
  let baseL := s₀.gpr.get 6
  let baseR := s₀.gpr.get 2
  ∃ cf o zf : Bool, ∃ y2 y3 y4 y5 y6 y7 : Vec256,
    a = ⟨if v = n then 83 else 8,
          (s₀.gpr.set 6 (ptrStride baseL 32 v) |>.set 2 (ptrStride baseR 32 v)
            |>.set 1 (UInt64.ofNat (n - v))),
          (s₀.ymm.set 2 y2 |>.set 3 y3 |>.set 4 y4 |>.set 5 y5 |>.set 6 y6 |>.set 7 y7
            |>.set 0 m.accLo |>.set 1 m.accHi),
          cf, o, zf, true, false, s₀.mem⟩ ∧
    m.lhsPtr = ptrStride baseL 32 v ∧
    m.rhsPtr = ptrStride baseR 32 v ∧
    m.outPtr = s₀.gpr.get 7 ∧
    m.remaining = n - v ∧
    m.mem = s₀.mem

def VpclmulLoopPost (s₀ : X86State) (n : Nat) (a : X86State) (m : AsmFfiBdozMac) : Prop :=
  let baseL := s₀.gpr.get 6
  let baseR := s₀.gpr.get 2
  ∃ cf o zf : Bool, ∃ y2 y3 y4 y5 y6 y7 : Vec256,
    a = ⟨83,
          (s₀.gpr.set 6 (ptrStride baseL 32 n) |>.set 2 (ptrStride baseR 32 n) |>.set 1 0),
          (s₀.ymm.set 2 y2 |>.set 3 y3 |>.set 4 y4 |>.set 5 y5 |>.set 6 y6 |>.set 7 y7
            |>.set 0 m.accLo |>.set 1 m.accHi),
          cf, o, zf, true, false, s₀.mem⟩ ∧
    m.outPtr = s₀.gpr.get 7 ∧
    m.remaining = 0 ∧
    m.mem = s₀.mem

/-- Both zero and positive expected results use the polynomial-field specification. -/
theorem vpclmulExpected_field (n : Word) (mem : UInt64 → UInt8) (pL pR : UInt64)
    (lane : Nat) (hl : lane < 2) :
    let acc := bdozMacAccum n.toNat mem pL pR Vec256.zero Vec256.zero
    gf128Lane (if n = 0 then Vec256.zero else poly87Reduce256 acc.1 acc.2) ⟨lane, hl⟩ =
      gf128BdozFieldSum n.toNat mem pL pR ⟨lane, hl⟩ := by
  by_cases hn : n = 0
  · subst n
    simp [gf128Lane, gf128Words_eq, gf128BdozFieldSum, Vec256.zero]
  · simp only [hn, ↓reduceIte]
    exact gf128_bdozMacAccum_field n.toNat mem pL pR lane hl

def VpclmulPost (s₀ : X86State) (n : Word) (out : X86State) (m : AsmFfiBdozMac) : Prop :=
  let acc := bdozMacAccum n.toNat s₀.mem (s₀.gpr.get 6) (s₀.gpr.get 2) Vec256.zero Vec256.zero
  let expected := if n = 0 then Vec256.zero else poly87Reduce256 acc.1 acc.2
  out.halted = true ∧
  out.mem = m.mem ∧
  out.mem = (if n = 0 then s₀.mem else writeMem256 s₀.mem (s₀.gpr.get 7) expected) ∧
  out.gpr.get 0 = 0 ∧ out.gpr.get 1 = 0 ∧
  out.ymmDirty = false ∧
  (n ≠ 0 → out.ymm.get 0 = Vec256.zero ∧ out.ymm.get 1 = Vec256.zero ∧
    out.ymm.get 2 = Vec256.zero ∧ out.ymm.get 3 = Vec256.zero ∧
    out.ymm.get 4 = Vec256.zero ∧ out.ymm.get 5 = Vec256.zero ∧
    out.ymm.get 6 = Vec256.zero ∧ out.ymm.get 7 = Vec256.zero ∧
    out.ymm.get 8 = Vec256.zero) ∧
  out.gpr.get 4 = (if n = 0 then s₀.gpr.get 4 else s₀.gpr.get 4 + 8) ∧ out.gpr.get 3 = s₀.gpr.get 3 ∧ out.gpr.get 5 = s₀.gpr.get 5 ∧
  out.gpr.get 12 = s₀.gpr.get 12 ∧ out.gpr.get 13 = s₀.gpr.get 13 ∧
  out.gpr.get 14 = s₀.gpr.get 14 ∧ out.gpr.get 15 = s₀.gpr.get 15 ∧
  ∀ lane : Nat, ∀ hl : lane < 2, gf128Lane expected ⟨lane, hl⟩ =
    gf128BdozFieldSum n.toNat s₀.mem (s₀.gpr.get 6) (s₀.gpr.get 2) ⟨lane, hl⟩

/-- What the production epilogue leaves in the vector bank and the caller-saved scratch
registers after a nonempty call: `vzeroall` clears every `ymm`, and `rdx`, `rsi`, `rdi`,
`r8`–`r11` are zeroed (`rax` and `rcx` are covered by `VpclmulPost`). -/
def VpclmulScratchWiped (n : Word) (out : X86State) : Prop :=
  n ≠ 0 → (∀ i, i < 16 → out.ymm.get i = Vec256.zero) ∧
    out.gpr.get 2 = 0 ∧ out.gpr.get 6 = 0 ∧ out.gpr.get 7 = 0 ∧ out.gpr.get 8 = 0 ∧
    out.gpr.get 9 = 0 ∧ out.gpr.get 10 = 0 ∧ out.gpr.get 11 = 0

/-- Postcondition of `qsag_asm_tower128_bdoz_mac_vpclmul`: the MAC result (`VpclmulPost`) together
with the scratch wipe. -/
def VpclmulMacPost (s₀ : X86State) (n : Word) (out : X86State) (m : AsmFfiBdozMac) : Prop :=
  VpclmulPost s₀ n out m ∧ VpclmulScratchWiped n out

def vpclmulPosCert (s₀ : X86State) (n : Nat) (hn : 0 < n) (hbound : n < 2 ^ 64) :
    LoopRelationCert X86State AsmFfiBdozMac n vpclmulBodyStep asmFfiVpclmulBodyStep
      ⟨8, s₀.gpr.set 1 (UInt64.ofNat n), (s₀.ymm.set 0 Vec256.zero |>.set 1 Vec256.zero),
        s₀.cf, s₀.ofFlag, s₀.zf, true, false, s₀.mem⟩
      ⟨s₀.gpr.get 6, s₀.gpr.get 2, s₀.gpr.get 7, Vec256.zero, Vec256.zero, n, s₀.mem⟩
      (VpclmulLoopPost s₀ n) where
  LoopRel := VpclmulRel s₀ n
  schedule := fun v => vpclmulBodyObs (ptrStride (s₀.gpr.get 6) 32 v) (ptrStride (s₀.gpr.get 2) 32 v)
  entry := by
    obtain ⟨_, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
      ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
      cf, o, zf, dy, _, m⟩ := s₀
    refine ⟨cf, o, zf, y2, y3, y4, y5, y6, y7, ?_, rfl, rfl, rfl, by dsimp only; omega, rfl⟩
    simp [ptrStride, Nat.ne_of_lt hn, b16get_2, b16get_6,
      b16set_0, b16set_1, b16set_2, b16set_3, b16set_4, b16set_5, b16set_6, b16set_7]
  body := by
    intro v a m hv ⟨cf, o, zf, y2, y3, y4, y5, y6, y7, ha, hpL, hpR, hout, hmr, hmem⟩
    subst ha
    obtain ⟨_, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
      ⟨oy0, oy1, oy2, oy3, oy4, oy5, oy6, oy7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
      _, _, _, _, _, mem⟩ := s₀
    have hpos : 0 < n - v := by omega
    have hlt : n - v < 2 ^ 64 := by omega
    have hdec := u64_ofNat_sub_one hpos hlt
    have hsub : n - v - 1 = n - (v + 1) := by omega
    have hzf : (UInt64.ofNat (n - (v + 1)) == 0) = decide (v + 1 = n) := by
      rw [u64_ofNat_eq_zero_iff (by omega)]
      by_cases heq : v + 1 = n <;> simp [heq] <;> omega
    have hjcc : jccPc (!(UInt64.ofNat (n - (v + 1)) == 0)) 8 83 = (if v + 1 = n then 83 else 8) := by
      rw [hzf]
      by_cases heq : v + 1 = n <;> simp [heq, jccPc]
    let pL := ptrStride r6 32 v
    let pR := ptrStride r2 32 v
    let va := readMem256 mem pL
    let vb := readMem256 mem pR
    let mid := evalVecBin256 .vpxor (clmul256 va vb 0x01) (clmul256 va vb 0x10)
    let shL := evalVecShift256 .vpslldq mid 8
    let shH := evalVecShift256 .vpsrldq mid 8
    let pLo := evalVecBin256 .vpxor (clmul256 va vb 0x00) shL
    let pHi := evalVecBin256 .vpxor (clmul256 va vb 0x11) shH
    let cf1 := (evalX86Alu .add true pL 32 cf).2.1
    let cf2 := (evalX86Alu .add true pR 32 cf1).2.1
    refine ⟨⟨cf2, evalX86IncDecOf false true (UInt64.ofNat (n - v)), UInt64.ofNat (n - (v + 1)) == 0,
      va, vb, pLo, pHi, shH, shL,
      ?_, ?_, ?_, hout, ?_, hmem⟩, ?_, ?_⟩
    · simp only [vpclmulBodyStep, asmFfiVpclmulBodyStep, karatsubaStepLo, karatsubaStepHi,
        b16get_0, b16get_1, b16get_2, b16get_6,
        b16set_0, b16set_1, b16set_2, b16set_3, b16set_4, b16set_5, b16set_6, b16set_7,
        hdec, hsub, hjcc, ptrStride, hpL, hpR, hmem]
      rfl
    · simp [asmFfiVpclmulBodyStep, hpL, ptrStride, b16get_6]
    · simp [asmFfiVpclmulBodyStep, hpR, ptrStride, b16get_2]
    · simp [asmFfiVpclmulBodyStep, hmr]; omega
    · simp [vpclmulBodyStep, b16get_2, b16get_6, b16set_1, b16set_2, b16set_6]
    · simp [asmFfiVpclmulBodyStep, hpL, hpR, b16get_2, b16get_6]
  exit := by
    intro a m ⟨cf, o, zf, y2, y3, y4, y5, y6, y7, ha, _, _, hout, hmr, hmem⟩
    exact ⟨cf, o, zf, y2, y3, y4, y5, y6, y7, by simpa using ha, hout, by omega, hmem⟩

theorem vpclmul_replay_loop (fetch : Nat → Option (DecodedInstr X86Instr))
    (hf : ∀ d ∈ vpclmulBdozMacProg, fetch d.offset = some d)
    (s₀ : X86State) (n : Nat) (hn : 0 < n) (hbound : n < 2 ^ 64) (rem : Nat) :
    ∀ v a m fuel, v + rem = n → VpclmulRel s₀ n v a m →
      runX86Fetch fetch (17 * rem + fuel) a =
        let loop := runCuts vpclmulBodyStep rem a
        let u := runX86Fetch fetch fuel loop.1
        (u.1, loop.2 ++ u.2) := by
  induction rem with
  | zero => intro v a m fuel _ _; simp [runCuts]
  | succ k ih =>
    intro v a m fuel hv hrel
    have hvn : v < n := by omega
    rcases hrel with ⟨cf, o, zf, y2, y3, y4, y5, y6, y7, ha, hpL, hpR, hout, hmr, hmem⟩
    have hrel' : VpclmulRel s₀ n v a m := ⟨cf, o, zf, y2, y3, y4, y5, y6, y7, ha, hpL, hpR, hout, hmr, hmem⟩
    have hbody := (vpclmulPosCert s₀ n hn hbound).body v a m hvn hrel'
    obtain ⟨_, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
      ⟨oy0, oy1, oy2, oy3, oy4, oy5, oy6, oy7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
      _, _, _, _, _, mem⟩ := s₀
    have ha8 : a = ⟨8, ⟨r0, UInt64.ofNat (n - v), ptrStride r2 32 v, r3, r4, r5, ptrStride r6 32 v,
        r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨m.accLo, m.accHi, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
        cf, o, zf, true, false, mem⟩ := by
      simpa [Nat.ne_of_lt hvn, b16get_2, b16get_6,
        b16set_0, b16set_1, b16set_2, b16set_3, b16set_4, b16set_5, b16set_6, b16set_7] using ha
    rw [show 17 * (k + 1) + fuel = 17 + (17 * k + fuel) from by omega, ha8]
    rw [vpclmul_body_full fetch hf]
    rw [← ha8]
    rw [ih (v + 1) (vpclmulBodyStep a).1 (asmFfiVpclmulBodyStep m).1 fuel (by omega) hbody.1]
    simp [runCuts, List.append_assoc]

/-- Complete `UnrestrictedLoopCert` for `qsag_asm_tower128_bdoz_mac_vpclmul` over **all `n : BitVec 64`**. -/
def vpclmulBdozMacUnrestrictedCert (fetch : Nat → Option (DecodedInstr X86Instr))
    (hf : ∀ d ∈ vpclmulBdozMacProg, fetch d.offset = some d)
    (s₀ : X86State) (fuel : Nat) (hpc : s₀.pc = 0) (hh : s₀.halted = false)
    (n : Word) (hcount : s₀.gpr.get 1 = UInt64.ofBitVec n)
    (hfuel : 17 * n.toNat + 35 ≤ fuel) :
    UnrestrictedLoopCert X86State AsmFfiBdozMac n
      (vpclmulGuardedRun fetch fuel)
      (fun m => asmFfiVpclmulRun (s₀.gpr.get 4) n m.lhsPtr m.rhsPtr m.outPtr m.mem)
      vpclmulBodyStep asmFfiVpclmulBodyStep
      s₀ ⟨s₀.gpr.get 6, s₀.gpr.get 2, s₀.gpr.get 7, Vec256.zero, Vec256.zero, n.toNat, s₀.mem⟩
      ⟨8, s₀.gpr.set 1 (UInt64.ofNat n.toNat), (s₀.ymm.set 0 Vec256.zero |>.set 1 Vec256.zero),
        s₀.cf, s₀.ofFlag, s₀.zf, true, false, s₀.mem⟩
      ⟨s₀.gpr.get 6, s₀.gpr.get 2, s₀.gpr.get 7, Vec256.zero, Vec256.zero, n.toNat, s₀.mem⟩
      (VpclmulLoopPost s₀ n.toNat)
      (VpclmulMacPost s₀ n) where
  zeroSchedule := [⟨0, [], true⟩]
  entrySchedule := vpclmulEntryObs
  bodySchedule := fun v => vpclmulBodyObs (ptrStride (s₀.gpr.get 6) 32 v) (ptrStride (s₀.gpr.get 2) 32 v)
  exitSchedule := (vpclmulExitObs (s₀.gpr.get 4)) (s₀.gpr.get 7)
  zero_cut := by
    intro hz; subst hz
    have hg0 : (s₀.gpr.get 1 == 0) = true := by simp [hcount]
    dsimp only [vpclmulGuardedRun, asmFfiVpclmulRun]
    rw [ite_eq_left hg0, ite_eq_left rfl]
    obtain ⟨_, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, _, _, _, _, _, _, _⟩ := s₀
    have hr1 : r1 = 0 := hcount
    refine ⟨⟨⟨rfl, rfl, rfl, rfl, hr1, rfl, fun h => absurd rfl h, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      vpclmulExpected_field 0 (fun _ => 0) 0 0⟩, fun h => absurd rfl h⟩, rfl, rfl⟩
  pos_cert := fun hn =>
    vpclmulPosCert s₀ n.toNat (bv64_pos_of_ne_zero n hn) n.isLt
  pos_sched := fun _ => rfl
  pos_replay := by
    intro hn hlp hal hml
    have hg0 : ¬ ((s₀.gpr.get 1 == 0) = true) := by
      rw [beq_false_of_ne (hcount ▸ (bv64_ne_zero_iff_u64_ne_zero n).mp hn)]; decide
    dsimp only [vpclmulGuardedRun, asmFfiVpclmulRun]
    rw [ite_eq_right hg0, ite_eq_right hn]
    obtain ⟨extra, hextra⟩ : ∃ extra, fuel = 2 + (17 * n.toNat + (33 + extra)) :=
      ⟨fuel - (17 * n.toNat + 35), by omega⟩
    rw [hextra]
    obtain ⟨pc, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
      ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
      cf, o, zf, dy, hlt, m⟩ := s₀
    cases hpc; cases hh
    have hr1 : r1 = UInt64.ofNat n.toNat := by
      apply u64_eq_of_toNat_eq
      have : r1 = UInt64.ofBitVec n := hcount
      rw [this, UInt64.toNat_ofNat', Nat.mod_eq_of_lt n.isLt]; rfl
    rw [vpclmul_entry_full fetch hf]
    have headEq : (⟨8, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨Vec256.zero, Vec256.zero, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
        cf, o, zf, true, false, m⟩ : X86State) =
      ⟨8, (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15).set 1 (UInt64.ofNat n.toNat),
        ((Bank16.mk y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).set 0 Vec256.zero |>.set 1 Vec256.zero),
        cf, o, zf, true, false, m⟩ := by
      simp [hr1, b16set_0, b16set_1]
    rw [headEq]
    have hpos := bv64_pos_of_ne_zero n hn
    have hrep := vpclmul_replay_loop fetch hf
      ⟨0, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩, cf, o, zf, dy, false, m⟩
      n.toNat hpos n.isLt n.toNat 0 _ ⟨r6, r2, r7, Vec256.zero, Vec256.zero, n.toNat, m⟩ (33 + extra) (by omega)
      (vpclmulPosCert _ n.toNat hpos n.isLt).entry
    dsimp only at hrep ⊢
    rw [hrep]
    rcases hlp with ⟨cfL, oL, zfL, y2L, y3L, y4L, y5L, y6L, y7L, haL, _, _, _⟩
    let mFinal := (runCuts asmFfiVpclmulBodyStep n.toNat ⟨r6, r2, r7, Vec256.zero, Vec256.zero, n.toNat, m⟩).1
    have ha83 : (runCuts vpclmulBodyStep n.toNat
        ⟨8, (Bank16.mk r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15).set 1 (UInt64.ofNat n.toNat),
          ((Bank16.mk y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).set 0 Vec256.zero
            |>.set 1 Vec256.zero),
          cf, o, zf, true, false, m⟩).1 =
      ⟨83, ⟨r0, 0, ptrStride r2 32 n.toNat, r3, r4, r5, ptrStride r6 32 n.toNat,
        r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨mFinal.accLo, mFinal.accHi, y2L, y3L, y4L, y5L, y6L, y7L, y8, y9, y10, y11, y12, y13, y14, y15⟩,
        cfL, oL, zfL, true, false, m⟩ := by
      simpa [mFinal, b16get_2, b16get_6, b16get_7,
        b16set_0, b16set_1, b16set_2, b16set_3, b16set_4, b16set_5, b16set_6, b16set_7] using haL
    rw [ha83, vpclmul_exit_full fetch hf]
    obtain ⟨hacc, _, _⟩ := asmFfiVpclmul_cuts_accum n.toNat r6 r2 r7 Vec256.zero Vec256.zero n.toNat m
    have hred : poly87Reduce256 mFinal.accLo mFinal.accHi =
        poly87Reduce256 (bdozMacAccum n.toNat m r6 r2 Vec256.zero Vec256.zero).1
          (bdozMacAccum n.toNat m r6 r2 Vec256.zero Vec256.zero).2 := by
      have h1 := congrArg Prod.fst hacc
      have h2 := congrArg Prod.snd hacc
      dsimp only at h1 h2
      rw [h1, h2]
    refine ⟨?_, by simp only [List.append_assoc, b16get_7]; rfl, rfl⟩
    refine ⟨⟨rfl, rfl, ?_, rfl, rfl, rfl, ?_, (by rw [ite_eq_right hn]; rfl), rfl, rfl, rfl, rfl, rfl, rfl, vpclmulExpected_field n m r6 r2⟩, ?_⟩
    · simp only [b16get_2, b16get_6, b16get_7, ite_eq_right hn, hred]
    · intro _
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · intro _
      exact ⟨fun i hi => match i, hi with
        | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl
        | 6, _ => rfl | 7, _ => rfl | 8, _ => rfl | 9, _ => rfl | 10, _ => rfl | 11, _ => rfl
        | 12, _ => rfl | 13, _ => rfl | 14, _ => rfl | 15, _ => rfl
        | i + 16, h => absurd h (by omega), rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Refinement and `StepObs` noninterference for the guarded runner of `qsag_asm_tower128_bdoz_mac_vpclmul` at every
`n : BitVec 64`. For `n ≠ 0` the runner is byte-decoded execution of the symbol
(`tower128_bdoz_mac_vpclmul_sydtv_refines_pos`); for `n = 0` it is the modelled wrapper early return. -/
theorem tower128_bdoz_mac_vpclmul_sydtv_refines_all_n (s₁ s₂ : X86State) (fuel : Nat) (n : Word)
    (hpc₁ : s₁.pc = 0) (hh₁ : s₁.halted = false) (hc₁ : s₁.gpr.get 1 = UInt64.ofBitVec n)
    (hpc₂ : s₂.pc = 0) (hh₂ : s₂.halted = false) (hc₂ : s₂.gpr.get 1 = UInt64.ofBitVec n)
    (hpL : s₁.gpr.get 6 = s₂.gpr.get 6) (hpR : s₁.gpr.get 2 = s₂.gpr.get 2)
    (hout : s₁.gpr.get 7 = s₂.gpr.get 7)
    (hfuel : 17 * n.toNat + 35 ≤ fuel)
    (hsp : s₁.gpr.get 4 = s₂.gpr.get 4) :
    let out₁ := vpclmulGuardedRun (decodeX86One vpclmulBdozMacCode) fuel s₁
    let out₂ := vpclmulGuardedRun (decodeX86One vpclmulBdozMacCode) fuel s₂
    let ffi₁ := asmFfiVpclmulRun (s₁.gpr.get 4) n (s₁.gpr.get 6) (s₁.gpr.get 2) (s₁.gpr.get 7) s₁.mem
    VpclmulMacPost s₁ n out₁.1 ffi₁.1 ∧ out₁.2 = out₂.2 ∧ out₁.2 = ffi₁.2 := by
  dsimp only
  let c₁ := vpclmulBdozMacUnrestrictedCert (decodeX86One vpclmulBdozMacCode) vpclmulBdozMac_fetch_decodeOne
    s₁ fuel hpc₁ hh₁ n hc₁ hfuel
  let c₂ := vpclmulBdozMacUnrestrictedCert (decodeX86One vpclmulBdozMacCode) vpclmulBdozMac_fetch_decodeOne
    s₂ fuel hpc₂ hh₂ n hc₂ hfuel
  obtain ⟨hp, _, _⟩ := unrestricted_loop_refinement_sound c₁
  have hz : c₁.zeroSchedule = c₂.zeroSchedule := by
    simp [c₁, c₂, vpclmulBdozMacUnrestrictedCert, hout]
  have hsched : c₁.bodySchedule = c₂.bodySchedule := by
    funext v; simp [c₁, c₂, vpclmulBdozMacUnrestrictedCert, hpL, hpR]
  have hex : c₁.exitSchedule = c₂.exitSchedule := by
    simp [c₁, c₂, vpclmulBdozMacUnrestrictedCert, hout, hsp]
  obtain ⟨hni1, hni2⟩ := unrestricted_three_way_noninterference c₁ c₂ hz rfl hsched hex
  exact ⟨hp, hni1, hni2⟩

theorem vpclmulGuardedRun_pos (fetch : Nat → Option (DecodedInstr X86Instr)) (fuel : Nat)
    (s : X86State) (n : Word) (hn : n ≠ 0) (hc : s.gpr.get 1 = UInt64.ofBitVec n) :
    vpclmulGuardedRun fetch fuel s = runX86Fetch fetch fuel s := by
  have hg0 : ¬ ((s.gpr.get 1 == 0) = true) := by
    rw [beq_false_of_ne (hc ▸ (bv64_ne_zero_iff_u64_ne_zero n).mp hn)]; decide
  unfold vpclmulGuardedRun
  rw [ite_eq_right hg0]

/-- `qsag_asm_tower128_bdoz_mac_vpclmul`, raw symbol bytes, nonzero block count. -/
theorem tower128_bdoz_mac_vpclmul_sydtv_refines_pos (s₁ s₂ : X86State) (fuel : Nat) (n : Word)
    (hn : n ≠ 0)
    (hpc₁ : s₁.pc = 0) (hh₁ : s₁.halted = false) (hc₁ : s₁.gpr.get 1 = UInt64.ofBitVec n)
    (hpc₂ : s₂.pc = 0) (hh₂ : s₂.halted = false) (hc₂ : s₂.gpr.get 1 = UInt64.ofBitVec n)
    (hpL : s₁.gpr.get 6 = s₂.gpr.get 6) (hpR : s₁.gpr.get 2 = s₂.gpr.get 2)
    (hout : s₁.gpr.get 7 = s₂.gpr.get 7)
    (hfuel : 17 * n.toNat + 35 ≤ fuel)
    (hsp : s₁.gpr.get 4 = s₂.gpr.get 4) :
    VpclmulMacPost s₁ n (runX86One vpclmulBdozMacCode fuel s₁).1
      (asmFfiVpclmulRun (s₁.gpr.get 4) n (s₁.gpr.get 6) (s₁.gpr.get 2) (s₁.gpr.get 7) s₁.mem).1 ∧
    (runX86One vpclmulBdozMacCode fuel s₁).2 = (runX86One vpclmulBdozMacCode fuel s₂).2 ∧
    (runX86One vpclmulBdozMacCode fuel s₁).2 =
      (asmFfiVpclmulRun (s₁.gpr.get 4) n (s₁.gpr.get 6) (s₁.gpr.get 2) (s₁.gpr.get 7) s₁.mem).2 := by
  have h := tower128_bdoz_mac_vpclmul_sydtv_refines_all_n s₁ s₂ fuel n hpc₁ hh₁ hc₁ hpc₂ hh₂ hc₂
    hpL hpR hout hfuel hsp
  dsimp only at h
  rw [vpclmulGuardedRun_pos _ fuel s₁ n hn hc₁, vpclmulGuardedRun_pos _ fuel s₂ n hn hc₂] at h
  simpa only [runX86One_eq, runArm64One_eq] using h

/-! ## §9. `#tooth` Mutation-Sensitivity & Non-Vacuity / Inhabitedness Witnesses -/

/-- `#tooth`: mutating `ct_eq_bytes`'s monotone `or eax, r8d` accumulator into an overwrite
`mov eax, r8d` (`acc' := byteDiff x y`) falsely reports equality (`acc = 0`) on `[1, 0]` vs `[0, 0]`! -/
def brokenOverwriteEqAcc : Nat → (UInt64 → UInt8) → UInt64 → UInt64 → UInt64 → UInt64
  | 0, _, _, _, acc => acc
  | k + 1, m, pA, pB, _ => brokenOverwriteEqAcc k m (pA + 1) (pB + 1) (byteDiff (m pA) (m pB))

/-- `#tooth`: an early-exit equality loop that stops on the first mismatch leaks the secret mismatch
index through `List StepObs` trace length (`1` load-pair on mismatch at byte 0 vs `2` load-pairs on
agreement at byte 0), violating 3-way `StepObs` noninterference. -/
def brokenEarlyExitEqTrace : Nat → (UInt64 → UInt8) → UInt64 → UInt64 → List StepObs
  | 0, _, _, _ => []
  | k + 1, m, pA, pB =>
    let obs := [⟨5, [(pA, 1)], true⟩, ⟨9, [(pB, 1)], true⟩]
    if m pA != m pB then obs
    else obs ++ brokenEarlyExitEqTrace k m (pA + 1) (pB + 1)

/-- Empty input follows the wrapper return: no output-buffer write or memory observation. -/
theorem vpclmul_zero_preserves_memory (fetch : Nat → Option (DecodedInstr X86Instr))
    (fuel : Nat) (s : X86State) (hz : s.gpr.get 1 = 0) :
    (vpclmulGuardedRun fetch fuel s).1.mem = s.mem ∧
    (vpclmulGuardedRun fetch fuel s).2 = [⟨0, [], true⟩] := by
  simp [vpclmulGuardedRun, hz]

/-- The certified postcondition entails the independent field specification,
with both packed lanes and every positive block count. -/
theorem VpclmulPost_field (s out : X86State) (n : Word) (m : AsmFfiBdozMac)
    (hn : n ≠ 0) (h : VpclmulPost s n out m) :
    ∃ v : Vec256, out.mem = writeMem256 s.mem (s.gpr.get 7) v ∧
      ∀ lane : Nat, ∀ hl : lane < 2,
        gf128Lane v ⟨lane, hl⟩ =
          gf128BdozFieldSum n.toNat s.mem (s.gpr.get 6) (s.gpr.get 2) ⟨lane, hl⟩ := by
  refine ⟨_, ?_, gf128_bdozMacAccum_field n.toNat s.mem (s.gpr.get 6) (s.gpr.get 2)⟩
  simpa only [VpclmulPost, hn, ↓reduceIte] using h.2.2.1

/-- A finite graph of certified loop cuts. Each node performs one actual cut step;
the loop certificate's replay lemmas connect these steps to decoded instructions. -/
def cutsGraph {S : Type} (step : S → S × List StepObs) (n : Nat) : TvGraph S where
  node := fun pc => if pc < n then .Assign (fun s => (step s).1) (pc + 1) else .Ret (fun _ => 0)
  entry := 0
  loopHeads := []
  fuel := n + 1

private theorem cutsGraph_remaining {S : Type} (step : S → S × List StepObs)
    (n k pc : Nat) (h : pc + k = n) (s : S) :
    execFrom (cutsGraph step n) (fun _ => id) (k + 1) pc s =
      .ret 0 (runCuts step k s).1 := by
  induction k generalizing pc s with
  | zero =>
    have hp : pc = n := by omega
    subst pc
    simp [execFrom, cutsGraph, runCuts]
  | succ k ih =>
    have hp : pc < n := by omega
    simpa only [execFrom, cutsGraph, List.not_mem_nil, ↓reduceIte, hp, runCuts] using
      ih (pc + 1) (by omega) (step s).1

theorem flatten_cutsGraph {S : Type} (step : S → S × List StepObs) (n : Nat) (s : S) :
    evalFlattened (flattenDag (cutsGraph step n) (fun _ => id)) s =
      .ret 0 (runCuts step n s).1 := by
  rw [flattenDag_sound]
  exact cutsGraph_remaining step n n 0 (Nat.zero_add n) s

def FlattenedLoopRefines {A M : Type} {n : Nat}
    {as : A → A × List StepObs} {ms : M → M × List StepObs}
    {a : A} {m : M} {P : A → M → Prop}
    (_cert : LoopRelationCert A M n as ms a m P) : Prop :=
    ∃ af mf,
      evalFlattened (flattenDag (cutsGraph as n) (fun _ => id)) a = .ret 0 af ∧
      evalFlattened (flattenDag (cutsGraph ms n) (fun _ => id)) m = .ret 0 mf ∧
      P af mf ∧ (runCuts as n a).2 = (runCuts ms n m).2

/-- Flattened assembly and FFI-wrapper cut graphs inherit the certificate's postcondition
and equal leakage traces. This consumes the same certificate as byte replay. -/
theorem LoopRelationCert.flattened_refinement {A M : Type} {n : Nat}
    {as : A → A × List StepObs} {ms : M → M × List StepObs}
    {a : A} {m : M} {P : A → M → Prop}
    (c : LoopRelationCert A M n as ms a m P) :
    FlattenedLoopRefines c := by
  obtain ⟨hp, ha, hm⟩ := sewell_loop_relation_refinement_sound c
  exact ⟨_, _, flatten_cutsGraph as n a, flatten_cutsGraph ms n m, hp, ha.trans hm.symm⟩

theorem ctMemzeroX86PosCert_flattened (s₀ : X86State) (n : Nat) (hn : 0 < n) (hbound : n < 2 ^ 64) :
    FlattenedLoopRefines (ctMemzeroX86PosCert s₀ n hn hbound) :=
  LoopRelationCert.flattened_refinement (ctMemzeroX86PosCert s₀ n hn hbound)

theorem ctMemzeroArmPosCert_flattened (s₀ : Arm64State) (n : Nat) (hn : 0 < n) (hbound : n < 2 ^ 64)
    (h1 : armGet s₀.gpr 1 = UInt64.ofNat n) (hpc : s₀.pc = 0) (hh : s₀.halted = false) :
    FlattenedLoopRefines (ctMemzeroArmPosCert s₀ n hn hbound h1 hpc hh) :=
  LoopRelationCert.flattened_refinement (ctMemzeroArmPosCert s₀ n hn hbound h1 hpc hh)

theorem ctEqBytesPosCert_flattened (s₀ : X86State) (n : Nat) (hn : 0 < n) (hbound : n < 2 ^ 64) :
    FlattenedLoopRefines (ctEqBytesPosCert s₀ n hn hbound) :=
  LoopRelationCert.flattened_refinement (ctEqBytesPosCert s₀ n hn hbound)

theorem gfniShamirMacPosCert_flattened (s₀ : X86State) (n : Nat) (hn : 0 < n) (hbound : n < 2 ^ 64) :
    FlattenedLoopRefines (gfniShamirMacPosCert s₀ n hn hbound) :=
  LoopRelationCert.flattened_refinement (gfniShamirMacPosCert s₀ n hn hbound)

theorem vpclmulPosCert_flattened (s₀ : X86State) (n : Nat) (hn : 0 < n) (hbound : n < 2 ^ 64) :
    FlattenedLoopRefines (vpclmulPosCert s₀ n hn hbound) :=
  LoopRelationCert.flattened_refinement (vpclmulPosCert s₀ n hn hbound)


end Qsag.SydTv
