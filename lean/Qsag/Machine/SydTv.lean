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

def memzeroX86ExitObs : List StepObs :=
  [⟨15, [], true⟩, ⟨18, [], true⟩, ⟨20, [], true⟩, ⟨22, [], true⟩, ⟨24, [], true⟩, ⟨26, [], true⟩,
   ⟨29, [], true⟩, ⟨32, [], true⟩, ⟨35, [], true⟩, ⟨38, [], true⟩, ⟨40, [], true⟩]

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

def asmFfiMemzeroX86Run (n : Word) (base : UInt64) (mem : UInt64 → UInt8) : AsmFfiMemzero × List StepObs :=
  if n = 0 then (⟨base, 0, mem⟩, [⟨0, [], true⟩])
  else
    let loop := runCuts asmFfiMemzeroX86BodyStep n.toNat ⟨base, n.toNat, mem⟩
    (loop.1, memzeroX86EntryObs ++ loop.2 ++ memzeroX86ExitObs)

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
      (⟨40, (wipeScratch g).set 0 0, y, false, false, true, dy, true, m⟩, memzeroX86ExitObs) := by
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
  out.gpr.get 4 = s₀.gpr.get 4 ∧
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
      (fun m => asmFfiMemzeroX86Run n m.ptr m.mem)
      memzeroX86BodyStep asmFfiMemzeroX86BodyStep
      s₀ ⟨s₀.gpr.get 7, n.toNat, s₀.mem⟩
      ⟨5, (s₀.gpr.set 0 0 |>.set 1 (UInt64.ofNat n.toNat)), s₀.ymm, false, false, true, s₀.ymmDirty, false, s₀.mem⟩
      ⟨s₀.gpr.get 7, n.toNat, s₀.mem⟩
      (MemzeroX86LoopPost s₀ n.toNat)
      (MemzeroX86Post s₀ n) where
  zeroSchedule := [⟨0, [], true⟩]
  entrySchedule := memzeroX86EntryObs
  bodySchedule := fun v => memzeroX86BodyObs (ptrStride (s₀.gpr.get 7) 1 v)
  exitSchedule := memzeroX86ExitObs
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
    refine ⟨?_, by simp [List.append_assoc], rfl⟩
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
    (hfuel : 4 * n.toNat + 13 ≤ fuel) :
    let c₁ := ctMemzeroX86UnrestrictedCert (decodeX86One zeroCode) ctMemzeroX86_fetch_decodeOne
      s₁ fuel hpc₁ hh₁ n hc₁ hfuel
    let out₁ := ctMemzeroX86GuardedRun (decodeX86One zeroCode) fuel s₁
    let out₂ := ctMemzeroX86GuardedRun (decodeX86One zeroCode) fuel s₂
    let ffi₁ := asmFfiMemzeroX86Run n (s₁.gpr.get 7) s₁.mem
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
      (asmFfiMemzeroX86Run n (s₁.gpr.get 7) s₁.mem).2 := by
    obtain ⟨_, hb₁, hm₁⟩ := unrestricted_loop_refinement_sound c₁
    obtain ⟨_, hb₂, _⟩ := unrestricted_loop_refinement_sound c₂
    have hsched : c₁.bodySchedule = c₂.bodySchedule := by
      funext v; simp [c₁, c₂, ctMemzeroX86UnrestrictedCert, hptr]
    exact ⟨hb₁.trans ((congrArg (fun bs => fullSchedule n [⟨0, [], true⟩] memzeroX86EntryObs bs memzeroX86ExitObs) hsched).trans hb₂.symm),
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
    (hfuel : 4 * n.toNat + 13 ≤ fuel) :
    MemzeroX86Post s₁ n (runX86One zeroCode fuel s₁).1 (asmFfiMemzeroX86Run n (s₁.gpr.get 7) s₁.mem).1 ∧
    (runX86One zeroCode fuel s₁).2 = (runX86One zeroCode fuel s₂).2 ∧
    (runX86One zeroCode fuel s₁).2 = (asmFfiMemzeroX86Run n (s₁.gpr.get 7) s₁.mem).2 := by
  have h := ct_memzero_x86_64_sydtv_refines_all_n s₁ s₂ fuel n hpc₁ hh₁ hc₁ hpc₂ hh₂ hc₂ hptr hfuel
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

