module
public import Qsag.Machine.ElfBinaryVerify
public import Qsag.Machine.McRefine
public import Qsag.Machine.ElfParse
import Qsag.Tactic.AssuranceKit
import Qsag.Math.Constructive
import all Qsag.Machine.ElfBinaryVerify
import all Qsag.Machine.McRefine
import all Qsag.Machine.ElfFixtureSlices
public section

/-!
# `Qsag.Machine.SydTvTranslationValidation` — Sewell–Myreen–Klein Cut-Point Translation Validation

Untrusted search / certificate checking over **real byte-decoded `ElfBinaryVerify` instructions**
(`decodeX86One` / `decodeArm64One`, `stepX86` / `runX86`, `stepArm64` / `runArm64`, `StepObs`)
extracted from compiled `qsag_asm` `.rlib` archives (`ElfFixtureSlices` / `ElfParse`):

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
   Every cut replays as concrete multi-instruction runs of `ElfBinaryVerify.stepX86` / `stepArm64`
   fetched live from `.rlib` symbol bytes via `decodeX86One` / `decodeArm64One` AND via
   `ElfBinaryVerify.runX86` / `runArm64` over `decodeX86Stream` / `decodeArm64Stream`.
3. **Five Certified Looping `.rlib` Kernels (Scalar, Multi-Pointer, Accumulator, GFNI & VPCLMUL SIMD)**:
   - `qsag_asm_ct_memzero_x86_64` (`x86ExtractedSlices[15]`, 19 B): 1-pointer affine + byte zeroing.
   - `qsag_asm_ct_memzero_aarch64` (`aarch64ExtractedSlices[6]`, 20 B): AArch64 post-index affine + byte zeroing.
   - `qsag_asm_ct_eq_bytes_x86_64` (`x86ExtractedSlices[14]`, 43 B): 2-pointer affine + OR-of-XOR accumulator.
   - `qsag_asm_gf256_shamir_mac_gfni` (`x86ExtractedSlices[3]`, 135 B): 2-pointer 32B stride + GFNI Wiedemann `T₃` SIMD MAC.
   - `qsag_asm_tower128_bdoz_mac_vpclmul` (`x86ExtractedSlices[6]`, 179 B): 2-pointer 32B stride + dual-256b Karatsuba carryless XOR accumulators + `0x87` reduction.
-/

namespace Qsag.SydTv

open Qsag

set_option autoImplicit false

-- These instances are proved classically; without them `simp` discharges `UInt64` equality
-- tests through the decidable-equality instance instead.
attribute [-instance] UInt64.instLawfulEqOrd UInt64.instLawfulOrderOrd

/-! ## §1. Cut-Point DAG Representation, Symbolic Flattening & Unrestricted Loop Certificates -/

abbrev Word := BitVec 64
abbrev Env := Nat → Word
abbrev Observation := Qsag.StepObs

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

/-- Counted sequence of DAG cuts emitting `ElfBinaryVerify.StepObs` leakage traces. -/
def runCuts {S : Type} (step : S → S × List StepObs) : Nat → S → S × List StepObs
  | 0, s => (s, [])
  | n + 1, s =>
    let t := step s
    let u := runCuts step n t.1
    (u.1, t.2 ++ u.2)

/-- Positive-count Sewell loop-relation certificate with public `StepObs` schedule. -/
structure LoopRelationCert (A M : Type) (bound : Nat)
    (asmStep : A → A × List StepObs) (mirStep : M → M × List StepObs)
    (asmHead : A) (mirInit : M) (Post : A → M → Prop) where
  LoopRel : Nat → A → M → Prop
  schedule : Nat → List StepObs
  entry : LoopRel 0 asmHead mirInit
  body : ∀ v a m, v < bound → LoopRel v a m →
    LoopRel (v + 1) (asmStep a).1 (mirStep m).1 ∧
    (asmStep a).2 = schedule v ∧ (mirStep m).2 = schedule v
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
    (asmExec : A → A × List StepObs) (mirExec : M → M × List StepObs)
    (asmBody : A → A × List StepObs) (mirBody : M → M × List StepObs)
    (asmInit : A) (mirInit : M)
    (asmHead : A) (mirHead : M)
    (LoopPost : A → M → Prop) (Post : A → M → Prop) where
  zeroSchedule : List StepObs
  entrySchedule : List StepObs
  bodySchedule : Nat → List StepObs
  exitSchedule : List StepObs
  zero_cut : n = 0 →
    Post (asmExec asmInit).1 (mirExec mirInit).1 ∧
    (asmExec asmInit).2 = zeroSchedule ∧
    (mirExec mirInit).2 = zeroSchedule
  pos_cert : n ≠ 0 →
    LoopRelationCert A M n.toNat asmBody mirBody asmHead mirHead LoopPost
  pos_sched : ∀ hn : n ≠ 0, (pos_cert hn).schedule = bodySchedule
  pos_replay : ∀ _hn : n ≠ 0,
    LoopPost (runCuts asmBody n.toNat asmHead).1 (runCuts mirBody n.toNat mirHead).1 →
    (runCuts asmBody n.toNat asmHead).2 = scheduleTrace bodySchedule n.toNat 0 →
    (runCuts mirBody n.toNat mirHead).2 = scheduleTrace bodySchedule n.toNat 0 →
    Post (asmExec asmInit).1 (mirExec mirInit).1 ∧
    (asmExec asmInit).2 = entrySchedule ++ (runCuts asmBody n.toNat asmHead).2 ++ exitSchedule ∧
    (mirExec mirInit).2 = entrySchedule ++ (runCuts mirBody n.toNat mirHead).2 ++ exitSchedule

def fullSchedule (n : Word) (zeroSched entrySched : List StepObs)
    (bodySched : Nat → List StepObs) (exitSched : List StepObs) : List StepObs :=
  if n = 0 then zeroSched else entrySched ++ scheduleTrace bodySched n.toNat 0 ++ exitSched

/-- Constructive (`0 Classical.choice`) soundness for unrestricted `n : BitVec 64` (`n = 0` and `n > 0`). -/
theorem unrestricted_loop_refinement_sound {A M : Type} {n : Word}
    {asmExec : A → A × List StepObs} {mirExec : M → M × List StepObs}
    {asmBody : A → A × List StepObs} {mirBody : M → M × List StepObs}
    {asmInit : A} {mirInit : M} {asmHead : A} {mirHead : M}
    {LP P : A → M → Prop}
    (c : UnrestrictedLoopCert A M n asmExec mirExec asmBody mirBody
      asmInit mirInit asmHead mirHead LP P) :
    P (asmExec asmInit).1 (mirExec mirInit).1 ∧
    (asmExec asmInit).2 =
      fullSchedule n c.zeroSchedule c.entrySchedule c.bodySchedule c.exitSchedule ∧
    (mirExec mirInit).2 =
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
    {asmExec : A → A × List StepObs} {mirExec mirExec₂ : M → M × List StepObs}
    {asmBody : A → A × List StepObs} {mirBody : M → M × List StepObs}
    {a₁ a₂ : A} {m₁ m₂ : M} {ah₁ ah₂ : A} {mh₁ mh₂ : M}
    {LP₁ LP₂ P₁ P₂ : A → M → Prop}
    (c₁ : UnrestrictedLoopCert A M n asmExec mirExec asmBody mirBody a₁ m₁ ah₁ mh₁ LP₁ P₁)
    (c₂ : UnrestrictedLoopCert A M n asmExec mirExec₂ asmBody mirBody a₂ m₂ ah₂ mh₂ LP₂ P₂)
    (hz : c₁.zeroSchedule = c₂.zeroSchedule)
    (he : c₁.entrySchedule = c₂.entrySchedule)
    (hb : c₁.bodySchedule = c₂.bodySchedule)
    (hx : c₁.exitSchedule = c₂.exitSchedule) :
    (asmExec a₁).2 = (asmExec a₂).2 ∧
    (asmExec a₁).2 = (mirExec m₁).2 := by
  obtain ⟨_, ha₁, hm₁⟩ := unrestricted_loop_refinement_sound c₁
  obtain ⟨_, ha₂, _⟩ := unrestricted_loop_refinement_sound c₂
  have hsched : fullSchedule n c₁.zeroSchedule c₁.entrySchedule c₁.bodySchedule c₁.exitSchedule =
      fullSchedule n c₂.zeroSchedule c₂.entrySchedule c₂.bodySchedule c₂.exitSchedule := by
    rw [hz, he, hb, hx]
  exact ⟨ha₁.trans (hsched.trans ha₂.symm), ha₁.trans hm₁.symm⟩

/-! ## §2. `ElfBinaryVerify` Single-Instruction Byte Decoders & `TvGraph` Welding -/

/-- Single-instruction `x86_64` byte decoder at offset `pc` wrapping `ElfBinaryVerify.decodeX86InstrAt`. -/
@[expose] def decodeX86One (code : List UInt8) (pc : Nat) : Option (DecodedInstr X86Instr) :=
  if pc < code.length then decodeX86InstrAt pc (code.drop pc) else none

/-- Single-instruction `AArch64` byte decoder at 4-byte-aligned offset `pc` wrapping `ElfBinaryVerify.decodeArm64Word`. -/
@[expose] def decodeArm64One (code : List UInt8) (pc : Nat) : Option (DecodedInstr Arm64Instr) :=
  if pc % 4 == 0 && pc + 4 ≤ code.length then
    match readU32LE? (code.drop pc) with
    | some w => (decodeArm64Word pc w).map (fun ins => ⟨pc, 4, ins⟩)
    | none => none
  else none

/-- Generic `x86_64` fetch-step runner parameterized by instruction fetch (`decodeX86One` or `findInstrAtPc`). -/
def runX86Fetch (fetch : Nat → Option (DecodedInstr X86Instr)) :
    Nat → X86State → X86State × List StepObs
  | 0, s => (s, [])
  | fuel + 1, s =>
    if s.halted then (s, [])
    else match fetch s.pc with
    | none => ({ s with halted := true }, [])
    | some d =>
      let (s', obs) := stepX86 d s
      let (sFinal, restObs) := runX86Fetch fetch fuel s'
      (sFinal, obs :: restObs)

/-- Live byte-decoded `x86_64` execution fetching each instruction directly via `decodeX86One`. -/
def runX86One (code : List UInt8) : Nat → X86State → X86State × List StepObs :=
  runX86Fetch (decodeX86One code)

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

/-- Generic `AArch64` fetch-step runner parameterized by instruction fetch (`decodeArm64One` or `findInstrAtPc`). -/
def runArm64Fetch (fetch : Nat → Option (DecodedInstr Arm64Instr)) :
    Nat → Arm64State → Arm64State × List StepObs
  | 0, s => (s, [])
  | fuel + 1, s =>
    if s.halted then (s, [])
    else match fetch s.pc with
    | none => ({ s with halted := true }, [])
    | some d =>
      let (s', obs) := stepArm64 d s
      let (sFinal, restObs) := runArm64Fetch fetch fuel s'
      (sFinal, obs :: restObs)

/-- Live byte-decoded `AArch64` execution fetching each instruction directly via `decodeArm64One`. -/
def runArm64One (code : List UInt8) : Nat → Arm64State → Arm64State × List StepObs :=
  runArm64Fetch (decodeArm64One code)

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

def bcastQword256 (w : UInt64) : Vec256 := ⟨w, w, w, w⟩

def bcastByte256 (b : UInt8) : Vec256 :=
  let w := mapBytes64 (fun _ => b)
  ⟨w, w, w, w⟩

def clmul256 (v1 v2 : Vec256) (imm : UInt8) : Vec256 :=
  let selLo1 := if (imm &&& 0x01) == 0 then v1.w0 else v1.w1
  let selLo2 := if (imm &&& 0x10) == 0 then v2.w0 else v2.w1
  let pLo := clmul64 selLo1 selLo2
  let selHi1 := if (imm &&& 0x01) == 0 then v1.w2 else v1.w3
  let selHi2 := if (imm &&& 0x10) == 0 then v2.w2 else v2.w3
  let pHi := clmul64 selHi1 selHi2
  ⟨pLo.w0, pLo.w1, pHi.w0, pHi.w1⟩

def zeroUpperVec256 (v : Vec256) : Vec256 := ⟨v.w0, v.w1, 0, 0⟩

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
      (⟨pc, g, y, cf, o, zf, dy, true, m⟩, ⟨off, [], true⟩) := by rfl

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

@[expose] def zeroCode : List UInt8 :=
  [0x48,0x89,0xf1,0x31,0xc0,0x88,0x07,0x48,0xff,0xc7,0x48,0xff,0xc9,0x75,0xf6,0x0f,0xae,0xf0,0xc3]

theorem zeroCode_is_rlib_slice :
    ((extractAllRlibFuncs x86RlibArchiveBytes)[15]?).map ElfFuncSlice.code = some zeroCode := by
  rw [x86_rlib_extracted_slices]; decide

theorem ctMemzeroX86_decodeOne_all :
    decodeX86Stream zeroCode = some ctMemzeroX86Prog ∧
    ctMemzeroX86Prog.all (fun d =>
      decodeX86One zeroCode d.offset == some d &&
      findInstrAtPc d.offset ctMemzeroX86Prog == some d) = true := by
  decide +kernel

structure MirMemzero where
  ptr : UInt64
  remaining : Nat
  mem : UInt64 → UInt8

def memzeroX86EntryObs : List StepObs := [⟨0, [], true⟩, ⟨3, [], true⟩]

def memzeroX86BodyObs (p : UInt64) : List StepObs :=
  [⟨5, [(p, 1)], true⟩, ⟨7, [], true⟩, ⟨10, [], true⟩, ⟨13, [], true⟩]

def memzeroX86ExitObs : List StepObs := [⟨15, [], true⟩, ⟨18, [], true⟩]

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

def mirMemzeroX86BodyStep (m : MirMemzero) : MirMemzero × List StepObs :=
  (⟨m.ptr + 1, m.remaining - 1, writeMem8 m.mem m.ptr 0⟩, memzeroX86BodyObs m.ptr)

theorem mirMemzero_cuts_mem (k : Nat) (p : UInt64) (rem : Nat) (mem : UInt64 → UInt8) :
    (runCuts mirMemzeroX86BodyStep k ⟨p, rem, mem⟩).1.mem = zeroRange k mem p := by
  induction k generalizing p rem mem with
  | zero => rfl
  | succ k ih =>
    simpa [runCuts, mirMemzeroX86BodyStep, zeroRange] using ih (p + 1) (rem - 1) (writeMem8 mem p 0)

/-- Symbol execution behind a zero-count guard on `rsi`. The guard branch is a hand-written
model of the Rust wrapper's early return on empty input, not decoded machine code. -/
def ctMemzeroX86GuardedRun (fetch : Nat → Option (DecodedInstr X86Instr))
    (fuel : Nat) (s : X86State) : X86State × List StepObs :=
  if s.gpr.get 6 == 0 then ({ s with halted := true }, [⟨0, [], true⟩])
  else runX86Fetch fetch fuel s

def mirMemzeroX86Run (n : Word) (base : UInt64) (mem : UInt64 → UInt8) : MirMemzero × List StepObs :=
  if n = 0 then (⟨base, 0, mem⟩, [⟨0, [], true⟩])
  else
    let loop := runCuts mirMemzeroX86BodyStep n.toNat ⟨base, n.toNat, mem⟩
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
  (hf18 : fetch 18 = some ⟨18, 1, .ret⟩)

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

include hf15 hf18 in
theorem ctMemzeroX86_exit_full (g : Bank16 UInt64) (y : Bank16 Vec256) (cf o zf dy : Bool)
    (m : UInt64 → UInt8) (extra : Nat) :
    runX86Fetch fetch (2 + extra) ⟨15, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨18, g, y, cf, o, zf, dy, true, m⟩, memzeroX86ExitObs) := by
  rw [show 2 + extra = (extra + 1) + 1 from by omega]
  rw [runX86Fetch_step fetch _ _ _ rfl hf15]
  simp only [stepX86Full_mfence]
  rw [runX86Fetch_step fetch _ _ _ rfl hf18]
  simp only [stepX86Full_ret, memzeroX86ExitObs]
  rw [runX86Fetch_halted _ _ _ rfl]

end MemzeroX86Fetch

def MemzeroX86Rel (s₀ : X86State) (n v : Nat) (a : X86State) (m : MirMemzero) : Prop :=
  ∃ o zf : Bool,
    a = ⟨if v = n then 15 else 5,
          (s₀.gpr.set 0 0 |>.set 1 (UInt64.ofNat (n - v)) |>.set 7 (ptrStride (s₀.gpr.get 7) 1 v)),
          s₀.ymm, false, o, zf, s₀.ymmDirty, false, m.mem⟩ ∧
    m.ptr = ptrStride (s₀.gpr.get 7) 1 v ∧
    m.remaining = n - v

def MemzeroX86LoopPost (s₀ : X86State) (n : Nat) (a : X86State) (m : MirMemzero) : Prop :=
  ∃ o zf : Bool,
    a = ⟨15, (s₀.gpr.set 0 0 |>.set 1 0 |>.set 7 (ptrStride (s₀.gpr.get 7) 1 n)),
          s₀.ymm, false, o, zf, s₀.ymmDirty, false, m.mem⟩ ∧
    m.remaining = 0

def MemzeroX86Post (s₀ : X86State) (n : Word) (out : X86State) (m : MirMemzero) : Prop :=
  out.halted = true ∧
  out.mem = m.mem ∧
  out.mem = zeroRange n.toNat s₀.mem (s₀.gpr.get 7) ∧
  (∀ i < n.toNat, out.mem (s₀.gpr.get 7 + UInt64.ofNat i) = 0) ∧
  (∀ addr, (∀ i < n.toNat, addr ≠ s₀.gpr.get 7 + UInt64.ofNat i) → out.mem addr = s₀.mem addr) ∧
  out.gpr.get 4 = s₀.gpr.get 4 ∧
  out.gpr.get 3 = s₀.gpr.get 3 ∧
  out.gpr.get 5 = s₀.gpr.get 5 ∧
  (∀ r, 12 ≤ r → r < 16 → out.gpr.get r = s₀.gpr.get r)

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
    LoopRelationCert X86State MirMemzero n memzeroX86BodyStep mirMemzeroX86BodyStep
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
    · simp only [memzeroX86BodyStep, mirMemzeroX86BodyStep, b16get_7, b16get_1,
        b16set_0, b16set_1, b16set_7, hdec, hsub, hjcc, ptrStride, hmp]
    · simp [mirMemzeroX86BodyStep, hmp, ptrStride]
    · simp [mirMemzeroX86BodyStep, hmr]; omega
    · simp [memzeroX86BodyStep, b16get_7, b16set_0, b16set_1, b16set_7]
    · simp [mirMemzeroX86BodyStep, hmp, b16get_7]
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
    rw [ih (v + 1) (memzeroX86BodyStep a).1 (mirMemzeroX86BodyStep m).1 fuel (by omega) hbody.1]
    simp [runCuts, List.append_assoc]

/-- Complete `UnrestrictedLoopCert` for `qsag_asm_ct_memzero_x86_64` over **all `n : BitVec 64`**
(`n = 0` zero-trip cut + `n ≠ 0` byte-decoded `.rlib` execution). -/
def ctMemzeroX86UnrestrictedCert (fetch : Nat → Option (DecodedInstr X86Instr))
    (hf : ∀ d ∈ ctMemzeroX86Prog, fetch d.offset = some d)
    (s₀ : X86State) (fuel : Nat) (hpc : s₀.pc = 0) (hh : s₀.halted = false)
    (n : Word) (hcount : s₀.gpr.get 6 = UInt64.ofBitVec n)
    (hfuel : 4 * n.toNat + 4 ≤ fuel) :
    UnrestrictedLoopCert X86State MirMemzero n
      (ctMemzeroX86GuardedRun fetch fuel)
      (fun m => mirMemzeroX86Run n m.ptr m.mem)
      memzeroX86BodyStep mirMemzeroX86BodyStep
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
    dsimp only [ctMemzeroX86GuardedRun, mirMemzeroX86Run]
    rw [ite_eq_left hg0, ite_eq_left rfl]
    refine ⟨⟨rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl, fun _ _ _ => rfl⟩, rfl, rfl⟩
    · intro i hi; exact absurd hi (Nat.not_lt_zero i)
    · intro _ _; rfl
  pos_cert := fun hn =>
    ctMemzeroX86PosCert s₀ n.toNat (bv64_pos_of_ne_zero n hn) n.isLt
  pos_sched := fun _ => rfl
  pos_replay := by
    intro hn hlp hal hml
    have hg0 : ¬ ((s₀.gpr.get 6 == 0) = true) := by
      rw [beq_false_of_ne (hcount ▸ (bv64_ne_zero_iff_u64_ne_zero n).mp hn)]; decide
    dsimp only [ctMemzeroX86GuardedRun, mirMemzeroX86Run]
    rw [ite_eq_right hg0, ite_eq_right hn]
    have hf0 := hf ⟨0, 3, .movRegReg true 1 6⟩ (by decide)
    have hf3 := hf ⟨3, 2, .aluRegReg .xorOp false 0 0⟩ (by decide)
    have hf5 := hf ⟨5, 2, .storeGpr 1 0 (.baseDisp 7 0)⟩ (by decide)
    have hf7 := hf ⟨7, 3, .incDec true true 7⟩ (by decide)
    have hf10 := hf ⟨10, 3, .incDec false true 1⟩ (by decide)
    have hf13 := hf ⟨13, 2, .jcc 5 5⟩ (by decide)
    have hf15 := hf ⟨15, 3, .mfence⟩ (by decide)
    have hf18 := hf ⟨18, 1, .ret⟩ (by decide)
    obtain ⟨extra, hextra⟩ : ∃ extra, fuel = 2 + (4 * n.toNat + (2 + extra)) :=
      ⟨fuel - (4 * n.toNat + 4), by omega⟩
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
      n.toNat hpos n.isLt n.toNat 0 _ ⟨r7, n.toNat, m⟩ (2 + extra) (by omega)
      (ctMemzeroX86PosCert _ n.toNat hpos n.isLt).entry
    dsimp only at hrep ⊢
    rw [hrep]
    rcases hlp with ⟨oL, zfL, haL, _⟩
    rw [haL, ctMemzeroX86_exit_full fetch hf15 hf18]
    have hzr := mirMemzero_cuts_mem n.toNat r7 n.toNat m
    refine ⟨?_, by simp [List.append_assoc], rfl⟩
    refine ⟨rfl, rfl, hzr, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    ∀ d ∈ ctMemzeroX86Prog, decodeX86One zeroCode d.offset = some d := by
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
    (hfuel : 4 * n.toNat + 4 ≤ fuel) :
    let c₁ := ctMemzeroX86UnrestrictedCert (decodeX86One zeroCode) ctMemzeroX86_fetch_decodeOne
      s₁ fuel hpc₁ hh₁ n hc₁ hfuel
    let out₁ := ctMemzeroX86GuardedRun (decodeX86One zeroCode) fuel s₁
    let out₂ := ctMemzeroX86GuardedRun (decodeX86One zeroCode) fuel s₂
    let mir₁ := mirMemzeroX86Run n (s₁.gpr.get 7) s₁.mem
    MemzeroX86Post s₁ n out₁.1 mir₁.1 ∧
    out₁.2 = out₂.2 ∧
    out₁.2 = mir₁.2 ∧
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
      (mirMemzeroX86Run n (s₁.gpr.get 7) s₁.mem).2 := by
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
`StepObs` trace, equal to the trace of the MIR-level loop. -/
theorem ct_memzero_x86_64_sydtv_refines_pos (s₁ s₂ : X86State) (fuel : Nat) (n : Word) (hn : n ≠ 0)
    (hpc₁ : s₁.pc = 0) (hh₁ : s₁.halted = false) (hc₁ : s₁.gpr.get 6 = UInt64.ofBitVec n)
    (hpc₂ : s₂.pc = 0) (hh₂ : s₂.halted = false) (hc₂ : s₂.gpr.get 6 = UInt64.ofBitVec n)
    (hptr : s₁.gpr.get 7 = s₂.gpr.get 7)
    (hfuel : 4 * n.toNat + 4 ≤ fuel) :
    MemzeroX86Post s₁ n (runX86One zeroCode fuel s₁).1 (mirMemzeroX86Run n (s₁.gpr.get 7) s₁.mem).1 ∧
    (runX86One zeroCode fuel s₁).2 = (runX86One zeroCode fuel s₂).2 ∧
    (runX86One zeroCode fuel s₁).2 = (mirMemzeroX86Run n (s₁.gpr.get 7) s₁.mem).2 := by
  have h := ct_memzero_x86_64_sydtv_refines_all_n s₁ s₂ fuel n hpc₁ hh₁ hc₁ hpc₂ hh₂ hc₂ hptr hfuel
  dsimp only at h
  rw [ctMemzeroX86GuardedRun_pos _ fuel s₁ n hn hc₁, ctMemzeroX86GuardedRun_pos _ fuel s₂ n hn hc₂] at h
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-! ## §5. Kernel 2 — `qsag_asm_ct_memzero_aarch64` (AArch64 Post-Index Affine, Unrestricted `∀ n : Word`) -/

@[expose] def armZeroCode : List UInt8 :=
  [0x1f,0x14,0x00,0x38,0x21,0x04,0x00,0xf1,0xc1,0xff,0xff,0x54,
   0xbf,0x3b,0x03,0xd5,0xc0,0x03,0x5f,0xd6]

theorem armZeroCode_is_rlib_slice :
    ((extractAllRlibFuncs aarch64RlibArchiveBytes)[6]?).map ElfFuncSlice.code = some armZeroCode := by
  rw [aarch64_rlib_extracted_slices]; decide

theorem ctMemzeroArm_decodeOne_all :
    decodeArm64Stream armZeroCode = some ctMemzeroArmProg ∧
    ctMemzeroArmProg.all (fun d =>
      decodeArm64One armZeroCode d.offset == some d &&
      findInstrAtPc d.offset ctMemzeroArmProg == some d) = true := by
  decide +kernel

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

def mirMemzeroArmBodyStep (m : MirMemzero) : MirMemzero × List StepObs :=
  (⟨m.ptr + 1, m.remaining - 1, writeMem8 m.mem m.ptr 0⟩, memzeroArmBodyObs m.ptr)

theorem mirMemzeroArm_cuts_mem (k : Nat) (p : UInt64) (rem : Nat) (mem : UInt64 → UInt8) :
    (runCuts mirMemzeroArmBodyStep k ⟨p, rem, mem⟩).1.mem = zeroRange k mem p := by
  induction k generalizing p rem mem with
  | zero => rfl
  | succ k ih =>
    simpa [runCuts, mirMemzeroArmBodyStep, zeroRange] using ih (p + 1) (rem - 1) (writeMem8 mem p 0)

/-- Symbol execution behind a zero-count guard on `x1`. The guard branch is a hand-written
model of the Rust wrapper's early return on empty input, not decoded machine code. -/
def ctMemzeroArmGuardedRun (fetch : Nat → Option (DecodedInstr Arm64Instr))
    (fuel : Nat) (s : Arm64State) : Arm64State × List StepObs :=
  if armGet s.gpr 1 == 0 then ({ s with halted := true }, [⟨0, [], true⟩])
  else runArm64Fetch fetch fuel s

def mirMemzeroArmRun (n : Word) (base : UInt64) (mem : UInt64 → UInt8) : MirMemzero × List StepObs :=
  if n = 0 then (⟨base, 0, mem⟩, [⟨0, [], true⟩])
  else
    let loop := runCuts mirMemzeroArmBodyStep n.toNat ⟨base, n.toNat, mem⟩
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

def MemzeroArmRel (s₀ : Arm64State) (n v : Nat) (a : Arm64State) (m : MirMemzero) : Prop :=
  ∃ cf zf : Bool,
    a = ⟨if v = n then 12 else 0,
          armSet (armSet s₀.gpr 0 (ptrStride (armGet s₀.gpr 0) 1 v)) 1 (UInt64.ofNat (n - v)),
          s₀.vec, cf, zf, s₀.dit, false, m.mem⟩ ∧
    m.ptr = ptrStride (armGet s₀.gpr 0) 1 v ∧
    m.remaining = n - v

def MemzeroArmLoopPost (s₀ : Arm64State) (n : Nat) (a : Arm64State) (m : MirMemzero) : Prop :=
  ∃ cf zf : Bool,
    a = ⟨12, armSet (armSet s₀.gpr 0 (ptrStride (armGet s₀.gpr 0) 1 n)) 1 0,
          s₀.vec, cf, zf, s₀.dit, false, m.mem⟩ ∧
    m.remaining = 0

def MemzeroArmPost (s₀ : Arm64State) (n : Word) (out : Arm64State) (m : MirMemzero) : Prop :=
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
    LoopRelationCert Arm64State MirMemzero n memzeroArmBodyStep mirMemzeroArmBodyStep
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
    · simp only [memzeroArmBodyStep, mirMemzeroArmBodyStep, armGet_0, armGet_1, armSet_0, armSet_1,
        hdec, hsub, hjcc, ptrStride, hmp]
    · simp [mirMemzeroArmBodyStep, hmp, ptrStride]
    · simp [mirMemzeroArmBodyStep, hmr]; omega
    · simp [memzeroArmBodyStep, armGet_0, armSet_0, armSet_1]
    · simp [mirMemzeroArmBodyStep, hmp, armGet_0]
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
    rw [ih (v + 1) (memzeroArmBodyStep a).1 (mirMemzeroArmBodyStep m).1 fuel (by omega) hbody.1]
    simp [runCuts, List.append_assoc]

/-- Complete `UnrestrictedLoopCert` for `qsag_asm_ct_memzero_aarch64` over **all `n : BitVec 64`**. -/
def ctMemzeroArmUnrestrictedCert (fetch : Nat → Option (DecodedInstr Arm64Instr))
    (hf : ∀ d ∈ ctMemzeroArmProg, fetch d.offset = some d)
    (s₀ : Arm64State) (fuel : Nat) (hpc : s₀.pc = 0) (hh : s₀.halted = false)
    (n : Word) (hcount : armGet s₀.gpr 1 = UInt64.ofBitVec n)
    (hfuel : 3 * n.toNat + 2 ≤ fuel) :
    UnrestrictedLoopCert Arm64State MirMemzero n
      (ctMemzeroArmGuardedRun fetch fuel)
      (fun m => mirMemzeroArmRun n m.ptr m.mem)
      memzeroArmBodyStep mirMemzeroArmBodyStep
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
    dsimp only [ctMemzeroArmGuardedRun, mirMemzeroArmRun]
    rw [ite_eq_left hg0, ite_eq_left rfl]
    refine ⟨⟨rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl⟩, rfl, rfl⟩
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
    dsimp only [ctMemzeroArmGuardedRun, mirMemzeroArmRun]
    rw [ite_eq_right hg0, ite_eq_right hn]
    have hf0 := hf ⟨0, 4, .strbPost 31 0 1⟩ (by decide)
    have hf4 := hf ⟨4, 4, .aluImm .subs true 1 1 1⟩ (by decide)
    have hf8 := hf ⟨8, 4, .bCond 1 0⟩ (by decide)
    have hf12 := hf ⟨12, 4, .dmbIsh⟩ (by decide)
    have hf16 := hf ⟨16, 4, .ret⟩ (by decide)
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
    have hzr := mirMemzeroArm_cuts_mem n.toNat (armGet s₀.gpr 0) n.toNat s₀.mem
    have hhi : (armSet (armSet s₀.gpr 0 (ptrStride (armGet s₀.gpr 0) 1 n.toNat)) 1 0).hi = s₀.gpr.hi := by
      obtain ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩ := s₀.gpr
      rfl
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
    let mir₁ := mirMemzeroArmRun n (armGet s₁.gpr 0) s₁.mem
    MemzeroArmPost s₁ n out₁.1 mir₁.1 ∧ out₁.2 = out₂.2 ∧ out₁.2 = mir₁.2 := by
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
      (mirMemzeroArmRun n (armGet s₁.gpr 0) s₁.mem).1 ∧
    (runArm64One armZeroCode fuel s₁).2 = (runArm64One armZeroCode fuel s₂).2 ∧
    (runArm64One armZeroCode fuel s₁).2 = (mirMemzeroArmRun n (armGet s₁.gpr 0) s₁.mem).2 := by
  have h := ct_memzero_aarch64_sydtv_refines_all_n s₁ s₂ fuel n hpc₁ hh₁ hc₁ hpc₂ hh₂ hc₂ hptr hfuel
  dsimp only at h
  rw [ctMemzeroArmGuardedRun_pos _ fuel s₁ n hn hc₁, ctMemzeroArmGuardedRun_pos _ fuel s₂ n hn hc₂] at h
  exact h

/-! ## §6. Kernel 3 — `qsag_asm_ct_eq_bytes_x86_64` (2-Pointer Affine + OR-of-XOR Accumulator, `∀ n : Word`) -/

@[expose] def eqBytesCode : List UInt8 :=
  [0x31,0xc0,0x48,0x89,0xd1,0x44,0x0f,0xb6,0x07,0x44,0x0f,0xb6,0x0e,0x45,0x31,0xc8,
   0x44,0x09,0xc0,0x48,0xff,0xc7,0x48,0xff,0xc6,0x48,0xff,0xc9,0x75,0xe7,0x83,0xe8,
   0x01,0xc1,0xe8,0x1f,0x45,0x31,0xc0,0x45,0x31,0xc9,0xc3]

theorem eqBytesCode_is_rlib_slice :
    ((extractAllRlibFuncs x86RlibArchiveBytes)[14]?).map ElfFuncSlice.code = some eqBytesCode := by
  rw [x86_rlib_extracted_slices]; decide

theorem ctEqBytesX86_decodeOne_all :
    decodeX86Stream eqBytesCode = some ctEqBytesX86Prog ∧
    ctEqBytesX86Prog.all (fun d =>
      decodeX86One eqBytesCode d.offset == some d &&
      findInstrAtPc d.offset ctEqBytesX86Prog == some d) = true := by
  decide +kernel

theorem ctEqBytesX86_fetch_decodeOne :
    ∀ d ∈ ctEqBytesX86Prog, decodeX86One eqBytesCode d.offset = some d := by
  intro d hd
  have hall := ctEqBytesX86_decodeOne_all.2
  rw [List.all_eq_true] at hall
  have h := hall d hd
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

structure MirEqBytes where
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

def eqBytesExitObs : List StepObs :=
  [⟨30, [], true⟩, ⟨33, [], true⟩, ⟨36, [], true⟩, ⟨39, [], true⟩, ⟨42, [], true⟩]

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

def mirEqBytesBodyStep (m : MirEqBytes) : MirEqBytes × List StepObs :=
  (⟨m.ptrA + 1, m.ptrB + 1, eqAccStepVal m.acc (m.mem m.ptrA) (m.mem m.ptrB),
    m.remaining - 1, m.mem, 0⟩,
   eqBytesBodyObs m.ptrA m.ptrB)

/-- Symbol execution behind a zero-count guard on `rdx`. The guard branch is a hand-written
model of the Rust wrapper's early return on empty input, not decoded machine code. -/
def ctEqBytesGuardedRun (fetch : Nat → Option (DecodedInstr X86Instr))
    (fuel : Nat) (s : X86State) : X86State × List StepObs :=
  if s.gpr.get 2 == 0 then
    ({ s with pc := 42, gpr := (s.gpr.set 0 1 |>.set 1 0 |>.set 8 0 |>.set 9 0), halted := true },
     [⟨0, [], true⟩])
  else runX86Fetch fetch fuel s

def mirEqBytesRun (n : Word) (baseA baseB : UInt64) (mem : UInt64 → UInt8) : MirEqBytes × List StepObs :=
  if n = 0 then
    (⟨baseA, baseB, 0, 0, mem, 1⟩, [⟨0, [], true⟩])
  else
    let loop := runCuts mirEqBytesBodyStep n.toNat ⟨baseA, baseB, 0, n.toNat, mem, 0⟩
    let res : UInt64 := if loop.1.acc = 0 then 1 else 0
    ({ loop.1 with result := res }, eqBytesEntryObs ++ loop.2 ++ eqBytesExitObs)

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
  (hf42 : fetch 42 = some ⟨42, 1, .ret⟩)

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

include hf30 hf33 hf36 hf39 hf42 in
theorem ctEqBytes_exit_full (acc r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) (hA : acc.toNat < 256) (extra : Nat) :
    runX86Fetch fetch (5 + extra)
      ⟨30, ⟨acc, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, y, cf, o, zf, dy, false, m⟩ =
      (⟨42, ⟨if acc = 0 then 1 else 0, r1, r2, r3, r4, r5, r6, r7, 0, 0, r10, r11, r12, r13, r14, r15⟩,
        y, false, false, true, dy, true, m⟩,
       eqBytesExitObs) := by
  rw [show 5 + extra = ((((extra + 1) + 1) + 1) + 1) + 1 from by omega]
  rw [runX86Fetch_step fetch _ _ _ rfl hf30]
  simp only [stepX86Full_subImm32, b16get_0, b16set_0]
  rw [runX86Fetch_step fetch _ _ _ rfl hf33]
  simp only [stepX86Full_shr32_31, b16get_0, b16set_0, eqTail_spec acc hA]
  rw [runX86Fetch_step fetch _ _ _ rfl hf36]
  simp only [stepX86Full_xorRR, b16get_8, mask32_xor_self_eq, u64_zero_beq_true, b16set_8]
  rw [runX86Fetch_step fetch _ _ _ rfl hf39]
  simp only [stepX86Full_xorRR, b16get_9, mask32_xor_self_eq, u64_zero_beq_true, b16set_9]
  rw [runX86Fetch_step fetch _ _ _ rfl hf42]
  simp only [stepX86Full_ret, eqBytesExitObs]
  rw [runX86Fetch_halted _ _ _ rfl]

end EqBytesFetch

def EqBytesRel (s₀ : X86State) (n v : Nat) (a : X86State) (m : MirEqBytes) : Prop :=
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

def EqBytesLoopPost (s₀ : X86State) (n : Nat) (a : X86State) (m : MirEqBytes) : Prop :=
  let baseA := s₀.gpr.get 7
  let baseB := s₀.gpr.get 6
  ∃ cf o zf : Bool, ∃ x8 x9 : UInt64,
    a = ⟨30,
          (s₀.gpr.set 8 x8 |>.set 9 x9 |>.set 0 (eqAcc n s₀.mem baseA baseB 0)
            |>.set 7 (ptrStride baseA 1 n) |>.set 6 (ptrStride baseB 1 n) |>.set 1 0),
          s₀.ymm, cf, o, zf, s₀.ymmDirty, false, s₀.mem⟩ ∧
    m.acc = eqAcc n s₀.mem baseA baseB 0 ∧
    m.remaining = 0

def EqBytesPost (s₀ : X86State) (n : Word) (out : X86State) (m : MirEqBytes) : Prop :=
  let baseA := s₀.gpr.get 7
  let baseB := s₀.gpr.get 6
  out.halted = true ∧
  out.mem = s₀.mem ∧
  out.gpr.get 0 = m.result ∧
  out.gpr.get 0 = (if ∀ i < n.toNat, s₀.mem (baseA + UInt64.ofNat i) = s₀.mem (baseB + UInt64.ofNat i) then 1 else 0) ∧
  out.gpr.get 1 = 0 ∧ out.gpr.get 8 = 0 ∧ out.gpr.get 9 = 0 ∧
  out.gpr.get 4 = s₀.gpr.get 4 ∧ out.gpr.get 3 = s₀.gpr.get 3 ∧ out.gpr.get 5 = s₀.gpr.get 5 ∧
  (∀ r, 12 ≤ r → r < 16 → out.gpr.get r = s₀.gpr.get r)

def ctEqBytesPosCert (s₀ : X86State) (n : Nat) (hn : 0 < n) (hbound : n < 2 ^ 64) :
    LoopRelationCert X86State MirEqBytes n eqBytesBodyStep mirEqBytesBodyStep
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
      rfl
    · simp [mirEqBytesBodyStep, hpA, ptrStride, b16get_7]
    · simp [mirEqBytesBodyStep, hpB, ptrStride, b16get_6]
    · simp only [mirEqBytesBodyStep, hacc, hpA, hpB, hmem, b16get_6, b16get_7, hsnoc]
    · simp [mirEqBytesBodyStep, hmr]; omega
    · simp [eqBytesBodyStep, b16get_6, b16get_7, b16set_0, b16set_1, b16set_6, b16set_7, b16set_8, b16set_9]
    · simp [mirEqBytesBodyStep, hpA, hpB, b16get_6, b16get_7]
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
    rw [ih (v + 1) (eqBytesBodyStep a).1 (mirEqBytesBodyStep m).1 fuel (by omega) hbody.1]
    simp [runCuts, List.append_assoc]

/-- Complete `UnrestrictedLoopCert` for `qsag_asm_ct_eq_bytes_x86_64` over **all `n : BitVec 64`**. -/
def ctEqBytesX86UnrestrictedCert (fetch : Nat → Option (DecodedInstr X86Instr))
    (hf : ∀ d ∈ ctEqBytesX86Prog, fetch d.offset = some d)
    (s₀ : X86State) (fuel : Nat) (hpc : s₀.pc = 0) (hh : s₀.halted = false)
    (n : Word) (hcount : s₀.gpr.get 2 = UInt64.ofBitVec n)
    (hfuel : 8 * n.toNat + 7 ≤ fuel) :
    UnrestrictedLoopCert X86State MirEqBytes n
      (ctEqBytesGuardedRun fetch fuel)
      (fun m => mirEqBytesRun n m.ptrA m.ptrB m.mem)
      eqBytesBodyStep mirEqBytesBodyStep
      s₀ ⟨s₀.gpr.get 7, s₀.gpr.get 6, 0, n.toNat, s₀.mem, 0⟩
      ⟨5, (s₀.gpr.set 0 0 |>.set 1 (UInt64.ofNat n.toNat)), s₀.ymm, false, false, true, s₀.ymmDirty, false, s₀.mem⟩
      ⟨s₀.gpr.get 7, s₀.gpr.get 6, 0, n.toNat, s₀.mem, 0⟩
      (EqBytesLoopPost s₀ n.toNat)
      (EqBytesPost s₀ n) where
  zeroSchedule := [⟨0, [], true⟩]
  entrySchedule := eqBytesEntryObs
  bodySchedule := fun v => eqBytesBodyObs (ptrStride (s₀.gpr.get 7) 1 v) (ptrStride (s₀.gpr.get 6) 1 v)
  exitSchedule := eqBytesExitObs
  zero_cut := by
    intro hz; subst hz
    have hg0 : (s₀.gpr.get 2 == 0) = true := by simp [hcount]
    dsimp only [ctEqBytesGuardedRun, mirEqBytesRun]
    rw [ite_eq_left hg0, ite_eq_left rfl]
    obtain ⟨_, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, _, _, _, _, _, _, mem⟩ := s₀
    have hvac : (∀ i < (0 : Word).toNat, mem (r7 + UInt64.ofNat i) = mem (r6 + UInt64.ofNat i)) := by
      intro i hi; exact absurd hi (Nat.not_lt_zero i)
    refine ⟨?_, rfl, rfl⟩
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    dsimp only [ctEqBytesGuardedRun, mirEqBytesRun]
    rw [ite_eq_right hg0, ite_eq_right hn]
    have hf0 := hf ⟨0, 2, .aluRegReg .xorOp false 0 0⟩ (by decide)
    have hf2 := hf ⟨2, 3, .movRegReg true 1 2⟩ (by decide)
    have hf5 := hf ⟨5, 4, .loadGpr 1 false 8 (.baseDisp 7 0)⟩ (by decide)
    have hf9 := hf ⟨9, 4, .loadGpr 1 false 9 (.baseDisp 6 0)⟩ (by decide)
    have hf13 := hf ⟨13, 3, .aluRegReg .xorOp false 8 9⟩ (by decide)
    have hf16 := hf ⟨16, 3, .aluRegReg .orOp false 0 8⟩ (by decide)
    have hf19 := hf ⟨19, 3, .incDec true true 7⟩ (by decide)
    have hf22 := hf ⟨22, 3, .incDec true true 6⟩ (by decide)
    have hf25 := hf ⟨25, 3, .incDec false true 1⟩ (by decide)
    have hf28 := hf ⟨28, 2, .jcc 5 5⟩ (by decide)
    have hf30 := hf ⟨30, 3, .aluImm .sub false 0 1⟩ (by decide)
    have hf33 := hf ⟨33, 3, .shiftImm .shr false 0 31⟩ (by decide)
    have hf36 := hf ⟨36, 3, .aluRegReg .xorOp false 8 8⟩ (by decide)
    have hf39 := hf ⟨39, 3, .aluRegReg .xorOp false 9 9⟩ (by decide)
    have hf42 := hf ⟨42, 1, .ret⟩ (by decide)
    obtain ⟨extra, hextra⟩ : ∃ extra, fuel = 2 + (8 * n.toNat + (5 + extra)) :=
      ⟨fuel - (8 * n.toNat + 7), by omega⟩
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
      n.toNat hpos n.isLt n.toNat 0 _ ⟨r7, r6, 0, n.toNat, m, 0⟩ (5 + extra) (by omega)
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
    rw [ha30, ctEqBytes_exit_full fetch hf30 hf33 hf36 hf39 hf42 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hspec.1]
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
    refine ⟨?_, by simp [List.append_assoc], rfl⟩
    refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
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
    (hfuel : 8 * n.toNat + 7 ≤ fuel) :
    let out₁ := ctEqBytesGuardedRun (decodeX86One eqBytesCode) fuel s₁
    let out₂ := ctEqBytesGuardedRun (decodeX86One eqBytesCode) fuel s₂
    let mir₁ := mirEqBytesRun n (s₁.gpr.get 7) (s₁.gpr.get 6) s₁.mem
    EqBytesPost s₁ n out₁.1 mir₁.1 ∧ out₁.2 = out₂.2 ∧ out₁.2 = mir₁.2 := by
  dsimp only
  let c₁ := ctEqBytesX86UnrestrictedCert (decodeX86One eqBytesCode) ctEqBytesX86_fetch_decodeOne
    s₁ fuel hpc₁ hh₁ n hc₁ hfuel
  let c₂ := ctEqBytesX86UnrestrictedCert (decodeX86One eqBytesCode) ctEqBytesX86_fetch_decodeOne
    s₂ fuel hpc₂ hh₂ n hc₂ hfuel
  obtain ⟨hp, _, _⟩ := unrestricted_loop_refinement_sound c₁
  have hsched : c₁.bodySchedule = c₂.bodySchedule := by
    funext v; simp [c₁, c₂, ctEqBytesX86UnrestrictedCert, hpA, hpB]
  obtain ⟨hni1, hni2⟩ := unrestricted_three_way_noninterference c₁ c₂ rfl rfl hsched rfl
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
    (hfuel : 8 * n.toNat + 7 ≤ fuel) :
    EqBytesPost s₁ n (runX86One eqBytesCode fuel s₁).1
      (mirEqBytesRun n (s₁.gpr.get 7) (s₁.gpr.get 6) s₁.mem).1 ∧
    (runX86One eqBytesCode fuel s₁).2 = (runX86One eqBytesCode fuel s₂).2 ∧
    (runX86One eqBytesCode fuel s₁).2 = (mirEqBytesRun n (s₁.gpr.get 7) (s₁.gpr.get 6) s₁.mem).2 := by
  have h := ct_eq_bytes_x86_64_sydtv_refines_all_n s₁ s₂ fuel n hpc₁ hh₁ hc₁ hpc₂ hh₂ hc₂ hpA hpB hfuel
  dsimp only at h
  rw [ctEqBytesGuardedRun_pos _ fuel s₁ n hn hc₁, ctEqBytesGuardedRun_pos _ fuel s₂ n hn hc₂] at h
  exact h

/-! ## §7. Kernel 4 — `qsag_asm_gf256_shamir_mac_gfni` (2-Pointer 32B Affine + GFNI SIMD MAC, `∀ n : Word`) -/

@[expose] def gfniShamirMacCode : List UInt8 :=
  [0x48,0xb8,0xce,0x78,0xbe,0x86,0x8a,0x0a,0x50,0x71,0xc4,0x61,0xf9,0x6e,0xf0,0xc4,
   0x42,0x7d,0x59,0xf6,0x48,0xb8,0x0c,0x70,0xa2,0x72,0xe0,0xf8,0xe4,0xa1,0xc4,0x61,
   0xf9,0x6e,0xf8,0xc4,0x42,0x7d,0x59,0xff,0xc5,0xf9,0x6e,0xda,0xc4,0xe2,0x7d,0x78,
   0xdb,0xc4,0xc3,0xe5,0xce,0xde,0x00,0xc5,0xfe,0x6f,0x06,0xc5,0xfe,0x6f,0x0f,0xc4,
   0xc3,0xfd,0xce,0xc6,0x00,0xc4,0xe2,0x7d,0xcf,0xd3,0xc4,0xc3,0xed,0xce,0xd7,0x00,
   0xc5,0xf5,0xef,0xca,0xc5,0xfe,0x7f,0x0f,0x48,0x83,0xc6,0x20,0x48,0x83,0xc7,0x20,
   0x48,0xff,0xc9,0x75,0xd2,0xc5,0xfd,0xef,0xc0,0xc5,0xf5,0xef,0xc9,0xc5,0xed,0xef,
   0xd2,0xc5,0xe5,0xef,0xdb,0xc4,0x41,0x0d,0xef,0xf6,0xc4,0x41,0x05,0xef,0xff,0x31,
   0xc0,0x31,0xd2,0xc5,0xf8,0x77,0xc3]

theorem gfniShamirMacCode_is_rlib_slice :
    ((extractAllRlibFuncs x86RlibArchiveBytes)[3]?).map ElfFuncSlice.code = some gfniShamirMacCode := by
  rw [x86_rlib_extracted_slices]; decide

def gfniShamirMacProg : List (DecodedInstr X86Instr) := [
  ⟨0, 10, .movImm true 0 0x71500a8a86be78ce⟩,
  ⟨10, 5, .vmovGprToXmm true 14 0⟩,
  ⟨15, 5, .vpbroadcast true true 14 14⟩,
  ⟨20, 10, .movImm true 0 0xa1e4f8e072a2700c⟩,
  ⟨30, 5, .vmovGprToXmm true 15 0⟩,
  ⟨35, 5, .vpbroadcast true true 15 15⟩,
  ⟨40, 4, .vmovGprToXmm false 3 2⟩,
  ⟨44, 5, .vpbroadcast false true 3 3⟩,
  ⟨49, 6, .vgf2p8affineqb true 3 3 14 0⟩,
  ⟨55, 4, .vload true 0 (.baseDisp 6 0)⟩,
  ⟨59, 4, .vload true 1 (.baseDisp 7 0)⟩,
  ⟨63, 6, .vgf2p8affineqb true 0 0 14 0⟩,
  ⟨69, 5, .vbinOp .vgf2p8mulb true 2 0 3⟩,
  ⟨74, 6, .vgf2p8affineqb true 2 2 15 0⟩,
  ⟨80, 4, .vbinOp .vpxor true 1 1 2⟩,
  ⟨84, 4, .vstore true 1 (.baseDisp 7 0)⟩,
  ⟨88, 4, .aluImm .add true 6 32⟩,
  ⟨92, 4, .aluImm .add true 7 32⟩,
  ⟨96, 3, .incDec false true 1⟩,
  ⟨99, 2, .jcc 5 55⟩,
  ⟨101, 4, .vbinOp .vpxor true 0 0 0⟩,
  ⟨105, 4, .vbinOp .vpxor true 1 1 1⟩,
  ⟨109, 4, .vbinOp .vpxor true 2 2 2⟩,
  ⟨113, 4, .vbinOp .vpxor true 3 3 3⟩,
  ⟨117, 5, .vbinOp .vpxor true 14 14 14⟩,
  ⟨122, 5, .vbinOp .vpxor true 15 15 15⟩,
  ⟨127, 2, .aluRegReg .xorOp false 0 0⟩,
  ⟨129, 2, .aluRegReg .xorOp false 2 2⟩,
  ⟨131, 3, .vzeroupper⟩,
  ⟨134, 1, .ret⟩
]

theorem gfniShamirMac_decodeOne_all :
    decodeX86Stream gfniShamirMacCode = some gfniShamirMacProg ∧
    gfniShamirMacProg.all (fun d =>
      decodeX86One gfniShamirMacCode d.offset == some d &&
      findInstrAtPc d.offset gfniShamirMacProg == some d) = true := by
  decide +kernel

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

structure MirShamirMac where
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

def gfniExitObs : List StepObs :=
  [⟨101, [], true⟩, ⟨105, [], true⟩, ⟨109, [], true⟩, ⟨113, [], true⟩, ⟨117, [], true⟩,
   ⟨122, [], true⟩, ⟨127, [], true⟩, ⟨129, [], true⟩, ⟨131, [], true⟩, ⟨134, [], true⟩]

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

def mirGfniBodyStep (m : MirShamirMac) : MirShamirMac × List StepObs :=
  let nextMem := writeMem256 m.mem m.accPtr
    (gfniShamirMacBlock m.coeff (readMem256 m.mem m.sharesPtr) (readMem256 m.mem m.accPtr))
  (⟨m.sharesPtr + 32, m.accPtr + 32, m.coeff, m.remaining - 1, nextMem⟩,
   gfniBodyObs m.sharesPtr m.accPtr)

theorem mirGfni_cuts_mem (k : Nat) (pS pA : UInt64) (coeff : Vec256) (rem : Nat) (mem : UInt64 → UInt8) :
    (runCuts mirGfniBodyStep k ⟨pS, pA, coeff, rem, mem⟩).1.mem = shamirMacRange k coeff mem pS pA := by
  induction k generalizing pS pA rem mem with
  | zero => rfl
  | succ k ih =>
    simpa [runCuts, mirGfniBodyStep, shamirMacRange] using
      ih (pS + 32) (pA + 32) (rem - 1)
        (writeMem256 mem pA (gfniShamirMacBlock coeff (readMem256 mem pS) (readMem256 mem pA)))

/-- Symbol execution behind a zero-count guard on `rcx`. The guard branch is a hand-written
model of the Rust wrapper's early return on empty input, not decoded machine code. -/
def gfniShamirMacGuardedRun (fetch : Nat → Option (DecodedInstr X86Instr))
    (fuel : Nat) (s : X86State) : X86State × List StepObs :=
  if s.gpr.get 1 == 0 then
    ({ s with pc := 134, gpr := (s.gpr.set 0 0 |>.set 2 0), ymmDirty := false, halted := true },
     [⟨0, [], true⟩])
  else runX86Fetch fetch fuel s

def mirGfniRun (n : Word) (baseS baseA scalar : UInt64) (mem : UInt64 → UInt8) :
    MirShamirMac × List StepObs :=
  let coeff := gfniScaledCoeff scalar
  if n = 0 then (⟨baseS, baseA, coeff, 0, mem⟩, [⟨0, [], true⟩])
  else
    let loop := runCuts mirGfniBodyStep n.toNat ⟨baseS, baseA, coeff, n.toNat, mem⟩
    (loop.1, gfniEntryObs ++ loop.2 ++ gfniExitObs)

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
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_movImm, maskGprWidth_true, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vmovGprToXmm, maskGprWidth_true, b16get_0, b16set_14]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vpbroadcastQ, b16get_14, b16set_14]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_movImm, maskGprWidth_true, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vmovGprToXmm, maskGprWidth_true, b16get_0, b16set_15]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vpbroadcastQ, b16get_15, b16set_15]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vmovGprToXmm, b16get_2, b16set_3]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vpbroadcastB, b16get_3, b16set_3]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]
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
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vload256, b16get_6, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vload256, b16get_7, b16set_1]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vgf2p8affine256, b16get_0, b16get_14, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vbinOp256, b16get_0, b16get_3, b16set_2]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vgf2p8affine256, b16get_2, b16get_15, b16set_2]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vbinOp256, b16get_1, b16get_2, b16set_1]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vstore256, b16get_7, b16get_1]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_addImm64, b16get_6, b16set_6]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_addImm64, b16get_7, b16set_7]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_dec64, b16get_1, b16set_1]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]
  simp only [stepX86Full_jnz, gfniBodyStep, gfniBodyObs,
    b16get_1, b16get_3, b16get_6, b16get_7, b16get_14, b16get_15,
    b16set_0, b16set_1, b16set_2, b16set_6, b16set_7]
  rfl

theorem gfni_exit_full (fetch : Nat → Option (DecodedInstr X86Instr))
    (hf : ∀ d ∈ gfniShamirMacProg, fetch d.offset = some d)
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Vec256)
    (cf o zf dy : Bool) (m : UInt64 → UInt8) (extra : Nat) :
    runX86Fetch fetch (10 + extra)
      ⟨101, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
        cf, o, zf, dy, false, m⟩ =
      (⟨134, ⟨0, r1, 0, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨Vec256.zero, Vec256.zero, Vec256.zero, Vec256.zero,
          zeroUpperVec256 y4, zeroUpperVec256 y5, zeroUpperVec256 y6, zeroUpperVec256 y7,
          zeroUpperVec256 y8, zeroUpperVec256 y9, zeroUpperVec256 y10, zeroUpperVec256 y11,
          zeroUpperVec256 y12, zeroUpperVec256 y13, Vec256.zero, Vec256.zero⟩,
        false, false, true, false, true, m⟩,
       gfniExitObs) := by
  rw [show 10 + extra = (((((((((extra + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 from by omega]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vbinOp256, b16get_0, vpxor_self, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vbinOp256, b16get_1, vpxor_self, b16set_1]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vbinOp256, b16get_2, vpxor_self, b16set_2]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vbinOp256, b16get_3, vpxor_self, b16set_3]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vbinOp256, b16get_14, vpxor_self, b16set_14]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vbinOp256, b16get_15, vpxor_self, b16set_15]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_xorRR, b16get_0, mask32_xor_self_eq, u64_zero_beq_true, b16set_0]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_xorRR, b16get_2, mask32_xor_self_eq, u64_zero_beq_true, b16set_2]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]; simp only [stepX86Full_vzeroupper, vzeroupper_bank16, zeroUpperVec256_zero]
  rw [runX86Fetch_step_prog fetch _ hf _ _ _ rfl rfl]
  simp only [stepX86Full_ret, gfniExitObs]
  rw [runX86Fetch_halted _ _ _ rfl]

def GfniMacRel (s₀ : X86State) (n v : Nat) (a : X86State) (m : MirShamirMac) : Prop :=
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

def GfniMacLoopPost (s₀ : X86State) (n : Nat) (a : X86State) (m : MirShamirMac) : Prop :=
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

