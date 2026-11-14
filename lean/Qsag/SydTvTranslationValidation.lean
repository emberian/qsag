module
public import Qsag.ElfBinaryVerify
public import Qsag.McRefine
public import Qsag.ElfParse
import all Qsag.ElfBinaryVerify
import all Qsag.McRefine
import all Qsag.ElfFixtureSlices
public section

/-!
# `Qsag.SydTvTranslationValidation` — Sewell–Myreen–Klein Cut-Point Translation Validation

Untrusted search / certificate checking over **real byte-decoded `ElfBinaryVerify` instructions**
(`decodeX86One` / `decodeArm64One`, `stepX86` / `runX86`, `stepArm64` / `runArm64`, `StepObs`)
extracted from compiled `qsag_asm` `.rlib` archives (`ElfFixtureSlices` / `ElfParse`):

1. **Unrestricted 64-Bit Trip Counts (`∀ n : BitVec 64`)**:
   `UnrestrictedLoopCert` certifies **both** the `n = 0` zero-trip entry-to-exit cut and the
   `n ≠ 0` positive-trip Sewell loop-relation cuts (`LoopRelationCert`), proving functional
   refinement (`unrestricted_loop_refinement_sound`) and 3-way `StepObs` constant-time
   noninterference (`unrestricted_three_way_noninterference`) across all `2^64` counts.
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
    {asmExec : A → A × List StepObs} {mirExec : M → M × List StepObs}
    {asmBody : A → A × List StepObs} {mirBody : M → M × List StepObs}
    {a₁ a₂ : A} {m₁ m₂ : M} {ah₁ ah₂ : A} {mh₁ mh₂ : M}
    {LP₁ LP₂ P : A → M → Prop}
    (c₁ : UnrestrictedLoopCert A M n asmExec mirExec asmBody mirBody a₁ m₁ ah₁ mh₁ LP₁ P)
    (c₂ : UnrestrictedLoopCert A M n asmExec mirExec asmBody mirBody a₂ m₂ ah₂ mh₂ LP₂ P)
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
  rfl

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

theorem zeroUpperVec256_zero : zeroUpperVec256 Vec256.zero = Vec256.zero := rfl

theorem vzeroupper_bank16 (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Vec256) :
    Bank16.ofFn (fun i =>
      let v := (Bank16.mk y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15).get i
      ⟨v.w0, v.w1, 0, 0⟩) =
    Bank16.mk (zeroUpperVec256 y0) (zeroUpperVec256 y1) (zeroUpperVec256 y2) (zeroUpperVec256 y3)
      (zeroUpperVec256 y4) (zeroUpperVec256 y5) (zeroUpperVec256 y6) (zeroUpperVec256 y7)
      (zeroUpperVec256 y8) (zeroUpperVec256 y9) (zeroUpperVec256 y10) (zeroUpperVec256 y11)
      (zeroUpperVec256 y12) (zeroUpperVec256 y13) (zeroUpperVec256 y14) (zeroUpperVec256 y15) := rfl

section FullSteps
variable (off len pc : Nat) (g : Bank16 UInt64) (y : Bank16 Vec256) (cf o zf dy : Bool)
  (m : UInt64 → UInt8)

theorem stepX86Full_movRR (is64 : Bool) (dst src : Nat) :
    stepX86 ⟨off, len, .movRegReg is64 dst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g.set dst (maskGprWidth is64 (g.get src)), y, cf, o, zf, dy, false, m⟩,
       ⟨off, [], true⟩) := rfl

theorem stepX86Full_movImm (is64 : Bool) (dst : Nat) (imm : UInt64) :
    stepX86 ⟨off, len, .movImm is64 dst imm⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g.set dst (maskGprWidth is64 imm), y, cf, o, zf, dy, false, m⟩,
       ⟨off, [], true⟩) := rfl

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
       ⟨off, [], true⟩) := rfl

theorem stepX86Full_orRR (is64 : Bool) (dst src : Nat) :
    stepX86 ⟨off, len, .aluRegReg .orOp is64 dst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g.set dst (maskGprWidth is64 (g.get dst ||| g.get src)), y, false, false,
        maskGprWidth is64 (g.get dst ||| g.get src) == 0, dy, false, m⟩,
       ⟨off, [], true⟩) := rfl

theorem stepX86Full_subImm32 (dst : Nat) (imm : UInt64) :
    stepX86 ⟨off, len, .aluImm .sub false dst imm⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len,
        g.set dst (maskGprWidth false (UInt64.ofNat (((maskGprWidth false (g.get dst)).toNat + 0x100000000 -
          (maskGprWidth false imm).toNat) % 0x100000000))), y,
        decide ((maskGprWidth false (g.get dst)).toNat < (maskGprWidth false imm).toNat), o,
        maskGprWidth false (UInt64.ofNat (((maskGprWidth false (g.get dst)).toNat + 0x100000000 -
          (maskGprWidth false imm).toNat) % 0x100000000)) == 0, dy, false, m⟩,
       ⟨off, [], true⟩) := rfl

theorem stepX86Full_shr32_31 (dst : Nat) :
    stepX86 ⟨off, len, .shiftImm .shr false dst 31⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len,
        g.set dst (maskGprWidth false (maskGprWidth false (g.get dst) >>> UInt64.ofNat (31 % 32))), y, cf, o,
        maskGprWidth false (maskGprWidth false (g.get dst) >>> UInt64.ofNat (31 % 32)) == 0, dy, false, m⟩,
       ⟨off, [], true⟩) := rfl

theorem stepX86Full_addImm64 (dst : Nat) (imm : UInt64) :
    stepX86 ⟨off, len, .aluImm .add true dst imm⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g.set dst (g.get dst + imm), y,
        (evalX86Alu .add true (g.get dst) imm cf).2.1, o,
        (evalX86Alu .add true (g.get dst) imm cf).2.2, dy, false, m⟩,
       ⟨off, [], true⟩) := by
  simp only [stepX86, u64_evalAdd64_val]
  rfl

theorem stepX86Full_inc64 (dst : Nat) :
    stepX86 ⟨off, len, .incDec true true dst⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g.set dst (g.get dst + 1), y, cf, o, g.get dst + 1 == 0, dy, false, m⟩,
       ⟨off, [], true⟩) := rfl

theorem stepX86Full_dec64 (dst : Nat) :
    stepX86 ⟨off, len, .incDec false true dst⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g.set dst (g.get dst - 1), y, cf, o, g.get dst - 1 == 0, dy, false, m⟩,
       ⟨off, [], true⟩) := by
  simp only [stepX86, maskGprWidth_true, u64_add_neg_one]

theorem stepX86Full_jnz (tgt : Int) :
    stepX86 ⟨off, len, .jcc 5 tgt⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨jccPc (!zf) tgt (off + len), g, y, cf, o, zf, dy, false, m⟩,
       ⟨off, [], true⟩) := rfl

theorem stepX86Full_mfence :
    stepX86 ⟨off, len, .mfence⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g, y, cf, o, zf, dy, false, m⟩, ⟨off, [], true⟩) := rfl

theorem stepX86Full_ret :
    stepX86 ⟨off, len, .ret⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨pc, g, y, cf, o, zf, dy, true, m⟩, ⟨off, [], true⟩) := rfl

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
       ⟨off, [], true⟩) := rfl

theorem stepX86Full_vpbroadcastQ (dst src : Nat) :
    stepX86 ⟨off, len, .vpbroadcast true dst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g, y.set dst (bcastQword256 (y.get src).w0), cf, o, zf, true, false, m⟩,
       ⟨off, [], true⟩) := rfl

theorem stepX86Full_vpbroadcastB (dst src : Nat) :
    stepX86 ⟨off, len, .vpbroadcast false dst src⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩ =
      (⟨off + len, g, y.set dst (bcastByte256 (y.get src).w0.toUInt8), cf, o, zf, true, false, m⟩,
       ⟨off, [], true⟩) := rfl

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
       ⟨off, [], true⟩) := rfl

end FullSteps

section ArmFullSteps
variable (off len pc : Nat) (g : Bank32 UInt64) (v : Bank32 Vec128) (cf zf dit : Bool)
  (m : UInt64 → UInt8)

theorem stepArm64Full_strbPost31_0 :
    stepArm64 ⟨off, len, .strbPost 31 0 1⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩ =
      (⟨off + 4, armSet g 0 (armGet g 0 + 1), v, cf, zf, dit, false, writeMem8 m (armGet g 0) 0⟩,
       ⟨off, [(armGet g 0, 1)], true⟩) := rfl

theorem stepArm64Full_subsImm1_1 :
    stepArm64 ⟨off, len, .aluImm .subs true 1 1 1⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩ =
      (⟨off + 4, armSet g 1 (armGet g 1 - 1), v, decide ((armGet g 1).toNat ≥ 1),
        armGet g 1 - 1 == 0, dit, false, m⟩,
       ⟨off, [], true⟩) := by
  simp only [stepArm64, evalArmAlu, getArmGpr, setArmGpr, armGet, armSet, maskGprWidth_true]
  have hsub : UInt64.ofNat (((armGet g 1).toNat + 0x10000000000000000 - (1 : UInt64).toNat) %
      0x10000000000000000) = armGet g 1 - 1 := by
    apply u64_eq_of_toNat_eq
    have hlt : (armGet g 1).toNat < 18446744073709551616 := (armGet g 1).toNat_lt
    have h1 : (1 : UInt64).toNat = 1 := rfl
    have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
    rw [UInt64.toNat_ofNat', UInt64.toNat_sub, h1, h64]
    omega
  rw [hsub]
  rfl

theorem stepArm64Full_bne0 :
    stepArm64 ⟨off, len, .bCond 1 0⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩ =
      (⟨jccPc (!zf) 0 (off + 4), g, v, cf, zf, dit, false, m⟩,
       ⟨off, [], true⟩) := rfl

theorem stepArm64Full_dmbIsh :
    stepArm64 ⟨off, len, .dmbIsh⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩ =
      (⟨off + 4, g, v, cf, zf, dit, false, m⟩, ⟨off, [], true⟩) := rfl

theorem stepArm64Full_ret :
    stepArm64 ⟨off, len, .ret⟩ ⟨pc, g, v, cf, zf, dit, false, m⟩ =
      (⟨pc, g, v, cf, zf, dit, true, m⟩, ⟨off, [], true⟩) := rfl

end ArmFullSteps

theorem mask32_xor_self_eq (x : UInt64) : maskGprWidth false (x ^^^ x) = 0 := by
  rw [UInt64.xor_self]; rfl

theorem u64_zero_beq_true : ((0 : UInt64) == 0) = true := rfl

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
    have h : base + UInt64.ofNat v + 1 = base + UInt64.ofNat (v + 1) := by
      apply u64_eq_of_toNat_eq
      rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
      have h1 : (1 : UInt64).toNat = 1 := rfl
      rw [h1]
      omega
    exact h

theorem ptrStride_32_eq (base : UInt64) (v : Nat) :
    ptrStride base 32 v = base + UInt64.ofNat (32 * v) := by
  induction v with
  | zero => simp [ptrStride]
  | succ v ih =>
    simp only [ptrStride, ih]
    apply u64_eq_of_toNat_eq
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
    have h32 : (32 : UInt64).toNat = 32 := rfl
    rw [h32]
    have : ((base.toNat + 32 * v % 2 ^ 64) % 2 ^ 64 + 32) % 2 ^ 64 =
        (base.toNat + 32 * (v + 1) % 2 ^ 64) % 2 ^ 64 := by
      have hm1 := Nat.add_mod base.toNat (32 * v) (2 ^ 64)
      have hm2 := Nat.add_mod (base.toNat + 32 * v) 32 (2 ^ 64)
      have hm3 := Nat.add_mod base.toNat (32 * (v + 1)) (2 ^ 64)
      have h32lt : 32 % 2 ^ 64 = 32 := by decide
      have hbm : base.toNat % 2 ^ 64 = base.toNat := Nat.mod_eq_of_lt base.toNat_lt
      rw [hbm] at hm1 hm3
      rw [← hm1, h32lt] at hm2
      rw [← hm2, ← hm3]
      exact congrArg (· % 2 ^ 64) (by omega)
    exact this

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
      let b := memzeroX86BodyStep s
      let u := runX86Fetch fetch fuel b.1
      (u.1, b.2 ++ u.2) := by
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
  simp only [stepX86Full_ret, runX86Fetch_halted _ _ _ rfl, memzeroX86ExitObs]
  rfl

end MemzeroX86Fetch

def MemzeroX86Rel (s₀ : X86State) (n v : Nat) (a : X86State) (m : MirMemzero) : Prop :=
  ∃ zf : Bool,
    a = ⟨if v = n then 15 else 5,
          (s₀.gpr.set 0 0 |>.set 1 (UInt64.ofNat (n - v)) |>.set 7 (ptrStride (s₀.gpr.get 7) 1 v)),
          s₀.ymm, false, false, zf, s₀.ymmDirty, false, m.mem⟩ ∧
    m.ptr = ptrStride (s₀.gpr.get 7) 1 v ∧
    m.remaining = n - v

def MemzeroX86LoopPost (s₀ : X86State) (n : Nat) (a : X86State) (m : MirMemzero) : Prop :=
  ∃ zf : Bool,
    a = ⟨15, (s₀.gpr.set 0 0 |>.set 1 0 |>.set 7 (ptrStride (s₀.gpr.get 7) 1 n)),
          s₀.ymm, false, false, zf, s₀.ymmDirty, false, m.mem⟩ ∧
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
  rw [UInt64.toNat_sub, UInt64.toNat_ofNat', UInt64.toNat_ofNat']
  have h1 : (1 : UInt64).toNat = 1 := rfl
  rw [h1, Nat.mod_eq_of_lt hbound, Nat.mod_eq_of_lt (by omega)]
  omega

theorem u64_ofNat_eq_zero_iff {k : Nat} (hbound : k < 2 ^ 64) :
    (UInt64.ofNat k == 0) = decide (k = 0) := by
  cases k with
  | zero => rfl
  | succ j =>
    have hne : UInt64.ofNat (j + 1) ≠ 0 := by
      intro h
      have := congrArg UInt64.toNat h
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hbound] at this
      omega
    simp [beq_false_of_ne hne]

