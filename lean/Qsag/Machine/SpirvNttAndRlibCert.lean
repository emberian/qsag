module
public import Qsag.Machine.SpirvKernelSem
public import Qsag.Spec.Assumptions
import Qsag.Machine.Tactic.KernelRfl
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Spv

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Initialize the Function-storage slots declared in the entry block. The fused loop's
    only live-ins are the local invocation index (%351) and the stage counter (%495).
    All other values used by its body are assigned in this epoch. -/
private def stageFrame {D : Type} (entry : List Inst) (stage lid : Nat) : Frame D :=
  let locals := entry.filterMap fun i => match i.op, i.args with
    | 59, [_, k, 7] => some (k, Val.undef)
    | _, _ => none
  ⟨put 351 (.n lid) (put 495 (.n stage) locals), []⟩

private def loopDecision {D : Type} (img : Image) (w : World D) (test : List Inst)
    (fr : Frame D) : Option (Res D) :=
  run img w (callFn img w 2 8)
    (fun l fr' g => some (some (.n l), fr', g)) test fr ⟨[.blk 500], [], 0⟩

private def butterfly {D : Type} (img : Image) (w : World D) (body : List Inst)
    (fr : Frame D) (g : Glob D) : Option (List Ev) := do
  let finish := fun l (fr' : Frame D) (g' : Glob D) =>
    if l = 499 then some (none, fr', g') else none
  let (_, _, out) ← run img w (callFn img w 2 8) finish body ⟨fr.vars, []⟩
    {g with evs := .blk 497 :: g.evs}
  return out.evs.reverse

private def afterTest {D : Type} (img : Image) (w : World D) (body : List Inst) :
    Option (Res D) → Option (List Ev)
  | some (some (.n 497), f, g) => butterfly img w body f g
  | _ => none

/-- Execute the fused loop test, its selected butterfly and the callees through the barrier. -/
def fusedEpoch {D : Type} (img : Image) (w : World D) (stage lid : Nat) : Option (List Ev) := do
  let f ← callBody.findFn img.entry img.functions
  let (_, decls) ← f.blocks.head?
  let test ← look 500 f.blocks
  let body ← look 497 f.blocks
  afterTest img w body (loopDecision img w test (stageFrame decls stage lid))

/-- Independent shared-load responses include adversarial interleavings. A data
    operator may inspect its payload; the evaluator still keeps its result opaque. -/
structure SecretMemory where
  read : Nat → List Nat → Nat → Nat
  binary : Nat → Nat → Nat → Nat → Nat
  unary : Nat → Nat → Nat → Nat
  select : Nat → Nat → Nat → Nat

def memoryWorld (d : SecretMemory) : World Nat where
  secBin := d.binary
  secUn := d.unary
  secSel := d.select
  inj := id
  pc := []
  builtin _ := .undef
  load v p n := .sec (d.read v p n)

private def zeroMemory : SecretMemory :=
  ⟨fun _ _ _ => 0, fun _ _ _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0⟩

def stageRun (img : Image) (d : SecretMemory) (stage lid : Nat) : Option (List Ev) :=
  fusedEpoch img (memoryWorld d) stage lid

private def loopTest (stage : Nat) : Bool := decide (stage % 2^32 ≤ 9)

private theorem inLoop (s : Fin 9) : loopTest (s.val + 1) = true := by
  unfold loopTest
  rw [Nat.mod_eq_of_lt (by have := s.isLt; omega)]
  exact decide_eq_true (by have := s.isLt; omega)

private def epochBlock (l : Nat) : List Inst :=
  (look l (ntt.functions.headD ⟨0, [], []⟩).blocks).getD []

private def bodyRun (d : SecretMemory) (s lid : Nat) :=
  butterfly ntt (memoryWorld d) (epochBlock 497) (stageFrame (epochBlock 5) s lid)
    ⟨[.blk 500], [], 0⟩

private theorem takeButterfly (s : Fin 9) (lid : Nat) (d : SecretMemory) :
    stageRun ntt d (s.val + 1) lid = bodyRun d (s.val + 1) lid := by
  let fr := stageFrame (D := Nat) (epochBlock 5) (s.val + 1) lid
  let g : Glob Nat := ⟨[.blk 500], [], 0⟩
  let test := loopDecision ntt (memoryWorld d) (epochBlock 500) fr
  let after := afterTest ntt (memoryWorld d) (epochBlock 497)
  have step : stageRun ntt d (s.val + 1) lid = after test := by kernel_rfl
  let x := (s.val + 1) % 2^32
  let c := loopTest (s.val + 1)
  let f : Frame Nat := ⟨fr.vars, [(502, .b c), (501, .n x)]⟩
  have branch : test = (bif c then some (some (.n 497), f, g)
                        else some (some (.n 498), f, g)) := by kernel_rfl
  rw [step, branch, show c = true from inLoop s]
  rfl

private abbrev u32 (n : Nat) := n % 4294967296
private abbrev sub32 (x y : Nat) := u32 (x + 4294967296 - u32 y)

private def swizzled (x : Nat) : Nat :=
  let i := u32 (u32 x)
  u32 (i ^^^ u32 (((i >>> 5) &&& 1) * 31))

/-- Normal form of the complete event sequence of block %497 and its callees.
    Width conversions reflect the typed loads and shifts of the shader. -/
private def butterflyEvents (stage lid : Nat) : List Ev :=
  let s := u32 stage
  let shift := sub32 s 1
  let half := u32 (1 <<< shift)
  let lane := u32 lid
  let j := u32 (lane &&& sub32 (u32 half) 1)
  let left := u32 (u32 ((lane >>> shift) <<< s) + j)
  let right := u32 (u32 left + u32 half)
  let tw := swizzled (u32 (j <<< sub32 9 s))
  let even := swizzled (u32 left)
  let odd := swizzled (u32 right)
  [.blk 500, .blk 497, .blk 25, .blk 11,
   .rd 118 [0, tw], .rd 118 [1, tw], .blk 16, .blk 11,
   .rd 79 [0, even], .rd 79 [1, even], .blk 16, .blk 11,
   .rd 79 [0, odd], .rd 79 [1, odd], .blk 50, .blk 33,
   .blk 33, .blk 46, .blk 33, .blk 38,
   .blk 33, .blk 33, .blk 42, .blk 33,
   .blk 33, .blk 38, .blk 33, .blk 33,
   .blk 22, .blk 11, .wr 79 [0, even], .wr 79 [1, even],
   .blk 42, .blk 33, .blk 33, .blk 22,
   .blk 11, .wr 79 [0, odd], .wr 79 [1, odd], .barrier]

private theorem bodyEvents (d : SecretMemory) (s lid : Nat) :
    bodyRun d s lid = some (butterflyEvents s lid) := by kernel_rfl

private theorem exactEpoch (s : Fin 9) (lid : Nat) (d : SecretMemory) :
    stageRun ntt d (s.val + 1) lid = some (butterflyEvents (s.val+1) lid) :=
  (takeButterfly s lid d).trans (bodyEvents d _ _)

theorem stageIndependent (s : Fin 9) (lid : Nat) (a b : SecretMemory) :
    stageRun ntt a (s.val + 1) lid = stageRun ntt b (s.val + 1) lid :=
  (exactEpoch s lid a).trans (exactEpoch s lid b).symm


/-- Follow the decoded post-barrier suffix through the increment and loop header.
    Stop immediately before the test. This carries the actual frame and log across jumps. -/
private def toTest {D : Type} (img : Image) (w : World D) (f : Fn) :
    Nat → Nat → Frame D → Glob D → Option (Res D)
  | fuel, label, fr, g =>
    if label = 500 then some (none, fr, g)
    else match fuel with
    | 0 => none
    | k+1 => do
      let code ← look label f.blocks
      run img w (callFn img w 2 8) (toTest img w f k) code ⟨fr.vars, []⟩
        {g with evs := .blk label :: g.evs}

/-- The zero-based stage counter agrees with the previous iteration's one-based
    shader counter. Stage zero starts after the initialization barrier in %458.
    Every subsequent stage starts after the preceding butterfly barrier in %497. -/
private def stagePreludeFrom (img : Image) (w : World Nat) (label s lid : Nat) :
    Option (Nat × Nat × List Ev) := do
  let f ← callBody.findFn img.entry img.functions
  let (_, decls) ← f.blocks.head?
  let code ← look label f.blocks
  let _ :: suffix := code.dropWhile (fun i => i.op != 224) | none
  let (_, fr, g) ← run img w (callFn img w 2 8) (toTest img w f 2) suffix
    (stageFrame decls s lid) ⟨[], [], 0⟩
  let .n next ← look 495 fr.vars | none
  let .n lane ← look 351 fr.vars | none
  return (next, lane, g.evs.reverse)

private def stagePrelude (img : Image) (w : World Nat) (s lid : Nat) :=
  stagePreludeFrom img w (if s = 0 then 458 else 497) s lid

private def prefixLabels (s : Nat) : List Ev :=
  if s = 0 then [.blk 496] else [.blk 499, .blk 496]

private theorem prelude_eq (s : Fin 9) (lid : Nat) (d : SecretMemory) :
    stagePrelude ntt (memoryWorld d) s lid = some (s.val+1,lid,prefixLabels s) := by
  by_cases h : s.val = 0
  · rw [h]; kernel_rfl
  · have body : stagePreludeFrom ntt (memoryWorld d) 497 s lid =
        some (((s.val % 2^32) + 1) % 2^32, lid, [.blk 499,.blk 496]) := by kernel_rfl
    have inc : ((s.val % 2^32) + 1) % 2^32 = s.val+1 := by have := s.isLt; omega
    simp only [stagePrelude, prefixLabels, h, ite_false, body, inc]

/-- Replay a full interval between barriers using the loop body's two live-in slots. -/
def barrierEpoch (d : SecretMemory) (s lid : Nat) : Option (List Ev) := do
  let (next,lane,entered) ← stagePrelude ntt (memoryWorld d) s lid
  let body ← stageRun ntt d next lane
  return entered ++ body

private theorem barrierEvents (s : Fin 9) (lid : Nat) (d : SecretMemory) :
    barrierEpoch d s lid = some (prefixLabels s ++ butterflyEvents (s.val+1) lid) := by
  unfold barrierEpoch
  rw [prelude_eq]
  change (stageRun ntt d (s.val+1) lid).bind _ = _
  rw [exactEpoch s]; rfl

/-- The architecture-level DIT observable here is the ordered branch and memory
    trace of a fused epoch. Data includes all shared-load responses and opaque ALU results. -/
def nttEpochDit : Spec.DitHardwareContract (Fin 9 × Nat) SecretMemory (Option (List Ev)) where
  observe _ op d := barrierEpoch d op.1 op.2
  dataIndependent op a b := (barrierEvents op.1 op.2 a).trans (barrierEvents op.1 op.2 b).symm

private def labels (evs : List Ev) : List Nat :=
  evs.filterMap fun e => match e with | .blk l => some l | _ => none

/-- Flatten the two uint32 planes of s_lds, followed by the two planes of s_tw. -/
private def cell (r : Nat) (path : List Nat) : Option Nat :=
  match r, path with
  | 79, [p,k] => some (512*p + k)
  | 118, [p,k] => some (1024 + 256*p + k)
  | _, _ => none

private def writes (evs : List Ev) :=
  evs.filterMap fun e => match e with | .wr r p => cell r p | _ => none

private def reads (evs : List Ev) :=
  evs.filterMap fun e => match e with | .rd r p => cell r p | _ => none

/-- The contract has the legacy zero-based stage argument. Valid stages execute
    the decoded condition and body with shader counter stage+1. -/
def decodedStageContract (stage : Nat) : Spec.SimtWorkgroupContract where
  subgroupSize := 32
  workgroupSize := ntt.localSize.headD 0
  blockTrace lid := labels ((barrierEpoch zeroMemory stage lid).getD [])
  writeSet lid := writes ((barrierEpoch zeroMemory stage lid).getD [])
  readSet lid := reads ((barrierEpoch zeroMemory stage lid).getD [])
  h_divides := ⟨by decide, ⟨8,rfl⟩⟩

private theorem blockTrace_eq (s : Fin 9) (lid : Nat) :
    (decodedStageContract s.val).blockTrace lid = labels (prefixLabels s ++ butterflyEvents (s.val+1) lid) :=
  congrArg (fun v : Option (List Ev) => labels (v.getD [])) (barrierEvents s lid zeroMemory)

theorem ntt_decoded_stage_nonempty (s : Fin 9) (lid : Nat) :
    (decodedStageContract s.val).blockTrace lid ≠ [] := by
  rw [blockTrace_eq]
  unfold prefixLabels
  split <;> exact List.cons_ne_nil _ _

theorem ntt_decoded_stage_uniform (s : Fin 9) :
    (decodedStageContract s.val).UniformControlFlow := by
  intro i j _ _ _
  have uniform : labels (butterflyEvents (s.val+1) i) = labels (butterflyEvents (s.val+1) j) := by kernel_rfl
  rw [blockTrace_eq, blockTrace_eq]
  unfold labels
  rw [List.filterMap_append, List.filterMap_append]
  exact congrArg (labels (prefixLabels s) ++ ·) uniform

private theorem projectEpoch (s : Fin 9) (lid : Nat) :
    (decodedStageContract s.val).writeSet lid = writes (butterflyEvents (s.val+1) lid) ∧
    (decodedStageContract s.val).readSet lid = reads (butterflyEvents (s.val+1) lid) := by
  have h := barrierEvents s lid zeroMemory
  change writes ((barrierEpoch zeroMemory s lid).getD []) = _ ∧ reads ((barrierEpoch zeroMemory s lid).getD []) = _
  rw [h]
  unfold prefixLabels; split <;> exact ⟨rfl,rfl⟩

private def writer (s k : Nat) :=
  let v := k % 512
  let i := v ^^^ (((v >>> 5) &&& 1) * 31)
  ((i >>> (s+1)) <<< s) + (i &&& (2^s-1))

/-- In the barrier epoch every written cell is in the main LDS array and belongs
    to the issuing lane. Twiddle planes are read-only and disjoint from that array. -/
private theorem owners : ∀ s : Fin 9, ∀ lid : Fin 256,
    (writes (butterflyEvents (s.val+1) lid)).all (fun k => k < 1024 && writer s k == lid.val) = true ∧
    (reads (butterflyEvents (s.val+1) lid)).all (fun k => k ≥ 1024 || writer s k == lid.val) = true := by
  decide +kernel

theorem ntt_decoded_stage_disjoint (s : Fin 9) :
    (decodedStageContract s.val).DisjointStorageBindings := by
  intro i j hi hj hne k hw
  rw [(projectEpoch s i).1] at hw
  obtain ⟨bound, wi⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp (owners s ⟨i,hi⟩).1 k hw)
  have hwi : writer s k = i := Nat.eq_of_beq_eq_true wi
  constructor
  · intro hwj
    rw [(projectEpoch s j).1] at hwj
    have h := Bool.and_eq_true_iff.mp (List.all_eq_true.mp (owners s ⟨j,hj⟩).1 k hwj)
    exact hne (hwi.symm.trans (Nat.eq_of_beq_eq_true h.2))
  · intro hrj
    rw [(projectEpoch s j).2] at hrj
    have h := Bool.or_eq_true_iff.mp (List.all_eq_true.mp (owners s ⟨j,hj⟩).2 k hrj)
    cases h with
    | inl bad => have h₁ := of_decide_eq_true bound; have h₂ := of_decide_eq_true bad; omega
    | inr wj => exact hne (hwi.symm.trans (Nat.eq_of_beq_eq_true wj))

/-- Global word accesses of one dispatch, in issue order. Storage is rooted at %413.
    Read responses remain arbitrary at each address and sequence number. -/
def nttGlobalAccesses (d : SecretMemory) (mode n logN stage lid : Nat) :
    Option (List (Bool × List Nat)) := do
  let w := {memoryWorld d with
    pc := [.n 1,.n n,.n logN,.n stage,.n mode,.n 0,.n 0]
    builtin := fun kind => if kind = 27 then .arr [.n lid,.n 0,.n 0]
      else if kind = 26 then .arr [.n 0,.n 0,.n 0] else .undef}
  let g ← runEntry ntt w 100 10
  return g.evs.reverse.filterMap fun e => match e with
    | .rd 413 path => some (false,path)
    | .wr 413 path => some (true,path)
    | _ => none

theorem ntt_global_butterfly (d : SecretMemory) :
    nttGlobalAccesses d 2 512 9 1 3 =
      some [(false,[0,6]), (false,[0,7]), (true,[0,6]), (true,[0,7])] := by kernel_rfl

theorem ntt_bit_reversal_swap (d : SecretMemory) :
    nttGlobalAccesses d 0 8 3 0 1 =
      some [(false,[0,1]), (false,[0,4]), (true,[0,1]), (true,[0,4])] := by kernel_rfl

/-- One edge connects a possible source of data to its consumer. A variable or
    pointer ID denotes its contents, a function ID denotes its return, and an SSA
    result ID denotes its value. Sinks are operands that control a branch or address. -/
structure Flow where
  edges : List (Nat × Nat) := []
  sinks : List Nat := []

private def operandsTo (xs : List Nat) (y : Nat) : Flow :=
  ⟨xs.map (fun x => (x,y)), []⟩

/-- Every instruction in every basic block is visited, including all loop back-edges'
    blocks. Actual and formal slots alias in both directions. Access-chain contents
    alias the base conservatively, and each subscript is independently a sink. -/
private def instructionFlow (img : Image) (f : Fn) (i : Inst) : Option Flow :=
  match i.op, i.args with
  | 59, [_,_,7] | 249, [_] | 253, [] | 246, [_,_,_] | 247, [_,_] => some {}
  | 62, [p,x] => some (operandsTo [x] p)
  | 61, [_,r,p] => some (operandsTo [p] r)
  | 65, _ :: r :: base :: indices => some ⟨[(base,r),(r,base)], indices⟩
  | 250, [c,_,_] => some ⟨[],[c]⟩
  | 224, [a,b,c] => some ⟨[],[a,b,c]⟩
  | 254, [v] => some (operandsTo [v] f.id)
  | 57, _ :: r :: id :: args => do
    let callee ← callBody.findFn id img.functions
    if args.length != callee.params.length then none
    else
      let pairs := args.zip callee.params
      some ⟨(id,r) :: pairs ++ pairs.map Prod.swap, []⟩
  | 169, [_,r,c,x,y] => some (operandsTo [c,x,y] r)
  | 113, [_,r,x] | 200, [_,r,x] | 204, [_,r,x] => some (operandsTo [x] r)
  | op, [_,r,x,y] =>
    if [128,130,132,170,171,172,174,176,178,194,196,197,198,199].contains op then
      some (operandsTo [x,y] r)
    else none
  | _, _ => none

def kernelFlow (img : Image) : Option Flow := do
  let chunks ← img.functions.mapM fun f => f.blocks.mapM fun (_, block) =>
    block.mapM (instructionFlow img f)
  let instructions := chunks.flatten.flatten
  return ⟨instructions.flatMap Flow.edges, instructions.flatMap Flow.sinks⟩

def sharedRoots (img : Image) : List Nat :=
  img.globals.filterMap fun (r,sc) => if sc == 4 || sc == 12 then some r else none

/-- A path from a shared load through any number of instructions, loop iterations or calls. -/
inductive MayDepend (roots : List Nat) (f : Flow) : Nat → Prop where
  | root {x} : x ∈ roots → MayDepend roots f x
  | step {x y} : MayDepend roots f x → (x,y) ∈ f.edges → MayDepend roots f y

def flowCheck (img : Image) (secret : Nat → Bool) : Bool :=
  match kernelFlow img with
  | none => false
  | some f =>
    (sharedRoots img).all secret &&
    f.edges.all (fun (x,y) => !secret x || secret y) &&
    f.sinks.all (fun x => !secret x)

private theorem checked_no_path {img : Image} {f : Flow} {secret : Nat → Bool}
    (hf : kernelFlow img = some f) (ok : flowCheck img secret = true) :
    ∀ x ∈ f.sinks, ¬ MayDepend (sharedRoots img) f x := by
  unfold flowCheck at ok
  rw [hf] at ok
  simp only [Bool.and_eq_true, List.all_eq_true] at ok
  obtain ⟨⟨roots, edges⟩, sinks⟩ := ok
  intro x sink path
  have tainted : secret x = true := by
    clear sink
    induction path with
    | root mem => exact roots _ mem
    | step _ edge ih =>
      have h := edges _ edge
      rw [ih] at h
      exact h
  have h := sinks _ sink
  rw [tainted] at h
  contradiction

/-- Bit i of this certificate marks ID i as potentially secret. All bits are checked
    against the decoded instruction constraints, including the three shared roots. -/
def nttSecret (id : Nat) : Bool :=
  Nat.testBit 0x678000fdfbf7702490000003f7efddfbe1080000014000140000900000000c06013e9ff998200000001203807000001f00dbdea2000000000000001e07c0005cf9ffffffffffffffffcffffeecfffff3ffffffe7a9f701f7403dc06e708000021bbbb989108000 id

theorem ntt_flow_checked : flowCheck ntt nttSecret = true := by kernel_rfl

theorem ntt_no_secret_branch_or_address :
    ∃ f, kernelFlow ntt = some f ∧ ∀ x ∈ f.sinks, ¬ MayDepend (sharedRoots ntt) f x := by
  cases h : kernelFlow ntt with
  | none =>
    have ok := ntt_flow_checked
    unfold flowCheck at ok
    rw [h] at ok
    contradiction
  | some f => exact ⟨f, rfl, checked_no_path h ntt_flow_checked⟩

/-- Mutate %89's second LDS subscript in lds_load to %85, the value just loaded
    from plane zero. Both the original index and its replacement have type uint32. -/
def secretIndexedNtt : Image :=
  { ntt with functions := ntt.functions.map fun f => {f with blocks := f.blocks.map fun (l, is) =>
      (l, is.map fun i => if i.op == 65 && i.args == [83,89,79,87,88]
                           then ⟨65,[83,89,79,87,85]⟩ else i)} }

theorem ntt_secret_lookup_rejected : ¬ ∃ mark, flowCheck secretIndexedNtt mark = true := by
  let f := (kernelFlow secretIndexedNtt).getD {}
  have decoded : kernelFlow secretIndexedNtt = some f := by kernel_rfl
  have root : 79 ∈ sharedRoots secretIndexedNtt := by decide +kernel
  have e₁ : (79,84) ∈ f.edges := by decide +kernel
  have e₂ : (84,85) ∈ f.edges := by decide +kernel
  have sink : 85 ∈ f.sinks := by decide +kernel
  intro ⟨mark, ok⟩
  exact checked_no_path decoded ok 85 sink (.step (.step (.root root) e₁) e₂)

#tooth_pair ntt_no_secret_branch_or_address vs ntt_secret_lookup_rejected

#print axioms ntt_global_butterfly
#print axioms ntt_bit_reversal_swap
#print axioms ntt_decoded
#print axioms ntt_no_secret_branch_or_address
#print axioms ntt_secret_lookup_rejected
#print axioms stageIndependent
#print axioms nttEpochDit
#print axioms ntt_decoded_stage_uniform
#print axioms ntt_decoded_stage_nonempty
#print axioms ntt_decoded_stage_disjoint

end Qsag.Spv
end
