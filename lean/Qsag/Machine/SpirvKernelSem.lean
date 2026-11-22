module
/-
# Qsag.Machine.SpirvKernelSem — evaluator for the decoded instruction streams of `SpirvKernelImages`

One invocation of a compute shader, executed instruction by instruction over an `Spv.Image`:
function frames with `Function`-storage variables, `OpAccessChain` into local arrays and into
module-scope variables, nested `OpFunctionCall`, structured control flow by jumping between the
decoded basic blocks, and a log of every basic block entered and every load from or store to
`StorageBuffer` / `Workgroup` memory.

What the evaluator fixes, and where it is narrower than SPIR-V:

* Integers are `Nat`s. Every arithmetic result is reduced modulo `2 ^ width` of its result type and
  every `OpLoad` of an integer type reduces what it reads, so no well-formedness invariant on the
  values is needed. A shift by at least the width (undefined in SPIR-V) is the mathematical shift.
* Data may be opaque (`Val.sec`). Arithmetic on it stays opaque through the operations of the
  `World`. An opaque value in a branch condition or an access-chain index has no rule: the run
  is `none`. A run that is `some` therefore never branched on, or indexed memory by, such a value.
* A load from `StorageBuffer` / `Workgroup` memory returns `World.load var path seq`, where `seq`
  counts the shared loads of the invocation. Statements quantify over the world, so the value of
  every shared load is arbitrary: this covers whatever other invocations stored.
* SSA results live for one basic block: a jump discards them. A use of a result of another block
  has no rule (`none`). glslang's unoptimised output, which both kernels are, passes values
  between blocks through `Function` variables only.
* `OpFunctionCall` copies the argument variables in and the parameter variables back out, and has
  no rule unless the arguments are distinct `Function` variables of the caller (then this is the
  pointer semantics).
* An opcode outside the ones below has no rule.

Recursion is structural (instruction list, block fuel `bf` per call, call depth), so the kernel
evaluates a run by definitional unfolding, also when values are free variables.
-/
public import Qsag.Machine.SpirvKernelImages

public section
namespace Qsag.Spv
set_option autoImplicit false

/-- A value of an invocation. `sec` is data the evaluator may compute with but not inspect. -/
inductive Val (D : Type) where
  | n (v : Nat)
  | b (v : Bool)
  | sec (d : D)
  | arr (xs : List (Val D))
  | ptr (root : Nat) (path : List Nat)
  | undef

/-- What an invocation does that another invocation or a timing observer can see. -/
inductive Ev where
  | blk (label : Nat)
  | rd (var : Nat) (path : List Nat)
  | wr (var : Nat) (path : List Nat)
  | barrier
  deriving DecidableEq, Repr

/-- Everything outside the invocation. -/
structure World (D : Type) where
  /-- Binary operation `opcode width` on opaque data. -/
  secBin : Nat → Nat → D → D → D
  /-- Unary operation `opcode width` on opaque data. -/
  secUn : Nat → Nat → D → D
  /-- `OpSelect` with an opaque condition. -/
  secSel : D → D → D → D
  /-- A known integer as an operand of an opaque operation. -/
  inj : Nat → D
  /-- Members of the push-constant block. -/
  pc : List (Val D)
  /-- Value of the input variable decorated `BuiltIn kind`. -/
  builtin : Nat → Val D
  /-- Value returned by the `seq`-th shared load, from `var` at `path`. -/
  load : Nat → List Nat → Nat → Val D

structure Frame (D : Type) where
  vars : List (Nat × Val D)
  ssa : List (Nat × Val D)

/-- Log of an invocation; `evs` and `outs` are newest first. -/
structure Glob (D : Type) where
  evs : List Ev
  outs : List (Nat × List Nat × Val D)
  seq : Nat

abbrev Res (D : Type) := Option (Val D) × Frame D × Glob D

/-- A callee: function id, argument values, log ↦ return value, final parameter values, log. -/
abbrev CallFn (D : Type) :=
  Nat → List (Val D) → Glob D → Option (Option (Val D) × List (Val D) × Glob D)

@[expose] def look {α : Type} (k : Nat) : List (Nat × α) → Option α
  | [] => none
  | (k', v) :: rest =>
    match Nat.beq k' k with
    | true => some v
    | false => look k rest

/-- Environments are shadowing association lists. A write changes precisely the first
    binding returned by lookup and shares the old tail with the caller's frame. -/
@[expose] def put {α : Type} (k : Nat) (v : α) (env : List (Nat × α)) : List (Nat × α) :=
  (k, v) :: env

@[expose] def Val.at {D : Type} : Val D → List Nat → Option (Val D)
  | v, [] => some v
  | .arr xs, i :: rest =>
    match xs[i]? with
    | some x => Val.at x rest
    | none => none
  | _, _ :: _ => none

@[expose] def Val.setAt {D : Type} : Val D → List Nat → Val D → Option (Val D)
  | _, [], x => some x
  | .arr xs, i :: rest, x =>
    match xs[i]? with
    | some old =>
      match Val.setAt old rest x with
      | some new => some (.arr (xs.set i new))
      | none => none
    | none => none
  | _, _ :: _, _ => none

/-- `OpIAdd`, `OpISub`, `OpIMul`, `OpShiftRightLogical`, `OpShiftLeftLogical`, `OpBitwiseOr`,
    `OpBitwiseXor`, `OpBitwiseAnd` at width `w`. -/
@[expose] def arith (op w a b : Nat) : Option Nat :=
  if op = 128 then some ((a + b) % 2 ^ w)
  else if op = 130 then some ((a + 2 ^ w - b % 2 ^ w) % 2 ^ w)
  else if op = 132 then some ((a * b) % 2 ^ w)
  else if op = 194 then some (a >>> b)
  else if op = 196 then some ((a <<< b) % 2 ^ w)
  else if op = 197 then some (a ||| b)
  else if op = 198 then some (a ^^^ b)
  else if op = 199 then some (a &&& b)
  else none

/-- `OpIEqual`, `OpINotEqual`, `OpUGreaterThan`, `OpUGreaterThanEqual`, `OpULessThan`,
    `OpULessThanEqual`. -/
@[expose] def cmp (op a b : Nat) : Option Bool :=
  if op = 170 then some (decide (a = b))
  else if op = 171 then some (!decide (a = b))
  else if op = 172 then some (decide (b < a))
  else if op = 174 then some (decide (b ≤ a))
  else if op = 176 then some (decide (a < b))
  else if op = 178 then some (decide (a ≤ b))
  else none

/-- `OpNot`, `OpUConvert` and `OpBitReverse` at result width `w`. -/
@[expose] def unop (op w a : Nat) : Option Nat :=
  if op = 200 then some (2 ^ w - 1 - a % 2 ^ w)
  else if op = 113 then some (a % 2 ^ w)
  else if op = 204 then some (reverseBits w a 0)
  else none
where
  reverseBits : Nat → Nat → Nat → Nat
    | 0, _, result => result
    | k+1, x, result => reverseBits k (x / 2) (2 * result + x % 2)

/-- Execute the rest of a basic block. `jump` continues at a label; `call` runs a callee. -/
@[expose] def run {D : Type} (img : Image) (W : World D) (call : CallFn D)
    (jump : Nat → Frame D → Glob D → Option (Res D)) :
    List Inst → Frame D → Glob D → Option (Res D)
  | [], _, _ => none
  | i :: rest, fr, g =>
    if i.op = 61 then
      match i.args with
      | [ty, res, p] =>
        match opnd img fr p with
        | some (.ptr root path) =>
          match loadAt img W fr g root path with
          | some (v, g') =>
            run img W call jump rest { vars := fr.vars, ssa := (res, nrm img ty v) :: fr.ssa } g'
          | none => none
        | _ => none
      | _ => none
    else if i.op = 62 then
      match i.args with
      | [p, x] =>
        match opnd img fr p, opnd img fr x with
        | some (.ptr root path), some v =>
          match storeAt img fr g root path v with
          | some (fr', g') => run img W call jump rest fr' g'
          | none => none
        | _, _ => none
      | _ => none
    else if i.op = 57 then
      match i.args with
      | _ :: res :: fid :: argIds =>
        match distinct argIds, argVals fr.vars argIds with
        | true, some vals =>
          match call fid vals g with
          | some (ret, outs, g') =>
            match writeBack argIds outs fr.vars with
            | some vars' =>
              match ret with
              | some v => run img W call jump rest { vars := vars', ssa := (res, v) :: fr.ssa } g'
              | none => run img W call jump rest { vars := vars', ssa := fr.ssa } g'
            | none => none
          | none => none
        | _, _ => none
      | _ => none
    else if i.op = 65 then
      match i.args with
      | _ :: res :: base :: idxIds =>
        match opnd img fr base, indices img fr idxIds with
        | some (.ptr root path), some ks =>
          run img W call jump rest { vars := fr.vars, ssa := (res, .ptr root (path ++ ks)) :: fr.ssa } g
        | _, _ => none
      | _ => none
    else if i.op = 249 then
      match i.args with
      | [l] => jump l fr g
      | _ => none
    else if i.op = 250 then
      match i.args with
      | c :: t :: f :: _ =>
        match opnd img fr c with
        | some (.b bv) => bif bv then jump t fr g else jump f fr g
        | _ => none
      | _ => none
    else if i.op = 246 then run img W call jump rest fr g
    else if i.op = 247 then run img W call jump rest fr g
    else if i.op = 59 then
      match i.args with
      | [ty, id, _] =>
        run img W call jump rest { vars := put id (initVal img ty) fr.vars, ssa := fr.ssa } g
      | [_, id, _, init] =>
        match opnd img fr init with
        | some v => run img W call jump rest { vars := put id v fr.vars, ssa := fr.ssa } g
        | none => none
      | _ => none
    else if i.op = 253 then some (none, fr, g)
    else if i.op = 254 then
      match i.args with
      | [x] =>
        match opnd img fr x with
        | some v => some (some v, fr, g)
        | none => none
      | _ => none
    else if i.op = 224 then
      run img W call jump rest fr { evs := .barrier :: g.evs, outs := g.outs, seq := g.seq }
    else if i.op = 169 then
      match i.args with
      | [_, res, c, t, f] =>
        match opnd img fr c, opnd img fr t, opnd img fr f with
        | some (.b bv), some (.n x), some (.n y) =>
          run img W call jump rest
            { vars := fr.vars, ssa := (res, .n (bif bv then x else y)) :: fr.ssa } g
        | some (.sec dc), some vt, some vf =>
          match toD W vt, toD W vf with
          | some dt, some df =>
            run img W call jump rest
              { vars := fr.vars, ssa := (res, .sec (W.secSel dc dt df)) :: fr.ssa } g
          | _, _ => none
        | _, _, _ => none
      | _ => none
    else
      match i.args with
      | [ty, res, a] =>
        match opnd img fr a with
        | some (.n x) =>
          match unop i.op (width img ty) x with
          | some r => run img W call jump rest { vars := fr.vars, ssa := (res, .n r) :: fr.ssa } g
          | none => none
        | some (.sec d) =>
          match unop i.op (width img ty) 0 with
          | some _ =>
            run img W call jump rest
              { vars := fr.vars, ssa := (res, .sec (W.secUn i.op (width img ty) d)) :: fr.ssa } g
          | none => none
        | _ => none
      | [ty, res, a, b] =>
        match opnd img fr a, opnd img fr b with
        | some (.n x), some (.n y) =>
          match arith i.op (width img ty) x y with
          | some r => run img W call jump rest { vars := fr.vars, ssa := (res, .n r) :: fr.ssa } g
          | none =>
            match cmp i.op x y with
            | some c => run img W call jump rest { vars := fr.vars, ssa := (res, .b c) :: fr.ssa } g
            | none => none
        | some va, some vb =>
          match toD W va, toD W vb, known i.op with
          | some da, some db, true =>
            run img W call jump rest
              { vars := fr.vars, ssa := (res, .sec (W.secBin i.op (width img ty) da db)) :: fr.ssa } g
          | _, _, _ => none
        | _, _ => none
      | _ => none
where
  /-- Value of an operand id: an SSA result of this block, a pointer to a variable, a constant. -/
  opnd (img : Image) (fr : Frame D) (id : Nat) : Option (Val D) :=
    match look id fr.ssa with
    | some v => some v
    | none =>
      match look id fr.vars with
      | some _ => some (.ptr id [])
      | none =>
        match look id img.scalars with
        | some k => some (.n k)
        | none =>
          match look id img.composites with
          | some ks => some (.arr (ks.map Val.n))
          | none =>
            match look id img.globals with
            | some _ => some (.ptr id [])
            | none => none
  width (img : Image) (ty : Nat) : Nat :=
    match look ty img.widths with
    | some w => w
    | none => 0
  /-- An integer read by `OpLoad` at an integer type is reduced to the width of that type. -/
  nrm (img : Image) (ty : Nat) (v : Val D) : Val D :=
    match v with
    | .n x =>
      match look ty img.widths with
      | some w => .n (x % 2 ^ w)
      | none => .n x
    | v => v
  /-- Initial value of a `Function` variable of pointer type `ty` without initializer. -/
  initVal (img : Image) (ty : Nat) : Val D :=
    match look ty img.pointers with
    | some pointee =>
      match look pointee img.arrays with
      | some len => .arr (List.replicate len .undef)
      | none => .undef
    | none => .undef
  /-- Read through a pointer: a `Function` variable (class 7), the push-constant block (9), a
      built-in input (1), or shared memory (`StorageBuffer` 12, `Workgroup` 4). -/
  loadAt (img : Image) (W : World D) (fr : Frame D) (g : Glob D) (root : Nat) (path : List Nat) :
      Option (Val D × Glob D) :=
    match look root fr.vars with
    | some v =>
      match v.at path with
      | some x => some (x, g)
      | none => none
    | none =>
      match look root img.globals with
      | some sc =>
        if sc = 9 then
          match (Val.arr W.pc).at path with
          | some x => some (x, g)
          | none => none
        else if sc = 1 then
          match look root img.builtins with
          | some kind =>
            match (W.builtin kind).at path with
            | some x => some (x, g)
            | none => none
          | none => none
        else if sc = 12 then
          some (W.load root path g.seq, { evs := .rd root path :: g.evs, outs := g.outs, seq := g.seq + 1 })
        else if sc = 4 then
          some (W.load root path g.seq, { evs := .rd root path :: g.evs, outs := g.outs, seq := g.seq + 1 })
        else none
      | none => none
  storeAt (img : Image) (fr : Frame D) (g : Glob D) (root : Nat) (path : List Nat) (v : Val D) :
      Option (Frame D × Glob D) :=
    match look root fr.vars with
    | some old =>
      match old.setAt path v with
      | some new => some ({ vars := put root new fr.vars, ssa := fr.ssa }, g)
      | none => none
    | none =>
      match look root img.globals with
      | some sc =>
        if sc = 12 then
          some (fr, { evs := .wr root path :: g.evs, outs := (root, path, v) :: g.outs, seq := g.seq })
        else if sc = 4 then
          some (fr, { evs := .wr root path :: g.evs, outs := (root, path, v) :: g.outs, seq := g.seq })
        else none
      | none => none
  /-- Access-chain indices: known integers only. -/
  indices (img : Image) (fr : Frame D) : List Nat → Option (List Nat)
    | [] => some []
    | id :: ids =>
      match opnd img fr id, indices img fr ids with
      | some (.n k), some ks => some (k :: ks)
      | _, _ => none
  distinct : List Nat → Bool
    | [] => true
    | a :: as =>
      match as.any (Nat.beq a) with
      | true => false
      | false => distinct as
  argVals (vars : List (Nat × Val D)) : List Nat → Option (List (Val D))
    | [] => some []
    | id :: ids =>
      match look id vars, argVals vars ids with
      | some v, some vs => some (v :: vs)
      | _, _ => none
  writeBack : List Nat → List (Val D) → List (Nat × Val D) → Option (List (Nat × Val D))
    | [], [], vars => some vars
    | id :: ids, v :: vs, vars => writeBack ids vs (put id v vars)
    | _, _, _ => none
  toD (W : World D) : Val D → Option D
    | .sec d => some d
    | .n x => some (W.inj x)
    | .b v => some (W.inj (bif v then 1 else 0))
    | _ => none
  known (op : Nat) : Bool :=
    match arith op 0 0 0, cmp op 0 0 with
    | none, none => false
    | _, _ => true

/-- Continue function `f` at block `l`, entering at most `fuel` blocks. -/
@[expose] def execFrom {D : Type} (img : Image) (W : World D) (call : CallFn D) (f : Fn) :
    Nat → Nat → Frame D → Glob D → Option (Res D)
  | 0, _, _, _ => none
  | fuel + 1, l, fr, g =>
    match look l f.blocks with
    | some insts =>
      run img W call (execFrom img W call f fuel) insts { vars := fr.vars, ssa := [] }
        { evs := .blk l :: g.evs, outs := g.outs, seq := g.seq }
    | none => none

/-- One call of function `fid` whose own calls are answered by `call`. -/
@[expose] def callBody {D : Type} (img : Image) (W : World D) (bf : Nat) (call : CallFn D) : CallFn D :=
  fun fid args g =>
    match findFn fid img.functions with
    | some f =>
      match bind f.params args, f.blocks with
      | some vars, (l, insts) :: _ =>
        match run img W call (execFrom img W call f bf) insts { vars := vars, ssa := [] }
            { evs := .blk l :: g.evs, outs := g.outs, seq := g.seq } with
        | some (ret, fr, g') =>
          match run.argVals fr.vars f.params with
          | some outs => some (ret, outs, g')
          | none => none
        | none => none
      | _, _ => none
    | none => none
where
  findFn (fid : Nat) : List Fn → Option Fn
    | [] => none
    | f :: fs =>
      match Nat.beq f.id fid with
      | true => some f
      | false => findFn fid fs
  bind : List Nat → List (Val D) → Option (List (Nat × Val D))
    | [], [] => some []
    | p :: ps, v :: vs =>
      match bind ps vs with
      | some tail => some ((p, v) :: tail)
      | none => none
    | _, _ => none

/-- Calls nested at most `depth` deep, each entering at most `bf` further blocks. -/
@[expose] def callFn {D : Type} (img : Image) (W : World D) (bf : Nat) : Nat → CallFn D
  | 0 => fun _ _ _ => none
  | depth + 1 => callBody img W bf (callFn img W bf depth)

theorem callFn_succ {D : Type} (img : Image) (W : World D) (bf depth : Nat) :
    callFn img W bf (depth + 1) = callBody img W bf (callFn img W bf depth) := rfl

/-- Run the entry point of `img` from an empty log. -/
@[expose] def runEntry {D : Type} (img : Image) (W : World D) (bf depth : Nat) : Option (Glob D) :=
  match callFn img W bf depth img.entry [] { evs := [], outs := [], seq := 0 } with
  | some (_, _, g) => some g
  | none => none

end Qsag.Spv
end
