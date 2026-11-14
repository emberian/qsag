module

public meta import Lean
import Lean.Data.Options
public import Aeneas.Std.Types

public section

open Lean Elab Command Term Meta

meta section

register_option linter.dupNamespace : Bool := {
  defValue := false
  descr := "Aeneas compatibility linter option"
}

register_option linter.hashCommand : Bool := {
  defValue := false
  descr := "Aeneas compatibility linter option"
}

register_option linter.style.whitespace : Bool := {
  defValue := false
  descr := "Aeneas compatibility linter option"
}

register_option linter.style.setOption : Bool := {
  defValue := false
  descr := "Aeneas compatibility linter option"
}

register_option linter.style.longLine : Bool := {
  defValue := false
  descr := "Aeneas compatibility linter option"
}

register_option linter.internalConstructors : Bool := {
  defValue := false
  descr := "Aeneas compatibility linter option"
}

end

syntax (name := aeneasGlobalSimps) "global_simps" : attr
syntax (name := aeneasRustLoopBody) "rust_loop_body" : attr
syntax (name := aeneasRustLoop) "rust_loop" : attr
syntax (name := aeneasDiscriminant) "discriminant " ident : attr

meta initialize
  registerBuiltinAttribute {
    name := `aeneasGlobalSimps
    descr := "Marker attribute emitted by Aeneas on global constants"
    add := fun _ _ _ => pure ()
  }
  registerBuiltinAttribute {
    name := `aeneasRustLoopBody
    descr := "Marker attribute emitted by Aeneas on extracted MIR loop bodies"
    add := fun _ _ _ => pure ()
  }
  registerBuiltinAttribute {
    name := `aeneasRustLoop
    descr := "Marker attribute emitted by Aeneas on extracted MIR loops"
    add := fun _ _ _ => pure ()
  }

meta def generateDiscriminantInst (declName : Name) (tyIdent : Ident) : CommandElabM Unit := do
  let indVal ← liftCoreM (getConstInfoInduct declName)
  if indVal.numParams > 0 || indVal.numIndices > 0 then
    throwError "discriminant: indexed/parametric inductives not needed for {declName}"
  let mut alts : Array (TSyntax ``Parser.Term.matchAlt) := #[]
  for idx in [:indVal.ctors.length] do
    let ctorName := indVal.ctors[idx]!
    let ctorInfo ← liftCoreM (getConstInfoCtor ctorName)
    let mut holes : Array Term := #[]
    for _ in [:ctorInfo.numFields] do
      holes := holes.push (← `(_))
    let pat ← `($(mkCIdent ctorName):ident $holes:term*)
    let lit := Syntax.mkNumLit (toString idx)
    let rhs : Term ← match tyIdent.getId with
      | `isize => `(Aeneas.Std.IScalar.ofInt .Isize (Int.ofNat $lit))
      | `usize => `(Aeneas.Std.UScalar.ofNat .Usize $lit)
      | `u8    => `(Aeneas.Std.UScalar.ofNat .U8 $lit)
      | `u32   => `(Aeneas.Std.UScalar.ofNat .U32 $lit)
      | other  => throwError "discriminant: unsupported scalar kind {other}"
    let alt ← `(Parser.Term.matchAltExpr| | $pat => $rhs)
    alts := alts.push alt
  let discrTy : Term ← match tyIdent.getId with
    | `isize => `(Aeneas.Std.Isize)
    | `usize => `(Aeneas.Std.Usize)
    | `u8    => `(Aeneas.Std.U8)
    | `u32   => `(Aeneas.Std.U32)
    | other  => throwError "discriminant: unsupported scalar kind {other}"
  let cmd ← `(
    @[reducible]
    public instance : Aeneas.Std.Discriminant $(mkCIdent declName) $discrTy where
      read_discriminant x := match x with $alts:matchAlt*
  )
  elabCommand cmd

meta initialize
  registerBuiltinAttribute {
    name := `aeneasDiscriminant
    descr := "Generates a faithful `Aeneas.Std.Discriminant` instance for a Rust enum"
    add := fun declName stx _ => do
      match stx with
      | `(attr| discriminant $ty:ident) =>
        liftCommandElabM (generateDiscriminantInst declName ty)
      | _ => throwUnsupportedSyntax
  }

meta partial def replaceSelfRef (selfId : Name) (replacement : Syntax) (stx : Syntax) : Syntax :=
  match stx with
  | .ident _ _ val _ =>
    if val == selfId then replacement else stx
  | .node info kind args =>
    .node info kind (args.map (replaceSelfRef selfId replacement))
  | _ => stx

/-- Elaborates Aeneas `impl_def` trait-dictionary definitions by breaking vacuous
    default-method self-references (`core.cmp.Eq.assert_fields_are_eq.default <self>`). -/
elab mods:declModifiers "impl_def " id:declId sig:optDeclSig " := " body:term : command => do
  let rawId : Name :=
    match id with
    | `(Parser.Command.declId| $n:ident $[.{$_us,*}]?) => n.getId
    | _ => Name.anonymous
  let unitStx ← `(())
  let cleanBody : Term := ⟨replaceSelfRef rawId unitStx.raw body.raw⟩
  let cmd ← `($mods:declModifiers def $id:declId $sig:optDeclSig := $cleanBody)
  elabCommand cmd
