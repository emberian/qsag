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
