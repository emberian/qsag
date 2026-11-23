module
import Lean
import all Aeneas.Elab.Attrs
import all Lean.Util.CollectAxioms

open Lean

private def funsModule : Name := `QsagWhirVerified.Funs

private def isToothTheorem (thm : Name) : Bool :=
  match thm with
  | .str _ s => s.startsWith "tooth_"
  | _ => false

private def extractedSymbols (env : Environment) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      if env.header.moduleNames[idx.toNat]! == funsModule && !name.isInternalDetail then
        if let .defnInfo _ := info then out := out.push name
  return out.qsort fun a b => a.toString < b.toString

private def definitionUses (env : Environment) (name used : Name) : Bool :=
  match env.find? name with
  | some (.defnInfo d) => d.value.getUsedConstants.contains used
  | _ => false

private def loopOrigin? (name : Name) : Option (Name × Name) :=
  let loopName := match name with
    | .str pre "body" => pre
    | other => other
  match loopName with
  | .str pre s =>
    if s.endsWith "_loop" && s.length > 5 then
      some (.str pre (String.ofList (s.toList.take (s.length - 5))), loopName)
    else none
  | _ => none

private def symbolCoverage (env : Environment) (theorems : Array Name) :
    Array Name × Array Name := Id.run do
  let symbols := extractedSymbols env
  let mut mentioned : NameSet := {}
  for thm in theorems do
    if !isToothTheorem thm then
      if let some (.thmInfo info) := env.find? thm then
        for used in info.type.getUsedConstants do
          mentioned := mentioned.insert used
  let mut gaps : Array Name := #[]
  for symbol in symbols do
    let covered :=
      match loopOrigin? symbol with
      | some (origin, loopName) =>
        symbols.contains origin && mentioned.contains origin &&
          definitionUses env origin loopName &&
          (symbol == loopName || definitionUses env loopName symbol)
      | none => mentioned.contains symbol
    if !covered then gaps := gaps.push symbol
  return (symbols, gaps)

private def symbolCoverageControlsFail (env : Environment) (theorems : Array Name) : Bool :=
  let (symbols, allGaps) := symbolCoverage env #[]
  let (_, toothOnlyGaps) := symbolCoverage env (theorems.filter isToothTheorem)
  let target := `qsag_whir_verified.checked_quorum_sum
  let withoutTarget := theorems.filter fun thm =>
    match env.find? thm with
    | some (.thmInfo info) => !info.type.getUsedConstants.contains target
    | _ => true
  let (_, targetGaps) := symbolCoverage env withoutTarget
  symbols.isEmpty || allGaps.size != symbols.size || toothOnlyGaps.size != symbols.size ||
    !(targetGaps.contains target &&
      targetGaps.contains `qsag_whir_verified.checked_quorum_sum_loop &&
      targetGaps.contains `qsag_whir_verified.checked_quorum_sum_loop.body)

private def isIdentRestChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.' || c == '\''

private def takeIdentChars : List Char → List Char
  | [] => []
  | c :: cs => if isIdentRestChar c then c :: takeIdentChars cs else []

private def extractTickNames : List Char → Array Name → Array Name
  | '`' :: '`' :: cs, acc =>
    let ident := String.ofList (takeIdentChars cs)
    let acc' := if ident.isEmpty then acc else acc.push ident.toName
    extractTickNames cs acc'
  | _ :: cs, acc => extractTickNames cs acc
  | [], acc => acc

private def parseAnchoredTheorems (src : String) : IO (Array Name) := do
  match src.splitOn "requiredWhirMirTheorems : Array Name := #[" with
  | _ :: rest :: _ =>
    let body := match rest.splitOn "]" with
      | b :: _ => b
      | [] => ""
    let out := extractTickNames body.toList #[]
    if out.isEmpty then
      throw (IO.userError "Parsed empty requiredWhirMirTheorems from AuditWhirMirAxioms.lean")
    return out
  | _ => throw (IO.userError "Could not locate requiredWhirMirTheorems in AuditWhirMirAxioms.lean")

public def main : IO UInt32 := do
  initSearchPath (← findSysroot) [".lake/build/lib/lean", "../../lean/.lake/build/lib/lean"]
  let requiredWhirMirTheorems ← parseAnchoredTheorems (← IO.FS.readFile "AuditWhirMirAxioms.lean")
  let imported ← importModules #[{ module := `AuditWhirMirAxioms, importAll := true }] {}
  let env := imported.setExporting false
  let summaries := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let mut missingAnchors : Array Name := #[]
  for req in requiredWhirMirTheorems do
    match env.find? req with
    | some (.thmInfo _) => pure ()
    | _ => missingAnchors := missingAnchors.push req
  let (negative, checked, theorems, modules, failures) := CollectAxioms.runM (env.setExporting false) do
    let negative ← CollectAxioms.collectAndGet summaries.find? ``Classical.choice
    let mut checked := 0
    let mut theorems := 0
    let mut modules : Array Name := #[]
    let mut failures : Array (Name × Array Name) := #[]
    for (name, _) in env.constants.toList do
      if let some idx := env.getModuleIdxFor? name then
        let owner := env.header.moduleNames[idx.toNat]!.toString
        if (owner == "QsagWhirSpecWeld" || owner == "QsagWhirVerified" || owner.startsWith "QsagWhirVerified." ||
            owner == "Aeneas" || owner.startsWith "Aeneas.") &&
            !(owner == "Aeneas.Elab.Attrs" && isMarkedMeta env name) then
          checked := checked + 1
          if let some (.thmInfo _) := env.find? name then theorems := theorems + 1
          let ownerName := env.header.moduleNames[idx.toNat]!
          if !modules.contains ownerName then modules := modules.push ownerName
          let axioms ← CollectAxioms.collectAndGet summaries.find? name
          let forbidden := axioms.filter fun ax => ax != ``propext && ax != ``Quot.sound
          if !forbidden.isEmpty then
            failures := failures.push (name, forbidden)
    return (negative, checked, theorems, modules, failures)
  if (negative.filter fun ax => ax != ``propext && ax != ``Quot.sound).isEmpty then
    throw (IO.userError "WHIR MIR axiom audit negative control unexpectedly passed")
  let config ← IO.ofExcept (Json.parse (← IO.FS.readFile "comparator.json"))
  let replayed := (← IO.ofExcept (config.getObjValAs? (Array String) "theorem_names")).map
    String.toName
  let unanchored := replayed.filter fun thm => !requiredWhirMirTheorems.contains thm
  let (symbols, gaps) := symbolCoverage env replayed
  if symbolCoverageControlsFail env replayed then
    throw (IO.userError "WHIR symbol coverage negative control unexpectedly passed")
  for thm in unanchored do
    IO.println s!"REPLAYED THEOREM WITHOUT AN AXIOM ANCHOR {thm}"
  for symbol in gaps do
    IO.println s!"EXTRACTED SYMBOL WITHOUT A REPLAYED THEOREM STATEMENT {symbol}"
  IO.println s!"WHIR symbol coverage: {symbols.size} extracted symbols, {replayed.size} replayed theorems; {gaps.size} uncovered, {unanchored.size} unanchored"
  for req in missingAnchors do
    IO.println s!"MISSING ANCHOR THEOREM {req}"
  for (name, forbidden) in failures do
    IO.println s!"REJECT {name}: {forbidden}"
  IO.println s!"WHIR MIR axiom audit: {checked} declarations, {theorems} theorems ({requiredWhirMirTheorems.size} anchored), {modules.size} modules; {failures.size} rejected, {missingAnchors.size} missing anchors"
  return if checked > 0 && failures.isEmpty && missingAnchors.isEmpty &&
      !symbols.isEmpty && gaps.isEmpty && unanchored.isEmpty then 0 else 1
