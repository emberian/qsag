module
import Lean
import AxiomAuditSupport
import all Aeneas.Elab.Attrs
import all Lean.Util.CollectAxioms

open Lean

private def funsModule : Name := `QsagWhirVerified.Funs

private def allowedAxiom (ax : Name) : Bool :=
  ax == ``propext || ax == ``Quot.sound

private def isPackageOwner (owner : String) : Bool :=
  owner == "QsagWhirSpecWeld" || owner == "QsagWhirVerified" || owner.startsWith "QsagWhirVerified."

private def isAeneasOwner (owner : String) : Bool :=
  owner == "Aeneas" || owner.startsWith "Aeneas."

private def isMetaElabHelper (env : Environment) (owner : String) (name : Name) : Bool :=
  (owner.startsWith "Aeneas.Elab." && (isDeclMeta env name || isDeclMeta env name.getPrefix)) ||
  (owner == "Aeneas.Elab.Attrs" && isMarkedMeta env name) ||
  QsagAudit.isCompileTimeAssurance env name

private def directDeps (info : ConstantInfo) : Array Name :=
  let tyDeps := info.type.getUsedConstants
  match info.value? (allowOpaque := true) with
  | some v => tyDeps ++ v.getUsedConstants
  | none => tyDeps

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
  let (negative, userDecls, userTheorems, pkgModules, pkgKernelConsts, aeneasConsts, transitiveConsts, failures) :=
    CollectAxioms.runM env do
      let negative ← CollectAxioms.collectAndGet summaries.find? ``Classical.choice
      let mut userDecls := 0
      let mut userTheorems := 0
      let mut pkgModules : Array Name := #[]
      let mut pkgKernelConsts := 0
      let mut aeneasConsts := 0
      let mut visited : NameSet := {}
      let mut todo : Array Name := #[]
      let mut failures : Array (Name × Array Name) := #[]
      for (name, info) in env.constants.toList do
        if let some idx := env.getModuleIdxFor? name then
          let ownerName := env.header.moduleNames[idx.toNat]!
          let owner := ownerName.toString
          if isMetaElabHelper env owner name then continue
          if isPackageOwner owner then
            pkgKernelConsts := pkgKernelConsts + 1
            if !pkgModules.contains ownerName then
              pkgModules := pkgModules.push ownerName
            if !QsagAudit.isCompilerGenerated env name then
              userDecls := userDecls + 1
              if info matches .thmInfo _ then
                userTheorems := userTheorems + 1
            if !visited.contains name then
              visited := visited.insert name
              todo := todo.push name
          else if isAeneasOwner owner then
            aeneasConsts := aeneasConsts + 1
            if !visited.contains name then
              visited := visited.insert name
              todo := todo.push name
      while h : todo.size > 0 do
        let cur := todo.back
        todo := todo.pop
        let axioms ← CollectAxioms.collectAndGet summaries.find? cur
        let forbidden := axioms.filter (!allowedAxiom ·)
        if !forbidden.isEmpty then
          failures := failures.push (cur, forbidden)
        if let some info := env.find? cur then
          for dep in directDeps info do
            if !visited.contains dep then
              if let some depIdx := env.getModuleIdxFor? dep then
                let depOwner := env.header.moduleNames[depIdx.toNat]!.toString
                if !isMetaElabHelper env depOwner dep then
                  visited := visited.insert dep
                  todo := todo.push dep
              else if (env.find? dep).isSome then
                visited := visited.insert dep
                todo := todo.push dep
      return (negative, userDecls, userTheorems, pkgModules, pkgKernelConsts, aeneasConsts, visited.size, failures)
  if (negative.filter (!allowedAxiom ·)).isEmpty then
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
  let userDefs := userDecls - userTheorems
  let otherDeps := transitiveConsts - (pkgKernelConsts + aeneasConsts)
  IO.println s!"WHIR MIR axiom audit (user-written & extracted QsagWhirVerified.*): {userDecls} declarations ({userTheorems} theorems, {userDefs} definitions/types; {requiredWhirMirTheorems.size} anchored) across {pkgModules.size} modules"
  IO.println s!"WHIR MIR axiom audit (transitive closure): {transitiveConsts} kernel constants audited ({pkgKernelConsts} in QsagWhirVerified/Weld, {aeneasConsts} in Aeneas stdlib, {otherDeps} reachable Qsag/Init/Std constants); {failures.size} rejected, {missingAnchors.size} missing anchors"
  return if userDecls > 0 && transitiveConsts >= pkgKernelConsts && failures.isEmpty &&
    missingAnchors.isEmpty && gaps.isEmpty && unanchored.isEmpty then 0 else 1
