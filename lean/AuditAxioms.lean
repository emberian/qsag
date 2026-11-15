module
import Qsag
import all Qsag.ElfFunctionalEquiv
import all Qsag.CorduroyAndHemAirCompleteness
import all Qsag.ActiveMigrationZeroTest
import all Qsag.AdvancedMpcAndCreds
import all Qsag.AffineProximityGaps
import all Qsag.Aggregation
import all Qsag.Apex
import all Qsag.BaggyAndRss256Security
import all Qsag.BinaryTower
import all Qsag.BlindVcQromSecurity
import all Qsag.CeremonyAtomicityAndAbort
import all Qsag.CompiledRlibFixtures
import all Qsag.ConcreteSecurityBudget
import all Qsag.ConstantTimeIsa
import all Qsag.Constructive
import all Qsag.Digest256
import all Qsag.MlDsa44Parameters
import all Qsag.CustodySuiteFull
import all Qsag.ElfBinaryVerify
import all Qsag.ElfFixtureSlices
import all Qsag.ElfFixtureVerify
import all Qsag.ElfInvCerts
import all Qsag.ElfParse
import all Qsag.FaultAndSpeculativeSafety
import all Qsag.Fips205
import all Qsag.GaussianHvzkAndDualLpn
import all Qsag.Goldilocks
import all Qsag.HashSigs
import all Qsag.HdToprfAndMigrationSecurity
import all Qsag.HypertreeEufCma
import all Qsag.IdealTsig
import all Qsag.InteractiveUcEngine
import all Qsag.IsaCosim
import all Qsag.JortsBeltLatchAndQuorumSwitching
import all Qsag.Keccak
import all Qsag.LatticePreprocessingFull
import all Qsag.MaliciousSecurity
import all Qsag.McRefine
import all Qsag.MirSpecBridge
import all Qsag.MirSpecBridgeCore
import all Qsag.MirSpecBridgeWitnesses
import all Qsag.MultiRoundFsQrom
import all Qsag.PallasAndBlsMigration
import all Qsag.ParallelSeededSpnSecurity
import all Qsag.Poseidon2
import all Qsag.Poseidon2AlgebraicAndRecursiveHem
import all Qsag.PosixCrashWal
import all Qsag.Preprocessing
import all Qsag.RlweCyclotomicExtraction
import all Qsag.RssSlhFullSecurity
import all Qsag.SimdBinaryEquiv
import all Qsag.SimulationSpine
import all Qsag.SpecOracle
import all Qsag.SpirvSimtGpuEquiv
import all Qsag.SuccinctAggregationIop
import all Qsag.SydTvTranslationValidation
import all Qsag.ThresholdApproval
import all Qsag.ThresholdMlDsaAndToprf
import all Qsag.ThresholdMlDsaSecurity
import all Qsag.ThresholdMpc
import all Qsag.UcGames
import all Qsag.CodingTheory.PolyMv3
import all Qsag.CodingTheory.SylvesterResultant
import all Qsag.CodingTheory.DynamicGcdSplit
import all Qsag.CodingTheory.HenselNumerators
import all Qsag.CodingTheory.UniversalHenselLift
import all Qsag.CodingTheory.TrivariateGsExplainer
import all Qsag.CodingTheory.SimpleRootStratification
import all Qsag.CodingTheory.AffineIncidenceBound
import all Qsag.CodingTheory.Cwyz26AffineGap
import all Qsag.Tactic.AssuranceKit
import all Qsag.Tactic.ConstructiveRing
import Lean
public meta import AxiomAuditSupport

/-!
# Constructive Kernel Axiom Gate (`AuditAxioms`)

Verifies that **every** declaration (both `public` and `.olean.private` via `import all` +
`setExporting false`) across the complete `Qsag` proof-module manifest depends strictly on a
subset of `{propext, Quot.sound}`:
1. **Zero Exclusions (`0` excluded modules):** Every proof module in `Qsag/` is held to the exact
   same constructive allowlist with zero diagnostic or exemption buckets.
2. **Negative Control:** Confirms `Lean.collectAxioms ``Classical.choice` is actively rejected.
3. **Manifest, `import all`, & Disk-Inventory Coverage:** Explicitly distinguishes meta/tactic
   infrastructure (`Qsag.Tactic.AssuranceKit`) from proof modules, verifies every manifest proof
   module is directly imported with `import all`, checks that no `Qsag/*.lean` file on disk or in
   the transitive import closure escapes the manifest, and verifies every proof module contributes
   `> 0` audited declarations.
-/

open Lean Elab Command in
run_cmd do
  let allow (ax : Name) : Bool := ax == ``propext || ax == ``Quot.sound

  -- 1. Negative control: the allowlist must reject `Classical.choice`.
  let negative ← Lean.collectAxioms ``Classical.choice
  if (negative.filter (!allow ·)).isEmpty then
    throwError "Axiom audit negative control unexpectedly passed"

  -- 2. Explicit proof-module vs meta-infrastructure manifest (all Qsag/*.lean modules).
  let infrastructureModules : Array Name := #[
    `Qsag.Tactic.AssuranceKit,
    `Qsag.Tactic.ConstructiveRing
  ]
  let auditedProofModules : Array Name := #[
    `Qsag.CodingTheory.PolyMv3,
    `Qsag.CodingTheory.SylvesterResultant,
    `Qsag.CodingTheory.DynamicGcdSplit,
    `Qsag.CodingTheory.HenselNumerators,
    `Qsag.CodingTheory.UniversalHenselLift,
    `Qsag.CodingTheory.TrivariateGsExplainer,
    `Qsag.CodingTheory.SimpleRootStratification,
    `Qsag.CodingTheory.AffineIncidenceBound,
    `Qsag.CodingTheory.Cwyz26AffineGap,
    `Qsag.ElfFunctionalEquiv,
    `Qsag.CorduroyAndHemAirCompleteness,
    `Qsag.ActiveMigrationZeroTest,
    `Qsag.AdvancedMpcAndCreds,
    `Qsag.AffineProximityGaps,
    `Qsag.Aggregation,
    `Qsag.Apex,
    `Qsag.BaggyAndRss256Security,
    `Qsag.BinaryTower,
    `Qsag.BlindVcQromSecurity,
    `Qsag.CeremonyAtomicityAndAbort,
    `Qsag.CompiledRlibFixtures,
    `Qsag.ConcreteSecurityBudget,
    `Qsag.ConstantTimeIsa,
    `Qsag.Constructive,
    `Qsag.Digest256,
    `Qsag.MlDsa44Parameters,
    `Qsag.MirSpecBridgeCore,
    `Qsag.MirSpecBridgeWitnesses,
    `Qsag.CustodySuiteFull,
    `Qsag.ElfBinaryVerify,
    `Qsag.ElfFixtureSlices,
    `Qsag.ElfFixtureVerify,
    `Qsag.ElfInvCerts,
    `Qsag.ElfParse,
    `Qsag.FaultAndSpeculativeSafety,
    `Qsag.Fips205,
    `Qsag.GaussianHvzkAndDualLpn,
    `Qsag.Goldilocks,
    `Qsag.HashSigs,
    `Qsag.HdToprfAndMigrationSecurity,
    `Qsag.HypertreeEufCma,
    `Qsag.IdealTsig,
    `Qsag.InteractiveUcEngine,
    `Qsag.IsaCosim,
    `Qsag.JortsBeltLatchAndQuorumSwitching,
    `Qsag.Keccak,
    `Qsag.LatticePreprocessingFull,
    `Qsag.MaliciousSecurity,
    `Qsag.McRefine,
    `Qsag.MirSpecBridge,
    `Qsag.MultiRoundFsQrom,
    `Qsag.PallasAndBlsMigration,
    `Qsag.ParallelSeededSpnSecurity,
    `Qsag.Poseidon2,
    `Qsag.Poseidon2AlgebraicAndRecursiveHem,
    `Qsag.PosixCrashWal,
    `Qsag.Preprocessing,
    `Qsag.RlweCyclotomicExtraction,
    `Qsag.RssSlhFullSecurity,
    `Qsag.SimdBinaryEquiv,
    `Qsag.SimulationSpine,
    `Qsag.SpecOracle,
    `Qsag.SpirvSimtGpuEquiv,
    `Qsag.SuccinctAggregationIop,
    `Qsag.SydTvTranslationValidation,
    `Qsag.ThresholdApproval,
    `Qsag.ThresholdMlDsaAndToprf,
    `Qsag.ThresholdMlDsaSecurity,
    `Qsag.ThresholdMpc,
    `Qsag.UcGames
  ]

  let privEnv := (← getEnv).setExporting false
  let importedNames := privEnv.header.moduleNames
  let directImports := privEnv.header.imports
  for infraMod in infrastructureModules do
    unless importedNames.contains infraMod do
      throwError "Infrastructure module missing from import closure: {infraMod}"
  for modName in auditedProofModules do
    unless importedNames.contains modName do
      throwError "Manifest proof module missing from import closure: {modName}"
    unless directImports.any (fun imp => imp.module == modName && imp.importAll) do
      throwError "Manifest proof module must be directly imported with `import all`: {modName}"
  for importedMod in importedNames do
    if importedMod.toString.startsWith "Qsag." then
      unless auditedProofModules.contains importedMod || infrastructureModules.contains importedMod do
        throwError "Transitive Qsag module missing from explicit audit manifest: {importedMod}"

  -- 3. Dynamic filesystem check: zero Qsag/*.lean modules on disk may escape the manifest.
  let qsagDir : System.FilePath :=
    if ← (System.FilePath.mk "Qsag").pathExists then System.FilePath.mk "Qsag"
    else System.FilePath.mk "lean/Qsag"
  unless ← qsagDir.pathExists do
    throwError "Cannot locate Qsag source directory for inventory check"
  let mut pending := [(qsagDir, `Qsag)]
  while !pending.isEmpty do
    let (dir, modulePrefix) := pending.head!
    pending := pending.tail!
    for entry in (← dir.readDir) do
      if ← entry.path.isDir then
        pending := (entry.path, modulePrefix.str entry.fileName) :: pending
      else if entry.path.extension == some "lean" then
        if let some stem := entry.path.fileStem then
          let diskMod := modulePrefix.str stem
          unless auditedProofModules.contains diskMod || infrastructureModules.contains diskMod do
            throwError "Unregistered Qsag source module missing from AuditAxioms: {diskMod}"

  let mut perModuleCounts : Array Nat := Array.replicate auditedProofModules.size 0
  let mut checked : Nat := 0
  let mut rejected : Nat := 0
  let mut examples : Array Name := #[]

  for (name, _) in privEnv.constants.toList do
    if let some idx := privEnv.getModuleIdxFor? name then
      let owner := importedNames[idx.toNat]!
      -- Select by owning module, including private and non-Qsag-namespaced declarations.
      if let some mPos := auditedProofModules.findIdx? (· == owner) then
        checked := checked + 1
        perModuleCounts := perModuleCounts.modify mPos (· + 1)
        let axioms ← withEnv privEnv <| Lean.collectAxioms name
        let forbidden := axioms.filter (!allow ·)
        if !forbidden.isEmpty then
          rejected := rejected + 1
          examples := examples.push name
          logInfo m!"REJECT {name} ({owner}): {forbidden}"

  -- Tactic implementation executes at compile time; its pure definitions and proofs
  -- remain subject to the same axiom policy as the library.
  let mut infrastructureChecked : Nat := 0
  let mut metaSkipped : Nat := 0
  for (name, _) in privEnv.constants.toList do
    if let some idx := privEnv.getModuleIdxFor? name then
      if infrastructureModules.contains importedNames[idx.toNat]! then
        if QsagAudit.isCompileTimeAssurance privEnv name then
          metaSkipped := metaSkipped + 1
        else
          infrastructureChecked := infrastructureChecked + 1
          let axioms ← withEnv privEnv <| Lean.collectAxioms name
          let forbidden := axioms.filter (!allow ·)
          if !forbidden.isEmpty then
            rejected := rejected + 1
            examples := examples.push name
            logInfo m!"REJECT {name}: {forbidden}"
  logInfo m!"Assurance infrastructure: {infrastructureChecked} pure declarations audited; {metaSkipped} compile-time declarations"

  if checked == 0 then
    throwError "No project declarations found; audit coverage is empty"

  for i in [:auditedProofModules.size] do
    if perModuleCounts[i]! == 0 then
      throwError "Manifest proof module contributed 0 audited declarations: {auditedProofModules[i]!}"

  logInfo m!"Axiom inventory: {checked} declarations across {auditedProofModules.size} proof modules (0 excluded), {rejected} rejected"
  if rejected > 0 then
    throwError "Axiom policy failed for {rejected} of {checked} declarations. Examples: {examples}"
