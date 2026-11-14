module
import Qsag
import all Qsag.AdvancedMpcAndCreds
import all Qsag.Aggregation
import all Qsag.BinaryTower
import all Qsag.CompiledRlibFixtures
import all Qsag.Constructive
import all Qsag.ConstantTimeIsa
import all Qsag.ElfBinaryVerify
import all Qsag.ElfFixtureSlices
import all Qsag.ElfFixtureVerify
import all Qsag.ElfInvCerts
import all Qsag.ElfParse
import all Qsag.Fips205
import all Qsag.Goldilocks
import all Qsag.HashSigs
import all Qsag.HypertreeEufCma
import all Qsag.IdealTsig
import all Qsag.Keccak
import all Qsag.MaliciousSecurity
import all Qsag.McRefine
import all Qsag.Apex
import all Qsag.Poseidon2
import all Qsag.Preprocessing
import all Qsag.ThresholdApproval
import all Qsag.ThresholdMpc
import all Qsag.UcGames
import all Qsag.SimulationSpine
import all Qsag.LatticePreprocessingFull
import all Qsag.CustodySuiteFull
import all Qsag.ThresholdMlDsaAndToprf
import all Qsag.InteractiveUcEngine
import all Qsag.RssSlhFullSecurity
import all Qsag.SuccinctAggregationIop
import all Qsag.MirSpecBridge
import Lean

open Lean Elab Command in
run_cmd do
  -- Negative control: the allowlist must reject a known transitive axiom root.
  let negative ← Lean.collectAxioms ``Classical.choice
  if (negative.filter fun ax => ax != ``propext && ax != ``Quot.sound).isEmpty then
    throwError "Axiom audit negative control unexpectedly passed"
  let env ← getEnv
  let mut checked : Nat := 0
  let mut rejected : Nat := 0
  let mut examples : Array Name := #[]
  let excluded := #[`Qsag.HashSigs, `Qsag.Fips205, `Qsag.HypertreeEufCma, `Qsag.Aggregation]
  let mut excludedCounts : Array Nat := #[0, 0, 0, 0]
  let mut inScope : Nat := 0
  for (name, _) in env.constants.toList do
    let spelling := name.toString
    if spelling.startsWith "Qsag." || spelling.startsWith "_private.Qsag." then
      checked := checked + 1
      let axioms ← Lean.collectAxioms name
      let forbidden := axioms.filter fun ax => ax != ``propext && ax != ``Quot.sound
      if !forbidden.isEmpty then
        rejected := rejected + 1
        let some idx := env.getModuleIdxFor? name
          | throwError "Missing owner for audited declaration {name}"
        let owner := env.header.moduleNames[idx.toNat]!
        if let some i := excluded.findIdx? (· == owner) then
          excludedCounts := excludedCounts.modify i (· + 1)
        else
          inScope := inScope + 1
        examples := examples.push name
        logInfo m!"REJECT {name}: {forbidden}"
  if checked == 0 then
    throwError "No project declarations found; audit coverage is empty"
  logInfo m!"Axiom inventory: {checked} declarations, {rejected} rejected"
  logInfo m!"In-scope rejected: {inScope}"
  for i in [:excluded.size] do
    logInfo m!"Excluded module {excluded[i]!}: {excludedCounts[i]!} rejected"
  if rejected > 0 then
    throwError "Axiom policy failed for {rejected} of {checked} declarations. Examples: {examples}"
