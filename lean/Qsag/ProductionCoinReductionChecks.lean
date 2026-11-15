module
import Qsag.ProductionCoinReduction
import all Qsag.ProductionCoinReduction
import all Qsag.RssSlhFullSecurity

open Qsag Qsag.ProductionCoinReduction

private def ctx : ProductionCoinContext := ⟨17, [0x61, 0x62], 29⟩
private def honest : List Entry := [⟨0, 37, 37⟩, ⟨1, 53, 53⟩, ⟨2, 71, 71⟩]

/- Executes the actual cSHAKE helper and negative mutants; no proof by evaluation. -/
#eval do
  let out := run concrete ctx honest
  unless out == some (productionCoinDerive ctx (37 ^^^ 53 ^^^ 71)) do
    throw (IO.userError "honest production coin release failed")
  unless out.map List.length == some 32 do
    throw (IO.userError "coin output width failed")
  unless (run concrete ctx [⟨0, 37, 38⟩, ⟨1, 53, 53⟩]) == none do
    throw (IO.userError "changed opening not rejected")
  unless run concrete ctx [⟨0, 37, 37⟩, ⟨1, 37, 37⟩] == some (productionCoinDerive ctx 0) do
    throw (IO.userError "reused share cancellation fixture failed")
  let changed := { ctx with transcriptDigest := 30 }
  if run concrete ctx honest == run concrete changed honest then
    throw (IO.userError "changed-context outputs unexpectedly agree")
  unless concrete (misboundDeriveQuery ctx 37) == concrete (misboundDeriveQuery changed 37) do
    throw (IO.userError "misbound context mutant did not replay")
  IO.println "production coin: honest 32-byte release; bad opening rejected; reused-share cancellation; context binding and misbound replay checked"

#print axioms helper_reduces_to_primitive
#print axioms helper_hybrid_bound
#print axioms honest_concrete
#print axioms reused_share_cancels
#print axioms changed_context_collision
#print axioms helper_abort_or_original
#print axioms independent_auxiliary_reduction
#print axioms eval_program
#print axioms program_bound
