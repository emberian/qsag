module
public import Qsag.RssSigningTreeCache
public import Qsag.RssSigningChecks
import all Qsag.RssSigningTreeCache
import all Qsag.RssSigningBatches
import all Qsag.RssSigningChecks
import all Qsag.RssSigningEnrollment
import all Qsag.ThresholdMpc
import all Qsag.HashSigs
import Qsag.Tactic.AssuranceKit

/-! Full-width grouped subtree execution with actual participant cSHAKE and
public-only completion. No active-opening capability is inferred by this test. -/
public section
namespace Qsag.RssSigning.TreeChecks
set_option autoImplicit false
set_option maxRecDepth 4096

def hashCount : {height : Nat} → LeafTree UnverifiedBatch height → Nat
  | 0, .leaf batch => batch.computations.foldl (fun total computation => total + computation.evidence.length) 0
  | _ + 1, .node left right => hashCount left + hashCount right

def fullSubtreeCheck : IO Unit := do
  let profile := Checks.profile
  let enrollment := sharedEnrollment profile
  let digits := List.replicate 32 7 ++ List.replicate 32 8
  unless checkTargetSum profile.params.w profile.params.ell1 profile.params.targetSum digits do
    throw (IO.userError "fixture digits fail actual target-sum check")
  let plan := wotsTreePlan profile.params 0 0 1 digits
  let computed := produceTree (publicPrepared enrollment Checks.request) profile.material Checks.tape 100 plan
  let cache := completeWotsCache profile.params profile.material.pkSeed 0 0 1 digits (candidateTree computed)
  unless decide (computed.nextInvocation = 356 ∧ treeQueryCount plan = 256) do
    throw (IO.userError "subtree reused/skipped invocation coordinates")
  unless decide (cacheRoot profile.material.pkSeed 0 0 cache 0 = enrollment.key.pkRoot) do
    throw (IO.userError "publicly completed grouped subtree differs from enrolled root")
  for selected in List.range 4 do
    let expected := buildMerkleAuthPathKp cshake256Suite profile.material.pkSeed 0 0 .tree 0
      (mpcComputeWotsPk cshake256Suite profile.params (RssProduction.sharedOracle profile).toPqHashMpcOracles
        profile.material.pkSeed 0 0) profile.params.subtreeHeight 0 0 selected
    unless decide (cachePath profile.material.pkSeed 0 0 cache 0 selected = expected) do
      throw (IO.userError "cached public authentication path differs from actual shared specification")
  IO.println s!"Grouped full-width subtree:256 distinct invocations, {hashCount computed.batches} concrete cSHAKE calls retained; public completion matches enrolled root and all4 actual authentication paths"

#verify_constructive produceTree_correct actual_wots_cache_root_and_path
end Qsag.RssSigning.TreeChecks
