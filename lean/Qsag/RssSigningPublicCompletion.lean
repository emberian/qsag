module
public import Qsag.RssSigningBackend
public import Qsag.RssSigningEnrollment
import all Qsag.RssSigningBackend
import all Qsag.RssSigningEnrollment
import all Qsag.RssProductionProfile
import all Qsag.ThresholdMpc
import all Qsag.HashSigs
import Qsag.Tactic.AssuranceKit

/-!
Public completion of selected WOTS values, as used by the Rust RSS subtree cut.
Once selected signature values are available, their endpoints and selected leaf
key require no further secret oracle calls. This is the arithmetic cache-elision
connection; whole grouped-cut scheduling/abort equivalence remains separate.
-/
public section
namespace Qsag.RssSigning
set_option autoImplicit false

def selectedValues (profile : RssProduction.Profile) (layer : UInt32) (tree : UInt64)
    (kp : Nat) (digits : List Nat) : List Bytes :=
  (List.range profile.params.ell1).map fun r =>
    (RssProduction.sharedOracle profile).evalWotsChainEnd layer tree kp r (digits.getD r 0)

/-- This function receives already disclosed values only and has no secret
material or oracle callback in its input. -/
def completeSelectedLeaf (params : PqHashParams) (pkSeed : Bytes) (layer : UInt32)
    (tree : UInt64) (kp : Nat) (digits : List Nat) (values : List Bytes) : Bytes :=
  recoverWotsPkFromSig cshake256Suite params pkSeed layer tree kp digits values

theorem selectedLeaf_from_actual_cut (profile : RssProduction.Profile)
    (layer : UInt32) (tree : UInt64) (kp : Nat) (digits : List Nat)
    (hCheck : checkTargetSum profile.params.w profile.params.ell1 profile.params.targetSum digits = true) :
    completeSelectedLeaf profile.params profile.material.pkSeed layer tree kp digits
      (selectedValues profile layer tree kp digits) =
      mpcComputeWotsPk cshake256Suite profile.params (RssProduction.sharedOracle profile).toPqHashMpcOracles
        profile.material.pkSeed layer tree kp := by
  have hm := (RssProduction.sharedOracle_matches profile).1
  unfold completeSelectedLeaf selectedValues
  simp only [hm.2.1]
  have h := recoverWotsPkFromSig_eq_computeWotsPk cshake256Suite profile.params
    (RssProduction.referenceKey profile) layer tree kp digits hCheck
  dsimp only [RssProduction.referenceKey] at h ⊢
  rw [h]
  exact (mpcComputeWotsPk_eq cshake256Suite profile.params
    (RssProduction.sharedOracle profile).toPqHashMpcOracles (RssProduction.referenceKey profile)
    hm layer tree kp).symm

/-- The digit check needed for public completion is obtained from the actual
public grinding branch, rather than asserted by a successful-signature premise. -/
theorem selectedLeaf_after_grind (profile : RssProduction.Profile)
    (rRand currentRoot : Bytes) (layerIndex : Nat) (tree : UInt64) (kp counter : Nat)
    (digits : List Nat) (digest : Bytes)
    (hGrind :
      (if profile.params.statefulJorts && decide (layerIndex = 0) then
        grindTswLeafCounterAux cshake256Suite profile.params.w profile.params.ell1 profile.params.targetSum
          rRand profile.material.pkSeed (RssProduction.enrolledKey profile).pkRoot currentRoot
          tree (UInt32.ofNat kp) 0 profile.grindLimit
      else
        grindTswInternalCounterAux cshake256Suite profile.params.w profile.params.ell1 profile.params.targetSum
          profile.material.pkSeed (RssProduction.enrolledKey profile).pkRoot currentRoot
          (UInt32.ofNat layerIndex) tree (UInt32.ofNat kp) 0 profile.grindLimit) =
      some (counter, digits, digest)) :
    completeSelectedLeaf profile.params profile.material.pkSeed (UInt32.ofNat layerIndex) tree kp digits
      (selectedValues profile (UInt32.ofNat layerIndex) tree kp digits) =
      mpcComputeWotsPk cshake256Suite profile.params (RssProduction.sharedOracle profile).toPqHashMpcOracles
        profile.material.pkSeed (UInt32.ofNat layerIndex) tree kp := by
  apply selectedLeaf_from_actual_cut
  split at hGrind
  · exact (grindTswLeafCounterAux_sound hGrind).2.2.2
  · exact (grindTswInternalCounterAux_sound hGrind).2.2.2

#verify_constructive selectedLeaf_from_actual_cut selectedLeaf_after_grind
end Qsag.RssSigning
