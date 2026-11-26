module
public import Qsag.Custody.DistributedAuthRun
public import Qsag.Top.CertCustodyAdaptiveBound
import Qsag.Tactic.Prelude

public section
attribute [-instance] Fin.instLinearOrderPackage
namespace Qsag.DistributedAuthRun
open Spec KeyHidingCustody DistCustody

section Probability
variable {F C PK D Sig : Type} [LawfulField F] [DecidableEq F] [DecidableEq C] [DecidableEq D]
variable (dep : AuthDeployment F C PK D Sig) {id : DeploymentId} {decode : Decoder dep}
variable (G : LinkGame N dep.core.quorum.numParties)
variable (client : Fin N → Client dep id decode (AuthState.init dep) b)

theorem distributed_authRun_adaptive_unsafe_release_bound
    (wf : dep.WellFormed) {classify keyLen inLen outLen εPrf εDigest εWal}
    (indep : G.Independent (fun ω => network dep (client ω)))
    (hard : G.Hard (fun ω => network dep (client ω)) keyLen inLen outLen εPrf εDigest classify)
    (wal : GameBound (walCollisionGame dep G client).winProb εWal) :
    GameBound (unsafeGame dep G client).winProb
      ((((εPrf.add (tagGuessBound outLen)).add εDigest).scale
        (dep.core.quorum.numParties * b)).add εWal) := by
  let A := fun ω => network dep (client ω)
  let split := CoinSplit.prod dep.core.quorum.numParties b
  let breaks := fun j => G.forgeGame A (split.chal j) (split.advc j)
  let anyBreak : FinGame N := ⟨G.positive, fun ω =>
    (List.finRange (dep.core.quorum.numParties * b)).any (fun j => (breaks j).win ω)⟩
  apply GameBound.trans (event_le_two_reductions _ anyBreak (walCollisionGame dep G client) ?_)
  · exact Spec.RatBound.add_le_add (event_le_family_reductions anyBreak breaks
      (fun _ h => by obtain ⟨j,_,hj⟩ := List.any_eq_true.mp h; exact ⟨j,hj⟩)
      (fun j => G.forgery_bound A hard (split.chal j) (split.advc j))) wal
  · intro ω win
    rcases G.extract A indep ω with eq | ⟨r,s,hit⟩
    · right
      change schedule dep G client false ω = schedule dep G client true ω at eq
      change authUnsafeRelease dep (authRun dep _ _ (schedule dep G client false ω)).1 = true at win
      rw [eq] at win
      have violation := authRun_unsafe_release_violation dep wf _ win
      change clash _ (walExtract dep _ _) = true
      rw [walExtract_correct]
      cases he : (authRun dep (diskBad dep) (AuthState.init dep) (schedule dep G client true ω)).2 with
      | true => rfl
      | false =>
        have clean := table_run_clean dep wf (client ω) (G.functions ω) []
          (fun _ => by simp only [anchored, AuthState.init.public_eqs]) (fun _ _ _ h => nomatch h) he
        exact Bool.noConfusion (violation.symm.trans clean)
    · left
      apply List.any_eq_true.mpr
      exact ⟨split.pair r s, List.mem_finRange _, by
        simpa only [breaks, split.chal_pair, split.advc_pair] using hit⟩

end Probability
#verify_constructive table_run_clean LinkGame.extract distributed_authRun_adaptive_unsafe_release_bound
#print axioms approve_seal_deliver
#print axioms ingress_foreign_refused
#print axioms table_run_clean
#print axioms LinkGame.extract
#print axioms LinkGame.forgery_bound
#print axioms network
#print axioms LinkGame.frame_collision_witness
#print axioms distributed_authRun_adaptive_unsafe_release_bound
#print axioms foreign_replay_rejected
#print axioms relabel_requires_collision
#print axioms walExtract_correct
end Qsag.DistributedAuthRun
