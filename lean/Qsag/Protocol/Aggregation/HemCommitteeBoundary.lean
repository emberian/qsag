module
/- Merge-tree quorum reduction at an arbitrary tree depth. `Composed.selected_leaf` and
`Composed.merged_quorum_reduction` fix the depth argument of `checkTree` at `16`; the two theorems
here take it as a parameter. The HEM-to-committee bridges that produce the `ExtractionBoundary`
premise (`boundary_of_committee_trace`, `boundary_of_hem_opening_batch`) are not defined here. -/
public import Qsag.Protocol.Aggregation.ComposedQsAgAndMergeSecurity
import Qsag.Tactic.AssuranceKit
public section
namespace Qsag.CompositionInstances
open Qsag.Composed
set_option autoImplicit false

/-- An accepted root bit selects an accepted leaf under exactly the root statement, for a tree
checked at any depth bound. -/
theorem selected_leaf_at_depth {n : Nat} (depth : Nat) (root : Header) (verify : Shard n → Bool)
    (tree : MergeTree n) (v : Nat) (h : checkTree root verify depth tree = true)
    (active : tree.bitmap.getLsbD v = true) :
    ∃ s ∈ tree.leaves, s.bitmap.getLsbD v = true ∧ s.header = root ∧ verify s = true := by
  have hs := binary_merge_sound root verify tree depth h
  have hc := hs.2.1 v
  simp only [active, ite_true] at hc
  have hp : 0 < tree.leaves.countP (fun s => s.bitmap.getLsbD v) := by omega
  obtain ⟨s, hm, hb⟩ := List.countP_pos_iff.mp hp
  exact ⟨s, hm, hb, (hs.2.2.1 s hm).1, (hs.2.2.1 s hm).2.1⟩

/-- Depth-parametric form of `Composed.merged_quorum_reduction`: an active validator of a tree
accepted at depth bound `depth` yields a bad leaf, a quorum forgery, or quorum participation. -/
theorem merged_quorum_reduction_at_depth {n : Nat} (depth : Nat) (geom : AggSigGeometry)
    (custody : Fin n → Custody) (verify : Shard n → Bool) (bad : Shard n → Prop)
    (boundary : ExtractionBoundary geom custody verify bad) (root : Header)
    (tree : MergeTree n) (h : checkTree root verify depth tree = true) (v : Fin n)
    (active : tree.bitmap.getLsbD v.val = true) :
    (∃ s ∈ tree.leaves, bad s) ∨
    QuorumForgery geom (custody v) (root.mode.message v.val) ∨
    quorumParticipated (custody v) (root.mode.message v.val) = true := by
  obtain ⟨s, hs, hv, hh, ha⟩ := selected_leaf_at_depth depth root verify tree v.val h active
  rcases boundary.extract s ha with hb | hex
  · exact .inl ⟨s, hs, hb⟩
  · obtain ⟨sig, hsig⟩ := hex v hv
    rw [hh] at hsig
    cases hq : quorumParticipated (custody v) (root.mode.message v.val) with
    | false => exact .inr (.inl ((quorumForgery_iff _ _ _).mpr ⟨sig, hsig, hq⟩))
    | true => exact .inr (.inr rfl)

#verify_constructive selected_leaf_at_depth merged_quorum_reduction_at_depth
end Qsag.CompositionInstances
end
