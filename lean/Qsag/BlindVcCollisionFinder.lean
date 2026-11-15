module

public import Qsag.BlindVcQromSecurity
import all Qsag.BlindVcQromSecurity
import all Qsag.ThresholdMlDsaAndToprf

/-!
Executable collision extraction from the finite BlindVC opening-table event.
The adversary below produces the table, not merely an existential collision. Its
random tape can have arbitrary finite weights. Extraction has no probability loss.
This does not construct three openings by rewinding a quantum adversary; the cost
and success probability of that upstream operation remain separate obligations.
-/
public section
namespace Qsag

/-- Both preimages are computational data; the certificate is erased at runtime. -/
abbrev VcHashCollision (H : List UInt8 → List UInt8) :=
  Σ m₁ : List UInt8, {m₂ : List UInt8 // m₁ ≠ m₂ ∧ H m₁ = H m₂}

/-- Select one of the three actual overlapping pairs, then descend through its
commitment and digest fold to return distinct byte strings with the same hash. -/
def vcRewoundCollisionFinder (H : List UInt8 → List UInt8)
    (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (nonce : Vec UInt8 32) (idx : Nat) (o0 o1 o2 : OpenedBlindVcRep) :
    Option (VcHashCollision H) :=
  if h01 : o0.viewE1 ≠ o1.viewE ∧
      vcCommitPartyView H nonce idx 1 o0.viewE1 (vcPartyFinalOutAt o1.finalOuts 1) =
      vcCommitPartyView H nonce idx 1 o1.viewE (vcPartyFinalOutAt o1.finalOuts 1) then
    some (vcCommitPartyViewCollision hHLen
      (fun he => h01.1 (congrArg Prod.fst he)) h01.2)
  else if h12 : o1.viewE1 ≠ o2.viewE ∧
      vcCommitPartyView H nonce idx 2 o1.viewE1 (vcPartyFinalOutAt o2.finalOuts 2) =
      vcCommitPartyView H nonce idx 2 o2.viewE (vcPartyFinalOutAt o2.finalOuts 2) then
    some (vcCommitPartyViewCollision hHLen
      (fun he => h12.1 (congrArg Prod.fst he)) h12.2)
  else if h20 : o2.viewE1 ≠ o0.viewE ∧
      vcCommitPartyView H nonce idx 0 o2.viewE1 (vcPartyFinalOutAt o0.finalOuts 0) =
      vcCommitPartyView H nonce idx 0 o0.viewE (vcPartyFinalOutAt o0.finalOuts 0) then
    some (vcCommitPartyViewCollision hHLen
      (fun he => h20.1 (congrArg Prod.fst he)) h20.2)
  else none

theorem vcRewoundCollisionFinder_isSome (H : List UInt8 → List UInt8)
    (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (nonce : Vec UInt8 32) (idx : Nat) (o0 o1 o2 : OpenedBlindVcRep) :
    (vcRewoundCollisionFinder H hHLen nonce idx o0 o1 o2).isSome =
      decide (VcRewoundCommitConflict H nonce idx o0 o1 o2) := by
  unfold vcRewoundCollisionFinder VcRewoundCommitConflict
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-- Scan the exact table indices used by `blindVcTableConflict`. -/
def blindVcCollisionScan {k : Nat} (H : List UInt8 → List UInt8)
    (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (stmt : BlindVcPublicStatement) (msg : BlindVcParallelMsg k) :
    List Nat → Option (VcHashCollision H)
  | [] => none
  | idx :: rest =>
    if hIdx : idx < k then
      let cand := (Vec.get msg.openTable ⟨idx, hIdx⟩).get
      match vcRewoundCollisionFinder H hHLen stmt.presNonce idx (cand 0) (cand 1) (cand 2) with
      | some pair => some pair
      | none => blindVcCollisionScan H hHLen stmt msg rest
    else blindVcCollisionScan H hHLen stmt msg rest

theorem blindVcCollisionScan_isSome {k : Nat} (H : List UInt8 → List UInt8)
    (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (stmt : BlindVcPublicStatement) (msg : BlindVcParallelMsg k) (indices : List Nat) :
    (blindVcCollisionScan H hHLen stmt msg indices).isSome =
      indices.any (fun idx => if hIdx : idx < k then
        let cand := (Vec.get msg.openTable ⟨idx, hIdx⟩).get
        decide (VcRewoundCommitConflict H stmt.presNonce idx (cand 0) (cand 1) (cand 2))
        else false) := by
  induction indices with
  | nil => rfl
  | cons idx rest ih =>
    simp only [blindVcCollisionScan, List.any_cons]
    split
    · rename_i hIdx
      have h := vcRewoundCollisionFinder_isSome H hHLen stmt.presNonce idx
        ((Vec.get msg.openTable ⟨idx, hIdx⟩).get 0)
        ((Vec.get msg.openTable ⟨idx, hIdx⟩).get 1)
        ((Vec.get msg.openTable ⟨idx, hIdx⟩).get 2)
      split <;> simp_all
    · rename_i hIdx
      simpa using ih

def blindVcTableCollisionFinder {k : Nat} (H : List UInt8 → List UInt8)
    (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (stmt : BlindVcPublicStatement) (msg : BlindVcParallelMsg k) :
    Option (VcHashCollision H) :=
  blindVcCollisionScan H hHLen stmt msg (List.range k)

theorem blindVcTableCollisionFinder_isSome {k : Nat} (H : List UInt8 → List UInt8)
    (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (stmt : BlindVcPublicStatement) (msg : BlindVcParallelMsg k) :
    (blindVcTableCollisionFinder H hHLen stmt msg).isSome = blindVcTableConflict H stmt msg :=
  blindVcCollisionScan_isSome H hHLen stmt msg (List.range k)

/-- A table-producing adversary may depend on the hash and its random tape. -/
def blindVcCollisionReduction {Seed : Type} {k : Nat}
    (adversary : (List UInt8 → List UInt8) → Seed →
      BlindVcPublicStatement × BlindVcParallelMsg k)
    (H : List UInt8 → List UInt8) (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (seed : Seed) : Option (VcHashCollision H) :=
  let out := adversary H seed
  blindVcTableCollisionFinder H hHLen out.1 out.2

/-- Exact weighted event reduction, hence no guessing loss for either the
repetition index or one of its three conflicting view pairs. Normalizing both
sides by the same total seed weight gives the probability equality. -/
theorem blindVcCollisionReduction_mass {Seed : Type} {k : Nat}
    (adversary : (List UInt8 → List UInt8) → Seed →
      BlindVcPublicStatement × BlindVcParallelMsg k)
    (H : List UInt8 → List UInt8) (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (seeds : List Seed) (weight : Seed → Nat) :
    (seeds.map (fun seed => if (blindVcCollisionReduction adversary H hHLen seed).isSome
      then weight seed else 0)).sum =
    (seeds.map (fun seed => if blindVcTableConflict H (adversary H seed).1
      (adversary H seed).2 then weight seed else 0)).sum := by
  simp only [blindVcCollisionReduction, blindVcTableCollisionFinder_isSome]

/-- The original acceptance game splits into a returned collision or the
existing filtered acceptance game, now with computational output on the bad arm. -/
theorem blindVc_fs_collisionFinder_decomposition {cardX k : Nat}
    (H : List UInt8 → List UInt8) (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmtAt : Fin cardX → BlindVcPublicStatement)
    (msgAt : Fin cardX → BlindVcParallelMsg k)
    (O : Fin cardX → BitVec (64 * k)) (x : Fin cardX)
    (hAccept : blindVcFsUnfilteredLiveAfter H prgExpand stmtAt msgAt O x = true) :
    (blindVcTableCollisionFinder H hHLen (stmtAt x) (msgAt x)).isSome = true ∨
    blindVcFsLiveAfter H prgExpand stmtAt msgAt O x = true := by
  rw [blindVcTableCollisionFinder_isSome]
  exact blindVc_fs_acceptance_decomposition H prgExpand stmtAt msgAt O x hAccept

/-- Weighted union bound for the actual unfiltered acceptance predicate. A
computational collision bound can now be applied to the executable bad arm;
its hash-query/runtime overhead still needs a separate resource analysis. -/
theorem blindVc_fs_collisionFinder_mass_bound {cardX k : Nat}
    (H : List UInt8 → List UInt8) (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (prgExpand : (D : Nat) → Nat → Fin 3 → Vec UInt8 32 → PartyGateCoins D)
    (stmtAt : Fin cardX → BlindVcPublicStatement)
    (msgAt : Fin cardX → BlindVcParallelMsg k)
    (O : Fin cardX → BitVec (64 * k)) (seeds : List (Fin cardX))
    (weight : Fin cardX → Nat) :
    (seeds.map (fun x => if blindVcFsUnfilteredLiveAfter H prgExpand stmtAt msgAt O x
      then weight x else 0)).sum ≤
    (seeds.map (fun x => if (blindVcTableCollisionFinder H hHLen (stmtAt x) (msgAt x)).isSome
      then weight x else 0)).sum +
    (seeds.map (fun x => if blindVcFsLiveAfter H prgExpand stmtAt msgAt O x
      then weight x else 0)).sum := by
  induction seeds with
  | nil => simp
  | cons x rest ih =>
    have hp := blindVc_fs_collisionFinder_decomposition H hHLen prgExpand stmtAt msgAt O x
    simp only [List.map_cons, List.sum_cons]
    cases ha : blindVcFsUnfilteredLiveAfter H prgExpand stmtAt msgAt O x <;>
      cases hc : (blindVcTableCollisionFinder H hHLen (stmtAt x) (msgAt x)).isSome <;>
      cases hf : blindVcFsLiveAfter H prgExpand stmtAt msgAt O x <;>
      simp_all <;> omega

/-- A consistent honest table produces no spurious collision. -/
theorem vcRewoundCollisionFinder_honest
    (H : List UInt8 → List UInt8) (hHLen : ∀ m, (H m).length < 256 ^ 8)
    (nonce : Vec UInt8 32) (idx : Nat) (tr : BlindVcRepTriple) :
    (vcRewoundCollisionFinder H hHLen nonce idx
      (openBlindVcRep H nonce idx tr 0) (openBlindVcRep H nonce idx tr 1)
      (openBlindVcRep H nonce idx tr 2)).isSome = false := by
  rw [vcRewoundCollisionFinder_isSome]
  simp only [vcRewoundCommitConflict_honest_table, decide_false]

/-- The concrete conflicting-view construction returns an actual collision. -/
theorem vcRewoundCollisionFinder_constant_hash
    (nonce : Vec UInt8 32) (idx : Nat) (o : OpenedBlindVcRep) :
    let bad := { o with
      viewE := { o.viewE with attrShares := [] }
      viewE1 := { o.viewE with attrShares := [Goldilocks.zero] } }
    (vcRewoundCollisionFinder (fun _ => []) (by intro _; decide)
      nonce idx bad bad bad).isSome = true := by
  intro bad
  rw [vcRewoundCollisionFinder_isSome]
  exact decide_eq_true (vcRewoundCommitConflict_constant_hash nonce idx o)

#verify_constructive foldFramesHash_collision_of_ne vcCommitPartyView_binding
  vcRewoundCollisionFinder_isSome blindVcCollisionScan_isSome
  blindVcTableCollisionFinder_isSome blindVcCollisionReduction_mass
  blindVc_fs_collisionFinder_decomposition blindVc_fs_collisionFinder_mass_bound
  vcRewoundCollisionFinder_honest vcRewoundCollisionFinder_constant_hash

end Qsag
