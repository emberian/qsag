module

public import Qsag.PosixCrashWal
public import Qsag.HashSigs
import all Qsag.HashSigs
import Qsag.Tactic.AssuranceKit

public section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace Qsag.SpecOracle

/-- Executable configuration predicate for the production global-liveness profile. -/
def quorumAccepts (t n f q : Nat) : Bool :=
  decide (0 < t ∧ t ≤ n ∧ n ≤ 255 ∧ 0 < q ∧ q ≤ n ∧ f < t ∧ t ≤ q ∧
    3 * f + 1 ≤ n ∧ n + f < 2 * q ∧ q ≤ n - f)

/-- Generic WOTS+C profile, including the unused zero suffix and exact digest width. -/
def wotsGenericAccepts (digest : List UInt8) : Bool :=
  match extractBaseWDigitsChecked 4 128 digest with
  | none => false
  | some digits => (digits.drop 127).all (· == 0) &&
      checkTargetSum 4 127 192 (digits.take 127)

/-- Deterministic fixture with real authenticated snapshot serialization and decoding.
Damage 1 truncates, 2 flips the final MAC byte, and 3 removes the slot. -/
def ledgerRecovery (damageA damageB checkpoint : Nat) : Option Nat := Id.run do
  let domain := "QSAG.FIRST.SIGNED".toUTF8.toList
  let key := List.replicate 32 (7 : UInt8)
  let genesisSeal :=  List.replicate 8 (1 : UInt8)
  let ledgerId := List.replicate 32 (2 : UInt8)
  let sealA := List.replicate 8 (3 : UInt8)
  let sealB := List.replicate 8 (4 : UInt8)
  let snapshot := fun generation =>
    let body := RustDurability.ledgerSnapshotBody generation []
    body ++ RustDurability.ledgerTag domain key genesisSeal ledgerId
      "snapshot".toUTF8.toList body
  let damage := fun kind (bytes : List UInt8) => match kind with
    | 0 => some bytes
    | 1 => some (bytes.take (bytes.length / 2))
    | 2 => some (bytes.take (bytes.length - 1) ++ [bytes.getLast! ^^^ 1])
    | _ => none
  let anchor : ExternalMonotoneAnchor :=
    ⟨checkpoint, (snapshot (min checkpoint 2)).drop 16⟩
  let genesis := RustDurability.ledgerGenesisBytes domain key genesisSeal ledgerId sealA sealB
  return (RustDurability.recoverLedgerBytes domain key genesisSeal ledgerId sealA sealB genesis
    anchor (damage damageA (snapshot 2)) (damage damageB (snapshot 1))).map (·.generation)

theorem quorum_privacy (t n f q : Nat) (h : quorumAccepts t n f q = true) : f < t := by
  simp only [quorumAccepts, decide_eq_true_eq] at h
  exact h.2.2.2.2.2.1

theorem generic_zero_digest_rejected :
    wotsGenericAccepts (List.replicate 32 0) = false := by decide

/-- Production-profile digit guard used by differential WOTS vectors. -/
def wots128Accepts (digest : List UInt8) : Bool :=
  checkTargetSum 4 128 192 (extractBaseWDigits 4 128 digest)

/-- Removing the constant-sum guard accepts the all-zero digest. -/
theorem tooth_zero_digest_rejected :
    wots128Accepts (List.replicate 32 0) = false := by decide

/-- Exact WOTS128 digest acceptance, including its wire size. -/
def ValidWots128Digest (digest : List UInt8) : Prop :=
  digest.length = 32 ∧ wots128Accepts digest = true

theorem accepted_digest_has_target_sum (digest : List UInt8)
    (h : ValidWots128Digest digest) :
    sumDigits (extractBaseWDigits 4 128 digest) = 192 := by
  have ha := h.2
  simp only [wots128Accepts, checkTargetSum, Bool.and_eq_true, decide_eq_true_eq] at ha
  exact ha.2

theorem witness_valid_digest : ∃ digest, ValidWots128Digest digest := by
  refine ⟨List.replicate 32 0x66, ?_⟩
  unfold ValidWots128Digest
  decide

theorem tooth_zero_digest_invalid : ¬ ValidWots128Digest (List.replicate 32 0) := by
  intro h
  have hx := h.2
  rw [tooth_zero_digest_rejected] at hx
  cases hx

end Qsag.SpecOracle

#tooth_pair Qsag.SpecOracle.accepted_digest_has_target_sum vs Qsag.SpecOracle.tooth_zero_digest_invalid
#verify_inhabited Qsag.SpecOracle.accepted_digest_has_target_sum Qsag.SpecOracle.witness_valid_digest

