module
/-
# Qsag.Protocol.Credentials.ToprfMachine — SPDZ TOPRF State Machine, Quintic `GF(p^5)` Algebra & Concrete `CredentialImplementation` Core

Protocol-layer state machine and algebraic soundness foundation for:
1. **`crates/qsag-cred/src/voprf_spdz.rs` (`2 ≤ t ≤ n ≤ 64` SPDZ TOPRF & `SpdzReservoir`)**:
   * Exact protocol constants (`MAX_SPDZ_SERVERS = 64`, `SBOXES_PER_ITEM = 118`,
     `MASKS_PER_ITEM = 16`, `TOPRF_LANES = 4`, `POW7_CHUNK = 4`, `BEAVER_CHUNK = 32`,
     domain `"QSAG.TOPRF.SPDZ.PREPROCESS.V2"`).
   * Committee threshold geometry (`SpdzConfig`, adaptive corruption `< threshold` leaving at least
     one honest server in every online quorum of size `≥ threshold`), `GoldilocksExt2` SPDZ MAC
     soundness (`Δval ≠ 0` leaves at most one `α ∈ GF(p^2)` accepting).
   * Two-pass `spdzReserveCounters` (`reserve_counters` at `voprf_spdz.rs:1538-1583`): pre-validates
     all quorum servers before mutating `stores[0]`, and unconditionally ratchets every server's
     in-memory `lastCounter` while burning prefix durable stores on partial I/O failure without
     ever recycling counters (`partial_reserve_burns_without_recycle`).
   * Monotone cursor `ToprfReservoir`, `ToprfRefusal` (`request` spends one session reservation only;
     `quorum` poisons and wipes the entire reservoir), and the three MAC-checked online evaluation
     phases (`"toprf_spdz_input_bind"`, `"toprf_spdz_circuit"`, `"toprf_spdz_output"`).
   * Concrete reactive protocol machines (`piToprfCredMachine`, `piToprfCredLockstepMachine`,
     `piToprfCredService`) combining SPDZ TOPRF evaluation with `PiBlindVc` issuance and
     selective-disclosure presentation, together with genuine non-identity forward simulations
     (`Spec.DataRefines` and `Spec.Refines`) to `Spec.idealCredMachine cfg`.
2. **`crates/qsag-cred/src/blind_vc.rs` (`GF(p^5) = GF(p)[T]/(T^5 - 3)` & `192 × 192` Limbo Kernel)**:
   * Constructive irreducibility of `T^5 - 3` over `Goldilocks` (`3^((p-1)/5) mod p ≠ 1` excludes
     degree-1 roots, and the exact integer Bézout identity
     `b^5 - 9 = (a^3 b - 2 a b^2 + 3) r_0 + (b^3 - a^2 b^2) r_1` forces `(b^3 · 3^{-1})^5 = 3`
     on any monic quadratic divisor `T^2 + a T + b`, excluding degree-2 factors) plus `UPoly.xgcd`
     inversion, establishing `LawfulField BlindVcFp5` and `NoZeroDivisors BlindVcFp5` isomorphic to
     `CredentialFp5`.
   * Symbolic canonical enumerations `allBlindVcFp5` (`|GF(p^5)| = p^5`) and `nonzeroBlindVcFp5`
     (`|GF(p^5)^×| = p^5 - 1 = fp5NonzeroCount`) with proved `Nodup` and cardinality.
   * Concrete `192 × 192` (`SD_GRID_B = 192`, `SD_GRID_L = 192`, `dG = 36864`, `dR = 384`)
     `blindVcRepetitionKernel : CutAndChoose.DefectChecker ...` with proved
     `blindVcRepetitionKernel_algebraicSound` and 33-repetition opening defect extraction
     `blindVcOpeningDoomed_has_33_defects`.
-/

public import Qsag.Spec.Primitives
public import Qsag.Spec.Parameters
public import Qsag.Spec.Refines
public import Qsag.Spec.GameBound
public import Qsag.Spec.Assumptions
public import Qsag.Spec.IdealCred
public import Qsag.Math.Goldilocks
public import Qsag.Math.CoeffPoly
public import Qsag.Math.PolyRing
public import Qsag.Math.EllipticCurves
public import Qsag.Protocol.Credentials.AdvancedMpcAndCreds
public import Qsag.Protocol.Credentials.RepetitionCutAndChoose
public import Qsag.Protocol.Credentials.BlindVcQromSecurity
import Qsag.Tactic.AssuranceKit

public section
-- Avoid choice-based LawfulBEq on Fin
attribute [-instance] Fin.instLinearOrderPackage

namespace Qsag

set_option autoImplicit false
set_option exponentiation.threshold 512

/-! ## 1. `voprf_spdz.rs` Constants, Committee Shape, Quorum Honesty & `GoldilocksExt2` MAC Soundness -/

/-- Maximum SPDZ TOPRF committee size (`voprf_spdz.rs:100`). -/
@[expose] def MAX_SPDZ_SERVERS : Nat := 64

/-- Width-12 Poseidon2 S-boxes per TOPRF item: `2 * 4 * 12 + 22 = 118` (`voprf_spdz.rs:102`). -/
@[expose] def SBOXES_PER_ITEM : Nat := 118

/-- Client mask Beaver triples per TOPRF item: `4` input + `4` output limbs × `2` copies (`voprf_spdz.rs:104`). -/
@[expose] def MASKS_PER_ITEM : Nat := 16

/-- Key and output Goldilocks lanes per TOPRF evaluation (`voprf_spdz.rs:105`). -/
@[expose] def TOPRF_LANES : Nat := 4

/-- SIMD power-7 tuple preprocessing chunk width (`POW7_CHUNK = 4`). -/
@[expose] def POW7_CHUNK : Nat := 4

/-- Linear authenticated preprocessing flight size (`BLOCK = 32`, `voprf_spdz.rs:59, 1365`). -/
@[expose] def BEAVER_CHUNK : Nat := 32

/-- `u64::MAX` counter ceiling excluded by `admit_counter` (`voprf.rs:313`, `voprf_spdz.rs:320`). -/
def TOPRF_COUNTER_MAX : Nat := 18446744073709551615

/-- Preprocessing domain tag `"QSAG.TOPRF.SPDZ.PREPROCESS.V2"` (`voprf_spdz.rs:1282`, 29 ASCII bytes). -/
def spdzPreprocessDomainV2 : Spec.Bytes :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x54, 0x4F, 0x50, 0x52, 0x46, 0x2E,
   0x53, 0x50, 0x44, 0x5A, 0x2E, 0x50, 0x52, 0x45, 0x50, 0x52, 0x4F,
   0x43, 0x45, 0x53, 0x53, 0x2E, 0x56, 0x32]

/-- Phase-1 dual-mask input-binding MAC check label `"toprf_spdz_input_bind"` (`voprf_spdz.rs:1135`). -/
def spdzPhaseInputBindTag : Spec.Bytes :=
  [0x74, 0x6F, 0x70, 0x72, 0x66, 0x5F, 0x73, 0x70, 0x64, 0x7A, 0x5F,
   0x69, 0x6E, 0x70, 0x75, 0x74, 0x5F, 0x62, 0x69, 0x6E, 0x64]

/-- Phase-2 batched 118-S-box Poseidon2 circuit MAC check label `"toprf_spdz_circuit"` (`voprf_spdz.rs:1167`). -/
def spdzPhaseCircuitTag : Spec.Bytes :=
  [0x74, 0x6F, 0x70, 0x72, 0x66, 0x5F, 0x73, 0x70, 0x64, 0x7A, 0x5F,
   0x63, 0x69, 0x72, 0x63, 0x75, 0x69, 0x74]

/-- Phase-3 dual-masked output MAC check label `"toprf_spdz_output"` (`voprf_spdz.rs:1188`). -/
def spdzPhaseOutputTag : Spec.Bytes :=
  [0x74, 0x6F, 0x70, 0x72, 0x66, 0x5F, 0x73, 0x70, 0x64, 0x7A, 0x5F,
   0x6F, 0x75, 0x74, 0x70, 0x75, 0x74]

theorem spdz_constants_exact :
    MAX_SPDZ_SERVERS = 64 ∧
    SBOXES_PER_ITEM = 2 * 4 * 12 + 22 ∧
    SBOXES_PER_ITEM = 29 * POW7_CHUNK + 2 ∧
    MASKS_PER_ITEM = 2 * 2 * TOPRF_LANES ∧
    BEAVER_CHUNK = 8 * POW7_CHUNK ∧
    spdzPreprocessDomainV2.length = 29 := by
  decide

/-- SPDZ TOPRF committee configuration (`2 ≤ threshold ≤ servers ≤ 64`, `voprf_spdz.rs:120-136`). -/
structure SpdzConfig where
  threshold : Nat
  servers : Nat
  deriving DecidableEq, Repr

/-- Admissibility check of `SpdzConfig::new` (`voprf_spdz.rs:125-130`). -/
@[expose] def SpdzConfig.Valid (cfg : SpdzConfig) : Bool :=
  decide (2 ≤ cfg.threshold) &&
  decide (cfg.threshold ≤ cfg.servers) &&
  decide (cfg.servers ≤ MAX_SPDZ_SERVERS)

def SpdzConfig.new (threshold servers : Nat) : Option SpdzConfig :=
  let cfg : SpdzConfig := ⟨threshold, servers⟩
  if cfg.Valid then some cfg else none

theorem SpdzConfig.new_isSome_iff (t n : Nat) :
    (SpdzConfig.new t n).isSome = true ↔ (2 ≤ t ∧ t ≤ n ∧ n ≤ MAX_SPDZ_SERVERS) := by
  unfold SpdzConfig.new SpdzConfig.Valid
  dsimp only
  by_cases h : 2 ≤ t ∧ t ≤ n ∧ n ≤ MAX_SPDZ_SERVERS
  · rcases h with ⟨h1, h2, h3⟩
    simp [h1, h2, h3]
  · constructor
    · intro hSome
      split at hSome
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact False.elim (h ⟨hc.1.1, hc.1.2, hc.2⟩)
      · cases hSome
    · intro hc
      exact False.elim (h hc)

private theorem countP_lt_length_exists_false {α : Type} (p : α → Bool) :
    ∀ (xs : List α), xs.countP p < xs.length → ∃ x ∈ xs, p x = false
  | [], h => absurd h (Nat.lt_irrefl 0)
  | x :: xs, h => by
    rw [List.countP_cons, List.length_cons] at h
    cases hp : p x with
    | false => exact ⟨x, .head _, hp⟩
    | true =>
      simp only [hp, ↓reduceIte] at h
      obtain ⟨y, hy, hpy⟩ := countP_lt_length_exists_false p xs (by omega)
      exact ⟨y, .tail _ hy, hpy⟩

private theorem nodup_countP_le_of_imp {α : Type} [DecidableEq α]
    (p : α → Bool) :
    ∀ (xs ys : List α), xs.Nodup → (∀ x ∈ xs, p x = true → x ∈ ys) →
      xs.countP p ≤ ys.countP p
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, ys, .cons hNotMem hNd, hSub => by
    rw [List.countP_cons]
    cases hp : p x with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact nodup_countP_le_of_imp p xs ys hNd (fun z hz hpz => hSub z (.tail _ hz) hpz)
    | true =>
      simp only [↓reduceIte]
      have hxInYs : x ∈ ys := hSub x (.head _) hp
      obtain ⟨ys₁, ys₂, rfl⟩ := List.append_of_mem hxInYs
      have hRestSub : ∀ z ∈ xs, p z = true → z ∈ ys₁ ++ ys₂ := by
        intro z hz hpz
        have hzIn := hSub z (.tail _ hz) hpz
        rcases List.mem_append.mp hzIn with hL | hR
        · exact List.mem_append_left _ hL
        · rcases List.mem_cons.mp hR with rfl | hR'
          · exact False.elim (hNotMem z hz rfl)
          · exact List.mem_append_right _ hR'
      have ih := nodup_countP_le_of_imp p xs (ys₁ ++ ys₂) hNd hRestSub
      simp only [List.countP_append, List.countP_cons, hp, ↓reduceIte]
      rw [List.countP_append] at ih
      omega

/-- **Adaptive Corruption `< threshold` Leaves an Honest Server in Every Quorum
    (`spdz_quorum_contains_honest_server`)**:
    For any valid `SpdzConfig` (`2 ≤ t ≤ n ≤ 64`), any duplicate-free quorum `quorum` of `≥ t`
    committee servers (`∀ i ∈ quorum, i < n`), and any adaptive corruption set `corruptServers`
    corrupting strictly fewer than `t` committee members, at least one server in `quorum` is
    uncorrupted (`i ∉ corruptServers`). -/
theorem spdz_quorum_contains_honest_server
    (cfg : SpdzConfig) (hValid : cfg.Valid = true)
    (quorum corruptServers : List Nat)
    (hNd : quorum.Nodup)
    (hBounds : ∀ i ∈ quorum, i < cfg.servers)
    (hQuorum : cfg.threshold ≤ quorum.length)
    (hCorruptLt : (List.range cfg.servers).countP (fun i => decide (i ∈ corruptServers)) < cfg.threshold) :
    2 ≤ quorum.length ∧ ∃ i ∈ quorum, i ∉ corruptServers := by
  have hCfg : (2 ≤ cfg.threshold ∧ cfg.threshold ≤ cfg.servers) ∧ cfg.servers ≤ MAX_SPDZ_SERVERS := by
    unfold SpdzConfig.Valid at hValid
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using hValid
  have hSub : quorum.countP (fun i => decide (i ∈ corruptServers)) ≤
      (List.range cfg.servers).countP (fun i => decide (i ∈ corruptServers)) :=
    nodup_countP_le_of_imp (fun i => decide (i ∈ corruptServers)) quorum (List.range cfg.servers) hNd
      (fun i hi _ => List.mem_range.mpr (hBounds i hi))
  have hLtLen : quorum.countP (fun i => decide (i ∈ corruptServers)) < quorum.length :=
    Nat.lt_of_le_of_lt hSub (Nat.lt_of_lt_of_le hCorruptLt hQuorum)
  obtain ⟨i, hi, hFalse⟩ := countP_lt_length_exists_false _ quorum hLtLen
  exact ⟨Nat.le_trans hCfg.1.1 hQuorum, i, hi, of_decide_eq_false hFalse⟩

/-- Authenticated SPDZ wire share `(val ∈ GF(p), mac ∈ GF(p^2))` (`Wire` in `voprf_spdz.rs:186-220`). -/
structure SpdzWire where
  val : Goldilocks
  mac : GoldilocksExt2
  deriving DecidableEq, Repr

def SpdzWire.zero : SpdzWire := ⟨Goldilocks.zero, GoldilocksExt2.zero⟩

def SpdzWire.publicConst (v : Goldilocks) (alpha : GoldilocksExt2) : SpdzWire :=
  ⟨v, CommRingOps.mul alpha (GoldilocksExt2.ofBase v)⟩

def SpdzWire.add (a b : SpdzWire) : SpdzWire :=
  ⟨CommRingOps.add a.val b.val, CommRingOps.add a.mac b.mac⟩

def SpdzWire.sub (a b : SpdzWire) : SpdzWire :=
  ⟨CommRingOps.sub a.val b.val, CommRingOps.sub a.mac b.mac⟩

def SpdzWire.scale (a : SpdzWire) (k : Goldilocks) : SpdzWire :=
  ⟨CommRingOps.mul a.val k, CommRingOps.mul a.mac (GoldilocksExt2.ofBase k)⟩

/-- SPDZ MAC verification equation on an opened wire: `openedMac = alpha * ofBase(openedVal)`. -/
def spdzMacCheckAccepts (alpha : GoldilocksExt2) (openedVal : Goldilocks)
    (openedMac : GoldilocksExt2) : Bool :=
  decide (openedMac = CommRingOps.mul alpha (GoldilocksExt2.ofBase openedVal))

/-- **SPDZ `GoldilocksExt2` MAC Soundness (`spdz_mac_check_unique_alpha_on_shift`)**:
    If an adversary shifts an authenticated wire by a nonzero value `deltaVal ≠ 0` (`openedVal = trueVal + deltaVal`)
    and injects MAC shift `deltaMac` (`openedMac = alpha * trueVal + deltaMac`), then at most ONE
    global MAC key `alpha ∈ GoldilocksExt2` (out of `p^2 > 2^127`) satisfies the MAC equation
    `deltaMac = alpha * ofBase(deltaVal)`. -/
theorem spdz_mac_check_unique_alpha_on_shift
    {deltaVal : Goldilocks} (hNe : deltaVal ≠ Goldilocks.zero)
    (deltaMac alpha₁ alpha₂ : GoldilocksExt2)
    (h1 : deltaMac = CommRingOps.mul alpha₁ (GoldilocksExt2.ofBase deltaVal))
    (h2 : deltaMac = CommRingOps.mul alpha₂ (GoldilocksExt2.ofBase deltaVal)) :
    alpha₁ = alpha₂ ∧ 2 ^ 127 < goldilocksPrime ^ 2 := by
  have hBaseNe : GoldilocksExt2.ofBase deltaVal ≠ GoldilocksExt2.zero := fun h0 =>
    hNe (GoldilocksExt2.ofBase_injective h0)
  have hEq : CommRingOps.mul alpha₁ (GoldilocksExt2.ofBase deltaVal) =
      CommRingOps.mul alpha₂ (GoldilocksExt2.ofBase deltaVal) := h1.symm.trans h2
  have hMulInv := congrArg (fun x => CommRingOps.mul x (GoldilocksExt2.inv (GoldilocksExt2.ofBase deltaVal))) hEq
  rw [LawfulCommRing.mul_assoc, LawfulCommRing.mul_assoc,
      GoldilocksExt2.mul_inv_cancel hBaseNe,
      LawfulCommRing.mul_one, LawfulCommRing.mul_one] at hMulInv
  exact ⟨hMulInv, goldilocksExt2_card_gt_two_pow_126 127 (Nat.le_refl 127)⟩

/-! ## 2. Two-Pass `spdzReserveCounters` & Partial-Failure Burn Without Recycling (`voprf_spdz.rs:1538-1583`) -/

/-- Per-server counter state in `reserve_counters`: in-memory `lastCounter` and durable `storeHighWater`,
    plus whether this server's durable `store.reserve(...)` I/O call succeeds on the current turn. -/
structure SpdzCounterSlot where
  party : Nat
  lastCounter : Option Nat
  storeHighWater : Option Nat
  ioSucceeds : Bool
  deriving DecidableEq, Repr

/-- Updated per-server counter state after `reserve_counters`. -/
structure SpdzCounterAfter where
  party : Nat
  lastCounter : Option Nat
  storeHighWater : Option Nat
  deriving DecidableEq, Repr

/-- Single-server `admit_counter` check (`voprf.rs:310-326`, `voprf_spdz.rs:1566`):
    `counter < u64::MAX`, strictly exceeds in-memory `lastCounter`, and strictly exceeds durable `storeHighWater`. -/
def spdzAdmitCounter (lastCounter storeHighWater : Option Nat) (counter : Nat) : Bool :=
  decide (counter < TOPRF_COUNTER_MAX) &&
  (match lastCounter with | none => true | some last => decide (last < counter)) &&
  (match storeHighWater with | none => true | some hw => decide (hw < counter))

/-- Ratchet loop of `reserve_counters` (`voprf_spdz.rs:1570-1582`):
    once pre-validation succeeds across ALL servers, iterates through the quorum:
    * if no earlier store failed (`persistErr = false`) and `slot.ioSucceeds = true`, updates durable
      `storeHighWater := some counter`;
    * if `slot.ioSucceeds = false`, sets `persistErr := true` and leaves this and subsequent durable
      stores unchanged;
    * **unconditionally** ratchets `lastCounter := some (max last counter)` on EVERY server in the quorum! -/
def spdzRatchetPass (counter : Nat) : Bool → List SpdzCounterSlot → Bool × List SpdzCounterAfter
  | persistErr, [] => (persistErr, [])
  | persistErr, slot :: rest =>
    let persistErr' := persistErr || !slot.ioSucceeds
    let newStore := if !persistErr && slot.ioSucceeds then some counter else slot.storeHighWater
    let newLast := some (match slot.lastCounter with
      | none => counter
      | some last => if last ≤ counter then counter else last)
    let tail := spdzRatchetPass counter persistErr' rest
    (tail.1, ⟨slot.party, newLast, newStore⟩ :: tail.2)

/-- Two-pass `spdzReserveCounters` (`voprf_spdz.rs:1538-1583`):
    1. Pre-validates quorum size, ascending party order, item batch bounds (`1 ≤ items ≤ 64`), and
       `spdzAdmitCounter` across ALL quorum servers before mutating `stores[0]`.
    2. Runs `spdzRatchetPass`: returns `StepOutcome.ok` if all durable writes succeeded, or
       `StepOutcome.err` with the ratcheted counter states if any store failed partway through. -/
def spdzReserveCounters (cfg : SpdzConfig) (slots : List SpdzCounterSlot)
    (counter items : Nat) : StepOutcome (List SpdzCounterAfter) Unit Bool :=
  let unchanged := slots.map (fun s => SpdzCounterAfter.mk s.party s.lastCounter s.storeHighWater)
  let quorumOk :=
    cfg.Valid &&
    decide (cfg.threshold ≤ slots.length) &&
    decide (slots.length ≤ cfg.servers) &&
    slots.all (fun s => decide (s.party < cfg.servers)) &&
    decide ((slots.map SpdzCounterSlot.party).Pairwise (· < ·)) &&
    decide (1 ≤ items ∧ items ≤ Spec.pqCredentialProfile.toprfMaxBatch) &&
    slots.all (fun s => spdzAdmitCounter s.lastCounter s.storeHighWater counter)
  if !quorumOk then
    .err unchanged false
  else
    let (hadIoErr, updated) := spdzRatchetPass counter false slots
    if hadIoErr then .err updated true else .ok updated ()

private theorem spdzRatchetPass_err_true (counter : Nat) :
    ∀ (xs : List SpdzCounterSlot), (spdzRatchetPass counter true xs).1 = true
  | [] => rfl
  | x :: xs => by
    show (spdzRatchetPass counter (true || !x.ioSucceeds) xs).1 = true
    rw [Bool.true_or]
    exact spdzRatchetPass_err_true counter xs

theorem spdzRatchetPass_ratchets_all (counter : Nat) :
    ∀ (persistErr : Bool) (slots : List SpdzCounterSlot),
      (spdzRatchetPass counter persistErr slots).2.length = slots.length ∧
      ∀ st ∈ (spdzRatchetPass counter persistErr slots).2,
        ∃ v : Nat, st.lastCounter = some v ∧ counter ≤ v
  | _, [] => ⟨rfl, fun _ h => nomatch h⟩
  | persistErr, slot :: rest => by
    obtain ⟨hLen, hAll⟩ := spdzRatchetPass_ratchets_all counter (persistErr || !slot.ioSucceeds) rest
    refine ⟨by simp only [spdzRatchetPass, List.length_cons, hLen], fun st hMem => ?_⟩
    simp only [spdzRatchetPass] at hMem
    rcases List.mem_cons.mp hMem with rfl | hTail
    · cases slot.lastCounter with
      | none => exact ⟨counter, rfl, Nat.le_refl counter⟩
      | some last => exact ⟨if last ≤ counter then counter else last, rfl, by split <;> omega⟩
    · exact hAll st hTail

theorem spdzRatchetPass_prefix_stores_burned (counter : Nat) :
    ∀ (pre : List SpdzCounterSlot) (failSlot : SpdzCounterSlot) (post : List SpdzCounterSlot),
      (∀ s ∈ pre, s.ioSucceeds = true) →
      failSlot.ioSucceeds = false →
      (spdzRatchetPass counter false (pre ++ failSlot :: post)).1 = true ∧
      ((spdzRatchetPass counter false (pre ++ failSlot :: post)).2.take pre.length).all
        (fun st => decide (st.storeHighWater = some counter)) = true ∧
      ∀ st ∈ (spdzRatchetPass counter false (pre ++ failSlot :: post)).2,
        ∀ c ≤ counter, spdzAdmitCounter st.lastCounter st.storeHighWater c = false
  | [], failSlot, post, _, hFail => by
    have hRat := (spdzRatchetPass_ratchets_all counter true post).2
    refine ⟨?_, rfl, ?_⟩
    · show (spdzRatchetPass counter (false || !failSlot.ioSucceeds) post).1 = true
      rw [hFail]
      exact spdzRatchetPass_err_true counter post
    · intro st hMem c hc
      simp only [List.nil_append, spdzRatchetPass, hFail] at hMem
      rcases List.mem_cons.mp hMem with rfl | hTail
      · unfold spdzAdmitCounter
        cases failSlot.lastCounter with
        | none =>
          have hNotLt : ¬ (counter < c) := by omega
          simp [decide_eq_false hNotLt]
        | some last =>
          have hNotLt : ¬ ((if last ≤ counter then counter else last) < c) := by
            split <;> omega
          simp [decide_eq_false hNotLt]
      · obtain ⟨v, hvEq, hvGe⟩ := hRat st hTail
        unfold spdzAdmitCounter
        rw [hvEq]
        have hNotLt : ¬ (v < c) := by omega
        simp [decide_eq_false hNotLt]
  | s0 :: pre, failSlot, post, hPre, hFail => by
    have hs0 : s0.ioSucceeds = true := hPre s0 (.head _)
    obtain ⟨h1, h2, h3⟩ := spdzRatchetPass_prefix_stores_burned counter pre failSlot post
      (fun s hs => hPre s (.tail _ hs)) hFail
    refine ⟨?_, ?_, ?_⟩
    · show (spdzRatchetPass counter (false || !s0.ioSucceeds) (pre ++ failSlot :: post)).1 = true
      rw [hs0]; exact h1
    · show (decide ((if (!false && s0.ioSucceeds) = true then some counter else s0.storeHighWater) = some counter) &&
        ((spdzRatchetPass counter (false || !s0.ioSucceeds) (pre ++ failSlot :: post)).2.take pre.length).all
          (fun st => decide (st.storeHighWater = some counter))) = true
      rw [hs0]
      simpa using h2
    · intro st hMem c hc
      simp only [List.cons_append, spdzRatchetPass, hs0] at hMem
      rcases List.mem_cons.mp hMem with rfl | hTail
      · unfold spdzAdmitCounter
        cases s0.lastCounter with
        | none =>
          have hNotLt : ¬ (counter < c) := by omega
          simp [decide_eq_false hNotLt]
        | some last =>
          have hNotLt : ¬ ((if last ≤ counter then counter else last) < c) := by
            split <;> omega
          simp [decide_eq_false hNotLt]
      · exact h3 st hTail c hc

private theorem list_all_false_of_mem {α : Type} (p : α → Bool) :
    ∀ {xs : List α} {b : α}, b ∈ xs → p b = false → xs.all p = false
  | _ :: _, _, .head _, hb => by simp [hb]
  | _ :: tl, _, .tail _ hm, hb => by simp [list_all_false_of_mem p hm hb]

/-- **Pre-Validation Before Mutating `stores[0]` (`spdzReserveCounters_prevalidates_before_mutating`)**:
    If ANY server in the quorum rejects `counter` in `spdzAdmitCounter` (for example `slots[1]` has
    already seen `counter`, even when `slots[0]` is fresh and `slots[0].ioSucceeds = true`),
    `spdzReserveCounters` aborts BEFORE mutating `slots[0]`'s durable store or high-water mark! -/
theorem spdzReserveCounters_prevalidates_before_mutating
    (cfg : SpdzConfig) (slots : List SpdzCounterSlot) (counter items : Nat)
    {badSlot : SpdzCounterSlot} (hMem : badSlot ∈ slots)
    (hReject : spdzAdmitCounter badSlot.lastCounter badSlot.storeHighWater counter = false) :
    spdzReserveCounters cfg slots counter items =
      .err (slots.map (fun s => ⟨s.party, s.lastCounter, s.storeHighWater⟩)) false := by
  unfold spdzReserveCounters
  have hAllFalse : slots.all (fun s => spdzAdmitCounter s.lastCounter s.storeHighWater counter) = false :=
    list_all_false_of_mem _ hMem hReject
  simp [hAllFalse]

/-- **Partial-Reservation Counter Burn Without Recycling (`partial_reserve_burns_without_recycle`)**:
    When pre-validation succeeds on `slots = pre ++ failSlot :: post` (`failSlot.ioSucceeds = false`,
    modeling an I/O failure on `stores[i]` partway through `reserve_counters` at `voprf_spdz.rs:1571-1578`),
    `spdzReserveCounters` returns `.err updated true` where:
    1. Every prefix server (`0 .. pre.length - 1`) durably burned `some counter` in `storeHighWater`,
    2. **Every** server in the entire quorum (`pre`, `failSlot`, and `post`) ratcheted its in-memory
       `lastCounter` to `≥ counter`, and
    3. **Zero counter recycling**: every server in `updated` strictly rejects `spdzAdmitCounter` for
       every `c ≤ counter` (in particular `c = counter` itself)! -/
theorem partial_reserve_burns_without_recycle
    (cfg : SpdzConfig) (pre : List SpdzCounterSlot) (failSlot : SpdzCounterSlot)
    (post : List SpdzCounterSlot) (counter items : Nat)
    (hValid : cfg.Valid = true)
    (hQuorumLo : cfg.threshold ≤ (pre ++ failSlot :: post).length)
    (hQuorumHi : (pre ++ failSlot :: post).length ≤ cfg.servers)
    (hPartyLt : ∀ s ∈ pre ++ failSlot :: post, s.party < cfg.servers)
    (hSorted : ((pre ++ failSlot :: post).map SpdzCounterSlot.party).Pairwise (· < ·))
    (hItems : 1 ≤ items ∧ items ≤ Spec.pqCredentialProfile.toprfMaxBatch)
    (hAdmit : ∀ s ∈ pre ++ failSlot :: post,
      spdzAdmitCounter s.lastCounter s.storeHighWater counter = true)
    (hPreOk : ∀ s ∈ pre, s.ioSucceeds = true)
    (hFail : failSlot.ioSucceeds = false) :
    ∃ updated : List SpdzCounterAfter,
      spdzReserveCounters cfg (pre ++ failSlot :: post) counter items = .err updated true ∧
      (updated.take pre.length).all (fun st => decide (st.storeHighWater = some counter)) = true ∧
      (∀ st ∈ updated, ∃ v : Nat, st.lastCounter = some v ∧ counter ≤ v) ∧
      (∀ st ∈ updated, ∀ c ≤ counter, spdzAdmitCounter st.lastCounter st.storeHighWater c = false) := by
  let slots := pre ++ failSlot :: post
  have hQOk :
      (cfg.Valid &&
       decide (cfg.threshold ≤ slots.length) &&
       decide (slots.length ≤ cfg.servers) &&
       slots.all (fun s => decide (s.party < cfg.servers)) &&
       decide ((slots.map SpdzCounterSlot.party).Pairwise (· < ·)) &&
       decide (1 ≤ items ∧ items ≤ Spec.pqCredentialProfile.toprfMaxBatch) &&
       slots.all (fun s => spdzAdmitCounter s.lastCounter s.storeHighWater counter)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    exact ⟨⟨⟨⟨⟨⟨hValid, hQuorumLo⟩, hQuorumHi⟩, hPartyLt⟩, hSorted⟩, hItems⟩, hAdmit⟩
  obtain ⟨hErr, hPrefix, hNoRecycle⟩ :=
    spdzRatchetPass_prefix_stores_burned counter pre failSlot post hPreOk hFail
  have hAllRat := (spdzRatchetPass_ratchets_all counter false slots).2
  refine ⟨(spdzRatchetPass counter false slots).2, ?_, hPrefix, hAllRat, hNoRecycle⟩
  unfold spdzReserveCounters
  dsimp only
  change (if !(cfg.Valid &&
      decide (cfg.threshold ≤ slots.length) &&
      decide (slots.length ≤ cfg.servers) &&
      slots.all (fun s => decide (s.party < cfg.servers)) &&
      decide ((slots.map SpdzCounterSlot.party).Pairwise (· < ·)) &&
      decide (1 ≤ items ∧ items ≤ Spec.pqCredentialProfile.toprfMaxBatch) &&
      slots.all (fun s => spdzAdmitCounter s.lastCounter s.storeHighWater counter))
    then _ else _) = _
  rw [hQOk]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  dsimp only [slots] at hErr ⊢
  rw [hErr]
  simp only [↓reduceIte]

/-! ## 3. `ToprfReservoir`, `ToprfRefusal` & 3-Phase MAC-Checked Online Evaluation (`voprf_spdz.rs`) -/

/-- Volatile, monotone-cursor preprocessing reservoir (`SpdzReservoir` & `TuplePool` in `voprf_spdz.rs:744-832, 1214`).
    Tuples are consumed by advancing `pow7Cursor` and `beaverCursor` BEFORE reading; `poisoned = true`
    permanently disables the reservoir upon any `Refusal.quorum` MAC/opening fault. -/
structure ToprfReservoir where
  preprocessSid : BitVec 256
  pow7Cursor : Nat
  pow7Total : Nat
  beaverCursor : Nat
  beaverTotal : Nat
  sessionsRemaining : Nat
  poisoned : Bool
  deriving DecidableEq, Repr

def ToprfReservoir.remainingPow7 (r : ToprfReservoir) : Nat :=
  if r.poisoned then 0 else r.pow7Total - r.pow7Cursor

def ToprfReservoir.remainingBeaver (r : ToprfReservoir) : Nat :=
  if r.poisoned then 0 else r.beaverTotal - r.beaverCursor

/-- Prepare a fresh reservoir for `items` total evaluations across `sessions` borrows (`voprf_spdz.rs:1224-1387`). -/
def ToprfReservoir.prepare (preprocessSid : BitVec 256) (items sessions : Nat) : Option ToprfReservoir :=
  if decide (1 ≤ sessions ∧ sessions ≤ items ∧ items ≤ Spec.pqCredentialProfile.toprfMaxBatch) then
    some {
      preprocessSid := preprocessSid
      pow7Cursor := 0
      pow7Total := items * SBOXES_PER_ITEM
      beaverCursor := 0
      beaverTotal := items * MASKS_PER_ITEM + sessions * TOPRF_LANES
      sessionsRemaining := sessions
      poisoned := false
    }
  else none

/-- Poison and wipe the entire reservoir after a quorum/MAC deviation (`voprf_spdz.rs:1504-1507`). -/
def ToprfReservoir.poison (r : ToprfReservoir) : ToprfReservoir :=
  { r with
    pow7Cursor := r.pow7Total
    beaverCursor := r.beaverTotal
    sessionsRemaining := 0
    poisoned := true }

/-- Advance cursors upfront to reserve `items` evaluations for one `SpdzPreparedSession` (`voprf_spdz.rs:1433-1485, 1528-1535`).
    Notice both `pow7Cursor` and `beaverCursor` strictly advance and `sessionsRemaining` decrements by 1! -/
def ToprfReservoir.reserveSession (r : ToprfReservoir) (items : Nat) : Option ToprfReservoir :=
  let needPow7 := items * SBOXES_PER_ITEM
  let needBeaver := items * MASKS_PER_ITEM + TOPRF_LANES
  if !r.poisoned &&
     decide (1 ≤ items ∧ items ≤ Spec.pqCredentialProfile.toprfMaxBatch) &&
     decide (1 ≤ r.sessionsRemaining) &&
     decide (needPow7 ≤ r.pow7Total - r.pow7Cursor) &&
     decide (needBeaver ≤ r.beaverTotal - r.beaverCursor) then
    some {
      r with
      pow7Cursor := r.pow7Cursor + needPow7
      beaverCursor := r.beaverCursor + needBeaver
      sessionsRemaining := r.sessionsRemaining - 1
    }
  else none

/-- Evaluation refusal classification (`enum Refusal` in `voprf_spdz.rs:835-841`):
    * `request`: malformed context, non-canonical input difference, or dual-mask mismatch in Phase 1
      (every MAC check passed, so ONLY this session's reservation is spent);
    * `quorum`: a quorum share opening or SPDZ MAC check failed in Phase 1, Phase 2, or Phase 3
      (a server deviated, so the ENTIRE reservoir is poisoned and discarded). -/
inductive ToprfRefusal where
  | request (reason : Nat)
  | quorum (phase : Nat)
  deriving DecidableEq, Repr

/-- Transcript summary of the 3 MAC-checked online phases of `SpdzSession::evaluate_inner` (`voprf_spdz.rs:1098-1206`). -/
structure SpdzOnlineTranscript where
  contextMatchesGrant : Bool
  canonicalDiffs : Bool
  phase1MacOk : Bool
  phase1DiffZero : Bool
  phase2MacOk : Bool
  phase3MacOk : Bool
  clientDualPadConsistent : Bool
  deriving DecidableEq, Repr

def SpdzOnlineTranscript.honest : SpdzOnlineTranscript :=
  { contextMatchesGrant := true
    canonicalDiffs := true
    phase1MacOk := true
    phase1DiffZero := true
    phase2MacOk := true
    phase3MacOk := true
    clientDualPadConsistent := true }

/-- Exact 3-phase gate of `SpdzPreparedSession::evaluate` (`voprf_spdz.rs:1098-1206, 1519-1525`). -/
def evaluatePreparedSpdzSession (afterReserve : ToprfReservoir)
    (tr : SpdzOnlineTranscript) : StepOutcome ToprfReservoir Unit ToprfRefusal :=
  if tr.contextMatchesGrant then
    if tr.canonicalDiffs then
      if tr.phase1MacOk then
        if tr.phase1DiffZero then
          if tr.phase2MacOk then
            if tr.phase3MacOk then
              if tr.clientDualPadConsistent then
                .ok afterReserve ()
              else
                .err afterReserve.poison (.quorum 4)
            else
              .err afterReserve.poison (.quorum 3)
          else
            .err afterReserve.poison (.quorum 2)
        else
          .err afterReserve (.request 2)
      else
        .err afterReserve.poison (.quorum 1)
    else
      .err afterReserve (.request 1)
  else
    .err afterReserve (.request 0)

/-- **Monotone Cursor Advance & Refusal Isolation (`reservoir_cursor_strict_monotone_and_refusal_isolation`)**:
    1. Every successful `reserveSession` strictly advances `pow7Cursor` by `items * 118` (`≥ 118`),
       `beaverCursor` by `items * 16 + 4` (`≥ 20`), and decrements `sessionsRemaining` by `1`.
    2. A `ToprfRefusal.request` error leaves `poisoned = false` and preserves the remaining tuple budget
       of subsequent sessions (`voprf_spdz.rs:1921-1976`).
    3. A `ToprfRefusal.quorum` error (failed MAC check in Phase 1, 2, or 3) sets `poisoned = true`,
       zeros `sessionsRemaining`, `remainingPow7`, and `remainingBeaver`, and causes every subsequent
       `reserveSession` to return `none` (`voprf_spdz.rs:1977-1986`). -/
theorem reservoir_cursor_strict_monotone_and_refusal_isolation
    (r r' : ToprfReservoir) (items : Nat)
    (hRes : r.reserveSession items = some r') :
    (r.pow7Cursor + 118 ≤ r'.pow7Cursor ∧
     r.beaverCursor + 20 ≤ r'.beaverCursor ∧
     r'.sessionsRemaining + 1 = r.sessionsRemaining ∧
     r'.poisoned = false) ∧
    (∀ tr rAfter reason,
      evaluatePreparedSpdzSession r' tr = .err rAfter (.request reason) →
      rAfter = r' ∧ rAfter.poisoned = false) ∧
    (∀ tr rAfter phase,
      evaluatePreparedSpdzSession r' tr = .err rAfter (.quorum phase) →
      rAfter.poisoned = true ∧ rAfter.sessionsRemaining = 0 ∧
      rAfter.remainingPow7 = 0 ∧ rAfter.remainingBeaver = 0 ∧
      ∀ k, rAfter.reserveSession k = none) := by
  have hReq : ∀ (s : ToprfReservoir) (hp : s.poisoned = false) (tr : SpdzOnlineTranscript)
      (rAfter : ToprfReservoir) (reason : Nat),
      evaluatePreparedSpdzSession s tr = .err rAfter (.request reason) →
      rAfter = s ∧ rAfter.poisoned = false := by
    intro s hp ⟨b0, b1, b2, b3, b4, b5, b6⟩ rAfter reason hEv
    cases b0 with
    | false => injection hEv with hR _; subst hR; exact ⟨rfl, hp⟩
    | true =>
      cases b1 with
      | false => injection hEv with hR _; subst hR; exact ⟨rfl, hp⟩
      | true =>
        cases b2 with
        | false => injection hEv with _ hE; cases hE
        | true =>
          cases b3 with
          | false => injection hEv with hR _; subst hR; exact ⟨rfl, hp⟩
          | true =>
            cases b4 with
            | false => injection hEv with _ hE; cases hE
            | true =>
              cases b5 with
              | false => injection hEv with _ hE; cases hE
              | true =>
                cases b6 with
                | false => injection hEv with _ hE; cases hE
                | true => cases hEv
  have hQuo : ∀ (s : ToprfReservoir) (tr : SpdzOnlineTranscript)
      (rAfter : ToprfReservoir) (phase : Nat),
      evaluatePreparedSpdzSession s tr = .err rAfter (.quorum phase) →
      rAfter.poisoned = true ∧ rAfter.sessionsRemaining = 0 ∧
      rAfter.remainingPow7 = 0 ∧ rAfter.remainingBeaver = 0 ∧
      ∀ k, rAfter.reserveSession k = none := by
    intro s ⟨b0, b1, b2, b3, b4, b5, b6⟩ rAfter phase hEv
    have hPois : s.poison.poisoned = true ∧ s.poison.sessionsRemaining = 0 ∧
        s.poison.remainingPow7 = 0 ∧ s.poison.remainingBeaver = 0 ∧
        ∀ k, s.poison.reserveSession k = none := by
      refine ⟨rfl, rfl, ?_, ?_, fun k => ?_⟩
      · unfold ToprfReservoir.remainingPow7 ToprfReservoir.poison; rfl
      · unfold ToprfReservoir.remainingBeaver ToprfReservoir.poison; rfl
      · unfold ToprfReservoir.reserveSession ToprfReservoir.poison; rfl
    cases b0 with
    | false => injection hEv with _ hE; cases hE
    | true =>
      cases b1 with
      | false => injection hEv with _ hE; cases hE
      | true =>
        cases b2 with
        | false => injection hEv with hR _; subst hR; exact hPois
        | true =>
          cases b3 with
          | false => injection hEv with _ hE; cases hE
          | true =>
            cases b4 with
            | false => injection hEv with hR _; subst hR; exact hPois
            | true =>
              cases b5 with
              | false => injection hEv with hR _; subst hR; exact hPois
              | true =>
                cases b6 with
                | false => injection hEv with hR _; subst hR; exact hPois
                | true => cases hEv
  unfold ToprfReservoir.reserveSession at hRes
  dsimp only at hRes
  split at hRes
  · rename_i hCond
    injection hRes with hEq
    subst hEq
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hCond
    rcases hCond with ⟨⟨⟨⟨hNotPois, hItems⟩, hSess⟩, _⟩, _⟩
    have hPowGe : 118 ≤ items * SBOXES_PER_ITEM := by
      have h1 := Nat.mul_le_mul_right 118 hItems.1
      unfold SBOXES_PER_ITEM
      omega
    have hBeavGe : 20 ≤ items * MASKS_PER_ITEM + TOPRF_LANES := by
      have h1 := Nat.mul_le_mul_right 16 hItems.1
      unfold MASKS_PER_ITEM TOPRF_LANES
      omega
    exact ⟨⟨by dsimp only; omega, by dsimp only; omega, by dsimp only; omega, hNotPois⟩,
      hReq _ hNotPois, hQuo _⟩
  · cases hRes

/-! ## 4. Quintic Extension `BlindVcFp5 = GF(p)[T]/(T^5 - 3)` (`LawfulField` & Canonical Enumeration) -/

private theorem goldilocks_zero_eq_cring : Goldilocks.zero = (CommRingOps.zero : Goldilocks) := rfl

private theorem goldilocks_one_eq_cring : Goldilocks.one = (CommRingOps.one : Goldilocks) := rfl

/-- Modulus polynomial `M₅(T) = T^5 - 3` over `Goldilocks` (`blind_vc.rs:14, 1576`). -/
def fp5ModPoly : UPoly Goldilocks :=
  UPoly.ofList [CommRingOps.neg (Goldilocks.ofNat 3), CommRingOps.zero, CommRingOps.zero,
    CommRingOps.zero, CommRingOps.zero, CommRingOps.one]

theorem fp5ModPoly_coeffs :
    fp5ModPoly.coeffs =
      [CommRingOps.neg (Goldilocks.ofNat 3), CommRingOps.zero, CommRingOps.zero,
       CommRingOps.zero, CommRingOps.zero, CommRingOps.one] := by
  decide +kernel

theorem fp5ModPoly_length : fp5ModPoly.coeffs.length = 6 := by
  rw [fp5ModPoly_coeffs]; rfl

theorem fp5ModPoly_natDeg : fp5ModPoly.natDeg = 5 := by
  unfold UPoly.natDeg
  rw [fp5ModPoly_length]

theorem fp5ModPoly_ne_zero : fp5ModPoly ≠ CommRingOps.zero := by
  intro h
  have hlen := congrArg (fun p => p.coeffs.length) h
  rw [fp5ModPoly_length, UPoly.coeffs_zero] at hlen
  exact absurd hlen (by decide)

private theorem pow_mod_congr_gl {x y m : Nat} (h : x % m = y % m) :
    ∀ k : Nat, (x ^ k) % m = (y ^ k) % m
  | 0 => rfl
  | k + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod, pow_mod_congr_gl h k, h, ← Nat.mul_mod]

/-- `3` has no 5th root in `Goldilocks` (`3^((p-1)/5) mod p ≠ 1`, `blind_vc.rs:1579`). -/
theorem goldilocks_three_not_fifth_power (r : Goldilocks) :
    CRing.npow r 5 ≠ Goldilocks.ofNat 3 := by
  intro h5
  have hrVal5 : (r.val ^ 5) % goldilocksPrime = 3 := by
    have hv := congrArg Goldilocks.val h5
    have hMul5 : (CRing.npow r 5).val = (r.val ^ 5) % goldilocksPrime := by
      have hC : CRing.npow r 5 = Goldilocks.mul (Goldilocks.mul (Goldilocks.mul (Goldilocks.mul
          (Goldilocks.mul Goldilocks.one r) r) r) r) r := rfl
      rw [hC]
      simp only [Goldilocks.mul_val, Goldilocks.one_val, Nat.one_mul, Nat.mod_mul_mod]
      have hPow5 : r.val ^ 5 = r.val * r.val * r.val * r.val * r.val := by
        simp [Nat.pow_succ, Nat.mul_assoc]
      rw [hPow5]
    rw [hMul5] at hv
    exact hv
  let fifth := (goldilocksPrime - 1) / 5
  have hPowEq : ((r.val ^ 5) ^ fifth) % goldilocksPrime = (3 ^ fifth) % goldilocksPrime :=
    pow_mod_congr_gl hrVal5 fifth
  rw [← Nat.pow_mul] at hPowEq
  have h5fifth : 5 * fifth = goldilocksPrime - 1 := by decide
  rw [h5fifth] at hPowEq
  have hrNe0 : r.val ≠ 0 := by
    intro h0; rw [h0] at hrVal5; revert hrVal5; decide
  have hNotDvd : ¬ (goldilocksPrime ∣ r.val) := fun hd => by
    have := Nat.le_of_dvd (by omega) hd; have := r.isLt; omega
  have hFlt := (goldilocksPrime_isPrime ()).pow_sub_one_mod hNotDvd
  have hModPow := modPowFuel_eq_pow_mod 64 3 fifth goldilocksPrime (by decide)
  rw [hFlt, ← hModPow] at hPowEq
  have hNe1 : modPowFuel 64 3 ((goldilocksPrime - 1) / 5) goldilocksPrime ≠ 1 := by
    decide
  exact hNe1 hPowEq.symm

private theorem coeffAt_X_pow :
    ∀ (m k : Nat), coeffAt (CRing.npow (UPoly.X : UPoly Goldilocks) m).coeffs k =
      if k = m then CommRingOps.one else CommRingOps.zero
  | 0, 0 => by
    show coeffAt (CommRingOps.one : UPoly Goldilocks).coeffs 0 = CommRingOps.one
    rw [UPoly.one_eq_C, UPoly.coeffAt_C_zero]
  | 0, k + 1 => by
    show coeffAt (CommRingOps.one : UPoly Goldilocks).coeffs (k + 1) =
      if k + 1 = 0 then CommRingOps.one else CommRingOps.zero
    rw [UPoly.one_eq_C, UPoly.coeffAt_C_succ]
    simp only [Nat.succ_ne_zero, ↓reduceIte]
  | m + 1, 0 => by
    show coeffAt (CommRingOps.mul (CRing.npow UPoly.X m) UPoly.X).coeffs 0 =
      if 0 = m + 1 then CommRingOps.one else CommRingOps.zero
    rw [LawfulCommRing.mul_comm, UPoly.coeffAt_X_mul_zero]
    have hNe : ¬ (0 = m + 1) := (Nat.succ_ne_zero m).symm
    simp only [hNe, ↓reduceIte]
  | m + 1, k + 1 => by
    show coeffAt (CommRingOps.mul (CRing.npow UPoly.X m) UPoly.X).coeffs (k + 1) =
      if k + 1 = m + 1 then CommRingOps.one else CommRingOps.zero
    rw [LawfulCommRing.mul_comm, UPoly.coeffAt_X_mul_succ, coeffAt_X_pow m k]
    if h : k = m then
      subst h
      simp only [↓reduceIte]
    else
      have h1 : ¬ (k + 1 = m + 1) := fun e => h (Nat.succ.inj e)
      simp only [h, h1, ↓reduceIte]

private theorem coeffAt_X5 :
    ∀ k : Nat, coeffAt (CRing.npow (UPoly.X : UPoly Goldilocks) 5).coeffs k =
      if k = 5 then CommRingOps.one else CommRingOps.zero :=
  coeffAt_X_pow 5

private theorem fp5ModPoly_eq_X5_sub_3 :
    fp5ModPoly = CommRingOps.sub (CRing.npow UPoly.X 5) (UPoly.C (Goldilocks.ofNat 3)) := by
  apply UPoly.ext_coeffAt
  intro k
  rw [fp5ModPoly_coeffs, UPoly.coeffAt_sub, coeffAt_X5]
  match k with
  | 0 =>
    rw [UPoly.coeffAt_C_zero]
    simp only [show ¬ (0 = 5) by decide, ↓reduceIte]
    rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.zero_add]
    rfl
  | 1 =>
    rw [UPoly.coeffAt_C_succ]
    simp only [show ¬ (1 = 5) by decide, ↓reduceIte, LawfulCommRing.sub_zero]
    rfl
  | 2 =>
    rw [UPoly.coeffAt_C_succ]
    simp only [show ¬ (2 = 5) by decide, ↓reduceIte, LawfulCommRing.sub_zero]
    rfl
  | 3 =>
    rw [UPoly.coeffAt_C_succ]
    simp only [show ¬ (3 = 5) by decide, ↓reduceIte, LawfulCommRing.sub_zero]
    rfl
  | 4 =>
    rw [UPoly.coeffAt_C_succ]
    simp only [show ¬ (4 = 5) by decide, ↓reduceIte, LawfulCommRing.sub_zero]
    rfl
  | 5 =>
    rw [UPoly.coeffAt_C_succ]
    simp only [↓reduceIte, LawfulCommRing.sub_zero]
    rfl
  | k' + 6 =>
    rw [UPoly.coeffAt_C_succ]
    simp only [show ¬ (k' + 6 = 5) by omega, ↓reduceIte, LawfulCommRing.sub_zero]
    rfl

private theorem fp5ModPoly_no_deg1_factor (h q : UPoly Goldilocks)
    (hMul : fp5ModPoly = CommRingOps.mul h q) (hDeg1 : h.natDeg = 1) : False := by
  have hhNe : h ≠ CommRingOps.zero := fun e => by
    rw [e] at hDeg1; unfold UPoly.natDeg at hDeg1; rw [UPoly.coeffs_zero] at hDeg1; cases hDeg1
  have hLeadNe : h.lead ≠ CommRingOps.zero := UPoly.lead_ne_zero hhNe
  have hLen2 : h.coeffs.length = 2 := by
    unfold UPoly.natDeg at hDeg1
    cases hc : h.coeffs with
    | nil => exact absurd (UPoly.ext hc) hhNe
    | cons _ tl =>
      cases tl with
      | nil => rw [hc] at hDeg1; cases hDeg1
      | cons _ tl2 =>
        cases tl2 with
        | nil => rfl
        | cons _ _ =>
          rw [hc] at hDeg1
          simp only [List.length_cons, Nat.add_sub_cancel] at hDeg1
          omega
  let c0 := coeffAt h.coeffs 0
  let c1 := coeffAt h.coeffs 1
  have hc1Lead : c1 = h.lead := by rw [UPoly.lead_eq, hDeg1]
  have hc1NeG : c1 ≠ Goldilocks.zero := hc1Lead ▸ hLeadNe
  let r := CommRingOps.mul (CommRingOps.neg c0) (Goldilocks.inv c1)
  have hEvalH : h.eval r = CommRingOps.zero := by
    rw [UPoly.eval_eq]
    cases hc : h.coeffs with
    | nil => rw [hc] at hLen2; cases hLen2
    | cons a0 tl =>
      cases htl : tl with
      | nil => rw [hc, htl] at hLen2; cases hLen2
      | cons a1 tl2 =>
        cases htl2 : tl2 with
        | cons _ _ => rw [hc, htl, htl2] at hLen2; cases hLen2
        | nil =>
          have ha0 : a0 = c0 := by dsimp [c0]; rw [hc]; rfl
          have ha1 : a1 = c1 := by dsimp [c1]; rw [hc, htl]; rfl
          rw [ha0, ha1]
          show CommRingOps.add c0 (CommRingOps.mul r (CommRingOps.add c1 (CommRingOps.mul r CommRingOps.zero))) =
            CommRingOps.zero
          rw [LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
          dsimp [r]
          have hInv : CommRingOps.mul (Goldilocks.inv c1) c1 = CommRingOps.one := by
            rw [LawfulCommRing.mul_comm]
            exact Goldilocks.mul_inv_cancel hc1NeG
          rw [LawfulCommRing.mul_assoc, hInv, LawfulCommRing.mul_one, LawfulCommRing.add_right_neg]
  have hEvalM : fp5ModPoly.eval r = CommRingOps.zero := by
    rw [hMul, UPoly.eval_mul, hEvalH, LawfulCommRing.zero_mul]
  have hEvalSub : fp5ModPoly.eval r = CommRingOps.sub (CRing.npow r 5) (Goldilocks.ofNat 3) := by
    rw [fp5ModPoly_eq_X5_sub_3]
    change (UPoly.evalHom r).toFun
      (CommRingOps.sub (CRing.npow UPoly.X 5) (UPoly.C (Goldilocks.ofNat 3))) = _
    rw [(UPoly.evalHom r).map_sub, RingHom.map_npow (UPoly.evalHom r),
        UPoly.evalHom_apply, UPoly.eval_X, UPoly.evalHom_apply, UPoly.eval_C]
  rw [hEvalSub] at hEvalM
  exact goldilocks_three_not_fifth_power r (LawfulCommRing.sub_eq_zero_iff.mp hEvalM)

private theorem upoly_C_sub (x y : Goldilocks) :
    UPoly.C (CommRingOps.sub x y) = CommRingOps.sub (UPoly.C x) (UPoly.C y) :=
  UPoly.CHom.map_sub x y

private theorem quad_div_X5_identity (a b : Goldilocks) :
    CommRingOps.sub (CRing.npow UPoly.X 5) (UPoly.C (Goldilocks.ofNat 3)) =
      CommRingOps.add
        (CommRingOps.mul
          (CommRingOps.add
            (CommRingOps.add
              (CommRingOps.sub (CRing.npow UPoly.X 3) (CommRingOps.mul (UPoly.C a) (CommRingOps.mul UPoly.X UPoly.X)))
              (CommRingOps.mul (CommRingOps.sub (CommRingOps.mul (UPoly.C a) (UPoly.C a)) (UPoly.C b)) UPoly.X))
            (CommRingOps.sub (CommRingOps.mul (UPoly.C (Goldilocks.ofNat 2)) (CommRingOps.mul (UPoly.C a) (UPoly.C b)))
              (CRing.npow (UPoly.C a) 3)))
          (CommRingOps.add (CommRingOps.add (CommRingOps.mul UPoly.X UPoly.X) (CommRingOps.mul (UPoly.C a) UPoly.X)) (UPoly.C b)))
        (CommRingOps.add
          (UPoly.C
            (CommRingOps.sub
              (CommRingOps.sub (CommRingOps.mul (CRing.npow a 3) b)
                (CommRingOps.mul (Goldilocks.ofNat 2) (CommRingOps.mul a (CommRingOps.mul b b))))
              (Goldilocks.ofNat 3)))
          (CommRingOps.mul
            (UPoly.C
              (CommRingOps.add
                (CommRingOps.sub (CRing.npow a 4)
                  (CommRingOps.mul (Goldilocks.ofNat 3) (CommRingOps.mul (CommRingOps.mul a a) b)))
                (CommRingOps.mul b b)))
            UPoly.X)) := by
  have h2g : Goldilocks.ofNat 2 = CommRingOps.add CommRingOps.one CommRingOps.one := by
    decide +kernel
  have h3g : Goldilocks.ofNat 3 =
      CommRingOps.add (CommRingOps.add CommRingOps.one CommRingOps.one) CommRingOps.one := by
    decide +kernel
  dsimp only [CRing.npow]
  rw [h2g, h3g]
  simp only [UPoly.C_add_eq, upoly_C_sub, UPoly.C_mul_eq, ← UPoly.one_eq_C]
  constructive_ring

/-- Exact Bézout elimination identity over `ℤ[a, b]`:
    `b^5 - 9 = (a^3 b - 2 a b^2 + 3) (a^3 b - 2 a b^2 - 3) + (b^3 - a^2 b^2) (a^4 - 3 a^2 b + b^2)`. -/
private theorem quad_b5_sub_9_bezout_identity (a b : Goldilocks) :
    CommRingOps.sub (CRing.npow b 5) (Goldilocks.ofNat 9) =
      CommRingOps.add
        (CommRingOps.mul
          (CommRingOps.add
            (CommRingOps.sub (CommRingOps.mul (CRing.npow a 3) b)
              (CommRingOps.mul (Goldilocks.ofNat 2) (CommRingOps.mul a (CommRingOps.mul b b))))
            (Goldilocks.ofNat 3))
          (CommRingOps.sub
            (CommRingOps.sub (CommRingOps.mul (CRing.npow a 3) b)
              (CommRingOps.mul (Goldilocks.ofNat 2) (CommRingOps.mul a (CommRingOps.mul b b))))
            (Goldilocks.ofNat 3)))
        (CommRingOps.mul
          (CommRingOps.sub (CRing.npow b 3) (CommRingOps.mul (CommRingOps.mul a a) (CommRingOps.mul b b)))
          (CommRingOps.add
            (CommRingOps.sub (CRing.npow a 4)
              (CommRingOps.mul (Goldilocks.ofNat 3) (CommRingOps.mul (CommRingOps.mul a a) b)))
            (CommRingOps.mul b b))) := by
  have h2 : Goldilocks.ofNat 2 = CommRingOps.add CommRingOps.one CommRingOps.one := by decide +kernel
  have h3 : Goldilocks.ofNat 3 = CommRingOps.add (Goldilocks.ofNat 2) CommRingOps.one := by decide +kernel
  have h9 : Goldilocks.ofNat 9 = CommRingOps.mul (Goldilocks.ofNat 3) (Goldilocks.ofNat 3) := by decide +kernel
  dsimp only [CRing.npow]
  rw [h9, h3, h2]
  constructive_ring

private theorem fp5ModPoly_no_deg2_factor (h q : UPoly Goldilocks)
    (hMul : fp5ModPoly = CommRingOps.mul h q) (hDeg2 : h.natDeg = 2) : False := by
  have hhNe : h ≠ CommRingOps.zero := fun e => by
    rw [e] at hDeg2; unfold UPoly.natDeg at hDeg2; rw [UPoly.coeffs_zero] at hDeg2; cases hDeg2
  have hLeadNe : h.lead ≠ CommRingOps.zero := UPoly.lead_ne_zero hhNe
  have hLeadNeG : h.lead ≠ Goldilocks.zero := hLeadNe
  let invL := Goldilocks.inv h.lead
  let hm := CommRingOps.mul (UPoly.C invL) h
  let qm := CommRingOps.mul (UPoly.C h.lead) q
  have hInvCancel : CommRingOps.mul invL h.lead = CommRingOps.one := by
    dsimp [invL]
    rw [LawfulCommRing.mul_comm]
    exact Goldilocks.mul_inv_cancel hLeadNeG
  have hMulM : fp5ModPoly = CommRingOps.mul hm qm := by
    have hCancel : CommRingOps.mul (UPoly.C invL) (UPoly.C h.lead) = CommRingOps.one := by
      rw [← UPoly.C_mul_eq, hInvCancel, ← UPoly.one_eq_C]
    calc fp5ModPoly = CommRingOps.mul CommRingOps.one (CommRingOps.mul h q) := by
          rw [LawfulCommRing.one_mul, ← hMul]
      _ = CommRingOps.mul (CommRingOps.mul (UPoly.C invL) (UPoly.C h.lead)) (CommRingOps.mul h q) := by
          rw [hCancel]
      _ = CommRingOps.mul hm qm := by
          dsimp [hm, qm]
          rw [LawfulCommRing.mul_assoc,
              ← LawfulCommRing.mul_assoc (UPoly.C h.lead) h q,
              LawfulCommRing.mul_comm (UPoly.C h.lead) h,
              LawfulCommRing.mul_assoc h (UPoly.C h.lead) q,
              ← LawfulCommRing.mul_assoc]
  let b := coeffAt hm.coeffs 0
  let a := coeffAt hm.coeffs 1
  have hHmCoeff2 : coeffAt hm.coeffs 2 = CommRingOps.one := by
    dsimp [hm]
    have hLead2 : coeffAt h.coeffs 2 = h.lead := by rw [UPoly.lead_eq, hDeg2]
    rw [UPoly.coeffAt_C_mul, hLead2, hInvCancel]
  have hHmAbove : ∀ k, 3 ≤ k → coeffAt hm.coeffs k = CommRingOps.zero := by
    intro k hk
    dsimp [hm]
    rw [UPoly.coeffAt_C_mul, h.coeffAt_eq_zero_of_natDeg_lt (by omega), LawfulCommRing.mul_zero]
  have hX0 : coeffAt (UPoly.X : UPoly Goldilocks).coeffs 0 = CommRingOps.zero := by decide +kernel
  have hX1 : coeffAt (UPoly.X : UPoly Goldilocks).coeffs 1 = CommRingOps.one := by decide +kernel
  have hXGe2 : ∀ m, coeffAt (UPoly.X : UPoly Goldilocks).coeffs (m + 2) = CommRingOps.zero := by
    intro m
    have hXDeg : (UPoly.X : UPoly Goldilocks).natDeg = 1 := by decide +kernel
    exact (UPoly.X : UPoly Goldilocks).coeffAt_eq_zero_of_natDeg_lt (by omega)
  have hHmEq : hm = CommRingOps.add
      (CommRingOps.add (CommRingOps.mul UPoly.X UPoly.X) (CommRingOps.mul (UPoly.C a) UPoly.X))
      (UPoly.C b) := by
    apply UPoly.ext_coeffAt
    intro k
    rw [UPoly.coeffAt_add, UPoly.coeffAt_add, LawfulCommRing.mul_comm (UPoly.C a) UPoly.X]
    match k with
    | 0 =>
      rw [UPoly.coeffAt_X_mul_zero, UPoly.coeffAt_X_mul_zero, UPoly.coeffAt_C_zero,
          LawfulCommRing.add_zero, LawfulCommRing.zero_add]
    | 1 =>
      rw [UPoly.coeffAt_X_mul_succ, UPoly.coeffAt_X_mul_succ, UPoly.coeffAt_C_succ,
          hX0, UPoly.coeffAt_C_zero, LawfulCommRing.zero_add, LawfulCommRing.add_zero]
    | 2 =>
      rw [UPoly.coeffAt_X_mul_succ, UPoly.coeffAt_X_mul_succ, UPoly.coeffAt_C_succ,
          hX1, UPoly.coeffAt_C_succ, LawfulCommRing.add_zero, LawfulCommRing.add_zero]
      exact hHmCoeff2
    | k' + 3 =>
      rw [UPoly.coeffAt_X_mul_succ, UPoly.coeffAt_X_mul_succ, UPoly.coeffAt_C_succ,
          hXGe2 k', UPoly.coeffAt_C_succ, LawfulCommRing.add_zero, LawfulCommRing.add_zero]
      exact hHmAbove (k' + 3) (by omega)
  have hOneNeZero : (CommRingOps.one : Goldilocks) ≠ CommRingOps.zero := by decide +kernel
  have hHmNe : hm ≠ CommRingOps.zero := fun e => by
    have hc := congrArg (fun p => coeffAt p.coeffs 2) e
    rw [hHmCoeff2, UPoly.coeffs_zero, coeffAt_nil] at hc
    exact hOneNeZero hc
  have hHmDeg2 : hm.natDeg = 2 := by
    apply Nat.le_antisymm
    · exact UPoly.natDeg_le_of_coeffAt hm 2 (fun k hk => hHmAbove k hk)
    · have hNotLt : ¬ (hm.natDeg < 2) := fun hlt => by
        have hz := hm.coeffAt_eq_zero_of_natDeg_lt hlt
        rw [hHmCoeff2] at hz
        exact hOneNeZero hz
      omega
  let r1 := CommRingOps.add
    (CommRingOps.sub (CRing.npow a 4)
      (CommRingOps.mul (Goldilocks.ofNat 3) (CommRingOps.mul (CommRingOps.mul a a) b)))
    (CommRingOps.mul b b)
  let r0 := CommRingOps.sub
    (CommRingOps.sub (CommRingOps.mul (CRing.npow a 3) b)
      (CommRingOps.mul (Goldilocks.ofNat 2) (CommRingOps.mul a (CommRingOps.mul b b))))
    (Goldilocks.ofNat 3)
  let rem := CommRingOps.add (UPoly.C r0) (CommRingOps.mul (UPoly.C r1) UPoly.X)
  let Q := CommRingOps.add
    (CommRingOps.add
      (CommRingOps.sub (CRing.npow UPoly.X 3) (CommRingOps.mul (UPoly.C a) (CommRingOps.mul UPoly.X UPoly.X)))
      (CommRingOps.mul (CommRingOps.sub (CommRingOps.mul (UPoly.C a) (UPoly.C a)) (UPoly.C b)) UPoly.X))
    (CommRingOps.sub (CommRingOps.mul (UPoly.C (Goldilocks.ofNat 2)) (CommRingOps.mul (UPoly.C a) (UPoly.C b)))
      (CRing.npow (UPoly.C a) 3))
  have hId : fp5ModPoly = CommRingOps.add (CommRingOps.mul Q hm) rem := by
    rw [fp5ModPoly_eq_X5_sub_3, hHmEq]
    exact quad_div_X5_identity a b
  have hRemMul : rem = CommRingOps.mul hm (CommRingOps.sub qm Q) := by
    apply LawfulCommRing.add_left_cancel (a := CommRingOps.mul Q hm)
    have hEq := hId.symm.trans hMulM
    calc CommRingOps.add (CommRingOps.mul Q hm) rem
        = CommRingOps.mul hm qm := hEq
      _ = CommRingOps.add (CommRingOps.mul hm Q) (CommRingOps.mul hm (CommRingOps.sub qm Q)) := by
          rw [← LawfulCommRing.left_distrib, LawfulCommRing.add_sub_cancel_left]
      _ = CommRingOps.add (CommRingOps.mul Q hm) (CommRingOps.mul hm (CommRingOps.sub qm Q)) := by
          rw [LawfulCommRing.mul_comm hm Q]
  have hRemDegLe1 : rem.natDeg ≤ 1 := by
    apply UPoly.natDeg_le_of_coeffAt rem 1
    intro k hk
    dsimp [rem]
    rw [UPoly.coeffAt_add, LawfulCommRing.mul_comm (UPoly.C r1) UPoly.X]
    match k with
    | 0 | 1 => omega
    | k' + 2 =>
      rw [UPoly.coeffAt_C_succ, UPoly.coeffAt_X_mul_succ, UPoly.coeffAt_C_succ,
          LawfulCommRing.zero_add]
  have hRemZero : rem = CommRingOps.zero := by
    if hDiff0 : CommRingOps.sub qm Q = CommRingOps.zero then
      rw [hRemMul, hDiff0, LawfulCommRing.mul_zero]
    else
      exfalso
      have hDegEq := UPoly.natDeg_mul hHmNe hDiff0
      rw [← hRemMul, hHmDeg2] at hDegEq
      omega
  have hr0Zero : r0 = CommRingOps.zero := by
    have hc0 := congrArg (fun p => coeffAt p.coeffs 0) hRemZero
    dsimp [rem] at hc0
    rw [UPoly.coeffAt_add, LawfulCommRing.mul_comm (UPoly.C r1) UPoly.X,
        UPoly.coeffAt_X_mul_zero, UPoly.coeffAt_C_zero, LawfulCommRing.add_zero,
        UPoly.coeffs_zero, coeffAt_nil] at hc0
    exact hc0
  have hr1Zero : r1 = CommRingOps.zero := by
    have hc1 := congrArg (fun p => coeffAt p.coeffs 1) hRemZero
    dsimp [rem] at hc1
    rw [UPoly.coeffAt_add, LawfulCommRing.mul_comm (UPoly.C r1) UPoly.X,
        UPoly.coeffAt_C_succ, UPoly.coeffAt_X_mul_succ, UPoly.coeffAt_C_zero,
        LawfulCommRing.zero_add, UPoly.coeffs_zero, coeffAt_nil] at hc1
    exact hc1
  have hBez := quad_b5_sub_9_bezout_identity a b
  change CommRingOps.sub (CRing.npow b 5) (Goldilocks.ofNat 9) =
    CommRingOps.add (CommRingOps.mul _ r0) (CommRingOps.mul _ r1) at hBez
  rw [hr0Zero, hr1Zero, LawfulCommRing.mul_zero, LawfulCommRing.mul_zero,
      LawfulCommRing.add_zero] at hBez
  have hb5 : CRing.npow b 5 = Goldilocks.ofNat 9 := LawfulCommRing.sub_eq_zero_iff.mp hBez
  let inv3 := Goldilocks.inv (Goldilocks.ofNat 3)
  let z := CommRingOps.mul (CRing.npow b 3) inv3
  have h3Cancel : CommRingOps.mul (Goldilocks.ofNat 3) inv3 = CommRingOps.one := by
    dsimp [inv3]
    exact Goldilocks.mul_inv_cancel (by decide)
  have h9Eq : Goldilocks.ofNat 9 = CommRingOps.mul (Goldilocks.ofNat 3) (Goldilocks.ofNat 3) := by
    decide +kernel
  have hz5 : CRing.npow z 5 = Goldilocks.ofNat 3 := by
    have hPowId : ∀ (B I : Goldilocks),
        CRing.npow (CommRingOps.mul (CRing.npow B 3) I) 5 =
          CommRingOps.mul (CRing.npow (CRing.npow B 5) 3) (CRing.npow I 5) := fun B I => by
      dsimp only [CRing.npow]
      constructive_ring
    dsimp [z]
    rw [hPowId b inv3, hb5, h9Eq]
    have hCancel3 : ∀ (T I : Goldilocks),
        CommRingOps.mul (CRing.npow (CommRingOps.mul T T) 3) (CRing.npow I 5) =
          CommRingOps.mul T
            (CommRingOps.mul (CommRingOps.mul T I)
              (CommRingOps.mul (CommRingOps.mul T I)
                (CommRingOps.mul (CommRingOps.mul T I)
                  (CommRingOps.mul (CommRingOps.mul T I) (CommRingOps.mul T I))))) := fun T I => by
      dsimp only [CRing.npow]
      constructive_ring
    rw [hCancel3 (Goldilocks.ofNat 3) inv3, h3Cancel]
    simp only [LawfulCommRing.mul_one]
  exact goldilocks_three_not_fifth_power z hz5

/-- **Irreducibility of `T^5 - 3` over `Goldilocks` (`fp5ModPoly_irreducible`)**:
    No factorization `fp5ModPoly = g * s` exists with `1 ≤ g.natDeg` and `1 ≤ s.natDeg`. -/
