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
   * Concrete reactive protocol machines (`piToprfCredService` and `piToprfCredMachine`) executing
     direct SPDZ TOPRF quorum/counter/reservoir validation and 33-repetition `N = 256` Limbo GGM
     selective-disclosure opening verification (`LimboSdOpeningWire.verify33`), with monotone
     multi-turn reservoir consumption (`piToprfCredService_reservoir_monotone`) and non-identity
     forward simulation (`piToprfCredMachine_dataRefines_idealCred` via `Spec.DataRefines`) to
     `Spec.idealCredMachine cfg`.
   * The evaluation wire carries data, not verdicts: `SpdzOnlineTranscript` holds the bound
     context, the request word and three MAC-carrying openings, and the machine computes the
     seven gate verdicts from them and from the MAC key in its state
     (`SpdzOnlineTranscript.checks`, `piToprfCredService_eval_accept_checks`). A counter-store
     write failure is its own wire event (`approveToprfStoreFault`), not a flag on an approval.
   * `prepareReservoir` turns install only a session identifier that is neither current nor
     retired (`piToprfCredMachine_reservoir_never_rewinds`), so no session's cursors restart.
   * Not modelled here: the SPDZ arithmetic itself. An accepted evaluation returns `cfg.oprf` at
     the ticket's point, issuance carries no ZKBoo transcript, and the MAC key is a plain state
     field (its initial value `initialSpdzMacKey` is a fixed constant).
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

/-- The seven verdicts of the online gate of `SpdzSession::evaluate_inner`
    (`voprf_spdz.rs:1098-1206`). The machine never reads these from a wire: they are computed by
    `SpdzOnlineTranscript.checks` from the opened values, the MAC sums and the MAC key in the
    machine state. -/
structure SpdzOnlineChecks where
  contextMatchesGrant : Bool
  canonicalDiffs : Bool
  phase1MacOk : Bool
  phase1DiffZero : Bool
  phase2MacOk : Bool
  phase3MacOk : Bool
  clientDualPadConsistent : Bool
  deriving DecidableEq, Repr

def SpdzOnlineChecks.honest : SpdzOnlineChecks :=
  { contextMatchesGrant := true
    canonicalDiffs := true
    phase1MacOk := true
    phase1DiffZero := true
    phase2MacOk := true
    phase3MacOk := true
    clientDualPadConsistent := true }

theorem SpdzOnlineChecks.eq_of_fields {a : SpdzOnlineChecks} {b0 b1 b2 b3 b4 b5 b6 : Bool}
    (h0 : a.contextMatchesGrant = b0) (h1 : a.canonicalDiffs = b1) (h2 : a.phase1MacOk = b2)
    (h3 : a.phase1DiffZero = b3) (h4 : a.phase2MacOk = b4) (h5 : a.phase3MacOk = b5)
    (h6 : a.clientDualPadConsistent = b6) : a = ⟨b0, b1, b2, b3, b4, b5, b6⟩ := by
  rcases a with ⟨a0, a1, a2, a3, a4, a5, a6⟩
  dsimp only at h0 h1 h2 h3 h4 h5 h6
  subst h0 h1 h2 h3 h4 h5 h6
  rfl

/-- One opened SPDZ value with the quorum's summed MAC share on it. -/
structure SpdzMacOpening where
  val : Goldilocks
  mac : GoldilocksExt2
  deriving DecidableEq, Repr

/-- The opening of `v` that passes the MAC check under `alpha`. -/
def SpdzMacOpening.authentic (alpha : GoldilocksExt2) (v : Goldilocks) : SpdzMacOpening :=
  ⟨v, CommRingOps.mul alpha (GoldilocksExt2.ofBase v)⟩

/-- What the online phases put on the wire for one evaluation: the context the quorum bound, the
    client's raw masked-difference word, and the three MAC-carrying openings (`"toprf_spdz_input_bind"`
    dual-copy difference, `"toprf_spdz_circuit"`, `"toprf_spdz_output"`), plus the two pad-masked
    copies of the output. It carries data only; no field is a verdict. -/
structure SpdzOnlineTranscript where
  context : Spec.ToprfTicket
  requestWord : Nat
  inputBind : SpdzMacOpening
  circuit : SpdzMacOpening
  output : SpdzMacOpening
  outputCopyA : Goldilocks
  outputCopyB : Goldilocks
  deriving DecidableEq, Repr

/-- The gate's verdicts, computed from the transcript, the granted ticket and the session MAC key:
    the context equals the grant, the request word is a canonical field element, each opening
    satisfies `mac = alpha * val` (`spdzMacCheckAccepts`), the opened dual-copy difference is zero,
    and the two output copies agree. -/
def SpdzOnlineTranscript.checks (tr : SpdzOnlineTranscript) (alpha : GoldilocksExt2)
    (grant : Spec.ToprfTicket) : SpdzOnlineChecks :=
  { contextMatchesGrant := decide (tr.context = grant)
    canonicalDiffs := decide (tr.requestWord < goldilocksPrime)
    phase1MacOk := spdzMacCheckAccepts alpha tr.inputBind.val tr.inputBind.mac
    phase1DiffZero := decide (tr.inputBind.val = Goldilocks.zero)
    phase2MacOk := spdzMacCheckAccepts alpha tr.circuit.val tr.circuit.mac
    phase3MacOk := spdzMacCheckAccepts alpha tr.output.val tr.output.mac
    clientDualPadConsistent := decide (tr.outputCopyA = tr.outputCopyB) }

/-- A transcript whose openings are authentic under `alpha` for the granted ticket, releasing `y`. -/
def SpdzOnlineTranscript.honest (alpha : GoldilocksExt2) (grant : Spec.ToprfTicket)
    (y : Goldilocks) : SpdzOnlineTranscript :=
  { context := grant
    requestWord := 0
    inputBind := SpdzMacOpening.authentic alpha Goldilocks.zero
    circuit := SpdzMacOpening.authentic alpha y
    output := SpdzMacOpening.authentic alpha y
    outputCopyA := y
    outputCopyB := y }

theorem SpdzOnlineTranscript.honest_checks (alpha : GoldilocksExt2) (grant : Spec.ToprfTicket)
    (y : Goldilocks) :
    (SpdzOnlineTranscript.honest alpha grant y).checks alpha grant = SpdzOnlineChecks.honest := by
  have hp : decide ((0 : Nat) < goldilocksPrime) = true := by decide
  exact SpdzOnlineChecks.eq_of_fields (decide_eq_true rfl) hp (decide_eq_true rfl)
    (decide_eq_true rfl) (decide_eq_true rfl) (decide_eq_true rfl) (decide_eq_true rfl)

/-- Exact 3-phase gate of `SpdzPreparedSession::evaluate` (`voprf_spdz.rs:1098-1206, 1519-1525`). -/
def evaluatePreparedSpdzSession (afterReserve : ToprfReservoir)
    (tr : SpdzOnlineChecks) : StepOutcome ToprfReservoir Unit ToprfRefusal :=
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

/-- The gate releases only when every verdict is `true`, and then leaves the reservation as is. -/
theorem evaluatePreparedSpdzSession_ok_all_checks (r r' : ToprfReservoir) (ch : SpdzOnlineChecks)
    (u : Unit) (h : evaluatePreparedSpdzSession r ch = .ok r' u) :
    ch = SpdzOnlineChecks.honest ∧ r' = r := by
  rcases ch with ⟨b0, b1, b2, b3, b4, b5, b6⟩
  unfold evaluatePreparedSpdzSession at h
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> cases b6 <;>
    cases h <;> exact ⟨rfl, rfl⟩

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
  have hReq : ∀ (s : ToprfReservoir) (hp : s.poisoned = false) (tr : SpdzOnlineChecks)
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
  have hQuo : ∀ (s : ToprfReservoir) (tr : SpdzOnlineChecks)
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
theorem fp5ModPoly_irreducible (g s : UPoly Goldilocks)
    (hMul : fp5ModPoly = CommRingOps.mul g s)
    (hgPos : 1 ≤ g.natDeg) (hsPos : 1 ≤ s.natDeg) : False := by
  have hgNe : g ≠ CommRingOps.zero := fun e => by
    rw [e] at hgPos; unfold UPoly.natDeg at hgPos; rw [UPoly.coeffs_zero] at hgPos; cases hgPos
  have hsNe : s ≠ CommRingOps.zero := fun e => by
    rw [e] at hsPos; unfold UPoly.natDeg at hsPos; rw [UPoly.coeffs_zero] at hsPos; cases hsPos
  have hSum : g.natDeg + s.natDeg = 5 := by
    have hd := UPoly.natDeg_mul hgNe hsNe
    rw [← hMul, fp5ModPoly_natDeg] at hd
    exact hd.symm
  if hg1 : g.natDeg = 1 then
    exact fp5ModPoly_no_deg1_factor g s hMul hg1
  else if hg2 : g.natDeg = 2 then
    exact fp5ModPoly_no_deg2_factor g s hMul hg2
  else if hs1 : s.natDeg = 1 then
    exact fp5ModPoly_no_deg1_factor s g (hMul.trans (LawfulCommRing.mul_comm g s)) hs1
  else
    have hs2 : s.natDeg = 2 := by omega
    exact fp5ModPoly_no_deg2_factor s g (hMul.trans (LawfulCommRing.mul_comm g s)) hs2

/-- Canonical remainder `p mod (T^5 - 3)` of formal length `< 6` (`degree ≤ 4`). -/
def fp5Rem (p : UPoly Goldilocks) : UPoly Goldilocks :=
  (UPoly.divMod p fp5ModPoly).2

theorem fp5Rem_length_lt (p : UPoly Goldilocks) : (fp5Rem p).coeffs.length < 6 := by
  have h := (UPoly.divMod_spec p fp5ModPoly fp5ModPoly_ne_zero).2
  rw [fp5ModPoly_length] at h
  exact h

private theorem ring_add_sub_cancel_right {R : Type} [LawfulCommRing R] (x y : R) :
    CommRingOps.sub (CommRingOps.add x y) y = x := by
  rw [LawfulCommRing.sub_eq_add_neg, LawfulCommRing.add_assoc,
      LawfulCommRing.add_right_neg, LawfulCommRing.add_zero]

private theorem ring_add_sub_cancel_left' {R : Type} [LawfulCommRing R] (x y : R) :
    CommRingOps.sub (CommRingOps.add x y) x = y := by
  rw [LawfulCommRing.add_comm x y, ring_add_sub_cancel_right]

private theorem ring_neg_add {R : Type} [LawfulCommRing R] (x y : R) :
    CommRingOps.neg (CommRingOps.add x y) = CommRingOps.add (CommRingOps.neg x) (CommRingOps.neg y) := by
  apply LawfulCommRing.add_left_cancel (a := CommRingOps.add x y)
  rw [LawfulCommRing.add_right_neg,
      LawfulCommRing.add_add_add_comm x y (CommRingOps.neg x) (CommRingOps.neg y),
      LawfulCommRing.add_right_neg, LawfulCommRing.add_right_neg, LawfulCommRing.add_zero]

private theorem ring_congr_rem_identity {R : Type} [LawfulCommRing R]
    (qa qb q ra rb m : R) :
    CommRingOps.sub
      (CommRingOps.add (CommRingOps.add (CommRingOps.mul qb m) rb) (CommRingOps.mul q m))
      (CommRingOps.mul qa m) = ra →
    CommRingOps.sub ra rb =
      CommRingOps.mul (CommRingOps.sub (CommRingOps.add qb q) qa) m := by
  intro hEq
  rw [← hEq]
  have hRearr :
      CommRingOps.sub
        (CommRingOps.sub
          (CommRingOps.add (CommRingOps.add (CommRingOps.mul qb m) rb) (CommRingOps.mul q m))
          (CommRingOps.mul qa m))
        rb =
      CommRingOps.sub (CommRingOps.add (CommRingOps.mul qb m) (CommRingOps.mul q m))
        (CommRingOps.mul qa m) := by
    rw [LawfulCommRing.add_assoc (CommRingOps.mul qb m) rb (CommRingOps.mul q m),
        LawfulCommRing.add_comm rb (CommRingOps.mul q m),
        ← LawfulCommRing.add_assoc (CommRingOps.mul qb m) (CommRingOps.mul q m) rb,
        LawfulCommRing.sub_eq_add_neg, LawfulCommRing.sub_eq_add_neg,
        LawfulCommRing.add_assoc,
        LawfulCommRing.add_comm (CommRingOps.neg (CommRingOps.mul qa m)) (CommRingOps.neg rb),
        ← LawfulCommRing.add_assoc,
        ← LawfulCommRing.sub_eq_add_neg _ rb,
        ring_add_sub_cancel_right,
        ← LawfulCommRing.sub_eq_add_neg]
  rw [hRearr, ← LawfulCommRing.right_distrib qb q m, ← LawfulCommRing.sub_mul]

theorem fp5Rem_eq_self {p : UPoly Goldilocks} (hp : p.coeffs.length < 6) :
    fp5Rem p = p := by
  obtain ⟨hdiv, _⟩ := UPoly.divMod_spec p fp5ModPoly fp5ModPoly_ne_zero
  change p = CommRingOps.add (CommRingOps.mul (UPoly.divMod p fp5ModPoly).1 fp5ModPoly) (fp5Rem p) at hdiv
  if hq0 : (UPoly.divMod p fp5ModPoly).1 = CommRingOps.zero then
    rw [hq0, LawfulCommRing.zero_mul, LawfulCommRing.zero_add] at hdiv
    exact hdiv.symm
  else
    exfalso
    have hDiff : CommRingOps.sub p (fp5Rem p) =
        CommRingOps.mul (UPoly.divMod p fp5ModPoly).1 fp5ModPoly := by
      conv => lhs; arg 1; rw [hdiv]
      exact ring_add_sub_cancel_right _ _
    have hDegGe5 : 5 ≤ (CommRingOps.mul (UPoly.divMod p fp5ModPoly).1 fp5ModPoly).natDeg := by
      rw [UPoly.natDeg_mul hq0 fp5ModPoly_ne_zero, fp5ModPoly_natDeg]
      omega
    rw [← hDiff] at hDegGe5
    have hSubDegLe4 : (CommRingOps.sub p (fp5Rem p)).natDeg ≤ 4 := by
      apply UPoly.natDeg_le_of_coeffAt _ 4
      intro k hk
      rw [UPoly.coeffAt_sub,
          p.coeffAt_eq_zero_of_natDeg_lt (by unfold UPoly.natDeg; omega),
          (fp5Rem p).coeffAt_eq_zero_of_natDeg_lt
            (by have := fp5Rem_length_lt p; unfold UPoly.natDeg; omega),
          LawfulCommRing.sub_self]
    omega

theorem fp5Rem_congr_of_sub_dvd {a b q : UPoly Goldilocks}
    (h : CommRingOps.sub a b = CommRingOps.mul q fp5ModPoly) :
    fp5Rem a = fp5Rem b := by
  obtain ⟨ha, _⟩ := UPoly.divMod_spec a fp5ModPoly fp5ModPoly_ne_zero
  obtain ⟨hb, _⟩ := UPoly.divMod_spec b fp5ModPoly fp5ModPoly_ne_zero
  change a = CommRingOps.add (CommRingOps.mul (UPoly.divMod a fp5ModPoly).1 fp5ModPoly) (fp5Rem a) at ha
  change b = CommRingOps.add (CommRingOps.mul (UPoly.divMod b fp5ModPoly).1 fp5ModPoly) (fp5Rem b) at hb
  let qDiff := CommRingOps.sub (CommRingOps.add (UPoly.divMod b fp5ModPoly).1 q)
    (UPoly.divMod a fp5ModPoly).1
  have hab : a = CommRingOps.add b (CommRingOps.mul q fp5ModPoly) := by
    have h1 := congrArg (fun z => CommRingOps.add b z) h
    rw [LawfulCommRing.add_sub_cancel_left] at h1
    exact h1
  have haEqRa : CommRingOps.sub
      (CommRingOps.add (CommRingOps.add (CommRingOps.mul (UPoly.divMod b fp5ModPoly).1 fp5ModPoly) (fp5Rem b))
        (CommRingOps.mul q fp5ModPoly))
      (CommRingOps.mul (UPoly.divMod a fp5ModPoly).1 fp5ModPoly) = fp5Rem a := by
    rw [← hb, ← hab]
    conv => lhs; arg 1; rw [ha]
    exact ring_add_sub_cancel_left' _ _
  have hRemSub : CommRingOps.sub (fp5Rem a) (fp5Rem b) = CommRingOps.mul qDiff fp5ModPoly :=
    ring_congr_rem_identity _ _ _ _ _ _ haEqRa
  if hq0 : qDiff = CommRingOps.zero then
    rw [hq0, LawfulCommRing.zero_mul] at hRemSub
    exact LawfulCommRing.sub_eq_zero_iff.mp hRemSub
  else
    exfalso
    have hDegGe5 : 5 ≤ (CommRingOps.mul qDiff fp5ModPoly).natDeg := by
      rw [UPoly.natDeg_mul hq0 fp5ModPoly_ne_zero, fp5ModPoly_natDeg]; omega
    rw [← hRemSub] at hDegGe5
    have hDegLe4 : (CommRingOps.sub (fp5Rem a) (fp5Rem b)).natDeg ≤ 4 := by
      apply UPoly.natDeg_le_of_coeffAt _ 4
      intro k hk
      rw [UPoly.coeffAt_sub,
          (fp5Rem a).coeffAt_eq_zero_of_natDeg_lt (by have := fp5Rem_length_lt a; unfold UPoly.natDeg; omega),
          (fp5Rem b).coeffAt_eq_zero_of_natDeg_lt (by have := fp5Rem_length_lt b; unfold UPoly.natDeg; omega),
          LawfulCommRing.sub_self]
    omega

private theorem ring_add_rem_sub_identity {R : Type} [LawfulCommRing R]
    (qa qb ra rb m : R) :
    CommRingOps.sub
      (CommRingOps.add (CommRingOps.add (CommRingOps.mul qa m) ra)
        (CommRingOps.add (CommRingOps.mul qb m) rb))
      (CommRingOps.add ra rb) =
    CommRingOps.mul (CommRingOps.add qa qb) m := by
  rw [LawfulCommRing.add_add_add_comm (CommRingOps.mul qa m) ra (CommRingOps.mul qb m) rb,
      ring_add_sub_cancel_right, ← LawfulCommRing.right_distrib]

theorem fp5Rem_add (a b : UPoly Goldilocks) :
    fp5Rem (CommRingOps.add a b) = CommRingOps.add (fp5Rem a) (fp5Rem b) := by
  have hAddLen : (CommRingOps.add (fp5Rem a) (fp5Rem b)).coeffs.length < 6 := by
    by_cases hz : CommRingOps.add (fp5Rem a) (fp5Rem b) = CommRingOps.zero
    · rw [hz, UPoly.coeffs_zero]; decide
    · have hDeg : (CommRingOps.add (fp5Rem a) (fp5Rem b)).natDeg ≤ 4 := by
        apply UPoly.natDeg_le_of_coeffAt _ 4
        intro k hk
        rw [UPoly.coeffAt_add,
            (fp5Rem a).coeffAt_eq_zero_of_natDeg_lt (by have := fp5Rem_length_lt a; unfold UPoly.natDeg; omega),
            (fp5Rem b).coeffAt_eq_zero_of_natDeg_lt (by have := fp5Rem_length_lt b; unfold UPoly.natDeg; omega),
            LawfulCommRing.add_zero]
      have hPos : 0 < (CommRingOps.add (fp5Rem a) (fp5Rem b)).coeffs.length := by
        cases hc : (CommRingOps.add (fp5Rem a) (fp5Rem b)).coeffs with
        | nil => exact absurd (UPoly.ext hc) hz
        | cons _ _ => simp
      unfold UPoly.natDeg at hDeg
      omega
  rw [← fp5Rem_eq_self hAddLen]
  obtain ⟨ha, _⟩ := UPoly.divMod_spec a fp5ModPoly fp5ModPoly_ne_zero
  obtain ⟨hb, _⟩ := UPoly.divMod_spec b fp5ModPoly fp5ModPoly_ne_zero
  change a = CommRingOps.add (CommRingOps.mul _ fp5ModPoly) (fp5Rem a) at ha
  change b = CommRingOps.add (CommRingOps.mul _ fp5ModPoly) (fp5Rem b) at hb
  refine fp5Rem_congr_of_sub_dvd (q := CommRingOps.add (UPoly.divMod a fp5ModPoly).1 (UPoly.divMod b fp5ModPoly).1) ?_
  conv => lhs; arg 1; rw [ha, hb]
  exact ring_add_rem_sub_identity _ _ _ _ _

private theorem ring_neg_mul_left {R : Type} [LawfulCommRing R] (x y : R) :
    CommRingOps.neg (CommRingOps.mul x y) = CommRingOps.mul (CommRingOps.neg x) y := by
  apply LawfulCommRing.add_left_cancel (a := CommRingOps.mul x y)
  rw [LawfulCommRing.add_right_neg, ← LawfulCommRing.right_distrib,
      LawfulCommRing.add_right_neg, LawfulCommRing.zero_mul]

private theorem ring_mul_rem_sub_identity {R : Type} [LawfulCommRing R]
    (qa ra b m : R) :
    CommRingOps.sub (CommRingOps.mul ra b)
      (CommRingOps.mul (CommRingOps.add (CommRingOps.mul qa m) ra) b) =
    CommRingOps.mul (CommRingOps.neg (CommRingOps.mul qa b)) m := by
  rw [LawfulCommRing.right_distrib, LawfulCommRing.add_comm (CommRingOps.mul (CommRingOps.mul qa m) b) _,
      LawfulCommRing.sub_eq_add_neg,
      ring_neg_add,
      ← LawfulCommRing.add_assoc, LawfulCommRing.add_right_neg, LawfulCommRing.zero_add,
      LawfulCommRing.mul_assoc qa m b, LawfulCommRing.mul_comm m b, ← LawfulCommRing.mul_assoc qa b m,
      ← ring_neg_mul_left]

theorem fp5Rem_mul_rem (a b : UPoly Goldilocks) :
    fp5Rem (CommRingOps.mul (fp5Rem a) b) = fp5Rem (CommRingOps.mul a b) := by
  obtain ⟨ha, _⟩ := UPoly.divMod_spec a fp5ModPoly fp5ModPoly_ne_zero
  change a = CommRingOps.add (CommRingOps.mul _ fp5ModPoly) (fp5Rem a) at ha
  refine fp5Rem_congr_of_sub_dvd (q := CommRingOps.neg (CommRingOps.mul (UPoly.divMod a fp5ModPoly).1 b)) ?_
  conv => lhs; arg 2; arg 1; rw [ha]
  exact ring_mul_rem_sub_identity _ _ _ _

/-- Quintic Goldilocks field `BlindVcFp5 = GF(p)[T]/(T^5 - 3)` (`Fp5` in `blind_vc.rs:1588`). -/
structure BlindVcFp5 where
  poly : UPoly Goldilocks
  len_lt : poly.coeffs.length < 6
  deriving DecidableEq

namespace BlindVcFp5

theorem ext {a b : BlindVcFp5} (h : a.poly = b.poly) : a = b := by
  cases a; cases b; subst h; rfl

def ofUPoly (p : UPoly Goldilocks) : BlindVcFp5 :=
  ⟨fp5Rem p, fp5Rem_length_lt p⟩

def zero : BlindVcFp5 := ⟨CommRingOps.zero, by rw [UPoly.coeffs_zero]; decide⟩
def one : BlindVcFp5 := ⟨CommRingOps.one, by decide +kernel⟩
def ofBase (c : Goldilocks) : BlindVcFp5 := ofUPoly (UPoly.C c)
def tBasis : BlindVcFp5 := ofUPoly UPoly.X

instance : Inhabited BlindVcFp5 := ⟨zero⟩

def add (a b : BlindVcFp5) : BlindVcFp5 := ofUPoly (CommRingOps.add a.poly b.poly)
def neg (a : BlindVcFp5) : BlindVcFp5 := ofUPoly (CommRingOps.neg a.poly)
def sub (a b : BlindVcFp5) : BlindVcFp5 := ofUPoly (CommRingOps.sub a.poly b.poly)
def mul (a b : BlindVcFp5) : BlindVcFp5 := ofUPoly (CommRingOps.mul a.poly b.poly)

theorem add_poly (a b : BlindVcFp5) : (add a b).poly = CommRingOps.add a.poly b.poly := by
  show fp5Rem (CommRingOps.add a.poly b.poly) = _
  rw [fp5Rem_add, fp5Rem_eq_self a.len_lt, fp5Rem_eq_self b.len_lt]

theorem neg_poly (a : BlindVcFp5) : (neg a).poly = CommRingOps.neg a.poly := by
  have hLen : (CommRingOps.neg a.poly).coeffs.length < 6 := by
    by_cases hz : CommRingOps.neg a.poly = CommRingOps.zero
    · rw [hz, UPoly.coeffs_zero]; decide
    · have hDeg : (CommRingOps.neg a.poly).natDeg ≤ 4 := by
        apply UPoly.natDeg_le_of_coeffAt _ 4
        intro k hk
        rw [UPoly.coeffAt_neg,
            a.poly.coeffAt_eq_zero_of_natDeg_lt (by have := a.len_lt; unfold UPoly.natDeg; omega),
            LawfulCommRing.neg_zero]
      have hPos : 0 < (CommRingOps.neg a.poly).coeffs.length := by
        cases hc : (CommRingOps.neg a.poly).coeffs with
        | nil => exact absurd (UPoly.ext hc) hz
        | cons _ _ => simp
      unfold UPoly.natDeg at hDeg; omega
  exact fp5Rem_eq_self hLen

theorem sub_poly (a b : BlindVcFp5) : (sub a b).poly = CommRingOps.sub a.poly b.poly := by
  show fp5Rem (CommRingOps.sub a.poly b.poly) = _
  rw [LawfulCommRing.sub_eq_add_neg, fp5Rem_add, fp5Rem_eq_self a.len_lt,
      show fp5Rem (CommRingOps.neg b.poly) = (neg b).poly from rfl, neg_poly,
      ← LawfulCommRing.sub_eq_add_neg]

instance instLawfulCommRing : LawfulCommRing BlindVcFp5 where
  zero := zero
  one := one
  add := add
  mul := mul
  neg := neg
  sub := sub
  add_assoc x y z := ext (by simp only [add_poly]; exact LawfulCommRing.add_assoc _ _ _)
  add_comm x y := ext (by simp only [add_poly]; exact LawfulCommRing.add_comm _ _)
  zero_add x := ext (by rw [add_poly]; exact LawfulCommRing.zero_add x.poly)
  add_zero x := ext (by rw [add_poly]; exact LawfulCommRing.add_zero x.poly)
  add_left_neg x := ext (by rw [add_poly, neg_poly]; exact LawfulCommRing.add_left_neg x.poly)
  sub_eq_add_neg x y := ext (by rw [sub_poly, add_poly, neg_poly]; exact LawfulCommRing.sub_eq_add_neg _ _)
  mul_comm x y := ext (by
    show fp5Rem (CommRingOps.mul x.poly y.poly) = fp5Rem (CommRingOps.mul y.poly x.poly)
    rw [LawfulCommRing.mul_comm])
  one_mul x := ext (by
    show fp5Rem (CommRingOps.mul one.poly x.poly) = x.poly
    rw [show one.poly = CommRingOps.one from rfl, LawfulCommRing.one_mul, fp5Rem_eq_self x.len_lt])
  mul_one x := ext (by
    show fp5Rem (CommRingOps.mul x.poly one.poly) = x.poly
    rw [show one.poly = CommRingOps.one from rfl, LawfulCommRing.mul_one, fp5Rem_eq_self x.len_lt])
  left_distrib x y z := ext (by
    show fp5Rem (CommRingOps.mul x.poly (add y z).poly) =
      (add (mul x y) (mul x z)).poly
    rw [add_poly, add_poly]
    show fp5Rem (CommRingOps.mul x.poly (CommRingOps.add y.poly z.poly)) =
      CommRingOps.add (fp5Rem (CommRingOps.mul x.poly y.poly)) (fp5Rem (CommRingOps.mul x.poly z.poly))
    rw [← fp5Rem_add, LawfulCommRing.left_distrib])
  right_distrib x y z := ext (by
    show fp5Rem (CommRingOps.mul (add x y).poly z.poly) =
      (add (mul x z) (mul y z)).poly
    rw [add_poly, add_poly]
    show fp5Rem (CommRingOps.mul (CommRingOps.add x.poly y.poly) z.poly) =
      CommRingOps.add (fp5Rem (CommRingOps.mul x.poly z.poly)) (fp5Rem (CommRingOps.mul y.poly z.poly))
    rw [← fp5Rem_add, LawfulCommRing.right_distrib])
  mul_assoc x y z := ext (by
    show fp5Rem (CommRingOps.mul (fp5Rem (CommRingOps.mul x.poly y.poly)) z.poly) =
      fp5Rem (CommRingOps.mul x.poly (fp5Rem (CommRingOps.mul y.poly z.poly)))
    rw [fp5Rem_mul_rem, LawfulCommRing.mul_comm x.poly (fp5Rem _), fp5Rem_mul_rem,
        LawfulCommRing.mul_comm _ x.poly, LawfulCommRing.mul_assoc])

/-- Constructive field inversion via extended Euclid `UPoly.xgcd fp5ModPoly a.poly`. -/
def inv (a : BlindVcFp5) : BlindVcFp5 :=
  if a = zero then zero
  else
    let res := UPoly.xgcd fp5ModPoly a.poly
    ofUPoly (CommRingOps.mul (UPoly.C (Goldilocks.inv res.1.lead)) res.2.2)

theorem mul_inv_cancel {a : BlindVcFp5} (ha : a ≠ CommRingOps.zero) :
    CommRingOps.mul a (inv a) = CommRingOps.one := by
  have haZ : a ≠ zero := ha
  unfold inv
  simp only [haZ, ↓reduceIte]
  have haPolyNe : a.poly ≠ CommRingOps.zero := fun hp => haZ (ext hp)
  obtain ⟨hbez, ⟨s, hs⟩, ⟨t, ht⟩⟩ := Poly2.xgcd_spec fp5ModPoly a.poly
  generalize UPoly.xgcd fp5ModPoly a.poly = res at hbez hs ht ⊢
  obtain ⟨g, u, v⟩ := res
  dsimp only at hbez hs ht ⊢
  have hgNe : g ≠ CommRingOps.zero := fun e => by
    rw [e, LawfulCommRing.zero_mul] at hs
    exact fp5ModPoly_ne_zero hs
  have htNe : t ≠ CommRingOps.zero := fun e => by
    rw [e, LawfulCommRing.mul_zero] at ht
    exact haPolyNe ht
  have haDegLe4 : a.poly.natDeg ≤ 4 := by
    have := a.len_lt; unfold UPoly.natDeg; omega
  have hgDegLe4 : g.natDeg ≤ 4 := by
    have hd := UPoly.natDeg_mul hgNe htNe
    rw [← ht] at hd
    omega
  have hsNe : s ≠ CommRingOps.zero := fun e => by
    rw [e, LawfulCommRing.mul_zero] at hs
    exact fp5ModPoly_ne_zero hs
  have hsDegPos : 1 ≤ s.natDeg := by
    have hd := UPoly.natDeg_mul hgNe hsNe
    rw [← hs, fp5ModPoly_natDeg] at hd
    omega
  have hgDeg0 : g.natDeg = 0 := by
    by_cases hg0 : g.natDeg = 0
    · exact hg0
    · exact False.elim (fp5ModPoly_irreducible g s hs (by omega) hsDegPos)
  have hgC : g = UPoly.C g.lead := Poly2.eq_C_lead_of_natDeg_zero hgDeg0
  have hLeadNe : g.lead ≠ CommRingOps.zero := UPoly.lead_ne_zero hgNe
  have hUnit : CommRingOps.mul (UPoly.C (Goldilocks.inv g.lead)) g = CommRingOps.one := by
    conv => lhs; arg 2; rw [hgC]
    rw [← UPoly.C_mul_eq, LawfulCommRing.mul_comm _ g.lead,
        Goldilocks.mul_inv_cancel hLeadNe, ← UPoly.one_eq_C]
  apply ext
  show fp5Rem (CommRingOps.mul a.poly
    (fp5Rem (CommRingOps.mul (UPoly.C (Goldilocks.inv g.lead)) v))) = CommRingOps.one
  rw [LawfulCommRing.mul_comm a.poly _, fp5Rem_mul_rem]
  have hBezScaled :
      CommRingOps.sub
        (CommRingOps.mul (CommRingOps.mul (UPoly.C (Goldilocks.inv g.lead)) v) a.poly)
        CommRingOps.one =
      CommRingOps.mul (CommRingOps.neg (CommRingOps.mul (UPoly.C (Goldilocks.inv g.lead)) u)) fp5ModPoly := by
    rw [← hUnit, ← hbez]
    have hId : ∀ (IL U G V A M : UPoly Goldilocks),
        CommRingOps.sub (CommRingOps.mul (CommRingOps.mul IL V) A) (CommRingOps.mul IL (CommRingOps.add (CommRingOps.mul U M) (CommRingOps.mul V A))) =
          CommRingOps.mul (CommRingOps.neg (CommRingOps.mul IL U)) M := fun IL U _ V A M => by
      rw [LawfulCommRing.left_distrib IL, LawfulCommRing.mul_assoc IL V A,
          LawfulCommRing.add_comm (CommRingOps.mul IL (CommRingOps.mul U M)) _,
          LawfulCommRing.sub_eq_add_neg, ring_neg_add,
          ← LawfulCommRing.add_assoc, LawfulCommRing.add_right_neg, LawfulCommRing.zero_add,
          ← LawfulCommRing.mul_assoc IL U M, ← ring_neg_mul_left]
    exact hId _ u g v a.poly fp5ModPoly
  rw [fp5Rem_congr_of_sub_dvd hBezScaled]
  have hOneLen : (CommRingOps.one : UPoly Goldilocks).coeffs.length < 6 := by
    rw [UPoly.one_eq_C]
    unfold UPoly.C
    have htr := trimPoly_length_le [(CommRingOps.one : Goldilocks)]
    have h1 : [(CommRingOps.one : Goldilocks)].length = 1 := rfl
    rw [UPoly.coeffs_ofList]
    omega
  exact fp5Rem_eq_self hOneLen

theorem zero_ne_one : (CommRingOps.zero : BlindVcFp5) ≠ CommRingOps.one := by
  intro h
  have hc := congrArg (fun x => coeffAt x.poly.coeffs 0) h
  have hz : zero.poly = CommRingOps.zero := rfl
  have ho : one.poly = CommRingOps.one := rfl
  change coeffAt zero.poly.coeffs 0 = coeffAt one.poly.coeffs 0 at hc
  rw [hz, ho, UPoly.coeffs_zero, coeffAt_nil, UPoly.one_eq_C, UPoly.coeffAt_C_zero] at hc
  exact absurd hc (by decide)

instance instLawfulField : LawfulField BlindVcFp5 where
  inv := inv
  zero_ne_one := zero_ne_one
  inv_zero := by
    show inv zero = zero
    unfold inv
    simp
  mul_inv_cancel := mul_inv_cancel

instance instNoZeroDivisors : NoZeroDivisors BlindVcFp5 :=
  LawfulField.toNoZeroDivisors BlindVcFp5

/-- Bijection between `BlindVcFp5` and the 5-limb wire carrier `CredentialFp5 = Fin 5 → Goldilocks`. -/
def toCredFp5 (x : BlindVcFp5) : CredentialFp5 :=
  fun i => coeffAt x.poly.coeffs i.val

def ofCredFp5 (f : CredentialFp5) : BlindVcFp5 :=
  ⟨UPoly.ofList [f 0, f 1, f 2, f 3, f 4], by
    have htr := trimPoly_length_le [f 0, f 1, f 2, f 3, f 4]
    have hL : [f 0, f 1, f 2, f 3, f 4].length = 5 := rfl
    rw [UPoly.coeffs_ofList]
    omega⟩

theorem toCredFp5_zero : toCredFp5 zero = credentialFp5Zero := by
  funext i
  unfold toCredFp5 zero
  rw [UPoly.coeffs_zero, coeffAt_nil, credentialFp5Zero_apply, goldilocks_zero_eq_cring]

theorem toCredFp5_injective {a b : BlindVcFp5} (h : toCredFp5 a = toCredFp5 b) : a = b := by
  apply ext; apply UPoly.ext_coeffAt; intro k
  if hk : k < 5 then
    exact congrFun h ⟨k, hk⟩
  else
    have ha0 : coeffAt a.poly.coeffs k = CommRingOps.zero :=
      a.poly.coeffAt_eq_zero_of_natDeg_lt (by have := a.len_lt; unfold UPoly.natDeg; omega)
    have hb0 : coeffAt b.poly.coeffs k = CommRingOps.zero :=
      b.poly.coeffAt_eq_zero_of_natDeg_lt (by have := b.len_lt; unfold UPoly.natDeg; omega)
    rw [ha0, hb0]

theorem toCredFp5_ofCredFp5 (f : CredentialFp5) : toCredFp5 (ofCredFp5 f) = f := by
  funext ⟨i, hi⟩
  unfold toCredFp5 ofCredFp5
  dsimp only
  rw [UPoly.coeffAt_ofList]
  match i, hi with
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl
  | _ + 5, hi => omega

theorem ofBase_coeff0 (c : Goldilocks) : coeffAt (ofBase c).poly.coeffs 0 = c := by
  have hLen : (UPoly.C c).coeffs.length < 6 := by
    have h := trimPoly_length_le [c]
    have h1 : [c].length = 1 := rfl
    unfold UPoly.C
    rw [UPoly.coeffs_ofList]
    omega
  change coeffAt (fp5Rem (UPoly.C c)).coeffs 0 = c
  rw [fp5Rem_eq_self hLen]
  exact UPoly.coeffAt_C_zero c

theorem ofBase_injective {a b : Goldilocks} (h : ofBase a = ofBase b) : a = b := by
  have h0 := congrArg (fun x => coeffAt x.poly.coeffs 0) h
  rwa [ofBase_coeff0, ofBase_coeff0] at h0

theorem ofBase_zero : ofBase Goldilocks.zero = zero := by
  apply ext
  show fp5Rem (UPoly.C Goldilocks.zero) = CommRingOps.zero
  rw [goldilocks_zero_eq_cring, UPoly.C_zero_eq]
  exact fp5Rem_eq_self (by rw [UPoly.coeffs_zero]; decide)

end BlindVcFp5

/-! ### Canonical Symbolic Enumerations of `GF(p^5)` (`allBlindVcFp5`) and `GF(p^5)^×` (`nonzeroBlindVcFp5`) -/

private theorem goldilocksPrime_pos : 0 < goldilocksPrime := by decide

private theorem mem_ofFn_exists {α : Type} :
    ∀ {m : Nat} (f : Fin m → α) {x : α}, x ∈ List.ofFn f → ∃ i : Fin m, f i = x
  | 0, _, _, h => nomatch h
  | m + 1, f, x, h => by
    rw [List.ofFn_succ] at h
    rcases List.mem_cons.mp h with rfl | hTail
    · exact ⟨⟨0, Nat.zero_lt_succ m⟩, rfl⟩
    · obtain ⟨j, hj⟩ := mem_ofFn_exists (fun i => f i.succ) hTail
      exact ⟨j.succ, hj⟩

private theorem nodup_ofFn_of_inj {α : Type} :
    ∀ {m : Nat} (f : Fin m → α), (∀ i j : Fin m, f i = f j → i = j) → (List.ofFn f).Nodup
  | 0, _, _ => .nil
  | m + 1, f, hInj => by
    rw [List.ofFn_succ]
    refine .cons ?_ (nodup_ofFn_of_inj (fun i => f i.succ) (fun i j hij => Fin.succ_inj.mp (hInj i.succ j.succ hij)))
    intro y hy hEq
    obtain ⟨j, rfl⟩ := mem_ofFn_exists (fun i => f i.succ) hy
    have hEq' : f ⟨0, Nat.zero_lt_succ m⟩ = f j.succ := hEq
    have h0 := hInj ⟨0, Nat.zero_lt_succ m⟩ j.succ hEq'
    exact absurd (congrArg Fin.val h0) (Nat.succ_ne_zero j.val).symm

/-- Base-`p` encoding of `idx < goldilocksPrime^5` as a canonical `BlindVcFp5` element (`0` choice). -/
def natToBlindVcFp5 (n : Nat) : BlindVcFp5 :=
  let p := goldilocksPrime
  let d0 : Goldilocks := ⟨n % p, Nat.mod_lt _ goldilocksPrime_pos⟩
  let d1 : Goldilocks := ⟨(n / p) % p, Nat.mod_lt _ goldilocksPrime_pos⟩
  let d2 : Goldilocks := ⟨(n / (p * p)) % p, Nat.mod_lt _ goldilocksPrime_pos⟩
  let d3 : Goldilocks := ⟨(n / (p * p * p)) % p, Nat.mod_lt _ goldilocksPrime_pos⟩
  let d4 : Goldilocks := ⟨(n / (p * p * p * p)) % p, Nat.mod_lt _ goldilocksPrime_pos⟩
  BlindVcFp5.ofCredFp5 (fun i =>
    match i.val with
    | 0 => d0 | 1 => d1 | 2 => d2 | 3 => d3 | _ => d4)

theorem natToBlindVcFp5_zero : natToBlindVcFp5 0 = BlindVcFp5.zero := by
  apply BlindVcFp5.toCredFp5_injective
  unfold natToBlindVcFp5
  dsimp only
  rw [BlindVcFp5.toCredFp5_ofCredFp5, BlindVcFp5.toCredFp5_zero]
  funext ⟨i, hi⟩
  rw [credentialFp5Zero_apply]
  have h0 : (⟨0 % goldilocksPrime, Nat.mod_lt 0 goldilocksPrime_pos⟩ : Goldilocks) = Goldilocks.zero := by
    apply Goldilocks.ext; decide
  match i, hi with
  | 0, _ => exact h0
  | 1, _ => exact h0
  | 2, _ => exact h0
  | 3, _ => exact h0
  | 4, _ => exact h0
  | _ + 5, hi => omega

theorem natToBlindVcFp5_injective_below {a b : Nat}
    (ha : a < goldilocksPrime ^ 5) (hb : b < goldilocksPrime ^ 5)
    (hEq : natToBlindVcFp5 a = natToBlindVcFp5 b) : a = b := by
  let p := goldilocksPrime
  have hp : 0 < p := goldilocksPrime_pos
  have hCred := congrArg BlindVcFp5.toCredFp5 hEq
  unfold natToBlindVcFp5 at hCred
  dsimp only at hCred
  rw [BlindVcFp5.toCredFp5_ofCredFp5, BlindVcFp5.toCredFp5_ofCredFp5] at hCred
  have hd0 := congrArg Goldilocks.val (congrFun hCred ⟨0, by decide⟩)
  have hd1 := congrArg Goldilocks.val (congrFun hCred ⟨1, by decide⟩)
  have hd2 := congrArg Goldilocks.val (congrFun hCred ⟨2, by decide⟩)
  have hd3 := congrArg Goldilocks.val (congrFun hCred ⟨3, by decide⟩)
  have hd4 := congrArg Goldilocks.val (congrFun hCred ⟨4, by decide⟩)
  dsimp only at hd0 hd1 hd2 hd3 hd4
  change a % p = b % p at hd0
  change (a / p) % p = (b / p) % p at hd1
  change (a / (p * p)) % p = (b / (p * p)) % p at hd2
  change (a / (p * p * p)) % p = (b / (p * p * p)) % p at hd3
  change (a / (p * p * p * p)) % p = (b / (p * p * p * p)) % p at hd4
  have hPow5 : p ^ 5 = p * (p * p * p * p) := by
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    ac_rfl
  have ha4Lt : a / (p * p * p * p) < p := by
    rw [Nat.div_lt_iff_lt_mul (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp hp) hp) hp), ← hPow5]
    exact ha
  have hb4Lt : b / (p * p * p * p) < p := by
    rw [Nat.div_lt_iff_lt_mul (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp hp) hp) hp), ← hPow5]
    exact hb
  rw [Nat.mod_eq_of_lt ha4Lt, Nat.mod_eq_of_lt hb4Lt] at hd4
  have hStep : ∀ x y : Nat, x / p = y / p → x % p = y % p → x = y := fun x y hq hr => by
    have hx := Nat.div_add_mod x p
    have hy := Nat.div_add_mod y p
    rw [hq, hr] at hx
    exact hx.symm.trans hy
  have hq3 : a / (p * p * p) = b / (p * p * p) := by
    apply hStep _ _ _ hd3
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
    exact hd4
  have hq2 : a / (p * p) = b / (p * p) := by
    apply hStep _ _ _ hd2
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
    exact hq3
  have hq1 : a / p = b / p := by
    apply hStep _ _ _ hd1
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
    exact hq2
  exact hStep a b hq1 hd0

/-- Symbolic duplicate-free list of all `p^5` elements of `BlindVcFp5`. -/
def allBlindVcFp5 : List BlindVcFp5 :=
  List.ofFn (fun i : Fin (goldilocksPrime ^ 5) => natToBlindVcFp5 i.val)

theorem allBlindVcFp5_length : allBlindVcFp5.length = goldilocksPrime ^ 5 :=
  List.length_ofFn

theorem allBlindVcFp5_nodup : allBlindVcFp5.Nodup :=
  nodup_ofFn_of_inj _ (fun i j hij => Fin.ext (natToBlindVcFp5_injective_below i.isLt j.isLt hij))

/-- Symbolic duplicate-free list of all `p^5 - 1 = fp5NonzeroCount` nonzero elements of `BlindVcFp5`. -/
def nonzeroBlindVcFp5 : List BlindVcFp5 :=
  List.ofFn (fun i : Fin CutAndChoose.fp5NonzeroCount => natToBlindVcFp5 (i.val + 1))

theorem nonzeroBlindVcFp5_length : nonzeroBlindVcFp5.length = CutAndChoose.fp5NonzeroCount :=
  List.length_ofFn

private theorem fp5NonzeroCount_succ_le : CutAndChoose.fp5NonzeroCount + 1 = goldilocksPrime ^ 5 := by
  rw [CutAndChoose.fp5NonzeroCount_eq]
  decide

theorem nonzeroBlindVcFp5_nodup : nonzeroBlindVcFp5.Nodup := by
  apply nodup_ofFn_of_inj
  intro i j hij
  have hiLt : i.val + 1 < goldilocksPrime ^ 5 := by
    have := i.isLt; have := fp5NonzeroCount_succ_le; omega
  have hjLt : j.val + 1 < goldilocksPrime ^ 5 := by
    have := j.isLt; have := fp5NonzeroCount_succ_le; omega
  exact Fin.ext (Nat.succ.inj (natToBlindVcFp5_injective_below hiLt hjLt hij))

/-! ## 5. Concrete `192 × 192` BlindVC Presentation `DefectChecker` & `AlgebraicSound` (`blind_vc.rs`) -/

/-- `SD_GRID_B = 192` (`blind_vc.rs:1717`). -/
@[expose] def SD_GRID_B : Nat := 192
/-- `SD_GRID_L = 192` (`blind_vc.rs:1718`). -/
@[expose] def SD_GRID_L : Nat := 192
/-- Total multiplication grid gates `192 × 192 = 36864` (`blind_vc.rs:2327`). -/
@[expose] def SD_GRID_GATES : Nat := SD_GRID_B * SD_GRID_L

/-- Folding luck bound for `dG = SD_GRID_GATES = 36864` over `GF(p^5)`:
    `36864 * 2^300 ≤ goldilocksPrime ^ 5` (`< 2^-300`). -/
theorem blindVc_grid_fold_luck :
    SD_GRID_GATES * 2 ^ 300 ≤ goldilocksPrime ^ 5 := by
  decide

private theorem limboEvalDegree_val : CutAndChoose.limboEvalDegree = 384 :=
  CutAndChoose.limboEvalDegree_eq

private theorem coeffAt_mem_of_lt_len {R : Type} [CommRingOps R] :
    ∀ (cs : List R) (k : Nat), k < cs.length → coeffAt cs k ∈ cs
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => .head _
  | _ :: tl, k + 1, h => .tail _ (coeffAt_mem_of_lt_len tl k (Nat.lt_of_succ_lt_succ h))

private theorem nodup_filter_local {α : Type} (p : α → Bool) :
    ∀ {l : List α}, l.Nodup → (l.filter p).Nodup
  | [], _ => .nil
  | _ :: _, .cons hrel htail => by
    simp only [List.filter]
    split
    · exact .cons (fun b hb => hrel b (List.mem_filter.mp hb).1) (nodup_filter_local p htail)
    · exact nodup_filter_local p htail

private theorem countIf_eq_filter_len {α : Type} (p : α → Bool) :
    ∀ (xs : List α), FrozenChallenge.countIf p xs = (xs.filter p).length
  | [] => rfl
  | x :: tl => by
    simp only [FrozenChallenge.countIf, List.filter]
    cases p x <;> simp [countIf_eq_filter_len p tl, Nat.add_comm]

/-- Root bound over `BlindVcFp5` from a single nonzero coefficient at `k < cs.length` via `gs_formal_root_bound`. -/
theorem blindVcFp5_roots_le_of_coeffAt_nonzero
    (d : Nat) (cs : List BlindVcFp5) (k : Nat)
    (hLen : cs.length ≤ d + 1) (hkLt : k < cs.length)
    (hkNe : coeffAt cs k ≠ CommRingOps.zero)
    (S : List BlindVcFp5) (hS : S.Nodup) :
    FrozenChallenge.countIf (fun r => decide (RoundPoly.evalCoeffs cs r = CommRingOps.zero)) S ≤ d := by
  rw [countIf_eq_filter_len]
  let p : BlindVcFp5 → Bool := fun r => decide (RoundPoly.evalCoeffs cs r = CommRingOps.zero)
  have hFiltNd : (S.filter p).Nodup := nodup_filter_local p hS
  have hFiltRoots : ∀ r ∈ S.filter p, RoundPoly.evalCoeffs cs r = CommRingOps.zero :=
    fun r hr => of_decide_eq_true (List.mem_filter.mp hr).2
  exact gs_formal_root_bound d cs (S.filter p) hLen
    ⟨coeffAt cs k, coeffAt_mem_of_lt_len cs k hkLt, hkNe⟩ hFiltNd hFiltRoots

/-- Committed Round-1 shares of all `256` parties across repetitions (`R1RepState` in `blind_vc.rs:3230`). -/
structure BlindVcCommittedProof where
  partyX : Nat → Fin credentialSdParties → Fin SD_GRID_GATES → Goldilocks
  partyY : Nat → Fin credentialSdParties → Fin SD_GRID_GATES → Goldilocks
  partyZ : Nat → Fin credentialSdParties → Fin SD_GRID_GATES → Goldilocks
  partyCPad : Nat → Fin credentialSdParties → BlindVcFp5
  partyRMask : Nat → Fin credentialSdParties → Fin CutAndChoose.limboEvalDegree → BlindVcFp5

/-- Round-2a prover message (`r_poly_without_b` of length `384 = 2 * SD_GRID_B`, degree `192` omitted!). -/
structure BlindVcR2aMsg where
  rPolyWithoutB : Nat → Fin CutAndChoose.limboEvalDegree → BlindVcFp5

/-- Round-2b prover message (online party broadcasts `(α_p, β_p, σ_p)` per repetition). -/
structure BlindVcR2bMsg where
  partySigma : Nat → Fin credentialSdParties → BlindVcFp5

/-- Sum a `Goldilocks` quantity across all `256` Limbo parties. -/
def sumAllPartiesGl (f : Fin credentialSdParties → Goldilocks) : Goldilocks :=
  (List.finRange credentialSdParties).foldl (fun acc p => CommRingOps.add acc (f p)) Goldilocks.zero

/-- Sum a `BlindVcFp5` quantity across all `256` Limbo parties (zero dependent `Prop` recursion). -/
def sumAllPartiesFp5 (f : Fin credentialSdParties → BlindVcFp5) : BlindVcFp5 :=
  (List.finRange credentialSdParties).foldl (fun acc p => CommRingOps.add acc (f p)) BlindVcFp5.zero

/-- Reconstructed gate defect `X_g * Y_g - Z_g` at gate `g < 36864` in repetition `j`. -/
def blindVcGateDefect (c : BlindVcCommittedProof) (j : Nat) (g : Fin SD_GRID_GATES) : Goldilocks :=
  let Xg := sumAllPartiesGl (fun p => c.partyX j p g)
  let Yg := sumAllPartiesGl (fun p => c.partyY j p g)
  let Zg := sumAllPartiesGl (fun p => c.partyZ j p g)
  CommRingOps.sub (CommRingOps.mul Xg Yg) Zg

/-- A committed Round-1 repetition `j` is false when at least one gate in the `192 × 192` grid has
    reconstructed `X_g * Y_g ≠ Z_g`. -/
def BlindVcRepHasGateFault (c : BlindVcCommittedProof) (j : Nat) : Prop :=
  ∃ g : Fin SD_GRID_GATES, blindVcGateDefect c j g ≠ Goldilocks.zero

/-- Folding polynomial coefficients of length `SD_GRID_GATES + 1 = 36865`. -/
def blindVcFoldCoeffs (c : BlindVcCommittedProof) (j : Nat) : List BlindVcFp5 :=
  sumAllPartiesFp5 (c.partyCPad j) ::
    List.ofFn (fun g : Fin SD_GRID_GATES => BlindVcFp5.ofBase (blindVcGateDefect c j g))

theorem blindVcFoldCoeffs_length (c : BlindVcCommittedProof) (j : Nat) :
    (blindVcFoldCoeffs c j).length = SD_GRID_GATES + 1 := by
  unfold blindVcFoldCoeffs
  rw [List.length_cons, List.length_ofFn]

private theorem coeffAt_ofFn_eq {m : Nat} (fn : Fin m → BlindVcFp5) (idx : Fin m) :
    coeffAt (List.ofFn fn) idx.val = fn idx := by
  obtain ⟨k, hlt⟩ := idx
  induction m generalizing k with
  | zero => omega
  | succ m ih =>
    cases k with
    | zero => simp [List.ofFn_succ, coeffAt_cons_zero]
    | succ k' =>
      simp only [List.ofFn_succ, coeffAt_cons_succ]
      exact ih (fun i => fn i.succ) k' (Nat.lt_of_succ_lt_succ hlt)

theorem blindVcFoldCoeffs_coeffAt_succ (c : BlindVcCommittedProof) (j : Nat) (g : Fin SD_GRID_GATES) :
    coeffAt (blindVcFoldCoeffs c j) (g.val + 1) = BlindVcFp5.ofBase (blindVcGateDefect c j g) := by
  unfold blindVcFoldCoeffs
  rw [coeffAt_cons_succ]
  exact coeffAt_ofFn_eq _ g

/-- Masked degree-`≤ 384` evaluation check polynomial coefficients (`blind_vc.rs:2623, 3444`):
    coefficient `192 = SD_GRID_B` is locked to `evalCoeffs (blindVcFoldCoeffs c j) γ`
    (because `r_poly_without_b` omits `X^{SD_GRID_B}`)! -/
def blindVcEvalDefectCoord (c : BlindVcCommittedProof) (j : Nat)
    (gamma : BlindVcFp5) (b1 : BlindVcR2aMsg) (d : Fin (CutAndChoose.limboEvalDegree + 1)) : BlindVcFp5 :=
  if hdLo : d.val < SD_GRID_B then
    let idx : Fin CutAndChoose.limboEvalDegree := ⟨d.val, by
      have h384 := limboEvalDegree_val
      have h192 : SD_GRID_B = 192 := rfl
      omega⟩
    CommRingOps.sub (sumAllPartiesFp5 (fun p => c.partyRMask j p idx)) (b1.rPolyWithoutB j idx)
  else if _ : d.val = SD_GRID_B then
    RoundPoly.evalCoeffs (blindVcFoldCoeffs c j) gamma
  else
    let idx : Fin CutAndChoose.limboEvalDegree := ⟨d.val - 1, by
      have := d.isLt
      have h384 := limboEvalDegree_val
      have h192 : SD_GRID_B = 192 := rfl
      omega⟩
    CommRingOps.sub (sumAllPartiesFp5 (fun p => c.partyRMask j p idx)) (b1.rPolyWithoutB j idx)

def blindVcEvalDefectCoeffs (c : BlindVcCommittedProof) (j : Nat)
    (gamma : BlindVcFp5) (b1 : BlindVcR2aMsg) : List BlindVcFp5 :=
  List.ofFn (blindVcEvalDefectCoord c j gamma b1)

theorem blindVcEvalDefectCoeffs_length (c : BlindVcCommittedProof) (j : Nat)
    (gamma : BlindVcFp5) (b1 : BlindVcR2aMsg) :
    (blindVcEvalDefectCoeffs c j gamma b1).length = CutAndChoose.limboEvalDegree + 1 :=
  List.length_ofFn

theorem blindVcEvalDefectCoeffs_coeffAt_B (c : BlindVcCommittedProof) (j : Nat)
    (gamma : BlindVcFp5) (b1 : BlindVcR2aMsg) :
    coeffAt (blindVcEvalDefectCoeffs c j gamma b1) SD_GRID_B =
      RoundPoly.evalCoeffs (blindVcFoldCoeffs c j) gamma := by
  have hLt : SD_GRID_B < CutAndChoose.limboEvalDegree + 1 := by
    rw [limboEvalDegree_val]; decide
  unfold blindVcEvalDefectCoeffs
  have h := coeffAt_ofFn_eq (blindVcEvalDefectCoord c j gamma b1) ⟨SD_GRID_B, hLt⟩
  dsimp only [blindVcEvalDefectCoord] at h
  simp only [Nat.lt_irrefl, ↓reduceDIte] at h
  exact h

/-- Honest per-party online evaluation share `σ_honest(p, r)` (`blind_vc.rs:4004-4005`). -/
def blindVcExpectedPartySigma (c : BlindVcCommittedProof) (j : Nat)
    (gamma : BlindVcFp5) (b1 : BlindVcR2aMsg) (r : BlindVcFp5)
    (b2 : BlindVcR2bMsg) (p : Fin credentialSdParties) : BlindVcFp5 :=
  let totalClaimed := sumAllPartiesFp5 (b2.partySigma j)
  let evalErr := RoundPoly.evalCoeffs (blindVcEvalDefectCoeffs c j gamma b1) r
  if p.val = 0 then
    CommRingOps.add (b2.partySigma j p) (CommRingOps.sub evalErr totalClaimed)
  else if p.val = 255 then
    CommRingOps.add (b2.partySigma j p) totalClaimed
  else
    b2.partySigma j p

/-- Concrete per-party check value in `CredentialFp5` for `CutAndChoose.DefectChecker`. -/
def blindVcPartyDefect (c : BlindVcCommittedProof) (j : Nat)
    (gamma : BlindVcFp5) (b1 : BlindVcR2aMsg) (r : BlindVcFp5)
    (b2 : BlindVcR2bMsg) (p : Fin credentialSdParties) : CredentialFp5 :=
  BlindVcFp5.toCredFp5 (CommRingOps.sub (blindVcExpectedPartySigma c j gamma b1 r b2 p) (b2.partySigma j p))

/-- Concrete `CutAndChoose.DefectChecker` on `BlindVcFp5` (`GF(p)[T]/(T^5 - 3)`), `192 × 192` grid,
    and `256` Limbo parties! -/
def blindVcRepetitionKernel :
    CutAndChoose.DefectChecker BlindVcCommittedProof BlindVcFp5 BlindVcR2aMsg BlindVcFp5 BlindVcR2bMsg where
  foldBad c j gamma :=
    decide (RoundPoly.evalCoeffs (blindVcFoldCoeffs c j) gamma = CommRingOps.zero)
  evalBad c j gamma b1 r :=
    decide (RoundPoly.evalCoeffs (blindVcEvalDefectCoeffs c j gamma b1) r = CommRingOps.zero)
  defect := blindVcPartyDefect

theorem blindVcPartyDefect_exists_nonzero_of_evalGood
    (c : BlindVcCommittedProof) (j : Nat) (gamma : BlindVcFp5)
    (b1 : BlindVcR2aMsg) (r : BlindVcFp5) (b2 : BlindVcR2bMsg)
    (hEvalNe : RoundPoly.evalCoeffs (blindVcEvalDefectCoeffs c j gamma b1) r ≠ CommRingOps.zero) :
    ∃ bad : Fin credentialSdParties, blindVcPartyDefect c j gamma b1 r b2 bad ≠ credentialFp5Zero := by
  let totalClaimed := sumAllPartiesFp5 (b2.partySigma j)
  let evalErr := RoundPoly.evalCoeffs (blindVcEvalDefectCoeffs c j gamma b1) r
  by_cases hTot : totalClaimed = CommRingOps.zero
  · let p0 : Fin credentialSdParties := ⟨0, by rw [credentialSdParties_eq]; decide⟩
    refine ⟨p0, fun hZero => ?_⟩
    have hDiff0 : CommRingOps.sub
        (blindVcExpectedPartySigma c j gamma b1 r b2 p0)
        (b2.partySigma j p0) = CommRingOps.zero := by
      apply BlindVcFp5.toCredFp5_injective
      change blindVcPartyDefect c j gamma b1 r b2 p0 = BlindVcFp5.toCredFp5 BlindVcFp5.zero
      rw [hZero, BlindVcFp5.toCredFp5_zero]
    have hExp0 : blindVcExpectedPartySigma c j gamma b1 r b2 p0 =
        CommRingOps.add (b2.partySigma j p0) (CommRingOps.sub evalErr totalClaimed) := rfl
    rw [hExp0] at hDiff0
    have hCancel : CommRingOps.sub
        (CommRingOps.add (b2.partySigma j p0) (CommRingOps.sub evalErr totalClaimed))
        (b2.partySigma j p0) = CommRingOps.sub evalErr totalClaimed :=
      ring_add_sub_cancel_left' _ _
    rw [hCancel, hTot, LawfulCommRing.sub_zero] at hDiff0
    exact hEvalNe hDiff0
  · let p255 : Fin credentialSdParties := ⟨255, by rw [credentialSdParties_eq]; decide⟩
    refine ⟨p255, fun hZero => ?_⟩
    have hDiff0 : CommRingOps.sub
        (blindVcExpectedPartySigma c j gamma b1 r b2 p255)
        (b2.partySigma j p255) = CommRingOps.zero := by
      apply BlindVcFp5.toCredFp5_injective
      change blindVcPartyDefect c j gamma b1 r b2 p255 = BlindVcFp5.toCredFp5 BlindVcFp5.zero
      rw [hZero, BlindVcFp5.toCredFp5_zero]
    have hExp255 : blindVcExpectedPartySigma c j gamma b1 r b2 p255 =
        CommRingOps.add (b2.partySigma j p255) totalClaimed := rfl
    rw [hExp255] at hDiff0
    have hCancel : CommRingOps.sub
        (CommRingOps.add (b2.partySigma j p255) totalClaimed)
        (b2.partySigma j p255) = totalClaimed :=
      ring_add_sub_cancel_left' _ _
    rw [hCancel] at hDiff0
    exact hTot hDiff0

/-- **Concrete `AlgebraicSound` on `GF(p^5) = GF(p)[T]/(T^5 - 3)` (`blindVcRepetitionKernel_algebraicSound`)**. -/
theorem blindVcRepetitionKernel_algebraicSound
    (c : BlindVcCommittedProof)
    (hFault : ∀ j : Nat, BlindVcRepHasGateFault c j)
    (Gs Rs : List BlindVcFp5) (hGs : Gs.Nodup) (hRs : Rs.Nodup) :
    blindVcRepetitionKernel.AlgebraicSound c Gs Rs SD_GRID_GATES CutAndChoose.limboEvalDegree where
  fold j := by
    obtain ⟨g, hgNe⟩ := hFault j
    have hCoeffNe : coeffAt (blindVcFoldCoeffs c j) (g.val + 1) ≠ CommRingOps.zero := by
      rw [blindVcFoldCoeffs_coeffAt_succ]
      intro h0
      apply hgNe
      apply BlindVcFp5.ofBase_injective
      have hz : BlindVcFp5.ofBase Goldilocks.zero = CommRingOps.zero := BlindVcFp5.ofBase_zero
      exact h0.trans hz.symm
    exact blindVcFp5_roots_le_of_coeffAt_nonzero
      SD_GRID_GATES (blindVcFoldCoeffs c j) (g.val + 1)
      (Nat.le_of_eq (blindVcFoldCoeffs_length c j))
      (by rw [blindVcFoldCoeffs_length]; exact Nat.succ_lt_succ g.isLt)
      hCoeffNe Gs hGs
  eval j gamma b1 hFoldOk := by
    have hFoldNe : RoundPoly.evalCoeffs (blindVcFoldCoeffs c j) gamma ≠ CommRingOps.zero :=
      of_decide_eq_false hFoldOk
    have hCoeffNe : coeffAt (blindVcEvalDefectCoeffs c j gamma b1) SD_GRID_B ≠ CommRingOps.zero := by
      rw [blindVcEvalDefectCoeffs_coeffAt_B]
      exact hFoldNe
    exact blindVcFp5_roots_le_of_coeffAt_nonzero
      CutAndChoose.limboEvalDegree (blindVcEvalDefectCoeffs c j gamma b1) SD_GRID_B
      (Nat.le_of_eq (blindVcEvalDefectCoeffs_length c j gamma b1))
      (by rw [blindVcEvalDefectCoeffs_length, limboEvalDegree_val]; decide)
      hCoeffNe Rs hRs
  nonzero j gamma b1 r b2 _ hEvalOk :=
    blindVcPartyDefect_exists_nonzero_of_evalGood c j gamma b1 r b2 (of_decide_eq_false hEvalOk)

/-- Concrete defect table indexed by `Fin 256` matching `credential_sd_opening_round_qrom_and_seed_tree_binding`. -/
def blindVcPartyDefect256 (c : BlindVcCommittedProof) (j : Nat)
    (gamma : BlindVcFp5) (b1 : BlindVcR2aMsg) (r : BlindVcFp5)
    (b2 : BlindVcR2bMsg) (p : Fin 256) : CredentialFp5 :=
  blindVcPartyDefect c j gamma b1 r b2 ⟨p.val, credentialSdParties_eq.symm ▸ p.isLt⟩

/-- Concrete doomed-point predicate for the 33-repetition QROM opening round on `GF(p^5)`. -/
def blindVcOpeningDoomed {cardX : Nat}
    (cAt : Fin cardX → BlindVcCommittedProof)
    (gammaAt : Fin cardX → Nat → BlindVcFp5)
    (b1At : Fin cardX → BlindVcR2aMsg)
    (rAt : Fin cardX → Nat → BlindVcFp5) (x : Fin cardX) : Bool :=
  (List.range 33).all (fun idx =>
    !blindVcRepetitionKernel.evalBad (cAt x) idx (gammaAt x idx) (b1At x) (rAt x idx))

/-- Discharges `hDefect` (`∀ x, doomed x = true → ∀ idx < 33, ∃ bad : Fin 256, defect x idx bad ≠ 0`)
    directly from the concrete `GF(p^5)` evaluation polynomial! -/
theorem blindVcOpeningDoomed_has_33_defects {cardX : Nat}
    (cAt : Fin cardX → BlindVcCommittedProof)
    (gammaAt : Fin cardX → Nat → BlindVcFp5)
    (b1At : Fin cardX → BlindVcR2aMsg)
    (rAt : Fin cardX → Nat → BlindVcFp5)
    (b2At : Fin cardX → BlindVcR2bMsg) :
    ∀ x : Fin cardX,
      blindVcOpeningDoomed cAt gammaAt b1At rAt x = true →
      ∀ idx < 33,
        ∃ bad : Fin 256,
          blindVcPartyDefect256 (cAt x) idx (gammaAt x idx) (b1At x) (rAt x idx) (b2At x) bad ≠
            credentialFp5Zero := by
  intro x hDoomed idx hIdxLt
  have hMem : idx ∈ List.range 33 := List.mem_range.mpr hIdxLt
  have hNotBad := List.all_eq_true.mp hDoomed idx hMem
  have hEvalFalse : blindVcRepetitionKernel.evalBad (cAt x) idx (gammaAt x idx) (b1At x) (rAt x idx) = false := by
    cases h : blindVcRepetitionKernel.evalBad (cAt x) idx (gammaAt x idx) (b1At x) (rAt x idx) with
    | false => rfl
    | true => rw [h] at hNotBad; cases hNotBad
  obtain ⟨bad, hBad⟩ := blindVcPartyDefect_exists_nonzero_of_evalGood
    (cAt x) idx (gammaAt x idx) (b1At x) (rAt x idx) (b2At x) (of_decide_eq_false hEvalFalse)
  refine ⟨⟨bad.val, credentialSdParties_eq ▸ bad.isLt⟩, ?_⟩
  unfold blindVcPartyDefect256
  have hFinEq : (⟨bad.val, _⟩ : Fin credentialSdParties) = bad := Fin.ext rfl
  rw [hFinEq]
  exact hBad

/-! ## 6. Concrete SPDZ TOPRF + `PiBlindVc` Protocol State Machine & Forward Simulations to `Spec.IdealCred` -/

/-- Concrete credential custody entry stored by the protocol machine (`PiBlindVc` root attestation + holder tag). -/
structure ConcreteCredEntry (Attr : Type) where
  credId : Nat
  holder : Nat
  attrs : List Attr
  epoch : Nat
  root : Spec.Digest256
  blindVcTag : BitVec 256
  deriving DecidableEq, Repr

/-- One sparse `GF(p^5)` party defect entry `(repIdx, partyIdx, c0..c4)` on the Limbo opening wire. -/
structure LimboDefectEntry where
  repIdx : Nat
  partyIdx : Nat
  c0 : Nat
  c1 : Nat
  c2 : Nat
  c3 : Nat
  c4 : Nat
  deriving DecidableEq, Repr

/-- Concrete 33-repetition `N = 256` Limbo GGM selective-disclosure opening bundle carried on
    `.presentWire`: `defectEntries` lists any nonzero `LimboDefectEntry` `GF(p^5)` check values
    across the 33 repetitions (`[]` for an honest zero-defect opening), and `challenge` is the
    packed base-`256` challenge integer checked by `credentialSdOpeningAccepts 33`. -/
structure LimboSdOpeningWire where
  defectEntries : List LimboDefectEntry
  challenge : Nat
  deriving DecidableEq, Repr

/-- Convert a `LimboDefectEntry` into `CredentialFp5` over `Goldilocks`. -/
def LimboDefectEntry.toCredFp5 (e : LimboDefectEntry) : CredentialFp5
  | ⟨0, _⟩ => Goldilocks.ofNat e.c0
  | ⟨1, _⟩ => Goldilocks.ofNat e.c1
  | ⟨2, _⟩ => Goldilocks.ofNat e.c2
  | ⟨3, _⟩ => Goldilocks.ofNat e.c3
  | ⟨_ + 4, _⟩ => Goldilocks.ofNat e.c4

/-- Reconstruct the `Nat → Fin 256 → CredentialFp5` defect table from `LimboSdOpeningWire`. -/
def LimboSdOpeningWire.defectTable (w : LimboSdOpeningWire) (idx : Nat) (p : Fin 256) :
    CredentialFp5 :=
  match w.defectEntries.find? (fun e => decide (e.repIdx = idx ∧ e.partyIdx = p.val)) with
  | some e => e.toCredFp5
  | none => credentialFp5Zero

/-- Execute the 33-repetition `N = 256` Limbo GGM selective-disclosure opening verifier. -/
def LimboSdOpeningWire.verify33 (w : LimboSdOpeningWire) : Bool :=
  credentialSdOpeningAccepts 33 w.defectTable w.challenge

/-- Honest zero-defect 33-repetition Limbo opening for challenge `ch`. -/
def LimboSdOpeningWire.honest (ch : Nat := 0) : LimboSdOpeningWire :=
  { defectEntries := [], challenge := ch }

theorem LimboSdOpeningWire.honest_verify33 (ch : Nat) :
    (LimboSdOpeningWire.honest ch).verify33 = true := by
  have hZero : (LimboSdOpeningWire.honest ch).defectTable = fun _ _ => credentialFp5Zero := by
    funext idx p
    rfl
  unfold LimboSdOpeningWire.verify33
  rw [hZero]
  exact credentialSdOpeningAccepts_zero 33 ch

/-- Concrete wire messages delivered on `(port : Spec.CredPort, wire : ToprfCredWire Attr)`. -/
inductive ToprfCredWire (Attr : Type) where
  | issueWire (holder : Nat) (attrs : List Attr) (newRoot : Spec.Digest256) (blindVcTag : BitVec 256)
  | advanceEpochWire (newEpoch : Nat) (newRoot : Spec.Digest256)
  | presentWire (holder : Nat) (credId : Nat) (stmt : Spec.CredentialStatement Attr)
      (opening : LimboSdOpeningWire)
  | issueChallengeWire (verifier : Nat) (scope : Spec.Bytes) (now ttl : Nat)
  | approveToprfWire (server : Nat) (ticket : Spec.ToprfTicket)
  | approveToprfStoreFault (server : Nat) (ticket : Spec.ToprfTicket)
  | evalToprfWire (ticket : Spec.ToprfTicket) (input : Spec.Bytes) (online : SpdzOnlineTranscript)
  | corruptWire (party : Spec.CredParty)
  deriving DecidableEq, Repr

/-- Extended concrete input including internal volatile `SpdzReservoir::prepare` turns (`visIn = none`). -/
inductive ToprfMachineInput (Attr : Type) where
  | external (port : Spec.CredPort) (wire : ToprfCredWire Attr)
  | prepareReservoir (preprocessSid : BitVec 256) (macKey : GoldilocksExt2) (items sessions : Nat)
  deriving DecidableEq, Repr

/-- Concrete protocol state combining `ToprfReservoir`, monotone server high-water marks, 3-phase
    audit counter `phaseAuditCount`, and `PiBlindVc` credential custody state. -/
structure PiToprfCredState (Attr O : Type) where
  spdzCfg : SpdzConfig
  reservoir : ToprfReservoir
  spdzMacKey : GoldilocksExt2
  retiredSids : List (BitVec 256)
  serverHighWater : List (Nat × Nat)
  phaseAuditCount : Nat
  issuerPk : Spec.Bytes
  epoch : Nat
  accumulatorRoot : Spec.Digest256
  issuedThisEpoch : Nat
  issuerCorrupt : Bool
  corruptHolders : List Nat
  corruptServers : List Nat
  entries : List (ConcreteCredEntry Attr)
  challengeLedgers : Spec.VerifierChallengeLedgers
  toprfApprovals : List (Nat × Spec.ToprfTicket)
  oprfTable : List (Spec.ToprfPoint × O)
  oprfCharges : List Spec.ToprfTicket

/-- Initial prepared `ToprfReservoir` (`MAX_BATCH = 64` items, `64` sessions, unpoisoned). -/
def initialToprfReservoir : ToprfReservoir :=
  { preprocessSid := 0x51534147_544f5052_465f5632#256
    pow7Cursor := 0
    pow7Total := 64 * SBOXES_PER_ITEM
    beaverCursor := 0
    beaverTotal := 64 * MASKS_PER_ITEM + 64 * TOPRF_LANES
    sessionsRemaining := 64
    poisoned := false }

/-- MAC key of the initial reservoir's preprocessing session. A fixed model value: secrecy of the
    key is not a property of this machine; `spdz_mac_check_unique_alpha_on_shift` is the statement
    about how many keys accept a shifted opening. -/
def initialSpdzMacKey : GoldilocksExt2 := GoldilocksExt2.ofBase (Goldilocks.ofNat 7)

/-- Initial concrete protocol state for `cfg : Spec.IdealCredConfig O`. -/
def PiToprfCredState.init {Attr O : Type} (cfg : Spec.IdealCredConfig O) : PiToprfCredState Attr O :=
  { spdzCfg := ⟨Spec.pqCredentialProfile.toprfThreshold, Spec.pqCredentialProfile.toprfServers⟩
    reservoir := initialToprfReservoir
    spdzMacKey := initialSpdzMacKey
    retiredSids := []
    serverHighWater := []
    phaseAuditCount := 0
    issuerPk := cfg.issuerPk
    epoch := cfg.epoch₀
    accumulatorRoot := cfg.root₀
    issuedThisEpoch := 0
    issuerCorrupt := cfg.issuerCorrupt
    corruptHolders := cfg.corruptHolders
    corruptServers := cfg.corruptServers
    entries := []
    challengeLedgers := fun verifier => { capacity := cfg.challengeCapacity verifier }
    toprfApprovals := []
    oprfTable := []
    oprfCharges := [] }

/-- Non-trivial abstraction map collapsing SPDZ reservoir cursors, `poisoned` flag, `serverHighWater`,
    `phaseAuditCount`, and `blindVcTag` onto `Spec.IdealCredState Attr O`! -/
def PiToprfCredState.abs {Attr O : Type} (c : PiToprfCredState Attr O) : Spec.IdealCredState Attr O :=
  { issuerPk := c.issuerPk
    epoch := c.epoch
    accumulatorRoot := c.accumulatorRoot
    issuedThisEpoch := c.issuedThisEpoch
    issuerCorrupt := c.issuerCorrupt
    corruptHolders := c.corruptHolders
    corruptServers := c.corruptServers
    records := c.entries.map (fun e => ⟨e.credId, e.holder, e.attrs, e.epoch, e.root⟩)
    challengeLedgers := c.challengeLedgers
    toprfApprovals := c.toprfApprovals
    oprfTable := c.oprfTable
    oprfCharges := c.oprfCharges }

/-- Extract the logical `Spec.CredCommand Attr` represented by a concrete wire message. -/
def ToprfCredWire.toCommand {Attr : Type} : ToprfCredWire Attr → Spec.CredCommand Attr
  | .issueWire h attrs newRoot _ => .issue h attrs newRoot
  | .advanceEpochWire newEpoch newRoot => .advanceEpoch newEpoch newRoot
  | .presentWire h cid stmt _ => .present h cid stmt
  | .issueChallengeWire verifier scope now ttl => .issueChallenge verifier scope now ttl
  | .approveToprfWire srv t => .approveToprf srv t
  | .approveToprfStoreFault srv t => .approveToprf srv t
  | .evalToprfWire t input _ => .evalToprf t input
  | .corruptWire party => .corrupt party

/-- Concrete caller-port authorization gate evaluated directly on `PiToprfCredState`. -/
def PiToprfCredState.checkCallerPort {Attr O : Type} (c : PiToprfCredState Attr O)
    (port : Spec.CredPort) : ToprfCredWire Attr → Bool
  | .issueWire _ _ _ _ => decide (port = .issuer) || (decide (port = .adversary) && c.issuerCorrupt)
  | .advanceEpochWire _ _ => decide (port = .issuer) || (decide (port = .adversary) && c.issuerCorrupt)
  | .presentWire h _ _ _ =>
    decide (port = .holder h) || (decide (port = .adversary) && decide (h ∈ c.corruptHolders))
  | .issueChallengeWire verifier _ _ _ => decide (port = .verifier verifier)
  | .approveToprfWire srv _ =>
    decide (port = .server srv) || (decide (port = .adversary) && decide (srv ∈ c.corruptServers))
  | .approveToprfStoreFault srv _ =>
    decide (port = .server srv) || (decide (port = .adversary) && decide (srv ∈ c.corruptServers))
  | .evalToprfWire _ _ _ => true
  | .corruptWire _ => decide (port = .adversary)

/-- Concrete issuance arity and accumulator-capacity check on `PiToprfCredState`. -/
def PiToprfCredState.checkIssueWire {Attr O : Type} (c : PiToprfCredState Attr O)
    (attrs : List Attr) : Bool :=
  decide (0 < attrs.length) &&
  decide (attrs.length ≤ Spec.pqCredentialProfile.maxAttrs) &&
  decide (c.issuedThisEpoch < 2 ^ Spec.pqCredentialProfile.accumulatorDepth)

/-- Concrete credential custody lookup over `c.entries` (`ConcreteCredEntry`). -/
def PiToprfCredState.hasMatchingEntry {Attr O : Type} [DecidableEq Attr]
    (c : PiToprfCredState Attr O) (h cid : Nat) (stmt : Spec.CredentialStatement Attr) : Bool :=
  c.entries.any (fun e =>
    decide (e.credId = cid) && decide (e.holder = h) && decide (e.epoch = c.epoch) &&
      Spec.CredentialMatchesAttributes stmt e.attrs)

/-- Concrete selective-disclosure statement & challenge-replay check on `PiToprfCredState`. -/
def PiToprfCredState.checkPresentation {Attr O : Type} [DecidableEq Attr]
    (c : PiToprfCredState Attr O) (h cid : Nat) (stmt : Spec.CredentialStatement Attr) : Bool :=
  decide (stmt.issuerPk = c.issuerPk) &&
  decide (stmt.epoch = c.epoch) &&
  decide (stmt.accumulatorRoot = c.accumulatorRoot) &&
  (c.challengeLedgers stmt.verifier).accepts stmt.verifierScope stmt.challengeNonce stmt.verificationTime &&
  c.hasMatchingEntry h cid stmt

/-- Concrete committee quorum count of distinct server approvals in `c.toprfApprovals`. -/
def PiToprfCredState.quorumApprovalCount {Attr O : Type} (c : PiToprfCredState Attr O)
    (t : Spec.ToprfTicket) : Nat :=
  (List.range Spec.pqCredentialProfile.toprfServers).countP
    (fun i => decide ((i, t) ∈ c.toprfApprovals))

/-- Concrete TOPRF ticket quorum, epoch, per-key quota, and `admit_counter` window check (`voprf.rs:310`). -/
def PiToprfCredState.checkToprfTicket {Attr O : Type} (c : PiToprfCredState Attr O)
    (cfg : Spec.IdealCredConfig O) (t : Spec.ToprfTicket) : Bool :=
  decide (Spec.pqCredentialProfile.toprfOnlineServers ≤ c.quorumApprovalCount t) &&
  decide (t.epoch = c.epoch) &&
  decide (c.oprfCharges.countP (fun ch => decide (ch.keyId = t.keyId)) < cfg.oprfQuota) &&
  c.oprfCharges.all (fun ch => !decide (ch.keyId = t.keyId) || decide (ch.counter < t.counter)) &&
  (c.oprfCharges.any (fun ch => decide (ch.keyId = t.keyId) &&
      decide (t.counter ≤ ch.counter + Spec.pqCredentialProfile.toprfCounterWindow)) ||
    (!c.oprfCharges.any (fun ch => decide (ch.keyId = t.keyId)) &&
      decide (t.counter < Spec.pqCredentialProfile.toprfCounterWindow))) &&
  decide (t.counter < 18446744073709551615)

/-- Concrete wire transition executing protocol state validation directly on `PiToprfCredState`
    (never calling `Spec.credExec` or `c.abs`):
    * caller port check (`c.checkCallerPort`),
    * issuance arity & accumulator capacity (`c.checkIssueWire`),
    * 33-repetition `N = 256` Limbo GGM opening verification (`opening.verify33`) + concrete
      custody entry & challenge freshness (`c.checkPresentation`),
    * counter-store high-water ratchet (`serverHighWater`) even on partial I/O failure (`ioOk = false`), and
    * direct TOPRF quorum/window check (`c.checkToprfTicket`) + SPDZ `ToprfReservoir` upfront cursor
      reservation (`c.reservoir.reserveSession 1`) + 3-phase MAC check (`evaluatePreparedSpdzSession`),
      burning one session on `Refusal.request` or poisoning the entire reservoir on `Refusal.quorum`! -/
def piToprfCredWireOutcome {Attr O : Type} [DecidableEq Attr] (cfg : Spec.IdealCredConfig O)
    (c : PiToprfCredState Attr O) (port : Spec.CredPort) (w : ToprfCredWire Attr) :
    StepOutcome (PiToprfCredState Attr O) (Spec.IdealCredOutput O) Unit :=
  if !c.checkCallerPort port w then
    .err { c with phaseAuditCount := c.phaseAuditCount + 1 } ()
  else
    match w with
    | .issueWire h attrs newRoot tag =>
      if c.checkIssueWire attrs then
        let cid := c.entries.length
        .ok { c with
              entries := c.entries ++ [⟨cid, h, attrs, c.epoch, newRoot, tag⟩]
              accumulatorRoot := newRoot
              issuedThisEpoch := c.issuedThisEpoch + 1
              phaseAuditCount := c.phaseAuditCount + 1 }
            (.issued cid)
      else
        .err { c with phaseAuditCount := c.phaseAuditCount + 1 } ()
    | .advanceEpochWire newEpoch newRoot =>
      if decide (c.epoch < newEpoch) then
        .ok { c with
              epoch := newEpoch
              accumulatorRoot := newRoot
              issuedThisEpoch := 0
              phaseAuditCount := c.phaseAuditCount + 1 }
            (.epochAdvanced newEpoch)
      else
        .err { c with phaseAuditCount := c.phaseAuditCount + 1 } ()
    | .presentWire h cid stmt opening =>
      if !opening.verify33 then
        .err { c with phaseAuditCount := c.phaseAuditCount + 1 } ()
      else if c.checkPresentation h cid stmt then
        .ok { c with
              challengeLedgers := c.challengeLedgers.consume stmt.verifier stmt.verifierScope stmt.challengeNonce
              phaseAuditCount := c.phaseAuditCount + 1 }
            (.presentationVerdict true)
      else
        .ok { c with phaseAuditCount := c.phaseAuditCount + 1 }
            (.presentationVerdict false)
    | .issueChallengeWire verifier scope now ttl =>
      let attempt := (c.challengeLedgers verifier).issueAttempt scope now ttl
      .ok { c with challengeLedgers := c.challengeLedgers.set verifier attempt.1
                   phaseAuditCount := c.phaseAuditCount + 1 } (Spec.challengeIssueOutput attempt.2)
    | .approveToprfStoreFault srv t =>
      .err { c with
             serverHighWater := (srv, t.counter) :: c.serverHighWater
             phaseAuditCount := c.phaseAuditCount + 1 } ()
    | .approveToprfWire srv t =>
      if decide (srv < Spec.pqCredentialProfile.toprfServers) && decide (t.epoch = c.epoch) then
        .ok { c with
              toprfApprovals := (srv, t) :: c.toprfApprovals
              serverHighWater := (srv, t.counter) :: c.serverHighWater
              phaseAuditCount := c.phaseAuditCount + 1 }
            .toprfApproved
      else
        .err { c with
               serverHighWater := (srv, t.counter) :: c.serverHighWater
               phaseAuditCount := c.phaseAuditCount + 1 } ()
    | .evalToprfWire t input online =>
      if !c.checkToprfTicket cfg t then
        .err { c with phaseAuditCount := c.phaseAuditCount + 1 } ()
      else
        match c.reservoir.reserveSession 1 with
        | none => .err { c with phaseAuditCount := c.phaseAuditCount + 1 } ()
        | some resReserved =>
          match evaluatePreparedSpdzSession resReserved (online.checks c.spdzMacKey t) with
          | .err resAfter _ =>
            .err { c with
                   reservoir := resAfter
                   phaseAuditCount := c.phaseAuditCount + 3 } ()
          | .ok resOk () =>
            let pt : Spec.ToprfPoint := ⟨t.keyId, t.epoch, input⟩
            match c.oprfTable.find? (fun e => decide (e.1 = pt)) with
            | some e =>
              .ok { c with
                    reservoir := resOk
                    oprfCharges := t :: c.oprfCharges
                    phaseAuditCount := c.phaseAuditCount + 3 }
                  (.toprfEvaluated e.2)
            | none =>
              let val := cfg.oprf pt
              .ok { c with
                    reservoir := resOk
                    oprfCharges := t :: c.oprfCharges
                    oprfTable := (pt, val) :: c.oprfTable
                    phaseAuditCount := c.phaseAuditCount + 3 }
                  (.toprfEvaluated val)
    | .corruptWire party =>
      match party with
      | .issuer =>
        .ok { c with issuerCorrupt := true, phaseAuditCount := c.phaseAuditCount + 1 } .corrupted
      | .holder h =>
        .ok { c with corruptHolders := h :: c.corruptHolders, phaseAuditCount := c.phaseAuditCount + 1 }
            .corrupted
      | .server i =>
        .ok { c with corruptServers := i :: c.corruptServers, phaseAuditCount := c.phaseAuditCount + 1 }
            .corrupted

/-- Port-facing concrete SPDZ TOPRF + `PiBlindVc` service (`Spec.Machine` over `CredPort × ToprfCredWire Attr`).
    Used directly to inhabit `Top.CredentialImplementation`! -/
def piToprfCredService {Attr O : Type} [DecidableEq Attr] (cfg : Spec.IdealCredConfig O) :
    Spec.Machine (PiToprfCredState Attr O) (Spec.CredPort × ToprfCredWire Attr) (Spec.IdealCredOutput O) where
  Init c := c = PiToprfCredState.init cfg
  step c inp :=
    match piToprfCredWireOutcome cfg c inp.1 inp.2 with
    | .ok c' out => some (c', out)
    | .err _ _ => none
  errStep c inp :=
    match piToprfCredWireOutcome cfg c inp.1 inp.2 with
    | .ok c' _ => c'
    | .err c' _ => c'

/-- Full concrete machine including internal `SpdzReservoir::prepare` stuttering transitions (`visIn = none`). -/
def piToprfCredMachine {Attr O : Type} [DecidableEq Attr] (cfg : Spec.IdealCredConfig O) :
    Spec.Machine (PiToprfCredState Attr O) (ToprfMachineInput Attr) (Option (Spec.IdealCredOutput O)) where
  Init c := c = PiToprfCredState.init cfg
  step c inp :=
    match inp with
    | .external port w =>
      match piToprfCredWireOutcome cfg c port w with
      | .ok c' out => some (c', some out)
      | .err _ _ => none
    | .prepareReservoir sid macKey items sessions =>
      if sid ≠ c.reservoir.preprocessSid ∧ sid ∉ c.retiredSids then
        match ToprfReservoir.prepare sid items sessions with
        | some freshRes =>
          some ({ c with
                  reservoir := freshRes
                  spdzMacKey := macKey
                  retiredSids := c.reservoir.preprocessSid :: c.retiredSids
                  phaseAuditCount := c.phaseAuditCount + 1 }, none)
        | none => none
      else none
  errStep c inp :=
    match inp with
    | .external port w => (piToprfCredService cfg).errStep c (port, w)
    | .prepareReservoir _ _ _ _ => c

/-- Visible input projection for `DataRefines`: `.prepareReservoir` is erased (`none`), `.external` maps
    `(port, w)` to `some (port, w.toCommand)`. -/
def toprfMachineVisIn {Attr : Type} : ToprfMachineInput Attr → Option (Spec.IdealCredInput Attr)
  | .external port w => some (port, w.toCommand)
  | .prepareReservoir _ _ _ _ => none

def toprfMachineVisOut {O : Type} (defaultOut : Spec.IdealCredOutput O) :
    Option (Spec.IdealCredOutput O) → Spec.IdealCredOutput O
  | some out => out
  | none => defaultOut

/-- Non-injectivity of `PiToprfCredState.abs`: distinct concrete states (differing in `pow7Cursor`,
    `beaverCursor`, `poisoned`, `serverHighWater`, `phaseAuditCount`, or `blindVcTag`) map to the
    exact same `IdealCredState`, proving the simulation relation is NOT an identity wrapper! -/
theorem piToprfCredState_abs_non_injective {Attr O : Type} (cfg : Spec.IdealCredConfig O) :
    ∃ c₁ c₂ : PiToprfCredState Attr O,
      c₁ ≠ c₂ ∧ c₁.reservoir ≠ c₂.reservoir ∧ c₁.abs = c₂.abs := by
  let c₁ := PiToprfCredState.init (Attr := Attr) cfg
  let c₂ := { c₁ with reservoir := c₁.reservoir.poison, phaseAuditCount := 99 }
  have hFalseNeTrue : false ≠ true := by decide
  refine ⟨c₁, c₂, ?_, ?_, rfl⟩
  · intro h
    exact hFalseNeTrue (congrArg (fun s => s.reservoir.poisoned) h)
  · intro h
    exact hFalseNeTrue (congrArg ToprfReservoir.poisoned h)

theorem piToprfCredService_init_abs {Attr O : Type} [DecidableEq Attr] (cfg : Spec.IdealCredConfig O)
    {c₀ : PiToprfCredState Attr O} (hInit : (piToprfCredService cfg).Init c₀) :
    c₀.abs = Spec.IdealCredState.empty cfg := by
  have hEq : c₀ = PiToprfCredState.init cfg := hInit
  subst hEq
  rfl

private theorem checkCallerPort_eq_speaksFor {Attr O : Type}
    (c : PiToprfCredState Attr O) (port : Spec.CredPort) (w : ToprfCredWire Attr) :
    c.checkCallerPort port w = c.abs.speaksFor port w.toCommand := by
  cases w <;> rfl

private theorem checkIssueWire_eq_issueAccepts {Attr O : Type}
    (c : PiToprfCredState Attr O) (attrs : List Attr) :
    c.checkIssueWire attrs = c.abs.issueAccepts attrs := by
  rw [Spec.IdealCredState.issueAccepts_eq]
  rfl

private theorem hasMatchingEntry_eq_eligible {Attr O : Type} [DecidableEq Attr]
    (c : PiToprfCredState Attr O) (h cid : Nat) (stmt : Spec.CredentialStatement Attr) :
    c.hasMatchingEntry h cid stmt = c.abs.eligible h cid stmt := by
  rw [Spec.IdealCredState.eligible_eq]
  unfold PiToprfCredState.hasMatchingEntry PiToprfCredState.abs
  dsimp only
  rw [List.any_map]
  rfl

private theorem checkPresentation_eq_presentAccepts {Attr O : Type} [DecidableEq Attr]
    (c : PiToprfCredState Attr O) (h cid : Nat) (stmt : Spec.CredentialStatement Attr) :
    c.checkPresentation h cid stmt = c.abs.presentAccepts h cid stmt := by
  rw [Spec.IdealCredState.presentAccepts_eq, ← hasMatchingEntry_eq_eligible]
  rfl

private theorem checkToprfTicket_eq_toprfAccepts {Attr O : Type}
    (c : PiToprfCredState Attr O) (cfg : Spec.IdealCredConfig O) (t : Spec.ToprfTicket) :
    c.checkToprfTicket cfg t = c.abs.toprfAccepts cfg t := by
  rw [Spec.IdealCredState.toprfAccepts_eq, Spec.IdealCredState.approvalCount_eq]
  rfl

theorem piToprfCredWireOutcome_sound {Attr O : Type} [DecidableEq Attr]
    (cfg : Spec.IdealCredConfig O) (c : PiToprfCredState Attr O)
    (port : Spec.CredPort) (w : ToprfCredWire Attr) :
    match piToprfCredWireOutcome cfg c port w with
    | .ok c' out =>
      (Spec.idealCredMachine cfg).step c.abs (port, w.toCommand) = some (c'.abs, out)
    | .err c' () =>
      c'.abs = c.abs := by
  unfold piToprfCredWireOutcome
  rw [checkCallerPort_eq_speaksFor]
  cases hSp : c.abs.speaksFor port w.toCommand with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    rfl
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    have hStepEq : (Spec.idealCredMachine cfg).step c.abs (port, w.toCommand) =
        Spec.credExec cfg c.abs w.toCommand :=
      Spec.idealCredStep_of_speaksFor hSp
    cases w with
    | issueChallengeWire verifier scope now ttl =>
      dsimp only [ToprfCredWire.toCommand] at hStepEq ⊢
      rw [hStepEq, Spec.credExec_issueChallenge_eq]
      rfl
    | issueWire h attrs newRoot tag =>
      dsimp only [ToprfCredWire.toCommand] at hStepEq ⊢
      rw [checkIssueWire_eq_issueAccepts]
      cases hIss : c.abs.issueAccepts attrs with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rfl
      | true =>
        simp only [↓reduceIte]
        rw [hStepEq, Spec.credExec_issue_eq, hIss]
        simp only [↓reduceIte, PiToprfCredState.abs, List.map_append, List.map_cons,
          List.map_nil, List.length_map]
    | advanceEpochWire newEpoch newRoot =>
      dsimp only [ToprfCredWire.toCommand] at hStepEq ⊢
      have hEpEq : c.epoch = c.abs.epoch := rfl
      rw [hEpEq]
      cases hAdv : decide (c.abs.epoch < newEpoch) with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rfl
      | true =>
        simp only [↓reduceIte]
        rw [hStepEq, Spec.credExec_advanceEpoch_eq, hAdv]
        rfl
    | presentWire h cid stmt opening =>
      dsimp only [ToprfCredWire.toCommand] at hStepEq ⊢
      cases opening.verify33 with
      | false =>
        simp only [Bool.not_false, ↓reduceIte]
        rfl
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        rw [checkPresentation_eq_presentAccepts, hStepEq, Spec.credExec_present_eq]
        cases c.abs.presentAccepts h cid stmt <;>
          simp only [↓reduceIte, Bool.false_eq_true, PiToprfCredState.abs]
    | approveToprfStoreFault srv t => rfl
    | approveToprfWire srv t =>
      dsimp only [ToprfCredWire.toCommand] at hStepEq ⊢
      have hEpEq : c.epoch = c.abs.epoch := rfl
      rw [hEpEq]
      cases hApp : (decide (srv < Spec.pqCredentialProfile.toprfServers) &&
          decide (t.epoch = c.abs.epoch)) with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rfl
      | true =>
        simp only [↓reduceIte]
        rw [hStepEq, Spec.credExec_approveToprf_eq, hApp]
        rfl
    | evalToprfWire t input online =>
      dsimp only [ToprfCredWire.toCommand] at hStepEq ⊢
      rw [checkToprfTicket_eq_toprfAccepts]
      cases hAcc : c.abs.toprfAccepts cfg t with
      | false =>
        simp only [Bool.not_false, ↓reduceIte]
        rfl
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases hRes : c.reservoir.reserveSession 1 with
        | none => rfl
        | some resReserved =>
          dsimp only
          cases hEv : evaluatePreparedSpdzSession resReserved (online.checks c.spdzMacKey t) with
          | err resAfter _ => rfl
          | ok resOk u =>
            cases u
            dsimp only
            rw [hStepEq, Spec.credExec_evalToprf_eq, hAcc]
            simp only [↓reduceIte]
            have hTblEq : c.oprfTable = c.abs.oprfTable := rfl
            rw [hTblEq]
            cases c.abs.oprfTable.find? (fun e => decide (e.1 = ⟨t.keyId, t.epoch, input⟩)) <;> rfl
    | corruptWire party =>
      dsimp only [ToprfCredWire.toCommand] at hStepEq ⊢
      have hSpAdv : port = .adversary := by
        dsimp only [Spec.IdealCredState.speaksFor] at hSp
        exact of_decide_eq_true hSp
      subst hSpAdv
      cases party <;> (dsimp only; exact Spec.idealCredStep_corrupt_eq cfg c.abs _)

/-- **Stuttering Forward Simulation (`piToprfCredMachine_dataRefines_idealCred`)**:
    `piToprfCredMachine cfg` refines `Spec.idealCredMachine cfg` via `Spec.DataRefines`, collapsing
    internal `SpdzReservoir::prepare` turns (`visIn = none`), monotone cursor advances, `Refusal.request`
    reservation burns, and `Refusal.quorum` reservoir poisonings onto `Spec.idealCredMachine cfg`! -/
def piToprfCredMachine_dataRefines_idealCred {Attr O : Type} [DecidableEq Attr]
    (cfg : Spec.IdealCredConfig O) :
    Spec.DataRefines (piToprfCredMachine (Attr := Attr) cfg) (Spec.idealCredMachine cfg)
      toprfMachineVisIn (toprfMachineVisOut .corrupted) where
  Rel c a := c.abs = a
  absInit c₀ := c₀.abs
  init_ok {c₀} hInit := by
    have hEq : c₀ = PiToprfCredState.init cfg := hInit
    subst hEq
    exact ⟨rfl, rfl⟩
  sim_visible {c c' a inp out j} hRel hStepC hVis := by
    subst hRel
    cases inp with
    | prepareReservoir _ _ _ _ => cases hVis
    | external port w =>
      injection hVis with hJ
      subst hJ
      dsimp only [piToprfCredMachine] at hStepC
      have hSound := piToprfCredWireOutcome_sound cfg c port w
      cases hOut : piToprfCredWireOutcome cfg c port w with
      | err _ _ => rw [hOut] at hStepC; cases hStepC
      | ok cNext v =>
        rw [hOut] at hStepC hSound
        injection hStepC with hPair
        obtain ⟨hC, hO⟩ := Prod.mk.inj hPair
        subst hC; subst hO
        exact ⟨cNext.abs, hSound, rfl⟩
  sim_internal {c c' a inp out} hRel hStepC hVis := by
    subst hRel
    cases inp with
    | external _ _ => cases hVis
    | prepareReservoir sid macKey items sessions =>
      dsimp only [piToprfCredMachine] at hStepC
      split at hStepC
      · cases hPrep : ToprfReservoir.prepare sid items sessions with
        | none => rw [hPrep] at hStepC; cases hStepC
        | some freshRes =>
          rw [hPrep] at hStepC
          injection hStepC with hPair
          obtain ⟨hC, _⟩ := Prod.mk.inj hPair
          subst hC
          rfl
      · cases hStepC
  sim_reject {c a inp} hRel hNoneC := by
    subst hRel
    cases inp with
    | prepareReservoir _ _ _ _ => rfl
    | external port w =>
      dsimp only [piToprfCredMachine, piToprfCredService] at hNoneC ⊢
      have hSound := piToprfCredWireOutcome_sound cfg c port w
      cases hOut : piToprfCredWireOutcome cfg c port w with
      | ok cNext v => rw [hOut] at hNoneC; cases hNoneC
      | err cNext u =>
        cases u
        rw [hOut] at hSound
        exact hSound

/-- Monotone SPDZ reservoir progression relation across concrete wire turns: the preprocessing
    session is the same one, cursors never decrease, remaining session quota never increases, and
    quorum poisoning is sticky. -/
def ReservoirStepMonotone (r r' : ToprfReservoir) : Prop :=
  r'.preprocessSid = r.preprocessSid ∧
  r.pow7Cursor ≤ r'.pow7Cursor ∧
  r.beaverCursor ≤ r'.beaverCursor ∧
  r'.sessionsRemaining ≤ r.sessionsRemaining ∧
  (r.poisoned = true → r'.poisoned = true)

private theorem reservoirStepMonotone_refl (r : ToprfReservoir) : ReservoirStepMonotone r r :=
  ⟨rfl, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, id⟩

private theorem reservoirStepMonotone_of_reserve_eval {r rRes rAfter : ToprfReservoir}
    {online : SpdzOnlineChecks}
    (hRes : r.reserveSession 1 = some rRes)
    (hEv : (∃ u, evaluatePreparedSpdzSession rRes online = .ok rAfter u) ∨
           (∃ reason, evaluatePreparedSpdzSession rRes online = .err rAfter reason)) :
    ReservoirStepMonotone r rAfter := by
  have hNotPois : r.poisoned = false := by
    unfold ToprfReservoir.reserveSession at hRes
    dsimp only at hRes
    cases hp : r.poisoned with
    | false => rfl
    | true => rw [hp] at hRes; simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hRes; cases hRes
  have hSid : rRes.preprocessSid = r.preprocessSid := by
    unfold ToprfReservoir.reserveSession at hRes
    dsimp only at hRes
    split at hRes
    · injection hRes with hEq
      subst hEq
      rfl
    · cases hRes
  have hBounds : r.pow7Cursor ≤ rRes.pow7Cursor ∧ rRes.pow7Cursor ≤ rRes.pow7Total ∧
      r.beaverCursor ≤ rRes.beaverCursor ∧ rRes.beaverCursor ≤ rRes.beaverTotal ∧
      rRes.sessionsRemaining ≤ r.sessionsRemaining := by
    unfold ToprfReservoir.reserveSession at hRes
    dsimp only at hRes
    split at hRes
    · rename_i hCond
      injection hRes with hEq
      subst hEq
      obtain ⟨hRest, hBeav⟩ := Bool.and_eq_true_iff.mp hCond
      obtain ⟨_, hPow7⟩ := Bool.and_eq_true_iff.mp hRest
      have hp7 := of_decide_eq_true hPow7
      have hb7 := of_decide_eq_true hBeav
      unfold SBOXES_PER_ITEM at hp7 ⊢
      unfold MASKS_PER_ITEM TOPRF_LANES at hb7 ⊢
      dsimp only
      refine ⟨by omega, by omega, by omega, by omega, by omega⟩
    · cases hRes
  have hPoisMono : ReservoirStepMonotone r rRes.poison :=
    ⟨hSid, Nat.le_trans hBounds.1 hBounds.2.1,
     Nat.le_trans hBounds.2.2.1 hBounds.2.2.2.1,
     Nat.zero_le _,
     fun hp => by rw [hNotPois] at hp; cases hp⟩
  have hIdMono : ReservoirStepMonotone r rRes :=
    ⟨hSid, hBounds.1, hBounds.2.2.1, hBounds.2.2.2.2, fun hp => by rw [hNotPois] at hp; cases hp⟩
  have hEvCases : rAfter = rRes ∨ rAfter = rRes.poison := by
    unfold evaluatePreparedSpdzSession at hEv
    rcases online with ⟨b0, b1, b2, b3, b4, b5, b6⟩
    dsimp only at hEv
    cases b0
    · rcases hEv with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h <;> exact Or.inl rfl
    · cases b1
      · rcases hEv with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h <;> exact Or.inl rfl
      · cases b2
        · rcases hEv with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h <;> exact Or.inr rfl
        · cases b3
          · rcases hEv with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h <;> exact Or.inl rfl
          · cases b4
            · rcases hEv with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h <;> exact Or.inr rfl
            · cases b5
              · rcases hEv with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h <;> exact Or.inr rfl
              · cases b6 <;> (rcases hEv with ⟨_, h⟩ | ⟨_, h⟩ <;> cases h <;>
                  first | exact Or.inl rfl | exact Or.inr rfl)
  rcases hEvCases with rfl | rfl
  · exact hIdMono
  · exact hPoisMono

/-- Closes a leaf of `piToprfCredWireOutcome_session_step`; `simp only` may already have reduced
    the two ledger equations to `True`. -/
local macro "session_step_close " t:term : tactic =>
  `(tactic| first
    | exact And.intro $t ⟨rfl, rfl⟩
    | exact And.intro $t ⟨trivial, trivial⟩)

/-- One wire step, accepted or rejected: the reservoir moves monotonically inside its session and
    the session ledger (retired identifiers, MAC key) is untouched. -/
private theorem piToprfCredWireOutcome_session_step {Attr O : Type} [DecidableEq Attr]
    (cfg : Spec.IdealCredConfig O) (c : PiToprfCredState Attr O)
    (port : Spec.CredPort) (w : ToprfCredWire Attr) :
    match piToprfCredWireOutcome cfg c port w with
    | .ok c' _ => ReservoirStepMonotone c.reservoir c'.reservoir ∧
        c'.retiredSids = c.retiredSids ∧ c'.spdzMacKey = c.spdzMacKey
    | .err c' _ => ReservoirStepMonotone c.reservoir c'.reservoir ∧
        c'.retiredSids = c.retiredSids ∧ c'.spdzMacKey = c.spdzMacKey := by
  unfold piToprfCredWireOutcome
  cases c.checkCallerPort port w with
  | false =>
    simp only [Bool.not_false, ↓reduceIte]
    session_step_close (reservoirStepMonotone_refl c.reservoir)
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases w with
    | issueChallengeWire verifier scope now ttl =>
      session_step_close (reservoirStepMonotone_refl c.reservoir)
    | issueWire h attrs newRoot tag =>
      dsimp only
      cases c.checkIssueWire attrs <;>
        (simp only [Bool.false_eq_true, ↓reduceIte]; session_step_close (reservoirStepMonotone_refl c.reservoir))
    | advanceEpochWire newEpoch newRoot =>
      dsimp only
      cases decide (c.epoch < newEpoch) <;>
        (simp only [Bool.false_eq_true, ↓reduceIte]; session_step_close (reservoirStepMonotone_refl c.reservoir))
    | presentWire h cid stmt opening =>
      dsimp only
      cases opening.verify33 with
      | false =>
        simp only [Bool.not_false, ↓reduceIte]
        session_step_close (reservoirStepMonotone_refl c.reservoir)
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases c.checkPresentation h cid stmt <;>
          (simp only [Bool.false_eq_true, ↓reduceIte]; session_step_close (reservoirStepMonotone_refl c.reservoir))
    | approveToprfStoreFault srv t => session_step_close (reservoirStepMonotone_refl c.reservoir)
    | approveToprfWire srv t =>
      dsimp only
      cases (decide (srv < Spec.pqCredentialProfile.toprfServers) && decide (t.epoch = c.epoch)) <;>
        (simp only [Bool.false_eq_true, ↓reduceIte]; session_step_close (reservoirStepMonotone_refl c.reservoir))
    | evalToprfWire t input online =>
      dsimp only
      cases c.checkToprfTicket cfg t with
      | false =>
        simp only [Bool.not_false, ↓reduceIte]
        session_step_close (reservoirStepMonotone_refl c.reservoir)
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases hRes : c.reservoir.reserveSession 1 with
        | none => session_step_close (reservoirStepMonotone_refl c.reservoir)
        | some resReserved =>
          dsimp only
          cases hEv : evaluatePreparedSpdzSession resReserved (online.checks c.spdzMacKey t) with
          | err resAfter reason =>
            session_step_close (reservoirStepMonotone_of_reserve_eval hRes (Or.inr ⟨reason, hEv⟩))
          | ok resOk u =>
            cases u
            dsimp only
            have hM := reservoirStepMonotone_of_reserve_eval hRes (Or.inl ⟨(), hEv⟩)
            cases c.oprfTable.find? (fun e => decide (e.1 = ⟨t.keyId, t.epoch, input⟩)) <;> session_step_close hM
    | corruptWire party =>
      dsimp only
      cases party <;> session_step_close (reservoirStepMonotone_refl c.reservoir)

/-- **Multi-Turn SPDZ Reservoir Monotonicity (`piToprfCredService_reservoir_monotone`)**:
    Every wire step of `piToprfCredService` (whether accepted via `.step` or rejected via `.errStep`)
    preserves `ReservoirStepMonotone`: `c.reservoir` is **never** reset to `initialToprfReservoir`,
    its `pow7Cursor` and `beaverCursor` only advance, `sessionsRemaining` only decreases, and
    quorum poisoning (`poisoned = true`) is irreversible across external wire turns! -/
theorem piToprfCredService_reservoir_monotone {Attr O : Type} [DecidableEq Attr]
    (cfg : Spec.IdealCredConfig O) (c : PiToprfCredState Attr O)
    (port : Spec.CredPort) (w : ToprfCredWire Attr) :
    ReservoirStepMonotone c.reservoir ((piToprfCredService cfg).errStep c (port, w)).reservoir ∧
    ∀ c' out, (piToprfCredService cfg).step c (port, w) = some (c', out) →
      ReservoirStepMonotone c.reservoir c'.reservoir := by
  have hOutMono := piToprfCredWireOutcome_session_step cfg c port w
  dsimp only [piToprfCredService]
  cases hOut : piToprfCredWireOutcome cfg c port w with
  | err cErr _ =>
    rw [hOut] at hOutMono
    exact ⟨hOutMono.1, fun _ _ hS => nomatch hS⟩
  | ok cOk v =>
    rw [hOut] at hOutMono
    refine ⟨hOutMono.1, fun c' out hS => ?_⟩
    injection hS with hPair
    obtain ⟨hC, _⟩ := Prod.mk.inj hPair
    subst hC
    exact hOutMono.1

/-- Forged 33-repetition Limbo opening carrying a nonzero `GF(p^5)` defect (`(1, 0, 0, 0, 0)`) on
    opened party `1` under challenge `0` (where hidden party in repetition `0` is `0 ≠ 1`). -/
def forgedLimboSdOpeningWire : LimboSdOpeningWire :=
  { defectEntries := [⟨0, 1, 1, 0, 0, 0, 0⟩], challenge := 0 }

/-- **`#tooth` Forged Limbo Selective-Disclosure Opening Rejected (`tooth_forged_limbo_opening_rejected_by_piToprfCredService`)**:
    `piToprfCredService` executes `LimboSdOpeningWire.verify33` (`credentialSdOpeningAccepts 33`)
    before consulting custody eligibility, deterministically rejecting (`= none`) any presentation
    wire whose opened Limbo party has a nonzero `GF(p^5)` gate/sigma defect! -/
theorem tooth_forged_limbo_opening_rejected_by_piToprfCredService {Attr O : Type} [DecidableEq Attr]
    (cfg : Spec.IdealCredConfig O) (c : PiToprfCredState Attr O)
    (port : Spec.CredPort) (h cid : Nat) (stmt : Spec.CredentialStatement Attr) :
    (piToprfCredService cfg).step c (port, .presentWire h cid stmt forgedLimboSdOpeningWire) = none := by
  have hBad : forgedLimboSdOpeningWire.defectTable 0 ⟨1, by decide⟩ ≠ credentialFp5Zero := by
    intro hZero
    rw [← BlindVcFp5.toCredFp5_zero] at hZero
    have hAt0 := congrFun hZero ⟨0, by decide⟩
    have hVal : forgedLimboSdOpeningWire.defectTable 0 ⟨1, by decide⟩ ⟨0, by decide⟩ = Goldilocks.ofNat 1 := rfl
    have hZVal : (BlindVcFp5.toCredFp5 BlindVcFp5.zero) ⟨0, by decide⟩ = Goldilocks.zero := rfl
    rw [hVal, hZVal] at hAt0
    exact (by decide : Goldilocks.ofNat 1 ≠ Goldilocks.zero) hAt0
  have hVerFalse : forgedLimboSdOpeningWire.verify33 = false :=
    credentialSdOpeningAccepts_false_of_opened_defect (by decide : 0 < 33) hBad (by decide)
  dsimp only [piToprfCredService]
  unfold piToprfCredWireOutcome
  cases c.checkCallerPort port (.presentWire h cid stmt forgedLimboSdOpeningWire) with
  | false => rfl
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hVerFalse, Bool.not_false]

/-- Invalid cryptographic openings never consume a verifier challenge, including on the
    concrete error-state path (which still advances its public phase audit counter). -/
theorem piToprfCred_invalid_opening_preserves_challenges {Attr O : Type} [DecidableEq Attr]
    (cfg : Spec.IdealCredConfig O) (c : PiToprfCredState Attr O)
    (port : Spec.CredPort) (h cid : Nat) (stmt : Spec.CredentialStatement Attr)
    (opening : LimboSdOpeningWire) (hv : opening.verify33 = false) :
    match piToprfCredWireOutcome cfg c port (.presentWire h cid stmt opening) with
    | .ok c' _ => c'.challengeLedgers = c.challengeLedgers
    | .err c' _ => c'.challengeLedgers = c.challengeLedgers := by
  unfold piToprfCredWireOutcome
  cases c.checkCallerPort port (.presentWire h cid stmt opening) with
  | false => rfl
  | true => simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hv, Bool.not_false]

/-- **An accepted TOPRF evaluation passed every check on the wire data.** If `piToprfCredService`
    accepts `.evalToprfWire t input online`, then the transcript's context is the granted ticket,
    its request word is canonical, all three openings satisfy the SPDZ MAC equation under the MAC
    key held in the machine state, the opened dual-copy difference is zero and the two output
    copies agree. The released value itself is `cfg.oprf` at the ticket's point: this machine
    models the gate around the SPDZ arithmetic, and does not recompute the PRF from shares. -/
theorem piToprfCredService_eval_accept_checks {Attr O : Type} [DecidableEq Attr]
    (cfg : Spec.IdealCredConfig O) (c c' : PiToprfCredState Attr O) (port : Spec.CredPort)
    (t : Spec.ToprfTicket) (input : Spec.Bytes) (online : SpdzOnlineTranscript)
    (out : Spec.IdealCredOutput O)
    (hStep : (piToprfCredService cfg).step c (port, .evalToprfWire t input online) =
      some (c', out)) :
    online.context = t ∧ online.requestWord < goldilocksPrime ∧
    online.inputBind.val = Goldilocks.zero ∧
    online.inputBind.mac =
      CommRingOps.mul c.spdzMacKey (GoldilocksExt2.ofBase online.inputBind.val) ∧
    online.circuit.mac = CommRingOps.mul c.spdzMacKey (GoldilocksExt2.ofBase online.circuit.val) ∧
    online.output.mac = CommRingOps.mul c.spdzMacKey (GoldilocksExt2.ofBase online.output.val) ∧
    online.outputCopyA = online.outputCopyB := by
  dsimp only [piToprfCredService] at hStep
  unfold piToprfCredWireOutcome at hStep
  cases hPort : c.checkCallerPort port (.evalToprfWire t input online) with
  | false =>
    rw [hPort] at hStep
    simp only [Bool.not_false, ↓reduceIte] at hStep
    cases hStep
  | true =>
    rw [hPort] at hStep
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep
    cases hTk : c.checkToprfTicket cfg t with
    | false =>
      rw [hTk] at hStep
      simp only [Bool.not_false, ↓reduceIte] at hStep
      cases hStep
    | true =>
      rw [hTk] at hStep
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hStep
      cases hRes : c.reservoir.reserveSession 1 with
      | none => rw [hRes] at hStep; cases hStep
      | some resReserved =>
        rw [hRes] at hStep
        dsimp only at hStep
        cases hEv : evaluatePreparedSpdzSession resReserved (online.checks c.spdzMacKey t) with
        | err resAfter reason => rw [hEv] at hStep; cases hStep
        | ok resOk u =>
          have hAll := (evaluatePreparedSpdzSession_ok_all_checks _ _ _ _ hEv).1
          have h0 : decide (online.context = t) = true :=
            congrArg SpdzOnlineChecks.contextMatchesGrant hAll
          have h1 : decide (online.requestWord < goldilocksPrime) = true :=
            congrArg SpdzOnlineChecks.canonicalDiffs hAll
          have h2 : spdzMacCheckAccepts c.spdzMacKey online.inputBind.val online.inputBind.mac =
              true := congrArg SpdzOnlineChecks.phase1MacOk hAll
          have h3 : decide (online.inputBind.val = Goldilocks.zero) = true :=
            congrArg SpdzOnlineChecks.phase1DiffZero hAll
          have h4 : spdzMacCheckAccepts c.spdzMacKey online.circuit.val online.circuit.mac =
              true := congrArg SpdzOnlineChecks.phase2MacOk hAll
          have h5 : spdzMacCheckAccepts c.spdzMacKey online.output.val online.output.mac =
              true := congrArg SpdzOnlineChecks.phase3MacOk hAll
          have h6 : decide (online.outputCopyA = online.outputCopyB) = true :=
            congrArg SpdzOnlineChecks.clientDualPadConsistent hAll
          unfold spdzMacCheckAccepts at h2 h4 h5
          exact ⟨of_decide_eq_true h0, of_decide_eq_true h1, of_decide_eq_true h3,
            of_decide_eq_true h2, of_decide_eq_true h4, of_decide_eq_true h5,
            of_decide_eq_true h6⟩

/-- Wire steps never touch the preprocessing-session ledger: the retired session identifiers and
    the session MAC key are those of the state before the step, accepted or rejected. -/
theorem piToprfCredWireOutcome_keeps_session_ledger {Attr O : Type} [DecidableEq Attr]
    (cfg : Spec.IdealCredConfig O) (c : PiToprfCredState Attr O)
    (port : Spec.CredPort) (w : ToprfCredWire Attr) :
    match piToprfCredWireOutcome cfg c port w with
    | .ok c' _ => c'.retiredSids = c.retiredSids ∧ c'.spdzMacKey = c.spdzMacKey
    | .err c' _ => c'.retiredSids = c.retiredSids ∧ c'.spdzMacKey = c.spdzMacKey := by
  have h := piToprfCredWireOutcome_session_step cfg c port w
  cases hOut : piToprfCredWireOutcome cfg c port w with
  | ok cNext v => rw [hOut] at h; exact h.2
  | err cNext u => rw [hOut] at h; exact h.2

/-- **The full machine never rewinds a preprocessing session.** Every accepted step of
    `piToprfCredMachine` either keeps the session (same `preprocessSid`, cursors only advance,
    session quota only drops, poisoning sticky, ledger untouched), or is a `prepareReservoir` turn
    that installs a session identifier different from the current one and from every retired one,
    and retires the current one. A retired or current identifier is therefore never installed
    again, so no tuple position of a session is ever handed out twice. -/
theorem piToprfCredMachine_reservoir_never_rewinds {Attr O : Type} [DecidableEq Attr]
    (cfg : Spec.IdealCredConfig O) (c c' : PiToprfCredState Attr O)
    (inp : ToprfMachineInput Attr) (out : Option (Spec.IdealCredOutput O))
    (hStep : (piToprfCredMachine cfg).step c inp = some (c', out)) :
    (ReservoirStepMonotone c.reservoir c'.reservoir ∧ c'.retiredSids = c.retiredSids ∧
      c'.spdzMacKey = c.spdzMacKey) ∨
    (c'.reservoir.preprocessSid ≠ c.reservoir.preprocessSid ∧
      c'.reservoir.preprocessSid ∉ c.retiredSids ∧
      c'.retiredSids = c.reservoir.preprocessSid :: c.retiredSids ∧
      c'.reservoir.pow7Cursor = 0 ∧ c'.reservoir.beaverCursor = 0) := by
  cases inp with
  | external port w =>
    dsimp only [piToprfCredMachine] at hStep
    have hMono := (piToprfCredService_reservoir_monotone cfg c port w).2
    have hLedger := piToprfCredWireOutcome_keeps_session_ledger cfg c port w
    dsimp only [piToprfCredService] at hMono
    cases hOut : piToprfCredWireOutcome cfg c port w with
    | err _ _ => rw [hOut] at hStep; cases hStep
    | ok cNext v =>
      rw [hOut] at hStep hMono hLedger
      injection hStep with hPair
      obtain ⟨hC, _⟩ := Prod.mk.inj hPair
      subst hC
      exact .inl (And.intro (hMono cNext v rfl) ⟨hLedger.1, hLedger.2⟩)
  | prepareReservoir sid macKey items sessions =>
    dsimp only [piToprfCredMachine] at hStep
    split at hStep
    · rename_i hFresh
      cases hPrep : ToprfReservoir.prepare sid items sessions with
      | none => rw [hPrep] at hStep; cases hStep
      | some freshRes =>
        rw [hPrep] at hStep
        injection hStep with hPair
        obtain ⟨hC, _⟩ := Prod.mk.inj hPair
        subst hC
        have hSid : freshRes.preprocessSid = sid ∧ freshRes.pow7Cursor = 0 ∧
            freshRes.beaverCursor = 0 := by
          unfold ToprfReservoir.prepare at hPrep
          split at hPrep
          · injection hPrep with hEq
            subst hEq
            exact ⟨rfl, rfl, rfl⟩
          · cases hPrep
        dsimp only
        rw [hSid.1]
        exact .inr ⟨hFresh.1, hFresh.2, rfl, hSid.2.1, hSid.2.2⟩
    · cases hStep

/-- A circuit-phase opening whose value was shifted by one while keeping the MAC of the true
    value, inside an otherwise authentic transcript. -/
def forgedCircuitTranscript (grant : Spec.ToprfTicket) : SpdzOnlineTranscript :=
  { SpdzOnlineTranscript.honest initialSpdzMacKey grant (Goldilocks.ofNat 5) with
    circuit := ⟨Goldilocks.ofNat 6,
      CommRingOps.mul initialSpdzMacKey (GoldilocksExt2.ofBase (Goldilocks.ofNat 5))⟩ }

/-- The authentic transcript passes the gate computed from its data. -/
theorem honest_transcript_passes_spdz_gate (alpha : GoldilocksExt2) (grant : Spec.ToprfTicket)
    (y : Goldilocks) (r : ToprfReservoir) :
    evaluatePreparedSpdzSession r
      ((SpdzOnlineTranscript.honest alpha grant y).checks alpha grant) = .ok r () := by
  rw [SpdzOnlineTranscript.honest_checks]
  rfl

/-- The shifted circuit opening fails the MAC equation computed by the machine: the gate refuses
    with `.quorum 2` and poisons the reservoir. No field of the transcript says so. -/
theorem forged_circuit_opening_poisons_reservoir (grant : Spec.ToprfTicket) :
    evaluatePreparedSpdzSession initialToprfReservoir
        ((forgedCircuitTranscript grant).checks initialSpdzMacKey grant) =
      .err initialToprfReservoir.poison (.quorum 2) := by
  have hBad : decide (CommRingOps.mul initialSpdzMacKey (GoldilocksExt2.ofBase (Goldilocks.ofNat 5)) =
      CommRingOps.mul initialSpdzMacKey (GoldilocksExt2.ofBase (Goldilocks.ofNat 6))) = false := by
    decide
  have hp : decide ((0 : Nat) < goldilocksPrime) = true := by decide
  have hChecks : (forgedCircuitTranscript grant).checks initialSpdzMacKey grant =
      ⟨true, true, true, true, false, true, true⟩ :=
    SpdzOnlineChecks.eq_of_fields (decide_eq_true rfl) hp (decide_eq_true rfl)
      (decide_eq_true rfl) hBad (decide_eq_true rfl) (decide_eq_true rfl)
  rw [hChecks]
  rfl

/-- `#tooth` The gate does not release on the shifted circuit opening. -/
theorem tooth_forged_circuit_opening_not_released (grant : Spec.ToprfTicket) :
    ¬ (evaluatePreparedSpdzSession initialToprfReservoir
        ((forgedCircuitTranscript grant).checks initialSpdzMacKey grant) =
      .ok initialToprfReservoir ()) := by
  rw [forged_circuit_opening_poisons_reservoir]
  intro h
  cases h

/-- `#tooth` A `prepareReservoir` turn naming the current preprocessing session is refused: the
    cursors of a session cannot be reset by preparing it again. -/
theorem tooth_reprepare_same_session_refused {Attr O : Type} [DecidableEq Attr]
    (cfg : Spec.IdealCredConfig O) (c : PiToprfCredState Attr O) (macKey : GoldilocksExt2)
    (items sessions : Nat) :
    (piToprfCredMachine cfg).step c
      (.prepareReservoir c.reservoir.preprocessSid macKey items sessions) = none := by
  dsimp only [piToprfCredMachine]
  rw [ite_eq_right (fun h => absurd rfl h.1)]

/-! ## 7. `#tooth` Mutation Guards for `ToprfMachine` -/

/-- Mutant evaluation gate that skips the Phase-2 (`"toprf_spdz_circuit"`) MAC check! -/
def evaluatePreparedWithoutCircuitMac (afterReserve : ToprfReservoir)
    (tr : SpdzOnlineChecks) : StepOutcome ToprfReservoir Unit ToprfRefusal :=
  evaluatePreparedSpdzSession afterReserve { tr with phase2MacOk := true }

/-- `#tooth` Skipping the Phase-2 `"toprf_spdz_circuit"` MAC check accepts a forged S-box opening
    transcript and leaves the compromised reservoir unpoisoned, whereas `evaluatePreparedSpdzSession`
    rejects with `.quorum 2` and poisons the entire reservoir! -/
theorem tooth_skipping_phase2_mac_check_releases_unauthenticated_output :
    ∃ (r : ToprfReservoir) (tr : SpdzOnlineChecks),
      tr.phase2MacOk = false ∧
      evaluatePreparedWithoutCircuitMac r tr = .ok r () ∧
      evaluatePreparedSpdzSession r tr = .err r.poison (.quorum 2) ∧
      r.poison.poisoned = true := by
  refine ⟨initialToprfReservoir, { SpdzOnlineChecks.honest with phase2MacOk := false },
    rfl, rfl, rfl, rfl⟩

/-- Mutant reservoir reservation that forgets to advance `pow7Cursor` and `beaverCursor`! -/
def reserveSessionWithoutCursorAdvance (r : ToprfReservoir) (_items : Nat) : Option ToprfReservoir :=
  if !r.poisoned && decide (1 ≤ r.sessionsRemaining) then
    some { r with sessionsRemaining := r.sessionsRemaining - 1 }
  else none

/-- `#tooth` Omitting the monotone cursor advance allows exhausting more items than `pow7Total`
    (reusing spent S-box power-7 masks across evaluations), whereas `ToprfReservoir.reserveSession`
    strictly advances `pow7Cursor` and rejects once the `118`-tuple budget is spent! -/
theorem tooth_omitting_cursor_advance_reuses_pow7_tuples :
    ∃ r₀ r₁ : ToprfReservoir,
      ToprfReservoir.prepare 0#256 1 1 = some r₀ ∧
      r₀.reserveSession 1 = some r₁ ∧
      r₁.remainingPow7 = 0 ∧
      (reserveSessionWithoutCursorAdvance { r₀ with sessionsRemaining := 2 } 1).bind
        (fun s => reserveSessionWithoutCursorAdvance s 1) ≠ none ∧
      ({ r₀ with sessionsRemaining := 2 }.reserveSession 1).bind
        (fun s => s.reserveSession 1) = none := by
  have hPrep : ToprfReservoir.prepare 0#256 1 1 =
      some ⟨0#256, 0, 118, 0, 20, 1, false⟩ := by
    unfold ToprfReservoir.prepare
    decide
  have hRes1 : ToprfReservoir.reserveSession ⟨0#256, 0, 118, 0, 20, 1, false⟩ 1 =
      some ⟨0#256, 118, 118, 20, 20, 0, false⟩ := by
    unfold ToprfReservoir.reserveSession
    decide
  have hMut : (reserveSessionWithoutCursorAdvance ⟨0#256, 0, 118, 0, 20, 2, false⟩ 1).bind
      (fun s => reserveSessionWithoutCursorAdvance s 1) =
      some ⟨0#256, 0, 118, 0, 20, 0, false⟩ := rfl
  have hHon : (ToprfReservoir.reserveSession ⟨0#256, 0, 118, 0, 20, 2, false⟩ 1).bind
      (fun s => s.reserveSession 1) = none := by
    have hFirst : ToprfReservoir.reserveSession ⟨0#256, 0, 118, 0, 20, 2, false⟩ 1 =
        some ⟨0#256, 118, 118, 20, 20, 1, false⟩ := by
      unfold ToprfReservoir.reserveSession; decide
    rw [hFirst]
    dsimp only [Option.bind]
    unfold ToprfReservoir.reserveSession
    decide
  exact ⟨⟨0#256, 0, 118, 0, 20, 1, false⟩, ⟨0#256, 118, 118, 20, 20, 0, false⟩,
    hPrep, hRes1, rfl, (by rw [hMut]; intro h; cases h), hHon⟩

/-- `#tooth` A sub-threshold quorum (`quorum.length < cfg.threshold`) can consist 100% of corrupt
    servers even when total corruptions are strictly below `cfg.threshold`, refuting quorum honesty! -/
theorem tooth_below_threshold_quorum_all_corrupt :
    ∃ (cfg : SpdzConfig) (quorum corruptServers : List Nat),
      cfg.Valid = true ∧
      quorum.Nodup ∧
      (∀ i ∈ quorum, i < cfg.servers) ∧
      quorum.length < cfg.threshold ∧
      (List.range cfg.servers).countP (fun i => decide (i ∈ corruptServers)) < cfg.threshold ∧
      ¬ (∃ i ∈ quorum, i ∉ corruptServers) := by
  refine ⟨⟨3, 5⟩, [0, 1], [0, 1], by decide, by decide, by decide, by decide, by decide, ?_⟩
  decide

/-! ## 8. Exported Equational & Inhabitedness Witnesses for Downstream Top/Tests Modules -/

theorem piToprfCredService_accept_ok {Attr O : Type} [DecidableEq Attr]
    (cfg : Spec.IdealCredConfig O)
    {c c' : PiToprfCredState Attr O} {sender : Spec.CredPort}
    {w : ToprfCredWire Attr} {out : Spec.IdealCredOutput O}
    (hStep : (piToprfCredService cfg).step c (sender, w) = some (c', out)) :
    (Spec.idealCredMachine cfg).step c.abs (sender, w.toCommand) = some (c'.abs, out) := by
  dsimp only [piToprfCredService] at hStep
  have hSound := piToprfCredWireOutcome_sound cfg c sender w
  cases hOut : piToprfCredWireOutcome cfg c sender w with
  | err _ _ => rw [hOut] at hStep; cases hStep
  | ok cNext v =>
    rw [hOut] at hStep hSound
    injection hStep with hPair
    obtain ⟨hC, hV⟩ := Prod.mk.inj hPair
    subst hC; subst hV
    exact hSound

theorem piToprfCredService_reject_ok {Attr O : Type} [DecidableEq Attr]
    (cfg : Spec.IdealCredConfig O)
    {c : PiToprfCredState Attr O} {sender : Spec.CredPort} {w : ToprfCredWire Attr}
    (hNone : (piToprfCredService cfg).step c (sender, w) = none) :
    ((piToprfCredService cfg).errStep c (sender, w)).abs = c.abs := by
  dsimp only [piToprfCredService] at hNone ⊢
  have hSound := piToprfCredWireOutcome_sound cfg c sender w
  cases hOut : piToprfCredWireOutcome cfg c sender w with
  | ok _ _ => rw [hOut] at hNone; cases hNone
  | err cNext u =>
    cases u
    rw [hOut] at hSound
    exact hSound

theorem piToprfCredService_non_identity_witness {Attr O : Type} [DecidableEq Attr]
    (cfg : Spec.IdealCredConfig O) :
    (∃ c₁ c₂ : PiToprfCredState Attr O,
      c₁ ≠ c₂ ∧
      c₁.reservoir ≠ c₂.reservoir ∧
      c₁.abs = Spec.IdealCredState.empty cfg ∧
      c₂.abs = Spec.IdealCredState.empty cfg) ∧
    ((piToprfCredService (Attr := Attr) cfg).errStep (PiToprfCredState.init cfg)
        (.client, .advanceEpochWire 0 0#256)).phaseAuditCount = 1 := by
  refine ⟨?_, ?_⟩
  · let c₁ := PiToprfCredState.init (Attr := Attr) cfg
    let c₂ := { c₁ with reservoir := c₁.reservoir.poison, phaseAuditCount := 99 }
    have hFalseNeTrue : false ≠ true := by decide
    refine ⟨c₁, c₂, ?_, ?_, rfl, rfl⟩
    · intro h; exact hFalseNeTrue (congrArg (fun s => s.reservoir.poisoned) h)
    · intro h; exact hFalseNeTrue (congrArg ToprfReservoir.poisoned h)
  · have hNotIss : decide (Spec.CredPort.client = .issuer) = false :=
      decide_eq_false (fun h => Spec.CredPort.noConfusion h)
    have hNotAdv : decide (Spec.CredPort.client = .adversary) = false :=
      decide_eq_false (fun h => Spec.CredPort.noConfusion h)
    have hSp : (PiToprfCredState.init (Attr := Attr) cfg).checkCallerPort
        .client (.advanceEpochWire (Attr := Attr) 0 0#256) = false := by
      dsimp only [PiToprfCredState.init, PiToprfCredState.checkCallerPort]
      rw [hNotIss, hNotAdv]
      rfl
    dsimp only [piToprfCredService, piToprfCredWireOutcome]
    rw [hSp]
    rfl

theorem piToprfCredService_issuer_issues_at_init {Attr O : Type} [DecidableEq Attr]
    (cfg : Spec.IdealCredConfig O) (holder : Nat) (attr0 : Attr)
    (newRoot blindVcTag : Spec.Digest256) :
    ∃ c' : PiToprfCredState Attr O,
      (piToprfCredService (Attr := Attr) cfg).Init (PiToprfCredState.init (Attr := Attr) cfg) ∧
      (piToprfCredService (Attr := Attr) cfg).step (PiToprfCredState.init (Attr := Attr) cfg)
        (.issuer, .issueWire holder [attr0] newRoot blindVcTag) = some (c', .issued 0) := by
  let c₀ := PiToprfCredState.init (Attr := Attr) cfg
  have hCaller : c₀.checkCallerPort .issuer (.issueWire holder [attr0] newRoot blindVcTag) = true := by
    simp only [PiToprfCredState.checkCallerPort, decide_true, Bool.true_or]
  have hIss : c₀.checkIssueWire [attr0] = true := by
    have h1 : decide (0 < (1 : Nat)) = true := by decide
    have h2 : decide ((1 : Nat) ≤ Spec.pqCredentialProfile.maxAttrs) = true := by decide
    have h3 : decide ((0 : Nat) < 2 ^ Spec.pqCredentialProfile.accumulatorDepth) = true := by decide
    dsimp only [c₀, PiToprfCredState.init, PiToprfCredState.checkIssueWire, List.length_cons, List.length_nil]
    rw [h1, h2, h3]
    rfl
  let c₁ : PiToprfCredState Attr O :=
    { c₀ with
      entries := c₀.entries ++ [⟨c₀.entries.length, holder, [attr0], c₀.epoch, newRoot, blindVcTag⟩]
      accumulatorRoot := newRoot
      issuedThisEpoch := c₀.issuedThisEpoch + 1
      phaseAuditCount := c₀.phaseAuditCount + 1 }
  have hOutEq : piToprfCredWireOutcome cfg c₀ .issuer
      (.issueWire holder [attr0] newRoot blindVcTag) = StepOutcome.ok c₁ (.issued 0) := by
    unfold piToprfCredWireOutcome
    rw [hCaller]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hIss]
    rfl
  refine ⟨c₁, rfl, ?_⟩
  dsimp only [piToprfCredService]
  rw [hOutEq]

private theorem foldl_gl_zero_after {α : Type} :
    ∀ (xs : List α) (acc : Goldilocks) (f : α → Goldilocks),
      (∀ x ∈ xs, f x = Goldilocks.zero) →
      xs.foldl (fun s x => CommRingOps.add s (f x)) acc = acc
  | [], acc, _, _ => rfl
  | x :: xs, acc, f, hAll => by
    simp only [List.foldl_cons, hAll x (.head _)]
    have hAddZ : CommRingOps.add acc Goldilocks.zero = acc := LawfulCommRing.add_zero acc
    rw [hAddZ]
    exact foldl_gl_zero_after xs acc f (fun y hy => hAll y (.tail _ hy))

private theorem sumFin_indicator0 (K : Nat) (hPos : 0 < K) :
    (List.finRange K).foldl
      (fun acc (p : Fin K) =>
        CommRingOps.add acc (if p.val == 0 && (0 == 0) then Goldilocks.one else Goldilocks.zero))
      Goldilocks.zero = Goldilocks.one := by
  cases K with
  | zero => cases hPos
  | succ m =>
    rw [List.finRange_succ, List.foldl_cons]
    have hZeroVal : (0 : Fin (m + 1)).val = 0 := rfl
    rw [hZeroVal]
    have hHead : CommRingOps.add Goldilocks.zero
        (if ((0 : Nat) == 0 && (0 == 0)) then Goldilocks.one else Goldilocks.zero) =
        Goldilocks.one := by
      decide
    rw [hHead]
    apply foldl_gl_zero_after
    intro x hx
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
    have hNe : (k.succ.val == 0) = false := rfl
    show (if k.succ.val == 0 && (0 == 0) then Goldilocks.one else Goldilocks.zero) = Goldilocks.zero
    rw [hNe]
    rfl

/-- Concrete Round-1 committed proof with multiplication gate 0 corrupted (`1 * 1 ≠ 0`) across all repetitions. -/
def faultyBlindVcCommit : BlindVcCommittedProof where
  partyX _ p g := if p.val == 0 && g.val == 0 then Goldilocks.one else Goldilocks.zero
  partyY _ p g := if p.val == 0 && g.val == 0 then Goldilocks.one else Goldilocks.zero
  partyZ _ _ _ := Goldilocks.zero
  partyCPad _ _ := BlindVcFp5.zero
  partyRMask _ _ _ := BlindVcFp5.zero

def faultyBlindVcProver :
    CutAndChoose.Prover BlindVcCommittedProof BlindVcFp5 BlindVcR2aMsg BlindVcFp5 BlindVcR2bMsg where
  commit := faultyBlindVcCommit
  respond1 _ := ⟨fun _ _ => BlindVcFp5.zero⟩
  respond2 _ _ := ⟨fun _ _ => BlindVcFp5.zero⟩

theorem faultyBlindVcProver_has_gate_fault :
    ∀ j : Nat, BlindVcRepHasGateFault faultyBlindVcProver.commit j := by
  intro j
  refine ⟨⟨0, by decide⟩, ?_⟩
  have hPos : 0 < credentialSdParties := by rw [credentialSdParties_eq]; decide
  have hSumOne : sumAllPartiesGl
      (fun p : Fin credentialSdParties => if p.val == 0 && (0 == 0) then Goldilocks.one else Goldilocks.zero) =
      Goldilocks.one :=
    sumFin_indicator0 credentialSdParties hPos
  have hSumZero : sumAllPartiesGl (fun _ : Fin credentialSdParties => Goldilocks.zero) = Goldilocks.zero := by
    unfold sumAllPartiesGl
    exact foldl_gl_zero_after _ _ _ (fun _ _ => rfl)
  unfold blindVcGateDefect faultyBlindVcProver faultyBlindVcCommit
  dsimp only
  rw [hSumOne, hSumZero]
  decide

theorem spdz_partial_reserve_burns_witness :
    ∃ (cfg : SpdzConfig) (pre : List SpdzCounterSlot) (failSlot : SpdzCounterSlot)
      (post : List SpdzCounterSlot) (counter items : Nat),
      cfg.Valid = true ∧
      cfg.threshold ≤ (pre ++ failSlot :: post).length ∧
      (pre ++ failSlot :: post).length ≤ cfg.servers ∧
      (∀ s ∈ pre ++ failSlot :: post, s.party < cfg.servers) ∧
      ((pre ++ failSlot :: post).map SpdzCounterSlot.party).Pairwise (· < ·) ∧
      (1 ≤ items ∧ items ≤ Spec.pqCredentialProfile.toprfMaxBatch) ∧
      (∀ s ∈ pre ++ failSlot :: post, spdzAdmitCounter s.lastCounter s.storeHighWater counter = true) ∧
      (∀ s ∈ pre, s.ioSucceeds = true) ∧
      failSlot.ioSucceeds = false :=
  ⟨⟨3, 5⟩,
   [⟨0, some 6, some 6, true⟩],
   ⟨1, some 6, some 6, false⟩,
   [⟨2, some 6, some 6, true⟩],
   7, 1,
   by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩

theorem tooth_unratcheted_failed_slot_recycles_counter :
    ∃ failSlot : SpdzCounterSlot, failSlot = ⟨1, some 6, some 6, false⟩ ∧
    spdzAdmitCounter failSlot.lastCounter failSlot.storeHighWater 7 = true ∧
    ∀ st ∈ (spdzRatchetPass 7 false [⟨0, some 6, some 6, true⟩, failSlot, ⟨2, some 6, some 6, true⟩]).2,
      spdzAdmitCounter st.lastCounter st.storeHighWater 7 = false := by
  exact ⟨⟨1, some 6, some 6, false⟩, rfl, by decide⟩

#verify_constructive
  piToprfCred_invalid_opening_preserves_challenges
  Qsag.spdz_constants_exact
  Qsag.SpdzConfig.new_isSome_iff
  Qsag.spdz_quorum_contains_honest_server
  Qsag.spdz_mac_check_unique_alpha_on_shift
  Qsag.spdzReserveCounters_prevalidates_before_mutating
  Qsag.partial_reserve_burns_without_recycle
  Qsag.reservoir_cursor_strict_monotone_and_refusal_isolation
  Qsag.goldilocks_three_not_fifth_power
  Qsag.fp5ModPoly_irreducible
  Qsag.BlindVcFp5.mul_inv_cancel
  Qsag.allBlindVcFp5_nodup
  Qsag.nonzeroBlindVcFp5_nodup
  Qsag.blindVc_grid_fold_luck
  Qsag.blindVcFp5_roots_le_of_coeffAt_nonzero
  Qsag.blindVcRepetitionKernel_algebraicSound
  Qsag.blindVcOpeningDoomed_has_33_defects
  Qsag.piToprfCredState_abs_non_injective
  Qsag.piToprfCredWireOutcome_sound
  Qsag.piToprfCredService_reservoir_monotone
  Qsag.SpdzOnlineTranscript.honest_checks
  Qsag.evaluatePreparedSpdzSession_ok_all_checks
  Qsag.piToprfCredService_eval_accept_checks
  Qsag.piToprfCredWireOutcome_keeps_session_ledger
  Qsag.piToprfCredMachine_reservoir_never_rewinds
  Qsag.honest_transcript_passes_spdz_gate
  Qsag.forged_circuit_opening_poisons_reservoir
  Qsag.tooth_forged_circuit_opening_not_released
  Qsag.tooth_reprepare_same_session_refused
  Qsag.tooth_forged_limbo_opening_rejected_by_piToprfCredService
  Qsag.piToprfCredService_accept_ok
  Qsag.piToprfCredService_reject_ok
  Qsag.piToprfCredService_non_identity_witness
  Qsag.piToprfCredService_issuer_issues_at_init
  Qsag.faultyBlindVcProver_has_gate_fault
  Qsag.spdz_partial_reserve_burns_witness
  Qsag.tooth_unratcheted_failed_slot_recycles_counter
  Qsag.tooth_skipping_phase2_mac_check_releases_unauthenticated_output
  Qsag.tooth_omitting_cursor_advance_reuses_pow7_tuples
  Qsag.tooth_below_threshold_quorum_all_corrupt

#tooth_pair Qsag.piToprfCredWireOutcome_sound vs
  Qsag.tooth_forged_limbo_opening_rejected_by_piToprfCredService
#tooth_pair Qsag.reservoir_cursor_strict_monotone_and_refusal_isolation vs
  Qsag.tooth_skipping_phase2_mac_check_releases_unauthenticated_output
#tooth_pair Qsag.honest_transcript_passes_spdz_gate vs
  Qsag.tooth_forged_circuit_opening_not_released
#tooth_pair Qsag.piToprfCredMachine_reservoir_never_rewinds vs
  Qsag.tooth_reprepare_same_session_refused
#tooth_pair Qsag.reservoir_cursor_strict_monotone_and_refusal_isolation vs
  Qsag.tooth_omitting_cursor_advance_reuses_pow7_tuples
#tooth_pair Qsag.spdz_quorum_contains_honest_server vs
  Qsag.tooth_below_threshold_quorum_all_corrupt
#tooth_pair Qsag.partial_reserve_burns_without_recycle vs
  Qsag.tooth_unratcheted_failed_slot_recycles_counter
#verify_inhabited Qsag.partial_reserve_burns_without_recycle
  Qsag.spdz_partial_reserve_burns_witness

end Qsag
end
