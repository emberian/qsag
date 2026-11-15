module

public import Qsag.Protocol.Signing.HashSigs
public import Qsag.Exec.PosixCrashWal
public import Qsag.Protocol.Threshold.MaliciousSecurity
public import Qsag.Machine.ConstantTimeIsa
public import Qsag.Machine.ElfBinaryVerify
public import Qsag.Machine.ElfFixtureSlices
import Lean
import Qsag.Tactic.AssuranceKit
import all Qsag.Protocol.Signing.HashSigs
import all Qsag.Protocol.Threshold.MaliciousSecurity
import all Qsag.Machine.ConstantTimeIsa
import all Qsag.Machine.ElfBinaryVerify
import all Qsag.Machine.ElfFixtureSlices

public section

/-!
# `Qsag.Machine.FaultAndSpeculativeSafety`: Fault Injection and Speculative Execution Boundaries

Two questions about the signer, answered on the real `HashSigs` primitives and the
`ConstantTimeIsa` instruction model.

## Part A. Transient computation faults (Sections 1 to 3)

Setting: a two-layer hypertree. The layer-0 subtree root is signed by one layer-1 WOTS+C one-time
key. A fault schedule `ComputeFault : Turn → Option CorruptedWire` corrupts one wire per signing
turn (`faultedAssemble`, which is `signHypertreeLayers` when there is no fault:
`faultedAssemble_no_fault_eq_honest`).

1. **Grafting works against an unguarded signer**
   (`tooth_unguarded_single_bitflip_grafts_second_wots_message`). One bit flip in the lower leaf
   node or on the lower root wire makes the upper one-time key sign a second root; both
   signatures are accepted by `verifyHypertreeLayers` at the same key position. Two signatures
   under one key forge every codeword above their coordinatewise minimum, from public data only
   (`two_wots_signatures_forge_any_dominated_codeword`,
   `honest_key_two_signatures_forge_dominated_codewords`).
2. **Verification alone does not stop it** (`tooth_verify_only_gate_releases_consistent_graft`).
   A fault on a sibling node that feeds both the emitted auth path and the root recomputation
   gives a signature that passes the full verifier while the upper key has signed a different
   root.
3. **Verification plus a write-once one-time-key cache does**
   (`verify_before_release_prevents_fault_wots_reuse_two_layer`,
   `guarded_signer_survives_any_fault_schedule`). The gate `verifyBeforeRelease` runs
   `verifyPqHashSig` and compares the one-time message of the upper key (lower root and grinding
   counter) with a write-once cache. Over traces of any length, with every candidate chosen by
   the fault adversary, two released signatures on the same upper key carry the same one-time
   message, and the same upper-layer opening unless a hash collision is exhibited. The counter is
   part of the cached message on purpose: a root-only cache would let a faulted grind select a
   second codeword for the same root.
4. **BDOZ gate on shares** (`bdoz_mac_blocks_faulted_party_share_release`). Over any number of
   turns, a faulted share is released under a global MAC key only if that key is one of the
   per-turn guesses fixed by the faulted openings.
5. **Physical boundary** (`terminal_check_holds_when_gate_tail_unglitched`,
   `dual_glitch_control_flow_bypass_impossibility`, `sign_release_gate_boundary`). Any glitch
   before the terminal `check; emit` pair is tolerated by the software gate. A glitch that upsets
   the register once and skips instruction slots releases any value from any gate program that
   contains a release, whatever predicates it checks.

Section 5 generalizes the message-uniqueness guarantee to every upper layer of an arbitrary-depth
hypertree (`verifyBeforeReleaseAll`, `all_depth_gate_complete`), enforcing canonical 32-byte
`HashAdrs` coordinate bounds (`OtsPosition.ValidCoords`, `AdrsGateValid`) and encoded-address
cache consistency (`AdrsCacheConsistent`) so mathematical `Nat` coordinates never alias truncated
`UInt32`/`UInt64` hash addresses (`otsPosition_toEncodedAdrs_injective`,
`tooth_unbounded_nat_position_aliases_u64_adrs`). The two-layer API above is kept
for its fault-circuit examples. The all-layer theorem also proves identical openings or a hash
collision, using the next cached input root to anchor every intermediate subtree. The full gate
uses the `HashSigs` verifier and its parameter validity rules; a layer count of 22 is not a
claim of equivalence to the separate FIPS 205 signature format. The layer-only
`verifyHypertreeBeforeRelease` gate enforces per-coordinate `HashAdrs` bounds without a 62-bit
total-height cap, admitting height-66 (`22 × 3`) profiles across all `globalIdx < 2^66`.

**Rust Architecture Boundary & Section 9 Production Crash-Recoverable Journal:**
In Rust, `crates/qsag-core/src/tsw_baggy.rs::sign_hypertree_core` runs stateless self-verification
(`verify_pq_hash_sig`) before returning `Some(sig)` (`verify-only` in the pure core, whose exact
sibling-fault grafting boundary is proved in `tooth_verify_only_gate_releases_consistent_graft`),
whereas stateful/quorum write-once release caches and durable ceremony journals reside in
`crates/qsag-quorum/src/quorum_jorts.rs` (`ots_release_cache`),
`crates/qsag-fts/src/frontier.rs` (`released_uses`), `crates/qsag-cli/src/keys.rs`, and
`crates/qsag-core/src/ceremony_journal.rs` (`FsCeremonyJournal`). Section 9 formalizes both the
production shared-core release gate (`verifyProductionBeforeReleaseAll` over
`verifyProductionPqHashSig` and `verifyProductionHypertreeLayers` with `TAG_H_INTERNAL` upper
layers, XOF-derived FORS indices, `(j, u)` FORS ADRS, and `kp0` `.forsTree` Merkle `keyPair`) and
its key-scoped crash-recoverable persistent upper-layer journal (`DurableUpperJournalState`,
`stepRecoverableProductionGate`, `recoverable_production_journal_prevents_upper_wots_reuse_across_crashes`),
distinguishing uninterrupted in-memory trace guarantees from multi-crash durable journal recovery.
The explicit counter-grinding
tooth exhibits two valid codewords for one root and key. Faults on the gate itself and on the
cache are the physical side of item 5. The collision alternatives are witnesses for `suite.rawHash`,
not probability bounds. Item 1 shows that the forged chains recover the public key; finding a
message whose digest is a dominated codeword is the adversary's remaining (grinding) work.

## Part B. Spectre-v1 (Section 4)

`specRun` is a speculative machine over `ConstantTimeIsa.X86Instr`: at each forward conditional branch the
adversarial `PredictorOracle` guesses; on a wrong guess up to `W` instructions run transiently on
a shadow state and all their leakage events are observed, then execution rolls back. `lfence`
ends a transient window.

1. `straightline_ct_implies_unbounded_speculative_ni`: a branch-free program accepted by the
   `ConstantTimeIsa` checker has the same speculative trace on public-equal states for every
   window and every predictor. Instantiated for `ctEq32X86Prog` and `goldilocksMulCtX86Prog`.
2. `tooth_unmasked_bounds_branch_leaks_under_speculation`: `if idx < pub_len then table[arr[idx]]`
   is constant-time without speculation and with `W ≤ 1`, and leaks a secret-dependent address
   for every `W ≥ 2`.
3. `slh_predicate_mask_prevents_oob_speculative_secret_load`,
   `slh_transient_loads_stay_in_bounds`: the `sbb` predicate mask restores non-interference for
   all windows and predictors on a non-empty array; `tooth_slh_mask_leaks_on_empty_array` shows
   the non-emptiness condition is needed. `lfence_after_bounds_branch_blocks_speculative_leak`
   is the barrier alternative.

Section 6 adds `pcSpecRun` with absolute backward branches and architectural fuel. Its
relational invariant must hold on transient paths as well as architectural paths. The
`compilePubLoop` lowering and public-pointer loop instance permit early predicted exits and
extra transient iterations. `binary_loop_fuel_bounded_speculative_ni` lifts the same discipline
to decoded x86 conditional back-edges. Named semantic schemas cover `ct_select_u64`,
`sbox_bitslice`, and `gf2_128_mul_acc`; these schemas do not assert the presence of a compiled
`ct_select` or `sbox` fixture. The compiled `ct_eq_32` and Goldilocks multiplication corollaries
use actual `ElfFixtureSlices` bytes and the binary decoder's semantics. Nested mispredictions
follow the predictor without a nested rollback. Indirect-branch, return-address and store-bypass
speculation are not modeled; `ret` ends execution.
-/

set_option autoImplicit false

namespace Qsag.FaultAndSpeculativeSafety

open Qsag Qsag.ConstantTimeIsa

/-! ## 1. Transient Computation Faults on the Two-Layer Hypertree Signer -/

/-- XOR mask of one bit position inside a byte. -/
def bitMask : Nat → UInt8
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | 4 => 16
  | 5 => 32
  | 6 => 64
  | _ => 128

theorem bitMask_ne_zero (k : Nat) : bitMask k ≠ 0 := by
  unfold bitMask
  split <;> decide

/-- Flip bit `bit` (little-endian within byte `bit / 8`) of a byte-string wire. -/
def flipBit (bit : Nat) (xs : List UInt8) : List UInt8 :=
  xs.set (bit / 8) (xs.getD (bit / 8) 0 ^^^ bitMask (bit % 8))

theorem flipBit_ne (bit : Nat) (xs : List UInt8) (h : bit / 8 < xs.length) :
    flipBit bit xs ≠ xs := by
  intro hEq
  have hGet := congrArg (fun l => l.getD (bit / 8) 0) hEq
  simp only [flipBit, List.getD_eq_getElem?_getD, List.getElem?_set_self h,
    Option.getD_some] at hGet
  have hCancel := congrArg (fun z => (xs[bit / 8]?.getD 0) ^^^ z) hGet
  simp only [← UInt8.xor_assoc, UInt8.xor_self, UInt8.zero_xor] at hCancel
  exact bitMask_ne_zero _ hCancel

/-- Wire of the two-layer signing circuit that a transient fault can hit: the lower-tree leaf
    node entering the root recomputation, a lower-tree sibling node shared by the emitted auth
    path and the root recomputation, the lower root wire entering the upper one-time key, or an
    emitted upper WOTS+C chain value. -/
inductive FaultSite where
  | lowerLeafNode
  | lowerAuthSibling (level : Nat)
  | lowerRootNode
  | upperChain (r : Nat)
  deriving DecidableEq, Repr

/-- A corrupted wire: where the fault lands and an arbitrary replacement function for the value
    on that wire (single-bit flips, stuck-at values and full replacement are all instances). -/
structure CorruptedWire where
  site : FaultSite
  corrupt : List UInt8 → List UInt8

abbrev Turn := Nat

/-- Adversarial transient computation fault schedule: at most one corrupted wire per turn. -/
abbrev ComputeFault := Turn → Option CorruptedWire

def faultLeaf (fault : Option CorruptedWire) (leaf : List UInt8) : List UInt8 :=
  match fault with
  | some ⟨.lowerLeafNode, c⟩ => c leaf
  | _ => leaf

def faultPath (fault : Option CorruptedWire) (path : List (List UInt8)) : List (List UInt8) :=
  match fault with
  | some ⟨.lowerAuthSibling j, c⟩ => path.set j (c (path.getD j []))
  | _ => path

def faultRoot (fault : Option CorruptedWire) (root : List UInt8) : List UInt8 :=
  match fault with
  | some ⟨.lowerRootNode, c⟩ => c root
  | _ => root

def faultUpperChains (fault : Option CorruptedWire) (chains : List (List UInt8)) :
    List (List UInt8) :=
  match fault with
  | some ⟨.upperChain r, c⟩ => chains.set r (c (chains.getD r []))
  | _ => chains

/-- Honest auth path of leaf `g mod 2^h` in the layer-0 subtree that holds global leaf `g`. -/
def lowerAuthPath (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (g : Nat) : List (List UInt8) :=
  buildMerkleAuthPath suite sk.pkSeed (UInt32.ofNat 0)
    (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) .tree
    (computeWotsPk suite params sk (UInt32.ofNat 0) (UInt64.ofNat (g / 2 ^ params.subtreeHeight)))
    params.subtreeHeight 0 (g % 2 ^ params.subtreeHeight)

/-- Lower-layer wires the signer hands onward: the emitted auth path and the root it recomputed. -/
structure LowerWires where
  authPath : List (List UInt8)
  root : List UInt8

/-- Lower-layer root recomputation under a fault: the signer walks the auth path from its leaf
    node; the fault may replace the leaf node, one sibling, or the resulting root. -/
def faultedLowerWires (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (g : Nat) (fault : Option CorruptedWire) : Option LowerWires :=
  (walkMerkleAuthPath suite sk.pkSeed (UInt32.ofNat 0)
      (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) .tree params.subtreeHeight 0
      (g % 2 ^ params.subtreeHeight)
      (faultLeaf fault (computeWotsPk suite params sk (UInt32.ofNat 0)
        (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) (g % 2 ^ params.subtreeHeight)))
      (faultPath fault (lowerAuthPath suite params sk g))).map
    fun r => { authPath := faultPath fault (lowerAuthPath suite params sk g), root := faultRoot fault r }

theorem lowerWalk_honest (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (g : Nat) :
    walkMerkleAuthPath suite sk.pkSeed (UInt32.ofNat 0)
      (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) .tree params.subtreeHeight 0
      (g % 2 ^ params.subtreeHeight)
      (computeWotsPk suite params sk (UInt32.ofNat 0)
        (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) (g % 2 ^ params.subtreeHeight))
      (lowerAuthPath suite params sk g) =
    some (computeXmssSubtreeRoot suite params sk (UInt32.ofNat 0)
      (UInt64.ofNat (g / 2 ^ params.subtreeHeight))) := by
  have hWalk := walkMerkleAuthPath_buildMerkleAuthPath suite sk.pkSeed (UInt32.ofNat 0)
    (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) .tree
    (computeWotsPk suite params sk (UInt32.ofNat 0) (UInt64.ofNat (g / 2 ^ params.subtreeHeight)))
    params.subtreeHeight 0 (g % 2 ^ params.subtreeHeight)
    (Nat.mod_lt _ (Nat.two_pow_pos _))
  simp only [Nat.zero_mul, Nat.zero_add] at hWalk
  exact hWalk

/-- Without a fault the recomputed lower root is the real layer-0 subtree root. -/
theorem faultedLowerWires_none (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (g : Nat) :
    faultedLowerWires suite params sk g none =
      some { authPath := lowerAuthPath suite params sk g
             root := computeXmssSubtreeRoot suite params sk (UInt32.ofNat 0)
               (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) } := by
  unfold faultedLowerWires
  simp only [faultLeaf, faultPath, faultRoot]
  rw [lowerWalk_honest]
  rfl

/-- Output of one signing turn: the lower root that actually reached the upper one-time key, and
    the two assembled layer signatures. -/
structure FaultedAssembly where
  rootWire : List UInt8
  layerSigs : List LayerXmssSig

/-- Two-layer signature assembly under at most one transient fault. Layer 0 signs `mu` with
    `signHypertreeLayers`; the lower root is recomputed (`faultedLowerWires`); the layer-1
    one-time key then signs whatever arrives on the root wire, again with `signHypertreeLayers`. -/
def faultedAssemble (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (pkRoot rRand : List UInt8) (maxGrind : Nat) (mu : List UInt8) (g : Nat)
    (fault : Option CorruptedWire) : Option FaultedAssembly :=
  match signHypertreeLayers suite params sk pkRoot rRand maxGrind 0 g mu 1,
        faultedLowerWires suite params sk g fault with
  | some [lower], some wires =>
    match signHypertreeLayers suite params sk pkRoot [] maxGrind 1
        (g / 2 ^ params.subtreeHeight) wires.root 1 with
    | some [upper] =>
      some { rootWire := wires.root
             layerSigs :=
               [ { lower with authPath := wires.authPath }
               , { upper with wotsChains := faultUpperChains fault upper.wotsChains } ] }
    | _ => none
  | _, _ => none

/-- Faithfulness: with no fault the assembly is exactly the real two-layer signer. -/
theorem faultedAssemble_no_fault_eq_honest (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pkRoot rRand : List UInt8) (maxGrind : Nat) (mu : List UInt8) (g : Nat) :
    (faultedAssemble suite params sk pkRoot rRand maxGrind mu g none).map (·.layerSigs) =
      signHypertreeLayers suite params sk pkRoot rRand maxGrind 0 g mu 2 := by
  unfold faultedAssemble
  rw [faultedLowerWires_none]
  simp only [signHypertreeLayers, faultUpperChains, lowerAuthPath]
  cases hG0 : grindTswCounterAux suite params.w params.ell1 params.targetSum rRand sk.pkSeed
      pkRoot mu (UInt32.ofNat 0) (UInt64.ofNat (g / 2 ^ params.subtreeHeight))
      (UInt32.ofNat (g % 2 ^ params.subtreeHeight)) 0 maxGrind with
  | none => rfl
  | some t0 =>
    rcases t0 with ⟨ctr0, digits0, hm0⟩
    dsimp only
    cases hG1 : grindTswCounterAux suite params.w params.ell1 params.targetSum [] sk.pkSeed
        pkRoot (computeXmssSubtreeRoot suite params sk (UInt32.ofNat 0)
          (UInt64.ofNat (g / 2 ^ params.subtreeHeight))) (UInt32.ofNat (0 + 1))
        (UInt64.ofNat (g / 2 ^ params.subtreeHeight / 2 ^ params.subtreeHeight))
        (UInt32.ofNat (g / 2 ^ params.subtreeHeight % 2 ^ params.subtreeHeight)) 0 maxGrind with
    | none => simp
    | some t1 =>
      rcases t1 with ⟨ctr1, digits1, hm1⟩
      simp

theorem computeMerkleNode_length (suite : TweakableHashSuite) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kind : AdrsKind) (leafFn : Nat → List UInt8)
    (hLeaf : ∀ i, (leafFn i).length = 32) (h idx : Nat) :
    (computeMerkleNode suite pkSeed layer tree kind leafFn h idx).length = 32 := by
  cases h with
  | zero => exact hLeaf idx
  | succ n => exact thCall_length _ _ _ _ _

theorem computeWotsPk_length (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (layer : UInt32) (tree : UInt64) (kp : Nat) :
    (computeWotsPk suite params sk layer tree kp).length = 32 :=
  thCall_length _ _ _ _ _

theorem computeXmssSubtreeRoot_length (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (layer : UInt32) (tree : UInt64) :
    (computeXmssSubtreeRoot suite params sk layer tree).length = 32 :=
  computeMerkleNode_length suite sk.pkSeed layer tree .tree _
    (computeWotsPk_length suite params sk layer tree) _ _

/-- Two WOTS+C signatures that the real verifier accepts at one upper leaf, on two different
    lower roots, both leading to the same top root: the one-time key has signed two messages. -/
structure WotsTwoMessageWitness (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed pkRoot : List UInt8) (upperLeaf : Nat) (topRoot : List UInt8) where
  root₁ : List UInt8
  root₂ : List UInt8
  sig₁ : LayerXmssSig
  sig₂ : LayerXmssSig
  roots_ne : root₁ ≠ root₂
  accepts₁ : verifyHypertreeLayers suite params pkSeed pkRoot [] 1 upperLeaf root₁ [sig₁] =
    some topRoot
  accepts₂ : verifyHypertreeLayers suite params pkSeed pkRoot [] 1 upperLeaf root₂ [sig₂] =
    some topRoot

/-- What an assembly that did not fault the upper chains exposes: its upper signature is the
    real upper signer's output on the root wire and verifies there, and the root wire is the
    (possibly faulted) lower-root recomputation. -/
theorem faultedAssemble_upper_accepts (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pkRoot rRand : List UInt8) (maxGrind : Nat) (mu : List UInt8) (g : Nat)
    (fault : Option CorruptedWire) (asm : FaultedAssembly)
    (hUpper : g / 2 ^ params.subtreeHeight < 2 ^ params.subtreeHeight)
    (hChains : ∀ cs, faultUpperChains fault cs = cs)
    (hAsm : faultedAssemble suite params sk pkRoot rRand maxGrind mu g fault = some asm) :
    ∃ lower upper wires,
      signHypertreeLayers suite params sk pkRoot rRand maxGrind 0 g mu 1 = some [lower] ∧
      faultedLowerWires suite params sk g fault = some wires ∧
      asm.rootWire = wires.root ∧
      asm.layerSigs = [{ lower with authPath := wires.authPath }, upper] ∧
      verifyHypertreeLayers suite params sk.pkSeed pkRoot [] 1 (g / 2 ^ params.subtreeHeight)
        asm.rootWire [upper] = some (computeXmssSubtreeRoot suite params sk (UInt32.ofNat 1) 0) := by
  unfold faultedAssemble at hAsm
  split at hAsm
  · next lower wires hLower hWires =>
    split at hAsm
    · next upper hSign =>
      simp only [Option.some.injEq] at hAsm
      subst hAsm
      have hSound := signHypertreeLayers_sound suite params sk pkRoot maxGrind 1 1
        (g / 2 ^ params.subtreeHeight) [] wires.root [upper] (by omega)
        (by simpa using hUpper) hSign
      refine ⟨lower, upper, wires, hLower, hWires, rfl, ?_, hSound.2⟩
      rw [hChains]
    · cases hAsm
  · cases hAsm

/-- **Fault-grafting tooth: one bit flip makes the unguarded signer reuse a one-time key.**
    Take the two-layer signer with no release check. Run it once without a fault and once with a
    single transient fault that flips one bit of the lower-tree leaf node or of the lower root
    wire. Whenever both runs emit a signature, the two upper-layer WOTS+C signatures are accepted
    by the real verifier at the same upper leaf, to the same top root, on two different lower
    roots. The only alternative is a hash collision, and only when the flipped leaf node hashes
    back to the same root. -/
theorem tooth_unguarded_single_bitflip_grafts_second_wots_message
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (pkRoot rRand : List UInt8) (maxGrind : Nat) (mu : List UInt8) (g bit : Nat)
    (hUpper : g / 2 ^ params.subtreeHeight < 2 ^ params.subtreeHeight) (hBit : bit < 256)
    (site : FaultSite) (hSite : site = .lowerLeafNode ∨ site = .lowerRootNode)
    (honest faulted : FaultedAssembly)
    (hHonest : faultedAssemble suite params sk pkRoot rRand maxGrind mu g none = some honest)
    (hFaulted : faultedAssemble suite params sk pkRoot rRand maxGrind mu g
      (some ⟨site, flipBit bit⟩) = some faulted) :
    Nonempty (WotsTwoMessageWitness suite params sk.pkSeed pkRoot
        (g / 2 ^ params.subtreeHeight)
        (computeXmssSubtreeRoot suite params sk (UInt32.ofNat 1) 0)) ∨
      (site = .lowerLeafNode ∧ Collision suite.rawHash) := by
  obtain ⟨_, upper₁, wires₁, _, hWires₁, hRoot₁, hSigs₁, hAcc₁⟩ :=
    faultedAssemble_upper_accepts suite params sk pkRoot rRand maxGrind mu g none honest hUpper
      (fun _ => rfl) hHonest
  have hChains : ∀ cs, faultUpperChains (some ⟨site, flipBit bit⟩) cs = cs := by
    intro cs
    rcases hSite with rfl | rfl <;> rfl
  obtain ⟨_, upper₂, wires₂, _, hWires₂, hRoot₂, hSigs₂, hAcc₂⟩ :=
    faultedAssemble_upper_accepts suite params sk pkRoot rRand maxGrind mu g _ faulted hUpper
      hChains hFaulted
  rw [faultedLowerWires_none] at hWires₁
  simp only [Option.some.injEq] at hWires₁
  have hR₁ : honest.rootWire = computeXmssSubtreeRoot suite params sk (UInt32.ofNat 0)
      (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) := by rw [hRoot₁, ← hWires₁]
  have hByte : bit / 8 < 32 := by omega
  have mk : faulted.rootWire ≠ honest.rootWire →
      Nonempty (WotsTwoMessageWitness suite params sk.pkSeed pkRoot
        (g / 2 ^ params.subtreeHeight)
        (computeXmssSubtreeRoot suite params sk (UInt32.ofNat 1) 0)) := fun hNe =>
    ⟨{ root₁ := honest.rootWire, root₂ := faulted.rootWire, sig₁ := upper₁, sig₂ := upper₂
       roots_ne := fun h => hNe h.symm, accepts₁ := hAcc₁, accepts₂ := hAcc₂ }⟩
  unfold faultedLowerWires at hWires₂
  rcases hSite with rfl | rfl
  · -- flipped leaf node
    simp only [faultLeaf, faultPath, faultRoot, Option.map_eq_some_iff] at hWires₂
    obtain ⟨r₂, hWalk₂, hW₂⟩ := hWires₂
    have hR₂ : faulted.rootWire = r₂ := by rw [hRoot₂, ← hW₂]
    by_cases hEq : faulted.rootWire = honest.rootWire
    · right
      refine ⟨rfl, ?_⟩
      have hWalk₁ := lowerWalk_honest suite params sk g
      rw [← hR₁, ← hEq, hR₂] at hWalk₁
      exact (walkMerkleAuthPath_collision_extract suite sk.pkSeed (UInt32.ofNat 0)
        (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) .tree params.subtreeHeight 0
        (g % 2 ^ params.subtreeHeight)
        (Or.inl (flipBit_ne bit _ (by rw [computeWotsPk_length]; exact hByte)))
        hWalk₂ hWalk₁).toCollision
    · exact Or.inl (mk hEq)
  · -- flipped root wire
    simp only [faultLeaf, faultPath, faultRoot, Option.map_eq_some_iff] at hWires₂
    obtain ⟨r₂, hWalk₂, hW₂⟩ := hWires₂
    rw [lowerWalk_honest] at hWalk₂
    simp only [Option.some.injEq] at hWalk₂
    left
    apply mk
    rw [hRoot₂, ← hW₂, hR₁, ← hWalk₂]
    exact flipBit_ne bit _ (by rw [computeXmssSubtreeRoot_length]; exact hByte)

/-! ### Why two messages under one WOTS+C key are fatal -/

/-- Public computation of the grafting adversary: from two signatures under one WOTS+C key,
    start each chain at the lower of the two revealed positions and walk it up to the target
    digit. No secret key material is used. -/
def graftForgeChains (suite : TweakableHashSuite) (params : PqHashParams) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp : Nat) (d₁ d₂ : List Nat)
    (c₁ c₂ : List (List UInt8)) (target : List Nat) : List (List UInt8) :=
  (List.range params.ell1).map fun r =>
    if d₁.getD r 0 ≤ d₂.getD r 0 then
      wotsChainSteps suite pkSeed layer tree kp r (d₁.getD r 0)
        (target.getD r 0 - d₁.getD r 0) (c₁.getD r [])
    else
      wotsChainSteps suite pkSeed layer tree kp r (d₂.getD r 0)
        (target.getD r 0 - d₂.getD r 0) (c₂.getD r [])

/-- **Two signatures under one WOTS+C key forge every dominated codeword.** If two signatures
    open the same chain endpoints at digit vectors `d₁` and `d₂`, then for every digit vector
    `target` that is coordinatewise at least `min d₁ d₂`, the chains computed by
    `graftForgeChains` from public data recover the same one-time public key. One signature alone
    only covers targets above `d₁`; the target-sum rule makes those unreachable, and the second
    signature removes that protection. -/
theorem two_wots_signatures_forge_any_dominated_codeword
    (suite : TweakableHashSuite) (params : PqHashParams) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp : Nat) (d₁ d₂ : List Nat) (c₁ c₂ : List (List UInt8))
    (hSame : recoverWotsEndpoints suite params pkSeed layer tree kp d₁ c₁ =
      recoverWotsEndpoints suite params pkSeed layer tree kp d₂ c₂)
    (target : List Nat)
    (hDom : ∀ r, r < params.ell1 →
      min (d₁.getD r 0) (d₂.getD r 0) ≤ target.getD r 0 ∧ target.getD r 0 ≤ params.w - 1) :
    recoverWotsPkFromSig suite params pkSeed layer tree kp target
        (graftForgeChains suite params pkSeed layer tree kp d₁ d₂ c₁ c₂ target) =
      recoverWotsPkFromSig suite params pkSeed layer tree kp d₁ c₁ := by
  unfold recoverWotsPkFromSig
  congr 1
  unfold recoverWotsEndpoints
  apply List.map_congr_left
  intro r hrMem
  have hr : r < params.ell1 := List.mem_range.mp hrMem
  obtain ⟨hLo, hHi⟩ := hDom r hr
  have hPoint := congrArg (fun l => l.getD r []) hSame
  simp only [recoverWotsEndpoints, list_getD_map_range params.ell1 _ [] hr] at hPoint
  simp only [graftForgeChains, list_getD_map_range params.ell1 _ [] hr]
  by_cases hLe : d₁.getD r 0 ≤ d₂.getD r 0
  · simp only [hLe, ↓reduceIte]
    have hAdd := wotsChainSteps_add suite pkSeed layer tree kp r
      (target.getD r 0 - d₁.getD r 0) (params.w - 1 - target.getD r 0) (d₁.getD r 0)
      (c₁.getD r [])
    have e₁ : d₁.getD r 0 + (target.getD r 0 - d₁.getD r 0) = target.getD r 0 := by omega
    have e₂ : target.getD r 0 - d₁.getD r 0 + (params.w - 1 - target.getD r 0) =
        params.w - 1 - d₁.getD r 0 := by omega
    rw [e₁, e₂] at hAdd
    exact hAdd
  · simp only [hLe, ↓reduceIte]
    have hAdd := wotsChainSteps_add suite pkSeed layer tree kp r
      (target.getD r 0 - d₂.getD r 0) (params.w - 1 - target.getD r 0) (d₂.getD r 0)
      (c₂.getD r [])
    have e₁ : d₂.getD r 0 + (target.getD r 0 - d₂.getD r 0) = target.getD r 0 := by omega
    have e₂ : target.getD r 0 - d₂.getD r 0 + (params.w - 1 - target.getD r 0) =
        params.w - 1 - d₂.getD r 0 := by omega
    rw [e₁, e₂] at hAdd
    rw [hAdd]
    exact hPoint.symm

/-- The honest signer's chain openings at a valid target-sum codeword recover the real chain
    endpoints of the one-time key. -/
theorem honest_wots_chains_open_real_endpoints (suite : TweakableHashSuite)
    (params : PqHashParams) (sk : PqSecretKey) (layer : UInt32) (tree : UInt64) (kp : Nat)
    (digits : List Nat)
    (hValid : checkTargetSum params.w params.ell1 params.targetSum digits = true) :
    recoverWotsEndpoints suite params sk.pkSeed layer tree kp digits
        ((List.range params.ell1).map fun r =>
          wotsChainSteps suite sk.pkSeed layer tree kp r 0 (digits.getD r 0)
            (wotsSecretBase suite sk layer tree kp r)) =
      computeWotsEndpoints suite params sk layer tree kp := by
  obtain ⟨hLen, hBound, _⟩ :=
    (checkTargetSum_iff params.w params.ell1 params.targetSum digits).mp hValid
  unfold recoverWotsEndpoints computeWotsEndpoints
  apply List.map_congr_left
  intro r hrMem
  have hr : r < params.ell1 := List.mem_range.mp hrMem
  simp only [list_getD_map_range params.ell1 _ [] hr]
  have hdr : digits.getD r 0 < params.w := by
    have hrDigits : r < digits.length := hLen ▸ hr
    rw [list_getD_eq_getElem digits 0 hrDigits]
    exact hBound _ (List.getElem_mem hrDigits)
  have hAdd := wotsChainSteps_add suite sk.pkSeed layer tree kp r (digits.getD r 0)
    (params.w - 1 - digits.getD r 0) 0 (wotsSecretBase suite sk layer tree kp r)
  simp only [Nat.zero_add] at hAdd
  have hSum : digits.getD r 0 + (params.w - 1 - digits.getD r 0) = params.w - 1 := by omega
  rw [hAdd, hSum]

/-- **A second honest signature under one WOTS+C key is a forgery kit.** Given the honest
    signer's openings at two valid codewords `d₁`, `d₂` of the same one-time key, the public
    function `graftForgeChains` produces, for every digit vector dominating their coordinatewise
    minimum, chain values that recover the key's real WOTS+C public key. -/
theorem honest_key_two_signatures_forge_dominated_codewords (suite : TweakableHashSuite)
    (params : PqHashParams) (sk : PqSecretKey) (layer : UInt32) (tree : UInt64) (kp : Nat)
    (d₁ d₂ target : List Nat)
    (hValid₁ : checkTargetSum params.w params.ell1 params.targetSum d₁ = true)
    (hValid₂ : checkTargetSum params.w params.ell1 params.targetSum d₂ = true)
    (hDom : ∀ r, r < params.ell1 →
      min (d₁.getD r 0) (d₂.getD r 0) ≤ target.getD r 0 ∧ target.getD r 0 ≤ params.w - 1) :
    recoverWotsPkFromSig suite params sk.pkSeed layer tree kp target
        (graftForgeChains suite params sk.pkSeed layer tree kp d₁ d₂
          ((List.range params.ell1).map fun r =>
            wotsChainSteps suite sk.pkSeed layer tree kp r 0 (d₁.getD r 0)
              (wotsSecretBase suite sk layer tree kp r))
          ((List.range params.ell1).map fun r =>
            wotsChainSteps suite sk.pkSeed layer tree kp r 0 (d₂.getD r 0)
              (wotsSecretBase suite sk layer tree kp r))
          target) =
      computeWotsPk suite params sk layer tree kp := by
  rw [two_wots_signatures_forge_any_dominated_codeword suite params sk.pkSeed layer tree kp d₁ d₂
    _ _ ((honest_wots_chains_open_real_endpoints suite params sk layer tree kp d₁ hValid₁).trans
      (honest_wots_chains_open_real_endpoints suite params sk layer tree kp d₂ hValid₂).symm)
    target hDom]
  exact recoverWotsPkFromSig_eq_computeWotsPk suite params sk layer tree kp d₁ hValid₁

/-- Inhabitedness of the tooth's premises: on the toy suite both the fault-free and the
    root-flipped run of the unguarded signer emit a signature, on different root wires. -/
theorem tooth_graft_premises_inhabited :
    (faultedAssemble zeroToySuite zeroToyParams ⟨[], [], []⟩ [] [] 1 [] 0 none).isSome = true ∧
    (faultedAssemble zeroToySuite zeroToyParams ⟨[], [], []⟩ [] [] 1 [] 0
      (some ⟨.lowerRootNode, flipBit 0⟩)).isSome = true ∧
    (faultedAssemble zeroToySuite zeroToyParams ⟨[], [], []⟩ [] [] 1 [] 0 none).map (·.rootWire) ≠
      (faultedAssemble zeroToySuite zeroToyParams ⟨[], [], []⟩ [] [] 1 [] 0
        (some ⟨.lowerRootNode, flipBit 0⟩)).map (·.rootWire) := by
  decide

/-! ## 2. Verify-Before-Release with a Write-Once One-Time-Key Cache -/

/-- A layer signature list verifies iff its first layer verifies to some intermediate root and
    the remaining layers verify from that root one layer up. -/
theorem verifyHypertreeLayers_split (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed pkRoot rand : List UInt8) (layer g : Nat) (cur : List UInt8) (l : LayerXmssSig)
    (rest : List LayerXmssSig) (top : List UInt8) :
    verifyHypertreeLayers suite params pkSeed pkRoot rand layer g cur (l :: rest) = some top ↔
      ∃ mid, verifyHypertreeLayers suite params pkSeed pkRoot rand layer g cur [l] = some mid ∧
        verifyHypertreeLayers suite params pkSeed pkRoot [] (layer + 1)
          (g / 2 ^ params.subtreeHeight) mid rest = some top := by
  rw [verifyHypertreeLayers_cons, verifyHypertreeLayers_cons]
  dsimp only
  split
  · simp
  · split
    · simp
    · split
      · simp
      · simp [verifyHypertreeLayers_nil]

/-- What acceptance of a single layer signature means: the chain count is right and the WOTS+C
    public key recovered at the digits of `(cur, tswCtr)` walks up the auth path to `top`. -/
theorem verifyHypertreeLayers_single (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed pkRoot rand : List UInt8) (layer g : Nat) (cur : List UInt8) (l : LayerXmssSig)
    (top : List UInt8)
    (h : verifyHypertreeLayers suite params pkSeed pkRoot rand layer g cur [l] = some top) :
    l.wotsChains.length = params.ell1 ∧
    walkMerkleAuthPath suite pkSeed (UInt32.ofNat layer)
      (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) .tree params.subtreeHeight 0
      (g % 2 ^ params.subtreeHeight)
      (recoverWotsPkFromSig suite params pkSeed (UInt32.ofNat layer)
        (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) (g % 2 ^ params.subtreeHeight)
        (extractBaseWDigits params.w params.ell1
          (thHashMsg suite rand pkSeed pkRoot cur (UInt32.ofNat layer)
            (UInt64.ofNat (g / 2 ^ params.subtreeHeight))
            (UInt32.ofNat (g % 2 ^ params.subtreeHeight)) l.tswCtr))
        l.wotsChains) l.authPath = some top := by
  rw [verifyHypertreeLayers_cons] at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · next hLen =>
      split at h
      · cases h
      · next mid hWalk =>
        rw [verifyHypertreeLayers_nil] at h
        rw [← h]
        exact ⟨Decidable.not_not.mp hLen, hWalk⟩

/-- **A WOTS+C key position opens one way.** Two chain lists and auth paths that the verifier
    accepts at the same key position, the same digits and the same subtree root are identical,
    or a hash collision is exhibited (in the Merkle path, the public-key compression, or a
    chain). -/
theorem wots_openings_unique_or_collision
    (suite : TweakableHashSuite) (params : PqHashParams) (pkSeed : List UInt8)
    (layer : UInt32) (tree : UInt64) (kp : Nat) (digits : List Nat)
    (c₁ c₂ : List (List UInt8)) (p₁ p₂ : List (List UInt8)) (top : List UInt8)
    (hLen₁ : c₁.length = params.ell1) (hLen₂ : c₂.length = params.ell1)
    (h₁ : walkMerkleAuthPath suite pkSeed layer tree .tree params.subtreeHeight 0 kp
      (recoverWotsPkFromSig suite params pkSeed layer tree kp digits c₁) p₁ = some top)
    (h₂ : walkMerkleAuthPath suite pkSeed layer tree .tree params.subtreeHeight 0 kp
      (recoverWotsPkFromSig suite params pkSeed layer tree kp digits c₂) p₂ = some top) :
    (c₁ = c₂ ∧ p₁ = p₂) ∨ Collision suite.rawHash := by
  by_cases hPk : recoverWotsPkFromSig suite params pkSeed layer tree kp digits c₁ =
      recoverWotsPkFromSig suite params pkSeed layer tree kp digits c₂
  · by_cases hPath : p₁ = p₂
    · unfold recoverWotsPkFromSig thTweakTl at hPk
      rcases thCall_binds_or_collision suite hPk with ⟨_, _, _, hArgs⟩ | col
      · by_cases hEx : ∃ r, r < params.ell1 ∧ c₁.getD r [] ≠ c₂.getD r []
        · obtain ⟨r, hr, hNe⟩ := hEx
          have hPoint := congrArg (fun l => l.getD r []) hArgs
          simp only [recoverWotsEndpoints, list_getD_map_range params.ell1 _ [] hr] at hPoint
          exact Or.inr (extractChainCollision suite pkSeed layer tree kp r _ _ _ _ hNe
            hPoint).toCollision
        · left
          refine ⟨?_, hPath⟩
          apply List.ext_getElem (hLen₁.trans hLen₂.symm)
          intro i hi₁ hi₂
          have hi : i < params.ell1 := hLen₁ ▸ hi₁
          have hEq : c₁.getD i [] = c₂.getD i [] :=
            Decidable.not_not.mp (fun hNe => hEx ⟨i, hi, hNe⟩)
          rw [list_getD_eq_getElem c₁ [] hi₁, list_getD_eq_getElem c₂ [] hi₂] at hEq
          exact hEq
      · exact Or.inr col.toCollision
    · exact Or.inr (walkMerkleAuthPath_collision_extract suite pkSeed layer tree .tree
        params.subtreeHeight 0 kp (Or.inr hPath) h₁ h₂).toCollision
  · exact Or.inr (walkMerkleAuthPath_collision_extract suite pkSeed layer tree .tree
      params.subtreeHeight 0 kp (Or.inl hPk) h₁ h₂).toCollision

/-- One signing turn as the terminal gate sees it: the message and the candidate signature left
    in the output buffer after that turn's computation, faults included. The candidate is
    unconstrained, so every fault before the gate is covered, whatever wire it hit. -/
structure FaultedSignTurn where
  msg : List UInt8
  candidate : PqHashSig

/-- Randomness and start value the verifier feeds into the hypertree layers (the pre-hash in
    stateful mode, the recovered FORS public key in stateless mode). -/
def hypertreeStart (suite : TweakableHashSuite) (params : PqHashParams) (pk : PqPublicKey)
    (msg : List UInt8) (sig : PqHashSig) : Option (List UInt8 × List UInt8) :=
  if params.statefulJorts then
    some (sig.rRand, thPreHash suite pk.pkSeed pk.pkRoot msg)
  else
    (recoverForsPk suite params pk.pkSeed
      (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
      (sig.leafGlobalIdx % 2 ^ params.subtreeHeight)
      (thHashMsg suite sig.rRand pk.pkSeed pk.pkRoot (thPreHash suite pk.pkSeed pk.pkRoot msg) 0
        (UInt64.ofNat (sig.leafGlobalIdx / 2 ^ params.subtreeHeight))
        (UInt32.ofNat (sig.leafGlobalIdx % 2 ^ params.subtreeHeight)) sig.msgTswCtr)
      sig.forsOpenings).map fun forsPk => ([], forsPk)

/-- An accepted signature verifies through the hypertree layers from `hypertreeStart` to the
    public root. -/
theorem verifyPqHashSig_layers (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (msg : List UInt8) (sig : PqHashSig)
    (h : verifyPqHashSig suite params pk msg sig = true) :
    ∃ rand start, hypertreeStart suite params pk msg sig = some (rand, start) ∧
      verifyHypertreeLayers suite params pk.pkSeed pk.pkRoot rand 0 sig.leafGlobalIdx start
        sig.layerSigs = some pk.pkRoot ∧
      sig.layerSigs.length = params.numLayers := by
  unfold verifyPqHashSig at h
  unfold hypertreeStart
  split at h
  · cases h
  · split at h
    · cases h
    · next hLen =>
      split at h
      · cases h
      · dsimp only at h
        split at h
        · next hStateful =>
          split at h
          · cases h
          · split at h
            · next top hVer =>
              refine ⟨sig.rRand, thPreHash suite pk.pkSeed pk.pkRoot msg,
                by simp only [hStateful, ↓reduceIte], ?_, Decidable.not_not.mp hLen⟩
              rw [hVer, of_decide_eq_true h]
            · cases h
        · next hStateful =>
          split at h
          · cases h
          · split at h
            · cases h
            · next forsPk hFors =>
              split at h
              · next top hVer =>
                refine ⟨[], forsPk,
                  by simp only [hStateful, Bool.false_eq_true, ↓reduceIte, hFors, Option.map_some],
                  ?_, Decidable.not_not.mp hLen⟩
                rw [hVer, of_decide_eq_true h]
              · cases h

/-- What the terminal gate recomputes from a candidate that passed full verification. -/
structure GateView where
  upperLeaf : Nat
  lowerRoot : List UInt8
  upperSig : LayerXmssSig

def gateView (suite : TweakableHashSuite) (params : PqHashParams) (pk : PqPublicKey)
    (turn : FaultedSignTurn) : Option GateView :=
  if verifyPqHashSig suite params pk turn.msg turn.candidate then
    match hypertreeStart suite params pk turn.msg turn.candidate, turn.candidate.layerSigs with
    | some (rand, start), [lower, upper] =>
      (verifyHypertreeLayers suite params pk.pkSeed pk.pkRoot rand 0
        turn.candidate.leafGlobalIdx start [lower]).map fun root =>
          { upperLeaf := turn.candidate.leafGlobalIdx / 2 ^ params.subtreeHeight
            lowerRoot := root
            upperSig := upper }
    | _, _ => none
  else none

/-- The upper signature in a gate view is accepted by the real verifier, at the view's upper
    leaf, on the view's lower root, up to the public root. -/
theorem gateView_upper_accepts (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (turn : FaultedSignTurn) (v : GateView)
    (h : gateView suite params pk turn = some v) :
    verifyHypertreeLayers suite params pk.pkSeed pk.pkRoot [] 1 v.upperLeaf v.lowerRoot
      [v.upperSig] = some pk.pkRoot := by
  unfold gateView at h
  split at h
  · next hVerify =>
    obtain ⟨rand', start', hStart', hLayers, _⟩ :=
      verifyPqHashSig_layers suite params pk turn.msg turn.candidate hVerify
    split at h
    · next rand start lower upper hStart hSigs =>
      rw [hStart'] at hStart
      simp only [Option.some.injEq, Prod.mk.injEq] at hStart
      obtain ⟨rfl, rfl⟩ := hStart
      rw [hSigs] at hLayers
      obtain ⟨mid, hMid, hUp⟩ := (verifyHypertreeLayers_split suite params pk.pkSeed pk.pkRoot
        rand' 0 turn.candidate.leafGlobalIdx start' lower [upper] pk.pkRoot).mp hLayers
      rw [hMid] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      exact hUp
    · cases h
  · cases h

/-- The message a one-time WOTS+C key signs: the lower root together with the grinding counter
    that selects its target-sum codeword. Caching the root alone is not enough, since a fault in
    the counter grind could select a second valid codeword for the same root. -/
structure OtsMessage where
  root : List UInt8
  tswCtr : Nat
  deriving DecidableEq, Repr

/-- Write-once record of what each upper one-time key has signed. -/
abbrev OtsCache := Nat → Option OtsMessage

def OtsCache.empty : OtsCache := fun _ => none

def OtsCache.record (cache : OtsCache) (leaf : Nat) (m : OtsMessage) : OtsCache :=
  fun i => if i = leaf then some m else cache i

/-- A signature that left the device. -/
structure ReleasedSig where
  upperLeaf : Nat
  signed : OtsMessage
  upperSig : LayerXmssSig
  msg : List UInt8
  sig : PqHashSig

/-- Terminal release gate: the candidate must pass the real verifier, and the one-time message
    its upper key signs must equal the cached one for that key, if any. -/
def verifyBeforeRelease (suite : TweakableHashSuite) (params : PqHashParams) (pk : PqPublicKey)
    (cache : OtsCache) (turn : FaultedSignTurn) : Option ReleasedSig :=
  match gateView suite params pk turn with
  | none => none
  | some v =>
    match cache v.upperLeaf with
    | none =>
      some { upperLeaf := v.upperLeaf, signed := ⟨v.lowerRoot, v.upperSig.tswCtr⟩
             upperSig := v.upperSig, msg := turn.msg, sig := turn.candidate }
    | some cached =>
      if cached = ⟨v.lowerRoot, v.upperSig.tswCtr⟩ then
        some { upperLeaf := v.upperLeaf, signed := ⟨v.lowerRoot, v.upperSig.tswCtr⟩
               upperSig := v.upperSig, msg := turn.msg, sig := turn.candidate }
      else none

/-- Multi-turn guarded signer: a rejected turn releases nothing and leaves the cache alone; a
    released turn records its one-time message. -/
def guardedSignTrace (suite : TweakableHashSuite) (params : PqHashParams) (pk : PqPublicKey) :
    OtsCache → List FaultedSignTurn → List ReleasedSig
  | _, [] => []
  | cache, turn :: rest =>
    match verifyBeforeRelease suite params pk cache turn with
    | none => guardedSignTrace suite params pk cache rest
    | some r => r :: guardedSignTrace suite params pk (cache.record r.upperLeaf r.signed) rest

theorem verifyBeforeRelease_spec (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (cache : OtsCache) (turn : FaultedSignTurn) (r : ReleasedSig)
    (h : verifyBeforeRelease suite params pk cache turn = some r) :
    (∀ m, cache r.upperLeaf = some m → m = r.signed) ∧
    r.signed.tswCtr = r.upperSig.tswCtr ∧
    verifyHypertreeLayers suite params pk.pkSeed pk.pkRoot [] 1 r.upperLeaf r.signed.root
      [r.upperSig] = some pk.pkRoot := by
  unfold verifyBeforeRelease at h
  split at h
  · cases h
  · next v hView =>
    have hAcc := gateView_upper_accepts suite params pk turn v hView
    split at h
    · next hNone =>
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨fun m hm => (by rw [hNone] at hm; cases hm), rfl, hAcc⟩
    · next cached hSome =>
      split at h
      · next hEq =>
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨fun m hm => ?_, rfl, hAcc⟩
        rw [hSome] at hm
        simp only [Option.some.injEq] at hm
        rw [← hm, hEq]
      · cases h

theorem guardedSignTrace_respects_cache (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (turns : List FaultedSignTurn) :
    ∀ (cache : OtsCache) (r : ReleasedSig), r ∈ guardedSignTrace suite params pk cache turns →
      (∀ m, cache r.upperLeaf = some m → m = r.signed) ∧
      r.signed.tswCtr = r.upperSig.tswCtr ∧
      verifyHypertreeLayers suite params pk.pkSeed pk.pkRoot [] 1 r.upperLeaf r.signed.root
        [r.upperSig] = some pk.pkRoot := by
  induction turns with
  | nil => intro cache r hr; cases hr
  | cons turn rest ih =>
    intro cache r hr
    unfold guardedSignTrace at hr
    split at hr
    · exact ih cache r hr
    · next r₀ hGate =>
      obtain ⟨hCache₀, hCtr₀, hAcc₀⟩ := verifyBeforeRelease_spec suite params pk cache turn r₀ hGate
      rcases List.mem_cons.mp hr with rfl | hTail
      · exact ⟨hCache₀, hCtr₀, hAcc₀⟩
      · obtain ⟨hCache, hCtr, hAcc⟩ := ih _ r hTail
        refine ⟨fun m hm => ?_, hCtr, hAcc⟩
        by_cases hLeaf : r.upperLeaf = r₀.upperLeaf
        · have h₁ := hCache r₀.signed (by simp [OtsCache.record, hLeaf])
          rw [hLeaf] at hm
          rw [hCache₀ m hm, h₁]
        · exact hCache m (by simpa [OtsCache.record, hLeaf] using hm)

/-- **Strict one message per one-time key, across the whole trace.** Any two released signatures
    that use the same upper one-time key carry the same one-time message (lower root and
    counter), whatever the candidates of the other turns looked like. -/
theorem guarded_trace_one_message_per_wots_key (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (turns : List FaultedSignTurn) :
    ∀ (cache : OtsCache) (r₁ r₂ : ReleasedSig),
      r₁ ∈ guardedSignTrace suite params pk cache turns →
      r₂ ∈ guardedSignTrace suite params pk cache turns →
      r₁.upperLeaf = r₂.upperLeaf → r₁.signed = r₂.signed := by
  induction turns with
  | nil => intro cache r₁ r₂ h₁; cases h₁
  | cons turn rest ih =>
    intro cache r₁ r₂ h₁ h₂ hLeaf
    unfold guardedSignTrace at h₁ h₂
    split at h₁
    · next hGate =>
      rw [hGate] at h₂
      exact ih cache r₁ r₂ h₁ h₂ hLeaf
    · next r₀ hGate =>
      rw [hGate] at h₂
      have hTail : ∀ r, r ∈ guardedSignTrace suite params pk
          (cache.record r₀.upperLeaf r₀.signed) rest → r.upperLeaf = r₀.upperLeaf →
          r.signed = r₀.signed := by
        intro r hr hEq
        have h := (guardedSignTrace_respects_cache suite params pk rest _ r hr).1 r₀.signed
          (by simp [OtsCache.record, hEq])
        exact h.symm
      rcases List.mem_cons.mp h₁ with rfl | h₁' <;> rcases List.mem_cons.mp h₂ with rfl | h₂'
      · rfl
      · exact (hTail r₂ h₂' hLeaf.symm).symm
      · exact hTail r₁ h₁' hLeaf
      · exact ih _ r₁ r₂ h₁' h₂' hLeaf

/-- **Verify-before-release with the one-time-key cache makes computation faults
    non-catastrophic.** Over a trace of any length, with every candidate signature chosen by the
    fault adversary, any two released signatures that use the same upper one-time key
    1. carry the same lower root and the same grinding counter, exactly, and
    2. carry the same upper-layer signature (chain openings and auth path), unless a hash
       collision is exhibited.
    No fault before the gate can make the device release a second opening of a one-time key. -/
theorem verify_before_release_prevents_fault_wots_reuse_two_layer (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (turns : List FaultedSignTurn)
    (r₁ r₂ : ReleasedSig)
    (h₁ : r₁ ∈ guardedSignTrace suite params pk OtsCache.empty turns)
    (h₂ : r₂ ∈ guardedSignTrace suite params pk OtsCache.empty turns)
    (hLeaf : r₁.upperLeaf = r₂.upperLeaf) :
    r₁.signed = r₂.signed ∧ (r₁.upperSig = r₂.upperSig ∨ Collision suite.rawHash) := by
  have hSigned := guarded_trace_one_message_per_wots_key suite params pk turns _ r₁ r₂ h₁ h₂ hLeaf
  refine ⟨hSigned, ?_⟩
  obtain ⟨_, hCtr₁, hAcc₁⟩ := guardedSignTrace_respects_cache suite params pk turns _ r₁ h₁
  obtain ⟨_, hCtr₂, hAcc₂⟩ := guardedSignTrace_respects_cache suite params pk turns _ r₂ h₂
  obtain ⟨hLen₁, hWalk₁⟩ := verifyHypertreeLayers_single suite params pk.pkSeed pk.pkRoot [] 1
    r₁.upperLeaf r₁.signed.root r₁.upperSig pk.pkRoot hAcc₁
  obtain ⟨hLen₂, hWalk₂⟩ := verifyHypertreeLayers_single suite params pk.pkSeed pk.pkRoot [] 1
    r₂.upperLeaf r₂.signed.root r₂.upperSig pk.pkRoot hAcc₂
  have hCtr : r₁.upperSig.tswCtr = r₂.upperSig.tswCtr := by rw [← hCtr₁, ← hCtr₂, hSigned]
  rw [← hLeaf, ← hSigned, ← hCtr] at hWalk₂
  rcases wots_openings_unique_or_collision suite params pk.pkSeed _ _ _ _ _ _ _ _ _ hLen₁ hLen₂
    hWalk₁ hWalk₂ with ⟨hChains, hPath⟩ | hCol
  · left
    cases hS₁ : r₁.upperSig
    cases hS₂ : r₂.upperSig
    rw [hS₁, hS₂] at hCtr hChains hPath
    simp only at hCtr hChains hPath
    rw [hCtr, hChains, hPath]
  · exact Or.inr hCol

/-- The requested release-level reading: same upper leaf implies same released root, or a
    collision. (The root half holds outright; the disjunct is kept for the stated shape.) -/
theorem released_root_unique_or_collision (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (turns : List FaultedSignTurn)
    (r₁ r₂ : ReleasedSig)
    (h₁ : r₁ ∈ guardedSignTrace suite params pk OtsCache.empty turns)
    (h₂ : r₂ ∈ guardedSignTrace suite params pk OtsCache.empty turns)
    (hLeaf : r₁.upperLeaf = r₂.upperLeaf) :
    r₁.signed.root = r₂.signed.root ∨ Collision suite.rawHash :=
  Or.inl (congrArg OtsMessage.root
    (verify_before_release_prevents_fault_wots_reuse_two_layer suite params pk turns r₁ r₂ h₁ h₂ hLeaf).1)

/-- A signing request of the stateful two-layer signer. -/
structure SignRequest where
  msg : List UInt8
  rRand : List UInt8
  leaf : Nat

/-- Candidate left in the output buffer by one faulted signing turn. -/
def faultedCandidate (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (pk : PqPublicKey) (maxGrind : Nat) (req : SignRequest) (fault : Option CorruptedWire) :
    Option FaultedSignTurn :=
  (faultedAssemble suite params sk pk.pkRoot req.rRand maxGrind
    (thPreHash suite pk.pkSeed pk.pkRoot req.msg) req.leaf fault).map fun asm =>
      { msg := req.msg
        candidate :=
          { rRand := req.rRand, msgTswCtr := 0, leafGlobalIdx := req.leaf, forsOpenings := []
            layerSigs := asm.layerSigs } }

/-- The faulted signer driven by a per-turn fault schedule. -/
def faultedSignerTurns (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (pk : PqPublicKey) (maxGrind : Nat) (schedule : ComputeFault) :
    Turn → List SignRequest → List FaultedSignTurn
  | _, [] => []
  | t, req :: rest =>
    match faultedCandidate suite params sk pk maxGrind req (schedule t) with
    | none => faultedSignerTurns suite params sk pk maxGrind schedule (t + 1) rest
    | some turn => turn :: faultedSignerTurns suite params sk pk maxGrind schedule (t + 1) rest

/-- The guarded signer under every transient fault schedule and every request sequence: one
    one-time message and one opening per upper key, or a collision. -/
theorem guarded_signer_survives_any_fault_schedule (suite : TweakableHashSuite)
    (params : PqHashParams) (sk : PqSecretKey) (pk : PqPublicKey) (maxGrind : Nat)
    (schedule : ComputeFault) (reqs : List SignRequest) (r₁ r₂ : ReleasedSig)
    (h₁ : r₁ ∈ guardedSignTrace suite params pk OtsCache.empty
      (faultedSignerTurns suite params sk pk maxGrind schedule 0 reqs))
    (h₂ : r₂ ∈ guardedSignTrace suite params pk OtsCache.empty
      (faultedSignerTurns suite params sk pk maxGrind schedule 0 reqs))
    (hLeaf : r₁.upperLeaf = r₂.upperLeaf) :
    r₁.signed = r₂.signed ∧ (r₁.upperSig = r₂.upperSig ∨ Collision suite.rawHash) :=
  verify_before_release_prevents_fault_wots_reuse_two_layer suite params pk _ r₁ r₂ h₁ h₂ hLeaf

/-- Any signature the real verifier accepts on a two-layer hypertree is released by the gate
    from an empty cache; in particular the honest signer's output is
    (`verifyPqHashSig_evalSingleSign`). The gate is not vacuously safe. -/
theorem gate_releases_accepted_two_layer_signature (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (turn : FaultedSignTurn)
    (hLayers : params.numLayers = 2)
    (h : verifyPqHashSig suite params pk turn.msg turn.candidate = true) :
    (verifyBeforeRelease suite params pk OtsCache.empty turn).isSome = true := by
  obtain ⟨rand, start, hStart, hVer, hLen⟩ :=
    verifyPqHashSig_layers suite params pk turn.msg turn.candidate h
  rw [hLayers] at hLen
  match hSigs : turn.candidate.layerSigs, hLen with
  | [lower, upper], _ =>
    rw [hSigs] at hVer
    obtain ⟨mid, hMid, _⟩ := (verifyHypertreeLayers_split suite params pk.pkSeed pk.pkRoot rand 0
      turn.candidate.leafGlobalIdx start lower [upper] pk.pkRoot).mp hVer
    simp [verifyBeforeRelease, gateView, h, hStart, hSigs, hMid, OtsCache.empty]

/-! ### Verification alone is not enough -/

/-- The layer-0 signature of the real signer still verifies when its auth path is replaced by
    any path that the signer's own leaf node walks to some root: verification only checks that
    leaf, path and root are consistent with each other. -/
