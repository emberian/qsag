module

public import Qsag.HashSigs
public import Qsag.PosixCrashWal
public import Qsag.MaliciousSecurity
public import Qsag.ConstantTimeIsa
public import Qsag.ElfBinaryVerify
public import Qsag.ElfFixtureSlices
import Lean
import Qsag.Tactic.AssuranceKit
import all Qsag.HashSigs
import all Qsag.MaliciousSecurity
import all Qsag.ConstantTimeIsa
import all Qsag.ElfBinaryVerify
import all Qsag.ElfFixtureSlices

public section

/-!
# `Qsag.FaultAndSpeculativeSafety`: Fault Injection and Speculative Execution Boundaries

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
theorem lower_layer_verifies_on_walked_path (suite : TweakableHashSuite) (params : PqHashParams)
    (sk : PqSecretKey) (pkRoot rRand : List UInt8) (maxGrind : Nat) (mu : List UInt8) (g : Nat)
    (lower : LayerXmssSig) (path : List (List UInt8)) (root : List UInt8)
    (hLower : signHypertreeLayers suite params sk pkRoot rRand maxGrind 0 g mu 1 = some [lower])
    (hWalk : walkMerkleAuthPath suite sk.pkSeed (UInt32.ofNat 0)
      (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) .tree params.subtreeHeight 0
      (g % 2 ^ params.subtreeHeight)
      (computeWotsPk suite params sk (UInt32.ofNat 0)
        (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) (g % 2 ^ params.subtreeHeight))
      path = some root) :
    verifyHypertreeLayers suite params sk.pkSeed pkRoot rRand 0 g mu
      [{ lower with authPath := path }] = some root := by
  rw [signHypertreeLayers] at hLower
  cases hGrind : grindTswCounterAux suite params.w params.ell1 params.targetSum
      rRand sk.pkSeed pkRoot mu (UInt32.ofNat 0)
      (UInt64.ofNat (g / 2 ^ params.subtreeHeight))
      (UInt32.ofNat (g % 2 ^ params.subtreeHeight)) 0 maxGrind with
  | none => rw [hGrind] at hLower; cases hLower
  | some triple =>
    rcases triple with ⟨ctr, digits, hmsgG⟩
    rw [hGrind] at hLower
    simp only [signHypertreeLayers, Option.some.injEq, List.cons.injEq, and_true] at hLower
    subst hLower
    obtain ⟨hMsgEq, hDigEq, hChk⟩ := grindTswCounterAux_sound hGrind
    simp only [verifyHypertreeLayers]
    rw [← hMsgEq, ← hDigEq, hChk]
    have hChainsLen : ((List.range params.ell1).map fun r =>
        wotsChainSteps suite sk.pkSeed (UInt32.ofNat 0)
          (UInt64.ofNat (g / 2 ^ params.subtreeHeight))
          (g % 2 ^ params.subtreeHeight) r 0 (digits.getD r 0)
          (wotsSecretBase suite sk (UInt32.ofNat 0)
            (UInt64.ofNat (g / 2 ^ params.subtreeHeight))
            (g % 2 ^ params.subtreeHeight) r)).length = params.ell1 := by simp
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hChainsLen, ne_eq, not_true_eq_false]
    have hWotsEq := recoverWotsPkFromSig_eq_computeWotsPk suite params sk
      (UInt32.ofNat 0) (UInt64.ofNat (g / 2 ^ params.subtreeHeight))
      (g % 2 ^ params.subtreeHeight) digits hChk
    dsimp only at hWotsEq
    rw [hWotsEq, hWalk]

/-- **Tooth: sign-then-verify without the one-time-key cache does not stop grafting.** A single
    fault on a lower-tree sibling node that feeds both the emitted auth path and the root
    recomputation yields a complete two-layer signature that passes the real verifier, exactly
    like the fault-free one, while the upper one-time key has signed a different root. The only
    alternative is a hash collision. Full verification cannot tell the grafted subtree from the
    real one; the write-once cache of `verifyBeforeRelease` is what rejects it. -/
theorem tooth_verify_only_gate_releases_consistent_graft
    (suite : TweakableHashSuite) (params : PqHashParams) (sk : PqSecretKey)
    (pkRoot rRand : List UInt8) (maxGrind : Nat) (mu : List UInt8) (g level : Nat)
    (corrupt : List UInt8 → List UInt8)
    (hUpper : g / 2 ^ params.subtreeHeight < 2 ^ params.subtreeHeight)
    (honest faulted : FaultedAssembly)
    (hHonest : faultedAssemble suite params sk pkRoot rRand maxGrind mu g none = some honest)
    (hFaulted : faultedAssemble suite params sk pkRoot rRand maxGrind mu g
      (some ⟨.lowerAuthSibling level, corrupt⟩) = some faulted)
    (hVisible : faultPath (some ⟨.lowerAuthSibling level, corrupt⟩)
      (lowerAuthPath suite params sk g) ≠ lowerAuthPath suite params sk g) :
    (verifyHypertreeLayers suite params sk.pkSeed pkRoot rRand 0 g mu honest.layerSigs =
        some (computeXmssSubtreeRoot suite params sk (UInt32.ofNat 1) 0) ∧
     verifyHypertreeLayers suite params sk.pkSeed pkRoot rRand 0 g mu faulted.layerSigs =
        some (computeXmssSubtreeRoot suite params sk (UInt32.ofNat 1) 0) ∧
     Nonempty (WotsTwoMessageWitness suite params sk.pkSeed pkRoot
        (g / 2 ^ params.subtreeHeight)
        (computeXmssSubtreeRoot suite params sk (UInt32.ofNat 1) 0))) ∨
      Collision suite.rawHash := by
  obtain ⟨lower₁, upper₁, wires₁, hLower₁, hWires₁, hRoot₁, hSigs₁, hAcc₁⟩ :=
    faultedAssemble_upper_accepts suite params sk pkRoot rRand maxGrind mu g none honest hUpper
      (fun _ => rfl) hHonest
  obtain ⟨lower₂, upper₂, wires₂, hLower₂, hWires₂, hRoot₂, hSigs₂, hAcc₂⟩ :=
    faultedAssemble_upper_accepts suite params sk pkRoot rRand maxGrind mu g _ faulted hUpper
      (fun _ => rfl) hFaulted
  rw [faultedLowerWires_none] at hWires₁
  simp only [Option.some.injEq] at hWires₁
  subst hWires₁
  unfold faultedLowerWires at hWires₂
  simp only [faultLeaf, faultRoot, Option.map_eq_some_iff] at hWires₂
  obtain ⟨r₂, hWalk₂, hW₂⟩ := hWires₂
  subst hW₂
  have hWalk₁ := lowerWalk_honest suite params sk g
  by_cases hEq : r₂ = computeXmssSubtreeRoot suite params sk (UInt32.ofNat 0)
      (UInt64.ofNat (g / 2 ^ params.subtreeHeight))
  · right
    rw [hEq] at hWalk₂
    exact (walkMerkleAuthPath_collision_extract suite sk.pkSeed (UInt32.ofNat 0)
      (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) .tree params.subtreeHeight 0
      (g % 2 ^ params.subtreeHeight) (Or.inr hVisible) hWalk₂ hWalk₁).toCollision
  · left
    have hV₁ := lower_layer_verifies_on_walked_path suite params sk pkRoot rRand maxGrind mu g
      lower₁ _ _ hLower₁ hWalk₁
    have hV₂ := lower_layer_verifies_on_walked_path suite params sk pkRoot rRand maxGrind mu g
      lower₂ _ _ hLower₂ hWalk₂
    rw [hRoot₁] at hAcc₁
    rw [hRoot₂] at hAcc₂
    refine ⟨?_, ?_, ⟨{ root₁ := _, root₂ := _, sig₁ := upper₁, sig₂ := upper₂
                       roots_ne := fun h => hEq h.symm, accepts₁ := hAcc₁, accepts₂ := hAcc₂ }⟩⟩
    · rw [hSigs₁]
      exact (verifyHypertreeLayers_split suite params sk.pkSeed pkRoot rRand 0 g mu _ [upper₁]
        _).mpr ⟨_, hV₁, hAcc₁⟩
    · rw [hSigs₂]
      exact (verifyHypertreeLayers_split suite params sk.pkSeed pkRoot rRand 0 g mu _ [upper₂]
        _).mpr ⟨_, hV₂, hAcc₂⟩

/-! ### BDOZ MAC gate on a faulted party share -/

/-- Share-release gate of a threshold party: the share leaves only if its two-lane BDOZ MAC
    verifies under the receiver's keys. -/
def bdozGatedShareRelease (vk : BdozVerifierKeys) (op : BdozPairOpening) : Option Tower128 :=
  if verifyBdozPairMac vk op then some op.shareX else none

/-- The gate releases the dealt share of an honest, unfaulted party. -/
theorem bdozGatedShareRelease_honest (vk : BdozVerifierKeys) (j : Nat) (x : Tower128) :
    bdozGatedShareRelease vk (bdozHonestOpening vk j x) = some x := by
  unfold bdozGatedShareRelease
  rw [bdozHonestOpening_accepted]
  rfl

/-- **BDOZ MAC blocks release of faulted shares, across a whole trace.** Let `faulted` be the
    openings a party's faulted computation produced over any number of turns, each with a share
    different from the dealt one and with arbitrarily corrupted tags. If the gate releases any of
    them under global key `alpha`, then `alpha` is one of the `faulted.length` key guesses that
    `bdozKeyGuess` computes from the faulted openings and the party's own view. The faults do not
    depend on the key, so at most `N` of the `2^256` two-lane keys (one in `2^128` per lane and
    per turn) let a faulted share out. -/
theorem bdoz_mac_blocks_faulted_party_share_release
    (hon : Nat → Tower128 × Tower128 × Tower128) (faulted : List BdozPairOpening)
    (hFault : ∀ op ∈ faulted, op.shareX ≠ (hon op.partyId).1)
    (alpha : Tower128 × Tower128)
    (hRelease : ∃ op ∈ faulted,
      (bdozGatedShareRelease (bdozKeyFromView alpha hon) op).isSome = true) :
    alpha ∈ faulted.map (bdozKeyGuess hon) := by
  obtain ⟨op, hMem, hSome⟩ := hRelease
  have hAcc : verifyBdozPairMac (bdozKeyFromView alpha hon) op = true := by
    unfold bdozGatedShareRelease at hSome
    cases hV : verifyBdozPairMac (bdozKeyFromView alpha hon) op
    · rw [hV] at hSome
      cases hSome
    · rfl
  exact List.mem_map.mpr ⟨op, hMem, (bdoz_forgery_pins_key alpha hon op (hFault op hMem) hAcc).symm⟩

/-! ## 3. The Physical Boundary: Dual Glitch on the Release Gate -/

/-- Instructions of a software release gate over an output register of type `α`: a pure
    computation step, a conditional abort on a pure predicate, and the release itself. -/
inductive GateInstr (α : Type) where
  | step (f : α → α)
  | check (p : α → Bool)
  | emit

/-- A physical glitch on one instruction slot: optionally upset the register, and optionally
    skip the instruction (`PC → PC + 1` without executing it, which for a `check` is the same as
    forcing its decision bit). -/
structure Glitch (α : Type) where
  upset : Option α
  skip : Bool

abbrev GlitchSchedule (α : Type) := Nat → Option (Glitch α)

def Glitch.applyUpset {α : Type} (g : Option (Glitch α)) (reg : α) : α :=
  match g with
  | some ⟨some v, _⟩ => v
  | _ => reg

def Glitch.skips {α : Type} (g : Option (Glitch α)) : Bool :=
  match g with
  | some ⟨_, true⟩ => true
  | _ => false

/-- Run a release gate under a glitch schedule. `none` means nothing was released. -/
def runGate {α : Type} (sched : GlitchSchedule α) : List (GateInstr α) → Nat → α → Option α
  | [], _, _ => none
  | ins :: rest, pc, reg =>
    if Glitch.skips (sched pc) then runGate sched rest (pc + 1) (Glitch.applyUpset (sched pc) reg)
    else
      match ins with
      | .step f => runGate sched rest (pc + 1) (f (Glitch.applyUpset (sched pc) reg))
      | .check p =>
        if p (Glitch.applyUpset (sched pc) reg) then
          runGate sched rest (pc + 1) (Glitch.applyUpset (sched pc) reg)
        else none
      | .emit => some (Glitch.applyUpset (sched pc) reg)

/-- **Software side of the boundary.** If the gate ends in `check p; emit`, has no earlier
    `emit`, and the last two instruction slots are not glitched, then whatever is released
    satisfies `p`. Every glitch before the terminal check is tolerated: register upsets, skipped
    computation, skipped earlier checks. -/
theorem terminal_check_holds_when_gate_tail_unglitched {α : Type} (p : α → Bool)
    (sched : GlitchSchedule α) (out : α) :
    ∀ (pre : List (GateInstr α)) (pc : Nat) (reg : α),
      GateInstr.emit ∉ pre →
      sched (pc + pre.length) = none → sched (pc + pre.length + 1) = none →
      runGate sched (pre ++ [.check p, .emit]) pc reg = some out → p out = true
  | [], pc, reg, _, hCheck, hEmit, hRun => by
    simp only [List.length_nil, Nat.add_zero] at hCheck hEmit
    simp only [List.nil_append, runGate, hCheck, hEmit, Glitch.skips, Glitch.applyUpset,
      Bool.false_eq_true, ↓reduceIte] at hRun
    split at hRun
    · next hp =>
      simp only [Option.some.injEq] at hRun
      rw [← hRun]
      exact hp
    · cases hRun
  | ins :: rest, pc, reg, hNoEmit, hCheck, hEmit, hRun => by
    have hRest : GateInstr.emit ∉ rest := fun hi => hNoEmit (List.mem_cons_of_mem _ hi)
    have hCheck' : sched (pc + 1 + rest.length) = none := by
      rw [← hCheck]; congr 1; simp only [List.length_cons]; omega
    have hEmit' : sched (pc + 1 + rest.length + 1) = none := by
      rw [← hEmit]; congr 1; simp only [List.length_cons]; omega
    simp only [List.cons_append, runGate] at hRun
    split at hRun
    · exact terminal_check_holds_when_gate_tail_unglitched p sched out rest (pc + 1) _ hRest
        hCheck' hEmit' hRun
    · cases ins with
      | step f =>
        exact terminal_check_holds_when_gate_tail_unglitched p sched out rest (pc + 1) _ hRest
          hCheck' hEmit' hRun
      | check q =>
        simp only at hRun
        split at hRun
        · exact terminal_check_holds_when_gate_tail_unglitched p sched out rest (pc + 1) _ hRest
            hCheck' hEmit' hRun
        · cases hRun
      | emit =>
        exact absurd List.mem_cons_self hNoEmit

/-- The dual-glitch schedule against a gate whose first `emit` sits at slot `n`: upset the
    register to `target` at slot `0`, and skip every slot before `n`. -/
def dualGlitchSchedule {α : Type} (n : Nat) (target : α) : GlitchSchedule α :=
  fun pc => some { upset := if pc = 0 then some target else none, skip := decide (pc < n) }

theorem runGate_dualGlitch_tail {α : Type} (target : α) (post : List (GateInstr α)) (n : Nat) :
    ∀ (pre : List (GateInstr α)) (pc : Nat), 0 < pc → pc + pre.length = n →
      runGate (dualGlitchSchedule n target) (pre ++ GateInstr.emit :: post) pc target =
        some target
  | [], pc, hPos, hLen => by
    have hpc : pc = n := by simpa using hLen
    have hne : ¬ pc = 0 := by omega
    simp [runGate, dualGlitchSchedule, Glitch.skips, Glitch.applyUpset, hpc ▸ hne, hpc]
  | ins :: rest, pc, hPos, hLen => by
    have hlt : pc < n := by simp only [List.length_cons] at hLen; omega
    have hne : ¬ pc = 0 := by omega
    have ih := runGate_dualGlitch_tail target post n rest (pc + 1) (by omega)
      (by simp only [List.length_cons] at hLen; omega)
    simp [runGate, dualGlitchSchedule, Glitch.skips, Glitch.applyUpset, hlt, hne]
    simpa [dualGlitchSchedule] using ih

/-- **Physical side of the boundary: no software gate survives a dual glitch.** For every gate
    program that can release at all (it contains an `emit`), whatever pure predicates it checks
    and however often, and for every target value, there is a glitch schedule that upsets the
    register once, before any check has run, and otherwise only skips instructions, under which
    the gate releases the target. The predicates are never evaluated on it, so no choice of
    predicate helps: the release decision itself has to be protected physically. -/
theorem dual_glitch_control_flow_bypass_impossibility {α : Type} (prog : List (GateInstr α))
    (hEmit : GateInstr.emit ∈ prog) (reg target : α) :
    ∃ sched : GlitchSchedule α,
      (∀ pc g, 0 < pc → sched pc = some g → g.upset = none) ∧
      runGate sched prog 0 reg = some target := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hEmit
  refine ⟨dualGlitchSchedule pre.length target, ?_, ?_⟩
  · intro pc g hPos hg
    have hne : ¬ pc = 0 := by omega
    simp only [dualGlitchSchedule, hne, ↓reduceIte, Option.some.injEq] at hg
    rw [← hg]
  · cases pre with
    | nil => simp [runGate, dualGlitchSchedule, Glitch.skips, Glitch.applyUpset]
    | cons ins rest =>
      have ih := runGate_dualGlitch_tail target post (rest.length + 1) rest 1 (by omega)
        (by omega)
      simp [runGate, dualGlitchSchedule, Glitch.skips, Glitch.applyUpset]
      simpa [dualGlitchSchedule] using ih

/-- The canonical verify-then-release gate falls to one dual glitch on its check slot, for every
    predicate, every honest register content and every target. -/
theorem single_dual_glitch_defeats_any_predicate {α : Type} (p : α → Bool) (reg target : α) :
    runGate (dualGlitchSchedule 1 target) [.check p, .emit] 0 reg = some target := by
  simp [runGate, dualGlitchSchedule, Glitch.skips, Glitch.applyUpset]

/-- The signing gate of Section 2 as a gate program over the output buffer. -/
def signReleaseGate (suite : TweakableHashSuite) (params : PqHashParams) (pk : PqPublicKey)
    (cache : OtsCache) : List (GateInstr FaultedSignTurn) :=
  [.check (fun turn => (verifyBeforeRelease suite params pk cache turn).isSome), .emit]

/-- **The exact line for the signer.** Without a glitch on its two slots, the signing gate only
    releases candidates that `verifyBeforeRelease` accepts (so Section 2 applies); with one dual
    glitch it releases any candidate at all, including a grafted one the gate would reject. -/
theorem sign_release_gate_boundary (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (cache : OtsCache) :
    (∀ (sched : GlitchSchedule FaultedSignTurn) (buf out : FaultedSignTurn),
      sched 0 = none → sched 1 = none →
      runGate sched (signReleaseGate suite params pk cache) 0 buf = some out →
      (verifyBeforeRelease suite params pk cache out).isSome = true) ∧
    (∀ buf bad : FaultedSignTurn,
      runGate (dualGlitchSchedule 1 bad) (signReleaseGate suite params pk cache) 0 buf =
        some bad) := by
  refine ⟨?_, ?_⟩
  · intro sched buf out h0 h1 hRun
    exact terminal_check_holds_when_gate_tail_unglitched _ sched out [] 0 buf
      List.not_mem_nil h0 h1 hRun
  · intro buf bad
    exact single_dual_glitch_defeats_any_predicate _ buf bad
/-! ## 4. Speculative Execution: Branch-Misprediction Shadow Semantics -/

/-- Conditional-branch conditions of the speculative ISA layer. `nz r` is the
    `test r, r; jnz` idiom; `below` / `aboveEq` read the carry flag left by `sub64`. -/
inductive BranchCond where
  | nz (r : X86Gpr)
  | below
  | aboveEq
  deriving DecidableEq, Repr

def BranchCond.eval (c : BranchCond) (st : ConstantTimeIsa.X86State) : Bool :=
  match c with
  | .nz r => st.gpr r != 0#64
  | .below => st.flags.cf
  | .aboveEq => !st.flags.cf

/-- Speculative ISA layer over the constant-time `ConstantTimeIsa.X86Instr` set: every non-branching instruction
    is an `op`, `jcc c skip` jumps forward over `skip` instructions when `c` holds, `lfence` is a
    speculation barrier, and `ret` ends the kernel. -/
inductive SpecInstr where
  | op (i : ConstantTimeIsa.X86Instr)
  | jcc (c : BranchCond) (skip : Nat)
  | lfence
  | ret
  deriving DecidableEq, Repr

abbrev Code := List SpecInstr

/-- Adversarial branch predictor: any function of the branch address and the history of
    directions it has seen. The same oracle is used on both runs of a non-interference pair. -/
abbrev PredictorOracle := Nat → List Bool → Bool

/-- Attacker-visible observation: an architecturally committed leakage event, or one emitted by
    a transient (later squashed) instruction. -/
inductive SpecObs where
  | arch (ev : LeakageEvent)
  | transient (ev : LeakageEvent)
  deriving DecidableEq, Repr

def branchEvent (pc : Nat) (taken : Bool) : LeakageEvent :=
  { pc := pc
    branchTaken := some taken
    memAddrs := []
    varLatencyOperands := []
    dirtyUpperYmmOnRet := false }

def retEvent (pc : Nat) (st : ConstantTimeIsa.X86State) : LeakageEvent :=
  { pc := pc
    branchTaken := none
    memAddrs := []
    varLatencyOperands := []
    dirtyUpperYmmOnRet := st.ymmUpperDirty }

/-- Transient execution down a mispredicted path. Runs on a shadow copy of the state for at most
    `W` executed instructions, recording every leakage event (load/store addresses and
    variable-latency operands included). Nested branches follow the predictor. `lfence` and `ret`
    end the window; `skip` counts instructions still to be jumped over. -/
def transientWindow (pred : PredictorOracle) :
    Code → Nat → Nat → Nat → List Bool → ConstantTimeIsa.X86State → List LeakageEvent
  | [], _, _, _, _, _ => []
  | _ :: rest, skip + 1, W, pc, hist, st => transientWindow pred rest skip W (pc + 1) hist st
  | _ :: _, 0, 0, _, _, _ => []
  | ins :: rest, 0, W + 1, pc, hist, st =>
    match ins with
    | .op i =>
      (execX86Instr i pc st).2 ::
        transientWindow pred rest 0 W (pc + 1) hist (execX86Instr i pc st).1
    | .jcc _ k =>
      branchEvent pc (pred pc hist) ::
        transientWindow pred rest (if pred pc hist then k else 0) W (pc + 1)
          (pred pc hist :: hist) st
    | .lfence => []
    | .ret => [retEvent pc st]

/-- Speculative machine. At each `jcc` the predictor guesses; on a wrong guess the machine first
    runs `transientWindow` along the wrong direction, then rolls back to the architectural state
    and continues along the right one. -/
def specRun (pred : PredictorOracle) (W : Nat) :
    Code → Nat → Nat → List Bool → ConstantTimeIsa.X86State → List SpecObs
  | [], _, _, _, _ => []
  | _ :: rest, skip + 1, pc, hist, st => specRun pred W rest skip (pc + 1) hist st
  | ins :: rest, 0, pc, hist, st =>
    match ins with
    | .op i =>
      .arch (execX86Instr i pc st).2 ::
        specRun pred W rest 0 (pc + 1) hist (execX86Instr i pc st).1
    | .jcc c k =>
      .arch (branchEvent pc (c.eval st)) ::
        ((if pred pc hist = c.eval st then []
          else transientWindow pred rest (if pred pc hist then k else 0) W (pc + 1)
            (pred pc hist :: hist) st).map .transient ++
         specRun pred W rest (if c.eval st then k else 0) (pc + 1) (c.eval st :: hist) st)
    | .lfence => specRun pred W rest 0 (pc + 1) hist st
    | .ret => [.arch (retEvent pc st)]

def execSpeculativeWindow (prog : Code) (W : Nat) (pred : PredictorOracle) (st : ConstantTimeIsa.X86State) :
    List SpecObs :=
  specRun pred W prog 0 0 [] st

def execSpeculativeObs (prog : Code) (st : ConstantTimeIsa.X86State) (pred : PredictorOracle) (W : Nat) :
    List SpecObs :=
  execSpeculativeWindow prog W pred st

/-- Branch-free code: a block of constant-time ISA instructions. -/
def straightline (blk : List ConstantTimeIsa.X86Instr) : Code := blk.map .op

theorem specRun_straightline_append (pred : PredictorOracle) (W : Nat) (blk : List ConstantTimeIsa.X86Instr)
    (rest : Code) (pc : Nat) (hist : List Bool) (st : ConstantTimeIsa.X86State) :
    specRun pred W (straightline blk ++ rest) 0 pc hist st =
      (execX86Block blk pc st).2.map .arch ++
        specRun pred W rest 0 (pc + blk.length) hist (execX86Block blk pc st).1 := by
  induction blk generalizing pc st with
  | nil => simp [straightline, execX86Block]
  | cons ins tl ih =>
    have ih' := ih (pc + 1) (execX86Instr ins pc st).1
    simp only [straightline] at ih' ⊢
    simp only [List.map_cons, List.cons_append, specRun, execX86Block, ih', List.length_cons,
      Nat.add_assoc, Nat.add_comm 1]

theorem specRun_straightline (pred : PredictorOracle) (W : Nat) (blk : List ConstantTimeIsa.X86Instr)
    (pc : Nat) (hist : List Bool) (st : ConstantTimeIsa.X86State) :
    specRun pred W (straightline blk) 0 pc hist st = (execX86Block blk pc st).2.map .arch := by
  have h := specRun_straightline_append pred W blk [] pc hist st
  simpa [specRun] using h

theorem specRun_skip_all (pred : PredictorOracle) (W : Nat) (code : Code)
    (pc : Nat) (hist : List Bool) (st : ConstantTimeIsa.X86State) :
    specRun pred W code code.length pc hist st = [] := by
  induction code generalizing pc with
  | nil => simp [specRun]
  | cons ins tl ih => simp only [List.length_cons, specRun, ih]

theorem transientWindow_straightline (pred : PredictorOracle) (blk : List ConstantTimeIsa.X86Instr) (W : Nat)
    (pc : Nat) (hist : List Bool) (st : ConstantTimeIsa.X86State) :
    transientWindow pred (straightline blk) 0 W pc hist st = (execX86Block blk pc st).2.take W := by
  induction blk generalizing W pc st with
  | nil => cases W <;> simp [straightline, execX86Block, transientWindow]
  | cons ins tl ih =>
    cases W with
    | zero => simp [straightline, transientWindow]
    | succ n =>
      have ih' := ih n (pc + 1) (execX86Instr ins pc st).1
      simp only [straightline] at ih' ⊢
      simp only [List.map_cons, transientWindow, execX86Block, ih', List.take_succ_cons]

theorem transientWindow_skip_all (pred : PredictorOracle) (code : Code) (W : Nat)
    (pc : Nat) (hist : List Bool) (st : ConstantTimeIsa.X86State) :
    transientWindow pred code code.length W pc hist st = [] := by
  induction code generalizing pc with
  | nil => simp [transientWindow]
  | cons ins tl ih => simp only [List.length_cons, transientWindow, ih]

/-- Embed a `ConstantTimeIsa` program that has no `jccNz` and no `pubLoop` back-edge. -/
def compileStraight : List X86Stmt → Option Code
  | [] => some []
  | .instr i :: rest => (compileStraight rest).map (SpecInstr.op i :: ·)
  | .ret :: _ => some [.ret]
  | .jccNz _ _ _ :: _ => none
  | .pubLoop _ _ :: _ => none

/-- On branch-free code the speculative machine emits exactly the architectural leakage trace of
    `execX86Prog`, for every predictor and every window: there is no branch to mispredict. -/
theorem straightline_speculation_is_architectural (pred : PredictorOracle) (W : Nat) :
    ∀ (prog : List X86Stmt) (code : Code) (pc : Nat) (hist : List Bool) (st : ConstantTimeIsa.X86State),
      compileStraight prog = some code →
      specRun pred W code 0 pc hist st = (execX86Prog prog pc st).2.map .arch
  | [], code, pc, hist, st, h => by
    simp only [compileStraight, Option.some.injEq] at h
    subst h
    simp [specRun, execX86Prog]
  | .instr i :: rest, code, pc, hist, st, h => by
    simp only [compileStraight, Option.map_eq_some_iff] at h
    obtain ⟨tl, hTl, rfl⟩ := h
    have ih := straightline_speculation_is_architectural pred W rest tl (pc + 1) hist
      (execX86Instr i pc st).1 hTl
    simp only [specRun, execX86Prog, ih, List.map_cons]
  | .ret :: _, code, pc, hist, st, h => by
    simp only [compileStraight, Option.some.injEq] at h
    subst h
    simp [specRun, execX86Prog, retEvent]
  | .jccNz _ _ _ :: _, _, _, _, _, h => by simp [compileStraight] at h
  | .pubLoop _ _ :: _, _, _, _, _, h => by simp [compileStraight] at h

/-- **Unbounded speculative non-interference of branch-free constant-time kernels.** A program
    accepted by the `ConstantTimeIsa` taint checker that contains no conditional branch emits the
    same speculative observation trace on any two states that agree on public inputs, for every
    speculation window `W` and every adversarial predictor. -/
theorem straightline_ct_implies_unbounded_speculative_ni
    (memPol : BitVec 64 → SecLabel) (secHeap : Bool)
    (hPol : secHeap = true → ∀ a, memPol a = .sec)
    (prog : List X86Stmt) (code : Code) (τ τ' : X86TaintState)
    (hStraight : compileStraight prog = some code)
    (hCheck : checkX86Prog secHeap τ prog = some τ')
    (s₁ s₂ : ConstantTimeIsa.X86State) (hLow : X86LowEq memPol τ s₁ s₂)
    (pred : PredictorOracle) (W : Nat) :
    execSpeculativeObs code s₁ pred W = execSpeculativeObs code s₂ pred W := by
  unfold execSpeculativeObs execSpeculativeWindow
  rw [straightline_speculation_is_architectural pred W prog code 0 [] s₁ hStraight,
    straightline_speculation_is_architectural pred W prog code 0 [] s₂ hStraight,
    (x86_ct_checker_sound memPol secHeap hPol prog τ τ' 0 hCheck s₁ s₂ hLow).1]

/-- `ct_eq_bytes32` (`ctEq32X86Prog`) as speculative code. -/
def ctEq32SpecCode : Code := (compileStraight ctEq32X86Prog).getD []

/-- Canonical Goldilocks multiplication (`goldilocksMulCtX86Prog`) as speculative code. -/
def goldilocksMulSpecCode : Code := (compileStraight goldilocksMulCtX86Prog).getD []

theorem ctEq32_unbounded_speculative_ni (s₁ s₂ : ConstantTimeIsa.X86State)
    (hLow : X86LowEq (fun _ => .sec) sysvPtrArgs4Taint s₁ s₂)
    (pred : PredictorOracle) (W : Nat) :
    execSpeculativeObs ctEq32SpecCode s₁ pred W = execSpeculativeObs ctEq32SpecCode s₂ pred W := by
  have hChk : ∃ τOut, checkX86Prog true sysvPtrArgs4Taint ctEq32X86Prog = some τOut := ⟨_, rfl⟩
  rcases hChk with ⟨τOut, hOpt⟩
  exact straightline_ct_implies_unbounded_speculative_ni (fun _ => .sec) true (fun _ _ => rfl)
    ctEq32X86Prog ctEq32SpecCode sysvPtrArgs4Taint τOut rfl hOpt s₁ s₂ hLow pred W

theorem goldilocksMul_unbounded_speculative_ni (s₁ s₂ : ConstantTimeIsa.X86State)
    (hLow : X86LowEq (fun _ => .sec) glAllSecretX86Taint s₁ s₂)
    (pred : PredictorOracle) (W : Nat) :
    execSpeculativeObs goldilocksMulSpecCode s₁ pred W =
      execSpeculativeObs goldilocksMulSpecCode s₂ pred W := by
  have hChk : ∃ τOut, checkX86Prog true glAllSecretX86Taint goldilocksMulCtX86Prog = some τOut :=
    ⟨_, rfl⟩
  rcases hChk with ⟨τOut, hOpt⟩
  exact straightline_ct_implies_unbounded_speculative_ni (fun _ => .sec) true (fun _ _ => rfl)
    goldilocksMulCtX86Prog goldilocksMulSpecCode glAllSecretX86Taint τOut rfl hOpt s₁ s₂ hLow pred W

/-! ### Bounds-checked table lookup: Spectre-v1 leak, SLH mask, `lfence` -/

/-- `pre; jcc c over body; body`: a block guarded by one forward conditional branch. -/
def guardedBlock (pre : List ConstantTimeIsa.X86Instr) (c : BranchCond) (body : List ConstantTimeIsa.X86Instr) : Code :=
  straightline pre ++ .jcc c body.length :: straightline body

/-- The same guard with an `lfence` as the first instruction of the guarded body. -/
def guardedBlockLfence (pre : List ConstantTimeIsa.X86Instr) (c : BranchCond) (body : List ConstantTimeIsa.X86Instr) : Code :=
  straightline pre ++ .jcc c (body.length + 1) :: .lfence :: straightline body

/-- Closed form of the speculative trace of a guarded block: the only transient events are the
    first `W` events of the body, run on the pre-branch state, when the branch is architecturally
    taken (body skipped) and the predictor says not-taken. -/
theorem execSpeculativeObs_guardedBlock (pre : List ConstantTimeIsa.X86Instr) (c : BranchCond)
    (body : List ConstantTimeIsa.X86Instr) (st : ConstantTimeIsa.X86State) (pred : PredictorOracle) (W : Nat) :
    execSpeculativeObs (guardedBlock pre c body) st pred W =
      (execX86Block pre 0 st).2.map .arch ++
        .arch (branchEvent pre.length (c.eval (execX86Block pre 0 st).1)) ::
          ((if pred pre.length [] = c.eval (execX86Block pre 0 st).1 then []
            else if pred pre.length [] then []
            else (execX86Block body (pre.length + 1) (execX86Block pre 0 st).1).2.take W).map
              .transient ++
           (if c.eval (execX86Block pre 0 st).1 then []
            else (execX86Block body (pre.length + 1) (execX86Block pre 0 st).1).2.map .arch)) := by
  unfold execSpeculativeObs execSpeculativeWindow guardedBlock
  rw [specRun_straightline_append]
  simp only [specRun, Nat.zero_add]
  have hLen : (straightline body).length = body.length := by simp [straightline]
  cases hG : pred pre.length [] <;> cases hA : c.eval (execX86Block pre 0 st).1 <;>
    simp [transientWindow_straightline, specRun_straightline,
      ← hLen, transientWindow_skip_all, specRun_skip_all]

theorem execX86Block_trace_length (blk : List ConstantTimeIsa.X86Instr) (pc : Nat) (st : ConstantTimeIsa.X86State) :
    (execX86Block blk pc st).2.length = blk.length := by
  induction blk generalizing pc st with
  | nil => rfl
  | cons ins tl ih => simp only [execX86Block, List.length_cons, ih]

/-- A speculation window longer than the guarded body adds nothing: the transient run ends when
    the body does. -/
theorem guardedBlock_window_saturates (pre : List ConstantTimeIsa.X86Instr) (c : BranchCond)
    (body : List ConstantTimeIsa.X86Instr) (st : ConstantTimeIsa.X86State) (pred : PredictorOracle) (W : Nat)
    (hW : body.length ≤ W) :
    execSpeculativeObs (guardedBlock pre c body) st pred W =
      execSpeculativeObs (guardedBlock pre c body) st pred body.length := by
  rw [execSpeculativeObs_guardedBlock, execSpeculativeObs_guardedBlock,
    List.take_of_length_le (by rw [execX86Block_trace_length]; exact hW),
    List.take_of_length_le (by rw [execX86Block_trace_length]; exact Nat.le_refl _)]

/-- With `lfence` at the head of the guarded body there are no transient events at all: the
    trace is independent of the predictor and of the speculation window. -/
theorem execSpeculativeObs_guardedBlockLfence (pre : List ConstantTimeIsa.X86Instr) (c : BranchCond)
    (body : List ConstantTimeIsa.X86Instr) (st : ConstantTimeIsa.X86State) (pred : PredictorOracle) (W : Nat) :
    execSpeculativeObs (guardedBlockLfence pre c body) st pred W =
      (execX86Block pre 0 st).2.map .arch ++
        .arch (branchEvent pre.length (c.eval (execX86Block pre 0 st).1)) ::
          (if c.eval (execX86Block pre 0 st).1 then []
           else (execX86Block body (pre.length + 2) (execX86Block pre 0 st).1).2.map .arch) := by
  unfold execSpeculativeObs execSpeculativeWindow guardedBlockLfence
  rw [specRun_straightline_append]
  simp only [specRun, Nat.zero_add]
  have hLen : (SpecInstr.lfence :: straightline body).length = body.length + 1 := by
    simp [straightline]
  cases hG : pred pre.length [] <;> cases hA : c.eval (execX86Block pre 0 st).1 <;>
    cases W <;>
    simp [transientWindow, specRun, specRun_straightline,
      ← hLen, transientWindow_skip_all, specRun_skip_all]

/-- Bounds-check prefix: `rax := idx - len`, leaving `cf = (idx < len)`. -/
def boundsCheckPre : List ConstantTimeIsa.X86Instr :=
  [.movReg64 .rax .rdi, .sub64 .rax .rsi]

/-- Unhardened body: `rcx := arr[idx]; r8 := table[rcx]`. -/
def boundsLookupBody : List ConstantTimeIsa.X86Instr :=
  [.loadIndexed64 .rcx .rdx .rdi 8#64, .loadIndexed64 .r8 .rbx .rcx 8#64]

/-- `if idx < pub_len then table[arr[idx]]` with `idx = rdi`, `pub_len = rsi`, `arr = rdx`,
    `table = rbx`, compiled to a compare and a forward `jae`. -/
def unmaskedBoundsProg : Code := guardedBlock boundsCheckPre .aboveEq boundsLookupBody

/-- The same lookup with `lfence` after the bounds branch. -/
def lfenceBoundsProg : Code := guardedBlockLfence boundsCheckPre .aboveEq boundsLookupBody

/-- Speculative-load-hardening prefix: the predicate mask `r9 := cf ? allOnes : 0` is computed
    from the comparison itself by `sbb`, so it carries the true bounds predicate into whichever
    direction the predictor sends execution. -/
def slhPre : List ConstantTimeIsa.X86Instr :=
  [.movReg64 .rax .rdi, .sub64 .rax .rsi, .sbbSelf64 .r9]

/-- Hardened body: the index is masked before the first load. -/
def slhBody : List ConstantTimeIsa.X86Instr :=
  [.and64 .rdi .r9, .loadIndexed64 .rcx .rdx .rdi 8#64, .loadIndexed64 .r8 .rbx .rcx 8#64]

def slhMaskedBoundsProg : Code := guardedBlock slhPre .aboveEq slhBody

/-- Public view of the lookup: all registers (index, length, both base pointers) and the
    in-bounds cells `arr[0 .. pub_len)`. Every other memory cell, including everything past the
    end of `arr`, is secret. -/
def BoundsLowEq (s₁ s₂ : ConstantTimeIsa.X86State) : Prop :=
  s₁.gpr = s₂.gpr ∧
  ∀ i : BitVec 64, i.toNat < (s₁.gpr .rsi).toNat →
    s₁.mem (s₁.gpr .rdx + i * 8#64) = s₂.mem (s₁.gpr .rdx + i * 8#64)

/-- The SLH-masked index: `idx` when in bounds, `0` otherwise. -/
def slhIndex (st : ConstantTimeIsa.X86State) : BitVec 64 :=
  st.gpr .rdi &&& (if (st.gpr .rdi).toNat < (st.gpr .rsi).toNat then 0xFFFFFFFFFFFFFFFF#64 else 0#64)

theorem slhIndex_in_bounds (st : ConstantTimeIsa.X86State) (hLen : 0 < (st.gpr .rsi).toNat) :
    (slhIndex st).toNat < (st.gpr .rsi).toNat := by
  unfold slhIndex
  rw [BitVec.toNat_and]
  by_cases h : (st.gpr .rdi).toNat < (st.gpr .rsi).toNat
  · exact Nat.lt_of_le_of_lt Nat.and_le_left h
  · simp only [h, ↓reduceIte]
    exact Nat.lt_of_le_of_lt Nat.and_le_right hLen

theorem boundsCheck_exec (st : ConstantTimeIsa.X86State) :
    (execX86Block boundsCheckPre 0 st).2 = [LeakageEvent.clean 0, LeakageEvent.clean 1] ∧
    BranchCond.aboveEq.eval (execX86Block boundsCheckPre 0 st).1 =
      !decide ((st.gpr .rdi).toNat < (st.gpr .rsi).toNat) ∧
    ∀ pc, (execX86Block boundsLookupBody pc (execX86Block boundsCheckPre 0 st).1).2 =
      [LeakageEvent.clean pc [st.gpr .rdx + st.gpr .rdi * 8#64],
       LeakageEvent.clean (pc + 1)
         [st.gpr .rbx + st.mem (st.gpr .rdx + st.gpr .rdi * 8#64) * 8#64]] := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [boundsCheckPre, boundsLookupBody, execX86Block, execX86Instr, ConstantTimeIsa.X86State.setGpr,
      BranchCond.eval]

theorem slh_exec (st : ConstantTimeIsa.X86State) :
    (execX86Block slhPre 0 st).2 =
      [LeakageEvent.clean 0, LeakageEvent.clean 1, LeakageEvent.clean 2] ∧
    BranchCond.aboveEq.eval (execX86Block slhPre 0 st).1 =
      !decide ((st.gpr .rdi).toNat < (st.gpr .rsi).toNat) ∧
    ∀ pc, (execX86Block slhBody pc (execX86Block slhPre 0 st).1).2 =
      [LeakageEvent.clean pc,
       LeakageEvent.clean (pc + 1) [st.gpr .rdx + slhIndex st * 8#64],
       LeakageEvent.clean (pc + 2)
         [st.gpr .rbx + st.mem (st.gpr .rdx + slhIndex st * 8#64) * 8#64]] := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [slhPre, slhBody, execX86Block, execX86Instr, ConstantTimeIsa.X86State.setGpr, BranchCond.eval, slhIndex]

/-- **Speculative load hardening blocks the out-of-bounds transient secret load.** For a
    non-empty public array, the SLH-masked lookup emits the same speculative observation trace on
    any two states with the same public view, for every speculation window `W` and every
    adversarial predictor: under misprediction the masked index is `0`, so the transient loads
    touch `arr[0]` and `table[arr[0]]` only. -/
theorem slh_predicate_mask_prevents_oob_speculative_secret_load
    (s₁ s₂ : ConstantTimeIsa.X86State) (hLow : BoundsLowEq s₁ s₂) (hNonEmpty : 0 < (s₁.gpr .rsi).toNat)
    (pred : PredictorOracle) (W : Nat) :
    execSpeculativeObs slhMaskedBoundsProg s₁ pred W =
      execSpeculativeObs slhMaskedBoundsProg s₂ pred W := by
  obtain ⟨hGpr, hMem⟩ := hLow
  have hIdx : slhIndex s₂ = slhIndex s₁ := by unfold slhIndex; rw [hGpr]
  have hCell := hMem (slhIndex s₁) (slhIndex_in_bounds s₁ hNonEmpty)
  obtain ⟨hPre₁, hCond₁, hBody₁⟩ := slh_exec s₁
  obtain ⟨hPre₂, hCond₂, hBody₂⟩ := slh_exec s₂
  have hBody : ∀ pc, (execX86Block slhBody pc (execX86Block slhPre 0 s₂).1).2 =
      (execX86Block slhBody pc (execX86Block slhPre 0 s₁).1).2 := by
    intro pc
    rw [hBody₁, hBody₂, hIdx, ← hGpr, hCell]
  unfold slhMaskedBoundsProg
  rw [execSpeculativeObs_guardedBlock, execSpeculativeObs_guardedBlock, hPre₁, hPre₂, hCond₁,
    hCond₂, hBody, ← hGpr]

/-- Every transient load of the SLH-masked lookup stays inside the public array or reads the
    table at a public in-bounds array value: no transient address depends on a cell outside
    `arr[0 .. pub_len)`. -/
theorem slh_transient_loads_stay_in_bounds
    (st : ConstantTimeIsa.X86State) (hNonEmpty : 0 < (st.gpr .rsi).toNat) (pred : PredictorOracle) (W : Nat)
    (ev : LeakageEvent)
    (hEv : SpecObs.transient ev ∈ execSpeculativeObs slhMaskedBoundsProg st pred W)
    (a : BitVec 64) (ha : a ∈ ev.memAddrs) :
    ∃ i : BitVec 64, i.toNat < (st.gpr .rsi).toNat ∧
      (a = st.gpr .rdx + i * 8#64 ∨ a = st.gpr .rbx + st.mem (st.gpr .rdx + i * 8#64) * 8#64) := by
  obtain ⟨hPre, hCond, hBody⟩ := slh_exec st
  unfold slhMaskedBoundsProg at hEv
  rw [execSpeculativeObs_guardedBlock, hPre, hCond, hBody] at hEv
  have hIn : ev ∈ [LeakageEvent.clean (slhPre.length + 1),
      LeakageEvent.clean (slhPre.length + 1 + 1) [st.gpr .rdx + slhIndex st * 8#64],
      LeakageEvent.clean (slhPre.length + 1 + 2)
        [st.gpr .rbx + st.mem (st.gpr .rdx + slhIndex st * 8#64) * 8#64]] := by
    simp only [List.mem_append, List.mem_cons, List.mem_map, reduceCtorEq, false_or,
      SpecObs.transient.injEq, exists_eq_right] at hEv
    rcases hEv with hEv | hEv
    · simp at hEv
    · rcases hEv with hEv | hEv
      · split at hEv
        · simp at hEv
        · split at hEv
          · simp at hEv
          · exact List.mem_of_mem_take hEv
      · split at hEv <;> simp at hEv
  refine ⟨slhIndex st, slhIndex_in_bounds st hNonEmpty, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hIn
  rcases hIn with rfl | rfl | rfl
  · simp [LeakageEvent.clean] at ha
  · left; simpa [LeakageEvent.clean] using ha
  · right; simpa [LeakageEvent.clean] using ha

/-- Victim state for the Spectre-v1 witness: `idx = 5` is out of bounds for `pub_len = 4`,
    `arr = 0x1000`, `table = 0x8000`, and the cell `arr[5]` (address `0x1028`) holds a secret. -/
def boundsVictimState (len secret : BitVec 64) : ConstantTimeIsa.X86State :=
  { gpr := fun r =>
      match r with
      | .rdi => 5#64
      | .rsi => len
      | .rdx => 0x1000#64
      | .rbx => 0x8000#64
      | _ => 0#64
    ymm := fun _ => ConstantTimeIsa.Vec256.zero
    flags := { cf := false, of := false, zf := false }
    mem := fun a => if a == 0x1028#64 then secret else 0#64
    doitEnabled := true
    ymmUpperDirty := false }

theorem boundsVictimState_lowEq (s₁ s₂ : BitVec 64) :
    BoundsLowEq (boundsVictimState 4#64 s₁) (boundsVictimState 4#64 s₂) := by
  refine ⟨rfl, ?_⟩
  intro i hi
  have hi4 : i.toNat < 4 := hi
  have hCases : i = 0#64 ∨ i = 1#64 ∨ i = 2#64 ∨ i = 3#64 := by
    have h : i.toNat = 0 ∨ i.toNat = 1 ∨ i.toNat = 2 ∨ i.toNat = 3 := by omega
    rcases h with h | h | h | h
    · exact Or.inl (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
    · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq (by rw [h]; rfl)))
    · exact Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq (by rw [h]; rfl))))
    · exact Or.inr (Or.inr (Or.inr (BitVec.eq_of_toNat_eq (by rw [h]; rfl))))
  rcases hCases with rfl | rfl | rfl | rfl <;> rfl

/-- The predictor that always guesses "bounds check passes" (branch not taken). -/
def alwaysInBoundsPredictor : PredictorOracle := fun _ _ => false

/-- **Spectre-v1 tooth.** The unhardened bounds-checked lookup
    `if idx < pub_len then table[arr[idx]]`:
    1. is architecturally constant-time: without speculation (`W = 0`) the trace is the same on
       any two states with the same public view, whatever the predictor does;
    2. still does not leak with a one-instruction window;
    3. leaks for every window `W ≥ 2`: two states with the same public view that differ only in
       the secret cell past the end of `arr` emit different traces once the predictor mispredicts
       the bounds check, because the second transient load is addressed by the secret. -/
theorem tooth_unmasked_bounds_branch_leaks_under_speculation :
    (∀ (s₁ s₂ : ConstantTimeIsa.X86State), BoundsLowEq s₁ s₂ → ∀ (pred : PredictorOracle) (W : Nat), W ≤ 1 →
      execSpeculativeObs unmaskedBoundsProg s₁ pred W =
        execSpeculativeObs unmaskedBoundsProg s₂ pred W) ∧
    BoundsLowEq (boundsVictimState 4#64 0#64) (boundsVictimState 4#64 1#64) ∧
    (∀ W : Nat, 2 ≤ W →
      execSpeculativeObs unmaskedBoundsProg (boundsVictimState 4#64 0#64)
          alwaysInBoundsPredictor W ≠
        execSpeculativeObs unmaskedBoundsProg (boundsVictimState 4#64 1#64)
          alwaysInBoundsPredictor W) := by
  refine ⟨?_, boundsVictimState_lowEq 0#64 1#64, ?_⟩
  · intro s₁ s₂ hLow pred W hW
    obtain ⟨hGpr, hMem⟩ := hLow
    obtain ⟨hPre₁, hCond₁, hBody₁⟩ := boundsCheck_exec s₁
    obtain ⟨hPre₂, hCond₂, hBody₂⟩ := boundsCheck_exec s₂
    unfold unmaskedBoundsProg
    rw [execSpeculativeObs_guardedBlock, execSpeculativeObs_guardedBlock, hPre₁, hPre₂, hCond₁,
      hCond₂, hBody₁, hBody₂, ← hGpr]
    by_cases hIn : (s₁.gpr .rdi).toNat < (s₁.gpr .rsi).toNat
    · rw [hMem _ hIn]
    · have hW' : W = 0 ∨ W = 1 := by omega
      rcases hW' with rfl | rfl <;> simp [hIn]
  · intro W hW
    unfold unmaskedBoundsProg
    rw [guardedBlock_window_saturates boundsCheckPre .aboveEq boundsLookupBody _ _ W hW,
      guardedBlock_window_saturates boundsCheckPre .aboveEq boundsLookupBody _ _ W hW]
    decide

/-- **`lfence` after the bounds branch restores non-interference** for every window and every
    predictor: the barrier ends the transient window before the first load. -/
theorem lfence_after_bounds_branch_blocks_speculative_leak
    (s₁ s₂ : ConstantTimeIsa.X86State) (hLow : BoundsLowEq s₁ s₂) (pred : PredictorOracle) (W : Nat) :
    execSpeculativeObs lfenceBoundsProg s₁ pred W =
      execSpeculativeObs lfenceBoundsProg s₂ pred W := by
  obtain ⟨hGpr, hMem⟩ := hLow
  obtain ⟨hPre₁, hCond₁, hBody₁⟩ := boundsCheck_exec s₁
  obtain ⟨hPre₂, hCond₂, hBody₂⟩ := boundsCheck_exec s₂
  unfold lfenceBoundsProg
  rw [execSpeculativeObs_guardedBlockLfence, execSpeculativeObs_guardedBlockLfence, hPre₁, hPre₂,
    hCond₁, hCond₂, hBody₁, hBody₂, ← hGpr]
  by_cases hIn : (s₁.gpr .rdi).toNat < (s₁.gpr .rsi).toNat
  · rw [hMem _ hIn]
  · simp [hIn]

/-- **Tooth: the SLH mask needs a non-empty array.** With `pub_len = 0` the masked index `0` is
    itself out of bounds, and the hardened lookup leaks the secret cell `arr[0]` for `W ≥ 3`. -/
theorem tooth_slh_mask_leaks_on_empty_array :
    let sA : ConstantTimeIsa.X86State := { boundsVictimState 0#64 0#64 with mem := fun _ => 0#64 }
    let sB : ConstantTimeIsa.X86State :=
      { boundsVictimState 0#64 0#64 with mem := fun a => if a == 0x1000#64 then 1#64 else 0#64 }
    BoundsLowEq sA sB ∧
    ∀ W : Nat, 3 ≤ W →
      execSpeculativeObs slhMaskedBoundsProg sA alwaysInBoundsPredictor W ≠
        execSpeculativeObs slhMaskedBoundsProg sB alwaysInBoundsPredictor W := by
  refine ⟨⟨rfl, ?_⟩, ?_⟩
  · intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  · intro W hW
    unfold slhMaskedBoundsProg
    rw [guardedBlock_window_saturates slhPre .aboveEq slhBody _ _ W hW,
      guardedBlock_window_saturates slhPre .aboveEq slhBody _ _ W hW]
    decide


/-! ## 5. All-layer release cache with canonical `HashAdrs` non-aliasing

The cache below stores the message at every upper position, keyed by canonical 32-byte encoded
`HashAdrs` (`AdrsCacheConsistent`) and gated by per-coordinate range bounds (`AdrsGateValid` /
`OtsPosition.ValidCoords`) so `Nat` positions never alias truncated `UInt32`/`UInt64` hash
addresses. Its list representation is an append-only journal: repeated encoded addresses must
agree on both root and counter. No secret key or honest-computation premise is required of a
candidate. Uninterrupted single-session traces use `guardedSignTraceAll`; multi-crash persistent
recovery over the production `H_INTERNAL` core is proved in Section 9.
-/

structure OtsPosition where
  layer : Nat
  treeIdx : Nat
  leafIdx : Nat
  deriving DecidableEq, Repr

/-- Canonical WOTS+C public-key `HashAdrs` corresponding to an `OtsPosition`. -/
def OtsPosition.toWotsPkAdrs (pos : OtsPosition) : HashAdrs :=
  ⟨UInt32.ofNat pos.layer, UInt64.ofNat pos.treeIdx, .wotsPk, UInt32.ofNat pos.leafIdx, 0, 0⟩

/-- Canonical 32-byte big-endian encoded OTS address (`encodeAdrs`) fed into `thPreimage`. -/
def OtsPosition.toEncodedAdrs (pos : OtsPosition) : List UInt8 :=
  encodeAdrs pos.toWotsPkAdrs

/-- Exact non-aliasing coordinate range for `(UInt32, UInt64, UInt32)` `HashAdrs` framing. -/
def OtsPosition.ValidCoords (pos : OtsPosition) : Bool :=
  decide (pos.layer < 2 ^ 32) && decide (pos.treeIdx < 2 ^ 64) && decide (pos.leafIdx < 2 ^ 32)

/-- Per-coordinate hypertree shape and index bounds preventing `Nat → UInt32/UInt64` modular
    aliasing at every layer `0 .. params.numLayers - 1` while admitting height-66 (`22 × 3`)
    hypertrees across their full `globalIdx < 2^66` leaf space. -/
def AdrsGateValid (params : PqHashParams) (globalIdx : Nat) : Bool :=
  decide (0 < params.subtreeHeight) &&
  decide (params.subtreeHeight ≤ 31) &&
  decide (params.numLayers ≤ 2 ^ 32) &&
  decide (globalIdx / 2 ^ params.subtreeHeight < 2 ^ 64)

/-- **Canonical `HashAdrs` Injectivity (`otsPosition_toEncodedAdrs_injective`)**:
    On range-validated `OtsPosition` coordinates, equality of the 32-byte encoded `HashAdrs`
    is equivalent to exact equality of the mathematical `(layer, treeIdx, leafIdx)` triple. -/
theorem otsPosition_toEncodedAdrs_injective {a b : OtsPosition}
    (ha : a.ValidCoords = true) (hb : b.ValidCoords = true) :
    a.toEncodedAdrs = b.toEncodedAdrs ↔ a = b := by
  constructor
  · intro hEnc
    have hAdrs : a.toWotsPkAdrs = b.toWotsPkAdrs := encodeAdrs_injective hEnc
    simp only [OtsPosition.ValidCoords, Bool.and_eq_true, decide_eq_true_eq] at ha hb
    rcases ha with ⟨⟨haL, haT⟩, haK⟩
    rcases hb with ⟨⟨hbL, hbT⟩, hbK⟩
    simp only [OtsPosition.toWotsPkAdrs, HashAdrs.mk.injEq] at hAdrs
    rcases hAdrs with ⟨hL, hT, _, hK, _, _⟩
    have hLayerEq : a.layer = b.layer := by
      have hNat := congrArg UInt32.toNat hL
      simp only [UInt32.toNat_ofNat', Nat.mod_eq_of_lt haL, Nat.mod_eq_of_lt hbL] at hNat
      exact hNat
    have hTreeEq : a.treeIdx = b.treeIdx := by
      have hNat := congrArg UInt64.toNat hT
      simp only [UInt64.toNat_ofNat', Nat.mod_eq_of_lt haT, Nat.mod_eq_of_lt hbT] at hNat
      exact hNat
    have hLeafEq : a.leafIdx = b.leafIdx := by
      have hNat := congrArg UInt32.toNat hK
      simp only [UInt32.toNat_ofNat', Nat.mod_eq_of_lt haK, Nat.mod_eq_of_lt hbK] at hNat
      exact hNat
    cases a; cases b; simp_all
  · intro hEq; rw [hEq]

/-- **`#tooth` Witness (`tooth_unbounded_nat_position_aliases_u64_adrs`)**:
    Without coordinate range validation (`ValidCoords` / `AdrsGateValid`), distinct mathematical
    `OtsPosition` keys (e.g. `subtreeHeight = 0` at `globalIdx = 0` vs `globalIdx = 2^64`, or
    `subtreeHeight = 3` at `globalIdx = 0` vs `globalIdx = 2^67`) produce **distinct `Nat` keys**
    that truncate to the **exact same 32-byte `HashAdrs`**! -/
theorem tooth_unbounded_nat_position_aliases_u64_adrs :
    let pos0 : OtsPosition := ⟨1, 0 / 2 ^ 0, 0 % 2 ^ 0⟩
    let posAlias : OtsPosition := ⟨1, (2 ^ 64) / 2 ^ 0, (2 ^ 64) % 2 ^ 0⟩
    pos0 ≠ posAlias ∧
    pos0.toEncodedAdrs = posAlias.toEncodedAdrs ∧
    posAlias.ValidCoords = false := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hT := congrArg OtsPosition.treeIdx h
    simp at hT
  · decide
  · decide

structure LayerRelease where
  key : OtsPosition
  signed : OtsMessage
  opening : LayerXmssSig
  deriving DecidableEq

/-- Recompute each input root by the real verifier, never trusting a root supplied by the
    signing computation. Failure at any layer fails the entire traversal. -/
def verifiedLayerMessages (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) : Nat → Nat → List UInt8 → List UInt8 →
      List LayerXmssSig → Option (List LayerRelease)
  | _, _, _, _, [] => some []
  | layer, g, rand, root, sig :: rest => do
    let next ← verifyHypertreeLayers suite params pk.pkSeed pk.pkRoot rand layer g root [sig]
    let tail ← verifiedLayerMessages suite params pk (layer + 1)
      (g / 2 ^ params.subtreeHeight) [] next rest
    pure (⟨⟨layer, g / 2 ^ params.subtreeHeight, g % 2 ^ params.subtreeHeight⟩,
      ⟨root, sig.tswCtr⟩, sig⟩ :: tail)

/-- Every verifier-accepted hypertree has a complete cache view, with one entry per layer. -/
theorem verifiedLayerMessages_complete (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (sigs : List LayerXmssSig) :
    ∀ layer g rand root top,
    verifyHypertreeLayers suite params pk.pkSeed pk.pkRoot rand layer g root sigs = some top →
    ∃ entries, verifiedLayerMessages suite params pk layer g rand root sigs = some entries ∧
      entries.map (fun e => e.key.layer) = List.range' layer sigs.length := by
  induction sigs with
  | nil => intro layer g rand root top _; exact ⟨[], rfl, rfl⟩
  | cons sig rest ih =>
    intro layer g rand root top h
    obtain ⟨mid, hm, ht⟩ := (verifyHypertreeLayers_split suite params pk.pkSeed pk.pkRoot
      rand layer g root sig rest top).mp h
    obtain ⟨entries, he, hl⟩ := ih _ _ _ _ _ ht
    refine ⟨⟨⟨layer, g / 2 ^ params.subtreeHeight, g % 2 ^ params.subtreeHeight⟩,
      ⟨root, sig.tswCtr⟩, sig⟩ :: entries, ?_, ?_⟩
    · simp [verifiedLayerMessages, hm, he]
    · simp [List.range', hl]

/-- Every entry extracted by `verifiedLayerMessages` under bounded subtree height, layer budget,
    and initial tree index satisfies `OtsPosition.ValidCoords = true`. -/
theorem verifiedLayerMessages_validCoords (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (sigs : List LayerXmssSig) :
    ∀ layer g rand root entries,
      params.subtreeHeight ≤ 31 →
      layer + sigs.length ≤ 2 ^ 32 →
      g / 2 ^ params.subtreeHeight < 2 ^ 64 →
      verifiedLayerMessages suite params pk layer g rand root sigs = some entries →
      ∀ e ∈ entries, e.key.ValidCoords = true := by
  induction sigs with
  | nil =>
    intro layer g rand root entries _ _ _ h e hm
    simp [verifiedLayerMessages] at h
    subst entries; cases hm
  | cons sig rest ih =>
    intro layer g rand root entries hSub hLay hTree h e hm
    simp only [verifiedLayerMessages, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨next, _, tail, hTail, rfl⟩ := h
    rcases List.mem_cons.mp hm with rfl | hMem
    · simp only [OtsPosition.ValidCoords, Bool.and_eq_true, decide_eq_true_eq]
      have hLayerLt : layer < 2 ^ 32 := by simp at hLay; omega
      have hPowLe : 2 ^ params.subtreeHeight ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) hSub
      have hModLt : g % 2 ^ params.subtreeHeight < 2 ^ params.subtreeHeight :=
        Nat.mod_lt _ (Nat.two_pow_pos _)
      have h31Lt32 : (2 : Nat) ^ 31 < 2 ^ 32 := by decide
      exact ⟨⟨hLayerLt, hTree⟩, by omega⟩
    · exact ih (layer + 1) (g / 2 ^ params.subtreeHeight) [] next tail hSub
        (by simp at hLay; omega)
        (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hTree) hTail e hMem

/-- Pairwise agreement on `Nat` positions. -/
def CacheConsistent (entries : List LayerRelease) : Prop :=
  ∀ a ∈ entries, ∀ b ∈ entries, a.key = b.key → a.signed = b.signed

instance (entries : List LayerRelease) : Decidable (CacheConsistent entries) :=
  inferInstanceAs (Decidable (∀ a ∈ entries, ∀ b ∈ entries,
    a.key = b.key → a.signed = b.signed))

/-- Canonical encoded-`HashAdrs` pairwise agreement: any two entries whose 32-byte encoded
    OTS addresses match must agree on both `(root, tswCtr)`. -/
def AdrsCacheConsistent (entries : List LayerRelease) : Prop :=
  ∀ a ∈ entries, ∀ b ∈ entries, a.key.toEncodedAdrs = b.key.toEncodedAdrs → a.signed = b.signed

instance (entries : List LayerRelease) : Decidable (AdrsCacheConsistent entries) :=
  inferInstanceAs (Decidable (∀ a ∈ entries, ∀ b ∈ entries,
    a.key.toEncodedAdrs = b.key.toEncodedAdrs → a.signed = b.signed))

theorem adrsCacheConsistent_implies_cacheConsistent {entries : List LayerRelease}
    (h : AdrsCacheConsistent entries) : CacheConsistent entries :=
  fun a ha b hb hk => h a ha b hb (congrArg OtsPosition.toEncodedAdrs hk)

/-- Full verification preceded by `AdrsGateValid` coordinate validation and followed by a
    transactional encoded-`HashAdrs` cache check. Layer zero is omitted from the upper-layer
    journal. Returning `none` commits neither a signature nor a partial cache. -/
def verifyBeforeReleaseAll (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (cache : List LayerRelease) (turn : FaultedSignTurn) :
    Option (List LayerRelease) := do
  if !AdrsGateValid params turn.candidate.leafGlobalIdx then none
  else if !verifyPqHashSig suite params pk turn.msg turn.candidate then none else do
    let (rand, root) ← hypertreeStart suite params pk turn.msg turn.candidate
    let entries ← verifiedLayerMessages suite params pk 0 turn.candidate.leafGlobalIdx
      rand root turn.candidate.layerSigs
    if AdrsCacheConsistent (cache ++ entries.drop 1) then some (entries.drop 1) else none

/-- The returned journal contains precisely the upper entries of successfully released
    candidates. Rejecting a turn leaves the journal unchanged. -/
def guardedSignTraceAll (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) : List LayerRelease → List FaultedSignTurn → List LayerRelease
  | cache, [] => cache
  | cache, turn :: rest =>
    match verifyBeforeReleaseAll suite params pk cache turn with
    | none => guardedSignTraceAll suite params pk cache rest
    | some entries => guardedSignTraceAll suite params pk (cache ++ entries) rest

theorem verifyBeforeReleaseAll_adrsConsistent (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (cache entries : List LayerRelease) (turn : FaultedSignTurn)
    (h : verifyBeforeReleaseAll suite params pk cache turn = some entries) :
    AdrsCacheConsistent (cache ++ entries) := by
  unfold verifyBeforeReleaseAll at h
  simp only [Option.bind_eq_bind] at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨⟨rand, root⟩, _, es, _, h⟩ := h
      split at h
      · next hc => cases h; exact hc
      · cases h

theorem verifyBeforeReleaseAll_consistent (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (cache entries : List LayerRelease) (turn : FaultedSignTurn)
    (h : verifyBeforeReleaseAll suite params pk cache turn = some entries) :
    CacheConsistent (cache ++ entries) :=
  adrsCacheConsistent_implies_cacheConsistent
    (verifyBeforeReleaseAll_adrsConsistent suite params pk cache entries turn h)

theorem verifyBeforeReleaseAll_validCoords (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (cache entries : List LayerRelease) (turn : FaultedSignTurn)
    (h : verifyBeforeReleaseAll suite params pk cache turn = some entries) :
    ∀ e ∈ entries, e.key.ValidCoords = true := by
  unfold verifyBeforeReleaseAll at h
  simp only [Option.bind_eq_bind] at h
  split at h
  · cases h
  · next hGateNeg =>
    have hGate : AdrsGateValid params turn.candidate.leafGlobalIdx = true := by
      cases hx : AdrsGateValid params turn.candidate.leafGlobalIdx <;> simp_all
    split at h
    · cases h
    · next hvNeg =>
      have hv : verifyPqHashSig suite params pk turn.msg turn.candidate = true := by
        cases hx : verifyPqHashSig suite params pk turn.msg turn.candidate <;> simp_all
      obtain ⟨_, _, _, _, hlen⟩ := verifyPqHashSig_layers suite params pk _ _ hv
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨⟨rand, root⟩, _, es, he, h⟩ := h
      split at h
      · cases h
        simp only [AdrsGateValid, Bool.and_eq_true, decide_eq_true_eq] at hGate
        rcases hGate with ⟨⟨⟨_, hSub⟩, hNum⟩, hTree⟩
        have hAll := verifiedLayerMessages_validCoords suite params pk turn.candidate.layerSigs
          0 turn.candidate.leafGlobalIdx rand root es hSub (by omega) hTree he
        intro e hMem
        exact hAll e (List.mem_of_mem_drop hMem)
      · cases h

theorem guardedSignTraceAll_adrsConsistent (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (turns : List FaultedSignTurn) :
    ∀ cache, AdrsCacheConsistent cache →
      AdrsCacheConsistent (guardedSignTraceAll suite params pk cache turns) := by
  induction turns with
  | nil => intro cache h; exact h
  | cons turn rest ih =>
    intro cache hc
    simp only [guardedSignTraceAll]
    split
    · exact ih cache hc
    · next entries he =>
      exact ih _ (verifyBeforeReleaseAll_adrsConsistent suite params pk _ _ turn he)

theorem guardedSignTraceAll_consistent (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (turns : List FaultedSignTurn) :
    ∀ cache, AdrsCacheConsistent cache →
      CacheConsistent (guardedSignTraceAll suite params pk cache turns) :=
  fun cache hc =>
    adrsCacheConsistent_implies_cacheConsistent
      (guardedSignTraceAll_adrsConsistent suite params pk turns cache hc)

theorem guardedSignTraceAll_validCoords (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (turns : List FaultedSignTurn) :
    ∀ cache, (∀ e ∈ cache, e.key.ValidCoords = true) →
      ∀ e ∈ guardedSignTraceAll suite params pk cache turns, e.key.ValidCoords = true := by
  induction turns with
  | nil => intro cache h; exact h
  | cons turn rest ih =>
    intro cache hc
    simp only [guardedSignTraceAll]
    split
    · exact ih cache hc
    · next entries he =>
      apply ih
      intro e hm
      rcases List.mem_append.mp hm with hOld | hNew
      · exact hc e hOld
      · exact verifyBeforeReleaseAll_validCoords suite params pk cache entries turn he e hNew

/-- Arbitrary depth, including seven and twenty-two layers: at every encoded `HashAdrs` the
    released root AND grinding counter are unique over the entire fault-adversarial trace. -/
theorem all_depth_released_adrs_message_unique (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (turns : List FaultedSignTurn)
    (a b : LayerRelease)
    (ha : a ∈ guardedSignTraceAll suite params pk [] turns)
    (hb : b ∈ guardedSignTraceAll suite params pk [] turns)
    (hk : a.key.toEncodedAdrs = b.key.toEncodedAdrs) :
    a.key = b.key ∧ a.signed = b.signed := by
  have hVa := guardedSignTraceAll_validCoords suite params pk turns [] (by simp) a ha
  have hVb := guardedSignTraceAll_validCoords suite params pk turns [] (by simp) b hb
  exact ⟨(otsPosition_toEncodedAdrs_injective hVa hVb).mp hk,
    guardedSignTraceAll_adrsConsistent suite params pk turns [] (by simp [AdrsCacheConsistent]) a ha b hb hk⟩

theorem all_depth_released_message_unique (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (turns : List FaultedSignTurn)
    (a b : LayerRelease)
    (ha : a ∈ guardedSignTraceAll suite params pk [] turns)
    (hb : b ∈ guardedSignTraceAll suite params pk [] turns)
    (hk : a.key = b.key) : a.signed = b.signed :=
  (all_depth_released_adrs_message_unique suite params pk turns a b ha hb
    (congrArg OtsPosition.toEncodedAdrs hk)).2

/-- An empty cache accepts every verified candidate with valid coordinates and a consistent
    upper-layer view; there is no two-layer shape test. -/
theorem gate_releases_accepted_arbitrary_depth (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (turn : FaultedSignTurn)
    (rand root : List UInt8) (entries : List LayerRelease)
    (hGate : AdrsGateValid params turn.candidate.leafGlobalIdx = true)
    (hv : verifyPqHashSig suite params pk turn.msg turn.candidate = true)
    (hs : hypertreeStart suite params pk turn.msg turn.candidate = some (rand, root))
    (he : verifiedLayerMessages suite params pk 0 turn.candidate.leafGlobalIdx rand root
      turn.candidate.layerSigs = some entries)
    (hc : AdrsCacheConsistent (entries.drop 1)) :
    verifyBeforeReleaseAll suite params pk [] turn = some (entries.drop 1) := by
  simpa [verifyBeforeReleaseAll, hGate, hv, hs, he] using hc

/-- Distinct layer indices imply `Nat`-key consistency without any cryptographic assumption. -/
theorem cacheConsistent_of_distinct_layers (es : List LayerRelease)
    (h : (es.map (fun e => e.key.layer)).Nodup) : CacheConsistent es := by
  induction es with
  | nil => simp [CacheConsistent]
  | cons e es ih =>
    obtain ⟨hne, ht⟩ := List.nodup_cons.mp h
    intro a ha b hb hk
    rcases List.mem_cons.mp ha with rfl | hA
    · rcases List.mem_cons.mp hb with rfl | hB
      · rfl
      · exact False.elim (hne (List.mem_map.mpr ⟨b, hB, (congrArg OtsPosition.layer hk).symm⟩))
    · rcases List.mem_cons.mp hb with rfl | hB
      · exact False.elim (hne (List.mem_map.mpr ⟨a, hA, congrArg OtsPosition.layer hk⟩))
      · exact ih ht a hA b hB hk

/-- Distinct range-valid entries imply encoded-`HashAdrs` consistency. -/
theorem adrsCacheConsistent_of_distinct_valid_layers (es : List LayerRelease)
    (hVal : ∀ e ∈ es, e.key.ValidCoords = true)
    (h : (es.map (fun e => e.key.layer)).Nodup) : AdrsCacheConsistent es := by
  have hNat := cacheConsistent_of_distinct_layers es h
  intro a ha b hb hEnc
  exact hNat a ha b hb ((otsPosition_toEncodedAdrs_injective (hVal a ha) (hVal b hb)).mp hEnc)

/-- Constructive range facts used by the cache coverage audit. -/
theorem layer_range_lower (n start : Nat) : ∀ x ∈ List.range' start n, start ≤ x := by
  induction n generalizing start with
  | zero => simp
  | succ n ih =>
    intro x hx
    rw [List.range'_succ] at hx
    rcases List.mem_cons.mp hx with rfl | ht
    · exact Nat.le_refl _
    · have := ih (start + 1) x ht; omega

theorem layer_range_nodup (n start : Nat) : (List.range' start n).Nodup := by
  induction n generalizing start with
  | zero => exact List.nodup_nil
  | succ n ih =>
    rw [List.range'_succ, List.nodup_cons]
    refine ⟨?_, ih (start + 1)⟩
    intro h
    have := layer_range_lower n (start + 1) start h
    omega

theorem layer_range_member (n start x : Nat) (hlo : start ≤ x) (hhi : x < start + n) :
    x ∈ List.range' start n := by
  induction n generalizing start with
  | zero => omega
  | succ n ih =>
    rw [List.range'_succ]
    by_cases hx : x = start
    · exact List.mem_cons.mpr (Or.inl hx)
    · exact List.mem_cons.mpr (Or.inr (ih (start + 1) (by omega) (by omega)))

theorem adrsGateValid_of_verifyPqHashSig (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (msg : List UInt8) (sig : PqHashSig)
    (hSubPos : 0 < params.subtreeHeight)
    (hv : verifyPqHashSig suite params pk msg sig = true) :
    AdrsGateValid params sig.leafGlobalIdx = true := by
  unfold verifyPqHashSig at hv
  have hWf : params.wellFormed = true := by
    cases hx : params.wellFormed <;> simp_all
  have hLeaf : sig.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight) := by
    split at hv
    · cases hv
    · split at hv
      · cases hv
      · next hNeg =>
        have hDec : decide (sig.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight)) = true := by
          cases hx : decide (sig.leafGlobalIdx < 2 ^ (params.numLayers * params.subtreeHeight)) <;> simp_all
        exact of_decide_eq_true hDec
  unfold PqHashParams.wellFormed at hWf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hWf
  have hSubLe30 : params.subtreeHeight ≤ 30 := hWf.1.1.1.1.2
  have hProdLe62 : params.numLayers * params.subtreeHeight ≤ 62 := hWf.1.2
  have hNumLe62 : params.numLayers ≤ 62 := by
    have h1 : params.numLayers * 1 ≤ params.numLayers * params.subtreeHeight :=
      Nat.mul_le_mul_left _ hSubPos
    omega
  have hPowLe : 2 ^ (params.numLayers * params.subtreeHeight) ≤ 2 ^ 62 :=
    Nat.pow_le_pow_right (by decide) hProdLe62
  have hDivLe : sig.leafGlobalIdx / 2 ^ params.subtreeHeight ≤ sig.leafGlobalIdx :=
    Nat.div_le_self _ _
  have h62Lt64 : (2 : Nat) ^ 62 < 2 ^ 64 := by decide
  simp only [AdrsGateValid, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨hSubPos, by omega⟩, by omega⟩, by omega⟩

/-- Non-vacuity and coverage: for every depth d with positive subtree height, a verified signature
    is released from the empty cache with exactly the upper layer indices 1 through d-1. -/
theorem all_depth_gate_complete (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (turn : FaultedSignTurn)
    (hSubPos : 0 < params.subtreeHeight)
    (hv : verifyPqHashSig suite params pk turn.msg turn.candidate = true) :
    ∃ es, verifyBeforeReleaseAll suite params pk [] turn = some es ∧
      es.map (fun e => e.key.layer) = List.range' 1 (params.numLayers - 1) := by
  have hGate := adrsGateValid_of_verifyPqHashSig suite params pk turn.msg turn.candidate hSubPos hv
  obtain ⟨rand, root, hs, ht, hlen⟩ := verifyPqHashSig_layers suite params pk _ _ hv
  obtain ⟨es, he, hl⟩ := verifiedLayerMessages_complete suite params pk _ _ _ _ _ _ ht
  have hd : (es.drop 1).map (fun e => e.key.layer) =
      List.range' 1 (params.numLayers - 1) := by
    rw [List.map_drop, hl, hlen, List.drop_range']
  have hGateFacts : params.subtreeHeight ≤ 31 ∧ params.numLayers ≤ 2 ^ 32 ∧
      turn.candidate.leafGlobalIdx / 2 ^ params.subtreeHeight < 2 ^ 64 := by
    simp only [AdrsGateValid, Bool.and_eq_true, decide_eq_true_eq] at hGate
    exact ⟨hGate.1.1.2, hGate.1.2, hGate.2⟩
  have hValAll := verifiedLayerMessages_validCoords suite params pk turn.candidate.layerSigs
    0 turn.candidate.leafGlobalIdx rand root es hGateFacts.1
    (by omega) hGateFacts.2.2 he
  refine ⟨es.drop 1, gate_releases_accepted_arbitrary_depth suite params pk turn rand root es
    hGate hv hs he (adrsCacheConsistent_of_distinct_valid_layers _
      (fun e hm => hValAll e (List.mem_of_mem_drop hm)) ?_), hd⟩
  rw [hd]
  exact layer_range_nodup _ _

/-! ## 6. Fuel-bounded backward branches

Absolute targets can point backward, to the loop exit, or beyond the code. Both architectural
and transient execution have explicit fuel. Transient branches follow the predictor, including
an early exit or extra iterations after the architectural exit; rollback restores the state.
-/

inductive PcInstr where
  | op (i : ConstantTimeIsa.X86Instr)
  | branch (c : BranchCond) (target : Nat)
  | jump (target : Nat)
  | lfence
  | ret
  deriving DecidableEq, Repr

abbrev PcCode := List PcInstr

def pcTransient (code : PcCode) (pred : PredictorOracle) :
    Nat → Nat → List Bool → ConstantTimeIsa.X86State → List LeakageEvent
  | 0, _, _, _ => []
  | fuel + 1, pc, hist, st =>
    match code[pc]? with
    | none => []
    | some (.op i) => (execX86Instr i pc st).2 ::
        pcTransient code pred fuel (pc + 1) hist (execX86Instr i pc st).1
    | some (.branch _ target) =>
        branchEvent pc (pred pc hist) :: pcTransient code pred fuel
          (if pred pc hist then target else pc + 1) (pred pc hist :: hist) st
    | some (.jump target) => branchEvent pc true :: pcTransient code pred fuel target hist st
    | some .lfence => []
    | some .ret => [retEvent pc st]

def pcSpecRun (code : PcCode) (pred : PredictorOracle) (W : Nat) :
    Nat → Nat → List Bool → ConstantTimeIsa.X86State → List SpecObs
  | 0, _, _, _ => []
  | fuel + 1, pc, hist, st =>
    match code[pc]? with
    | none => []
    | some (.op i) => .arch (execX86Instr i pc st).2 ::
        pcSpecRun code pred W fuel (pc + 1) hist (execX86Instr i pc st).1
    | some (.branch c target) =>
        .arch (branchEvent pc (c.eval st)) ::
          ((if pred pc hist = c.eval st then [] else
            pcTransient code pred W (if pred pc hist then target else pc + 1)
              (pred pc hist :: hist) st).map .transient ++
            pcSpecRun code pred W fuel (if c.eval st then target else pc + 1)
              (c.eval st :: hist) st)
    | some (.jump target) => .arch (branchEvent pc true) :: pcSpecRun code pred W fuel target hist st
    | some .lfence => pcSpecRun code pred W fuel (pc + 1) hist st
    | some .ret => [.arch (retEvent pc st)]

/-- Relational invariant on *all* reachable paths, including the paths after wrong predictions.
    Public addresses are required even on extra iterations; architectural loop safety alone
    would not justify a speculative theorem. -/
structure PcPublicInvariant (code : PcCode) (R : ConstantTimeIsa.X86State → ConstantTimeIsa.X86State → Prop) : Prop where
  op : ∀ pc i, code[pc]? = some (.op i) → ∀ a b, R a b →
    (execX86Instr i pc a).2 = (execX86Instr i pc b).2 ∧
      R (execX86Instr i pc a).1 (execX86Instr i pc b).1
  branch : ∀ (pc : Nat) (c : BranchCond) (target : Nat), code[pc]? = some (PcInstr.branch c target) →
    ∀ a b, R a b → c.eval a = c.eval b
  ret : ∀ a b, R a b → a.ymmUpperDirty = b.ymmUpperDirty

theorem pcTransient_public_ni (code : PcCode) (R : ConstantTimeIsa.X86State → ConstantTimeIsa.X86State → Prop)
    (inv : PcPublicInvariant code R) (pred : PredictorOracle) (fuel : Nat) :
    ∀ pc hist a b, R a b →
      pcTransient code pred fuel pc hist a = pcTransient code pred fuel pc hist b := by
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro pc hist a b hab
    cases hi : code[pc]? with
    | none => simp [pcTransient, hi]
    | some ins =>
      cases ins with
      | op i =>
        obtain ⟨he, hr⟩ := inv.op pc i hi a b hab
        simp only [pcTransient, hi, he]
        rw [ih _ _ _ _ hr]
      | branch c target => simp only [pcTransient, hi]; rw [ih _ _ _ _ hab]
      | jump target => simp only [pcTransient, hi]; rw [ih _ _ _ _ hab]
      | lfence => simp [pcTransient, hi]
      | ret => simp [pcTransient, hi, retEvent, inv.ret a b hab]

/-- Fuel-bounded speculative non-interference, with no restriction on forward/backward targets,
    fuel, predictor, or transient window length. -/
theorem public_loop_fuel_bounded_speculative_ni (code : PcCode)
    (R : ConstantTimeIsa.X86State → ConstantTimeIsa.X86State → Prop) (inv : PcPublicInvariant code R)
    (pred : PredictorOracle) (W fuel : Nat) :
    ∀ pc hist a b, R a b →
      pcSpecRun code pred W fuel pc hist a = pcSpecRun code pred W fuel pc hist b := by
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro pc hist a b hab
    cases hi : code[pc]? with
    | none => simp [pcSpecRun, hi]
    | some ins =>
      cases ins with
      | op i =>
        obtain ⟨he, hr⟩ := inv.op pc i hi a b hab
        simp only [pcSpecRun, hi, he]
        rw [ih _ _ _ _ hr]
      | branch c target =>
        have hc := inv.branch pc c target hi a b hab
        simp only [pcSpecRun, hi, hc]
        rw [ih _ _ _ _ hab]
        split <;> simp only [pcTransient_public_ni code R inv pred W _ _ a b hab]
      | jump target => simp only [pcSpecRun, hi]; rw [ih _ _ _ _ hab]
      | lfence => simp only [pcSpecRun, hi]; exact ih _ _ _ _ hab
      | ret => simp [pcSpecRun, hi, retEvent, inv.ret a b hab]


attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd

/-! ### Counter grinding: the same root can have two valid incomparable codewords -/

/-- Small executable hash family for the counter tooth. Its last input byte distinguishes
    counter zero from counter one. This is a model witness, not a cryptographic hash claim. -/
def counterToothSuite : TweakableHashSuite where
  suiteId := []
  rawHash := fun msg => (if msg.getLastD 0 = 0 then 128 else 64) :: List.replicate 31 0
  rawHash_len := by intro msg; simp

def counterToothParams : PqHashParams := { zeroToyParams with w := 2, ell1 := 2, subtreeHeight := 0 }

def counterCodeword (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed pkRoot root : List UInt8) (layer g ctr : Nat) : List Nat :=
  extractBaseWDigits params.w params.ell1
    (thHashMsg suite [] pkSeed pkRoot root (UInt32.ofNat layer)
      (UInt64.ofNat (g / 2 ^ params.subtreeHeight))
      (UInt32.ofNat (g % 2 ^ params.subtreeHeight)) ctr)

def counterToothOpening (ctr : Nat) : LayerXmssSig :=
  let digits := counterCodeword counterToothSuite counterToothParams [] [] [] 1 0 ctr
  { tswCtr := ctr
    wotsChains := (List.range 2).map fun r =>
      wotsChainSteps counterToothSuite [] 1 0 0 r 0 (digits.getD r 0)
        (wotsSecretBase counterToothSuite ⟨[], [], []⟩ 1 0 0 r)
    authPath := [] }

/-- A root-only cache accepts an opening when the recomputed root matches the cache and the
    actual layer verifier accepts. It deliberately does not compare the grinding counter. -/
def rootOnlyCacheRelease (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed pkRoot : List UInt8) (layer g : Nat) (cached root top : List UInt8)
    (sig : LayerXmssSig) : Bool :=
  decide (cached = root ∧
    verifyHypertreeLayers suite params pkSeed pkRoot [] layer g root [sig] = some top)

theorem counterToothOpening_accepts (ctr : Nat)
    (hv : checkTargetSum 2 2 1
      (counterCodeword counterToothSuite counterToothParams [] [] [] 1 0 ctr) = true) :
    rootOnlyCacheRelease counterToothSuite counterToothParams [] [] 1 0 [] []
      (computeWotsPk counterToothSuite counterToothParams ⟨[], [], []⟩ 1 0 0)
      (counterToothOpening ctr) = true := by
  have hp := congrArg
    (thTweakTl counterToothSuite [] ⟨1, 0, .wotsPk, 0, 0, 0⟩)
    (honest_wots_chains_open_real_endpoints counterToothSuite counterToothParams
      ⟨[], [], []⟩ 1 0 0 (counterCodeword counterToothSuite counterToothParams [] [] [] 1 0 ctr) hv)
  unfold rootOnlyCacheRelease
  apply decide_eq_true
  refine ⟨rfl, ?_⟩
  rw [verifyHypertreeLayers_cons]
  change (if !checkTargetSum 2 2 1
      (counterCodeword counterToothSuite counterToothParams [] [] [] 1 0 ctr) then none else
      if (counterToothOpening ctr).wotsChains.length ≠ 2 then none else _) = _
  rw [hv]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hl : (counterToothOpening ctr).wotsChains.length = 2 := by
    simp [counterToothOpening]
  simp only [hl, ne_eq, not_true_eq_false, ↓reduceIte]
  change (match walkMerkleAuthPath counterToothSuite [] 1 0 .tree 0 0 0
      (recoverWotsPkFromSig counterToothSuite counterToothParams [] 1 0 0
        (counterCodeword counterToothSuite counterToothParams [] [] [] 1 0 ctr)
        (counterToothOpening ctr).wotsChains) [] with
    | none => none
    | some next => some next) = _
  change recoverWotsPkFromSig counterToothSuite counterToothParams [] 1 0 0
      (counterCodeword counterToothSuite counterToothParams [] [] [] 1 0 ctr)
      (counterToothOpening ctr).wotsChains = _ at hp
  rw [hp]
  rfl

/- Explicit #tooth: two accepted openings on exactly the same root, at exactly the same key,
    with counters 0 and 1 and distinct valid target-sum codewords. A root-only cache releases
    both. The full cache rejects the second message. -/
set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
 theorem tooth_root_only_cache_leaks_second_wotsc_counter_codeword :
    let top := computeWotsPk counterToothSuite counterToothParams ⟨[], [], []⟩ 1 0 0
    rootOnlyCacheRelease counterToothSuite counterToothParams [] [] 1 0 [] [] top
      (counterToothOpening 0) = true ∧
    rootOnlyCacheRelease counterToothSuite counterToothParams [] [] 1 0 [] [] top
      (counterToothOpening 1) = true ∧
    (counterToothOpening 0).tswCtr ≠ (counterToothOpening 1).tswCtr ∧
    counterCodeword counterToothSuite counterToothParams [] [] [] 1 0 0 ≠
      counterCodeword counterToothSuite counterToothParams [] [] [] 1 0 1 ∧
    checkTargetSum 2 2 1 (counterCodeword counterToothSuite counterToothParams [] [] [] 1 0 0) = true ∧
    checkTargetSum 2 2 1 (counterCodeword counterToothSuite counterToothParams [] [] [] 1 0 1) = true ∧
    (OtsMessage.mk [] 0) ≠ ⟨[], 1⟩ := by
  refine ⟨counterToothOpening_accepts 0 (by decide +kernel),
    counterToothOpening_accepts 1 (by decide +kernel), ?_⟩
  decide +kernel

/-! ### Speculation on the byte-decoded compiled kernels

This uses the binary decoder's state, byte PCs and instruction semantics directly. In particular
there is no hand transcription into the smaller instruction model above.
-/

inductive BinarySpecObs where
  | arch (obs : StepObs)
  | transient (obs : StepObs)
  deriving DecidableEq, Repr

def binaryTransient (prog : List (DecodedInstr Qsag.X86Instr)) (pred : PredictorOracle) :
    Nat → List Bool → Qsag.X86State → List StepObs
  | 0, _, _ => []
  | fuel + 1, hist, st =>
    if st.halted then [] else
    match findInstrAtPc st.pc prog with
    | none => []
    | some d =>
      match d.instr with
      | .jcc _ target =>
        (stepX86 d st).2 :: binaryTransient prog pred fuel (pred st.pc hist :: hist)
          { st with pc := if pred st.pc hist then target.toNat else st.pc + d.byteLen }
      | _ => (stepX86 d st).2 :: binaryTransient prog pred fuel hist (stepX86 d st).1

def binarySpecRun (prog : List (DecodedInstr Qsag.X86Instr)) (pred : PredictorOracle)
    (W : Nat) : Nat → List Bool → Qsag.X86State → List BinarySpecObs
  | 0, _, _ => []
  | fuel + 1, hist, st =>
    if st.halted then [] else
    match findInstrAtPc st.pc prog with
    | none => []
    | some d =>
      match d.instr with
      | .jcc cc target =>
        .arch (stepX86 d st).2 ::
          ((if pred st.pc hist = evalX86Cond cc st then [] else
            binaryTransient prog pred W (pred st.pc hist :: hist)
              { st with pc := if pred st.pc hist then target.toNat else st.pc + d.byteLen }).map
                .transient ++
          binarySpecRun prog pred W fuel (evalX86Cond cc st :: hist) (stepX86 d st).1)
      | _ => .arch (stepX86 d st).2 :: binarySpecRun prog pred W fuel hist (stepX86 d st).1

/-- Relational proof obligation for decoded programs with arbitrary forward and backward
    conditional branches. The invariant includes PC and halt agreement, every instruction's
    public observation, and equality of every branch condition. -/
structure BinaryPublicInvariant (prog : List (DecodedInstr Qsag.X86Instr))
    (R : Qsag.X86State → Qsag.X86State → Prop) : Prop where
  pc : ∀ a b, R a b → a.pc = b.pc
  halted : ∀ a b, R a b → a.halted = b.halted
  step : ∀ d a b, findInstrAtPc a.pc prog = some d → R a b →
    (stepX86 d a).2 = (stepX86 d b).2 ∧ R (stepX86 d a).1 (stepX86 d b).1
  branch : ∀ d cc target a b, findInstrAtPc a.pc prog = some d →
    d.instr = .jcc cc target → R a b → evalX86Cond cc a = evalX86Cond cc b

theorem binaryTransient_public_ni (prog : List (DecodedInstr Qsag.X86Instr))
    (R : Qsag.X86State → Qsag.X86State → Prop) (inv : BinaryPublicInvariant prog R)
    (pred : PredictorOracle) (fuel : Nat) :
    ∀ hist a b, R a b → binaryTransient prog pred fuel hist a =
      binaryTransient prog pred fuel hist b := by
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro hist a b hab
    have hHalt := inv.halted a b hab
    have hPc := inv.pc a b hab
    cases hd : findInstrAtPc a.pc prog with
    | none => simp [binaryTransient, hHalt, hPc, hd]
    | some d =>
      obtain ⟨hObs, hNext⟩ := inv.step d a b hd hab
      match hInstr : d.instr with
      | .jcc cc target =>
        simp only [binaryTransient, hHalt, hPc, hd, hInstr, hObs]
        exact congrArg ((stepX86 d a).2 :: ·) (ih (pred a.pc hist :: hist) a b hab)
      | _ =>
        simp only [binaryTransient, hHalt, hPc, hd, hInstr, hObs]
        exact congrArg ((stepX86 d a).2 :: ·) (ih hist _ _ hNext)

/-- Decoded-byte speculative NI for loops, not only straight-line code. Wrong-path execution
    uses the original state and the architectural path uses the stepped state, exactly as in
    `binarySpecRun`; both are covered by the same relational invariant. -/
theorem binary_loop_fuel_bounded_speculative_ni (prog : List (DecodedInstr Qsag.X86Instr))
    (R : Qsag.X86State → Qsag.X86State → Prop) (inv : BinaryPublicInvariant prog R)
    (pred : PredictorOracle) (W fuel : Nat) :
    ∀ hist a b, R a b → binarySpecRun prog pred W fuel hist a =
      binarySpecRun prog pred W fuel hist b := by
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro hist a b hab
    have hHalt := inv.halted a b hab
    have hPc := inv.pc a b hab
    cases hd : findInstrAtPc a.pc prog with
    | none => simp [binarySpecRun, hHalt, hPc, hd]
    | some d =>
      obtain ⟨hObs, hNext⟩ := inv.step d a b hd hab
      match hInstr : d.instr with
      | .jcc cc target =>
        have hCond := inv.branch d cc target a b hd hInstr hab
        simp only [binarySpecRun, hHalt, hPc, hd, hInstr, hObs, hCond]
        rw [ih (evalX86Cond cc a :: hist) _ _ hNext]
        split <;>
          simp only [binaryTransient_public_ni prog R inv pred W _ a b hab, List.map_inj_left]
      | _ =>
        simp only [binarySpecRun, hHalt, hPc, hd, hInstr, hObs]
        exact congrArg (BinarySpecObs.arch (stepX86 d a).2 :: ·) (ih hist _ _ hNext)

/-- Named loop-kernel families covered by the relational model. These are semantic program
    schemas; compiled-symbol claims still require a decoded fixture and its own invariant. -/
inductive NamedCtKernel where
  | ct_select_u64
  | sbox_bitslice
  | gf2_128_mul_acc
  deriving DecidableEq, Repr

def namedCtKernelBody : NamedCtKernel → List ConstantTimeIsa.X86Instr
  | .ct_select_u64 => [.cmovnz64 .rax .rsi]
  | .sbox_bitslice => [.vgf2p8affineqb0 .ymm0 .ymm0 .ymm14]
  | .gf2_128_mul_acc => [.vpclmulqdq .ymm0 .ymm1 .ymm2 0x00#8]

def namedCtKernelLoop (kernel : NamedCtKernel) (trips : Nat) : PcCode :=
  compilePubLoop trips (namedCtKernelBody kernel) [.ret]

theorem namedCtKernelLoop_spectre_v1_immunity (kernel : NamedCtKernel) (trips : Nat)
    (R : ConstantTimeIsa.X86State → ConstantTimeIsa.X86State → Prop)
    (inv : PcPublicInvariant (namedCtKernelLoop kernel trips) R)
    (a b : ConstantTimeIsa.X86State) (h : R a b) (pred : PredictorOracle) (W fuel : Nat) :
    pcSpecRun (namedCtKernelLoop kernel trips) pred W fuel 0 [] a =
      pcSpecRun (namedCtKernelLoop kernel trips) pred W fuel 0 [] b :=
  pubLoop_speculative_ni trips (namedCtKernelBody kernel) [.ret] R inv a b h pred W fuel

/-- Every named schema has an actual predictor-visible back-edge at its final branch. -/
theorem namedCtKernelLoop_has_back_edge (kernel : NamedCtKernel) (trips : Nat) :
    (namedCtKernelLoop kernel trips)[namedCtKernelBody kernel |>.length + 4]? =
      some (.branch (.nz .rcx) 3) := by
  cases kernel <;> simp [namedCtKernelLoop, compilePubLoop, namedCtKernelBody]

def binaryNoConditionalBranches (prog : List (DecodedInstr Qsag.X86Instr)) : Bool :=
  prog.all fun d => match d.instr with | .jcc _ _ => false | _ => true

theorem binary_branchfree_speculation_is_architectural
    (prog : List (DecodedInstr Qsag.X86Instr))
    (hn : binaryNoConditionalBranches prog = true) (pred : PredictorOracle) (W fuel : Nat) :
    ∀ hist st, binarySpecRun prog pred W fuel hist st = (runX86 prog fuel st).2.map .arch := by
  induction fuel with
  | zero => intros; rfl
  | succ fuel ih =>
    intro hist st
    simp only [binarySpecRun, runX86]
    split
    · rfl
    · cases hd : findInstrAtPc st.pc prog with
      | none => rfl
      | some d =>
        have hm : d ∈ prog := by
          have aux : ∀ (xs : List (DecodedInstr Qsag.X86Instr)),
              findInstrAtPc st.pc xs = some d → d ∈ xs := by
            intro xs
            induction xs with
            | nil => simp [findInstrAtPc]
            | cons x xs ih =>
              intro hx
              simp only [findInstrAtPc] at hx
              split at hx
              · cases hx; exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ (ih hx)
          exact aux prog hd
        have hb := List.all_eq_true.mp hn d hm
        cases hi : d.instr <;> simp_all only [Bool.false_eq_true, List.map_cons]
        all_goals exact congrArg (BinarySpecObs.arch (stepX86 d st).2 :: ·) (ih hist (stepX86 d st).1)

/-- Checked byte decoding plus checked binary CT imply Spectre-v1 NI for every window and fuel
    on branch-free compiled symbols. -/
theorem decoded_kernel_speculative_ni (bytes : List UInt8) (contract : FuncContract)
    (prog : List (DecodedInstr Qsag.X86Instr))
    (hd : decodeX86Stream bytes = some prog)
    (hn : binaryNoConditionalBranches prog = true)
    (hc : checkX86ThreeWayNI bytes contract = true)
    (a b : Qsag.X86State) (hi : X86ContractInit contract a b)
    (pred : PredictorOracle) (W fuel : Nat) :
    binarySpecRun prog pred W fuel [] a = binarySpecRun prog pred W fuel [] b := by
  obtain ⟨decoded, he, htr, _⟩ := checkX86ThreeWayNI_sound hc hi fuel
  rw [hd] at he
  cases he
  rw [binary_branchfree_speculation_is_architectural prog hn pred W fuel,
    binary_branchfree_speculation_is_architectural prog hn pred W fuel, htr]

/-- The fixture index is checked against the symbol name below; absent symbols are not
    represented by an empty default stream in any theorem. -/
def fixtureSpecBytes (i : Nat) : List UInt8 :=
  ((x86ExtractedSlices[i]?).map (·.code)).getD []

def fixtureSpecContract (i : Nat) : FuncContract :=
  (x86SymbolContracts[i]?).getD (mkContract "missing" [] [] [])

def fixtureSpecProgram (i : Nat) : List (DecodedInstr Qsag.X86Instr) :=
  (decodeX86Stream (fixtureSpecBytes i)).getD []

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
 theorem ct_eq_32_rlib_speculation_certificate :
    (x86ExtractedSlices[13]?).map (·.name) = some "qsag_asm_ct_eq_32_x86_64" ∧
    decodeX86Stream (fixtureSpecBytes 13) = some (fixtureSpecProgram 13) ∧
    binaryNoConditionalBranches (fixtureSpecProgram 13) = true ∧
    checkX86ThreeWayNI (fixtureSpecBytes 13) (fixtureSpecContract 13) = true := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
 theorem goldilocks_mul_rlib_speculation_certificate :
    (x86ExtractedSlices[8]?).map (·.name) = some "qsag_asm_goldilocks_mul_ct_x86_64" ∧
    decodeX86Stream (fixtureSpecBytes 8) = some (fixtureSpecProgram 8) ∧
    binaryNoConditionalBranches (fixtureSpecProgram 8) = true ∧
    checkX86ThreeWayNI (fixtureSpecBytes 8) (fixtureSpecContract 8) = true := by
  decide +kernel

theorem ct_eq_32_rlib_spectre_v1_immunity (a b : Qsag.X86State)
    (hi : X86ContractInit (fixtureSpecContract 13) a b) (pred : PredictorOracle) (W fuel : Nat) :
    binarySpecRun (fixtureSpecProgram 13) pred W fuel [] a =
      binarySpecRun (fixtureSpecProgram 13) pred W fuel [] b :=
  decoded_kernel_speculative_ni _ _ _ ct_eq_32_rlib_speculation_certificate.2.1
    ct_eq_32_rlib_speculation_certificate.2.2.1 ct_eq_32_rlib_speculation_certificate.2.2.2
    a b hi pred W fuel

theorem goldilocks_mul_rlib_spectre_v1_immunity (a b : Qsag.X86State)
    (hi : X86ContractInit (fixtureSpecContract 8) a b) (pred : PredictorOracle) (W fuel : Nat) :
    binarySpecRun (fixtureSpecProgram 8) pred W fuel [] a =
      binarySpecRun (fixtureSpecProgram 8) pred W fuel [] b :=
  decoded_kernel_speculative_ni _ _ _ goldilocks_mul_rlib_speculation_certificate.2.1
    goldilocks_mul_rlib_speculation_certificate.2.2.1 goldilocks_mul_rlib_speculation_certificate.2.2.2
    a b hi pred W fuel


/-- Lower a public-trip loop with a reserved counter register. The zero-trip entry check and
    the back-edge are both predictor-visible. `after` remains executable on a predicted exit.
    Trips below 2^64 have the expected counter representation. -/
def compilePubLoop (trips : Nat) (body : List ConstantTimeIsa.X86Instr) (after : PcCode) : PcCode :=
  [.op (.movImm64 .rcx (BitVec.ofNat 64 trips)), .branch (.nz .rcx) 3,
    .jump (body.length + 5)] ++
    body.map .op ++ [.op (.addImm64 .rcx (-1)), .branch (.nz .rcx) 3] ++ after

/-- A `pubLoop` lowering inherits fuel-bounded speculative NI from an invariant which holds on
    both the loop and its continuation, not merely the architecturally executed iterations. -/
theorem pubLoop_speculative_ni (trips : Nat) (body : List ConstantTimeIsa.X86Instr)
    (after : PcCode) (R : ConstantTimeIsa.X86State → ConstantTimeIsa.X86State → Prop)
    (inv : PcPublicInvariant (compilePubLoop trips body after) R)
    (a b : ConstantTimeIsa.X86State) (h : R a b) (pred : PredictorOracle) (W fuel : Nat) :
    pcSpecRun (compilePubLoop trips body after) pred W fuel 0 [] a =
      pcSpecRun (compilePubLoop trips body after) pred W fuel 0 [] b :=
  public_loop_fuel_bounded_speculative_ni _ R inv pred W fuel 0 [] a b h

/-- Only the pointer, loop counter and return hygiene are public. All memory and the loaded
    data register can differ. Thus extra speculative loads do not require in-bounds contents
    to be public: their addresses are public and their data never become an address. -/
def PublicPointerEq (a b : ConstantTimeIsa.X86State) : Prop :=
  a.gpr .rdi = b.gpr .rdi ∧ a.gpr .rcx = b.gpr .rcx ∧ a.ymmUpperDirty = b.ymmUpperDirty

def publicPointerLoop (trips : Nat) : PcCode :=
  compilePubLoop trips [.load64 .rax .rdi 0, .addImm64 .rdi 8]
    [.op (.load64 .rax .rdi 0), .ret]

theorem publicPointerLoop_invariant (trips : Nat) :
    PcPublicInvariant (publicPointerLoop trips) PublicPointerEq := by
  constructor
  · intro pc i hi a b hab
    rcases hab with ⟨hp, hc, hd⟩
    rcases pc with _ | pc <;> simp [publicPointerLoop, compilePubLoop] at hi
    · cases hi
      simp [execX86Instr, ConstantTimeIsa.X86State.setGpr, PublicPointerEq, hp, hd]
    · rcases pc with _ | pc <;> simp at hi
      rcases pc with _ | pc <;> simp at hi
      rcases pc with _ | pc <;> simp at hi
      · cases hi
        simp [execX86Instr, ConstantTimeIsa.X86State.setGpr, PublicPointerEq, hp, hc, hd]
      · rcases pc with _ | pc <;> simp at hi
        · cases hi
          simp [execX86Instr, ConstantTimeIsa.X86State.setGpr, PublicPointerEq, hp, hc, hd]
        · rcases pc with _ | pc <;> simp at hi
          · cases hi
            simp [execX86Instr, ConstantTimeIsa.X86State.setGpr, PublicPointerEq, hp, hc, hd]
          · rcases pc with _ | pc <;> simp at hi
            rcases pc with _ | pc <;> simp at hi
            · cases hi
              simp [execX86Instr, ConstantTimeIsa.X86State.setGpr, PublicPointerEq, hp, hc, hd]
            · rcases pc with _ | pc <;> simp at hi
  · intro pc c target hi a b hab
    rcases pc with _ | pc <;> simp [publicPointerLoop, compilePubLoop] at hi
    rcases pc with _ | pc <;> simp at hi
    · obtain ⟨rfl, rfl⟩ := hi
      simp [BranchCond.eval, hab.2.1]
    · rcases pc with _ | pc <;> simp at hi
      rcases pc with _ | pc <;> simp at hi
      rcases pc with _ | pc <;> simp at hi
      rcases pc with _ | pc <;> simp at hi
      rcases pc with _ | pc <;> simp at hi
      · obtain ⟨rfl, rfl⟩ := hi
        simp [BranchCond.eval, hab.2.1]
      · rcases pc with _ | pc <;> simp at hi
        rcases pc with _ | pc <;> simp at hi
  · intro a b h; exact h.2.2

theorem public_pointer_pubLoop_spectre_v1_immunity (trips : Nat)
    (a b : ConstantTimeIsa.X86State) (h : PublicPointerEq a b)
    (pred : PredictorOracle) (W fuel : Nat) :
    pcSpecRun (publicPointerLoop trips) pred W fuel 0 [] a =
      pcSpecRun (publicPointerLoop trips) pred W fuel 0 [] b :=
  public_loop_fuel_bounded_speculative_ni _ _ (publicPointerLoop_invariant trips)
    pred W fuel 0 [] a b h


/-- Every requested upper index occurs in an accepted empty-cache release, for all d >= 2. -/
theorem all_depth_gate_covers_every_upper_layer (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (turn : FaultedSignTurn)
    (hSubPos : 0 < params.subtreeHeight)
    (hv : verifyPqHashSig suite params pk turn.msg turn.candidate = true)
    (l : Nat) (hl : 1 ≤ l) (hd : l < params.numLayers) :
    ∃ es, verifyBeforeReleaseAll suite params pk [] turn = some es ∧
      ∃ e ∈ es, e.key.layer = l := by
  obtain ⟨es, he, hm⟩ := all_depth_gate_complete suite params pk turn hSubPos hv
  refine ⟨es, he, ?_⟩
  have hmem : l ∈ es.map (fun e => e.key.layer) := by
    rw [hm]
    apply layer_range_member <;> omega
  exact List.mem_map.mp hmem

/-- The counter tooth's second opening is rejected by the full `(root,counter)` cache. -/
theorem full_cache_rejects_counter_tooth :
    ¬ CacheConsistent
      [⟨⟨1, 0, 0⟩, ⟨[], 0⟩, counterToothOpening 0⟩,
       ⟨⟨1, 0, 0⟩, ⟨[], 1⟩, counterToothOpening 1⟩] := by
  intro h
  have he := h ⟨⟨1, 0, 0⟩, ⟨[], 0⟩, counterToothOpening 0⟩ (by simp)
    ⟨⟨1, 0, 0⟩, ⟨[], 1⟩, counterToothOpening 1⟩ (by simp) rfl
  have hc := congrArg OtsMessage.tswCtr he
  cases hc

/-- Reusable connection to the ISA taint checker. A stable taint state suffices for loops whose
    operations preserve it; branch registers/flags and return hygiene are public in the low
    equivalence relation. More precise invariants can use `PcPublicInvariant` directly. -/
theorem pcPublicInvariant_of_checker (code : PcCode) (memPol : BitVec 64 → SecLabel)
    (secHeap : Bool) (hPol : secHeap = true → ∀ a, memPol a = .sec)
    (τ : X86TaintState)
    (hOp : ∀ (pc : Nat) (i : ConstantTimeIsa.X86Instr), code[pc]? = some (PcInstr.op i) → checkX86Instr secHeap τ i = some τ)
    (hBranch : ∀ (pc : Nat) (c : BranchCond) (target : Nat), code[pc]? = some (PcInstr.branch c target) →
      match c with | .nz r => τ.gpr r = .pub | .below | .aboveEq => τ.cf = .pub) :
    PcPublicInvariant code (X86LowEq memPol τ) := by
  constructor
  · intro pc i hi a b h
    exact checkX86Instr_sound memPol secHeap hPol τ τ i pc (hOp pc i hi) a b h
  · intro pc c target hi a b h
    have hb := hBranch pc c target hi
    cases c with
    | nz r => simp only [BranchCond.eval, h.1 r hb]
    | below => exact h.2.2.1 hb
    | aboveEq => simp only [BranchCond.eval, h.2.2.1 hb]
  · intro a b h; exact h.2.2.2.2.2.2.2.2.1

/-- Executable non-vacuity at both requested depths, with an inexpensive toy hash suite. -/
def deepToyParams (d : Nat) : PqHashParams :=
  { zeroToyParams with numLayers := d, statefulJorts := true }

def deepToyTurn (d : Nat) : FaultedSignTurn :=
  { msg := []
    candidate := ⟨[], 0, 0, [], List.replicate d ⟨0, [List.replicate 32 0], [List.replicate 32 0]⟩⟩ }

set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
 theorem seven_and_twenty_two_layer_release_inhabited :
    (verifyBeforeReleaseAll zeroToySuite (deepToyParams 7) ⟨[], List.replicate 32 0⟩ []
      (deepToyTurn 7)).map (fun es => es.map (fun e => e.key.layer)) = some (List.range' 1 6) ∧
    (verifyBeforeReleaseAll zeroToySuite (deepToyParams 22) ⟨[], List.replicate 32 0⟩ []
      (deepToyTurn 22)).map (fun es => es.map (fun e => e.key.layer)) = some (List.range' 1 21) := by
  decide +kernel

/-- Hypertree-level input, after the enclosing signature scheme has authenticated its initial
    digest/FORS root. This API does not impose the full `HashSigs` format's total-height cap. -/
structure HypertreeGateTurn where
  globalIdx : Nat
  rand : List UInt8
  root : List UInt8
  sigs : List LayerXmssSig

/-- Layer-level gate for any d-layer hypertree. Enforces `AdrsGateValid` per-coordinate bounds
    (admitting height-66 `22 × 3` trees without `UInt32`/`UInt64` address aliasing), layer count,
    verified top root, and encoded-`HashAdrs` cache consistency before committing. -/
def verifyHypertreeBeforeRelease (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (cache : List LayerRelease) (turn : HypertreeGateTurn) :
    Option (List LayerRelease) := do
  if !AdrsGateValid params turn.globalIdx then none
  else if turn.sigs.length ≠ params.numLayers then none else do
    if verifyHypertreeLayers suite params pk.pkSeed pk.pkRoot turn.rand 0 turn.globalIdx
        turn.root turn.sigs ≠ some pk.pkRoot then none else do
      let es ← verifiedLayerMessages suite params pk 0 turn.globalIdx turn.rand turn.root turn.sigs
      if AdrsCacheConsistent (cache ++ es.drop 1) then some (es.drop 1) else none

theorem verifyHypertreeBeforeRelease_adrsConsistent (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (cache es : List LayerRelease)
    (turn : HypertreeGateTurn)
    (h : verifyHypertreeBeforeRelease suite params pk cache turn = some es) :
    AdrsCacheConsistent (cache ++ es) := by
  unfold verifyHypertreeBeforeRelease at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨entries, _, h⟩ := h
        split at h
        · next hc => cases h; exact hc
        · cases h

theorem verifyHypertreeBeforeRelease_consistent (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (cache es : List LayerRelease)
    (turn : HypertreeGateTurn)
    (h : verifyHypertreeBeforeRelease suite params pk cache turn = some es) :
    CacheConsistent (cache ++ es) :=
  adrsCacheConsistent_implies_cacheConsistent
    (verifyHypertreeBeforeRelease_adrsConsistent suite params pk cache es turn h)

theorem verifyHypertreeBeforeRelease_validCoords (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (cache es : List LayerRelease)
    (turn : HypertreeGateTurn)
    (h : verifyHypertreeBeforeRelease suite params pk cache turn = some es) :
    ∀ e ∈ es, e.key.ValidCoords = true := by
  unfold verifyHypertreeBeforeRelease at h
  split at h
  · cases h
  · next hGateNeg =>
    have hGate : AdrsGateValid params turn.globalIdx = true := by
      cases hx : AdrsGateValid params turn.globalIdx
      · exact False.elim (hGateNeg (by simp only [hx, Bool.not_false]))
      · rfl
    split at h
    · cases h
    · next hn =>
      have hlen : turn.sigs.length = params.numLayers := Decidable.of_not_not hn
      clear hn
      split at h
      · cases h
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨entries, he, h⟩ := h
        split at h
        · cases h
          simp only [AdrsGateValid, Bool.and_eq_true, decide_eq_true_eq] at hGate
          rcases hGate with ⟨⟨⟨_, hSub⟩, hNum⟩, hTree⟩
          have hAll := verifiedLayerMessages_validCoords suite params pk turn.sigs
            0 turn.globalIdx turn.rand turn.root entries hSub (by omega) hTree he
          intro e hm
          exact hAll e (List.mem_of_mem_drop hm)
        · cases h

def guardedHypertreeTrace (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) : List LayerRelease → List HypertreeGateTurn → List LayerRelease
  | cache, [] => cache
  | cache, turn :: rest =>
    match verifyHypertreeBeforeRelease suite params pk cache turn with
    | none => guardedHypertreeTrace suite params pk cache rest
    | some es => guardedHypertreeTrace suite params pk (cache ++ es) rest

theorem guardedHypertreeTrace_adrsConsistent (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (turns : List HypertreeGateTurn) :
    ∀ cache, AdrsCacheConsistent cache →
      AdrsCacheConsistent (guardedHypertreeTrace suite params pk cache turns) := by
  induction turns with
  | nil => intro cache h; exact h
  | cons turn rest ih =>
    intro cache hc
    simp only [guardedHypertreeTrace]
    split
    · exact ih cache hc
    · next es he =>
      exact ih _ (verifyHypertreeBeforeRelease_adrsConsistent suite params pk _ _ turn he)

theorem guardedHypertreeTrace_consistent (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (turns : List HypertreeGateTurn) :
    ∀ cache, AdrsCacheConsistent cache →
      CacheConsistent (guardedHypertreeTrace suite params pk cache turns) :=
  fun cache hc =>
    adrsCacheConsistent_implies_cacheConsistent
      (guardedHypertreeTrace_adrsConsistent suite params pk turns cache hc)

theorem guardedHypertreeTrace_validCoords (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (turns : List HypertreeGateTurn) :
    ∀ cache, (∀ e ∈ cache, e.key.ValidCoords = true) →
      ∀ e ∈ guardedHypertreeTrace suite params pk cache turns, e.key.ValidCoords = true := by
  induction turns with
  | nil => intro cache h; exact h
  | cons turn rest ih =>
    intro cache hc
    simp only [guardedHypertreeTrace]
    split
    · exact ih cache hc
    · next es he =>
      apply ih
      intro e hm
      rcases List.mem_append.mp hm with hOld | hNew
      · exact hc e hOld
      · exact verifyHypertreeBeforeRelease_validCoords suite params pk cache es turn he e hNew

/-- Any depth and total height: the layer-level verifier/cache gate excludes a second WOTS+C
    message at every encoded 32-byte `HashAdrs` throughout an arbitrary adversarial trace. -/
theorem arbitrary_hypertree_gate_prevents_adrs_wots_reuse (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (turns : List HypertreeGateTurn)
    (a b : LayerRelease)
    (ha : a ∈ guardedHypertreeTrace suite params pk [] turns)
    (hb : b ∈ guardedHypertreeTrace suite params pk [] turns)
    (hk : a.key.toEncodedAdrs = b.key.toEncodedAdrs) :
    a.key = b.key ∧ a.signed = b.signed := by
  have hVa := guardedHypertreeTrace_validCoords suite params pk turns [] (by simp) a ha
  have hVb := guardedHypertreeTrace_validCoords suite params pk turns [] (by simp) b hb
  exact ⟨(otsPosition_toEncodedAdrs_injective hVa hVb).mp hk,
    guardedHypertreeTrace_adrsConsistent suite params pk turns [] (by simp [AdrsCacheConsistent]) a ha b hb hk⟩

theorem arbitrary_hypertree_gate_prevents_fault_wots_reuse (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (turns : List HypertreeGateTurn)
    (a b : LayerRelease)
    (ha : a ∈ guardedHypertreeTrace suite params pk [] turns)
    (hb : b ∈ guardedHypertreeTrace suite params pk [] turns)
    (hk : a.key = b.key) : a.signed = b.signed :=
  (arbitrary_hypertree_gate_prevents_adrs_wots_reuse suite params pk turns a b ha hb
    (congrArg OtsPosition.toEncodedAdrs hk)).2

/-- Complete coverage under coordinate bounds (no 62-bit total-height premise): each upper layer
    1,...,d-1 is cached. -/
theorem hypertree_gate_complete (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (turn : HypertreeGateTurn)
    (hGate : AdrsGateValid params turn.globalIdx = true)
    (hlen : turn.sigs.length = params.numLayers)
    (hv : verifyHypertreeLayers suite params pk.pkSeed pk.pkRoot turn.rand 0 turn.globalIdx
      turn.root turn.sigs = some pk.pkRoot) :
    ∃ es, verifyHypertreeBeforeRelease suite params pk [] turn = some es ∧
      es.map (fun e => e.key.layer) = List.range' 1 (params.numLayers - 1) := by
  obtain ⟨es, he, hl⟩ := verifiedLayerMessages_complete suite params pk _ _ _ _ _ _ hv
  have hd : (es.drop 1).map (fun e => e.key.layer) =
      List.range' 1 (params.numLayers - 1) := by
    rw [List.map_drop, hl, hlen, List.drop_range']
  have hGateFacts : params.subtreeHeight ≤ 31 ∧ params.numLayers ≤ 2 ^ 32 ∧
      turn.globalIdx / 2 ^ params.subtreeHeight < 2 ^ 64 := by
    simp only [AdrsGateValid, Bool.and_eq_true, decide_eq_true_eq] at hGate
    exact ⟨hGate.1.1.2, hGate.1.2, hGate.2⟩
  have hValAll := verifiedLayerMessages_validCoords suite params pk turn.sigs
    0 turn.globalIdx turn.rand turn.root es hGateFacts.1 (by omega) hGateFacts.2.2 he
  have hc := adrsCacheConsistent_of_distinct_valid_layers (es.drop 1)
    (fun e hm => hValAll e (List.mem_of_mem_drop hm))
    (by rw [hd]; exact layer_range_nodup _ _)
  refine ⟨es.drop 1, ?_, hd⟩
  simpa [verifyHypertreeBeforeRelease, hGate, hlen, hv, he] using hc

/-- **`#tooth` Witness (`tooth_adrs_gate_rejects_aliasing_inputs`)**:
    `verifyHypertreeBeforeRelease` rejects `subtreeHeight = 0` and rejects oversized `globalIdx = 2^67`
    at `22 × 3`, while admitting the entire height-66 leaf domain (`globalIdx = 2^66 - 1`). -/
theorem tooth_adrs_gate_rejects_aliasing_inputs :
    verifyHypertreeBeforeRelease zeroToySuite { deepToyParams 2 with subtreeHeight := 0 }
      ⟨[], List.replicate 32 0⟩ [] ⟨2 ^ 64, [], [], []⟩ = none ∧
    verifyHypertreeBeforeRelease zeroToySuite { deepToyParams 22 with subtreeHeight := 3 }
      ⟨[], List.replicate 32 0⟩ [] ⟨2 ^ 67, [], [], []⟩ = none ∧
    AdrsGateValid { deepToyParams 22 with subtreeHeight := 3 } (2 ^ 66 - 1) = true := by
  exact ⟨by decide, by decide, by decide⟩

/- The 22-layer, height-3 shape (66 total levels) is not rejected by the layer gate. This is
    an executable model witness for the shape, not an identification of WOTS+C with FIPS WOTS+. -/
set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
 theorem twenty_two_height_three_layer_gate_inhabited :
    (verifyHypertreeBeforeRelease zeroToySuite
      { deepToyParams 22 with subtreeHeight := 3 } ⟨[], List.replicate 32 0⟩ []
      ⟨0, [], [], List.replicate 22
        ⟨0, [List.replicate 32 0], List.replicate 3 (List.replicate 32 0)⟩⟩).map
        (fun es => es.map (fun e => e.key.layer)) = some (List.range' 1 21) := by
  decide +kernel

/-- The next upper key consumes the tree index of the current key as its global index. -/
def nextOtsPosition (params : PqHashParams) (key : OtsPosition) : OtsPosition :=
  ⟨key.layer + 1, key.treeIdx / 2 ^ params.subtreeHeight, key.treeIdx % 2 ^ params.subtreeHeight⟩

def openingGlobalIdx (params : PqHashParams) (key : OtsPosition) : Nat :=
  key.treeIdx * 2 ^ params.subtreeHeight + key.leafIdx

/-- The opening is anchored to the next cached root, or to the public root at the top layer.
    Only input roots/counters are cached; this proposition does not add a cached output root. -/
def OpeningBound (suite : TweakableHashSuite) (params : PqHashParams) (pk : PqPublicKey)
    (journal : List LayerRelease) (e : LayerRelease) : Prop :=
  e.signed.tswCtr = e.opening.tswCtr ∧
  ∃ top, verifyHypertreeLayers suite params pk.pkSeed pk.pkRoot [] e.key.layer
    (openingGlobalIdx params e.key) e.signed.root [e.opening] = some top ∧
    (if e.key.layer + 1 = params.numLayers then top = pk.pkRoot
     else ∃ next ∈ journal, next.key = nextOtsPosition params e.key ∧ top = next.signed.root)

theorem openingBound_mono (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (xs ys : List LayerRelease) (e : LayerRelease)
    (hsub : ∀ x ∈ xs, x ∈ ys) (h : OpeningBound suite params pk xs e) :
    OpeningBound suite params pk ys e := by
  obtain ⟨hc, top, hv, ht⟩ := h
  refine ⟨hc, top, hv, ?_⟩
  by_cases hl : e.key.layer + 1 = params.numLayers
  · simpa only [hl, ↓reduceIte] using ht
  · simp only [hl, ↓reduceIte] at ht ⊢
    obtain ⟨n, hn, hk, hr⟩ := ht
    exact ⟨n, hsub n hn, hk, hr⟩

/-- Successful upper-layer traversals give each opening its next-root anchor. -/
theorem verifiedLayerMessages_openingBound (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (sigs : List LayerXmssSig) :
    ∀ layer g root es journal,
      layer + sigs.length = params.numLayers →
      verifiedLayerMessages suite params pk layer g [] root sigs = some es →
      verifyHypertreeLayers suite params pk.pkSeed pk.pkRoot [] layer g root sigs = some pk.pkRoot →
      (∀ e ∈ es, e ∈ journal) →
      ∀ e ∈ es, OpeningBound suite params pk journal e := by
  induction sigs with
  | nil =>
    intro layer g root es journal _ he _ _ e hm
    simp only [verifiedLayerMessages, Option.some.injEq] at he
    subst es; cases hm
  | cons sig rest ih =>
    intro layer g root es journal hlen he hv hsub e hm
    obtain ⟨mid, hs, ht⟩ := (verifyHypertreeLayers_split suite params pk.pkSeed pk.pkRoot
      [] layer g root sig rest pk.pkRoot).mp hv
    simp only [verifiedLayerMessages, hs, Option.bind_some, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at he
    obtain ⟨tail, htail, rfl⟩ := he
    rcases List.mem_cons.mp hm with rfl | hm
    · refine ⟨rfl, mid, ?_, ?_⟩
      · change verifyHypertreeLayers suite params pk.pkSeed pk.pkRoot [] layer
          (g / 2 ^ params.subtreeHeight * 2 ^ params.subtreeHeight + g % 2 ^ params.subtreeHeight)
          root [sig] = some mid
        rw [Nat.div_add_mod']
        exact hs
      · dsimp only
        by_cases hlast : layer + 1 = params.numLayers
        · rw [ite_eq_left hlast]
          have hn : rest.length = 0 := by simp only [List.length_cons] at hlen; omega
          have hr : rest = [] := List.length_eq_zero_iff.mp hn
          subst rest
          simpa only [verifyHypertreeLayers_nil, Option.some.injEq] using ht
        · rw [ite_eq_right hlast]
          cases rest with
          | nil => simp at hlen; exact False.elim (hlast hlen)
          | cons next rest =>
            simp only [verifiedLayerMessages, Option.bind_eq_bind, Option.bind_eq_some_iff,
              Option.pure_def, Option.some.injEq] at htail
            obtain ⟨mid', _, tail', _, rfl⟩ := htail
            exact ⟨_, hsub _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl, rfl⟩
    · exact ih (layer + 1) (g / 2 ^ params.subtreeHeight) mid tail journal
        (by simp only [List.length_cons] at hlen; omega) htail ht
        (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) e hm

/-- A full-verifier release has anchored upper openings at every depth. -/
theorem verifyBeforeReleaseAll_openingBound (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (cache es : List LayerRelease) (turn : FaultedSignTurn)
    (h : verifyBeforeReleaseAll suite params pk cache turn = some es) :
    ∀ e ∈ es, OpeningBound suite params pk (cache ++ es) e := by
  unfold verifyBeforeReleaseAll at h
  split at h
  · cases h
  · split at h
    · cases h
    · next hv =>
      have hv' : verifyPqHashSig suite params pk turn.msg turn.candidate = true := by
        cases hx : verifyPqHashSig suite params pk turn.msg turn.candidate <;> simp_all
      obtain ⟨rand, root, hs, ht, hlen⟩ := verifyPqHashSig_layers suite params pk _ _ hv'
      simp only [hs] at h
      cases hsig : turn.candidate.layerSigs with
      | nil =>
        simp [hsig, verifiedLayerMessages] at h
        rw [h.2]; intro e he; cases he
      | cons sig rest =>
        rw [hsig] at ht hlen h
        obtain ⟨mid, hm, hu⟩ := (verifyHypertreeLayers_split suite params pk.pkSeed pk.pkRoot
          rand 0 turn.candidate.leafGlobalIdx root sig rest pk.pkRoot).mp ht
        simp only [verifiedLayerMessages, hm, Option.bind_some, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
        obtain ⟨all, ⟨tail, he, rfl⟩, h⟩ := h
        simp only [List.drop_succ_cons, List.drop_zero] at h
        split at h
        · cases h
          exact verifiedLayerMessages_openingBound suite params pk rest 1
            (turn.candidate.leafGlobalIdx / 2 ^ params.subtreeHeight) mid es (cache ++ es)
            (by simpa [Nat.add_comm] using hlen) he hu
            (fun x hx => List.mem_append.mpr (Or.inr hx))
        · cases h

theorem guardedSignTraceAll_openingBound (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (turns : List FaultedSignTurn) :
    ∀ cache, (∀ e ∈ cache, OpeningBound suite params pk cache e) →
      ∀ e ∈ guardedSignTraceAll suite params pk cache turns,
        OpeningBound suite params pk (guardedSignTraceAll suite params pk cache turns) e := by
  induction turns with
  | nil => intro cache h; exact h
  | cons turn rest ih =>
    intro cache hc
    simp only [guardedSignTraceAll]
    split
    · exact ih cache hc
    · next es he =>
      apply ih
      intro e hm
      rcases List.mem_append.mp hm with hOld | hNew
      · exact openingBound_mono suite params pk cache (cache ++ es) e
          (fun x hx => List.mem_append.mpr (Or.inl hx)) (hc e hOld)
      · exact verifyBeforeReleaseAll_openingBound suite params pk cache es turn he e hNew

/-- The stronger opening-uniqueness conclusion also lifts to arbitrary depth. Equality of the
    next cached root anchors non-top layers; the public root anchors the top layer. -/
theorem bound_cached_openings_unique_or_collision (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (journal : List LayerRelease)
    (hc : CacheConsistent journal)
    (valid : ∀ e ∈ journal, OpeningBound suite params pk journal e)
    (a b : LayerRelease) (ha : a ∈ journal) (hb : b ∈ journal) (hk : a.key = b.key) :
    a.signed = b.signed ∧ (a.opening = b.opening ∨ Collision suite.rawHash) := by
  have hm := hc a ha b hb hk
  refine ⟨hm, ?_⟩
  obtain ⟨hca, topa, hva, hta⟩ := valid a ha
  obtain ⟨hcb, topb, hvb, htb⟩ := valid b hb
  have ht : topa = topb := by
    rw [← hk] at htb
    by_cases hl : a.key.layer + 1 = params.numLayers
    · simp only [hl, ↓reduceIte] at hta htb
      exact hta.trans htb.symm
    · simp only [hl, ↓reduceIte] at hta htb
      obtain ⟨na, hna, hka, hra⟩ := hta
      obtain ⟨nb, hnb, hkb, hrb⟩ := htb
      have hn := hc na hna nb hnb (hka.trans hkb.symm)
      exact hra.trans ((congrArg OtsMessage.root hn).trans hrb.symm)
  have hctr : a.opening.tswCtr = b.opening.tswCtr := by rw [← hca, ← hcb, hm]
  obtain ⟨hla, hwa⟩ := verifyHypertreeLayers_single suite params pk.pkSeed pk.pkRoot []
    a.key.layer (openingGlobalIdx params a.key) a.signed.root a.opening topa hva
  obtain ⟨hlb, hwb⟩ := verifyHypertreeLayers_single suite params pk.pkSeed pk.pkRoot []
    b.key.layer (openingGlobalIdx params b.key) b.signed.root b.opening topb hvb
  rw [← hk, ← hm, ← hctr, ← ht] at hwb
  rcases wots_openings_unique_or_collision suite params pk.pkSeed _ _ _ _ _ _ _ _ _
    hla hlb hwa hwb with ⟨hchains, hpath⟩ | hcol
  · left
    cases ha' : a.opening
    cases hb' : b.opening
    rw [ha', hb'] at hctr hchains hpath
    simp only at hctr hchains hpath
    rw [hctr, hchains, hpath]
  · exact Or.inr hcol

/-- Encoded-`HashAdrs`-level opening uniqueness on `guardedSignTraceAll`: any two entries whose
    32-byte WOTS+C addresses agree have identical `Nat` positions, identical `(root, tswCtr)`,
    and identical openings unless a `suite.rawHash` collision is exhibited. -/
theorem verify_before_release_adrs_openings_unique_or_collision (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (turns : List FaultedSignTurn)
    (a b : LayerRelease)
    (ha : a ∈ guardedSignTraceAll suite params pk [] turns)
    (hb : b ∈ guardedSignTraceAll suite params pk [] turns)
    (hk : a.key.toEncodedAdrs = b.key.toEncodedAdrs) :
    a.key = b.key ∧ a.signed = b.signed ∧ (a.opening = b.opening ∨ Collision suite.rawHash) := by
  have hkEq := (all_depth_released_adrs_message_unique suite params pk turns a b ha hb hk).1
  exact ⟨hkEq, bound_cached_openings_unique_or_collision suite params pk _
    (guardedSignTraceAll_consistent suite params pk turns [] (by simp [AdrsCacheConsistent]))
    (guardedSignTraceAll_openingBound suite params pk turns [] (by simp)) a b ha hb hkEq⟩

/-- Full-signature gate, all depths: one message and one opening per upper key, or collision. -/
theorem verify_before_release_prevents_fault_wots_reuse (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (turns : List FaultedSignTurn)
    (a b : LayerRelease)
    (ha : a ∈ guardedSignTraceAll suite params pk [] turns)
    (hb : b ∈ guardedSignTraceAll suite params pk [] turns)
    (hk : a.key = b.key) :
    a.signed = b.signed ∧ (a.opening = b.opening ∨ Collision suite.rawHash) :=
  (verify_before_release_adrs_openings_unique_or_collision suite params pk turns a b ha hb
    (congrArg OtsPosition.toEncodedAdrs hk)).2

theorem verifyHypertreeBeforeRelease_openingBound (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (cache es : List LayerRelease)
    (turn : HypertreeGateTurn)
    (h : verifyHypertreeBeforeRelease suite params pk cache turn = some es) :
    ∀ e ∈ es, OpeningBound suite params pk (cache ++ es) e := by
  unfold verifyHypertreeBeforeRelease at h
  split at h
  · cases h
  · split at h
    · cases h
    · next hn =>
      have hlen : turn.sigs.length = params.numLayers := Decidable.of_not_not hn
      clear hn
      split at h
      · cases h
      · next hv =>
        have ht : verifyHypertreeLayers suite params pk.pkSeed pk.pkRoot turn.rand 0
            turn.globalIdx turn.root turn.sigs = some pk.pkRoot :=
          Decidable.of_not_not hv
        cases hsig : turn.sigs with
        | nil =>
          simp [hsig, verifiedLayerMessages] at h
          rw [h.2]; intro e he; cases he
        | cons sig rest =>
          rw [hsig] at ht hlen h
          obtain ⟨mid, hm, hu⟩ := (verifyHypertreeLayers_split suite params pk.pkSeed pk.pkRoot
            turn.rand 0 turn.globalIdx turn.root sig rest pk.pkRoot).mp ht
          simp only [verifiedLayerMessages, hm, Option.bind_some, Option.bind_eq_bind,
            Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
          obtain ⟨all, ⟨tail, he, rfl⟩, h⟩ := h
          simp only [List.drop_succ_cons, List.drop_zero] at h
          split at h
          · cases h
            exact verifiedLayerMessages_openingBound suite params pk rest 1
              (turn.globalIdx / 2 ^ params.subtreeHeight) mid es (cache ++ es)
              (by simpa [Nat.add_comm] using hlen) he hu
              (fun x hx => List.mem_append.mpr (Or.inr hx))
          · cases h

theorem guardedHypertreeTrace_openingBound (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (turns : List HypertreeGateTurn) :
    ∀ cache, (∀ e ∈ cache, OpeningBound suite params pk cache e) →
      ∀ e ∈ guardedHypertreeTrace suite params pk cache turns,
        OpeningBound suite params pk (guardedHypertreeTrace suite params pk cache turns) e := by
  induction turns with
  | nil => intro cache h; exact h
  | cons turn rest ih =>
    intro cache hc
    simp only [guardedHypertreeTrace]
    split
    · exact ih cache hc
    · next es he =>
      apply ih
      intro e hm
      rcases List.mem_append.mp hm with hOld | hNew
      · exact openingBound_mono suite params pk cache (cache ++ es) e
          (fun x hx => List.mem_append.mpr (Or.inl hx)) (hc e hOld)
      · exact verifyHypertreeBeforeRelease_openingBound suite params pk cache es turn he e hNew

/-- Encoded-`HashAdrs`-level opening uniqueness on `guardedHypertreeTrace` (including `22 × 3`). -/
theorem arbitrary_depth_adrs_openings_unique_or_collision (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (turns : List HypertreeGateTurn)
    (a b : LayerRelease)
    (ha : a ∈ guardedHypertreeTrace suite params pk [] turns)
    (hb : b ∈ guardedHypertreeTrace suite params pk [] turns)
    (hk : a.key.toEncodedAdrs = b.key.toEncodedAdrs) :
    a.key = b.key ∧ a.signed = b.signed ∧ (a.opening = b.opening ∨ Collision suite.rawHash) := by
  have hkEq := (arbitrary_hypertree_gate_prevents_adrs_wots_reuse suite params pk turns a b ha hb hk).1
  exact ⟨hkEq, bound_cached_openings_unique_or_collision suite params pk _
    (guardedHypertreeTrace_consistent suite params pk turns [] (by simp [AdrsCacheConsistent]))
    (guardedHypertreeTrace_openingBound suite params pk turns [] (by simp)) a b ha hb hkEq⟩

/-- The layer-level gate retains the full opening-uniqueness conclusion, without a total-height
    bound, including the 22-by-3 shape demonstrated above. -/
theorem arbitrary_depth_openings_unique_or_collision (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (turns : List HypertreeGateTurn)
    (a b : LayerRelease)
    (ha : a ∈ guardedHypertreeTrace suite params pk [] turns)
    (hb : b ∈ guardedHypertreeTrace suite params pk [] turns)
    (hk : a.key = b.key) :
    a.signed = b.signed ∧ (a.opening = b.opening ∨ Collision suite.rawHash) :=
  (arbitrary_depth_adrs_openings_unique_or_collision suite params pk turns a b ha hb
    (congrArg OtsPosition.toEncodedAdrs hk)).2

/-! ## 9. Production Shared-Core (`TAG_H_INTERNAL`) Gate & Crash-Recoverable Persistent Journal

This section lifts the all-layer fault-injection gate directly onto the Rust-exact production
verifier (`verifyProductionPqHashSig` and `verifyProductionHypertreeLayers` in `Qsag.HashSigs`),
where upper layers hash via `TAG_H_INTERNAL` (`productionLayerDigest`), stateless FORS indices are
threaded from `deriveProductionStatelessInputs`, FORS leaves use `(j, u)` addressing, and `.forsTree`
Merkle nodes bind `keyPair = kp0`.

It then models a crash-recoverable signer (`DurableUpperJournalState`) whose upper-layer journal
is persisted to durable storage *before* signature emission (`stepRecoverableProductionGate`),
proving multi-crash WOTS+C non-reuse alongside a `#tooth` witness showing volatile-only caches fail
across reboots.
-/

theorem verifyProductionHypertreeLayers_split (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed pkRoot rand : List UInt8) (layer g : Nat) (cur : List UInt8) (l : LayerXmssSig)
    (rest : List LayerXmssSig) (top : List UInt8) :
    verifyProductionHypertreeLayers suite params pkSeed pkRoot rand layer g cur (l :: rest) = some top ↔
      ∃ mid, verifyProductionHypertreeLayers suite params pkSeed pkRoot rand layer g cur [l] = some mid ∧
        verifyProductionHypertreeLayers suite params pkSeed pkRoot rand (layer + 1)
          (g / 2 ^ params.subtreeHeight) mid rest = some top := by
  rw [verifyProductionHypertreeLayers_cons, verifyProductionHypertreeLayers_cons]
  dsimp only
  split
  · simp
  · split
    · simp
    · split
      · simp
      · split
        · simp
        · split
          · simp
          · simp [verifyProductionHypertreeLayers_nil]

theorem verifyProductionHypertreeLayers_upper_rand_irrel (suite : TweakableHashSuite)
    (params : PqHashParams) (pkSeed pkRoot rand : List UInt8) (sigs : List LayerXmssSig) :
    ∀ layer g cur,
      1 ≤ layer →
      verifyProductionHypertreeLayers suite params pkSeed pkRoot rand layer g cur sigs =
        verifyProductionHypertreeLayers suite params pkSeed pkRoot [] layer g cur sigs := by
  induction sigs with
  | nil => intro layer g cur _; rfl
  | cons l rest ih =>
    intro layer g cur hLay
    have hNe0 : decide (layer = 0) = false := decide_eq_false (by omega)
    have hDig : productionLayerDigest suite params rand pkSeed pkRoot cur layer
        (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) (UInt32.ofNat (g % 2 ^ params.subtreeHeight)) l.tswCtr =
        productionLayerDigest suite params [] pkSeed pkRoot cur layer
        (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) (UInt32.ofNat (g % 2 ^ params.subtreeHeight)) l.tswCtr := by
      simp only [productionLayerDigest_eq, hNe0, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    rw [verifyProductionHypertreeLayers_cons, verifyProductionHypertreeLayers_cons]
    dsimp only
    rw [hDig]
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · split
            · rfl
            · exact ih (layer + 1) (g / 2 ^ params.subtreeHeight) _ (by omega)

theorem verifyProductionHypertreeLayers_single (suite : TweakableHashSuite) (params : PqHashParams)
    (pkSeed pkRoot rand : List UInt8) (layer g : Nat) (cur : List UInt8) (l : LayerXmssSig)
    (top : List UInt8)
    (h : verifyProductionHypertreeLayers suite params pkSeed pkRoot rand layer g cur [l] = some top) :
    ∃ digits,
      extractBaseWDigitsChecked params.w params.ell1
        (productionLayerDigest suite params rand pkSeed pkRoot cur layer
          (UInt64.ofNat (g / 2 ^ params.subtreeHeight))
          (UInt32.ofNat (g % 2 ^ params.subtreeHeight)) l.tswCtr) = some digits ∧
      l.wotsChains.length = params.ell1 ∧
      walkMerkleAuthPath suite pkSeed (UInt32.ofNat layer)
        (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) .tree params.subtreeHeight 0
        (g % 2 ^ params.subtreeHeight)
        (recoverWotsPkFromSig suite params pkSeed (UInt32.ofNat layer)
          (UInt64.ofNat (g / 2 ^ params.subtreeHeight)) (g % 2 ^ params.subtreeHeight)
          digits l.wotsChains) l.authPath = some top := by
  rw [verifyProductionHypertreeLayers_cons] at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · next digits hDig =>
      split at h
      · cases h
      · split at h
        · cases h
        · next hLen =>
          split at h
          · cases h
          · next mid hWalk =>
            rw [verifyProductionHypertreeLayers_nil] at h
            injection h with hEq; subst hEq
            rw [walkMerkleAuthPathKp_zero_eq] at hWalk
            exact ⟨digits, hDig, Decidable.not_not.mp hLen, hWalk⟩

/-- Production hypertree layer-0 start root (`thPreHash` in stateful mode, `recoverProductionForsPk`
    over XOF-derived FORS indices in stateless mode). -/
def productionHypertreeStart (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (msg : List UInt8) (sig : PqHashSig) : Option (List UInt8 × List UInt8) :=
  let mu := thPreHash suite pk.pkSeed pk.pkRoot msg
  if params.statefulJorts then
    if !sig.forsOpenings.isEmpty then none
    else some (sig.rRand, mu)
  else
    if sig.forsOpenings.length ≠ params.forsTrees then none
    else
      match deriveProductionStatelessInputs suite params sig.rRand pk.pkSeed pk.pkRoot mu with
      | none => none
      | some (derivedLeafIdx, idxs) =>
        if sig.leafGlobalIdx ≠ derivedLeafIdx then none
        else
          let subLeaves := 2 ^ params.subtreeHeight
          let kp0 := sig.leafGlobalIdx % subLeaves
          let tree0 := UInt64.ofNat (sig.leafGlobalIdx / subLeaves)
          (recoverProductionForsPk suite params pk.pkSeed tree0 kp0 idxs sig.forsOpenings).map
            fun forsPk => (sig.rRand, forsPk)

theorem adrsGateValid_of_productionWellFormed (params : PqHashParams) (leafIdx : Nat)
    (hWf : params.productionWellFormed = true)
    (hRange : params.productionLeafIdxInRange leafIdx = true) :
    AdrsGateValid params leafIdx = true := by
  obtain ⟨_, _, _, _, _, hSubPos, hSubLe30, _, _, hTot62, _, _, _, _⟩ :=
    params.productionWellFormed_facts hWf
  rw [PqHashParams.productionLeafIdxInRange_eq] at hRange
  dsimp only at hRange
  have hLtCap := of_decide_eq_true hRange
  have hCapLe62 : (if params.statefulJorts && decide (params.maxSigsLog2 < params.numLayers * params.subtreeHeight)
      then params.maxSigsLog2 else params.numLayers * params.subtreeHeight) ≤ 62 := by
    split
    · rename_i hC; simp only [Bool.and_eq_true, decide_eq_true_eq] at hC; omega
    · exact hTot62
  have hPowLe : 2 ^ (if params.statefulJorts && decide (params.maxSigsLog2 < params.numLayers * params.subtreeHeight)
      then params.maxSigsLog2 else params.numLayers * params.subtreeHeight) ≤ 2 ^ 62 :=
    Nat.pow_le_pow_right (by decide) hCapLe62
  have hNumLe62 : params.numLayers ≤ 62 := by
    have h1 : params.numLayers * 1 ≤ params.numLayers * params.subtreeHeight :=
      Nat.mul_le_mul_left _ hSubPos
    omega
  have hDivLe : leafIdx / 2 ^ params.subtreeHeight ≤ leafIdx := Nat.div_le_self _ _
  have h62Lt64 : (2 : Nat) ^ 62 < 2 ^ 64 := by decide
  simp only [AdrsGateValid, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨hSubPos, by omega⟩, by omega⟩, by omega⟩

theorem verifyProductionPqHashSig_layers (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (msg : List UInt8) (sig : PqHashSig)
    (h : verifyProductionPqHashSig suite params pk msg sig = true) :
    AdrsGateValid params sig.leafGlobalIdx = true ∧
    sig.layerSigs.length = params.numLayers ∧
    ∃ rand start,
      productionHypertreeStart suite params pk msg sig = some (rand, start) ∧
      verifyProductionHypertreeLayers suite params pk.pkSeed pk.pkRoot rand 0
        sig.leafGlobalIdx start sig.layerSigs = some pk.pkRoot := by
  rw [verifyProductionPqHashSig_eq] at h
  cases hWf : params.productionWellFormed
  · simp [hWf] at h
  · cases hRange : params.productionLeafIdxInRange sig.leafGlobalIdx
    · simp [hWf, hRange] at h
    · have hGate := adrsGateValid_of_productionWellFormed params sig.leafGlobalIdx hWf hRange
      simp only [hWf, hRange, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at h
      by_cases hLen : sig.layerSigs.length = params.numLayers
      · by_cases hCtr0 : sig.msgTswCtr = 0
        · simp only [hLen, hCtr0, ne_eq, not_true_eq_false, decide_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte] at h
          refine ⟨hGate, hLen, ?_⟩
          unfold productionHypertreeStart
          dsimp only at h ⊢
          split at h
          · next hSt =>
            simp only [hSt, ↓reduceIte]
            split at h
            · cases h
            · next hEmpty =>
              simp only [hEmpty]
              split at h
              · next top hVer =>
                exact ⟨sig.rRand, thPreHash suite pk.pkSeed pk.pkRoot msg, rfl,
                  by rw [hVer, of_decide_eq_true h]⟩
              · cases h
          · next hSt =>
            simp only [hSt]
            split at h
            · cases h
            · next hFLen =>
              simp only [hFLen, ↓reduceIte]
              split at h
              · cases h
              · next derivedLeaf idxs hDer =>
                simp only [hDer]
                split at h
                · cases h
                · next hLeafEq =>
                  simp only [hLeafEq, ↓reduceIte]
                  split at h
                  · cases h
                  · next forsPk hFors =>
                    split at h
                    · next top hVer =>
                      exact ⟨sig.rRand, forsPk, by simp [hFors],
                        by rw [hVer, of_decide_eq_true h]⟩
                    · cases h
        · simp [hLen, hCtr0] at h
      · simp [hLen] at h

/-- Extract per-layer `(OtsPosition, OtsMessage, LayerXmssSig)` entries via the production
    `verifyProductionHypertreeLayers` verifier (`TAG_H_INTERNAL` on all upper layers). -/
def verifiedProductionLayerMessages (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) : Nat → Nat → List UInt8 → List UInt8 →
      List LayerXmssSig → Option (List LayerRelease)
  | _, _, _, _, [] => some []
  | layer, g, rand, root, sig :: rest => do
    let next ← verifyProductionHypertreeLayers suite params pk.pkSeed pk.pkRoot rand layer g root [sig]
    let tail ← verifiedProductionLayerMessages suite params pk (layer + 1)
      (g / 2 ^ params.subtreeHeight) [] next rest
    pure (⟨⟨layer, g / 2 ^ params.subtreeHeight, g % 2 ^ params.subtreeHeight⟩,
      ⟨root, sig.tswCtr⟩, sig⟩ :: tail)

theorem verifiedProductionLayerMessages_complete (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (sigs : List LayerXmssSig) :
    ∀ layer g rand root top,
      verifyProductionHypertreeLayers suite params pk.pkSeed pk.pkRoot rand layer g root sigs = some top →
      ∃ entries, verifiedProductionLayerMessages suite params pk layer g rand root sigs = some entries ∧
        entries.map (fun e => e.key.layer) = List.range' layer sigs.length := by
  induction sigs with
  | nil => intro layer g rand root top _; exact ⟨[], rfl, rfl⟩
  | cons sig rest ih =>
    intro layer g rand root top h
    obtain ⟨mid, hm, ht⟩ := (verifyProductionHypertreeLayers_split suite params pk.pkSeed pk.pkRoot
      rand layer g root sig rest top).mp h
    rw [verifyProductionHypertreeLayers_upper_rand_irrel suite params pk.pkSeed pk.pkRoot rand rest
      (layer + 1) (g / 2 ^ params.subtreeHeight) mid (by omega)] at ht
    obtain ⟨entries, he, hl⟩ := ih _ _ _ _ _ ht
    refine ⟨⟨⟨layer, g / 2 ^ params.subtreeHeight, g % 2 ^ params.subtreeHeight⟩,
      ⟨root, sig.tswCtr⟩, sig⟩ :: entries, ?_, ?_⟩
    · simp [verifiedProductionLayerMessages, hm, he]
    · simp [List.range', hl]

theorem verifiedProductionLayerMessages_validCoords (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (sigs : List LayerXmssSig) :
    ∀ layer g rand root entries,
      params.subtreeHeight ≤ 31 →
      layer + sigs.length ≤ 2 ^ 32 →
      g / 2 ^ params.subtreeHeight < 2 ^ 64 →
      verifiedProductionLayerMessages suite params pk layer g rand root sigs = some entries →
      ∀ e ∈ entries, e.key.ValidCoords = true := by
  induction sigs with
  | nil =>
    intro layer g rand root entries _ _ _ h e hm
    simp [verifiedProductionLayerMessages] at h
    subst entries; cases hm
  | cons sig rest ih =>
    intro layer g rand root entries hSub hLay hTree h e hm
    simp only [verifiedProductionLayerMessages, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨next, _, tail, hTail, rfl⟩ := h
    rcases List.mem_cons.mp hm with rfl | hMem
    · simp only [OtsPosition.ValidCoords, Bool.and_eq_true, decide_eq_true_eq]
      have hLayerLt : layer < 2 ^ 32 := by simp at hLay; omega
      have hPowLe : 2 ^ params.subtreeHeight ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) hSub
      have hModLt : g % 2 ^ params.subtreeHeight < 2 ^ params.subtreeHeight :=
        Nat.mod_lt _ (Nat.two_pow_pos _)
      have h31Lt32 : (2 : Nat) ^ 31 < 2 ^ 32 := by decide
      exact ⟨⟨hLayerLt, hTree⟩, by omega⟩
    · exact ih (layer + 1) (g / 2 ^ params.subtreeHeight) [] next tail hSub
        (by simp at hLay; omega)
        (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hTree) hTail e hMem

/-- Production transactional upper-layer release gate built directly on `verifyProductionPqHashSig`
    and `verifiedProductionLayerMessages`. -/
def verifyProductionBeforeReleaseAll (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (cache : List LayerRelease) (turn : FaultedSignTurn) :
    Option (List LayerRelease) := do
  if !verifyProductionPqHashSig suite params pk turn.msg turn.candidate then none else do
    let (rand, root) ← productionHypertreeStart suite params pk turn.msg turn.candidate
    let entries ← verifiedProductionLayerMessages suite params pk 0 turn.candidate.leafGlobalIdx
      rand root turn.candidate.layerSigs
    if AdrsCacheConsistent (cache ++ entries.drop 1) then some (entries.drop 1) else none

def guardedProductionSignTraceAll (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) : List LayerRelease → List FaultedSignTurn → List LayerRelease
  | cache, [] => cache
  | cache, turn :: rest =>
    match verifyProductionBeforeReleaseAll suite params pk cache turn with
    | none => guardedProductionSignTraceAll suite params pk cache rest
    | some entries => guardedProductionSignTraceAll suite params pk (cache ++ entries) rest

/-- Unconditional completeness on the empty journal for every production-valid signature. -/
theorem production_gate_complete (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (turn : FaultedSignTurn)
    (hv : verifyProductionPqHashSig suite params pk turn.msg turn.candidate = true) :
    ∃ es, verifyProductionBeforeReleaseAll suite params pk [] turn = some es ∧
      es.map (fun e => e.key.layer) = List.range' 1 (params.numLayers - 1) := by
  obtain ⟨hGate, hlen, rand, root, hs, ht⟩ :=
    verifyProductionPqHashSig_layers suite params pk turn.msg turn.candidate hv
  obtain ⟨es, he, hl⟩ := verifiedProductionLayerMessages_complete suite params pk _ _ _ _ _ _ ht
  have hd : (es.drop 1).map (fun e => e.key.layer) =
      List.range' 1 (params.numLayers - 1) := by
    rw [List.map_drop, hl, hlen, List.drop_range']
  have hGateFacts : params.subtreeHeight ≤ 31 ∧ params.numLayers ≤ 2 ^ 32 ∧
      turn.candidate.leafGlobalIdx / 2 ^ params.subtreeHeight < 2 ^ 64 := by
    simp only [AdrsGateValid, Bool.and_eq_true, decide_eq_true_eq] at hGate
    exact ⟨hGate.1.1.2, hGate.1.2, hGate.2⟩
  have hValAll := verifiedProductionLayerMessages_validCoords suite params pk turn.candidate.layerSigs
    0 turn.candidate.leafGlobalIdx rand root es hGateFacts.1 (by omega) hGateFacts.2.2 he
  have hc := adrsCacheConsistent_of_distinct_valid_layers (es.drop 1)
    (fun e hm => hValAll e (List.mem_of_mem_drop hm))
    (by rw [hd]; exact layer_range_nodup _ _)
  refine ⟨es.drop 1, ?_, hd⟩
  simpa [verifyProductionBeforeReleaseAll, hv, hs, he] using hc

/-- Production opening anchor using `verifyProductionHypertreeLayers` (`TAG_H_INTERNAL` upper layers). -/
def ProductionOpeningBound (suite : TweakableHashSuite) (params : PqHashParams) (pk : PqPublicKey)
    (journal : List LayerRelease) (e : LayerRelease) : Prop :=
  e.signed.tswCtr = e.opening.tswCtr ∧
  ∃ top, verifyProductionHypertreeLayers suite params pk.pkSeed pk.pkRoot [] e.key.layer
    (openingGlobalIdx params e.key) e.signed.root [e.opening] = some top ∧
    (if e.key.layer + 1 = params.numLayers then top = pk.pkRoot
     else ∃ next ∈ journal, next.key = nextOtsPosition params e.key ∧ top = next.signed.root)

theorem productionOpeningBound_mono (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (xs ys : List LayerRelease) (e : LayerRelease)
    (hsub : ∀ x ∈ xs, x ∈ ys) (h : ProductionOpeningBound suite params pk xs e) :
    ProductionOpeningBound suite params pk ys e := by
  obtain ⟨hc, top, hv, ht⟩ := h
  refine ⟨hc, top, hv, ?_⟩
  by_cases hl : e.key.layer + 1 = params.numLayers
  · simpa only [hl, ↓reduceIte] using ht
  · simp only [hl, ↓reduceIte] at ht ⊢
    obtain ⟨n, hn, hk, hr⟩ := ht
    exact ⟨n, hsub n hn, hk, hr⟩

theorem verifiedProductionLayerMessages_openingBound (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (sigs : List LayerXmssSig) :
    ∀ layer g root es journal,
      layer + sigs.length = params.numLayers →
      verifiedProductionLayerMessages suite params pk layer g [] root sigs = some es →
      verifyProductionHypertreeLayers suite params pk.pkSeed pk.pkRoot [] layer g root sigs = some pk.pkRoot →
      (∀ e ∈ es, e ∈ journal) →
      ∀ e ∈ es, ProductionOpeningBound suite params pk journal e := by
  induction sigs with
  | nil =>
    intro layer g root es journal _ he _ _ e hm
    simp only [verifiedProductionLayerMessages, Option.some.injEq] at he
    subst es; cases hm
  | cons sig rest ih =>
    intro layer g root es journal hlen he hv hsub e hm
    obtain ⟨mid, hs, ht⟩ := (verifyProductionHypertreeLayers_split suite params pk.pkSeed pk.pkRoot
      [] layer g root sig rest pk.pkRoot).mp hv
    simp only [verifiedProductionLayerMessages, hs, Option.bind_some, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at he
    obtain ⟨tail, htail, rfl⟩ := he
    rcases List.mem_cons.mp hm with rfl | hm
    · refine ⟨rfl, mid, ?_, ?_⟩
      · change verifyProductionHypertreeLayers suite params pk.pkSeed pk.pkRoot [] layer
          (g / 2 ^ params.subtreeHeight * 2 ^ params.subtreeHeight + g % 2 ^ params.subtreeHeight)
          root [sig] = some mid
        rw [Nat.div_add_mod']
        exact hs
      · dsimp only
        by_cases hlast : layer + 1 = params.numLayers
        · rw [ite_eq_left hlast]
          have hn : rest.length = 0 := by simp only [List.length_cons] at hlen; omega
          have hr : rest = [] := List.length_eq_zero_iff.mp hn
          subst rest
          simpa only [verifyProductionHypertreeLayers_nil, Option.some.injEq] using ht
        · rw [ite_eq_right hlast]
          cases rest with
          | nil => simp at hlen; exact False.elim (hlast hlen)
          | cons next rest =>
            simp only [verifiedProductionLayerMessages, Option.bind_eq_bind, Option.bind_eq_some_iff,
              Option.pure_def, Option.some.injEq] at htail
            obtain ⟨mid', _, tail', _, rfl⟩ := htail
            exact ⟨_, hsub _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl, rfl⟩
    · exact ih (layer + 1) (g / 2 ^ params.subtreeHeight) mid tail journal
        (by simp only [List.length_cons] at hlen; omega) htail ht
        (fun x hx => hsub x (List.mem_cons_of_mem _ hx)) e hm

theorem verifyProductionBeforeReleaseAll_props (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (cache es : List LayerRelease) (turn : FaultedSignTurn)
    (h : verifyProductionBeforeReleaseAll suite params pk cache turn = some es) :
    AdrsCacheConsistent (cache ++ es) ∧
    (∀ e ∈ es, e.key.ValidCoords = true) ∧
    (∀ e ∈ es, ProductionOpeningBound suite params pk (cache ++ es) e) := by
  unfold verifyProductionBeforeReleaseAll at h
  split at h
  · cases h
  · next hvNeg =>
    have hv : verifyProductionPqHashSig suite params pk turn.msg turn.candidate = true := by
      cases hx : verifyProductionPqHashSig suite params pk turn.msg turn.candidate <;> simp_all
    obtain ⟨hGate, hlen, rand, root, hs, ht⟩ :=
      verifyProductionPqHashSig_layers suite params pk turn.msg turn.candidate hv
    simp only [hs, Option.bind_eq_bind, Option.bind_some] at h
    have hGateFacts : params.subtreeHeight ≤ 31 ∧ params.numLayers ≤ 2 ^ 32 ∧
        turn.candidate.leafGlobalIdx / 2 ^ params.subtreeHeight < 2 ^ 64 := by
      simp only [AdrsGateValid, Bool.and_eq_true, decide_eq_true_eq] at hGate
      exact ⟨hGate.1.1.2, hGate.1.2, hGate.2⟩
    cases hsig : turn.candidate.layerSigs with
    | nil =>
      simp only [hsig, verifiedProductionLayerMessages, Option.bind_some, List.drop_nil] at h
      split at h
      · next hc =>
        cases h
        simp only [List.append_nil] at hc
        refine ⟨?_, ?_, ?_⟩
        · simpa using hc
        · intro e he; cases he
        · intro e he; cases he
      · cases h
    | cons sig rest =>
      rw [hsig] at ht hlen h
      obtain ⟨mid, hm, hu⟩ := (verifyProductionHypertreeLayers_split suite params pk.pkSeed pk.pkRoot
        rand 0 turn.candidate.leafGlobalIdx root sig rest pk.pkRoot).mp ht
      rw [verifyProductionHypertreeLayers_upper_rand_irrel suite params pk.pkSeed pk.pkRoot rand rest
        1 (turn.candidate.leafGlobalIdx / 2 ^ params.subtreeHeight) mid (by decide)] at hu
      simp only [verifiedProductionLayerMessages, hm, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨all, ⟨tail, he, rfl⟩, h⟩ := h
      simp only [List.drop_succ_cons, List.drop_zero] at h
      split at h
      · next hc =>
        cases h
        have hValTail := verifiedProductionLayerMessages_validCoords suite params pk rest
          1 (turn.candidate.leafGlobalIdx / 2 ^ params.subtreeHeight) [] mid es
          hGateFacts.1 (by simp only [List.length_cons] at hlen; omega)
          (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hGateFacts.2.2) he
        have hBoundTail := verifiedProductionLayerMessages_openingBound suite params pk rest
          1 (turn.candidate.leafGlobalIdx / 2 ^ params.subtreeHeight) mid es (cache ++ es)
          (by simpa [Nat.add_comm] using hlen) he hu
          (fun x hx => List.mem_append.mpr (Or.inr hx))
        exact ⟨hc, hValTail, hBoundTail⟩
      · cases h

theorem production_bound_cached_openings_unique_or_collision (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (journal : List LayerRelease)
    (hc : AdrsCacheConsistent journal)
    (hVal : ∀ e ∈ journal, e.key.ValidCoords = true)
    (valid : ∀ e ∈ journal, ProductionOpeningBound suite params pk journal e)
    (a b : LayerRelease) (ha : a ∈ journal) (hb : b ∈ journal)
    (hkEnc : a.key.toEncodedAdrs = b.key.toEncodedAdrs) :
    a.key = b.key ∧ a.signed = b.signed ∧ (a.opening = b.opening ∨ Collision suite.rawHash) := by
  have hk : a.key = b.key := (otsPosition_toEncodedAdrs_injective (hVal a ha) (hVal b hb)).mp hkEnc
  have hm := hc a ha b hb hkEnc
  refine ⟨hk, hm, ?_⟩
  have hcNat := adrsCacheConsistent_implies_cacheConsistent hc
  obtain ⟨hca, topa, hva, hta⟩ := valid a ha
  obtain ⟨hcb, topb, hvb, htb⟩ := valid b hb
  have ht : topa = topb := by
    rw [← hk] at htb
    by_cases hl : a.key.layer + 1 = params.numLayers
    · simp only [hl, ↓reduceIte] at hta htb
      exact hta.trans htb.symm
    · simp only [hl, ↓reduceIte] at hta htb
      obtain ⟨na, hna, hka, hra⟩ := hta
      obtain ⟨nb, hnb, hkb, hrb⟩ := htb
      have hn := hcNat na hna nb hnb (hka.trans hkb.symm)
      exact hra.trans ((congrArg OtsMessage.root hn).trans hrb.symm)
  have hctr : a.opening.tswCtr = b.opening.tswCtr := by rw [← hca, ← hcb, hm]
  obtain ⟨digitsA, hDigA, hla, hwa⟩ := verifyProductionHypertreeLayers_single suite params
    pk.pkSeed pk.pkRoot [] a.key.layer (openingGlobalIdx params a.key) a.signed.root a.opening topa hva
  obtain ⟨digitsB, hDigB, hlb, hwb⟩ := verifyProductionHypertreeLayers_single suite params
    pk.pkSeed pk.pkRoot [] b.key.layer (openingGlobalIdx params b.key) b.signed.root b.opening topb hvb
  rw [← hk, ← hm, ← hctr] at hDigB
  rw [← hk, ← ht] at hwb
  have hDigEq : digitsA = digitsB := Option.some.inj (hDigA.symm.trans hDigB)
  rw [← hDigEq] at hwb
  rcases wots_openings_unique_or_collision suite params pk.pkSeed _ _ _ _ _ _ _ _ _
    hla hlb hwa hwb with ⟨hchains, hpath⟩ | hcol
  · left
    cases ha' : a.opening
    cases hb' : b.opening
    rw [ha', hb'] at hctr hchains hpath
    simp only at hctr hchains hpath
    rw [hctr, hchains, hpath]
  · exact Or.inr hcol

/-! ### 9B. Key-Scoped Crash-Recoverable Persistent Upper-Layer Journal -/

/-- Persistent signer state separating durable `fsync`ed journal storage (`diskJournal`) from
    in-memory `volatileCache`, plus the audit trace `emittedEntries` of all upper-layer openings
    ever released to the network. -/
structure DurableUpperJournalState where
  diskJournal : List LayerRelease
  volatileCache : List LayerRelease
  emittedEntries : List LayerRelease

def DurableUpperJournalState.init : DurableUpperJournalState :=
  { diskJournal := [], volatileCache := [], emittedEntries := [] }

/-- Multi-crash operational event schedule: normal persisted signing, disk-commit failure before
    signature emission, and mid-session power loss + reboot recovery from `diskJournal`. -/
inductive RecoverableGateEvent where
  | signAndPersistOk (turn : FaultedSignTurn)
  | signDiskWriteFail (turn : FaultedSignTurn)
  | persistThenCrash (turn : FaultedSignTurn)
  | powerLossAndRecover

/-- Transactional step: a candidate signature is emitted (`some sig`) **only** when
    `verifyProductionBeforeReleaseAll` succeeds AND its upper-layer entries commit to `diskJournal`.
    If disk persistence fails, `none` is returned and `volatileCache` remains synced to `diskJournal`.
    On crash/reboot, `volatileCache` is reloaded from `diskJournal`. -/
def stepRecoverableProductionGate (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (st : DurableUpperJournalState) (ev : RecoverableGateEvent) :
    DurableUpperJournalState × Option PqHashSig :=
  match ev with
  | .signAndPersistOk turn =>
    match verifyProductionBeforeReleaseAll suite params pk st.volatileCache turn with
    | none => (st, none)
    | some es =>
      let committed := st.diskJournal ++ es
      ({ diskJournal := committed
         volatileCache := committed
         emittedEntries := st.emittedEntries ++ es },
       some turn.candidate)
  | .persistThenCrash turn =>
    match verifyProductionBeforeReleaseAll suite params pk st.diskJournal turn with
    | none => ({ st with volatileCache := st.diskJournal }, none)
    | some es =>
      ({ diskJournal := st.diskJournal ++ es
         volatileCache := st.diskJournal ++ es
         emittedEntries := st.emittedEntries }, none)
  | .signDiskWriteFail _ =>
    ({ st with volatileCache := st.diskJournal }, none)
  | .powerLossAndRecover =>
    ({ st with volatileCache := st.diskJournal }, none)

def runRecoverableProductionSchedule (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) : DurableUpperJournalState → List RecoverableGateEvent → DurableUpperJournalState
  | st, [] => st
  | st, ev :: rest =>
    runRecoverableProductionSchedule suite params pk
      (stepRecoverableProductionGate suite params pk st ev).1 rest

def DurableJournalInv (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (st : DurableUpperJournalState) : Prop :=
  st.volatileCache = st.diskJournal ∧
  (∀ e ∈ st.emittedEntries, e ∈ st.diskJournal) ∧
  AdrsCacheConsistent st.diskJournal ∧
  (∀ e ∈ st.diskJournal, e.key.ValidCoords = true) ∧
  (∀ e ∈ st.diskJournal, ProductionOpeningBound suite params pk st.diskJournal e)

theorem stepRecoverableProductionGate_preserves_inv (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (st : DurableUpperJournalState)
    (ev : RecoverableGateEvent) (hInv : DurableJournalInv suite params pk st) :
    DurableJournalInv suite params pk (stepRecoverableProductionGate suite params pk st ev).1 := by
  obtain ⟨hVol, hEmit, hCons, hVal, hBound⟩ := hInv
  cases ev with
  | signAndPersistOk turn =>
    simp only [stepRecoverableProductionGate]
    cases hVer : verifyProductionBeforeReleaseAll suite params pk st.volatileCache turn with
    | none => simpa only [hVer] using (show DurableJournalInv suite params pk st from ⟨hVol, hEmit, hCons, hVal, hBound⟩)
    | some es =>
      dsimp only
      change DurableJournalInv suite params pk { diskJournal := st.diskJournal ++ es, volatileCache := st.diskJournal ++ es, emittedEntries := st.emittedEntries ++ es }
      rw [hVol] at hVer
      obtain ⟨hCons', hValEs, hBoundEs⟩ :=
        verifyProductionBeforeReleaseAll_props suite params pk st.diskJournal es turn hVer
      refine ⟨rfl, ?_, hCons', ?_, ?_⟩
      · intro e he
        rcases List.mem_append.mp he with ho | hn
        · exact List.mem_append_left _ (hEmit e ho)
        · exact List.mem_append_right _ hn
      · intro e hm
        rcases List.mem_append.mp hm with hOld | hNew
        · exact hVal e hOld
        · exact hValEs e hNew
      · intro e hm
        rcases List.mem_append.mp hm with hOld | hNew
        · exact productionOpeningBound_mono suite params pk st.diskJournal (st.diskJournal ++ es) e
            (fun x hx => List.mem_append.mpr (Or.inl hx)) (hBound e hOld)
        · exact hBoundEs e hNew
  | persistThenCrash turn =>
    simp only [stepRecoverableProductionGate]
    cases hv : verifyProductionBeforeReleaseAll suite params pk st.diskJournal turn with
    | none => exact ⟨rfl, hEmit, hCons, hVal, hBound⟩
    | some es =>
      obtain ⟨hc, hvEs, hbEs⟩ := verifyProductionBeforeReleaseAll_props suite params pk st.diskJournal es turn hv
      refine ⟨rfl, fun e he => List.mem_append_left _ (hEmit e he), hc, ?_, ?_⟩
      · intro e he
        rcases List.mem_append.mp he with ho | hn
        · exact hVal e ho
        · exact hvEs e hn
      · intro e he
        rcases List.mem_append.mp he with ho | hn
        · exact productionOpeningBound_mono suite params pk _ _ e
            (fun x hx => List.mem_append_left _ hx) (hBound e ho)
        · exact hbEs e hn
  | signDiskWriteFail _ =>
    exact ⟨rfl, hEmit, hCons, hVal, hBound⟩
  | powerLossAndRecover =>
    exact ⟨rfl, hEmit, hCons, hVal, hBound⟩

theorem runRecoverableProductionSchedule_preserves_inv (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (evs : List RecoverableGateEvent) :
    ∀ st, DurableJournalInv suite params pk st →
      DurableJournalInv suite params pk (runRecoverableProductionSchedule suite params pk st evs) := by
  induction evs with
  | nil => intro st h; exact h
  | cons ev rest ih =>
    intro st h
    exact ih _ (stepRecoverableProductionGate_preserves_inv suite params pk st ev h)

/-- **Multi-Crash Production Upper-Layer Non-Reuse (`recoverable_production_journal_prevents_upper_wots_reuse_across_crashes`)**:
    Across arbitrary interleavings of faulted signing attempts, failed disk writes, and power-loss
    crashes/reboots, any two upper-layer openings ever emitted by `stepRecoverableProductionGate`
    at the same 32-byte encoded `HashAdrs` have identical `(layer, treeIdx, leafIdx)`, identical
    signed `(root, tswCtr)`, and identical openings unless a `suite.rawHash` collision is exhibited. -/
theorem recoverable_production_journal_prevents_upper_wots_reuse_across_crashes
    (suite : TweakableHashSuite) (params : PqHashParams) (pk : PqPublicKey)
    (evs : List RecoverableGateEvent) (a b : LayerRelease)
    (ha : a ∈ (runRecoverableProductionSchedule suite params pk .init evs).emittedEntries)
    (hb : b ∈ (runRecoverableProductionSchedule suite params pk .init evs).emittedEntries)
    (hk : a.key.toEncodedAdrs = b.key.toEncodedAdrs) :
    a.key = b.key ∧ a.signed = b.signed ∧ (a.opening = b.opening ∨ Collision suite.rawHash) := by
  have hInit : DurableJournalInv suite params pk .init :=
    ⟨rfl, by simp [DurableUpperJournalState.init], by simp [AdrsCacheConsistent, DurableUpperJournalState.init],
     by simp [DurableUpperJournalState.init], by simp [DurableUpperJournalState.init]⟩
  obtain ⟨_, hEmit, hCons, hVal, hBound⟩ :=
    runRecoverableProductionSchedule_preserves_inv suite params pk evs .init hInit
  exact production_bound_cached_openings_unique_or_collision suite params pk _
    hCons hVal hBound a b (hEmit a ha) (hEmit b hb) hk

/-- Uninterrupted single-session corollary on `guardedProductionSignTraceAll`. -/
theorem production_verify_before_release_adrs_unique_or_collision
    (suite : TweakableHashSuite) (params : PqHashParams) (pk : PqPublicKey)
    (turns : List FaultedSignTurn) (a b : LayerRelease)
    (ha : a ∈ guardedProductionSignTraceAll suite params pk [] turns)
    (hb : b ∈ guardedProductionSignTraceAll suite params pk [] turns)
    (hk : a.key.toEncodedAdrs = b.key.toEncodedAdrs) :
    a.key = b.key ∧ a.signed = b.signed ∧ (a.opening = b.opening ∨ Collision suite.rawHash) := by
  have hEquiv : ∀ (turns' : List FaultedSignTurn) (st : DurableUpperJournalState),
      st.volatileCache = st.diskJournal →
      guardedProductionSignTraceAll suite params pk st.diskJournal turns' =
        (runRecoverableProductionSchedule suite params pk st
          (turns'.map RecoverableGateEvent.signAndPersistOk)).diskJournal := by
    intro turns'
    induction turns' with
    | nil => intro st _; rfl
    | cons t rest ih =>
      intro st hVol
      simp only [List.map_cons, guardedProductionSignTraceAll, runRecoverableProductionSchedule,
        stepRecoverableProductionGate, hVol]
      cases verifyProductionBeforeReleaseAll suite params pk st.diskJournal t with
      | none => exact ih st hVol
      | some es => exact ih { diskJournal := st.diskJournal ++ es, volatileCache := st.diskJournal ++ es, emittedEntries := st.emittedEntries ++ es } rfl
  have hInit := hEquiv turns .init rfl
  change guardedProductionSignTraceAll suite params pk [] turns = _ at hInit
  rw [hInit] at ha hb
  have hInv := runRecoverableProductionSchedule_preserves_inv suite params pk
    (turns.map RecoverableGateEvent.signAndPersistOk) .init
    ⟨rfl, by simp [DurableUpperJournalState.init], by simp [AdrsCacheConsistent, DurableUpperJournalState.init],
     by simp [DurableUpperJournalState.init], by simp [DurableUpperJournalState.init]⟩
  exact production_bound_cached_openings_unique_or_collision suite params pk _
    hInv.2.2.1 hInv.2.2.2.1 hInv.2.2.2.2 a b ha hb hk

/-- **`#tooth` Witness (`tooth_volatile_only_cache_forgets_across_crash_allows_reuse`)**:
    A broken crash model that wipes `volatileCache` to `[]` on reboot instead of reloading a
    durable `diskJournal` permits two distinct `(root, tswCtr)` releases (`⟨[], 0⟩ ≠ ⟨[], 1⟩`)
    at the identical encoded `HashAdrs` `⟨1, 0, 0⟩.toEncodedAdrs` across a reboot. -/
theorem tooth_volatile_only_cache_forgets_across_crash_allows_reuse :
    let e0 : LayerRelease := ⟨⟨1, 0, 0⟩, ⟨[], 0⟩, counterToothOpening 0⟩
    let e1 : LayerRelease := ⟨⟨1, 0, 0⟩, ⟨[], 1⟩, counterToothOpening 1⟩
    AdrsCacheConsistent ([] ++ [e0]) ∧
    ¬ AdrsCacheConsistent ([e0] ++ [e1]) ∧
    AdrsCacheConsistent ([] ++ [e1]) ∧
    e0.key.toEncodedAdrs = e1.key.toEncodedAdrs ∧
    e0.signed ≠ e1.signed := by
  refine ⟨?_, ?_, ?_, rfl, ?_⟩
  · simp [AdrsCacheConsistent]
  · intro h
    have he := h ⟨⟨1, 0, 0⟩, ⟨[], 0⟩, counterToothOpening 0⟩ (by simp)
      ⟨⟨1, 0, 0⟩, ⟨[], 1⟩, counterToothOpening 1⟩ (by simp) rfl
    cases congrArg OtsMessage.tswCtr he
  · simp [AdrsCacheConsistent]
  · intro h; cases congrArg OtsMessage.tswCtr h

/-- Canonical framed upper-journal payload. Counters use unbounded canonical
LEB128, so malformed/truncated fixed-width coordinates cannot alias here. -/
def upperJournalPayload (keyId : List UInt8) (generation : Nat)
    (entries : List LayerRelease) : List UInt8 :=
  encodeMultiFrame [keyId, leb128 generation, encodeMultiFrame (entries.map (fun e =>
    encodeMultiFrame [e.key.toEncodedAdrs, e.signed.root, leb128 e.signed.tswCtr,
      leb128 e.opening.tswCtr, encodeMultiFrame e.opening.wotsChains,
      encodeMultiFrame e.opening.authPath]))]

def upperJournalTag (key identity keyId : List UInt8) (generation : Nat)
    (entries : List LayerRelease) : List UInt8 :=
  RustDurability.keyedMac "QSAG.UPPER.JOURNAL.MAC/v1".toUTF8.data.toList key
    (encodeMultiFrame [identity, upperJournalPayload keyId generation entries])

/-- A decoded candidate is accepted only after exact byte re-encoding, lock identity,
MAC and independent rollback-floor checks. Decoder failure is represented by `none`. -/
structure UpperJournalCandidate where
  generation : Nat
  entries : List LayerRelease
  identity : List UInt8
  body : List UInt8
  tag : List UInt8

structure AuthenticatedUpperJournal where
  keyId : List UInt8
  macKey : List UInt8
  lock : RustDurability.LockedIdentityHandle
  anchor : ExternalMonotoneAnchor
  runtime : DurableUpperJournalState
  generation : Nat
  poisoned : Bool := false

def recoverAuthenticatedUpperJournal (st : AuthenticatedUpperJournal)
    (candidate : Option UpperJournalCandidate) : Option AuthenticatedUpperJournal := do
  let c ← candidate
  if st.poisoned || !(RustDurability.verifyLockIdentity st.lock c.identity).2 then none else
  if c.body ≠ upperJournalPayload st.keyId c.generation c.entries ∨
      c.tag ≠ upperJournalTag st.macKey c.identity st.keyId c.generation c.entries ∨
      verifyAgainstExternalAnchor st.anchor c.generation c.tag ≠ true then none else
    some { st with generation := c.generation, runtime := { st.runtime with diskJournal := c.entries, volatileCache := c.entries } }

/-- Storage errors poison the live handle. A completed persistence barrier updates
both the authenticated snapshot generation and retained checkpoint before emission.
`persistThenCrash` commits exactly the same bytes without releasing a signature. -/
def stepAuthenticatedUpperJournal (suite : TweakableHashSuite) (params : PqHashParams)
    (pk : PqPublicKey) (st : AuthenticatedUpperJournal) (ev : RecoverableGateEvent)
    (syncSucceeded : Bool) : AuthenticatedUpperJournal × Option PqHashSig :=
  if st.poisoned then (st, none) else
  if !syncSucceeded then ({ st with poisoned := true }, none) else
    let result := stepRecoverableProductionGate suite params pk st.runtime ev
    let generation := st.generation + 1
    let identity := RustDurability.lockIdentitySeal st.lock.device st.lock.inode st.lock.nonce
    let tag := upperJournalTag st.macKey identity st.keyId generation result.1.diskJournal
    ({ st with runtime := result.1, generation := generation, anchor := ⟨generation, tag⟩ }, result.2)

theorem authenticated_upper_storage_failure_no_release (suite : TweakableHashSuite)
    (params : PqHashParams) (pk : PqPublicKey) (st : AuthenticatedUpperJournal)
    (ev : RecoverableGateEvent) :
    (stepAuthenticatedUpperJournal suite params pk st ev false).2 = none := by
  cases hp : st.poisoned <;> simp [stepAuthenticatedUpperJournal, hp]

theorem authenticated_upper_recovery_checks_anchor (st next : AuthenticatedUpperJournal)
    (c : UpperJournalCandidate)
    (h : recoverAuthenticatedUpperJournal st (some c) = some next) :
    verifyAgainstExternalAnchor st.anchor c.generation c.tag = true ∧
    c.body = upperJournalPayload st.keyId c.generation c.entries ∧
    c.tag = upperJournalTag st.macKey c.identity st.keyId c.generation c.entries := by
  simp only [recoverAuthenticatedUpperJournal, Option.bind_eq_bind, Option.bind_some] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i good
      simp only [not_or, Decidable.not_not] at good
      exact ⟨good.2.2, good.1, good.2.1⟩

#verify_inhabited pubLoop_speculative_ni publicPointerLoop_invariant
#tooth_pair recoverable_production_journal_prevents_upper_wots_reuse_across_crashes vs
  tooth_volatile_only_cache_forgets_across_crash_allows_reuse

end Qsag.FaultAndSpeculativeSafety

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut failures : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "Qsag.FaultAndSpeculativeSafety." ||
        name.toString.startsWith "_private.Qsag.FaultAndSpeculativeSafety." then
      checked := checked + 1
      let axioms ← Lean.collectAxioms name
      let rejected := axioms.filter fun ax => ax != ``propext && ax != ``Quot.sound
      unless rejected.isEmpty do
        failures := failures + 1
        logInfo m!"Rejected axioms in {name}: {rejected}"
  if failures > 0 then throwError "Axiom audit rejected {failures} declarations"
  if checked == 0 then throwError "Empty fault/speculation axiom audit"
  logInfo m!"Fault/speculation axiom audit: {checked} declarations, 0 rejected axioms"
