module
/-
# Qsag.Spec.Assumptions — Explicit Cryptographic, Oracle-Model, and Platform Locales

Explicit `CryptHOL`-style assumption records (`structure`s, zero `axiom` declarations, zero bare
existential `Prop` breaks) documenting every cryptographic hardness premise, idealized oracle
model, and operating-system / hardware platform contract referenced by top-level security theorems.
-/

public import Qsag.Spec.Primitives
public import Qsag.Spec.Refines
public import Qsag.Spec.GameBound
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Spec

set_option autoImplicit false

/-! ## 1. Constructive Hash-Break Witness Types (`Type`, Zero Bare Existential `Prop`) -/

/-- Constructive collision witness for a byte-to-byte hash function `H`. -/
structure HashCollision (H : Bytes → Bytes) where
  m₁ : Bytes
  m₂ : Bytes
  distinct : m₁ ≠ m₂
  collides : H m₁ = H m₂

/-- Constructive second-preimage witness against a fixed `target` input under `H`. -/
structure SecondPreimage (H : Bytes → Bytes) (target : Bytes) where
  candidate : Bytes
  distinct : candidate ≠ target
  sameDigest : H candidate = H target

/-- Any `SecondPreimage H target` immediately furnishes a `HashCollision H`. -/
@[expose] def SecondPreimage.toCollision {H : Bytes → Bytes} {target : Bytes}
    (w : SecondPreimage H target) : HashCollision H where
  m₁ := w.candidate
  m₂ := target
  distinct := w.distinct
  collides := w.sameDigest

theorem SecondPreimage.toCollision_collides {H : Bytes → Bytes} {target : Bytes}
    (w : SecondPreimage H target) :
    H w.toCollision.m₁ = H w.toCollision.m₂ ∧ w.toCollision.m₁ ≠ w.toCollision.m₂ :=
  ⟨w.toCollision.collides, w.toCollision.distinct⟩

/-- Prefix-free codec collision extractor: if `H (c.encode x)` collides on distinct inputs `x ≠ y`,
    we constructively obtain a concrete `HashCollision H` (`0 Classical.choice`). -/
def FramedCodec.collisionOfDigestEq {α : Type} [DecidableEq α]
    (c : FramedCodec α) (H : Bytes → Bytes) {x y : α}
    (hDigest : H (c.encode x) = H (c.encode y)) :
    PSum (x = y) (HashCollision H) :=
  match decEq x y with
  | .isTrue hEq => .inl hEq
  | .isFalse hNe =>
    .inr
      { m₁ := c.encode x
        m₂ := c.encode y
        distinct := fun hEnc => hNe (c.encode_injective hEnc)
        collides := hDigest }

theorem FramedCodec.collisionOfDigestEq_sound {α : Type} [DecidableEq α]
    (c : FramedCodec α) (H : Bytes → Bytes) {x y : α}
    (hDigest : H (c.encode x) = H (c.encode y)) :
    match c.collisionOfDigestEq H hDigest with
    | .inl _ => x = y
    | .inr col => x ≠ y ∧ H col.m₁ = H col.m₂ ∧ col.m₁ ≠ col.m₂ := by
  unfold FramedCodec.collisionOfDigestEq
  cases decEq x y with
  | isTrue hEq => exact hEq
  | isFalse hNe => exact ⟨hNe, hDigest, fun hEnc => hNe (c.encode_injective hEnc)⟩

/-! ## 2. Standard-Model Tweakable-Hash, PRF, and Lattice Assumption Locales -/

/-- Multi-target, distinct-tweak target-collision resistance (`SM-DT-TCR`) assumption locale
    for a tweakable hash family at query budget `qSign` and advantage bound `εTcr`. -/
structure SmDtTcrAssumption (n : Nat) where
  qSign : Nat
  εTcr : RatBound
  tcrGame : FinGame n
  bound : GameBound tcrGame.winProb εTcr

/-- Multi-target, distinct-tweak preimage resistance (`SM-DT-PRE`) assumption locale. -/
structure SmDtPreAssumption (n : Nat) where
  qSign : Nat
  εPre : RatBound
  preGame : FinGame n
  bound : GameBound preGame.winProb εPre

/-- Interleaved target subset resilience (`ITSR`) assumption locale for FORS / TSW message hashing. -/
structure ItsrAssumption (n : Nat) where
  qSign : Nat
  εItsr : RatBound
  itsrGame : FinGame n
  bound : GameBound itsrGame.winProb εItsr

/-- Keyed pseudorandom function (`PRF`) distinguishing assumption locale (used in PRSS & keygen). -/
structure KeyedPrfAssumption (n : Nat) where
  qPrf : Nat
  εPrf : RatBound
  realGame : FinGame n
  idealGame : FinGame n
  bound : GameBound (AdvDist realGame idealGame) εPrf

/-- Decision Ring-LWE / Module-LWE distinguishing assumption locale (`N = 1024, q = 12289` or FIPS-204). -/
structure DecisionRlweAssumption (n : Nat) where
  ringDim : Nat
  modulus : Nat
  εRlwe : RatBound
  rlweReal : FinGame n
  rlweUniform : FinGame n
  bound : GameBound (AdvDist rlweReal rlweUniform) εRlwe

/-- Module-SIS hardness assumption locale parameterized by infinity-norm bound `betaInf`. -/
structure ModuleSisAssumption (n : Nat) where
  ringDim : Nat
  modulus : Nat
  betaInf : Nat
  εSis : RatBound
  sisGame : FinGame n
  bound : GameBound sisGame.winProb εSis

/-- Dual-LPN distinguishing assumption locale for silent VOLE / PCG expansion (`N = 32768`, weight `64`). -/
structure DualLpnAssumption (n : Nat) where
  ambientDim : Nat
  rowWeight : Nat
  εLpn : RatBound
  lpnReal : FinGame n
  lpnUniform : FinGame n
  bound : GameBound (AdvDist lpnReal lpnUniform) εLpn

/-- Composed standard-model hash-signature assumption bundle (`ITSR + SM-DT-TCR + SM-DT-PRE`). -/
structure HashSigAssumptions (n : Nat) where
  itsr : ItsrAssumption n
  tcr : SmDtTcrAssumption n
  pre : SmDtPreAssumption n

/-- Combined rational upper bound `εItsr + εTcr + εPre` for `HashSigAssumptions`. -/
@[expose] def HashSigAssumptions.totalBound {n : Nat} (A : HashSigAssumptions n) : RatBound :=
  (A.itsr.εItsr.add A.tcr.εTcr).add A.pre.εPre

theorem HashSigAssumptions.forger_bound {n : Nat} (A : HashSigAssumptions n)
    (forger : FinGame n)
    (hExtract : ∀ ω : Fin n, forger.win ω = true →
      A.itsr.itsrGame.win ω = true ∨
      A.tcr.tcrGame.win ω = true ∨
      A.pre.preGame.win ω = true) :
    GameBound forger.winProb A.totalBound := by
  let tcrOrPre : FinGame n :=
    { samplePos := A.tcr.tcrGame.samplePos
      win := fun ω => A.tcr.tcrGame.win ω || A.pre.preGame.win ω }
  have h1 : GameBound forger.winProb (A.itsr.itsrGame.winProb.add tcrOrPre.winProb) := by
    apply event_le_two_reductions forger A.itsr.itsrGame tcrOrPre
    intro ω hw
    rcases hExtract ω hw with hI | hT | hP
    · exact .inl hI
    · exact .inr (by dsimp only [tcrOrPre]; rw [hT]; rfl)
    · exact .inr (by dsimp only [tcrOrPre]; rw [hP, Bool.or_true])
  have h2 : GameBound tcrOrPre.winProb (A.tcr.tcrGame.winProb.add A.pre.preGame.winProb) := by
    apply event_le_two_reductions tcrOrPre A.tcr.tcrGame A.pre.preGame
    intro ω hw
    dsimp only [tcrOrPre] at hw
    cases ht : A.tcr.tcrGame.win ω
    · rw [ht, Bool.false_or] at hw
      exact .inr hw
    · exact .inl rfl
  have h2Bound : tcrOrPre.winProb.le (A.tcr.εTcr.add A.pre.εPre) :=
    RatBound.le_trans h2 (RatBound.add_le_add A.tcr.bound A.pre.bound)
  have hTotal : (A.itsr.itsrGame.winProb.add tcrOrPre.winProb).le
      (A.itsr.εItsr.add (A.tcr.εTcr.add A.pre.εPre)) :=
    RatBound.add_le_add A.itsr.bound h2Bound
  have hAssoc : (A.itsr.εItsr.add (A.tcr.εTcr.add A.pre.εPre)).le A.totalBound := by
    unfold HashSigAssumptions.totalBound RatBound.le RatBound.add
    dsimp only
    have hEq :
        (A.itsr.εItsr.num * (A.tcr.εTcr.den * A.pre.εPre.den) +
          (A.tcr.εTcr.num * A.pre.εPre.den + A.pre.εPre.num * A.tcr.εTcr.den) * A.itsr.εItsr.den) *
          (A.itsr.εItsr.den * A.tcr.εTcr.den * A.pre.εPre.den) =
        ((A.itsr.εItsr.num * A.tcr.εTcr.den + A.tcr.εTcr.num * A.itsr.εItsr.den) * A.pre.εPre.den +
          A.pre.εPre.num * (A.itsr.εItsr.den * A.tcr.εTcr.den)) *
          (A.itsr.εItsr.den * (A.tcr.εTcr.den * A.pre.εPre.den)) := by
      have hDen : A.itsr.εItsr.den * A.tcr.εTcr.den * A.pre.εPre.den =
          A.itsr.εItsr.den * (A.tcr.εTcr.den * A.pre.εPre.den) := Nat.mul_assoc _ _ _
      rw [hDen]
      apply congrArg (· * (A.itsr.εItsr.den * (A.tcr.εTcr.den * A.pre.εPre.den)))
      simp only [Nat.left_distrib, Nat.mul_left_comm, Nat.mul_comm, Nat.add_assoc]
    rw [hEq]
    exact Nat.le_refl _
  exact RatBound.le_trans h1 (RatBound.le_trans hTotal hAssoc)

/-! ## 3. Idealized Oracle-Model Locales (ROM / Ideal Permutation / Compressed QROM) -/

/-- Classical lazy random-oracle model locale tracking digest bit-width `digestBits` and
    adversarial query budget `qRo`. -/
structure RandomOracleModel where
  digestBits : Nat
  qRo : Nat
  h_width : 256 ≤ digestBits

/-- Ideal public-permutation / sponge model locale tracking state width `stateBits`,
    capacity `capacityBits`, and permutation query budget `qPerm`. -/
structure IdealPermutationModel where
  stateBits : Nat
  capacityBits : Nat
  qPerm : Nat
  h_cap : 256 ≤ capacityBits ∧ capacityBits ≤ stateBits

/-- Zhandry compressed quantum random-oracle model (`QROM`) locale tracking digest width `digestBits`
    and superposition query budget `qQuantum`. -/
structure CompressedQromModel where
  digestBits : Nat
  qQuantum : Nat
  h_width : 256 ≤ digestBits

/-! ## 4. Operating-System and Hardware Platform Contracts -/

/-- POSIX crash-consistent write-ahead log contract: `fsync` on file + directory after atomic
    `rename` persists committed records across crashes, paired with an external monotone epoch anchor
    preventing whole-snapshot rollback. -/
structure PosixFsyncContract where
  atomicRenameDurable : Bool
  parentDirFsyncDurable : Bool
  externalMonotoneAnchor : Bool
  deriving DecidableEq, Repr

@[expose] def PosixFsyncContract.satisfied (c : PosixFsyncContract) : Prop :=
  c.atomicRenameDurable = true ∧
  c.parentDirFsyncDurable = true ∧
  c.externalMonotoneAnchor = true

/-- Sender-authenticated point-to-point channel contract between threshold custody / MPC peers. -/
structure AuthenticatedChannelContract where
  peerAuthenticated : Bool
  replayProtected : Bool
  deriving DecidableEq, Repr

@[expose] def AuthenticatedChannelContract.satisfied (c : AuthenticatedChannelContract) : Prop :=
  c.peerAuthenticated = true ∧ c.replayProtected = true

/-- Post-quarantine secret-key erasure contract (`ct_memzero` before fault/error return). -/
structure KeyErasureContract where
  quarantineZeroizesShares : Bool
  compilerDeadStoreBarrier : Bool
  deriving DecidableEq, Repr

@[expose] def KeyErasureContract.satisfied (c : KeyErasureContract) : Prop :=
  c.quarantineZeroizesShares = true ∧ c.compilerDeadStoreBarrier = true

/-- Hardware data-independent timing (`DOIT` / `DIT`) contract matching `ExecMode.constantTimeSafe`. -/
structure DitHardwareContract where
  mode : ExecMode
  mode_safe : mode = ExecMode.constantTimeSafe

/-- GPU SIMT workgroup execution contract for SPIR-V batch verification / NTT kernels. -/
structure SimtWorkgroupContract where
  subgroupSize : Nat
  workgroupSize : Nat
  uniformControlFlow : Bool
  disjointStorageBindings : Bool
  h_subgroup_pos : 0 < subgroupSize
  h_divides : subgroupSize ≤ workgroupSize

theorem DitHardwareContract.dit_enabled (c : DitHardwareContract) :
    c.mode.ditEnabled = true ∧ c.mode.cleanSimdUpper = true ∧ c.mode.speculationFence = true := by
  rw [c.mode_safe]
  exact ⟨rfl, rfl, rfl⟩

#verify_constructive
  Qsag.Spec.SecondPreimage.toCollision_collides
  Qsag.Spec.FramedCodec.collisionOfDigestEq_sound
  Qsag.Spec.HashSigAssumptions.forger_bound
  Qsag.Spec.DitHardwareContract.dit_enabled

end Qsag.Spec
end
