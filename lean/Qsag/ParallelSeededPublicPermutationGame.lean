module
/-
# Coherent public-permutation game for the ParallelSeeded chain mode

Uses the repository's exact Gaussian-integer scaled-unitary `QuantumAdv` semantics.
One coherent primitive query has a 257-bit address (direction + 256-bit input),
and XORs the complete 256-bit response into its target register. Direction can be
in superposition: inverse access is not omitted or treated as a secret capability.

The experiment below is conditional on a supplied public permutation. Sampling a
uniform ideal permutation, comparing the fixed deployed SPN with it, and proving
any quantum preimage/collision bound are separate obligations. There is no claim
that independently keyed random permutations model the cSHAKE-derived tweak family.
-/
public import Qsag.ParallelSeededPublicPermutation
import all Qsag.ParallelSeededPublicPermutation
public section
namespace Qsag
set_option autoImplicit false
set_option exponentiation.threshold 512

def publicSpnPack (x : PublicSpnState) : BitVec 256 := x.2 ++ x.1

def publicSpnUnpack (x : BitVec 256) : PublicSpnState :=
  (x.extractLsb' 0 128, x.extractLsb' 128 128)

theorem publicSpnUnpack_pack (x : PublicSpnState) :
    publicSpnUnpack (publicSpnPack x) = x := by
  simp only [publicSpnUnpack, publicSpnPack, BitVec.extractLsb'_append_eq_right,
    BitVec.extractLsb'_append_eq_left]

theorem publicSpnPack_unpack (x : BitVec 256) :
    publicSpnPack (publicSpnUnpack x) = x := by
  exact BitVec.extractLsb'_append_extractLsb'

def publicSpnQueryCode (direction : PublicPermutationDirection) (x : PublicSpnState) :
    Fin (2 ^ 257) :=
  ((match direction with | .forward => 0#1 | .inverse => 1#1) ++ publicSpnPack x).toFin

def publicSpnQueryDecode (code : Fin (2 ^ 257)) : PublicPermutationDirection × PublicSpnState :=
  let word := BitVec.ofFin code
  (if word.extractLsb' 256 1 = 0#1 then .forward else .inverse,
    publicSpnUnpack (word.extractLsb' 0 256))

theorem publicSpnQueryDecode_code (direction : PublicPermutationDirection) (x : PublicSpnState) :
    publicSpnQueryDecode (publicSpnQueryCode direction x) = (direction, x) := by
  have h : (1#1 : BitVec 1) ≠ 0#1 := by decide
  cases direction <;>
    simp only [publicSpnQueryDecode, publicSpnQueryCode, BitVec.ofFin_toFin,
      BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right,
      publicSpnUnpack_pack, h, ↓reduceIte]

/-- Both operations exposed as one bitstring oracle table. -/
def publicSpnOracleTable (p : PublicPermutation PublicSpnState)
    (code : Fin (2 ^ 257)) : BitVec 256 :=
  let query := publicSpnQueryDecode code
  publicSpnPack (publicPermutationQuery p query.1 query.2)

theorem publicSpnOracleTable_code (p : PublicPermutation PublicSpnState)
    (direction : PublicPermutationDirection) (x : PublicSpnState) :
    publicSpnOracleTable p (publicSpnQueryCode direction x) =
      publicSpnPack (publicPermutationQuery p direction x) := by
  unfold publicSpnOracleTable
  rw [publicSpnQueryDecode_code]

/-- Coherent XOR query, including a coherent direction register. -/
def publicSpnCoherentQuery {anc : Nat} (p : PublicPermutation PublicSpnState)
    (state : QVec (2 ^ 257) 256 anc) : QVec (2 ^ 257) 256 anc :=
  oracleXor (publicSpnOracleTable p) state

theorem publicSpnCoherentQuery_involutive {anc : Nat} (p : PublicPermutation PublicSpnState)
    (state : QVec (2 ^ 257) 256 anc) :
    publicSpnCoherentQuery p (publicSpnCoherentQuery p state) = state :=
  oracleXor_involutive (publicSpnOracleTable p) state

theorem publicSpnCoherentQuery_isometry {anc : Nat} (p : PublicPermutation PublicSpnState)
    (state : QVec (2 ^ 257) 256 anc) :
    QVec.stateNormSq (publicSpnCoherentQuery p state) = QVec.stateNormSq state :=
  oracleXor_isometry (publicSpnOracleTable p) state

/-- The target is given before the online run. This family is fixed before sampling p;
there is no extra oracle-correlated advice parameter. `q` counts forward/inverse
primitive calls together; a superposition of directions costs one call. -/
abbrev PublicSpnPreimageAdversary (anc q : Nat) :=
  PublicSpnState → QuantumAdv (2 ^ 257) 256 anc q

/-- Fresh-image challenge: sample x, compute target=P(x) XOR x, then run the adversary
on target with BOTH primitive directions. One sampler forward call is additional to q.
The final target register is measured as the proposed preimage; the input and ancilla
registers are ignored. The verifier makes one further forward call. -/
def publicSpnPreimageFinalState {anc q : Nat} (p : PublicPermutation PublicSpnState)
    (adversary : PublicSpnPreimageAdversary anc q) (challenge : PublicSpnState) :
    QVec (2 ^ 257) 256 anc :=
  runQuantumAdv (adversary (publicSpnFeedForward p challenge)) (publicSpnOracleTable p)

/-- Unnormalized Born mass of the actual feed-forward preimage relation. -/
def publicSpnPreimageMass {anc q : Nat} (p : PublicPermutation PublicSpnState)
    (adversary : PublicSpnPreimageAdversary anc q) (challenge : PublicSpnState) : Nat :=
  let state := publicSpnPreimageFinalState p adversary challenge
  qsum (2 ^ 257) (fun input => qsum (2 ^ 256) (fun output => qsum anc (fun auxiliary =>
    if publicSpnFeedForward p (publicSpnUnpack (BitVec.ofFin output)) =
        publicSpnFeedForward p challenge
    then GaussInt.normSq (state input output auxiliary) else 0)))

def publicSpnPreimageProbability {anc q : Nat} (p : PublicPermutation PublicSpnState)
    (adversary : PublicSpnPreimageAdversary anc q) (challenge : PublicSpnState) : RatBound where
  num := publicSpnPreimageMass p adversary challenge
  den := QVec.stateNormSq (publicSpnPreimageFinalState p adversary challenge)
  h_pos := runQuantumAdv_normSq_pos _ _

/-- Uniform fresh 256-bit input challenge, sampled after the public primitive.
Normalization is performed per challenge before averaging, since target-dependent
scaled circuits may have different squared norms. -/
def publicSpnFreshPreimageProbability {anc q : Nat} (p : PublicPermutation PublicSpnState)
    (adversary : PublicSpnPreimageAdversary anc q) : RatBound :=
  RatBound.mul (RatBound.invPow2 256) (RatBound.sumList (List.ofFn
    (fun challenge : Fin (2 ^ 256) => publicSpnPreimageProbability p adversary
      (publicSpnUnpack (BitVec.ofFin challenge)))))

/-- Exact experiment for a finite primitive ensemble: select an entry uniformly,
then a fresh uniform input, then run the fixed adversary family. The same adversary
is used for every primitive. Repeated entries carry repeated probability weight.
This does NOT assert the supplied ensemble is uniform over all permutations; such
an ideal sampler and its uniformity certificate remain separate work. -/
def publicSpnEnsemblePreimageProbability {anc q : Nat}
    (primitives : List (PublicPermutation PublicSpnState)) (nonempty : 0 < primitives.length)
    (adversary : PublicSpnPreimageAdversary anc q) : RatBound :=
  RatBound.mul ⟨1, primitives.length, nonempty⟩
    (RatBound.sumList (primitives.map (fun p => publicSpnFreshPreimageProbability p adversary)))

/-- The game probability is normalized even when the adversary uses scaled unitaries. -/
theorem publicSpnPreimageMass_le_norm {anc q : Nat} (p : PublicPermutation PublicSpnState)
    (adversary : PublicSpnPreimageAdversary anc q) (challenge : PublicSpnState) :
    publicSpnPreimageMass p adversary challenge ≤
      QVec.stateNormSq (publicSpnPreimageFinalState p adversary challenge) := by
  unfold publicSpnPreimageMass QVec.stateNormSq QVec.queryWeight
  apply qsum_le_qsum
  intro input
  apply qsum_le_qsum
  intro output
  apply qsum_le_qsum
  intro auxiliary
  split
  · exact Nat.le_refl _
  · exact Nat.zero_le _

theorem publicSpnPreimageProbability_le_one {anc q : Nat} (p : PublicPermutation PublicSpnState)
    (adversary : PublicSpnPreimageAdversary anc q) (challenge : PublicSpnState) :
    RatBound.le (publicSpnPreimageProbability p adversary challenge) RatBound.one := by
  simpa only [RatBound.le, publicSpnPreimageProbability, RatBound.one,
    Nat.mul_one, Nat.one_mul] using publicSpnPreimageMass_le_norm p adversary challenge

/-- Concrete single-address experiment. Public address parameters are given to the
adversary before its online run; the function family and code may depend on them.
This does not model extra queries to OTHER chain addresses or a full signature game. -/
def publicChainPreimageProbability {anc q : Nat}
    (hash32 : List UInt8 → List (List UInt8) → List UInt8) (address : PublicChainAddress)
    (adversary : PublicChainAddress → PublicSpnPreimageAdversary anc q) : RatBound :=
  publicSpnFreshPreimageProbability (publicChainPermutation hash32 address) (adversary address)

/-- Nonvacuity control in the QUANTUM game: the identity primitive makes the mode
constant, so every online adversary wins for every challenge. This does not describe
the actual SPN; it rules out deriving mode hardness from permutation laws alone. -/
theorem identityPublicPermutation_quantum_preimage_mass {anc q : Nat}
    (adversary : PublicSpnPreimageAdversary anc q) (challenge : PublicSpnState) :
    publicSpnPreimageMass identityPublicPermutation adversary challenge =
      QVec.stateNormSq (publicSpnPreimageFinalState identityPublicPermutation adversary challenge) := by
  unfold publicSpnPreimageMass QVec.stateNormSq QVec.queryWeight
  simp only [publicSpnFeedForward, identityPublicPermutation, id_eq, BitVec.xor_self, ↓reduceIte]

end Qsag
end
#verify_constructive
  Qsag.publicSpnPack_unpack
  Qsag.publicSpnPreimageProbability_le_one
  Qsag.publicSpnQueryDecode_code
  Qsag.publicSpnOracleTable_code
  Qsag.publicSpnCoherentQuery_involutive
  Qsag.publicSpnCoherentQuery_isometry
  Qsag.publicSpnPreimageMass_le_norm
  Qsag.identityPublicPermutation_quantum_preimage_mass
