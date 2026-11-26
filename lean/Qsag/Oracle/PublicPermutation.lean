module
public import Qsag.Math.Gf2Pow128
public import Qsag.Spec.Encoding
public import Qsag.Oracle.Keccak

public section
namespace Qsag

theorem towerSq_add (k : Nat) (a b : TowerElem k) :
    towerMul k (towerAdd k a b) (towerAdd k a b) =
      towerAdd k (towerMul k a a) (towerMul k b b) := by
  rw [towerMul_add_distrib, towerAdd_mul_distrib, towerAdd_mul_distrib,
      towerMul_comm k b a, towerAdd_assoc,
      ← towerAdd_assoc k (towerMul k a b) (towerMul k a b) (towerMul k b b),
      towerAdd_self_zero, towerZero_add]

theorem encodeNatLeBytes_decodeNatLeBytes : ∀ bs : List UInt8,
    encodeNatLeBytes bs.length (decodeNatLeBytes bs) = bs
  | [] => rfl
  | b :: bs => by
    have hb := b.toNat_lt
    have hmod : (b.toNat + 256 * decodeNatLeBytes bs) % 256 = b.toNat := by omega
    have hdiv : (b.toNat + 256 * decodeNatLeBytes bs) / 256 = decodeNatLeBytes bs := by omega
    show UInt8.ofNat ((b.toNat + 256 * decodeNatLeBytes bs) % 256) ::
        encodeNatLeBytes bs.length ((b.toNat + 256 * decodeNatLeBytes bs) / 256) = b :: bs
    rw [hmod, hdiv, UInt8.ofNat_toNat, encodeNatLeBytes_decodeNatLeBytes bs]

theorem decodeNatLeBytes_lt : ∀ bs : List UInt8, decodeNatLeBytes bs < 256 ^ bs.length
  | [] => Nat.zero_lt_one
  | b :: bs => by
    have hb := b.toNat_lt
    have ih := decodeNatLeBytes_lt bs
    show b.toNat + 256 * decodeNatLeBytes bs < 256 ^ (bs.length + 1)
    rw [Nat.pow_succ]
    omega

/-- Public reversible primitive. Both directions are exposed to the adversary. -/
structure PublicPermutation (State : Type) where
  forward : State → State
  inverse : State → State
  inverse_forward : ∀ x, inverse (forward x) = x
  forward_inverse : ∀ x, forward (inverse x) = x

/-- Primitive access includes both public directions. This operational classical subgame
is also available to quantum adversaries, but does not purport to define quantum states. -/
inductive PublicPermutationDirection where
  | forward | inverse
  deriving DecidableEq

@[expose] def publicPermutationQuery {State : Type} (p : PublicPermutation State)
    (direction : PublicPermutationDirection) (x : State) : State :=
  match direction with
  | .forward => p.forward x
  | .inverse => p.inverse x

/-- Adaptive terminating public-primitive programs. The continuation receives the actual
answer, not an assumed classically observable log of a coherent quantum query. -/
inductive PublicPermutationProgram (State Result : Type) where
  | done : Result → PublicPermutationProgram State Result
  | query : PublicPermutationDirection → State →
      (State → PublicPermutationProgram State Result) → PublicPermutationProgram State Result

/-- Result and separate forward/inverse query counts along the actual execution. -/
def runPublicPermutationProgram {State Result : Type} (p : PublicPermutation State) :
    PublicPermutationProgram State Result → Result × Nat × Nat
  | .done result => (result, 0, 0)
  | .query direction x next =>
      let answer := runPublicPermutationProgram p (next (publicPermutationQuery p direction x))
      match direction with
      | .forward => (answer.1, answer.2.1 + 1, answer.2.2)
      | .inverse => (answer.1, answer.2.1, answer.2.2 + 1)

end Qsag
