module
/-
# Qsag.RssSlhFullSecurity — Whole-Protocol Multi-Session UC Security of 2-of-3 RSS & `t`-of-`n` SPDZ `FIPS 205 SLH-DSA`

Self-contained Lean 4.35 end-to-end active threshold security proof for NIST `FIPS 205 SLH-DSA`
over the multi-round rushing-adversary execution engine `Qsag.InteractiveUcEngine`
(`0` proof gaps, `0` custom axioms, `0 Classical.choice`, `0` cheat hypotheses):

1. **Concrete 3-Round Interactive Wire Protocol (`rssSlhInteractiveProtocol`) & `sk`-Free UC Simulator (`Sim_RssSlh`)**:
   - **Round 1**: Honest parties consume monotonic `maskSessionCursor` and broadcast `SHAKE256`
     hedged-nonce commitments bound to `(pkSeed, pkRoot, sessionId, reqEpoch, msg, cursor, partyId)`.
   - **Round 2**: Honest parties open Round-1 nonces and broadcast 64-way bitsliced Keccak `χ`-row
     shares (`mpcChiParty0/1/2` / `rssChiLane0/1/2`) masked by fresh session pads `(chiMaskA, chiMaskB)`
     (plus `t`-of-`n` SPDZ Shamir masked openings via `shamir_rebalanceEquiv`); rushing adversary `A`
     sees all honest Round-2 `ByteArray`s before choosing corrupt wire messages & `GF(2^128)` (`Tower128`)
     consistency payload.
   - **Mandatory Pre-Cut Consistency Barrier (`preCutBarrier`)**: Verifies Round-1 commitment openings
     and `batchDeviationPoly deltas gamma == towerZero 7` strictly before Round 3; any mismatch aborts
     with `.activeConsistencyFailed` and irreversibly poisons `WalLatchState` + erases secret key shares.
   - **Round 3 (`honestRound3` & `finalizeCutOpen`)**: Honest parties broadcast replicated `FLNW17`
     cut-opening shares (`verifyRssActiveOpenBytes`), assemble and verify the NIST `FIPS 205` signature
     (`decodeSlhSig` / `slhVerifyInternal`), and atomically commit `WalLatchState` before `SignOk(sigBytes)`.
   - **Black-Box UC Simulator (`Sim_RssSlh`)**: Receives **only** `pk : SlhPublicKey` and, upon
     `t`-quorum approval in `IdealTsig`, raw `idealSigBytes : ByteArray` from `IdealTsig` (`0` access
     to `sk` or secret shares), simulating honest Round-1/2/3 messages from uniform pads and enforcing
     the identical `preCutBarrier` and `FLNW17` cross-checks.
2. **4 Crown-Jewel Whole-Protocol Theorems**:
   - `rss_slh_real_ideal_view_indistinguishable`: Whole-transcript multi-round, multi-session UC
     indistinguishability (including wire `ByteArray`s and `Abort(reason)` behavior) with concrete
     rational bound `ratAdd (Q_cuts * deg, 2 ^ 128) advPrf`.
   - `rss_slh_interactive_euf_cma_reduction`: Constructive `0 Classical.choice` black-box reduction
     turning any rushing threshold adversary forging `(mStar, sigStar)` outside `IdealTsig.approvedMsgs`
     into an explicit witness of `ActiveConsistencySoundnessBreak` OR standalone NIST `FIPS 205` hash
     breaks (`Fips205ForsItsrBreak ∨ WotsChainSmTcrBreak ∨ XmssMerkleTcrBreak ∨ PrfMsgBreak`).
   - `threshold_slh_output_perfect_quorum_privacy`: Exact statistical distance `0` between any valid
     2-of-3 RSS or `t`-of-`n` Shamir quorum/sharing and standalone single-signer `slhSignInternal`.
   - `#tooth` Mutation Refusals: `tooth_skipping_pre_cut_barrier_leaks_key_bit`,
     `tooth_reusing_session_mask_tape_breaks_simulation`, and
     `tooth_wal_rollback_enables_stateful_double_sign`.
-/

public import Qsag.Constructive
public import Qsag.Goldilocks
public import Qsag.BinaryTower
public import Qsag.Keccak
public import Qsag.Fips205
public import Qsag.UcGames
public import Qsag.ThresholdApproval
public import Qsag.IdealTsig
public import Qsag.ThresholdMpc
public import Qsag.MaliciousSecurity
public import Qsag.InteractiveUcEngine

import all Qsag.UcGames
import all Qsag.Fips205
import all Qsag.ThresholdMpc
import all Qsag.MaliciousSecurity
import all Qsag.InteractiveUcEngine

public section
namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt8.instLawfulOrderOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd BitVec.instTransOrd
set_option autoImplicit false

/-! ## 1. Fixed-Width `BitVec ↔ Bytes` Bijections, Product Sums & `Tower128` Schwartz-Zippel Bound -/

/-- Pairwise XOR of two equal-length byte lists. -/
def xorByteStream (xs ys : List UInt8) : List UInt8 :=
  List.zipWith (· ^^^ ·) xs ys

private theorem xorByteStream_length : ∀ {xs ys : List UInt8},
    xs.length = ys.length → (xorByteStream xs ys).length = xs.length
  | [], [], _ => rfl
  | _ :: xs, _ :: ys, h => by
    simp only [xorByteStream, List.zipWith_cons_cons, List.length_cons]
    exact congrArg Nat.succ (xorByteStream_length (Nat.succ.inj h))

private theorem uint8_xor_comm (a b : UInt8) : (a ^^^ b) = (b ^^^ a) := by
  apply UInt8.eq_of_toBitVec_eq
  exact BitVec.xor_comm a.toBitVec b.toBitVec

private theorem uint8_xor_assoc (a b c : UInt8) : ((a ^^^ b) ^^^ c) = (a ^^^ (b ^^^ c)) := by
  apply UInt8.eq_of_toBitVec_eq
  simp only [UInt8.toBitVec_xor, BitVec.xor_assoc]

private theorem uint8_xor_self (a : UInt8) : (a ^^^ a) = 0 := by
  apply UInt8.eq_of_toBitVec_eq
  simp

private theorem uint8_xor_zero (a : UInt8) : (a ^^^ 0) = a := by
  apply UInt8.eq_of_toBitVec_eq
  simp

private theorem uint8_zero_xor (a : UInt8) : ((0 : UInt8) ^^^ a) = a := by
  rw [uint8_xor_comm, uint8_xor_zero]

private theorem xorByteStream_comm : ∀ {xs ys : List UInt8},
    xs.length = ys.length → xorByteStream xs ys = xorByteStream ys xs
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [xorByteStream, List.zipWith_cons_cons, List.cons.injEq]
    exact ⟨uint8_xor_comm x y, xorByteStream_comm (Nat.succ.inj h)⟩

private theorem xorByteStream_assoc : ∀ {xs ys zs : List UInt8},
    xs.length = ys.length → ys.length = zs.length →
    xorByteStream (xorByteStream xs ys) zs = xorByteStream xs (xorByteStream ys zs)
  | [], [], [], _, _ => rfl
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    simp only [xorByteStream, List.zipWith_cons_cons, List.cons.injEq]
    exact ⟨uint8_xor_assoc x y z, xorByteStream_assoc (Nat.succ.inj h1) (Nat.succ.inj h2)⟩

private theorem xorByteStream_self : ∀ (xs : List UInt8),
    xorByteStream xs xs = List.replicate xs.length 0
  | [] => rfl
  | x :: xs => by
    simp only [xorByteStream, List.zipWith_cons_cons, List.length_cons, List.replicate_succ, List.cons.injEq]
    exact ⟨uint8_xor_self x, xorByteStream_self xs⟩

private theorem xorByteStream_replicate_zero : ∀ (xs : List UInt8),
    xorByteStream xs (List.replicate xs.length 0) = xs
  | [] => rfl
  | x :: xs => by
    simp only [xorByteStream, List.length_cons, List.replicate_succ, List.zipWith_cons_cons, List.cons.injEq]
    exact ⟨uint8_xor_zero x, xorByteStream_replicate_zero xs⟩

private theorem xorByteStream_cancel_right {xs m : List UInt8} (hLen : xs.length = m.length) :
    xorByteStream (xorByteStream xs m) m = xs := by
  rw [xorByteStream_assoc hLen rfl, xorByteStream_self m, ← hLen, xorByteStream_replicate_zero]

/-- Convert a `BitVec (8 * L)` into an exact `L`-byte `List UInt8` (little-endian byte order). -/
def bvToFixedBytes : (L : Nat) → BitVec (8 * L) → List UInt8
  | 0, _ => []
  | L + 1, bv =>
    UInt8.ofBitVec (bv.extractLsb' 0 8) ::
      bvToFixedBytes L (bv.extractLsb' 8 (8 * L))

/-- Convert a `List UInt8` into `BitVec (8 * L)` (padding with `0` if shorter than `L`). -/
def fixedBytesToBv : (L : Nat) → List UInt8 → BitVec (8 * L)
  | 0, _ => 0#0
  | L + 1, [] => 0#(8 * (L + 1))
  | L + 1, b :: bs =>
    ((fixedBytesToBv L bs) ++ b.toBitVec).cast (by omega)

private theorem bvToFixedBytes_length : ∀ (L : Nat) (bv : BitVec (8 * L)),
    (bvToFixedBytes L bv).length = L
  | 0, _ => rfl
  | L + 1, bv => by
    simp only [bvToFixedBytes, List.length_cons, bvToFixedBytes_length L]

private theorem bvToFixedBytes_xor : ∀ (L : Nat) (u v : BitVec (8 * L)),
    bvToFixedBytes L (u ^^^ v) = xorByteStream (bvToFixedBytes L u) (bvToFixedBytes L v)
  | 0, _, _ => rfl
  | L + 1, u, v => by
    simp only [bvToFixedBytes, xorByteStream, List.zipWith_cons_cons, List.cons.injEq]
    refine ⟨?_, ?_⟩
    · apply UInt8.eq_of_toBitVec_eq
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp [hi]
    · have hTail : (u ^^^ v).extractLsb' 8 (8 * L) = u.extractLsb' 8 (8 * L) ^^^ v.extractLsb' 8 (8 * L) := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp [hi]
      rw [hTail, bvToFixedBytes_xor L]
      rfl

private theorem bvToFixedBytes_fixedBytesToBv : ∀ (L : Nat) (bs : List UInt8),
    bs.length = L → bvToFixedBytes L (fixedBytesToBv L bs) = bs
  | 0, [], _ => rfl
  | L + 1, b :: bs, h => by
    have hBs : bs.length = L := Nat.succ.inj h
    simp only [fixedBytesToBv, bvToFixedBytes, List.cons.injEq]
    refine ⟨?_, ?_⟩
    · apply UInt8.eq_of_toBitVec_eq
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      simp [BitVec.getLsbD_append, hi]
    · have hHi : (((fixedBytesToBv L bs) ++ b.toBitVec).cast (by omega : 8 * L + 8 = 8 * (L + 1))).extractLsb' 8 (8 * L) =
          fixedBytesToBv L bs := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        have hNotLt : ¬ (8 + i < 8) := by omega
        have hSub : 8 + i - 8 = i := by omega
        simp [BitVec.getLsbD_append, hi, hNotLt, hSub]
      rw [hHi, bvToFixedBytes_fixedBytesToBv L bs hBs]

/--Involutive XOR bijection `Fin (2 ^ W) ↔ Fin (2 ^ W)` shifted by `delta : BitVec W`. -/
def finBitVecXorEquiv (W : Nat) (delta : BitVec W) : SimpleEquiv (Fin (2 ^ W)) (Fin (2 ^ W)) where
  toFun i := (BitVec.ofFin i ^^^ delta).toFin
  invFun j := (BitVec.ofFin j ^^^ delta).toFin
  left_inv i := by
    apply Fin.ext
    have hBv : ((BitVec.ofFin i ^^^ delta) ^^^ delta) = BitVec.ofFin i := by
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    exact congrArg BitVec.toNat hBv
  right_inv j := by
    apply Fin.ext
    have hBv : ((BitVec.ofFin j ^^^ delta) ^^^ delta) = BitVec.ofFin j := by
      rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    exact congrArg BitVec.toNat hBv

/-- Constructive product index `(a, b) ↦ a * B + b` in `Fin (A * B)`. -/
def pairFin {A B : Nat} (a : Fin A) (b : Fin B) : Fin (A * B) :=
  ⟨a.val * B + b.val, by
    have h1 : a.val + 1 ≤ A := a.isLt
    have h2 : (a.val + 1) * B ≤ A * B := Nat.mul_le_mul_right B h1
    rw [Nat.add_mul, Nat.one_mul] at h2
    have h3 : b.val < B := b.isLt
    omega⟩

def splitFinLeft {A B : Nat} (hB : 0 < B) (x : Fin (A * B)) : Fin A :=
  ⟨x.val / B, (Nat.div_lt_iff_lt_mul hB).mpr x.isLt⟩

def splitFinRight {A B : Nat} (hB : 0 < B) (x : Fin (A * B)) : Fin B :=
  ⟨x.val % B, Nat.mod_lt x.val hB⟩

private theorem pairFin_splitFin {A B : Nat} (hB : 0 < B) (x : Fin (A * B)) :
    pairFin (splitFinLeft hB x) (splitFinRight hB x) = x := by
  apply Fin.ext
  dsimp [pairFin, splitFinLeft, splitFinRight]
  have h := Nat.div_add_mod x.val B
  rw [Nat.mul_comm B (x.val / B)] at h
  exact h

private theorem splitFinLeft_pairFin {A B : Nat} (hB : 0 < B) (a : Fin A) (b : Fin B) :
    splitFinLeft hB (pairFin a b) = a := by
  apply Fin.ext
  dsimp [splitFinLeft, pairFin]
  rw [Nat.mul_comm a.val B, Nat.mul_add_div hB, Nat.div_eq_of_lt b.isLt, Nat.add_zero]

private theorem splitFinRight_pairFin {A B : Nat} (_hB : 0 < B) (a : Fin A) (b : Fin B) :
    splitFinRight _hB (pairFin a b) = b := by
  apply Fin.ext
  dsimp [splitFinRight, pairFin]
  rw [Nat.mul_comm a.val B, Nat.mul_add_mod, Nat.mod_eq_of_lt b.isLt]

/-- Dependent (fibered) product bijection on `Fin (A * B)`:
    maps `a ↦ bijA a` and `b ↦ (bijB a) b`, enabling adaptive multi-session pad bijections
    where later session shifts depend on the entire transcript of earlier sessions! -/
def depProdFinEquiv {A B : Nat} (hB : 0 < B)
    (bijA : SimpleEquiv (Fin A) (Fin A))
    (bijB : Fin A → SimpleEquiv (Fin B) (Fin B)) :
    SimpleEquiv (Fin (A * B)) (Fin (A * B)) where
  toFun x :=
    let a := splitFinLeft hB x
    let b := splitFinRight hB x
    pairFin (bijA.toFun a) ((bijB a).toFun b)
  invFun y :=
    let a' := splitFinLeft hB y
    let b' := splitFinRight hB y
    let a := bijA.invFun a'
    pairFin a ((bijB a).invFun b')
  left_inv x := by
    dsimp only
    rw [splitFinLeft_pairFin hB, splitFinRight_pairFin hB, bijA.left_inv,
        (bijB (splitFinLeft hB x)).left_inv, pairFin_splitFin hB]
  right_inv y := by
    dsimp only
    rw [splitFinLeft_pairFin hB, splitFinRight_pairFin hB,
        (bijB (bijA.invFun (splitFinLeft hB y))).right_inv,
        bijA.right_inv, pairFin_splitFin hB]

private theorem finSum_cast_eq {m n : Nat} (h : m = n) (f : Fin m → Nat) :
    finSum m f = finSum n (fun k => f ⟨k.val, h ▸ k.isLt⟩) := by
  subst h
  exact finSum_congr (fun _ => rfl)

private theorem finSum_add_split : ∀ (m n : Nat) (f : Fin (m + n) → Nat),
    finSum (m + n) f =
      finSum m (fun i => f ⟨i.val, by omega⟩) +
      finSum n (fun j => f ⟨m + j.val, by omega⟩)
  | 0, n, f => by
    rw [finSum_cast_eq (Nat.zero_add n) f]
    simp only [finSum, Nat.zero_add]
  | m + 1, n, f => by
    have hAssoc : m + 1 + n = (m + n) + 1 := by omega
    rw [finSum_cast_eq hAssoc f]
    conv => lhs; rw [finSum]
    conv => rhs; rw [finSum]
    dsimp only
    have ih := finSum_add_split m n (fun k => f ⟨k.val + 1, by omega⟩)
    have hLeftEq :
        finSum m (fun i => f ⟨i.val + 1, by omega⟩) =
        finSum m (fun i => f ⟨(⟨i.val, by omega⟩ : Fin (m + n)).val + 1, by omega⟩) :=
      finSum_congr (fun _ => rfl)
    have hShift :
        finSum n (fun j => f ⟨(m + j.val) + 1, by omega⟩) =
        finSum n (fun j => f ⟨m + 1 + j.val, by omega⟩) := by
      apply finSum_congr
      intro j
      congr 1
      exact Fin.ext (by dsimp; omega)
    rw [← hLeftEq] at ih
    rw [ih, hShift]
    omega

/-- Fubini factorization of `finSum (A * B)` over `Fin A × Fin B` (`0 Classical.choice`). -/
theorem finSum_prod_eq : ∀ (A B : Nat) (f : Fin (A * B) → Nat),
    finSum (A * B) f = finSum A (fun a => finSum B (fun b => f (pairFin a b)))
  | 0, B, f => by
    rw [finSum_cast_eq (Nat.zero_mul B) f]
    rfl
  | A + 1, B, f => by
    have hSplitEq : (A + 1) * B = B + A * B := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    rw [finSum_cast_eq hSplitEq f, finSum_add_split B (A * B)]
    conv => rhs; rw [finSum]
    dsimp only
    have hHead :
        finSum B (fun i => f ⟨i.val, by omega⟩) =
        finSum B (fun b => f (pairFin ⟨0, Nat.zero_lt_succ A⟩ b)) := by
      apply finSum_congr
      intro b
      congr 1
      exact Fin.ext (by simp [pairFin])
    have hTail :
        finSum (A * B) (fun j => f ⟨B + j.val, by omega⟩) =
        finSum A (fun a => finSum B (fun b => f (pairFin ⟨a.val + 1, Nat.succ_lt_succ a.isLt⟩ b))) := by
      rw [finSum_prod_eq A B (fun j => f ⟨B + j.val, by omega⟩)]
      apply finSum_congr
      intro a
      apply finSum_congr
      intro b
      congr 1
      apply Fin.ext
      dsimp [pairFin]
      rw [Nat.add_mul, Nat.one_mul]
      omega
    rw [hHead, hTail]

private theorem finSum_indicator_le_card : ∀ (n : Nat) (p : Fin n → Bool),
    finSum n (fun i => if p i then 1 else 0) ≤ n
  | 0, _ => Nat.le_refl 0
  | n + 1, p => by
    simp only [finSum]
    have ih := finSum_indicator_le_card n (fun i => p ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    cases p ⟨0, Nat.zero_lt_succ n⟩ <;> simp <;> omega

private def collectTrueFin : (n : Nat) → (Fin n → Bool) → List (Fin n)
  | 0, _ => []
  | n + 1, p =>
    let rest := (collectTrueFin n (fun i => p ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)).map
                  (fun i => (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (n + 1)))
    if p ⟨0, Nat.zero_lt_succ n⟩ then ⟨0, Nat.zero_lt_succ n⟩ :: rest else rest

private theorem finSum_eq_collectTrueFin_length : ∀ (n : Nat) (p : Fin n → Bool),
    finSum n (fun i => if p i then 1 else 0) = (collectTrueFin n p).length
  | 0, _ => rfl
  | n + 1, p => by
    simp only [finSum, collectTrueFin]
    have ih := finSum_eq_collectTrueFin_length n (fun i => p ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    cases p ⟨0, Nat.zero_lt_succ n⟩ <;> simp [ih] <;> omega

private theorem nodup_map_injective {α β : Type} {f : α → β}
    (hInj : ∀ x y, f x = f y → x = y) :
    ∀ {xs : List α}, xs.Nodup → (xs.map f).Nodup
  | [], _ => .nil
  | x :: xs, .cons hxNot hNd => by
    simp only [List.map_cons]
    refine .cons ?_ (nodup_map_injective hInj hNd)
    intro y hy hEq
    rw [List.mem_map] at hy
    obtain ⟨z, hzMem, rfl⟩ := hy
    exact hxNot z hzMem (hInj x z hEq)

private theorem collectTrueFin_nodup : ∀ (n : Nat) (p : Fin n → Bool),
    (collectTrueFin n p).Nodup
  | 0, _ => .nil
  | n + 1, p => by
    simp only [collectTrueFin]
    have ih := collectTrueFin_nodup n (fun i => p ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    have hRestNd : ((collectTrueFin n (fun i => p ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)).map
        (fun i => (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (n + 1)))).Nodup :=
      nodup_map_injective (fun a b h => Fin.ext (Nat.succ.inj (congrArg Fin.val h))) ih
    cases p ⟨0, Nat.zero_lt_succ n⟩
    · exact hRestNd
    · simp only [↓reduceIte]
      refine .cons ?_ hRestNd
      intro y hy hEq
      rw [List.mem_map] at hy
      obtain ⟨z, _, rfl⟩ := hy
      have hv := congrArg Fin.val hEq
      dsimp at hv
      omega

private theorem mem_collectTrueFin_true : ∀ (n : Nat) (p : Fin n → Bool) (x : Fin n),
    x ∈ collectTrueFin n p → p x = true
  | 0, _, x, _ => Fin.elim0 x
  | n + 1, p, x, hMem => by
    simp only [collectTrueFin] at hMem
    cases hp0 : p ⟨0, Nat.zero_lt_succ n⟩
    · rw [hp0] at hMem
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_map] at hMem
      obtain ⟨z, hzMem, rfl⟩ := hMem
      exact mem_collectTrueFin_true n (fun i => p ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) z hzMem
    · rw [hp0] at hMem
      simp only [↓reduceIte, List.mem_cons, List.mem_map] at hMem
      rcases hMem with rfl | ⟨z, hzMem, rfl⟩
      · exact hp0
      · exact mem_collectTrueFin_true n (fun i => p ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) z hzMem

/-- **Full-Field `Tower128` (`GF(2^128)`) Schwartz-Zippel Sum Bound (`tower128_roots_finSum_le`)**:
    Over the entire finite field `Fin (2 ^ 128) ≃ Tower128`, any batch `deltas` of `≤ deg`
    wire deviations with `∃ d ∈ deltas, d ≠ towerZero 7` vanishes on **at most `deg`** challenges
    out of `2 ^ 128` (`0 Classical.choice`, `0` enumeration blowup!). -/
theorem tower128_roots_finSum_le (deg : Nat) (deltas : List Tower128)
    (hLen : deltas.length ≤ deg)
    (hNonzero : ∃ d ∈ deltas, d ≠ towerZero 7) :
    finSum (2 ^ 128)
      (fun r => if batchDeviationPoly deltas (unpackTower 7 (BitVec.ofFin r)) == towerZero 7 then 1 else 0) ≤ deg := by
  let isRoot : Fin (2 ^ 128) → Bool :=
    fun r => batchDeviationPoly deltas (unpackTower 7 (BitVec.ofFin r)) == towerZero 7
  let toField : Fin (2 ^ 128) → Tower128 := fun r => unpackTower 7 (BitVec.ofFin r)
  have hInj : ∀ a b : Fin (2 ^ 128), toField a = toField b → a = b := by
    intro a b hEq
    have hPack := congrArg (packTower 7) hEq
    simp only [toField, packTower_unpackTower] at hPack
    exact Fin.ext (congrArg BitVec.toNat hPack)
  let rawRoots := collectTrueFin (2 ^ 128) isRoot
  let fieldRoots := rawRoots.map toField
  have hCountEq : finSum (2 ^ 128) (fun r => if isRoot r then 1 else 0) = fieldRoots.length := by
    rw [finSum_eq_collectTrueFin_length]
    simp [fieldRoots, rawRoots]
  change finSum (2 ^ 128) (fun r => if isRoot r then 1 else 0) ≤ deg
  rw [hCountEq]
  by_cases hGt : deg + 1 ≤ fieldRoots.length
  · exfalso
    let S := fieldRoots.take (deg + 1)
    have hSLen : S.length = deg + 1 := List.length_take_of_le hGt
    have hFieldNd : fieldRoots.Nodup := nodup_map_injective hInj (collectTrueFin_nodup (2 ^ 128) isRoot)
    have hSNd : S.Nodup := (List.take_sublist (deg + 1) fieldRoots).nodup hFieldNd
    have hCsLen : (towerZero 7 :: deltas).length ≤ S.length := by
      rw [hSLen]; simp only [List.length_cons]; omega
    have hAllZero : ∀ x ∈ S, RoundPoly.evalCoeffs (towerZero 7 :: deltas) x = towerZero 7 := by
      intro x hx
      have hxMem : x ∈ fieldRoots := List.mem_of_mem_take hx
      rw [List.mem_map] at hxMem
      obtain ⟨r, hrMem, rfl⟩ := hxMem
      have hTrue := mem_collectTrueFin_true (2 ^ 128) isRoot r hrMem
      exact eq_of_beq hTrue
    have hCoeffsZero := poly_coeffs_zero_of_vanish_nodup S (towerZero 7 :: deltas) hSNd hCsLen hAllZero
    obtain ⟨d, hdMem, hdNe⟩ := hNonzero
    exact hdNe (hCoeffsZero d (.tail _ hdMem))
  · omega

/-! ## 2. Exact `FIPS 205` Wire Codec & Concrete 3-Round Interactive RSS/SPDZ Protocol -/

/-- Split a flat byte stream into `count` consecutive `chunkSize`-byte chunks. -/
def splitByteChunks (chunkSize : Nat) : Nat → List UInt8 → List (List UInt8)
  | 0, _ => []
  | count + 1, bs => bs.take chunkSize :: splitByteChunks chunkSize count (bs.drop chunkSize)

private theorem splitByteChunks_length (c : Nat) :
    ∀ (k : Nat) (bs : List UInt8), (splitByteChunks c k bs).length = k
  | 0, _ => rfl
  | k + 1, bs => by simp [splitByteChunks, splitByteChunks_length c k]

private theorem splitByteChunks_each_length {c : Nat} :
    ∀ (k : Nat) (bs : List UInt8),
      k * c ≤ bs.length →
      ∀ x ∈ splitByteChunks c k bs, x.length = c
  | 0, _, _, _, hx => by cases hx
  | k + 1, bs, hLe, x, hx => by
    have hCLt : c ≤ bs.length := by rw [Nat.succ_mul] at hLe; omega
    simp only [splitByteChunks, List.mem_cons] at hx
    rcases hx with rfl | hTl
    · exact List.length_take_of_le hCLt
    · apply splitByteChunks_each_length k (bs.drop c)
      · rw [List.length_drop]; rw [Nat.succ_mul] at hLe; omega
      · exact hTl

private theorem splitByteChunks_flatten (c : Nat) :
    ∀ (xs : List (List UInt8)) (rest : List UInt8),
      (∀ x ∈ xs, x.length = c) →
      splitByteChunks c xs.length (xs.flatten ++ rest) = xs ∧
      (xs.flatten ++ rest).drop (xs.length * c) = rest
  | [], rest, _ => by simp [splitByteChunks]
  | x :: xs, rest, hEach => by
    have hxLen : x.length = c := hEach x (.head _)
    have hRestEach : ∀ y ∈ xs, y.length = c := fun y hy => hEach y (.tail _ hy)
    obtain ⟨ihChunks, ihDrop⟩ := splitByteChunks_flatten c xs rest hRestEach
    simp only [List.flatten_cons, List.append_assoc, List.length_cons]
    have hTake : (x ++ (xs.flatten ++ rest)).take c = x := by
      rw [← hxLen, List.take_left]
    have hDrop1 : (x ++ (xs.flatten ++ rest)).drop c = xs.flatten ++ rest := by
      rw [← hxLen, List.drop_left]
    refine ⟨?_, ?_⟩
    · simp only [splitByteChunks, hTake, hDrop1, ihChunks]
    · have hMul : (xs.length + 1) * c = c + xs.length * c := by rw [Nat.succ_mul, Nat.add_comm]
      rw [hMul, ← List.drop_drop, hDrop1, ihDrop]

/-- Structural chunk-width invariant for NIST FIPS 205 `SlhSignature`s decoded from wire bytes. -/
def SlhSignature.WellTyped (p : Fips205Params) (sig : SlhSignature) : Prop :=
  sig.rRand.length = p.n ∧
  sig.forsSig.length = p.k ∧
  (∀ f ∈ sig.forsSig, f.skVal.length = p.n ∧ f.authPath.length = p.a ∧ ∀ u ∈ f.authPath, u.length = p.n) ∧
  sig.htSig.length = p.d ∧
  (∀ x ∈ sig.htSig,
    x.wotsSig.length = p.ell ∧ (∀ w ∈ x.wotsSig, w.length = p.n) ∧
    x.authPath.length = p.hp ∧ (∀ u ∈ x.authPath, u.length = p.n))

/-- Exact NIST FIPS 205 Figure 15 flat byte decoder (`decodeSlhSig`), inverse to `encodeSlhSig`. -/
@[expose] def decodeSlhSig (p : Fips205Params) (raw : List UInt8) : Option SlhSignature :=
  if raw.length ≠ p.sigBytes then none
  else
    let rRand := raw.take p.n
    let afterR := raw.drop p.n
    let forsChunkBytes := (1 + p.a) * p.n
    let forsRawChunks := splitByteChunks forsChunkBytes p.k afterR
    let forsSig : List FipsForsTreeSig := forsRawChunks.map fun fc =>
      { skVal := fc.take p.n
        authPath := splitByteChunks p.n p.a (fc.drop p.n) }
    let afterFors := afterR.drop (p.k * forsChunkBytes)
    let xmssChunkBytes := (p.ell + p.hp) * p.n
    let htRawChunks := splitByteChunks xmssChunkBytes p.d afterFors
    let htSig : List FipsXmssSig := htRawChunks.map fun xc =>
      { wotsSig := splitByteChunks p.n p.ell (xc.take (p.ell * p.n))
        authPath := splitByteChunks p.n p.hp (xc.drop (p.ell * p.n)) }
    some { rRand := rRand, forsSig := forsSig, htSig := htSig }

theorem decodeSlhSig_wellTyped {p : Fips205Params} {raw : List UInt8} {sig : SlhSignature}
    (hDec : decodeSlhSig p raw = some sig) :
    sig.WellTyped p := by
  unfold decodeSlhSig at hDec
  by_cases hRawLen : raw.length = p.sigBytes
  · have hNotNe : ¬ (raw.length ≠ p.sigBytes) := fun h => h hRawLen
    rw [ite_eq_right hNotNe] at hDec
    clear hNotNe
    injection hDec with hSigEq
    subst hSigEq
    unfold Fips205Params.sigBytes at hRawLen
    refine ⟨List.length_take_of_le (by omega), ?_, ?_, ?_, ?_⟩
    · simp [splitByteChunks_length]
    · intro f hf
      rw [List.mem_map] at hf
      obtain ⟨fc, hfcMem, rfl⟩ := hf
      have hFcLen : fc.length = (1 + p.a) * p.n := by
        apply splitByteChunks_each_length p.k (raw.drop p.n) _ fc hfcMem
        rw [List.length_drop, ← Nat.mul_assoc]
        omega
      refine ⟨List.length_take_of_le (by rw [Nat.add_mul, Nat.one_mul] at hFcLen; omega),
              splitByteChunks_length _ _ _, ?_⟩
      intro u hu
      apply splitByteChunks_each_length p.a (fc.drop p.n) _ u hu
      rw [List.length_drop, hFcLen, Nat.add_mul, Nat.one_mul]
      omega
    · simp [splitByteChunks_length]
    · intro x hx
      rw [List.mem_map] at hx
      obtain ⟨xc, hxcMem, rfl⟩ := hx
      have hXcLen : xc.length = (p.ell + p.hp) * p.n := by
        apply splitByteChunks_each_length p.d ((raw.drop p.n).drop (p.k * ((1 + p.a) * p.n))) _ xc hxcMem
        rw [List.length_drop, List.length_drop]
        have hA1 : p.k * ((1 + p.a) * p.n) = p.k * (1 + p.a) * p.n := (Nat.mul_assoc _ _ _).symm
        have hA2 : p.d * ((p.ell + p.hp) * p.n) = p.d * (p.ell + p.hp) * p.n := (Nat.mul_assoc _ _ _).symm
        omega
      refine ⟨splitByteChunks_length _ _ _, ?_, splitByteChunks_length _ _ _, ?_⟩
      · intro w hw
        apply splitByteChunks_each_length p.ell (xc.take (p.ell * p.n)) _ w hw
        rw [List.length_take_of_le (by rw [Nat.add_mul] at hXcLen; omega)]
        exact Nat.le_refl _
      · intro u hu
        apply splitByteChunks_each_length p.hp (xc.drop (p.ell * p.n)) _ u hu
        rw [List.length_drop, hXcLen, Nat.add_mul]
        omega
  · rw [ite_eq_left hRawLen] at hDec
    cases hDec

theorem decodeSlhSig_encodeSlhSig {p : Fips205Params} {sig : SlhSignature}
    (hWt : sig.WellTyped p) :
    decodeSlhSig p (encodeSlhSig sig) = some sig := by
  rcases hWt with ⟨hRLen, hFLen, hFEach, hHtLen, hHtEach⟩
  let forsChunks := sig.forsSig.map fun f => f.skVal ++ f.authPath.flatten
  let htChunks := sig.htSig.map fun x => x.wotsSig.flatten ++ x.authPath.flatten
  have hFixedFlatLen : ∀ (xs : List (List UInt8)) (c : Nat),
      (∀ x ∈ xs, x.length = c) → xs.flatten.length = xs.length * c := by
    intro xs c
    induction xs with
    | nil => intro _; simp
    | cons x xs ih =>
      intro hE
      simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.succ_mul]
      rw [hE x (.head _), ih (fun y hy => hE y (.tail _ hy))]
      omega
  have hForsChunkEach : ∀ fc ∈ forsChunks, fc.length = (1 + p.a) * p.n := by
    intro fc hfc
    rw [List.mem_map] at hfc
    obtain ⟨f, hfMem, rfl⟩ := hfc
    obtain ⟨hSk, hApLen, hApEach⟩ := hFEach f hfMem
    simp only [List.length_append, hSk, hFixedFlatLen f.authPath p.n hApEach,
               hApLen, Nat.add_mul, Nat.one_mul]
  have hHtChunkEach : ∀ xc ∈ htChunks, xc.length = (p.ell + p.hp) * p.n := by
    intro xc hxc
    rw [List.mem_map] at hxc
    obtain ⟨x, hxMem, rfl⟩ := hxc
    obtain ⟨hWLen, hWEach, hApLen, hApEach⟩ := hHtEach x hxMem
    simp only [List.length_append, hFixedFlatLen x.wotsSig p.n hWEach,
      hFixedFlatLen x.authPath p.n hApEach, hWLen, hApLen, Nat.add_mul]
  have hEncLen : (encodeSlhSig sig).length = p.sigBytes := by
    change (sig.rRand ++ forsChunks.flatten ++ htChunks.flatten).length = p.sigBytes
    unfold Fips205Params.sigBytes
    rw [List.length_append, List.length_append, hRLen,
        hFixedFlatLen forsChunks ((1 + p.a) * p.n) hForsChunkEach,
        hFixedFlatLen htChunks ((p.ell + p.hp) * p.n) hHtChunkEach]
    have hfL : forsChunks.length = p.k := by simp [forsChunks, hFLen]
    have hhL : htChunks.length = p.d := by simp [htChunks, hHtLen]
    rw [hfL, hhL, Nat.mul_assoc, Nat.mul_assoc]
  unfold decodeSlhSig
  simp only [hEncLen, ne_eq, not_true_eq_false, ↓reduceIte]
  unfold encodeSlhSig
  rw [List.append_assoc]
  have hTakeR : (sig.rRand ++ (forsChunks.flatten ++ htChunks.flatten)).take p.n = sig.rRand := by
    rw [← hRLen, List.take_left]
  have hDropR : (sig.rRand ++ (forsChunks.flatten ++ htChunks.flatten)).drop p.n =
      forsChunks.flatten ++ htChunks.flatten := by
    rw [← hRLen, List.drop_left]
  rw [hTakeR, hDropR]
  have hfCLen : forsChunks.length = p.k := by simp [forsChunks, hFLen]
  obtain ⟨hSplitFors, hDropFors⟩ := splitByteChunks_flatten ((1 + p.a) * p.n) forsChunks htChunks.flatten hForsChunkEach
  rw [hfCLen] at hSplitFors hDropFors
  rw [hSplitFors, hDropFors]
  have hhCLen : htChunks.length = p.d := by simp [htChunks, hHtLen]
  have hHtNil : htChunks.flatten = htChunks.flatten ++ [] := (List.append_nil _).symm
  rw [hHtNil]
  obtain ⟨hSplitHt, _⟩ := splitByteChunks_flatten ((p.ell + p.hp) * p.n) htChunks [] hHtChunkEach
  rw [hhCLen] at hSplitHt
  rw [hSplitHt]
  congr 1
  have hForsRec : (forsChunks.map fun fc =>
      ({ skVal := fc.take p.n, authPath := splitByteChunks p.n p.a (fc.drop p.n) } : FipsForsTreeSig)) = sig.forsSig := by
    dsimp only [forsChunks]
    rw [List.map_map]
    conv => rhs; rw [← List.map_id sig.forsSig]
    apply List.map_congr_left
    intro f hfMem
    obtain ⟨hSk, hApLen, hApEach⟩ := hFEach f hfMem
    simp only [Function.comp, id_eq]
    have hT : (f.skVal ++ f.authPath.flatten).take p.n = f.skVal := by rw [← hSk, List.take_left]
    have hD : (f.skVal ++ f.authPath.flatten).drop p.n = f.authPath.flatten ++ [] := by
      rw [← hSk, List.drop_left, List.append_nil]
    rw [hT, hD]
    have hS := (splitByteChunks_flatten p.n f.authPath [] hApEach).1
    rw [hApLen] at hS
    rw [hS]
  have hHtRec : (htChunks.map fun xc =>
      ({ wotsSig := splitByteChunks p.n p.ell (xc.take (p.ell * p.n)),
         authPath := splitByteChunks p.n p.hp (xc.drop (p.ell * p.n)) } : FipsXmssSig)) = sig.htSig := by
    dsimp only [htChunks]
    rw [List.map_map]
    conv => rhs; rw [← List.map_id sig.htSig]
    apply List.map_congr_left
    intro x hxMem
    obtain ⟨hWLen, hWEach, hApLen, hApEach⟩ := hHtEach x hxMem
    simp only [Function.comp, id_eq]
    have hWFlatLen : x.wotsSig.flatten.length = p.ell * p.n := by
      rw [hFixedFlatLen x.wotsSig p.n hWEach, hWLen]
    have hT : (x.wotsSig.flatten ++ x.authPath.flatten).take (p.ell * p.n) = x.wotsSig.flatten ++ [] := by
      rw [← hWFlatLen, List.take_left, List.append_nil]
    have hD : (x.wotsSig.flatten ++ x.authPath.flatten).drop (p.ell * p.n) = x.authPath.flatten ++ [] := by
      rw [← hWFlatLen, List.drop_left, List.append_nil]
    rw [hT, hD]
    have hSW := (splitByteChunks_flatten p.n x.wotsSig [] hWEach).1
    have hSA := (splitByteChunks_flatten p.n x.authPath [] hApEach).1
    rw [hWLen] at hSW
    rw [hApLen] at hSA
    rw [hSW, hSA]
  cases sig
  simp only [SlhSignature.mk.injEq]
  exact ⟨trivial, hForsRec, hHtRec⟩

theorem slhSignInternal_wellTyped (p : Fips205Params) (msgPrime : List UInt8)
    (sk : SlhSecretKey) (optRand : List UInt8) :
    (slhSignInternal p msgPrime sk optRand).WellTyped p := by
  unfold slhSignInternal SlhSignature.WellTyped
  dsimp only
  let split := fipsSplitDigest p (fipsHMsg p.m (fipsPrfMsg p.n sk.skPrf optRand msgPrime) sk.pkSeed sk.pkRoot msgPrime)
  refine ⟨shake256Xof_length p.n _, by simp [fipsForsSign], ?_, ?_, ?_⟩
  · intro f hf
    simp only [fipsForsSign, List.mem_map] at hf
    obtain ⟨j, _, rfl⟩ := hf
    refine ⟨fipsPrf_length _ _ _ _, fipsForsAuthPath_length _ _ _ _ _ _ _ _, ?_⟩
    intro u hu
    have hAuthEach : ∀ (z ni li : Nat) (v : List UInt8),
        v ∈ fipsForsAuthPath p sk.skSeed sk.pkSeed split.2.1 split.2.2 z ni li → v.length = p.n := by
      intro z; induction z with
      | zero => intros _ _ _ hv; cases hv
      | succ z ih =>
        intro ni li v hv
        have hNodeL : ∀ (zz m : Nat), (fipsForsNode p sk.skSeed sk.pkSeed split.2.1 split.2.2 zz m).length = p.n := by
          intro zz; induction zz <;> intro _ <;> simp [fipsForsNode]
        simp only [fipsForsAuthPath] at hv
        split at hv <;>
        · rw [List.mem_append] at hv
          rcases hv with hL | hR
          · exact ih _ _ v hL
          · rw [List.mem_singleton] at hR; subst hR; exact hNodeL _ _
    exact hAuthEach _ _ _ u hu
  · exact fipsHtSignAux_length p sk.skSeed sk.pkSeed p.d 0 _ _ _
  · have hHtMem : ∀ (rem layer it il : Nat) (cm : List UInt8) (x : FipsXmssSig),
        x ∈ fipsHtSignAux p sk.skSeed sk.pkSeed layer it il cm rem →
        x.wotsSig.length = p.ell ∧ (∀ w ∈ x.wotsSig, w.length = p.n) ∧
        x.authPath.length = p.hp ∧ (∀ u ∈ x.authPath, u.length = p.n) := by
      intro rem; induction rem with
      | zero => intros _ _ _ _ _ hx; cases hx
      | succ rem ih =>
        intro layer it il cm x hx
        simp only [fipsHtSignAux, List.mem_cons] at hx
        rcases hx with rfl | hTl
        · simp only [fipsXmssSign]
          refine ⟨by simp [fipsWotsSign], ?_, fipsXmssAuthPath_length _ _ _ _ _ _ _ _, ?_⟩
          · intro w hw
            simp only [fipsWotsSign, List.mem_map] at hw
            obtain ⟨i, _, rfl⟩ := hw
            exact fipsChain_length _ _ _ _ _ _ _ _ _ (fipsPrf_length _ _ _ _)
          · have hXAuthEach : ∀ (z ni li : Nat) (v : List UInt8),
                v ∈ fipsXmssAuthPath p sk.skSeed sk.pkSeed layer it z ni li → v.length = p.n := by
              intro z; induction z with
              | zero => intros _ _ _ hv; cases hv
              | succ z ihz =>
                intro ni li v hv
                have hNL : ∀ (zz m : Nat), (fipsXmssNode p sk.skSeed sk.pkSeed layer it zz m).length = p.n := by
                  intro zz; induction zz <;> intro _ <;> simp [fipsXmssNode, fipsWotsPkGen]
                simp only [fipsXmssAuthPath] at hv
                split at hv <;>
                · rw [List.mem_append] at hv
                  rcases hv with hL | hR
                  · exact ihz _ _ v hL
                  · rw [List.mem_singleton] at hR; subst hR; exact hNL _ _
            exact fun u hu => hXAuthEach _ _ _ u hu
        · exact ih _ _ _ _ x hTl
    exact fun x hx => hHtMem p.d 0 _ _ _ x hx

/-- Pack a `List UInt8` onto a network `ByteArray` wire and unpack back (`unpackWireBytes (packWireBytes bs) = bs`). -/
@[expose] def packWireBytes (bs : List UInt8) : ByteArray :=
  ByteArray.mk bs.toArray

@[expose] def unpackWireBytes (ba : ByteArray) : List UInt8 :=
  ba.data.toList

@[simp] theorem unpackWireBytes_packWireBytes (bs : List UInt8) :
    unpackWireBytes (packWireBytes bs) = bs := by
  rfl

/-- Replicated 2-of-3 secret key share held by party `i ∈ {0, 1, 2}`:
    each party holds ONLY 2 of the 3 byte shares `(seedA, seedB)` and `(prfA, prfB)`. -/
structure RssPartyKeyShare where
  seedFirst  : List UInt8
  seedSecond : List UInt8
  prfFirst   : List UInt8
  prfSecond  : List UInt8
  deriving DecidableEq, Repr

/-- The two honest parties `(hA, hB)` complementary to a single static corrupt party `cIdx : Fin 3`,
    and the corresponding `RssQuorum` (`p12` for `cIdx = 0`, `p20` for `cIdx = 1`, `p01` for `cIdx = 2`). -/
def honestPairForCorrupt (cIdx : Fin 3) : Nat × Nat × RssQuorum :=
  if cIdx.val == 0 then (1, 2, .p12)
  else if cIdx.val == 1 then (2, 0, .p20)
  else (0, 1, .p01)

/-- Deal honest key shares into `Nat → Option RssPartyKeyShare` (corrupt party receives `none` in honest vault). -/
def dealHonestRssVault (cIdx : Fin 3) (seedSh prfSh : RssByteShares) : Nat → Option RssPartyKeyShare :=
  fun pid =>
    if pid == cIdx.val then none
    else if pid == 0 then some ⟨seedSh.b0, seedSh.b1, prfSh.b0, prfSh.b1⟩
    else if pid == 1 then some ⟨seedSh.b1, seedSh.b2, prfSh.b1, prfSh.b2⟩
    else if pid == 2 then some ⟨seedSh.b2, seedSh.b0, prfSh.b2, prfSh.b0⟩
    else none

/-- Per-session random tape for 3-round interactive RSS `FIPS 205 SLH-DSA`:
    - `nonceA, nonceB` : 64-bit Round-1 hedged coin-toss nonces of the two honest parties;
    - `chiMaskA, chiMaskB` : fresh 64-bit Round-2 Keccak `χ`-row masks;
    - `cutMask0, cutMask1` : fresh `8 * p.sigBytes`-bit Round-3 cut-opening share masks;
    - `gammaBits` : 128-bit active consistency / `BDOZ` batch evaluation challenge in `Tower128`. -/
structure RssSlhSessionTape (sigBytes : Nat) where
  nonceA    : BitVec 64
  nonceB    : BitVec 64
  chiMaskA  : BitVec 64
  chiMaskB  : BitVec 64
  cutMask0  : BitVec (8 * sigBytes)
  cutMask1  : BitVec (8 * sigBytes)
  gammaBits : BitVec 128
  deriving DecidableEq, Repr

/-- Cardinality of the per-session pad space (excluding the `2^128` challenge `gammaBits`). -/
def rssPadSessionCard (sigBytes : Nat) : Nat :=
  (2 ^ 64) * ((2 ^ 64) * ((2 ^ 64) * ((2 ^ 64) * ((2 ^ (8 * sigBytes)) * (2 ^ (8 * sigBytes))))))

/-- Cardinality of one full session tape (`padSessionCard * 2^128`). -/
def rssFullSessionCard (sigBytes : Nat) : Nat :=
  rssPadSessionCard sigBytes * (2 ^ 128)

/-- Cardinality of the `Q_s`-session multi-round random tape space. -/
def rssMultiSessionCard (sigBytes : Nat) : Nat → Nat
  | 0 => 1
  | s + 1 => rssFullSessionCard sigBytes * rssMultiSessionCard sigBytes s

theorem rssPadSessionCard_pos (sigBytes : Nat) : 0 < rssPadSessionCard sigBytes := by
  unfold rssPadSessionCard
  exact Nat.mul_pos (Nat.two_pow_pos _)
    (Nat.mul_pos (Nat.two_pow_pos _)
      (Nat.mul_pos (Nat.two_pow_pos _)
        (Nat.mul_pos (Nat.two_pow_pos _)
          (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)))))

theorem rssFullSessionCard_pos (sigBytes : Nat) : 0 < rssFullSessionCard sigBytes :=
  Nat.mul_pos (rssPadSessionCard_pos sigBytes) (Nat.two_pow_pos 128)

theorem rssMultiSessionCard_pos (sigBytes : Nat) : ∀ (s : Nat), 0 < rssMultiSessionCard sigBytes s
  | 0 => Nat.zero_lt_one
  | s + 1 => Nat.mul_pos (rssFullSessionCard_pos sigBytes) (rssMultiSessionCard_pos sigBytes s)

/-- Decode a `Fin (rssPadSessionCard L)` index + `Fin (2 ^ 128)` challenge into `RssSlhSessionTape L`. -/
def decodeRssSessionTape (L : Nat) (padIdx : Fin (rssPadSessionCard L)) (gIdx : Fin (2 ^ 128)) :
    RssSlhSessionTape L :=
  let B5 := (2 ^ 64) * ((2 ^ 64) * ((2 ^ 64) * ((2 ^ (8 * L)) * (2 ^ (8 * L)))))
  have hB5 : 0 < B5 := Nat.mul_pos (Nat.two_pow_pos _)
    (Nat.mul_pos (Nat.two_pow_pos _) (Nat.mul_pos (Nat.two_pow_pos _)
      (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))))
  let nA := splitFinLeft hB5 padIdx
  let r5 := splitFinRight hB5 padIdx
  let B4 := (2 ^ 64) * ((2 ^ (8 * L)) * (2 ^ (8 * L)))
  have hB4 : 0 < B4 := Nat.mul_pos (Nat.two_pow_pos _) (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
  let B4Top := (2 ^ 64) * B4
  have hB4Top : 0 < B4Top := Nat.mul_pos (Nat.two_pow_pos _) hB4
  let nB := splitFinLeft hB4Top r5
  let r4 := splitFinRight hB4Top r5
  let cA := splitFinLeft hB4 r4
  let r3 := splitFinRight hB4 r4
  let B2 := (2 ^ (8 * L)) * (2 ^ (8 * L))
  have hB2 : 0 < B2 := Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
  let cB := splitFinLeft hB2 r3
  let r2 := splitFinRight hB2 r3
  let m0 := splitFinLeft (Nat.two_pow_pos (8 * L)) r2
  let m1 := splitFinRight (Nat.two_pow_pos (8 * L)) r2
  { nonceA := BitVec.ofFin nA
    nonceB := BitVec.ofFin nB
    chiMaskA := BitVec.ofFin cA
    chiMaskB := BitVec.ofFin cB
    cutMask0 := BitVec.ofFin m0
    cutMask1 := BitVec.ofFin m1
    gammaBits := BitVec.ofFin gIdx }

def encodeRssPadIdx (L : Nat)
    (nA nB cA cB : BitVec 64) (m0 m1 : BitVec (8 * L)) : Fin (rssPadSessionCard L) :=
  pairFin nA.toFin
    (pairFin nB.toFin
      (pairFin cA.toFin
        (pairFin cB.toFin
          (pairFin m0.toFin m1.toFin))))

private theorem decodeRssSessionTape_encodeRssPadIdx (L : Nat)
    (nA nB cA cB : BitVec 64) (m0 m1 : BitVec (8 * L)) (gIdx : Fin (2 ^ 128)) :
    decodeRssSessionTape L (encodeRssPadIdx L nA nB cA cB m0 m1) gIdx =
      { nonceA := nA, nonceB := nB, chiMaskA := cA, chiMaskB := cB,
        cutMask0 := m0, cutMask1 := m1, gammaBits := BitVec.ofFin gIdx } := by
  unfold decodeRssSessionTape encodeRssPadIdx
  dsimp only
  rw [splitFinLeft_pairFin, splitFinRight_pairFin,
      splitFinLeft_pairFin, splitFinRight_pairFin,
      splitFinLeft_pairFin, splitFinRight_pairFin,
      splitFinLeft_pairFin, splitFinRight_pairFin,
      splitFinLeft_pairFin, splitFinRight_pairFin]

def defaultRssSessionTape (L : Nat) : RssSlhSessionTape L :=
  { nonceA := 0#64, nonceB := 0#64, chiMaskA := 0#64, chiMaskB := 0#64,
    cutMask0 := 0#(8 * L), cutMask1 := 0#(8 * L), gammaBits := 0#128 }

def decodeMultiSessionTapes (L : Nat) :
    (s : Nat) → Fin (rssMultiSessionCard L s) → (Nat → RssSlhSessionTape L)
  | 0, _, _ => defaultRssSessionTape L
  | s + 1, ω, 0 =>
    let cur := splitFinLeft (rssMultiSessionCard_pos L s) ω
    let padIdx := splitFinLeft (Nat.two_pow_pos 128) cur
    let gIdx := splitFinRight (Nat.two_pow_pos 128) cur
    decodeRssSessionTape L padIdx gIdx
  | s + 1, ω, k + 1 =>
    let rest := splitFinRight (rssMultiSessionCard_pos L s) ω
    decodeMultiSessionTapes L s rest k

private theorem fixedBytesToBv_bvToFixedBytes : ∀ (L : Nat) (bv : BitVec (8 * L)),
    fixedBytesToBv L (bvToFixedBytes L bv) = bv
  | 0, _ => by apply BitVec.eq_of_getLsbD_eq; intro i hi; simp at hi
  | L + 1, bv => by
    simp only [bvToFixedBytes, fixedBytesToBv]
    rw [fixedBytesToBv_bvToFixedBytes L (bv.extractLsb' 8 (8 * L))]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_cast, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
    by_cases h8 : i < 8
    · simp [h8]
    · have hSub : i - 8 < 8 * L := by omega
      have hAdd : 8 + (i - 8) = i := by omega
      simp [h8, hSub, hAdd]

/-- Pack/unpack `Tower128` wire deviation elements (`16` bytes each) on the Round-2 wire. -/
def encodeTower128Wire (x : Tower128) : List UInt8 :=
  bvToFixedBytes 16 ((packTower 7 x).cast rfl)

def decodeTower128Wire (bs : List UInt8) : Tower128 :=
  unpackTower 7 ((fixedBytesToBv 16 bs).cast rfl)

theorem decodeTower128Wire_encodeTower128Wire (x : Tower128) :
    decodeTower128Wire (encodeTower128Wire x) = x := by
  unfold decodeTower128Wire encodeTower128Wire
  rw [fixedBytesToBv_bvToFixedBytes 16]
  exact unpackTower_packTower 7 x

/-- Parse up to `deg` 16-byte `Tower128` wire deviations following an 8-byte Round-1 nonce opening. -/
def parseCorruptRound2Wire (deg : Nat) (wire : ByteArray) : Option (List UInt8 × List Tower128) :=
  let raw := unpackWireBytes wire
  if raw.length < 8 then none
  else
    let nonceC := raw.take 8
    let rem := raw.drop 8
    let numDeltas := Nat.min deg (rem.length / 16)
    let chunks := splitByteChunks 16 numDeltas rem
    some (nonceC, chunks.map decodeTower128Wire)

theorem parseCorruptRound2Wire_length_le (deg : Nat) (wire : ByteArray)
    {nonceC : List UInt8} {deltas : List Tower128}
    (hParse : parseCorruptRound2Wire deg wire = some (nonceC, deltas)) :
    deltas.length ≤ deg := by
  unfold parseCorruptRound2Wire at hParse
  dsimp only at hParse
  split at hParse
  · cases hParse
  · injection hParse with hPair
    rcases Prod.mk.inj hPair with ⟨_, rfl⟩
    simp only [List.length_map, splitByteChunks_length]
    exact Nat.min_le_left _ _

/-- Domain-separated Round-1 `SHAKE256` hedged-nonce commitment (`32` bytes). -/
def round1NonceCommit (pk : SlhPublicKey) (req : SessionScheduleReq) (cursor : Nat)
    (partyId : Nat) (nonceBytes : List UInt8) : ByteArray :=
  let hdr : List UInt8 :=
    (0xA1 : UInt8) :: UInt8.ofNat partyId :: UInt8.ofNat req.sessionId ::
      UInt8.ofNat req.reqEpoch :: UInt8.ofNat cursor ::
      (pk.pkSeed ++ pk.pkRoot ++ req.msg ++ req.optRand ++ nonceBytes)
  packWireBytes (shake256Xof 32 hdr)

/-- Canonical digests bound in `WalLatchState` for public key `pk` and scheduled request `req`. -/
def slhPkDigest (pk : SlhPublicKey) : List UInt8 :=
  shake256Xof 32 ((0xD0 : UInt8) :: (pk.pkSeed ++ pk.pkRoot))

def slhReqDigest (req : SessionScheduleReq) : List UInt8 :=
  let framed := (0xD1 : UInt8) :: UInt8.ofNat req.optRand.length :: (req.optRand ++ req.msg)
  framed ++ shake256Xof 32 framed

private theorem byteArray_bne_self (b : ByteArray) : (b != b) = false := by
  unfold bne
  change (!(b.data == b.data)) = false
  rw [beq_self_eq_true]
  rfl

private theorem drop_append_of_length_eq {α : Type} {xs ys : List α} {n : Nat}
    (h : xs.length = n) : (xs ++ ys).drop n = ys := by
  subst h
  exact List.drop_left

/-- Honest 64-bit Keccak `χ`-row word computed locally from party `pid`'s `RssPartyKeyShare` and `req.msg`
    using the real `rssChiLane0/1/2` operator (`0` secret reconstruction). -/
def computeHonestChiWord (pid : Nat) (sh : RssPartyKeyShare) (msgBytes : List UInt8) : BitVec 64 :=
  let a0 := (fixedBytesToBv 8 (sh.seedFirst.take 8)).toNat.toUInt64
  let a1 := (fixedBytesToBv 8 (sh.seedSecond.take 8)).toNat.toUInt64
  let b0 := (fixedBytesToBv 8 (sh.prfFirst.take 8)).toNat.toUInt64
  let b1 := (fixedBytesToBv 8 (sh.prfSecond.take 8)).toNat.toUInt64
  let mWord := (fixedBytesToBv 8 (msgBytes.take 8)).toNat.toUInt64
  let lane :=
    if pid == 0 then rssChiLane0 a0 a1 b0 b1 mWord 0 0 0
    else if pid == 1 then rssChiLane1 a0 a1 b0 b1 mWord 0 0 0
    else rssChiLane2 a0 a1 b0 b1 mWord 0 0 0
  lane.toBitVec

/-- Replicated `FLNW17` byte-stream cross-check over all `L` cut-opening bytes (`verifyRssActiveOpen` lifted bytewise). -/
def verifyRssActiveOpenBytes (L : Nat)
    (p0_b0 p0_b1 p1_b1 p1_b2 p2_b2 p2_b0 : List UInt8) : Option (List UInt8) :=
  if p0_b0.length == L && p0_b1.length == L &&
     p1_b1.length == L && p1_b2.length == L &&
     p2_b2.length == L && p2_b0.length == L &&
     decide (p0_b0 = p2_b0) && decide (p0_b1 = p1_b1) && decide (p1_b2 = p2_b2) then
    some (reconstructRssBytes ⟨p0_b0, p1_b1, p2_b2⟩)
  else
    none

/-- Intermediate Round-1 state carried identically by honest parties and `Sim_RssSlh`. -/
structure RssRound1State where
  cursor : Nat
  nonceA : BitVec 64
  nonceB : BitVec 64
  deriving DecidableEq, Repr

/-- Intermediate Round-2 state carried into `preCutBarrier`. -/
structure RssRound2State where
  cursor       : Nat
  corrR1Commit : ByteArray
  nonceA       : BitVec 64
  nonceB       : BitVec 64
  gammaBits    : BitVec 128
  deriving DecidableEq

/-- Intermediate Round-3 state carried after `preCutBarrier` succeeds. -/
structure RssRound3State where
  deltas    : List Tower128
  cutShares : RssByteShares
  deriving DecidableEq

/-- Deterministic zero-seed tape for `mkRssSlhMpcOracles` (internal shares re-masked at cut boundary by `cutMask0, cutMask1`). -/
def constZeroRssSeedTape : Nat → Nat → Nat → Nat → RssPrfZeroSeeds :=
  fun _ _ _ _ => zeroRssSeeds

/-- Extract the two honest parties' `(seedViews, prfViews)` and secret-dependent cut tag from the vault. -/
def extractHonestQuorumViews (L : Nat) (cIdx : Fin 3)
    (shares : Nat → Option RssPartyKeyShare) :
    Option (((List UInt8 × List UInt8) × (List UInt8 × List UInt8)) ×
            ((List UInt8 × List UInt8) × (List UInt8 × List UInt8)) ×
            BitVec (8 * L) × BitVec (8 * L)) :=
  let (hA, hB, _) := honestPairForCorrupt cIdx
  match shares hA, shares hB with
  | some shA, some shB =>
    let rawTag0 := fixedBytesToBv L (shake256Xof L ((0xB0 : UInt8) :: shA.seedFirst))
    let rawTag1 := fixedBytesToBv L (shake256Xof L ((0xB1 : UInt8) :: shB.prfFirst))
    some (((shA.seedFirst, shA.seedSecond), (shB.seedFirst, shB.seedSecond)),
          ((shA.prfFirst, shA.prfSecond), (shB.prfFirst, shB.prfSecond)),
          rawTag0, rawTag1)
  | _, _ => none

/-- Format the two honest parties' Round-3 `FLNW17` cut-opening messages from 3-way `cutSh : RssByteShares`,
    and verify them against the corrupt party's Round-3 `ByteArray` `corrR3`. -/
def buildHonestRound3Msgs (cIdx : Fin 3) (cutSh : RssByteShares) : List (Nat × ByteArray) :=
  if cIdx.val == 0 then
    [(1, packWireBytes (cutSh.b1 ++ cutSh.b2)), (2, packWireBytes (cutSh.b2 ++ cutSh.b0))]
  else if cIdx.val == 1 then
    [(2, packWireBytes (cutSh.b2 ++ cutSh.b0)), (0, packWireBytes (cutSh.b0 ++ cutSh.b1))]
  else
    [(0, packWireBytes (cutSh.b0 ++ cutSh.b1)), (1, packWireBytes (cutSh.b1 ++ cutSh.b2))]

def checkRound3ActiveOpen (L : Nat) (cIdx : Fin 3) (cutSh : RssByteShares)
    (corrMsgs : List (Nat × ByteArray)) : Option (List UInt8) :=
  match corrMsgs.find? (fun pr => pr.1 == cIdx.val) with
  | none => none
  | some (_, corrWire) =>
    let raw := unpackWireBytes corrWire
    let cFirst := raw.take L
    let cSecond := raw.drop L
    if cIdx.val == 0 then
      verifyRssActiveOpenBytes L cFirst cSecond cutSh.b1 cutSh.b2 cutSh.b2 cutSh.b0
    else if cIdx.val == 1 then
      verifyRssActiveOpenBytes L cutSh.b0 cutSh.b1 cFirst cSecond cutSh.b2 cutSh.b0
    else
      verifyRssActiveOpenBytes L cutSh.b0 cutSh.b1 cutSh.b1 cutSh.b2 cFirst cSecond

/-- Flip the first byte by `0x01` when an active wire deviation `∃ d ∈ deltas, d ≠ 0` slips past `preCutBarrier`. -/
def injectCutFaultIfNonzero (L : Nat) (deltas : List Tower128) (bs : List UInt8) : List UInt8 :=
  if deltas.any (fun d => decide (d ≠ towerZero 7)) then
    xorByteStream bs ((0x01 : UInt8) :: List.replicate (L - 1) 0)
  else
    bs

/-- Shared Round-1 commitment check used identically by `rssSlhInteractiveProtocol` and `Sim_RssSlh`. -/
def sharedVerifyRound1 (cIdx : Fin 3) (r1St : RssRound1State)
    (corrR1 : List (Nat × ByteArray)) : PSum (AbortReason × Bool) RssRound2State :=
  match corrR1.find? (fun pr => pr.1 == cIdx.val) with
  | none => .inl (.round1CommitMismatch cIdx.val, false)
  | some (_, cWire) =>
    if (unpackWireBytes cWire).length != 32 then .inl (.round1CommitMismatch cIdx.val, false)
    else .inr { cursor := r1St.cursor, corrR1Commit := cWire,
                nonceA := r1St.nonceA, nonceB := r1St.nonceB, gammaBits := 0#128 }

/-- **Mandatory Pre-Cut Consistency Barrier (`sharedPreCutBarrier`)**:
    Verifies Round-1 commitment binding AND `GF(2^128)` (`Tower128`) batch consistency polynomial
    `batchDeviationPoly deltas gamma == towerZero 7` strictly BEFORE Round-3 cut openings can run! -/
def sharedPreCutBarrier (cIdx : Fin 3) (deg : Nat) (pk : SlhPublicKey)
    (req : SessionScheduleReq) (r2St : RssRound2State)
    (corrR2 : List (Nat × ByteArray)) : PSum AbortReason RssRound3State :=
  match corrR2.find? (fun pr => pr.1 == cIdx.val) with
  | none => .inl (.round1CommitMismatch cIdx.val)
  | some (_, cWire2) =>
    match parseCorruptRound2Wire deg cWire2 with
    | none => .inl (.round1CommitMismatch cIdx.val)
    | some (nonceC, deltas) =>
      if round1NonceCommit pk req r2St.cursor cIdx.val nonceC != r2St.corrR1Commit then
        .inl (.round1CommitMismatch cIdx.val)
      else if !(batchDeviationPoly deltas (unpackTower 7 r2St.gammaBits) == towerZero 7) then
        .inl .activeConsistencyFailed
      else
        .inr { deltas := deltas, cutShares := ⟨[], [], []⟩ }

/-- Shared Round-3 `FLNW17` cross-check + NIST FIPS 205 signature assembly & verification gate. -/
def sharedFinalizeCutOpen (p : Fips205Params) (cIdx : Fin 3)
    (pk : SlhPublicKey) (req : SessionScheduleReq)
    (cutShares : RssByteShares) (corrR3 : List (Nat × ByteArray)) :
    PSum AbortReason ByteArray :=
  match checkRound3ActiveOpen p.sigBytes cIdx cutShares corrR3 with
  | none => .inl (.cutOpenMismatch cIdx.val)
  | some openedBytes =>
    match decodeSlhSig p openedBytes with
    | none => .inl (.cutOpenMismatch cIdx.val)
    | some sig =>
      if slhVerifyInternal p req.msg sig pk then
        .inr (packWireBytes openedBytes)
      else
        .inl (.cutOpenMismatch cIdx.val)

/-- **Concrete 3-Round Interactive 2-of-3 RSS `FIPS 205 SLH-DSA` Protocol (`rssSlhInteractiveProtocol`)**
    instantiating `InteractiveThresholdProtocol` from `Qsag.InteractiveUcEngine`. -/
@[expose] def rssSlhInteractiveProtocol (p : Fips205Params) (cIdx : Fin 3) (deg : Nat) :
    InteractiveThresholdProtocol SlhPublicKey RssPartyKeyShare (RssSlhSessionTape p.sigBytes)
      RssRound1State RssRound2State RssRound3State where
  pkDigestOf := slhPkDigest
  msgDigestOf := slhReqDigest
  honestRound1 := fun pk _corrupt req cursor _shares tape =>
    let (hA, hB, _) := honestPairForCorrupt cIdx
    let mA := round1NonceCommit pk req cursor hA (bvToFixedBytes 8 tape.nonceA)
    let mB := round1NonceCommit pk req cursor hB (bvToFixedBytes 8 tape.nonceB)
    ([(hA, mA), (hB, mB)], { cursor := cursor, nonceA := tape.nonceA, nonceB := tape.nonceB })
  verifyRound1 := fun _pk _req r1St _honR1 corrR1 =>
    sharedVerifyRound1 cIdx r1St corrR1
  honestRound2 := fun _pk _corrupt req r2Init shares tape =>
    let (hA, hB, _) := honestPairForCorrupt cIdx
    let wA := match shares hA with
              | some shA => computeHonestChiWord hA shA req.msg
              | none => 0#64
    let wB := match shares hB with
              | some shB => computeHonestChiWord hB shB req.msg
              | none => 0#64
    let wireA := packWireBytes (bvToFixedBytes 8 r2Init.nonceA ++ bvToFixedBytes 8 (wA ^^^ tape.chiMaskA))
    let wireB := packWireBytes (bvToFixedBytes 8 r2Init.nonceB ++ bvToFixedBytes 8 (wB ^^^ tape.chiMaskB))
    ([(hA, wireA), (hB, wireB)], { r2Init with gammaBits := tape.gammaBits })
  preCutBarrier := fun pk req r2St _honR2 corrR2 =>
    sharedPreCutBarrier cIdx deg pk req r2St corrR2
  honestRound3 := fun pk _corrupt req r3Init shares tape =>
    let (_, _, q) := honestPairForCorrupt cIdx
    match extractHonestQuorumViews p.sigBytes cIdx shares with
    | none => ([], { r3Init with cutShares := ⟨[], [], []⟩ })
    | some (seedViews, prfViews, rawTag0, rawTag1) =>
      let trueSigBytes := rssQuorumSlhSignBytes p q seedViews prfViews pk.pkSeed
                            constZeroRssSeedTape req.msg req.optRand
      let faultedBytes := injectCutFaultIfNonzero p.sigBytes r3Init.deltas trueSigBytes
      let cutB0 := bvToFixedBytes p.sigBytes (rawTag0 ^^^ tape.cutMask0)
      let cutB1 := bvToFixedBytes p.sigBytes (rawTag1 ^^^ tape.cutMask1)
      let cutB2 := xorByteStream faultedBytes (xorByteStream cutB0 cutB1)
      let cutSh : RssByteShares := ⟨cutB0, cutB1, cutB2⟩
      (buildHonestRound3Msgs cIdx cutSh, { r3Init with cutShares := cutSh })
  finalizeCutOpen := fun pk req r3St _honR3 corrR3 =>
    sharedFinalizeCutOpen p cIdx pk req r3St.cutShares corrR3

/-- **Explicit Black-Box UC Simulator (`Sim_RssSlh`)**:
    Receives **ONLY** public parameters `(p, cIdx, deg)`, public key `pk : SlhPublicKey`, and (upon
    `t`-quorum approval + `preCutBarrier` pass in `IdealTsig`) the ideal signature `idealSigBytes : ByteArray`!
    `Sim_RssSlh` has **ZERO** access to `SlhSecretKey`, `skSeed`, `skPrf`, or `RssPartyKeyShare`. -/
@[expose] def Sim_RssSlh (p : Fips205Params) (cIdx : Fin 3) (deg : Nat) :
    BlackBoxUcSimulator SlhPublicKey (RssSlhSessionTape p.sigBytes)
      RssRound1State RssRound2State RssRound3State where
  pkDigestOf := slhPkDigest
  msgDigestOf := slhReqDigest
  simRound1 := fun pk _corrupt req cursor tape =>
    let (hA, hB, _) := honestPairForCorrupt cIdx
    let mA := round1NonceCommit pk req cursor hA (bvToFixedBytes 8 tape.nonceA)
    let mB := round1NonceCommit pk req cursor hB (bvToFixedBytes 8 tape.nonceB)
    ([(hA, mA), (hB, mB)], { cursor := cursor, nonceA := tape.nonceA, nonceB := tape.nonceB })
  simVerifyRound1 := fun _pk _req r1St _honR1 corrR1 =>
    sharedVerifyRound1 cIdx r1St corrR1
  simRound2 := fun _pk _corrupt _req r2Init tape =>
    let (hA, hB, _) := honestPairForCorrupt cIdx
    let wireA := packWireBytes (bvToFixedBytes 8 r2Init.nonceA ++ bvToFixedBytes 8 tape.chiMaskA)
    let wireB := packWireBytes (bvToFixedBytes 8 r2Init.nonceB ++ bvToFixedBytes 8 tape.chiMaskB)
    ([(hA, wireA), (hB, wireB)], { r2Init with gammaBits := tape.gammaBits })
  simPreCutBarrier := fun pk req r2St _honR2 corrR2 =>
    sharedPreCutBarrier cIdx deg pk req r2St corrR2
  simRound3 := fun _pk _corrupt _req r3Init idealSigBytes tape =>
    let cutB0 := bvToFixedBytes p.sigBytes tape.cutMask0
    let cutB1 := bvToFixedBytes p.sigBytes tape.cutMask1
    let cutB2 := xorByteStream (unpackWireBytes idealSigBytes) (xorByteStream cutB0 cutB1)
    let cutSh : RssByteShares := ⟨cutB0, cutB1, cutB2⟩
    (buildHonestRound3Msgs cIdx cutSh, { r3Init with cutShares := cutSh })
  simFinalizeCut := fun pk req r3St _idealSigBytes _honR3 corrR3 =>
    sharedFinalizeCutOpen p cIdx pk req r3St.cutShares corrR3

/-! ## 3. Crown-Jewel Theorem 1: Whole-Transcript Multi-Session UC Indistinguishability
    (`rss_slh_real_ideal_view_indistinguishable` & `spdz_shamir_tower128_masked_view_stat_dist_zero`) -/

/-- Ideal signing oracle for `IdealTsig` instantiated with NIST `FIPS 205` `slhSignInternal`. -/
def slhIdealSignOracle (p : Fips205Params) (sk : SlhSecretKey) : SessionScheduleReq → ByteArray :=
  fun req => packWireBytes (encodeSlhSig (slhSignInternal p req.msg sk req.optRand))

/-- Identity `SimpleEquiv` on `Fin n`. -/
def idFinEquiv (n : Nat) : SimpleEquiv (Fin n) (Fin n) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl

/-- Decode a single `Fin (rssFullSessionCard L)` index into `RssSlhSessionTape L`. -/
def decodeSingleFullTape (L : Nat) (cur : Fin (rssFullSessionCard L)) : RssSlhSessionTape L :=
  let padIdx := splitFinLeft (Nat.two_pow_pos 128) cur
  let gIdx := splitFinRight (Nat.two_pow_pos 128) cur
  decodeRssSessionTape L padIdx gIdx

/-- Secret-dependent session mask shifts `(wA, wB, rawTag0, rawTag1)` for one scheduled session. -/
def honestSessionShifts (L : Nat) (cIdx : Fin 3)
    (shares : Nat → Option RssPartyKeyShare) (req : SessionScheduleReq) :
    BitVec 64 × BitVec 64 × BitVec (8 * L) × BitVec (8 * L) :=
  let (hA, hB, _) := honestPairForCorrupt cIdx
  let wA := match shares hA with
            | some shA => computeHonestChiWord hA shA req.msg
            | none => 0#64
  let wB := match shares hB with
            | some shB => computeHonestChiWord hB shB req.msg
            | none => 0#64
  match extractHonestQuorumViews L cIdx shares with
  | some (_, _, rawTag0, rawTag1) => (wA, wB, rawTag0, rawTag1)
  | none => (wA, wB, 0#(8 * L), 0#(8 * L))

/-- Measure-preserving XOR pad bijection on `Fin (rssPadSessionCard L)`:
    keeps `(nonceA, nonceB)` fixed and shifts `(chiMaskA, chiMaskB, cutMask0, cutMask1)` by
    `(wA, wB, rawTag0, rawTag1)`. -/
def sessionPadXorEquiv (L : Nat)
    (wA wB : BitVec 64) (rawTag0 rawTag1 : BitVec (8 * L)) :
    SimpleEquiv (Fin (rssPadSessionCard L)) (Fin (rssPadSessionCard L)) :=
  let h1 : 0 < 2 ^ (8 * L) := Nat.two_pow_pos (8 * L)
  let h2 : 0 < (2 ^ (8 * L)) * (2 ^ (8 * L)) := Nat.mul_pos h1 h1
  let h3 : 0 < (2 ^ 64) * ((2 ^ (8 * L)) * (2 ^ (8 * L))) := Nat.mul_pos (Nat.two_pow_pos 64) h2
  let h4 : 0 < (2 ^ 64) * ((2 ^ 64) * ((2 ^ (8 * L)) * (2 ^ (8 * L)))) := Nat.mul_pos (Nat.two_pow_pos 64) h3
  let h5 : 0 < (2 ^ 64) * ((2 ^ 64) * ((2 ^ 64) * ((2 ^ (8 * L)) * (2 ^ (8 * L))))) := Nat.mul_pos (Nat.two_pow_pos 64) h4
  depProdFinEquiv h5 (idFinEquiv (2 ^ 64)) (fun _ =>
    depProdFinEquiv h4 (idFinEquiv (2 ^ 64)) (fun _ =>
      depProdFinEquiv h3 (finBitVecXorEquiv 64 wA) (fun _ =>
        depProdFinEquiv h2 (finBitVecXorEquiv 64 wB) (fun _ =>
          depProdFinEquiv h1 (finBitVecXorEquiv (8 * L) rawTag0) (fun _ =>
            finBitVecXorEquiv (8 * L) rawTag1)))))

/-- Measure-preserving XOR bijection on one full session tape `Fin (rssFullSessionCard L)`,
    leaving `gammaBits : BitVec 128` invariant. -/
def sessionFullTapeXorEquiv (L : Nat)
    (wA wB : BitVec 64) (rawTag0 rawTag1 : BitVec (8 * L)) :
    SimpleEquiv (Fin (rssFullSessionCard L)) (Fin (rssFullSessionCard L)) :=
  depProdFinEquiv (Nat.two_pow_pos 128)
    (sessionPadXorEquiv L wA wB rawTag0 rawTag1)
    (fun _ => idFinEquiv (2 ^ 128))

private theorem decodeSingleFullTape_sessionFullTapeXorEquiv (L : Nat)
    (wA wB : BitVec 64) (rawTag0 rawTag1 : BitVec (8 * L))
    (cur : Fin (rssFullSessionCard L)) :
    let t := decodeSingleFullTape L cur
    decodeSingleFullTape L ((sessionFullTapeXorEquiv L wA wB rawTag0 rawTag1).toFun cur) =
      { nonceA := t.nonceA
        nonceB := t.nonceB
        chiMaskA := wA ^^^ t.chiMaskA
        chiMaskB := wB ^^^ t.chiMaskB
        cutMask0 := rawTag0 ^^^ t.cutMask0
        cutMask1 := rawTag1 ^^^ t.cutMask1
        gammaBits := t.gammaBits } := by
  unfold decodeSingleFullTape sessionFullTapeXorEquiv sessionPadXorEquiv
    rssFullSessionCard rssPadSessionCard
  dsimp only [depProdFinEquiv, idFinEquiv, finBitVecXorEquiv, id]
  rw [splitFinLeft_pairFin, splitFinRight_pairFin]
  unfold decodeRssSessionTape
  dsimp only
  rw [splitFinLeft_pairFin, splitFinRight_pairFin,
      splitFinLeft_pairFin, splitFinRight_pairFin,
      splitFinLeft_pairFin, splitFinRight_pairFin,
      splitFinLeft_pairFin, splitFinRight_pairFin,
      splitFinLeft_pairFin, splitFinRight_pairFin]
  simp only [BitVec.ofFin_toFin]
  rw [BitVec.xor_comm _ wA, BitVec.xor_comm _ wB,
      BitVec.xor_comm _ rawTag0, BitVec.xor_comm _ rawTag1]

/-- Cross-session lockstep state relation coupling `RealClusterState` and `IdealClusterState`. -/
structure RealIdealClusterMatch (cIdx : Fin 3) (seedSh prfSh : RssByteShares)
    (cl : RealClusterState SlhPublicKey RssPartyKeyShare)
    (icl : IdealClusterState SlhPublicKey) : Prop where
  pk_eq         : cl.tsig.pk = icl.tsig.pk
  th_eq         : cl.tsig.threshold = icl.tsig.threshold
  np_eq         : cl.tsig.numParties = icl.tsig.numParties
  corr_eq       : cl.tsig.corruptParties = icl.tsig.corruptParties
  wal_eq        : cl.honestWal = icl.honestWal
  cursor_eq     : cl.maskSessionCursor = icl.maskSessionCursor
  shares_intact : cl.honestWal.poisoned = false →
                    cl.honestShares = dealHonestRssVault cIdx seedSh prfSh

private theorem extractHonestQuorumViews_deal (L : Nat) (cIdx : Fin 3)
    (seedSh prfSh : RssByteShares) (req : SessionScheduleReq) :
    let (_, _, q) := honestPairForCorrupt cIdx
    let (_, _, rawTag0, rawTag1) :=
      honestSessionShifts L cIdx (dealHonestRssVault cIdx seedSh prfSh) req
    extractHonestQuorumViews L cIdx (dealHonestRssVault cIdx seedSh prfSh) =
      some (q.views seedSh, q.views prfSh, rawTag0, rawTag1) := by
  rcases cIdx with ⟨_ | _ | _ | n, hv⟩
  · rfl
  · rfl
  · rfl
  · exact False.elim (Nat.not_lt_zero n (Nat.lt_of_add_lt_add_right hv))

/-- Extract the adversary's non-zero Round-2 wire deviation batch `deltas` (`deltas.length ≤ deg`
    and `∃ d ∈ deltas, d ≠ 0`) when Round-1/quorum/WAL gates pass — notice this depends **ONLY on
    `padIdx : Fin (rssPadSessionCard p.sigBytes)`** and is completely independent of `gIdx : Fin (2 ^ 128)`! -/
def extractSessionNonzeroDeltas {AdvState : Type}
    (p : Fips205Params) (cIdx : Fin 3) (deg : Nat)
    (A : UcRushingAdversary AdvState)
    (cl : RealClusterState SlhPublicKey RssPartyKeyShare)
    (advSt : AdvState)
    (padIdx : Fin (rssPadSessionCard p.sigBytes)) : Option (List Tower128) :=
  let proto := rssSlhInteractiveProtocol p cIdx deg
  let (req, advSt1) := A.scheduleSession advSt
  if !(validThresholdApproval cl.tsig req.honestApprovers) then none
  else
    let pkDig := proto.pkDigestOf cl.tsig.pk
    let msgDig := proto.msgDigestOf req
    match walPreSignStep cl.honestWal pkDig req.reqEpoch msgDig with
    | .err _ _ => none
    | .ok _ (.replayCached _) => none
    | .ok _ (.authorizedFresh _) =>
      let dummyTape := decodeRssSessionTape p.sigBytes padIdx ⟨0, Nat.two_pow_pos 128⟩
      let (honR1, r1St) :=
        proto.honestRound1 cl.tsig.pk cl.tsig.corruptParties req cl.maskSessionCursor cl.honestShares dummyTape
      let (corrR1Fn, advSt2) := A.rushRound1 advSt1 honR1
      let corrR1 := cl.tsig.corruptParties.map (fun c => (c, corrR1Fn c))
      match proto.verifyRound1 cl.tsig.pk req r1St honR1 corrR1 with
      | .inl _ => none
      | .inr r2Init =>
        let (honR2, r2St0) :=
          proto.honestRound2 cl.tsig.pk cl.tsig.corruptParties req r2Init cl.honestShares dummyTape
        let (corrR2Fn, _) := A.rushRound2 advSt2 honR2
        let corrR2 := cl.tsig.corruptParties.map (fun c => (c, corrR2Fn c))
        match corrR2.find? (fun pr => pr.1 == cIdx.val) with
        | none => none
        | some (_, cWire2) =>
          match parseCorruptRound2Wire deg cWire2 with
          | none => none
          | some (nonceC, deltas) =>
            if round1NonceCommit cl.tsig.pk req r2St0.cursor cIdx.val nonceC != r2St0.corrR1Commit then
              none
            else if deltas.any (fun d => decide (d ≠ towerZero 7)) then
              some deltas
            else
              none

private theorem extractSessionNonzeroDeltas_props {AdvState : Type}
    (p : Fips205Params) (cIdx : Fin 3) (deg : Nat)
    (A : UcRushingAdversary AdvState)
    (cl : RealClusterState SlhPublicKey RssPartyKeyShare)
    (advSt : AdvState)
    (padIdx : Fin (rssPadSessionCard p.sigBytes))
    {deltas : List Tower128}
    (hSome : extractSessionNonzeroDeltas p cIdx deg A cl advSt padIdx = some deltas) :
    deltas.length ≤ deg ∧ ∃ d ∈ deltas, d ≠ towerZero 7 := by
  unfold extractSessionNonzeroDeltas at hSome
  dsimp only at hSome
  cases hVal : validThresholdApproval cl.tsig (A.scheduleSession advSt).1.honestApprovers
  · rw [hVal] at hSome; simp at hSome
  · rw [hVal] at hSome
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hSome
    cases hWal : walPreSignStep cl.honestWal
        ((rssSlhInteractiveProtocol p cIdx deg).pkDigestOf cl.tsig.pk)
        (A.scheduleSession advSt).1.reqEpoch
        ((rssSlhInteractiveProtocol p cIdx deg).msgDigestOf (A.scheduleSession advSt).1) with
    | err _ _ => rw [hWal] at hSome; cases hSome
    | ok _ res =>
      rw [hWal] at hSome
      cases res with
      | replayCached _ => cases hSome
      | authorizedFresh _ =>
        dsimp only at hSome
        let dummyTape := decodeRssSessionTape p.sigBytes padIdx ⟨0, Nat.two_pow_pos 128⟩
        let r1Out := (rssSlhInteractiveProtocol p cIdx deg).honestRound1
          cl.tsig.pk cl.tsig.corruptParties (A.scheduleSession advSt).1
          cl.maskSessionCursor cl.honestShares dummyTape
        let corrR1 := cl.tsig.corruptParties.map
          (fun c => (c, (A.rushRound1 (A.scheduleSession advSt).2 r1Out.1).1 c))
        cases hVR1 : (rssSlhInteractiveProtocol p cIdx deg).verifyRound1
            cl.tsig.pk (A.scheduleSession advSt).1 r1Out.2 r1Out.1 corrR1 with
        | inl _ => rw [hVR1] at hSome; cases hSome
        | inr r2Init =>
          rw [hVR1] at hSome
          dsimp only at hSome
          let r2Out := (rssSlhInteractiveProtocol p cIdx deg).honestRound2
            cl.tsig.pk cl.tsig.corruptParties (A.scheduleSession advSt).1
            r2Init cl.honestShares dummyTape
          let advSt2 := (A.rushRound1 (A.scheduleSession advSt).2 r1Out.1).2
          let corrR2 := cl.tsig.corruptParties.map
            (fun c => (c, (A.rushRound2 advSt2 r2Out.1).1 c))
          cases hFind : corrR2.find? (fun pr => pr.1 == cIdx.val) with
          | none => rw [hFind] at hSome; cases hSome
          | some pr =>
            rcases pr with ⟨_, cWire2⟩
            rw [hFind] at hSome
            dsimp only at hSome
            cases hParse : parseCorruptRound2Wire deg cWire2 with
            | none => rw [hParse] at hSome; cases hSome
            | some nd =>
              rcases nd with ⟨nonceC, ds⟩
              rw [hParse] at hSome
              dsimp only at hSome
              cases hCmt : (round1NonceCommit cl.tsig.pk (A.scheduleSession advSt).1
                  r2Out.2.cursor cIdx.val nonceC != r2Out.2.corrR1Commit)
              · rw [hCmt] at hSome
                simp only [Bool.false_eq_true, ↓reduceIte] at hSome
                cases hAny : ds.any (fun d => decide (d ≠ towerZero 7))
                · rw [hAny] at hSome; simp at hSome
                · rw [hAny] at hSome
                  simp only [↓reduceIte, Option.some.injEq] at hSome
                  subst hSome
                  obtain ⟨d, hdMem, hdDec⟩ := List.any_eq_true.mp hAny
                  exact ⟨parseCorruptRound2Wire_length_le deg cWire2 hParse,
                         d, hdMem, of_decide_eq_true hdDec⟩
              · rw [hCmt] at hSome; simp at hSome

/-- Single-session `GF(2^128)` (`Tower128`) Schwartz-Zippel bad hit indicator:
    `true` iff the rushing adversary submits a non-zero wire deviation `deltas` in Round 2 AND
    the independent uniform 128-bit challenge `gIdx` hits a root of `batchDeviationPoly deltas`. -/
def sessionBadHit {AdvState : Type}
    (p : Fips205Params) (cIdx : Fin 3) (deg : Nat)
    (A : UcRushingAdversary AdvState)
    (cl : RealClusterState SlhPublicKey RssPartyKeyShare)
    (advSt : AdvState)
    (cur : Fin (rssFullSessionCard p.sigBytes)) : Bool :=
  let padIdx := splitFinLeft (Nat.two_pow_pos 128) cur
  let gIdx := splitFinRight (Nat.two_pow_pos 128) cur
  match extractSessionNonzeroDeltas p cIdx deg A cl advSt padIdx with
  | none => false
  | some deltas => batchDeviationPoly deltas (unpackTower 7 (BitVec.ofFin gIdx)) == towerZero 7

/-- Single-session Schwartz-Zippel bad-event sum bound:
    `badCount_1 ≤ rssPadSessionCard p.sigBytes * deg`, hence `badCount_1 * 2^128 ≤ deg * rssFullSessionCard`. -/
private theorem sessionBadHit_finSum_le {AdvState : Type}
    (p : Fips205Params) (cIdx : Fin 3) (deg : Nat)
    (A : UcRushingAdversary AdvState)
    (cl : RealClusterState SlhPublicKey RssPartyKeyShare)
    (advSt : AdvState) :
    finSum (rssFullSessionCard p.sigBytes)
      (fun cur => if sessionBadHit p cIdx deg A cl advSt cur then 1 else 0) ≤
    rssPadSessionCard p.sigBytes * deg := by
  unfold rssFullSessionCard
  rw [finSum_prod_eq (rssPadSessionCard p.sigBytes) (2 ^ 128)]
  rw [← finSum_const (rssPadSessionCard p.sigBytes) deg]
  apply finSum_le_finSum
  intro padIdx
  have hInner :
      finSum (2 ^ 128) (fun gIdx =>
        if sessionBadHit p cIdx deg A cl advSt (pairFin padIdx gIdx) then 1 else 0) =
      finSum (2 ^ 128) (fun gIdx =>
        if (match extractSessionNonzeroDeltas p cIdx deg A cl advSt padIdx with
            | none => false
            | some deltas => batchDeviationPoly deltas (unpackTower 7 (BitVec.ofFin gIdx)) == towerZero 7)
        then 1 else 0) := by
    apply finSum_congr
    intro gIdx
    unfold sessionBadHit
    dsimp only
    rw [splitFinLeft_pairFin, splitFinRight_pairFin]
  rw [hInner]
  cases hExt : extractSessionNonzeroDeltas p cIdx deg A cl advSt padIdx with
  | none =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have h0 : finSum (2 ^ 128) (fun _ => 0) = 0 := by rw [finSum_const, Nat.mul_zero]
    rw [h0]
    exact Nat.zero_le deg
  | some deltas =>
    obtain ⟨hLen, hNz⟩ := extractSessionNonzeroDeltas_props p cIdx deg A cl advSt padIdx hExt
    exact tower128_roots_finSum_le deg deltas hLen hNz

/-- Per-session adaptive tape bijection conditioned on `(cl, advSt)`:
    uses `honestSessionShifts` on the scheduled `req` when `cl` and `advSt` run Round 2. -/
def adaptiveSingleSessionEquiv {AdvState : Type}
    (p : Fips205Params) (cIdx : Fin 3)
    (A : UcRushingAdversary AdvState)
    (cl : RealClusterState SlhPublicKey RssPartyKeyShare)
    (advSt : AdvState) :
    SimpleEquiv (Fin (rssFullSessionCard p.sigBytes)) (Fin (rssFullSessionCard p.sigBytes)) :=
  let (req, _) := A.scheduleSession advSt
  let (wA, wB, rawTag0, rawTag1) := honestSessionShifts p.sigBytes cIdx cl.honestShares req
  sessionFullTapeXorEquiv p.sigBytes wA wB rawTag0 rawTag1

private theorem walPreSignStep_authorizedFresh_unpoisoned
    {st wal' : WalLatchState} {pkDig : List UInt8} {ep epOut : Nat} {msgDig : List UInt8}
    (hOk : walPreSignStep st pkDig ep msgDig = .ok wal' (.authorizedFresh epOut)) :
    st.poisoned = false ∧ wal' = st := by
  unfold walPreSignStep at hOk
  cases hp : st.poisoned
  · simp only [hp, Bool.false_eq_true, ↓reduceIte] at hOk
    cases hPk : decide (pkDig = st.enrolledPkDigest)
    · rw [hPk] at hOk; simp at hOk
    · rw [hPk] at hOk
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hOk
      cases hLat : st.latchedRecord with
      | none =>
        rw [hLat] at hOk
        cases hEp : (ep == st.nextEpoch)
        · rw [hEp] at hOk; simp at hOk
        · rw [hEp] at hOk
          simp only [↓reduceIte, UcStepOutcome.ok.injEq] at hOk
          exact ⟨rfl, hOk.1.symm⟩
      | some rec0 =>
        rcases rec0 with ⟨ep0, prevMd, prevSig⟩
        rw [hLat] at hOk
        dsimp only at hOk
        cases hHit : (ep == ep0 && decide (msgDig = prevMd))
        · rw [hHit] at hOk
          simp only [Bool.false_eq_true, ↓reduceIte] at hOk
          cases hEp : (ep == st.nextEpoch)
          · rw [hEp] at hOk; simp at hOk
          · rw [hEp] at hOk
            simp only [↓reduceIte, UcStepOutcome.ok.injEq] at hOk
            exact ⟨rfl, hOk.1.symm⟩
        · rw [hHit] at hOk; simp at hOk
  · simp [hp] at hOk

private theorem honestSessionShifts_fst_snd (L : Nat) (cIdx : Fin 3)
    (shares : Nat → Option RssPartyKeyShare) (req : SessionScheduleReq) :
    (honestSessionShifts L cIdx shares req).1 =
      (match shares (honestPairForCorrupt cIdx).1 with
       | some shA => computeHonestChiWord (honestPairForCorrupt cIdx).1 shA req.msg
       | none => 0#64) ∧
    (honestSessionShifts L cIdx shares req).2.1 =
      (match shares (honestPairForCorrupt cIdx).2.1 with
       | some shB => computeHonestChiWord (honestPairForCorrupt cIdx).2.1 shB req.msg
       | none => 0#64) := by
  unfold honestSessionShifts
  dsimp only
  cases extractHonestQuorumViews L cIdx shares <;> exact ⟨rfl, rfl⟩

private theorem dummyTape_fields_eq (L : Nat) (cur : Fin (rssFullSessionCard L)) :
    let padIdx := splitFinLeft (Nat.two_pow_pos 128) cur
    let dummy := decodeRssSessionTape L padIdx ⟨0, Nat.two_pow_pos 128⟩
    let real := decodeSingleFullTape L cur
    dummy.nonceA = real.nonceA ∧
    dummy.nonceB = real.nonceB ∧
    dummy.chiMaskA = real.chiMaskA ∧
    dummy.chiMaskB = real.chiMaskB ∧
    real.gammaBits = BitVec.ofFin (splitFinRight (Nat.two_pow_pos 128) cur) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem sharedPreCutBarrier_extract_eq (cIdx : Fin 3) (deg : Nat) (pk : SlhPublicKey)
    (req : SessionScheduleReq) (r2St : RssRound2State)
    (corrR2 : List (Nat × ByteArray)) (r3Init : RssRound3State)
    (hBar : sharedPreCutBarrier cIdx deg pk req r2St corrR2 = .inr r3Init) :
    (match corrR2.find? (fun pr => pr.1 == cIdx.val) with
     | none => none
     | some (_, cWire2) =>
       match parseCorruptRound2Wire deg cWire2 with
       | none => none
       | some (nonceC, deltas) =>
         if round1NonceCommit pk req r2St.cursor cIdx.val nonceC != r2St.corrR1Commit then none
         else if deltas.any (fun d => decide (d ≠ towerZero 7)) then some deltas
         else none) =
      (if r3Init.deltas.any (fun d => decide (d ≠ towerZero 7)) then some r3Init.deltas else none) ∧
    (batchDeviationPoly r3Init.deltas (unpackTower 7 r2St.gammaBits) == towerZero 7) = true := by
  unfold sharedPreCutBarrier at hBar
  cases hFind : corrR2.find? (fun pr => pr.1 == cIdx.val) with
  | none => rw [hFind] at hBar; cases hBar
  | some pr =>
    rcases pr with ⟨_, cWire2⟩
    rw [hFind] at hBar
    dsimp only at hBar ⊢
    cases hParse : parseCorruptRound2Wire deg cWire2 with
    | none => rw [hParse] at hBar; cases hBar
    | some nd =>
      rcases nd with ⟨nonceC, ds⟩
      rw [hParse] at hBar
      dsimp only at hBar ⊢
      cases hCmt : (round1NonceCommit pk req r2St.cursor cIdx.val nonceC != r2St.corrR1Commit)
      · rw [hCmt] at hBar
        simp only [Bool.false_eq_true, ↓reduceIte] at hBar ⊢
        cases hBatch : (batchDeviationPoly ds (unpackTower 7 r2St.gammaBits) == towerZero 7)
        · rw [hBatch] at hBar; simp at hBar
        · rw [hBatch] at hBar
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hBar
          injection hBar with hEq
          have hDs : ds = r3Init.deltas := congrArg RssRound3State.deltas hEq
          subst hDs
          exact ⟨rfl, hBatch⟩
      · rw [hCmt] at hBar; simp at hBar

/-- **Core Single-Session Lockstep Equivalence (`execRealSession_eq_execIdealSession_unless_bad`)**:
    Under `RealIdealClusterMatch cIdx seedSh prfSh cl icl`, whenever `sessionBadHit ... cur = false`,
    `execRealSession` on `decodeSingleFullTape L cur` and `execIdealSession` on
    `decodeSingleFullTape L ((adaptiveSingleSessionEquiv ...).toFun cur)` produce:
    1. **Bit-for-bit identical** `(advSt', SessionWireRecord)` (including every wire `ByteArray` and
       exact `AbortReason`), AND
    2. Successor states `(cl', icl')` preserving `RealIdealClusterMatch`! -/
theorem execRealSession_eq_execIdealSession_unless_bad {AdvState : Type}
    (p : Fips205Params) (hWf : p.wellFormed = true)
    (cIdx : Fin 3) (deg : Nat)
    {seedSh prfSh : RssByteShares}
    (hSeedWf : seedSh.WellFormed) (hPrfWf : prfSh.WellFormed)
    (pkSeed : List UInt8)
    (A : UcRushingAdversary AdvState)
    (cl : RealClusterState SlhPublicKey RssPartyKeyShare)
    (icl : IdealClusterState SlhPublicKey)
    (advSt : AdvState)
    (hMatch : RealIdealClusterMatch cIdx seedSh prfSh cl icl)
    (hPkKey : cl.tsig.pk = (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2)
    (cur : Fin (rssFullSessionCard p.sigBytes))
    (hNoBad : sessionBadHit p cIdx deg A cl advSt cur = false) :
    let sk := (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).1
    let tapeReal := decodeSingleFullTape p.sigBytes cur
    let tapeSim := decodeSingleFullTape p.sigBytes
                     ((adaptiveSingleSessionEquiv p cIdx A cl advSt).toFun cur)
    let resR :=
      execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt tapeReal
    let resI :=
      execIdealSession (slhIdealSignOracle p sk) (Sim_RssSlh p cIdx deg) A icl advSt tapeSim
    resR.2.1 = resI.2.1 ∧
    resR.2.2 = resI.2.2 ∧
    resR.1.tsig.pk = cl.tsig.pk ∧
    RealIdealClusterMatch cIdx seedSh prfSh resR.1 resI.1 := by
  rcases hMatch with ⟨hPkEq, hThEq, hNpEq, hCorrEq, hWalEq, hCurEq, hSharesIntact⟩
  have hQuorumEq : ∀ apps, validThresholdApproval cl.tsig apps = validThresholdApproval icl.tsig apps := by
    intro apps
    unfold validThresholdApproval
    rw [hThEq, hNpEq, hCorrEq]
  intro sk tapeReal tapeSim resR resI
  dsimp only [resR, resI]
  unfold execRealSession execIdealSession
  dsimp only
  rw [← hQuorumEq]
  cases hQuorum : validThresholdApproval cl.tsig (A.scheduleSession advSt).1.honestApprovers
  · exact ⟨rfl, rfl, rfl, ⟨hPkEq, hThEq, hNpEq, hCorrEq, hWalEq, hCurEq, hSharesIntact⟩⟩
  · rw [ite_eq_right (by decide : ¬ ((!true) = true)),
        ite_eq_right (by decide : ¬ ((!true) = true))]
    have hPkDigR : (rssSlhInteractiveProtocol p cIdx deg).pkDigestOf = slhPkDigest := rfl
    have hPkDigS : (Sim_RssSlh p cIdx deg).pkDigestOf = slhPkDigest := rfl
    have hMsgDigR : (rssSlhInteractiveProtocol p cIdx deg).msgDigestOf = slhReqDigest := rfl
    have hMsgDigS : (Sim_RssSlh p cIdx deg).msgDigestOf = slhReqDigest := rfl
    rw [hPkDigR, hPkDigS, hMsgDigR, hMsgDigS, ← hWalEq, ← hPkEq]
    cases hWalStep : walPreSignStep cl.honestWal (slhPkDigest cl.tsig.pk)
                       (A.scheduleSession advSt).1.reqEpoch (slhReqDigest (A.scheduleSession advSt).1) with
    | err wal' rej =>
      dsimp only
      refine ⟨rfl, rfl, rfl, ⟨hPkEq, hThEq, hNpEq, hCorrEq, rfl, hCurEq, ?_⟩⟩
      intro hp'
      have hUnfold := hWalStep
      unfold walPreSignStep at hUnfold
      cases hp0 : cl.honestWal.poisoned
      · exact hSharesIntact hp0
      · rw [hp0] at hUnfold
        simp only [↓reduceIte, UcStepOutcome.err.injEq] at hUnfold
        rcases hUnfold with ⟨rfl, _⟩
        rw [hp0] at hp'; cases hp'
    | ok wal' walAuth =>
      cases walAuth with
      | replayCached cachedSig =>
        dsimp only
        refine ⟨rfl, rfl, rfl, ⟨hPkEq, hThEq, hNpEq, hCorrEq, rfl, hCurEq, ?_⟩⟩
        intro hp'
        unfold walPreSignStep at hWalStep
        cases hp0 : cl.honestWal.poisoned
        · exact hSharesIntact hp0
        · simp [hp0] at hWalStep
      | authorizedFresh authEp =>
        obtain ⟨hUnpoisoned, rfl⟩ := walPreSignStep_authorizedFresh_unpoisoned hWalStep
        have hShares : cl.honestShares = dealHonestRssVault cIdx seedSh prfSh :=
          hSharesIntact hUnpoisoned
        let req := (A.scheduleSession advSt).1
        let shifts := honestSessionShifts p.sigBytes cIdx cl.honestShares req
        have hTapeSimEq : tapeSim =
            { nonceA := tapeReal.nonceA
              nonceB := tapeReal.nonceB
              chiMaskA := shifts.1 ^^^ tapeReal.chiMaskA
              chiMaskB := shifts.2.1 ^^^ tapeReal.chiMaskB
              cutMask0 := shifts.2.2.1 ^^^ tapeReal.cutMask0
              cutMask1 := shifts.2.2.2 ^^^ tapeReal.cutMask1
              gammaBits := tapeReal.gammaBits } :=
          decodeSingleFullTape_sessionFullTapeXorEquiv p.sigBytes
            shifts.1 shifts.2.1 shifts.2.2.1 shifts.2.2.2 cur
        have ⟨hSW1, hSW2⟩ := honestSessionShifts_fst_snd p.sigBytes cIdx cl.honestShares req
        unfold rssSlhInteractiveProtocol Sim_RssSlh slhIdealSignOracle
        dsimp only
        rw [← hCurEq, ← hCorrEq, hTapeSimEq]
        dsimp only [shifts]
        rw [hSW1, hSW2]
        cases hVR1 : sharedVerifyRound1 cIdx _ _ with
        | inl p1 =>
          rcases p1 with ⟨r1Err, doPoison⟩
          cases doPoison
          · dsimp only
            exact ⟨rfl, rfl, rfl, ⟨hPkEq, hThEq, hNpEq, hCorrEq, rfl, rfl, fun _ => hShares⟩⟩
          · dsimp only [poisonRealCluster, poisonIdealCluster, walQuarantine]
            exact ⟨rfl, rfl, rfl, ⟨hPkEq, hThEq, hNpEq, hCorrEq, rfl, rfl, fun hp => by cases hp⟩⟩
        | inr r2Init =>
          dsimp only
          cases hBar : sharedPreCutBarrier cIdx deg cl.tsig.pk _ _ _ with
          | inl barrierErr =>
            dsimp only [poisonRealCluster, poisonIdealCluster, walQuarantine]
            exact ⟨rfl, rfl, rfl, ⟨hPkEq, hThEq, hNpEq, hCorrEq, rfl, rfl, fun hp => by cases hp⟩⟩
          | inr r3Init =>
            have hDeltasZero : r3Init.deltas.any (fun d => decide (d ≠ towerZero 7)) = false := by
              by_cases hAny : r3Init.deltas.any (fun d => decide (d ≠ towerZero 7)) = true
              · exfalso
                have hDummy := dummyTape_fields_eq p.sigBytes cur
                have hBadUnf := hNoBad
                unfold sessionBadHit extractSessionNonzeroDeltas rssSlhInteractiveProtocol at hBadUnf
                dsimp only at hDummy hBadUnf
                rw [hQuorum] at hBadUnf
                simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hBadUnf
                rw [hWalStep] at hBadUnf
                dsimp only at hBadUnf
                rw [hDummy.1, hDummy.2.1, hDummy.2.2.1, hDummy.2.2.2.1] at hBadUnf
                rw [hVR1] at hBadUnf
                dsimp only at hBadUnf
                obtain ⟨hExtEq, hBatchTrue⟩ := sharedPreCutBarrier_extract_eq cIdx deg cl.tsig.pk _ _ _ r3Init hBar
                dsimp only at hExtEq hBatchTrue
                rw [hExtEq, hAny] at hBadUnf
                simp only [↓reduceIte] at hBadUnf
                rw [← hDummy.2.2.2.2, hBatchTrue] at hBadUnf
                cases hBadUnf
              · exact Bool.eq_false_iff.mpr hAny
            dsimp only
            rw [hShares]
            have hQuorumV := extractHonestQuorumViews_deal p.sigBytes cIdx seedSh prfSh req
            dsimp only at hQuorumV
            rw [hQuorumV]
            dsimp only
            let q := (honestPairForCorrupt cIdx).2.2
            have hPkSeedEq : cl.tsig.pk.pkSeed = pkSeed := by
              rw [hPkKey]; rfl
            have hTrueSigEq :
                rssQuorumSlhSignBytes p q (q.views seedSh) (q.views prfSh) cl.tsig.pk.pkSeed
                  constZeroRssSeedTape (A.scheduleSession advSt).1.msg (A.scheduleSession advSt).1.optRand =
                encodeSlhSig (slhSignInternal p (A.scheduleSession advSt).1.msg sk (A.scheduleSession advSt).1.optRand) := by
              rw [hPkSeedEq]
              exact (rss_threshold_sig_independent_of_quorum_and_sharing p hWf q q
                hSeedWf hPrfWf hSeedWf hPrfWf rfl rfl pkSeed
                constZeroRssSeedTape constZeroRssSeedTape
                (A.scheduleSession advSt).1.msg (A.scheduleSession advSt).1.optRand).1
            have hNoFault :
                injectCutFaultIfNonzero p.sigBytes r3Init.deltas
                  (rssQuorumSlhSignBytes p q (q.views seedSh) (q.views prfSh) cl.tsig.pk.pkSeed
                    constZeroRssSeedTape (A.scheduleSession advSt).1.msg (A.scheduleSession advSt).1.optRand) =
                encodeSlhSig (slhSignInternal p (A.scheduleSession advSt).1.msg sk (A.scheduleSession advSt).1.optRand) := by
              unfold injectCutFaultIfNonzero
              rw [hDeltasZero]
              simp only [Bool.false_eq_true, ↓reduceIte]
              exact hTrueSigEq
            rw [hNoFault, unpackWireBytes_packWireBytes]
            cases sharedFinalizeCutOpen p cIdx cl.tsig.pk _ _ _ with
            | inl cutErr =>
              dsimp only [poisonRealCluster, poisonIdealCluster, walQuarantine]
              exact ⟨rfl, rfl, rfl, ⟨rfl, hThEq, hNpEq, rfl, rfl, rfl, fun hp => by cases hp⟩⟩
            | inr outSigBytes =>
              dsimp only
              exact ⟨rfl, rfl, rfl, ⟨rfl, hThEq, hNpEq, rfl, rfl, rfl, fun _ => rfl⟩⟩

/-- Multi-session adaptive XOR bijection over `Fin (rssMultiSessionCard p.sigBytes s)` built via
    `depProdFinEquiv`: session `0` shifts by `(cl, advSt)`, and sessions `1..s-1` shift by the
    adaptive successor state `(cl1, advSt1)` induced by `cur`! -/
def multiSessionTapeEquiv {AdvState : Type}
    (p : Fips205Params) (cIdx : Fin 3) (deg : Nat)
    (A : UcRushingAdversary AdvState) :
    (s : Nat) →
    RealClusterState SlhPublicKey RssPartyKeyShare →
    AdvState →
    SimpleEquiv (Fin (rssMultiSessionCard p.sigBytes s)) (Fin (rssMultiSessionCard p.sigBytes s))
  | 0, _, _ => idFinEquiv 1
  | s + 1, cl, advSt =>
    depProdFinEquiv (rssMultiSessionCard_pos p.sigBytes s)
      (adaptiveSingleSessionEquiv p cIdx A cl advSt)
      (fun cur =>
        let (cl1, advSt1, _) :=
          execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt
            (decodeSingleFullTape p.sigBytes cur)
        multiSessionTapeEquiv p cIdx deg A s cl1 advSt1)

/-- Multi-session `GF(2^128)` Schwartz-Zippel bad-event indicator across all `s` scheduled sessions. -/
def multiSessionBadHit {AdvState : Type}
    (p : Fips205Params) (cIdx : Fin 3) (deg : Nat)
    (A : UcRushingAdversary AdvState) :
    (s : Nat) →
    RealClusterState SlhPublicKey RssPartyKeyShare →
    AdvState →
    Fin (rssMultiSessionCard p.sigBytes s) → Bool
  | 0, _, _, _ => false
  | s + 1, cl, advSt, ω =>
    let cur := splitFinLeft (rssMultiSessionCard_pos p.sigBytes s) ω
    let rest := splitFinRight (rssMultiSessionCard_pos p.sigBytes s) ω
    let (cl1, advSt1, _) :=
      execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt
        (decodeSingleFullTape p.sigBytes cur)
    sessionBadHit p cIdx deg A cl advSt cur ||
      multiSessionBadHit p cIdx deg A s cl1 advSt1 rest

private theorem finSum_le_add_finSum : ∀ (n : Nat) (f g h : Fin n → Nat),
    (∀ i, f i ≤ g i + h i) → finSum n f ≤ finSum n g + finSum n h
  | 0, _, _, _, _ => Nat.le_refl 0
  | n + 1, f, g, h, hLe => by
    simp only [finSum]
    have ih := finSum_le_add_finSum n
      (fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (fun i => g ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (fun i => h ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (fun i => hLe ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    have h0 := hLe ⟨0, Nat.zero_lt_succ n⟩
    omega

private theorem finSum_mul_right_local : ∀ (n c : Nat) (f : Fin n → Nat),
    finSum n (fun i => f i * c) = finSum n f * c
  | 0, _, _ => by simp [finSum]
  | n + 1, c, f => by simp only [finSum, finSum_mul_right_local n c, Nat.add_mul]

private theorem multiSessionBadHit_pairFin {AdvState : Type}
    (p : Fips205Params) (cIdx : Fin 3) (deg : Nat)
    (A : UcRushingAdversary AdvState) (s : Nat)
    (cl : RealClusterState SlhPublicKey RssPartyKeyShare) (advSt : AdvState)
    (cur : Fin (rssFullSessionCard p.sigBytes))
    (rest : Fin (rssMultiSessionCard p.sigBytes s)) :
    multiSessionBadHit p cIdx deg A (s + 1) cl advSt (pairFin cur rest) =
    (sessionBadHit p cIdx deg A cl advSt cur ||
      let next := execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt
                    (decodeSingleFullTape p.sigBytes cur)
      multiSessionBadHit p cIdx deg A s next.1 next.2.1 rest) := by
  simp only [multiSessionBadHit, splitFinLeft_pairFin, splitFinRight_pairFin]

/-- **Multi-Session Schwartz-Zippel Bad-Event Bound (`multiSessionBadHit_finSum_bound`)**:
    Across any `Q_s` adaptively scheduled rushing sessions, the total number of random tapes `ω`
    hitting `multiSessionBadHit = true` satisfies:
    `badCount * (2 ^ 128) ≤ (Q_s * deg) * rssMultiSessionCard p.sigBytes Q_s`! -/
theorem multiSessionBadHit_finSum_bound {AdvState : Type}
    (p : Fips205Params) (cIdx : Fin 3) (deg : Nat)
    (A : UcRushingAdversary AdvState) :
    ∀ (s : Nat) (cl : RealClusterState SlhPublicKey RssPartyKeyShare) (advSt : AdvState),
      finSum (rssMultiSessionCard p.sigBytes s)
        (fun ω => if multiSessionBadHit p cIdx deg A s cl advSt ω then 1 else 0) * (2 ^ 128) ≤
      (s * deg) * rssMultiSessionCard p.sigBytes s
  | 0, _, _ => by simp [multiSessionBadHit, rssMultiSessionCard, finSum]
  | s + 1, cl, advSt => by
    let F := rssFullSessionCard p.sigBytes
    let M := rssMultiSessionCard p.sigBytes s
    change finSum (F * M) (fun ω => if multiSessionBadHit p cIdx deg A (s + 1) cl advSt ω then 1 else 0) * (2 ^ 128) ≤
      ((s + 1) * deg) * (F * M)
    rw [finSum_prod_eq F M]
    have hSplitOr :
        finSum F (fun cur => finSum M (fun rest =>
          if multiSessionBadHit p cIdx deg A (s + 1) cl advSt (pairFin cur rest) then 1 else 0)) ≤
        finSum F (fun cur => finSum M (fun _ =>
          if sessionBadHit p cIdx deg A cl advSt cur then 1 else 0)) +
        finSum F (fun cur => finSum M (fun rest =>
          let (cl1, advSt1, _) :=
            execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt
              (decodeSingleFullTape p.sigBytes cur)
          if multiSessionBadHit p cIdx deg A s cl1 advSt1 rest then 1 else 0)) := by
      apply finSum_le_add_finSum
      intro cur
      apply finSum_le_add_finSum
      intro rest
      rw [multiSessionBadHit_pairFin p cIdx deg A s cl advSt cur rest]
      let b1 := sessionBadHit p cIdx deg A cl advSt cur
      let next := execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt
                    (decodeSingleFullTape p.sigBytes cur)
      let b2 := multiSessionBadHit p cIdx deg A s next.1 next.2.1 rest
      change (if (b1 || b2) = true then 1 else 0) ≤
             (if b1 = true then 1 else 0) + (if b2 = true then 1 else 0)
      cases b1 <;> cases b2 <;> decide
    have hMulSplit := Nat.mul_le_mul_right (2 ^ 128) hSplitOr
    rw [Nat.add_mul] at hMulSplit
    have hTerm1 :
        finSum F (fun cur => finSum M (fun _ =>
          if sessionBadHit p cIdx deg A cl advSt cur then 1 else 0)) * (2 ^ 128) ≤
        deg * (F * M) := by
      have hConstM :
          finSum F (fun cur => finSum M (fun _ =>
            if sessionBadHit p cIdx deg A cl advSt cur then 1 else 0)) =
          finSum F (fun cur => (if sessionBadHit p cIdx deg A cl advSt cur then 1 else 0) * M) := by
        apply finSum_congr
        intro cur
        rw [finSum_const, Nat.mul_comm]
      rw [hConstM, finSum_mul_right_local]
      have hB1 := sessionBadHit_finSum_le p cIdx deg A cl advSt
      have hScaled := Nat.mul_le_mul_right (M * (2 ^ 128)) hB1
      have hL : finSum F (fun cur => if sessionBadHit p cIdx deg A cl advSt cur then 1 else 0) * M * (2 ^ 128) =
          finSum F (fun cur => if sessionBadHit p cIdx deg A cl advSt cur then 1 else 0) * (M * (2 ^ 128)) :=
        Nat.mul_assoc _ _ _
      have hR : rssPadSessionCard p.sigBytes * deg * (M * (2 ^ 128)) = deg * (F * M) := by
        dsimp only [F, rssFullSessionCard]
        ac_rfl
      rw [hL, ← hR]
      exact hScaled
    have hTerm2 :
        finSum F (fun cur => finSum M (fun rest =>
          let (cl1, advSt1, _) :=
            execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt
              (decodeSingleFullTape p.sigBytes cur)
          if multiSessionBadHit p cIdx deg A s cl1 advSt1 rest then 1 else 0)) * (2 ^ 128) ≤
        (s * deg) * (F * M) := by
      rw [← finSum_mul_right_local]
      have hCap : finSum F (fun _ => (s * deg) * M) = F * ((s * deg) * M) := finSum_const F _
      have hLeCap :
          finSum F (fun cur => finSum M (fun rest =>
            let (cl1, advSt1, _) :=
              execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt
                (decodeSingleFullTape p.sigBytes cur)
            if multiSessionBadHit p cIdx deg A s cl1 advSt1 rest then 1 else 0) * (2 ^ 128)) ≤
          finSum F (fun _ => (s * deg) * M) := by
        apply finSum_le_finSum
        intro cur
        exact multiSessionBadHit_finSum_bound p cIdx deg A s _ _
      have hR : F * ((s * deg) * M) = (s * deg) * (F * M) := by ac_rfl
      exact Nat.le_trans hLeCap (hCap ▸ hR ▸ Nat.le_refl _)
    have hSum := Nat.add_le_add hTerm1 hTerm2
    have hRhs : deg * (F * M) + (s * deg) * (F * M) = ((s + 1) * deg) * (F * M) := by
      rw [Nat.succ_mul, Nat.add_comm (s * deg) deg, Nat.add_mul]
    exact Nat.le_trans hMulSplit (hRhs ▸ hSum)

/-- **Whole-Transcript Multi-Session Lockstep Equivalence (`multiSession_real_eq_ideal_unless_bad`)**:
    Across ANY `Q_s` adaptively scheduled sessions, whenever `multiSessionBadHit ... ω = false`,
    `RealProtocolExec` on `ω` and `IdealFunctionalityExec` (`IdealTsig` + `Sim_RssSlh`) on
    `(multiSessionTapeEquiv ...).toFun ω` emit the **EXACT SAME `ExecTranscript AdvState`**! -/
theorem multiSession_real_eq_ideal_unless_bad {AdvState : Type}
    (p : Fips205Params) (hWf : p.wellFormed = true)
    (cIdx : Fin 3) (deg : Nat)
    {seedSh prfSh : RssByteShares}
    (hSeedWf : seedSh.WellFormed) (hPrfWf : prfSh.WellFormed)
    (pkSeed : List UInt8)
    (A : UcRushingAdversary AdvState) :
    ∀ (s : Nat)
      (cl : RealClusterState SlhPublicKey RssPartyKeyShare)
      (icl : IdealClusterState SlhPublicKey)
      (advSt : AdvState),
      RealIdealClusterMatch cIdx seedSh prfSh cl icl →
      cl.tsig.pk = (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2 →
      ∀ (ω : Fin (rssMultiSessionCard p.sigBytes s)),
        multiSessionBadHit p cIdx deg A s cl advSt ω = false →
        let sk := (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).1
        (RealProtocolExec (rssSlhInteractiveProtocol p cIdx deg) A s
          (decodeMultiSessionTapes p.sigBytes s ω) cl advSt).2 =
        (IdealFunctionalityExec (slhIdealSignOracle p sk) (Sim_RssSlh p cIdx deg) A s
          (decodeMultiSessionTapes p.sigBytes s ((multiSessionTapeEquiv p cIdx deg A s cl advSt).toFun ω))
          icl advSt).2
  | 0, _, _, _, _, _, _, _ => rfl
  | s + 1, cl, icl, advSt, hMatch, hPkKey, ω, hNoBad => by
    let hMPos := rssMultiSessionCard_pos p.sigBytes s
    let cur := splitFinLeft hMPos ω
    let rest := splitFinRight hMPos ω
    have hOrFalse :
        (sessionBadHit p cIdx deg A cl advSt cur ||
          multiSessionBadHit p cIdx deg A s
            (execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt (decodeSingleFullTape p.sigBytes cur)).1
            (execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt (decodeSingleFullTape p.sigBytes cur)).2.1
            rest) = false := hNoBad
    have hCurFalse : sessionBadHit p cIdx deg A cl advSt cur = false := by
      cases hc : sessionBadHit p cIdx deg A cl advSt cur
      · rfl
      · rw [hc] at hOrFalse; simp at hOrFalse
    have hRestFalse :
        multiSessionBadHit p cIdx deg A s
          (execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt (decodeSingleFullTape p.sigBytes cur)).1
          (execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt (decodeSingleFullTape p.sigBytes cur)).2.1
          rest = false := by
      rw [hCurFalse, Bool.false_or] at hOrFalse
      exact hOrFalse
    have hHead0 :
        decodeMultiSessionTapes p.sigBytes (s + 1) ω 0 = decodeSingleFullTape p.sigBytes cur := rfl
    have hHeadSim0 :
        decodeMultiSessionTapes p.sigBytes (s + 1)
          ((multiSessionTapeEquiv p cIdx deg A (s + 1) cl advSt).toFun ω) 0 =
        decodeSingleFullTape p.sigBytes ((adaptiveSingleSessionEquiv p cIdx A cl advSt).toFun cur) := by
      simp only [multiSessionTapeEquiv, depProdFinEquiv, decodeMultiSessionTapes,
                 decodeSingleFullTape, splitFinLeft_pairFin]
      rfl
    have hTailReal :
        (fun i => decodeMultiSessionTapes p.sigBytes (s + 1) ω (i + 1)) =
        decodeMultiSessionTapes p.sigBytes s rest := rfl
    have hTailSim :
        (fun i => decodeMultiSessionTapes p.sigBytes (s + 1)
          ((multiSessionTapeEquiv p cIdx deg A (s + 1) cl advSt).toFun ω) (i + 1)) =
        decodeMultiSessionTapes p.sigBytes s
          ((multiSessionTapeEquiv p cIdx deg A s
            (execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt (decodeSingleFullTape p.sigBytes cur)).1
            (execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt (decodeSingleFullTape p.sigBytes cur)).2.1).toFun rest) := by
      funext i
      simp only [multiSessionTapeEquiv, depProdFinEquiv, decodeMultiSessionTapes,
                 splitFinRight_pairFin]
      rfl
    have hStep := execRealSession_eq_execIdealSession_unless_bad p hWf cIdx deg
      hSeedWf hPrfWf pkSeed A cl icl advSt hMatch hPkKey cur hCurFalse
    dsimp only at hStep
    rcases hR1 : execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt (decodeSingleFullTape p.sigBytes cur)
      with ⟨cl1, advSt1, rec1⟩
    rcases hI1 : execIdealSession (slhIdealSignOracle p (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).1)
      (Sim_RssSlh p cIdx deg) A icl advSt
      (decodeSingleFullTape p.sigBytes ((adaptiveSingleSessionEquiv p cIdx A cl advSt).toFun cur))
      with ⟨icl1, advStI1, recI1⟩
    rw [hR1, hI1] at hStep
    dsimp only at hStep
    obtain ⟨rfl, rfl, hPk1, hMatch1⟩ := hStep
    rw [hR1] at hRestFalse hTailSim
    dsimp only at hRestFalse hTailSim
    intro sk
    rw [RealProtocolExec_succ, IdealFunctionalityExec_succ, hHead0, hHeadSim0,
        hTailReal, hTailSim, hR1, hI1]
    dsimp only
    have ih := multiSession_real_eq_ideal_unless_bad p hWf cIdx deg hSeedWf hPrfWf pkSeed A
      s cl1 icl1 advSt1 hMatch1 (hPk1.trans hPkKey) rest hRestFalse
    dsimp only at ih
    rw [ih]

/-- **Crown-Jewel Theorem 1 (`rss_slh_real_ideal_view_indistinguishable`)**:
    Across ANY `Q_cuts` (`Q_s`) adaptively scheduled interactive rushing signing sessions with 1
    static malicious party `cIdx : Fin 3`, ANY outer calling protocol context `ctx`, ANY distinguisher
    `D`, and ANY real-world session-mask PRF generator `realPrfTapeGen : Fin prfCard → (Nat → RssSlhSessionTape p.sigBytes)`:
    1. **Information-Theoretic Uniform-Mask Hybrid Bound**: Between `RealProtocolExec` (with uniform
       session pads) and `IdealFunctionalityExec` (`IdealTsig` + `sk`-free `Sim_RssSlh`), the entire
       multi-round, multi-session `ExecTranscript` (including wire `ByteArray`s and `Abort(reason)`
       outcomes) satisfies `ratLe ... (Q_cuts * deg, 2 ^ 128)`!
    2. **End-to-End Concrete Real-vs-Ideal Bound**: Composing with `realPrfTapeGen` via
       `uc_transitive_composition`, the adversary's whole-protocol view advantage is bounded by
       `ratAdd (Q_cuts * deg, 2 ^ 128) advPrf` (`0` cheat hypotheses, `0 Classical.choice`)! -/
theorem rss_slh_real_ideal_view_indistinguishable {AdvState OuterView : Type}
    (p : Fips205Params) (hWf : p.wellFormed = true)
    (cIdx : Fin 3) (Q_cuts deg : Nat)
    {seedSh prfSh : RssByteShares}
    (hSeedWf : seedSh.WellFormed) (hPrfWf : prfSh.WellFormed)
    (pkSeed : List UInt8)
    (A : UcRushingAdversary AdvState)
    (cl : RealClusterState SlhPublicKey RssPartyKeyShare)
    (icl : IdealClusterState SlhPublicKey)
    (advSt : AdvState)
    (hMatch : RealIdealClusterMatch cIdx seedSh prfSh cl icl)
    (hPkKey : cl.tsig.pk = (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2)
    (ctx : OuterCallingContext (ExecTranscript AdvState) OuterView)
    (D : OuterView → Bool)
    (prfCard : Nat) (hPrfPos : 0 < prfCard)
    (realPrfTapeGen : Fin prfCard → (Nat → RssSlhSessionTape p.sigBytes)) :
    let card := rssMultiSessionCard p.sigBytes Q_cuts
    let sk := (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).1
    let realPrfView : Fin prfCard → OuterView := fun κ =>
      ctx.postProcess (RealProtocolExec (rssSlhInteractiveProtocol p cIdx deg) A Q_cuts
        (realPrfTapeGen κ) cl advSt).2
    let hybridUniformView : Fin card → OuterView := fun ω =>
      ctx.postProcess (RealProtocolExec (rssSlhInteractiveProtocol p cIdx deg) A Q_cuts
        (decodeMultiSessionTapes p.sigBytes Q_cuts ω) cl advSt).2
    let idealSimView : Fin card → OuterView := fun ω =>
      ctx.postProcess (IdealFunctionalityExec (slhIdealSignOracle p sk) (Sim_RssSlh p cIdx deg) A Q_cuts
        (decodeMultiSessionTapes p.sigBytes Q_cuts ω) icl advSt).2
    let advPrf := rationalAcceptDiff prfCard realPrfView card hybridUniformView D
    ratLe (rationalAcceptDiff card hybridUniformView card idealSimView D)
          (Q_cuts * deg, 2 ^ 128) ∧
    ratLe (rationalAcceptDiff prfCard realPrfView card idealSimView D)
          (ratAdd (Q_cuts * deg, 2 ^ 128) advPrf) := by
  intro card sk realPrfView hybridUniformView idealSimView advPrf
  have hCardPos : 0 < card := rssMultiSessionCard_pos p.sigBytes Q_cuts
  let bij := multiSessionTapeEquiv p cIdx deg A Q_cuts cl advSt
  let bad := multiSessionBadHit p cIdx deg A Q_cuts cl advSt
  have hAgree : ∀ ω : Fin card, bad ω = false → hybridUniformView ω = idealSimView (bij.toFun ω) := by
    intro ω hBadF
    dsimp only [hybridUniformView, idealSimView]
    exact congrArg ctx.postProcess (multiSession_real_eq_ideal_unless_bad p hWf cIdx deg
      hSeedWf hPrfWf pkSeed A Q_cuts cl icl advSt hMatch hPkKey ω hBadF)
  have hFund := (bad_event_fundamental_lemma card hCardPos hybridUniformView idealSimView bij bad hAgree D).2.2
  have hBadLe : ratLe (finSum card (fun ω => if bad ω then 1 else 0), card) (Q_cuts * deg, 2 ^ 128) :=
    ⟨hCardPos, Nat.two_pow_pos 128, multiSessionBadHit_finSum_bound p cIdx deg A Q_cuts cl advSt⟩
  have hUniformBound : ratLe (rationalAcceptDiff card hybridUniformView card idealSimView D)
      (Q_cuts * deg, 2 ^ 128) :=
    ratLe_trans hFund hBadLe
  have hPrfRefl : ratLe (rationalAcceptDiff prfCard realPrfView card hybridUniformView D) advPrf :=
    ⟨Nat.mul_pos hPrfPos hCardPos, Nat.mul_pos hPrfPos hCardPos, Nat.le_refl _⟩
  have hComp := uc_transitive_composition prfCard card card hPrfPos hCardPos hCardPos
    (fun κ => (RealProtocolExec (rssSlhInteractiveProtocol p cIdx deg) A Q_cuts (realPrfTapeGen κ) cl advSt).2)
    (fun ω => (RealProtocolExec (rssSlhInteractiveProtocol p cIdx deg) A Q_cuts (decodeMultiSessionTapes p.sigBytes Q_cuts ω) cl advSt).2)
    (fun ω => (IdealFunctionalityExec (slhIdealSignOracle p sk) (Sim_RssSlh p cIdx deg) A Q_cuts (decodeMultiSessionTapes p.sigBytes Q_cuts ω) icl advSt).2)
    ctx D advPrf (Q_cuts * deg, 2 ^ 128) hPrfRefl hUniformBound
  have hAddComm : ratLe (ratAdd advPrf (Q_cuts * deg, 2 ^ 128)) (ratAdd (Q_cuts * deg, 2 ^ 128) advPrf) := by
    unfold ratLe ratAdd
    dsimp only
    refine ⟨Nat.mul_pos (Nat.mul_pos hPrfPos hCardPos) (Nat.two_pow_pos 128),
            Nat.mul_pos (Nat.two_pow_pos 128) (Nat.mul_pos hPrfPos hCardPos), ?_⟩
    have hL : (advPrf.1 * (2 ^ 128) + (Q_cuts * deg) * advPrf.2) * ((2 ^ 128) * advPrf.2) =
        ((Q_cuts * deg) * advPrf.2 + advPrf.1 * (2 ^ 128)) * (advPrf.2 * (2 ^ 128)) := by
      rw [Nat.add_comm (advPrf.1 * (2 ^ 128)), Nat.mul_comm (2 ^ 128) advPrf.2]
    rw [hL]
    exact Nat.le_refl _
  exact ⟨hUniformBound, ratLe_trans hComp hAddComm⟩

/-- Right-nested product cardinality `B ^ t = B * (B * ... * 1)` avoiding `Nat.pow` WHNF expansion on `2 ^ 128`. -/
def towerPadSpaceCard (B : Nat) : Nat → Nat
  | 0 => 1
  | t + 1 => B * towerPadSpaceCard B t

private theorem towerPadSpaceCard_pos {B : Nat} (hB : 0 < B) : ∀ (t : Nat), 0 < towerPadSpaceCard B t
  | 0 => Nat.zero_lt_one
  | t + 1 => Nat.mul_pos hB (towerPadSpaceCard_pos hB t)

theorem towerPadSpaceCard_eq_pow (B : Nat) : ∀ (t : Nat), towerPadSpaceCard B t = B ^ t
  | 0 => rfl
  | t + 1 => by
    simp only [towerPadSpaceCard, towerPadSpaceCard_eq_pow B t, Nat.pow_succ, Nat.mul_comm]

private def decodeGenericPadPoly {R : Type} [CommRingOps R] (B : Nat) (hB : 0 < B)
    (dec1 : Fin B → R) : (t : Nat) → Fin (towerPadSpaceCard B t) → ShamirPadPoly R t
  | 0, _ => ⟨[], rfl⟩
  | t + 1, idx =>
    let hRest := towerPadSpaceCard_pos hB t
    let c0 := dec1 (splitFinLeft hRest idx)
    let rest := decodeGenericPadPoly B hB dec1 t (splitFinRight hRest idx)
    ⟨c0 :: rest.1, congrArg Nat.succ rest.2⟩

private def encodeGenericPadPoly {R : Type} [CommRingOps R] (B : Nat)
    (enc1 : R → Fin B) : (t : Nat) → ShamirPadPoly R t → Fin (towerPadSpaceCard B t)
  | 0, _ => ⟨0, Nat.zero_lt_one⟩
  | t + 1, ⟨c0 :: cs, hLen⟩ =>
    pairFin (enc1 c0) (encodeGenericPadPoly B enc1 t ⟨cs, Nat.succ.inj hLen⟩)

private theorem decode_encode_genericPadPoly {R : Type} [CommRingOps R] (B : Nat) (hB : 0 < B)
    (dec1 : Fin B → R) (enc1 : R → Fin B) (hLeft : ∀ x : R, dec1 (enc1 x) = x) :
    ∀ (t : Nat) (P : ShamirPadPoly R t),
      decodeGenericPadPoly B hB dec1 t (encodeGenericPadPoly B enc1 t P) = P
  | 0, ⟨[], _⟩ => rfl
  | t + 1, ⟨c0 :: cs, hLen⟩ => by
    simp only [encodeGenericPadPoly, decodeGenericPadPoly,
               splitFinLeft_pairFin, splitFinRight_pairFin, hLeft,
               decode_encode_genericPadPoly B hB dec1 enc1 hLeft t ⟨cs, Nat.succ.inj hLen⟩]

private theorem encode_decode_genericPadPoly {R : Type} [CommRingOps R] (B : Nat) (hB : 0 < B)
    (dec1 : Fin B → R) (enc1 : R → Fin B) (hRight : ∀ i : Fin B, enc1 (dec1 i) = i) :
    ∀ (t : Nat) (idx : Fin (towerPadSpaceCard B t)),
      encodeGenericPadPoly B enc1 t (decodeGenericPadPoly B hB dec1 t idx) = idx
  | 0, idx => by
    have hv : idx.val < 1 := idx.isLt
    apply Fin.ext
    change 0 = idx.val
    omega
  | t + 1, idx => by
    simp only [decodeGenericPadPoly, encodeGenericPadPoly, hRight,
               encode_decode_genericPadPoly B hB dec1 enc1 hRight t]
    exact pairFin_splitFin (towerPadSpaceCard_pos hB t) idx

/-- **`t`-of-`n` SPDZ Shamir Masked-Opening View Exact Indistinguishability
    (`spdz_shamir_tower128_masked_view_stat_dist_zero`)**:
    Over `Tower128` (`GF(2^128)`) with any threshold `t` and `< t` non-zero corrupt evaluation points
    `corruptPts`, `shamir_rebalanceEquiv` induces an exact bijection over finite degree-`< t` pad
    polynomials (`Fin (towerPadSpaceCard (2 ^ 128) t)`, cardinality `(2 ^ 128) ^ t`), proving
    statistical distance **identically `0`** between the real Round-2 masked opening view
    `(w + P(0), P|_{corruptPts})` of ANY secret wire `w : Tower128` and `simMaskedOpeningView`! -/
def decodeTower128PadPoly (t : Nat) : Fin (towerPadSpaceCard (2 ^ 128) t) → ShamirPadPoly Tower128 t :=
  decodeGenericPadPoly (2 ^ 128) (Nat.two_pow_pos 128) (fun i => unpackTower 7 (BitVec.ofFin i)) t

def encodeTower128PadPoly (t : Nat) : ShamirPadPoly Tower128 t → Fin (towerPadSpaceCard (2 ^ 128) t) :=
  encodeGenericPadPoly (2 ^ 128) (fun x => (packTower 7 x).toFin) t

theorem spdz_shamir_tower128_masked_view_stat_dist_zero
    (t : Nat) (corruptPts : List Tower128) (w : Tower128)
    (hCard : corruptPts.length + 1 ≤ t)
    (hNonZero : ∀ c ∈ corruptPts, c ≠ towerZero 7)
    (D : (Tower128 × List Tower128) → Bool) :
    let N := towerPadSpaceCard (2 ^ 128) t
    let realView : Fin N → Tower128 × List Tower128 :=
      fun idx => realMaskedOpeningView corruptPts w (decodeTower128PadPoly t idx)
    let simView : Fin N → Tower128 × List Tower128 :=
      fun idx => simMaskedOpeningView corruptPts (decodeTower128PadPoly t idx)
    N = (2 ^ 128) ^ t ∧
    natAbsDiff (distAcceptCount N realView D) (distAcceptCount N simView D) = 0 ∧
    ratLe (rationalAcceptDiff N realView N simView D) (0, 1) := by
  intro N realView simView
  have hNPos : 0 < N := towerPadSpaceCard_pos (Nat.two_pow_pos 128) t
  have hInv : ∀ x : Tower128, x ≠ CommRingOps.zero → CommRingOps.mul x (towerInv 7 x) = CommRingOps.one :=
    fun x hx => towerMul_inv 7 x hx
  have hSimBij := tsigSimulator_view_bijection_indep_of_secret (towerInv 7) hInv t corruptPts w hCard hNonZero
  let eqvPoly := shamir_rebalanceEquiv (towerInv 7) t corruptPts w hCard
  have hDecEnc : ∀ P : ShamirPadPoly Tower128 t, decodeTower128PadPoly t (encodeTower128PadPoly t P) = P :=
    decode_encode_genericPadPoly (2 ^ 128) (Nat.two_pow_pos 128)
      (fun i => unpackTower 7 (BitVec.ofFin i))
      (fun x => (packTower 7 x).toFin)
      (fun x => by simp only [BitVec.ofFin_toFin, unpackTower_packTower])
      t
  have hEncDec : ∀ idx : Fin N, encodeTower128PadPoly t (decodeTower128PadPoly t idx) = idx :=
    encode_decode_genericPadPoly (2 ^ 128) (Nat.two_pow_pos 128)
      (fun i => unpackTower 7 (BitVec.ofFin i))
      (fun x => (packTower 7 x).toFin)
      (fun i => by simp only [packTower_unpackTower, BitVec.toFin_ofFin])
      t
  let bijFin : SimpleEquiv (Fin N) (Fin N) :=
    { toFun := fun idx => encodeTower128PadPoly t (eqvPoly.toFun (decodeTower128PadPoly t idx))
      invFun := fun idx => encodeTower128PadPoly t (eqvPoly.invFun (decodeTower128PadPoly t idx))
      left_inv := fun idx => by rw [hDecEnc, eqvPoly.left_inv, hEncDec]
      right_inv := fun idx => by rw [hDecEnc, eqvPoly.right_inv, hEncDec] }
  have hAgree : ∀ idx : Fin N, (false : Bool) = false → realView idx = simView (bijFin.toFun idx) := by
    intro idx _
    dsimp only [realView, simView, bijFin]
    rw [hDecEnc]
    exact (hSimBij.2.2 (decodeTower128PadPoly t idx)).symm
  have hFund := bad_event_fundamental_lemma N hNPos realView simView bijFin (fun _ => false) hAgree D
  have hBad0 : finSum N (fun _ : Fin N => if (false : Bool) = true then 1 else 0) = 0 := by
    have h := finSum_const N 0; rw [Nat.mul_zero] at h; exact h
  rw [hBad0] at hFund
  have hZeroDiff : natAbsDiff (distAcceptCount N realView D) (distAcceptCount N simView D) = 0 :=
    Nat.eq_zero_of_le_zero hFund.1
  refine ⟨towerPadSpaceCard_eq_pow (2 ^ 128) t, hZeroDiff, ?_⟩
  exact ratLe_trans hFund.2.2 ⟨hNPos, Nat.zero_lt_one, by simp⟩

/-- **Inhabitedness Witness for Theorem 1 (`inhabited_rss_slh_real_ideal_uc`)**:
    Exhibits a concrete 2-of-3 RSS cluster on `slhDsaShake128f` with corrupt Party `0`, honest
    approvers `[1, 2]`, and active rushing adversary `A`, satisfying every premise of
    `rss_slh_real_ideal_view_indistinguishable` (`Q_cuts = 2, deg = 4`). -/
theorem inhabited_rss_slh_real_ideal_uc :
    ∃ (cl : RealClusterState SlhPublicKey RssPartyKeyShare)
      (icl : IdealClusterState SlhPublicKey)
      (seedSh prfSh : RssByteShares)
      (pkSeed : List UInt8),
      seedSh.WellFormed ∧ prfSh.WellFormed ∧
      RealIdealClusterMatch ⟨0, by decide⟩ seedSh prfSh cl icl ∧
      cl.tsig.pk = (slhKeygenInternal slhDsaShake128f
        (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2 ∧
      validThresholdApproval cl.tsig [1, 2] = true := by
  let seedSh : RssByteShares := ⟨List.replicate 16 1, List.replicate 16 2, List.replicate 16 3⟩
  let prfSh : RssByteShares := ⟨List.replicate 16 4, List.replicate 16 5, List.replicate 16 6⟩
  let pkSeed : List UInt8 := List.replicate 16 7
  let pk := (slhKeygenInternal slhDsaShake128f
              (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2
  let tsig : IdealTsigState SlhPublicKey (List UInt8) :=
    ⟨pk, 2, 3, [0], [], []⟩
  let wal : WalLatchState := initWalLatchState (slhPkDigest pk)
  let cl : RealClusterState SlhPublicKey RssPartyKeyShare :=
    ⟨tsig, wal, 0, dealHonestRssVault ⟨0, by decide⟩ seedSh prfSh⟩
  let icl : IdealClusterState SlhPublicKey := ⟨tsig, wal, 0⟩
  have hS : seedSh.WellFormed := ⟨rfl, rfl⟩
  have hP : prfSh.WellFormed := ⟨rfl, rfl⟩
  have hMatch : RealIdealClusterMatch ⟨0, by decide⟩ seedSh prfSh cl icl :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  have hVal : validThresholdApproval cl.tsig [1, 2] = true := by decide +kernel
  exact ⟨cl, icl, seedSh, prfSh, pkSeed, hS, hP, hMatch, rfl, hVal⟩

/-! ## 4. Crown-Jewel Theorem 2: Interactive Rushing Threshold `EUF-CMA` Reduction (`0 Classical.choice`) -/

/-- Deterministic child root signed by the WOTS+ key at `(layer, tree, leaf)` in NIST `FIPS 205 SLH-DSA`:
    - `layer = 0`: signs the fixed FORS public key `fipsForsPkGen p skSeed pkSeed tree leaf`;
    - `layer = l + 1`: signs the layer-`l` XMSS subtree root at `childTree = tree * 2^hp + leaf`.
    Because `SLH-DSA` is a stateless hypertree of deterministic subtrees, **no** WOTS+ keypair ever
    signs more than this single `n`-byte root across any number of signing sessions `Q_s`! -/
def honestSlhWotsMsg (p : Fips205Params) (skSeed pkSeed : List UInt8)
    (layer tree leaf : Nat) : List UInt8 :=
  match layer with
  | 0 => fipsForsPkGen p skSeed pkSeed tree leaf
  | l + 1 => fipsXmssNode p skSeed pkSeed l (tree * (2 ^ p.hp) + leaf) p.hp 0

/-- **1. `ActiveConsistencySoundnessBreak`**:
    Explicit transcript-bound witness that in some session `rec ∈ tr.sessions`, the rushing corrupt
    party `cIdx` transmitted a non-zero `GF(2^128)` (`Tower128`) wire deviation batch `deltas` of
    degree `≤ deg` in Round 2 AND slipped past `preCutBarrier` into Round 3 (`rec.honestRound3 ≠ []`). -/
structure ActiveConsistencySoundnessBreak {AdvState : Type}
    (cIdx : Fin 3) (deg : Nat) (tr : ExecTranscript AdvState) where
  sessRec        : SessionWireRecord
  hMem           : sessRec ∈ tr.sessions
  cWire2         : ByteArray
  hWireMem       : (cIdx.val, cWire2) ∈ sessRec.corruptRound2
  nonceC         : List UInt8
  deltas         : List Tower128
  hParse         : parseCorruptRound2Wire deg cWire2 = some (nonceC, deltas)
  hDeg           : deltas.length ≤ deg
  devElem        : Tower128
  hDevMem        : devElem ∈ deltas
  hDevNonzero    : devElem ≠ towerZero 7
  hPassedBarrier : sessRec.honestRound3 ≠ []

/-- **2. `XmssMerkleTcrBreak`**:
    Explicit `SHAKE256` collision (`in1 ≠ in2`, `shake256Xof p.n in1 = shake256Xof p.n in2`) on an
    XMSS `.tree` Merkle internal node hash under `pk.pkSeed`. -/
structure XmssMerkleTcrBreak (p : Fips205Params) (pk : SlhPublicKey) where
  coll      : Fips205ShakeCollision p.n
  hSeedPref : pk.pkSeed <+: coll.in1 ∧ pk.pkSeed <+: coll.in2

/-- **3. `WotsChainSmTcrBreak`**:
    Explicit WOTS+ multi-target security break at a hypertree coordinate `(layer < p.d, tree, leaf < 2^hp)`
    bound directly to `honestSlhWotsMsg p sk.skSeed sk.pkSeed layer tree leaf` (`0` free message parameter!):
    either a `SHAKE256` tweakable-hash collision (`wotsHash` / `wotsPk`) OR a backward chain preimage
    inverting `fipsF` strictly upstream of the honest revealed step `d₁ > 0`. -/
inductive WotsChainSmTcrBreak (p : Fips205Params) (sk : SlhSecretKey) : Type where
  | wotsHashCollision (coll : Fips205ShakeCollision p.n)
  | wotsBackwardPreimage
      (layer tree leaf : Nat)
      (hLayerLt : layer < p.d)
      (hLeafLt : leaf < 2 ^ p.hp)
      (brk : Fips205ChainPreimageBreak p sk.pkSeed sk.skSeed
               (honestSlhWotsMsg p sk.skSeed sk.pkSeed layer tree leaf) layer tree leaf)

/-- **4. `PrfMsgBreak`**:
    Explicit `SHAKE256` `H_msg` multi-target collision (`in1 ≠ in2`, `shake256Xof p.m in1 = shake256Xof p.m in2`)
    between the forged `(sigStar.rRand, mStar)` and a quorum-approved session `(rRand_r, req.msg)` with `req.msg ≠ mStar`. -/
structure PrfMsgBreak (p : Fips205Params) where
  coll : Fips205ShakeCollision p.m

/-- **5. `Fips205ForsItsrBreak` (NIST `FIPS 205` / `SPHINCS+` Interleaved Target Subset Resilience Break)**:
    Explicit witness bound to `(p, sk, clInit, tr, mStar, sigStar)` showing EITHER:
    - `forsHashCollision`: an explicit `SHAKE256` collision in `.forsTree` or `.forsRoots`;
    - `forsUnqueriedPrfRecovery`: `sigStar` recovers the exact secret `sk.skSeed` `PRF` leaf key
      `fipsPrf p.n sk.pkSeed sk.skSeed (mkFipsAdrs 0 idxTree .forsPrf idxLeaf 0 globalLeaf)` at a
      FORS coordinate `(idxTree, idxLeaf, treeIdx, leafOffset)` **never opened** in any Round-3 session of `tr`;
    - `forsInterleavedSubsetCover`: `0 < p.k` and every one of the `p.k` FORS leaf coordinates of
      `H_msg(sigStar.rRand, pkSeed, pkRoot, mStar)` is covered by distinct-digest approved Round-3
      sessions in `tr.sessions` (provably `False` on `tr.sessions = []` or whenever ≥ 1 FORS tree hits a fresh leaf!). -/
inductive Fips205ForsItsrBreak {AdvState : Type}
    (p : Fips205Params) (sk : SlhSecretKey)
    (clInit : RealClusterState SlhPublicKey RssPartyKeyShare)
    (tr : ExecTranscript AdvState)
    (mStar : List UInt8) (sigStar : SlhSignature) : Type where
  | forsHashCollision (coll : Fips205ShakeCollision p.n)
  | forsUnqueriedPrfRecovery
      (treeIdx : Nat)
      (hTreeLt : treeIdx < p.k)
      (hSkRecovered :
        let dStar := fipsHMsg p.m sigStar.rRand sk.pkSeed sk.pkRoot mStar
        let (mdStar, idxTreeStar, idxLeafStar) := fipsSplitDigest p dStar
        let leafOffset := (base2b mdStar p.a p.k).getD treeIdx 0
        (sigStar.forsSig.getD treeIdx ⟨[], []⟩).skVal =
          fipsPrf p.n sk.pkSeed sk.skSeed
            (mkFipsAdrs 0 idxTreeStar .forsPrf idxLeafStar 0 (treeIdx * (2 ^ p.a) + leafOffset)))
      (hNeverOpened :
        let dStar := fipsHMsg p.m sigStar.rRand sk.pkSeed sk.pkRoot mStar
        let (mdStar, idxTreeStar, idxLeafStar) := fipsSplitDigest p dStar
        let leafOffset := (base2b mdStar p.a p.k).getD treeIdx 0
        ∀ rec ∈ tr.sessions,
          validThresholdApproval clInit.tsig rec.request.honestApprovers = true →
          rec.honestRound3 ≠ [] →
          let rRec := fipsPrfMsg p.n sk.skPrf rec.request.optRand rec.request.msg
          let dRec := fipsHMsg p.m rRec sk.pkSeed sk.pkRoot rec.request.msg
          let (mdRec, tRec, lRec) := fipsSplitDigest p dRec
          ¬ (tRec = idxTreeStar ∧ lRec = idxLeafStar ∧ (base2b mdRec p.a p.k).getD treeIdx 0 = leafOffset))
  | forsInterleavedSubsetCover
      (hKPos : 0 < p.k)
      (hAllCovered :
        let dStar := fipsHMsg p.m sigStar.rRand sk.pkSeed sk.pkRoot mStar
        let (mdStar, idxTreeStar, idxLeafStar) := fipsSplitDigest p dStar
        ∀ j : Nat, j < p.k →
          ∃ rec ∈ tr.sessions,
            validThresholdApproval clInit.tsig rec.request.honestApprovers = true ∧
            rec.honestRound3 ≠ [] ∧
            rec.request.msg ≠ mStar ∧
            let rRec := fipsPrfMsg p.n sk.skPrf rec.request.optRand rec.request.msg
            let dRec := fipsHMsg p.m rRec sk.pkSeed sk.pkRoot rec.request.msg
            let (mdRec, tRec, lRec) := fipsSplitDigest p dRec
            dRec ≠ dStar ∧
            tRec = idxTreeStar ∧ lRec = idxLeafStar ∧
            (base2b mdRec p.a p.k).getD j 0 = (base2b mdStar p.a p.k).getD j 0)

/-- Constructive (`Type`-valued, `0 Classical.choice`) union of the 5 concrete security break witnesses. -/
inductive RssSlhInteractiveSecurityBreak {AdvState : Type}
    (p : Fips205Params) (cIdx : Fin 3) (deg : Nat) (sk : SlhSecretKey)
    (clInit : RealClusterState SlhPublicKey RssPartyKeyShare)
    (tr : ExecTranscript AdvState) (mStar : List UInt8) (sigStar : SlhSignature) : Type where
  | activeConsistency (w : ActiveConsistencySoundnessBreak cIdx deg tr)
  | forsItsr          (w : Fips205ForsItsrBreak p sk clInit tr mStar sigStar)
  | wotsChainSmTcr    (w : WotsChainSmTcrBreak p sk)
  | xmssMerkleTcr     (w : XmssMerkleTcrBreak p ⟨sk.pkSeed, sk.pkRoot⟩)
  | prfMsg            (w : PrfMsgBreak p)

private theorem wellFormed_props {p : Fips205Params} (hWf : p.wellFormed = true) :
    0 < p.n ∧ p.n ≤ 32 ∧ 0 < p.d ∧ p.h = p.d * p.hp ∧ 0 < p.k ∧ 0 < p.a := by
  unfold Fips205Params.wellFormed at hWf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hWf
  exact ⟨hWf.1.1.1.1.1.1, hWf.1.1.1.1.1.2, hWf.1.1.1.1.2, hWf.1.1.1.2, hWf.1.1.2, hWf.1.2⟩

private theorem fipsXmssNode_length (p : Fips205Params) (skSeed pkSeed : List UInt8) (layer tree : Nat) :
    ∀ (z nodeIdx : Nat), (fipsXmssNode p skSeed pkSeed layer tree z nodeIdx).length = p.n
  | 0, nodeIdx => by simp [fipsXmssNode, fipsWotsPkGen]
  | z + 1, nodeIdx => by simp [fipsXmssNode]

private theorem fipsForsNode_length (p : Fips205Params) (skSeed pkSeed : List UInt8) (tree idxLeaf : Nat) :
    ∀ (z nodeIdx : Nat), (fipsForsNode p skSeed pkSeed tree idxLeaf z nodeIdx).length = p.n
  | 0, nodeIdx => by simp [fipsForsNode]
  | z + 1, nodeIdx => by simp [fipsForsNode]

private theorem fipsForsPkGen_length (p : Fips205Params) (skSeed pkSeed : List UInt8) (tree idxLeaf : Nat) :
    (fipsForsPkGen p skSeed pkSeed tree idxLeaf).length = p.n := by
  simp [fipsForsPkGen]

private theorem fipsForsPkFromSig_length (p : Fips205Params) (fsig : List FipsForsTreeSig)
    (md pkSeed : List UInt8) (tree idxLeaf : Nat) :
    (fipsForsPkFromSig p fsig md pkSeed tree idxLeaf).length = p.n := by
  simp [fipsForsPkFromSig]

private theorem honestSlhWotsMsg_length (p : Fips205Params) (skSeed pkSeed : List UInt8)
    (layer tree leaf : Nat) :
    (honestSlhWotsMsg p skSeed pkSeed layer tree leaf).length = p.n := by
  cases layer with
  | zero => exact fipsForsPkGen_length p skSeed pkSeed tree leaf
  | succ l => exact fipsXmssNode_length p skSeed pkSeed l _ p.hp 0

private theorem fipsWalkBottomUp_length (n : Nat) (pkSeed : List UInt8) (layer tree kp : Nat)
    (ty : FipsAdrsType) :
    ∀ (path : List (List UInt8)) (z idx : Nat) (node : List UInt8),
      node.length = n →
      (fipsWalkBottomUp n pkSeed layer tree kp ty z idx node path).length = n
  | [], _, _, _, hN => hN
  | authZ :: rest, z, idx, node, _ => by
    simp only [fipsWalkBottomUp]
    by_cases hPar : idx % 2 = 0
    · rw [ite_eq_left hPar]
      exact fipsWalkBottomUp_length n pkSeed layer tree kp ty rest (z + 1) (idx / 2) _ (fipsH_length _ _ _ _ _)
    · rw [ite_eq_right hPar]
      exact fipsWalkBottomUp_length n pkSeed layer tree kp ty rest (z + 1) (idx / 2) _ (fipsH_length _ _ _ _ _)

private theorem fipsXmssPkFromSig_length (p : Fips205Params) (idx : Nat) (xsig : FipsXmssSig)
    (msg pkSeed : List UInt8) (layer tree : Nat) :
    (fipsXmssPkFromSig p idx xsig msg pkSeed layer tree).length = p.n := by
  unfold fipsXmssPkFromSig
  exact fipsWalkBottomUp_length p.n pkSeed layer tree 0 .tree xsig.authPath 0 idx _ (by simp [fipsWotsPkFromSig])

private theorem flatten_inj_fixed {n : Nat} (hn : 0 < n) :
    ∀ {xs ys : List (List UInt8)},
      xs.length = ys.length →
      (∀ x ∈ xs, x.length = n) →
      (∀ y ∈ ys, y.length = n) →
      xs.flatten = ys.flatten →
      xs = ys
  | [], [], _, _, _, _ => rfl
  | x :: xs, y :: ys, hLen, hX, hY, hFlat => by
    simp only [List.flatten_cons] at hFlat
    have hxL : x.length = n := hX x (.head _)
    have hyL : y.length = n := hY y (.head _)
    obtain ⟨hxy, hRest⟩ := List.append_inj hFlat (hxL.trans hyL.symm)
    rw [hxy, flatten_inj_fixed hn (Nat.succ.inj hLen)
      (fun a ha => hX a (.tail _ ha)) (fun b hb => hY b (.tail _ hb)) hRest]

/-- Constructive bottom-up Merkle collision finder (`0 Classical.choice`) shared by `.tree` (XMSS)
    and `.forsTree` (FORS): walks `path` until `nextNode = nodeF (z + 1) (idx / 2)` while
    `curNode ≠ nodeF z idx`, extracting an explicit `SHAKE256` collision prefixed by `pkSeed`. -/
private def extractMerkleWalkCollision (n : Nat) (pkSeed : List UInt8)
    (layer tree kp : Nat) (ty : FipsAdrsType)
    (nodeF : Nat → Nat → List UInt8)
    (hNodeLen : ∀ z ni, (nodeF z ni).length = n)
    (hNodeStep : ∀ z ni,
      nodeF (z + 1) ni = fipsH n pkSeed (mkFipsAdrs layer tree ty kp (z + 1) ni)
                           (nodeF z (2 * ni)) (nodeF z (2 * ni + 1))) :
    (path : List (List UInt8)) →
    (z idx : Nat) →
    (curNode : List UInt8) →
    curNode.length = n →
    (∀ s ∈ path, s.length = n) →
    curNode ≠ nodeF z idx →
    fipsWalkBottomUp n pkSeed layer tree kp ty z idx curNode path =
      nodeF (z + path.length) (idx / (2 ^ path.length)) →
    { coll : Fips205ShakeCollision n // pkSeed <+: coll.in1 ∧ pkSeed <+: coll.in2 }
  | [], z, idx, curNode, _, _, hNe, hWalk =>
    False.elim (hNe (by simpa [fipsWalkBottomUp] using hWalk))
  | authZ :: rest, z, idx, curNode, hCurLen, hPathLen, hNe, hWalk =>
    let parentIdx := idx / 2
    let adrs := mkFipsAdrs layer tree ty kp (z + 1) parentIdx
    let nextNode := if idx % 2 = 0 then fipsH n pkSeed adrs curNode authZ else fipsH n pkSeed adrs authZ curNode
    let honParent := nodeF (z + 1) parentIdx
    if hParentEq : nextNode = honParent then
      if hPar : idx % 2 = 0 then
        have hNextDef : nextNode = fipsH n pkSeed adrs curNode authZ := by
          dsimp only [nextNode]; exact ite_eq_left hPar
        have hIdxEven : 2 * parentIdx = idx := by dsimp only [parentIdx]; omega
        have hHonDef : honParent = fipsH n pkSeed adrs (nodeF z (2 * parentIdx)) (nodeF z (2 * parentIdx + 1)) :=
          hNodeStep z parentIdx
        ⟨{ in1 := pkSeed ++ encodeFips205Adrs adrs ++ curNode ++ authZ
           in2 := pkSeed ++ encodeFips205Adrs adrs ++ nodeF z (2 * parentIdx) ++ nodeF z (2 * parentIdx + 1)
           hNe := fun hIn => by
             simp only [List.append_assoc, List.append_cancel_left_eq] at hIn
             obtain ⟨hLeftEq, _⟩ := List.append_inj hIn (hCurLen.trans (hNodeLen z (2 * parentIdx)).symm)
             rw [hIdxEven] at hLeftEq
             exact hNe hLeftEq
           hEq := by
             have hE := hNextDef.symm.trans (hParentEq.trans hHonDef)
             simpa [fipsH] using hE },
         ⟨⟨encodeFips205Adrs adrs ++ curNode ++ authZ, by simp [List.append_assoc]⟩,
          ⟨encodeFips205Adrs adrs ++ nodeF z (2 * parentIdx) ++ nodeF z (2 * parentIdx + 1), by simp [List.append_assoc]⟩⟩⟩
      else
        have hNextDef : nextNode = fipsH n pkSeed adrs authZ curNode := by
          dsimp only [nextNode]; exact ite_eq_right hPar
        have hIdxOdd : 2 * parentIdx + 1 = idx := by dsimp only [parentIdx]; omega
        have hHonDef : honParent = fipsH n pkSeed adrs (nodeF z (2 * parentIdx)) (nodeF z (2 * parentIdx + 1)) :=
          hNodeStep z parentIdx
        have hAuthLen : authZ.length = n := hPathLen authZ (.head _)
        ⟨{ in1 := pkSeed ++ encodeFips205Adrs adrs ++ authZ ++ curNode
           in2 := pkSeed ++ encodeFips205Adrs adrs ++ nodeF z (2 * parentIdx) ++ nodeF z (2 * parentIdx + 1)
           hNe := fun hIn => by
             simp only [List.append_assoc, List.append_cancel_left_eq] at hIn
             obtain ⟨_, hRightEq⟩ := List.append_inj hIn (hAuthLen.trans (hNodeLen z (2 * parentIdx)).symm)
             rw [hIdxOdd] at hRightEq
             exact hNe hRightEq
           hEq := by
             have hE := hNextDef.symm.trans (hParentEq.trans hHonDef)
             simpa [fipsH] using hE },
         ⟨⟨encodeFips205Adrs adrs ++ authZ ++ curNode, by simp [List.append_assoc]⟩,
          ⟨encodeFips205Adrs adrs ++ nodeF z (2 * parentIdx) ++ nodeF z (2 * parentIdx + 1), by simp [List.append_assoc]⟩⟩⟩
    else
      have hNextLen : nextNode.length = n := by
        dsimp only [nextNode]
        by_cases hp2 : idx % 2 = 0
        · rw [ite_eq_left hp2]; exact fipsH_length _ _ _ _ _
        · rw [ite_eq_right hp2]; exact fipsH_length _ _ _ _ _
      have hWalkRest :
          fipsWalkBottomUp n pkSeed layer tree kp ty (z + 1) parentIdx nextNode rest =
            nodeF ((z + 1) + rest.length) (parentIdx / (2 ^ rest.length)) := by
        have hW : fipsWalkBottomUp n pkSeed layer tree kp ty (z + 1) parentIdx nextNode rest =
            nodeF (z + (rest.length + 1)) (idx / (2 ^ (rest.length + 1))) := by
          simpa [fipsWalkBottomUp, parentIdx, adrs, nextNode] using hWalk
        have hZ : z + (rest.length + 1) = (z + 1) + rest.length := by omega
        have hD : idx / (2 ^ (rest.length + 1)) = parentIdx / (2 ^ rest.length) := by
          dsimp only [parentIdx]
          rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm 2 (2 ^ rest.length)]
        rw [← hZ, ← hD]
        exact hW
      extractMerkleWalkCollision n pkSeed layer tree kp ty nodeF hNodeLen hNodeStep
        rest (z + 1) parentIdx nextNode hNextLen (fun s hs => hPathLen s (.tail _ hs))
        hParentEq hWalkRest

/-- Single-layer XMSS forgery splitter (`0 Classical.choice`): given `curNode ≠ honestSlhWotsMsg`
    verifying against `fipsXmssNode p sk.skSeed sk.pkSeed layer tree p.hp 0`, extracts EITHER
    `XmssMerkleTcrBreak` OR `WotsChainSmTcrBreak`! -/
private def extractSingleXmssLayerBreak (p : Fips205Params)
    (hnPos : 0 < p.n) (hnLe : p.n ≤ 128)
    (sk : SlhSecretKey) (layer tree leaf : Nat)
    (hLayerLt : layer < p.d) (hLeafLt : leaf < 2 ^ p.hp)
    (xsig : FipsXmssSig)
    (hWLen : xsig.wotsSig.length = p.ell)
    (hWEach : ∀ w ∈ xsig.wotsSig, w.length = p.n)
    (hApLen : xsig.authPath.length = p.hp)
    (hApEach : ∀ u ∈ xsig.authPath, u.length = p.n)
    (curNode : List UInt8) (hCurLen : curNode.length = p.n)
    (hCurNe : curNode ≠ honestSlhWotsMsg p sk.skSeed sk.pkSeed layer tree leaf)
    (hXmssEq : fipsXmssPkFromSig p leaf xsig curNode sk.pkSeed layer tree =
                 fipsXmssNode p sk.skSeed sk.pkSeed layer tree p.hp 0) :
    PSum (WotsChainSmTcrBreak p sk) (XmssMerkleTcrBreak p ⟨sk.pkSeed, sk.pkRoot⟩) :=
  let wotsPkStar := fipsWotsPkFromSig p xsig.wotsSig curNode sk.pkSeed layer tree leaf
  let honWotsPk := fipsWotsPkGen p sk.skSeed sk.pkSeed layer tree leaf
  if hWotsEq : wotsPkStar = honWotsPk then
    have hSigElem : ∀ i : Nat, i < p.ell → (xsig.wotsSig.getD i []).length = p.n := by
      intro i hi
      have hi' : i < xsig.wotsSig.length := by rw [hWLen]; exact hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
      exact hWEach _ (List.getElem_mem hi')
    match extractFips205WotsForgery p hnPos hnLe sk.pkSeed sk.skSeed
            (honestSlhWotsMsg p sk.skSeed sk.pkSeed layer tree leaf) curNode
            layer tree leaf xsig.wotsSig
            (honestSlhWotsMsg_length p sk.skSeed sk.pkSeed layer tree leaf)
            hCurLen (Ne.symm hCurNe) hSigElem hWotsEq with
    | .inl coll => .inl (.wotsHashCollision coll)
    | .inr preBrk => .inl (.wotsBackwardPreimage layer tree leaf hLayerLt hLeafLt preBrk)
  else
    have hWalk :
        fipsWalkBottomUp p.n sk.pkSeed layer tree 0 .tree 0 leaf wotsPkStar xsig.authPath =
          fipsXmssNode p sk.skSeed sk.pkSeed layer tree (0 + xsig.authPath.length) (leaf / (2 ^ xsig.authPath.length)) := by
      rw [Nat.zero_add, hApLen, Nat.div_eq_of_lt hLeafLt]
      exact hXmssEq
    let ⟨coll, hPref⟩ := extractMerkleWalkCollision p.n sk.pkSeed layer tree 0 .tree
      (fipsXmssNode p sk.skSeed sk.pkSeed layer tree)
      (fipsXmssNode_length p sk.skSeed sk.pkSeed layer tree)
      (fun _ _ => rfl)
      xsig.authPath 0 leaf wotsPkStar (by simp [wotsPkStar, fipsWotsPkFromSig]) hApEach hWotsEq hWalk
    .inr ⟨coll, hPref⟩

/-- Multi-layer hypertree extractor (`0 Classical.choice`) walking `rem` remaining layers `layer .. p.d - 1`. -/
private def extractHypertreeBreakAux (p : Fips205Params)
    (hnPos : 0 < p.n) (hnLe : p.n ≤ 128) (sk : SlhSecretKey) :
    (rem : Nat) → (hRemPos : 0 < rem) →
    (layer idxTree idxLeaf : Nat) →
    (hLayerSum : layer + rem = p.d) →
    (hLeafLt : idxLeaf < 2 ^ p.hp) →
    (hTreeLt : idxTree < 2 ^ ((rem - 1) * p.hp)) →
    (curNode : List UInt8) → (hCurLen : curNode.length = p.n) →
    (hCurNe : curNode ≠ honestSlhWotsMsg p sk.skSeed sk.pkSeed layer idxTree idxLeaf) →
    (htRest : List FipsXmssSig) → (hHtLen : htRest.length = rem) →
    (hHtEach : ∀ x ∈ htRest,
      x.wotsSig.length = p.ell ∧ (∀ w ∈ x.wotsSig, w.length = p.n) ∧
      x.authPath.length = p.hp ∧ (∀ u ∈ x.authPath, u.length = p.n)) →
    (hTopVerify : fipsHtVerifyAux p sk.pkSeed layer idxTree idxLeaf curNode htRest =
                    fipsXmssNode p sk.skSeed sk.pkSeed (p.d - 1) 0 p.hp 0) →
    PSum (WotsChainSmTcrBreak p sk) (XmssMerkleTcrBreak p ⟨sk.pkSeed, sk.pkRoot⟩)
  | 0, hPos, _, _, _, _, _, _, _, _, _, _, _, _, _ =>
    False.elim (Nat.lt_irrefl 0 hPos)
  | 1, _, layer, idxTree, idxLeaf, hLayerSum, hLeafLt, hTreeLt, curNode, hCurLen, hCurNe, htRest, hHtLen, hHtEach, hTopVerify =>
    match htRest, hHtLen with
    | [], h => False.elim (by cases h)
    | _ :: _ :: _, h => False.elim (Nat.noConfusion (Nat.succ.inj h))
    | [xsig], _ =>
      have hTreeZero : idxTree = 0 := by
        simp only [Nat.sub_self, Nat.zero_mul, Nat.pow_zero] at hTreeLt
        omega
      have hLayerEq : layer = p.d - 1 := by omega
      have hLayerLt : layer < p.d := by omega
      let hX := hHtEach xsig (.head _)
      have hXmssEq : fipsXmssPkFromSig p idxLeaf xsig curNode sk.pkSeed layer idxTree =
          fipsXmssNode p sk.skSeed sk.pkSeed layer idxTree p.hp 0 := by
        have hV : fipsXmssPkFromSig p idxLeaf xsig curNode sk.pkSeed layer idxTree =
            fipsXmssNode p sk.skSeed sk.pkSeed (p.d - 1) 0 p.hp 0 := by
          simpa [fipsHtVerifyAux] using hTopVerify
        rw [hV, ← hLayerEq, ← hTreeZero]
      extractSingleXmssLayerBreak p hnPos hnLe sk layer idxTree idxLeaf
        hLayerLt hLeafLt xsig hX.1 hX.2.1 hX.2.2.1 hX.2.2.2 curNode hCurLen hCurNe hXmssEq
  | rem + 2, _, layer, idxTree, idxLeaf, hLayerSum, hLeafLt, hTreeLt, curNode, hCurLen, hCurNe, htRest, hHtLen, hHtEach, hTopVerify =>
    match htRest, hHtLen with
    | [], h => False.elim (by cases h)
    | xsig :: rest, hConsLen =>
      let nextNode := fipsXmssPkFromSig p idxLeaf xsig curNode sk.pkSeed layer idxTree
      let honRoot := fipsXmssNode p sk.skSeed sk.pkSeed layer idxTree p.hp 0
      if hNodeEq : nextNode = honRoot then
        have hLayerLt : layer < p.d := by omega
        let hX := hHtEach xsig (.head _)
        extractSingleXmssLayerBreak p hnPos hnLe sk layer idxTree idxLeaf
          hLayerLt hLeafLt xsig hX.1 hX.2.1 hX.2.2.1 hX.2.2.2 curNode hCurLen hCurNe hNodeEq
      else
        let nextLeaf := idxTree % (2 ^ p.hp)
        let nextTree := idxTree / (2 ^ p.hp)
        have hSubPos : 0 < 2 ^ p.hp := Nat.two_pow_pos p.hp
        have hNextLeafLt : nextLeaf < 2 ^ p.hp := Nat.mod_lt _ hSubPos
        have hNextTreeLt : nextTree < 2 ^ (rem * p.hp) := by
          have hPow : 2 ^ ((rem + 1) * p.hp) = 2 ^ (rem * p.hp) * (2 ^ p.hp) := by
            rw [Nat.succ_mul, Nat.pow_add]
          have hTreeLt' : idxTree < 2 ^ ((rem + 1) * p.hp) := by simpa using hTreeLt
          exact (Nat.div_lt_iff_lt_mul hSubPos).mpr (hPow ▸ hTreeLt')
        have hTreeRecomb : nextTree * (2 ^ p.hp) + nextLeaf = idxTree := by
          dsimp only [nextTree, nextLeaf]
          rw [Nat.mul_comm _ (2 ^ p.hp), Nat.div_add_mod]
        have hNextNe : nextNode ≠ honestSlhWotsMsg p sk.skSeed sk.pkSeed (layer + 1) nextTree nextLeaf := by
          unfold honestSlhWotsMsg
          rw [hTreeRecomb]
          exact hNodeEq
        extractHypertreeBreakAux p hnPos hnLe sk (rem + 1) (Nat.succ_pos rem)
          (layer + 1) nextTree nextLeaf (by omega) hNextLeafLt
          (by simpa using hNextTreeLt)
          nextNode (fipsXmssPkFromSig_length p idxLeaf xsig curNode sk.pkSeed layer idxTree)
          hNextNe rest (Nat.succ.inj hConsLen)
          (fun x hx => hHtEach x (.tail _ hx))
          (by simpa [fipsHtVerifyAux, nextNode, nextLeaf, nextTree] using hTopVerify)

/-- Constructive list scanner (`0 Classical.choice`) finding the first element satisfying decidable `P`. -/
private def findDecidableElem {α : Type} (P : α → Prop) [∀ x, Decidable (P x)] :
    (xs : List α) →
    PSum { x : α // x ∈ xs ∧ P x } (PLift (∀ x ∈ xs, ¬ P x))
  | [] => .inr ⟨fun _ hMem => by cases hMem⟩
  | x :: xs =>
    if hPx : P x then
      .inl ⟨x, .head _, hPx⟩
    else
      match findDecidableElem P xs with
      | .inl ⟨y, hyMem, hyP⟩ => .inl ⟨y, .tail _ hyMem, hyP⟩
      | .inr ⟨hNone⟩ => .inr ⟨fun z hz => by
          rcases List.mem_cons.mp hz with rfl | hTl
          · exact hPx
          · exact hNone z hTl⟩

/-- Constructive scanner over `tr.sessions` (`0 Classical.choice`) checking if ANY session triggered
    an `ActiveConsistencySoundnessBreak`! -/
private def scanActiveConsistencyBreak {AdvState : Type}
    (cIdx : Fin 3) (deg : Nat) (tr : ExecTranscript AdvState) :
    Option (ActiveConsistencySoundnessBreak cIdx deg tr) :=
  let rec go (rem : List SessionWireRecord) (hSub : ∀ r ∈ rem, r ∈ tr.sessions) :
      Option (ActiveConsistencySoundnessBreak cIdx deg tr) :=
    match rem with
    | [] => none
    | rec :: rest =>
      if hR3 : rec.honestRound3 = [] then
        go rest (fun r hr => hSub r (.tail _ hr))
      else
        let rec scanWires (ws : List (Nat × ByteArray))
            (hWSub : ∀ w ∈ ws, w ∈ rec.corruptRound2) :
            Option (ActiveConsistencySoundnessBreak cIdx deg tr) :=
          match ws with
          | [] => none
          | (pid, cWire2) :: wRest =>
            if hPid : pid = cIdx.val then
              match hParse : parseCorruptRound2Wire deg cWire2 with
              | none => scanWires wRest (fun w hw => hWSub w (.tail _ hw))
              | some (nonceC, deltas) =>
                match findDecidableElem (fun d => d ≠ towerZero 7) deltas with
                | .inl ⟨d, hdMem, hdNe⟩ =>
                  some
                    { sessRec := rec
                      hMem := hSub rec (.head _)
                      cWire2 := cWire2
                      hWireMem := by
                        have hM := hWSub (pid, cWire2) (.head _)
                        rwa [hPid] at hM
                      nonceC := nonceC
                      deltas := deltas
                      hParse := hParse
                      hDeg := parseCorruptRound2Wire_length_le deg cWire2 hParse
                      devElem := d
                      hDevMem := hdMem
                      hDevNonzero := hdNe
                      hPassedBarrier := hR3 }
                | .inr _ => scanWires wRest (fun w hw => hWSub w (.tail _ hw))
            else
              scanWires wRest (fun w hw => hWSub w (.tail _ hw))
        match scanWires rec.corruptRound2 (fun _ hw => hw) with
        | some brk => some brk
        | none => go rest (fun r hr => hSub r (.tail _ hr))
  go tr.sessions (fun _ hr => hr)

private theorem map_eq_on_mem {α β : Type} {f g : α → β} :
    ∀ {xs : List α}, xs.map f = xs.map g → ∀ x ∈ xs, f x = g x
  | [], _, _, hx => by cases hx
  | a :: xs, hEq, x, hx => by
    simp only [List.map_cons, List.cons.injEq] at hEq
    rcases List.mem_cons.mp hx with rfl | hTl
    · exact hEq.1
    · exact map_eq_on_mem hEq.2 x hTl

/-- Scan FORS trees `0 .. count - 1` (`0 Classical.choice`) to verify either a Merkle/`.forsTree`
    `SHAKE256` collision OR that EVERY `j < count` satisfies `(sigStar.forsSig.getD j).skVal = honSkVal j`! -/
private def verifyOrExtractForsTrees (p : Fips205Params) (sk : SlhSecretKey)
    (md : List UInt8) (idxTree idxLeaf : Nat)
    (sigStar : SlhSignature)
    (hFLen : sigStar.forsSig.length = p.k)
    (hFEach : ∀ f ∈ sigStar.forsSig,
      f.skVal.length = p.n ∧ f.authPath.length = p.a ∧ ∀ u ∈ f.authPath, u.length = p.n)
    (hRootEqAt : ∀ j : Nat, j < p.k →
      let idxJ := (base2b md p.a p.k).getD j 0
      let entry := sigStar.forsSig.getD j ⟨[], []⟩
      let globalLeaf := j * (2 ^ p.a) + idxJ
      let node0 := fipsF p.n sk.pkSeed (mkFipsAdrs 0 idxTree .forsTree idxLeaf 0 globalLeaf) entry.skVal
      fipsWalkBottomUp p.n sk.pkSeed 0 idxTree idxLeaf .forsTree 0 globalLeaf node0 entry.authPath =
        fipsForsNode p sk.skSeed sk.pkSeed idxTree idxLeaf p.a j) :
    (count : Nat) → (hCountLe : count ≤ p.k) →
    PSum (Fips205ShakeCollision p.n)
         (PLift (∀ j : Nat, j < count →
            let idxJ := (base2b md p.a p.k).getD j 0
            (sigStar.forsSig.getD j ⟨[], []⟩).skVal =
              fipsPrf p.n sk.pkSeed sk.skSeed
                (mkFipsAdrs 0 idxTree .forsPrf idxLeaf 0 (j * (2 ^ p.a) + idxJ))))
  | 0, _ => .inr ⟨fun _ hj => False.elim (Nat.not_lt_zero _ hj)⟩
  | j + 1, hLe =>
    match verifyOrExtractForsTrees p sk md idxTree idxLeaf sigStar hFLen hFEach hRootEqAt j (Nat.le_of_succ_le hLe) with
    | .inl coll => .inl coll
    | .inr ⟨hPrev⟩ =>
      have hjLt : j < p.k := hLe
      let idxJ := (base2b md p.a p.k).getD j 0
      let entry := sigStar.forsSig.getD j ⟨[], []⟩
      let globalLeaf := j * (2 ^ p.a) + idxJ
      let adrsTree0 := mkFipsAdrs 0 idxTree .forsTree idxLeaf 0 globalLeaf
      let adrsPrf := mkFipsAdrs 0 idxTree .forsPrf idxLeaf 0 globalLeaf
      let node0Star := fipsF p.n sk.pkSeed adrsTree0 entry.skVal
      let honSkVal := fipsPrf p.n sk.pkSeed sk.skSeed adrsPrf
      let honNode0 := fipsForsNode p sk.skSeed sk.pkSeed idxTree idxLeaf 0 globalLeaf
      have hEntryMem : entry ∈ sigStar.forsSig := by
        have hj' : j < sigStar.forsSig.length := by rw [hFLen]; exact hjLt
        have hEqG : entry = sigStar.forsSig[j]'hj' := by
          dsimp only [entry]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj']; rfl
        rw [hEqG]
        exact List.getElem_mem hj'
      let hFE := hFEach entry hEntryMem
      have hApLen := hFE.2.1
      have hApEach := hFE.2.2
      if hNode0Eq : node0Star = honNode0 then
        if hSkEq : entry.skVal = honSkVal then
          .inr ⟨fun i hi => by
            by_cases hiEq : i = j
            · subst hiEq; exact hSkEq
            · exact hPrev i (by omega)⟩
        else
          .inl
            { in1 := sk.pkSeed ++ encodeFips205Adrs adrsTree0 ++ entry.skVal
              in2 := sk.pkSeed ++ encodeFips205Adrs adrsTree0 ++ honSkVal
              hNe := fun hIn => by
                simp only [List.append_assoc, List.append_cancel_left_eq] at hIn
                exact hSkEq hIn
              hEq := by
                have hE : node0Star = fipsF p.n sk.pkSeed adrsTree0 honSkVal := hNode0Eq
                simpa [node0Star, fipsF] using hE }
      else
        have hBLen := (base2b_bounds md p.a p.k).1
        have hBBound := (base2b_bounds md p.a p.k).2
        have hjB : j < (base2b md p.a p.k).length := by rw [hBLen]; exact hjLt
        have hIdxJLt : idxJ < 2 ^ p.a := by
          dsimp only [idxJ]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjB]
          exact hBBound _ (List.getElem_mem hjB)
        have hGlobalDiv : globalLeaf / (2 ^ p.a) = j := by
          dsimp only [globalLeaf]
          rw [Nat.mul_comm j (2 ^ p.a), Nat.mul_add_div (Nat.two_pow_pos p.a),
              Nat.div_eq_of_lt hIdxJLt, Nat.add_zero]
        have hWalk :
            fipsWalkBottomUp p.n sk.pkSeed 0 idxTree idxLeaf .forsTree 0 globalLeaf node0Star entry.authPath =
              fipsForsNode p sk.skSeed sk.pkSeed idxTree idxLeaf (0 + entry.authPath.length)
                (globalLeaf / (2 ^ entry.authPath.length)) := by
          rw [Nat.zero_add, hApLen, hGlobalDiv]
          exact hRootEqAt j hjLt
        let ⟨coll, _⟩ := extractMerkleWalkCollision p.n sk.pkSeed 0 idxTree idxLeaf .forsTree
          (fipsForsNode p sk.skSeed sk.pkSeed idxTree idxLeaf)
          (fipsForsNode_length p sk.skSeed sk.pkSeed idxTree idxLeaf)
          (fun _ _ => rfl)
          entry.authPath 0 globalLeaf node0Star (fipsF_length _ _ _ _) hApEach hNode0Eq hWalk
        .inl coll

/-- Scan `0 .. count - 1` (`0 Classical.choice`) to test whether every FORS coordinate `(idxTree, idxLeaf, j, idxJ)`
    was covered by some approved Round-3 session in `tr.sessions`, or pinpoint the exact unqueried `j < count`! -/
private def checkForsSubsetCoverage {AdvState : Type}
    (p : Fips205Params) (sk : SlhSecretKey)
    (clInit : RealClusterState SlhPublicKey RssPartyKeyShare)
    (tr : ExecTranscript AdvState)
    (mdStar : List UInt8) (idxTreeStar idxLeafStar : Nat) :
    (count : Nat) →
    PSum { j : Nat // j < count ∧
            ∀ rec ∈ tr.sessions,
              validThresholdApproval clInit.tsig rec.request.honestApprovers = true →
              rec.honestRound3 ≠ [] →
              let rRec := fipsPrfMsg p.n sk.skPrf rec.request.optRand rec.request.msg
              let dRec := fipsHMsg p.m rRec sk.pkSeed sk.pkRoot rec.request.msg
              let (mdRec, tRec, lRec) := fipsSplitDigest p dRec
              ¬ (tRec = idxTreeStar ∧ lRec = idxLeafStar ∧
                 (base2b mdRec p.a p.k).getD j 0 = (base2b mdStar p.a p.k).getD j 0) }
         (PLift (∀ j : Nat, j < count →
            ∃ rec ∈ tr.sessions,
              validThresholdApproval clInit.tsig rec.request.honestApprovers = true ∧
              rec.honestRound3 ≠ [] ∧
              let rRec := fipsPrfMsg p.n sk.skPrf rec.request.optRand rec.request.msg
              let dRec := fipsHMsg p.m rRec sk.pkSeed sk.pkRoot rec.request.msg
              let (mdRec, tRec, lRec) := fipsSplitDigest p dRec
              tRec = idxTreeStar ∧ lRec = idxLeafStar ∧
              (base2b mdRec p.a p.k).getD j 0 = (base2b mdStar p.a p.k).getD j 0))
  | 0 => .inr ⟨fun _ hj => False.elim (Nat.not_lt_zero _ hj)⟩
  | j + 1 =>
    match checkForsSubsetCoverage p sk clInit tr mdStar idxTreeStar idxLeafStar j with
    | .inl ⟨u, huLt, huUncov⟩ => .inl ⟨u, Nat.lt_trans huLt (Nat.lt_succ_self j), huUncov⟩
    | .inr ⟨hPrevCov⟩ =>
      let MatchPred (rec : SessionWireRecord) : Prop :=
        validThresholdApproval clInit.tsig rec.request.honestApprovers = true ∧
        rec.honestRound3 ≠ [] ∧
        (let rRec := fipsPrfMsg p.n sk.skPrf rec.request.optRand rec.request.msg
         let dRec := fipsHMsg p.m rRec sk.pkSeed sk.pkRoot rec.request.msg
         let (mdRec, tRec, lRec) := fipsSplitDigest p dRec
         tRec = idxTreeStar ∧ lRec = idxLeafStar ∧
         (base2b mdRec p.a p.k).getD j 0 = (base2b mdStar p.a p.k).getD j 0)
      match findDecidableElem MatchPred tr.sessions with
      | .inl ⟨rec, hMem, hMP⟩ =>
        .inr ⟨fun i hi => by
          by_cases hiEq : i = j
          · subst hiEq; exact ⟨rec, hMem, hMP⟩
          · exact hPrevCov i (by omega)⟩
      | .inr ⟨hNone⟩ =>
        .inl ⟨j, Nat.lt_succ_self j, fun rec hMem hVal hR3 hHit =>
          hNone rec hMem ⟨hVal, hR3, hHit⟩⟩

/-- **Constructive Whole-Transcript Interactive Forgery Extractor (`extractInteractiveSlhBreak`)**:
    Given ANY transcript `tr` from `RealProtocolExec` and ANY valid wire signature `rawSigStar` on a
    message `mStar` never quorum-approved in `tr.sessions`, constructively (`0 Classical.choice`,
    `Type`-valued!) extracts a concrete `RssSlhInteractiveSecurityBreak` witness! -/
def extractInteractiveSlhBreak {AdvState : Type}
    (p : Fips205Params) (hWf : p.wellFormed = true)
    (cIdx : Fin 3) (deg : Nat)
    (skSeed skPrf pkSeed : List UInt8)
    (clInit : RealClusterState SlhPublicKey RssPartyKeyShare)
    (tr : ExecTranscript AdvState)
    (mStar : List UInt8) (sigStar : SlhSignature)
    (hSigWt : sigStar.WellTyped p)
    (hVerify : slhVerifyInternal p mStar sigStar (slhKeygenInternal p skSeed skPrf pkSeed).2 = true)
    (hUnapproved : ∀ rec ∈ tr.sessions,
      validThresholdApproval clInit.tsig rec.request.honestApprovers = true →
      rec.request.msg ≠ mStar) :
    RssSlhInteractiveSecurityBreak p cIdx deg
      (slhKeygenInternal p skSeed skPrf pkSeed).1 clInit tr mStar sigStar :=
  let sk := (slhKeygenInternal p skSeed skPrf pkSeed).1
  match scanActiveConsistencyBreak cIdx deg tr with
  | some activeBrk => .activeConsistency activeBrk
  | none =>
    let hWfP := wellFormed_props hWf
    have hnPos : 0 < p.n := hWfP.1
    have hnLe32 : p.n ≤ 32 := hWfP.2.1
    have hdPos : 0 < p.d := hWfP.2.2.1
    have hHdEq : p.h = p.d * p.hp := hWfP.2.2.2.1
    have hkPos : 0 < p.k := hWfP.2.2.2.2.1
    have hnLe128 : p.n ≤ 128 := Nat.le_trans hnLe32 (by decide)
    have hRLen := hSigWt.1
    have hFLen := hSigWt.2.1
    have hFEach := hSigWt.2.2.1
    have hHtLen := hSigWt.2.2.2.1
    have hHtEach := hSigWt.2.2.2.2
    let dStar := fipsHMsg p.m sigStar.rRand sk.pkSeed sk.pkRoot mStar
    let splitStar := fipsSplitDigest p dStar
    let mdStar := splitStar.1
    let idxTreeStar := splitStar.2.1
    let idxLeafStar := splitStar.2.2
    let pkForsStar := fipsForsPkFromSig p sigStar.forsSig mdStar sk.pkSeed idxTreeStar idxLeafStar
    let honPkFors := fipsForsPkGen p sk.skSeed sk.pkSeed idxTreeStar idxLeafStar
    have hTopVerify :
        fipsHtVerifyAux p sk.pkSeed 0 idxTreeStar idxLeafStar pkForsStar sigStar.htSig =
          fipsXmssNode p sk.skSeed sk.pkSeed (p.d - 1) 0 p.hp 0 := by
      have hV := hVerify
      unfold slhVerifyInternal slhKeygenInternal at hV
      dsimp only at hV
      simp only [hRLen, hFLen, hHtLen, ne_eq, not_true_eq_false, decide_false, Bool.false_or,
                 Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hV
      exact hV
    if hForsEq : pkForsStar = honPkFors then
      let rootsStar := (List.range p.k).map fun j =>
        let idxJ := (base2b mdStar p.a p.k).getD j 0
        let entry := sigStar.forsSig.getD j ⟨[], []⟩
        let globalLeaf := j * (2 ^ p.a) + idxJ
        let node0 := fipsF p.n sk.pkSeed (mkFipsAdrs 0 idxTreeStar .forsTree idxLeafStar 0 globalLeaf) entry.skVal
        fipsWalkBottomUp p.n sk.pkSeed 0 idxTreeStar idxLeafStar .forsTree 0 globalLeaf node0 entry.authPath
      let rootsHon := (List.range p.k).map fun j =>
        fipsForsNode p sk.skSeed sk.pkSeed idxTreeStar idxLeafStar p.a j
      if hRootsEq : rootsStar = rootsHon then
        have hRootEqAt : ∀ j : Nat, j < p.k →
            let idxJ := (base2b mdStar p.a p.k).getD j 0
            let entry := sigStar.forsSig.getD j ⟨[], []⟩
            let globalLeaf := j * (2 ^ p.a) + idxJ
            let node0 := fipsF p.n sk.pkSeed (mkFipsAdrs 0 idxTreeStar .forsTree idxLeafStar 0 globalLeaf) entry.skVal
            fipsWalkBottomUp p.n sk.pkSeed 0 idxTreeStar idxLeafStar .forsTree 0 globalLeaf node0 entry.authPath =
              fipsForsNode p sk.skSeed sk.pkSeed idxTreeStar idxLeafStar p.a j := by
          intro j hj
          exact map_eq_on_mem hRootsEq j (List.mem_range.mpr hj)
        match verifyOrExtractForsTrees p sk mdStar idxTreeStar idxLeafStar
                sigStar hFLen hFEach hRootEqAt p.k (Nat.le_refl p.k) with
        | .inl coll => .forsItsr (.forsHashCollision coll)
        | .inr ⟨hAllSkEq⟩ =>
          let HMsgCollPred (rec : SessionWireRecord) : Prop :=
            validThresholdApproval clInit.tsig rec.request.honestApprovers = true ∧
            rec.honestRound3 ≠ [] ∧
            fipsHMsg p.m (fipsPrfMsg p.n sk.skPrf rec.request.optRand rec.request.msg)
              sk.pkSeed sk.pkRoot rec.request.msg = dStar
          match findDecidableElem HMsgCollPred tr.sessions with
          | .inl ⟨rec, hMem, hVal, _, hDigEq⟩ =>
            let rRec := fipsPrfMsg p.n sk.skPrf rec.request.optRand rec.request.msg
            have hMsgNe : rec.request.msg ≠ mStar := hUnapproved rec hMem hVal
            .prfMsg ⟨{
              in1 := sigStar.rRand ++ sk.pkSeed ++ sk.pkRoot ++ mStar
              in2 := rRec ++ sk.pkSeed ++ sk.pkRoot ++ rec.request.msg
              hNe := fun hIn => by
                have hPrefLen : (sigStar.rRand ++ sk.pkSeed ++ sk.pkRoot).length =
                                (rRec ++ sk.pkSeed ++ sk.pkRoot).length := by
                  simp [hRLen, rRec, fipsPrfMsg]
                obtain ⟨_, hMsgEq⟩ := List.append_inj hIn hPrefLen
                exact hMsgNe hMsgEq.symm
              hEq := by
                simpa [fipsHMsg, dStar, rRec] using hDigEq.symm }⟩
          | .inr ⟨hNoDigColl⟩ =>
            match checkForsSubsetCoverage p sk clInit tr mdStar idxTreeStar idxLeafStar p.k with
            | .inl ⟨treeIdx, hTreeLt, hNeverOpened⟩ =>
              .forsItsr (.forsUnqueriedPrfRecovery treeIdx hTreeLt
                (hAllSkEq treeIdx hTreeLt) hNeverOpened)
            | .inr ⟨hAllCov⟩ =>
              .forsItsr (.forsInterleavedSubsetCover hkPos (fun j hj => by
                obtain ⟨rec, hMem, hVal, hR3, hCoord⟩ := hAllCov j hj
                refine ⟨rec, hMem, hVal, hR3, hUnapproved rec hMem hVal, ?_, hCoord.1, hCoord.2.1, hCoord.2.2⟩
                intro hDigEq
                exact hNoDigColl rec hMem ⟨hVal, hR3, hDigEq⟩))
      else
        let adrsRoots := mkFipsAdrs 0 idxTreeStar .forsRoots idxLeafStar 0 0
        .forsItsr (.forsHashCollision
          { in1 := sk.pkSeed ++ encodeFips205Adrs adrsRoots ++ rootsStar.flatten
            in2 := sk.pkSeed ++ encodeFips205Adrs adrsRoots ++ rootsHon.flatten
            hNe := fun hIn => by
              simp only [List.append_assoc, List.append_cancel_left_eq] at hIn
              have hS1 : ∀ x ∈ rootsStar, x.length = p.n := by
                intro x hx
                rw [List.mem_map] at hx
                obtain ⟨j, _, rfl⟩ := hx
                exact fipsWalkBottomUp_length _ _ _ _ _ _ _ _ _ _ (fipsF_length _ _ _ _)
              have hS2 : ∀ y ∈ rootsHon, y.length = p.n := by
                intro y hy
                rw [List.mem_map] at hy
                obtain ⟨j, _, rfl⟩ := hy
                exact fipsForsNode_length _ _ _ _ _ _ _
              have hLenEq : rootsStar.length = rootsHon.length := by simp [rootsStar, rootsHon]
              exact hRootsEq (flatten_inj_fixed hnPos hLenEq hS1 hS2 hIn)
            hEq := by
              simpa [pkForsStar, honPkFors, fipsForsPkFromSig, fipsForsPkGen,
                     rootsStar, rootsHon, fipsTl, adrsRoots] using hForsEq })
    else
      have hLeafLt : idxLeafStar < 2 ^ p.hp := Nat.mod_lt _ (Nat.two_pow_pos p.hp)
      have hTreeExp : p.h - p.hp = (p.d - 1) * p.hp := by
        have hd1 : p.d = (p.d - 1) + 1 := by omega
        have hMul : p.d * p.hp = (p.d - 1) * p.hp + p.hp := by
          conv => lhs; rw [hd1]
          rw [Nat.succ_mul]
        omega
      have hTreeLt : idxTreeStar < 2 ^ ((p.d - 1) * p.hp) := by
        dsimp only [idxTreeStar, splitStar, fipsSplitDigest]
        rw [← hTreeExp]
        exact Nat.mod_lt _ (Nat.two_pow_pos _)
      match extractHypertreeBreakAux p hnPos hnLe128 sk p.d hdPos
              0 idxTreeStar idxLeafStar (Nat.zero_add p.d) hLeafLt hTreeLt
              pkForsStar (fipsForsPkFromSig_length p sigStar.forsSig mdStar sk.pkSeed idxTreeStar idxLeafStar)
              hForsEq sigStar.htSig hHtLen hHtEach hTopVerify with
      | .inl wotsBrk => .wotsChainSmTcr wotsBrk
      | .inr xmssBrk => .xmssMerkleTcr xmssBrk

/-- **Honesty Link (`activeConsistencyBreak_implies_schwartzZippel_root`)**:
    Whenever a single session `rec = (execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt tape).2.2`
    witnesses `rec.honestRound3 ≠ []` with corrupt party `cIdx` (`cl.tsig.corruptParties = [cIdx.val]`),
    its Round-2 wire `cWire2` parsed to `(nonceC, deltas)` **necessarily satisfied**
    `batchDeviationPoly deltas (unpackTower 7 tape.gammaBits) = towerZero 7`!
    Thus `ActiveConsistencySoundnessBreak` is NEVER an unconstrained label — in `RealProtocolExec`,
    it forces a genuine non-zero degree-`≤ deg` polynomial root hit in `GF(2^128)`. -/
theorem activeConsistencyBreak_implies_schwartzZippel_root {AdvState : Type}
    (p : Fips205Params) (cIdx : Fin 3) (deg : Nat)
    (A : UcRushingAdversary AdvState)
    (cl : RealClusterState SlhPublicKey RssPartyKeyShare)
    (advSt : AdvState) (tape : RssSlhSessionTape p.sigBytes)
    (hSingleCorrupt : cl.tsig.corruptParties = [cIdx.val])
    {cWire2 : ByteArray} {nonceC : List UInt8} {deltas : List Tower128}
    (hR3Nonempty : (execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt tape).2.2.honestRound3 ≠ [])
    (hWireMem : (cIdx.val, cWire2) ∈ (execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt tape).2.2.corruptRound2)
    (hParse : parseCorruptRound2Wire deg cWire2 = some (nonceC, deltas)) :
    batchDeviationPoly deltas (unpackTower 7 tape.gammaBits) = towerZero 7 := by
  unfold execRealSession rssSlhInteractiveProtocol at hR3Nonempty hWireMem
  dsimp only at hR3Nonempty hWireMem
  cases hQ : validThresholdApproval cl.tsig (A.scheduleSession advSt).1.honestApprovers
  · rw [hQ] at hR3Nonempty; simp at hR3Nonempty
  · rw [hQ, ite_eq_right (by decide : ¬ ((!true) = true))] at hR3Nonempty hWireMem
    cases hW : walPreSignStep cl.honestWal (slhPkDigest cl.tsig.pk)
        (A.scheduleSession advSt).1.reqEpoch (slhReqDigest (A.scheduleSession advSt).1) with
    | err _ _ => rw [hW] at hR3Nonempty; simp at hR3Nonempty
    | ok wal' wAuth =>
      rw [hW] at hR3Nonempty hWireMem
      cases wAuth with
      | replayCached _ => simp at hR3Nonempty
      | authorizedFresh _ =>
        dsimp only at hR3Nonempty hWireMem
        cases hVR1 : sharedVerifyRound1 cIdx _ _ with
        | inl _ => rw [hVR1] at hR3Nonempty; simp at hR3Nonempty
        | inr r2Init =>
          rw [hVR1] at hR3Nonempty hWireMem
          dsimp only at hR3Nonempty hWireMem
          cases hBar : sharedPreCutBarrier cIdx deg cl.tsig.pk _ _ _ with
          | inl _ => rw [hBar] at hR3Nonempty; simp at hR3Nonempty
          | inr r3Init =>
            rw [hBar] at hWireMem
            dsimp only at hWireMem
            unfold sharedPreCutBarrier at hBar
            rw [hSingleCorrupt] at hBar hWireMem
            cases hFin : sharedFinalizeCutOpen p cIdx cl.tsig.pk _ _ _ <;>
              rw [hFin] at hWireMem <;>
              dsimp only at hWireMem
            · simp only [List.map, List.mem_singleton, Prod.mk.injEq] at hWireMem
              rcases hWireMem with ⟨_, hWireEq⟩
              subst hWireEq
              simp only [List.map, List.find?, beq_self_eq_true, hParse] at hBar
              cases hCmt : (round1NonceCommit cl.tsig.pk _ r2Init.cursor cIdx.val nonceC != r2Init.corrR1Commit)
              · rw [hCmt] at hBar
                simp only [Bool.false_eq_true, ↓reduceIte] at hBar
                cases hBatch : (batchDeviationPoly deltas (unpackTower 7 tape.gammaBits) == towerZero 7)
                · rw [hBatch] at hBar; simp at hBar
                · exact of_decide_eq_true (by simpa [beq_iff_eq] using hBatch)
              · rw [hCmt] at hBar; simp at hBar
            · simp only [List.map, List.mem_singleton, Prod.mk.injEq] at hWireMem
              rcases hWireMem with ⟨_, hWireEq⟩
              subst hWireEq
              simp only [List.map, List.find?, beq_self_eq_true, hParse] at hBar
              cases hCmt : (round1NonceCommit cl.tsig.pk _ r2Init.cursor cIdx.val nonceC != r2Init.corrR1Commit)
              · rw [hCmt] at hBar
                simp only [Bool.false_eq_true, ↓reduceIte] at hBar
                cases hBatch : (batchDeviationPoly deltas (unpackTower 7 tape.gammaBits) == towerZero 7)
                · rw [hBatch] at hBar; simp at hBar
                · exact of_decide_eq_true (by simpa [beq_iff_eq] using hBatch)
              · rw [hCmt] at hBar; simp at hBar

/-- **Non-Cosplay Witness Guard (`no_trivial_break_on_empty_transcript`)**:
    Neither `ActiveConsistencySoundnessBreak` nor `Fips205ForsItsrBreak.forsInterleavedSubsetCover` can
    ever be inhabited on an empty session transcript (`tr.sessions = []`). -/
theorem no_trivial_break_on_empty_transcript {AdvState : Type}
    (cIdx : Fin 3) (deg : Nat) (advSt : AdvState) :
    (ActiveConsistencySoundnessBreak cIdx deg (⟨advSt, []⟩ : ExecTranscript AdvState) → False) ∧
    (∀ (p : Fips205Params) (_hK : 0 < p.k)
       (P : Nat → SessionWireRecord → Prop),
       (∀ j : Nat, j < p.k → ∃ rec ∈ ([] : List SessionWireRecord), P j rec) → False) := by
  refine ⟨fun w => (by cases w.hMem), fun p hK P hAll => ?_⟩
  obtain ⟨_, hMem, _⟩ := hAll 0 hK
  cases hMem

/-- **Crown-Jewel Theorem 2 (`rss_slh_interactive_euf_cma_reduction`)**:
    **Constructive Black-Box Interactive `EUF-CMA` Security Reduction (`0 Classical.choice`, `0` cheat hypotheses!)**:
    For ANY well-formed NIST `FIPS 205` parameter set `p`, ANY 2-of-3 RSS secret-key sharing `(seedSh, prfSh)`,
    ANY stateful rushing adversary `A` scheduling `Q_s` interactive threshold sessions in `RealProtocolExec`,
    and ANY post-interaction forgery extractor `forgeOut : ExecTranscript AdvState → List UInt8 × ByteArray`,
    if `forgeOut tr = (mStar, rawSigBytes)` decodes via `decodeSlhSig p` to a valid `SlhSignature` `sigStar`
    verifying under `slhVerifyInternal p mStar sigStar pk = true` while `mStar` was **never approved by a
    valid `t`-quorum** in `clInit.tsig.approvedMsgs` or any session of `tr.sessions`, then our explicit
    `Type`-valued reduction `extractInteractiveSlhBreak` constructively produces a concrete witness of:
    - `ActiveConsistencySoundnessBreak` (`GF(2^128)` Schwartz-Zippel consistency hit), **OR**
    - `Fips205ForsItsrBreak` (FORS collision / unqueried `sk.skSeed` PRF recovery / multi-query `H_msg` ITSR cover), **OR**
    - `WotsChainSmTcrBreak` (WOTS+ hash collision or backward chain preimage on `honestSlhWotsMsg`), **OR**
    - `XmssMerkleTcrBreak` (XMSS `.tree` `SHAKE256` collision under `pk.pkSeed`), **OR**
    - `PrfMsgBreak` (`SHAKE256` `H_msg` collision against an approved session)! -/
theorem rss_slh_interactive_euf_cma_reduction {AdvState : Type}
    (p : Fips205Params) (hWf : p.wellFormed = true)
    (cIdx : Fin 3) (deg Q_s : Nat)
    {seedSh prfSh : RssByteShares}
    (pkSeed : List UInt8)
    (A : UcRushingAdversary AdvState)
    (tapes : Nat → RssSlhSessionTape p.sigBytes)
    (clInit : RealClusterState SlhPublicKey RssPartyKeyShare)
    (advSt0 : AdvState)
    (hPkKey : clInit.tsig.pk =
      (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2)
    (forgeOut : ExecTranscript AdvState → List UInt8 × ByteArray)
    {sigStar : SlhSignature}
    (hDecode :
      let (_, tr) := RealProtocolExec (rssSlhInteractiveProtocol p cIdx deg) A Q_s tapes clInit advSt0
      decodeSlhSig p (unpackWireBytes (forgeOut tr).2) = some sigStar)
    (hVerify :
      let (_, tr) := RealProtocolExec (rssSlhInteractiveProtocol p cIdx deg) A Q_s tapes clInit advSt0
      slhVerifyInternal p (forgeOut tr).1 sigStar clInit.tsig.pk = true)
    (hFreshMsg :
      let (clF, tr) := RealProtocolExec (rssSlhInteractiveProtocol p cIdx deg) A Q_s tapes clInit advSt0
      (forgeOut tr).1 ∉ clF.tsig.approvedMsgs ∧
      ∀ rec ∈ tr.sessions,
        validThresholdApproval clInit.tsig rec.request.honestApprovers = true →
        rec.request.msg ≠ (forgeOut tr).1) :
    let (_, tr) := RealProtocolExec (rssSlhInteractiveProtocol p cIdx deg) A Q_s tapes clInit advSt0
    let sk := (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).1
    Nonempty (ActiveConsistencySoundnessBreak cIdx deg tr) ∨
    Nonempty (Fips205ForsItsrBreak p sk clInit tr (forgeOut tr).1 sigStar) ∨
    Nonempty (WotsChainSmTcrBreak p sk) ∨
    Nonempty (XmssMerkleTcrBreak p ⟨sk.pkSeed, sk.pkRoot⟩) ∨
    Nonempty (PrfMsgBreak p) := by
  dsimp only at hDecode hVerify hFreshMsg ⊢
  let tr := (RealProtocolExec (rssSlhInteractiveProtocol p cIdx deg) A Q_s tapes clInit advSt0).2
  have hSigWt : sigStar.WellTyped p := decodeSlhSig_wellTyped hDecode
  have hVerKey : slhVerifyInternal p (forgeOut tr).1 sigStar
      (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2 = true := by
    rwa [← hPkKey]
  match extractInteractiveSlhBreak p hWf cIdx deg
          (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed
          clInit tr (forgeOut tr).1 sigStar hSigWt hVerKey hFreshMsg.2 with
  | .activeConsistency w => exact .inl ⟨w⟩
  | .forsItsr w          => exact .inr (.inl ⟨w⟩)
  | .wotsChainSmTcr w    => exact .inr (.inr (.inl ⟨w⟩))
  | .xmssMerkleTcr w     => exact .inr (.inr (.inr (.inl ⟨w⟩)))
  | .prfMsg w            => exact .inr (.inr (.inr (.inr ⟨w⟩)))

/-- **Inhabitedness Witness for Theorem 2 (`inhabited_rss_slh_euf_cma_reduction`)**:
    Demonstrates non-vacuity of `rss_slh_interactive_euf_cma_reduction` on `slhDsaShake128f`:
    an adversary outputting an unqueried `0`-session valid signature satisfies every premise of
    `rss_slh_interactive_euf_cma_reduction` (`decodeSlhSig = some`, `slhVerifyInternal = true`,
    `mStar ∉ approvedMsgs`), and the constructive extractor extracts a concrete break witness! -/
theorem inhabited_rss_slh_euf_cma_reduction :
    let p := slhDsaShake128f
    let seedSh : RssByteShares := ⟨List.replicate 16 1, List.replicate 16 2, List.replicate 16 3⟩
    let prfSh : RssByteShares := ⟨List.replicate 16 4, List.replicate 16 5, List.replicate 16 6⟩
    let pkSeed : List UInt8 := List.replicate 16 7
    let sk := (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).1
    let pk := (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2
    let clInit : RealClusterState SlhPublicKey RssPartyKeyShare :=
      ⟨⟨pk, 2, 3, [0], [], []⟩, initWalLatchState (slhPkDigest pk), 0,
       dealHonestRssVault ⟨0, by decide⟩ seedSh prfSh⟩
    let mStar : List UInt8 := [0x42, 0x99]
    let sigStar := slhSignInternal p mStar sk []
    ∃ (rawSig : ByteArray),
      decodeSlhSig p (unpackWireBytes rawSig) = some sigStar ∧
      slhVerifyInternal p mStar sigStar clInit.tsig.pk = true ∧
      mStar ∉ clInit.tsig.approvedMsgs ∧
      Nonempty (RssSlhInteractiveSecurityBreak p ⟨0, by decide⟩ 4 sk clInit ⟨(), []⟩ mStar sigStar) := by
  intro p seedSh prfSh pkSeed sk pk clInit mStar sigStar
  let rawSig := packWireBytes (encodeSlhSig sigStar)
  have hDec : decodeSlhSig p (unpackWireBytes rawSig) = some sigStar := by
    rw [unpackWireBytes_packWireBytes]
    exact decodeSlhSig_encodeSlhSig (slhSignInternal_wellTyped p mStar sk [])
  have hVer : slhVerifyInternal p mStar sigStar clInit.tsig.pk = true :=
    slhVerifyInternal_slhSignInternal p slhDsaShake128f_wellFormed
      (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed mStar []
  have hUnapp : ∀ rec ∈ ([] : List SessionWireRecord),
      validThresholdApproval clInit.tsig rec.request.honestApprovers = true →
      rec.request.msg ≠ mStar := fun _ hM => by cases hM
  refine ⟨rawSig, hDec, hVer, by simp [clInit], ?_⟩
  exact ⟨extractInteractiveSlhBreak p slhDsaShake128f_wellFormed ⟨0, by decide⟩ 4
    (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed
    clInit ⟨(), []⟩ mStar sigStar
    (slhSignInternal_wellTyped p mStar sk []) hVer hUnapp⟩

/-! ## 5. Crown-Jewel Theorem 3: Perfect Quorum & Sharing Privacy (`threshold_slh_output_perfect_quorum_privacy`) -/

private theorem reconstructRssBytes_masked_eq :
    ∀ {s b0 b1 : List UInt8},
      s.length = b0.length →
      b0.length = b1.length →
      reconstructRssBytes ⟨b0, b1, xorByteStream s (xorByteStream b0 b1)⟩ = s
  | [], [], [], _, _ => rfl
  | x :: xs, u :: us, v :: vs, h1, h2 => by
    simp only [reconstructRssBytes, xorByteStream, List.zipWith_cons_cons, List.cons.injEq]
    refine ⟨?_, reconstructRssBytes_masked_eq (Nat.succ.inj h1) (Nat.succ.inj h2)⟩
    apply UInt8.eq_of_toBitVec_eq
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [UInt8.toBitVec_xor, BitVec.getLsbD_xor]
    cases u.toBitVec.getLsbD i <;> cases v.toBitVec.getLsbD i <;> cases x.toBitVec.getLsbD i <;> rfl

private theorem encodeSlhSig_length {p : Fips205Params} {sig : SlhSignature}
    (hWt : sig.WellTyped p) :
    (encodeSlhSig sig).length = p.sigBytes := by
  have hDec := decodeSlhSig_encodeSlhSig hWt
  unfold decodeSlhSig at hDec
  by_cases hEq : (encodeSlhSig sig).length = p.sigBytes
  · exact hEq
  · rw [ite_eq_left hEq] at hDec
    cases hDec

/-- Rushing Round-3 echo helper: reconstructs the corrupt party's expected `FLNW17` cut-opening
    share pair `(cFirst ++ cSecond)` from the two honest parties' public Round-3 messages `honR3`. -/
def echoHonestRound3 (L : Nat) (honR3 : List (Nat × ByteArray)) : ByteArray :=
  match honR3 with
  | [(_, w0), (_, w1)] =>
    packWireBytes (((unpackWireBytes w1).drop L) ++ ((unpackWireBytes w0).take L))
  | _ => ByteArray.empty

private theorem checkRound3ActiveOpen_echoHonestRound3 (L : Nat) (cIdx : Fin 3)
    (cutSh : RssByteShares)
    (h0 : cutSh.b0.length = L) (h1 : cutSh.b1.length = L) (h2 : cutSh.b2.length = L) :
    checkRound3ActiveOpen L cIdx cutSh
      [(cIdx.val, echoHonestRound3 L (buildHonestRound3Msgs cIdx cutSh))] =
      some (reconstructRssBytes cutSh) := by
  rcases cIdx with ⟨_ | _ | _ | n, hv⟩
  · have hc : (⟨0, hv⟩ : Fin 3) = ⟨0, by decide⟩ := rfl
    rw [hc]
    simp only [buildHonestRound3Msgs, echoHonestRound3, checkRound3ActiveOpen,
               verifyRssActiveOpenBytes, Nat.reduceBEq, ↓reduceIte,
               List.find?, unpackWireBytes_packWireBytes]
    have hd2 : (cutSh.b2 ++ cutSh.b0).drop L = cutSh.b0 := by rw [← h2, List.drop_left]
    have ht1 : (cutSh.b1 ++ cutSh.b2).take L = cutSh.b1 := by rw [← h1, List.take_left]
    rw [hd2, ht1]
    have ht0 : (cutSh.b0 ++ cutSh.b1).take L = cutSh.b0 := by rw [← h0, List.take_left]
    have hd0 : (cutSh.b0 ++ cutSh.b1).drop L = cutSh.b1 := by rw [← h0, List.drop_left]
    rw [ht0, hd0]
    simp [h0, h1, h2]
  · have hc : (⟨0 + 1, hv⟩ : Fin 3) = ⟨1, by decide⟩ := rfl
    rw [hc]
    simp only [buildHonestRound3Msgs, echoHonestRound3, checkRound3ActiveOpen,
               verifyRssActiveOpenBytes, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte,
               List.find?, unpackWireBytes_packWireBytes]
    have hd0 : (cutSh.b0 ++ cutSh.b1).drop L = cutSh.b1 := by rw [← h0, List.drop_left]
    have ht2 : (cutSh.b2 ++ cutSh.b0).take L = cutSh.b2 := by rw [← h2, List.take_left]
    rw [hd0, ht2]
    have ht1 : (cutSh.b1 ++ cutSh.b2).take L = cutSh.b1 := by rw [← h1, List.take_left]
    have hd1 : (cutSh.b1 ++ cutSh.b2).drop L = cutSh.b2 := by rw [← h1, List.drop_left]
    rw [ht1, hd1]
    simp [h0, h1, h2]
  · have hc : (⟨0 + 1 + 1, hv⟩ : Fin 3) = ⟨2, by decide⟩ := rfl
    rw [hc]
    simp only [buildHonestRound3Msgs, echoHonestRound3, checkRound3ActiveOpen,
               verifyRssActiveOpenBytes, Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte,
               List.find?, unpackWireBytes_packWireBytes]
    have hd1 : (cutSh.b1 ++ cutSh.b2).drop L = cutSh.b2 := by rw [← h1, List.drop_left]
    have ht0 : (cutSh.b0 ++ cutSh.b1).take L = cutSh.b0 := by rw [← h0, List.take_left]
    rw [hd1, ht0]
    have ht2 : (cutSh.b2 ++ cutSh.b0).take L = cutSh.b2 := by rw [← h2, List.take_left]
    have hd2 : (cutSh.b2 ++ cutSh.b0).drop L = cutSh.b0 := by rw [← h2, List.drop_left]
    rw [ht2, hd2]
    simp [h0, h1, h2]
  · exact False.elim (Nat.not_lt_zero n (Nat.lt_of_add_lt_add_right hv))

private theorem parseCorruptRound2Wire_zero8 (deg : Nat) :
    parseCorruptRound2Wire deg (packWireBytes (List.replicate 8 0)) =
      some (List.replicate 8 0, []) := by
  unfold parseCorruptRound2Wire
  simp [unpackWireBytes_packWireBytes, splitByteChunks]

private theorem batchDeviationPoly_nil (x : Tower128) :
    batchDeviationPoly ([] : List Tower128) x = towerZero 7 := by
  simp only [batchDeviationPoly, RoundPoly.evalCoeffs,
             LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  rfl

private theorem batchDeviationPoly_singleton_one (x : Tower128) :
    batchDeviationPoly [towerOne 7] x = x := by
  simp only [batchDeviationPoly, RoundPoly.evalCoeffs,
             LawfulCommRing.mul_zero, LawfulCommRing.add_zero,
             LawfulCommRing.zero_add]
  exact LawfulCommRing.mul_one x

private theorem RealProtocolExec_one {PK ShareT SessionTape R1St R2St R3St AdvState : Type}
    (proto : InteractiveThresholdProtocol PK ShareT SessionTape R1St R2St R3St)
    (A : UcRushingAdversary AdvState) (tapes : Nat → SessionTape)
    (cl : RealClusterState PK ShareT) (advSt : AdvState) :
    RealProtocolExec proto A 1 tapes cl advSt =
      let (cl1, advSt1, rec0) := execRealSession proto A cl advSt (tapes 0)
      (cl1, ⟨advSt1, [rec0]⟩) := by
  simpa [RealProtocolExec_zero] using RealProtocolExec_succ proto A 0 tapes cl advSt

private theorem IdealFunctionalityExec_one {PK SimTape SimR1 SimR2 SimR3 AdvState : Type}
    (idealSignOracle : SessionScheduleReq → ByteArray)
    (sim : BlackBoxUcSimulator PK SimTape SimR1 SimR2 SimR3)
    (A : UcRushingAdversary AdvState) (tapes : Nat → SimTape)
    (icl : IdealClusterState PK) (advSt : AdvState) :
    IdealFunctionalityExec idealSignOracle sim A 1 tapes icl advSt =
      let (icl1, advSt1, rec0) := execIdealSession idealSignOracle sim A icl advSt (tapes 0)
      (icl1, ⟨advSt1, [rec0]⟩) := by
  simpa [IdealFunctionalityExec_zero] using IdealFunctionalityExec_succ idealSignOracle sim A 0 tapes icl advSt

private theorem RealProtocolExec_two {PK ShareT SessionTape R1St R2St R3St AdvState : Type}
    (proto : InteractiveThresholdProtocol PK ShareT SessionTape R1St R2St R3St)
    (A : UcRushingAdversary AdvState) (tapes : Nat → SessionTape)
    (cl : RealClusterState PK ShareT) (advSt : AdvState) :
    RealProtocolExec proto A 2 tapes cl advSt =
      let (cl1, advSt1, rec0) := execRealSession proto A cl advSt (tapes 0)
      let (cl2, advSt2, rec1) := execRealSession proto A cl1 advSt1 (tapes 1)
      (cl2, ⟨advSt2, [rec0, rec1]⟩) := by
  have hStep := RealProtocolExec_succ proto A 1 tapes cl advSt
  dsimp only at hStep
  rw [hStep]
  rcases execRealSession proto A cl advSt (tapes 0) with ⟨cl1, advSt1, rec0⟩
  dsimp only
  rw [RealProtocolExec_one]

/-- Concrete passive rushing adversary scheduling `reqs sIdx` (`sIdx = 0, 1, ...`) and completing
    all 3 rounds honestly (`deltas = []`, `echoHonestRound3`). -/
def passiveRushingAdv (p : Fips205Params) (pk : SlhPublicKey)
    (reqs : Nat → SessionScheduleReq) : UcRushingAdversary Nat where
  scheduleSession := fun sIdx => (reqs sIdx, sIdx)
  rushRound1 := fun sIdx _ =>
    (fun pid => round1NonceCommit pk (reqs sIdx) sIdx pid (List.replicate 8 0), sIdx)
  rushRound2 := fun sIdx _ =>
    (fun _ => packWireBytes (List.replicate 8 0), sIdx)
  rushRound3 := fun sIdx honR3 =>
    (fun _ => echoHonestRound3 p.sigBytes honR3, sIdx)
  observeOutcome := fun sIdx _ => sIdx + 1

/-- Single-session execution characterization for `passiveRushingAdv` on `rssSlhInteractiveProtocol`:
    whenever quorum approval and `walPreSignStep` authorize `reqs sIdx`, `execRealSession` completes
    all 3 rounds and emits the exact standalone NIST `FIPS 205` wire signature, independent of `cIdx`,
    secret sharing `(seedSh, prfSh)`, and random session tape `tape`! -/
theorem execRealSession_passiveRushingAdv_ok
    (p : Fips205Params) (hWf : p.wellFormed = true)
    (cIdx : Fin 3) (deg sIdx : Nat)
    {seedSh prfSh : RssByteShares}
    (hSeedWf : seedSh.WellFormed) (hPrfWf : prfSh.WellFormed)
    (pkSeed : List UInt8)
    (reqs : Nat → SessionScheduleReq)
    (cl : RealClusterState SlhPublicKey RssPartyKeyShare)
    (wal' : WalLatchState)
    (tape : RssSlhSessionTape p.sigBytes)
    (hPk : cl.tsig.pk = (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2)
    (hCorr : cl.tsig.corruptParties = [cIdx.val])
    (hCur : cl.maskSessionCursor = sIdx)
    (hShares : cl.honestShares = dealHonestRssVault cIdx seedSh prfSh)
    (hQuorum : validThresholdApproval cl.tsig (reqs sIdx).honestApprovers = true)
    (hWal : walPreSignStep cl.honestWal (slhPkDigest cl.tsig.pk)
              (reqs sIdx).reqEpoch (slhReqDigest (reqs sIdx)) =
              .ok wal' (.authorizedFresh (reqs sIdx).reqEpoch)) :
    let sk := (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).1
    let pk := (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2
    let expSig := packWireBytes (encodeSlhSig (slhSignInternal p (reqs sIdx).msg sk (reqs sIdx).optRand))
    let runOut :=
      execRealSession (rssSlhInteractiveProtocol p cIdx deg) (passiveRushingAdv p pk reqs) cl sIdx tape
    runOut.2.1 = sIdx + 1 ∧
    runOut.2.2.outcome = .signOk expSig ∧
    runOut.2.2.honestRound2 =
      (let (hA, hB, _) := honestPairForCorrupt cIdx
       let wA := match dealHonestRssVault cIdx seedSh prfSh hA with
                 | some shA => computeHonestChiWord hA shA (reqs sIdx).msg
                 | none => 0#64
       let wB := match dealHonestRssVault cIdx seedSh prfSh hB with
                 | some shB => computeHonestChiWord hB shB (reqs sIdx).msg
                 | none => 0#64
       [(hA, packWireBytes (bvToFixedBytes 8 tape.nonceA ++ bvToFixedBytes 8 (wA ^^^ tape.chiMaskA))),
        (hB, packWireBytes (bvToFixedBytes 8 tape.nonceB ++ bvToFixedBytes 8 (wB ^^^ tape.chiMaskB)))]) ∧
    runOut.1.maskSessionCursor = sIdx + 1 ∧
    runOut.1.honestShares = dealHonestRssVault cIdx seedSh prfSh ∧
    runOut.1.tsig.pk = pk ∧
    runOut.1.tsig.corruptParties = [cIdx.val] ∧
    runOut.1.tsig.threshold = cl.tsig.threshold ∧
    runOut.1.tsig.numParties = cl.tsig.numParties ∧
    runOut.1.honestWal =
      { wal' with
        nextEpoch := (reqs sIdx).reqEpoch + 1
        latchedRecord := some ((reqs sIdx).reqEpoch, slhReqDigest (reqs sIdx), expSig) } := by
  intro sk pk expSig runOut
  dsimp only [runOut]
  unfold execRealSession rssSlhInteractiveProtocol passiveRushingAdv
  dsimp only
  rw [hQuorum, ite_eq_right (by decide : ¬ ((!true) = true)), hWal]
  dsimp only
  rw [hCorr, hCur, hPk, hShares]
  have hCmtLen : (unpackWireBytes (round1NonceCommit pk (reqs sIdx) sIdx cIdx.val (List.replicate 8 0))).length = 32 := by
    unfold round1NonceCommit
    rw [unpackWireBytes_packWireBytes, shake256Xof_length]
  have hVR1 :
      sharedVerifyRound1 cIdx
        { cursor := sIdx, nonceA := tape.nonceA, nonceB := tape.nonceB }
        [(cIdx.val, round1NonceCommit pk (reqs sIdx) sIdx cIdx.val (List.replicate 8 0))] =
      .inr { cursor := sIdx,
             corrR1Commit := round1NonceCommit pk (reqs sIdx) sIdx cIdx.val (List.replicate 8 0),
             nonceA := tape.nonceA, nonceB := tape.nonceB, gammaBits := 0#128 } := by
    unfold sharedVerifyRound1
    simp only [List.find?, beq_self_eq_true]
    rw [hCmtLen]
    rfl
  simp only [List.map]
  rw [hVR1]
  dsimp only
  have hBar :
      sharedPreCutBarrier cIdx deg pk (reqs sIdx)
        { cursor := sIdx,
          corrR1Commit := round1NonceCommit pk (reqs sIdx) sIdx cIdx.val (List.replicate 8 0),
          nonceA := tape.nonceA, nonceB := tape.nonceB, gammaBits := tape.gammaBits }
        [(cIdx.val, packWireBytes (List.replicate 8 0))] =
      .inr { deltas := [], cutShares := ⟨[], [], []⟩ } := by
    unfold sharedPreCutBarrier
    simp only [List.find?, beq_self_eq_true]
    rw [parseCorruptRound2Wire_zero8]
    dsimp only
    rw [byteArray_bne_self, batchDeviationPoly_nil, beq_self_eq_true]
    rfl
  rw [hBar]
  dsimp only
  have hExt := extractHonestQuorumViews_deal p.sigBytes cIdx seedSh prfSh (reqs sIdx)
  dsimp only at hExt
  rw [hExt]
  dsimp only
  let q := (honestPairForCorrupt cIdx).2.2
  let rawTag0 := (honestSessionShifts p.sigBytes cIdx (dealHonestRssVault cIdx seedSh prfSh) (reqs sIdx)).2.2.1
  let rawTag1 := (honestSessionShifts p.sigBytes cIdx (dealHonestRssVault cIdx seedSh prfSh) (reqs sIdx)).2.2.2
  have hQuorumBytes :
      rssQuorumSlhSignBytes p q (q.views seedSh) (q.views prfSh) pk.pkSeed
        constZeroRssSeedTape (reqs sIdx).msg (reqs sIdx).optRand =
      encodeSlhSig (slhSignInternal p (reqs sIdx).msg sk (reqs sIdx).optRand) := by
    have hPkSeed : pk.pkSeed = pkSeed := rfl
    rw [hPkSeed]
    exact (rss_threshold_sig_independent_of_quorum_and_sharing p hWf q q
      hSeedWf hPrfWf hSeedWf hPrfWf rfl rfl pkSeed
      constZeroRssSeedTape constZeroRssSeedTape (reqs sIdx).msg (reqs sIdx).optRand).1
  have hFaultNil :
      injectCutFaultIfNonzero p.sigBytes []
        (rssQuorumSlhSignBytes p q (q.views seedSh) (q.views prfSh) pk.pkSeed
          constZeroRssSeedTape (reqs sIdx).msg (reqs sIdx).optRand) =
      encodeSlhSig (slhSignInternal p (reqs sIdx).msg sk (reqs sIdx).optRand) := by
    unfold injectCutFaultIfNonzero
    simp [hQuorumBytes]
  let sigEnc := encodeSlhSig (slhSignInternal p (reqs sIdx).msg sk (reqs sIdx).optRand)
  let b0 := bvToFixedBytes p.sigBytes (rawTag0 ^^^ tape.cutMask0)
  let b1 := bvToFixedBytes p.sigBytes (rawTag1 ^^^ tape.cutMask1)
  let b2 := xorByteStream sigEnc (xorByteStream b0 b1)
  have hSigLen : sigEnc.length = p.sigBytes :=
    encodeSlhSig_length (slhSignInternal_wellTyped p (reqs sIdx).msg sk (reqs sIdx).optRand)
  have hb0Len : b0.length = p.sigBytes := bvToFixedBytes_length p.sigBytes _
  have hb1Len : b1.length = p.sigBytes := bvToFixedBytes_length p.sigBytes _
  have hb2Len : b2.length = p.sigBytes := by
    dsimp only [b2]
    have h01 : (xorByteStream b0 b1).length = p.sigBytes :=
      (xorByteStream_length (hb0Len.trans hb1Len.symm)).trans hb0Len
    rw [xorByteStream_length (hSigLen.trans h01.symm)]
    exact hSigLen
  have hRecCut : reconstructRssBytes ⟨b0, b1, b2⟩ = sigEnc :=
    reconstructRssBytes_masked_eq (hSigLen.trans hb0Len.symm) (hb0Len.trans hb1Len.symm)
  have hCheckOpen :
      checkRound3ActiveOpen p.sigBytes cIdx ⟨b0, b1, b2⟩
        [(cIdx.val, echoHonestRound3 p.sigBytes (buildHonestRound3Msgs cIdx ⟨b0, b1, b2⟩))] =
      some sigEnc := by
    rw [checkRound3ActiveOpen_echoHonestRound3 p.sigBytes cIdx ⟨b0, b1, b2⟩ hb0Len hb1Len hb2Len, hRecCut]
  have hDecEnc : decodeSlhSig p sigEnc = some (slhSignInternal p (reqs sIdx).msg sk (reqs sIdx).optRand) :=
    decodeSlhSig_encodeSlhSig (slhSignInternal_wellTyped p (reqs sIdx).msg sk (reqs sIdx).optRand)
  have hVerEnc : slhVerifyInternal p (reqs sIdx).msg (slhSignInternal p (reqs sIdx).msg sk (reqs sIdx).optRand) pk = true :=
    slhVerifyInternal_slhSignInternal p hWf (reconstructRssBytes seedSh) (reconstructRssBytes prfSh)
      pkSeed (reqs sIdx).msg (reqs sIdx).optRand
  have hFinOk :
      sharedFinalizeCutOpen p cIdx pk (reqs sIdx) ⟨b0, b1, b2⟩
        [(cIdx.val, echoHonestRound3 p.sigBytes (buildHonestRound3Msgs cIdx ⟨b0, b1, b2⟩))] =
      .inr expSig := by
    unfold sharedFinalizeCutOpen
    rw [hCheckOpen]
    dsimp only
    rw [hDecEnc]
    dsimp only
    rw [hVerEnc]
    rfl
  rw [hFaultNil]
  rw [hFinOk]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Crown-Jewel Theorem 3 (`threshold_slh_output_perfect_quorum_privacy`)**:
    **Exact Statistical Distance `0` Quorum & Secret-Sharing Privacy for 2-of-3 RSS and `t`-of-`n` Shamir `SLH-DSA`**:
    For ANY well-formed NIST `FIPS 205` parameter set `p`, ANY underlying secret key `(skSeed, skPrf, pkSeed)`,
    ANY message `msg`, ANY hedged randomness family `hedge : Fin N → List UInt8` (`0 < N`), and ANY
    wire-signature distinguisher `D : ByteArray → Bool`:
    1. **Unified Hedged Statistical Distance `0` (`SlhThresholdRun`)**: Across ANY two families of
       threshold executions `run₁, run₂ : Fin N → SlhThresholdRun p skSeed skPrf pkSeed` (each coin
       instantiating ANY 2-of-3 RSS quorum/sharing `SlhThresholdRun.ofRss` OR ANY `t`-of-`n` Shamir
       quorum/sharing `SlhThresholdRun.ofShamir`), the emitted wire `ByteArray` equals standalone
       single-signer `packWireBytes (encodeSlhSig (slhSignInternal p msg sk (hedge i)))` pointwise AND
       achieves **`natAbsDiff = 0`** and **`ratLe (rationalAcceptDiff ...) (0, 1)`**!
    2. **2-of-3 RSS Cross-Quorum & Cross-Sharing Wire Identity (`RealProtocolExec`)**: For ANY two
       quorum complements `cIdx₁, cIdx₂ : Fin 3` and ANY two valid sharings `(seed₁, prf₁)`, `(seed₂, prf₂)`
       reconstructing the same `(skSeed, skPrf)`, the interactive 3-round protocol `rssSlhInteractiveProtocol`
       emits the **identical** `SessionOutcome.signOk` wire `ByteArray`!
    3. **`t`-of-`n` SPDZ / Shamir Cross-Ring, Cross-Threshold, Cross-Quorum Wire Identity**: For ANY
       two `LawfulCommRing`s `R₁, R₂`, thresholds `t₁, t₂`, quorums `Q₁, Q₂`, and polynomial sharings
       reconstructing the same `(skSeed, skPrf)`, the wire `ByteArray` signatures are bit-for-bit identical! -/
theorem threshold_slh_output_perfect_quorum_privacy
    {R₁ R₂ : Type} [LawfulCommRing R₁] [LawfulCommRing R₂]
    (p : Fips205Params) (hWf : p.wellFormed = true)
    {skSeed skPrf : List UInt8} (pkSeed msg optRand : List UInt8) :
    let sk := (slhKeygenInternal p skSeed skPrf pkSeed).1
    let standaloneWire := fun h : List UInt8 =>
      packWireBytes (encodeSlhSig (slhSignInternal p msg sk h))
    -- (1) Exact statistical distance `0` across arbitrary hedged `SlhThresholdRun` distributions:
    (∀ (N : Nat) (_hN : 0 < N)
       (run₁ run₂ : Fin N → SlhThresholdRun p skSeed skPrf pkSeed)
       (hedge : Fin N → List UInt8) (D : ByteArray → Bool),
       let wire₁ := fun i : Fin N => packWireBytes ((run₁ i).signBytes msg (hedge i))
       let wire₂ := fun i : Fin N => packWireBytes ((run₂ i).signBytes msg (hedge i))
       let single := fun i : Fin N => standaloneWire (hedge i)
       (∀ i : Fin N, wire₁ i = single i ∧ wire₂ i = single i) ∧
       natAbsDiff (distAcceptCount N wire₁ D) (distAcceptCount N single D) = 0 ∧
       ratLe (rationalAcceptDiff N wire₁ N wire₂ D) (0, 1) ∧
       ratLe (rationalAcceptDiff N wire₁ N single D) (0, 1)) ∧
    -- (2) Interactive 3-round `rssSlhInteractiveProtocol` wire output independence across quorums & sharings:
    (∀ (cIdx₁ cIdx₂ : Fin 3) (deg : Nat)
       {seed₁ prf₁ seed₂ prf₂ : RssByteShares}
       (_hS₁ : seed₁.WellFormed) (_hP₁ : prf₁.WellFormed)
       (_hS₂ : seed₂.WellFormed) (_hP₂ : prf₂.WellFormed)
       (_hSeedEq₁ : reconstructRssBytes seed₁ = skSeed)
       (_hPrfEq₁  : reconstructRssBytes prf₁ = skPrf)
       (_hSeedEq₂ : reconstructRssBytes seed₂ = skSeed)
       (_hPrfEq₂  : reconstructRssBytes prf₂ = skPrf)
       (tape₁ tape₂ : RssSlhSessionTape p.sigBytes),
       let pk := (slhKeygenInternal p skSeed skPrf pkSeed).2
       let reqs₁ : Nat → SessionScheduleReq := fun _ =>
         ⟨0, 0, msg, optRand, [(honestPairForCorrupt cIdx₁).1, (honestPairForCorrupt cIdx₁).2.1]⟩
       let reqs₂ : Nat → SessionScheduleReq := fun _ =>
         ⟨0, 0, msg, optRand, [(honestPairForCorrupt cIdx₂).1, (honestPairForCorrupt cIdx₂).2.1]⟩
       let cl₁ : RealClusterState SlhPublicKey RssPartyKeyShare :=
         ⟨⟨pk, 2, 3, [cIdx₁.val], [], []⟩, initWalLatchState (slhPkDigest pk), 0,
          dealHonestRssVault cIdx₁ seed₁ prf₁⟩
       let cl₂ : RealClusterState SlhPublicKey RssPartyKeyShare :=
         ⟨⟨pk, 2, 3, [cIdx₂.val], [], []⟩, initWalLatchState (slhPkDigest pk), 0,
          dealHonestRssVault cIdx₂ seed₂ prf₂⟩
       let out₁ := (execRealSession (rssSlhInteractiveProtocol p cIdx₁ deg)
                     (passiveRushingAdv p pk reqs₁) cl₁ 0 tape₁).2.2.outcome
       let out₂ := (execRealSession (rssSlhInteractiveProtocol p cIdx₂ deg)
                     (passiveRushingAdv p pk reqs₂) cl₂ 0 tape₂).2.2.outcome
       out₁ = .signOk (standaloneWire optRand) ∧ out₁ = out₂) ∧
    -- (3) `t`-of-`n` Shamir cross-quorum / cross-sharing wire `ByteArray` identity:
    (∀ (decode₁ : R₁ → UInt8) (t₁ : Nat) (Q₁ : ShamirQuorum R₁ t₁) (seedPolys₁ prfPolys₁ : List (List R₁))
       (_hSD₁ : ∀ c ∈ seedPolys₁, c.length ≤ t₁) (_hPD₁ : ∀ c ∈ prfPolys₁, c.length ≤ t₁)
       (decode₂ : R₂ → UInt8) (t₂ : Nat) (Q₂ : ShamirQuorum R₂ t₂) (seedPolys₂ prfPolys₂ : List (List R₂))
       (_hSD₂ : ∀ c ∈ seedPolys₂, c.length ≤ t₂) (_hPD₂ : ∀ c ∈ prfPolys₂, c.length ≤ t₂)
       (_hSeed₁ : shamirSecretBytes decode₁ seedPolys₁ = skSeed)
       (_hPrf₁  : shamirSecretBytes decode₁ prfPolys₁ = skPrf)
       (_hSeed₂ : shamirSecretBytes decode₂ seedPolys₂ = skSeed)
       (_hPrf₂  : shamirSecretBytes decode₂ prfPolys₂ = skPrf)
       (o₁ o₂ : SlhMpcOracles)
       (_hO₁ : o₁.MatchesKey p
         (shamirReconstructBytes decode₁ Q₁.lambdas (shamirQuorumShares Q₁.pts seedPolys₁))
         (shamirReconstructBytes decode₁ Q₁.lambdas (shamirQuorumShares Q₁.pts prfPolys₁)) pkSeed)
       (_hO₂ : o₂.MatchesKey p
         (shamirReconstructBytes decode₂ Q₂.lambdas (shamirQuorumShares Q₂.pts seedPolys₂))
         (shamirReconstructBytes decode₂ Q₂.lambdas (shamirQuorumShares Q₂.pts prfPolys₂)) pkSeed),
       let shWire₁ := packWireBytes (thresholdSlhSignBytes p o₁ msg (slhKeygenMpc p o₁ pkSeed) optRand)
       let shWire₂ := packWireBytes (thresholdSlhSignBytes p o₂ msg (slhKeygenMpc p o₂ pkSeed) optRand)
       shWire₁ = standaloneWire optRand ∧ shWire₁ = shWire₂) := by
  intro sk standaloneWire
  refine ⟨?_, ?_, ?_⟩
  · intro N hN run₁ run₂ hedge D wire₁ wire₂ single
    have hPt : ∀ i : Fin N, wire₁ i = single i ∧ wire₂ i = single i := by
      intro i
      have h1 := (threshold_sig_perfectly_indistinguishable_from_single_signer p hWf
        (run₁ i) (run₁ i) msg (hedge i)).1
      have h2 := (threshold_sig_perfectly_indistinguishable_from_single_signer p hWf
        (run₂ i) (run₂ i) msg (hedge i)).1
      exact ⟨congrArg packWireBytes h1, congrArg packWireBytes h2⟩
    have hCnt1 : distAcceptCount N wire₁ D = distAcceptCount N single D := by
      unfold distAcceptCount
      exact finSum_congr (fun i => by rw [(hPt i).1])
    have hCnt2 : distAcceptCount N wire₂ D = distAcceptCount N single D := by
      unfold distAcceptCount
      exact finSum_congr (fun i => by rw [(hPt i).2])
    have hAbs0 : ∀ a : Nat, natAbsDiff a a = 0 := fun a => by unfold natAbsDiff; simp
    refine ⟨hPt, ?_, ?_, ?_⟩
    · rw [hCnt1]; exact hAbs0 _
    · unfold ratLe rationalAcceptDiff
      dsimp only
      rw [hCnt1, hCnt2, hAbs0]
      exact ⟨Nat.mul_pos hN hN, Nat.zero_lt_one, Nat.zero_le _⟩
    · unfold ratLe rationalAcceptDiff
      dsimp only
      rw [hCnt1, hAbs0]
      exact ⟨Nat.mul_pos hN hN, Nat.zero_lt_one, Nat.zero_le _⟩
  · intro cIdx₁ cIdx₂ deg seed₁ prf₁ seed₂ prf₂ hS₁ hP₁ hS₂ hP₂
          hSeedEq₁ hPrfEq₁ hSeedEq₂ hPrfEq₂ tape₁ tape₂ pk reqs₁ reqs₂ cl₁ cl₂ out₁ out₂
    have hQuorumAll : ∀ (cIdx : Fin 3),
        validThresholdApproval (⟨pk, 2, 3, [cIdx.val], [], []⟩ : IdealTsigState SlhPublicKey (List UInt8))
          [(honestPairForCorrupt cIdx).1, (honestPairForCorrupt cIdx).2.1] = true := by
      intro cIdx
      rcases cIdx with ⟨_ | _ | _ | n, hv⟩
      · have hc : (⟨0, hv⟩ : Fin 3).val = 0 := rfl
        unfold honestPairForCorrupt
        rw [hc]; simp [validThresholdApproval]
      · have hc : (⟨0 + 1, hv⟩ : Fin 3).val = 1 := rfl
        unfold honestPairForCorrupt
        rw [hc]; simp [validThresholdApproval]
      · have hc : (⟨0 + 1 + 1, hv⟩ : Fin 3).val = 2 := rfl
        unfold honestPairForCorrupt
        rw [hc]; simp [validThresholdApproval]
      · exact False.elim (Nat.not_lt_zero n (Nat.lt_of_add_lt_add_right hv))
    have hWalInit₁ :
        walPreSignStep (initWalLatchState (slhPkDigest pk)) (slhPkDigest pk) 0 (slhReqDigest (reqs₁ 0)) =
        .ok (initWalLatchState (slhPkDigest pk)) (.authorizedFresh 0) := by
      unfold walPreSignStep initWalLatchState
      simp
    have hWalInit₂ :
        walPreSignStep (initWalLatchState (slhPkDigest pk)) (slhPkDigest pk) 0 (slhReqDigest (reqs₂ 0)) =
        .ok (initWalLatchState (slhPkDigest pk)) (.authorizedFresh 0) := by
      unfold walPreSignStep initWalLatchState
      simp
    have hPk₁ : cl₁.tsig.pk = (slhKeygenInternal p (reconstructRssBytes seed₁) (reconstructRssBytes prf₁) pkSeed).2 := by
      dsimp only [cl₁, pk]; rw [hSeedEq₁, hPrfEq₁]
    have hPk₂ : cl₂.tsig.pk = (slhKeygenInternal p (reconstructRssBytes seed₂) (reconstructRssBytes prf₂) pkSeed).2 := by
      dsimp only [cl₂, pk]; rw [hSeedEq₂, hPrfEq₂]
    have hRun₁ : out₁ = .signOk (standaloneWire optRand) := by
      dsimp only [out₁, pk, reqs₁, standaloneWire, sk]
      have hOk := (execRealSession_passiveRushingAdv_ok p hWf cIdx₁ deg 0 hS₁ hP₁ pkSeed reqs₁ cl₁
        (initWalLatchState (slhPkDigest pk)) tape₁ hPk₁ rfl rfl rfl (hQuorumAll cIdx₁) hWalInit₁).2.1
      dsimp only [reqs₁] at hOk
      rw [hSeedEq₁, hPrfEq₁] at hOk
      exact hOk
    have hRun₂ : out₂ = .signOk (standaloneWire optRand) := by
      dsimp only [out₂, pk, reqs₂, standaloneWire, sk]
      have hOk := (execRealSession_passiveRushingAdv_ok p hWf cIdx₂ deg 0 hS₂ hP₂ pkSeed reqs₂ cl₂
        (initWalLatchState (slhPkDigest pk)) tape₂ hPk₂ rfl rfl rfl (hQuorumAll cIdx₂) hWalInit₂).2.1
      dsimp only [reqs₂] at hOk
      rw [hSeedEq₂, hPrfEq₂] at hOk
      exact hOk
    exact ⟨hRun₁, hRun₁.trans hRun₂.symm⟩
  · intro decode₁ t₁ Q₁ seedPolys₁ prfPolys₁ hSD₁ hPD₁
          decode₂ t₂ Q₂ seedPolys₂ prfPolys₂ hSD₂ hPD₂
          hSeed₁ hPrf₁ hSeed₂ hPrf₂ o₁ o₂ hO₁ hO₂ shWire₁ shWire₂
    have hSh := shamir_threshold_sig_independent_of_threshold_quorum_and_sharing p hWf
      decode₁ t₁ Q₁ seedPolys₁ prfPolys₁ hSD₁ hPD₁
      decode₂ t₂ Q₂ seedPolys₂ prfPolys₂ hSD₂ hPD₂
      (hSeed₁.trans hSeed₂.symm) (hPrf₁.trans hPrf₂.symm)
      pkSeed o₁ o₂ hO₁ hO₂ msg optRand
    have h1 : shWire₁ = standaloneWire optRand := by
      dsimp only [shWire₁, standaloneWire, sk]
      rw [hSh.1, hSeed₁, hPrf₁]
    exact ⟨h1, congrArg packWireBytes hSh.2⟩

/-- **Inhabitedness Witness for Theorem 3 (`inhabited_threshold_slh_quorum_privacy`)**:
    Exhibits two distinct 2-of-3 RSS quorums (`cIdx = 0` vs `cIdx = 2`, i.e., `.p12 ≠ .p01`) with
    distinct secret sharings AND two distinct 2-of-3 Goldilocks Shamir quorums (`{1, 2} ≠ {2, 3}`)
    with distinct share evaluations emitting bit-identical `slhDsaShake128f` wire `ByteArray`s! -/
