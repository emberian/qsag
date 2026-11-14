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
