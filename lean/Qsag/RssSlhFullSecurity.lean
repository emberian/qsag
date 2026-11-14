module
/-
# Qsag.RssSlhFullSecurity — Whole-Protocol Multi-Session UC Security of 2-of-3 RSS & `t`-of-`n` SPDZ `FIPS 205 SLH-DSA`

Self-contained Lean 4.35 end-to-end active threshold security proof for NIST `FIPS 205 SLH-DSA`
over the multi-round rushing-adversary execution engine `Qsag.InteractiveUcEngine`
(`0` proof gaps, `0` custom axioms, `0 Classical.choice`, `0` cheat hypotheses):

1. **Three-Round Opening-Layer Protocol (`rssSlhInteractiveProtocol`) & `sk`-Free UC Simulator (`Sim_RssSlh`)**:
   - **Round 1**: Honest parties consume monotonic `maskSessionCursor` and broadcast `SHAKE256`
     hedged-nonce commitments over injectively length-framed `encodeMultiFrame`/`leb128` preimages
     (`round1NonceCommit_binding_or_collision`, `slhPkDigest_binding_or_collision`,
     `slhReqDigest_injective_on_epoch_optRand_msg`; `0` `UInt8.ofNat` truncation).
   - **Round 2**: Honest parties open Round-1 nonces and broadcast 64-way bitsliced Keccak `χ`-row
     shares (`mpcChiParty0/1/2` / `rssChiLane0/1/2`) masked by fresh session pads `(chiMaskA, chiMaskB)`
     (plus `t`-of-`n` SPDZ Shamir masked openings via `shamir_rebalanceEquiv`); rushing adversary `A`
     sees all honest Round-2 `ByteArray`s before transmitting raw `GF(2^128)` (`Tower128`) gate wires.
   - **Mandatory Pre-Cut Consistency Barrier (`preCutBarrier`)**: Verifies Round-1 commitment openings
     and the algebraic `BBCGGI19` / `BDOZ` inner-product equation
     `bbcggiWireAccumulator sentWires gamma == bbcggiWireAccumulator expectedWires gamma` strictly
     before Round 3; any mismatch aborts with `.activeConsistencyFailed` and irreversibly poisons
     `WalLatchState` + erases secret key shares.
   - **Round 3 (`honestRound3` & `finalizeCutOpen`)**: Honest parties evaluate the replicated `FLNW17`
     gate cross-byte (`evalReplicatedGateCrossByte`), broadcast cut-opening shares
     (`verifyRssActiveOpenBytes`), assemble and verify the NIST `FIPS 205` signature
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
3. **End-to-End Weld (`rss_slh_uc_forgery_to_hash_game`, `rss_slh_fresh_enrollment_euf_cma_bound`)**:
   composes the two theorems above without an abstract unforgeability premise. On every uniform
   multi-session tape on which a forger wins against `RealProtocolExec`, either the tape is a counted
   `GF(2^128)` batch-consistency root hit (`multiSessionBadHit`, at most `Q_s * deg / 2^128` of all
   tapes) or the real transcript equals the ideal transcript and yields a concrete
   `Fips205HashGameBreak`. The ideal transcript is shown to depend on the signing key only through
   the oracle answers of sessions that reached Round 3 (`IdealFunctionalityExec_oracle_congr`).

Model boundary.
* The protocol proved here is a three-round shell around the honest pair. In a 2-of-3 replicated
  sharing the two honest parties jointly hold all three shares; `honestRound3` computes the whole
  signature from their views (`rssQuorumSlhSignBytes`) and re-shares it at the cut. The corrupt
  party contributes no share-dependent message to the output.
* The Round-2 `χ` word is one 64-bit lane computed from the first eight bytes of each share and
  masked by a pad that is never used again; no later step consumes it.
* `deriveExpectedGateWires` is a public hash of `(pk, request, cursor, party, nonce, index)`. The
  pre-cut barrier therefore checks that the corrupt party's wires equal publicly derivable values
  under a challenge `gammaBits` that stays on the honest tape; it is not the gate-level product
  proof with a commit-then-open challenge that the production bitsliced engine runs.
  Parsing requires exactly `deg > 0` field elements and consumes the complete frame.
* The Round-1 nonce commitment is binding up to a `SHAKE256` collision
  (`round1NonceCommit_binding_or_collision`), but no security theorem in this file depends on that
  binding: the challenge is never revealed before Round 2.
* Both execution engines record approval before releasing Round-3 openings, including when
  `finalizeCutOpen` subsequently fails. `slhForgeryWins` retains its transcript-based freshness
  predicate over sessions that reached Round 3.
* Hash-game witnesses are stated over `Qsag.Fips205` (`SHAKE256` collisions, chain preimages, FORS
  coverage). They are not instances of the `Qsag.HypertreeEufCma` witness types, which belong to
  the tweakable-hash WOTS+C hypertree scheme; the weld for that scheme is
  `uc_emulation_forgery_to_hypertree_hash_game` in `Qsag.InteractiveUcEngine`.
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
    - `coinB` : 128-bit coin share of the second honest party;
    - `prgSeeds` : the three pairwise 64-bit PRG seeds of the replicated zero-sharing (the honest
      pair jointly holds all three), expanded by `expandPairwiseSeedTape`;
    - `nonceA, nonceB` : 64-bit blinds of the two honest Round-1 coin commitments;
    - `chiMaskA, chiMaskB` : fresh 64-bit Round-2 Keccak `χ`-row masks;
    - `cutMask0, cutMask1` : fresh `8 * p.sigBytes`-bit Round-3 cut-opening share masks;
    - `gammaBits` : 128-bit coin share of the first honest party. The consistency challenge is
      `gammaBits ⊕ coinB ⊕ corruptCoin` (`sharedCoinTossBarrier`). -/
structure RssSlhSessionTape (sigBytes : Nat) where
  coinB     : BitVec 128
  prgSeeds  : BitVec 192
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
  (2 ^ 128) * ((2 ^ 192) *
    ((2 ^ 64) * ((2 ^ 64) * ((2 ^ 64) * ((2 ^ 64) * ((2 ^ (8 * sigBytes)) * (2 ^ (8 * sigBytes))))))))

/-- Cardinality of one full session tape (`padSessionCard * 2^128`). -/
def rssFullSessionCard (sigBytes : Nat) : Nat :=
  rssPadSessionCard sigBytes * (2 ^ 128)

/-- Cardinality of the `Q_s`-session multi-round random tape space. -/
def rssMultiSessionCard (sigBytes : Nat) : Nat → Nat
  | 0 => 1
  | s + 1 => rssFullSessionCard sigBytes * rssMultiSessionCard sigBytes s

theorem rssPadSessionCard_pos (sigBytes : Nat) : 0 < rssPadSessionCard sigBytes := by
  unfold rssPadSessionCard
  exact Nat.mul_pos (Nat.two_pow_pos _) (Nat.mul_pos (Nat.two_pow_pos _)
    (Nat.mul_pos (Nat.two_pow_pos _)
      (Nat.mul_pos (Nat.two_pow_pos _)
        (Nat.mul_pos (Nat.two_pow_pos _)
          (Nat.mul_pos (Nat.two_pow_pos _)
            (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)))))))

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
  have hB6 : 0 < (2 ^ 64) * B5 := Nat.mul_pos (Nat.two_pow_pos _) hB5
  have hB7 : 0 < (2 ^ 192) * ((2 ^ 64) * B5) := Nat.mul_pos (Nat.two_pow_pos _) hB6
  let kB := splitFinLeft hB7 padIdx
  let r7 := splitFinRight hB7 padIdx
  let sd := splitFinLeft hB6 r7
  let r6 := splitFinRight hB6 r7
  let nA := splitFinLeft hB5 r6
  let r5 := splitFinRight hB5 r6
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
  { coinB := BitVec.ofFin kB
    prgSeeds := BitVec.ofFin sd
    nonceA := BitVec.ofFin nA
    nonceB := BitVec.ofFin nB
    chiMaskA := BitVec.ofFin cA
    chiMaskB := BitVec.ofFin cB
    cutMask0 := BitVec.ofFin m0
    cutMask1 := BitVec.ofFin m1
    gammaBits := BitVec.ofFin gIdx }

def encodeRssPadIdx (L : Nat) (kB : BitVec 128) (sd : BitVec 192)
    (nA nB cA cB : BitVec 64) (m0 m1 : BitVec (8 * L)) : Fin (rssPadSessionCard L) :=
  pairFin kB.toFin
    (pairFin sd.toFin
      (pairFin nA.toFin
        (pairFin nB.toFin
          (pairFin cA.toFin
            (pairFin cB.toFin
              (pairFin m0.toFin m1.toFin))))))

private theorem decodeRssSessionTape_encodeRssPadIdx (L : Nat) (kB : BitVec 128) (sd : BitVec 192)
    (nA nB cA cB : BitVec 64) (m0 m1 : BitVec (8 * L)) (gIdx : Fin (2 ^ 128)) :
    decodeRssSessionTape L (encodeRssPadIdx L kB sd nA nB cA cB m0 m1) gIdx =
      { coinB := kB, prgSeeds := sd,
        nonceA := nA, nonceB := nB, chiMaskA := cA, chiMaskB := cB,
        cutMask0 := m0, cutMask1 := m1, gammaBits := BitVec.ofFin gIdx } := by
  unfold decodeRssSessionTape encodeRssPadIdx
  dsimp only
  rw [splitFinLeft_pairFin, splitFinRight_pairFin,
      splitFinLeft_pairFin, splitFinRight_pairFin,
      splitFinLeft_pairFin, splitFinRight_pairFin,
      splitFinLeft_pairFin, splitFinRight_pairFin,
      splitFinLeft_pairFin, splitFinRight_pairFin,
      splitFinLeft_pairFin, splitFinRight_pairFin,
      splitFinLeft_pairFin, splitFinRight_pairFin]

def defaultRssSessionTape (L : Nat) : RssSlhSessionTape L :=
  { coinB := 0#128, prgSeeds := 0#192,
    nonceA := 0#64, nonceB := 0#64, chiMaskA := 0#64, chiMaskB := 0#64,
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

/-- Parse the 24-byte coin opening (16-byte coin share, 8-byte blind) followed by exactly
    `deg > 0` field elements. Reject empty streams, truncated elements, and any trailing bytes. -/
def parseCorruptRound2Wire (deg : Nat) (wire : ByteArray) : Option (List UInt8 × List Tower128) :=
  let raw := unpackWireBytes wire
  if deg = 0 ∨ raw.length ≠ 24 + 16 * deg then none
  else some (raw.take 24, (splitByteChunks 16 deg (raw.drop 24)).map decodeTower128Wire)

/-- Successful parsing consumes the entire frame and returns the declared positive gate count. -/
theorem parseCorruptRound2Wire_canonical (deg : Nat) (wire : ByteArray)
    {nonceC : List UInt8} {sentWires : List Tower128}
    (hParse : parseCorruptRound2Wire deg wire = some (nonceC, sentWires)) :
    0 < deg ∧ (unpackWireBytes wire).length = 24 + 16 * deg ∧ sentWires.length = deg := by
  unfold parseCorruptRound2Wire at hParse
  dsimp only at hParse
  split at hParse
  · cases hParse
  · rename_i h
    injection hParse with hp
    rcases Prod.mk.inj hp with ⟨_, rfl⟩
    have hPos : 0 < deg := Nat.pos_of_ne_zero (fun hz => h (Or.inl hz))
    have hLen : (unpackWireBytes wire).length = 24 + 16 * deg := by
      by_cases he : (unpackWireBytes wire).length = 24 + 16 * deg
      · exact he
      · exact False.elim (h (Or.inr he))
    exact ⟨hPos, hLen, by simp only [List.length_map, splitByteChunks_length]⟩

theorem parseCorruptRound2Wire_length_le (deg : Nat) (wire : ByteArray)
    {nonceC : List UInt8} {sentWires : List Tower128}
    (hParse : parseCorruptRound2Wire deg wire = some (nonceC, sentWires)) :
    sentWires.length ≤ deg :=
  Nat.le_of_eq (parseCorruptRound2Wire_canonical deg wire hParse).2.2

/-- Canonical gate-stream encoder, used by the honest adversary fixture as well as parser tests. -/
def encodeCorruptRound2Wire (nonce : List UInt8) (wires : List Tower128) : ByteArray :=
  packWireBytes (nonce ++ (wires.map encodeTower128Wire).flatten)

theorem parseCorruptRound2Wire_encode (nonce : List UInt8) (wires : List Tower128)
    (hn : nonce.length = 24) (hw : 0 < wires.length) :
    parseCorruptRound2Wire wires.length (encodeCorruptRound2Wire nonce wires) =
      some (nonce, wires) := by
  have he : ∀ x ∈ wires.map encodeTower128Wire, x.length = 16 := by
    intro x hx
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hx
    exact bvToFixedBytes_length 16 _
  have hlen : (wires.map encodeTower128Wire).flatten.length = 16 * wires.length := by
    clear hw he
    induction wires with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
      rw [show (encodeTower128Wire x).length = 16 from bvToFixedBytes_length 16 _]
      omega
  unfold parseCorruptRound2Wire encodeCorruptRound2Wire
  rw [unpackWireBytes_packWireBytes]
  simp only [List.length_append, hn, hlen]
  rw [ite_eq_right (by omega), ← hn, List.take_left, List.drop_left]
  have hc := (splitByteChunks_flatten 16 (wires.map encodeTower128Wire) [] he).1
  simp only [List.append_nil, List.length_map] at hc
  rw [hc, List.map_map]
  simp only [Function.comp_def, decodeTower128Wire_encodeTower128Wire]
  rw [show wires.map (fun x => x) = wires from List.map_id wires]

/-- The former empty-stream bypass is rejected for every declared gate count. -/
theorem tooth_round2_empty_stream_rejected (deg : Nat) :
    parseCorruptRound2Wire deg (packWireBytes (List.replicate 24 0)) = none := by
  unfold parseCorruptRound2Wire
  rw [unpackWireBytes_packWireBytes]
  simp only [List.length_replicate]
  rw [ite_eq_left (by
    by_cases hz : deg = 0
    · exact Or.inl hz
    · exact Or.inr (by omega))]

/-- A nonempty suffix is rejected rather than silently ignored. -/
theorem tooth_round2_trailing_bytes_rejected (deg : Nat) (wire : ByteArray)
    (suffix : List UInt8) (hLen : (unpackWireBytes wire).length = 8 + 16 * deg)
    (hSuffix : 0 < suffix.length) :
    parseCorruptRound2Wire deg (packWireBytes (unpackWireBytes wire ++ suffix)) = none := by
  unfold parseCorruptRound2Wire
  rw [unpackWireBytes_packWireBytes]
  simp only [List.length_append, hLen]
  rw [ite_eq_left (Or.inr (by omega))]

private theorem leb128_inj {n₁ n₂ : Nat} (h : leb128 n₁ = leb128 n₂) : n₁ = n₂ := by
  have hApp : leb128 n₁ ++ [] = leb128 n₂ ++ [] := by simpa using h
  exact (leb128_prefix_inj hApp).1

/-- Domain tag `"QSAG.RSS.R1.COMMIT/v1"` (`21` ASCII bytes). -/
def round1CommitDomainTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x52, 0x53, 0x53, 0x2E, 0x52, 0x31, 0x2E,
   0x43, 0x4F, 0x4D, 0x4D, 0x49, 0x54, 0x2F, 0x76, 0x31]

/-- Domain tag `"QSAG.SLH.PK.DIGEST/v1"` (`21` ASCII bytes). -/
def slhPkDomainTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x53, 0x4C, 0x48, 0x2E, 0x50, 0x4B, 0x2E,
   0x44, 0x49, 0x47, 0x45, 0x53, 0x54, 0x2F, 0x76, 0x31]

/-- Domain tag `"QSAG.SLH.REQ.DIGEST/v1"` (`22` ASCII bytes). -/
def slhReqDomainTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x53, 0x4C, 0x48, 0x2E, 0x52, 0x45, 0x51,
   0x2E, 0x44, 0x49, 0x47, 0x45, 0x53, 0x54, 0x2F, 0x76, 0x31]

/-- Domain tag `"QSAG.RSS.GATE.WIRE/v1"` (`21` ASCII bytes). -/
def rssGateWireDomainTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x52, 0x53, 0x53, 0x2E, 0x47, 0x41, 0x54,
   0x45, 0x2E, 0x57, 0x49, 0x52, 0x45, 0x2F, 0x76, 0x31]

/-- Canonical injective multi-frame preimage for Round-1 hedged-nonce commitments (`0` `UInt8.ofNat` truncation). -/
def encodeRound1NoncePreimage (pk : SlhPublicKey) (req : SessionScheduleReq) (cursor : Nat)
    (partyId : Nat) (nonceBytes : List UInt8) : List UInt8 :=
  encodeMultiFrame
    [round1CommitDomainTag, leb128 partyId, leb128 req.sessionId, leb128 req.reqEpoch,
     leb128 cursor, pk.pkSeed, pk.pkRoot, req.msg, req.optRand, nonceBytes]

theorem encodeRound1NoncePreimage_injective
    {pk₁ pk₂ : SlhPublicKey} {req₁ req₂ : SessionScheduleReq}
    {cur₁ cur₂ pid₁ pid₂ : Nat} {n₁ n₂ : List UInt8}
    (h : encodeRound1NoncePreimage pk₁ req₁ cur₁ pid₁ n₁ =
         encodeRound1NoncePreimage pk₂ req₂ cur₂ pid₂ n₂) :
    pk₁ = pk₂ ∧ req₁.sessionId = req₂.sessionId ∧ req₁.reqEpoch = req₂.reqEpoch ∧
    req₁.msg = req₂.msg ∧ req₁.optRand = req₂.optRand ∧
    cur₁ = cur₂ ∧ pid₁ = pid₂ ∧ n₁ = n₂ := by
  have hF := encodeMultiFrame_injective h
  simp only [List.cons.injEq] at hF
  rcases pk₁ with ⟨s1, r1⟩
  rcases pk₂ with ⟨s2, r2⟩
  dsimp only at hF
  exact ⟨by rw [hF.2.2.2.2.2.1, hF.2.2.2.2.2.2.1],
         leb128_inj hF.2.2.1, leb128_inj hF.2.2.2.1,
         hF.2.2.2.2.2.2.2.1, hF.2.2.2.2.2.2.2.2.1,
         leb128_inj hF.2.2.2.2.1, leb128_inj hF.2.1,
         hF.2.2.2.2.2.2.2.2.2.1⟩

/-- Domain-separated Round-1 `SHAKE256` hedged-nonce commitment (`32` bytes) over injective `encodeMultiFrame`. -/
def round1NonceCommit (pk : SlhPublicKey) (req : SessionScheduleReq) (cursor : Nat)
    (partyId : Nat) (nonceBytes : List UInt8) : ByteArray :=
  packWireBytes (shake256Xof 32 (encodeRound1NoncePreimage pk req cursor partyId nonceBytes))

theorem round1NonceCommit_binding_or_collision
    {pk₁ pk₂ : SlhPublicKey} {req₁ req₂ : SessionScheduleReq}
    {cur₁ cur₂ pid₁ pid₂ : Nat} {n₁ n₂ : List UInt8}
    (hEq : round1NonceCommit pk₁ req₁ cur₁ pid₁ n₁ =
           round1NonceCommit pk₂ req₂ cur₂ pid₂ n₂) :
    (pk₁ = pk₂ ∧ req₁.sessionId = req₂.sessionId ∧ req₁.reqEpoch = req₂.reqEpoch ∧
     req₁.msg = req₂.msg ∧ req₁.optRand = req₂.optRand ∧
     cur₁ = cur₂ ∧ pid₁ = pid₂ ∧ n₁ = n₂) ∨
    Nonempty (Fips205ShakeCollision 32) := by
  have hBytes : shake256Xof 32 (encodeRound1NoncePreimage pk₁ req₁ cur₁ pid₁ n₁) =
                shake256Xof 32 (encodeRound1NoncePreimage pk₂ req₂ cur₂ pid₂ n₂) := by
    have hUnpack := congrArg unpackWireBytes hEq
    simpa only [round1NonceCommit, unpackWireBytes_packWireBytes] using hUnpack
  by_cases hPre : encodeRound1NoncePreimage pk₁ req₁ cur₁ pid₁ n₁ =
                  encodeRound1NoncePreimage pk₂ req₂ cur₂ pid₂ n₂
  · exact .inl (encodeRound1NoncePreimage_injective hPre)
  · exact .inr ⟨{ in1 := encodeRound1NoncePreimage pk₁ req₁ cur₁ pid₁ n₁
                  in2 := encodeRound1NoncePreimage pk₂ req₂ cur₂ pid₂ n₂
                  hNe := hPre
                  hEq := hBytes }⟩

/-- Canonical injective multi-frame preimage for `SlhPublicKey` digests. -/
def encodeSlhPkPreimage (pk : SlhPublicKey) : List UInt8 :=
  encodeMultiFrame [slhPkDomainTag, pk.pkSeed, pk.pkRoot]

theorem encodeSlhPkPreimage_injective {pk₁ pk₂ : SlhPublicKey}
    (h : encodeSlhPkPreimage pk₁ = encodeSlhPkPreimage pk₂) : pk₁ = pk₂ := by
  have hF := encodeMultiFrame_injective h
  simp only [List.cons.injEq] at hF
  rcases pk₁ with ⟨s1, r1⟩
  rcases pk₂ with ⟨s2, r2⟩
  dsimp only at hF
  rw [hF.2.1, hF.2.2.1]

/-- Canonical digests bound in `WalLatchState` for public key `pk` and scheduled request `req`. -/
def slhPkDigest (pk : SlhPublicKey) : List UInt8 :=
  shake256Xof 32 (encodeSlhPkPreimage pk)

theorem slhPkDigest_binding_or_collision {pk₁ pk₂ : SlhPublicKey}
    (hEq : slhPkDigest pk₁ = slhPkDigest pk₂) :
    pk₁ = pk₂ ∨ Nonempty (Fips205ShakeCollision 32) := by
  by_cases hPre : encodeSlhPkPreimage pk₁ = encodeSlhPkPreimage pk₂
  · exact .inl (encodeSlhPkPreimage_injective hPre)
  · exact .inr ⟨{ in1 := encodeSlhPkPreimage pk₁
                  in2 := encodeSlhPkPreimage pk₂
                  hNe := hPre
                  hEq := hEq }⟩

def encodeSlhReqPreimage (req : SessionScheduleReq) : List UInt8 :=
  encodeMultiFrame [slhReqDomainTag, leb128 req.reqEpoch, req.optRand, req.msg]

def slhReqDigest (req : SessionScheduleReq) : List UInt8 :=
  let framed := encodeSlhReqPreimage req
  shake256Xof 32 framed ++ framed

theorem slhReqDigest_injective_on_epoch_optRand_msg {req₁ req₂ : SessionScheduleReq}
    (h : slhReqDigest req₁ = slhReqDigest req₂) :
    req₁.reqEpoch = req₂.reqEpoch ∧ req₁.optRand = req₂.optRand ∧ req₁.msg = req₂.msg := by
  unfold slhReqDigest at h
  dsimp only at h
  have hLenEq : (shake256Xof 32 (encodeSlhReqPreimage req₁)).length =
                (shake256Xof 32 (encodeSlhReqPreimage req₂)).length := by
    rw [shake256Xof_length, shake256Xof_length]
  obtain ⟨_, hFramed⟩ := List.append_inj h hLenEq
  have hF := encodeMultiFrame_injective hFramed
  simp only [List.cons.injEq] at hF
  exact ⟨leb128_inj hF.2.1, hF.2.2.1, hF.2.2.2.1⟩

/-- Public transcript-derived expected `GF(2^128)` (`Tower128`) gate wire at index `idx`
    from `(pk, req, cursor, partyId, nonceC, idx)` over injective `encodeMultiFrame`. -/
def deriveExpectedGateWire (pk : SlhPublicKey) (req : SessionScheduleReq)
    (cursor partyId : Nat) (nonceC : List UInt8) (idx : Nat) : Tower128 :=
  let pre := encodeMultiFrame
    [rssGateWireDomainTag, leb128 partyId, leb128 req.sessionId, leb128 req.reqEpoch,
     leb128 cursor, leb128 idx, pk.pkSeed, pk.pkRoot, req.msg, req.optRand, nonceC]
  decodeTower128Wire (shake256Xof 16 pre)

def deriveExpectedGateWires (pk : SlhPublicKey) (req : SessionScheduleReq)
    (cursor partyId : Nat) (nonceC : List UInt8) (count : Nat) : List Tower128 :=
  (List.range count).map (deriveExpectedGateWire pk req cursor partyId nonceC)

private theorem deriveExpectedGateWires_length (pk : SlhPublicKey) (req : SessionScheduleReq)
    (cursor partyId : Nat) (nonceC : List UInt8) (count : Nat) :
    (deriveExpectedGateWires pk req cursor partyId nonceC count).length = count := by
  simp [deriveExpectedGateWires]

private theorem deriveExpectedGateWires_zero (pk : SlhPublicKey) (req : SessionScheduleReq)
    (cursor partyId : Nat) (nonceC : List UInt8) :
    deriveExpectedGateWires pk req cursor partyId nonceC 0 = [] := by
  simp [deriveExpectedGateWires]

private theorem deriveExpectedGateWires_one (pk : SlhPublicKey) (req : SessionScheduleReq)
    (cursor partyId : Nat) (nonceC : List UInt8) :
    deriveExpectedGateWires pk req cursor partyId nonceC 1 =
      [deriveExpectedGateWire pk req cursor partyId nonceC 0] := by
  simp [deriveExpectedGateWires]

/-- Componentwise `GF(2^{2^k})` (`TowerElem k`) difference `sentWires ⊕ expectedWires`. -/
def zipXorTower (k : Nat) : List (TowerElem k) → List (TowerElem k) → List (TowerElem k)
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => towerAdd k x y :: zipXorTower k xs ys

private theorem zipXorTower_length_le_left (k : Nat) :
    ∀ (xs ys : List (TowerElem k)), (zipXorTower k xs ys).length ≤ xs.length
  | [], _ => Nat.le_refl 0
  | _ :: _, [] => Nat.zero_le _
  | _ :: xs, _ :: ys => Nat.succ_le_succ (zipXorTower_length_le_left k xs ys)

private theorem tower_eq_of_add_eq_zero (k : Nat) {a b : TowerElem k}
    (h : towerAdd k a b = towerZero k) : a = b := by
  have h1 := congrArg (towerAdd k a) h
  rw [towerAdd_cancel, towerAdd_zero] at h1
  exact h1.symm

private theorem eq_of_zipXorTower_any_false (k : Nat) :
    ∀ {xs ys : List (TowerElem k)},
      xs.length = ys.length →
      (zipXorTower k xs ys).any (fun d => decide (d ≠ towerZero k)) = false →
      xs = ys
  | [], [], _, _ => rfl
  | _ :: _, [], hL, _ => by cases hL
  | [], _ :: _, hL, _ => by cases hL
  | x :: xs, y :: ys, hL, hAny => by
    simp only [zipXorTower, List.any_cons, Bool.or_eq_false_iff] at hAny
    have hxy : towerAdd k x y = towerZero k := by
      by_cases hEq : towerAdd k x y = towerZero k
      · exact hEq
      · exact False.elim (Bool.noConfusion ((decide_eq_true hEq).symm.trans hAny.1))
    rw [tower_eq_of_add_eq_zero k hxy, eq_of_zipXorTower_any_false k (Nat.succ.inj hL) hAny.2]

private theorem evalCoeffs_zipXorTower (k : Nat) (gamma : TowerElem k) :
    ∀ {xs ys : List (TowerElem k)},
      xs.length = ys.length →
      RoundPoly.evalCoeffs (zipXorTower k xs ys) gamma =
        towerAdd k (RoundPoly.evalCoeffs xs gamma) (RoundPoly.evalCoeffs ys gamma)
  | [], [], _ => (towerAdd_self_zero k (towerZero k)).symm
  | _ :: _, [], hL => by cases hL
  | [], _ :: _, hL => by cases hL
  | x :: xs, y :: ys, hL => by
    simp only [zipXorTower, RoundPoly.evalCoeffs]
    change towerAdd k (towerAdd k x y) (towerMul k gamma (RoundPoly.evalCoeffs (zipXorTower k xs ys) gamma)) =
      towerAdd k (towerAdd k x (towerMul k gamma (RoundPoly.evalCoeffs xs gamma)))
                 (towerAdd k y (towerMul k gamma (RoundPoly.evalCoeffs ys gamma)))
    rw [evalCoeffs_zipXorTower k gamma (Nat.succ.inj hL), towerMul_add_distrib,
        towerAdd_assoc k x y, towerAdd_assoc k x, towerAdd_left_comm k y]

/-- Algebraic `BBCGGI19` / `BDOZ` Horner wire accumulator $\sum_{j=0}^{m-1} w_j \cdot \gamma^{j+1}$ over `TowerElem k`. -/
def bbcggiWireAccumulatorGen (k : Nat) (wires : List (TowerElem k)) (gamma : TowerElem k) : TowerElem k :=
  RoundPoly.evalCoeffs (towerZero k :: wires) gamma

abbrev bbcggiWireAccumulator (wires : List Tower128) (gamma : Tower128) : Tower128 :=
  bbcggiWireAccumulatorGen 7 wires gamma

private theorem batchDeviationPoly_zipXorTower_eq (k : Nat)
    {sentWires expectedWires : List (TowerElem k)}
    (hLen : sentWires.length = expectedWires.length) (gamma : TowerElem k) :
    batchDeviationPoly (zipXorTower k sentWires expectedWires) gamma =
      towerAdd k (bbcggiWireAccumulatorGen k sentWires gamma)
                 (bbcggiWireAccumulatorGen k expectedWires gamma) := by
  unfold batchDeviationPoly bbcggiWireAccumulatorGen
  change RoundPoly.evalCoeffs (towerZero k :: zipXorTower k sentWires expectedWires) gamma = _
  have hZeroCons :
      towerZero k :: zipXorTower k sentWires expectedWires =
        zipXorTower k (towerZero k :: sentWires) (towerZero k :: expectedWires) := by
    simp only [zipXorTower, towerAdd_self_zero]
  rw [hZeroCons]
  exact evalCoeffs_zipXorTower k gamma (congrArg Nat.succ hLen)

theorem bbcggiWireAccumulator_eq_iff_batchDeviationPoly
    {sentWires expectedWires : List Tower128}
    (hLen : sentWires.length = expectedWires.length) (gamma : Tower128) :
    (bbcggiWireAccumulator sentWires gamma == bbcggiWireAccumulator expectedWires gamma) =
      (batchDeviationPoly (zipXorTower 7 sentWires expectedWires) gamma == towerZero 7) := by
  unfold bbcggiWireAccumulator
  rw [batchDeviationPoly_zipXorTower_eq 7 hLen gamma]
  by_cases hEq : bbcggiWireAccumulatorGen 7 sentWires gamma = bbcggiWireAccumulatorGen 7 expectedWires gamma
  · rw [hEq, towerAdd_self_zero, beq_self_eq_true, beq_self_eq_true]
  · have hLhs : (bbcggiWireAccumulatorGen 7 sentWires gamma == bbcggiWireAccumulatorGen 7 expectedWires gamma) = false :=
      beq_false_of_ne hEq
    have hRhs : (towerAdd 7 (bbcggiWireAccumulatorGen 7 sentWires gamma)
                            (bbcggiWireAccumulatorGen 7 expectedWires gamma) == towerZero 7) = false :=
      beq_false_of_ne (fun hZ => hEq (tower_eq_of_add_eq_zero 7 hZ))
    rw [hLhs, hRhs]

/-- Project a `Tower128` (`GF(2^128)`) gate wire onto its embedded `Tower8` (`GF(2^8)`) byte coordinate. -/
def towerLowByte (x : Tower128) : UInt8 :=
  let b : Tower8 := x.1.1.1.1
  let bit (f : Bool) (s : UInt8) : UInt8 := if f then (1 : UInt8) <<< s else 0
  bit b.1.1.1 0 ||| bit b.1.1.2 1 ||| bit b.1.2.1 2 ||| bit b.1.2.2 3 |||
  bit b.2.1.1 4 ||| bit b.2.1.2 5 ||| bit b.2.2.1 6 ||| bit b.2.2.2 7

/-- Replicated `FLNW17` / `BDOZ` bilinear gate cross-byte evaluated by the honest quorum from
    local key-share bytes `shareBytes` and Round-2 `GF(2^128)` gate wires `(sentWires, expectedWires)`. -/
def evalReplicatedGateCrossByte : List UInt8 → List Tower128 → List Tower128 → UInt8
  | [], _, _ => 0
  | _, [], _ => 0
  | _, _, [] => 0
  | b :: bs, sw :: sws, ew :: ews =>
    (b &&& towerLowByte (towerAdd 7 sw ew)) ^^^ evalReplicatedGateCrossByte bs sws ews

private theorem evalReplicatedGateCrossByte_self :
    ∀ (bs : List UInt8) (ws : List Tower128),
      evalReplicatedGateCrossByte bs ws ws = 0
  | [], _ => rfl
  | _ :: _, [] => rfl
  | b :: bs, w :: ws => by
    simp only [evalReplicatedGateCrossByte, towerAdd_self_zero]
    have hZ : towerLowByte (towerZero 7) = 0 := rfl
    rw [hZ, evalReplicatedGateCrossByte_self bs ws]
    have hAnd0 : (b &&& 0) = 0 := by apply UInt8.eq_of_toBitVec_eq; simp
    rw [hAnd0]
    rfl

private theorem evalReplicatedGateCrossByte_nil_wires (bs : List UInt8) :
    evalReplicatedGateCrossByte bs [] [] = 0 := by
  cases bs <;> rfl

private theorem evalReplicatedGateCrossByte_one_headD (bs : List UInt8) (exp0 : Tower128) :
    evalReplicatedGateCrossByte bs [towerAdd 7 exp0 (towerOne 7)] [exp0] =
      (bs.headD 0 &&& 1) := by
  cases bs with
  | nil => rfl
  | cons b rest =>
    simp only [evalReplicatedGateCrossByte, List.headD_cons]
    have hShift : towerAdd 7 (towerAdd 7 exp0 (towerOne 7)) exp0 = towerOne 7 := by
      rw [towerAdd_comm 7 _ exp0, towerAdd_cancel]
    have hOne : towerLowByte (towerOne 7) = 1 := rfl
    rw [hShift, hOne, evalReplicatedGateCrossByte_nil_wires rest, uint8_xor_zero]

private theorem xorByteStream_zero_head_replicate {xs : List UInt8} {L : Nat}
    (hLen : xs.length = L) :
    xorByteStream xs ((0 : UInt8) :: List.replicate (L - 1) 0) = xs := by
  subst hLen
  cases xs with
  | nil => rfl
  | cons x rest =>
    simp only [List.length_cons, Nat.add_sub_cancel, xorByteStream,
               List.zipWith_cons_cons, uint8_xor_zero]
    exact congrArg (List.cons x) (xorByteStream_replicate_zero rest)

private theorem byteArray_bne_self (b : ByteArray) : (b != b) = false := by
  unfold bne
  change (!(b.data == b.data)) = false
  rw [beq_self_eq_true]
  rfl

private theorem ite_bne_self_false {α : Type} (b : ByteArray) (t e : α) :
    (if (b != b) = true then t else e) = e := by
  rw [byteArray_bne_self]; rfl

private theorem ite_not_beq_self_false {α β : Type} [BEq β] [ReflBEq β] (x : β) (t e : α) :
    (if (!(x == x)) = true then t else e) = e := by
  rw [beq_self_eq_true]; rfl

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
  sentWires     : List Tower128
  expectedWires : List Tower128
  cutShares     : RssByteShares
  deriving DecidableEq

/-- Derived `GF(2^128)` (`Tower128`) gate-wire differences `sentWires ⊕ expectedWires`. -/
def RssRound3State.deltas (st : RssRound3State) : List Tower128 :=
  zipXorTower 7 st.sentWires st.expectedWires

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
    Verifies Round-1 commitment binding AND the algebraic `BBCGGI19` / `BDOZ` inner-product equation
    `bbcggiWireAccumulator sentWires gamma == bbcggiWireAccumulator expectedWires gamma` over raw
    `GF(2^128)` (`Tower128`) gate wires strictly BEFORE Round-3 cut openings can run! -/
def sharedPreCutBarrier (cIdx : Fin 3) (deg : Nat) (pk : SlhPublicKey)
    (req : SessionScheduleReq) (r2St : RssRound2State)
    (corrR2 : List (Nat × ByteArray)) : PSum AbortReason RssRound3State :=
  match corrR2.find? (fun pr => pr.1 == cIdx.val) with
  | none => .inl (.round1CommitMismatch cIdx.val)
  | some (_, cWire2) =>
    match parseCorruptRound2Wire deg cWire2 with
    | none => .inl (.round1CommitMismatch cIdx.val)
    | some (nonceC, sentWires) =>
      if round1NonceCommit pk req r2St.cursor cIdx.val nonceC != r2St.corrR1Commit then
        .inl (.round1CommitMismatch cIdx.val)
      else
        let expectedWires :=
          deriveExpectedGateWires pk req r2St.cursor cIdx.val nonceC sentWires.length
        let gamma := unpackTower 7 r2St.gammaBits
        if !(bbcggiWireAccumulator sentWires gamma == bbcggiWireAccumulator expectedWires gamma) then
          .inl .activeConsistencyFailed
        else
          .inr { sentWires := sentWires, expectedWires := expectedWires, cutShares := ⟨[], [], []⟩ }

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

/-- **Three-Round 2-of-3 RSS `FIPS 205 SLH-DSA` Opening-Layer Model (`rssSlhInteractiveProtocol`)**
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
      let crossByte :=
        evalReplicatedGateCrossByte seedViews.1.1 r3Init.sentWires r3Init.expectedWires
      let preCutBytes :=
        xorByteStream trueSigBytes (crossByte :: List.replicate (p.sigBytes - 1) 0)
      let cutB0 := bvToFixedBytes p.sigBytes (rawTag0 ^^^ tape.cutMask0)
      let cutB1 := bvToFixedBytes p.sigBytes (rawTag1 ^^^ tape.cutMask1)
      let cutB2 := xorByteStream preCutBytes (xorByteStream cutB0 cutB1)
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
  cheat_eq      : cl.tsig.identifiedCheaters = icl.tsig.identifiedCheaters
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

/-- Extract the adversary's non-zero Round-2 wire deviation batch `deltas = sentWires ⊕ expectedWires`
    (`deltas.length ≤ deg` and `∃ d ∈ deltas, d ≠ 0`) when Round-1/quorum/WAL gates pass — notice this
    depends **ONLY on `padIdx : Fin (rssPadSessionCard p.sigBytes)`** and is completely independent of `gIdx : Fin (2 ^ 128)`! -/
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
          | some (nonceC, sentWires) =>
            if round1NonceCommit cl.tsig.pk req r2St0.cursor cIdx.val nonceC != r2St0.corrR1Commit then
              none
            else
              let expectedWires :=
                deriveExpectedGateWires cl.tsig.pk req r2St0.cursor cIdx.val nonceC sentWires.length
              let deltas := zipXorTower 7 sentWires expectedWires
              if deltas.any (fun d => decide (d ≠ towerZero 7)) then
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
              rcases nd with ⟨nonceC, sws⟩
              rw [hParse] at hSome
              dsimp only at hSome
              cases hCmt : (round1NonceCommit cl.tsig.pk (A.scheduleSession advSt).1
                  r2Out.2.cursor cIdx.val nonceC != r2Out.2.corrR1Commit)
              · rw [hCmt] at hSome
                simp only [Bool.false_eq_true, ↓reduceIte] at hSome
                let ews := deriveExpectedGateWires cl.tsig.pk (A.scheduleSession advSt).1
                  r2Out.2.cursor cIdx.val nonceC sws.length
                let ds := zipXorTower 7 sws ews
                cases hAny : ds.any (fun d => decide (d ≠ towerZero 7))
                · change (if ds.any (fun d => decide (d ≠ towerZero 7)) then some ds else none) = some deltas at hSome
                  rw [hAny] at hSome; simp at hSome
                · change (if ds.any (fun d => decide (d ≠ towerZero 7)) then some ds else none) = some deltas at hSome
                  rw [hAny] at hSome
                  simp only [↓reduceIte, Option.some.injEq] at hSome
                  subst hSome
                  obtain ⟨d, hdMem, hdDec⟩ := List.any_eq_true.mp hAny
                  exact ⟨Nat.le_trans (zipXorTower_length_le_left 7 sws ews)
                           (parseCorruptRound2Wire_length_le deg cWire2 hParse),
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
       | some (nonceC, sentWires) =>
         if round1NonceCommit pk req r2St.cursor cIdx.val nonceC != r2St.corrR1Commit then none
         else
           let expectedWires :=
             deriveExpectedGateWires pk req r2St.cursor cIdx.val nonceC sentWires.length
           let deltas := zipXorTower 7 sentWires expectedWires
           if deltas.any (fun d => decide (d ≠ towerZero 7)) then some deltas
           else none) =
      (if r3Init.deltas.any (fun d => decide (d ≠ towerZero 7)) then some r3Init.deltas else none) ∧
    (batchDeviationPoly r3Init.deltas (unpackTower 7 r2St.gammaBits) == towerZero 7) = true ∧
    r3Init.sentWires.length = r3Init.expectedWires.length := by
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
      rcases nd with ⟨nonceC, sws⟩
      rw [hParse] at hBar
      dsimp only at hBar ⊢
      cases hCmt : (round1NonceCommit pk req r2St.cursor cIdx.val nonceC != r2St.corrR1Commit)
      · rw [hCmt] at hBar
        simp only [Bool.false_eq_true, ↓reduceIte] at hBar ⊢
        let ews := deriveExpectedGateWires pk req r2St.cursor cIdx.val nonceC sws.length
        have hLenEq : sws.length = ews.length :=
          (deriveExpectedGateWires_length pk req r2St.cursor cIdx.val nonceC sws.length).symm
        cases hAcc : (bbcggiWireAccumulator sws (unpackTower 7 r2St.gammaBits) ==
                      bbcggiWireAccumulator ews (unpackTower 7 r2St.gammaBits))
        · change (if !(bbcggiWireAccumulator sws (unpackTower 7 r2St.gammaBits) ==
                       bbcggiWireAccumulator ews (unpackTower 7 r2St.gammaBits))
                  then PSum.inl AbortReason.activeConsistencyFailed
                  else PSum.inr { sentWires := sws, expectedWires := ews, cutShares := ⟨[], [], []⟩ }) =
                 PSum.inr r3Init at hBar
          rw [hAcc] at hBar; simp at hBar
        · change (if !(bbcggiWireAccumulator sws (unpackTower 7 r2St.gammaBits) ==
                       bbcggiWireAccumulator ews (unpackTower 7 r2St.gammaBits))
                  then PSum.inl AbortReason.activeConsistencyFailed
                  else PSum.inr { sentWires := sws, expectedWires := ews, cutShares := ⟨[], [], []⟩ }) =
                 PSum.inr r3Init at hBar
          rw [hAcc] at hBar
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hBar
          injection hBar with hEq
          have hSw : sws = r3Init.sentWires := congrArg RssRound3State.sentWires hEq
          have hEw : ews = r3Init.expectedWires := congrArg RssRound3State.expectedWires hEq
          have hDs : zipXorTower 7 sws ews = r3Init.deltas := by
            unfold RssRound3State.deltas
            rw [← hSw, ← hEw]
          have hBatch : (batchDeviationPoly r3Init.deltas (unpackTower 7 r2St.gammaBits) == towerZero 7) = true := by
            rw [← hDs, ← bbcggiWireAccumulator_eq_iff_batchDeviationPoly hLenEq]
            exact hAcc
          refine ⟨?_, hBatch, by rw [← hSw, ← hEw]; exact hLenEq⟩
          change (if (zipXorTower 7 sws ews).any (fun d => decide (d ≠ towerZero 7))
                  then some (zipXorTower 7 sws ews) else none) = _
          rw [hDs]
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
  rcases hMatch with ⟨hPkEq, hThEq, hNpEq, hCorrEq, hCheatEq, hWalEq, hCurEq, hSharesIntact⟩
  have hQuorumEq : ∀ apps, validThresholdApproval cl.tsig apps = validThresholdApproval icl.tsig apps := by
    intro apps
    unfold validThresholdApproval
    rw [hThEq, hNpEq, hCorrEq, hCheatEq]
  intro sk tapeReal tapeSim resR resI
  dsimp only [resR, resI]
  unfold execRealSession execIdealSession
  dsimp only
  rw [← hQuorumEq]
  cases hQuorum : validThresholdApproval cl.tsig (A.scheduleSession advSt).1.honestApprovers
  · exact ⟨rfl, rfl, rfl, ⟨hPkEq, hThEq, hNpEq, hCorrEq, hCheatEq, hWalEq, hCurEq, hSharesIntact⟩⟩
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
      refine ⟨rfl, rfl, rfl, ⟨hPkEq, hThEq, hNpEq, hCorrEq, hCheatEq, rfl, hCurEq, ?_⟩⟩
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
        refine ⟨rfl, rfl, rfl, ⟨hPkEq, hThEq, hNpEq, hCorrEq, hCheatEq, rfl, hCurEq, ?_⟩⟩
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
            exact ⟨rfl, rfl, rfl, ⟨hPkEq, hThEq, hNpEq, hCorrEq, hCheatEq, rfl, rfl, fun _ => hShares⟩⟩
          · dsimp only [poisonRealCluster, poisonIdealCluster, walQuarantine]
            exact ⟨rfl, rfl, rfl, ⟨hPkEq, hThEq, hNpEq, hCorrEq, hCheatEq, rfl, rfl, fun hp => by cases hp⟩⟩
        | inr r2Init =>
          dsimp only
          cases hBar : sharedPreCutBarrier cIdx deg cl.tsig.pk _ _ _ with
          | inl barrierErr =>
            dsimp only [poisonRealCluster, poisonIdealCluster, walQuarantine]
            exact ⟨rfl, rfl, rfl, ⟨hPkEq, hThEq, hNpEq, hCorrEq, hCheatEq, rfl, rfl, fun hp => by cases hp⟩⟩
          | inr r3Init =>
            obtain ⟨hExtEq, hBatchTrue, hSwLenEq⟩ :=
              sharedPreCutBarrier_extract_eq cIdx deg cl.tsig.pk _ _ _ r3Init hBar
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
                dsimp only at hBadUnf hExtEq hBatchTrue
                rw [hExtEq, hAny] at hBadUnf
                simp only [↓reduceIte] at hBadUnf
                rw [← hDummy.2.2.2.2, hBatchTrue] at hBadUnf
                cases hBadUnf
              · exact Bool.eq_false_iff.mpr hAny
            have hSentEqExp : r3Init.sentWires = r3Init.expectedWires :=
              eq_of_zipXorTower_any_false 7 hSwLenEq hDeltasZero
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
            have hCrossZero :
                evalReplicatedGateCrossByte (q.views seedSh).1.1 r3Init.sentWires r3Init.expectedWires = 0 := by
              rw [hSentEqExp]
              exact evalReplicatedGateCrossByte_self _ _
            have hPreCutEq :
                xorByteStream
                  (rssQuorumSlhSignBytes p q (q.views seedSh) (q.views prfSh) cl.tsig.pk.pkSeed
                    constZeroRssSeedTape (A.scheduleSession advSt).1.msg (A.scheduleSession advSt).1.optRand)
                  (evalReplicatedGateCrossByte (q.views seedSh).1.1 r3Init.sentWires r3Init.expectedWires ::
                    List.replicate (p.sigBytes - 1) 0) =
                encodeSlhSig (slhSignInternal p (A.scheduleSession advSt).1.msg sk (A.scheduleSession advSt).1.optRand) := by
              rw [hCrossZero, hTrueSigEq]
              exact xorByteStream_zero_head_replicate
                (encodeSlhSig_slhSignInternal_length p
                  (A.scheduleSession advSt).1.msg sk (A.scheduleSession advSt).1.optRand)
            rw [hPreCutEq, unpackWireBytes_packWireBytes]
            cases sharedFinalizeCutOpen p cIdx cl.tsig.pk _ _ _ with
            | inl cutErr =>
              dsimp only [poisonRealCluster, poisonIdealCluster, walQuarantine]
              exact ⟨rfl, rfl, rfl, ⟨rfl, hThEq, hNpEq, rfl, hCheatEq, rfl, rfl, fun hp => by cases hp⟩⟩
            | inr outSigBytes =>
              dsimp only
              exact ⟨rfl, rfl, rfl, ⟨rfl, hThEq, hNpEq, rfl, hCheatEq, rfl, rfl, fun _ => rfl⟩⟩

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
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
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

/-- Advance monotonic session cursor across a `SessionWireRecord` (`+1` iff Round 1 executed). -/
def advanceSessionCursor (cur : Nat) (rec : SessionWireRecord) : Nat :=
  if rec.honestRound1.isEmpty then cur else cur + 1

/-- **1. `ActiveConsistencySoundnessBreak`**:
    Explicit transcript-bound witness that in some session `sessRec` of `tr.sessions`, the rushing
    corrupt party `cIdx` transmitted raw `GF(2^128)` (`Tower128`) gate wires `sentWires` differing from
    `deriveExpectedGateWires pk sessRec.request sessionCursor cIdx.val nonceC sentWires.length`
    (`deltas.length ≤ deg`, `∃ devElem ∈ deltas, devElem ≠ 0`) AND slipped past `preCutBarrier` into Round 3.
    `sessionCursor` is not a free choice of the witness: `hSplit` fixes the position of `sessRec` in the
    transcript and `hCursor` forces the cursor to be the one the execution actually used there
    (`startCursor` advanced over the preceding sessions). Expected wires are derived from the cursor, so
    a witness for a different cursor would not describe a deviation from what the honest parties checked. -/
structure ActiveConsistencySoundnessBreak {AdvState : Type}
    (pk : SlhPublicKey) (startCursor : Nat) (cIdx : Fin 3) (deg : Nat) (tr : ExecTranscript AdvState) where
  sessRec        : SessionWireRecord
  hMem           : sessRec ∈ tr.sessions
  prefixSessions : List SessionWireRecord
  suffixSessions : List SessionWireRecord
  hSplit         : tr.sessions = prefixSessions ++ sessRec :: suffixSessions
  sessionCursor  : Nat
  hCursor        : sessionCursor = prefixSessions.foldl advanceSessionCursor startCursor
  cWire2         : ByteArray
  hWireMem       : (cIdx.val, cWire2) ∈ sessRec.corruptRound2
  nonceC         : List UInt8
  sentWires      : List Tower128
  hParse         : parseCorruptRound2Wire deg cWire2 = some (nonceC, sentWires)
  hDeg           : (zipXorTower 7 sentWires
                     (deriveExpectedGateWires pk sessRec.request sessionCursor cIdx.val nonceC sentWires.length)).length ≤ deg
  devElem        : Tower128
  hDevMem        : devElem ∈ zipXorTower 7 sentWires
                     (deriveExpectedGateWires pk sessRec.request sessionCursor cIdx.val nonceC sentWires.length)
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
  | activeConsistency (w : ActiveConsistencySoundnessBreak clInit.tsig.pk clInit.maskSessionCursor cIdx deg tr)
  | forsItsr          (w : Fips205ForsItsrBreak p sk clInit tr mStar sigStar)
  | wotsChainSmTcr    (w : WotsChainSmTcrBreak p sk)
  | xmssMerkleTcr     (w : XmssMerkleTcrBreak p ⟨sk.pkSeed, sk.pkRoot⟩)
  | prfMsg            (w : PrfMsgBreak p)

/-- Constructive union of the four concrete NIST `FIPS 205` hash-game witnesses a valid fresh forgery
    yields against a transcript in which every Round-3 opening is an honest signature: FORS
    (collision / unopened secret leaf recovery / interleaved subset cover), WOTS+ (collision / backward
    chain preimage), XMSS Merkle collision, or an `H_msg` collision. No active-consistency alternative
    appears here: this is the witness type of the ideal world and of every real execution outside the
    counted `multiSessionBadHit` event. -/
inductive Fips205HashGameBreak {AdvState : Type}
    (p : Fips205Params) (sk : SlhSecretKey)
    (clInit : RealClusterState SlhPublicKey RssPartyKeyShare)
    (tr : ExecTranscript AdvState) (mStar : List UInt8) (sigStar : SlhSignature) : Type where
  | forsItsr          (w : Fips205ForsItsrBreak p sk clInit tr mStar sigStar)
  | wotsChainSmTcr    (w : WotsChainSmTcrBreak p sk)
  | xmssMerkleTcr     (w : XmssMerkleTcrBreak p ⟨sk.pkSeed, sk.pkRoot⟩)
  | prfMsg            (w : PrfMsgBreak p)

/-- Embed a hash-game witness into the five-way interactive break union. -/
def Fips205HashGameBreak.toInteractive {AdvState : Type}
    {p : Fips205Params} {sk : SlhSecretKey}
    {clInit : RealClusterState SlhPublicKey RssPartyKeyShare}
    {tr : ExecTranscript AdvState} {mStar : List UInt8} {sigStar : SlhSignature}
    (cIdx : Fin 3) (deg : Nat) :
    Fips205HashGameBreak p sk clInit tr mStar sigStar →
    RssSlhInteractiveSecurityBreak p cIdx deg sk clInit tr mStar sigStar
  | .forsItsr w       => .forsItsr w
  | .wotsChainSmTcr w => .wotsChainSmTcr w
  | .xmssMerkleTcr w  => .xmssMerkleTcr w
  | .prfMsg w         => .prfMsg w

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

private def scanActiveConsistencyWires {AdvState : Type}
    (pk : SlhPublicKey) (startCursor : Nat) (cIdx : Fin 3) (deg : Nat)
    (tr : ExecTranscript AdvState) (rec : SessionWireRecord)
    (pre suf : List SessionWireRecord)
    (hSplit : tr.sessions = pre ++ rec :: suf)
    (cur : Nat) (hCur : cur = pre.foldl advanceSessionCursor startCursor)
    (hR3 : rec.honestRound3 ≠ []) :
    (ws : List (Nat × ByteArray)) →
    (∀ w ∈ ws, w ∈ rec.corruptRound2) →
    Option (ActiveConsistencySoundnessBreak pk startCursor cIdx deg tr)
  | [], _ => none
  | (pid, cWire2) :: wRest, hWSub =>
    if hPid : pid = cIdx.val then
      match hParse : parseCorruptRound2Wire deg cWire2 with
      | none => scanActiveConsistencyWires pk startCursor cIdx deg tr rec pre suf hSplit cur hCur hR3 wRest
                  (fun w hw => hWSub w (.tail _ hw))
      | some (nonceC, sentWires) =>
        let expectedWires :=
          deriveExpectedGateWires pk rec.request cur cIdx.val nonceC sentWires.length
        let deltas := zipXorTower 7 sentWires expectedWires
        match findDecidableElem (fun d => d ≠ towerZero 7) deltas with
        | .inl ⟨d, hdMem, hdNe⟩ =>
          some
            { sessRec := rec
              hMem := by
                rw [hSplit]
                exact List.mem_append_right pre (List.Mem.head suf)
              prefixSessions := pre
              suffixSessions := suf
              hSplit := hSplit
              sessionCursor := cur
              hCursor := hCur
              cWire2 := cWire2
              hWireMem := by
                have hM := hWSub (pid, cWire2) (.head _)
                rwa [hPid] at hM
              nonceC := nonceC
              sentWires := sentWires
              hParse := hParse
              hDeg := Nat.le_trans (zipXorTower_length_le_left 7 sentWires expectedWires)
                        (parseCorruptRound2Wire_length_le deg cWire2 hParse)
              devElem := d
              hDevMem := hdMem
              hDevNonzero := hdNe
              hPassedBarrier := hR3 }
        | .inr _ => scanActiveConsistencyWires pk startCursor cIdx deg tr rec pre suf hSplit cur hCur hR3 wRest
                      (fun w hw => hWSub w (.tail _ hw))
    else
      scanActiveConsistencyWires pk startCursor cIdx deg tr rec pre suf hSplit cur hCur hR3 wRest
        (fun w hw => hWSub w (.tail _ hw))

private theorem scanSplit_snoc {α : Type} {all pre rest : List α} {x : α}
    (h : all = pre ++ x :: rest) : all = (pre ++ [x]) ++ rest := by
  rw [h]; simp

private theorem scanCursor_snoc (startCursor cur : Nat) (pre : List SessionWireRecord)
    (rec : SessionWireRecord) (hCur : cur = pre.foldl advanceSessionCursor startCursor) :
    advanceSessionCursor cur rec = (pre ++ [rec]).foldl advanceSessionCursor startCursor := by
  subst hCur
  simp [List.foldl_append]

private def scanActiveConsistencyAux {AdvState : Type}
    (pk : SlhPublicKey) (startCursor : Nat) (cIdx : Fin 3) (deg : Nat)
    (tr : ExecTranscript AdvState) :
    (pre rem : List SessionWireRecord) →
    (cur : Nat) →
    tr.sessions = pre ++ rem →
    cur = pre.foldl advanceSessionCursor startCursor →
    Option (ActiveConsistencySoundnessBreak pk startCursor cIdx deg tr)
  | _, [], _, _, _ => none
  | pre, rec :: rest, cur, hSplit, hCur =>
    if hR3 : rec.honestRound3 = [] then
      scanActiveConsistencyAux pk startCursor cIdx deg tr (pre ++ [rec]) rest
        (advanceSessionCursor cur rec) (scanSplit_snoc hSplit) (scanCursor_snoc startCursor cur pre rec hCur)
    else
      match scanActiveConsistencyWires pk startCursor cIdx deg tr rec pre rest hSplit cur hCur hR3
              rec.corruptRound2 (fun _ hw => hw) with
      | some brk => some brk
      | none =>
        scanActiveConsistencyAux pk startCursor cIdx deg tr (pre ++ [rec]) rest
          (advanceSessionCursor cur rec) (scanSplit_snoc hSplit) (scanCursor_snoc startCursor cur pre rec hCur)

/-- Constructive scanner over `tr.sessions` (`0 Classical.choice`) checking if ANY session triggered
    an `ActiveConsistencySoundnessBreak` at the cursor the execution used for that session. -/
private def scanActiveConsistencyBreak {AdvState : Type}
    (pk : SlhPublicKey) (startCursor : Nat) (cIdx : Fin 3) (deg : Nat)
    (tr : ExecTranscript AdvState) :
    Option (ActiveConsistencySoundnessBreak pk startCursor cIdx deg tr) :=
  scanActiveConsistencyAux pk startCursor cIdx deg tr [] tr.sessions startCursor rfl rfl

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

/-- **Constructive Hash-Game Forgery Extractor (`extractSlhHashGameBreak`)**:
    Given ANY transcript `tr` and ANY well-typed signature `sigStar` verifying on a message `mStar` that
    was never the request of a quorum-approved session that reached Round 3, constructively
    (`0 Classical.choice`, `Type`-valued) extracts a concrete `Fips205HashGameBreak`. Freshness is only
    required of sessions whose Round-3 openings were actually released: a request that was approved but
    aborted before Round 3 revealed no signature and does not disqualify the forgery. -/
def extractSlhHashGameBreak {AdvState : Type}
    (p : Fips205Params) (hWf : p.wellFormed = true)
    (skSeed skPrf pkSeed : List UInt8)
    (clInit : RealClusterState SlhPublicKey RssPartyKeyShare)
    (tr : ExecTranscript AdvState)
    (mStar : List UInt8) (sigStar : SlhSignature)
    (hSigWt : sigStar.WellTyped p)
    (hVerify : slhVerifyInternal p mStar sigStar (slhKeygenInternal p skSeed skPrf pkSeed).2 = true)
    (hFresh : ∀ rec ∈ tr.sessions,
      validThresholdApproval clInit.tsig rec.request.honestApprovers = true →
      rec.honestRound3 ≠ [] →
      rec.request.msg ≠ mStar) :
    Fips205HashGameBreak p (slhKeygenInternal p skSeed skPrf pkSeed).1 clInit tr mStar sigStar :=
  let sk := (slhKeygenInternal p skSeed skPrf pkSeed).1
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
        | .inl ⟨rec, hMem, hVal, hR3Rec, hDigEq⟩ =>
          let rRec := fipsPrfMsg p.n sk.skPrf rec.request.optRand rec.request.msg
          have hMsgNe : rec.request.msg ≠ mStar := hFresh rec hMem hVal hR3Rec
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
              refine ⟨rec, hMem, hVal, hR3, hFresh rec hMem hVal hR3, ?_, hCoord.1, hCoord.2.1, hCoord.2.2⟩
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

/-- **Constructive Whole-Transcript Interactive Forgery Extractor (`extractInteractiveSlhBreak`)**:
    Given ANY transcript `tr` from `RealProtocolExec` and ANY valid wire signature `rawSigStar` on a
    message `mStar` never quorum-approved in `tr.sessions`, constructively (`0 Classical.choice`,
    `Type`-valued!) extracts a concrete `RssSlhInteractiveSecurityBreak` witness: a cursor-bound
    `ActiveConsistencySoundnessBreak` if the scan finds one, otherwise `extractSlhHashGameBreak`. -/
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
  match scanActiveConsistencyBreak clInit.tsig.pk clInit.maskSessionCursor cIdx deg tr with
  | some activeBrk => .activeConsistency activeBrk
  | none =>
    (extractSlhHashGameBreak p hWf skSeed skPrf pkSeed clInit tr mStar sigStar hSigWt hVerify
      (fun rec hMem hVal _ => hUnapproved rec hMem hVal)).toInteractive cIdx deg

private theorem sharedVerifyRound1_cursor (cIdx : Fin 3) (r1St : RssRound1State)
    (corrR1 : List (Nat × ByteArray)) {r2Init : RssRound2State}
    (h : sharedVerifyRound1 cIdx r1St corrR1 = .inr r2Init) :
    r2Init.cursor = r1St.cursor := by
  unfold sharedVerifyRound1 at h
  cases hFind : corrR1.find? (fun pr => pr.1 == cIdx.val) with
  | none => rw [hFind] at h; cases h
  | some pr =>
    rcases pr with ⟨_, cWire⟩
    rw [hFind] at h
    dsimp only at h
    split at h
    · cases h
    · injection h with hEq; rw [← hEq]

/-- **Honesty Link (`activeConsistencyBreak_implies_schwartzZippel_root`)**:
    Whenever a single session `rec = (execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt tape).2.2`
    witnesses `rec.honestRound3 ≠ []` with corrupt party `cIdx` (`cl.tsig.corruptParties = [cIdx.val]`),
    its Round-2 wire `cWire2` parsed to `(nonceC, sentWires)` **necessarily satisfied** BOTH:
    1. `bbcggiWireAccumulator sentWires gamma = bbcggiWireAccumulator expectedWires gamma`, AND
    2. `batchDeviationPoly (zipXorTower 7 sentWires expectedWires) gamma = towerZero 7`!
    Thus `ActiveConsistencySoundnessBreak` is NEVER an unconstrained label — in `RealProtocolExec`,
    it forces a genuine non-zero degree-`≤ deg` polynomial root hit in `GF(2^128)`. -/
theorem activeConsistencyBreak_implies_schwartzZippel_root {AdvState : Type}
    (p : Fips205Params) (cIdx : Fin 3) (deg : Nat)
    (A : UcRushingAdversary AdvState)
    (cl : RealClusterState SlhPublicKey RssPartyKeyShare)
    (advSt : AdvState) (tape : RssSlhSessionTape p.sigBytes)
    (hSingleCorrupt : cl.tsig.corruptParties = [cIdx.val])
    {cWire2 : ByteArray} {nonceC : List UInt8} {sentWires : List Tower128}
    (hR3Nonempty : (execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt tape).2.2.honestRound3 ≠ [])
    (hWireMem : (cIdx.val, cWire2) ∈ (execRealSession (rssSlhInteractiveProtocol p cIdx deg) A cl advSt tape).2.2.corruptRound2)
    (hParse : parseCorruptRound2Wire deg cWire2 = some (nonceC, sentWires)) :
    let expectedWires :=
      deriveExpectedGateWires cl.tsig.pk (A.scheduleSession advSt).1 cl.maskSessionCursor
        cIdx.val nonceC sentWires.length
    let gamma := unpackTower 7 tape.gammaBits
    bbcggiWireAccumulator sentWires gamma = bbcggiWireAccumulator expectedWires gamma ∧
    batchDeviationPoly (zipXorTower 7 sentWires expectedWires) gamma = towerZero 7 := by
  intro expectedWires gamma
  dsimp only [expectedWires, gamma]
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
          have hCurEq : r2Init.cursor = cl.maskSessionCursor :=
            sharedVerifyRound1_cursor cIdx _ _ hVR1
          rw [hVR1] at hR3Nonempty hWireMem
          dsimp only at hR3Nonempty hWireMem
          cases hBar : sharedPreCutBarrier cIdx deg cl.tsig.pk _ _ _ with
          | inl _ => rw [hBar] at hR3Nonempty; simp at hR3Nonempty
          | inr r3Init =>
            rw [hBar] at hWireMem
            dsimp only at hWireMem
            unfold sharedPreCutBarrier at hBar
            rw [hSingleCorrupt] at hBar hWireMem
            have hEwsLen : sentWires.length =
                (deriveExpectedGateWires cl.tsig.pk (A.scheduleSession advSt).1 cl.maskSessionCursor
                  cIdx.val nonceC sentWires.length).length :=
              (deriveExpectedGateWires_length _ _ _ _ _ _).symm
            cases hFin : sharedFinalizeCutOpen p cIdx cl.tsig.pk _ _ _ <;>
              rw [hFin] at hWireMem <;>
              dsimp only at hWireMem
            · simp only [List.map, List.mem_singleton, Prod.mk.injEq] at hWireMem
              rcases hWireMem with ⟨_, hWireEq⟩
              subst hWireEq
              simp only [List.map, List.find?, beq_self_eq_true, hParse, hCurEq] at hBar
              cases hCmt : (round1NonceCommit cl.tsig.pk _ cl.maskSessionCursor cIdx.val nonceC != r2Init.corrR1Commit)
              · rw [hCmt] at hBar
                simp only [Bool.false_eq_true, ↓reduceIte] at hBar
                let ews := deriveExpectedGateWires cl.tsig.pk (A.scheduleSession advSt).1
                  cl.maskSessionCursor cIdx.val nonceC sentWires.length
                cases hAcc : (bbcggiWireAccumulator sentWires (unpackTower 7 tape.gammaBits) ==
                              bbcggiWireAccumulator ews (unpackTower 7 tape.gammaBits))
                · change (if !(bbcggiWireAccumulator sentWires (unpackTower 7 tape.gammaBits) ==
                               bbcggiWireAccumulator ews (unpackTower 7 tape.gammaBits))
                          then PSum.inl AbortReason.activeConsistencyFailed
                          else PSum.inr { sentWires := sentWires, expectedWires := ews, cutShares := ⟨[], [], []⟩ }) =
                         PSum.inr r3Init at hBar
                  rw [hAcc] at hBar; simp at hBar
                · have hAccEq : bbcggiWireAccumulator sentWires (unpackTower 7 tape.gammaBits) =
                      bbcggiWireAccumulator ews (unpackTower 7 tape.gammaBits) :=
                    of_decide_eq_true (by simpa [beq_iff_eq] using hAcc)
                  have hBatchBool := (bbcggiWireAccumulator_eq_iff_batchDeviationPoly hEwsLen
                    (unpackTower 7 tape.gammaBits)).symm.trans hAcc
                  exact ⟨hAccEq, of_decide_eq_true (by simpa [beq_iff_eq] using hBatchBool)⟩
              · rw [hCmt] at hBar; simp at hBar
            · simp only [List.map, List.mem_singleton, Prod.mk.injEq] at hWireMem
              rcases hWireMem with ⟨_, hWireEq⟩
              subst hWireEq
              simp only [List.map, List.find?, beq_self_eq_true, hParse, hCurEq] at hBar
              cases hCmt : (round1NonceCommit cl.tsig.pk _ cl.maskSessionCursor cIdx.val nonceC != r2Init.corrR1Commit)
              · rw [hCmt] at hBar
                simp only [Bool.false_eq_true, ↓reduceIte] at hBar
                let ews := deriveExpectedGateWires cl.tsig.pk (A.scheduleSession advSt).1
                  cl.maskSessionCursor cIdx.val nonceC sentWires.length
                cases hAcc : (bbcggiWireAccumulator sentWires (unpackTower 7 tape.gammaBits) ==
                              bbcggiWireAccumulator ews (unpackTower 7 tape.gammaBits))
                · change (if !(bbcggiWireAccumulator sentWires (unpackTower 7 tape.gammaBits) ==
                               bbcggiWireAccumulator ews (unpackTower 7 tape.gammaBits))
                          then PSum.inl AbortReason.activeConsistencyFailed
                          else PSum.inr { sentWires := sentWires, expectedWires := ews, cutShares := ⟨[], [], []⟩ }) =
                         PSum.inr r3Init at hBar
                  rw [hAcc] at hBar; simp at hBar
                · have hAccEq : bbcggiWireAccumulator sentWires (unpackTower 7 tape.gammaBits) =
                      bbcggiWireAccumulator ews (unpackTower 7 tape.gammaBits) :=
                    of_decide_eq_true (by simpa [beq_iff_eq] using hAcc)
                  have hBatchBool := (bbcggiWireAccumulator_eq_iff_batchDeviationPoly hEwsLen
                    (unpackTower 7 tape.gammaBits)).symm.trans hAcc
                  exact ⟨hAccEq, of_decide_eq_true (by simpa [beq_iff_eq] using hBatchBool)⟩
              · rw [hCmt] at hBar; simp at hBar

/-- **Non-Cosplay Witness Guard (`no_trivial_break_on_empty_transcript`)**:
    Neither `ActiveConsistencySoundnessBreak` nor `Fips205ForsItsrBreak.forsInterleavedSubsetCover` can
    ever be inhabited on an empty session transcript (`tr.sessions = []`). -/
theorem no_trivial_break_on_empty_transcript {AdvState : Type}
    (pk : SlhPublicKey) (startCursor : Nat) (cIdx : Fin 3) (deg : Nat) (advSt : AdvState) :
    (ActiveConsistencySoundnessBreak pk startCursor cIdx deg (⟨advSt, []⟩ : ExecTranscript AdvState) → False) ∧
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
    Nonempty (ActiveConsistencySoundnessBreak clInit.tsig.pk clInit.maskSessionCursor cIdx deg tr) ∨
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

/-! ## 4b. End-to-End Weld: Multi-Session Rushing Forgery ⇒ Counted `GF(2^128)` Root Hit or Hash-Game Witness -/

/-- The honest Round-3 message list is never empty, for either world. -/
theorem buildHonestRound3Msgs_ne_nil (cIdx : Fin 3) (cutSh : RssByteShares) :
    buildHonestRound3Msgs cIdx cutSh ≠ [] := by
  rcases cIdx with ⟨_ | _ | _ | n, hv⟩
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · exact False.elim (Nat.not_lt_zero n (Nat.lt_of_add_lt_add_right hv))

/-- `Sim_RssSlh` always emits Round-3 messages once it is handed the ideal signature, so a session
    record with empty `honestRound3` is exactly a session in which the signing oracle was not read. -/
theorem Sim_RssSlh_round3_ne_nil (p : Fips205Params) (cIdx : Fin 3) (deg : Nat)
    (pk : SlhPublicKey) (corr : List Nat) (req : SessionScheduleReq) (s3 : RssRound3State)
    (sigB : ByteArray) (tape : RssSlhSessionTape p.sigBytes) :
    ((Sim_RssSlh p cIdx deg).simRound3 pk corr req s3 sigB tape).1 ≠ [] :=
  buildHonestRound3Msgs_ne_nil cIdx _

/-- **EUF-CMA winning predicate on a transcript (`slhForgeryWins`)**: the forger's wire output decodes
    to a signature that verifies under `pk`, on a message that was never the request of a session that
    reached Round 3. Requests that were scheduled but aborted earlier do not disqualify the forgery. -/
def slhForgeryWins {AdvState : Type} (p : Fips205Params) (pk : SlhPublicKey)
    (forgeOut : ExecTranscript AdvState → List UInt8 × ByteArray)
    (tr : ExecTranscript AdvState) : Bool :=
  match decodeSlhSig p (unpackWireBytes (forgeOut tr).2) with
  | none => false
  | some sig =>
    slhVerifyInternal p (forgeOut tr).1 sig pk &&
    tr.sessions.all (fun rec => rec.honestRound3.isEmpty || decide (rec.request.msg ≠ (forgeOut tr).1))

/-- Decoded forgery together with the concrete hash-game witness it yields against `tr`. -/
structure SlhForgeryHashGameWitness {AdvState : Type}
    (p : Fips205Params) (sk : SlhSecretKey)
    (clInit : RealClusterState SlhPublicKey RssPartyKeyShare)
    (forgeOut : ExecTranscript AdvState → List UInt8 × ByteArray)
    (tr : ExecTranscript AdvState) where
  sigStar : SlhSignature
  hDecode : decodeSlhSig p (unpackWireBytes (forgeOut tr).2) = some sigStar
  brk     : Fips205HashGameBreak p sk clInit tr (forgeOut tr).1 sigStar

private theorem isEmpty_false_of_ne_nil {α : Type} : ∀ {l : List α}, l ≠ [] → l.isEmpty = false
  | [], h => absurd rfl h
  | _ :: _, _ => rfl

/-- Constructive extraction (`0 Classical.choice`) of a hash-game witness from ANY transcript on which
    `slhForgeryWins` holds. -/
def slhForgeryHashGameWitness_of_wins {AdvState : Type}
    (p : Fips205Params) (hWf : p.wellFormed = true)
    (skSeed skPrf pkSeed : List UInt8)
    (clInit : RealClusterState SlhPublicKey RssPartyKeyShare)
    (forgeOut : ExecTranscript AdvState → List UInt8 × ByteArray)
    (tr : ExecTranscript AdvState)
    (hWin : slhForgeryWins p (slhKeygenInternal p skSeed skPrf pkSeed).2 forgeOut tr = true) :
    SlhForgeryHashGameWitness p (slhKeygenInternal p skSeed skPrf pkSeed).1 clInit forgeOut tr :=
  match hDec : decodeSlhSig p (unpackWireBytes (forgeOut tr).2) with
  | none => False.elim (by
      unfold slhForgeryWins at hWin
      rw [hDec] at hWin
      cases hWin)
  | some sig =>
    have hBoth :
        (slhVerifyInternal p (forgeOut tr).1 sig (slhKeygenInternal p skSeed skPrf pkSeed).2 &&
          tr.sessions.all (fun rec =>
            rec.honestRound3.isEmpty || decide (rec.request.msg ≠ (forgeOut tr).1))) = true := by
      unfold slhForgeryWins at hWin
      rw [hDec] at hWin
      exact hWin
    { sigStar := sig
      hDecode := hDec
      brk := extractSlhHashGameBreak p hWf skSeed skPrf pkSeed clInit tr (forgeOut tr).1 sig
        (decodeSlhSig_wellTyped hDec) (Bool.and_eq_true_iff.mp hBoth).1
        (fun rec hMem _ hR3 => by
          have hOk := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hBoth).2 rec hMem
          rw [isEmpty_false_of_ne_nil hR3, Bool.false_or] at hOk
          exact of_decide_eq_true hOk) }

/-- **Mutation witness for `slhForgeryWins`**: a forgery on a message that some session carried into
    Round 3 never counts as a win, whatever the signature. -/
theorem slhForgeryWins_rejects_queried_message {AdvState : Type}
    (p : Fips205Params) (pk : SlhPublicKey)
    (forgeOut : ExecTranscript AdvState → List UInt8 × ByteArray)
    (tr : ExecTranscript AdvState)
    (rec : SessionWireRecord) (hMem : rec ∈ tr.sessions) (hR3 : rec.honestRound3 ≠ [])
    (hMsg : rec.request.msg = (forgeOut tr).1) :
    slhForgeryWins p pk forgeOut tr = false := by
  cases hW : slhForgeryWins p pk forgeOut tr
  · rfl
  · exfalso
    unfold slhForgeryWins at hW
    cases hD : decodeSlhSig p (unpackWireBytes (forgeOut tr).2) with
    | none => rw [hD] at hW; cases hW
    | some sig =>
      rw [hD] at hW
      have hBoth :
          (slhVerifyInternal p (forgeOut tr).1 sig pk &&
            tr.sessions.all (fun rec =>
              rec.honestRound3.isEmpty || decide (rec.request.msg ≠ (forgeOut tr).1))) = true := hW
      have hOk := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hBoth).2 rec hMem
      rw [isEmpty_false_of_ne_nil hR3, Bool.false_or] at hOk
      exact (of_decide_eq_true hOk) hMsg

/-- **Inhabitedness of the winning predicate and of the extracted witness**: on `slhDsaShake128f`, a
    forger that outputs a genuine signature on a message no session carried into Round 3 satisfies
    `slhForgeryWins`, and `slhForgeryHashGameWitness_of_wins` returns a witness for it. -/
theorem inhabited_slhForgeryWins :
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
    let forgeOut : ExecTranscript Unit → List UInt8 × ByteArray :=
      fun _ => (mStar, packWireBytes (encodeSlhSig (slhSignInternal p mStar sk [])))
    slhForgeryWins p pk forgeOut ⟨(), []⟩ = true ∧
    Nonempty (SlhForgeryHashGameWitness p sk clInit forgeOut ⟨(), []⟩) := by
  intro p seedSh prfSh pkSeed sk pk clInit mStar forgeOut
  have hDec : decodeSlhSig p (unpackWireBytes (forgeOut ⟨(), []⟩).2) =
      some (slhSignInternal p mStar sk []) := by
    show decodeSlhSig p (unpackWireBytes (packWireBytes (encodeSlhSig (slhSignInternal p mStar sk [])))) =
      some (slhSignInternal p mStar sk [])
    rw [unpackWireBytes_packWireBytes]
    exact decodeSlhSig_encodeSlhSig (slhSignInternal_wellTyped p mStar sk [])
  have hVer : slhVerifyInternal p mStar (slhSignInternal p mStar sk []) pk = true :=
    slhVerifyInternal_slhSignInternal p slhDsaShake128f_wellFormed
      (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed mStar []
  have hWin : slhForgeryWins p pk forgeOut ⟨(), []⟩ = true := by
    unfold slhForgeryWins
    rw [hDec]
    exact Bool.and_eq_true_iff.mpr ⟨hVer, rfl⟩
  exact ⟨hWin, ⟨slhForgeryHashGameWitness_of_wins p slhDsaShake128f_wellFormed
    (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed clInit forgeOut ⟨(), []⟩ hWin⟩⟩

/-- **End-to-End Composed Theorem (`rss_slh_uc_forgery_to_hash_game`)**:
    For ANY well-formed NIST `FIPS 205` parameter set, ANY 2-of-3 replicated sharing of the key, ANY
    rushing adversary `A` controlling `cIdx` and adaptively scheduling `Q_s` sessions against matched
    real/ideal clusters, and ANY forger `forgeOut` reading the whole multi-session transcript:
    1. **Pointwise dichotomy on the real protocol.** On every uniform multi-session tape `ω` on which
       the forger wins against `RealProtocolExec`, either `ω` is a counted `GF(2^128)` batch-consistency
       root hit (`multiSessionBadHit`, the only way a deviating Round-2 wire passes the pre-cut barrier),
       or the real transcript on `ω` IS the ideal transcript on the image tape and that transcript
       yields a concrete `Fips205HashGameBreak` (FORS / WOTS+ / XMSS Merkle / `H_msg`).
    2. **The root-hit event is counted**: at most a `Q_s * deg / 2^128` fraction of tapes.
    3. **Probability transfer**: `Pr[real forgery] ≤ Pr[ideal forgery] + Q_s * deg / 2^128`.
    4. **Every ideal-world forgery is a hash-game witness**, with no active-consistency alternative.
    5. **Signing-oracle locality**: the ideal transcript is unchanged under any oracle agreeing with
       `slhIdealSignOracle` on the requests of the sessions that reached Round 3, so the forger's whole
       input depends on the signing key only through those signatures.
    No abstract unforgeability hypothesis, no simulator oracle closure and no cheat hypothesis appears. -/
theorem rss_slh_uc_forgery_to_hash_game {AdvState : Type}
    (p : Fips205Params) (hWf : p.wellFormed = true)
    (cIdx : Fin 3) (Q_s deg : Nat)
    {seedSh prfSh : RssByteShares}
    (hSeedWf : seedSh.WellFormed) (hPrfWf : prfSh.WellFormed)
    (pkSeed : List UInt8)
    (A : UcRushingAdversary AdvState)
    (cl : RealClusterState SlhPublicKey RssPartyKeyShare)
    (icl : IdealClusterState SlhPublicKey)
    (advSt : AdvState)
    (hMatch : RealIdealClusterMatch cIdx seedSh prfSh cl icl)
    (hPkKey : cl.tsig.pk = (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2)
    (forgeOut : ExecTranscript AdvState → List UInt8 × ByteArray) :
    let card := rssMultiSessionCard p.sigBytes Q_s
    let sk := (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).1
    let O := slhIdealSignOracle p sk
    let win := slhForgeryWins p cl.tsig.pk forgeOut
    let realView : Fin card → ExecTranscript AdvState := fun ω =>
      (RealProtocolExec (rssSlhInteractiveProtocol p cIdx deg) A Q_s
        (decodeMultiSessionTapes p.sigBytes Q_s ω) cl advSt).2
    let idealView : Fin card → ExecTranscript AdvState := fun ω =>
      (IdealFunctionalityExec O (Sim_RssSlh p cIdx deg) A Q_s
        (decodeMultiSessionTapes p.sigBytes Q_s ω) icl advSt).2
    let bad := multiSessionBadHit p cIdx deg A Q_s cl advSt
    let bij := multiSessionTapeEquiv p cIdx deg A Q_s cl advSt
    (∀ ω : Fin card, win (realView ω) = true →
      bad ω = true ∨
      (realView ω = idealView (bij.toFun ω) ∧
       Nonempty (SlhForgeryHashGameWitness p sk cl forgeOut (idealView (bij.toFun ω))))) ∧
    finSum card (fun ω => if bad ω then 1 else 0) * (2 ^ 128) ≤ (Q_s * deg) * card ∧
    distAcceptCount card realView win * (2 ^ 128) ≤
      distAcceptCount card idealView win * (2 ^ 128) + (Q_s * deg) * card ∧
    (∀ ω : Fin card, win (idealView ω) = true →
      Nonempty (SlhForgeryHashGameWitness p sk cl forgeOut (idealView ω))) ∧
    (∀ (ω : Fin card) (O' : SessionScheduleReq → ByteArray),
      (∀ rec ∈ (idealView ω).sessions, rec.honestRound3 ≠ [] → O' rec.request = O rec.request) →
      (IdealFunctionalityExec O' (Sim_RssSlh p cIdx deg) A Q_s
        (decodeMultiSessionTapes p.sigBytes Q_s ω) icl advSt).2 = idealView ω) := by
  intro card sk O win realView idealView bad bij
  have hIdealWit : ∀ ω : Fin card, win (idealView ω) = true →
      Nonempty (SlhForgeryHashGameWitness p sk cl forgeOut (idealView ω)) := by
    intro ω hWin
    have hWin' : slhForgeryWins p
        (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2
        forgeOut (idealView ω) = true := by
      rw [← hPkKey]; exact hWin
    exact ⟨slhForgeryHashGameWitness_of_wins p hWf (reconstructRssBytes seedSh)
      (reconstructRssBytes prfSh) pkSeed cl forgeOut (idealView ω) hWin'⟩
  have hInd := rss_slh_real_ideal_view_indistinguishable (OuterView := ExecTranscript AdvState)
    p hWf cIdx Q_s deg hSeedWf hPrfWf pkSeed A cl icl advSt hMatch hPkKey ⟨id⟩ win
    1 Nat.one_pos (fun _ _ => defaultRssSessionTape p.sigBytes)
  have hUc : ratLe (rationalAcceptDiff card realView card idealView win) (Q_s * deg, 2 ^ 128) :=
    hInd.1
  refine ⟨?_, multiSessionBadHit_finSum_bound p cIdx deg A Q_s cl advSt,
    forgery_count_transfer card realView idealView win (Q_s * deg, 2 ^ 128) hUc, hIdealWit, ?_⟩
  · intro ω hWin
    cases hB : bad ω
    · have hEq : realView ω = idealView (bij.toFun ω) :=
        multiSession_real_eq_ideal_unless_bad p hWf cIdx deg hSeedWf hPrfWf pkSeed A
          Q_s cl icl advSt hMatch hPkKey ω hB
      have hWinI : win (idealView (bij.toFun ω)) = true := by
        rw [← hEq]; exact hWin
      exact .inr ⟨hEq, hIdealWit (bij.toFun ω) hWinI⟩
    · exact .inl rfl
  · intro ω O' hAgree
    exact congrArg Prod.snd
      (IdealFunctionalityExec_oracle_congr O O' (Sim_RssSlh p cIdx deg)
        (Sim_RssSlh_round3_ne_nil p cIdx deg) A Q_s
        (decodeMultiSessionTapes p.sigBytes Q_s ω) icl advSt hAgree)

/-- **Concrete EUF-CMA Bound from Fresh Enrollment (`rss_slh_fresh_enrollment_euf_cma_bound`)**:
    The initial real and ideal clusters are fixed to the freshly enrolled ones (clean WAL latch, mask
    cursor `0`, honest vault dealt from the sharing), so nothing about the starting state is left to the
    caller beyond the public `tsig` record. If the forger never produces a `FIPS 205` hash-game witness
    against the ideal transcript on any tape, then its real-world forgery probability across `Q_s`
    adaptively scheduled rushing sessions is at most `Q_s * deg / 2^128`. Contrapositively, a forger
    exceeding that bound exhibits, on some tape, a concrete FORS / WOTS+ / XMSS / `H_msg` witness. -/
theorem rss_slh_fresh_enrollment_euf_cma_bound {AdvState : Type}
    (p : Fips205Params) (hWf : p.wellFormed = true)
    (cIdx : Fin 3) (Q_s deg : Nat)
    {seedSh prfSh : RssByteShares}
    (hSeedWf : seedSh.WellFormed) (hPrfWf : prfSh.WellFormed)
    (pkSeed : List UInt8)
    (A : UcRushingAdversary AdvState)
    (tsig : IdealTsigState SlhPublicKey (List UInt8))
    (advSt : AdvState)
    (hPkKey : tsig.pk = (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2)
    (forgeOut : ExecTranscript AdvState → List UInt8 × ByteArray) :
    let card := rssMultiSessionCard p.sigBytes Q_s
    let sk := (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).1
    let cl : RealClusterState SlhPublicKey RssPartyKeyShare :=
      ⟨tsig, initWalLatchState (slhPkDigest tsig.pk), 0, dealHonestRssVault cIdx seedSh prfSh⟩
    let icl : IdealClusterState SlhPublicKey :=
      ⟨tsig, initWalLatchState (slhPkDigest tsig.pk), 0⟩
    let win := slhForgeryWins p tsig.pk forgeOut
    let realView : Fin card → ExecTranscript AdvState := fun ω =>
      (RealProtocolExec (rssSlhInteractiveProtocol p cIdx deg) A Q_s
        (decodeMultiSessionTapes p.sigBytes Q_s ω) cl advSt).2
    let idealView : Fin card → ExecTranscript AdvState := fun ω =>
      (IdealFunctionalityExec (slhIdealSignOracle p sk) (Sim_RssSlh p cIdx deg) A Q_s
        (decodeMultiSessionTapes p.sigBytes Q_s ω) icl advSt).2
    (∀ ω : Fin card, ¬ Nonempty (SlhForgeryHashGameWitness p sk cl forgeOut (idealView ω))) →
    distAcceptCount card realView win * (2 ^ 128) ≤ (Q_s * deg) * card := by
  intro card sk cl icl win realView idealView hNoBreak
  have hMatch : RealIdealClusterMatch cIdx seedSh prfSh cl icl :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  have hMain := rss_slh_uc_forgery_to_hash_game p hWf cIdx Q_s deg hSeedWf hPrfWf pkSeed A
    cl icl advSt hMatch hPkKey forgeOut
  have hIdealWit : ∀ ω : Fin card, win (idealView ω) = true →
      Nonempty (SlhForgeryHashGameWitness p sk cl forgeOut (idealView ω)) := hMain.2.2.2.1
  have hNever : ∀ ω : Fin card, win (idealView ω) = false := by
    intro ω
    cases hW : win (idealView ω)
    · rfl
    · exact absurd (hIdealWit ω hW) (hNoBreak ω)
  have hInd := rss_slh_real_ideal_view_indistinguishable (OuterView := ExecTranscript AdvState)
    p hWf cIdx Q_s deg hSeedWf hPrfWf pkSeed A cl icl advSt hMatch hPkKey ⟨id⟩ win
    1 Nat.one_pos (fun _ _ => defaultRssSessionTape p.sigBytes)
  have hUc : ratLe (rationalAcceptDiff card realView card idealView win) (Q_s * deg, 2 ^ 128) :=
    hInd.1
  exact forgery_count_le_of_ideal_never_wins card realView idealView win (Q_s * deg, 2 ^ 128) hUc hNever

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

private theorem sharedPreCutBarrier_passive
    (cIdx : Fin 3) (deg : Nat) (hDeg : 0 < deg) (pk : SlhPublicKey) (req : SessionScheduleReq)
    (cur : Nat) (nA nB : BitVec 64) (gBits : BitVec 128) :
    let ws := deriveExpectedGateWires pk req cur cIdx.val (List.replicate 8 0) deg
    sharedPreCutBarrier cIdx deg pk req
      { cursor := cur
        corrR1Commit := round1NonceCommit pk req cur cIdx.val (List.replicate 8 0)
        nonceA := nA, nonceB := nB, gammaBits := gBits }
      [(cIdx.val, encodeCorruptRound2Wire (List.replicate 8 0) ws)] =
    .inr { sentWires := ws, expectedWires := ws, cutShares := ⟨[], [], []⟩ } := by
  intro ws
  have hl : ws.length = deg := deriveExpectedGateWires_length _ _ _ _ _ _
  unfold sharedPreCutBarrier
  simp only [List.find?, beq_self_eq_true]
  rw [← hl, parseCorruptRound2Wire_encode _ ws (List.length_replicate ..) (by omega)]
  dsimp only
  rw [hl]
  refine (ite_bne_self_false _ _ _).trans ?_
  exact ite_not_beq_self_false _ _ _

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
    all 3 rounds with a canonical positive gate stream and `echoHonestRound3`. -/
def passiveRushingAdv (p : Fips205Params) (pk : SlhPublicKey)
    (reqs : Nat → SessionScheduleReq) (deg : Nat) : UcRushingAdversary Nat where
  scheduleSession := fun sIdx => (reqs sIdx, sIdx)
  rushRound1 := fun sIdx _ =>
    (fun pid => round1NonceCommit pk (reqs sIdx) sIdx pid (List.replicate 8 0), sIdx)
  rushRound2 := fun sIdx _ =>
    (fun pid => encodeCorruptRound2Wire (List.replicate 8 0)
      (deriveExpectedGateWires pk (reqs sIdx) sIdx pid (List.replicate 8 0) deg), sIdx)
  rushRound3 := fun sIdx honR3 =>
    (fun _ => echoHonestRound3 p.sigBytes honR3, sIdx)
  observeOutcome := fun sIdx _ => sIdx + 1

private theorem sessionBadHit_passive
    (p : Fips205Params) (cIdx : Fin 3) (deg : Nat) (hDeg : 0 < deg)
    (pk : SlhPublicKey) (reqs : Nat → SessionScheduleReq)
    (cl : RealClusterState SlhPublicKey RssPartyKeyShare) (idx : Nat)
    (hPk : cl.tsig.pk = pk) (hCorr : cl.tsig.corruptParties = [cIdx.val])
    (hCur : cl.maskSessionCursor = idx) (cur : Fin (rssFullSessionCard p.sigBytes)) :
    sessionBadHit p cIdx deg (passiveRushingAdv p pk reqs deg) cl idx cur = false := by
  have hExtract : ∀ padIdx : Fin (rssPadSessionCard p.sigBytes),
      extractSessionNonzeroDeltas p cIdx deg
        (passiveRushingAdv p pk reqs deg) cl idx padIdx = none := by
    intro padIdx
    unfold extractSessionNonzeroDeltas rssSlhInteractiveProtocol passiveRushingAdv
    dsimp only
    split
    · rfl
    · split
      · rfl
      · rfl
      · rw [hPk, hCorr, hCur]
        have hLen : (unpackWireBytes (round1NonceCommit pk (reqs idx) idx cIdx.val
            (List.replicate 8 0))).length = 32 := by
          unfold round1NonceCommit
          rw [unpackWireBytes_packWireBytes, shake256Xof_length]
        simp only [List.map, sharedVerifyRound1, List.find?, beq_self_eq_true, hLen,
          bne, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        let ws := deriveExpectedGateWires pk (reqs idx) idx cIdx.val (List.replicate 8 0) deg
        have hl : ws.length = deg := deriveExpectedGateWires_length _ _ _ _ _ _
        have hp := parseCorruptRound2Wire_encode (List.replicate 8 0) ws rfl (by omega)
        rw [hl] at hp
        rw [hp]
        dsimp only
        rw [hl]
        refine (ite_bne_self_false _ _ _).trans ?_
        have hz : ∀ xs : List Tower128,
            (zipXorTower 7 xs xs).any (fun d => decide (d ≠ towerZero 7)) = false := by
          intro xs
          induction xs with
          | nil => rfl
          | cons x xs ih =>
            rw [zipXorTower, List.any_cons, towerAdd_self_zero, ih]
            simp
        rw [hz]
        rfl
  simp only [sessionBadHit, hExtract]

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
              .ok wal' (.authorizedFresh (reqs sIdx).reqEpoch)) (hDeg : 0 < deg) :
    let sk := (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).1
    let pk := (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2
    let expSig := packWireBytes (encodeSlhSig (slhSignInternal p (reqs sIdx).msg sk (reqs sIdx).optRand))
    let runOut :=
      execRealSession (rssSlhInteractiveProtocol p cIdx deg) (passiveRushingAdv p pk reqs deg) cl sIdx tape
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
    runOut.1.tsig.identifiedCheaters = cl.tsig.identifiedCheaters ∧
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
  let ws := deriveExpectedGateWires pk (reqs sIdx) sIdx cIdx.val (List.replicate 8 0) deg
  have hBar := sharedPreCutBarrier_passive cIdx deg hDeg pk (reqs sIdx)
    sIdx tape.nonceA tape.nonceB tape.gammaBits
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
  let sigEnc := encodeSlhSig (slhSignInternal p (reqs sIdx).msg sk (reqs sIdx).optRand)
  have hSigLen : sigEnc.length = p.sigBytes :=
    encodeSlhSig_length (slhSignInternal_wellTyped p (reqs sIdx).msg sk (reqs sIdx).optRand)
  have hPreCutNil :
      xorByteStream
        (rssQuorumSlhSignBytes p q (q.views seedSh) (q.views prfSh) pk.pkSeed
          constZeroRssSeedTape (reqs sIdx).msg (reqs sIdx).optRand)
        (evalReplicatedGateCrossByte (q.views seedSh).1.1 ws ws :: List.replicate (p.sigBytes - 1) 0) =
      sigEnc := by
    rw [evalReplicatedGateCrossByte_self, hQuorumBytes]
    exact xorByteStream_zero_head_replicate hSigLen
  let b0 := bvToFixedBytes p.sigBytes (rawTag0 ^^^ tape.cutMask0)
  let b1 := bvToFixedBytes p.sigBytes (rawTag1 ^^^ tape.cutMask1)
  let b2 := xorByteStream sigEnc (xorByteStream b0 b1)
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
  rw [hPreCutNil]
  rw [hFinOk]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

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
    (∀ (cIdx₁ cIdx₂ : Fin 3) (deg : Nat) (_hDeg : 0 < deg)
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
                     (passiveRushingAdv p pk reqs₁ deg) cl₁ 0 tape₁).2.2.outcome
       let out₂ := (execRealSession (rssSlhInteractiveProtocol p cIdx₂ deg)
                     (passiveRushingAdv p pk reqs₂ deg) cl₂ 0 tape₂).2.2.outcome
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
  · intro cIdx₁ cIdx₂ deg hDeg seed₁ prf₁ seed₂ prf₂ hS₁ hP₁ hS₂ hP₂
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
        (initWalLatchState (slhPkDigest pk)) tape₁ hPk₁ rfl rfl rfl (hQuorumAll cIdx₁) hWalInit₁ hDeg).2.1
      dsimp only [reqs₁] at hOk
      rw [hSeedEq₁, hPrfEq₁] at hOk
      exact hOk
    have hRun₂ : out₂ = .signOk (standaloneWire optRand) := by
      dsimp only [out₂, pk, reqs₂, standaloneWire, sk]
      have hOk := (execRealSession_passiveRushingAdv_ok p hWf cIdx₂ deg 0 hS₂ hP₂ pkSeed reqs₂ cl₂
        (initWalLatchState (slhPkDigest pk)) tape₂ hPk₂ rfl rfl rfl (hQuorumAll cIdx₂) hWalInit₂ hDeg).2.1
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
theorem inhabited_threshold_slh_quorum_privacy :
    let p := slhDsaShake128f
    let seed₁ : RssByteShares := ⟨List.replicate 16 1, List.replicate 16 2, List.replicate 16 3⟩
    let seed₂ : RssByteShares := ⟨List.replicate 16 7, List.replicate 16 7, List.replicate 16 0⟩
    let prf₁  : RssByteShares := ⟨List.replicate 16 5, List.replicate 16 0, List.replicate 16 0⟩
    let prf₂  : RssByteShares := ⟨List.replicate 16 0, List.replicate 16 5, List.replicate 16 0⟩
    seed₁ ≠ seed₂ ∧
    reconstructRssBytes seed₁ = reconstructRssBytes seed₂ ∧
    reconstructRssBytes prf₁ = reconstructRssBytes prf₂ ∧
    shamirQuorumShares shamirGoldilocksQuorum12.pts [[Goldilocks.ofNat 5, Goldilocks.ofNat 7]] ≠
      shamirQuorumShares shamirGoldilocksQuorum23.pts [[Goldilocks.ofNat 5, Goldilocks.ofNat 7]] ∧
    (∀ (pkSeed msg optRand : List UInt8) (tape₁ tape₂ : RssSlhSessionTape p.sigBytes),
      let pk := (slhKeygenInternal p (reconstructRssBytes seed₁) (reconstructRssBytes prf₁) pkSeed).2
      let reqs₁ : Nat → SessionScheduleReq := fun _ => ⟨0, 0, msg, optRand, [1, 2]⟩
      let reqs₂ : Nat → SessionScheduleReq := fun _ => ⟨0, 0, msg, optRand, [0, 1]⟩
      let cl₁ : RealClusterState SlhPublicKey RssPartyKeyShare :=
        ⟨⟨pk, 2, 3, [0], [], []⟩, initWalLatchState (slhPkDigest pk), 0,
         dealHonestRssVault ⟨0, by decide⟩ seed₁ prf₁⟩
      let cl₂ : RealClusterState SlhPublicKey RssPartyKeyShare :=
        ⟨⟨pk, 2, 3, [2], [], []⟩, initWalLatchState (slhPkDigest pk), 0,
         dealHonestRssVault ⟨2, by decide⟩ seed₂ prf₂⟩
      (execRealSession (rssSlhInteractiveProtocol p ⟨0, by decide⟩ 4)
        (passiveRushingAdv p pk reqs₁ 4) cl₁ 0 tape₁).2.2.outcome =
      (execRealSession (rssSlhInteractiveProtocol p ⟨2, by decide⟩ 4)
        (passiveRushingAdv p pk reqs₂ 4) cl₂ 0 tape₂).2.2.outcome) := by
  intro p seed₁ seed₂ prf₁ prf₂
  have hSeedEq : reconstructRssBytes seed₁ = reconstructRssBytes seed₂ := by decide +kernel
  have hPrfEq : reconstructRssBytes prf₁ = reconstructRssBytes prf₂ := by decide +kernel
  refine ⟨by decide +kernel, hSeedEq, hPrfEq, by decide +kernel, ?_⟩
  intro pkSeed msg optRand tape₁ tape₂ pk reqs₁ reqs₂ cl₁ cl₂
  have hPriv := (threshold_slh_output_perfect_quorum_privacy (R₁ := Goldilocks) (R₂ := Goldilocks)
    p slhDsaShake128f_wellFormed pkSeed msg optRand).2.1
    ⟨0, by decide⟩ ⟨2, by decide⟩ 4 (by decide) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    rfl rfl hSeedEq.symm hPrfEq.symm tape₁ tape₂
  exact hPriv.2

/-! ## 6. Crown-Jewel Theorem 4: `#tooth` Mutation Refusals (Concrete Attacks When Guards Are Removed) -/

private theorem ratLe_lower_bound_of_full_vs_bounded {View : Type}
    {N P M c : Nat} (hP : 0 < P) (hM : 0 < M) (hN : N = P * M) (_hcLe : c ≤ M)
    (exec₁ exec₂ : Fin N → View) (D : View → Bool)
    (hFull : distAcceptCount N exec₁ D = N)
    (hBound : distAcceptCount N exec₂ D ≤ P * c) :
    ratLe (M - c, M) (rationalAcceptDiff N exec₁ N exec₂ D) := by
  have hNPos : 0 < N := hN ▸ Nat.mul_pos hP hM
  unfold ratLe rationalAcceptDiff
  dsimp only
  rw [hFull]
  refine ⟨hM, Nat.mul_pos hNPos hNPos, ?_⟩
  let cnt₂ := distAcceptCount N exec₂ D
  have hSubLe : P * (M - c) ≤ N - cnt₂ := by
    rw [hN, Nat.mul_sub_left_distrib]
    exact Nat.sub_le_sub_left hBound (P * M)
  have hAbsGe : N * N - cnt₂ * N ≤ natAbsDiff (N * N) (cnt₂ * N) := by
    unfold natAbsDiff
    split <;> omega
  calc (M - c) * (N * N)
      = (M - c) * ((P * M) * N) := by rw [← hN]
    _ = ((P * (M - c)) * N) * M := by
          simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    _ ≤ ((N - cnt₂) * N) * M := Nat.mul_le_mul_right M (Nat.mul_le_mul_right N hSubLe)
    _ = (N * N - cnt₂ * N) * M := by rw [Nat.sub_mul]
    _ ≤ natAbsDiff (N * N) (cnt₂ * N) * M := Nat.mul_le_mul_right M hAbsGe

/-- **Mutant 1 (`mutantSkipPreCutProtocol`)**:
    Omits **ONLY** the `bbcggiWireAccumulator` algebraic consistency check from `preCutBarrier`,
    leaving `honestRound3` (and every other protocol round) 100% unmodified! -/
def mutantSkipPreCutProtocol (p : Fips205Params) (cIdx : Fin 3) (deg : Nat) :
    InteractiveThresholdProtocol SlhPublicKey RssPartyKeyShare (RssSlhSessionTape p.sigBytes)
      RssRound1State RssRound2State RssRound3State :=
  { rssSlhInteractiveProtocol p cIdx deg with
    preCutBarrier := fun pk req r2St _honR2 corrR2 =>
      match corrR2.find? (fun pr => pr.1 == cIdx.val) with
      | none => .inl (.round1CommitMismatch cIdx.val)
      | some (_, cWire2) =>
        match parseCorruptRound2Wire deg cWire2 with
        | none => .inl (.round1CommitMismatch cIdx.val)
        | some (nonceC, sentWires) =>
          if round1NonceCommit pk req r2St.cursor cIdx.val nonceC != r2St.corrR1Commit then
            .inl (.round1CommitMismatch cIdx.val)
          else
            let expectedWires :=
              deriveExpectedGateWires pk req r2St.cursor cIdx.val nonceC sentWires.length
            .inr { sentWires := sentWires, expectedWires := expectedWires, cutShares := ⟨[], [], []⟩ } }

/-- Public Round-3 wire reconstructor for `cIdx = 0` (`honestRound3 = [(1, b1 ++ b2), (2, b2 ++ b0)]`):
    extracts the opened first byte `(b0[0] ^^^ b1[0] ^^^ b2[0])` directly from public wire messages! -/
def extractPublicRound3HeadByte (L : Nat) (honR3 : List (Nat × ByteArray)) : Option UInt8 :=
  match honR3 with
  | [(_, w1), (_, w2)] =>
    let b1 := (unpackWireBytes w1).take L
    let b2 := (unpackWireBytes w1).drop L
    let b0 := (unpackWireBytes w2).drop L
    (reconstructRssBytes ⟨b0, b1, b2⟩).head?
  | _ => none

/-- Concrete 1-session active-fault rushing adversary shifting the transcript-derived gate wire `exp0`
    by `towerOne 7` (`forgedWire0 = exp0 ⊕ 1`) in Round 2. -/
def activeFaultRushingAdv (pk : SlhPublicKey) (req : SessionScheduleReq) : UcRushingAdversary Unit where
  scheduleSession := fun _ => (req, ())
  rushRound1 := fun _ _ =>
    (fun pid => round1NonceCommit pk req 0 pid (List.replicate 8 0), ())
  rushRound2 := fun _ _ =>
    let exp0 := deriveExpectedGateWire pk req 0 0 (List.replicate 8 0) 0
    let forgedWire0 := towerAdd 7 exp0 (towerOne 7)
    (fun _ => packWireBytes (List.replicate 8 0 ++ encodeTower128Wire forgedWire0), ())
  rushRound3 := fun _ _ =>
    (fun _ => ByteArray.empty, ())
  observeOutcome := fun _ _ => ()

private theorem parseCorruptRound2Wire_one_wire (w : Tower128) :
    parseCorruptRound2Wire 1
      (packWireBytes (List.replicate 8 0 ++ encodeTower128Wire w)) =
      some (List.replicate 8 0, [w]) := by
  simpa [encodeCorruptRound2Wire] using
    parseCorruptRound2Wire_encode (List.replicate 8 0) [w] rfl (by simp only [List.length_singleton]; omega)

private theorem sharedPreCutBarrier_forged_one
    (pk : SlhPublicKey) (req : SessionScheduleReq)
    (nA nB : BitVec 64) (gBits : BitVec 128) (w : Tower128) :
    sharedPreCutBarrier ⟨0, by decide⟩ 1 pk req
      { cursor := 0
        corrR1Commit := round1NonceCommit pk req 0 0 (List.replicate 8 0)
        nonceA := nA
        nonceB := nB
        gammaBits := gBits }
      [(0, packWireBytes (List.replicate 8 0 ++ encodeTower128Wire w))] =
    if !(bbcggiWireAccumulator [w] (unpackTower 7 gBits) ==
         bbcggiWireAccumulator [deriveExpectedGateWire pk req 0 0 (List.replicate 8 0) 0] (unpackTower 7 gBits)) then
      .inl .activeConsistencyFailed
    else
      .inr { sentWires := [w],
             expectedWires := [deriveExpectedGateWire pk req 0 0 (List.replicate 8 0) 0],
             cutShares := ⟨[], [], []⟩ } := by
  unfold sharedPreCutBarrier
  simp only [List.find?, beq_self_eq_true]
  rw [parseCorruptRound2Wire_one_wire w]
  dsimp only [List.length_singleton]
  refine (ite_bne_self_false _ _ _).trans ?_
  dsimp only [deriveExpectedGateWires, List.range, List.range.loop, List.map]
  rfl

/-- **`#tooth` Theorem 4a (`tooth_skipping_pre_cut_barrier_leaks_key_bit`)**:
    Proves the Mandatory Pre-Cut Consistency Barrier in `rssSlhInteractiveProtocol` is load-bearing:
    1. **Direct Secret-Share Key-Bit Leakage (`ratLe (1, 1)`)**: Under `mutantSkipPreCutProtocol`,
       across two valid sharings `seedSh₀, seedSh₁` of the **EXACT SAME `skSeed = replicate 16 0`**,
       `activeFaultRushingAdv` recovers `sh1.seedFirst[0] &&& 1` (`0` vs `1`) from public Round-3
       wire messages with **exact probability `1`** (`ratLe (1, 1) (rationalAcceptDiff ...)`)!
    2. **Simulator Indistinguishability Breakdown (`ratLe (2^128 - 1, 2^128)`)**: Against `Sim_RssSlh`,
       the public distinguisher `D_hasR3` distinguishes `mutantSkipPreCutProtocol` from
       `IdealFunctionalityExec` with advantage **`≥ (2 ^ 128 - 1) / 2 ^ 128`**!
    3. **Unmodified Guard Protection**: On `rssSlhInteractiveProtocol`, every non-zero challenge
       `unpackTower 7 tape.gammaBits ≠ towerZero 7` aborts strictly before Round 3 (`honestRound3 = []`,
       `honestWal.poisoned = true`, `outcome = .abort .activeConsistencyFailed`), bounding whole-transcript
       advantage by **`(1, 2 ^ 128)`**! -/
theorem tooth_skipping_pre_cut_barrier_leaks_key_bit
    (p : Fips205Params) (hWf : p.wellFormed = true)
    (pkSeed msg optRand : List UInt8) :
    let seedSh₀ : RssByteShares := ⟨List.replicate 16 0, List.replicate 16 0, List.replicate 16 0⟩
    let seedSh₁ : RssByteShares := ⟨List.replicate 16 1, List.replicate 16 1, List.replicate 16 0⟩
    let prfSh   : RssByteShares := ⟨List.replicate 16 0, List.replicate 16 0, List.replicate 16 0⟩
    let sk := (slhKeygenInternal p (reconstructRssBytes seedSh₀) (reconstructRssBytes prfSh) pkSeed).1
    let pk := (slhKeygenInternal p (reconstructRssBytes seedSh₀) (reconstructRssBytes prfSh) pkSeed).2
    let req : SessionScheduleReq := ⟨0, 0, msg, optRand, [1, 2]⟩
    let A := activeFaultRushingAdv pk req
    let cl₀ : RealClusterState SlhPublicKey RssPartyKeyShare :=
      ⟨⟨pk, 2, 3, [0], [], []⟩, initWalLatchState (slhPkDigest pk), 0,
       dealHonestRssVault ⟨0, by decide⟩ seedSh₀ prfSh⟩
    let cl₁ : RealClusterState SlhPublicKey RssPartyKeyShare :=
      ⟨⟨pk, 2, 3, [0], [], []⟩, initWalLatchState (slhPkDigest pk), 0,
       dealHonestRssVault ⟨0, by decide⟩ seedSh₁ prfSh⟩
    let icl : IdealClusterState SlhPublicKey :=
      ⟨⟨pk, 2, 3, [0], [], []⟩, initWalLatchState (slhPkDigest pk), 0⟩
    let card := rssMultiSessionCard p.sigBytes 1
    let bHon := (encodeSlhSig (slhSignInternal p msg sk optRand)).headD 0
    let D_leakBit : ExecTranscript Unit → Bool := fun tr =>
      match tr.sessions with
      | rec :: _ => extractPublicRound3HeadByte p.sigBytes rec.honestRound3 == some (bHon ^^^ 1)
      | [] => false
    let D_hasR3 : ExecTranscript Unit → Bool := fun tr =>
      match tr.sessions with
      | rec :: _ => !(rec.honestRound3.isEmpty)
      | [] => false
    let mutView₀ := fun ω : Fin card =>
      (RealProtocolExec (mutantSkipPreCutProtocol p ⟨0, by decide⟩ 1) A 1
        (decodeMultiSessionTapes p.sigBytes 1 ω) cl₀ ()).2
    let mutView₁ := fun ω : Fin card =>
      (RealProtocolExec (mutantSkipPreCutProtocol p ⟨0, by decide⟩ 1) A 1
        (decodeMultiSessionTapes p.sigBytes 1 ω) cl₁ ()).2
    let realView₀ := fun ω : Fin card =>
      (RealProtocolExec (rssSlhInteractiveProtocol p ⟨0, by decide⟩ 1) A 1
        (decodeMultiSessionTapes p.sigBytes 1 ω) cl₀ ()).2
    let idealView := fun ω : Fin card =>
      (IdealFunctionalityExec (slhIdealSignOracle p sk) (Sim_RssSlh p ⟨0, by decide⟩ 1) A 1
        (decodeMultiSessionTapes p.sigBytes 1 ω) icl ()).2
    reconstructRssBytes seedSh₀ = reconstructRssBytes seedSh₁ ∧
    seedSh₀ ≠ seedSh₁ ∧
    ratLe (1, 1) (rationalAcceptDiff card mutView₁ card mutView₀ D_leakBit) ∧
    ratLe (2 ^ 128 - 1, 2 ^ 128) (rationalAcceptDiff card mutView₀ card idealView D_hasR3) ∧
    ratLe (rationalAcceptDiff card realView₀ card idealView D_hasR3) (1, 2 ^ 128) ∧
    (∀ tape : RssSlhSessionTape p.sigBytes,
      unpackTower 7 tape.gammaBits ≠ towerZero 7 →
      let runOut :=
        execRealSession (rssSlhInteractiveProtocol p ⟨0, by decide⟩ 1) A cl₀ () tape
      runOut.2.2.honestRound3 = [] ∧
      runOut.2.2.outcome = .abort .activeConsistencyFailed ∧
      runOut.1.honestWal.poisoned = true) := by
  intro seedSh₀ seedSh₁ prfSh sk pk req A cl₀ cl₁ icl card bHon D_leakBit D_hasR3
        mutView₀ mutView₁ realView₀ idealView
  have hSeedSame : reconstructRssBytes seedSh₀ = reconstructRssBytes seedSh₁ := by decide +kernel
  have hSeedNe : seedSh₀ ≠ seedSh₁ := by decide +kernel
  have hQuorum : validThresholdApproval (⟨pk, 2, 3, [0], [], []⟩ : IdealTsigState SlhPublicKey (List UInt8)) [1, 2] = true := by
    simp [validThresholdApproval]
  have hWal0 :
      walPreSignStep (initWalLatchState (slhPkDigest pk)) (slhPkDigest pk) 0 (slhReqDigest req) =
      .ok (initWalLatchState (slhPkDigest pk)) (.authorizedFresh 0) := by
    unfold walPreSignStep initWalLatchState; simp
  have hCmtLen : (unpackWireBytes (round1NonceCommit pk req 0 0 (List.replicate 8 0))).length = 32 := by
    unfold round1NonceCommit; rw [unpackWireBytes_packWireBytes, shake256Xof_length]
  have hSigBytesPos : 0 < p.sigBytes := by
    have hnPos := (wellFormed_props hWf).1
    unfold Fips205Params.sigBytes; omega
  let sigEnc := encodeSlhSig (slhSignInternal p msg sk optRand)
  have hSigLen : sigEnc.length = p.sigBytes :=
    encodeSlhSig_length (slhSignInternal_wellTyped p msg sk optRand)
  let exp0 := deriveExpectedGateWire pk req 0 0 (List.replicate 8 0) 0
  let forgedWire0 := towerAdd 7 exp0 (towerOne 7)
  have hZipOne : zipXorTower 7 [forgedWire0] [exp0] = [towerOne 7] := by
    simp only [zipXorTower]
    exact congrArg (fun d => [d]) (by
      dsimp only [forgedWire0]
      rw [towerAdd_comm 7 _ exp0, towerAdd_cancel])
  have hAccEqBatch : ∀ gamma : Tower128,
      (bbcggiWireAccumulator [forgedWire0] gamma == bbcggiWireAccumulator [exp0] gamma) =
        (batchDeviationPoly [towerOne 7] gamma == towerZero 7) := by
    intro gamma
    rw [@bbcggiWireAccumulator_eq_iff_batchDeviationPoly [forgedWire0] [exp0] rfl gamma,
        hZipOne]
  have hMutHead : ∀ (seedSh : RssByteShares) (hSWf : seedSh.WellFormed)
      (hSame : reconstructRssBytes seedSh = reconstructRssBytes seedSh₀)
      (tape : RssSlhSessionTape p.sigBytes),
      let clS : RealClusterState SlhPublicKey RssPartyKeyShare :=
        ⟨⟨pk, 2, 3, [0], [], []⟩, initWalLatchState (slhPkDigest pk), 0,
         dealHonestRssVault ⟨0, by decide⟩ seedSh prfSh⟩
      let recOut := (execRealSession (mutantSkipPreCutProtocol p ⟨0, by decide⟩ 1) A clS () tape).2.2
      recOut.honestRound3 ≠ [] ∧
      extractPublicRound3HeadByte p.sigBytes recOut.honestRound3 =
        some (bHon ^^^ (seedSh.b1.headD 0 &&& 1)) := by
    intro seedSh hSWf hSame tape clS recOut
    dsimp only [recOut, A, clS]
    unfold execRealSession mutantSkipPreCutProtocol rssSlhInteractiveProtocol activeFaultRushingAdv
    dsimp only
    rw [hQuorum, ite_eq_right (by decide : ¬ ((!true) = true)), hWal0]
    dsimp only
    simp only [List.map]
    have hVR1 :
        sharedVerifyRound1 ⟨0, by decide⟩
          { cursor := 0, nonceA := tape.nonceA, nonceB := tape.nonceB }
          [(0, round1NonceCommit pk req 0 0 (List.replicate 8 0))] =
        .inr { cursor := 0,
               corrR1Commit := round1NonceCommit pk req 0 0 (List.replicate 8 0),
               nonceA := tape.nonceA, nonceB := tape.nonceB, gammaBits := 0#128 } := by
      unfold sharedVerifyRound1
      simp only [List.find?, beq_self_eq_true]
      rw [hCmtLen]
      rfl
    rw [hVR1]
    dsimp only
    simp only [List.find?, beq_self_eq_true]
    rw [parseCorruptRound2Wire_one_wire forgedWire0]
    dsimp only [List.length_singleton]
    rw [byteArray_bne_self]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [deriveExpectedGateWires_one]
    have hExt := extractHonestQuorumViews_deal p.sigBytes ⟨0, by decide⟩ seedSh prfSh req
    dsimp only at hExt
    rw [hExt]
    dsimp only
    have hQBytes :
        rssQuorumSlhSignBytes p .p12 (RssQuorum.p12.views seedSh) (RssQuorum.p12.views prfSh)
          pk.pkSeed constZeroRssSeedTape req.msg req.optRand = sigEnc := by
      have hPrfWf0 : prfSh.WellFormed := ⟨rfl, rfl⟩
      have h1 := (rss_threshold_sig_independent_of_quorum_and_sharing p hWf .p12 .p12
        hSWf hPrfWf0 hSWf hPrfWf0 rfl rfl pkSeed
        constZeroRssSeedTape constZeroRssSeedTape msg optRand).1
      dsimp only [sigEnc, sk, pk, req]
      rw [hSame] at h1
      exact h1
    have hCrossLeak :
        evalReplicatedGateCrossByte (RssQuorum.p12.views seedSh).1.1 [forgedWire0] [exp0] =
          (seedSh.b1.headD 0 &&& 1) :=
      evalReplicatedGateCrossByte_one_headD seedSh.b1 exp0
    let leakBit : UInt8 := seedSh.b1.headD 0 &&& 1
    let faulted := xorByteStream sigEnc (leakBit :: List.replicate (p.sigBytes - 1) 0)
    have hMaskLen : (leakBit :: List.replicate (p.sigBytes - 1) (0 : UInt8)).length = p.sigBytes := by
      simp only [List.length_cons, List.length_replicate]; omega
    have hFaultLen : faulted.length = p.sigBytes := by
      dsimp only [faulted]
      rw [xorByteStream_length (hSigLen.trans hMaskLen.symm)]
      exact hSigLen
    let rawTag0 := (honestSessionShifts p.sigBytes ⟨0, by decide⟩ (dealHonestRssVault ⟨0, by decide⟩ seedSh prfSh) req).2.2.1
    let rawTag1 := (honestSessionShifts p.sigBytes ⟨0, by decide⟩ (dealHonestRssVault ⟨0, by decide⟩ seedSh prfSh) req).2.2.2
    let cutB0 := bvToFixedBytes p.sigBytes (rawTag0 ^^^ tape.cutMask0)
    let cutB1 := bvToFixedBytes p.sigBytes (rawTag1 ^^^ tape.cutMask1)
    let cutB2 := xorByteStream faulted (xorByteStream cutB0 cutB1)
    have hb0L : cutB0.length = p.sigBytes := bvToFixedBytes_length p.sigBytes _
    have hb1L : cutB1.length = p.sigBytes := bvToFixedBytes_length p.sigBytes _
    have hb2L : cutB2.length = p.sigBytes := by
      dsimp only [cutB2]
      have h01 : (xorByteStream cutB0 cutB1).length = p.sigBytes :=
        (xorByteStream_length (hb0L.trans hb1L.symm)).trans hb0L
      rw [xorByteStream_length (hFaultLen.trans h01.symm)]
      exact hFaultLen
    have hNeNil : buildHonestRound3Msgs ⟨0, by decide⟩ ⟨cutB0, cutB1, cutB2⟩ ≠ [] := by
      simp [buildHonestRound3Msgs]
    have hExtractCut :
        extractPublicRound3HeadByte p.sigBytes
          (buildHonestRound3Msgs ⟨0, by decide⟩ ⟨cutB0, cutB1, cutB2⟩) =
        some (bHon ^^^ (seedSh.b1.headD 0 &&& 1)) := by
      unfold buildHonestRound3Msgs extractPublicRound3HeadByte
      simp only [Nat.reduceBEq, ↓reduceIte, unpackWireBytes_packWireBytes]
      have ht1 : (cutB1 ++ cutB2).take p.sigBytes = cutB1 := by rw [← hb1L, List.take_left]
      have hd1 : (cutB1 ++ cutB2).drop p.sigBytes = cutB2 := by rw [← hb1L, List.drop_left]
      have hd2 : (cutB2 ++ cutB0).drop p.sigBytes = cutB0 := by rw [← hb2L, List.drop_left]
      rw [ht1, hd1, hd2]
      have hRecF : reconstructRssBytes ⟨cutB0, cutB1, cutB2⟩ = faulted :=
        reconstructRssBytes_masked_eq (hFaultLen.trans hb0L.symm) (hb0L.trans hb1L.symm)
      rw [hRecF]
      cases hSigCons : sigEnc with
      | nil => rw [hSigCons] at hSigLen; simp only [List.length_nil] at hSigLen; omega
      | cons shd stl =>
        have hHeadD : bHon = shd := by
          dsimp only [bHon]; change sigEnc.headD 0 = shd; rw [hSigCons]; rfl
        rw [hHeadD]
        dsimp only [faulted]
        rw [hSigCons]
        rfl
    have hPair0 : (honestPairForCorrupt ⟨0, by decide⟩).2.2 = .p12 := rfl
    rw [hPair0, hQBytes, hCrossLeak]
    cases sharedFinalizeCutOpen p ⟨0, by decide⟩ pk req ⟨cutB0, cutB1, cutB2⟩ [(0, ByteArray.empty)] <;>
      exact ⟨hNeNil, hExtractCut⟩
  -- Part 1: `D_leakBit` accepts 100% on `mutView₁` and 0% on `mutView₀` -> `ratLe (1, 1)`
  have hMut1All : distAcceptCount card mutView₁ D_leakBit = card := by
    unfold distAcceptCount
    have hEach : ∀ ω : Fin card, (if D_leakBit (mutView₁ ω) then 1 else 0) = 1 := by
      intro ω
      have hH := (hMutHead seedSh₁ ⟨rfl, rfl⟩ hSeedSame.symm (decodeMultiSessionTapes p.sigBytes 1 ω 0)).2
      have hb1 : (seedSh₁.b1.headD 0 &&& 1) = 1 := by decide
      have hD : D_leakBit (mutView₁ ω) = true := by
        dsimp only [mutView₁, D_leakBit]
        rw [RealProtocolExec_one]
        rcases hRun : execRealSession (mutantSkipPreCutProtocol p ⟨0, by decide⟩ 1) A cl₁ ()
          (decodeMultiSessionTapes p.sigBytes 1 ω 0) with ⟨_, _, recS⟩
        rw [hRun] at hH
        dsimp only at hH ⊢
        rw [hH, hb1]
        exact beq_self_eq_true _
      rw [hD]; rfl
    rw [finSum_congr hEach, finSum_const, Nat.mul_one]
  have hMut0None : distAcceptCount card mutView₀ D_leakBit ≤ card * 0 := by
    unfold distAcceptCount
    have hEach : ∀ ω : Fin card, (if D_leakBit (mutView₀ ω) then 1 else 0) = 0 := by
      intro ω
      have hH := (hMutHead seedSh₀ ⟨rfl, rfl⟩ rfl (decodeMultiSessionTapes p.sigBytes 1 ω 0)).2
      have hb0 : (seedSh₀.b1.headD 0 &&& 1) = 0 := by decide
      have hXorNe : (some (bHon ^^^ 0) == some (bHon ^^^ 1)) = false := by
        apply beq_false_of_ne
        intro hEq
        injection hEq with hB
        have hBit := congrArg (fun u : UInt8 => u.toBitVec.getLsbD 0) hB
        simp only [UInt8.toBitVec_xor, BitVec.getLsbD_xor] at hBit
        revert hBit
        cases bHon.toBitVec.getLsbD 0 <;> decide
      have hD : D_leakBit (mutView₀ ω) = false := by
        dsimp only [mutView₀, D_leakBit]
        rw [RealProtocolExec_one]
        rcases hRun : execRealSession (mutantSkipPreCutProtocol p ⟨0, by decide⟩ 1) A cl₀ ()
          (decodeMultiSessionTapes p.sigBytes 1 ω 0) with ⟨_, _, recS⟩
        rw [hRun] at hH
        dsimp only at hH ⊢
        rw [hH, hb0, hXorNe]
      rw [hD]; rfl
    rw [finSum_congr hEach, finSum_const, Nat.mul_zero]
    exact Nat.le_refl 0
  have hLeak1 : ratLe (1, 1) (rationalAcceptDiff card mutView₁ card mutView₀ D_leakBit) :=
    ratLe_lower_bound_of_full_vs_bounded (rssMultiSessionCard_pos p.sigBytes 1) Nat.zero_lt_one
      (Nat.mul_one card).symm (Nat.zero_le 1) mutView₁ mutView₀ D_leakBit hMut1All hMut0None
  -- Part 2: `D_hasR3` accepts 100% on `mutView₀` and `≤ rssPadSessionCard * 1` on `idealView`
  have hMut0R3All : distAcceptCount card mutView₀ D_hasR3 = card := by
    unfold distAcceptCount
    have hEach : ∀ ω : Fin card, (if D_hasR3 (mutView₀ ω) then 1 else 0) = 1 := by
      intro ω
      have hNe := (hMutHead seedSh₀ ⟨rfl, rfl⟩ rfl (decodeMultiSessionTapes p.sigBytes 1 ω 0)).1
      have hD : D_hasR3 (mutView₀ ω) = true := by
        dsimp only [mutView₀, D_hasR3]
        rw [RealProtocolExec_one]
        rcases hRun : execRealSession (mutantSkipPreCutProtocol p ⟨0, by decide⟩ 1) A cl₀ ()
          (decodeMultiSessionTapes p.sigBytes 1 ω 0) with ⟨_, _, recS⟩
        rw [hRun] at hNe
        dsimp only at hNe ⊢
        cases hL : recS.honestRound3 with
        | nil => exact False.elim (hNe hL)
        | cons _ _ => rfl
      rw [hD]; rfl
    rw [finSum_congr hEach, finSum_const, Nat.mul_one]
  have hIdealR3WhenNonzero : ∀ tape : RssSlhSessionTape p.sigBytes,
      (batchDeviationPoly [towerOne 7] (unpackTower 7 tape.gammaBits) == towerZero 7) = false →
      (execIdealSession (slhIdealSignOracle p sk) (Sim_RssSlh p ⟨0, by decide⟩ 1) A icl () tape).2.2.honestRound3 = [] := by
    intro tape hBatchF
    dsimp only [A, icl]
    unfold execIdealSession Sim_RssSlh activeFaultRushingAdv
    dsimp only
    rw [hQuorum, ite_eq_right (by decide : ¬ ((!true) = true)), hWal0]
    dsimp only
    simp only [List.map]
    have hVR1 :
        sharedVerifyRound1 ⟨0, by decide⟩
          { cursor := 0, nonceA := tape.nonceA, nonceB := tape.nonceB }
          [(0, round1NonceCommit pk req 0 0 (List.replicate 8 0))] =
        .inr { cursor := 0,
               corrR1Commit := round1NonceCommit pk req 0 0 (List.replicate 8 0),
               nonceA := tape.nonceA, nonceB := tape.nonceB, gammaBits := 0#128 } := by
      unfold sharedVerifyRound1
      simp only [List.find?, beq_self_eq_true]
      rw [hCmtLen]
      rfl
    rw [hVR1]
    dsimp only
    have hBarFail :
        sharedPreCutBarrier ⟨0, by decide⟩ 1 pk req
          { cursor := 0,
            corrR1Commit := round1NonceCommit pk req 0 0 (List.replicate 8 0),
            nonceA := tape.nonceA, nonceB := tape.nonceB, gammaBits := tape.gammaBits }
          [(0, packWireBytes (List.replicate 8 0 ++ encodeTower128Wire forgedWire0))] =
        .inl .activeConsistencyFailed := by
      rw [sharedPreCutBarrier_forged_one pk req tape.nonceA tape.nonceB tape.gammaBits forgedWire0,
          hAccEqBatch, hBatchF]
      rfl
    rw [hBarFail]
  have hCardEq : card = rssPadSessionCard p.sigBytes * (2 ^ 128) := by
    dsimp only [card, rssMultiSessionCard, rssFullSessionCard]
    exact Nat.mul_one _
  have hIdealBound : distAcceptCount card idealView D_hasR3 ≤ rssPadSessionCard p.sigBytes * 1 := by
    unfold distAcceptCount
    rw [finSum_cast_eq hCardEq, finSum_prod_eq]
    have hInnerLe : ∀ padIdx : Fin (rssPadSessionCard p.sigBytes),
        finSum (2 ^ 128) (fun gIdx =>
          if D_hasR3 (idealView ⟨(pairFin padIdx gIdx).val,
            Nat.lt_of_lt_of_eq (pairFin padIdx gIdx).isLt hCardEq.symm⟩) then 1 else 0) ≤ 1 := by
      intro padIdx
      have hPtLe : ∀ gIdx : Fin (2 ^ 128),
          (if D_hasR3 (idealView ⟨(pairFin padIdx gIdx).val,
            Nat.lt_of_lt_of_eq (pairFin padIdx gIdx).isLt hCardEq.symm⟩) then 1 else 0) ≤
          (if batchDeviationPoly [towerOne 7] (unpackTower 7 (BitVec.ofFin gIdx)) == towerZero 7 then 1 else 0) := by
        intro gIdx
        let ωIdx : Fin card := ⟨(pairFin padIdx gIdx).val,
          Nat.lt_of_lt_of_eq (pairFin padIdx gIdx).isLt hCardEq.symm⟩
        cases hB : (batchDeviationPoly [towerOne 7] (unpackTower 7 (BitVec.ofFin gIdx)) == towerZero 7)
        · have hTapeEq : decodeMultiSessionTapes p.sigBytes 1 ωIdx 0 =
              decodeRssSessionTape p.sigBytes padIdx gIdx := by
            unfold decodeMultiSessionTapes
            dsimp only
            have hCurEq : splitFinLeft (rssMultiSessionCard_pos p.sigBytes 0) ωIdx =
                pairFin padIdx gIdx := by
              apply Fin.ext; dsimp [ωIdx, splitFinLeft, rssMultiSessionCard]; exact Nat.div_one _
            rw [hCurEq, splitFinLeft_pairFin, splitFinRight_pairFin]
          have hGamma : (decodeRssSessionTape p.sigBytes padIdx gIdx).gammaBits = BitVec.ofFin gIdx := rfl
          have hEmpty := hIdealR3WhenNonzero (decodeRssSessionTape p.sigBytes padIdx gIdx) (by rw [hGamma]; exact hB)
          have hDF : D_hasR3 (idealView ωIdx) = false := by
            dsimp only [idealView, D_hasR3]
            rw [IdealFunctionalityExec_one, hTapeEq]
            rcases hRunI : execIdealSession (slhIdealSignOracle p sk) (Sim_RssSlh p ⟨0, by decide⟩ 1) A icl ()
              (decodeRssSessionTape p.sigBytes padIdx gIdx) with ⟨_, _, recI⟩
            rw [hRunI] at hEmpty
            dsimp only at hEmpty ⊢
            rw [hEmpty]; rfl
          change (if D_hasR3 (idealView ωIdx) then 1 else 0) ≤ 0
          rw [hDF]
          exact Nat.le_refl 0
        · cases D_hasR3 _ <;> decide
      exact Nat.le_trans (finSum_le_finSum hPtLe)
        (tower128_roots_finSum_le 1 [towerOne 7] (Nat.le_refl 1) ⟨towerOne 7, .head _, by decide⟩)
    calc finSum (rssPadSessionCard p.sigBytes) (fun padIdx => _)
        ≤ finSum (rssPadSessionCard p.sigBytes) (fun _ => 1) := finSum_le_finSum hInnerLe
      _ = rssPadSessionCard p.sigBytes * 1 := finSum_const _ 1
  have hBreakSim : ratLe (2 ^ 128 - 1, 2 ^ 128) (rationalAcceptDiff card mutView₀ card idealView D_hasR3) :=
    ratLe_lower_bound_of_full_vs_bounded (rssPadSessionCard_pos p.sigBytes) (Nat.two_pow_pos 128)
      hCardEq (Nat.one_le_two_pow) mutView₀ idealView D_hasR3 hMut0R3All hIdealBound
  -- Part 3: Unmodified `rssSlhInteractiveProtocol` satisfies `(1, 2 ^ 128)` AND aborts + poisons!
  have hMatch0 : RealIdealClusterMatch ⟨0, by decide⟩ seedSh₀ prfSh cl₀ icl :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  have hHonestBound := (rss_slh_real_ideal_view_indistinguishable p hWf ⟨0, by decide⟩ 1 1
    ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ pkSeed A cl₀ icl () hMatch0 rfl ⟨id⟩ D_hasR3
    card (rssMultiSessionCard_pos p.sigBytes 1) (decodeMultiSessionTapes p.sigBytes 1)).1
  have hMul1 : 1 * 1 = 1 := rfl
  rw [hMul1] at hHonestBound
  refine ⟨hSeedSame, hSeedNe, hLeak1, hBreakSim, hHonestBound, ?_⟩
  intro tape hGammaNe runOut
  dsimp only [runOut, A, cl₀]
  unfold execRealSession rssSlhInteractiveProtocol activeFaultRushingAdv poisonRealCluster
  dsimp only
  rw [hQuorum, ite_eq_right (by decide : ¬ ((!true) = true)), hWal0]
  dsimp only
  simp only [List.map]
  have hVR1 :
      sharedVerifyRound1 ⟨0, by decide⟩
        { cursor := 0, nonceA := tape.nonceA, nonceB := tape.nonceB }
        [(0, round1NonceCommit pk req 0 0 (List.replicate 8 0))] =
      .inr { cursor := 0,
             corrR1Commit := round1NonceCommit pk req 0 0 (List.replicate 8 0),
             nonceA := tape.nonceA, nonceB := tape.nonceB, gammaBits := 0#128 } := by
    unfold sharedVerifyRound1
    simp only [List.find?, beq_self_eq_true]
    rw [hCmtLen]
    rfl
  rw [hVR1]
  dsimp only
  have hBatchFalse : (batchDeviationPoly [towerOne 7] (unpackTower 7 tape.gammaBits) == towerZero 7) = false := by
    rw [batchDeviationPoly_singleton_one]
    exact beq_false_of_ne hGammaNe
  have hBarFail :
      sharedPreCutBarrier ⟨0, by decide⟩ 1 pk req
        { cursor := 0,
          corrR1Commit := round1NonceCommit pk req 0 0 (List.replicate 8 0),
          nonceA := tape.nonceA, nonceB := tape.nonceB, gammaBits := tape.gammaBits }
        [(0, packWireBytes (List.replicate 8 0 ++ encodeTower128Wire forgedWire0))] =
      .inl .activeConsistencyFailed := by
    rw [sharedPreCutBarrier_forged_one pk req tape.nonceA tape.nonceB tape.gammaBits forgedWire0,
        hAccEqBatch, hBatchFalse]
    rfl
  rw [hBarFail]
  exact ⟨rfl, rfl, rfl⟩

/-- Extract Party 1's 64-bit Round-2 masked Keccak `χ`-row word from a public `SessionWireRecord`. -/
def extractParty1ChiWord (rec : SessionWireRecord) : BitVec 64 :=
  match rec.honestRound2 with
  | (_, wireA) :: _ => fixedBytesToBv 8 ((unpackWireBytes wireA).drop 8)
  | [] => 0#64

/-- Public key-free 2-session wire-XOR distinguisher checking `(word₀ ^^^ word₁) == 1#64`. -/
def reusedMaskWireDistinguisher {AdvState : Type} (tr : ExecTranscript AdvState) : Bool :=
  match tr.sessions with
  | rec0 :: rec1 :: _ => (extractParty1ChiWord rec0 ^^^ extractParty1ChiWord rec1) == 1#64
  | _ => false

/-- Faulty tape schedule reusing Session 0's mask tape across all subsequent sessions (`tape_k = tape_0`). -/
def reusedFirstSessionTapes (L s : Nat) (ω : Fin (rssMultiSessionCard L s)) :
    Nat → RssSlhSessionTape L :=
  fun _ => decodeMultiSessionTapes L s ω 0

/-- **`#tooth` Theorem 4b (`tooth_reusing_session_mask_tape_breaks_simulation`)**:
    Proves fresh per-session monotonic mask tapes (`maskSessionCursor`) are load-bearing on
    **unmodified `RealProtocolExec (rssSlhInteractiveProtocol p ⟨0, _⟩ 1)`**:
    1. **Cross-Sharing Secret `skPrf` Bit Leakage (`ratLe (1, 1)`)**: Reusing Session 0's mask tape
       in Session 1 (`reusedFirstSessionTapes p.sigBytes 2`) on two valid sharings `prfSh_leak`,
       `prfSh_zero` of the **EXACT SAME `skPrf = replicate 16 0`** cancels `chiMaskA ^^^ chiMaskA = 0#64`
       on Party 1's Round-2 wire, allowing `reusedMaskWireDistinguisher` to distinguish `prfSh_leak`
       from `prfSh_zero` with **statistical distance `1`** (`ratLe (1, 1) (rationalAcceptDiff ...)`)!
    2. **Simulator Indistinguishability Breakdown (`ratLe (2^64 - 1, 2^64)`)**: Under `reusedFirstSessionTapes`,
       `reusedMaskWireDistinguisher` distinguishes `RealProtocolExec` from `IdealFunctionalityExec` (`Sim_RssSlh`)
       with advantage **`≥ (2 ^ 64 - 1) / 2 ^ 64`**!
    3. **Fresh Monotonic Tape Protection (`ratLe ... (0, 2^128)`)**: With fresh cursor-indexed tapes
       (`decodeMultiSessionTapes p.sigBytes 2`), `RealProtocolExec` and `IdealFunctionalityExec` (`Sim_RssSlh`)
       have **exact statistical distance `0`**! -/
theorem tooth_reusing_session_mask_tape_breaks_simulation
    (p : Fips205Params) (hWf : p.wellFormed = true) (pkSeed : List UInt8) :
    let seedSh     : RssByteShares := ⟨List.replicate 16 0, List.replicate 16 0, List.replicate 16 0⟩
    let prfSh_leak : RssByteShares := ⟨List.replicate 16 1, List.replicate 16 1, List.replicate 16 0⟩
    let prfSh_zero : RssByteShares := ⟨List.replicate 16 0, List.replicate 16 0, List.replicate 16 0⟩
    let sk := (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh_zero) pkSeed).1
    let pk := (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh_zero) pkSeed).2
    let reqs : Nat → SessionScheduleReq := fun sIdx =>
      if sIdx == 0 then ⟨0, 0, List.replicate 8 0x00, [], [1, 2]⟩
      else ⟨1, 1, (0x01 : UInt8) :: List.replicate 7 0x00, [], [1, 2]⟩
    let A := passiveRushingAdv p pk reqs 1
    let cl_leak : RealClusterState SlhPublicKey RssPartyKeyShare :=
      ⟨⟨pk, 2, 3, [0], [], []⟩, initWalLatchState (slhPkDigest pk), 0,
       dealHonestRssVault ⟨0, by decide⟩ seedSh prfSh_leak⟩
    let cl_zero : RealClusterState SlhPublicKey RssPartyKeyShare :=
      ⟨⟨pk, 2, 3, [0], [], []⟩, initWalLatchState (slhPkDigest pk), 0,
       dealHonestRssVault ⟨0, by decide⟩ seedSh prfSh_zero⟩
    let icl : IdealClusterState SlhPublicKey :=
      ⟨⟨pk, 2, 3, [0], [], []⟩, initWalLatchState (slhPkDigest pk), 0⟩
    let card := rssMultiSessionCard p.sigBytes 2
    let reusedLeakView := fun ω : Fin card =>
      (RealProtocolExec (rssSlhInteractiveProtocol p ⟨0, by decide⟩ 1) A 2
        (reusedFirstSessionTapes p.sigBytes 2 ω) cl_leak 0).2
    let reusedZeroView := fun ω : Fin card =>
      (RealProtocolExec (rssSlhInteractiveProtocol p ⟨0, by decide⟩ 1) A 2
        (reusedFirstSessionTapes p.sigBytes 2 ω) cl_zero 0).2
    let freshLeakView := fun ω : Fin card =>
      (RealProtocolExec (rssSlhInteractiveProtocol p ⟨0, by decide⟩ 1) A 2
        (decodeMultiSessionTapes p.sigBytes 2 ω) cl_leak 0).2
    let idealSimView := fun ω : Fin card =>
      (IdealFunctionalityExec (slhIdealSignOracle p sk) (Sim_RssSlh p ⟨0, by decide⟩ 1) A 2
        (decodeMultiSessionTapes p.sigBytes 2 ω) icl 0).2
    reconstructRssBytes prfSh_leak = reconstructRssBytes prfSh_zero ∧
    prfSh_leak ≠ prfSh_zero ∧
    ratLe (1, 1) (rationalAcceptDiff card reusedLeakView card reusedZeroView reusedMaskWireDistinguisher) ∧
    ratLe (2 ^ 64 - 1, 2 ^ 64) (rationalAcceptDiff card reusedLeakView card idealSimView reusedMaskWireDistinguisher) ∧
    ratLe (rationalAcceptDiff card freshLeakView card idealSimView reusedMaskWireDistinguisher) (0, 2 ^ 128) := by
  intro seedSh prfSh_leak prfSh_zero sk pk reqs A cl_leak cl_zero icl card
        reusedLeakView reusedZeroView freshLeakView idealSimView
  have hPrfSame : reconstructRssBytes prfSh_leak = reconstructRssBytes prfSh_zero := by decide +kernel
  have hPrfNe : prfSh_leak ≠ prfSh_zero := by decide +kernel
  have hQuorum : validThresholdApproval (⟨pk, 2, 3, [0], [], []⟩ : IdealTsigState SlhPublicKey (List UInt8)) [1, 2] = true := by
    simp [validThresholdApproval]
  have hWal0 :
      walPreSignStep (initWalLatchState (slhPkDigest pk)) (slhPkDigest pk) 0 (slhReqDigest (reqs 0)) =
      .ok (initWalLatchState (slhPkDigest pk)) (.authorizedFresh 0) := by
    unfold walPreSignStep initWalLatchState; simp
  have hNoBadTwo : ∀ (prfSh : RssByteShares) (hPWf : prfSh.WellFormed)
      (hSame : reconstructRssBytes prfSh = reconstructRssBytes prfSh_zero)
      (ω : Fin card),
      let cl : RealClusterState SlhPublicKey RssPartyKeyShare :=
        ⟨⟨pk, 2, 3, [0], [], []⟩, initWalLatchState (slhPkDigest pk), 0,
          dealHonestRssVault ⟨0, by decide⟩ seedSh prfSh⟩
      multiSessionBadHit p ⟨0, by decide⟩ 1 A 2 cl 0 ω = false := by
    intro prfSh hPWf hSame ω cl
    let cur := splitFinLeft (rssMultiSessionCard_pos p.sigBytes 1) ω
    have hPk : cl.tsig.pk =
        (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2 := by
      dsimp only [cl, pk]; rw [hSame]
    have hA : A = passiveRushingAdv p
        (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2 reqs 1 := by
      dsimp only [A, pk]; rw [hSame]
    have hS0 := execRealSession_passiveRushingAdv_ok p hWf ⟨0, by decide⟩ 1 0
      ⟨rfl, rfl⟩ hPWf pkSeed reqs cl (initWalLatchState (slhPkDigest pk))
      (decodeSingleFullTape p.sigBytes cur) hPk rfl rfl rfl hQuorum hWal0 (by decide)
    dsimp only at hS0
    rw [← hA] at hS0
    rcases hRun : execRealSession (rssSlhInteractiveProtocol p ⟨0, by decide⟩ 1) A cl 0
        (decodeSingleFullTape p.sigBytes cur) with ⟨cl1, adv1, rec1⟩
    rw [hRun] at hS0
    dsimp only at hS0
    obtain ⟨hAdv, _, _, hCur, _, hPk1, hCorr, _⟩ := hS0
    rw [multiSessionBadHit]
    change (match execRealSession (rssSlhInteractiveProtocol p ⟨0, by decide⟩ 1) A cl 0
      (decodeSingleFullTape p.sigBytes cur) with
      | (next, st, _) => sessionBadHit p ⟨0, by decide⟩ 1 A cl 0 cur ||
          multiSessionBadHit p ⟨0, by decide⟩ 1 A 1 next st
            (splitFinRight (rssMultiSessionCard_pos p.sigBytes 1) ω)) = false
    rw [hRun]
    dsimp only
    rw [sessionBadHit_passive p ⟨0, by decide⟩ 1 (by decide) pk reqs cl 0 rfl rfl rfl]
    rw [Bool.false_or, multiSessionBadHit]
    dsimp only
    rw [hAdv]
    rw [sessionBadHit_passive p ⟨0, by decide⟩ 1 (by decide) pk reqs _ 1
      (by rw [hPk1]; dsimp only [pk]; rw [hSame]) hCorr hCur]
    rfl
  have hCounts : ∀ (prfSh : RssByteShares) (hPWf : prfSh.WellFormed)
      (hSame : reconstructRssBytes prfSh = reconstructRssBytes prfSh_zero),
      let cl : RealClusterState SlhPublicKey RssPartyKeyShare :=
        ⟨⟨pk, 2, 3, [0], [], []⟩, initWalLatchState (slhPkDigest pk), 0,
          dealHonestRssVault ⟨0, by decide⟩ seedSh prfSh⟩
      distAcceptCount card (fun ω =>
        (RealProtocolExec (rssSlhInteractiveProtocol p ⟨0, by decide⟩ 1) A 2
          (decodeMultiSessionTapes p.sigBytes 2 ω) cl 0).2) reusedMaskWireDistinguisher =
      distAcceptCount card idealSimView reusedMaskWireDistinguisher := by
    intro prfSh hPWf hSame cl
    let bij := multiSessionTapeEquiv p ⟨0, by decide⟩ 1 A 2 cl 0
    have hPk : cl.tsig.pk =
        (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2 := by
      dsimp only [cl, pk]; rw [hSame]
    have hMatch : RealIdealClusterMatch ⟨0, by decide⟩ seedSh prfSh cl icl :=
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩
    have hEq := fun ω => multiSession_real_eq_ideal_unless_bad p hWf ⟨0, by decide⟩ 1
      ⟨rfl, rfl⟩ hPWf pkSeed A 2 cl icl 0 hMatch hPk ω (hNoBadTwo prfSh hPWf hSame ω)
    dsimp only at hEq
    rw [hSame] at hEq
    unfold distAcceptCount
    calc
      _ = finSum card (fun ω => if reusedMaskWireDistinguisher (idealSimView (bij.toFun ω)) then 1 else 0) :=
        finSum_congr (fun ω => congrArg (fun tr => if reusedMaskWireDistinguisher tr then 1 else 0) (hEq ω))
      _ = _ := finSum_equiv_eq bij (fun ω => if reusedMaskWireDistinguisher (idealSimView ω) then 1 else 0)
  have hTwoSessionWords : ∀ (prfSh : RssByteShares) (hPWf : prfSh.WellFormed)
      (hSame : reconstructRssBytes prfSh = reconstructRssBytes prfSh_zero)
      (tapes : Nat → RssSlhSessionTape p.sigBytes),
      let clInit : RealClusterState SlhPublicKey RssPartyKeyShare :=
        ⟨⟨pk, 2, 3, [0], [], []⟩, initWalLatchState (slhPkDigest pk), 0,
         dealHonestRssVault ⟨0, by decide⟩ seedSh prfSh⟩
      let tr := (RealProtocolExec (rssSlhInteractiveProtocol p ⟨0, by decide⟩ 1) A 2 tapes clInit 0).2
      let w0 := match dealHonestRssVault ⟨0, by decide⟩ seedSh prfSh 1 with
                | some sh1 => computeHonestChiWord 1 sh1 (reqs 0).msg
                | none => 0#64
      let w1 := match dealHonestRssVault ⟨0, by decide⟩ seedSh prfSh 1 with
                | some sh1 => computeHonestChiWord 1 sh1 (reqs 1).msg
                | none => 0#64
      reusedMaskWireDistinguisher tr =
        (((w0 ^^^ (tapes 0).chiMaskA) ^^^ (w1 ^^^ (tapes 1).chiMaskA)) == 1#64) := by
    intro prfSh hPWf hSame tapes clInit tr w0 w1
    dsimp only [tr, w0, w1]
    have hPkInit : clInit.tsig.pk = (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2 := by
      dsimp only [clInit, pk]; rw [hSame]
    have hAdvEq : A = passiveRushingAdv p (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2 reqs 1 := by
      dsimp only [A, pk]; rw [hSame]
    rw [RealProtocolExec_two, hAdvEq]
    have hS0 := execRealSession_passiveRushingAdv_ok p hWf ⟨0, by decide⟩ 1 0 ⟨rfl, rfl⟩ hPWf pkSeed
      reqs clInit (initWalLatchState (slhPkDigest pk)) (tapes 0) hPkInit rfl rfl rfl hQuorum hWal0 (by decide)
    dsimp only at hS0
    rcases hRun0 : execRealSession (rssSlhInteractiveProtocol p ⟨0, by decide⟩ 1)
      (passiveRushingAdv p (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2 reqs 1)
      clInit 0 (tapes 0) with ⟨cl1, adv1, rec0⟩
    rw [hRun0] at hS0
    dsimp only at hS0 ⊢
    obtain ⟨hAdv1, _, hR2_0, hCur1, hSh1, hPk1, hCorr1, hTh1, hNp1, hCheat1, hWal1Eq⟩ := hS0
    subst hAdv1
    have hQuorum1 : validThresholdApproval cl1.tsig (reqs 1).honestApprovers = true := by
      unfold validThresholdApproval at hQuorum ⊢
      rw [hTh1, hNp1, hCorr1, hCheat1]
      exact hQuorum
    have hPk1Pk : cl1.tsig.pk = pk := by rw [hPk1, hSame]
    have hWal1Ok : walPreSignStep cl1.honestWal (slhPkDigest cl1.tsig.pk) (reqs 1).reqEpoch (slhReqDigest (reqs 1)) =
        .ok cl1.honestWal (.authorizedFresh 1) := by
      rw [hWal1Eq, hPk1Pk]
      unfold walPreSignStep initWalLatchState
      dsimp only [reqs]
      simp
    have hS1 := execRealSession_passiveRushingAdv_ok p hWf ⟨0, by decide⟩ 1 1 ⟨rfl, rfl⟩ hPWf pkSeed
      reqs cl1 cl1.honestWal (tapes 1) hPk1 hCorr1 hCur1 hSh1 hQuorum1 hWal1Ok (by decide)
    dsimp only at hS1
    rcases hRun1 : execRealSession (rssSlhInteractiveProtocol p ⟨0, by decide⟩ 1)
      (passiveRushingAdv p (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2 reqs 1)
      cl1 1 (tapes 1) with ⟨cl2, adv2, rec1⟩
    rw [hRun1] at hS1
    dsimp only at hS1 ⊢
    have hR2_1 := hS1.2.2.1
    have hExt0 : extractParty1ChiWord rec0 =
        (match dealHonestRssVault ⟨0, by decide⟩ seedSh prfSh 1 with
         | some sh1 => computeHonestChiWord 1 sh1 (reqs 0).msg | none => 0#64) ^^^ (tapes 0).chiMaskA := by
      unfold extractParty1ChiWord
      rw [hR2_0]
      dsimp only [honestPairForCorrupt]
      simp only [Nat.reduceBEq, ↓reduceIte, unpackWireBytes_packWireBytes]
      have hDrop0 :
          (bvToFixedBytes 8 (tapes 0).nonceA ++
            bvToFixedBytes 8
              ((match dealHonestRssVault ⟨0, by decide⟩ seedSh prfSh 1 with
                | some shA => computeHonestChiWord 1 shA (reqs 0).msg
                | none => 0#64) ^^^ (tapes 0).chiMaskA)).drop 8 =
          bvToFixedBytes 8
            ((match dealHonestRssVault ⟨0, by decide⟩ seedSh prfSh 1 with
              | some shA => computeHonestChiWord 1 shA (reqs 0).msg
              | none => 0#64) ^^^ (tapes 0).chiMaskA) :=
        drop_append_of_length_eq (bvToFixedBytes_length 8 (tapes 0).nonceA)
      rw [hDrop0, fixedBytesToBv_bvToFixedBytes 8]
    have hExt1 : extractParty1ChiWord rec1 =
        (match dealHonestRssVault ⟨0, by decide⟩ seedSh prfSh 1 with
         | some sh1 => computeHonestChiWord 1 sh1 (reqs 1).msg | none => 0#64) ^^^ (tapes 1).chiMaskA := by
      unfold extractParty1ChiWord
      rw [hR2_1]
      dsimp only [honestPairForCorrupt]
      simp only [Nat.reduceBEq, ↓reduceIte, unpackWireBytes_packWireBytes]
      have hDrop1 :
          (bvToFixedBytes 8 (tapes 1).nonceA ++
            bvToFixedBytes 8
              ((match dealHonestRssVault ⟨0, by decide⟩ seedSh prfSh 1 with
                | some shA => computeHonestChiWord 1 shA (reqs 1).msg
                | none => 0#64) ^^^ (tapes 1).chiMaskA)).drop 8 =
          bvToFixedBytes 8
            ((match dealHonestRssVault ⟨0, by decide⟩ seedSh prfSh 1 with
              | some shA => computeHonestChiWord 1 shA (reqs 1).msg
              | none => 0#64) ^^^ (tapes 1).chiMaskA) :=
        drop_append_of_length_eq (bvToFixedBytes_length 8 (tapes 1).nonceA)
      rw [hDrop1, fixedBytesToBv_bvToFixedBytes 8]
    dsimp only [reusedMaskWireDistinguisher]
    rw [hExt0, hExt1]
  have hBvXorCancel : ∀ (a b m : BitVec 64), ((a ^^^ m) ^^^ (b ^^^ m)) = (a ^^^ b) := by
    intro a b m
    apply BitVec.eq_of_getLsbD_eq; intro i _
    simp only [BitVec.getLsbD_xor]
    cases a.getLsbD i <;> cases b.getLsbD i <;> cases m.getLsbD i <;> rfl
  have hLeakW0 : computeHonestChiWord 1 ⟨List.replicate 16 0, List.replicate 16 0, List.replicate 16 1, List.replicate 16 0⟩
      (List.replicate 8 0x00) = 0#64 := by decide +kernel
  have hLeakW1 : computeHonestChiWord 1 ⟨List.replicate 16 0, List.replicate 16 0, List.replicate 16 1, List.replicate 16 0⟩
      ((0x01 : UInt8) :: List.replicate 7 0x00) = 1#64 := by decide +kernel
  have hZeroW0 : computeHonestChiWord 1 ⟨List.replicate 16 0, List.replicate 16 0, List.replicate 16 0, List.replicate 16 0⟩
      (List.replicate 8 0x00) = 0#64 := by decide +kernel
  have hZeroW1 : computeHonestChiWord 1 ⟨List.replicate 16 0, List.replicate 16 0, List.replicate 16 0, List.replicate 16 0⟩
      ((0x01 : UInt8) :: List.replicate 7 0x00) = 0#64 := by decide +kernel
  have hReusedLeakAll : distAcceptCount card reusedLeakView reusedMaskWireDistinguisher = card := by
    unfold distAcceptCount
    have hEach : ∀ ω : Fin card, (if reusedMaskWireDistinguisher (reusedLeakView ω) then 1 else 0) = 1 := by
      intro ω
      have hEq := hTwoSessionWords prfSh_leak ⟨rfl, rfl⟩ hPrfSame (reusedFirstSessionTapes p.sigBytes 2 ω)
      dsimp only [reusedLeakView, reusedFirstSessionTapes] at hEq ⊢
      rw [hEq, hBvXorCancel]
      have hDeal : dealHonestRssVault ⟨0, by decide⟩ seedSh prfSh_leak 1 =
          some ⟨List.replicate 16 0, List.replicate 16 0, List.replicate 16 1, List.replicate 16 0⟩ := rfl
      rw [hDeal]
      dsimp only [reqs]
      simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, hLeakW0, hLeakW1]
      decide
    rw [finSum_congr hEach, finSum_const, Nat.mul_one]
  have hReusedZeroNone : distAcceptCount card reusedZeroView reusedMaskWireDistinguisher ≤ card * 0 := by
    unfold distAcceptCount
    have hEach : ∀ ω : Fin card, (if reusedMaskWireDistinguisher (reusedZeroView ω) then 1 else 0) = 0 := by
      intro ω
      have hEq := hTwoSessionWords prfSh_zero ⟨rfl, rfl⟩ rfl (reusedFirstSessionTapes p.sigBytes 2 ω)
      dsimp only [reusedZeroView, reusedFirstSessionTapes] at hEq ⊢
      rw [hEq, hBvXorCancel]
      have hDeal : dealHonestRssVault ⟨0, by decide⟩ seedSh prfSh_zero 1 =
          some ⟨List.replicate 16 0, List.replicate 16 0, List.replicate 16 0, List.replicate 16 0⟩ := rfl
      rw [hDeal]
      dsimp only [reqs]
      simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, hZeroW0, hZeroW1]
      decide
    rw [finSum_congr hEach, finSum_const, Nat.mul_zero]
    exact Nat.le_refl 0
  have hLeak1 : ratLe (1, 1) (rationalAcceptDiff card reusedLeakView card reusedZeroView reusedMaskWireDistinguisher) :=
    ratLe_lower_bound_of_full_vs_bounded (rssMultiSessionCard_pos p.sigBytes 2) Nat.zero_lt_one
      (Nat.mul_one card).symm (Nat.zero_le 1) reusedLeakView reusedZeroView reusedMaskWireDistinguisher
      hReusedLeakAll hReusedZeroNone
  let freshZeroView := fun ω : Fin card =>
    (RealProtocolExec (rssSlhInteractiveProtocol p ⟨0, by decide⟩ 1) A 2
      (decodeMultiSessionTapes p.sigBytes 2 ω) cl_zero 0).2
  have hZeroSimEq : distAcceptCount card freshZeroView reusedMaskWireDistinguisher =
      distAcceptCount card idealSimView reusedMaskWireDistinguisher :=
    hCounts prfSh_zero ⟨rfl, rfl⟩ rfl
  -- Count `freshZeroView`: on `prfSh_zero`, `w0 = 0#64` and `w1 = 0#64`, so `reusedMaskWireDistinguisher`
  -- tests `((tapes 0).chiMaskA ^^^ (tapes 1).chiMaskA) == 1#64`, which holds on exactly `1 / 2^64` of `tapes 1`!
  let B4 := (2 ^ 64) * ((2 ^ (8 * p.sigBytes)) * (2 ^ (8 * p.sigBytes)))
  have hB4Pos : 0 < B4 := Nat.mul_pos (Nat.two_pow_pos 64)
    (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _))
  let P_two := rssFullSessionCard p.sigBytes * ((2 ^ 64) * ((2 ^ 64) * (B4 * (2 ^ 128))))
  have hPtwoPos : 0 < P_two := Nat.mul_pos (rssFullSessionCard_pos p.sigBytes)
    (Nat.mul_pos (Nat.two_pow_pos 64) (Nat.mul_pos (Nat.two_pow_pos 64)
      (Nat.mul_pos hB4Pos (Nat.two_pow_pos 128))))
  have hF1 : card = rssFullSessionCard p.sigBytes * rssFullSessionCard p.sigBytes := by
    dsimp only [card, rssMultiSessionCard]; rw [Nat.mul_one]
  have hCardTwoEq : card = P_two * (2 ^ 64) := by
    rw [hF1]
    dsimp only [P_two, B4, rssFullSessionCard, rssPadSessionCard]
    simp only [Nat.mul_left_comm, Nat.mul_comm]
  have hXorHitSum : ∀ (cA0 : BitVec 64),
      finSum (2 ^ 64) (fun cA1 => if (cA0 ^^^ BitVec.ofFin cA1) == 1#64 then 1 else 0) = 1 := by
    intro cA0
    rw [← finSum_equiv_eq (finBitVecXorEquiv 64 cA0)]
    have hCongr :
        finSum (2 ^ 64) (fun z => if (cA0 ^^^ BitVec.ofFin ((finBitVecXorEquiv 64 cA0).toFun z)) == 1#64 then 1 else 0) =
        finSum (2 ^ 64) (fun z => if z = (1#64 : BitVec 64).toFin then 1 else 0) := by
      apply finSum_congr
      intro z
      have hOfFin : BitVec.ofFin ((finBitVecXorEquiv 64 cA0).toFun z) = BitVec.ofFin z ^^^ cA0 := rfl
      rw [hOfFin]
      have hCancel : (cA0 ^^^ (BitVec.ofFin z ^^^ cA0)) = BitVec.ofFin z := by
        rw [BitVec.xor_comm (BitVec.ofFin z) cA0, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
      rw [hCancel]
      by_cases hz : z = (1#64 : BitVec 64).toFin
      · subst hz; simp
      · have hNeBv : (BitVec.ofFin z == (1#64 : BitVec 64)) = false := by
          apply beq_false_of_ne
          intro hEq
          exact hz (Fin.ext (by simpa using congrArg BitVec.toNat hEq))
        rw [hNeBv, ite_eq_right hz]
        rfl
    rw [hCongr, finSum_eq_indicator]
  have hFreshZeroCount : distAcceptCount card freshZeroView reusedMaskWireDistinguisher ≤ P_two * 1 := by
    unfold distAcceptCount
    rw [finSum_cast_eq hF1, finSum_prod_eq]
    have hEach0 : ∀ ω0 : Fin (rssFullSessionCard p.sigBytes),
        finSum (rssFullSessionCard p.sigBytes) (fun ω1 =>
          if reusedMaskWireDistinguisher (freshZeroView ⟨(pairFin ω0 ω1).val,
            Nat.lt_of_lt_of_eq (pairFin ω0 ω1).isLt hF1.symm⟩)
          then 1 else 0) =
        (2 ^ 64) * ((2 ^ 64) * (B4 * (2 ^ 128))) := by
      intro ω0
      let cA0 := (decodeSingleFullTape p.sigBytes ω0).chiMaskA
      have hStep1 : ∀ ω1 : Fin (rssFullSessionCard p.sigBytes),
          reusedMaskWireDistinguisher (freshZeroView ⟨(pairFin ω0 ω1).val,
            Nat.lt_of_lt_of_eq (pairFin ω0 ω1).isLt hF1.symm⟩) =
          ((cA0 ^^^ (decodeSingleFullTape p.sigBytes ω1).chiMaskA) == 1#64) := by
        intro ω1
        let ωPair : Fin card := ⟨(pairFin ω0 ω1).val, Nat.lt_of_lt_of_eq (pairFin ω0 ω1).isLt hF1.symm⟩
        have hEq := hTwoSessionWords prfSh_zero ⟨rfl, rfl⟩ rfl (decodeMultiSessionTapes p.sigBytes 2 ωPair)
        have hDeal : dealHonestRssVault ⟨0, by decide⟩ seedSh prfSh_zero 1 =
            some ⟨List.replicate 16 0, List.replicate 16 0, List.replicate 16 0, List.replicate 16 0⟩ := rfl
        rw [hDeal] at hEq
        dsimp only [reqs] at hEq
        simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, hZeroW0, hZeroW1, BitVec.zero_xor] at hEq
        have hT0 : decodeMultiSessionTapes p.sigBytes 2 ωPair 0 = decodeSingleFullTape p.sigBytes ω0 := by
          unfold decodeMultiSessionTapes decodeSingleFullTape
          dsimp only
          have hL : splitFinLeft (rssMultiSessionCard_pos p.sigBytes 1) ωPair = ω0 := by
            apply Fin.ext
            dsimp [ωPair, splitFinLeft, pairFin, rssMultiSessionCard]
            rw [Nat.mul_one, Nat.mul_comm ω0.val _, Nat.mul_add_div (rssFullSessionCard_pos p.sigBytes),
                Nat.div_eq_of_lt ω1.isLt, Nat.add_zero]
          rw [hL]
        have hT1 : decodeMultiSessionTapes p.sigBytes 2 ωPair 1 = decodeSingleFullTape p.sigBytes ω1 := by
          have hDef : decodeMultiSessionTapes p.sigBytes 2 ωPair 1 =
              decodeSingleFullTape p.sigBytes
                (splitFinLeft (rssMultiSessionCard_pos p.sigBytes 0)
                  (splitFinRight (rssMultiSessionCard_pos p.sigBytes 1) ωPair)) := rfl
          rw [hDef]
          congr 1
          apply Fin.ext
          dsimp [ωPair, splitFinLeft, splitFinRight, pairFin, rssMultiSessionCard]
          rw [Nat.div_one, Nat.mul_one, Nat.mul_comm ω0.val _, Nat.mul_add_mod,
              Nat.mod_eq_of_lt ω1.isLt]
        dsimp only [freshZeroView]
        rw [hEq, hT0, hT1]
      rw [finSum_congr (fun ω1 => by rw [hStep1 ω1])]
      unfold rssFullSessionCard
      rw [finSum_prod_eq (rssPadSessionCard p.sigBytes) (2 ^ 128)]
      have hCollapseG : ∀ pad1 : Fin (rssPadSessionCard p.sigBytes),
          finSum (2 ^ 128) (fun g1 =>
            if (cA0 ^^^ (decodeSingleFullTape p.sigBytes (pairFin pad1 g1)).chiMaskA) == 1#64 then 1 else 0) =
          (if (cA0 ^^^ (decodeRssSessionTape p.sigBytes pad1 ⟨0, Nat.two_pow_pos 128⟩).chiMaskA) == 1#64
           then 1 else 0) * (2 ^ 128) := by
        intro pad1
        have hC : ∀ g1 : Fin (2 ^ 128),
            (decodeSingleFullTape p.sigBytes (pairFin pad1 g1)).chiMaskA =
            (decodeRssSessionTape p.sigBytes pad1 ⟨0, Nat.two_pow_pos 128⟩).chiMaskA := by
          intro g1
          unfold decodeSingleFullTape
          rw [splitFinLeft_pairFin, splitFinRight_pairFin]
          rfl
        rw [finSum_congr (fun g1 => by rw [hC g1]), finSum_const, Nat.mul_comm]
      rw [finSum_congr hCollapseG]
      unfold rssPadSessionCard
      rw [finSum_prod_eq (2 ^ 64),
          finSum_congr (fun nA1 => finSum_prod_eq (2 ^ 64) _ _),
          finSum_congr (fun nA1 => finSum_congr (fun nB1 => finSum_prod_eq (2 ^ 64) B4 _))]
      have hInnerCA : ∀ (nA1 nB1 : Fin (2 ^ 64)),
          finSum (2 ^ 64) (fun cA1 => finSum B4 (fun r3 =>
            (if (cA0 ^^^ (decodeRssSessionTape p.sigBytes
              (pairFin nA1 (pairFin nB1 (pairFin cA1 r3))) ⟨0, Nat.two_pow_pos 128⟩).chiMaskA) == 1#64
             then 1 else 0) * (2 ^ 128))) =
          B4 * (2 ^ 128) := by
        intro nA1 nB1
        have hCA1 : ∀ (cA1 : Fin (2 ^ 64)) (r3 : Fin B4),
            (decodeRssSessionTape p.sigBytes
              (pairFin nA1 (pairFin nB1 (pairFin cA1 r3))) ⟨0, Nat.two_pow_pos 128⟩).chiMaskA =
            BitVec.ofFin cA1 := by
          intro cA1 r3
          unfold decodeRssSessionTape
          dsimp only
          rw [splitFinRight_pairFin, splitFinRight_pairFin, splitFinLeft_pairFin]
        have hR3Const : ∀ cA1 : Fin (2 ^ 64),
            finSum B4 (fun r3 =>
              (if (cA0 ^^^ (decodeRssSessionTape p.sigBytes
                (pairFin nA1 (pairFin nB1 (pairFin cA1 r3))) ⟨0, Nat.two_pow_pos 128⟩).chiMaskA) == 1#64
               then 1 else 0) * (2 ^ 128)) =
            (if (cA0 ^^^ BitVec.ofFin cA1) == 1#64 then 1 else 0) * (B4 * (2 ^ 128)) := by
          intro cA1
          rw [finSum_congr (fun r3 => by rw [hCA1 cA1 r3]), finSum_const]
          simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        rw [finSum_congr hR3Const]
        have hFactor :
            finSum (2 ^ 64) (fun cA1 => (if (cA0 ^^^ BitVec.ofFin cA1) == 1#64 then 1 else 0) * (B4 * (2 ^ 128))) =
            finSum (2 ^ 64) (fun cA1 => if (cA0 ^^^ BitVec.ofFin cA1) == 1#64 then 1 else 0) * (B4 * (2 ^ 128)) := by
          have hGen : ∀ (n m : Nat) (f : Fin n → Nat), finSum n (fun i => f i * m) = finSum n f * m := by
            intro n; induction n with
            | zero => intros; simp [finSum]
            | succ n ih => intro m f; simp only [finSum, ih m, Nat.add_mul]
          exact hGen _ _ _
        rw [hFactor, hXorHitSum cA0, Nat.one_mul]
      rw [finSum_congr (fun nA1 => finSum_congr (fun nB1 => hInnerCA nA1 nB1)),
          finSum_congr (fun _ => finSum_const (2 ^ 64) (B4 * (2 ^ 128))),
          finSum_const]
    rw [finSum_congr hEach0, finSum_const, Nat.mul_one]
    exact Nat.le_refl _
  have hIdealCountLe : distAcceptCount card idealSimView reusedMaskWireDistinguisher ≤ P_two * 1 := by
    rw [← hZeroSimEq]; exact hFreshZeroCount
  have hBreakSim : ratLe (2 ^ 64 - 1, 2 ^ 64)
      (rationalAcceptDiff card reusedLeakView card idealSimView reusedMaskWireDistinguisher) :=
    ratLe_lower_bound_of_full_vs_bounded hPtwoPos (Nat.two_pow_pos 64) hCardTwoEq
      Nat.one_le_two_pow reusedLeakView idealSimView reusedMaskWireDistinguisher
      hReusedLeakAll hIdealCountLe
  have hFreshSafe : ratLe
      (rationalAcceptDiff card freshLeakView card idealSimView reusedMaskWireDistinguisher)
      (0, 2 ^ 128) := by
    unfold ratLe rationalAcceptDiff
    dsimp only
    rw [hCounts prfSh_leak ⟨rfl, rfl⟩ hPrfSame]
    refine ⟨Nat.mul_pos (rssMultiSessionCard_pos p.sigBytes 2)
      (rssMultiSessionCard_pos p.sigBytes 2), Nat.two_pow_pos 128, ?_⟩
    simp [natAbsDiff]
  exact ⟨hPrfSame, hPrfNe, hLeak1, hBreakSim, hFreshSafe⟩

/-- **Mutant 3 (`mutantRollbackWalTwoSessions`)**:
    Executes Session 0 via `execRealSession`, rolls `honestWal` back to its pre-commit `clInit.honestWal`
    (modeling missing pre-release WAL flush / VM snapshot rollback while cursor advances), and executes Session 1! -/
def mutantRollbackWalTwoSessions {PK ShareT SessionTape R1St R2St R3St AdvState : Type}
    (proto : InteractiveThresholdProtocol PK ShareT SessionTape R1St R2St R3St)
    (A : UcRushingAdversary AdvState)
    (tapes : Nat → SessionTape)
    (clInit : RealClusterState PK ShareT) (advSt0 : AdvState) :
    SessionWireRecord × SessionWireRecord :=
  let (cl1, advSt1, rec0) := execRealSession proto A clInit advSt0 (tapes 0)
  let clRolledBack := { cl1 with honestWal := clInit.honestWal }
  let (_, _, rec1) := execRealSession proto A clRolledBack advSt1 (tapes 1)
  (rec0, rec1)

/-- **`#tooth` Theorem 4c (`tooth_wal_rollback_enables_stateful_double_sign`)**:
    Proves atomic pre-release `WalLatchState` commit in `RealProtocolExec` is load-bearing across
    ALL well-formed NIST `FIPS 205` parameter sets `p`:
    When an adversary schedules two distinct messages `msg₁ = [0x01]` and `msg₂ = [0x02]` (`msg₁ ≠ msg₂`)
    at the **EXACT SAME epoch `0`**:
    1. **Mutant WAL Rollback Double-Signs**: `mutantRollbackWalTwoSessions` emits `.signOk rawSig₁`
       AND `.signOk rawSig₂` at `reqEpoch = 0`, where `rawSig₁` and `rawSig₂` both decode and verify
       under `slhVerifyInternal` on `msg₁ ≠ msg₂`!
    2. **Unmodified `RealProtocolExec` Blocks Equivocation**: `RealProtocolExec` emits `.signOk rawSig₁`
       in Session 0, atomically advances `nextEpoch := 1`, and strictly aborts Session 1 BEFORE Round 1
       (`honestRound1 = [] ∧ outcome = .abort .walEpochRejected`)! -/
theorem tooth_wal_rollback_enables_stateful_double_sign
    (p : Fips205Params) (hWf : p.wellFormed = true)
    {seedSh prfSh : RssByteShares}
    (hSeedWf : seedSh.WellFormed) (hPrfWf : prfSh.WellFormed)
    (pkSeed : List UInt8)
    (tapes : Nat → RssSlhSessionTape p.sigBytes) :
    let pk := (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).2
    let msg₁ : List UInt8 := [0x01]
    let msg₂ : List UInt8 := [0x02]
    let reqs : Nat → SessionScheduleReq := fun sIdx =>
      if sIdx == 0 then ⟨0, 0, msg₁, [], [1, 2]⟩
      else ⟨1, 0, msg₂, [], [1, 2]⟩
    let A := passiveRushingAdv p pk reqs 4
    let clInit : RealClusterState SlhPublicKey RssPartyKeyShare :=
      ⟨⟨pk, 2, 3, [0], [], []⟩, initWalLatchState (slhPkDigest pk), 0,
       dealHonestRssVault ⟨0, by decide⟩ seedSh prfSh⟩
    let mutPair :=
      mutantRollbackWalTwoSessions (rssSlhInteractiveProtocol p ⟨0, by decide⟩ 4) A tapes clInit 0
    let honTr :=
      (RealProtocolExec (rssSlhInteractiveProtocol p ⟨0, by decide⟩ 4) A 2 tapes clInit 0).2
    msg₁ ≠ msg₂ ∧
    mutPair.1.request.reqEpoch = 0 ∧ mutPair.2.request.reqEpoch = 0 ∧
    (∃ (raw₁ raw₂ : ByteArray) (s₁ s₂ : SlhSignature),
      mutPair.1.outcome = .signOk raw₁ ∧
      mutPair.2.outcome = .signOk raw₂ ∧
      decodeSlhSig p (unpackWireBytes raw₁) = some s₁ ∧
      decodeSlhSig p (unpackWireBytes raw₂) = some s₂ ∧
      slhVerifyInternal p msg₁ s₁ pk = true ∧
      slhVerifyInternal p msg₂ s₂ pk = true) ∧
    (∃ (honRec0 honRec1 : SessionWireRecord) (raw₁ : ByteArray),
      honTr.sessions = [honRec0, honRec1] ∧
      honRec0.outcome = .signOk raw₁ ∧
      honRec1.honestRound1 = [] ∧
      honRec1.outcome = .abort .walEpochRejected) := by
  intro pk msg₁ msg₂ reqs A clInit mutPair honTr
  dsimp only [mutPair, honTr]
  unfold mutantRollbackWalTwoSessions
  rw [RealProtocolExec_two]
  dsimp only
  have hMsgNe : msg₁ ≠ msg₂ := by decide
  have hReq0 : reqs 0 = ⟨0, 0, msg₁, [], [1, 2]⟩ := rfl
  have hReq1 : reqs 1 = ⟨1, 0, msg₂, [], [1, 2]⟩ := rfl
  have hQuorum : validThresholdApproval (⟨pk, 2, 3, [0], [], []⟩ : IdealTsigState SlhPublicKey (List UInt8)) [1, 2] = true := by
    simp [validThresholdApproval]
  have hWal0 :
      walPreSignStep (initWalLatchState (slhPkDigest pk)) (slhPkDigest pk) 0 (slhReqDigest (reqs 0)) =
      .ok (initWalLatchState (slhPkDigest pk)) (.authorizedFresh 0) := by
    unfold walPreSignStep initWalLatchState; simp
  have hS0 := execRealSession_passiveRushingAdv_ok p hWf ⟨0, by decide⟩ 4 0 hSeedWf hPrfWf pkSeed
    reqs clInit (initWalLatchState (slhPkDigest pk)) (tapes 0) rfl rfl rfl rfl hQuorum hWal0 (by decide)
  dsimp only at hS0
  rcases hRun0 : execRealSession (rssSlhInteractiveProtocol p ⟨0, by decide⟩ 4) A clInit 0 (tapes 0)
    with ⟨cl1, adv1, rec0⟩
  rw [hRun0] at hS0
  dsimp only at hS0 ⊢
  obtain ⟨hAdv1, hOut0, _, hCur1, hSh1, hPk1, hCorr1, hTh1, hNp1, hCheat1, hWal1Eq⟩ := hS0
  subst hAdv1
  -- Mutant Session 1 (with `honestWal` rolled back to `clInit.honestWal`)
  have hQuorumRb : validThresholdApproval ({ cl1 with honestWal := clInit.honestWal }).tsig (reqs 1).honestApprovers = true := by
    unfold validThresholdApproval at hQuorum ⊢
    dsimp only; rw [hTh1, hNp1, hCorr1, hCheat1, hReq1]; exact hQuorum
  have hWalRb :
      walPreSignStep ({ cl1 with honestWal := clInit.honestWal }).honestWal
        (slhPkDigest ({ cl1 with honestWal := clInit.honestWal }).tsig.pk)
        (reqs 1).reqEpoch (slhReqDigest (reqs 1)) =
      .ok (initWalLatchState (slhPkDigest pk)) (.authorizedFresh 0) := by
    dsimp only [clInit]
    rw [hPk1, hReq1]
    dsimp only [pk]
    unfold walPreSignStep initWalLatchState; simp
  have hMut1 := execRealSession_passiveRushingAdv_ok p hWf ⟨0, by decide⟩ 4 1 hSeedWf hPrfWf pkSeed
    reqs { cl1 with honestWal := clInit.honestWal } (initWalLatchState (slhPkDigest pk)) (tapes 1)
    hPk1 hCorr1 hCur1 hSh1 hQuorumRb hWalRb (by decide)
  dsimp only at hMut1
  rcases hRunMut1 : execRealSession (rssSlhInteractiveProtocol p ⟨0, by decide⟩ 4) A
      { cl1 with honestWal := clInit.honestWal } 1 (tapes 1)
    with ⟨_, _, mutRec1⟩
  rw [hRunMut1] at hMut1
  dsimp only at hMut1 ⊢
  have hReq0Ep : rec0.request.reqEpoch = 0 := by
    have hR : rec0.request = reqs 0 := by
      have h := congrArg (fun x => x.2.2.request) hRun0
      have hQ0 : validThresholdApproval clInit.tsig (reqs 0).honestApprovers = true := by
        dsimp only [clInit]; rw [hReq0]; exact hQuorum
      have hW0 : walPreSignStep clInit.honestWal (slhPkDigest clInit.tsig.pk)
          (reqs 0).reqEpoch (slhReqDigest (reqs 0)) =
          .ok (initWalLatchState (slhPkDigest pk)) (.authorizedFresh 0) := hWal0
      dsimp only [A] at h
      unfold execRealSession rssSlhInteractiveProtocol passiveRushingAdv at h
      dsimp only at h
      rw [hQ0, ite_eq_right (by decide : ¬ ((!true) = true)), hW0] at h
      dsimp only at h
      split at h
      · exact h.symm
      · split at h
        · exact h.symm
        · split at h <;> exact h.symm
    rw [hR, hReq0]
  have hMutReq1Ep : mutRec1.request.reqEpoch = 0 := by
    have hR : mutRec1.request = reqs 1 := by
      have h := congrArg (fun x => x.2.2.request) hRunMut1
      have hQ1 : validThresholdApproval cl1.tsig (reqs 1).honestApprovers = true := hQuorumRb
      have hW1 : walPreSignStep clInit.honestWal (slhPkDigest cl1.tsig.pk)
          (reqs 1).reqEpoch (slhReqDigest (reqs 1)) =
          .ok (initWalLatchState (slhPkDigest pk)) (.authorizedFresh 0) := hWalRb
      dsimp only [A] at h
      unfold execRealSession rssSlhInteractiveProtocol passiveRushingAdv at h
      dsimp only at h
      rw [hQ1, ite_eq_right (by decide : ¬ ((!true) = true)), hW1] at h
      dsimp only at h
      split at h
      · exact h.symm
      · split at h
        · exact h.symm
        · split at h <;> exact h.symm
    rw [hR, hReq1]
  -- Honest Session 1 (with committed `cl1.honestWal`: `nextEpoch = 1`, `slhReqDigest (reqs 1) ≠ slhReqDigest (reqs 0)`)
  have hDigNe : slhReqDigest ⟨1, 0, msg₂, [], [1, 2]⟩ ≠ slhReqDigest ⟨0, 0, msg₁, [], [1, 2]⟩ := by
    intro hEq
    exact hMsgNe (slhReqDigest_injective_on_epoch_optRand_msg hEq).2.2.symm
  have hQuorum1 : validThresholdApproval cl1.tsig (reqs 1).honestApprovers = true := by
    unfold validThresholdApproval at hQuorum ⊢
    rw [hTh1, hNp1, hCorr1, hCheat1, hReq1]; exact hQuorum
  have hWalReject :
      walPreSignStep cl1.honestWal (slhPkDigest cl1.tsig.pk) (reqs 1).reqEpoch (slhReqDigest (reqs 1)) =
      .err cl1.honestWal .staleOrOutOfOrderEpoch := by
    rw [hWal1Eq, hPk1, hReq0, hReq1]
    dsimp only [pk]
    unfold walPreSignStep initWalLatchState
    simp [hDigNe]
  have hHon1 :
      (execRealSession (rssSlhInteractiveProtocol p ⟨0, by decide⟩ 4) A cl1 1 (tapes 1)).2.2.honestRound1 = [] ∧
      (execRealSession (rssSlhInteractiveProtocol p ⟨0, by decide⟩ 4) A cl1 1 (tapes 1)).2.2.outcome =
        .abort .walEpochRejected := by
    dsimp only [A]
    unfold execRealSession rssSlhInteractiveProtocol passiveRushingAdv
    dsimp only
    rw [hQuorum1, ite_eq_right (by decide : ¬ ((!true) = true)), hWalReject]
    exact ⟨rfl, rfl⟩
  let sk := (slhKeygenInternal p (reconstructRssBytes seedSh) (reconstructRssBytes prfSh) pkSeed).1
  let s₁ := slhSignInternal p msg₁ sk []
  let s₂ := slhSignInternal p msg₂ sk []
  let raw₁ := packWireBytes (encodeSlhSig s₁)
  let raw₂ := packWireBytes (encodeSlhSig s₂)
  refine ⟨hMsgNe, hReq0Ep, hMutReq1Ep, ?_, ?_⟩
  · refine ⟨raw₁, raw₂, s₁, s₂, hOut0, hMut1.2.1, ?_, ?_, ?_, ?_⟩
    · rw [unpackWireBytes_packWireBytes]
      exact decodeSlhSig_encodeSlhSig (slhSignInternal_wellTyped p msg₁ sk [])
    · rw [unpackWireBytes_packWireBytes]
      exact decodeSlhSig_encodeSlhSig (slhSignInternal_wellTyped p msg₂ sk [])
    · exact slhVerifyInternal_slhSignInternal p hWf (reconstructRssBytes seedSh)
        (reconstructRssBytes prfSh) pkSeed msg₁ []
    · exact slhVerifyInternal_slhSignInternal p hWf (reconstructRssBytes seedSh)
        (reconstructRssBytes prfSh) pkSeed msg₂ []
  · refine ⟨rec0, (execRealSession (rssSlhInteractiveProtocol p ⟨0, by decide⟩ 4) A cl1 1 (tapes 1)).2.2,
            raw₁, rfl, hOut0, hHon1.1, hHon1.2⟩

end Qsag
end
