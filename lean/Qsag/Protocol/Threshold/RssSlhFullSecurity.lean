module
/-
# Qsag.Protocol.Threshold.RssSlhFullSecurity — Multi-Session Simulation of the RSS SLH-DSA Cluster Shell

Constructive Lean 4.35 simulation and forgery-transfer results for a three-round SLH-DSA
cluster shell over `Qsag.InteractiveUcEngine`. The model boundary below specifies which
transcripts, resources, and implementation refinements these theorems cover:

1. **Three-Round Protocol (`rssSlhInteractiveProtocol`) & `sk`-Free UC Simulator (`Sim_RssSlh`)**:
   - **Round 1 (coin commitments)**: every party commits with `SHAKE256` to a 128-bit coin share
     under a 64-bit blind, over an injectively length-framed preimage binding the public key, the
     request (session id, epoch, message, hedge), the monotonic `maskSessionCursor` and the party
     id (`round1NonceCommit_binding_or_collision`, `slhPkDigest_binding_or_collision`,
     `slhReqDigest_injective_on_epoch_optRand_msg`; `0` `UInt8.ofNat` truncation).
   - **Round 2**: honest parties broadcast one 64-way bitsliced Keccak `χ`-row share each
     (`rssChiLane0/1/2`), masked by fresh session pads `(chiMaskA, chiMaskB)`, and no coin share.
     The rushing adversary sees these before sending one frame holding its coin opening and its
     `deg` raw `GF(2^128)` (`Tower128`) gate wires.
   - **Coin toss and Pre-Cut Consistency Barrier (`sharedCoinTossBarrier`)**: the corrupt opening
     is checked against its Round-1 commitment, and the `BBCGGI19` / `BDOZ` Horner equation
     `bbcggiWireAccumulator sentWires gamma == bbcggiWireAccumulator expectedWires gamma` is checked
     at `gamma = coinA ⊕ coinB ⊕ corruptCoin` strictly before Round 3; any mismatch aborts with
     `.round1CommitMismatch` / `.activeConsistencyFailed`, poisons `WalLatchState` and erases the
     secret key shares.
   - **Round 3 (`honestRound3` & `finalizeCutOpen`)**: honest parties evaluate the signature
     under the zero-sharing tape expanded from the three pairwise PRG seeds
     (`expandPairwiseSeedTape`), broadcast cut-opening shares (`verifyRssActiveOpenBytes`) and
     their coin openings (`honest_coin_openings_open_round1_commitments`), assemble and verify
     the NIST `FIPS 205` signature (`decodeSlhSig` / `slhVerifyInternal`), and atomically commit
     `WalLatchState` before `SignOk(sigBytes)`.
   - **Black-Box UC Simulator (`Sim_RssSlh`)**: receives **only** `pk : SlhPublicKey` and, upon
     `t`-quorum approval in `IdealTsig`, raw `idealSigBytes : ByteArray` (`0` access to `sk` or
     secret shares). It runs the coin toss as the honest parties do and simulates the masked
     messages from uniform pads.
2. **Cluster-Shell Theorems**:
   - `rss_slh_real_ideal_view_indistinguishable`: whole-transcript multi-round, multi-session
     distance (wire `ByteArray`s and `Abort(reason)` included) at most the root-hit probability
     of the joint coin; that probability is at most `Q_cuts * deg / 2^128` in the game where the
     honest commitments carry the zero coin, and the theorem carries the difference between the
     two games as the explicit term `advCoinHide`, next to the tape-generator term `advPrf`.
   - `rss_slh_interactive_euf_cma_reduction`: constructive `0 Classical.choice` black-box reduction
     turning any rushing threshold adversary forging `(mStar, sigStar)` outside `IdealTsig.approvedMsgs`
     into an explicit witness of `ActiveConsistencySoundnessBreak` OR standalone NIST `FIPS 205` hash
     breaks (`Fips205ForsItsrBreak ∨ WotsChainSmTcrBreak ∨ XmssMerkleTcrBreak ∨ PrfMsgBreak`).
   - `threshold_slh_output_perfect_quorum_privacy`: the output of any valid 2-of-3 RSS or
     `t`-of-`n` Shamir quorum/sharing equals standalone single-signer `slhSignInternal`.
   - `#tooth` mutation refusals: `tooth_skipping_pre_cut_barrier_leaks_key_bit`,
     `tooth_reusing_session_mask_tape_breaks_simulation`,
     `tooth_wal_rollback_enables_stateful_double_sign`,
     `tooth_corrupt_coin_opening_must_match_commitment`,
     `tooth_known_challenge_admits_nonzero_deviation`.
3. **Shell-to-Hash-Game Transfer (`rss_slh_uc_forgery_to_hash_game`, `rss_slh_fresh_enrollment_euf_cma_bound`)**:
   composes the theorems above without an abstract unforgeability premise. On every uniform
   multi-session tape on which a forger wins against `RealProtocolExec`, either the tape is a
   root hit of the joint coin (`multiSessionBadHit true`) or the real transcript equals the ideal
   transcript and yields a concrete `Fips205HashGameBreak`. The forgery bound is
   `Pr[ideal forgery] + Q_s * deg / 2^128 + advCoinHide`. The ideal transcript depends on the
   signing key only through the oracle answers of sessions that reached Round 3
   (`IdealFunctionalityExec_oracle_congr`).
4. **Horner tag as a tag scheme (`hornerTagScheme`, `rss_active_tag_forgery_count_le`,
   `rss_active_malicious_threshold_sig_hedged_bound`)**: bounds by `deg / 2^128` the forgery term
   of `Qsag.ThresholdMpc.active_malicious_threshold_sig_abort_or_exact_hedged_dist`.

Model boundary.
* The protocol proved here is a three-round shell around the honest pair. In a 2-of-3 replicated
  sharing the two honest parties jointly hold all three shares; `honestRound3` computes the whole
  signature from their views (`rssQuorumSlhSignBytes`) and re-shares it at the cut. The corrupt
  party contributes no share-dependent message to the output.
* The gate evaluation inside `rssQuorumSlhSignBytes` runs under an arbitrary zero-sharing tape
  expanded from the session's pairwise PRG seeds, but its gate messages are not on the modelled
  wire. The Round-2 honest message is still one 64-bit `χ` lane computed from the first eight
  bytes of each share and masked by a pad that is never used again; no later step consumes it.
  The full gate transcript of the signature computation is not modelled.
* The corrupt Round-2 frame carries a private `deg`-gate stream. The barrier recomputes it
  from the corrupt party's replicated share windows held by the honest vault, checks its
  length, and compares Horner accumulators. This replaces the public-hash wire check, but
  does not yet identify that stream with every gate of the production signing circuit.
* Coin toss. The challenge is `coinA ⊕ coinB ⊕ corruptCoin` read directly as a `GF(2^128)` point.
  The production engine commits with `cSHAKE256` to 32-byte shares bound to the wave transcript
  digest, hashes the XOR of the opened shares, and expands evaluation points from that hash;
  those hashing steps are random-oracle steps and are not modelled. The corrupt party opens its
  share in the same Round-2 frame as its wires, before the honest shares are opened in Round 3.
  The honest Round-1 commitments are deterministic `SHAKE256` values of the honest coin shares;
  nothing in this file proves that they hide those shares. The counted `deg / 2^128` bound is
  proved in the game where they carry the zero coin, and the hop to the protocol is the explicit
  term `advCoinHide` (an adversary that ignores honest Round-1 messages has `advCoinHide = 0`, as
  used in `tooth_skipping_pre_cut_barrier_leaks_key_bit`).
* Parsing requires a 24-byte opening and exactly `deg > 0` field elements, and consumes the
  complete frame.
* Both execution engines record approval before releasing Round-3 openings, including when
  `finalizeCutOpen` subsequently fails. `slhForgeryWins` retains its transcript-based freshness
  predicate over sessions that reached Round 3.
* Hash-game witnesses are stated over `Qsag.Fips205` (`SHAKE256` collisions, chain preimages, FORS
  coverage). They are not instances of the `Qsag.HypertreeEufCma` witness types, which belong to
  the tweakable-hash WOTS+C hypertree scheme; the weld for that scheme is
  `uc_emulation_forgery_to_hypertree_hash_game` in `Qsag.InteractiveUcEngine`.
-/

public import Qsag.Math.Constructive
public import Qsag.Math.Goldilocks
public import Qsag.Math.BinaryTower
public import Qsag.Oracle.Keccak
public import Qsag.Protocol.Signing.Fips205
public import Qsag.Oracle.UcGames
public import Qsag.Protocol.Threshold.ThresholdApproval
public import Qsag.Protocol.Threshold.IdealTsig
public import Qsag.Protocol.Threshold.ThresholdMpc
public import Qsag.Protocol.Threshold.MaliciousSecurity
public import Qsag.Exec.InteractiveUcEngine

import all Qsag.Oracle.UcGames
import all Qsag.Protocol.Signing.Fips205
import all Qsag.Protocol.Threshold.ThresholdMpc
import all Qsag.Protocol.Threshold.MaliciousSecurity
import all Qsag.Exec.InteractiveUcEngine

import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt8.instLawfulOrderOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd BitVec.instTransOrd
set_option autoImplicit false
set_option maxHeartbeats 2000000

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

/-- The root count is invariant under translating the challenge by a fixed `k`: a uniform coin
    share XORed with any value fixed beforehand is still a uniform challenge. -/
theorem tower128_shifted_roots_finSum_le (deg : Nat) (deltas : List Tower128) (k : BitVec 128)
    (hLen : deltas.length ≤ deg)
    (hNonzero : ∃ d ∈ deltas, d ≠ towerZero 7) :
    finSum (2 ^ 128)
      (fun r => if batchDeviationPoly deltas (unpackTower 7 (BitVec.ofFin r ^^^ k)) == towerZero 7
                then 1 else 0) ≤ deg := by
  refine Nat.le_trans (Nat.le_of_eq ?_) (tower128_roots_finSum_le deg deltas hLen hNonzero)
  refine Eq.trans ?_ (finSum_equiv_eq (finBitVecXorEquiv 128 k) _)
  exact finSum_congr (fun _ => rfl)

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

/-- The challenge index only fills the `gammaBits` field. -/
private theorem decodeRssSessionTape_gamma (L : Nat) (padIdx : Fin (rssPadSessionCard L))
    (gIdx : Fin (2 ^ 128)) :
    decodeRssSessionTape L padIdx gIdx =
      { decodeRssSessionTape L padIdx ⟨0, Nat.two_pow_pos 128⟩ with gammaBits := BitVec.ofFin gIdx } :=
  rfl

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
    (suffix : List UInt8) (hLen : (unpackWireBytes wire).length = 24 + 16 * deg)
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

/-- Canonical injective multi-frame preimage for Round-1 coin commitments (`0` `UInt8.ofNat`
    truncation). `nonceBytes` is the 24-byte opening `coinOpeningBytes coin blind`. -/
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

/-- Domain-separated Round-1 `SHAKE256` coin commitment (`32` bytes) over injective `encodeMultiFrame`:
    `commit(pk ‖ session id ‖ epoch ‖ cursor ‖ party ‖ message ‖ hedge ‖ coin ‖ blind)`. -/
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

/-! ### Private per-gate `χ` stream of the corrupt party

The `deg` gate wires the corrupt party owes in Round 2 are its own `χ` lane words, one per gate,
computed from its replicated share view. They are never derived from public transcript hashes.
In a 2-of-3 replicated sharing the two honest parties jointly hold the corrupt party's two
shares, so they recompute this stream from their vault (`corruptViewOfVault`); the simulator
receives the corrupt party's own view (`corruptRssView`), which is what the adversary holds. -/

abbrev PrivateChiStream (M : Nat) := Fin M → Tower128

def privateChiGateStream (M pid : Nat) (inputs : Fin M → RssPartyKeyShare)
    (messages : Fin M → List UInt8) : PrivateChiStream M :=
  fun i => unpackTower 7 ((computeHonestChiWord pid (inputs i) (messages i)).zeroExtend 128)

def privateChiStreamList {M : Nat} (wires : PrivateChiStream M) : List Tower128 :=
  (List.finRange M).map wires

/-- Gate `i` reads the 8-byte window `[8 i, 8 i + 8)` of every share component. -/
def gateShareWindow (sh : RssPartyKeyShare) (i : Nat) : RssPartyKeyShare :=
  ⟨sh.seedFirst.drop (8 * i), sh.seedSecond.drop (8 * i),
   sh.prfFirst.drop (8 * i), sh.prfSecond.drop (8 * i)⟩

/-- Replicated share view dealt to the corrupt party `cIdx` (shares `cIdx` and `cIdx + 1`). -/
def corruptRssView (cIdx : Fin 3) (seedSh prfSh : RssByteShares) : RssPartyKeyShare :=
  if cIdx.val == 0 then ⟨seedSh.b0, seedSh.b1, prfSh.b0, prfSh.b1⟩
  else if cIdx.val == 1 then ⟨seedSh.b1, seedSh.b2, prfSh.b1, prfSh.b2⟩
  else ⟨seedSh.b2, seedSh.b0, prfSh.b2, prfSh.b0⟩

/-- The corrupt party's view as the honest pair reads it off its own vault entries: the second
    honest party's second share and the first honest party's first share. `none` once the vault
    has been erased. -/
def corruptViewOfVault (cIdx : Fin 3) (shares : Nat → Option RssPartyKeyShare) :
    Option RssPartyKeyShare :=
  match shares (honestPairForCorrupt cIdx).1, shares (honestPairForCorrupt cIdx).2.1 with
  | some shA, some shB => some ⟨shB.seedSecond, shA.seedFirst, shB.prfSecond, shA.prfFirst⟩
  | _, _ => none

theorem corruptViewOfVault_deal (cIdx : Fin 3) (seedSh prfSh : RssByteShares) :
    corruptViewOfVault cIdx (dealHonestRssVault cIdx seedSh prfSh) =
      some (corruptRssView cIdx seedSh prfSh) := by
  rcases cIdx with ⟨_ | _ | _ | n, hv⟩
  · rfl
  · rfl
  · rfl
  · exact False.elim (Nat.not_lt_zero n (Nat.lt_of_add_lt_add_right hv))

/-- Private stream the barrier holds the corrupt party to: gate `i` is the corrupt party's `χ`
    lane word on window `i` of its share view and of the message. Empty when no view is
    available, which the barrier's length test then rejects for every `deg > 0` frame. -/
def corruptExpectedChiStream (cIdx : Fin 3) (deg : Nat) (view : Option RssPartyKeyShare)
    (msg : List UInt8) : List Tower128 :=
  match view with
  | none => []
  | some sh =>
    privateChiStreamList (privateChiGateStream deg cIdx.val
      (fun i => gateShareWindow sh i.val) (fun i => msg.drop (8 * i.val)))

theorem corruptExpectedChiStream_length (cIdx : Fin 3) (deg : Nat) (sh : RssPartyKeyShare)
    (msg : List UInt8) : (corruptExpectedChiStream cIdx deg (some sh) msg).length = deg := by
  simp [corruptExpectedChiStream, privateChiStreamList]

/-- The barrier's wire test. The length is fixed by the private computation, not by the
    adversary's frame, and the two Horner accumulators must agree at the challenge. -/
def verifyPrivateChiWires (expected sent : List Tower128) (gamma : Tower128) : Bool :=
  decide (sent.length = expected.length) &&
    (bbcggiWireAccumulator sent gamma == bbcggiWireAccumulator expected gamma)

theorem verifyPrivateChiWires_self (ws : List Tower128) (gamma : Tower128) :
    verifyPrivateChiWires ws ws gamma = true := by
  simp [verifyPrivateChiWires]

/-- Gate `0` of the corrupt party's private stream. -/
def corruptExpectedChiWire0 (cIdx : Fin 3) (sh : RssPartyKeyShare) (msg : List UInt8) : Tower128 :=
  unpackTower 7 ((computeHonestChiWord cIdx.val (gateShareWindow sh 0) (msg.drop (8 * 0))).zeroExtend 128)

theorem corruptExpectedChiStream_one (cIdx : Fin 3) (sh : RssPartyKeyShare) (msg : List UInt8) :
    corruptExpectedChiStream cIdx 1 (some sh) msg = [corruptExpectedChiWire0 cIdx sh msg] := by
  rfl

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
  deriving DecidableEq, Repr

/-- Intermediate Round-2 state carried into the barrier. After `honestRound2`, `gammaBits` is the
    honest pair's joint coin share `coinA ⊕ coinB`; `sharedCoinTossBarrier` XORs in the corrupt
    opening, so the value `sharedPreCutBarrier` evaluates at is the joint coin of all three
    parties. `expectedWires` is the corrupt
    party's private `deg`-gate `χ` stream (`corruptExpectedChiStream`), fixed in Round 2 from
    share views and never sent. -/
structure RssRound2State where
  cursor       : Nat
  corrR1Commit : ByteArray
  gammaBits    : BitVec 128
  expectedWires : List Tower128
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

/-- Domain tag `"QSAG.RSS.PRG/v1"` (`15` ASCII bytes) of the pairwise zero-sharing PRG. -/
def rssPairwisePrgDomainTag : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2E, 0x52, 0x53, 0x53, 0x2E, 0x50, 0x52, 0x47, 0x2F, 0x76, 0x31]

/-- One 64-bit PRG word of pairwise seed `seed` at the gate coordinate `(i, j, k, l)` that
    `mkRssSlhMpcOracles` uses to index its zero-sharings: `SHAKE256` over an injective frame. -/
def pairwisePrgWord (seed : BitVec 64) (i j k l : Nat) : UInt64 :=
  (fixedBytesToBv 8 (shake256Xof 8 (encodeMultiFrame
    [rssPairwisePrgDomainTag, bvToFixedBytes 8 seed, leb128 i, leb128 j, leb128 k, leb128 l]))).toNat.toUInt64

/-- Zero-sharing tape of the gate evaluation, expanded from the three pairwise PRG seeds packed
    in `seeds` (low, middle and high 64 bits). Party `i` holds seeds `i` and `i + 1`, so the two
    honest parties jointly hold all three. The tape is an arbitrary function of the seeds as far
    as output correctness is concerned (`rss_threshold_sig_independent_of_quorum_and_sharing`
    holds for every tape); its pseudorandomness is not used by any theorem in this file. -/
def expandPairwiseSeedTape (seeds : BitVec 192) : Nat → Nat → Nat → Nat → RssPrfZeroSeeds :=
  fun i j k l =>
    ⟨pairwisePrgWord (seeds.extractLsb' 0 64) i j k l,
     pairwisePrgWord (seeds.extractLsb' 64 64) i j k l,
     pairwisePrgWord (seeds.extractLsb' 128 64) i j k l⟩

/-- The decoy game hides the challenge by committing to zero. -/
def committedCoin (commitCoins : Bool) (coin : BitVec 128) : BitVec 128 :=
  match commitCoins with
  | true => coin
  | false => 0#128

theorem committedCoin_true (coin : BitVec 128) : committedCoin true coin = coin := by rfl

/-- Opening of a coin commitment: 16-byte coin share followed by the 8-byte blind. -/
def coinOpeningBytes (coin : BitVec 128) (blind : BitVec 64) : List UInt8 :=
  bvToFixedBytes 16 coin ++ bvToFixedBytes 8 blind

theorem coinOpeningBytes_length (coin : BitVec 128) (blind : BitVec 64) :
    (coinOpeningBytes coin blind).length = 24 := by
  unfold coinOpeningBytes
  rw [List.length_append, bvToFixedBytes_length, bvToFixedBytes_length]

/-- Coin share read from the first 16 bytes of an opening. -/
def openingCoin (opening : List UInt8) : BitVec 128 :=
  fixedBytesToBv 16 (opening.take 16)

theorem openingCoin_coinOpeningBytes (coin : BitVec 128) (blind : BitVec 64) :
    openingCoin (coinOpeningBytes coin blind) = coin := by
  unfold openingCoin coinOpeningBytes
  rw [List.take_left' (bvToFixedBytes_length 16 coin)]
  exact fixedBytesToBv_bvToFixedBytes 16 coin

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

/-- The two honest parties' Round-3 coin openings, appended after their cut-opening messages. -/
def honestCoinOpeningMsgs (cIdx : Fin 3) (coinA : BitVec 128) (blindA : BitVec 64)
    (coinB : BitVec 128) (blindB : BitVec 64) : List (Nat × ByteArray) :=
  [((honestPairForCorrupt cIdx).1, packWireBytes (coinOpeningBytes coinA blindA)),
   ((honestPairForCorrupt cIdx).2.1, packWireBytes (coinOpeningBytes coinB blindB))]

/-- Coin share the corrupt party opens in Round 2 (the zero share if its frame does not parse;
    such a frame is rejected by `sharedPreCutBarrier` anyway). -/
def corruptOpenedCoin (cIdx : Fin 3) (deg : Nat) (corrR2 : List (Nat × ByteArray)) : BitVec 128 :=
  match corrR2.find? (fun pr => pr.1 == cIdx.val) with
  | none => 0#128
  | some (_, cWire2) =>
    match parseCorruptRound2Wire deg cWire2 with
    | none => 0#128
    | some (opening, _) => openingCoin opening

/-- Shared Round-1 commitment check used identically by `rssSlhInteractiveProtocol` and `Sim_RssSlh`. -/
def sharedVerifyRound1 (cIdx : Fin 3) (r1St : RssRound1State)
    (corrR1 : List (Nat × ByteArray)) : PSum (AbortReason × Bool) RssRound2State :=
  match corrR1.find? (fun pr => pr.1 == cIdx.val) with
  | none => .inl (.round1CommitMismatch cIdx.val, false)
  | some (_, cWire) =>
    if (unpackWireBytes cWire).length != 32 then .inl (.round1CommitMismatch cIdx.val, false)
    else .inr { cursor := r1St.cursor, corrR1Commit := cWire, gammaBits := 0#128,
                expectedWires := [] }

/-- **Mandatory Pre-Cut Consistency Barrier (`sharedPreCutBarrier`)**:
    Verifies Round-1 commitment binding and `verifyPrivateChiWires` against the private stream
    `r2St.expectedWires`: the frame must carry exactly as many wires as the private computation
    has gates, and the `BBCGGI19` / `BDOZ` Horner accumulators over raw `GF(2^128)` (`Tower128`)
    gate wires must agree at the challenge, strictly before Round-3 cut openings can run. -/
