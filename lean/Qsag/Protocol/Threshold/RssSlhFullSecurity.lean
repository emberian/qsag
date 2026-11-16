module
public import Qsag.Spec.Sessions
/-
# Qsag.Protocol.Threshold.RssSlhFullSecurity — Engine-Independent Core of the RSS SLH-DSA Cluster Shell

Wire formats, counting lemmas, hash-game extractors and the consistency-tag bound used by the
three-round RSS SLH-DSA cluster shell. Nothing here refers to the interactive UC engine; the
protocol (`rssSlhInteractiveProtocol`), its simulator and the transcript theorems
(`rss_slh_real_ideal_view_indistinguishable`, `rss_slh_interactive_euf_cma_reduction`,
`rss_slh_uc_forgery_to_hash_game`, `threshold_slh_output_perfect_quorum_privacy`) and their
mutation teeth are in `Qsag.Exec.RssSlhFullSecurityUc`, whose header states the model boundary.

1. **Byte/`BitVec` bijections and finite sums**: `bvToFixedBytes` / `fixedBytesToBv`, the product
   index `pairFin` with `splitFinLeft` / `splitFinRight`, the fibered tape bijection
   `depProdFinEquiv`, the Fubini identity `qsum_prod_eq`, and the `GF(2^128)` root count
   `tower128_roots_qsum_le` (at most `deg` of the `2^128` challenges cancel a nonzero deviation
   list of length at most `deg`).
2. **`FIPS 205` wire codec and shares**: `encodeSlhSig` / `decodeSlhSig` round trips
   (`decodeSlhSig_encodeSlhSig`, `slhSignInternal_wellTyped`), replicated 2-of-3 key shares
   (`RssPartyKeyShare`), per-session tapes (`RssSlhSessionTape`) and their
   tape bijections, the private per-gate `χ` stream check (`verifyPrivateChiWires`) and the
   Round-3 cut-opening check (`checkRound3ActiveOpen`, `checkRound3ActiveOpen_output`).
3. **Hash-game witness types and extractors over `Qsag.Fips205`**: `XmssMerkleTcrBreak`,
   `WotsChainSmTcrBreak`, `PrfMsgBreak`, and the Merkle-walk, XMSS-layer, hypertree and FORS
   splitters that turn a verifying forged path into a `SHAKE256` collision or a WOTS chain break.
4. **Horner tag as a tag scheme** (`hornerTagScheme`, `rss_active_tag_forgery_count_le`,
   `rss_active_malicious_threshold_sig_hedged_bound`): bounds by `deg / 2^128` the forgery term
   of `active_malicious_threshold_sig_abort_or_exact_hedged_dist`
   (`Qsag.Protocol.Threshold.ThresholdMpc`).
5. **Production coin framing** (`productionCoinCommit`, `productionCoinDerive`,
   `productionCoinCommit_binding_or_collision`, `production_coin_ro_query_hybrid_bound`) and the
   counts for the private-stream test (`verifyPrivateChiWires_any_changed_gate_count`).
-/

public import Qsag.Tactic.Prelude
public import Qsag.Math.Goldilocks
public import Qsag.Math.Gf2Pow128
public import Qsag.Oracle.Keccak
public import Qsag.Protocol.Signing.Fips205
public import Qsag.Protocol.Aggregation.UcGames
public import Qsag.Protocol.Threshold.ThresholdApproval
public import Qsag.Protocol.Threshold.IdealTsig
public import Qsag.Protocol.Threshold.ThresholdMpc
public import Qsag.Protocol.Threshold.MaliciousSecurity


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

theorem xorByteStream_length : ∀ {xs ys : List UInt8},
    xs.length = ys.length → (xorByteStream xs ys).length = xs.length
  | [], [], _ => rfl
  | _ :: xs, _ :: ys, h => by
    simp only [xorByteStream, List.zipWith_cons_cons, List.length_cons]
    exact congrArg Nat.succ (xorByteStream_length (Nat.succ.inj h))

theorem uint8_xor_comm (a b : UInt8) : (a ^^^ b) = (b ^^^ a) := by
  apply UInt8.eq_of_toBitVec_eq
  exact BitVec.xor_comm a.toBitVec b.toBitVec

theorem uint8_xor_assoc (a b c : UInt8) : ((a ^^^ b) ^^^ c) = (a ^^^ (b ^^^ c)) := by
  apply UInt8.eq_of_toBitVec_eq
  simp only [UInt8.toBitVec_xor, BitVec.xor_assoc]

theorem uint8_xor_self (a : UInt8) : (a ^^^ a) = 0 := by
  apply UInt8.eq_of_toBitVec_eq
  simp

theorem uint8_xor_zero (a : UInt8) : (a ^^^ 0) = a := by
  apply UInt8.eq_of_toBitVec_eq
  simp

theorem uint8_zero_xor (a : UInt8) : ((0 : UInt8) ^^^ a) = a := by
  rw [uint8_xor_comm, uint8_xor_zero]

theorem xorByteStream_comm : ∀ {xs ys : List UInt8},
    xs.length = ys.length → xorByteStream xs ys = xorByteStream ys xs
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [xorByteStream, List.zipWith_cons_cons, List.cons.injEq]
    exact ⟨uint8_xor_comm x y, xorByteStream_comm (Nat.succ.inj h)⟩

theorem xorByteStream_assoc : ∀ {xs ys zs : List UInt8},
    xs.length = ys.length → ys.length = zs.length →
    xorByteStream (xorByteStream xs ys) zs = xorByteStream xs (xorByteStream ys zs)
  | [], [], [], _, _ => rfl
  | x :: xs, y :: ys, z :: zs, h1, h2 => by
    simp only [xorByteStream, List.zipWith_cons_cons, List.cons.injEq]
    exact ⟨uint8_xor_assoc x y z, xorByteStream_assoc (Nat.succ.inj h1) (Nat.succ.inj h2)⟩

theorem xorByteStream_self : ∀ (xs : List UInt8),
    xorByteStream xs xs = List.replicate xs.length 0
  | [] => rfl
  | x :: xs => by
    simp only [xorByteStream, List.zipWith_cons_cons, List.length_cons, List.replicate_succ, List.cons.injEq]
    exact ⟨uint8_xor_self x, xorByteStream_self xs⟩

theorem xorByteStream_replicate_zero : ∀ (xs : List UInt8),
    xorByteStream xs (List.replicate xs.length 0) = xs
  | [] => rfl
  | x :: xs => by
    simp only [xorByteStream, List.length_cons, List.replicate_succ, List.zipWith_cons_cons, List.cons.injEq]
    exact ⟨uint8_xor_zero x, xorByteStream_replicate_zero xs⟩

theorem xorByteStream_cancel_right {xs m : List UInt8} (hLen : xs.length = m.length) :
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

theorem bvToFixedBytes_length : ∀ (L : Nat) (bv : BitVec (8 * L)),
    (bvToFixedBytes L bv).length = L
  | 0, _ => rfl
  | L + 1, bv => by
    simp only [bvToFixedBytes, List.length_cons, bvToFixedBytes_length L]

theorem bvToFixedBytes_xor : ∀ (L : Nat) (u v : BitVec (8 * L)),
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

theorem bvToFixedBytes_fixedBytesToBv : ∀ (L : Nat) (bs : List UInt8),
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

theorem finBitVecXorEquiv_toFun (W : Nat) (delta : BitVec W) (i : Fin (2 ^ W)) :
    (finBitVecXorEquiv W delta).toFun i = (BitVec.ofFin i ^^^ delta).toFin := by
  rfl

/-- Constructive product index `(a, b) ↦ a * B + b` in `Fin (A * B)`. -/
@[expose] def pairFin {A B : Nat} (a : Fin A) (b : Fin B) : Fin (A * B) :=
  ⟨a.val * B + b.val, by
    have h1 : a.val + 1 ≤ A := a.isLt
    have h2 : (a.val + 1) * B ≤ A * B := Nat.mul_le_mul_right B h1
    rw [Nat.add_mul, Nat.one_mul] at h2
    have h3 : b.val < B := b.isLt
    omega⟩

@[expose] def splitFinLeft {A B : Nat} (hB : 0 < B) (x : Fin (A * B)) : Fin A :=
  ⟨x.val / B, (Nat.div_lt_iff_lt_mul hB).mpr x.isLt⟩

@[expose] def splitFinRight {A B : Nat} (hB : 0 < B) (x : Fin (A * B)) : Fin B :=
  ⟨x.val % B, Nat.mod_lt x.val hB⟩

theorem pairFin_splitFin {A B : Nat} (hB : 0 < B) (x : Fin (A * B)) :
    pairFin (splitFinLeft hB x) (splitFinRight hB x) = x := by
  apply Fin.ext
  dsimp [pairFin, splitFinLeft, splitFinRight]
  have h := Nat.div_add_mod x.val B
  rw [Nat.mul_comm B (x.val / B)] at h
  exact h

theorem splitFinLeft_pairFin {A B : Nat} (hB : 0 < B) (a : Fin A) (b : Fin B) :
    splitFinLeft hB (pairFin a b) = a := by
  apply Fin.ext
  dsimp [splitFinLeft, pairFin]
  rw [Nat.mul_comm a.val B, Nat.mul_add_div hB, Nat.div_eq_of_lt b.isLt, Nat.add_zero]

theorem splitFinRight_pairFin {A B : Nat} (_hB : 0 < B) (a : Fin A) (b : Fin B) :
    splitFinRight _hB (pairFin a b) = b := by
  apply Fin.ext
  dsimp [splitFinRight, pairFin]
  rw [Nat.mul_comm a.val B, Nat.mul_add_mod, Nat.mod_eq_of_lt b.isLt]

/-- Dependent (fibered) product bijection on `Fin (A * B)`:
    maps `a ↦ bijA a` and `b ↦ (bijB a) b`, enabling adaptive multi-session pad bijections
    where later session shifts depend on the entire transcript of earlier sessions! -/
@[expose] def depProdFinEquiv {A B : Nat} (hB : 0 < B)
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

theorem depProdFinEquiv_toFun {A B : Nat} (hB : 0 < B)
    (bijA : SimpleEquiv (Fin A) (Fin A))
    (bijB : Fin A → SimpleEquiv (Fin B) (Fin B)) (x : Fin (A * B)) :
    (depProdFinEquiv hB bijA bijB).toFun x =
      pairFin (bijA.toFun (splitFinLeft hB x))
        ((bijB (splitFinLeft hB x)).toFun (splitFinRight hB x)) := by
  rfl

theorem qsum_cast_eq {m n : Nat} (h : m = n) (f : Fin m → Nat) :
    qsum m f = qsum n (fun k => f ⟨k.val, h ▸ k.isLt⟩) := by
  subst h
  exact qsum_congr (fun _ => rfl)

theorem qsum_add_split : ∀ (m n : Nat) (f : Fin (m + n) → Nat),
    qsum (m + n) f =
      qsum m (fun i => f ⟨i.val, by omega⟩) +
      qsum n (fun j => f ⟨m + j.val, by omega⟩)
  | 0, n, f => by
    rw [qsum_cast_eq (Nat.zero_add n) f]
    simp only [qsum_zero, Nat.zero_add]
  | m + 1, n, f => by
    have hAssoc : m + 1 + n = (m + n) + 1 := by omega
    rw [qsum_cast_eq hAssoc f]
    conv => lhs; rw [qsum_succ]
    conv => rhs; rw [qsum_succ]
    dsimp only
    have ih := qsum_add_split m n (fun k => f ⟨k.val + 1, by omega⟩)
    have hLeftEq :
        qsum m (fun i => f ⟨i.val + 1, by omega⟩) =
        qsum m (fun i => f ⟨(⟨i.val, by omega⟩ : Fin (m + n)).val + 1, by omega⟩) :=
      qsum_congr (fun _ => rfl)
    have hShift :
        qsum n (fun j => f ⟨(m + j.val) + 1, by omega⟩) =
        qsum n (fun j => f ⟨m + 1 + j.val, by omega⟩) := by
      apply qsum_congr
      intro j
      congr 1
      exact Fin.ext (by dsimp; omega)
    rw [← hLeftEq] at ih
    rw [ih, hShift]
    omega

/-- Fubini factorization of `qsum (A * B)` over `Fin A × Fin B` (`0 Classical.choice`). -/
theorem qsum_prod_eq : ∀ (A B : Nat) (f : Fin (A * B) → Nat),
    qsum (A * B) f = qsum A (fun a => qsum B (fun b => f (pairFin a b)))
  | 0, B, f => by
    rw [qsum_cast_eq (Nat.zero_mul B) f]
    simp only [qsum_zero]
  | A + 1, B, f => by
    have hSplitEq : (A + 1) * B = B + A * B := by rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    rw [qsum_cast_eq hSplitEq f, qsum_add_split B (A * B)]
    conv => rhs; rw [qsum_succ]
    dsimp only
    have hHead :
        qsum B (fun i => f ⟨i.val, by omega⟩) =
        qsum B (fun b => f (pairFin ⟨0, Nat.zero_lt_succ A⟩ b)) := by
      apply qsum_congr
      intro b
      congr 1
      exact Fin.ext (by simp [pairFin])
    have hTail :
        qsum (A * B) (fun j => f ⟨B + j.val, by omega⟩) =
        qsum A (fun a => qsum B (fun b => f (pairFin ⟨a.val + 1, Nat.succ_lt_succ a.isLt⟩ b))) := by
      rw [qsum_prod_eq A B (fun j => f ⟨B + j.val, by omega⟩)]
      apply qsum_congr
      intro a
      apply qsum_congr
      intro b
      congr 1
      apply Fin.ext
      dsimp [pairFin]
      rw [Nat.add_mul, Nat.one_mul]
      omega
    rw [hHead, hTail]

theorem qsum_indicator_le_card : ∀ (n : Nat) (p : Fin n → Bool),
    qsum n (fun i => if p i then 1 else 0) ≤ n
  | 0, _ => by rw [qsum_zero]; exact Nat.le_refl 0
  | n + 1, p => by
    simp only [qsum_succ]
    have ih := qsum_indicator_le_card n (fun i => p ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    cases p ⟨0, Nat.zero_lt_succ n⟩ <;> simp <;> omega

def collectTrueFin : (n : Nat) → (Fin n → Bool) → List (Fin n)
  | 0, _ => []
  | n + 1, p =>
    let rest := (collectTrueFin n (fun i => p ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)).map
                  (fun i => (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (n + 1)))
    if p ⟨0, Nat.zero_lt_succ n⟩ then ⟨0, Nat.zero_lt_succ n⟩ :: rest else rest

theorem qsum_eq_collectTrueFin_length : ∀ (n : Nat) (p : Fin n → Bool),
    qsum n (fun i => if p i then 1 else 0) = (collectTrueFin n p).length
  | 0, _ => by rw [qsum_zero]; rfl
  | n + 1, p => by
    simp only [qsum_succ, collectTrueFin]
    have ih := qsum_eq_collectTrueFin_length n (fun i => p ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    cases p ⟨0, Nat.zero_lt_succ n⟩ <;> simp [ih] <;> omega

theorem nodup_map_injective {α β : Type} {f : α → β}
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

theorem collectTrueFin_nodup : ∀ (n : Nat) (p : Fin n → Bool),
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

theorem mem_collectTrueFin_true : ∀ (n : Nat) (p : Fin n → Bool) (x : Fin n),
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

/-- **Full-Field `Tower128` (`GF(2^128)`) Schwartz-Zippel Sum Bound (`tower128_roots_qsum_le`)**:
    Over the entire finite field `Fin (2 ^ 128) ≃ Tower128`, any batch `deltas` of `≤ deg`
    wire deviations with `∃ d ∈ deltas, d ≠ towerZero 7` vanishes on **at most `deg`** challenges
    out of `2 ^ 128` (`0 Classical.choice`, `0` enumeration blowup!). -/
theorem tower128_roots_qsum_le (deg : Nat) (deltas : List Tower128)
    (hLen : deltas.length ≤ deg)
    (hNonzero : ∃ d ∈ deltas, d ≠ towerZero 7) :
    qsum (2 ^ 128)
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
  have hCountEq : qsum (2 ^ 128) (fun r => if isRoot r then 1 else 0) = fieldRoots.length := by
    rw [qsum_eq_collectTrueFin_length]
    simp [fieldRoots, rawRoots]
  change qsum (2 ^ 128) (fun r => if isRoot r then 1 else 0) ≤ deg
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

/-! ## 2. Exact `FIPS 205` Wire Codec, Replicated Shares, Session Tapes & Barrier Checks -/

/-- Split a flat byte stream into `count` consecutive `chunkSize`-byte chunks. -/
def splitByteChunks (chunkSize : Nat) : Nat → List UInt8 → List (List UInt8)
  | 0, _ => []
  | count + 1, bs => bs.take chunkSize :: splitByteChunks chunkSize count (bs.drop chunkSize)

theorem splitByteChunks_length (c : Nat) :
    ∀ (k : Nat) (bs : List UInt8), (splitByteChunks c k bs).length = k
  | 0, _ => rfl
  | k + 1, bs => by simp [splitByteChunks, splitByteChunks_length c k]

theorem splitByteChunks_each_length {c : Nat} :
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

theorem splitByteChunks_flatten (c : Nat) :
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
def decodeSlhSig (p : Fips205Params) (raw : List UInt8) : Option SlhSignature :=
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
    rw [Fips205Params.sigBytes_def] at hRawLen
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
    rw [Fips205Params.sigBytes_def]
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
  refine ⟨by rw [fipsPrfMsg_eq]; exact shake256Xof_length p.n _, by simp [fipsForsSign_def], ?_, ?_, ?_⟩
  · intro f hf
    simp only [fipsForsSign_def, List.mem_map] at hf
    obtain ⟨j, _, rfl⟩ := hf
    refine ⟨fipsPrf_length _ _ _ _, fipsForsAuthPath_length_eq _ _ _ _ _ _ _ _, ?_⟩
    intro u hu
    have hAuthEach : ∀ (z ni li : Nat) (v : List UInt8),
        v ∈ fipsForsAuthPath p sk.skSeed sk.pkSeed split.2.1 split.2.2 z ni li → v.length = p.n := by
      intro z; induction z with
      | zero => intro _ _ _ hv; rw [fipsForsAuthPath_zero] at hv; cases hv
      | succ z ih =>
        intro ni li v hv
        have hNodeL : ∀ (zz m : Nat), (fipsForsNode p sk.skSeed sk.pkSeed split.2.1 split.2.2 zz m).length = p.n := by
          intro zz; cases zz <;> intro _ <;>
            first | simp [fipsForsNode_zero] | simp [fipsForsNode_succ]
        simp only [fipsForsAuthPath_succ] at hv
        split at hv <;>
        · rw [List.mem_append] at hv
          rcases hv with hL | hR
          · exact ih _ _ v hL
          · rw [List.mem_singleton] at hR; subst hR; exact hNodeL _ _
    exact hAuthEach _ _ _ u hu
  · exact fipsHtSignAux_length_eq p sk.skSeed sk.pkSeed p.d 0 _ _ _
  · have hHtMem : ∀ (rem layer it il : Nat) (cm : List UInt8) (x : FipsXmssSig),
        x ∈ fipsHtSignAux p sk.skSeed sk.pkSeed layer it il cm rem →
        x.wotsSig.length = p.ell ∧ (∀ w ∈ x.wotsSig, w.length = p.n) ∧
        x.authPath.length = p.hp ∧ (∀ u ∈ x.authPath, u.length = p.n) := by
      intro rem; induction rem with
      | zero => intro _ _ _ _ _ hx; rw [fipsHtSignAux_zero] at hx; cases hx
      | succ rem ih =>
        intro layer it il cm x hx
        simp only [fipsHtSignAux_succ, List.mem_cons] at hx
        rcases hx with rfl | hTl
        · simp only [fipsXmssSign_def]
          refine ⟨by simp [fipsWotsSign_def], ?_, fipsXmssAuthPath_length_eq _ _ _ _ _ _ _ _, ?_⟩
          · intro w hw
            simp only [fipsWotsSign_def, List.mem_map] at hw
            obtain ⟨i, _, rfl⟩ := hw
            exact fipsChain_length _ _ _ _ _ _ _ _ _ (fipsPrf_length _ _ _ _)
          · have hXAuthEach : ∀ (z ni li : Nat) (v : List UInt8),
                v ∈ fipsXmssAuthPath p sk.skSeed sk.pkSeed layer it z ni li → v.length = p.n := by
              intro z; induction z with
              | zero => intro _ _ _ hv; rw [fipsXmssAuthPath_zero] at hv; cases hv
              | succ z ihz =>
                intro ni li v hv
                have hNL : ∀ (zz m : Nat), (fipsXmssNode p sk.skSeed sk.pkSeed layer it zz m).length = p.n := by
                  intro zz; cases zz <;> intro _ <;>
                    first | simp [fipsXmssNode_zero, fipsWotsPkGen_def] | simp [fipsXmssNode_succ]
                simp only [fipsXmssAuthPath_succ] at hv
                split at hv <;>
                · rw [List.mem_append] at hv
                  rcases hv with hL | hR
                  · exact ihz _ _ v hL
                  · rw [List.mem_singleton] at hR; subst hR; exact hNL _ _
            exact fun u hu => hXAuthEach _ _ _ u hu
        · exact ih _ _ _ _ x hTl
    exact fun x hx => hHtMem p.d 0 _ _ _ x hx

/-- Pack a `List UInt8` onto a network `ByteArray` wire and unpack back (`unpackWireBytes (packWireBytes bs) = bs`). -/
def packWireBytes (bs : List UInt8) : ByteArray :=
  ByteArray.mk bs.toArray

def unpackWireBytes (ba : ByteArray) : List UInt8 :=
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
@[expose] def honestPairForCorrupt (cIdx : Fin 3) : Nat × Nat × RssQuorum :=
  if cIdx.val == 0 then (1, 2, .p12)
  else if cIdx.val == 1 then (2, 0, .p20)
  else (0, 1, .p01)

/-- Deal honest key shares into `Nat → Option RssPartyKeyShare` (corrupt party receives `none` in honest vault). -/
@[expose] def dealHonestRssVault (cIdx : Fin 3) (seedSh prfSh : RssByteShares) : Nat → Option RssPartyKeyShare :=
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
@[expose] def rssPadSessionCard (sigBytes : Nat) : Nat :=
  (2 ^ 128) * ((2 ^ 192) *
    ((2 ^ 64) * ((2 ^ 64) * ((2 ^ 64) * ((2 ^ 64) * ((2 ^ (8 * sigBytes)) * (2 ^ (8 * sigBytes))))))))

/-- Cardinality of one full session tape (`padSessionCard * 2^128`). -/
abbrev rssFullSessionCard (sigBytes : Nat) : Nat :=
  rssPadSessionCard sigBytes * (2 ^ 128)

/-- Cardinality of the `Q_s`-session multi-round random tape space. -/
@[expose] def rssMultiSessionCard (sigBytes : Nat) : Nat → Nat
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
@[expose] def decodeRssSessionTape (L : Nat) (padIdx : Fin (rssPadSessionCard L)) (gIdx : Fin (2 ^ 128)) :
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
theorem decodeRssSessionTape_gamma (L : Nat) (padIdx : Fin (rssPadSessionCard L))
    (gIdx : Fin (2 ^ 128)) :
    decodeRssSessionTape L padIdx gIdx =
      { decodeRssSessionTape L padIdx ⟨0, Nat.two_pow_pos 128⟩ with gammaBits := BitVec.ofFin gIdx } := by rfl

def encodeRssPadIdx (L : Nat) (kB : BitVec 128) (sd : BitVec 192)
    (nA nB cA cB : BitVec 64) (m0 m1 : BitVec (8 * L)) : Fin (rssPadSessionCard L) :=
  pairFin kB.toFin
    (pairFin sd.toFin
      (pairFin nA.toFin
        (pairFin nB.toFin
          (pairFin cA.toFin
            (pairFin cB.toFin
              (pairFin m0.toFin m1.toFin))))))

theorem decodeRssSessionTape_encodeRssPadIdx (L : Nat) (kB : BitVec 128) (sd : BitVec 192)
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

@[expose] def decodeMultiSessionTapes (L : Nat) :
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

theorem fixedBytesToBv_bvToFixedBytes : ∀ (L : Nat) (bv : BitVec (8 * L)),
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

theorem leb128_inj {n₁ n₂ : Nat} (h : leb128 n₁ = leb128 n₂) : n₁ = n₂ := by
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

/-- Componentwise `GF(2^{2^k})` (`TowerElem k`) difference `sentWires ⊕ expectedWires`. -/
def zipXorTower (k : Nat) : List (TowerElem k) → List (TowerElem k) → List (TowerElem k)
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys => towerAdd k x y :: zipXorTower k xs ys

theorem zipXorTower_length_le_left (k : Nat) :
    ∀ (xs ys : List (TowerElem k)), (zipXorTower k xs ys).length ≤ xs.length
  | [], _ => Nat.le_refl 0
  | _ :: _, [] => Nat.zero_le _
  | _ :: xs, _ :: ys => Nat.succ_le_succ (zipXorTower_length_le_left k xs ys)

theorem tower_eq_of_add_eq_zero (k : Nat) {a b : TowerElem k}
    (h : towerAdd k a b = towerZero k) : a = b := by
  have h1 := congrArg (towerAdd k a) h
  rw [towerAdd_cancel, towerAdd_zero] at h1
  exact h1.symm

theorem eq_of_zipXorTower_any_false (k : Nat) :
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

theorem evalCoeffs_zipXorTower (k : Nat) (gamma : TowerElem k) :
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

theorem batchDeviationPoly_zipXorTower_eq (k : Nat)
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

theorem evalReplicatedGateCrossByte_self :
    ∀ (bs : List UInt8) (ws : List Tower128),
      evalReplicatedGateCrossByte bs ws ws = 0
  | [], _ => rfl
  | _ :: _, [] => rfl
  | b :: bs, w :: ws => by
    simp only [evalReplicatedGateCrossByte, towerAdd_self_zero]
    have hZ : towerLowByte (towerZero 7) = 0 := by rfl
    rw [hZ, evalReplicatedGateCrossByte_self bs ws]
    have hAnd0 : (b &&& 0) = 0 := by apply UInt8.eq_of_toBitVec_eq; simp
    rw [hAnd0]
    rfl

theorem evalReplicatedGateCrossByte_nil_wires (bs : List UInt8) :
    evalReplicatedGateCrossByte bs [] [] = 0 := by
  cases bs <;> rfl

theorem evalReplicatedGateCrossByte_one_headD (bs : List UInt8) (exp0 : Tower128) :
    evalReplicatedGateCrossByte bs [towerAdd 7 exp0 (towerOne 7)] [exp0] =
      (bs.headD 0 &&& 1) := by
  cases bs with
  | nil => rfl
  | cons b rest =>
    simp only [evalReplicatedGateCrossByte, List.headD_cons]
    have hShift : towerAdd 7 (towerAdd 7 exp0 (towerOne 7)) exp0 = towerOne 7 := by
      rw [towerAdd_comm 7 _ exp0, towerAdd_cancel]
    have hOne : towerLowByte (towerOne 7) = 1 := by rfl
    rw [hShift, hOne, evalReplicatedGateCrossByte_nil_wires rest, uint8_xor_zero]

theorem xorByteStream_zero_head_replicate {xs : List UInt8} {L : Nat}
    (hLen : xs.length = L) :
    xorByteStream xs ((0 : UInt8) :: List.replicate (L - 1) 0) = xs := by
  subst hLen
  cases xs with
  | nil => rfl
  | cons x rest =>
    simp only [List.length_cons, Nat.add_sub_cancel, xorByteStream,
               List.zipWith_cons_cons, uint8_xor_zero]
    exact congrArg (List.cons x) (xorByteStream_replicate_zero rest)

theorem byteArray_bne_self (b : ByteArray) : (b != b) = false := by
  unfold bne
  change (!(b.data == b.data)) = false
  rw [beq_self_eq_true]
  rfl

theorem ite_bne_self_false {α : Type} (b : ByteArray) (t e : α) :
    (if (b != b) = true then t else e) = e := by
  rw [byteArray_bne_self]; rfl

theorem ite_not_beq_self_false {α β : Type} [BEq β] [ReflBEq β] (x : β) (t e : α) :
    (if (!(x == x)) = true then t else e) = e := by
  rw [beq_self_eq_true]; rfl

theorem drop_append_of_length_eq {α : Type} {xs ys : List α} {n : Nat}
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
@[expose] def extractHonestQuorumViews (L : Nat) (cIdx : Fin 3)
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

/-- Accepted corrupt cut openings cannot change the bytes reconstructed from the
    honest cut shares. This is the output-origin obligation used by the strengthened
    ideal-delivery boundary below. -/
theorem checkRound3ActiveOpen_output (L : Nat) (cIdx : Fin 3) (cutSh : RssByteShares)
    (corr : List (Nat × ByteArray)) (opened : List UInt8)
    (h : checkRound3ActiveOpen L cIdx cutSh corr = some opened) :
    opened = reconstructRssBytes cutSh := by
  unfold checkRound3ActiveOpen at h
  cases hf : corr.find? (fun pr => pr.1 == cIdx.val) with
  | none => rw [hf] at h; cases h
  | some pair =>
    rw [hf] at h
    dsimp only at h
    split at h
    · unfold verifyRssActiveOpenBytes at h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        have heq := hc.1.1.2
        simp only [heq] at h
        cases h
        rfl
      · cases h
    · split at h
      · unfold verifyRssActiveOpenBytes at h
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          have heq := hc.1.2
          simp only [← heq] at h
          cases h
          rfl
        · cases h
      · unfold verifyRssActiveOpenBytes at h
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
          have heq := hc.2
          simp only [← heq] at h
          cases h
          rfl
        · cases h

theorem reconstructRssBytes_masked_eq :
    ∀ {s b0 b1 : List UInt8},
      s.length = b0.length →
      b0.length = b1.length →
      reconstructRssBytes ⟨b0, b1, xorByteStream s (xorByteStream b0 b1)⟩ = s
  | [], [], [], _, _ => rfl
  | x :: xs, u :: us, v :: tailV, h1, h2 => by
    simp only [reconstructRssBytes, xorByteStream, List.zipWith_cons_cons, List.cons.injEq]
    refine ⟨?_, reconstructRssBytes_masked_eq (Nat.succ.inj h1) (Nat.succ.inj h2)⟩
    apply UInt8.eq_of_toBitVec_eq
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [UInt8.toBitVec_xor, BitVec.getLsbD_xor]
    cases u.toBitVec.getLsbD i <;> cases v.toBitVec.getLsbD i <;> cases x.toBitVec.getLsbD i <;> rfl

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

/-- Measure-preserving XOR pad bijection on `Fin (rssPadSessionCard L)`:
    keeps `(nonceA, nonceB)` fixed and shifts `(chiMaskA, chiMaskB, cutMask0, cutMask1)` by
    `(wA, wB, rawTag0, rawTag1)`; the coin share `coinB` and the PRG seeds are left fixed. -/
def sessionPadXorEquiv (L : Nat)
    (wA wB : BitVec 64) (rawTag0 rawTag1 : BitVec (8 * L)) :
    SimpleEquiv (Fin (rssPadSessionCard L)) (Fin (rssPadSessionCard L)) :=
  let h1 : 0 < 2 ^ (8 * L) := Nat.two_pow_pos (8 * L)
  let h2 : 0 < (2 ^ (8 * L)) * (2 ^ (8 * L)) := Nat.mul_pos h1 h1
  let h3 : 0 < (2 ^ 64) * ((2 ^ (8 * L)) * (2 ^ (8 * L))) := Nat.mul_pos (Nat.two_pow_pos 64) h2
  let h4 : 0 < (2 ^ 64) * ((2 ^ 64) * ((2 ^ (8 * L)) * (2 ^ (8 * L)))) := Nat.mul_pos (Nat.two_pow_pos 64) h3
  let h5 : 0 < (2 ^ 64) * ((2 ^ 64) * ((2 ^ 64) * ((2 ^ (8 * L)) * (2 ^ (8 * L))))) := Nat.mul_pos (Nat.two_pow_pos 64) h4
  let h6 : 0 < (2 ^ 64) * ((2 ^ 64) * ((2 ^ 64) * ((2 ^ 64) * ((2 ^ (8 * L)) * (2 ^ (8 * L)))))) :=
    Nat.mul_pos (Nat.two_pow_pos 64) h5
  let h7 : 0 < (2 ^ 192) * ((2 ^ 64) * ((2 ^ 64) * ((2 ^ 64) * ((2 ^ 64) * ((2 ^ (8 * L)) * (2 ^ (8 * L))))))) :=
    Nat.mul_pos (Nat.two_pow_pos 192) h6
  depProdFinEquiv h7 (idFinEquiv (2 ^ 128)) (fun _ =>
  depProdFinEquiv h6 (idFinEquiv (2 ^ 192)) (fun _ =>
  depProdFinEquiv h5 (idFinEquiv (2 ^ 64)) (fun _ =>
    depProdFinEquiv h4 (idFinEquiv (2 ^ 64)) (fun _ =>
      depProdFinEquiv h3 (finBitVecXorEquiv 64 wA) (fun _ =>
        depProdFinEquiv h2 (finBitVecXorEquiv 64 wB) (fun _ =>
          depProdFinEquiv h1 (finBitVecXorEquiv (8 * L) rawTag0) (fun _ =>
            finBitVecXorEquiv (8 * L) rawTag1)))))))

/-- Measure-preserving XOR bijection on one full session tape `Fin (rssFullSessionCard L)`,
    leaving `gammaBits : BitVec 128` invariant. -/
def sessionFullTapeXorEquiv (L : Nat)
    (wA wB : BitVec 64) (rawTag0 rawTag1 : BitVec (8 * L)) :
    SimpleEquiv (Fin (rssFullSessionCard L)) (Fin (rssFullSessionCard L)) :=
  depProdFinEquiv (Nat.two_pow_pos 128)
    (sessionPadXorEquiv L wA wB rawTag0 rawTag1)
    (fun _ => idFinEquiv (2 ^ 128))

theorem decodeSingleFullTape_sessionFullTapeXorEquiv (L : Nat)
    (wA wB : BitVec 64) (rawTag0 rawTag1 : BitVec (8 * L))
    (cur : Fin (rssFullSessionCard L)) :
    let t := decodeSingleFullTape L cur
    decodeSingleFullTape L ((sessionFullTapeXorEquiv L wA wB rawTag0 rawTag1).toFun cur) =
      { coinB := t.coinB
        prgSeeds := t.prgSeeds
        nonceA := t.nonceA
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
      splitFinLeft_pairFin, splitFinRight_pairFin,
      splitFinLeft_pairFin, splitFinRight_pairFin,
      splitFinLeft_pairFin, splitFinRight_pairFin]
  simp only [BitVec.ofFin_toFin]
  rw [BitVec.xor_comm _ wA, BitVec.xor_comm _ wB,
      BitVec.xor_comm _ rawTag0, BitVec.xor_comm _ rawTag1]

theorem qsum_le_add_qsum : ∀ (n : Nat) (f g h : Fin n → Nat),
    (∀ i, f i ≤ g i + h i) → qsum n f ≤ qsum n g + qsum n h
  | 0, _, _, _, _ => by simp only [qsum_zero]; exact Nat.le_refl 0
  | n + 1, f, g, h, hLe => by
    simp only [qsum_succ]
    have ih := qsum_le_add_qsum n
      (fun i => f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (fun i => g ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (fun i => h ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (fun i => hLe ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    have h0 := hLe ⟨0, Nat.zero_lt_succ n⟩
    omega

theorem qsum_mul_right_local : ∀ (n c : Nat) (f : Fin n → Nat),
    qsum n (fun i => f i * c) = qsum n f * c
  | 0, _, _ => by simp [qsum_zero]
  | n + 1, c, f => by simp only [qsum_succ, qsum_mul_right_local n c, Nat.add_mul]

/-- Right-nested product cardinality `B ^ t = B * (B * ... * 1)` avoiding `Nat.pow` WHNF expansion on `2 ^ 128`. -/
def towerPadSpaceCard (B : Nat) : Nat → Nat
  | 0 => 1
  | t + 1 => B * towerPadSpaceCard B t

theorem towerPadSpaceCard_pos {B : Nat} (hB : 0 < B) : ∀ (t : Nat), 0 < towerPadSpaceCard B t
  | 0 => Nat.zero_lt_one
  | t + 1 => Nat.mul_pos hB (towerPadSpaceCard_pos hB t)

theorem towerPadSpaceCard_eq_pow (B : Nat) : ∀ (t : Nat), towerPadSpaceCard B t = B ^ t
  | 0 => rfl
  | t + 1 => by
    simp only [towerPadSpaceCard, towerPadSpaceCard_eq_pow B t, Nat.pow_succ, Nat.mul_comm]

def decodeGenericPadPoly {R : Type} [CommRingOps R] (B : Nat) (hB : 0 < B)
    (dec1 : Fin B → R) : (t : Nat) → Fin (towerPadSpaceCard B t) → ShamirPadPoly R t
  | 0, _ => ⟨[], rfl⟩
  | t + 1, idx =>
    let hRest := towerPadSpaceCard_pos hB t
    let c0 := dec1 (splitFinLeft hRest idx)
    let rest := decodeGenericPadPoly B hB dec1 t (splitFinRight hRest idx)
    ⟨c0 :: rest.1, congrArg Nat.succ rest.2⟩

def encodeGenericPadPoly {R : Type} [CommRingOps R] (B : Nat)
    (enc1 : R → Fin B) : (t : Nat) → ShamirPadPoly R t → Fin (towerPadSpaceCard B t)
  | 0, _ => ⟨0, Nat.zero_lt_one⟩
  | t + 1, ⟨c0 :: cs, hLen⟩ =>
    pairFin (enc1 c0) (encodeGenericPadPoly B enc1 t ⟨cs, Nat.succ.inj hLen⟩)

theorem decode_encode_genericPadPoly {R : Type} [CommRingOps R] (B : Nat) (hB : 0 < B)
    (dec1 : Fin B → R) (enc1 : R → Fin B) (hLeft : ∀ x : R, dec1 (enc1 x) = x) :
    ∀ (t : Nat) (P : ShamirPadPoly R t),
      decodeGenericPadPoly B hB dec1 t (encodeGenericPadPoly B enc1 t P) = P
  | 0, ⟨[], _⟩ => rfl
  | t + 1, ⟨c0 :: cs, hLen⟩ => by
    simp only [encodeGenericPadPoly, decodeGenericPadPoly,
               splitFinLeft_pairFin, splitFinRight_pairFin, hLeft,
               decode_encode_genericPadPoly B hB dec1 enc1 hLeft t ⟨cs, Nat.succ.inj hLen⟩]

theorem encode_decode_genericPadPoly {R : Type} [CommRingOps R] (B : Nat) (hB : 0 < B)
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

/-! ## 3. `FIPS 205` Hash-Game Witness Types & Collision/Chain-Break Extractors -/

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

theorem wellFormed_props {p : Fips205Params} (hWf : p.wellFormed = true) :
    0 < p.n ∧ p.n ≤ 32 ∧ 0 < p.d ∧ p.h = p.d * p.hp ∧ 0 < p.k ∧ 0 < p.a := by
  rw [Fips205Params.wellFormed_def] at hWf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hWf
  exact ⟨hWf.1.1.1.1.1.1, hWf.1.1.1.1.1.2, hWf.1.1.1.1.2, hWf.1.1.1.2, hWf.1.1.2, hWf.1.2⟩

theorem fipsXmssNode_length (p : Fips205Params) (skSeed pkSeed : List UInt8) (layer tree : Nat) :
    ∀ (z nodeIdx : Nat), (fipsXmssNode p skSeed pkSeed layer tree z nodeIdx).length = p.n
  | 0, nodeIdx => by simp [fipsXmssNode_zero, fipsWotsPkGen_def]
  | z + 1, nodeIdx => by simp [fipsXmssNode_succ]

theorem fipsForsNode_length (p : Fips205Params) (skSeed pkSeed : List UInt8) (tree idxLeaf : Nat) :
    ∀ (z nodeIdx : Nat), (fipsForsNode p skSeed pkSeed tree idxLeaf z nodeIdx).length = p.n
  | 0, nodeIdx => by simp [fipsForsNode_zero]
  | z + 1, nodeIdx => by simp [fipsForsNode_succ]

theorem fipsForsPkGen_length (p : Fips205Params) (skSeed pkSeed : List UInt8) (tree idxLeaf : Nat) :
    (fipsForsPkGen p skSeed pkSeed tree idxLeaf).length = p.n := by
  simp [fipsForsPkGen_def]

theorem fipsForsPkFromSig_length (p : Fips205Params) (fsig : List FipsForsTreeSig)
    (md pkSeed : List UInt8) (tree idxLeaf : Nat) :
    (fipsForsPkFromSig p fsig md pkSeed tree idxLeaf).length = p.n := by
  simp [fipsForsPkFromSig_def]

theorem honestSlhWotsMsg_length (p : Fips205Params) (skSeed pkSeed : List UInt8)
    (layer tree leaf : Nat) :
    (honestSlhWotsMsg p skSeed pkSeed layer tree leaf).length = p.n := by
  cases layer with
  | zero => exact fipsForsPkGen_length p skSeed pkSeed tree leaf
  | succ l => exact fipsXmssNode_length p skSeed pkSeed l _ p.hp 0

theorem fipsWalkBottomUp_length (n : Nat) (pkSeed : List UInt8) (layer tree kp : Nat)
    (ty : FipsAdrsType) :
    ∀ (path : List (List UInt8)) (z idx : Nat) (node : List UInt8),
      node.length = n →
      (fipsWalkBottomUp n pkSeed layer tree kp ty z idx node path).length = n
  | [], _, _, _, hN => by rw [fipsWalkBottomUp_nil]; exact hN
  | authZ :: rest, z, idx, node, _ => by
    simp only [fipsWalkBottomUp_cons]
    by_cases hPar : idx % 2 = 0
    · rw [ite_eq_left hPar]
      exact fipsWalkBottomUp_length n pkSeed layer tree kp ty rest (z + 1) (idx / 2) _ (fipsH_length _ _ _ _ _)
    · rw [ite_eq_right hPar]
      exact fipsWalkBottomUp_length n pkSeed layer tree kp ty rest (z + 1) (idx / 2) _ (fipsH_length _ _ _ _ _)

theorem fipsXmssPkFromSig_length (p : Fips205Params) (idx : Nat) (xsig : FipsXmssSig)
    (msg pkSeed : List UInt8) (layer tree : Nat) :
    (fipsXmssPkFromSig p idx xsig msg pkSeed layer tree).length = p.n := by
  simp only [fipsXmssPkFromSig_def]
  exact fipsWalkBottomUp_length p.n pkSeed layer tree 0 .tree xsig.authPath 0 idx _ (by simp [fipsWotsPkFromSig_def])

theorem flatten_inj_fixed {n : Nat} (hn : 0 < n) :
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
def extractMerkleWalkCollision (n : Nat) (pkSeed : List UInt8)
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
    False.elim (hNe (by simpa [fipsWalkBottomUp_nil, fipsWalkBottomUp_cons] using hWalk))
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
             simpa [fipsH_def] using hE },
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
             simpa [fipsH_def] using hE },
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
          simpa [fipsWalkBottomUp_nil, fipsWalkBottomUp_cons, parentIdx, adrs, nextNode] using hWalk
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
def extractSingleXmssLayerBreak (p : Fips205Params)
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
      exact (fipsXmssPkFromSig_def p leaf xsig curNode sk.pkSeed layer tree).symm.trans hXmssEq
    let ⟨coll, hPref⟩ := extractMerkleWalkCollision p.n sk.pkSeed layer tree 0 .tree
      (fipsXmssNode p sk.skSeed sk.pkSeed layer tree)
      (fipsXmssNode_length p sk.skSeed sk.pkSeed layer tree)
      (fun z ni => fipsXmssNode_succ p sk.skSeed sk.pkSeed layer tree z ni)
      xsig.authPath 0 leaf wotsPkStar (by simp [wotsPkStar, fipsWotsPkFromSig_def]) hApEach
      (fun h => hWotsEq (h.trans (fipsXmssNode_zero p sk.skSeed sk.pkSeed layer tree leaf))) hWalk
    .inr ⟨coll, hPref⟩

/-- Multi-layer hypertree extractor (`0 Classical.choice`) walking `rem` remaining layers `layer .. p.d - 1`. -/
def extractHypertreeBreakAux (p : Fips205Params)
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
          simpa [fipsHtVerifyAux_nil, fipsHtVerifyAux_cons] using hTopVerify
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
          (by simpa [fipsHtVerifyAux_nil, fipsHtVerifyAux_cons, nextNode, nextLeaf, nextTree] using hTopVerify)

/-- Constructive list scanner (`0 Classical.choice`) finding the first element satisfying decidable `P`. -/
def findDecidableElem {α : Type} (P : α → Prop) [∀ x, Decidable (P x)] :
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

theorem map_eq_on_mem {α β : Type} {f g : α → β} :
    ∀ {xs : List α}, xs.map f = xs.map g → ∀ x ∈ xs, f x = g x
  | [], _, _, hx => by cases hx
  | a :: xs, hEq, x, hx => by
    simp only [List.map_cons, List.cons.injEq] at hEq
    rcases List.mem_cons.mp hx with rfl | hTl
    · exact hEq.1
    · exact map_eq_on_mem hEq.2 x hTl

/-- Scan FORS trees `0 .. count - 1` (`0 Classical.choice`) to verify either a Merkle/`.forsTree`
    `SHAKE256` collision OR that EVERY `j < count` satisfies `(sigStar.forsSig.getD j).skVal = honSkVal j`! -/
def verifyOrExtractForsTrees (p : Fips205Params) (sk : SlhSecretKey)
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
                have hE : node0Star = fipsF p.n sk.pkSeed adrsTree0 honSkVal :=
                  hNode0Eq.trans (fipsForsNode_zero p sk.skSeed sk.pkSeed idxTree idxLeaf globalLeaf)
                simpa [node0Star, fipsF_eq] using hE }
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
          (fun z ni => fipsForsNode_succ p sk.skSeed sk.pkSeed idxTree idxLeaf z ni)
          entry.authPath 0 globalLeaf node0Star (fipsF_length _ _ _ _) hApEach hNode0Eq hWalk
        .inl coll

/-! ## 4. Counting and Round-3 Helper Lemmas for the Transcript Theorems -/

/-- The honest Round-3 message list is never empty, for either world. -/
theorem buildHonestRound3Msgs_ne_nil (cIdx : Fin 3) (cutSh : RssByteShares) :
    buildHonestRound3Msgs cIdx cutSh ≠ [] := by
  rcases cIdx with ⟨_ | _ | _ | n, hv⟩
  · intro h; cases h
  · intro h; cases h
  · intro h; cases h
  · exact False.elim (Nat.not_lt_zero n (Nat.lt_of_add_lt_add_right hv))

theorem isEmpty_false_of_ne_nil {α : Type} : ∀ {l : List α}, l ≠ [] → l.isEmpty = false
  | [], h => absurd rfl h
  | _ :: _, _ => rfl

/-- Forgery-count transfer through the root-hit event, with the commitment-hop gap explicit. -/
theorem count_transfer_with_coin_gap {cR cI bR bD card num : Nat} (hCard : 0 < card)
    (hT : cR * card ≤ cI * card + bR * card) (hDecoy : bD * 2 ^ 128 ≤ num * card) :
    cR * 2 ^ 128 ≤ cI * 2 ^ 128 + num * card + natAbsDiff bR bD * 2 ^ 128 := by
  have h1 : cR ≤ cI + bR := by
    rw [← Nat.add_mul] at hT
    exact Nat.le_of_mul_le_mul_right hT hCard
  have hTri : bR ≤ bD + natAbsDiff bR bD := by
    simp only [natAbsDiff_eq]
    split <;> omega
  have h2 := Nat.mul_le_mul_right (2 ^ 128) (Nat.le_trans h1 (Nat.add_le_add_left hTri cI))
  rw [Nat.add_mul, Nat.add_mul] at h2
  have h3 : cI * 2 ^ 128 + (bD * 2 ^ 128 + natAbsDiff bR bD * 2 ^ 128) ≤
      cI * 2 ^ 128 + num * card + natAbsDiff bR bD * 2 ^ 128 := by
    rw [Nat.add_assoc]
    exact Nat.add_le_add_left (Nat.add_le_add_right hDecoy _) _
  exact Nat.le_trans h2 h3

/-! ## 5. Honest Round-3 Echo, Small Horner Facts & the Horner Tag as a Tag Scheme -/

theorem encodeSlhSig_length {p : Fips205Params} {sig : SlhSignature}
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
  | (_, w0) :: (_, w1) :: _ =>
    packWireBytes (((unpackWireBytes w1).drop L) ++ ((unpackWireBytes w0).take L))
  | _ => ByteArray.empty

/-- The echo reads only the two cut-opening messages; the coin openings after them are ignored. -/
theorem echoHonestRound3_append (L : Nat) (cIdx : Fin 3) (cutSh : RssByteShares)
    (extra : List (Nat × ByteArray)) :
    echoHonestRound3 L (buildHonestRound3Msgs cIdx cutSh ++ extra) =
      echoHonestRound3 L (buildHonestRound3Msgs cIdx cutSh) := by
  rcases cIdx with ⟨_ | _ | _ | n, hv⟩
  · rfl
  · rfl
  · rfl
  · exact False.elim (Nat.not_lt_zero n (Nat.lt_of_add_lt_add_right hv))

theorem checkRound3ActiveOpen_echoHonestRound3 (L : Nat) (cIdx : Fin 3)
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
  · have hc : (⟨0 + 1 + 1, hv⟩ : Fin 3) = ⟨2, by decide⟩ := by rfl
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

theorem batchDeviationPoly_nil (x : Tower128) :
    batchDeviationPoly ([] : List Tower128) x = towerZero 7 := by
  simp only [batchDeviationPoly, RoundPoly.evalCoeffs,
             LawfulCommRing.mul_zero, LawfulCommRing.add_zero]
  rfl

theorem batchDeviationPoly_singleton_one (x : Tower128) :
    batchDeviationPoly [towerOne 7] x = x := by
  simp only [batchDeviationPoly, RoundPoly.evalCoeffs,
             LawfulCommRing.mul_zero, LawfulCommRing.add_zero,
             LawfulCommRing.zero_add]
  exact LawfulCommRing.mul_one x

/-- Public Round-3 wire reconstructor for `cIdx = 0` (`honestRound3 = [(1, b1 ++ b2), (2, b2 ++ b0)]`):
    extracts the opened first byte `(b0[0] ^^^ b1[0] ^^^ b2[0])` directly from public wire messages! -/
def extractPublicRound3HeadByte (L : Nat) (honR3 : List (Nat × ByteArray)) : Option UInt8 :=
  match honR3 with
  | (_, w1) :: (_, w2) :: _ =>
    let b1 := (unpackWireBytes w1).take L
    let b2 := (unpackWireBytes w1).drop L
    let b0 := (unpackWireBytes w2).drop L
    (reconstructRssBytes ⟨b0, b1, b2⟩).head?
  | _ => none

theorem parseCorruptRound2Wire_one_wire (w : Tower128) :
    parseCorruptRound2Wire 1
      (packWireBytes (List.replicate 24 0 ++ encodeTower128Wire w)) =
      some (List.replicate 24 0, [w]) := by
  simpa [encodeCorruptRound2Wire] using
    parseCorruptRound2Wire_encode (List.replicate 24 0) [w] rfl (by simp only [List.length_singleton]; omega)

attribute [local irreducible] slhPkDigest computeHonestChiWord

/-- Faulty tape schedule reusing Session 0's mask tape across all subsequent sessions (`tape_k = tape_0`). -/
def reusedFirstSessionTapes (L s : Nat) (ω : Fin (rssMultiSessionCard L s)) :
    Nat → RssSlhSessionTape L :=
  fun _ => decodeMultiSessionTapes L s ω 0

/-- **`#tooth`: a challenge known before the wires are fixed protects nothing.** For every
    challenge `gamma` the non-zero two-wire deviation `[gamma, 1]` is a root of the batch
    deviation polynomial (`gamma * (gamma + gamma) = 0` in characteristic 2). The barrier is
    therefore only as strong as the unpredictability of `coinA ⊕ coinB ⊕ corruptCoin` at the
    moment the corrupt party sends its Round-2 frame. -/
theorem tooth_known_challenge_admits_nonzero_deviation (gamma : Tower128) :
    (∃ d ∈ [gamma, towerOne 7], d ≠ towerZero 7) ∧
    batchDeviationPoly [gamma, towerOne 7] gamma = towerZero 7 := by
  refine ⟨⟨towerOne 7, List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl), by decide⟩, ?_⟩
  unfold batchDeviationPoly
  change towerAdd 7 (towerZero 7) (towerMul 7 gamma
    (towerAdd 7 gamma (towerMul 7 gamma
      (towerAdd 7 (towerOne 7) (towerMul 7 gamma (towerZero 7)))))) = towerZero 7
  have hMulZero : towerMul 7 gamma (towerZero 7) = towerZero 7 := LawfulCommRing.mul_zero gamma
  have hMulOne : towerMul 7 gamma (towerOne 7) = gamma := LawfulCommRing.mul_one gamma
  rw [hMulZero, towerAdd_zero, hMulOne, towerAdd_self_zero, hMulZero, towerAdd_self_zero]

theorem evalCoeffs_all_zero (x : Tower128) : ∀ (ds : List Tower128),
    ds.any (fun d => decide (d ≠ towerZero 7)) = false →
    RoundPoly.evalCoeffs ds x = towerZero 7
  | [], _ => rfl
  | d :: ds, h => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    have hd : d = towerZero 7 := by
      by_cases hEq : d = towerZero 7
      · exact hEq
      · exact False.elim (Bool.noConfusion ((decide_eq_true hEq).symm.trans h.1))
    have hMulZero : towerMul 7 x (towerZero 7) = towerZero 7 := LawfulCommRing.mul_zero x
    change towerAdd 7 d (towerMul 7 x (RoundPoly.evalCoeffs ds x)) = towerZero 7
    rw [evalCoeffs_all_zero x ds h.2, hd, hMulZero, towerAdd_self_zero]

/-- The `GF(2^128)` Horner check of the barrier as a `ConsistencyTagScheme`: a deviation is the
    list of wire differences, it is honest when every difference is zero, and it is accepted
    at challenge `c` when `c` is a root of its batch deviation polynomial. -/
def hornerTagScheme : ConsistencyTagScheme (List Tower128) (2 ^ 128) where
  isHonest := fun ds => !(ds.any (fun d => decide (d ≠ towerZero 7)))
  accepts := fun ds c => batchDeviationPoly ds (unpackTower 7 (BitVec.ofFin c)) == towerZero 7
  complete := by
    intro ds c hH
    have hAny : ds.any (fun d => decide (d ≠ towerZero 7)) = false := by
      cases hA : ds.any (fun d => decide (d ≠ towerZero 7))
      · rfl
      · rw [hA] at hH; cases hH
    have hMulZero : towerMul 7 (unpackTower 7 (BitVec.ofFin c)) (towerZero 7) = towerZero 7 :=
      LawfulCommRing.mul_zero _
    have hZero : batchDeviationPoly ds (unpackTower 7 (BitVec.ofFin c)) = towerZero 7 := by
      unfold batchDeviationPoly
      change towerAdd 7 (towerZero 7) (towerMul 7 (unpackTower 7 (BitVec.ofFin c))
        (RoundPoly.evalCoeffs ds (unpackTower 7 (BitVec.ofFin c)))) = towerZero 7
      rw [evalCoeffs_all_zero _ ds hAny, hMulZero, towerAdd_self_zero]
    rw [hZero]
    exact beq_self_eq_true _

/-- **Counted tag-forgery term for the Horner tag (`rss_active_tag_forgery_count_le`).** For a
    corrupt strategy whose share modification has at most `deg` wire differences and is fixed
    before the challenge, at most `2^width * deg` of the `2^width * 2^128` pairs
    (honest coin share, challenge) are tag forgeries: probability at most `deg / 2^128`. -/
theorem rss_active_tag_forgery_count_le {width : Nat} (deg : Nat)
    (adv : ActiveSlhAdversary width (2 ^ 128) (List Tower128))
    (hDeg : ∀ h, (adv.deviation h).length ≤ deg) :
    qsum (2 ^ width) (fun h => qsum (2 ^ 128) (fun c =>
      if activeTagForgery hornerTagScheme adv h c then 1 else 0)) ≤ 2 ^ width * deg := by
  rw [← qsum_const (2 ^ width) deg]
  apply qsum_le_qsum
  intro h
  cases hA : (adv.deviation (BitVec.ofFin h)).any (fun d => decide (d ≠ towerZero 7))
  · have hZ : ∀ c : Fin (2 ^ 128),
        (if activeTagForgery hornerTagScheme adv h c then 1 else 0) = 0 := by
      intro c
      have hF : activeTagForgery hornerTagScheme adv h c = false := by
        simp only [activeTagForgery_def]
        change (!(adv.aborts (BitVec.ofFin h) c) &&
          hornerTagScheme.accepts (adv.deviation (BitVec.ofFin h)) c &&
          !(!((adv.deviation (BitVec.ofFin h)).any (fun d => decide (d ≠ towerZero 7))))) = false
        rw [hA]
        exact Bool.and_false _
      rw [hF]
      rfl
    rw [qsum_congr hZ, qsum_const, Nat.mul_zero]
    exact Nat.zero_le deg
  · obtain ⟨d, hdMem, hdDec⟩ := List.any_eq_true.mp hA
    refine Nat.le_trans (qsum_le_qsum (fun c => ?_))
      (tower128_roots_qsum_le deg (adv.deviation (BitVec.ofFin h)) (hDeg _)
        ⟨d, hdMem, of_decide_eq_true hdDec⟩)
    simp only [activeTagForgery_def]
    change (if (!(adv.aborts (BitVec.ofFin h) c) &&
        (batchDeviationPoly (adv.deviation (BitVec.ofFin h)) (unpackTower 7 (BitVec.ofFin c)) ==
          towerZero 7) &&
        !(hornerTagScheme.isHonest (adv.deviation (BitVec.ofFin h)))) = true then 1 else 0) ≤
      (if (batchDeviationPoly (adv.deviation (BitVec.ofFin h)) (unpackTower 7 (BitVec.ofFin c)) ==
          towerZero 7) = true then 1 else 0)
    cases adv.aborts (BitVec.ofFin h) c <;>
      cases (batchDeviationPoly (adv.deviation (BitVec.ofFin h)) (unpackTower 7 (BitVec.ofFin c)) ==
        towerZero 7) <;>
      cases hornerTagScheme.isHonest (adv.deviation (BitVec.ofFin h)) <;> decide

/-- **Active-malicious hedged threshold signing under the Horner tag
    (`rss_active_malicious_threshold_sig_hedged_bound`).** Composition of
    `active_malicious_threshold_sig_abort_or_exact_hedged_dist` with
    `rss_active_tag_forgery_count_le`: over a uniform honest coin share and a uniform
    `GF(2^128)` challenge, for every test `D` the number of runs whose released bytes pass `D`
    is within `2^width * deg` of the number of runs in which the single-signer signature on
    hedge `honestCoin ⊕ corruptCoin` passes `D` and the run is in the corrupt party's release
    set. As a probability the distance from the ideal functionality with abort is at most
    `deg / 2^128`. -/
theorem rss_active_malicious_threshold_sig_hedged_bound
    (p : Fips205Params) (hWf : p.wellFormed = true) {skSeed skPrf pkSeed : List UInt8}
    (run : SlhThresholdRun p skSeed skPrf pkSeed) {width : Nat} (deg : Nat)
    (adv : ActiveSlhAdversary width (2 ^ 128) (List Tower128))
    (hDeg : ∀ h, (adv.deviation h).length ≤ deg)
    (encode : BitVec width → List UInt8) (msgPrime : List UInt8) (D : List UInt8 → Bool) :
    natAbsDiff
      (qsum (2 ^ width) (fun h => qsum (2 ^ 128) (fun c =>
        if (match activeMaliciousThresholdSign run hornerTagScheme adv encode msgPrime h c with
            | some s => D s
            | none => false) then 1 else 0)))
      (qsum (2 ^ width) (fun h => qsum (2 ^ 128) (fun c =>
        if (activeReleased hornerTagScheme adv h c &&
            D (encodeSlhSig (slhSignInternal p msgPrime
              (slhKeygenInternal p skSeed skPrf pkSeed).1
              (encode (BitVec.ofFin h ^^^ adv.corruptCoin))))) then 1 else 0))) ≤
    2 ^ width * deg :=
  Nat.le_trans
    ((active_malicious_threshold_sig_abort_or_exact_hedged_dist p hWf run hornerTagScheme adv
      encode msgPrime).2.1 D)
    (rss_active_tag_forgery_count_le deg adv hDeg)

/-! ### Production coin framing

These are the byte-level commitments used by the Rust run_commit_and_open_coin_with_hook function in
`preprocessing.rs`. They are deliberately separate from the legacy 24-byte RSS shell above:
that shell's hiding-game theorem does not yet reduce to this 32-byte production coin. -/

structure ProductionCoinContext where
  sessionId : BitVec 256
  phaseLabel : List UInt8
  transcriptDigest : BitVec 256

def productionCoinCommitCustom : List UInt8 := [0x51, 0x53, 0x41, 0x47, 0x2e, 0x43, 0x4f, 0x49, 0x4e, 0x2e, 0x43, 0x4f, 0x4d, 0x4d, 0x49, 0x54, 0x2f, 0x76, 0x31]
def productionCoinDeriveCustom : List UInt8 := [0x51, 0x53, 0x41, 0x47, 0x2e, 0x43, 0x4f, 0x49, 0x4e, 0x2e, 0x44, 0x45, 0x52, 0x49, 0x56, 0x45, 0x2f, 0x76, 0x31]

def productionCoinCommitFrame (ctx : ProductionCoinContext) (party : UInt64)
    (share : BitVec 256) : List UInt8 :=
  encodeMultiFrame [bvToFixedBytes 32 ctx.sessionId, ctx.phaseLabel,
    bvToFixedBytes 32 ctx.transcriptDigest, (bvToFixedBytes 8 party.toBitVec).reverse,
    bvToFixedBytes 32 share]

def productionCoinCommit (ctx : ProductionCoinContext) (party : UInt64)
    (share : BitVec 256) : List UInt8 :=
  cshake256Bytes productionCoinCommitCustom (productionCoinCommitFrame ctx party share)

def productionCoinDerive (ctx : ProductionCoinContext) (combined : BitVec 256) : List UInt8 :=
  cshake256Bytes productionCoinDeriveCustom
    (encodeMultiFrame [bvToFixedBytes 32 ctx.sessionId, ctx.phaseLabel,
      bvToFixedBytes 32 ctx.transcriptDigest, bvToFixedBytes 32 combined])

/-- A changed accepted opening yields an explicit cSHAKE collision on framed inputs. -/
def productionCoinCommit_binding_or_collision (ctx : ProductionCoinContext) (party : UInt64)
    (a b : BitVec 256) (h : productionCoinCommit ctx party a = productionCoinCommit ctx party b) :
    PSum (a = b) (HashCollisionWitness (cshake256Bytes productionCoinCommitCustom)) :=
  if same : productionCoinCommitFrame ctx party a = productionCoinCommitFrame ctx party b then
    .inl (by
      have fields := encodeMultiFrame_injective same
      have bytes : bvToFixedBytes 32 a = bvToFixedBytes 32 b := by
        simpa only [List.cons.injEq, true_and, and_true] using fields
      have recovered := congrArg (fixedBytesToBv 32) bytes
      simpa only [fixedBytesToBv_bvToFixedBytes] using recovered)
  else .inr ⟨productionCoinCommitFrame ctx party a, productionCoinCommitFrame ctx party b, same, h⟩

/-- Commit and derive domains are distinct, independently of the byte framing. -/
theorem tooth_production_coin_domains_distinct :
    productionCoinCommitCustom ≠ productionCoinDeriveCustom := by
  unfold productionCoinCommitCustom productionCoinDeriveCustom
  decide +kernel

/-! ### The barrier's private-stream test (`verifyPrivateChiWires`)

Counting statements about the test that `sharedPreCutBarrier` runs against the corrupt party's
private `deg`-gate `χ` stream. `activeConsistencyBreak_implies_schwartzZippel_root` ties the test
to the stream the honest pair computes from its vault in a real session. -/

/-- All gates are covered by one nonzero deviation polynomial. The expected stream and the
corrupt frame are fixed before the challenge. -/
theorem verifyPrivateChiWires_active_forgery_count (expected sent : List Tower128)
    (hlen : sent.length = expected.length)
    (hbad : ∃ d ∈ zipXorTower 7 sent expected, d ≠ towerZero 7) :
    qsum (2 ^ 128) (fun c =>
      if verifyPrivateChiWires expected sent (unpackTower 7 (BitVec.ofFin c)) then 1 else 0) ≤
      expected.length := by
  have hd : (zipXorTower 7 sent expected).length ≤ expected.length :=
    Nat.le_trans (zipXorTower_length_le_left 7 sent expected) (Nat.le_of_eq hlen)
  have hc : ∀ c : Fin (2 ^ 128),
      verifyPrivateChiWires expected sent (unpackTower 7 (BitVec.ofFin c)) =
      (batchDeviationPoly (zipXorTower 7 sent expected)
        (unpackTower 7 (BitVec.ofFin c)) == towerZero 7) := by
    intro c
    simp only [verifyPrivateChiWires, hlen, decide_true, Bool.true_and]
    exact bbcggiWireAccumulator_eq_iff_batchDeviationPoly hlen _
  simp only [hc]
  exact tower128_roots_qsum_le expected.length _ hd hbad

/-- Any altered gate, including deletion or insertion, is covered. A malformed length is
rejected for every challenge; an equal-length modification supplies a constructively extracted
nonzero coefficient to the polynomial root bound. -/
theorem verifyPrivateChiWires_any_changed_gate_count (expected sent : List Tower128)
    (hne : sent ≠ expected) :
    qsum (2 ^ 128) (fun c =>
      if verifyPrivateChiWires expected sent (unpackTower 7 (BitVec.ofFin c)) then 1 else 0) ≤
      expected.length := by
  by_cases hl : sent.length = expected.length
  · apply verifyPrivateChiWires_active_forgery_count expected sent hl
    cases ha : (zipXorTower 7 sent expected).any (fun d => decide (d ≠ towerZero 7)) with
    | false => exact False.elim (hne (eq_of_zipXorTower_any_false 7 hl ha))
    | true =>
      obtain ⟨d, hm, hd⟩ := List.any_eq_true.mp ha
      exact ⟨d, hm, of_decide_eq_true hd⟩
  · have hz : ∀ c : Fin (2 ^ 128),
        (if verifyPrivateChiWires expected sent (unpackTower 7 (BitVec.ofFin c)) then 1 else 0) = 0 := by
      intro c
      simp only [verifyPrivateChiWires, hl, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rw [qsum_congr hz, qsum_const, Nat.mul_zero]
    exact Nat.zero_le _

theorem tooth_verifyPrivateChiWires_rejects_truncation
    (expected sent : List Tower128) (gamma : Tower128)
    (h : sent.length ≠ expected.length) : verifyPrivateChiWires expected sent gamma = false := by
  simp [verifyPrivateChiWires, h]

set_option maxRecDepth 4096 in
/-- Query-bounded hidden-share hybrid at the production 256-bit coin width.
Queries are indexed by the secret share and the (context, party) frame tag.
This is a ROM theorem; replacing this oracle by concrete cSHAKE, or reducing the
legacy 24-byte shell's `advCoinHide` to this game, is not asserted here. -/
theorem production_coin_ro_query_hybrid_bound
    (Q : Nat) (oracle : List UInt8 → List UInt8)
    (programmed : ProductionCoinContext × UInt64 → List UInt8)
    (A : OracleComp (Fin (2 ^ 256) × (ProductionCoinContext × UInt64)) (List UInt8) Bool)
    (hQ : QueryBounded Q A) :
    let base := fun q : Fin (2 ^ 256) × (ProductionCoinContext × UInt64) =>
      oracle (productionCoinCommitFrame q.2.1 q.2.2 (BitVec.ofFin q.1))
    let gap := natAbsDiff (keyedPrfRealAccept (2 ^ 256) base programmed A)
      (keyedPrfIdealAccept (2 ^ 256) base A)
    gap ≤ Q ∧ ratLe (gap, 2 ^ 256) (Q, 2 ^ 256) := by
  intro base gap
  have hb : gap ≤ Q := (hidingAdv_le (2 ^ 256) Q (Nat.two_pow_pos 256)
    base programmed A hQ).1
  refine ⟨hb, ?_⟩
  unfold ratLe
  dsimp only
  exact ⟨Nat.two_pow_pos 256, Nat.two_pow_pos 256, Nat.mul_le_mul_right (2 ^ 256) hb⟩


/-- A two-gate private stream and an actual truncated transmission. -/
theorem witness_private_stream_changed :
    ∃ expected sent : List Tower128, sent ≠ expected ∧
      verifyPrivateChiWires expected sent (towerOne 7) = false := by
  refine ⟨[towerOne 7, towerOne 7], [towerOne 7], ?_, ?_⟩
  · intro h
    have hlen := congrArg List.length h
    cases hlen
  · apply tooth_verifyPrivateChiWires_rejects_truncation
    decide +kernel

#tooth_pair Qsag.verifyPrivateChiWires_any_changed_gate_count vs Qsag.tooth_verifyPrivateChiWires_rejects_truncation
#verify_inhabited Qsag.verifyPrivateChiWires_any_changed_gate_count Qsag.witness_private_stream_changed
#verify_constructive checkRound3ActiveOpen_output

/-! ### Exports for lane threshold-a -/

theorem productionCoinCommit_def (ctx : ProductionCoinContext) (party : UInt64)
    (share : BitVec 256) :
    productionCoinCommit ctx party share =
      cshake256Bytes productionCoinCommitCustom (productionCoinCommitFrame ctx party share) := by
  rfl

theorem productionCoinDerive_def (ctx : ProductionCoinContext) (combined : BitVec 256) :
    productionCoinDerive ctx combined =
      cshake256Bytes productionCoinDeriveCustom
        (encodeMultiFrame [bvToFixedBytes 32 ctx.sessionId, ctx.phaseLabel,
          bvToFixedBytes 32 ctx.transcriptDigest, bvToFixedBytes 32 combined]) := by
  rfl

theorem fixedBytesToBv_of_bvToFixedBytes (L : Nat) (bv : BitVec (8 * L)) :
    fixedBytesToBv L (bvToFixedBytes L bv) = bv :=
  fixedBytesToBv_bvToFixedBytes L bv

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

/-- **Mandatory Pre-Cut Consistency Barrier (`sharedPreCutBarrier`)**:
    Verifies Round-1 commitment binding and `verifyPrivateChiWires` against the private stream
    `r2St.expectedWires`: the frame must carry exactly as many wires as the private computation
    has gates, and the `BBCGGI19` / `BDOZ` Horner accumulators over raw `GF(2^128)` (`Tower128`)
    gate wires must agree at the challenge, strictly before Round-3 cut openings can run. -/
@[expose] def sharedPreCutBarrier (cIdx : Fin 3) (deg : Nat) (pk : SlhPublicKey)
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
        if !(verifyPrivateChiWires r2St.expectedWires sentWires (unpackTower 7 r2St.gammaBits)) then
          .inl .activeConsistencyFailed
        else
          .inr { sentWires := sentWires, expectedWires := r2St.expectedWires,
                 cutShares := ⟨[], [], []⟩ }


/-- Deviations fixed by the public Round-2 wire and the private expected stream,
    before either honest coin share is opened. The same function is used by the
    protocol barrier theorem and the execution game's bad-event extractor. -/
def preCutNonzeroDeltas (cIdx : Fin 3) (deg : Nat) (pk : SlhPublicKey)
    (req : SessionScheduleReq) (cursor : Nat) (corrR1Commit : ByteArray)
    (expectedWires : List Tower128) (corrR2 : List (Nat × ByteArray)) : Option (List Tower128) :=
  match corrR2.find? (fun pr => pr.1 == cIdx.val) with
     | none => none
     | some (_, cWire2) =>
       match parseCorruptRound2Wire deg cWire2 with
       | none => none
       | some (nonceC, sentWires) =>
         if round1NonceCommit pk req cursor cIdx.val nonceC != corrR1Commit then none
         else if sentWires.length ≠ expectedWires.length then none
         else
           let deltas := zipXorTower 7 sentWires expectedWires
           if deltas.any (fun d => decide (d ≠ towerZero 7)) then some deltas
           else none

theorem sharedPreCutBarrier_extract_eq (cIdx : Fin 3) (deg : Nat) (pk : SlhPublicKey)
    (req : SessionScheduleReq) (r2St : RssRound2State)
    (corrR2 : List (Nat × ByteArray)) (r3Init : RssRound3State)
    (hBar : sharedPreCutBarrier cIdx deg pk req r2St corrR2 = .inr r3Init) :
    preCutNonzeroDeltas cIdx deg pk req r2St.cursor r2St.corrR1Commit r2St.expectedWires corrR2 =
      (if r3Init.deltas.any (fun d => decide (d ≠ towerZero 7)) then some r3Init.deltas else none) ∧
    (batchDeviationPoly r3Init.deltas (unpackTower 7 r2St.gammaBits) == towerZero 7) = true ∧
    r3Init.sentWires.length = r3Init.expectedWires.length := by
  unfold preCutNonzeroDeltas
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
        let ews := r2St.expectedWires
        cases hVer : verifyPrivateChiWires r2St.expectedWires sws (unpackTower 7 r2St.gammaBits)
        · rw [hVer] at hBar; simp at hBar
        · rw [hVer] at hBar
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hBar
          have hLenEq : sws.length = ews.length :=
            of_decide_eq_true (Bool.and_eq_true_iff.mp hVer).1
          have hAcc : (bbcggiWireAccumulator sws (unpackTower 7 r2St.gammaBits) ==
              bbcggiWireAccumulator ews (unpackTower 7 r2St.gammaBits)) = true :=
            (Bool.and_eq_true_iff.mp hVer).2
          rw [ite_eq_right (show ¬ (sws.length ≠ r2St.expectedWires.length) from fun h => h hLenEq)]
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



theorem decodeMultiSessionTapes_zero (L : Nat) (ω : Fin (rssMultiSessionCard L 0)) (k : Nat) :
    decodeMultiSessionTapes L 0 ω k = defaultRssSessionTape L := by rfl

theorem decodeMultiSessionTapes_succ (L s : Nat) (ω : Fin (rssMultiSessionCard L (s + 1))) (k : Nat) :
    decodeMultiSessionTapes L (s + 1) ω k =
      let cur := splitFinLeft (rssMultiSessionCard_pos L s) ω
      let rest := splitFinRight (rssMultiSessionCard_pos L s) ω
      match k with
      | 0 => decodeSingleFullTape L cur
      | k' + 1 => decodeMultiSessionTapes L s rest k' := by
  cases k <;> rfl

theorem decodeSingleFullTape_def (L : Nat) (cur : Fin (rssFullSessionCard L)) :
    decodeSingleFullTape L cur =
      decodeRssSessionTape L (splitFinLeft (Nat.two_pow_pos 128) cur) (splitFinRight (Nat.two_pow_pos 128) cur) := by rfl

theorem idFinEquiv_toFun (N : Nat) (x : Fin N) : (idFinEquiv N).toFun x = x := by rfl

theorem decodeTower128PadPoly_def (t : Nat) :
    decodeTower128PadPoly t =
      decodeGenericPadPoly (2 ^ 128) (Nat.two_pow_pos 128) (fun i => unpackTower 7 (BitVec.ofFin i)) t := by rfl

theorem encodeTower128PadPoly_def (t : Nat) :
    encodeTower128PadPoly t =
      encodeGenericPadPoly (2 ^ 128) (fun x => (packTower 7 x).toFin) t := by rfl

theorem SlhSignature.wellTyped_def (p : Fips205Params) (sig : SlhSignature) :
    sig.WellTyped p ↔
      sig.rRand.length = p.n ∧
      sig.forsSig.length = p.k ∧
      (∀ f ∈ sig.forsSig, f.skVal.length = p.n ∧ f.authPath.length = p.a ∧ (∀ u ∈ f.authPath, u.length = p.n)) ∧
      sig.htSig.length = p.d ∧
      (∀ x ∈ sig.htSig, x.wotsSig.length = p.ell ∧ (∀ w ∈ x.wotsSig, w.length = p.n) ∧
        x.authPath.length = p.hp ∧ (∀ u ∈ x.authPath, u.length = p.n)) := Iff.rfl

#export_eqns committedCoin honestCoinOpeningMsgs corruptOpenedCoin round1NonceCommit
  buildHonestRound3Msgs extractPublicRound3HeadByte preCutNonzeroDeltas
  computeHonestChiWord evalReplicatedGateCrossByte reusedFirstSessionTapes
  zipXorTower verifyPrivateChiWires honestSlhWotsMsg

@[simp] theorem fixedBytesToBv_zero (bs : List UInt8) : fixedBytesToBv 0 bs = 0#0 := by rfl
@[simp] theorem fixedBytesToBv_succ_nil (L : Nat) : fixedBytesToBv (L + 1) [] = 0#(8 * (L + 1)) := by rfl
@[simp] theorem fixedBytesToBv_succ_cons (L : Nat) (b : UInt8) (bs : List UInt8) :
    fixedBytesToBv (L + 1) (b :: bs) = ((fixedBytesToBv L bs) ++ b.toBitVec).cast (by omega) := by rfl

theorem finBitVecXorEquiv_toFun_ofFin (W : Nat) (delta : BitVec W) (z : Fin (2 ^ W)) :
    BitVec.ofFin ((finBitVecXorEquiv W delta).toFun z) = BitVec.ofFin z ^^^ delta := by rfl

#export_eqns RssRound3State.deltas xorByteStream

end Qsag
end
