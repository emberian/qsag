module

public import Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf.DkgAndSigning
public import Qsag.Protocol.Threshold.ThresholdMlDsaAndToprf.Ext6RabinField
import Qsag.Math.Primality
import Qsag.Tactic.AssuranceKit

public section

namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
attribute [-instance] Fin.instLinearOrderPackage

set_option autoImplicit false

/-! ## Checked transform and serialization boundaries

The generic helpers imported from `AdvancedMpcAndCreds` are not used below. In particular,
interpolation uses the proved inverse NTT, and LDE length is the source length times blowup.
-/

structure CosetDomain204 where
  blowup : Nat
  shift : Fq204
  root : Fq204

def cosetDomain204Valid (d : CosetDomain204) : Bool :=
  decide (0 < d.blowup) && decide (d.shift ≠ Fq204.zero) &&
  decide (Fq204.pow d.root (256 * d.blowup) = Fq204.one) &&
  decide (((List.range (256 * d.blowup)).map (Fq204.pow d.root)).Nodup)

/-- Interpolate the source NTT evaluations, then evaluate on the validated multiplicative coset.
    Duplicate domain points, zero shift, and zero blowup are rejected. -/
def cosetLde204 (d : CosetDomain204) (evals : Poly256) : Option (List Fq204) :=
  if cosetDomain204Valid d then
    some ((List.range (256 * d.blowup)).map (fun i =>
      evalPoly204 (PolyTree.toList (fips204InvNtt evals))
        (Fq204.mul d.shift (Fq204.pow d.root i))))
  else none

theorem cosetLde204_size {d : CosetDomain204} {evals : Poly256} {out : List Fq204}
    (h : cosetLde204 d evals = some out) :
    out.length = (PolyTree.toList evals).length * d.blowup := by
  unfold cosetLde204 at h
  split at h
  · cases h
    simp only [List.length_map, List.length_range, PolyTree.length_toList]
  · cases h

theorem cosetLde204_ntt (d : CosetDomain204) (p : Poly256)
    (h : cosetDomain204Valid d = true) :
    cosetLde204 d (fips204Ntt p) = some
      ((List.range (256 * d.blowup)).map (fun i =>
        evalPoly204 (PolyTree.toList p) (Fq204.mul d.shift (Fq204.pow d.root i)))) := by
  simp only [cosetLde204, h, ↓reduceIte, fips204InvNtt_ntt]

/-- No power `ζ^d` with `0 < d < 512` has residue `1`: one modular power per exponent. -/
private theorem mldsaZeta_pow_ne_one_check :
    (List.range 512).all (fun d => d == 0 || 1753 ^ d % mldsaQ != 1) = true := by
  decide +kernel

/-- The first 512 powers of `ζ = 1753` are pairwise distinct: `ζ^i = ζ^j` with `i < j < 512`
    gives `ζ^(j-i) = 1` after cancelling `ζ^i` against `ζ^(512-i)`. -/
private theorem mldsaZeta_pow_ne_of_lt {i j : Nat} (hij : i < j) (hj : j < 512) :
    Fq204.pow mldsaZeta i ≠ Fq204.pow mldsaZeta j := by
  intro hEq
  have hInv : Fq204.mul (Fq204.pow mldsaZeta (512 - i)) (Fq204.pow mldsaZeta i) = Fq204.one := by
    rw [← Fq204.pow_add, Nat.sub_add_cancel (Nat.le_of_lt (Nat.lt_trans hij hj)),
      mldsaZeta_pow512_eq_one]
  have hOne : Fq204.pow mldsaZeta (j - i) = Fq204.one := by
    rw [← Fq204.one_mul (Fq204.pow mldsaZeta (j - i)), ← hInv, Fq204.mul_assoc, ← Fq204.pow_add,
      Nat.add_sub_of_le (Nat.le_of_lt hij), ← hEq, hInv]
  have hVal : 1753 ^ (j - i) % mldsaQ = 1 :=
    (Fq204.pow_val mldsaZeta (j - i)).symm.trans (congrArg Fq204.val hOne)
  have hChk : ((j - i) == 0 || 1753 ^ (j - i) % mldsaQ != 1) = true :=
    List.all_eq_true.mp mldsaZeta_pow_ne_one_check (j - i)
      (List.mem_range.mpr (Nat.lt_of_le_of_lt (Nat.sub_le j i) hj))
  rcases Bool.or_eq_true_iff.mp hChk with h0 | hne
  · exact Nat.sub_ne_zero_of_lt hij (beq_iff_eq.mp h0)
  · exact bne_iff_ne.mp hne hVal

private theorem mldsaZeta_pow_injOn {i j : Nat} (hi : i < 512) (hj : j < 512) (hne : i ≠ j) :
    Fq204.pow mldsaZeta i ≠ Fq204.pow mldsaZeta j := by
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact mldsaZeta_pow_ne_of_lt h hj
  · exact fun hEq => mldsaZeta_pow_ne_of_lt h hi hEq.symm

/-- The four validity conditions, stated as propositions about an arbitrary domain. -/
theorem cosetDomain204Valid_of {d : CosetDomain204}
    (hBlowup : 0 < d.blowup) (hShift : d.shift ≠ Fq204.zero)
    (hRoot : Fq204.pow d.root (256 * d.blowup) = Fq204.one)
    (hNodup : ((List.range (256 * d.blowup)).map (Fq204.pow d.root)).Nodup) :
    cosetDomain204Valid d = true := by
  unfold cosetDomain204Valid
  rw [decide_eq_true hBlowup, decide_eq_true hShift, decide_eq_true hRoot, decide_eq_true hNodup]
  rfl

/-- A valid blowup-2 domain exists: the 512th root of unity `1753` with coset shift `7`.
    All 512 domain points are distinct. -/
theorem cosetDomain204_inhabited :
    cosetDomain204Valid ⟨2, Fq204.ofNat 7, mldsaZeta⟩ = true :=
  cosetDomain204Valid_of (by decide) (by decide) mldsaZeta_pow512_eq_one
    (List.pairwise_map.mpr (List.Pairwise.imp_of_mem
      (fun hi hj hne => mldsaZeta_pow_injOn (List.mem_range.mp hi) (List.mem_range.mp hj) hne)
      (Constructive.nodup_range 512)))

theorem tooth_cosetLde204_zero_shift (d : CosetDomain204) (p : Poly256)
    (h : d.shift = Fq204.zero) : cosetLde204 d p = none := by
  simp [cosetLde204, cosetDomain204Valid, h]

/-- Raw-input boundary: unlike a saturating natural subtraction, this rejects every `v ≥ q`. -/
def canonicalNorm204 (bound : Nat) (coeffs : List Nat) : Bool :=
  coeffs.all (fun v => decide (v < mldsaQ ∧ min v (mldsaQ - v) < bound))

theorem canonicalNorm204_sound {b : Nat} {xs : List Nat}
    (h : canonicalNorm204 b xs = true) :
    ∀ v ∈ xs, v < mldsaQ ∧ min v (mldsaQ - v) < b := by
  simpa only [canonicalNorm204, List.all_eq_true, decide_eq_true_eq] using h

theorem tooth_canonicalNorm204_rejects_q : canonicalNorm204 1 [mldsaQ] = false := by
  decide

theorem tooth_canonicalNorm204_noncanonical (v b : Nat) (h : mldsaQ ≤ v) :
    canonicalNorm204 b [v] = false := by
  have hn : ¬ v < mldsaQ := by omega
  simp [canonicalNorm204, hn]

/-- Bounded byte strings are mandatory at the four-byte framing boundary. -/
structure Frame204 where
  bytes : List UInt8
  bounded : bytes.length < 2 ^ 32

def merkleLeafPreimage204 (leaf : Frame204) : List UInt8 :=
  [0] ++ frameBytes leaf.bytes

def merkleNodePreimage204 (left right : Frame204) : List UInt8 :=
  [1] ++ frameBytes left.bytes ++ frameBytes right.bytes

theorem merkleLeafPreimage204_injective {a b : Frame204}
    (h : merkleLeafPreimage204 a = merkleLeafPreimage204 b) : a.bytes = b.bytes := by
  apply FramedBytesCodec.frameBytes_injective a.bounded b.bounded
  exact List.append_cancel_left h

theorem merkleNodePreimage204_injective {a b c d : Frame204}
    (h : merkleNodePreimage204 a b = merkleNodePreimage204 c d) :
    a.bytes = c.bytes ∧ b.bytes = d.bytes := by
  have hp := congrArg List.tail h
  change frameBytes a.bytes ++ frameBytes b.bytes =
    frameBytes c.bytes ++ frameBytes d.bytes at hp
  obtain ⟨hl, hr⟩ := (FramedBytesCodec.prefix_free_injective a.bounded c.bounded).mp hp
  exact ⟨hl, FramedBytesCodec.frameBytes_injective b.bounded d.bounded hr⟩

theorem tooth_merkle204_leaf_node_disjoint (a b c : Frame204) :
    merkleLeafPreimage204 a ≠ merkleNodePreimage204 b c := by
  intro h
  have ht := congrArg List.head? h
  change some (0 : UInt8) = some 1 at ht
  cases ht

/-! ## Concrete FIPS 204 byte verifier

The legacy `mldsaVerify` signature is retained for `MirSpecBridge`. The entry point below
fixes SHAKE, matrix expansion, challenge sampling, packing, and strict signature decoding.
Rejection samplers have an explicit byte budget and return failure on exhaustion; no
modulo fallback or padded challenge is accepted. Proving a sufficient budget for every
SHAKE stream is deliberately not assumed.
-/

private def xorRate168204 (s : KState) (block : List UInt8) : KState :=
  let t := xorRate136 s block
  { t with a17 := t.a17 ^^^ loadLe64 block 17,
           a18 := t.a18 ^^^ loadLe64 block 18,
           a19 := t.a19 ^^^ loadLe64 block 19,
           a20 := t.a20 ^^^ loadLe64 block 20 }

private def pad168204 (bytes : List UInt8) : List UInt8 :=
  let count := 168 - bytes.length % 168
  if count = 1 then bytes ++ [0x9f]
  else bytes ++ [0x1f] ++ List.replicate (count - 2) 0 ++ [0x80]

private def absorb168204 : Nat → KState → List UInt8 → KState
  | 0, s, _ => s
  | n + 1, s, bs => absorb168204 n (keccakF1600 (xorRate168204 s (bs.take 168))) (bs.drop 168)

private def rate168Bytes204 (s : KState) : List UInt8 :=
  rateBlockBytes s ++ encodeNatLeBytes 8 s.a17.toNat ++ encodeNatLeBytes 8 s.a18.toNat ++
    encodeNatLeBytes 8 s.a19.toNat ++ encodeNatLeBytes 8 s.a20.toNat

private def squeeze168204 : Nat → Nat → KState → List UInt8
  | 0, _, _ => []
  | n + 1, count, s =>
    if count ≤ 168 then (rate168Bytes204 s).take count
    else rate168Bytes204 s ++ squeeze168204 n (count - 168) (keccakF1600 s)

def shake128Xof204 (count : Nat) (msg : List UInt8) : List UInt8 :=
  let padded := pad168204 msg
  squeeze168204 (count / 168 + 1) count
    (absorb168204 (padded.length / 168) zeroKState padded)

private def readBits204 (bs : List UInt8) (offset width : Nat) : Nat :=
  ((List.range width).map (fun j =>
    (((bs.getD ((offset + j) / 8) 0).toNat / 2 ^ ((offset + j) % 8)) % 2) * 2 ^ j)).sum

private def sampleBall204Aux (signs : Nat) (i : Nat) (cs : List Fq204) :
    List UInt8 → Option Poly256
  | [] => if i = 256 then some (PolyTree.ofList 8 cs) else none
  | b :: bs =>
    if i = 256 then some (PolyTree.ofList 8 cs)
    else if b.toNat ≤ i then
      let next := (cs.set i (cs.getD b.toNat Fq204.zero)).set b.toNat
        (if signs % 2 = 0 then Fq204.one else Fq204.neg Fq204.one)
      sampleBall204Aux (signs / 2) (i + 1) next bs
    else sampleBall204Aux signs i cs bs

def sampleInBall204 (byteBudget : Nat) (seed : List UInt8) : Option Poly256 :=
  let stream := shake256Xof (8 + byteBudget) seed
  sampleBall204Aux (readBits204 stream 0 64) 217 (List.replicate 256 Fq204.zero) (stream.drop 8)

private def rejNtt204Aux : Nat → Nat → List UInt8 → List Fq204 → Option Poly256
  | 0, _, _, _ => none
  | fuel + 1, count, bs, acc =>
    if count = 256 then some (PolyTree.ofList 8 acc.reverse)
    else match bs with
    | b0 :: b1 :: b2 :: rest =>
      let v := b0.toNat + 256 * b1.toNat + 65536 * (b2.toNat % 128)
      if hv : v < mldsaQ then rejNtt204Aux fuel (count + 1) rest (⟨v, hv⟩ :: acc)
      else rejNtt204Aux fuel count rest acc
    | _ => none

def expandA204 (byteBudget : Nat) (rho : List UInt8) : Option PolyMat4 := do
  if rho.length ≠ 32 then none else do
    let entries ← (List.range 16).mapM (fun ij =>
      rejNtt204Aux (byteBudget + 1) 0
        (shake128Xof204 byteBudget (rho ++ [UInt8.ofNat (ij % 4), UInt8.ofNat (ij / 4)])) [])
    pure (fun i j => fips204InvNtt (entries.getD (4 * i.val + j.val) (PolyTree.zero 8)))

private def hintTree204 : (d : Nat) → List Bool → HintTree d
  | 0, bs => .leaf (bs.headD false)
  | d + 1, bs => .branch (hintTree204 d (bs.take (2 ^ d))) (hintTree204 d (bs.drop (2 ^ d)))

private def decodeHintRows204 (bytes : List UInt8) : Nat → Nat → Nat → Option (List (HintTree 8))
  | 0, _, start =>
    if (bytes.drop start |>.take (80 - start)).all (fun b => b == 0) then some [] else none
  | n + 1, row, start => do
    let stop := (bytes.getD (80 + row) 0).toNat
    if stop < start ∨ 80 < stop then none else do
      let indices := (bytes.drop start |>.take (stop - start)).map UInt8.toNat
      if ¬ indices.Pairwise (· < ·) then none else do
        let rest ← decodeHintRows204 bytes n (row + 1) stop
        pure (hintTree204 8 ((List.range 256).map (fun j => decide (j ∈ indices))) :: rest)

structure DecodedSignature204 where
  challenge : List UInt8
  z : PolyVec4
  hints : Fin 4 → HintTree 8

def decodeSignature204 (sig : List UInt8) : Option DecodedSignature204 := do
  if sig.length ≠ 2420 then none else do
    let hs ← decodeHintRows204 (sig.drop 2336) 4 0 0
    pure
      { challenge := sig.take 32
        z := fun i => PolyTree.ofList 8 ((List.range 256).map (fun j =>
          Fq204.ofInt (131072 - Int.ofNat (readBits204 sig (256 + i.val * 4608 + 18 * j) 18))))
        hints := fun i => hs.getD i.val (hintTree204 8 []) }

/-- Standalone, pure ML-DSA-44 verifier on wire bytes. Budget exhaustion fails closed.
    `t1` is decoded as ten-bit unsigned coefficients and scaled by `2^13` exactly once. -/
def mldsaVerifyBytes204 (byteBudget : Nat) (pk msg ctx sig : List UInt8) : Bool :=
  if pk.length ≠ 1312 ∨ 255 < ctx.length then false else
  match expandA204 byteBudget (pk.take 32), decodeSignature204 sig with
  | some A, some decoded =>
    match sampleInBall204 byteBudget decoded.challenge with
    | none => false
    | some c =>
      let t1Scaled : PolyVec4 := fun i => PolyTree.ofList 8 ((List.range 256).map (fun j =>
        Fq204.ofNat (8192 * readBits204 pk (256 + i.val * 2560 + 10 * j) 10)))
      let mu := shake256Xof 64 (shake256Xof 64 pk ++ [0, UInt8.ofNat ctx.length] ++ ctx ++ msg)
      mldsaVerify mldsa44ChallengeHash (fun _ => c) A t1Scaled mu
        decoded.challenge decoded.z decoded.hints
  | _, _ => false

theorem tooth_mldsaVerifyBytes204_bad_key_length (fuel : Nat) (pk msg ctx sig : List UInt8)
    (h : pk.length ≠ 1312) : mldsaVerifyBytes204 fuel pk msg ctx sig = false := by
  simp [mldsaVerifyBytes204, h]

theorem tooth_decodeSignature204_bad_length (sig : List UInt8) (h : sig.length ≠ 2420) :
    decodeSignature204 sig = none := by
  simp [decodeSignature204, h]


/-! ## Transcript-computed multiplication check

The signing transition below does not receive a success flag. It receives, for every
multiplication it consumes, a list of gates in the NTT domain together with one sacrificial
triple per gate, and computes the verdict from the three values each gate opens. Operands
and products are base-field elements; the challenge and the triple masks are extension
elements, and extension elements are only ever scaled by base-field elements. Uniqueness of
the bad challenge therefore needs only inversion in the base field.

The opened pair `(rho, sigma)` is a bijective image of the triple masks `(a, b)`; `tau` is
zero in every honest execution. The engine's recursive inner-product compression of the same
check additionally multiplies extension elements and so relies on the extension modulus being
irreducible, which the numeric certificate above does not prove. Per-party share views and
the MAC layer are not modelled: the gate values here are the reconstructed ones.
-/

/-- One checked multiplication `z = x * y` with its sacrificial triple `(a, b, c)`. -/
structure SacGate204 where
  x : Fq204
  y : Fq204
  z : Fq204
  a : Ext6Fq204
  b : Fq204
  c : Ext6Fq204

/-- The values opened for one gate. -/
structure SacOpening204 where
  rho : Ext6Fq204
  sigma : Fq204
  tau : Ext6Fq204

def sacOpen204 (chi : Ext6Fq204) (g : SacGate204) : SacOpening204 :=
  { rho := ext6Sub (ext6Scale chi g.x) g.a
    sigma := Fq204.sub g.y g.b
    tau :=
      ext6Sub
        (ext6Sub (ext6Sub (ext6Scale chi g.z) g.c) (ext6Scale g.a (Fq204.sub g.y g.b)))
        (ext6Scale (ext6Sub (ext6Scale chi g.x) g.a) (Fq204.add g.b (Fq204.sub g.y g.b))) }

def sacVerdict204 (o : SacOpening204) : Bool := decide (o.tau = ext6Zero)

def sacAccept204 (chi : Ext6Fq204) (g : SacGate204) : Bool := sacVerdict204 (sacOpen204 chi g)

def sacGateError204 (g : SacGate204) : Fq204 := Fq204.sub g.z (Fq204.mul g.x g.y)

def sacTripleError204 (g : SacGate204) : Ext6Fq204 := ext6Sub g.c (ext6Scale g.a g.b)

/-- The single challenge under which a gate with multiplication error `d ≠ 0` is accepted. -/
def sacBadChallenge204 (g : SacGate204) : Ext6Fq204 :=
  ext6Scale (sacTripleError204 g) (Fq204.inv (sacGateError204 g))

private theorem sac_coord204 (k x y z a b c : Fq204) :
    Fq204.sub (Fq204.sub (Fq204.sub (Fq204.mul k z) c) (Fq204.mul a (Fq204.sub y b)))
        (Fq204.mul (Fq204.sub (Fq204.mul k x) a) (Fq204.add b (Fq204.sub y b))) =
      Fq204.sub (Fq204.mul k (Fq204.sub z (Fq204.mul x y))) (Fq204.sub c (Fq204.mul a b)) := by
  rw [← Fq204.ofInt_nat k, ← Fq204.ofInt_nat x, ← Fq204.ofInt_nat y, ← Fq204.ofInt_nat z,
    ← Fq204.ofInt_nat a, ← Fq204.ofInt_nat b, ← Fq204.ofInt_nat c]
  simp only [Fq204.ofInt_mul, Fq204.ofInt_sub, Fq204.ofInt_add]
  congr 1
  simp only [Int.sub_mul, Int.mul_sub, Int.mul_add, ← Int.mul_assoc]
  omega

theorem fq204_eq_of_sub_eq_zero {a b : Fq204} (h : Fq204.sub a b = Fq204.zero) : a = b := by
  have hc := fq204_sub_add_cancel_left b a
  rw [h, Fq204.add_zero] at hc
  exact hc.symm

theorem fq204_sub_self (a : Fq204) : Fq204.sub a a = Fq204.zero := by
  rw [Fq204.sub_eq_add_neg, Fq204.add_right_neg]

private theorem fq204_sub_sub_self (t r : Fq204) : Fq204.sub t (Fq204.sub t r) = r := by
  rw [← Fq204.ofInt_nat t, ← Fq204.ofInt_nat r]
  simp only [Fq204.ofInt_sub]
  congr 1
  omega

private theorem ext6_sub_sub_self (t r : Ext6Fq204) : ext6Sub t (ext6Sub t r) = r := by
  rcases t with ⟨t0, t1, t2, t3, t4, t5⟩
  rcases r with ⟨r0, r1, r2, r3, r4, r5⟩
  simp only [ext6Sub_eq, fq204_sub_sub_self]

private theorem sac_solve204 {k d t : Fq204} (hd : d ≠ Fq204.zero)
    (h : Fq204.sub (Fq204.mul k d) t = Fq204.zero) : k = Fq204.mul t (Fq204.inv d) := by
  have he := fq204_eq_of_sub_eq_zero h
  rw [← he, Fq204.mul_assoc, Fq204.mul_inv_cancel hd, Fq204.mul_one]

/-- The opened check value is `chi * (z - x*y) - (c - a*b)`. -/
theorem sacOpen204_tau (chi : Ext6Fq204) (g : SacGate204) :
    (sacOpen204 chi g).tau =
      ext6Sub (ext6Scale chi (sacGateError204 g)) (sacTripleError204 g) := by
  rcases chi with ⟨k0, k1, k2, k3, k4, k5⟩
  rcases g with ⟨x, y, z, ⟨a0, a1, a2, a3, a4, a5⟩, b, ⟨c0, c1, c2, c3, c4, c5⟩⟩
  simp only [sacOpen204, sacGateError204, sacTripleError204, ext6Sub_eq, ext6Scale_eq, sac_coord204]

/-- An accepted gate is a correct multiplication unless the challenge is the one bad value
    determined by the gate. The bad value does not depend on the challenge. -/
theorem sacAccept204_sound {chi : Ext6Fq204} {g : SacGate204}
    (h : sacAccept204 chi g = true) :
    g.z = Fq204.mul g.x g.y ∨ chi = sacBadChallenge204 g := by
  unfold sacAccept204 sacVerdict204 at h
  rw [sacOpen204_tau] at h
  have hTau := of_decide_eq_true h
  if hd : sacGateError204 g = Fq204.zero then
    exact Or.inl (fq204_eq_of_sub_eq_zero hd)
  else
    refine Or.inr ?_
    unfold sacBadChallenge204
    generalize sacGateError204 g = d at hTau hd
    generalize sacTripleError204 g = t at hTau
    rcases chi with ⟨k0, k1, k2, k3, k4, k5⟩
    rcases t with ⟨t0, t1, t2, t3, t4, t5⟩
    simp only [ext6Sub_eq, ext6Scale_eq, ext6Zero_eq, Ext6Fq204.mk.injEq] at hTau ⊢
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hTau
    exact ⟨sac_solve204 hd h0, sac_solve204 hd h1, sac_solve204 hd h2,
      sac_solve204 hd h3, sac_solve204 hd h4, sac_solve204 hd h5⟩

/-- A correct gate with a correct triple is accepted under every challenge. -/
theorem sacAccept204_complete (chi : Ext6Fq204) {g : SacGate204}
    (hz : g.z = Fq204.mul g.x g.y) (hc : g.c = ext6Scale g.a g.b) :
    sacAccept204 chi g = true := by
  unfold sacAccept204 sacVerdict204
  rw [sacOpen204_tau]
  apply decide_eq_true
  unfold sacGateError204 sacTripleError204
  rw [hz, hc, fq204_sub_self]
  generalize ext6Scale g.a g.b = t
  rcases chi with ⟨k0, k1, k2, k3, k4, k5⟩
  rcases t with ⟨t0, t1, t2, t3, t4, t5⟩
  simp only [ext6Sub_eq, ext6Scale_eq, ext6Zero_eq, Fq204.mul_zero, fq204_sub_self]

theorem tooth_sacAccept204_rejects_corrupt {chi : Ext6Fq204} {g : SacGate204}
    (hz : g.z ≠ Fq204.mul g.x g.y) (hchi : chi ≠ sacBadChallenge204 g) :
    sacAccept204 chi g = false := by
  cases h : sacAccept204 chi g with
  | false => rfl
  | true =>
    rcases sacAccept204_sound h with hg | hb
    · exact False.elim (hz hg)
    · exact False.elim (hchi hb)

/-- Why the challenge must be sampled after the gate values are fixed: a prover who knows
    the challenge in advance passes the check on a wrong product. -/
theorem sac204_predicted_challenge_accepts_corrupt {g : SacGate204}
    (hd : sacGateError204 g ≠ Fq204.zero) :
    sacAccept204 (sacBadChallenge204 g) g = true := by
  unfold sacAccept204 sacVerdict204
  rw [sacOpen204_tau]
  apply decide_eq_true
  unfold sacBadChallenge204
  generalize sacGateError204 g = d at hd
  generalize sacTripleError204 g = t
  rcases t with ⟨t0, t1, t2, t3, t4, t5⟩
  simp only [ext6Sub_eq, ext6Scale_eq, ext6Zero_eq, Fq204.mul_assoc, Fq204.inv_mul_cancel hd,
    Fq204.mul_one, fq204_sub_self]

/-- For a fixed challenge and fixed operands, the triple masks `(a, b)` and the opened pair
    `(rho, sigma)` determine each other. Uniform masks give a uniform opening. -/
def sacOpeningMaskEquiv204 (chi : Ext6Fq204) (x y : Fq204) :
    SimpleEquiv (Ext6Fq204 × Fq204) (Ext6Fq204 × Fq204) where
  toFun m := (ext6Sub (ext6Scale chi x) m.1, Fq204.sub y m.2)
  invFun o := (ext6Sub (ext6Scale chi x) o.1, Fq204.sub y o.2)
  left_inv m := by
    rcases m with ⟨a, b⟩
    simp only [ext6_sub_sub_self, fq204_sub_sub_self]
  right_inv o := by
    rcases o with ⟨r, s⟩
    simp only [ext6_sub_sub_self, fq204_sub_sub_self]

theorem sacOpen204_masked (chi : Ext6Fq204) (g : SacGate204) :
    ((sacOpen204 chi g).rho, (sacOpen204 chi g).sigma) =
      (sacOpeningMaskEquiv204 chi g.x g.y).toFun (g.a, g.b) := by
  rfl

def sacAcceptAll204 (chi : Ext6Fq204) (gs : List SacGate204) : Bool :=
  gs.all (sacAccept204 chi)

/-- Batch soundness: either every gate is a correct multiplication, or the challenge lies
    in a list of at most `gs.length` values fixed by the gates alone. -/
theorem sacAcceptAll204_sound {chi : Ext6Fq204} :
    ∀ {gs : List SacGate204}, sacAcceptAll204 chi gs = true →
      (∀ g ∈ gs, g.z = Fq204.mul g.x g.y) ∨ chi ∈ gs.map sacBadChallenge204
  | [], _ => Or.inl (fun _ hg => nomatch hg)
  | g :: gs, h => by
    unfold sacAcceptAll204 at h
    simp only [List.all_cons, Bool.and_eq_true] at h
    rcases sacAccept204_sound h.1 with hg | hb
    · rcases sacAcceptAll204_sound (gs := gs) h.2 with ht | hb
      · refine Or.inl ?_
        intro g' hg'
        rcases List.mem_cons.mp hg' with rfl | hin
        · exact hg
        · exact ht g' hin
      · exact Or.inr (.tail _ hb)
    · subst hb
      exact Or.inr (.head _)

theorem sacBadChallenges204_length (gs : List SacGate204) :
    (gs.map sacBadChallenge204).length = gs.length :=
  List.length_map _

/-- The 256 NTT-domain slots of a claimed ring product `z = x * y`. -/
def nttSlots204 (x y z : Poly256) : List (Fq204 × Fq204 × Fq204) :=
  (PolyTree.toList (fips204Ntt x)).zip
    ((PolyTree.toList (fips204Ntt y)).zip (PolyTree.toList (fips204Ntt z)))

private theorem zip3_append204 {d : Nat} (p0 p1 q0 q1 r0 r1 : PolyTree d) :
    (PolyTree.toList p0 ++ PolyTree.toList p1).zip
        ((PolyTree.toList q0 ++ PolyTree.toList q1).zip
          (PolyTree.toList r0 ++ PolyTree.toList r1)) =
      (PolyTree.toList p0).zip ((PolyTree.toList q0).zip (PolyTree.toList r0)) ++
        (PolyTree.toList p1).zip ((PolyTree.toList q1).zip (PolyTree.toList r1)) := by
  have hq : (PolyTree.toList q0).length = (PolyTree.toList r0).length := by
    rw [PolyTree.length_toList, PolyTree.length_toList]
  have hp : (PolyTree.toList p0).length =
      ((PolyTree.toList q0).zip (PolyTree.toList r0)).length := by
    rw [List.length_zip, PolyTree.length_toList, PolyTree.length_toList,
      PolyTree.length_toList, Nat.min_self]
  rw [List.zip_append hq, List.zip_append hp]

private theorem pointwiseMul_of_slots204 : ∀ {d : Nat} (p q r : PolyTree d),
    (∀ m ∈ (PolyTree.toList p).zip ((PolyTree.toList q).zip (PolyTree.toList r)),
      m.2.2 = Fq204.mul m.1 m.2.1) → PolyTree.pointwiseMul p q = r
  | 0, .leaf a, .leaf b, .leaf c, h => by
    have hm := h (a, b, c) (.head _)
    simp only [PolyTree.pointwiseMul]
    exact congrArg PolyTree.leaf hm.symm
  | d + 1, .branch p0 p1, .branch q0 q1, .branch r0 r1, h => by
    simp only [PolyTree.toList] at h
    rw [zip3_append204] at h
    simp only [PolyTree.pointwiseMul]
    rw [pointwiseMul_of_slots204 p0 q0 r0 (fun m hm => h m (List.mem_append_left _ hm)),
      pointwiseMul_of_slots204 p1 q1 r1 (fun m hm => h m (List.mem_append_right _ hm))]

private theorem slots_of_pointwiseMul204 : ∀ {d : Nat} (p q : PolyTree d)
    (m : Fq204 × Fq204 × Fq204),
    m ∈ (PolyTree.toList p).zip
      ((PolyTree.toList q).zip (PolyTree.toList (PolyTree.pointwiseMul p q))) →
      m.2.2 = Fq204.mul m.1 m.2.1
  | 0, .leaf a, .leaf b, m, hm => by
    have he : m = (a, b, Fq204.mul a b) := by
      rcases hm with _ | ⟨_, hnil⟩
      · rfl
      · exact nomatch hnil
    rw [he]
  | d + 1, .branch p0 p1, .branch q0 q1, m, hm => by
    simp only [PolyTree.toList, PolyTree.pointwiseMul] at hm
    rw [zip3_append204] at hm
    rcases List.mem_append.mp hm with h0 | h1
    · exact slots_of_pointwiseMul204 p0 q0 m h0
    · exact slots_of_pointwiseMul204 p1 q1 m h1

def sacGateOperands204 (g : SacGate204) : Fq204 × Fq204 × Fq204 := (g.x, g.y, g.z)

/-- The gate list is bound to the polynomials the signer actually consumes. -/
def sacBinds204 (gs : List SacGate204) (x y z : Poly256) : Bool :=
  decide (gs.map sacGateOperands204 = nttSlots204 x y z)

/-- Checked ring product: binding plus the sacrifice verdict over all 256 slots. -/
def sacProductOk204 (chi : Ext6Fq204) (gs : List SacGate204) (x y z : Poly256) : Bool :=
  sacBinds204 gs x y z && sacAcceptAll204 chi gs

theorem sacPolyProduct204_sound {chi : Ext6Fq204} {gs : List SacGate204} {x y z : Poly256}
    (h : sacProductOk204 chi gs x y z = true) :
    z = negacyclicMul x y ∨ chi ∈ gs.map sacBadChallenge204 := by
  unfold sacProductOk204 at h
  simp only [Bool.and_eq_true] at h
  rcases sacAcceptAll204_sound h.2 with hAll | hBad
  · refine Or.inl ?_
    have hSlots : gs.map sacGateOperands204 = nttSlots204 x y z := of_decide_eq_true h.1
    apply fips204Ntt_injective
    rw [fips204Ntt_negacyclicMul]
    refine (pointwiseMul_of_slots204 _ _ _ ?_).symm
    intro m hm
    have hm' : m ∈ gs.map sacGateOperands204 := by
      rw [hSlots]
      exact hm
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hm'
    exact hAll g hg
  · exact Or.inr hBad

/-- Honest gate list for `z = x * y`, with triple masks `(a, b)` and `c = a * b`. -/
def sacHonestGates204 (a : Ext6Fq204) (b : Fq204) (x y : Poly256) : List SacGate204 :=
  (nttSlots204 x y (negacyclicMul x y)).map
    (fun m => { x := m.1, y := m.2.1, z := m.2.2, a := a, b := b, c := ext6Scale a b })

private theorem map_operands_honest204 (a : Ext6Fq204) (b : Fq204) :
    ∀ ms : List (Fq204 × Fq204 × Fq204),
      (ms.map (fun m =>
        ({ x := m.1, y := m.2.1, z := m.2.2, a := a, b := b, c := ext6Scale a b } : SacGate204))).map
          sacGateOperands204 = ms
  | [] => rfl
  | m :: ms => by
    rw [List.map_cons, List.map_cons, map_operands_honest204 a b ms]
    rfl

theorem sacHonestGates204_ok (chi a : Ext6Fq204) (b : Fq204) (x y : Poly256) :
    sacProductOk204 chi (sacHonestGates204 a b x y) x y (negacyclicMul x y) = true := by
  unfold sacProductOk204
  rw [Bool.and_eq_true]
  refine ⟨?_, ?_⟩
  · unfold sacBinds204 sacHonestGates204
    exact decide_eq_true (map_operands_honest204 a b _)
  · unfold sacAcceptAll204 sacHonestGates204
    rw [List.all_eq_true]
    intro g hg
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hg
    refine sacAccept204_complete chi ?_ rfl
    have hm' : m ∈ (PolyTree.toList (fips204Ntt x)).zip
        ((PolyTree.toList (fips204Ntt y)).zip
          (PolyTree.toList (PolyTree.pointwiseMul (fips204Ntt x) (fips204Ntt y)))) := by
      rw [← fips204Ntt_negacyclicMul]
      exact hm
    exact slots_of_pointwiseMul204 _ _ m hm'

/-- Sacrifice transcript for the twelve secret-dependent ring products of one signing
    attempt. `w = A * y` is a public-matrix image of the shared nonce and is recomputed. -/
structure RssSacrificeTranscript204 where
  cs1 : Fin 4 → List SacGate204
  cs2 : Fin 4 → List SacGate204
  ct0 : Fin 4 → List SacGate204

/-- Challenges under which some corrupted product of this transcript would be accepted.
    The list is a function of the gate values alone. -/
def rssSacrificeBadChallenges204 (T : RssSacrificeTranscript204) : List Ext6Fq204 :=
  (List.finRange 4).flatMap
    (fun i => (T.cs1 i ++ T.cs2 i ++ T.ct0 i).map sacBadChallenge204)

private def fin4All204 (f : Fin 4 → Bool) : Bool :=
  f ⟨0, by decide⟩ && f ⟨1, by decide⟩ && f ⟨2, by decide⟩ && f ⟨3, by decide⟩

private theorem fin4All204_true {f : Fin 4 → Bool} (h : fin4All204 f = true) :
    ∀ i, f i = true := by
  unfold fin4All204 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  intro i
  rcases i with ⟨idx, hidx⟩
  have hCases : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by omega
  rcases hCases with rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3

private theorem fin4All204_of_forall {f : Fin 4 → Bool} (h : ∀ i, f i = true) :
    fin4All204 f = true := by
  unfold fin4All204
  simp only [h, Bool.and_self]

def rssSacrificedProductsValid
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204) : Bool :=
  polyVec4EqBool inp.products.w (matVecMul4 st.A (rssSumVec4List inp.ySubsets)) &&
  fin4All204 (fun i => sacProductOk204 chi (T.cs1 i)
    (sampleInBall (chalHash inp.mu
      (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inp.ySubsets)))))
    (rssSumVec4List st.s1Subsets i) (inp.products.cs1 i)) &&
  fin4All204 (fun i => sacProductOk204 chi (T.cs2 i)
    (sampleInBall (chalHash inp.mu
      (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inp.ySubsets)))))
    (rssSumVec4List st.s2Subsets i) (inp.products.cs2 i)) &&
  fin4All204 (fun i => sacProductOk204 chi (T.ct0 i)
    (sampleInBall (chalHash inp.mu
      (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inp.ySubsets)))))
    (power2RoundLowVec4 (addVec4 (matVecMul4 st.A (rssSumVec4List st.s1Subsets))
      (rssSumVec4List st.s2Subsets)) i) (inp.products.ct0 i))

private theorem sacVec204_sound {chi : Ext6Fq204} {gs : Fin 4 → List SacGate204}
    {c : Poly256} {s p : PolyVec4} {bad : List Ext6Fq204}
    (hbad : ∀ i, ∀ k ∈ (gs i).map sacBadChallenge204, k ∈ bad)
    (h : fin4All204 (fun i => sacProductOk204 chi (gs i) c (s i) (p i)) = true) :
    p = mulPolyVec4 c s ∨ chi ∈ bad := by
  have step : ∀ i : Fin 4, p i = negacyclicMul c (s i) ∨ chi ∈ bad := by
    intro i
    have hok : sacProductOk204 chi (gs i) c (s i) (p i) = true := fin4All204_true h i
    rcases sacPolyProduct204_sound hok with hz | hb
    · exact Or.inl hz
    · exact Or.inr (hbad i _ hb)
  rcases step ⟨0, by decide⟩ with h0 | hb
  · rcases step ⟨1, by decide⟩ with h1 | hb
    · rcases step ⟨2, by decide⟩ with h2 | hb
      · rcases step ⟨3, by decide⟩ with h3 | hb
        · refine Or.inl ?_
          funext i
          rcases i with ⟨idx, hidx⟩
          have hCases : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by omega
          rcases hCases with rfl | rfl | rfl | rfl
          · exact h0
          · exact h1
          · exact h2
          · exact h3
        · exact Or.inr hb
      · exact Or.inr hb
    · exact Or.inr hb
  · exact Or.inr hb

/-- The transcript-computed verdict implies the exact product relation, except when the
    challenge is one of the bad values fixed by the transcript. -/
theorem rssSacrificedProductsValid_sound
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204)
    (h : rssSacrificedProductsValid chalHash sampleInBall st inp chi T = true) :
    rssProductsValid chalHash sampleInBall st inp = true ∨
      chi ∈ rssSacrificeBadChallenges204 T := by
  unfold rssSacrificedProductsValid at h
  simp only [Bool.and_eq_true, polyVec4EqBool_eq_true_iff] at h
  obtain ⟨⟨⟨hw, h1⟩, h2⟩, h3⟩ := h
  have b1 : ∀ i, ∀ k ∈ (T.cs1 i).map sacBadChallenge204,
      k ∈ rssSacrificeBadChallenges204 T := fun i k hk =>
    List.mem_flatMap.mpr ⟨i, List.mem_finRange i, by
      rw [List.map_append, List.map_append]
      exact List.mem_append_left _ (List.mem_append_left _ hk)⟩
  have b2 : ∀ i, ∀ k ∈ (T.cs2 i).map sacBadChallenge204,
      k ∈ rssSacrificeBadChallenges204 T := fun i k hk =>
    List.mem_flatMap.mpr ⟨i, List.mem_finRange i, by
      rw [List.map_append, List.map_append]
      exact List.mem_append_left _ (List.mem_append_right _ hk)⟩
  have b3 : ∀ i, ∀ k ∈ (T.ct0 i).map sacBadChallenge204,
      k ∈ rssSacrificeBadChallenges204 T := fun i k hk =>
    List.mem_flatMap.mpr ⟨i, List.mem_finRange i, by
      rw [List.map_append, List.map_append]
      exact List.mem_append_right _ hk⟩
  rcases sacVec204_sound b1 h1 with e1 | hb
  · rcases sacVec204_sound b2 h2 with e2 | hb
    · rcases sacVec204_sound b3 h3 with e3 | hb
      · refine Or.inl ?_
        rw [rssProductsValid.public_eq_1]
        simp only [Bool.and_eq_true, polyVec4EqBool_eq_true_iff]
        exact ⟨⟨⟨hw, e1⟩, e2⟩, e3⟩
      · exact Or.inr hb
    · exact Or.inr hb
  · exact Or.inr hb

theorem tooth_rssSacrificedProductsValid_corrupt
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204)
    (hbad : inp.products ≠ rssComputeProducts chalHash sampleInBall st inp.mu inp.ySubsets)
    (hchi : chi ∉ rssSacrificeBadChallenges204 T) :
    rssSacrificedProductsValid chalHash sampleInBall st inp chi T = false := by
  cases h : rssSacrificedProductsValid chalHash sampleInBall st inp chi T with
  | false => rfl
  | true =>
    rcases rssSacrificedProductsValid_sound chalHash sampleInBall st inp chi T h with hv | hb
    · exact False.elim (hbad ((rssProductsValid_eq_true_iff chalHash sampleInBall st inp).mp hv))
    · exact False.elim (hchi hb)

/-- Honest transcript for an attempt, with triple masks `(a, b)`. -/
def rssHonestSacrifice204
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (a : Ext6Fq204) (b : Fq204) : RssSacrificeTranscript204 :=
  { cs1 := fun i => sacHonestGates204 a b
      (sampleInBall (chalHash inp.mu
        (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inp.ySubsets)))))
      (rssSumVec4List st.s1Subsets i)
    cs2 := fun i => sacHonestGates204 a b
      (sampleInBall (chalHash inp.mu
        (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inp.ySubsets)))))
      (rssSumVec4List st.s2Subsets i)
    ct0 := fun i => sacHonestGates204 a b
      (sampleInBall (chalHash inp.mu
        (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inp.ySubsets)))))
      (power2RoundLowVec4 (addVec4 (matVecMul4 st.A (rssSumVec4List st.s1Subsets))
        (rssSumVec4List st.s2Subsets)) i) }

/-- The check is satisfiable: correct products with the honest transcript pass under every
    challenge and every choice of triple masks. -/
theorem rssSacrificedProductsValid_complete
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (chi a : Ext6Fq204) (b : Fq204)
    (hp : inp.products = rssComputeProducts chalHash sampleInBall st inp.mu inp.ySubsets) :
    rssSacrificedProductsValid chalHash sampleInBall st inp chi
      (rssHonestSacrifice204 chalHash sampleInBall st inp a b) = true := by
  unfold rssSacrificedProductsValid
  rw [hp]
  simp only [Bool.and_eq_true, polyVec4EqBool_eq_true_iff]
  refine ⟨⟨⟨rfl, ?_⟩, ?_⟩, ?_⟩
  · exact fin4All204_of_forall (fun i => sacHonestGates204_ok chi a b _ _)
  · exact fin4All204_of_forall (fun i => sacHonestGates204_ok chi a b _ _)
  · exact fin4All204_of_forall (fun i => sacHonestGates204_ok chi a b _ _)

/-- Signing transition gated by the transcript-computed verdict. No exact-product oracle
    is consulted: the consumed products are whatever the sacrifice accepted. -/
@[expose] def rssSacrificedSignStep
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204) :
    StepOutcome RssMlDsaSignerState
      (RssSignPublicAbortView × Option ThresholdSignSig)
      RssPreOpenAbortReason :=
  match decide (inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt) with
  | false => .err st .attemptReplay
  | true =>
    match rssSacrificedProductsValid chalHash sampleInBall st inp chi T with
    | false => .err { st with nextAttempt := st.nextAttempt + 1 } .mpcSacrificeFailed
    | true => rssSignCore chalHash { st with nextAttempt := st.nextAttempt + 1 } inp

theorem rssSacrificedSignStep_eq_of_valid
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204)
    (h : rssSacrificedProductsValid chalHash sampleInBall st inp chi T = true)
    (hv : rssProductsValid chalHash sampleInBall st inp = true) :
    rssSacrificedSignStep chalHash sampleInBall st inp chi T =
      rssThresholdSignStep chalHash sampleInBall st inp := by
  unfold rssSacrificedSignStep rssThresholdSignStep
  rw [h, hv]
  cases decide (inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt) <;> rfl

/-- The sacrificed transition refines the exact-product reference transition, except on the
    bad-challenge event. -/
theorem rssSacrificedSignStep_refines
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204)
    (h : rssSacrificedProductsValid chalHash sampleInBall st inp chi T = true) :
    rssSacrificedSignStep chalHash sampleInBall st inp chi T =
        rssThresholdSignStep chalHash sampleInBall st inp ∨
      chi ∈ rssSacrificeBadChallenges204 T := by
  rcases rssSacrificedProductsValid_sound chalHash sampleInBall st inp chi T h with hv | hb
  · exact Or.inl (rssSacrificedSignStep_eq_of_valid chalHash sampleInBall st inp chi T h hv)
  · exact Or.inr hb

private theorem rssSacrificedSignStep_ok_valid
    {chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8}
    {sampleInBall : List UInt8 → Poly256}
    {st st' : RssMlDsaSignerState} {inp : RssMlDsaAttemptInput}
    {chi : Ext6Fq204} {T : RssSacrificeTranscript204}
    {out : RssSignPublicAbortView × Option ThresholdSignSig}
    (hok : rssSacrificedSignStep chalHash sampleInBall st inp chi T = .ok st' out) :
    rssSacrificedProductsValid chalHash sampleInBall st inp chi T = true := by
  cases hv : rssSacrificedProductsValid chalHash sampleInBall st inp chi T with
  | true => rfl
  | false =>
    unfold rssSacrificedSignStep at hok
    rw [hv] at hok
    cases hg : decide (inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt) with
    | false => rw [hg] at hok; cases hok
    | true => rw [hg] at hok; cases hok

private theorem rssSacrificedSignStep_released
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204) :
    rssStepReleased204 (rssSacrificedSignStep chalHash sampleInBall st inp chi T) =
      if (decide (inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt) &&
          rssSacrificedProductsValid chalHash sampleInBall st inp chi T) = true then
        rssStepReleased204
          (rssSignCore chalHash { st with nextAttempt := st.nextAttempt + 1 } inp)
      else none := by
  unfold rssSacrificedSignStep
  cases hg : decide (inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt) with
  | false => rfl
  | true =>
    cases hv : rssSacrificedProductsValid chalHash sampleInBall st inp chi T with
    | false => rfl
    | true => rfl

/-- The released signature does not depend on the masks the caller selected. -/
theorem rssSacrificedSignStep_released_mask_independent
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204) (maskW maskZ maskLow : PolyVec4) :
    rssStepReleased204 (rssSacrificedSignStep chalHash sampleInBall st
        (rssRemask204 inp maskW maskZ maskLow) chi T) =
      rssStepReleased204 (rssSacrificedSignStep chalHash sampleInBall st inp chi T) := by
  have hc : (decide ((rssRemask204 inp maskW maskZ maskLow).epoch = st.epoch ∧
        (rssRemask204 inp maskW maskZ maskLow).attempt = st.nextAttempt) &&
      rssSacrificedProductsValid chalHash sampleInBall st
        (rssRemask204 inp maskW maskZ maskLow) chi T) =
      (decide (inp.epoch = st.epoch ∧ inp.attempt = st.nextAttempt) &&
        rssSacrificedProductsValid chalHash sampleInBall st inp chi T) := by
    rw [rssRemask204.public_eq_1]
    rfl
  rw [rssSacrificedSignStep_released, rssSacrificedSignStep_released, hc,
    rssSignCore_released_mask_independent]

/-! ## Durable reservation composed with checked signing

The durable record below contains both the existing epoch journal and exact nonce material.
Keeping the material (rather than just an attempt identifier or its hash) makes non-reuse
independent of a hash-collision assumption. A real store must persist both fields atomically.
The disk outcome is an environment event, not a protocol-validation input.
-/

structure RssDurableDisk204 where
  journal : DurableNonceBurnStore
  burnedNonces : List (List UInt8)

structure RssDurableSigner204 where
  key : RssMlDsaSignerState
  disk : RssDurableDisk204

inductive RssDiskOutcome204 where
  | committed
  | failed
  deriving DecidableEq

def rssNonceMaterial204 (inp : RssMlDsaAttemptInput) : List UInt8 :=
  encodePolyVec4Bytes (rssSumVec4List inp.ySubsets)

/-- Reserve before running any check or releasing any signing output. The nonce ledger is
    global to this key, so changing the session, epoch, attempt, or share decomposition does
    not permit reuse of the aggregate nonce. -/
def rssDurableReserve204 (party : UInt16) (diskResult : RssDiskOutcome204)
    (st : RssDurableSigner204) (inp : RssMlDsaAttemptInput) : Bool × RssDurableSigner204 :=
  if inp.epoch ≠ st.key.epoch ∨ inp.attempt ≠ st.key.nextAttempt ∨
      2 ^ 64 ≤ inp.epoch ∨ 2 ^ 32 ≤ inp.attempt ∨ rssNonceMaterial204 inp ∈ st.disk.burnedNonces then
    (false, st)
  else
    match durableBurnReserve st.disk.journal party (UInt64.ofNat inp.epoch)
        inp.sessionId (UInt32.ofNat inp.attempt) (decide (diskResult = .committed)) with
    | (true, journal) =>
      (true,
        { key := { st.key with
            epoch := st.key.epoch + 1
            nextAttempt := st.key.nextAttempt + 1 }
          disk :=
            { journal := journal
              burnedNonces := rssNonceMaterial204 inp :: st.disk.burnedNonces } })
    | (false, journal) =>
      (false,
        { key := st.key
          disk :=
            { journal := journal
              burnedNonces := st.disk.burnedNonces } })

/-- Only a final signature escapes the durable boundary. Rejected attempts expose neither
    individual norms nor the masked vectors of the reference transition. The reservation is
    evaluated first; the sacrificed transition's output is discarded unless it succeeded. -/
def rssDurableSign204
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (party : UInt16) (diskResult : RssDiskOutcome204)
    (st : RssDurableSigner204) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204) :
    RssDurableSigner204 × Option ThresholdSignSig :=
  ((rssDurableReserve204 party diskResult st inp).2,
    match (rssDurableReserve204 party diskResult st inp).1 with
    | false => none
    | true =>
      rssStepReleased204 (rssSacrificedSignStep chalHash sampleInBall st.key inp chi T))

/-- The durable signer released `sig` for this attempt. -/
def RssDurableReleased204
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (party : UInt16) (diskResult : RssDiskOutcome204)
    (st : RssDurableSigner204) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204) (sig : ThresholdSignSig) : Prop :=
  (rssDurableSign204 chalHash sampleInBall party diskResult st inp chi T).2 = some sig

/-- A crash loses volatile memory. The epoch is rebuilt from the journal, the in-epoch
    attempt counter restarts, and the burned-nonce ledger is exactly what was on disk. -/
def rssDurableRecover204 (party : UInt16) (st : RssDurableSigner204) : RssDurableSigner204 :=
  { key := { st.key with
      epoch := persistedNextEpochNat st.disk.journal.keyId party st.disk.journal.burns
      nextAttempt := 0 }
    disk := st.disk }

theorem rssDurableReserve204_burns {party : UInt16} {result : RssDiskOutcome204}
    {st : RssDurableSigner204} {inp : RssMlDsaAttemptInput}
    (h : (rssDurableReserve204 party result st inp).1 = true) :
    (rssDurableReserve204 party result st inp).2.disk.burnedNonces =
      rssNonceMaterial204 inp :: st.disk.burnedNonces := by
  unfold rssDurableReserve204 at h ⊢
  split
  · rename_i hc
    rw [ite_true_of hc] at h
    cases h
  · rename_i hc
    rw [ite_false_of hc] at h
    split
    · rfl
    · rename_i hm
      rw [hm] at h
      cases h

theorem rssDurableReserve204_monotone (party : UInt16) (result : RssDiskOutcome204)
    (st : RssDurableSigner204) (inp : RssMlDsaAttemptInput) :
    ∀ material ∈ st.disk.burnedNonces,
      material ∈ (rssDurableReserve204 party result st inp).2.disk.burnedNonces := by
  intro material hm
  unfold rssDurableReserve204
  split
  · exact hm
  · split
    · exact .tail _ hm
    · exact hm

theorem tooth_rssDurableReserve204_nonce_replay (party : UInt16) (result : RssDiskOutcome204)
    (st : RssDurableSigner204) (inp : RssMlDsaAttemptInput)
    (h : rssNonceMaterial204 inp ∈ st.disk.burnedNonces) :
    (rssDurableReserve204 party result st inp).1 = false := by
  unfold rssDurableReserve204
  rw [ite_true_of (Or.inr (Or.inr (Or.inr (Or.inr h))))]

/-- A failed durable write refuses the reservation, whatever the journal contained. -/
theorem rssDurableReserve204_failed_write (party : UInt16)
    (st : RssDurableSigner204) (inp : RssMlDsaAttemptInput) :
    (rssDurableReserve204 party .failed st inp).1 = false := by
  unfold rssDurableReserve204
  split
  · rfl
  · have hw := durableBurnReserve_failed_write st.disk.journal party (UInt64.ofNat inp.epoch)
      inp.sessionId (UInt32.ofNat inp.attempt)
    have hd : decide (RssDiskOutcome204.failed = RssDiskOutcome204.committed) = false := by decide
    rw [hd]
    split
    · rename_i hm
      rw [hm] at hw
      cases hw
    · rfl

/-- The durable state returned by signing is exactly the state committed by reservation. -/
theorem rssDurableSign204_state
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256) (party : UInt16) (result : RssDiskOutcome204)
    (st : RssDurableSigner204) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204) :
    (rssDurableSign204 chalHash sampleInBall party result st inp chi T).1 =
      (rssDurableReserve204 party result st inp).2 := by
  rfl

/-- No reservation, no output: a refused reservation releases nothing. -/
theorem rssDurableSign204_none_of_refused
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256) (party : UInt16) (result : RssDiskOutcome204)
    (st : RssDurableSigner204) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204)
    (h : (rssDurableReserve204 party result st inp).1 = false) :
    (rssDurableSign204 chalHash sampleInBall party result st inp chi T).2 = none := by
  unfold rssDurableSign204
  dsimp only
  rw [h]

theorem rssDurableSign204_reserved_of_release
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (party : UInt16) (result : RssDiskOutcome204)
    (st : RssDurableSigner204) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204) (sig : ThresholdSignSig)
    (h : RssDurableReleased204 chalHash sampleInBall party result st inp chi T sig) :
    (rssDurableReserve204 party result st inp).1 = true := by
  cases hr : (rssDurableReserve204 party result st inp).1 with
  | true => rfl
  | false =>
    unfold RssDurableReleased204 at h
    rw [rssDurableSign204_none_of_refused chalHash sampleInBall party result st inp chi T hr] at h
    cases h

theorem rssDurableSign204_release_burned
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (party : UInt16) (result : RssDiskOutcome204)
    (st : RssDurableSigner204) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204) (sig : ThresholdSignSig)
    (h : RssDurableReleased204 chalHash sampleInBall party result st inp chi T sig) :
    rssNonceMaterial204 inp ∈
      (rssDurableSign204 chalHash sampleInBall party result st inp chi T).1.disk.burnedNonces := by
  rw [rssDurableSign204_state,
    rssDurableReserve204_burns
      (rssDurableSign204_reserved_of_release chalHash sampleInBall party result st inp chi T sig h)]
  exact .head _

/-- Every released signature verifies under the signer's public key, unless the sacrifice
    challenge is one of the bad values fixed by the transcript. -/
theorem rssDurableSign204_release_verifies
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (party : UInt16) (result : RssDiskOutcome204)
    (st : RssDurableSigner204) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204) (sig : ThresholdSignSig)
    (h : RssDurableReleased204 chalHash sampleInBall party result st inp chi T sig) :
    mldsaVerify chalHash sampleInBall st.key.A
        (power2RoundHighVec4 (addVec4 (matVecMul4 st.key.A (rssSumVec4List st.key.s1Subsets))
          (rssSumVec4List st.key.s2Subsets)))
        inp.mu sig.cTilde sig.z sig.h = true ∨
      chi ∈ rssSacrificeBadChallenges204 T := by
  have hres := rssDurableSign204_reserved_of_release chalHash sampleInBall party result st inp chi T sig h
  unfold RssDurableReleased204 rssDurableSign204 at h
  dsimp only at h
  rw [hres] at h
  dsimp only at h
  cases hstep : rssSacrificedSignStep chalHash sampleInBall st.key inp chi T with
  | err next reason => rw [hstep] at h; cases h
  | ok next out =>
    rw [hstep] at h
    rcases out with ⟨view, msig⟩
    have hsig : msig = some sig := h
    subst hsig
    rcases rssSacrificedSignStep_refines chalHash sampleInBall st.key inp chi T
        (rssSacrificedSignStep_ok_valid hstep) with heq | hb
    · rw [heq] at hstep
      exact Or.inl ((rssThresholdSignStep_ok_meta hstep).2.2.2.2.2 sig rfl).2.2
    · exact Or.inr hb

/-- The released value does not depend on the masks the caller selected, so a zero or
    otherwise chosen mask cannot move information across the durable boundary. -/
theorem rssDurableSign204_mask_independent
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (party : UInt16) (result : RssDiskOutcome204)
    (st : RssDurableSigner204) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204) (maskW maskZ maskLow : PolyVec4) :
    (rssDurableSign204 chalHash sampleInBall party result st
        (rssRemask204 inp maskW maskZ maskLow) chi T).2 =
      (rssDurableSign204 chalHash sampleInBall party result st inp chi T).2 := by
  have hr : rssDurableReserve204 party result st (rssRemask204 inp maskW maskZ maskLow) =
      rssDurableReserve204 party result st inp := by
    rw [rssRemask204.public_eq_1]
    rfl
  unfold rssDurableSign204
  dsimp only
  rw [hr, rssSacrificedSignStep_released_mask_independent]

theorem rssDurableRecover204_preserves_burns (party : UInt16) (st : RssDurableSigner204) :
    (rssDurableRecover204 party st).disk = st.disk := by
  rfl

theorem tooth_rssDurableSign204_failed_write
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (party : UInt16) (st : RssDurableSigner204) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) (T : RssSacrificeTranscript204) :
    (rssDurableSign204 chalHash sampleInBall party .failed st inp chi T).2 = none :=
  rssDurableSign204_none_of_refused chalHash sampleInBall party .failed st inp chi T
    (rssDurableReserve204_failed_write party st inp)

inductive RssDurableTransition204
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256) (party : UInt16) :
    RssDurableSigner204 → RssDurableSigner204 → Prop where
  | sign (st : RssDurableSigner204) (result : RssDiskOutcome204) (inp : RssMlDsaAttemptInput)
      (chi : Ext6Fq204) (T : RssSacrificeTranscript204) :
      RssDurableTransition204 chalHash sampleInBall party st
        (rssDurableSign204 chalHash sampleInBall party result st inp chi T).1
  | crash (st : RssDurableSigner204) :
      RssDurableTransition204 chalHash sampleInBall party st (rssDurableRecover204 party st)

inductive RssDurableTrace204
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256) (party : UInt16) :
    RssDurableSigner204 → RssDurableSigner204 → Prop where
  | nil (st : RssDurableSigner204) : RssDurableTrace204 chalHash sampleInBall party st st
  | cons {a b c : RssDurableSigner204} :
      RssDurableTransition204 chalHash sampleInBall party a b →
      RssDurableTrace204 chalHash sampleInBall party b c →
      RssDurableTrace204 chalHash sampleInBall party a c

theorem rssDurableTransition204_monotone
    {chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8}
    {sampleInBall : List UInt8 → Poly256} {party : UInt16} {a b : RssDurableSigner204}
    (h : RssDurableTransition204 chalHash sampleInBall party a b) :
    ∀ material ∈ a.disk.burnedNonces, material ∈ b.disk.burnedNonces := by
  intro material hm
  cases h with
  | sign result inp chi T =>
    rw [rssDurableSign204_state]
    exact rssDurableReserve204_monotone party result a inp material hm
  | crash => exact hm

theorem rssDurableTrace204_monotone
    {chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8}
    {sampleInBall : List UInt8 → Poly256} {party : UInt16} {a b : RssDurableSigner204}
    (h : RssDurableTrace204 chalHash sampleInBall party a b) :
    ∀ material ∈ a.disk.burnedNonces, material ∈ b.disk.burnedNonces := by
  induction h with
  | nil => exact fun _ hm => hm
  | cons step _ ih =>
    intro material hm
    exact ih material (rssDurableTransition204_monotone step material hm)

/-- Replay remains rejected after any number of intervening signs, failures, and crashes. -/
theorem tooth_rssDurableTrace204_replay
    {chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8}
    {sampleInBall : List UInt8 → Poly256} {party : UInt16} {a b : RssDurableSigner204}
    (h : RssDurableTrace204 chalHash sampleInBall party a b)
    (inp : RssMlDsaAttemptInput) (result : RssDiskOutcome204)
    (hb : rssNonceMaterial204 inp ∈ a.disk.burnedNonces) :
    (rssDurableReserve204 party result b inp).1 = false :=
  tooth_rssDurableReserve204_nonce_replay party result b inp (rssDurableTrace204_monotone h _ hb)

/-- Two signatures released anywhere along one durable execution, with arbitrary signing
    attempts, failed writes and crashes in between, never share an aggregate nonce. The
    session, epoch, attempt and share decomposition of the second attempt are unconstrained. -/
theorem rssDurable204_released_nonces_distinct
    {chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8}
    {sampleInBall : List UInt8 → Poly256} {party : UInt16}
    {a b : RssDurableSigner204} {r₁ r₂ : RssDiskOutcome204}
    {inp₁ inp₂ : RssMlDsaAttemptInput} {chi₁ chi₂ : Ext6Fq204}
    {T₁ T₂ : RssSacrificeTranscript204} {sig₁ sig₂ : ThresholdSignSig}
    (h₁ : RssDurableReleased204 chalHash sampleInBall party r₁ a inp₁ chi₁ T₁ sig₁)
    (htr : RssDurableTrace204 chalHash sampleInBall party
      (rssDurableSign204 chalHash sampleInBall party r₁ a inp₁ chi₁ T₁).1 b)
    (h₂ : RssDurableReleased204 chalHash sampleInBall party r₂ b inp₂ chi₂ T₂ sig₂) :
    rssSumVec4List inp₁.ySubsets ≠ rssSumVec4List inp₂.ySubsets := by
  intro hEq
  have hBurned := rssDurableTrace204_monotone htr _
    (rssDurableSign204_release_burned chalHash sampleInBall party r₁ a inp₁ chi₁ T₁ sig₁ h₁)
  have hMat : rssNonceMaterial204 inp₂ = rssNonceMaterial204 inp₁ := by
    unfold rssNonceMaterial204
    rw [hEq]
  have hRefused := tooth_rssDurableReserve204_nonce_replay party r₂ b inp₂ (hMat ▸ hBurned)
  unfold RssDurableReleased204 at h₂
  rw [rssDurableSign204_none_of_refused chalHash sampleInBall party r₂ b inp₂ chi₂ T₂ hRefused] at h₂
  cases h₂

/-- The same nonce is also refused when it is offered again after any execution. -/
theorem tooth_rssDurable204_reuse_after_release
    {chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8}
    {sampleInBall : List UInt8 → Poly256} {party : UInt16}
    {a b : RssDurableSigner204} {r₁ r₂ : RssDiskOutcome204}
    {inp₁ inp₂ : RssMlDsaAttemptInput} {chi₁ chi₂ : Ext6Fq204}
    {T₁ T₂ : RssSacrificeTranscript204} {sig₁ : ThresholdSignSig}
    (h₁ : RssDurableReleased204 chalHash sampleInBall party r₁ a inp₁ chi₁ T₁ sig₁)
    (htr : RssDurableTrace204 chalHash sampleInBall party
      (rssDurableSign204 chalHash sampleInBall party r₁ a inp₁ chi₁ T₁).1 b)
    (hEq : rssSumVec4List inp₂.ySubsets = rssSumVec4List inp₁.ySubsets) :
    (rssDurableSign204 chalHash sampleInBall party r₂ b inp₂ chi₂ T₂).2 = none := by
  have hBurned := rssDurableTrace204_monotone htr _
    (rssDurableSign204_release_burned chalHash sampleInBall party r₁ a inp₁ chi₁ T₁ sig₁ h₁)
  have hMat : rssNonceMaterial204 inp₂ = rssNonceMaterial204 inp₁ := by
    unfold rssNonceMaterial204
    rw [hEq]
  exact rssDurableSign204_none_of_refused chalHash sampleInBall party r₂ b inp₂ chi₂ T₂
    (tooth_rssDurableReserve204_nonce_replay party r₂ b inp₂ (hMat ▸ hBurned))

private theorem rssDurableReserve204_ok_of {party : UInt16} {result : RssDiskOutcome204}
    {st : RssDurableSigner204} {inp : RssMlDsaAttemptInput}
    (hc : ¬ (inp.epoch ≠ st.key.epoch ∨ inp.attempt ≠ st.key.nextAttempt ∨
      2 ^ 64 ≤ inp.epoch ∨ 2 ^ 32 ≤ inp.attempt ∨
      rssNonceMaterial204 inp ∈ st.disk.burnedNonces))
    (hr : (durableBurnReserve st.disk.journal party (UInt64.ofNat inp.epoch)
      inp.sessionId (UInt32.ofNat inp.attempt) (decide (result = .committed))).1 = true) :
    (rssDurableReserve204 party result st inp).1 = true := by
  unfold rssDurableReserve204
  rw [ite_false_of hc]
  split
  · rfl
  · rename_i hm
    rw [hm] at hr
    cases hr

private theorem rssThresholdSignMachine_step_ok
    {chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8}
    {sampleInBall : List UInt8 → Poly256}
    {st st' : RssMlDsaSignerState} {inp : RssMlDsaAttemptInput}
    {out : RssSignPublicAbortView × Option ThresholdSignSig}
    (h : (rssThresholdSignMachine chalHash sampleInBall).step st inp = some (st', out)) :
    rssThresholdSignStep chalHash sampleInBall st inp = .ok st' out := by
  simp only [rssThresholdSignMachine.public_eqs, PartyMachine.ofOutcome] at h
  cases hs : rssThresholdSignStep chalHash sampleInBall st inp with
  | err next reason => rw [hs] at h; cases h
  | ok next o =>
    rw [hs] at h
    injection h with hp
    injection hp with h1 h2
    rw [h1, h2]

/-- The durable sacrificed signer releases a signature in a reachable execution: a fresh
    journal, a committed write, nonzero key shares, nonzero triple masks and the honest
    sacrifice transcript. -/
theorem rssDurableSign204_inhabited :
    ∃ (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
      (sampleInBall : List UInt8 → Poly256)
      (st : RssDurableSigner204) (inp : RssMlDsaAttemptInput)
      (chi : Ext6Fq204) (T : RssSacrificeTranscript204) (sig : ThresholdSignSig),
      RssDurableReleased204 chalHash sampleInBall 0 .committed st inp chi T sig ∧
      rssSumVec4List st.key.s1Subsets ≠ rssZeroVec4 := by
  obtain ⟨chalHash, sampleInBall, st, stAcc, _, inpAcc, _, pubAcc, _, sig,
    hStep, _, _, _, _, hEp, hAtt, hProd, hNz⟩ := threshold_mldsa_rss_inhabited
  have hOk := rssThresholdSignMachine_step_ok hStep
  obtain ⟨hInpEp, hInpAtt, _⟩ := rssThresholdSignStep_ok_meta hOk
  have he0 : inpAcc.epoch = 0 := hInpEp.trans hEp
  have ha0 : inpAcc.attempt = 0 := hInpAtt.trans hAtt
  refine ⟨chalHash, sampleInBall, ⟨st, ⟨⟨[], [], false⟩, []⟩⟩, inpAcc, (⟨Fq204.ofNat 3, Fq204.one, Fq204.zero, Fq204.ofNat 5, Fq204.zero, Fq204.ofNat 2⟩ : Ext6Fq204),
    rssHonestSacrifice204 chalHash sampleInBall st inpAcc (⟨Fq204.ofNat 2, Fq204.ofNat 7, Fq204.zero, Fq204.one, Fq204.zero, Fq204.zero⟩ : Ext6Fq204) Fq204.one,
    sig, ?_, hNz⟩
  have hValid := rssSacrificedProductsValid_complete chalHash sampleInBall st inpAcc
    (⟨Fq204.ofNat 3, Fq204.one, Fq204.zero, Fq204.ofNat 5, Fq204.zero, Fq204.ofNat 2⟩ : Ext6Fq204) (⟨Fq204.ofNat 2, Fq204.ofNat 7, Fq204.zero, Fq204.one, Fq204.zero, Fq204.zero⟩ : Ext6Fq204) Fq204.one hProd
  have hEq := rssSacrificedSignStep_eq_of_valid chalHash sampleInBall st inpAcc (⟨Fq204.ofNat 3, Fq204.one, Fq204.zero, Fq204.ofNat 5, Fq204.zero, Fq204.ofNat 2⟩ : Ext6Fq204) _ hValid
    ((rssProductsValid_eq_true_iff chalHash sampleInBall st inpAcc).mpr hProd)
  have hRes : (rssDurableReserve204 0 .committed
      (⟨st, ⟨⟨[], [], false⟩, []⟩⟩ : RssDurableSigner204) inpAcc).1 = true := by
    apply rssDurableReserve204_ok_of
    · intro hc
      rcases hc with hc | hc | hc | hc | hc
      · exact hc hInpEp
      · exact hc hInpAtt
      · rw [he0] at hc
        exact absurd hc (by decide)
      · rw [ha0] at hc
        exact absurd hc (by decide)
      · exact nomatch hc
    · dsimp only
      rw [he0, ha0]
      exact durableBurnReserve_empty _ _ _ _ _ (by decide)
  unfold RssDurableReleased204 rssDurableSign204
  dsimp only
  rw [hRes]
  dsimp only
  rw [hEq, hOk]
  rfl

theorem tooth_rssProductsValid_corrupted_output
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (h : inp.products.cs1 ≠ (rssComputeProducts chalHash sampleInBall st inp.mu inp.ySubsets).cs1) :
    rssProductsValid chalHash sampleInBall st inp = false := by
  cases hv : rssProductsValid chalHash sampleInBall st inp with
  | false => rfl
  | true =>
    exact False.elim (h (congrArg RssSignProducts.cs1
      ((rssProductsValid_eq_true_iff chalHash sampleInBall st inp).mp hv)))

/-! ## Commit / freeze / reveal DKG

Commitments bind the complete canonical share record and salt. The phase boundary is
explicit: every participant commits before any reveal is accepted, and no commitment
can be replaced after freezing. Hash binding remains a cryptographic assumption.
-/

structure DkgCommitState204 where
  participants : Nat
  session : Frame204
  commitments : List (List UInt8)
  frozen : Bool
  revealed : List SubsetShareRecord

def dkgSharePreimage204 (session salt : Frame204) (sh : SubsetShareRecord) : List UInt8 :=
  cshake256FramedPreimage dkgConfirmDomainTag
    [session.bytes, salt.bytes, encodePolyVec4Bytes sh.s1, encodePolyVec4Bytes sh.s2, encodePolyVec4Bytes sh.publicT]

def dkgCommit204 (st : DkgCommitState204) (digest : List UInt8) : Option DkgCommitState204 :=
  if st.frozen || decide (st.participants ≤ st.commitments.length) then none
  else some { st with commitments := st.commitments ++ [digest] }

def dkgFreeze204 (st : DkgCommitState204) : Option DkgCommitState204 :=
  if st.frozen || decide (st.participants = 0 ∨ st.commitments.length ≠ st.participants) then none
  else some { st with frozen := true }

def dkgReveal204 (H : List UInt8 → List UInt8) (A : PolyMat4) (eta : Nat)
    (st : DkgCommitState204) (salt : Frame204) (sh : SubsetShareRecord) : Option DkgCommitState204 :=
  if st.frozen && decide (st.commitments.length = st.participants) &&
      decide (st.revealed.length < st.participants) &&
      decide (H (dkgSharePreimage204 st.session salt sh) = st.commitments.getD st.revealed.length []) &&
      validSubsetShare A eta sh then
    some { st with revealed := st.revealed ++ [sh] }
  else none

theorem tooth_dkgReveal204_before_freeze (H : List UInt8 → List UInt8) (A : PolyMat4)
    (eta : Nat) (st : DkgCommitState204) (salt : Frame204) (sh : SubsetShareRecord)
    (h : st.frozen = false) : dkgReveal204 H A eta st salt sh = none := by
  simp [dkgReveal204, h]

theorem tooth_dkgCommit204_after_freeze (st : DkgCommitState204) (digest : List UInt8)
    (h : st.frozen = true) : dkgCommit204 st digest = none := by
  simp [dkgCommit204, h]

theorem dkgReveal204_valid_share {H : List UInt8 → List UInt8} {A : PolyMat4} {eta : Nat}
    {st next : DkgCommitState204} {salt : Frame204} {sh : SubsetShareRecord}
    (h : dkgReveal204 H A eta st salt sh = some next) :
    st.frozen = true ∧ st.commitments.length = st.participants ∧
      sh.publicT = addVec4 (matVecMul4 A sh.s1) sh.s2 ∧
      infNormVec4 sh.s1 ≤ eta ∧ infNormVec4 sh.s2 ≤ eta := by
  unfold dkgReveal204 at h
  split at h
  · rename_i hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    exact ⟨hg.1.1.1.1, hg.1.1.1.2, (validSubsetShare_eq_true_iff A eta sh).mp hg.2⟩
  · cases h

private theorem dkgFrames204_bounded (session salt : Frame204) (sh : SubsetShareRecord) :
    ∀ f ∈ [session.bytes, salt.bytes, encodePolyVec4Bytes sh.s1, encodePolyVec4Bytes sh.s2,
      encodePolyVec4Bytes sh.publicT], f.length < 256 ^ 8 := by
  intro f hf
  have hb32 : (2 : Nat) ^ 32 < 256 ^ 8 := by decide
  have hv : (4096 : Nat) < 256 ^ 8 := by decide
  rcases List.mem_cons.mp hf with rfl | hf
  · exact Nat.lt_trans session.bounded hb32
  · rcases List.mem_cons.mp hf with rfl | hf
    · exact Nat.lt_trans salt.bounded hb32
    · rcases List.mem_cons.mp hf with rfl | hf
      · rw [encodePolyVec4Bytes_length]; exact hv
      · rcases List.mem_cons.mp hf with rfl | hf
        · rw [encodePolyVec4Bytes_length]; exact hv
        · rcases List.mem_cons.mp hf with rfl | hf
          · rw [encodePolyVec4Bytes_length]; exact hv
          · exact nomatch hf

/-- The commitment preimage determines the salt and every field of the share record. -/
theorem dkgSharePreimage204_injective {session salt salt' : Frame204}
    {sh sh' : SubsetShareRecord}
    (h : dkgSharePreimage204 session salt sh = dkgSharePreimage204 session salt' sh') :
    salt.bytes = salt'.bytes ∧ sh = sh' := by
  rcases sh with ⟨a, b, c⟩
  rcases sh' with ⟨a', b', c'⟩
  unfold dkgSharePreimage204 at h
  have h5 : (5 : Nat) < 256 ^ 8 := by decide
  have hfs := cshake256FramedPreimage_frames_injective (by exact h5) (by exact h5)
    (dkgFrames204_bounded session salt ⟨a, b, c⟩)
    (dkgFrames204_bounded session salt' ⟨a', b', c'⟩) h
  have h1 := List.cons.inj (List.cons.inj hfs).2
  have h2 := List.cons.inj h1.2
  have h3 := List.cons.inj h2.2
  have h4 := List.cons.inj h3.2
  have ea : a = a' := encodePolyVec4Bytes_injective h2.1
  have eb : b = b' := encodePolyVec4Bytes_injective h3.1
  have ec : c = c' := encodePolyVec4Bytes_injective h4.1
  subst ea eb ec
  exact ⟨h1.1, rfl⟩

private theorem dkgReveal204_some {H : List UInt8 → List UInt8} {A : PolyMat4} {eta : Nat}
    {st next : DkgCommitState204} {salt : Frame204} {sh : SubsetShareRecord}
    (h : dkgReveal204 H A eta st salt sh = some next) :
    st.frozen = true ∧
      H (dkgSharePreimage204 st.session salt sh) = st.commitments.getD st.revealed.length [] ∧
      next = { st with revealed := st.revealed ++ [sh] } := by
  unfold dkgReveal204 at h
  split at h
  · rename_i hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    injection h with h
    exact ⟨hg.1.1.1.1, hg.1.2, h.symm⟩
  · cases h

private theorem dkgCommit204_some {st next : DkgCommitState204} {digest : List UInt8}
    (h : dkgCommit204 st digest = some next) :
    st.frozen = false ∧ next = { st with commitments := st.commitments ++ [digest] } := by
  unfold dkgCommit204 at h
  split at h
  · cases h
  · rename_i hg
    injection h with h
    refine ⟨?_, h.symm⟩
    cases hf : st.frozen with
    | false => rfl
    | true =>
      rw [hf] at hg
      exact False.elim (hg rfl)

private theorem dkgFreeze204_some {st next : DkgCommitState204}
    (h : dkgFreeze204 st = some next) :
    st.frozen = false ∧ st.commitments.length = st.participants ∧
      next = { st with frozen := true } := by
  unfold dkgFreeze204 at h
  split at h
  · cases h
  · rename_i hg
    injection h with h
    cases hf : st.frozen with
    | true =>
      rw [hf] at hg
      exact False.elim (hg rfl)
    | false =>
      rw [hf] at hg
      have hP : ¬ (st.participants = 0 ∨ st.commitments.length ≠ st.participants) :=
        fun p => hg (decide_eq_true p)
      exact ⟨rfl, Decidable.byContradiction (fun hne => hP (Or.inr hne)), h.symm⟩

/-- Binding of a reveal to the frozen commitment at its position: two accepted openings of
    one commitment agree in salt and in every share field, or exhibit a hash collision. -/
theorem dkgReveal204_binding {H : List UInt8 → List UInt8} {A : PolyMat4} {eta : Nat}
    {st st' next next' : DkgCommitState204} {salt salt' : Frame204}
    {sh sh' : SubsetShareRecord}
    (hs : st'.session = st.session) (hc : st'.commitments = st.commitments)
    (hk : st'.revealed.length = st.revealed.length)
    (h : dkgReveal204 H A eta st salt sh = some next)
    (h' : dkgReveal204 H A eta st' salt' sh' = some next') :
    (salt.bytes = salt'.bytes ∧ sh = sh') ∨ HashCollision204 H := by
  obtain ⟨_, hh, _⟩ := dkgReveal204_some h
  obtain ⟨_, hh', _⟩ := dkgReveal204_some h'
  rw [hs, hc, hk] at hh'
  if hp : dkgSharePreimage204 st.session salt sh = dkgSharePreimage204 st.session salt' sh' then
    exact Or.inl (dkgSharePreimage204_injective hp)
  else
    exact Or.inr ⟨_, _, hp, hh.trans hh'.symm⟩

/-- One DKG protocol move. -/
inductive DkgStep204 (H : List UInt8 → List UInt8) (A : PolyMat4) (eta : Nat) :
    DkgCommitState204 → DkgCommitState204 → Prop where
  | commit {st next : DkgCommitState204} (digest : List UInt8) :
      dkgCommit204 st digest = some next → DkgStep204 H A eta st next
  | freeze {st next : DkgCommitState204} :
      dkgFreeze204 st = some next → DkgStep204 H A eta st next
  | reveal {st next : DkgCommitState204} (salt : Frame204) (sh : SubsetShareRecord) :
      dkgReveal204 H A eta st salt sh = some next → DkgStep204 H A eta st next

inductive DkgTrace204 (H : List UInt8 → List UInt8) (A : PolyMat4) (eta : Nat) :
    DkgCommitState204 → DkgCommitState204 → Prop where
  | nil (st : DkgCommitState204) : DkgTrace204 H A eta st st
  | cons {a b c : DkgCommitState204} :
      DkgStep204 H A eta a b → DkgTrace204 H A eta b c → DkgTrace204 H A eta a c

theorem dkgStep204_frozen_stable {H : List UInt8 → List UInt8} {A : PolyMat4} {eta : Nat}
    {a b : DkgCommitState204} (h : DkgStep204 H A eta a b) (hf : a.frozen = true) :
    b.frozen = true ∧ b.commitments = a.commitments ∧ b.session = a.session := by
  cases h with
  | commit digest hc =>
    have hn := (dkgCommit204_some hc).1
    rw [hf] at hn
    cases hn
  | freeze hz =>
    have hn := (dkgFreeze204_some hz).1
    rw [hf] at hn
    cases hn
  | reveal salt sh hr =>
    obtain ⟨_, _, hn⟩ := dkgReveal204_some hr
    subst hn
    exact ⟨hf, rfl, rfl⟩

/-- After freezing, no execution changes the commitment list or the session. -/
theorem dkgTrace204_frozen_stable {H : List UInt8 → List UInt8} {A : PolyMat4} {eta : Nat}
    {a b : DkgCommitState204} (h : DkgTrace204 H A eta a b) :
    a.frozen = true →
      b.frozen = true ∧ b.commitments = a.commitments ∧ b.session = a.session := by
  induction h with
  | nil st => exact fun hf => ⟨hf, rfl, rfl⟩
  | cons step _ ih =>
    intro hf
    obtain ⟨hf1, hc1, hs1⟩ := dkgStep204_frozen_stable step hf
    obtain ⟨hf2, hc2, hs2⟩ := ih hf1
    exact ⟨hf2, hc2.trans hc1, hs2.trans hs1⟩

/-- No share is revealed in any execution before the commitment list is frozen. -/
theorem dkgTrace204_no_reveal_before_freeze {H : List UInt8 → List UInt8} {A : PolyMat4}
    {eta : Nat} {a b : DkgCommitState204} (h : DkgTrace204 H A eta a b) :
    (a.frozen = false → a.revealed = []) → b.frozen = false → b.revealed = [] := by
  induction h with
  | nil st => exact fun ha => ha
  | cons step _ ih =>
    intro ha
    apply ih
    intro hbf
    cases step with
    | commit digest hc =>
      obtain ⟨hfa, hn⟩ := dkgCommit204_some hc
      subst hn
      exact ha hfa
    | freeze hz =>
      obtain ⟨_, _, hn⟩ := dkgFreeze204_some hz
      subst hn
      exact Bool.noConfusion hbf
    | reveal salt sh hr =>
      obtain ⟨hfa, _, hn⟩ := dkgReveal204_some hr
      subst hn
      have hfb : _ = false := hbf
      rw [hfa] at hfb
      exact Bool.noConfusion hfb

/-- Once the commitment list is frozen, the share accepted at each position is fixed up to
    a hash collision on every continuation: what a participant reveals cannot be chosen
    after seeing what the others revealed. -/
theorem dkg204_reveal_determined_at_freeze {H : List UInt8 → List UInt8} {A : PolyMat4}
    {eta : Nat} {a b b' n n' : DkgCommitState204} {salt salt' : Frame204}
    {sh sh' : SubsetShareRecord}
    (hf : a.frozen = true)
    (hb : DkgTrace204 H A eta a b) (hb' : DkgTrace204 H A eta a b')
    (hk : b'.revealed.length = b.revealed.length)
    (h : dkgReveal204 H A eta b salt sh = some n)
    (h' : dkgReveal204 H A eta b' salt' sh' = some n') :
    (salt.bytes = salt'.bytes ∧ sh = sh') ∨ HashCollision204 H := by
  obtain ⟨_, hc, hs⟩ := dkgTrace204_frozen_stable hb hf
  obtain ⟨_, hc', hs'⟩ := dkgTrace204_frozen_stable hb' hf
  exact dkgReveal204_binding (hs'.trans hs.symm) (hc'.trans hc.symm) hk h h'

/-- A complete commit, freeze, reveal execution with a nonzero share exists. -/
theorem dkg204_honest_run_inhabited :
    ∃ (H : List UInt8 → List UInt8) (A : PolyMat4) (init final : DkgCommitState204)
      (sh : SubsetShareRecord),
      DkgTrace204 H A 2 init final ∧ init.frozen = false ∧ init.revealed = [] ∧
      final.revealed = [sh] ∧ sh.s1 ≠ rssZeroVec4 := by
  have hn : infNormVec4 (fun _ => polyTreeConstLeaf 8 Fq204.one) ≤ 2 := by
    rw [infNormVec4_eq]
    simp only [polyTreeConstLeaf_infNorm, Nat.max_self]
    decide
  have hvalid : validSubsetShare idMat4 2
      ⟨fun _ => polyTreeConstLeaf 8 Fq204.one, fun _ => polyTreeConstLeaf 8 Fq204.one,
        addVec4 (matVecMul4 idMat4 (fun _ => polyTreeConstLeaf 8 Fq204.one))
          (fun _ => polyTreeConstLeaf 8 Fq204.one)⟩ = true :=
    (validSubsetShare_eq_true_iff _ _ _).mpr ⟨rfl, hn, hn⟩
  generalize hsh : (⟨fun _ => polyTreeConstLeaf 8 Fq204.one,
      fun _ => polyTreeConstLeaf 8 Fq204.one,
      addVec4 (matVecMul4 idMat4 (fun _ => polyTreeConstLeaf 8 Fq204.one))
        (fun _ => polyTreeConstLeaf 8 Fq204.one)⟩ : SubsetShareRecord) = sh at hvalid
  have hs1 : sh.s1 ≠ rssZeroVec4 := by
    rw [← hsh]
    intro h
    have he : polyTreeConstLeaf 8 Fq204.one = PolyTree.zero 8 := congrFun h (0 : Fin 4)
    have hv := congrArg PolyTree.infNorm he
    rw [polyTreeConstLeaf_infNorm] at hv
    change 1 = 0 at hv
    omega
  generalize hd : dkgSharePreimage204 ⟨[], by decide⟩ ⟨[], by decide⟩ sh = d
  have hc : dkgCommit204 ⟨1, ⟨[], by decide⟩, [], false, []⟩ d =
      some ⟨1, ⟨[], by decide⟩, [d], false, []⟩ := by
    rfl
  have hz : dkgFreeze204 ⟨1, ⟨[], by decide⟩, [d], false, []⟩ =
      some ⟨1, ⟨[], by decide⟩, [d], true, []⟩ := by
    rfl
  have hr : dkgReveal204 id idMat4 2 ⟨1, ⟨[], by decide⟩, [d], true, []⟩ ⟨[], by decide⟩ sh =
      some ⟨1, ⟨[], by decide⟩, [d], true, [sh]⟩ := by
    unfold dkgReveal204
    dsimp only
    rw [hd, hvalid]
    have hdec : decide (id d = [d].getD ([] : List SubsetShareRecord).length []) = true :=
      decide_eq_true rfl
    rw [hdec]
    rfl
  exact ⟨id, idMat4, _, _, sh,
    .cons (.commit d hc) (.cons (.freeze hz) (.cons (.reveal _ sh hr) (.nil _))),
    rfl, rfl, rfl, hs1⟩

def RssProductsChecked204
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput) : Prop :=
  rssProductsValid chalHash sampleInBall st inp = true

theorem rssProductsChecked204_sound
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (h : RssProductsChecked204 chalHash sampleInBall st inp) :
    inp.products = rssComputeProducts chalHash sampleInBall st inp.mu inp.ySubsets :=
  (rssProductsValid_eq_true_iff chalHash sampleInBall st inp).mp h

theorem rssProductsChecked204_inhabited
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput) :
    ∃ checked : RssMlDsaAttemptInput, RssProductsChecked204 chalHash sampleInBall st checked := by
  refine ⟨{ inp with products := rssComputeProducts chalHash sampleInBall st inp.mu inp.ySubsets }, ?_⟩
  exact (rssProductsValid_eq_true_iff chalHash sampleInBall st _).mpr rfl

/-- A corrupt *consumed* response product is rejected by the signing state machine itself,
    while its attempt is burned. This tests the checker/consumer connection. -/
theorem tooth_rssThresholdSignStep_corrupt_product
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (hep : inp.epoch = st.epoch) (hatt : inp.attempt = st.nextAttempt)
    (hbad : inp.products.cs1 ≠ (rssComputeProducts chalHash sampleInBall st inp.mu inp.ySubsets).cs1) :
    rssThresholdSignStep chalHash sampleInBall st inp =
      .err { st with nextAttempt := st.nextAttempt + 1 } .mpcSacrificeFailed := by
  unfold rssThresholdSignStep
  rw [decide_eq_true ⟨hep, hatt⟩,
    tooth_rssProductsValid_corrupted_output chalHash sampleInBall st inp hbad]

/-- Acceptance of the byte verifier enforces the same response and hint bounds as the
    algebraic core, on the *decoded wire signature*. -/
theorem mldsaVerifyBytes204_bounds (budget : Nat) (pk msg ctx sig : List UInt8)
    (h : mldsaVerifyBytes204 budget pk msg ctx sig = true) :
    ∃ decoded : DecodedSignature204,
      decodeSignature204 sig = some decoded ∧
      infNormVec4 decoded.z < mldsa44Gamma1 - mldsa44Beta ∧
      hintWeightVec4 decoded.hints ≤ mldsa44Omega := by
  unfold mldsaVerifyBytes204 at h
  split at h
  · cases h
  · cases ha : expandA204 budget (pk.take 32) with
    | none => simp only [ha] at h; cases h
    | some A =>
      cases hd : decodeSignature204 sig with
      | none => simp only [ha, hd] at h; cases h
      | some decoded =>
        rw [ha, hd] at h
        dsimp only at h
        cases hc : sampleInBall204 budget decoded.challenge with
        | none => simp [hc] at h
        | some c =>
          rw [hc] at h
          simp only [mldsaVerify, Bool.and_eq_true, decide_eq_true_eq] at h
          exact ⟨decoded, rfl, h.1.1, h.1.2⟩

/-- An accepting run of the wire verifier decodes a key and a signature that the algebraic
core accepts at the FIPS 204 message representative of `(pk, ctx, msg)`. -/
theorem mldsaVerifyBytes204_accepts_core {budget : Nat} {pk msg ctx sig : List UInt8}
    (h : mldsaVerifyBytes204 budget pk msg ctx sig = true) :
    ∃ (A : PolyMat4) (t1Scaled : PolyVec4) (c : Poly256) (decoded : DecodedSignature204),
      decodeSignature204 sig = some decoded ∧
      mldsaVerify mldsa44ChallengeHash (fun _ => c) A t1Scaled
        (shake256Xof 64 (shake256Xof 64 pk ++ [0, UInt8.ofNat ctx.length] ++ ctx ++ msg))
        decoded.challenge decoded.z decoded.hints = true := by
  unfold mldsaVerifyBytes204 at h
  split at h
  · cases h
  · cases ha : expandA204 budget (pk.take 32) with
    | none => simp only [ha] at h; cases h
    | some A =>
      cases hd : decodeSignature204 sig with
      | none => simp only [ha, hd] at h; cases h
      | some decoded =>
        rw [ha, hd] at h
        dsimp only at h
        cases hc : sampleInBall204 budget decoded.challenge with
        | none => simp [hc] at h
        | some c =>
          rw [hc] at h
          exact ⟨A, _, c, decoded, rfl, h⟩

/-! ## Exports for `SacrificeFreezeSample` ↔ `rssSacrificedSignStep` Bridge -/

/-- All multiplication sacrifice gates in one `RssSacrificeTranscript204`. -/
def rssTranscriptAllGates204 (T : RssSacrificeTranscript204) : List SacGate204 :=
  (List.finRange 4).flatMap (fun i => T.cs1 i ++ T.cs2 i ++ T.ct0 i)

theorem sacTripleError204_eq (g : SacGate204) :
    sacTripleError204 g = ext6Sub g.c (ext6Scale g.a g.b) := by
  unfold sacTripleError204; rfl

theorem sacAccept204_iff_tau_eq (chi : Ext6Fq204) (g : SacGate204) :
    sacAccept204 chi g = true ↔
      ext6Sub (ext6Scale chi (sacGateError204 g)) (sacTripleError204 g) = ext6Zero := by
  unfold sacAccept204 sacVerdict204
  rw [sacOpen204_tau, decide_eq_true_eq]

private theorem exists_bad_gate_of_binds_and_poly_ne
    {gs : List SacGate204} {x y z : Poly256}
    (hBinds : sacBinds204 gs x y z = true)
    (hPolyNe : z ≠ negacyclicMul x y) :
    ∃ g ∈ gs, sacGateError204 g ≠ Fq204.zero := by
  have hNotAll : ¬ (∀ g ∈ gs, sacGateError204 g = Fq204.zero) := by
    intro hAllZero
    apply hPolyNe
    have hSlots : gs.map sacGateOperands204 = nttSlots204 x y z := of_decide_eq_true hBinds
    apply fips204Ntt_injective
    rw [fips204Ntt_negacyclicMul]
    refine (pointwiseMul_of_slots204 _ _ _ ?_).symm
    intro m hm
    have hm' : m ∈ gs.map sacGateOperands204 := by rw [hSlots]; exact hm
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hm'
    exact fq204_eq_of_sub_eq_zero (hAllZero g hg)
  have hFind : ∀ (xs : List SacGate204),
      ¬ (∀ g ∈ xs, sacGateError204 g = Fq204.zero) →
      ∃ g ∈ xs, sacGateError204 g ≠ Fq204.zero := by
    intro xs
    induction xs with
    | nil => intro h; exact False.elim (h (fun _ hm => nomatch hm))
    | cons g rest ih =>
      intro h
      if hg0 : sacGateError204 g = Fq204.zero then
        have hRest : ¬ (∀ g' ∈ rest, sacGateError204 g' = Fq204.zero) := by
          intro hAllR
          apply h
          intro g' hm
          rcases List.mem_cons.mp hm with rfl | hIn
          · exact hg0
          · exact hAllR g' hIn
        obtain ⟨g', hg'In, hg'Nz⟩ := ih hRest
        exact ⟨g', .tail _ hg'In, hg'Nz⟩
      else
        exact ⟨g, .head _, hg0⟩
  exact hFind gs hNotAll

private theorem find_diff_fin4 {p q : PolyVec4} (hNe : p ≠ q) :
    ∃ i : Fin 4, p i ≠ q i := by
  if h0 : p ⟨0, by decide⟩ = q ⟨0, by decide⟩ then
    if h1 : p ⟨1, by decide⟩ = q ⟨1, by decide⟩ then
      if h2 : p ⟨2, by decide⟩ = q ⟨2, by decide⟩ then
        if h3 : p ⟨3, by decide⟩ = q ⟨3, by decide⟩ then
          exfalso
          apply hNe
          funext ⟨idx, hidx⟩
          have hCases : idx = 0 ∨ idx = 1 ∨ idx = 2 ∨ idx = 3 := by omega
          rcases hCases with rfl | rfl | rfl | rfl
          · exact h0
          · exact h1
          · exact h2
          · exact h3
        else exact ⟨⟨3, by decide⟩, h3⟩
      else exact ⟨⟨2, by decide⟩, h2⟩
    else exact ⟨⟨1, by decide⟩, h1⟩
  else exact ⟨⟨0, by decide⟩, h0⟩

/-- **Challenge-Independent Forged-Gate Extraction (`rssSacrificedProductsValid_forged_exists_bad_gate`)**:
    Whenever `inp.products ≠ rssComputeProducts chalHash sampleInBall st inp.mu inp.ySubsets`,
    EITHER `rssSacrificedProductsValid` rejects **every** challenge `chi : Ext6Fq204` (`= false`),
    OR there exists a **fixed** gate `g ∈ rssTranscriptAllGates204 T` (independent of `chi`!) with
    `sacGateError204 g ≠ 0` such that every accepted challenge `chi` satisfies BOTH
    `sacAccept204 chi g = true` AND `chi = sacBadChallenge204 g`! -/
theorem rssSacrificedProductsValid_forged_exists_bad_gate
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (T : RssSacrificeTranscript204)
    (hForged : inp.products ≠ rssComputeProducts chalHash sampleInBall st inp.mu inp.ySubsets) :
    (∀ chi : Ext6Fq204, rssSacrificedProductsValid chalHash sampleInBall st inp chi T = false) ∨
    ∃ g ∈ rssTranscriptAllGates204 T,
      sacGateError204 g ≠ Fq204.zero ∧
      (∀ chi : Ext6Fq204,
        rssSacrificedProductsValid chalHash sampleInBall st inp chi T = true →
        sacAccept204 chi g = true ∧ chi = sacBadChallenge204 g) ∧
      (∀ chi : Ext6Fq204,
        rssSacrificedProductsValid chalHash sampleInBall st inp chi T = true →
        ∀ g' ∈ rssTranscriptAllGates204 T, sacAccept204 chi g' = true) := by
  let wExp := matVecMul4 st.A (rssSumVec4List inp.ySubsets)
  let cPoly := sampleInBall (chalHash inp.mu (highBitsVec4 wExp))
  let s1 := rssSumVec4List st.s1Subsets
  let s2 := rssSumVec4List st.s2Subsets
  let t0 := power2RoundLowVec4 (addVec4 (matVecMul4 st.A s1) s2)
  have hAllGatesAcc : ∀ chi : Ext6Fq204,
      rssSacrificedProductsValid chalHash sampleInBall st inp chi T = true →
      ∀ g' ∈ rssTranscriptAllGates204 T, sacAccept204 chi g' = true := by
    intro chi hVal g' hg'
    unfold rssSacrificedProductsValid at hVal
    simp only [Bool.and_eq_true] at hVal
    obtain ⟨⟨⟨_, hc1⟩, hc2⟩, hc3⟩ := hVal
    obtain ⟨i, _, hInI⟩ := List.mem_flatMap.mp hg'
    rcases List.mem_append.mp hInI with hIn12 | hIn3
    · rcases List.mem_append.mp hIn12 with hIn1 | hIn2
      · have hOk := fin4All204_true hc1 i
        unfold sacProductOk204 sacAcceptAll204 at hOk
        simp only [Bool.and_eq_true] at hOk
        exact List.all_eq_true.mp hOk.2 g' hIn1
      · have hOk := fin4All204_true hc2 i
        unfold sacProductOk204 sacAcceptAll204 at hOk
        simp only [Bool.and_eq_true] at hOk
        exact List.all_eq_true.mp hOk.2 g' hIn2
    · have hOk := fin4All204_true hc3 i
      unfold sacProductOk204 sacAcceptAll204 at hOk
      simp only [Bool.and_eq_true] at hOk
      exact List.all_eq_true.mp hOk.2 g' hIn3
  if hw : polyVec4EqBool inp.products.w wExp = true then
    if hb1 : fin4All204 (fun i => sacBinds204 (T.cs1 i) cPoly (s1 i) (inp.products.cs1 i)) = true then
      if hb2 : fin4All204 (fun i => sacBinds204 (T.cs2 i) cPoly (s2 i) (inp.products.cs2 i)) = true then
        if hb3 : fin4All204 (fun i => sacBinds204 (T.ct0 i) cPoly (t0 i) (inp.products.ct0 i)) = true then
          have hDiff : inp.products.cs1 ≠ mulPolyVec4 cPoly s1 ∨
              inp.products.cs2 ≠ mulPolyVec4 cPoly s2 ∨
              inp.products.ct0 ≠ mulPolyVec4 cPoly t0 := by
            if he1 : polyVec4EqBool inp.products.cs1 (mulPolyVec4 cPoly s1) = true then
              if he2 : polyVec4EqBool inp.products.cs2 (mulPolyVec4 cPoly s2) = true then
                if he3 : polyVec4EqBool inp.products.ct0 (mulPolyVec4 cPoly t0) = true then
                  exfalso
                  apply hForged
                  apply (rssProductsValid_eq_true_iff chalHash sampleInBall st inp).mp
                  rw [rssProductsValid.public_eq_1]
                  simp only [Bool.and_eq_true]
                  exact ⟨⟨⟨hw, he1⟩, he2⟩, he3⟩
                else
                  exact Or.inr (Or.inr (fun h => by
                    rw [(polyVec4EqBool_eq_true_iff _ _).mpr h] at he3; exact he3 rfl))
              else
                exact Or.inr (Or.inl (fun h => by
                  rw [(polyVec4EqBool_eq_true_iff _ _).mpr h] at he2; exact he2 rfl))
            else
              exact Or.inl (fun h => by
                rw [(polyVec4EqBool_eq_true_iff _ _).mpr h] at he1; exact he1 rfl)
          have hBadGate : ∃ g ∈ rssTranscriptAllGates204 T, sacGateError204 g ≠ Fq204.zero := by
            rcases hDiff with hNe1 | hNe2 | hNe3
            · obtain ⟨i, hiNe⟩ := find_diff_fin4 hNe1
              obtain ⟨g, hgIn, hgNz⟩ :=
                exists_bad_gate_of_binds_and_poly_ne (fin4All204_true hb1 i) hiNe
              exact ⟨g, List.mem_flatMap.mpr ⟨i, List.mem_finRange i,
                List.mem_append_left _ (List.mem_append_left _ hgIn)⟩, hgNz⟩
            · obtain ⟨i, hiNe⟩ := find_diff_fin4 hNe2
              obtain ⟨g, hgIn, hgNz⟩ :=
                exists_bad_gate_of_binds_and_poly_ne (fin4All204_true hb2 i) hiNe
              exact ⟨g, List.mem_flatMap.mpr ⟨i, List.mem_finRange i,
                List.mem_append_left _ (List.mem_append_right _ hgIn)⟩, hgNz⟩
            · obtain ⟨i, hiNe⟩ := find_diff_fin4 hNe3
              obtain ⟨g, hgIn, hgNz⟩ :=
                exists_bad_gate_of_binds_and_poly_ne (fin4All204_true hb3 i) hiNe
              exact ⟨g, List.mem_flatMap.mpr ⟨i, List.mem_finRange i,
                List.mem_append_right _ hgIn⟩, hgNz⟩
          obtain ⟨g, hgMem, hgNz⟩ := hBadGate
          refine Or.inr ⟨g, hgMem, hgNz, ?_, hAllGatesAcc⟩
          intro chi hVal
          have hAccG := hAllGatesAcc chi hVal g hgMem
          rcases sacAccept204_sound hAccG with hMulEq | hChiBad
          · exfalso
            apply hgNz
            unfold sacGateError204
            rw [hMulEq, fq204_sub_self]
          · exact ⟨hAccG, hChiBad⟩
        else
          refine Or.inl (fun chi => ?_)
          cases hv : rssSacrificedProductsValid chalHash sampleInBall st inp chi T with
          | false => rfl
          | true =>
            exfalso; apply hb3
            unfold rssSacrificedProductsValid at hv
            simp only [Bool.and_eq_true] at hv
            apply fin4All204_of_forall; intro i
            have hOk := fin4All204_true hv.2 i
            unfold sacProductOk204 at hOk
            exact (Bool.and_eq_true _ _).mp hOk |>.1
      else
        refine Or.inl (fun chi => ?_)
        cases hv : rssSacrificedProductsValid chalHash sampleInBall st inp chi T with
        | false => rfl
        | true =>
          exfalso; apply hb2
          unfold rssSacrificedProductsValid at hv
          simp only [Bool.and_eq_true] at hv
          apply fin4All204_of_forall; intro i
          have hOk := fin4All204_true hv.1.2 i
          unfold sacProductOk204 at hOk
          exact (Bool.and_eq_true _ _).mp hOk |>.1
    else
      refine Or.inl (fun chi => ?_)
      cases hv : rssSacrificedProductsValid chalHash sampleInBall st inp chi T with
      | false => rfl
      | true =>
        exfalso; apply hb1
        unfold rssSacrificedProductsValid at hv
        simp only [Bool.and_eq_true] at hv
        apply fin4All204_of_forall; intro i
        have hOk := fin4All204_true hv.1.1.2 i
        unfold sacProductOk204 at hOk
        exact (Bool.and_eq_true _ _).mp hOk |>.1
  else
    refine Or.inl (fun chi => ?_)
    cases hv : rssSacrificedProductsValid chalHash sampleInBall st inp chi T with
    | false => rfl
    | true =>
      exfalso; apply hw
      unfold rssSacrificedProductsValid at hv
      simp only [Bool.and_eq_true] at hv
      exact hv.1.1.1

/-- Fitted gate list for an arbitrary claimed polynomial `z` when the sacrifice challenge `chi`
    is revealed before freezing the transcript (swapped-order `#tooth` support). -/
def sacFittedGates204 (chi : Ext6Fq204) (x y z : Poly256) : List SacGate204 :=
  (nttSlots204 x y z).map (fun m =>
    { x := m.1
      y := m.2.1
      z := m.2.2
      a := ext6Zero
      b := Fq204.zero
      c := ext6Scale chi (Fq204.sub m.2.2 (Fq204.mul m.1 m.2.1)) })

private theorem map_operands_fitted204 (chi : Ext6Fq204) :
    ∀ ms : List (Fq204 × Fq204 × Fq204),
      (ms.map (fun m =>
        ({ x := m.1, y := m.2.1, z := m.2.2, a := ext6Zero, b := Fq204.zero,
           c := ext6Scale chi (Fq204.sub m.2.2 (Fq204.mul m.1 m.2.1)) } : SacGate204))).map
        sacGateOperands204 = ms
  | [] => rfl
  | m :: ms => by
    rw [List.map_cons, List.map_cons, map_operands_fitted204 chi ms]
    rfl

private theorem sacFittedGates204_ok (chi : Ext6Fq204) (x y z : Poly256) :
    sacProductOk204 chi (sacFittedGates204 chi x y z) x y z = true := by
  unfold sacProductOk204
  rw [Bool.and_eq_true]
  refine ⟨decide_eq_true (map_operands_fitted204 chi _), ?_⟩
  unfold sacAcceptAll204 sacFittedGates204
  rw [List.all_eq_true]
  intro g hg
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp hg
  rw [sacAccept204_iff_tau_eq, sacGateError204, sacTripleError204]
  dsimp only
  rw [ext6_sub_sub_self, ext6Scale_eq]
  simp only [ext6Zero_eq, Fq204.mul_zero]

/-- Swapped-order fitted sacrifice transcript for any claimed `inp.products` when `chi` is
    sampled before freezing `T`. -/
def rssFittedSacrifice204
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204) : RssSacrificeTranscript204 :=
  let cPoly := sampleInBall (chalHash inp.mu
    (highBitsVec4 (matVecMul4 st.A (rssSumVec4List inp.ySubsets))))
  let s1 := rssSumVec4List st.s1Subsets
  let s2 := rssSumVec4List st.s2Subsets
  let t0 := power2RoundLowVec4 (addVec4 (matVecMul4 st.A s1) s2)
  { cs1 := fun i => sacFittedGates204 chi cPoly (s1 i) (inp.products.cs1 i)
    cs2 := fun i => sacFittedGates204 chi cPoly (s2 i) (inp.products.cs2 i)
    ct0 := fun i => sacFittedGates204 chi cPoly (t0 i) (inp.products.ct0 i) }

theorem rssSacrificedProductsValid_fitted_accepts
    (chalHash : List UInt8 → (Fin 4 → NatTree 8) → List UInt8)
    (sampleInBall : List UInt8 → Poly256)
    (st : RssMlDsaSignerState) (inp : RssMlDsaAttemptInput)
    (chi : Ext6Fq204)
    (hw : inp.products.w = matVecMul4 st.A (rssSumVec4List inp.ySubsets)) :
    rssSacrificedProductsValid chalHash sampleInBall st inp chi
      (rssFittedSacrifice204 chalHash sampleInBall st inp chi) = true := by
  unfold rssSacrificedProductsValid rssFittedSacrifice204
  dsimp only
  simp only [Bool.and_eq_true, polyVec4EqBool_eq_true_iff]
  exact ⟨⟨⟨hw,
    fin4All204_of_forall (fun i => sacFittedGates204_ok chi _ _ _)⟩,
    fin4All204_of_forall (fun i => sacFittedGates204_ok chi _ _ _)⟩,
    fin4All204_of_forall (fun i => sacFittedGates204_ok chi _ _ _)⟩

#verify_constructive
  rssSacrificedProductsValid_forged_exists_bad_gate
  rssSacrificedProductsValid_fitted_accepts

theorem sacGateError204_eq (g : SacGate204) :
    sacGateError204 g = Fq204.sub g.z (Fq204.mul g.x g.y) := by unfold sacGateError204; rfl

/-- The all-`false` hint vector, as decoded from an empty hint encoding. -/
def mldsaZeroHints204 : Fin 4 → HintTree 8 := fun _ => hintTree204 8 []

/-- With the challenge hash that returns its message representative, the zero key and the zero
    response, the algebraic core accepts every `μ` presented as its own challenge bytes. -/
theorem mldsaVerify_echo_zero_accepts (mu : List UInt8) :
    mldsaVerify (fun m _ => m) (fun _ => PolyTree.zero 8) (fun _ _ => PolyTree.zero 8)
      (fun _ => PolyTree.zero 8) mu mu (fun _ => PolyTree.zero 8) mldsaZeroHints204 = true := by
  have h1 : infNormVec4 (fun _ => PolyTree.zero 8) < mldsa44Gamma1 - mldsa44Beta := by
    rw [infNormVec4_eq]
    decide +kernel
  have h2 : hintWeightVec4 mldsaZeroHints204 ≤ mldsa44Omega := by
    simp only [hintWeightVec4_eq, mldsaZeroHints204, hintTree204, HintTree.weight_branch, HintTree.weight_leaf]
    decide +kernel
  unfold mldsaVerify
  simp only [decide_eq_true h1, decide_eq_true h2, decide_true, Bool.and_self]

#tooth_pair mldsaVerifyBytes204_bounds vs tooth_mldsaVerifyBytes204_bad_key_length
#tooth_pair cosetLde204_size vs tooth_cosetLde204_zero_shift
#tooth_pair canonicalNorm204_sound vs tooth_canonicalNorm204_noncanonical
#tooth_pair merkleNodePreimage204_injective vs tooth_merkle204_leaf_node_disjoint
#tooth_pair rssProductsValid_eq_true_iff vs tooth_rssProductsValid_corrupted_output
#tooth_pair rssDurableReserve204_burns vs tooth_rssDurableReserve204_nonce_replay
#tooth_pair rssDurableSign204_release_burned vs tooth_rssDurableSign204_failed_write
#tooth_pair dkgReveal204_valid_share vs tooth_dkgReveal204_before_freeze

#tooth_pair rssDurableTrace204_monotone vs tooth_rssDurableTrace204_replay
#verify_inhabited rssProductsChecked204_sound rssProductsChecked204_inhabited
#tooth_pair sacAccept204_sound vs tooth_sacAccept204_rejects_corrupt
#tooth_pair rssSacrificedProductsValid_sound vs tooth_rssSacrificedProductsValid_corrupt
#tooth_pair rssDurable204_released_nonces_distinct vs tooth_rssDurable204_reuse_after_release
#tooth_pair dkgReveal204_binding vs tooth_dkgCommit204_after_freeze

#verify_inhabited rssDurableSign204_release_verifies rssDurableSign204_inhabited

#verify_constructive mldsaVerify_echo_zero_accepts

end Qsag
end
