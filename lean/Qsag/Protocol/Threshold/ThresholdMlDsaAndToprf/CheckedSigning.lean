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
