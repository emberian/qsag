module

public import Aeneas
public import QsagVerified.Types
public import QsagVerified.Funs

public section

/-!
# Independent statement file for the Rust MIR refinement theorems

This module fixes the statements of the key functional-correctness theorems
about the generated Rust MIR model: Goldilocks arithmetic, the binary tower,
Keccak-f[1600], the FIPS 205 address codec and WOTS+ helpers, the BDOZ two-lane
MAC, Shamir sharing and the epoch latch. `lake comparator --paranoid` checks
that the proof development (`QsagMirProofs`) proves exactly these statements,
over identical definitions, using no axiom other than `propext` and
`Quot.sound`, and replays the proofs through the external kernels.

It imports only the generated model (`Aeneas`, `QsagVerified.Types`,
`QsagVerified.Funs`) and never a proofs module. Every specification definition
a statement mentions is declared again here, verbatim, so the comparison also
pins those definitions.

Every theorem body below is `sorry`. That is the comparator convention for a
statement file: only the types are compared, and the proofs are taken from the
solution module. This is the only module in the package where `sorry` appears.

Coverage boundary. The Keccak theorems state termination without failure
plus one non-constancy witness, not general FIPS 202 value equivalence.
Tower128 now has MIR equality to independent pure Wiedemann arithmetic,
commutativity, and basis-sensitive vectors; the general recursive tower and
basis-change theorem remain separate obligations. The WOTS+ chain
theorems cover composition and range rejection, not the hash values. Lagrange
reconstruction is covered for 2-of-2 and 3-of-3 only. Theorems outside the
roster in `comparator.json` are not checked by this gate.
-/

namespace qsag_verified.proofs

open Aeneas Aeneas.Std Result ControlFlow Error
open qsag_verified

set_option maxRecDepth 4096

/-! ## Goldilocks field (p = 2^64 - 2^32 + 1) and its quadratic extension -/

/-- Canonical Goldilocks prime $p = 2^{64} - 2^{32} + 1$. -/
@[expose]
def GoldilocksP : Nat := 18446744069414584321

theorem goldilocks_canon_spec (x : Std.U64) :
    ∃ y : goldilocks.Goldilocks,
      goldilocks.goldilocks_canon x = .ok y ∧
      y.val = x.val % GoldilocksP ∧
      y.val < GoldilocksP := sorry

theorem goldilocks_add_spec (a b : goldilocks.Goldilocks) :
    ∃ y : goldilocks.Goldilocks,
      goldilocks.goldilocks_add a b = .ok y ∧
      y.val = (a.val % GoldilocksP + b.val % GoldilocksP) % GoldilocksP ∧
      y.val < GoldilocksP := sorry

theorem goldilocks_sub_spec (a b : goldilocks.Goldilocks) :
    ∃ y : goldilocks.Goldilocks,
      goldilocks.goldilocks_sub a b = .ok y ∧
      y.val = (GoldilocksP + a.val % GoldilocksP - b.val % GoldilocksP) % GoldilocksP ∧
      y.val < GoldilocksP := sorry

theorem goldilocks_reduce128_spec (x : Std.U128) :
    ∃ y : goldilocks.Goldilocks,
      goldilocks.goldilocks_reduce128 x = .ok y ∧
      y.val = x.val % GoldilocksP ∧
      y.val < GoldilocksP := sorry

theorem goldilocks_mul_spec (a b : goldilocks.Goldilocks) :
    ∃ y : goldilocks.Goldilocks,
      goldilocks.goldilocks_mul a b = .ok y ∧
      y.val = ((a.val % GoldilocksP) * (b.val % GoldilocksP)) % GoldilocksP ∧
      y.val < GoldilocksP := sorry

theorem goldilocks_pow7_spec (x : goldilocks.Goldilocks) :
    ∃ y : goldilocks.Goldilocks,
      goldilocks.goldilocks_pow7 x = .ok y ∧
      y.val = ((x.val % GoldilocksP) ^ 7) % GoldilocksP ∧
      y.val < GoldilocksP := sorry

theorem goldilocks_inv_or_zero_spec (a : goldilocks.Goldilocks) :
    ∃ y, goldilocks.goldilocks_inv_or_zero a = .ok y ∧
      y.val = (a.val % GoldilocksP) ^ (GoldilocksP - 2) % GoldilocksP ∧
      y.val < GoldilocksP ∧ (a.val % GoldilocksP = 0 → y = 0#u64) := sorry

theorem goldilocks_inv_spec (a : goldilocks.Goldilocks) :
    ∃ inv, goldilocks.goldilocks_inv_or_zero a = .ok inv ∧
      (goldilocks.goldilocks_inv a = .ok none ↔ a.val % GoldilocksP = 0 ∨ inv = 0#u64) ∧
      (inv ≠ 0#u64 → goldilocks.goldilocks_inv a = .ok (some inv)) := sorry

theorem goldilocks_ext2_add_spec (a b : goldilocks.GoldilocksExt2) :
    ∃ y, goldilocks.goldilocks_ext2_add a b = .ok y ∧
      y.c0.val < GoldilocksP ∧ y.c1.val < GoldilocksP ∧
      y.c0.val = (a.c0.val % GoldilocksP + b.c0.val % GoldilocksP) % GoldilocksP ∧
      y.c1.val = (a.c1.val % GoldilocksP + b.c1.val % GoldilocksP) % GoldilocksP := sorry

theorem goldilocks_ext2_mul_spec (a b : goldilocks.GoldilocksExt2) :
    ∃ y, goldilocks.goldilocks_ext2_mul a b = .ok y ∧
      y.c0.val < GoldilocksP ∧ y.c1.val < GoldilocksP ∧
      y.c0.val = ((a.c0.val % GoldilocksP) * (b.c0.val % GoldilocksP) +
        7 * ((a.c1.val % GoldilocksP) * (b.c1.val % GoldilocksP))) % GoldilocksP ∧
      y.c1.val = ((a.c0.val % GoldilocksP) * (b.c1.val % GoldilocksP) +
        (a.c1.val % GoldilocksP) * (b.c0.val % GoldilocksP)) % GoldilocksP := sorry

/-! ## Binary tower: GF(2^8) against a pure specification, field laws, Tower128 -/

@[expose]
def pureMulT1 (a b : Std.U8) : Std.U8 :=
  let a_lo := a &&& 1#u8
  let a_hi := ⟨a.bv >>> 1⟩ &&& 1#u8
  let b_lo := b &&& 1#u8
  let b_hi := ⟨b.bv >>> 1⟩ &&& 1#u8
  let p := a_lo &&& b_lo
  let q := a_hi &&& b_hi
  let r := (a_lo ^^^ a_hi) &&& (b_lo ^^^ b_hi)
  (p ^^^ q) ||| ⟨(r ^^^ p).bv <<< 1⟩

@[expose]
def pureScaleXT1 (a : Std.U8) : Std.U8 :=
  let lo := a &&& 1#u8
  let hi := ⟨a.bv >>> 1⟩ &&& 1#u8
  hi ||| ⟨(lo ^^^ hi).bv <<< 1⟩

@[expose]
def pureMulT2 (a b : Std.U8) : Std.U8 :=
  let a_lo := a &&& 3#u8
  let a_hi := ⟨a.bv >>> 2⟩ &&& 3#u8
  let b_lo := b &&& 3#u8
  let b_hi := ⟨b.bv >>> 2⟩ &&& 3#u8
  let p := pureMulT1 a_lo b_lo
  let q := pureMulT1 a_hi b_hi
  let r := pureMulT1 (a_lo ^^^ a_hi) (b_lo ^^^ b_hi)
  let hi := ((r ^^^ p) ^^^ q) ^^^ pureScaleXT1 q
  (p ^^^ q) ||| ⟨hi.bv <<< 2⟩

@[expose]
def pureScaleXT2 (a : Std.U8) : Std.U8 :=
  let lo := a &&& 3#u8
  let hi := ⟨a.bv >>> 2⟩ &&& 3#u8
  hi ||| ⟨(lo ^^^ pureScaleXT1 hi).bv <<< 2⟩

@[expose]
def pureGf256Mul (a b : Std.U8) : Std.U8 :=
  let a_lo := a &&& 15#u8
  let a_hi := ⟨a.bv >>> 4⟩ &&& 15#u8
  let b_lo := b &&& 15#u8
  let b_hi := ⟨b.bv >>> 4⟩ &&& 15#u8
  let p := pureMulT2 a_lo b_lo
  let q := pureMulT2 a_hi b_hi
  let r := pureMulT2 (a_lo ^^^ a_hi) (b_lo ^^^ b_hi)
  let hi := ((r ^^^ p) ^^^ q) ^^^ pureScaleXT2 q
  (p ^^^ q) ||| ⟨hi.bv <<< 4⟩

@[expose]
def pureGf256Inv (a : Std.U8) : Std.U8 :=
  let a2 := pureGf256Mul a a
  let a4 := pureGf256Mul a2 a2
  let a6 := pureGf256Mul a4 a2
  let a8 := pureGf256Mul a4 a4
  let a14 := pureGf256Mul a8 a6
  let a16 := pureGf256Mul a8 a8
  let a32 := pureGf256Mul a16 a16
  let a64 := pureGf256Mul a32 a32
  let a128 := pureGf256Mul a64 a64
  pureGf256Mul (pureGf256Mul (pureGf256Mul a128 a64)
    (pureGf256Mul a32 a16)) a14

theorem gf256_mul_eq_pure (a b : tower.Gf256) :
    tower.gf256_mul a b = .ok (pureGf256Mul a b) := sorry

theorem gf256_inv_or_zero_eq_pure (a : Std.U8) :
    tower.gf256_inv_or_zero a = .ok (pureGf256Inv a) := sorry

theorem tower_gf256_field_laws (a b c : tower.Gf256) :
    pureGf256Mul a 0#u8 = 0#u8 ∧ pureGf256Mul a 1#u8 = a ∧
    pureGf256Mul a b = pureGf256Mul b a ∧
    pureGf256Mul (pureGf256Mul a b) c = pureGf256Mul a (pureGf256Mul b c) ∧
    pureGf256Mul a (b ^^^ c) = pureGf256Mul a b ^^^ pureGf256Mul a c := sorry

theorem tower_gf256_inv_spec (a : tower.Gf256) :
    (a = 0#u8 → tower.gf256_inv a = .ok none) ∧
    (a ≠ 0#u8 → ∃ inv, tower.gf256_inv a = .ok (some inv) ∧
      tower.gf256_mul a inv = .ok 1#u8) := sorry

theorem tower_gf256_boolean_iff_frobenius (x : tower.Gf256) :
    (tower.gf256_frobenius_residual x = .ok 0#u8 ↔ (x = 0#u8 ∨ x = 1#u8)) ∧
    tower.gf256_is_boolean_frobenius x = .ok (decide (x = 0#u8 ∨ x = 1#u8)) := sorry

theorem tower128_mul_total (a b : tower.Tower128) :
    ∃ c : tower.Tower128, tower.tower128_mul a b = .ok c := sorry

/-! ## Keccak-f[1600] -/

theorem keccak_f1600_total (state : Array Std.U64 25#usize) :
    ∃ state', keccak.keccak_f1600 state = .ok state' := sorry

theorem keccak_f1600_zero_state_nonconstant :
    ∃ out, keccak.keccak_f1600 (Std.Array.repeat 25#usize 0#u64) = .ok out ∧
      out ≠ Std.Array.repeat 25#usize 0#u64 := sorry

/-! ## FIPS 205: ADRS codec, WOTS+ checksum and chain -/

@[expose]
def natPrefixSum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => natPrefixSum f n + f n

@[expose]
def wotsChecksumNat (digits : Std.Array Std.U8 32#usize) : Nat :=
  natPrefixSum (fun k => 15 - (digits.val.getD k 0#u8).val % 16) 32

theorem fips205_adrs_roundtrip_spec (adrs : fips205.Fips205Adrs) :
    ∃ bytes, fips205.encode_fips205_adrs adrs = .ok bytes ∧
      fips205.decode_fips205_adrs bytes = .ok (some adrs) := sorry

theorem fips205_adrs_decode_encode_spec (bytes : Std.Array Std.U8 32#usize)
    (adrs : fips205.Fips205Adrs)
    (h : fips205.decode_fips205_adrs bytes = .ok (some adrs)) :
    fips205.encode_fips205_adrs adrs = .ok bytes := sorry

theorem wots_extract_base16_digits_spec (msg16 : Std.Array Std.U8 16#usize) :
    ∃ digits, fips205.wots_extract_base16_digits msg16 = .ok digits ∧
      (∀ k < 16, (digits.val.getD (2 * k) 0#u8).val = (msg16.val.getD k 0#u8).val / 16 ∧
        (digits.val.getD (2 * k + 1) 0#u8).val = (msg16.val.getD k 0#u8).val % 16) ∧
      (∀ k < 32, (digits.val.getD k 0#u8).val < 16) := sorry

theorem wots_checksum_base16_spec (digits : Std.Array Std.U8 32#usize) :
    ∃ csum, fips205.wots_checksum_base16 digits = .ok csum ∧
      csum.val = wotsChecksumNat digits ∧ csum.val ≤ 480 := sorry

theorem fips205_wots_checksum_spec (msg16 : Std.Array Std.U8 16#usize) :
    ∃ digits csum out,
      fips205.wots_extract_base16_digits msg16 = .ok digits ∧
      fips205.wots_checksum_base16 digits = .ok csum ∧
      fips205.fips205_wots_checksum msg16 = .ok out ∧
      csum.val = wotsChecksumNat digits ∧ csum.val ≤ 480 ∧
      (∀ k < 32, out.val.getD k 0#u8 = digits.val.getD k 0#u8) ∧
      (∀ k < 35, (out.val.getD k 0#u8).val < 16) ∧
      csum.val = 256 * (out.val.getD 32 0#u8).val +
        16 * (out.val.getD 33 0#u8).val + (out.val.getD 34 0#u8).val := sorry

theorem fips205_wots_chain_compose (x pk_seed : Std.Array Std.U8 16#usize)
    (adrs : fips205.Fips205Adrs) (start_i s1 s2 : Std.U32)
    (h : start_i.val + s1.val + s2.val ≤ 15) :
    ∃ mid out,
      fips205.fips205_wots_chain x start_i s1 pk_seed adrs = .ok (some mid) ∧
      fips205.fips205_wots_chain mid ⟨start_i.bv + s1.bv⟩ s2 pk_seed adrs = .ok (some out) ∧
      fips205.fips205_wots_chain x start_i ⟨s1.bv + s2.bv⟩ pk_seed adrs = .ok (some out) := sorry

theorem fips205_wots_chain_oob_none
    (x pk_seed : Array Std.U8 16#usize) (base_adrs : fips205.Fips205Adrs)
    (start_i steps_s : Std.U32)
    (h : start_i.val > 15 ∨ start_i.val + steps_s.val > 15) :
    fips205.fips205_wots_chain x start_i steps_s pk_seed base_adrs = .ok none := sorry

/-! ## BDOZ two-lane MAC: authenticated opening, one-time burn, tamper rejection -/

@[expose] def pureScaleXT3 (a : Std.U8) : Std.U8 :=
  let lo := a &&& 15#u8
  let hi := (⟨a.bv >>> 4⟩ : Std.U8) &&& 15#u8
  hi ||| ⟨(lo ^^^ pureScaleXT2 hi).bv <<< 4⟩

@[expose] def pureMulT4 (a b : Std.U16) : Std.U16 :=
  let alo : Std.U8 := UScalar.cast .U8 (a &&& 255#u16)
  let ahi : Std.U8 := UScalar.cast .U8 ((⟨a.bv >>> 8⟩ : Std.U16) &&& 255#u16)
  let blo : Std.U8 := UScalar.cast .U8 (b &&& 255#u16)
  let bhi : Std.U8 := UScalar.cast .U8 ((⟨b.bv >>> 8⟩ : Std.U16) &&& 255#u16)
  let p := pureGf256Mul alo blo
  let q := pureGf256Mul ahi bhi
  let r := pureGf256Mul (alo ^^^ ahi) (blo ^^^ bhi)
  let sx := pureScaleXT3 q
  ⟨(UScalar.cast .U16 (p ^^^ q)).bv ||| ((UScalar.cast .U16 (r ^^^ p ^^^ q ^^^ sx)).bv <<< 8)⟩

@[expose] def pureScaleXT4 (a : Std.U16) : Std.U16 :=
  let hi : Std.U8 := UScalar.cast .U8 ((⟨a.bv >>> 8⟩ : Std.U16) &&& 255#u16)
  let sx := pureScaleXT3 hi
  ⟨(UScalar.cast .U16 hi).bv ||| ((UScalar.cast .U16 ((UScalar.cast .U8 (a &&& 255#u16)) ^^^ sx)).bv <<< 8)⟩

@[expose] def pureMulT5 (a b : Std.U32) : Std.U32 :=
  let alo : Std.U16 := UScalar.cast .U16 (a &&& 65535#u32)
  let ahi : Std.U16 := UScalar.cast .U16 ((⟨a.bv >>> 16⟩ : Std.U32) &&& 65535#u32)
  let blo : Std.U16 := UScalar.cast .U16 (b &&& 65535#u32)
  let bhi : Std.U16 := UScalar.cast .U16 ((⟨b.bv >>> 16⟩ : Std.U32) &&& 65535#u32)
  let p := pureMulT4 alo blo
  let q := pureMulT4 ahi bhi
  let r := pureMulT4 (alo ^^^ ahi) (blo ^^^ bhi)
  let sx := pureScaleXT4 q
  ⟨(UScalar.cast .U32 (p ^^^ q)).bv ||| ((UScalar.cast .U32 (r ^^^ p ^^^ q ^^^ sx)).bv <<< 16)⟩

@[expose] def pureScaleXT5 (a : Std.U32) : Std.U32 :=
  let hi : Std.U16 := UScalar.cast .U16 ((⟨a.bv >>> 16⟩ : Std.U32) &&& 65535#u32)
  let sx := pureScaleXT4 hi
  ⟨(UScalar.cast .U32 hi).bv ||| ((UScalar.cast .U32 ((UScalar.cast .U16 (a &&& 65535#u32)) ^^^ sx)).bv <<< 16)⟩

@[expose] def pureMulT6 (a b : Std.U64) : Std.U64 :=
  let alo : Std.U32 := UScalar.cast .U32 (a &&& 4294967295#u64)
  let ahi : Std.U32 := UScalar.cast .U32 ((⟨a.bv >>> 32⟩ : Std.U64) &&& 4294967295#u64)
  let blo : Std.U32 := UScalar.cast .U32 (b &&& 4294967295#u64)
  let bhi : Std.U32 := UScalar.cast .U32 ((⟨b.bv >>> 32⟩ : Std.U64) &&& 4294967295#u64)
  let p := pureMulT5 alo blo
  let q := pureMulT5 ahi bhi
  let r := pureMulT5 (alo ^^^ ahi) (blo ^^^ bhi)
  let sx := pureScaleXT5 q
  ⟨(UScalar.cast .U64 (p ^^^ q)).bv ||| ((UScalar.cast .U64 (r ^^^ p ^^^ q ^^^ sx)).bv <<< 32)⟩

@[expose] def pureScaleXT6 (a : Std.U64) : Std.U64 :=
  let hi : Std.U32 := UScalar.cast .U32 ((⟨a.bv >>> 32⟩ : Std.U64) &&& 4294967295#u64)
  let sx := pureScaleXT5 hi
  ⟨(UScalar.cast .U64 hi).bv ||| ((UScalar.cast .U64 ((UScalar.cast .U32 (a &&& 4294967295#u64)) ^^^ sx)).bv <<< 32)⟩

@[expose] def pureTower128Mul (a b : Std.U128) : Std.U128 :=
  let alo : Std.U64 := UScalar.cast .U64 (a &&& 18446744073709551615#u128)
  let ahi : Std.U64 := UScalar.cast .U64 ((⟨a.bv >>> 64⟩ : Std.U128) &&& 18446744073709551615#u128)
  let blo : Std.U64 := UScalar.cast .U64 (b &&& 18446744073709551615#u128)
  let bhi : Std.U64 := UScalar.cast .U64 ((⟨b.bv >>> 64⟩ : Std.U128) &&& 18446744073709551615#u128)
  let p := pureMulT6 alo blo
  let q := pureMulT6 ahi bhi
  let r := pureMulT6 (alo ^^^ ahi) (blo ^^^ bhi)
  let sx := pureScaleXT6 q
  ⟨(UScalar.cast .U128 (p ^^^ q)).bv ||| ((UScalar.cast .U128 (r ^^^ p ^^^ q ^^^ sx)).bv <<< 64)⟩

@[expose]
def bdozMaskedSum (batch : tower.BdozCommittedBatchOpening2Lane) (item : tower.BdozWireOpening2Lane) : tower.Tower128 :=
  batch.mask_value ^^^ pureTower128Mul item.chal_weight (UScalar.cast .U128 item.opened_value)

@[expose]
def bdozFoldedKey (batch : tower.BdozCommittedBatchOpening2Lane) (item : tower.BdozWireOpening2Lane) (lane : Nat) : tower.Tower128 :=
  batch.mask_key_lanes.val.getD lane 0#u128 ^^^ pureTower128Mul item.chal_weight (item.key_lanes.val.getD lane 0#u128)

@[expose]
def bdozExpectedMacLanes (session : tower.BdozVerifierSession2Lane)
    (batch : tower.BdozCommittedBatchOpening2Lane) (item : tower.BdozWireOpening2Lane) : Std.Array tower.Tower128 2#usize :=
  Std.Array.make 2#usize [
    bdozFoldedKey batch item 0 ^^^ pureTower128Mul (session.alpha_lanes.val.getD 0 0#u128) (bdozMaskedSum batch item),
    bdozFoldedKey batch item 1 ^^^ pureTower128Mul (session.alpha_lanes.val.getD 1 0#u128) (bdozMaskedSum batch item)]

abbrev bdozOpening1 (item : tower.BdozWireOpening2Lane) : Slice tower.BdozWireOpening2Lane :=
  Std.Array.to_slice (Std.Array.make 1#usize [item])

theorem bdoz_authenticate_open_spec (session : tower.BdozVerifierSession2Lane)
    (batch : tower.BdozCommittedBatchOpening2Lane) (item : tower.BdozWireOpening2Lane) :
    ∃ committed_tag session' accepted,
      tower.bdoz_commit_masked_tag batch.session_id batch.round_id (bdozMaskedSum batch item)
        batch.peer_masked_mac_lanes batch.open_nonce = .ok committed_tag ∧
      tower.verify_mac_2lane_with_burn session batch (bdozOpening1 item) = .ok (session', accepted) ∧
      (accepted = true ↔ session.burned = false ∧ item.chal_weight ≠ 0#u128 ∧
        batch.tag_commitment = committed_tag ∧ batch.peer_masked_mac_lanes = bdozExpectedMacLanes session batch item) := sorry

theorem bdoz_mac_one_time_burn_spec (session : tower.BdozVerifierSession2Lane)
    (batch : tower.BdozCommittedBatchOpening2Lane) (openings : Slice tower.BdozWireOpening2Lane) :
    ∃ session' accepted,
      tower.verify_mac_2lane_with_burn session batch openings = .ok (session', accepted) ∧
      ((accepted = false ∨ session.burned = true) →
        session'.burned = true ∧ session'.alpha_lanes = Std.Array.make 2#usize [0#u128, 0#u128] ∧
        ∀ batch' openings', tower.verify_mac_2lane_with_burn session' batch' openings' =
          .ok (⟨Std.Array.make 2#usize [0#u128, 0#u128], true⟩, false)) := sorry

theorem bdoz_tampered_mac_rejected (session : tower.BdozVerifierSession2Lane)
    (batch : tower.BdozCommittedBatchOpening2Lane) (item : tower.BdozWireOpening2Lane)
    (htamper : batch.peer_masked_mac_lanes ≠ bdozExpectedMacLanes session batch item) :
    ∃ session', tower.verify_mac_2lane_with_burn session batch (bdozOpening1 item) = .ok (session', false) := sorry

/-! ## Shamir sharing: Horner evaluation, point validation, Lagrange reconstruction -/

/-- Horner recurrence on the first `n` coefficients, consuming highest degree first. -/
@[expose]
def pureHornerGf256Prefix (coeffs : List tower.Gf256) (x : tower.Gf256) :
    Nat → tower.Gf256 → tower.Gf256
  | 0, acc => acc
  | n + 1, acc => pureHornerGf256Prefix coeffs x n
      (pureGf256Mul acc x ^^^ coeffs.getD n 0#u8)

@[expose]
def pureHornerGf256 (coeffs : List tower.Gf256) (x : tower.Gf256) : tower.Gf256 :=
  pureHornerGf256Prefix coeffs x coeffs.length 0#u8

@[expose]
def pureHornerGoldilocksPrefix (coeffs : List goldilocks.Goldilocks) (x : Nat) :
    Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => pureHornerGoldilocksPrefix coeffs x n
      ((acc % GoldilocksP * (x % GoldilocksP) +
        (coeffs.getD n 0#u64).val % GoldilocksP) % GoldilocksP)

@[expose]
def pureHornerGoldilocks (coeffs : List goldilocks.Goldilocks) (x : Nat) : Nat :=
  pureHornerGoldilocksPrefix coeffs x coeffs.length 0

abbrev gfSlice2 (a b : Std.U8) : Slice Std.U8 :=
  Std.Array.to_slice (Std.Array.make 2#usize [a, b])

abbrev gfSlice3 (a b c : Std.U8) : Slice Std.U8 :=
  Std.Array.to_slice (Std.Array.make 3#usize [a, b, c])

theorem shamir_eval_poly_gf256_spec (coeffs : Slice tower.Gf256) (x : tower.Gf256) :
    threshold.shamir_eval_poly_gf256 coeffs x = .ok (pureHornerGf256 coeffs.val x) := sorry

theorem shamir_eval_poly_goldilocks_spec (coeffs : Slice goldilocks.Goldilocks)
    (x : goldilocks.Goldilocks) :
    ∃ y, threshold.shamir_eval_poly_goldilocks coeffs x = .ok y ∧
      y.val = pureHornerGoldilocks coeffs.val (x.val % GoldilocksP) := sorry

theorem shamir_validate_points_gf256_3_spec (x0 x1 x2 : tower.Gf256) :
    threshold.shamir_validate_points_gf256
      (Array.to_slice (Array.make 3#usize [x0, x1, x2])) =
      .ok (decide (x0 ≠ 0#u8 ∧ x1 ≠ 0#u8 ∧ x2 ≠ 0#u8 ∧
        x0 ≠ x1 ∧ x0 ≠ x2 ∧ x1 ≠ x2)) := sorry

theorem shamir_lagrange_at_zero_gf256_rejects_invalid
    (points shares : Slice tower.Gf256)
    (h : points.val = [] ∨ shares.val.length ≠ points.val.length) :
    threshold.shamir_lagrange_at_zero_gf256 points shares = .ok none := sorry

theorem shamir_lagrange_at_zero_gf256_2of2_spec (c0 c1 x0 x1 : tower.Gf256)
    (hx0 : x0 ≠ 0#u8) (hx1 : x1 ≠ 0#u8) (hne : x0 ≠ x1) :
    (∀ x, threshold.shamir_eval_poly_gf256 (gfSlice2 c0 c1) x =
      .ok (c0 ^^^ pureGf256Mul c1 x)) ∧
    threshold.shamir_lagrange_at_zero_gf256 (gfSlice2 x0 x1)
      (gfSlice2 (c0 ^^^ pureGf256Mul c1 x0) (c0 ^^^ pureGf256Mul c1 x1)) = .ok (some c0) := sorry

theorem shamir_lagrange_at_zero_gf256_3of3_spec (c0 c1 c2 x0 x1 x2 : tower.Gf256)
    (hx0 : x0 ≠ 0#u8) (hx1 : x1 ≠ 0#u8) (hx2 : x2 ≠ 0#u8)
    (hne01 : x0 ≠ x1) (hne02 : x0 ≠ x2) (hne12 : x1 ≠ x2) :
    (∀ x, threshold.shamir_eval_poly_gf256 (gfSlice3 c0 c1 c2) x =
      .ok (c0 ^^^ pureGf256Mul c1 x ^^^ pureGf256Mul c2 (pureGf256Mul x x))) ∧
    threshold.shamir_lagrange_at_zero_gf256 (gfSlice3 x0 x1 x2)
      (gfSlice3
        (c0 ^^^ pureGf256Mul c1 x0 ^^^ pureGf256Mul c2 (pureGf256Mul x0 x0))
        (c0 ^^^ pureGf256Mul c1 x1 ^^^ pureGf256Mul c2 (pureGf256Mul x1 x1))
        (c0 ^^^ pureGf256Mul c1 x2 ^^^ pureGf256Mul c2 (pureGf256Mul x2 x2))) = .ok (some c0) := sorry

/-! ## Epoch latch: single-call transition and multi-turn safety -/

set_option genSizeOf false in
set_option genInjectivity false in
/-- One observable protocol call, retaining domain rejections in the history. -/
inductive EpochTurn where
  | acquire (request : threshold.EpochSignRequest)
      (result : core.result.Result threshold.EpochAuthGrant threshold.EpochLatchError)
  | advance (request : threshold.EpochRequest)
      (result : core.result.Result Std.U64 threshold.EpochLatchError)

@[expose]
def traceGrants : List EpochTurn → List threshold.EpochAuthGrant
  | [] => []
  | .acquire _ (.Ok g) :: ts => g :: traceGrants ts
  | _ :: ts => traceGrants ts

/-- Executable MIR transitions, with rejections leaving the persisted state unchanged. -/
inductive EpochTrace : threshold.EpochLatch → List EpochTurn → threshold.EpochLatch → Prop where
  | nil (st) : EpochTrace st [] st
  | acquire_ok {st mid final req g ts}
      (step : threshold.EpochLatch.acquire_or_retry st req = .ok (.Ok (mid, g)))
      (tail : EpochTrace mid ts final) : EpochTrace st (.acquire req (.Ok g) :: ts) final
  | acquire_err {st final req e ts}
      (step : threshold.EpochLatch.acquire_or_retry st req = .ok (.Err e))
      (tail : EpochTrace st ts final) : EpochTrace st (.acquire req (.Err e) :: ts) final
  | advance_ok {st mid final req ep ts}
      (step : threshold.epoch_latch_advance st req = .ok (.Ok (mid, ep)))
      (tail : EpochTrace mid ts final) : EpochTrace st (.advance req (.Ok ep) :: ts) final
  | advance_err {st final req e ts}
      (step : threshold.epoch_latch_advance st req = .ok (.Err e))
      (tail : EpochTrace st ts final) : EpochTrace st (.advance req (.Err e) :: ts) final

@[expose]
def WellFormedWal (st : threshold.EpochLatch) : Prop :=
  st.next_epoch.val ≤ st.max_epoch.val ∧
    ∀ b, st.last_bound = .Bound b → b.epoch.val < st.next_epoch.val

/-- Complete successful acquire-or-retry transition, including the persisted binding. -/
@[expose]
def EpochAcquireSuccess (st : threshold.EpochLatch) (req : threshold.EpochSignRequest)
    (st' : threshold.EpochLatch) (g : threshold.EpochAuthGrant) : Prop :=
  WellFormedWal st' ∧ st'.key_epoch_id = st.key_epoch_id ∧ st'.max_epoch = st.max_epoch ∧
  st.key_epoch_id = req.key_epoch_id ∧ g.authorized_epoch = req.requested_epoch ∧
  g.msg_digest = req.msg_digest ∧ g.r_rand = req.deterministic_r_rand ∧
  st'.last_bound = .Bound ⟨g.authorized_epoch, g.msg_digest, g.r_rand⟩ ∧
  ((g.is_idempotent_retry = true ∧ st' = st) ∨
   (g.is_idempotent_retry = false ∧ g.authorized_epoch = st.next_epoch ∧
    st'.next_epoch.val = st.next_epoch.val + 1))

@[expose]
def EpochFreshError (st : threshold.EpochLatch) (requested : Std.U64)
    (e : threshold.EpochLatchError) : Prop :=
  (requested ≠ st.next_epoch ∧ e = .NonSequentialEpoch st.next_epoch requested) ∨
  (requested = st.next_epoch ∧ st.next_epoch >= st.max_epoch ∧ e = .TreeExhausted st.max_epoch)

@[expose]
def EpochAcquireError (st : threshold.EpochLatch) (req : threshold.EpochSignRequest)
    (e : threshold.EpochLatchError) : Prop :=
  if st.key_epoch_id = req.key_epoch_id then
    match st.last_bound with
    | .Unset => EpochFreshError st req.requested_epoch e
    | .Bound b =>
      if req.requested_epoch = b.epoch then
        (b.msg_digest ≠ req.msg_digest ∧ e = .EpochEquivocationAttempt b.epoch) ∨
        (b.msg_digest = req.msg_digest ∧ b.r_rand ≠ req.deterministic_r_rand ∧
          e = .RetryRandomizerMismatch b.epoch)
      else EpochFreshError st req.requested_epoch e
  else e = .KeyBindingMismatch

@[expose]
def traceAssignedEpochs : List EpochTurn → List Std.U64
  | [] => []
  | .advance _ (.Ok ep) :: ts => ep :: traceAssignedEpochs ts
  | _ :: ts => traceAssignedEpochs ts

theorem epoch_latch_acquire_or_retry_spec (st : threshold.EpochLatch)
    (req : threshold.EpochSignRequest) (hw : WellFormedWal st) :
    ∃ res, threshold.EpochLatch.acquire_or_retry st req = .ok res ∧
      match res with
      | .Err e => EpochAcquireError st req e
      | .Ok (st', grant) => EpochAcquireSuccess st req st' grant := sorry

theorem epoch_latch_multiturn_safety (max_epoch : Std.U64)
    (key_epoch_id : Std.Array Std.U8 32#usize) (st0 st : threshold.EpochLatch)
    (turns : List EpochTurn)
    (hnew : threshold.EpochLatch.new max_epoch key_epoch_id = .ok st0)
    (trace : EpochTrace st0 turns st) :
    (WellFormedWal st ∧ st.key_epoch_id = key_epoch_id ∧ st.max_epoch = max_epoch) ∧
    (∀ g ∈ traceGrants turns,
      g.authorized_epoch.val < st.next_epoch.val ∧ st.next_epoch.val ≤ max_epoch.val) ∧
    (∀ g1 ∈ traceGrants turns, ∀ g2 ∈ traceGrants turns,
      g1.authorized_epoch = g2.authorized_epoch →
        g1.msg_digest = g2.msg_digest ∧ g1.r_rand = g2.r_rand) ∧
    (∀ ep ∈ traceAssignedEpochs turns, ep.val < st.next_epoch.val) ∧
    (traceAssignedEpochs turns).Pairwise (fun a b => a ≠ b) ∧
    (∀ ep ∈ traceAssignedEpochs turns, ∀ g ∈ traceGrants turns, g.authorized_epoch ≠ ep) := sorry

/-! ## Concrete-input controls (rejections and one inverse witness) -/

theorem tooth_goldilocks_noncanonical_rejected :
    goldilocks.goldilocks_from_canonical 18446744069414584321#u64 =
      .ok (.Err { raw_value := 18446744069414584321#u64 }) := sorry

theorem tooth_goldilocks_inv_seven :
    (goldilocks.goldilocks_inv_or_zero 7#u64 >>= fun inv =>
      goldilocks.goldilocks_mul inv 7#u64) = .ok 1#u64 := sorry

theorem tooth_shamir_duplicate_points_rejected :
    threshold.shamir_validate_points_gf256
      (Array.to_slice (Array.make 3#usize [1#u8, 1#u8, 2#u8])) = .ok false := sorry

theorem tooth_adrs_invalid_type_rejected :
    fips205.decode_fips205_adrs
      (Array.make 32#usize [
        0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
        0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8,
        0#u8, 0#u8, 0#u8, 7#u8, 0#u8, 0#u8, 0#u8, 0#u8,
        0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8, 0#u8]) = .ok none := sorry

theorem tower128_mul_eq_independent (a b : Std.U128) :
    tower.tower128_mul a b = .ok (pureTower128Mul a b) := sorry

theorem tower128_mul_comm (a b : tower.Tower128) :
    tower.tower128_mul a b = tower.tower128_mul b a := sorry

theorem tower_basis_square_vector : pureMulT2 4#u8 4#u8 = 9#u8 := sorry

theorem tower_basis_is_not_untranslated_artin_schreier :
    pureMulT2 4#u8 4#u8 ≠ 6#u8 := sorry

@[expose]
def BeltAckCountInvariant (st : authenticated_belt.VerifiedBeltQuorumGuard) : Prop :=
  st.inner.ack_count.val = (List.range 64).countP (fun i => st.ack_bitmap.bv.getLsbD i)

@[expose]
def repeatCustodianAck (epoch : Std.U64) (msg tag : Array Std.U8 32#usize) (id : Std.U8) :
    Nat → authenticated_belt.VerifiedBeltQuorumGuard → Result authenticated_belt.VerifiedBeltQuorumGuard
  | 0, st => .ok st
  | n + 1, st => do
      let (next, _) ← authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack st epoch msg id tag
      repeatCustodianAck epoch msg tag id n next

theorem authenticated_belt_initial_count_invariant
    (n t f q : Std.U32) (gl : Bool) (epoch window : Std.U64)
    (commit wal : Array Std.U8 32#usize) (keys : Array (Array Std.U8 32#usize) 64#usize)
    (st : authenticated_belt.VerifiedBeltQuorumGuard)
    (h : authenticated_belt.VerifiedBeltQuorumGuard.new_validated n t f q gl epoch window commit keys wal =
      .ok (core.result.Result.Ok st)) : BeltAckCountInvariant st := sorry

theorem authenticated_belt_forged_tag_fails_closed
    (st : authenticated_belt.VerifiedBeltQuorumGuard)
    (epoch : Std.U64) (msg key expected forged : Array Std.U8 32#usize) (id : Std.U8)
    (hin : ¬ UScalar.cast .Usize id >= UScalar.cast .Usize st.inner.n)
    (h64 : ¬ id >= 64#u8)
    (hkey : Array.index_usize st.custodian_keys (UScalar.cast .Usize id) = .ok key)
    (htag : authenticated_belt.custodian_ack_tag key st.guard_key_commit epoch msg id = .ok expected)
    (hforged : expected ≠ forged) :
    authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack st epoch msg id forged =
      .ok (st, core.result.Result.Err authenticated_belt.BeltAuthError.InvalidCustodianTag) := sorry

theorem authenticated_belt_duplicate_ack_unchanged
    (st : authenticated_belt.VerifiedBeltQuorumGuard)
    (epoch : Std.U64) (msg key tag : Array Std.U8 32#usize) (id : Std.U8) (bit : Std.U64)
    (hin : ¬ UScalar.cast .Usize id >= UScalar.cast .Usize st.inner.n)
    (h64 : ¬ id >= 64#u8)
    (hkey : Array.index_usize st.custodian_keys (UScalar.cast .Usize id) = .ok key)
    (htag : authenticated_belt.custodian_ack_tag key st.guard_key_commit epoch msg id = .ok tag)
    (hp : st.inner.poisoned = false) (hb : st.inner.has_bound_epoch = true)
    (he : epoch = st.inner.bound_epoch) (hm : msg = st.inner.bound_msg_tag)
    (hbit : (1#u64 <<< id : Result Std.U64) = .ok bit)
    (hused : st.ack_bitmap &&& bit ≠ 0#u64) :
    authenticated_belt.VerifiedBeltQuorumGuard.record_custodian_ack st epoch msg id tag =
      .ok (st, core.result.Result.Ok st.inner.ack_count) := sorry

theorem tooth_duplicate_custodian_cannot_reach_quorum
    (st : authenticated_belt.VerifiedBeltQuorumGuard)
    (epoch : Std.U64) (msg key tag : Array Std.U8 32#usize) (id : Std.U8) (bit : Std.U64)
    (hin : ¬ UScalar.cast .Usize id >= UScalar.cast .Usize st.inner.n)
    (h64 : ¬ id >= 64#u8)
    (hkey : Array.index_usize st.custodian_keys (UScalar.cast .Usize id) = .ok key)
    (htag : authenticated_belt.custodian_ack_tag key st.guard_key_commit epoch msg id = .ok tag)
    (hp : st.inner.poisoned = false) (hb : st.inner.has_bound_epoch = true)
    (he : epoch = st.inner.bound_epoch) (hm : msg = st.inner.bound_msg_tag)
    (hbit : (1#u64 <<< id : Result Std.U64) = .ok bit)
    (hused : st.ack_bitmap &&& bit ≠ 0#u64)
    (hone : st.inner.ack_count.val = 1) (hq : 2 ≤ st.inner.q.val) (calls : Nat) :
    repeatCustodianAck epoch msg tag id calls st = .ok st ∧ st.inner.ack_count.val < st.inner.q.val := sorry

theorem tower128_mul_zero (a : tower.Tower128) :
    tower.tower128_mul a 0#u128 = .ok 0#u128 := sorry

theorem tower128_mul_small_vectors :
    pureTower128Mul 0#u128 7#u128 = 0#u128 ∧
    pureTower128Mul 1#u128 7#u128 = 7#u128 ∧
    pureTower128Mul 2#u128 2#u128 = 3#u128 := sorry

end qsag_verified.proofs
