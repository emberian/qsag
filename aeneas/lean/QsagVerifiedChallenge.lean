module

public import Aeneas
public import QsagVerified.Types
public import QsagVerified.Funs
public import Qsag.Machine.ElfFunctionalEquiv
public import Qsag.Machine.McRefine
public import Qsag.Oracle.Keccak
public import Qsag.Math.Gf2Pow128
public import QsagVerifiedChallengeDefs2

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

It imports the generated model and canonical Keccak and binary-tower specifications,
but never a proofs module. Every specification definition
a statement mentions is declared again here or in the independent ChallengeDefs modules,
verbatim, so the comparison also
pins those definitions.

Every theorem body below is `sorry`. That is the comparator convention for a
statement file: only the types are compared, and the proofs are taken from the
solution module. This is the only module in the package where `sorry` appears.

Coverage boundary. Keccak is compared on every input lane and against the exact
zero-state vector. ADRS bytes have fixed field positions and big-endian encoding.
WOTS steps evaluate the extracted F at successive hash addresses; this pins the
chain semantics but does not establish full sponge absorb/padding equivalence.
Squeeze byte selection and canonical permutation at rate boundaries are checked.
BDOZ checks arbitrary batch residuals and one-shot handle consumption; fresh handle
provisioning and commitment-before-challenge remain caller obligations.
Lagrange reconstruction is covered for 2-of-2 and 3-of-3 only. Theorems outside the
roster in `comparator.json` are not checked by this gate.
-/

namespace qsag_verified.proofs

open Aeneas Aeneas.Std Result ControlFlow Error
open qsag_verified

set_option maxRecDepth 4096

/-! ## Goldilocks field (p = 2^64 - 2^32 + 1) and its quadratic extension -/




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



/-! ## FIPS 205: ADRS codec, WOTS+ checksum and chain -/





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























/-! ## Shamir sharing: Horner evaluation, point validation, Lagrange reconstruction -/

/-- Horner recurrence on the first `n` coefficients, consuming highest degree first. -/








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

theorem epoch_latch_from_cursor_well_formed (next limit : Std.U64)
    (key : Array Std.U8 32#usize) (last : threshold.LastBoundEpoch) (st : threshold.EpochLatch)
    (accepted : threshold.EpochLatch.from_cursor next limit key last = .ok (.Ok st)) :
    WellFormedWal st := by sorry

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


/-! ## Exact value and lifecycle conformance -/

@[expose] def keccakZeroExpected : Std.Array Std.U64 25#usize :=
  Std.Array.make 25#usize [
    17376452488221285863#u64, 9571781953733019530#u64, 15391093639620504046#u64, 13624874521033984333#u64, 10027350355371872343#u64,
    18417369716475457492#u64, 10448040663659726788#u64, 10113917136857017974#u64, 12479658147685402012#u64, 3500241080921619556#u64,
    16959053435453822517#u64, 12224711289652453635#u64, 9342009439668884831#u64, 4879704952849025062#u64, 140226327413610143#u64,
    424854978622500449#u64, 7259519967065370866#u64, 7004910057750291985#u64, 13293599522548616907#u64, 10105770293752443592#u64,
    10668034807192757780#u64, 1747952066141424100#u64, 1654286879329379778#u64, 8500057116360352059#u64, 16929593379567477321#u64
  ]

def keccakArrayOfState (s : Qsag.KState) : Array Std.U64 25#usize :=
  Array.make 25#usize [⟨s.a0.toBitVec⟩, ⟨s.a1.toBitVec⟩, ⟨s.a2.toBitVec⟩, ⟨s.a3.toBitVec⟩, ⟨s.a4.toBitVec⟩, ⟨s.a5.toBitVec⟩, ⟨s.a6.toBitVec⟩, ⟨s.a7.toBitVec⟩, ⟨s.a8.toBitVec⟩, ⟨s.a9.toBitVec⟩, ⟨s.a10.toBitVec⟩, ⟨s.a11.toBitVec⟩, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]

def keccakStateOfArray (a : Array Std.U64 25#usize) : Qsag.KState :=
  ⟨UInt64.ofBitVec (a.val.getD 0 0#u64).bv, UInt64.ofBitVec (a.val.getD 1 0#u64).bv, UInt64.ofBitVec (a.val.getD 2 0#u64).bv, UInt64.ofBitVec (a.val.getD 3 0#u64).bv, UInt64.ofBitVec (a.val.getD 4 0#u64).bv, UInt64.ofBitVec (a.val.getD 5 0#u64).bv, UInt64.ofBitVec (a.val.getD 6 0#u64).bv, UInt64.ofBitVec (a.val.getD 7 0#u64).bv, UInt64.ofBitVec (a.val.getD 8 0#u64).bv, UInt64.ofBitVec (a.val.getD 9 0#u64).bv, UInt64.ofBitVec (a.val.getD 10 0#u64).bv, UInt64.ofBitVec (a.val.getD 11 0#u64).bv, UInt64.ofBitVec (a.val.getD 12 0#u64).bv, UInt64.ofBitVec (a.val.getD 13 0#u64).bv, UInt64.ofBitVec (a.val.getD 14 0#u64).bv, UInt64.ofBitVec (a.val.getD 15 0#u64).bv, UInt64.ofBitVec (a.val.getD 16 0#u64).bv, UInt64.ofBitVec (a.val.getD 17 0#u64).bv, UInt64.ofBitVec (a.val.getD 18 0#u64).bv, UInt64.ofBitVec (a.val.getD 19 0#u64).bv, UInt64.ofBitVec (a.val.getD 20 0#u64).bv, UInt64.ofBitVec (a.val.getD 21 0#u64).bv, UInt64.ofBitVec (a.val.getD 22 0#u64).bv, UInt64.ofBitVec (a.val.getD 23 0#u64).bv, UInt64.ofBitVec (a.val.getD 24 0#u64).bv⟩

def adrsByte32 (v : Std.U32) (shift : Nat) : Std.U8 :=
  UScalar.cast .U8 ((⟨v.bv >>> shift⟩ : Std.U32) &&& 255#u32)

def adrsByte64 (v : Std.U64) (shift : Nat) : Std.U8 :=
  UScalar.cast .U8 ((⟨v.bv >>> shift⟩ : Std.U64) &&& 255#u64)

def adrsTypeWord : fips205.Fips205AdrsType → Std.U32
  | .WotsHash => 0#u32
  | .WotsPk => 1#u32
  | .Tree => 2#u32
  | .ForsTree => 3#u32
  | .ForsRoots => 4#u32
  | .WotsPrf => 5#u32
  | .ForsPrf => 6#u32

def adrsBytes (a : fips205.Fips205Adrs) : Std.Array Std.U8 32#usize :=
  Std.Array.make 32#usize [
    adrsByte32 a.layer 24, adrsByte32 a.layer 16, adrsByte32 a.layer 8, adrsByte32 a.layer 0,
    adrsByte32 a.tree_hi 24, adrsByte32 a.tree_hi 16, adrsByte32 a.tree_hi 8, adrsByte32 a.tree_hi 0,
    adrsByte64 a.tree_lo 56, adrsByte64 a.tree_lo 48, adrsByte64 a.tree_lo 40, adrsByte64 a.tree_lo 32, adrsByte64 a.tree_lo 24, adrsByte64 a.tree_lo 16, adrsByte64 a.tree_lo 8, adrsByte64 a.tree_lo 0,
    adrsByte32 (adrsTypeWord a.adrs_type) 24, adrsByte32 (adrsTypeWord a.adrs_type) 16, adrsByte32 (adrsTypeWord a.adrs_type) 8, adrsByte32 (adrsTypeWord a.adrs_type) 0,
    adrsByte32 a.kp 24, adrsByte32 a.kp 16, adrsByte32 a.kp 8, adrsByte32 a.kp 0,
    adrsByte32 a.chain 24, adrsByte32 a.chain 16, adrsByte32 a.chain 8, adrsByte32 a.chain 0,
    adrsByte32 a.hash 24, adrsByte32 a.hash 16, adrsByte32 a.hash 8, adrsByte32 a.hash 0]

@[expose] def wotsIter (pk_seed : Std.Array Std.U8 16#usize) (adrs : fips205.Fips205Adrs)
    (start : Nat) : Nat → Std.Array Std.U8 16#usize → Result (Std.Array Std.U8 16#usize)
  | 0, x => .ok x
  | n + 1, x => do
      let y ← fips205.fips205_f pk_seed { adrs with hash := ⟨BitVec.ofNat 32 start⟩ } x
      wotsIter pk_seed adrs (start + 1) n y

@[expose] def spongeRateByte (a : Array Std.U64 25#usize) (offset : Nat) : Std.U8 :=
  UScalar.cast .U8 ((⟨(a.val.getD (offset / 8) 0#u64).bv >>> (8 * (offset % 8))⟩ : Std.U64) &&& 255#u64)


theorem keccak_f1600_zero_state_nist :
    keccak.keccak_f1600 (Std.Array.repeat 25#usize 0#u64) =
      .ok keccakZeroExpected := sorry

theorem keccak_zero_expected_lane0 :
    keccakZeroExpected.val.getD 0 0#u64 = 0xF1258F7940E1DDE7#u64 := sorry

theorem keccak_f1600_array_refines_qsag (a : Array Std.U64 25#usize) :
    keccak.keccak_f1600 a =
      .ok (keccakArrayOfState (Qsag.keccakF1600 (keccakStateOfArray a))) := sorry

theorem adrs_encode_eq (a : fips205.Fips205Adrs) :
    fips205.encode_fips205_adrs a = .ok (adrsBytes a) := sorry

theorem fips205_wots_chain_steps (x pk : Std.Array Std.U8 16#usize)
    (a : fips205.Fips205Adrs) (start steps : Std.U32)
    (h : start.val + steps.val ≤ 15) :
    fips205.fips205_wots_chain x start steps pk a =
      (do let y ← wotsIter pk a start.val steps.val x; .ok (some y)) := sorry

theorem sponge_squeeze_byte (s : keccak.Shake256Sponge) (dst : Slice Std.U8)
    (i : Std.Usize) (hi : i.val < dst.val.length) (ho : s.squeeze_offset.val < 136) :
    ∃ dst' i' off',
      keccak.Shake256Sponge.squeeze_loop.body s dst i =
        .ok (.cont ({s with squeeze_offset := off'}, dst', i')) ∧
      dst'.val = dst.val.set i.val (spongeRateByte s.state s.squeeze_offset.val) ∧
      i'.val = i.val + 1 ∧ off'.val = s.squeeze_offset.val + 1 := sorry

theorem sponge_squeeze_rollover (s : keccak.Shake256Sponge) (dst : Slice Std.U8)
    (i : Std.Usize) (hi : i.val < dst.val.length) (ho : 136 ≤ s.squeeze_offset.val) :
    keccak.Shake256Sponge.squeeze_loop.body s dst i =
      keccak.Shake256Sponge.squeeze_loop.body
        {s with state := keccakArrayOfState (Qsag.keccakF1600 (keccakStateOfArray s.state)), squeeze_offset := 0#usize} dst i := sorry

theorem tower128_mul_refines_qsag (a b : Std.U128) :
    ∃ y, tower.tower128_mul a b = .ok y ∧
      Qsag.unpackTower 7 y.bv =
        Qsag.towerMul 7 (Qsag.unpackTower 7 a.bv) (Qsag.unpackTower 7 b.bv) := sorry

theorem tower128_mul_eq_zero_iff (a b : Std.U128) :
    tower.tower128_mul a b = .ok 0#u128 ↔ a = 0#u128 ∨ b = 0#u128 := sorry

theorem sigma_release_iff (sid : Array Std.U8 32#usize) (round : Std.U64)
    (binding : Array Std.U8 32#usize) (n : Std.U64) (xs : List OpeningInput) :
    (∃ t p, openingRound sid round binding n xs sid round binding = .ok (t, some p)) ↔
      (n ≠ 0#u64 ∧ xs.length = n.val ∧ (∀ x ∈ xs, x.1 = x.2.1) ∧
        openingLaneSum xs 0 = 0#u128 ∧ openingLaneSum xs 1 = 0#u128) := sorry

theorem sigma_release_permit (sid : Array Std.U8 32#usize) (round : Std.U64)
    (binding : Array Std.U8 32#usize) (n : Std.U64) (xs : List OpeningInput)
    (t : OpeningGuard) (p : OpeningPermit)
    (h : openingRound sid round binding n xs sid round binding = .ok (t, some p)) :
    p.session_id = sid ∧ p.round_id = round ∧ p.openings = n ∧ t.consumed = true := sorry

theorem plane_open_release_iff (sid : Array Std.U8 32#usize) (round : Std.U64)
    (binding copyPred copySucc : Array Std.U8 32#usize) :
    (∃ t p, openingRound sid round binding 1#u64
        [(copyPred, copySucc, Array.repeat 2#usize 0#u128)] sid round binding =
          .ok (t, some p)) ↔ copyPred = copySucc := sorry

theorem tooth_opening_wrong_context_refused (sid : Array Std.U8 32#usize) (round : Std.U64)
    (binding : Array Std.U8 32#usize) (n : Std.U64) (xs : List OpeningInput)
    (sid' : Array Std.U8 32#usize) (round' : Std.U64) (binding' : Array Std.U8 32#usize)
    (hctx : sid' ≠ sid ∨ round' ≠ round ∨ binding' ≠ binding) :
    ∃ t, openingRound sid round binding n xs sid' round' binding' = .ok (t, none) ∧
      t.consumed = true := sorry

theorem tooth_sigma_nonzero_lane_refused (sid : Array Std.U8 32#usize) (round : Std.U64)
    (binding c : Array Std.U8 32#usize) :
    ∃ t, openingRound sid round binding 1#u64
        [(c, c, Array.make 2#usize [1#u128, 0#u128])] sid round binding = .ok (t, none) := sorry

theorem shake256_32_refines (input : Slice Std.U8) :
    ∃ out, keccak.shake256_32 input = .ok out ∧
      u8Bytes out.val = Qsag.shake256Xof 32 (u8Bytes input.val) := sorry

def goldilocksAbs (x : goldilocks.Goldilocks) : Qsag.Goldilocks :=
  Qsag.Goldilocks.ofNat x.val

def mirFieldWord (a : Qsag.Goldilocks) : Std.U64 := ⟨BitVec.ofNat 64 a.val⟩

theorem elf_mir_goldilocks_add_x86_64 (a b : Qsag.Goldilocks) :
    ∃ slice prog y,
      Qsag.findSliceByNameBytes
        (Qsag.extractAllRlibFuncs Qsag.currentX86RlibArchiveBytes) Qsag.goldAddX86Name = some slice ∧
      Qsag.decodeX86Stream slice.code = some prog ∧
      goldilocks.goldilocks_add (mirFieldWord a) (mirFieldWord b) = .ok y ∧
      goldilocksAbs y = Qsag.Goldilocks.add a b ∧
      ∀ (s : Qsag.X86State) (fuel : Nat),
        s.pc = 0 → s.halted = false →
        s.gpr.get 7 = UInt64.ofNat a.val → s.gpr.get 6 = UInt64.ofNat b.val →
        25 ≤ fuel →
          (Qsag.runX86 prog fuel s).1.halted = true ∧
          (Qsag.runX86 prog fuel s).1.mem = s.mem ∧
          ((Qsag.runX86 prog fuel s).1.gpr.get 0).toNat = y.val := by sorry

theorem elf_mir_goldilocks_sub_x86_64 (a b : Qsag.Goldilocks) :
    ∃ slice prog y,
      Qsag.findSliceByNameBytes
        (Qsag.extractAllRlibFuncs Qsag.currentX86RlibArchiveBytes) Qsag.goldSubX86Name = some slice ∧
      Qsag.decodeX86Stream slice.code = some prog ∧
      goldilocks.goldilocks_sub (mirFieldWord a) (mirFieldWord b) = .ok y ∧
      goldilocksAbs y = Qsag.Goldilocks.sub a b ∧
      ∀ (s : Qsag.X86State) (fuel : Nat),
        s.pc = 0 → s.halted = false →
        s.gpr.get 7 = UInt64.ofNat a.val → s.gpr.get 6 = UInt64.ofNat b.val →
        31 ≤ fuel →
          (Qsag.runX86 prog fuel s).1.halted = true ∧
          (Qsag.runX86 prog fuel s).1.mem = s.mem ∧
          ((Qsag.runX86 prog fuel s).1.gpr.get 0).toNat = y.val := by sorry

theorem elf_mir_goldilocks_mul_x86_64 (a b : Qsag.Goldilocks) :
    ∃ slice prog y,
      Qsag.findSliceByNameBytes
        (Qsag.extractAllRlibFuncs Qsag.currentX86RlibArchiveBytes) Qsag.goldMulX86Name = some slice ∧
      Qsag.decodeX86Stream slice.code = some prog ∧
      goldilocks.goldilocks_mul (mirFieldWord a) (mirFieldWord b) = .ok y ∧
      goldilocksAbs y = Qsag.Goldilocks.mul a b ∧
      ∀ (s : Qsag.X86State) (fuel : Nat),
        s.pc = 0 → s.halted = false →
        s.gpr.get 7 = UInt64.ofNat a.val → s.gpr.get 6 = UInt64.ofNat b.val →
        33 ≤ fuel →
          (Qsag.runX86 prog fuel s).1.halted = true ∧
          (Qsag.runX86 prog fuel s).1.mem = s.mem ∧
          ((Qsag.runX86 prog fuel s).1.gpr.get 0).toNat = y.val := by sorry

theorem elf_mir_goldilocks_mul_aarch64 (a b : Qsag.Goldilocks) :
    ∃ slice prog y,
      Qsag.findSliceByNameBytes
        (Qsag.extractAllRlibFuncs Qsag.currentAarch64RlibArchiveBytes) Qsag.goldMulArmName = some slice ∧
      Qsag.decodeArm64Stream slice.code = some prog ∧
      goldilocks.goldilocks_mul (mirFieldWord a) (mirFieldWord b) = .ok y ∧
      goldilocksAbs y = Qsag.Goldilocks.mul a b ∧
      ∀ (s : Qsag.Arm64State) (fuel : Nat),
        s.pc = 0 → s.halted = false →
        s.gpr.get 0 = UInt64.ofNat a.val → s.gpr.get 1 = UInt64.ofNat b.val →
        30 ≤ fuel →
          (Qsag.runArm64 prog fuel s).1.halted = true ∧
          (Qsag.runArm64 prog fuel s).1.mem = s.mem ∧
          ((Qsag.runArm64 prog fuel s).1.gpr.get 0).toNat = y.val := by sorry

theorem mlDsa_abort_in_place_refuses_valid_checks
    (g : cred_and_hd_guards.MlDsaReleaseGate) (out₀ : Array Std.U8 32#usize) :
    let cOk : cred_and_hd_guards.MlDsaBarrierChecks :=
      ⟨g.session_id, g.attempt, true, true, true, true⟩
    ∃ g' : cred_and_hd_guards.MlDsaReleaseGate,
      cred_and_hd_guards.MlDsaReleaseGate.abort_in_place g = .ok g' ∧
      cred_and_hd_guards.MlDsaReleaseGate.try_release_z_share_into g' cOk out₀ =
        .ok (.Err .GateAbortedOrReleased, g', Array.repeat 32#usize 0#u8) := sorry

theorem mlDsa_try_release_into_eq_by_value
    (g : cred_and_hd_guards.MlDsaReleaseGate)
    (c : cred_and_hd_guards.MlDsaBarrierChecks)
    (out₀ : Array Std.U8 32#usize) :
    cred_and_hd_guards.MlDsaReleaseGate.try_release_z_share_into g c out₀ =
      Result.bind (cred_and_hd_guards.MlDsaReleaseGate.try_release_z_share g c)
        fun (g', res) =>
          match res with
          | .Ok z_out => .ok (.Ok (), g', z_out)
          | .Err err => .ok (.Err err, g', Array.repeat 32#usize 0#u8) := sorry

end qsag_verified.proofs
