module
public import Qsag.Oracle.Keccak
public import Qsag.Protocol.Aggregation.Aggregation
public import Qsag.Math.GoldilocksEncoding
public import Qsag.Math.QuinticExt5
public import Qsag.Math.GoldilocksBase


public import Qsag.Exec.PosixCrashWal
public import Qsag.Protocol.Signing.HashSigs
public import Qsag.Custody.JortsBeltLatchAndQuorumSwitching
public import Qsag.Protocol.Aggregation.Poseidon2AlgebraicAndRecursiveHem
public import Qsag.Math.Primality
public import Qsag.Oracle.Poseidon2
import Qsag.Tactic.AssuranceKit
public import Qsag.Math.Tactic.MaskBijection

public section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace Qsag.SpecOracle

open Qsag Aggregation

/-! ## 0. Core Oracle Predicates & Two-Slot Ledger Recovery -/

/-- Executable configuration predicate for the production global-liveness profile (`n ≤ 64`). -/
def quorumAccepts (t n f q : Nat) : Bool :=
  decide (0 < t ∧ t ≤ n ∧ n ≤ 64 ∧ 0 < q ∧ q ≤ n ∧ f < t ∧ t ≤ q ∧
    3 * f + 1 ≤ n ∧ n + f < 2 * q ∧ q ≤ n - f)

/-- Generic WOTS+C profile, including the unused zero suffix and exact digest width. -/
def wotsGenericAccepts (digest : List UInt8) : Bool :=
  match extractBaseWDigitsChecked 4 128 digest with
  | none => false
  | some digits => (digits.drop 127).all (· == 0) &&
      checkTargetSum 4 127 192 (digits.take 127)

/-- Production `WotsCParams::is_well_formed` + `WotsCParams::digits` gate
    (`crates/qsag-core/src/wots_c.rs:66-81`): only `WotsCParams::V128`
    (`chains = 128`, `zero_digits = 0`, `target_sum = 192`) is accepted,
    refusing every off-profile shape rather than decoding via an unverified path. -/
def wotsParamsAccepts (chains zeroDigits targetSum : Nat) (digest : List UInt8) : Bool :=
  decide (chains = 128 ∧ zeroDigits = 0 ∧ targetSum = 192) &&
  match extractBaseWDigitsChecked 4 128 digest with
  | none => false
  | some digits => checkTargetSum 4 128 192 digits

theorem wotsParamsAccepts_offProfile_rejected
    (chains zeroDigits targetSum : Nat) (digest : List UInt8)
    (hOff : ¬ (chains = 128 ∧ zeroDigits = 0 ∧ targetSum = 192)) :
    wotsParamsAccepts chains zeroDigits targetSum digest = false := by
  simp [wotsParamsAccepts, hOff]

/-- Explicit ASCII `"QSAG.FIRST.SIGNED"` bytes (`0` UTF-8 decoder dependency). -/
private def firstSignedDomainBytes : List UInt8 :=
  [0x51, 0x53, 0x41, 0x47, 0x2e, 0x46, 0x49, 0x52, 0x53, 0x54,
   0x2e, 0x53, 0x49, 0x47, 0x4e, 0x45, 0x44]

/-- Explicit ASCII `"snapshot"` bytes (`0` UTF-8 decoder dependency). -/
private def snapshotPurposeBytes : List UInt8 :=
  [0x73, 0x6e, 0x61, 0x70, 0x73, 0x68, 0x6f, 0x74]

/-- Deterministic fixture with real authenticated snapshot serialization and decoding.
Damage 1 truncates, 2 flips the final MAC byte, and 3 removes the slot. -/
def ledgerRecovery (damageA damageB checkpoint : Nat) : Option Nat := Id.run do
  let domain := firstSignedDomainBytes
  let key := List.replicate 32 (7 : UInt8)
  let genesisSeal := List.replicate 8 (1 : UInt8)
  let ledgerId := List.replicate 32 (2 : UInt8)
  let sealA := List.replicate 8 (3 : UInt8)
  let sealB := List.replicate 8 (4 : UInt8)
  let snapshot := fun generation =>
    let body := RustDurability.ledgerSnapshotBody generation []
    body ++ RustDurability.ledgerTag domain key genesisSeal ledgerId
      snapshotPurposeBytes body
  let damage := fun kind (bytes : List UInt8) => match kind with
    | 0 => some bytes
    | 1 => some (bytes.take (bytes.length / 2))
    | 2 => some (bytes.take (bytes.length - 1) ++ [bytes.getLastD 0 ^^^ 1])
    | _ => none
  let anchor : ExternalMonotoneAnchor :=
    ⟨checkpoint, (snapshot (min checkpoint 2)).drop 16⟩
  let genesis := RustDurability.ledgerGenesisBytes domain key genesisSeal ledgerId sealA sealB
  return (RustDurability.recoverLedgerBytes domain key genesisSeal ledgerId sealA sealB genesis
    anchor (damage damageA (snapshot 2)) (damage damageB (snapshot 1))).map (·.generation)

theorem quorum_privacy (t n f q : Nat) (h : quorumAccepts t n f q = true) : f < t := by
  simp only [quorumAccepts, decide_eq_true_eq] at h
  exact h.2.2.2.2.2.1

private theorem sumDigits_eq_sum : ∀ ds : List Nat, sumDigits ds = ds.sum
  | [] => by rw [sumDigits_nil, List.sum_nil]
  | d :: ds => by rw [sumDigits_cons, List.sum_cons, sumDigits_eq_sum ds]

private theorem checkTargetSum_eq_sum (w ell1 target : Nat) (digits : List Nat) :
    checkTargetSum w ell1 target digits =
      (decide (digits.length = ell1) && digits.all (fun d => decide (d < w)) &&
        decide (digits.sum = target)) := by
  simp only [checkTargetSum, sumDigits_eq_sum]

theorem generic_zero_digest_rejected :
    wotsGenericAccepts (List.replicate 32 0) = false := by
  simp only [wotsGenericAccepts, extractBaseWDigitsChecked_eq, extractBaseWDigits_eq,
    checkTargetSum_eq_sum]
  decide

/-- Production-profile digit guard used by differential WOTS vectors. -/
def wots128Accepts (digest : List UInt8) : Bool :=
  checkTargetSum 4 128 192 (extractBaseWDigits 4 128 digest)

/-- Removing the constant-sum guard accepts the all-zero digest. -/
theorem tooth_zero_digest_rejected :
    wots128Accepts (List.replicate 32 0) = false := by
  simp only [wots128Accepts, extractBaseWDigits_eq, checkTargetSum_eq_sum]
  decide

/-- Exact WOTS128 digest acceptance, including its wire size. -/
def ValidWots128Digest (digest : List UInt8) : Prop :=
  digest.length = 32 ∧ wots128Accepts digest = true

theorem accepted_digest_has_target_sum (digest : List UInt8)
    (h : ValidWots128Digest digest) :
    sumDigits (extractBaseWDigits 4 128 digest) = 192 := by
  have ha := h.2
  simp only [wots128Accepts, checkTargetSum, Bool.and_eq_true, decide_eq_true_eq] at ha
  exact ha.2

theorem witness_valid_digest : ∃ digest, ValidWots128Digest digest := by
  refine ⟨List.replicate 32 0x66, ?_⟩
  unfold ValidWots128Digest
  simp only [wots128Accepts, extractBaseWDigits_eq, checkTargetSum_eq_sum]
  decide

theorem tooth_zero_digest_invalid : ¬ ValidWots128Digest (List.replicate 32 0) := by
  intro h
  have hx := h.2
  rw [tooth_zero_digest_rejected] at hx
  cases hx

/-! ## 1. Verified `QuorumConfig` (`crates/qsag-quorum/src/quorum_jorts.rs:1249-1309`) -/

/-- Exact structural mirror of `qsag_quorum::quorum_jorts::QuorumConfig` (`Mode QS-B` global BFT). -/
structure QuorumConfig where
  t : Nat
  n : Nat
  f : Nat
  q : Nat
  deriving DecidableEq, Repr

/-- `QuorumConfig::with_quorum(t, n, f, q)`: accepts iff `quorumAccepts t n f q = true`. -/
def QuorumConfig.withQuorum (t n f q : Nat) : Option QuorumConfig :=
  if quorumAccepts t n f q then some ⟨t, n, f, q⟩ else none

/-- `QuorumConfig::new(t, n, f)`: smallest safe quorum `q = (n + f) / 2 + 1`. -/
def QuorumConfig.new (t n f : Nat) : Option QuorumConfig :=
  QuorumConfig.withQuorum t n f ((n + f) / 2 + 1)

/-- `QuorumConfig::tight(t)`: tightest global-liveness profile `n = 3t - 2`, `f = t - 1`, `q = 2t - 1`. -/
def QuorumConfig.tight (t : Nat) : Option QuorumConfig :=
  if 0 < t ∧ 3 * t - 2 ≤ 64 then QuorumConfig.new t (3 * t - 2) (t - 1) else none

def ValidQuorumConfig (cfg : QuorumConfig) : Prop :=
  QuorumConfig.withQuorum cfg.t cfg.n cfg.f cfg.q = some cfg

/-- Every accepted `QuorumConfig` enforces privacy (`f < t`), reconstruction (`t ≤ q`),
    honest availability (`q ≤ n - f`, `3f + 1 ≤ n`), and constructive BFT quorum intersection
    (`extractBeltHonestQuorumWitness`). -/
theorem quorumConfig_withQuorum_sound (cfg : QuorumConfig)
    (hValid : ValidQuorumConfig cfg) :
    0 < cfg.t ∧ cfg.t ≤ cfg.n ∧ cfg.n ≤ 64 ∧
    cfg.f < cfg.t ∧ cfg.t ≤ cfg.q ∧
    3 * cfg.f + 1 ≤ cfg.n ∧ cfg.n + cfg.f < 2 * cfg.q ∧ cfg.q ≤ cfg.n - cfg.f ∧
    (∀ (Q1 Q2 Corrupt : CustodiansMask cfg.n)
       (hQ1 : cfg.q ≤ maskCard Q1) (hQ2 : cfg.q ≤ maskCard Q2)
       (hC : maskCard Corrupt ≤ cfg.f),
       let w := extractBeltHonestQuorumWitness Q1 Q2 Corrupt
         (by
           unfold ValidQuorumConfig QuorumConfig.withQuorum quorumAccepts at hValid
           split at hValid
           · next ha => simp only [decide_eq_true_eq] at ha; omega
           · cases hValid) hQ1 hQ2 hC
       Q1.mem w.val = true ∧ Q2.mem w.val = true ∧ Corrupt.mem w.val = false) := by
  unfold ValidQuorumConfig QuorumConfig.withQuorum at hValid
  split at hValid
  · next ha =>
    simp only [quorumAccepts, decide_eq_true_eq] at ha
    rcases ha with ⟨ht0, htn, hn64, _, _, hft, htq, h3f, h2q, hqnf⟩
    refine ⟨ht0, htn, hn64, hft, htq, h3f, h2q, hqnf, ?_⟩
    intro Q1 Q2 Corrupt hQ1 hQ2 hC
    exact (extractBeltHonestQuorumWitness Q1 Q2 Corrupt h2q hQ1 hQ2 hC).property
  · cases hValid

/-- `QuorumConfig.tight t` constructs `⟨t, 3t - 2, t - 1, 2t - 1⟩` whenever `1 ≤ t` and `3t - 2 ≤ 64`. -/
theorem quorumConfig_tight_sound (t : Nat) (hPos : 0 < t) (hCap : 3 * t - 2 ≤ 64) :
    QuorumConfig.tight t = some ⟨t, 3 * t - 2, t - 1, 2 * t - 1⟩ := by
  have hLt23 : t < 23 :=
    if h : t < 23 then h
    else False.elim <| by
      have h23 : 23 ≤ t := Nat.le_of_not_lt h
      have h69 : 69 ≤ 3 * t := Nat.mul_le_mul_left 3 h23
      have h67 : 67 ≤ 3 * t - 2 := Nat.sub_le_sub_right h69 2
      exact Nat.not_le_of_gt (Nat.lt_of_lt_of_le (by decide : 64 < 67) h67) hCap
  have hFin : ∀ x : Fin 23, 0 < x.val → 3 * x.val - 2 ≤ 64 →
      QuorumConfig.tight x.val = some ⟨x.val, 3 * x.val - 2, x.val - 1, 2 * x.val - 1⟩ := by
    decide
  exact hFin ⟨t, hLt23⟩ hPos hCap

theorem witness_quorumConfig_valid : ∃ cfg : QuorumConfig, ValidQuorumConfig cfg := by
  refine ⟨⟨2, 4, 1, 3⟩, ?_⟩
  unfold ValidQuorumConfig QuorumConfig.withQuorum quorumAccepts
  decide

/-- `#tooth`: Split quorum `(t=2, n=4, f=1, q=2)` violates `2q > n + f` (`4 ≤ 5`) and is rejected. -/
theorem tooth_quorumConfig_rejects_split_quorum :
    ¬ ValidQuorumConfig ⟨2, 4, 1, 2⟩ := by
  unfold ValidQuorumConfig QuorumConfig.withQuorum quorumAccepts
  decide

/-! ## 2. Exported `SHA3-256`, `SHA3-512` & `Keccak-256` Digests (`crates/qsag-accel/src/keccak.rs`) -/

/-- NIST FIPS 202 `SHA3-256` (`rate = 136`, domain suffix `0x06`, 32-byte squeeze). -/
def sha3_256Bytes (input : List UInt8) : List UInt8 :=
  squeezeXofAux 32 (absorbPadded (padForRate input 0x06))

/-- Original `Keccak-256` (`rate = 136`, domain suffix `0x01`, 32-byte squeeze) matching `qsag_accel::keccak::keccak256`. -/
def keccak256Bytes (input : List UInt8) : List UInt8 :=
  squeezeXofAux 32 (absorbPadded (padForRate input 0x01))

/-- Rate-72 (`576`-bit, 9-lane) multi-rate `10*1` padding for `SHA3-512`. -/
def padRate72 (bytes : List UInt8) (suffix : UInt8) : List UInt8 :=
  let count := 72 - bytes.length % 72
  if count = 1 then
    bytes ++ [suffix ^^^ (0x80 : UInt8)]
  else
    bytes ++ [suffix] ++ List.replicate (count - 2) 0 ++ [0x80]

/-- XOR a 72-byte block into the 9 rate lanes `a0 .. a8` of `KState`. -/
def xorRate72 (s : KState) (block : List UInt8) : KState :=
  { s with
    a0 := s.a0 ^^^ loadLe64 block 0
    a1 := s.a1 ^^^ loadLe64 block 1
    a2 := s.a2 ^^^ loadLe64 block 2
    a3 := s.a3 ^^^ loadLe64 block 3
    a4 := s.a4 ^^^ loadLe64 block 4
    a5 := s.a5 ^^^ loadLe64 block 5
    a6 := s.a6 ^^^ loadLe64 block 6
    a7 := s.a7 ^^^ loadLe64 block 7
    a8 := s.a8 ^^^ loadLe64 block 8 }

def absorbBlocks72 : Nat → KState → List UInt8 → KState
  | 0, s, _ => s
  | k + 1, s, rest =>
    absorbBlocks72 k (keccakF1600 (xorRate72 s (rest.take 72))) (rest.drop 72)

def absorbPadded72 (padded : List UInt8) : KState :=
  absorbBlocks72 (padded.length / 72) zeroKState padded

/-- NIST FIPS 202 `SHA3-512` (`rate = 72`, domain suffix `0x06`, 64-byte squeeze ≤ 72). -/
def sha3_512Bytes (input : List UInt8) : List UInt8 :=
  squeezeXofAux 64 (absorbPadded72 (padRate72 input 0x06))

@[simp] theorem sha3_256Bytes_length (input : List UInt8) :
    (sha3_256Bytes input).length = 32 :=
  squeezeXofAux_length 32 _

@[simp] theorem keccak256Bytes_length (input : List UInt8) :
    (keccak256Bytes input).length = 32 :=
  squeezeXofAux_length 32 _

@[simp] theorem sha3_512Bytes_length (input : List UInt8) :
    (sha3_512Bytes input).length = 64 :=
  squeezeXofAux_length 64 _

/-- Official NIST FIPS 202 `SHA3-256("")` conformance theorem. -/
theorem sha3_256Bytes_empty_nist :
    sha3_256Bytes [] =
      [0xa7, 0xff, 0xc6, 0xf8, 0xbf, 0x1e, 0xd7, 0x66,
       0x51, 0xc1, 0x47, 0x56, 0xa0, 0x61, 0xd6, 0x62,
       0xf5, 0x80, 0xff, 0x4d, 0xe4, 0x3b, 0x49, 0xfa,
       0x82, 0xd8, 0x0a, 0x4b, 0x80, 0xf8, 0x43, 0x4a] :=
  sha3_256_empty_squeeze_kat

/-- Original `Keccak-256("")` digest. -/
theorem keccak256Bytes_empty :
    keccak256Bytes [] =
      [0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c,
       0x92, 0x7e, 0x7d, 0xb2, 0xdc, 0xc7, 0x03, 0xc0,
       0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b,
       0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70] :=
  keccak256_empty_squeeze_kat

/-- Official NIST FIPS 202 `SHA3-512("")` conformance theorem. -/
theorem sha3_512Bytes_empty_nist :
    sha3_512Bytes [] =
      [0xa6, 0x9f, 0x73, 0xcc, 0xa2, 0x3a, 0x9a, 0xc5,
       0xc8, 0xb5, 0x67, 0xdc, 0x18, 0x5a, 0x75, 0x6e,
       0x97, 0xc9, 0x82, 0x16, 0x4f, 0xe2, 0x58, 0x59,
       0xe0, 0xd1, 0xdc, 0xc1, 0x47, 0x5c, 0x80, 0xa6,
       0x15, 0xb2, 0x12, 0x3a, 0xf1, 0xf5, 0xf9, 0x4c,
       0x11, 0xe3, 0xe9, 0x40, 0x2c, 0x3a, 0xc5, 0x58,
       0xf5, 0x00, 0x19, 0x9d, 0x95, 0xb6, 0xd3, 0xe3,
       0x01, 0x75, 0x85, 0x86, 0x28, 0x1d, 0xcd, 0x26] := by
  have hPad : padRate72 [] 0x06 = 0x06 :: (List.replicate 70 0 ++ [0x80]) := by decide
  have hState : absorbPadded72 (padRate72 [] 0x06) =
      keccakF1600 ⟨0x06, 0, 0, 0, 0, 0, 0, 0, 0x8000000000000000, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ := by
    rw [hPad]
    change absorbBlocks72 1 zeroKState _ = _
    simp only [absorbBlocks72]
    congr 1
    rw [zeroKState_eq]
    simp only [xorRate72, loadLe64_eq]
    rfl
  unfold sha3_512Bytes
  rw [hState]
  exact sha3_512_empty_squeeze_kat

def Sha3_256Matches (msg digest : List UInt8) : Prop :=
  sha3_256Bytes msg = digest

theorem sha3_256Matches_width_and_keccak_sep (msg digest : List UInt8)
    (h : Sha3_256Matches msg digest) :
    digest.length = 32 ∧ (msg = [] → digest ≠ keccak256Bytes []) := by
  unfold Sha3_256Matches at h
  subst h
  refine ⟨sha3_256Bytes_length msg, fun hm => ?_⟩
  subst hm
  rw [sha3_256Bytes_empty_nist, keccak256Bytes_empty]
  decide

theorem witness_sha3_256Matches_empty :
    ∃ (msg digest : List UInt8), Sha3_256Matches msg digest :=
  ⟨[], sha3_256Bytes [], rfl⟩

/-- `#tooth`: Substituting Keccak-256 (`0x01` pad) for SHA3-256 (`0x06` pad) yields a distinct digest. -/
theorem tooth_sha3_256_rejects_keccak256_pad :
    ¬ Sha3_256Matches [] (keccak256Bytes []) := by
  unfold Sha3_256Matches
  rw [sha3_256Bytes_empty_nist, keccak256Bytes_empty]
  decide

/-! ## 3. Width-16 Goldilocks `Poseidon2` Permutation ($R_F = 8, R_P = 22$) -/

/-! Legacy width-16 invertibility model. Production uses canonical Poseidon2-12 from
`Qsag.Oracle.Poseidon2`; these historical helpers are retained only for the explicit legacy
oracle commands and make no production permutation claim. -/
namespace LegacyPoseidon16

def Poseidon2State16.toList (s : Poseidon2State16) : List Goldilocks :=
  [s.b0.x0, s.b0.x1, s.b0.x2, s.b0.x3,
   s.b1.x0, s.b1.x1, s.b1.x2, s.b1.x3,
   s.b2.x0, s.b2.x1, s.b2.x2, s.b2.x3,
   s.b3.x0, s.b3.x1, s.b3.x2, s.b3.x3]

def Poseidon2State16.ofList (ws : List Goldilocks) : Poseidon2State16 :=
  let g := fun i => ws.getD i Goldilocks.zero
  ⟨⟨g 0, g 1, g 2, g 3⟩, ⟨g 4, g 5, g 6, g 7⟩, ⟨g 8, g 9, g 10, g 11⟩, ⟨g 12, g 13, g 14, g 15⟩⟩

def state16Add (a b : Poseidon2State16) : Poseidon2State16 :=
  ⟨lane4Add a.b0 b.b0, lane4Add a.b1 b.b1, lane4Add a.b2 b.b2, lane4Add a.b3 b.b3⟩

def state16Sub (a b : Poseidon2State16) : Poseidon2State16 :=
  ⟨lane4Sub a.b0 b.b0, lane4Sub a.b1 b.b1, lane4Sub a.b2 b.b2, lane4Sub a.b3 b.b3⟩

def sboxState16 (st : Poseidon2State16) : Poseidon2State16 :=
  ⟨sboxLane4 st.b0, sboxLane4 st.b1, sboxLane4 st.b2, sboxLane4 st.b3⟩

def sboxState16Inv (st : Poseidon2State16) : Poseidon2State16 :=
  ⟨sboxLane4Inv st.b0, sboxLane4Inv st.b1, sboxLane4Inv st.b2, sboxLane4Inv st.b3⟩

private theorem sboxState16Inv_sboxState16 (st : Poseidon2State16) :
    sboxState16Inv (sboxState16 st) = st := by
  unfold sboxState16Inv sboxState16
  simp only [sboxLane4Inv_eq, sboxLane4_eq]
  apply Poseidon2State16.ext <;> apply Lane4.ext <;> exact sbox7Inv_sbox7 _

private theorem sboxState16_sboxState16Inv (st : Poseidon2State16) :
    sboxState16 (sboxState16Inv st) = st := by
  unfold sboxState16 sboxState16Inv
  simp only [sboxLane4Inv_eq, sboxLane4_eq]
  apply Poseidon2State16.ext <;> apply Lane4.ext <;> exact sbox7_sbox7Inv _

private theorem state16Sub_add_right (a c : Poseidon2State16) :
    state16Sub (state16Add a c) c = a := by
  have h4 : ∀ x y : Lane4, lane4Sub (lane4Add x y) y = x := fun x y => by
    simp only [lane4Sub_eq, lane4Add_eq]
    apply Lane4.ext <;> exact ring_add_sub_cancel_right _ _
  unfold state16Sub state16Add
  exact Poseidon2State16.ext (h4 _ _) (h4 _ _) (h4 _ _) (h4 _ _)

private theorem state16Add_sub_right (a c : Poseidon2State16) :
    state16Add (state16Sub a c) c = a := by
  have h4 : ∀ x y : Lane4, lane4Add (lane4Sub x y) y = x := fun x y => by
    simp only [lane4Add_eq, lane4Sub_eq]
    apply Lane4.ext <;> exact ring_sub_add_cancel_right _ _
  unfold state16Add state16Sub
  exact Poseidon2State16.ext (h4 _ _) (h4 _ _) (h4 _ _) (h4 _ _)

def state16Sum (st : Poseidon2State16) : Goldilocks :=
  Goldilocks.add
    (Goldilocks.add (Goldilocks.add (lane4Sum st.b0) (lane4Sum st.b1)) (lane4Sum st.b2))
    (lane4Sum st.b3)

/-- Width-16 Sherman–Morrison internal diffusion $M_I = J + \operatorname{diag}(-2, 1, 2, 4, \dots, 2^{14})$,
    with $\det(M_I) = \prod V_i \cdot (1 + \sum V_i^{-1})$ where $16384 \cdot (1 + \sum V_i^{-1}) = 40959 \not\equiv 0 \pmod p$. -/
def applyMI16 (st : Poseidon2State16) : Poseidon2State16 :=
  let s := state16Sum st
  ⟨⟨Goldilocks.add (Goldilocks.mul (goldOfInt (-2)) st.b0.x0) s,
    Goldilocks.add st.b0.x1 s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 2) st.b0.x2) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 4) st.b0.x3) s⟩,
   ⟨Goldilocks.add (Goldilocks.mul (goldOfInt 8) st.b1.x0) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 16) st.b1.x1) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 32) st.b1.x2) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 64) st.b1.x3) s⟩,
   ⟨Goldilocks.add (Goldilocks.mul (goldOfInt 128) st.b2.x0) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 256) st.b2.x1) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 512) st.b2.x2) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 1024) st.b2.x3) s⟩,
   ⟨Goldilocks.add (Goldilocks.mul (goldOfInt 2048) st.b3.x0) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 4096) st.b3.x1) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 8192) st.b3.x2) s,
    Goldilocks.add (Goldilocks.mul (goldOfInt 16384) st.b3.x3) s⟩⟩

private def inv16384G : Goldilocks := ⟨18445618169508003841, by decide⟩
private def inv40959G : Goldilocks := ⟨10284220826316121804, by decide⟩

private theorem gold_mul_cancel_16 {u k : Goldilocks}
    (h : Goldilocks.mul u k = Goldilocks.one) (x : Goldilocks) :
    Goldilocks.mul u (Goldilocks.mul k x) = x := by
  change CommRingOps.mul u (CommRingOps.mul k x) = x
  rw [← LawfulCommRing.mul_assoc]
  change CommRingOps.mul (Goldilocks.mul u k) x = x
  rw [h]
  exact LawfulCommRing.one_mul x

private theorem inv16384G_mul_cancel (x : Goldilocks) :
    Goldilocks.mul inv16384G (Goldilocks.mul (Goldilocks.ofNat 16384) x) = x :=
  gold_mul_cancel_16 (Goldilocks.ext (by rw [Goldilocks.mul_val]; decide)) x

private theorem inv40959G_mul_cancel (x : Goldilocks) :
    Goldilocks.mul inv40959G (Goldilocks.mul (Goldilocks.ofNat 40959) x) = x :=
  gold_mul_cancel_16 (Goldilocks.ext (by rw [Goldilocks.mul_val]; decide)) x

private theorem mul_inv40959G_cancel (x : Goldilocks) :
    Goldilocks.mul (Goldilocks.ofNat 40959) (Goldilocks.mul inv40959G x) = x :=
  gold_mul_cancel_16 (Goldilocks.ext (by rw [Goldilocks.mul_val]; decide)) x

private theorem ofNat_eq_goldOfInt_spec (k : Nat) :
    Goldilocks.ofNat k = goldOfInt (k : Int) := by
  apply Goldilocks.ext
  apply Int.ofNat_inj.mp
  rw [goldOfInt_val]
  simp [Goldilocks.ofNat, goldP, Int.natCast_emod]

private def weightedSumMI16 (y : Poseidon2State16) : Goldilocks :=
  let t0 := Goldilocks.add
    (Goldilocks.add (Goldilocks.mul (goldOfInt (-8192)) y.b0.x0) (Goldilocks.mul (goldOfInt 16384) y.b0.x1))
    (Goldilocks.add (Goldilocks.mul (goldOfInt 8192) y.b0.x2) (Goldilocks.mul (goldOfInt 4096) y.b0.x3))
  let t1 := Goldilocks.add
    (Goldilocks.add (Goldilocks.mul (goldOfInt 2048) y.b1.x0) (Goldilocks.mul (goldOfInt 1024) y.b1.x1))
    (Goldilocks.add (Goldilocks.mul (goldOfInt 512) y.b1.x2) (Goldilocks.mul (goldOfInt 256) y.b1.x3))
  let t2 := Goldilocks.add
    (Goldilocks.add (Goldilocks.mul (goldOfInt 128) y.b2.x0) (Goldilocks.mul (goldOfInt 64) y.b2.x1))
    (Goldilocks.add (Goldilocks.mul (goldOfInt 32) y.b2.x2) (Goldilocks.mul (goldOfInt 16) y.b2.x3))
  let t3 := Goldilocks.add
    (Goldilocks.add (Goldilocks.mul (goldOfInt 8) y.b3.x0) (Goldilocks.mul (goldOfInt 4) y.b3.x1))
    (Goldilocks.add (Goldilocks.mul (goldOfInt 2) y.b3.x2) y.b3.x3)
  Goldilocks.add (Goldilocks.add (Goldilocks.add t0 t1) t2) t3

private def makeMI16InvRaw (y : Poseidon2State16) (inv16384 s : Goldilocks) : Poseidon2State16 :=
  let scale (w : Int) (yi : Goldilocks) : Goldilocks :=
    Goldilocks.mul inv16384 (Goldilocks.mul (goldOfInt w) (Goldilocks.sub yi s))
  ⟨⟨scale (-8192) y.b0.x0, scale 16384 y.b0.x1, scale 8192 y.b0.x2, scale 4096 y.b0.x3⟩,
   ⟨scale 2048 y.b1.x0, scale 1024 y.b1.x1, scale 512 y.b1.x2, scale 256 y.b1.x3⟩,
   ⟨scale 128 y.b2.x0, scale 64 y.b2.x1, scale 32 y.b2.x2, scale 16 y.b2.x3⟩,
   ⟨scale 8 y.b3.x0, scale 4 y.b3.x1, scale 2 y.b3.x2, scale 1 y.b3.x3⟩⟩

def applyMI16Inv (y : Poseidon2State16) : Poseidon2State16 :=
  makeMI16InvRaw y inv16384G (Goldilocks.mul inv40959G (weightedSumMI16 y))

private theorem weightedSumMI16_applyMI16 (st : Poseidon2State16) :
    weightedSumMI16 (applyMI16 st) = Goldilocks.mul (Goldilocks.ofNat 40959) (state16Sum st) := by
  unfold weightedSumMI16 applyMI16 state16Sum
  simp only [lane4Sum_def]
  rw [← goldOfInt_nat st.b0.x0, ← goldOfInt_nat st.b0.x1, ← goldOfInt_nat st.b0.x2, ← goldOfInt_nat st.b0.x3,
      ← goldOfInt_nat st.b1.x0, ← goldOfInt_nat st.b1.x1, ← goldOfInt_nat st.b1.x2, ← goldOfInt_nat st.b1.x3,
      ← goldOfInt_nat st.b2.x0, ← goldOfInt_nat st.b2.x1, ← goldOfInt_nat st.b2.x2, ← goldOfInt_nat st.b2.x3,
      ← goldOfInt_nat st.b3.x0, ← goldOfInt_nat st.b3.x1, ← goldOfInt_nat st.b3.x2, ← goldOfInt_nat st.b3.x3]
  simp only [ofNat_eq_goldOfInt_spec, goldOfInt_add, goldOfInt_mul]
  congr 1; omega

private theorem mi16_lane_recover (v w : Int) (hv : v * w = 16384) (x s : Goldilocks) :
    Goldilocks.mul inv16384G (Goldilocks.mul (goldOfInt w)
      (Goldilocks.sub (Goldilocks.add (Goldilocks.mul (goldOfInt v) x) s) s)) = x := by
  have hProd : Goldilocks.mul (goldOfInt w)
      (Goldilocks.sub (Goldilocks.add (Goldilocks.mul (goldOfInt v) x) s) s) =
      Goldilocks.mul (Goldilocks.ofNat 16384) x := by
    rw [← goldOfInt_nat x, ← goldOfInt_nat s, ofNat_eq_goldOfInt_spec]
    simp only [goldOfInt_add, goldOfInt_sub, goldOfInt_mul]
    congr 1
    have hEq : w * (v * (x.val : Int) + (s.val : Int) - (s.val : Int)) = (v * w) * (x.val : Int) := by
      rw [Int.add_sub_cancel, ← Int.mul_assoc, Int.mul_comm w v]
    rw [hEq, hv]
    omega
  rw [hProd, inv16384G_mul_cancel x]

theorem applyMI16Inv_applyMI16 (st : Poseidon2State16) : applyMI16Inv (applyMI16 st) = st := by
  unfold applyMI16Inv
  rw [weightedSumMI16_applyMI16, inv40959G_mul_cancel (state16Sum st)]
  unfold makeMI16InvRaw applyMI16
  dsimp only
  have h1 : Goldilocks.add st.b0.x1 (state16Sum st) =
      Goldilocks.add (Goldilocks.mul (goldOfInt 1) st.b0.x1) (state16Sum st) := by
    have hone : goldOfInt 1 = CommRingOps.one := rfl
    change _ = Goldilocks.add (CommRingOps.mul (goldOfInt 1) st.b0.x1) _
    rw [hone, LawfulCommRing.one_mul]
  apply Poseidon2State16.ext
  · apply Lane4.ext
    · exact mi16_lane_recover (-2) (-8192) rfl st.b0.x0 (state16Sum st)
    · rw [h1]; exact mi16_lane_recover 1 16384 rfl st.b0.x1 (state16Sum st)
    · exact mi16_lane_recover 2 8192 rfl st.b0.x2 (state16Sum st)
    · exact mi16_lane_recover 4 4096 rfl st.b0.x3 (state16Sum st)
  · apply Lane4.ext
    · exact mi16_lane_recover 8 2048 rfl st.b1.x0 (state16Sum st)
    · exact mi16_lane_recover 16 1024 rfl st.b1.x1 (state16Sum st)
    · exact mi16_lane_recover 32 512 rfl st.b1.x2 (state16Sum st)
    · exact mi16_lane_recover 64 256 rfl st.b1.x3 (state16Sum st)
  · apply Lane4.ext
    · exact mi16_lane_recover 128 128 rfl st.b2.x0 (state16Sum st)
    · exact mi16_lane_recover 256 64 rfl st.b2.x1 (state16Sum st)
    · exact mi16_lane_recover 512 32 rfl st.b2.x2 (state16Sum st)
    · exact mi16_lane_recover 1024 16 rfl st.b2.x3 (state16Sum st)
  · apply Lane4.ext
    · exact mi16_lane_recover 2048 8 rfl st.b3.x0 (state16Sum st)
    · exact mi16_lane_recover 4096 4 rfl st.b3.x1 (state16Sum st)
    · exact mi16_lane_recover 8192 2 rfl st.b3.x2 (state16Sum st)
    · exact mi16_lane_recover 16384 1 rfl st.b3.x3 (state16Sum st)

private theorem mi16_lane_assoc_aux (v w : Int) (hv : v * w = 16384) (inv16384 yi s : Goldilocks) :
    Goldilocks.mul (goldOfInt v)
      (Goldilocks.mul inv16384 (Goldilocks.mul (goldOfInt w) (Goldilocks.sub yi s))) =
      Goldilocks.mul inv16384 (Goldilocks.mul (Goldilocks.ofNat 16384) (Goldilocks.sub yi s)) := by
  rw [← goldOfInt_nat inv16384, ← goldOfInt_nat yi, ← goldOfInt_nat s, ofNat_eq_goldOfInt_spec]
  simp only [goldOfInt_sub, goldOfInt_mul]
  congr 1
  have hEq : v * ((inv16384.val : Int) * (w * ((yi.val : Int) - (s.val : Int)))) =
      (inv16384.val : Int) * ((v * w) * ((yi.val : Int) - (s.val : Int))) := by
    rw [← Int.mul_assoc, ← Int.mul_assoc, Int.mul_comm v (inv16384.val : Int),
        Int.mul_assoc (inv16384.val : Int) v w, Int.mul_assoc]
  rw [hEq, hv]
  rfl

private theorem mi16_lane_forward (v w : Int) (hv : v * w = 16384) (yi s : Goldilocks) :
    Goldilocks.add (Goldilocks.mul (goldOfInt v)
      (Goldilocks.mul inv16384G (Goldilocks.mul (goldOfInt w) (Goldilocks.sub yi s)))) s = yi := by
  rw [mi16_lane_assoc_aux v w hv inv16384G yi s, inv16384G_mul_cancel (Goldilocks.sub yi s)]
  exact ring_sub_add_cancel_right yi s

private theorem state16Sum_makeMI16InvRaw (y : Poseidon2State16) (inv16384 s : Goldilocks) :
    state16Sum (makeMI16InvRaw y inv16384 s) =
      Goldilocks.mul inv16384 (Goldilocks.sub (weightedSumMI16 y) (Goldilocks.mul (goldOfInt 24575) s)) := by
  unfold state16Sum makeMI16InvRaw weightedSumMI16
  simp only [lane4Sum_def]
  rw [← goldOfInt_nat inv16384, ← goldOfInt_nat s,
      ← goldOfInt_nat y.b0.x0, ← goldOfInt_nat y.b0.x1, ← goldOfInt_nat y.b0.x2, ← goldOfInt_nat y.b0.x3,
      ← goldOfInt_nat y.b1.x0, ← goldOfInt_nat y.b1.x1, ← goldOfInt_nat y.b1.x2, ← goldOfInt_nat y.b1.x3,
      ← goldOfInt_nat y.b2.x0, ← goldOfInt_nat y.b2.x1, ← goldOfInt_nat y.b2.x2, ← goldOfInt_nat y.b2.x3,
      ← goldOfInt_nat y.b3.x0, ← goldOfInt_nat y.b3.x1, ← goldOfInt_nat y.b3.x2, ← goldOfInt_nat y.b3.x3]
  simp only [goldOfInt_add, goldOfInt_sub, goldOfInt_mul, ← Int.mul_add]
  congr 1; congr 1; omega

private theorem mi16_40959_sub_24575 (s : Goldilocks) :
    Goldilocks.sub (Goldilocks.mul (Goldilocks.ofNat 40959) s) (Goldilocks.mul (goldOfInt 24575) s) =
      Goldilocks.mul (Goldilocks.ofNat 16384) s := by
  rw [← goldOfInt_nat s, ofNat_eq_goldOfInt_spec, ofNat_eq_goldOfInt_spec]
  simp only [goldOfInt_sub, goldOfInt_mul]
  congr 1; omega

theorem applyMI16_applyMI16Inv (y : Poseidon2State16) : applyMI16 (applyMI16Inv y) = y := by
  let s := Goldilocks.mul inv40959G (weightedSumMI16 y)
  have hs40959 : Goldilocks.mul (Goldilocks.ofNat 40959) s = weightedSumMI16 y :=
    mul_inv40959G_cancel (weightedSumMI16 y)
  have hSumEq : state16Sum (makeMI16InvRaw y inv16384G s) = s := by
    rw [state16Sum_makeMI16InvRaw]
    conv => lhs; arg 2; arg 1; rw [← hs40959]
    rw [mi16_40959_sub_24575, inv16384G_mul_cancel]
  unfold applyMI16 applyMI16Inv
  change applyMI16 (makeMI16InvRaw y inv16384G s) = y
  unfold applyMI16
  rw [hSumEq]
  unfold makeMI16InvRaw
  dsimp only
  have h1 : ∀ a : Goldilocks, a = Goldilocks.mul (goldOfInt 1) a := fun a => by
    rw [← goldOfInt_nat a, goldOfInt_mul, Int.one_mul]
  apply Poseidon2State16.ext
  · apply Lane4.ext
    · exact mi16_lane_forward (-2) (-8192) rfl y.b0.x0 s
    · rw [h1 (Goldilocks.mul inv16384G (Goldilocks.mul (goldOfInt 16384) (Goldilocks.sub y.b0.x1 s)))]
      exact mi16_lane_forward 1 16384 rfl y.b0.x1 s
    · exact mi16_lane_forward 2 8192 rfl y.b0.x2 s
    · exact mi16_lane_forward 4 4096 rfl y.b0.x3 s
  · apply Lane4.ext
    · exact mi16_lane_forward 8 2048 rfl y.b1.x0 s
    · exact mi16_lane_forward 16 1024 rfl y.b1.x1 s
    · exact mi16_lane_forward 32 512 rfl y.b1.x2 s
    · exact mi16_lane_forward 64 256 rfl y.b1.x3 s
  · apply Lane4.ext
    · exact mi16_lane_forward 128 128 rfl y.b2.x0 s
    · exact mi16_lane_forward 256 64 rfl y.b2.x1 s
    · exact mi16_lane_forward 512 32 rfl y.b2.x2 s
    · exact mi16_lane_forward 1024 16 rfl y.b2.x3 s
  · apply Lane4.ext
    · exact mi16_lane_forward 2048 8 rfl y.b3.x0 s
    · exact mi16_lane_forward 4096 4 rfl y.b3.x1 s
    · exact mi16_lane_forward 8192 2 rfl y.b3.x2 s
    · exact mi16_lane_forward 16384 1 rfl y.b3.x3 s

def externalRound16 (rc st : Poseidon2State16) : Poseidon2State16 :=
  applyME16 (sboxState16 (state16Add st rc))

def externalRound16Inv (rc st : Poseidon2State16) : Poseidon2State16 :=
  state16Sub (sboxState16Inv (applyME16Inv st)) rc

private theorem externalRound16Inv_externalRound16 (rc st : Poseidon2State16) :
    externalRound16Inv rc (externalRound16 rc st) = st := by
  unfold externalRound16Inv externalRound16
  rw [applyME16Inv_applyME16, sboxState16Inv_sboxState16, state16Sub_add_right]

private theorem externalRound16_externalRound16Inv (rc st : Poseidon2State16) :
    externalRound16 rc (externalRound16Inv rc st) = st := by
  unfold externalRound16 externalRound16Inv
  rw [state16Add_sub_right, sboxState16_sboxState16Inv, applyME16_applyME16Inv]

def internalRound16 (rc : Goldilocks) (st : Poseidon2State16) : Poseidon2State16 :=
  let x0' := sbox7 (Goldilocks.add st.b0.x0 rc)
  applyMI16 ⟨⟨x0', st.b0.x1, st.b0.x2, st.b0.x3⟩, st.b1, st.b2, st.b3⟩

def internalRound16Inv (rc : Goldilocks) (st : Poseidon2State16) : Poseidon2State16 :=
  let u := applyMI16Inv st
  let x0 := Goldilocks.sub (sbox7Inv u.b0.x0) rc
  ⟨⟨x0, u.b0.x1, u.b0.x2, u.b0.x3⟩, u.b1, u.b2, u.b3⟩

private theorem gold_add_sub_cancel16 (a b : Goldilocks) :
    Goldilocks.sub (Goldilocks.add a b) b = a :=
  ring_add_sub_cancel_right a b

private theorem gold_sub_add_cancel16 (a b : Goldilocks) :
    Goldilocks.add (Goldilocks.sub a b) b = a :=
  ring_sub_add_cancel_right a b

private theorem internalRound16Inv_internalRound16 (rc : Goldilocks) (st : Poseidon2State16) :
    internalRound16Inv rc (internalRound16 rc st) = st := by
  unfold internalRound16Inv internalRound16
  rw [applyMI16Inv_applyMI16]
  dsimp only
  rw [sbox7Inv_sbox7, gold_add_sub_cancel16]

private theorem internalRound16_internalRound16Inv (rc : Goldilocks) (st : Poseidon2State16) :
    internalRound16 rc (internalRound16Inv rc st) = st := by
  unfold internalRound16Inv
  dsimp only
  cases h : applyMI16Inv st with | mk b0 b1 b2 b3 =>
    cases b0 with | mk x0 x1 x2 x3 =>
      unfold internalRound16
      dsimp only
      rw [gold_sub_add_cancel16, sbox7_sbox7Inv, ← h, applyMI16_applyMI16Inv]

def poseidon2ExtRoundConst16 (tag round : Nat) : Poseidon2State16 :=
  ⟨⟨poseidon2ConstAt tag round 0, poseidon2ConstAt tag round 1,
    poseidon2ConstAt tag round 2, poseidon2ConstAt tag round 3⟩,
   ⟨poseidon2ConstAt tag round 4, poseidon2ConstAt tag round 5,
    poseidon2ConstAt tag round 6, poseidon2ConstAt tag round 7⟩,
   ⟨poseidon2ConstAt tag round 8, poseidon2ConstAt tag round 9,
    poseidon2ConstAt tag round 10, poseidon2ConstAt tag round 11⟩,
   ⟨poseidon2ConstAt tag round 12, poseidon2ConstAt tag round 13,
    poseidon2ConstAt tag round 14, poseidon2ConstAt tag round 15⟩⟩

def poseidon2InitialExtConsts16 : List Poseidon2State16 :=
  (List.range 4).map (poseidon2ExtRoundConst16 0)

def poseidon2InternalConsts16 : List Goldilocks :=
  (List.range 22).map (fun r => poseidon2ConstAt 1 r 0)

def poseidon2TerminalExtConsts16 : List Poseidon2State16 :=
  (List.range 4).map (poseidon2ExtRoundConst16 2)

/-- Full 30-round Width-16 Goldilocks `Poseidon2` permutation ($R_F = 8, R_P = 22$). -/
def poseidon2Perm16 (st : Poseidon2State16) : Poseidon2State16 :=
  let s0 := applyME16 st
  let s1 := runRounds externalRound16 poseidon2InitialExtConsts16 s0
  let s2 := runRounds internalRound16 poseidon2InternalConsts16 s1
  runRounds externalRound16 poseidon2TerminalExtConsts16 s2

/-- Exact two-sided inverse of `poseidon2Perm16`. -/
def poseidon2Perm16Inv (st : Poseidon2State16) : Poseidon2State16 :=
  let s2 := runRoundsInv externalRound16Inv poseidon2TerminalExtConsts16 st
  let s1 := runRoundsInv internalRound16Inv poseidon2InternalConsts16 s2
  let s0 := runRoundsInv externalRound16Inv poseidon2InitialExtConsts16 s1
  applyME16Inv s0

private theorem runRoundsInv_runRounds16 {α σ : Type} (step stepInv : α → σ → σ)
    (hInv : ∀ c s, stepInv c (step c s) = s) (cs : List α) :
    ∀ (s : σ), runRoundsInv stepInv cs (runRounds step cs s) = s := by
  induction cs with
  | nil => intro _; rw [runRounds_nil, runRoundsInv_nil]
  | cons c cs ih => intro s; simp only [runRounds_cons, runRoundsInv_cons, ih (step c s), hInv]

private theorem runRounds_runRoundsInv16 {α σ : Type} (step stepInv : α → σ → σ)
    (hInv : ∀ c s, step c (stepInv c s) = s) (cs : List α) :
    ∀ (s : σ), runRounds step cs (runRoundsInv stepInv cs s) = s := by
  induction cs with
  | nil => intro _; rw [runRoundsInv_nil, runRounds_nil]
  | cons c cs ih => intro s; simp only [runRoundsInv_cons, runRounds_cons, hInv, ih s]

theorem poseidon2Perm16Inv_left_inv (st : Poseidon2State16) :
    poseidon2Perm16Inv (poseidon2Perm16 st) = st := by
  unfold poseidon2Perm16Inv poseidon2Perm16
  dsimp only
  rw [runRoundsInv_runRounds16 externalRound16 externalRound16Inv externalRound16Inv_externalRound16,
      runRoundsInv_runRounds16 internalRound16 internalRound16Inv internalRound16Inv_internalRound16,
      runRoundsInv_runRounds16 externalRound16 externalRound16Inv externalRound16Inv_externalRound16,
      applyME16Inv_applyME16]

theorem poseidon2Perm16Inv_right_inv (st : Poseidon2State16) :
    poseidon2Perm16 (poseidon2Perm16Inv st) = st := by
  unfold poseidon2Perm16 poseidon2Perm16Inv
  dsimp only
  rw [applyME16_applyME16Inv,
      runRounds_runRoundsInv16 externalRound16 externalRound16Inv externalRound16_externalRound16Inv,
      runRounds_runRoundsInv16 internalRound16 internalRound16Inv internalRound16_internalRound16Inv,
      runRounds_runRoundsInv16 externalRound16 externalRound16Inv externalRound16_externalRound16Inv]

def Poseidon16Pair (inp out : Poseidon2State16) : Prop :=
  poseidon2Perm16 inp = out

theorem poseidon2Perm16_pair_invertible (inp out : Poseidon2State16)
    (h : Poseidon16Pair inp out) :
    poseidon2Perm16Inv out = inp ∧
    (∀ alt : Poseidon2State16, poseidon2Perm16 alt = out → alt = inp) := by
  unfold Poseidon16Pair at h
  subst h
  refine ⟨poseidon2Perm16Inv_left_inv inp, fun alt hAlt => ?_⟩
  have hInv := congrArg poseidon2Perm16Inv hAlt
  rwa [poseidon2Perm16Inv_left_inv, poseidon2Perm16Inv_left_inv] at hInv

theorem witness_poseidon2Perm16_pair :
    ∃ (inp out : Poseidon2State16), Poseidon16Pair inp out :=
  ⟨state16Zero, poseidon2Perm16 state16Zero, rfl⟩

/-! Kernel-transparent forms of the round functions. Each one is obtained by rewriting the
round with the public defining equations of the `Qsag.Oracle.Poseidon2` operations it calls, so
the kernel can evaluate the permutation on a concrete state. -/

private def applyME16K :
    { f : Poseidon2State16 → Poseidon2State16 // ∀ st, applyME16 st = f st } :=
  ⟨_, fun st => by
    simp only [applyME16_eq, applyM4_eq, lane4Add_eq, lane4Sum_def]
    rfl⟩

private def externalRound16K :
    { f : Poseidon2State16 → Poseidon2State16 → Poseidon2State16 //
      ∀ rc st, externalRound16 rc st = f rc st } :=
  ⟨_, fun rc st => by
    simp only [externalRound16, sboxState16, state16Add, applyME16_eq, applyM4_eq, lane4Add_eq,
      lane4Sum_def, sboxLane4_eq]
    rfl⟩

private def internalRound16K :
    { f : Goldilocks → Poseidon2State16 → Poseidon2State16 //
      ∀ rc st, internalRound16 rc st = f rc st } :=
  ⟨_, fun rc st => by
    simp only [internalRound16, applyMI16, state16Sum, lane4Sum_def]
    rfl⟩

private def poseidon2ConstAtK :
    { f : Nat → Nat → Nat → Goldilocks // ∀ tag round lane, poseidon2ConstAt tag round lane = f tag round lane } :=
  ⟨_, fun tag round lane => by
    simp only [poseidon2ConstAt_eq, splitMix64Mix_eq]
    rfl⟩

private theorem applyME16_eqK (st : Poseidon2State16) : applyME16 st = applyME16K.val st :=
  applyME16K.property st

private theorem externalRound16_eqK (rc st : Poseidon2State16) :
    externalRound16 rc st = externalRound16K.val rc st :=
  externalRound16K.property rc st

private theorem internalRound16_eqK (rc : Goldilocks) (st : Poseidon2State16) :
    internalRound16 rc st = internalRound16K.val rc st :=
  internalRound16K.property rc st

private theorem poseidon2ConstAt_eqK (tag round lane : Nat) :
    poseidon2ConstAt tag round lane = poseidon2ConstAtK.val tag round lane :=
  poseidon2ConstAtK.property tag round lane

/-- `#tooth`: Round constants make `poseidon2Perm16` non-fixing on `state16Zero`. -/
theorem tooth_poseidon2Perm16_zero_not_fixed :
    ¬ Poseidon16Pair state16Zero state16Zero := by
  unfold Poseidon16Pair
  intro h
  have hE : poseidon2InitialExtConsts16 =
      [poseidon2ExtRoundConst16 0 0, poseidon2ExtRoundConst16 0 1,
       poseidon2ExtRoundConst16 0 2, poseidon2ExtRoundConst16 0 3] := rfl
  have hI : poseidon2InternalConsts16 =
      [poseidon2ConstAt 1 0 0, poseidon2ConstAt 1 1 0, poseidon2ConstAt 1 2 0, poseidon2ConstAt 1 3 0, poseidon2ConstAt 1 4 0, poseidon2ConstAt 1 5 0, poseidon2ConstAt 1 6 0, poseidon2ConstAt 1 7 0, poseidon2ConstAt 1 8 0, poseidon2ConstAt 1 9 0, poseidon2ConstAt 1 10 0, poseidon2ConstAt 1 11 0, poseidon2ConstAt 1 12 0, poseidon2ConstAt 1 13 0, poseidon2ConstAt 1 14 0, poseidon2ConstAt 1 15 0, poseidon2ConstAt 1 16 0, poseidon2ConstAt 1 17 0, poseidon2ConstAt 1 18 0, poseidon2ConstAt 1 19 0, poseidon2ConstAt 1 20 0, poseidon2ConstAt 1 21 0] := rfl
  have hT : poseidon2TerminalExtConsts16 =
      [poseidon2ExtRoundConst16 2 0, poseidon2ExtRoundConst16 2 1,
       poseidon2ExtRoundConst16 2 2, poseidon2ExtRoundConst16 2 3] := rfl
  unfold poseidon2Perm16 at h
  rw [hE, hI, hT] at h
  simp only [runRounds_cons, runRounds_nil, externalRound16_eqK, internalRound16_eqK,
    applyME16_eqK, poseidon2ExtRoundConst16, poseidon2ConstAt_eqK, state16Zero_eq,
    lane4Zero_eq] at h
  exact absurd (congrArg (fun s => s.b0.x0.val) h) (by decide +kernel)

end LegacyPoseidon16

/-! ## 4. `Hem` Affine Duet Fold & CWYZ Sumcheck Bridge (`aeneas/qsag-whir-verified/src/lib.rs`) -/


/-! ## 5. POSIX Crash WAL Schedules (`DurableBurnJournal` & `FsBeltWal`) -/

/-- Events exercised against the byte-level `QSBURN05` `DurableBurnJournal` (`crates/qsag-fts/src/wal.rs`)
    and `RustDurability.openBurnBytes` (`lean/Qsag/PosixCrashWal.lean`). -/
inductive PosixBurnEvent where
  | reserve (party epoch : Nat)
  | retain
  | reopen
  | tear (len : Nat)
  | trunc
  | flip
  | copy
  deriving DecidableEq, Repr

structure PosixBurnState where
  diskBytes : List UInt8
  inode : Nat
  /-- `some (bodies, lastTag)` while an unfailed descriptor is open; `none` when closed/poisoned. -/
  openState : Option (List (List UInt8) × List UInt8)
  retained : Option ExternalMonotoneAnchor
  deriving DecidableEq, Repr

private def posixBurnMacKey : List UInt8 := List.replicate 32 (2 : UInt8)
private def posixBurnKeyId : List UInt8 := List.replicate 32 (1 : UInt8)
private def posixBurnGenesis : List UInt8 := List.replicate 32 (9 : UInt8)

def PosixBurnState.init : PosixBurnState :=
  let id0 := RustDurability.burnIdentity 1 100
  let hdr := RustDurability.burnHeader posixBurnMacKey id0 posixBurnKeyId posixBurnGenesis
  let tag0 := RustDurability.burnGenesisTag posixBurnMacKey id0 posixBurnKeyId posixBurnGenesis
  { diskBytes := hdr
    inode := 100
    openState := some ([], tag0)
    retained := none }

private def reopenPosixBurnDisk (diskBytes : List UInt8) (inode : Nat)
    (retained : Option ExternalMonotoneAnchor) : Option (List (List UInt8) × List UInt8) :=
  let idBytes := RustDurability.burnIdentity 1 inode
  match RustDurability.openBurnBytes posixBurnMacKey idBytes posixBurnKeyId diskBytes with
  | none => none
  | some (bodies, lastTag) =>
    match retained with
    | none => some (bodies, lastTag)
    | some anchor =>
      if verifyAgainstExternalAnchor anchor bodies.length lastTag then
        some (bodies, lastTag)
      else none

inductive PosixBurnOutcome where
  | ok
  | okCount (count : Nat)
  | err
  deriving DecidableEq, Repr

def PosixBurnOutcome.render : PosixBurnOutcome → String
  | .ok => "ok"
  | .okCount n => "ok:" ++ toString n
  | .err => "err"

def posixBurnStep (st : PosixBurnState) (ev : PosixBurnEvent) : PosixBurnState × PosixBurnOutcome :=
  match ev with
  | .reserve party epoch =>
    match st.openState with
    | none => (st, .err)
    | some (bodies, lastTag) =>
      let body := RustDurability.burnRecordBody party epoch
      if bodies.contains body then
        (st, .err)
      else
        let recBytes := RustDurability.burnRecord posixBurnMacKey posixBurnKeyId
          posixBurnGenesis lastTag party epoch
        let newTag := RustDurability.burnRecordTag posixBurnMacKey posixBurnKeyId
          posixBurnGenesis lastTag body
        let bodies' := bodies ++ [body]
        let retained' := st.retained.map (fun _ => ⟨bodies'.length, newTag⟩)
        ({ st with
           diskBytes := st.diskBytes ++ recBytes
           openState := some (bodies', newTag)
           retained := retained' }, .ok)
  | .retain =>
    match st.openState with
    | none => (st, .err)
    | some (bodies, lastTag) =>
      ({ st with retained := some ⟨bodies.length, lastTag⟩ }, .ok)
  | .reopen =>
    let opened := reopenPosixBurnDisk st.diskBytes st.inode st.retained
    match opened with
    | some (bodies, _) => ({ st with openState := opened }, .okCount bodies.length)
    | none => ({ st with openState := none }, .err)
  | .tear k =>
    let len := if k == 0 then 1 else if k ≥ 42 then 41 else k
    let disk' := st.diskBytes ++ List.replicate len (0xaa : UInt8)
    let opened := reopenPosixBurnDisk disk' st.inode st.retained
    match opened with
    | some (bodies, _) => ({ st with diskBytes := disk', openState := opened }, .okCount bodies.length)
    | none => ({ st with diskBytes := disk', openState := none }, .err)
  | .trunc =>
    let disk' := st.diskBytes.take 104
    let opened := reopenPosixBurnDisk disk' st.inode st.retained
    match opened with
    | some (bodies, _) => ({ st with diskBytes := disk', openState := opened }, .okCount bodies.length)
    | none => ({ st with diskBytes := disk', openState := none }, .err)
  | .flip =>
    let disk' := if st.diskBytes.isEmpty then []
      else st.diskBytes.take (st.diskBytes.length - 1) ++ [st.diskBytes.getLastD 0 ^^^ 1]
    let opened := reopenPosixBurnDisk disk' st.inode st.retained
    match opened with
    | some (bodies, _) => ({ st with diskBytes := disk', openState := opened }, .okCount bodies.length)
    | none => ({ st with diskBytes := disk', openState := none }, .err)
  | .copy =>
    let inode' := st.inode + 1
    let opened := reopenPosixBurnDisk st.diskBytes inode' st.retained
    match opened with
    | some (bodies, _) => ({ st with inode := inode', openState := opened }, .okCount bodies.length)
    | none => ({ st with inode := inode', openState := none }, .err)

def posixBurnTraceOutcomes (evs : List PosixBurnEvent) : List PosixBurnOutcome :=
  (evs.foldl (fun (acc : PosixBurnState × List PosixBurnOutcome) ev =>
    let (st', out) := posixBurnStep acc.1 ev
    (st', acc.2 ++ [out])) (PosixBurnState.init, [])).2

def posixBurnTrace (evs : List PosixBurnEvent) : List String :=
  (posixBurnTraceOutcomes evs).map PosixBurnOutcome.render

def PosixBurnTornDisk (st : PosixBurnState) (n k : Nat) : Prop :=
  st.diskBytes.length = 104 + 42 * n ∧ 0 < k ∧ k < 42

/-- Any partial record append (`0 < k < 42`) fails closed on reopen (`openState = none`, `.err`),
    directly discharging `RustDurability.partial_append_refuses`. -/
theorem posixBurnStep_tear_fails_closed (st : PosixBurnState) (n k : Nat)
    (hTorn : PosixBurnTornDisk st n k) :
    (posixBurnStep st (.tear k)).2 = .err ∧ (posixBurnStep st (.tear k)).1.openState = none := by
  rcases hTorn with ⟨hLen, hk0, hk42⟩
  have hkZero : (k == 0) = false := by cases k with | zero => omega | succ _ => rfl
  have hkGe : ¬ (k ≥ 42) := by omega
  have hClamp : (if k == 0 then 1 else if k ≥ 42 then 41 else k) = k := by
    rw [hkZero]; simp [hkGe]
  have hRefuse : RustDurability.openBurnBytes posixBurnMacKey
      (RustDurability.burnIdentity 1 st.inode) posixBurnKeyId
      (st.diskBytes ++ List.replicate k (0xaa : UInt8)) = none :=
    RustDurability.partial_append_refuses posixBurnMacKey
      (RustDurability.burnIdentity 1 st.inode) posixBurnKeyId
      st.diskBytes (List.replicate k (0xaa : UInt8)) n hLen
      (by simp [List.length_replicate, hk0, hk42])
  unfold posixBurnStep reopenPosixBurnDisk
  dsimp only
  rw [hClamp, hRefuse]
  exact ⟨rfl, rfl⟩

theorem witness_posixBurnTornDisk :
    ∃ (st : PosixBurnState) (n k : Nat), PosixBurnTornDisk st n k := by
  refine ⟨PosixBurnState.init, 0, 7, ?_⟩
  unfold PosixBurnTornDisk PosixBurnState.init
  refine ⟨?_, by decide, by decide⟩
  have hH : (RustDurability.burnHeader posixBurnMacKey (RustDurability.burnIdentity 1 100)
      posixBurnKeyId posixBurnGenesis).length = 104 :=
    RustDurability.burnHeader_length (by decide) (by decide)
  omega

/-- `#tooth`: Same-inode tail truncation to the 104-byte genesis header when `st.retained = some anchor`
    has `0 < anchor.attestedEpoch` cannot recover as `.okCount 0`. -/
theorem tooth_posixBurn_retained_rejects_truncation
    (st : PosixBurnState) (anchor : ExternalMonotoneAnchor)
    (hRet : st.retained = some anchor) (hAdv : 0 < anchor.attestedEpoch) :
    (posixBurnStep st .trunc).2 ≠ .okCount 0 := by
  unfold posixBurnStep reopenPosixBurnDisk
  dsimp only
  rw [hRet]
  cases hOpen : RustDurability.openBurnBytes posixBurnMacKey
      (RustDurability.burnIdentity 1 st.inode) posixBurnKeyId (st.diskBytes.take 104) with
  | none => intro h; cases h
  | some p =>
    rcases p with ⟨bodies, lastTag⟩
    dsimp only
    cases hV : verifyAgainstExternalAnchor anchor bodies.length lastTag
    · intro h; cases h
    · intro hEq
      injection hEq with hLenEq
      have hRej : verifyAgainstExternalAnchor anchor bodies.length lastTag = false := by
        rw [hLenEq]
        exact externalAnchor_rejects_whole_disk_rollback lastTag hAdv
      rw [hV] at hRej
      cases hRej

/-- Events exercised against POSIX `BeltLatch<FsBeltWal>` (`crates/qsag-core/src/belt_latch.rs`). -/
inductive FsBeltWalEvent where
  | bind (record : BeltLatchRecord)
  | retain
  | crash
  | rollback
  | corrupt
  | rmlock
  deriving DecidableEq, Repr

inductive FsBeltWalOutcome where
  | bindResult (accepted : Bool)
  | ok
  | closed
  | recovered (nextEpoch generation : Nat)
  | err
  deriving DecidableEq, Repr

def FsBeltWalOutcome.render : FsBeltWalOutcome → String
  | .bindResult true => "true"
  | .bindResult false => "false"
  | .ok => "ok"
  | .closed => "closed"
  | .recovered ep gen => "ok:" ++ toString ep ++ ":" ++ toString gen
  | .err => "err"

structure FsBeltWalState where
  node : BeltLatchNodeState
  generation : Nat
  retainedGen : Option Nat
  snapshot : Option (BeltLatchNodeState × Nat)
  diskCorrupted : Bool
  lockPresent : Bool
  live : Bool
  deriving DecidableEq, Repr

def FsBeltWalState.init : FsBeltWalState :=
  let n0 := BeltLatchNodeState.init 12 64
  { node := n0
    generation := 1
    retainedGen := none
    snapshot := some (n0, 1)
    diskCorrupted := false
    lockPresent := true
    live := true }

private def reopenFsBeltWal (st : FsBeltWalState) : FsBeltWalState × FsBeltWalOutcome :=
  if st.diskCorrupted || !st.lockPresent then
    ({ st with live := false }, .err)
  else
    let okAnchor := match st.retainedGen with
      | none => true
      | some minGen => decide (minGen ≤ st.generation)
    if !okAnchor then
      ({ st with live := false }, .err)
    else
      let recovered := beltLatchCrashAndRecover st.node
      ({ st with node := recovered, live := true },
       .recovered recovered.nextEpoch st.generation)

def fsBeltWalStep (st : FsBeltWalState) (ev : FsBeltWalEvent) : FsBeltWalState × FsBeltWalOutcome :=
  match ev with
  | .bind rec =>
    if !st.live then (st, .closed)
    else
      match beltLatchBindStep st.node rec with
      | .accepted next outcome =>
        let gen' := match outcome with
          | .replay => st.generation
          | .fresh => st.generation + 1
        let ret' := st.retainedGen.map (fun r => max r gen')
        ({ st with node := next, generation := gen', retainedGen := ret' }, .bindResult true)
      | .rejected next _ =>
        ({ st with node := next }, .bindResult false)
  | .retain =>
    if !st.live then (st, .closed)
    else
      ({ st with retainedGen := some st.generation, snapshot := some (st.node, st.generation) }, .ok)
  | .crash => reopenFsBeltWal st
  | .rollback =>
    match st.snapshot with
    | none => reopenFsBeltWal st
    | some (snapNode, snapGen) =>
      reopenFsBeltWal { st with node := snapNode, generation := snapGen, diskCorrupted := false }
  | .corrupt =>
    reopenFsBeltWal { st with diskCorrupted := true }
  | .rmlock =>
    reopenFsBeltWal { st with lockPresent := false }

def fsBeltWalTraceOutcomes (evs : List FsBeltWalEvent) : List FsBeltWalOutcome :=
  (evs.foldl (fun (acc : FsBeltWalState × List FsBeltWalOutcome) ev =>
    let (st', out) := fsBeltWalStep acc.1 ev
    (st', acc.2 ++ [out])) (FsBeltWalState.init, [])).2

def fsBeltWalTrace (evs : List FsBeltWalEvent) : List String :=
  (fsBeltWalTraceOutcomes evs).map FsBeltWalOutcome.render

def FsBeltWalRollbackArmed (st : FsBeltWalState) : Prop :=
  ∃ snapNode snapGen minGen,
    st.snapshot = some (snapNode, snapGen) ∧
    st.retainedGen = some minGen ∧
    snapGen < minGen ∧
    st.lockPresent = true

/-- Restoring an older authenticated `FsBeltWal` disk image below `retainedGen` is refused
    closed (`live = false`, `.err`). -/
theorem fsBeltWal_rollback_refused (st : FsBeltWalState)
    (hArmed : FsBeltWalRollbackArmed st) :
    (fsBeltWalStep st .rollback).2 = .err ∧ (fsBeltWalStep st .rollback).1.live = false := by
  rcases hArmed with ⟨snapNode, snapGen, minGen, hSnap, hRet, hLt, hLock⟩
  have hNotLe : decide (minGen ≤ snapGen) = false := by
    simp [Nat.not_le.mpr hLt]
  unfold fsBeltWalStep reopenFsBeltWal
  simp [hSnap, hRet, hLock, hNotLe]

theorem witness_fsBeltWalRollbackArmed :
    ∃ st : FsBeltWalState, FsBeltWalRollbackArmed st := by
  let n0 := BeltLatchNodeState.init 12 64
  refine ⟨{ node := n0
            generation := 2
            retainedGen := some 2
            snapshot := some (n0, 1)
            diskCorrupted := false
            lockPresent := true
            live := true }, n0, 1, 2, rfl, rfl, by decide, rfl⟩

/-- `#tooth`: Corrupting the MAC tag or removing the `.lock` sidecar refuses recovery (`live = false`). -/
theorem tooth_fsBeltWal_corrupt_and_rmlock_refused
    (st : FsBeltWalState) (ev : FsBeltWalEvent)
    (hEv : ev = .corrupt ∨ ev = .rmlock) :
    (fsBeltWalStep st ev).1.live = false := by
  rcases hEv with rfl | rfl <;> simp [fsBeltWalStep, reopenFsBeltWal]

end Qsag.SpecOracle

#tooth_pair Qsag.SpecOracle.accepted_digest_has_target_sum vs Qsag.SpecOracle.tooth_zero_digest_invalid
#verify_inhabited Qsag.SpecOracle.accepted_digest_has_target_sum Qsag.SpecOracle.witness_valid_digest

#tooth_pair Qsag.SpecOracle.quorumConfig_withQuorum_sound vs Qsag.SpecOracle.tooth_quorumConfig_rejects_split_quorum
#verify_inhabited Qsag.SpecOracle.quorumConfig_withQuorum_sound Qsag.SpecOracle.witness_quorumConfig_valid

#tooth_pair Qsag.SpecOracle.sha3_256Matches_width_and_keccak_sep vs Qsag.SpecOracle.tooth_sha3_256_rejects_keccak256_pad
#verify_inhabited Qsag.SpecOracle.sha3_256Matches_width_and_keccak_sep Qsag.SpecOracle.witness_sha3_256Matches_empty

#tooth_pair Qsag.SpecOracle.LegacyPoseidon16.poseidon2Perm16_pair_invertible vs Qsag.SpecOracle.LegacyPoseidon16.tooth_poseidon2Perm16_zero_not_fixed
#verify_inhabited Qsag.SpecOracle.LegacyPoseidon16.poseidon2Perm16_pair_invertible Qsag.SpecOracle.LegacyPoseidon16.witness_poseidon2Perm16_pair


#tooth_pair Qsag.SpecOracle.posixBurnStep_tear_fails_closed vs Qsag.SpecOracle.tooth_posixBurn_retained_rejects_truncation
#verify_inhabited Qsag.SpecOracle.posixBurnStep_tear_fails_closed Qsag.SpecOracle.witness_posixBurnTornDisk

#tooth_pair Qsag.SpecOracle.fsBeltWal_rollback_refused vs Qsag.SpecOracle.tooth_fsBeltWal_corrupt_and_rmlock_refused
#verify_inhabited Qsag.SpecOracle.fsBeltWal_rollback_refused Qsag.SpecOracle.witness_fsBeltWalRollbackArmed

public section
namespace Qsag.SpecOracle
end Qsag.SpecOracle
end
