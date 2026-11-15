module

public import Qsag.Exec.PosixCrashWal
public import Qsag.Protocol.Signing.HashSigs
import all Qsag.Protocol.Signing.HashSigs
public import Qsag.Custody.JortsBeltLatchAndQuorumSwitching
public import Qsag.Protocol.Aggregation.Poseidon2AlgebraicAndRecursiveHem
import all Qsag.Oracle.Poseidon2
import all Qsag.Protocol.Aggregation.Poseidon2AlgebraicAndRecursiveHem
import Qsag.Tactic.AssuranceKit

public section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace Qsag.SpecOracle

open Qsag Aggregation

/-! ## 0. Core Oracle Predicates & Two-Slot Ledger Recovery -/

/-- Executable configuration predicate for the production global-liveness profile. -/
def quorumAccepts (t n f q : Nat) : Bool :=
  decide (0 < t ∧ t ≤ n ∧ n ≤ 255 ∧ 0 < q ∧ q ≤ n ∧ f < t ∧ t ≤ q ∧
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

theorem generic_zero_digest_rejected :
    wotsGenericAccepts (List.replicate 32 0) = false := by decide

/-- Production-profile digit guard used by differential WOTS vectors. -/
def wots128Accepts (digest : List UInt8) : Bool :=
  checkTargetSum 4 128 192 (extractBaseWDigits 4 128 digest)

/-- Removing the constant-sum guard accepts the all-zero digest. -/
theorem tooth_zero_digest_rejected :
    wots128Accepts (List.replicate 32 0) = false := by decide

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
  if 0 < t ∧ t ≤ 255 then QuorumConfig.new t (3 * t - 2) (t - 1) else none

def ValidQuorumConfig (cfg : QuorumConfig) : Prop :=
  QuorumConfig.withQuorum cfg.t cfg.n cfg.f cfg.q = some cfg

/-- Every accepted `QuorumConfig` enforces privacy (`f < t`), reconstruction (`t ≤ q`),
    honest availability (`q ≤ n - f`, `3f + 1 ≤ n`), and constructive BFT quorum intersection
    (`extractBeltHonestQuorumWitness`). -/
theorem quorumConfig_withQuorum_sound (cfg : QuorumConfig)
    (hValid : ValidQuorumConfig cfg) :
    0 < cfg.t ∧ cfg.t ≤ cfg.n ∧ cfg.n ≤ 255 ∧
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
    rcases ha with ⟨ht0, htn, hn255, _, _, hft, htq, h3f, h2q, hqnf⟩
    refine ⟨ht0, htn, hn255, hft, htq, h3f, h2q, hqnf, ?_⟩
    intro Q1 Q2 Corrupt hQ1 hQ2 hC
    exact (extractBeltHonestQuorumWitness Q1 Q2 Corrupt h2q hQ1 hQ2 hC).property
  · cases hValid

/-- `QuorumConfig.tight t` constructs `⟨t, 3t - 2, t - 1, 2t - 1⟩` whenever `1 ≤ t` and `3t - 2 ≤ 255`. -/
theorem quorumConfig_tight_sound (t : Nat) (hPos : 0 < t) (hCap : 3 * t - 2 ≤ 255) :
    QuorumConfig.tight t = some ⟨t, 3 * t - 2, t - 1, 2 * t - 1⟩ := by
  have hLt86 : t < 86 :=
    if h : t < 86 then h
    else False.elim <| by
      have h86 : 86 ≤ t := Nat.le_of_not_lt h
      have h258 : 258 ≤ 3 * t := Nat.mul_le_mul_left 3 h86
      have h256 : 256 ≤ 3 * t - 2 := Nat.sub_le_sub_right h258 2
      exact Nat.not_le_of_gt (Nat.lt_of_lt_of_le (by decide : 255 < 256) h256) hCap
  have hFin : ∀ x : Fin 86, 0 < x.val → 3 * x.val - 2 ≤ 255 →
      QuorumConfig.tight x.val = some ⟨x.val, 3 * x.val - 2, x.val - 1, 2 * x.val - 1⟩ := by
    decide
  exact hFin ⟨t, hLt86⟩ hPos hCap

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
       0x82, 0xd8, 0x0a, 0x4b, 0x80, 0xf8, 0x43, 0x4a] := by
  decide +kernel

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
  decide +kernel

def Sha3_256Matches (msg digest : List UInt8) : Prop :=
  sha3_256Bytes msg = digest

theorem sha3_256Matches_width_and_keccak_sep (msg digest : List UInt8)
    (h : Sha3_256Matches msg digest) :
    digest.length = 32 ∧ (msg = [] → digest ≠ keccak256Bytes []) := by
  unfold Sha3_256Matches at h
  subst h
  refine ⟨sha3_256Bytes_length msg, fun hm => ?_⟩
  subst hm
  decide +kernel

theorem witness_sha3_256Matches_empty :
    ∃ (msg digest : List UInt8), Sha3_256Matches msg digest :=
  ⟨[], sha3_256Bytes [], rfl⟩

/-- `#tooth`: Substituting Keccak-256 (`0x01` pad) for SHA3-256 (`0x06` pad) yields a distinct digest. -/
theorem tooth_sha3_256_rejects_keccak256_pad :
    ¬ Sha3_256Matches [] (keccak256Bytes []) := by
  unfold Sha3_256Matches
  decide +kernel

/-! ## 3. Width-16 Goldilocks `Poseidon2` Permutation ($R_F = 8, R_P = 22$) -/

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
  unfold sboxState16Inv sboxState16 sboxLane4Inv sboxLane4
  apply Poseidon2State16.ext <;> apply Lane4.ext <;> exact sbox7Inv_sbox7 _

private theorem sboxState16_sboxState16Inv (st : Poseidon2State16) :
    sboxState16 (sboxState16Inv st) = st := by
  unfold sboxState16 sboxState16Inv sboxLane4 sboxLane4Inv
  apply Poseidon2State16.ext <;> apply Lane4.ext <;> exact sbox7_sbox7Inv _

private theorem state16Sub_add_right (a c : Poseidon2State16) :
    state16Sub (state16Add a c) c = a := by
  have h4 : ∀ x y : Lane4, lane4Sub (lane4Add x y) y = x := fun x y => by
    unfold lane4Sub lane4Add
    apply Lane4.ext <;> exact ring_add_sub_cancel_right _ _
  unfold state16Sub state16Add
  exact Poseidon2State16.ext (h4 _ _) (h4 _ _) (h4 _ _) (h4 _ _)

private theorem state16Add_sub_right (a c : Poseidon2State16) :
    state16Add (state16Sub a c) c = a := by
  have h4 : ∀ x y : Lane4, lane4Add (lane4Sub x y) y = x := fun x y => by
    unfold lane4Add lane4Sub
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
  unfold weightedSumMI16 applyMI16 state16Sum lane4Sum
  dsimp only
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
  unfold state16Sum makeMI16InvRaw lane4Sum weightedSumMI16
  dsimp only
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

