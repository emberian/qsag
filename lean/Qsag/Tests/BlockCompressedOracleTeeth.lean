module
/-
# Qsag.Tests.BlockCompressedOracleTeeth — audits for the block compressed oracle and prefix extraction

The assurance commands read proof bodies, and this module does not `import all`. Each audited
theorem of `Qsag.Oracle.BlockCompressedOracle` and `Qsag.Oracle.PrefixMerkleExtraction` is
therefore restated here with its statement unchanged and a one-line proof by the library
theorem; the audit of the restatement walks into the library proof through Lean's axiom
summaries.

The `Qrom`-facing corollaries are audited in their premise-free form (`BlockCompressedOracle`
§9, where the law structures `QromRuntimeLaws` / `QromBitTableLaws` are proved from the
equation lemmas of `Qsag.Oracle.Qrom`).
-/
public import Qsag.Tactic.Prelude
public import Qsag.Oracle.BlockCompressedOracle
public import Qsag.Oracle.PrefixMerkleExtraction
public section
namespace Qsag.BlockCompressedOracleTeeth
open Qsag.BlockCompressedOracle Qsag.PrefixMerkleExtraction
set_option autoImplicit false
set_option exponentiation.threshold 2048

/-! ## 1. Fourier database support for `w`-bit answers -/

theorem support_any_width {n w cardAnc Q : Nat} (A : BlockAdv n w cardAnc Q)
    (t : Nat) (ht : t ≤ Q) (d : BlockTable w n) (hd : t < blockWeight w n d) :
    fourierBlockState (fun h => blockAdvStateAt A (blockOracle w n h) t ht) d =
      qzero n w cardAnc :=
  block_fourier_coherent_support A t ht d hd

theorem support_256 {n cardAnc Q : Nat} (A : BlockAdv n 256 cardAnc Q)
    (t : Nat) (ht : t ≤ Q) (d : BlockTable 256 n) (hd : t < blockWeight 256 n d) :
    fourierBlockState (fun h => blockAdvStateAt A (blockOracle 256 n h) t ht) d =
      qzero n 256 cardAnc :=
  block256_fourier_coherent_support A t ht d hd

theorem runtime_support_256 {n cardAnc Q : Nat} (A : BlockAdv n 256 cardAnc Q)
    (t : Nat) (ht : t ≤ Q) (d : BlockTable 256 n) (hd : t < blockWeight 256 n d) :
    fourierBlockAdvStateAt A t ht d = qzero n 256 cardAnc :=
  block256_fourier_runtime_support A t ht d hd

theorem overflow_mass_zero_256 {n cardAnc Q : Nat} (A : BlockAdv n 256 cardAnc Q) :
    blockTableSum 256 n (fun d => if Q < blockWeight 256 n d then
      qnormSq (fourierBlockAdvStateAt A Q (Nat.le_refl Q) d) else 0) = 0 :=
  block256_fourier_database_overflow_mass_zero A

theorem qrom_support_any_width {n w cardAnc Q : Nat}
    (A : QuantumAdv n w cardAnc Q) (t : Nat) (ht : t ≤ Q) (d : BlockTable w n)
    (hd : t < blockWeight w n d) :
    fourierBlockState (fun h => advStateAt A (blockOracle w n h) t ht) d =
      QVec.zero n w cardAnc :=
  quantumAdv_block_fourier_coherent_support A t ht d hd

theorem qrom_one_bit_statement_recovered
    {n cardAnc Q : Nat} (A : QuantumAdv n 1 cardAnc Q) (t : Nat) (ht : t ≤ Q)
    (d : OracleBitTable n) (hd : t < tableWeight n d) :
    fourierOracleState (fun h => advStateAt A (tableBitOracle n h) t ht) d =
      QVec.zero n 1 cardAnc :=
  quantumAdv_fourier_coherent_support_from_block A t ht d hd

/-- A constant nonzero amplitude over two addresses, 256-bit responses and a trivial
    ancilla. It is a function; the `2 ^ 256` response values are never listed. -/
def onesState : QVec 2 256 1 := fun _ _ _ => ⟨1, 0⟩

/-- One query followed by the identity gate, against a 256-bit oracle on two addresses. -/
def oneQueryAdv : BlockAdv 2 256 1 1 := ⟨onesState, fun _ => BlockGate.id 2 256 1⟩

/-- The premises of `support_256` hold together: one query, a database with two nonzero
    256-bit blocks. -/
theorem witness_support_256 :
    ∃ (_A : BlockAdv 2 256 1 1) (d : BlockTable 256 2), (1 : Nat) ≤ 1 ∧ 1 < blockWeight 256 2 d :=
  ⟨oneQueryAdv, hotLabel₂ 255, Nat.le_refl 1,
    Nat.lt_of_lt_of_eq (Nat.lt_succ_self 1) (blockWeight_hotLabel₂ 255).symm⟩

theorem onesState_ne_zzero : ¬ (onesState ⟨0, Nat.zero_lt_two⟩ ⟨0, Nat.two_pow_pos 256⟩
    ⟨0, Nat.zero_lt_one⟩ = zzero) := by
  intro h
  have hre := congrArg GaussInt.re h
  rw [zzero_eq] at hre
  have h1 : (1 : Int) = 0 := hre
  exact absurd h1 (by decide)

/-- Tooth: the bound is on labels with MORE than `t` nonzero blocks. Before any query the
    empty 256-bit database carries the initial state, so `t < blockWeight` cannot be relaxed
    to `t ≤ blockWeight`. -/
theorem tooth_empty_database_keeps_amplitude :
    ¬ (fourierBlockState (fun h => blockAdvStateAt oneQueryAdv (blockOracle 256 2 h) 0
        (Nat.zero_le 1)) (zeroLabel 256 2) = qzero 2 256 1) := by
  rw [fourier_block_initial_zeroLabel]
  exact qdblPow_ne_qzero (2 * 256) onesState ⟨0, Nat.zero_lt_two⟩ ⟨0, Nat.two_pow_pos 256⟩
    ⟨0, Nat.zero_lt_one⟩ onesState_ne_zzero

/-- Tooth for the Fourier runtime: same label, same conclusion. -/
theorem tooth_runtime_empty_database_keeps_amplitude :
    ¬ (fourierBlockAdvStateAt oneQueryAdv 0 (Nat.zero_le 1) (zeroLabel 256 2) =
        qzero 2 256 1) := by
  rw [fourierBlockAdvStateAt_initial_zeroLabel]
  exact qdblPow_ne_qzero (2 * 256) onesState ⟨0, Nat.zero_lt_two⟩ ⟨0, Nat.two_pow_pos 256⟩
    ⟨0, Nat.zero_lt_one⟩ onesState_ne_zzero

#verify_constructive Qsag.BlockCompressedOracleTeeth.support_any_width
#verify_constructive Qsag.BlockCompressedOracleTeeth.support_256
#verify_constructive Qsag.BlockCompressedOracleTeeth.runtime_support_256
#verify_constructive Qsag.BlockCompressedOracleTeeth.overflow_mass_zero_256
#verify_constructive Qsag.BlockCompressedOracleTeeth.qrom_support_any_width
#verify_constructive Qsag.BlockCompressedOracleTeeth.qrom_one_bit_statement_recovered
#verify_constructive Qsag.BlockCompressedOracleTeeth.tooth_empty_database_keeps_amplitude
#verify_constructive Qsag.BlockCompressedOracleTeeth.tooth_runtime_empty_database_keeps_amplitude

#verify_inhabited Qsag.BlockCompressedOracleTeeth.support_256
  Qsag.BlockCompressedOracleTeeth.witness_support_256
#verify_inhabited Qsag.BlockCompressedOracleTeeth.runtime_support_256
  Qsag.BlockCompressedOracleTeeth.witness_support_256

#tooth_pair Qsag.BlockCompressedOracleTeeth.support_256 vs
  Qsag.BlockCompressedOracleTeeth.tooth_empty_database_keeps_amplitude
#tooth_pair Qsag.BlockCompressedOracleTeeth.runtime_support_256 vs
  Qsag.BlockCompressedOracleTeeth.tooth_runtime_empty_database_keeps_amplitude
#tooth_pair Qsag.BlockCompressedOracleTeeth.overflow_mass_zero_256 vs
  Qsag.BlockCompressedOracleTeeth.tooth_runtime_empty_database_keeps_amplitude

/-! ## 2. Prefix extraction in the two-phase experiment -/

theorem prefix_bound {cardX w Q₁ Q₂ : Nat} {St Chal : Type}
    (A : TwoPhaseAdversary cardX w Q₁ Q₂ St Chal) (L : MerkleAddressLayout cardX w)
    (lvl d : Nat) (hLvl : lvl + d ≤ L.levels) (ch : Chal) :
    2 ^ w * uniformOracleSum w cardX
        (fun H => if prefixFailure A L lvl d H ch = true then 1 else 0) ≤
      ((d + Q₂ + Q₁) * (3 * Q₁ + 1)) * (2 ^ w) ^ cardX :=
  prefix_extraction_failure_bound A L lvl d hLvl ch

theorem prefix_cover {cardX w Q₁ Q₂ : Nat} {St Chal : Type}
    (A : TwoPhaseAdversary cardX w Q₁ Q₂ St Chal) (L : MerkleAddressLayout cardX w)
    (lvl d : Nat) (hLvl : lvl + d ≤ L.levels) (H : Fin cardX → BitVec w) (ch : Chal)
    (hFail : prefixFailure A L lvl d H ch = true) :
    ∃ s : Fin (d + Q₂ + Q₁), stepHit A L lvl d ch s.1 H = true :=
  prefixFailure_cover A L lvl d hLvl H ch hFail

theorem prefix_binding {cardX w Q₁ Q₂ : Nat} {St Chal : Type}
    (A : TwoPhaseAdversary cardX w Q₁ Q₂ St Chal) (L : MerkleAddressLayout cardX w)
    (lvl d : Nat) (H : Fin cardX → BitVec w) (ch ch' : Chal)
    (hAcc : accepts A L lvl d H ch = true) (hAcc' : accepts A L lvl d H ch' = true)
    (hOk : prefixFailure A L lvl d H ch = false) (hOk' : prefixFailure A L lvl d H ch' = false)
    (hIdx : (opening A H ch).idx = (opening A H ch').idx)
    (hLen : (opening A H ch).path.length = (opening A H ch').path.length) :
    (opening A H ch).leaf = (opening A H ch').leaf ∧
    (opening A H ch).path = (opening A H ch').path :=
  two_challenge_binding A L lvl d H ch ch' hAcc hAcc' hOk hOk' hIdx hLen

/-- A depth-one tree over one-bit digests: the four compression inputs `(u, v)` are the four
    oracle addresses. -/
def tinyLayout : MerkleAddressLayout 4 1 where
  encode _ _ u v := ⟨2 * u.toNat + v.toNat, by
    have hu := u.isLt
    have hv := v.isLt
    omega⟩
  decode x := some (0, 0, BitVec.ofNat 1 (x.val / 2), BitVec.ofNat 1 (x.val % 2))
  levels := 1
  nodes := 1
  decode_sound := by
    intro x l n u v h
    cases h
    revert x
    decide
  decode_encode := by
    intro l n u v hl hn
    have hl0 : l = 0 := by omega
    have hn0 : n = 0 := by omega
    subst hl0
    subst hn0
    have hu := u.isLt
    have hv := v.isLt
    have h1 : BitVec.ofNat 1 ((2 * u.toNat + v.toNat) / 2) = u := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      omega
    have h2 : BitVec.ofNat 1 ((2 * u.toNat + v.toNat) % 2) = v := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      omega
    show some (0, 0, BitVec.ofNat 1 ((2 * u.toNat + v.toNat) / 2),
      BitVec.ofNat 1 ((2 * u.toNat + v.toNat) % 2)) = some (0, 0, u, v)
    rw [h1, h2]

/-- Announces root `1` with no query, and asks for `H(0, 1)` only after the challenge. -/
def lateAdv : TwoPhaseAdversary 4 1 0 1 Unit Unit := lateOpenAdversary tinyLayout 1#1 0#1 1#1 Unit

/-- An oracle under which the late query happens to return the announced root. -/
def onesOracle : Fin 4 → BitVec 1 := fun _ => 1#1

/-- The premises of `prefix_bound` hold together, on an experiment in which the verifier
    does accept. -/
theorem witness_prefix_bound :
    ∃ (A : TwoPhaseAdversary 4 1 0 1 Unit Unit) (L : MerkleAddressLayout 4 1)
      (H : Fin 4 → BitVec 1), 0 + 1 ≤ L.levels ∧ accepts A L 0 1 H () = true :=
  ⟨lateAdv, tinyLayout, onesOracle, Nat.le_refl 1,
    (lateOpen_final_log_extracts_uncommitted tinyLayout Nat.zero_lt_one Nat.zero_lt_one
      onesOracle 1#1 0#1 1#1 rfl ()).1⟩

/-- **Negative witness.** A concrete run in which the verifier accepts and extraction from
    the FINAL log returns the opening `(0, [1])` of the announced root, although the only
    preimage query of that root was made after the challenge. Extraction from the Phase-1 log
    returns `none`, and the run is a `prefixFailure`: it is charged to the bound, not
    credited as a commitment. -/
theorem tooth_final_log_extraction_accepts_post_challenge_root :
    ∃ (A : TwoPhaseAdversary 4 1 0 1 Unit Unit) (H : Fin 4 → BitVec 1),
      accepts A tinyLayout 0 1 H () = true ∧
      finalLogExtract A tinyLayout 0 H () 0 1 = some (0#1, [1#1]) ∧
      prefixCommitted A tinyLayout 0 H 0 1 = none ∧
      prefixFailure A tinyLayout 0 1 H () = true :=
  ⟨lateAdv, onesOracle,
    lateOpen_final_log_extracts_uncommitted tinyLayout Nat.zero_lt_one Nat.zero_lt_one
      onesOracle 1#1 0#1 1#1 rfl ()⟩

/-- The two extractors disagree on that run. -/
theorem tooth_prefix_and_final_log_extraction_differ :
    ¬ (prefixCommitted lateAdv tinyLayout 0 onesOracle 0 1 =
        finalLogExtract lateAdv tinyLayout 0 onesOracle () 0 1) := by
  have h := lateOpen_final_log_extracts_uncommitted tinyLayout Nat.zero_lt_one Nat.zero_lt_one
    onesOracle 1#1 0#1 1#1 rfl ()
  intro hEq
  have hNone : prefixCommitted lateAdv tinyLayout 0 onesOracle 0 1 = none := h.2.2.1
  have hSome : finalLogExtract lateAdv tinyLayout 0 onesOracle () 0 1 = some (0#1, [1#1]) :=
    h.2.1
  rw [hNone, hSome] at hEq
  cases hEq

/-- The late run is covered by a counted step: the Phase-2 query is a fresh address whose
    answer hits the Phase-1 target (the announced root). -/
theorem late_run_is_charged :
    ∃ s : Fin (1 + 1 + 0), stepHit lateAdv tinyLayout 0 1 () s.1 onesOracle = true :=
  prefixFailure_cover lateAdv tinyLayout 0 1 (Nat.le_refl 1) onesOracle ()
    (lateOpen_final_log_extracts_uncommitted tinyLayout Nat.zero_lt_one Nat.zero_lt_one
      onesOracle 1#1 0#1 1#1 rfl ()).2.2.2

#verify_constructive Qsag.BlockCompressedOracleTeeth.prefix_bound
#verify_constructive Qsag.BlockCompressedOracleTeeth.prefix_cover
#verify_constructive Qsag.BlockCompressedOracleTeeth.prefix_binding
#verify_constructive Qsag.BlockCompressedOracleTeeth.tooth_final_log_extraction_accepts_post_challenge_root
#verify_constructive Qsag.BlockCompressedOracleTeeth.tooth_prefix_and_final_log_extraction_differ
#verify_constructive Qsag.BlockCompressedOracleTeeth.late_run_is_charged

#verify_inhabited Qsag.BlockCompressedOracleTeeth.prefix_bound
  Qsag.BlockCompressedOracleTeeth.witness_prefix_bound

#tooth_pair Qsag.BlockCompressedOracleTeeth.prefix_bound vs
  Qsag.BlockCompressedOracleTeeth.tooth_final_log_extraction_accepts_post_challenge_root
#tooth_pair Qsag.BlockCompressedOracleTeeth.prefix_binding vs
  Qsag.BlockCompressedOracleTeeth.tooth_prefix_and_final_log_extraction_differ

end Qsag.BlockCompressedOracleTeeth
