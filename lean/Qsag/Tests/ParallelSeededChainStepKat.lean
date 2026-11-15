module
/-
# Qsag.Tests.ParallelSeededChainStepKat — executed-Rust known answer for `parallel_chain_step`

`ParallelSeededSpnPolyBasis.rustParallelChainStep` is a transcription. This module evaluates
it in the Lean kernel with `spnCshake256Framed32` as the hash and compares against the bytes
printed by the compiled Rust function `qsag_fts::parallel_mpc::parallel_chain_step` (private
harness; source hashes and command in `/tmp/qsag-subfable-field-correspondence.md`).

The vector exercises one tweak derivation, 48 round-constant derivations, 384 `gf2_128_mul`
loops for the S-boxes, 96 for the mixing layer, the feed-forward and both lane framings.
Agreement is evidence for the transcription (modulus, bit order, byte order, frame layout,
constants); it is not a refinement proof of the Rust code.

`spnCshake256Framed32` repeats the body of `ThresholdMlDsaAndToprf.cshake256FramedBytes`
(`cshake256Bytes customization (u64_le(#frames) ‖ (u64_le(len) ‖ frame)*)`) so that this
check does not import that module; an `rfl` identification of the two is left to integration.

The evaluation is staged (tweak, lanes, six blocks of eight rounds, output) so that each
kernel check stays small; the intermediate states are checked, not trusted.
-/

public import Qsag.Oracle.ParallelSeededSpnPolyBasis
import all Qsag.Oracle.ParallelSeededSpnPolyBasis
import all Qsag.Math.Tower128PolyBasisIso
import all Qsag.Oracle.ParallelSeededSpnSecurity
import all Qsag.Protocol.Migration.ActiveMigrationZeroTest
import all Qsag.Exec.SimulationSpine
import all Qsag.Oracle.Keccak

public section
namespace Qsag
open MigrationExecution

set_option autoImplicit false

/-- Frame body of `cshake256_framed_xof` (`keccak.rs:281-284`). -/
def spnFramesU64LeBody : List (List UInt8) → List UInt8
  | [] => []
  | f :: fs => (encodeNatLeBytes 8 f.length ++ f) ++ spnFramesU64LeBody fs

/-- `cshake256_framed_32` (`keccak.rs:277-295`) over the `Qsag.Keccak` cSHAKE256 model. -/
def spnCshake256Framed32 (customization : List UInt8) (frames : List (List UInt8)) :
    List UInt8 :=
  cshake256Bytes customization (encodeNatLeBytes 8 frames.length ++ spnFramesU64LeBody frames)

/-- Rounds `m, …, m+n-1` of the Rust loop. -/
def rustSpnIterFrom (rcs : Nat → BitVec 128 × BitVec 128) (m : Nat) :
    Nat → BitVec 128 × BitVec 128 → BitVec 128 × BitVec 128
  | 0, st => st
  | n + 1, st => rustSpnRound (rcs (m + n)) (rustSpnIterFrom rcs m n st)

theorem rustSpnIter_add (rcs : Nat → BitVec 128 × BitVec 128) (m : Nat) :
    ∀ (n : Nat) (st : BitVec 128 × BitVec 128),
      rustSpnIter rcs (m + n) st = rustSpnIterFrom rcs m n (rustSpnIter rcs m st)
  | 0, _ => rfl
  | n + 1, st => by
    show rustSpnRound (rcs (m + n)) (rustSpnIter rcs (m + n) st) =
      rustSpnRound (rcs (m + n)) (rustSpnIterFrom rcs m n (rustSpnIter rcs m st))
    rw [rustSpnIter_add rcs m n st]

/-- `pk_seed = 00 01 … 1f`. -/
def chainStepKatPkSeed : List UInt8 :=
  [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b,
   0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17,
   0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f]

/-- `cur = a0 a1 … bf`. -/
def chainStepKatCur : List UInt8 :=
  [0xa0, 0xa1, 0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7, 0xa8, 0xa9, 0xaa, 0xab,
   0xac, 0xad, 0xae, 0xaf, 0xb0, 0xb1, 0xb2, 0xb3, 0xb4, 0xb5, 0xb6, 0xb7,
   0xb8, 0xb9, 0xba, 0xbb, 0xbc, 0xbd, 0xbe, 0xbf]

/-- Output printed by the Rust harness for `(pk_seed, epoch 7, chain_idx 3, step 2, cur)`. -/
def chainStepKatRustOutput : List UInt8 :=
  [0x24, 0xc1, 0x9a, 0x2d, 0x42, 0x51, 0xdf, 0x83, 0x40, 0xd1, 0x7d, 0xf8,
   0xde, 0xc6, 0x6b, 0x9c, 0xd4, 0x60, 0x46, 0xb7, 0xb2, 0x34, 0x72, 0xb1,
   0x4b, 0xb6, 0x8f, 0x62, 0x11, 0x22, 0x91, 0x4b]

def chainStepKatTweak : BitVec 128 × BitVec 128 :=
  (0x4668a6864f7bee9787e94643de34423c#128, 0x2f7744435eb81c943103f437706a0e10#128)

/-- State after `8k` rounds, `k ≤ 6`. -/
def chainStepKatState : Nat → BitVec 128 × BitVec 128
  | 0 => (0xafaeadacabaaa9a8a7a6a5a4a3a2a1a0#128, 0xbfbebdbcbbbab9b8b7b6b5b4b3b2b1b0#128)
  | 1 => (0x2bd5eef093126656772fb98cf70d43c1#128, 0x58b1a4a862530ca569b93c0c9f839923#128)
  | 2 => (0x6cdc2dacdcb33e5347e44c9e8d276445#128, 0xba352c8a0c0bd7639d484ab60c75f57d#128)
  | 3 => (0x7b5d995999b5e650e78f4b0ca3b6fd89#128, 0xbe4268d7c4890e6f38438a0aa7b69114#128)
  | 4 => (0x6f7b16116ee2bf063beea2ad89749e8e#128, 0xedfb215302775491fab2c19cca81af56#128)
  | 5 => (0xef989eea2f03174c916b4ff381b3b153#128, 0xabd713ce96b31b4227d0d661999e014f#128)
  | 6 => (0x33c56b7253d778e82479f4e68e386084#128, 0xf42f9fadd9350ff306c4810604f4d164#128)
  | _ => (0#128, 0#128)

set_option maxRecDepth 8192 in
theorem chainStepKat_tweak :
    rustDeriveChainTweak spnCshake256Framed32 chainStepKatPkSeed 7 3 2 = chainStepKatTweak := by
  decide +kernel

theorem chainStepKat_lanes : rustBytes32ToLanes chainStepKatCur = chainStepKatState 0 := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem chainStepKat_rounds_0_8 :
    rustSpnIterFrom (rustSpnRoundConstants spnCshake256Framed32 chainStepKatTweak) 0 8
      (chainStepKatState 0) = chainStepKatState 1 := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem chainStepKat_rounds_8_16 :
    rustSpnIterFrom (rustSpnRoundConstants spnCshake256Framed32 chainStepKatTweak) 8 8
      (chainStepKatState 1) = chainStepKatState 2 := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem chainStepKat_rounds_16_24 :
    rustSpnIterFrom (rustSpnRoundConstants spnCshake256Framed32 chainStepKatTweak) 16 8
      (chainStepKatState 2) = chainStepKatState 3 := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem chainStepKat_rounds_24_32 :
    rustSpnIterFrom (rustSpnRoundConstants spnCshake256Framed32 chainStepKatTweak) 24 8
      (chainStepKatState 3) = chainStepKatState 4 := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem chainStepKat_rounds_32_40 :
    rustSpnIterFrom (rustSpnRoundConstants spnCshake256Framed32 chainStepKatTweak) 32 8
      (chainStepKatState 4) = chainStepKatState 5 := by
  decide +kernel

set_option maxRecDepth 8192 in
theorem chainStepKat_rounds_40_48 :
    rustSpnIterFrom (rustSpnRoundConstants spnCshake256Framed32 chainStepKatTweak) 40 8
      (chainStepKatState 5) = chainStepKatState 6 := by
  decide +kernel

theorem chainStepKat_rounds_0_48 :
    rustSpnIter (rustSpnRoundConstants spnCshake256Framed32 chainStepKatTweak) spnRounds
      (chainStepKatState 0) = chainStepKatState 6 := by
  let rcs := rustSpnRoundConstants spnCshake256Framed32 chainStepKatTweak
  have step : ∀ (m k : Nat), rustSpnIter rcs m (chainStepKatState 0) = chainStepKatState k →
      rustSpnIterFrom rcs m 8 (chainStepKatState k) = chainStepKatState (k + 1) →
      rustSpnIter rcs (m + 8) (chainStepKatState 0) = chainStepKatState (k + 1) :=
    fun m k hPrev hChunk =>
      (rustSpnIter_add rcs m 8 _).trans ((congrArg (rustSpnIterFrom rcs m 8) hPrev).trans hChunk)
  have h8 := step 0 0 rfl chainStepKat_rounds_0_8
  have h16 := step 8 1 h8 chainStepKat_rounds_8_16
  have h24 := step 16 2 h16 chainStepKat_rounds_16_24
  have h32 := step 24 3 h24 chainStepKat_rounds_24_32
  have h40 := step 32 4 h32 chainStepKat_rounds_32_40
  exact step 40 5 h40 chainStepKat_rounds_40_48

/-- **Executed-Rust agreement.** The Lean transcription of `parallel_chain_step`, evaluated by
    the kernel over the Lean cSHAKE256 model, returns the 32 bytes the compiled Rust function
    printed for the same arguments. -/
theorem rust_parallel_chain_step_executed_kat :
    rustParallelChainStep spnCshake256Framed32 chainStepKatPkSeed 7 3 2 chainStepKatCur =
      chainStepKatRustOutput := by
  have hStep : rustAlgebraicStep
      (rustSpnRoundConstants spnCshake256Framed32 chainStepKatTweak) (chainStepKatState 0) =
      ((chainStepKatState 6).1 ^^^ (chainStepKatState 0).1,
       (chainStepKatState 6).2 ^^^ (chainStepKatState 0).2) := by
    show ((rustSpnIter (rustSpnRoundConstants spnCshake256Framed32 chainStepKatTweak) spnRounds
          (chainStepKatState 0)).1 ^^^ (chainStepKatState 0).1,
        (rustSpnIter (rustSpnRoundConstants spnCshake256Framed32 chainStepKatTweak) spnRounds
          (chainStepKatState 0)).2 ^^^ (chainStepKatState 0).2) = _
    rw [chainStepKat_rounds_0_48]
  unfold rustParallelChainStep
  rw [chainStepKat_tweak, chainStepKat_lanes, hStep]
  decide +kernel

end Qsag
end

#verify_constructive
  Qsag.rust_parallel_chain_step_executed_kat
