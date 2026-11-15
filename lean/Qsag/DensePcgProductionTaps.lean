module
/-
# Qsag.DensePcgProductionTaps — row 0 of a production tap matrix from the Keccak specification

`lpnTap` is `BatchedTapGenerator` of `pcg_dense.rs`: one SHAKE-256 block per counter over the
62-byte input `"QSAG.DPCG.LPNTAP" ‖ session ‖ sender ‖ receiver ‖ tree ‖ depth ‖ counter`, read as
68 little-endian 16-bit words per block and masked to the tree depth. `prodRow0Taps_eq_generator`
evaluates it with the kernel for the 64 trees of row 0 (session `00..1f`, sender 0, receiver 1,
depth 15) and obtains the tap list used by `prodRow0_bias_bracket`.
-/
public import Qsag.Keccak
import all Qsag.Keccak
public import Qsag.DensePcgTapLinearTests
import all Qsag.DensePcgTapLinearTests

public section
namespace Qsag
set_option autoImplicit false

/-- Absorbed state of one tap block: lanes 0..7 hold the input and the `0x1F` suffix at byte 62,
lane 16 holds the final `0x80` of the 136-byte rate. `session` is the four little-endian lanes
of the 32-byte session id. -/
def lpnTapBlockState (session : UInt64 × UInt64 × UInt64 × UInt64)
    (sender receiver tree depth ctr : Nat) : KState :=
  { zeroKState with
    a0 := 0x4350442E47415351
    a1 := 0x5041544E504C2E47
    a2 := session.1
    a3 := session.2.1
    a4 := session.2.2.1
    a5 := session.2.2.2
    a6 := UInt64.ofNat (sender % 65536 + (receiver % 65536) * 2 ^ 16 + (tree % 256) * 2 ^ 32 +
      (depth % 256) * 2 ^ 40 + (ctr % 65536) * 2 ^ 48)
    a7 := UInt64.ofNat ((ctr / 65536) % 2 ^ 48 + 0x1F * 2 ^ 48)
    a16 := 0x8000000000000000 }

def kstateLane (s : KState) : Nat → UInt64
  | 0 => s.a0 | 1 => s.a1 | 2 => s.a2 | 3 => s.a3 | 4 => s.a4 | 5 => s.a5 | 6 => s.a6
  | 7 => s.a7 | 8 => s.a8 | 9 => s.a9 | 10 => s.a10 | 11 => s.a11 | 12 => s.a12 | 13 => s.a13
  | 14 => s.a14 | 15 => s.a15 | _ => s.a16

/-- The `idx`-th masked tap of a tree's stream. -/
def lpnTap (session : UInt64 × UInt64 × UInt64 × UInt64)
    (sender receiver tree depth idx : Nat) : Nat :=
  let out := keccakF1600 (lpnTapBlockState session sender receiver tree depth (idx / 68))
  ((kstateLane out ((idx % 68) / 4)).toNat / 2 ^ (16 * (idx % 4))) % 65536 % 2 ^ depth

def lpnRowTaps (session : UInt64 × UInt64 × UInt64 × UInt64)
    (sender receiver tree depth row : Nat) : Nat × Nat × Nat :=
  (lpnTap session sender receiver tree depth (3 * row),
   lpnTap session sender receiver tree depth (3 * row + 1),
   lpnTap session sender receiver tree depth (3 * row + 2))

/-- Session id `00 01 .. 1f` as little-endian lanes. -/
def auditSession : UInt64 × UInt64 × UInt64 × UInt64 :=
  (0x0706050403020100, 0x0F0E0D0C0B0A0908, 0x1716151413121110, 0x1F1E1D1C1B1A1918)

def lpnMatrixRow (session : UInt64 × UInt64 × UInt64 × UInt64)
    (sender receiver depth row : Nat) : List (Nat × Nat × Nat) :=
  (List.range 64).map (fun tree => lpnRowTaps session sender receiver tree depth row)

/-- The tap list of `prodRow0_bias_bracket` is row 0 of the generator for the audit session. -/
theorem prodRow0Taps_eq_generator : lpnMatrixRow auditSession 0 1 15 0 = prodRow0Taps := by
  decide +kernel

/-- Row 0 of the generated matrix: the exact regular-noise signed count of its one-row test has
magnitude strictly between `2^-118` and `2^-117` of the `32768^64` noise tuples. -/
theorem generatedRow0_bias_bracket :
    (noiseSignedSum 32768 (rowTestFns (lpnMatrixRow auditSession 0 1 15 0)) false).natAbs * 2 ^ 117
        < 32768 ^ 64 ∧
    32768 ^ 64 <
      (noiseSignedSum 32768 (rowTestFns (lpnMatrixRow auditSession 0 1 15 0)) false).natAbs * 2 ^ 118 := by
  rw [prodRow0Taps_eq_generator, prodRow0_bias_bracket.2.1]
  exact prodRow0_bias_bracket.2.2

/-- Row 543 of the same matrix, the largest one-row bias among its first 1024 rows in the
external audit. -/
def prodRow543Taps : List (Nat × Nat × Nat) := [
  (17811, 19186, 1144), (8163, 8063, 7741), (14982, 9969, 29441), (11138, 17046, 28217),
  (27137, 10060, 2594), (14186, 4239, 7023), (26594, 32455, 26675), (29144, 11850, 22795),
  (13007, 32005, 7932), (9809, 5690, 6408), (7976, 9150, 20007), (8608, 23219, 10343),
  (11788, 5209, 1596), (9498, 25269, 31220), (24200, 23386, 17038), (25190, 25033, 3534),
  (31785, 12453, 31351), (25646, 15813, 16610), (16910, 23477, 16018), (14872, 13255, 2456),
  (13680, 18179, 1660), (4152, 20176, 24844), (30219, 4858, 24625), (7375, 13585, 13886),
  (13609, 27444, 13521), (29699, 10375, 26489), (28259, 3048, 24577), (32440, 507, 31497),
  (12159, 3194, 24273), (2537, 27166, 12734), (7730, 11162, 11463), (20660, 17540, 10506),
  (12915, 18221, 3417), (21164, 15848, 18517), (31037, 27423, 27934), (31861, 23242, 23731),
  (11256, 1974, 14515), (5502, 8465, 5236), (2496, 12327, 18443), (15990, 20076, 24045),
  (23817, 11317, 26044), (23259, 5891, 24656), (31247, 2015, 1429), (17016, 5659, 17455),
  (3095, 8161, 25266), (4433, 358, 10445), (8050, 103, 32212), (215, 18606, 14090),
  (7698, 25781, 10590), (27500, 27600, 26363), (22885, 29266, 4459), (7496, 25050, 22696),
  (17256, 10779, 30145), (9449, 26777, 26387), (25982, 5216, 5585), (29724, 11024, 10801),
  (32083, 29232, 22970), (11501, 2020, 9780), (25907, 6319, 26123), (19703, 7890, 26062),
  (5716, 24250, 2709), (4497, 11050, 31832), (23568, 22531, 29332), (12298, 22371, 20043)]

theorem prodRow543Taps_eq_generator : lpnMatrixRow auditSession 0 1 15 543 = prodRow543Taps := by
  decide +kernel

private theorem prodRow543_below : tapsBelow 32768 prodRow543Taps = true := by decide +kernel
private theorem prodRow543_upper : rowBiasNat 32768 prodRow543Taps * 2 ^ 89 < 32768 ^ 64 := by
  decide +kernel
private theorem prodRow543_lower : 32768 ^ 64 < rowBiasNat 32768 prodRow543Taps * 2 ^ 90 := by
  decide +kernel

/-- Its one-row bias lies strictly between `2^-90` and `2^-89`. -/
theorem generatedRow543_bias_bracket :
    (noiseSignedSum 32768 (rowTestFns (lpnMatrixRow auditSession 0 1 15 543)) false).natAbs * 2 ^ 89
        < 32768 ^ 64 ∧
    32768 ^ 64 <
      (noiseSignedSum 32768 (rowTestFns (lpnMatrixRow auditSession 0 1 15 543)) false).natAbs * 2 ^ 90 := by
  rw [prodRow543Taps_eq_generator, row_signed_count_natAbs 32768 prodRow543Taps prodRow543_below]
  exact ⟨prodRow543_upper, prodRow543_lower⟩

end Qsag
end

#verify_constructive Qsag.prodRow0Taps_eq_generator Qsag.generatedRow0_bias_bracket
  Qsag.prodRow543Taps_eq_generator Qsag.generatedRow543_bias_bracket
