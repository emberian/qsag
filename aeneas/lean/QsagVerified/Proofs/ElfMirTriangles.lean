module
public import QsagVerified.Proofs.RealSpecFieldWeld
public import QsagVerified.Proofs.RealSpecTowerWeld
public import QsagVerified.Proofs.RealSpecKeccakWeld
public import QsagVerified.Proofs.MirWpKit
public import Qsag.Machine.McRefine
public import Qsag.Machine.ElfFunctionalEquiv
import Qsag.Tactic.AssuranceKit

/-!
# Decoded ELF / canonical mathematics / extracted MIR triangles

Each execution theorem retains the real archive symbol lookup and byte decoder.
The output equality composes the ISA functional theorem with an extracted-function
weld through the same canonical mathematical specification. This is functional
refinement under the stated ABI preconditions, not a compiler-correctness theorem.
The 28-symbol leakage contracts are separately instantiated in PlatformContractInstances.
-/

public section
namespace qsag_verified.proofs
open Aeneas Aeneas.Std Result qsag_verified
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Canonical mathematical field elements encoded as extracted Rust words. -/
def mirFieldWord (a : Qsag.Goldilocks) : Std.U64 := ⟨BitVec.ofNat 64 a.val⟩

private theorem mirFieldWord_val (a : Qsag.Goldilocks) : (mirFieldWord a).val = a.val :=
  Nat.mod_eq_of_lt (Qsag.Goldilocks.val_lt_two_pow_64 a)

private theorem mirFieldWord_abs (a : Qsag.Goldilocks) : goldilocksAbs (mirFieldWord a) = a := by
  apply Qsag.Goldilocks.ext
  rw [goldilocksAbs_val]
  rw [mirFieldWord_val, Nat.mod_eq_of_lt a.isLt]

private theorem fieldWord_toNat (a : Qsag.Goldilocks) :
    (UInt64.ofNat a.val).toNat = a.val :=
  Nat.mod_eq_of_lt (Qsag.Goldilocks.val_lt_two_pow_64 a)

/-- The decoded x86_64 `.rlib` add symbol and extracted MIR compute the same canonical
    Goldilocks sum on every caller frame `s` (`pc = 0`, `halted = false`, `rdi = a`, `rsi = b`). -/
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
          ((Qsag.runX86 prog fuel s).1.gpr.get 0).toNat = y.val := by
  obtain ⟨y, hy, ha, hlt⟩ := goldilocks_add_refines_qsag (mirFieldWord a) (mirFieldWord b)
  rw [mirFieldWord_abs, mirFieldWord_abs] at ha
  have hv : y.val = (Qsag.Goldilocks.add a b).val := by
    have h := congrArg (fun x : Qsag.Goldilocks => x.val) ha
    rw [goldilocksAbs_val] at h
    rwa [Nat.mod_eq_of_lt hlt] at h
  obtain ⟨sl, prog, hf, hd, hs⟩ := Qsag.current_goldilocks_add_ct_x86_64_mc_refines
  rw [← Qsag.currentX86_rlib_extracted_slices] at hf
  refine ⟨sl, prog, y, hf, hd, hy, ha, fun s fuel hpc hh hr7 hr6 hfuel => ?_⟩
  have h := hs s fuel hpc hh hfuel
  refine ⟨h.1, h.2.2.1, ?_⟩
  rw [h.2.1, hr7, hr6, hv, fieldWord_toNat, fieldWord_toNat]
  exact (Qsag.Goldilocks.add_val a b).symm

/-- The decoded x86_64 `.rlib` sub symbol and extracted MIR compute the same canonical
    Goldilocks difference on every caller frame `s` (`pc = 0`, `halted = false`, `rdi = a`, `rsi = b`). -/
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
          ((Qsag.runX86 prog fuel s).1.gpr.get 0).toNat = y.val := by
  obtain ⟨y, hy, ha, hlt⟩ := goldilocks_sub_refines_qsag (mirFieldWord a) (mirFieldWord b)
  rw [mirFieldWord_abs, mirFieldWord_abs] at ha
  have hv : y.val = (Qsag.Goldilocks.sub a b).val := by
    have h := congrArg (fun x : Qsag.Goldilocks => x.val) ha
    rw [goldilocksAbs_val] at h
    rwa [Nat.mod_eq_of_lt hlt] at h
  obtain ⟨sl, prog, hf, hd, hs⟩ := Qsag.current_goldilocks_sub_ct_x86_64_mc_refines
  rw [← Qsag.currentX86_rlib_extracted_slices] at hf
  refine ⟨sl, prog, y, hf, hd, hy, ha, fun s fuel hpc hh hr7 hr6 hfuel => ?_⟩
  have h := hs s fuel hpc hh hfuel
  refine ⟨h.1, h.2.2.1, ?_⟩
  rw [h.2.1, hr7, hr6, hv, fieldWord_toNat, fieldWord_toNat, Nat.mod_eq_of_lt b.isLt,
    Qsag.Goldilocks.sub_val]

/-- The decoded x86_64 `.rlib` mul symbol and extracted MIR compute the same canonical
    Goldilocks product on every caller frame `s` (`pc = 0`, `halted = false`, `rdi = a`, `rsi = b`). -/
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
          ((Qsag.runX86 prog fuel s).1.gpr.get 0).toNat = y.val := by
  obtain ⟨y, hy, ha, hlt⟩ := goldilocks_mul_refines_qsag (mirFieldWord a) (mirFieldWord b)
  rw [mirFieldWord_abs, mirFieldWord_abs] at ha
  have hv : y.val = (Qsag.Goldilocks.mul a b).val := by
    have h := congrArg (fun x : Qsag.Goldilocks => x.val) ha
    rw [goldilocksAbs_val] at h
    rwa [Nat.mod_eq_of_lt hlt] at h
  obtain ⟨sl, prog, hf, hd, hs⟩ := Qsag.current_goldilocks_mul_ct_x86_64_mc_refines
  rw [← Qsag.currentX86_rlib_extracted_slices] at hf
  refine ⟨sl, prog, y, hf, hd, hy, ha, fun s fuel hpc hh hr7 hr6 hfuel => ?_⟩
  have h := hs s fuel hpc hh hfuel
  refine ⟨h.1, h.2.2.1, ?_⟩
  rw [h.2.1, hr7, hr6, hv, fieldWord_toNat, fieldWord_toNat]
  exact (Qsag.Goldilocks.mul_val a b).symm

/-- The decoded aarch64 `.rlib` mul symbol and extracted MIR compute the same canonical
    Goldilocks product on every caller frame `s` (`pc = 0`, `halted = false`, `x0 = a`, `x1 = b`). -/
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
          ((Qsag.runArm64 prog fuel s).1.gpr.get 0).toNat = y.val := by
  obtain ⟨y, hy, ha, hlt⟩ := goldilocks_mul_refines_qsag (mirFieldWord a) (mirFieldWord b)
  rw [mirFieldWord_abs, mirFieldWord_abs] at ha
  have hv : y.val = (Qsag.Goldilocks.mul a b).val := by
    have h := congrArg (fun x : Qsag.Goldilocks => x.val) ha
    rw [goldilocksAbs_val] at h
    rwa [Nat.mod_eq_of_lt hlt] at h
  obtain ⟨sl, prog, hf, hd, hs⟩ := Qsag.current_goldilocks_mul_ct_aarch64_mc_refines
  rw [← Qsag.currentAarch64_rlib_extracted_slices] at hf
  refine ⟨sl, prog, y, hf, hd, hy, ha, fun s fuel hpc hh hr0 hr1 hfuel => ?_⟩
  have h := hs s fuel hpc hh hfuel
  refine ⟨h.1, h.2.2.1, ?_⟩
  rw [h.2.1, hr0, hr1, hv, fieldWord_toNat, fieldWord_toNat]
  exact (Qsag.Goldilocks.mul_val a b).symm

/-- All four lanes of the real AVX2 `.rlib` symbol compute `Qsag.keccakF1600` and agree with
    extracted `keccak.keccak_f1600`; the ISA theorem also supplies termination and YMM cleanup. -/
theorem elf_mir_keccak_f1600_avx2_4x (s : Qsag.X86State) (h : Qsag.keccak4xFullEntry s) :
    ∃ slice prog,
      Qsag.findSliceByNameBytes
        (Qsag.extractAllRlibFuncs Qsag.currentX86RlibArchiveBytes) Qsag.keccak4xName = some slice ∧
      Qsag.decodeX86Stream slice.code = some prog ∧
      (Qsag.runX86 prog 6661 s).1.halted = true ∧
      (Qsag.runX86 prog 6661 s).1.ymm = Qsag.Bank16.const Qsag.Vec256.zero ∧
      (Qsag.runX86 prog 6661 s).1.ymmDirty = false ∧
      ∀ q : Nat, q < 4 →
        let laneIn := Qsag.keccak4xLaneState (Qsag.keccak4xSource s.mem (s.gpr.get 7)) q
        let laneOut := Qsag.keccak4xLaneState
          (Qsag.keccak4xSource (Qsag.runX86 prog 6661 s).1.mem (s.gpr.get 7)) q
        laneOut = Qsag.keccakF1600 laneIn ∧
        keccak.keccak_f1600 (keccakArrayOfState laneIn) = .ok (keccakArrayOfState laneOut) := by
  obtain ⟨sl, prog, hf, hd, _, hh, hy, hdy, hout⟩ :=
    Qsag.current_rlib_keccak_f1600_avx2_4x_functional s h
  rw [← Qsag.currentX86_rlib_extracted_slices] at hf
  refine ⟨sl, prog, hf, hd, hh, hy, hdy, fun q hq => ?_⟩
  dsimp only
  refine ⟨hout q hq, ?_⟩
  rw [hout q hq]
  exact keccak_f1600_refines_qsag _

/-- The real GFNI `.rlib` symbol's 32 byte products compute `Qsag.towerMul 3` under `unpackTower 3`
    and equal the extracted `tower.gf256_mul` output byte-for-byte with clean upper YMM state. -/
theorem elf_mir_gf256_gfni :
    ∃ slice,
      Qsag.extractRlibFuncBytes Qsag.currentX86RlibArchiveBytes
        "qsag_asm_gf256_shamir_mul_gfni" = some slice ∧
      Qsag.ElfSliceThreeWayNISafe slice
        (Qsag.mkContract "qsag_asm_gf256_shamir_mul_gfni" [4, 7, 6, 2, 1]) ∧
      ∀ st : Qsag.X86BvState, st.pc = 0 → st.halted = false → st.gpr.get 1 = 1#64 →
        ∃ st' trace, Qsag.execDecodedX86 slice.code 35 st = some (st', trace) ∧
          st'.halted = true ∧
          st'.ymmDirty = false ∧
          ∀ k : Nat, k < 32 →
            let aBv := (st.mem (st.gpr.get 6 + BitVec.ofNat 64 k)).toBitVec
            let bBv := (st.mem (st.gpr.get 2 + BitVec.ofNat 64 k)).toBitVec
            let outBv := (st'.mem (st.gpr.get 7 + BitVec.ofNat 64 k)).toBitVec
            Qsag.unpackTower 3 outBv =
              Qsag.towerMul 3 (Qsag.unpackTower 3 aBv) (Qsag.unpackTower 3 bBv) ∧
            tower.gf256_mul ⟨aBv⟩ ⟨bBv⟩ = .ok ⟨outBv⟩ := by
  obtain ⟨sl, _, he, _, _, _, hsafe, _, hs⟩ :=
    Qsag.current_rlib_gf256_shamir_mul_gfni_functional_and_ct
  refine ⟨sl, he, hsafe, fun st hp hh hn => ?_⟩
  obtain ⟨st', tr, hex, hhalt, _, _, hclean, _, _, _, _, _, _, _, _, _, _, hout, _⟩ :=
    (hs st hp hh hn).2 0
  refine ⟨st', tr, hex, hhalt, hclean, fun k hk => ?_⟩
  dsimp only
  have hm := Qsag.elfSimulates_pack_eq (hout k hk).2
  have hspec : Qsag.unpackTower 3 (st'.mem (st.gpr.get 7 + BitVec.ofNat 64 k)).toBitVec =
      Qsag.towerMul 3
        (Qsag.unpackTower 3 (st.mem (st.gpr.get 6 + BitVec.ofNat 64 k)).toBitVec)
        (Qsag.unpackTower 3 (st.mem (st.gpr.get 2 + BitVec.ofNat 64 k)).toBitVec) := by
    rw [← hm, Qsag.unpackTower_packTower]
  refine ⟨hspec, ?_⟩
  obtain ⟨y, hy, habs⟩ := gf256_mul_refines_qsag
    ⟨(st.mem (st.gpr.get 6 + BitVec.ofNat 64 k)).toBitVec⟩
    ⟨(st.mem (st.gpr.get 2 + BitVec.ofNat 64 k)).toBitVec⟩
  rw [hy]
  congr 1
  apply UScalar.ext
  have heq := congrArg (Qsag.packTower 3) habs
  rw [Qsag.packTower_unpackTower, hm] at heq
  exact heq

/-- A PCLMUL `.rlib` polynomial-basis product, converted through the proved basis isomorphism,
    agrees with `Qsag.towerMul 7` and extracted `tower.tower128_mul`, preserving the initial accumulator. -/
theorem elf_mir_tower128_pclmul (s : Qsag.X86State)
    (hp : s.pc = 0) (hh : s.halted = false) (hn : s.gpr.r1 = 1) :
    let a := Qsag.polyToTower128 (Qsag.gf128Words
      (Qsag.readMem128 s.mem s.gpr.r6).w0 (Qsag.readMem128 s.mem s.gpr.r6).w1)
    let b := Qsag.polyToTower128 (Qsag.gf128Words
      (Qsag.readMem128 s.mem s.gpr.r2).w0 (Qsag.readMem128 s.mem s.gpr.r2).w1)
    ∃ slice y,
      Qsag.findSliceByNameBytes
        (Qsag.extractAllRlibFuncs Qsag.currentX86RlibArchiveBytes) Qsag.gf128PclmulName = some slice ∧
      Qsag.decodeX86Stream slice.code = some Qsag.gf128PclmulProg ∧
      tower.tower128_mul ⟨Qsag.packTower 7 a⟩ ⟨Qsag.packTower 7 b⟩ = .ok y ∧
      Qsag.unpackTower 7 y.bv = Qsag.towerMul 7 a b ∧
      (Qsag.runX86 Qsag.gf128PclmulProg 50 s).1.halted = true ∧
      Qsag.polyToTower128 (Qsag.gf128Words
        (Qsag.readMem64 (Qsag.runX86 Qsag.gf128PclmulProg 50 s).1.mem s.gpr.r7)
        (Qsag.readMem64 (Qsag.runX86 Qsag.gf128PclmulProg 50 s).1.mem (s.gpr.r7 + 8))) =
      Qsag.towerAdd 7
        (Qsag.polyToTower128 (Qsag.gf128Words (Qsag.readMem64 s.mem s.gpr.r7)
          (Qsag.readMem64 s.mem (s.gpr.r7 + 8)))) (Qsag.unpackTower 7 y.bv) := by
  intro a b
  obtain ⟨y, hy, habs⟩ := tower128_mul_refines_qsag ⟨Qsag.packTower 7 a⟩ ⟨Qsag.packTower 7 b⟩
  dsimp only at habs
  rw [Qsag.unpackTower_packTower, Qsag.unpackTower_packTower] at habs
  obtain ⟨sl, hf, hd, hhalt, _, _⟩ :=
    Qsag.current_rlib_gf2_128_mul_acc_pclmul_functional s 0 0 (by decide) hp hh hn
  rw [← Qsag.currentX86_rlib_extracted_slices] at hf
  refine ⟨sl, y, hf, hd, hy, habs, hhalt, ?_⟩
  have hout := Qsag.current_rlib_gf2_128_mul_acc_pclmul_tower_dot s 0 0 (by decide) hp hh hn
  rw [habs]
  simpa only [Nat.zero_add, Qsag.gf128PclmulTowerSum_one] using hout

end qsag_verified.proofs
end

#verify_constructive qsag_verified.proofs.elf_mir_goldilocks_add_x86_64
#verify_constructive qsag_verified.proofs.elf_mir_goldilocks_sub_x86_64
#verify_constructive qsag_verified.proofs.elf_mir_goldilocks_mul_x86_64
#verify_constructive qsag_verified.proofs.elf_mir_goldilocks_mul_aarch64
#verify_constructive qsag_verified.proofs.elf_mir_keccak_f1600_avx2_4x
#verify_constructive qsag_verified.proofs.elf_mir_gf256_gfni

#verify_constructive qsag_verified.proofs.elf_mir_tower128_pclmul
