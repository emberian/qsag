module
/-
# Qsag.SpirvSimtGpuEquiv — Binary SPIR-V 1.6 Compute, Multi-Wave Wave32 SIMT, Faial DRF & SIMT-CT

Machine-checked Lean 4.35 GPU verification foundation (`0 sorry`, `0 bv_decide`, `0 native_decide`,
`0 Classical.choice`, axioms strictly within `{propext, Quot.sound}`):

1. **§1 Structured `SPIR-V 1.6` Compute Module AST & Binary `Array UInt32` Word Codec:**
   Exact Khronos `SPIR-V 1.6` 5-word binary header (`magic = 0x07230203`, `version = 0x00010600`),
   capabilities (`Shader`, `Int64`, `SubgroupDispatch`, `GroupNonUniform`, `VulkanMemoryModel`),
   execution modes (`LocalSize`, `SubgroupSize 32`), decorations, SSA type/global declarations,
   64-bit & 32-bit `OpUMulExtended` / `OpSelect` / `OpAccessChain` / `OpLoad` / `OpStore` /
   `OpControlBarrier` (`Workgroup`, `AcquireRelease | WorkgroupMemory = 0x108`), and verified
   roundtrip `decodeSpirvModule (encodeSpirvModule m) = .ok m` (`encodeSpirvModule_injective`).
2. **§2 Genuine Multi-Wave Wave32 Workgroup Operational Semantics (`64 KiB` Shared LDS):**
   Models `numWaves * 32` threads (e.g. `8` Wave32 subgroups = `256` threads) sharing persistent
   `64 KiB` (`16,384`-dword) `Workgroup` LDS and global `StorageBuffer` memory under arbitrary
   cross-wave instruction interleavings with lockstep workgroup-wide `OpControlBarrier` release.
3. **§3 Compositional `Faial` MAP Data-Race Freedom & `SIMT-CT` Side-Channel Immunity:**
   Proves deterministic confluence across all valid wave interleavings (`multiWave_schedule_confluence`)
   from per-epoch pairwise write/read disjointness, paired with `#tooth` witnesses for missing
   barriers (`tooth_missing_barrier_causes_cross_wave_lds_race`) and single-wave LDS-wipe models
   (`tooth_single_wave_lds_wipe_corrupts_multiwave_reduction`). Establishes `SIMT-CT` hardware
   leakage-trace noninterference (`simt_ct_noninterference`) covering zero `EXEC`-mask divergence,
   public-affine coalesced global addressing, and 32-bank conflict-free LDS addressing
   (`odd_stride_lds_bank_conflict_free`, `merkle_skewed_lds_bank_conflict_free_both_epochs`, and
   `tooth_stride32_lds_causes_32way_bank_conflict`).
4. **§4 Parametric Functional Equivalence (`∀ numBlocks`, Scaling to $N = 2^{22}$ in $O(1)$ Proof Size):**
   - Branchless 32-bit KoalaBear (`p = 2^31 - 2^24 + 1 = 2130706433`) Montgomery & 64-bit
     Goldilocks (`p = 2^64 - 2^32 + 1`) Solinas `OpUMulExtended` + `OpSelect` compute kernels;
   - Batched Width-12 `Poseidon2` (`x^7` S-box, zero-mul `M_4` / `M_E`, internal diagonal `M_I`,
     full 30-round `poseidon2Perm12`) and multi-wave shared-LDS 2-layer Merkle tree compute kernel;
   - Batched quartic `KoalaBearExt4` and `GoldilocksExt4` WHIR coset duet fold (`foldDuet`) kernels
     with `Faial` DRF and `SIMT-CT` proved simultaneously.
-/

public import Qsag.Constructive
import all Qsag.Constructive
public import Qsag.Goldilocks
import all Qsag.Goldilocks
public import Qsag.Poseidon2
import all Qsag.Poseidon2
public import Qsag.Aggregation
import all Qsag.Aggregation

public section
namespace Qsag

open Aggregation

attribute [-instance] UInt8.instLawfulEqOrd UInt32.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd

set_option autoImplicit false

/-! ## §1. Binary `SPIR-V 1.6` Compute Module AST & Verified `Array UInt32` Encoder/Decoder -/

/-- Khronos SPIR-V magic number (`0x07230203`). -/
def spirvMagic : UInt32 := 0x07230203

/-- Khronos SPIR-V 1.6 version word (`major = 1, minor = 6 -> 0x00010600`). -/
def spirvVersion16 : UInt32 := 0x00010600

/-- Little-endian UTF-8 word 0 of entry-point literal `"main\0"`. -/
def spirvMainWord0 : UInt32 := 0x6E69616D

/-- Little-endian UTF-8 word 1 (null padding) of entry-point literal `"main\0"`. -/
def spirvMainWord1 : UInt32 := 0x00000000

/-- SPIR-V `ExecutionModel.GLCompute = 5`. -/
def spirvExecModelGLCompute : UInt32 := 5

/-- SPIR-V `MemorySemantics` bitmasks (`AcquireRelease = 0x8`, `WorkgroupMemory = 0x100`). -/
def spirvSemAcquireRelease : UInt32 := 0x00000008
def spirvSemUniformMemory : UInt32 := 0x00000040
def spirvSemWorkgroupMemory : UInt32 := 0x00000100
def spirvSemWorkgroupAcqRel : UInt32 := 0x00000108

theorem spirvSemWorkgroupAcqRel_eq_or :
    spirvSemWorkgroupAcqRel = (spirvSemWorkgroupMemory ||| spirvSemAcquireRelease) := by
  decide

/-- Pack a SPIR-V instruction header word `(wordCount <<< 16) ||| opcode`. -/
def packSpirvWord0 (wordCount opcode : Nat) : UInt32 :=
  (UInt32.ofNat wordCount <<< 16) ||| UInt32.ofNat opcode

/-- Extract the 16-bit `wordCount` field from a SPIR-V instruction header word. -/
def unpackSpirvWordCount (w0 : UInt32) : Nat :=
  (w0 >>> 16).toNat

/-- Extract the 16-bit `opcode` field from a SPIR-V instruction header word. -/
def unpackSpirvOpcode (w0 : UInt32) : Nat :=
  (w0 &&& 0xFFFF).toNat

private theorem nat_shiftLeft_16_lt {wc : Nat} (hwc : wc < 65536) :
    wc <<< 16 < 4294967296 := by
  rw [Nat.shiftLeft_eq]
  have h16 : (2 : Nat) ^ 16 = 65536 := rfl
  rw [h16]
  omega

private theorem toNat_packSpirvWord0 {wc op : Nat} (hwc : wc < 65536) (hop : op < 65536) :
    (packSpirvWord0 wc op).toNat = (wc <<< 16) ||| op := by
  unfold packSpirvWord0
  have hwc32 : wc < 4294967296 := by omega
  have hop32 : op < 4294967296 := by omega
  have hsh32 : wc <<< 16 < 4294967296 := nat_shiftLeft_16_lt hwc
  have h1 : (UInt32.ofNat wc <<< 16).toNat = wc <<< 16 := by
    rw [UInt32.toNat_shiftLeft]
    simp only [UInt32.toNat_ofNat', show (2 : Nat) ^ 32 = 4294967296 from rfl,
      Nat.mod_eq_of_lt hwc32, show (16 : Nat) % 4294967296 % 32 = 16 from rfl,
      Nat.mod_eq_of_lt hsh32]
  have h2 : (UInt32.ofNat op).toNat = op := by
    rw [UInt32.toNat_ofNat', show (2 : Nat) ^ 32 = 4294967296 from rfl, Nat.mod_eq_of_lt hop32]
  rw [UInt32.toNat_or, h1, h2]

theorem unpack_packSpirvWord0 {wc op : Nat} (hwc : wc < 65536) (hop : op < 65536) :
    unpackSpirvWordCount (packSpirvWord0 wc op) = wc ∧
    unpackSpirvOpcode (packSpirvWord0 wc op) = op := by
  have hPack := toNat_packSpirvWord0 hwc hop
  have hopPow : op < 2 ^ 16 := by
    simpa [show (2 : Nat) ^ 16 = 65536 from rfl] using hop
  refine ⟨?_, ?_⟩
  · unfold unpackSpirvWordCount
    rw [UInt32.toNat_shiftRight, hPack]
    simp only [UInt32.toNat_ofNat', show (16 : Nat) % 2 ^ 32 % 32 = 16 from rfl]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_shiftRight, Nat.testBit_or]
    have hOpZero : op.testBit (16 + i) = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hopPow (Nat.pow_le_pow_right (by decide) (by omega)))
    have hSh : (wc <<< 16).testBit (16 + i) = wc.testBit i := by
      rw [Nat.testBit_shiftLeft]
      simp [show 16 ≤ 16 + i by omega, show 16 + i - 16 = i by omega]
    rw [hOpZero, hSh, Bool.or_false]
  · unfold unpackSpirvOpcode
    rw [UInt32.toNat_and, hPack]
    have hMask : (0xFFFF : UInt32).toNat = 2 ^ 16 - 1 := rfl
    rw [hMask]
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_or, Constructive.testBit_mask]
    by_cases hi : i < 16
    · have hShZero : (wc <<< 16).testBit i = false := by
        rw [Nat.testBit_shiftLeft]
        simp [show ¬ (16 ≤ i) by omega]
      simp [hi, hShZero]
    · have hOpZero : op.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hopPow (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hi, hOpZero]

/-- Split a `UInt64` into its low and high 32-bit `UInt32` words (little-endian SPIR-V literal order). -/
def u64Lo32 (v : UInt64) : UInt32 := UInt32.ofNat (v.toNat % 4294967296)
def u64Hi32 (v : UInt64) : UInt32 := UInt32.ofNat (v.toNat / 4294967296)
def u64OfLoHi32 (lo hi : UInt32) : UInt64 := UInt64.ofNat (lo.toNat + 4294967296 * hi.toNat)

theorem u64OfLoHi32_lo_hi (v : UInt64) : u64OfLoHi32 (u64Lo32 v) (u64Hi32 v) = v := by
  unfold u64OfLoHi32 u64Lo32 u64Hi32
  have hv : v.toNat < 18446744073709551616 := v.toNat_lt
  have hlo : v.toNat % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)
  have hhi : v.toNat / 4294967296 < 4294967296 := by omega
  apply UInt64.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  change (UInt64.ofNat _).toNat = v.toNat
  rw [UInt64.toNat_ofNat']
  simp only [UInt32.toNat_ofNat', show (2 : Nat) ^ 32 = 4294967296 from rfl,
    show (2 : Nat) ^ 64 = 18446744073709551616 from rfl,
    Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hhi]
  rw [Nat.mod_add_div, Nat.mod_eq_of_lt hv]

theorem u64Lo32_u64OfLoHi32 (lo hi : UInt32) : u64Lo32 (u64OfLoHi32 lo hi) = lo := by
  unfold u64Lo32 u64OfLoHi32
  have hlo : lo.toNat < 4294967296 := lo.toNat_lt
  have hhi : hi.toNat < 4294967296 := hi.toNat_lt
  have hsum : lo.toNat + 4294967296 * hi.toNat < 18446744073709551616 := by omega
  apply UInt32.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  change (UInt32.ofNat _).toNat = lo.toNat
  rw [UInt32.toNat_ofNat', UInt64.toNat_ofNat']
  simp only [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl,
    show (2 : Nat) ^ 32 = 4294967296 from rfl, Nat.mod_eq_of_lt hsum]
  omega

theorem u64Hi32_u64OfLoHi32 (lo hi : UInt32) : u64Hi32 (u64OfLoHi32 lo hi) = hi := by
  unfold u64Hi32 u64OfLoHi32
  have hlo : lo.toNat < 4294967296 := lo.toNat_lt
  have hhi : hi.toNat < 4294967296 := hi.toNat_lt
  have hsum : lo.toNat + 4294967296 * hi.toNat < 18446744073709551616 := by omega
  apply UInt32.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  change (UInt32.ofNat _).toNat = hi.toNat
  rw [UInt32.toNat_ofNat', UInt64.toNat_ofNat']
  simp only [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl,
    show (2 : Nat) ^ 32 = 4294967296 from rfl, Nat.mod_eq_of_lt hsum]
  omega

/-- Capabilities in the compute `SPIR-V 1.6` profile (`OpCapability = 17`). -/
inductive SpirvCapability where
  | shader
  | int64
  | subgroupDispatch
  | groupNonUniform
  | vulkanMemoryModel
  deriving DecidableEq, Repr

def SpirvCapability.toWord : SpirvCapability → UInt32
  | .shader => 1
  | .int64 => 11
  | .subgroupDispatch => 58
  | .groupNonUniform => 61
  | .vulkanMemoryModel => 5345

def SpirvCapability.ofWord? (w : UInt32) : Option SpirvCapability :=
  if w == 1 then some .shader
  else if w == 11 then some .int64
  else if w == 58 then some .subgroupDispatch
  else if w == 61 then some .groupNonUniform
  else if w == 5345 then some .vulkanMemoryModel
  else none

theorem SpirvCapability.ofWord?_toWord (c : SpirvCapability) :
    SpirvCapability.ofWord? c.toWord = some c := by
  cases c <;> decide

/-- Addressing model (`OpMemoryModel` operand 0). -/
inductive SpirvAddressingModel where
  | logical
  | physicalStorageBuffer64
  deriving DecidableEq, Repr

def SpirvAddressingModel.toWord : SpirvAddressingModel → UInt32
  | .logical => 0
  | .physicalStorageBuffer64 => 5348

def SpirvAddressingModel.ofWord? (w : UInt32) : Option SpirvAddressingModel :=
  if w == 0 then some .logical
  else if w == 5348 then some .physicalStorageBuffer64
  else none

theorem SpirvAddressingModel.ofWord?_toWord (a : SpirvAddressingModel) :
    SpirvAddressingModel.ofWord? a.toWord = some a := by
  cases a <;> decide

/-- Memory consistency model (`OpMemoryModel` operand 1). -/
inductive SpirvMemoryModelKind where
  | glsl450
  | vulkan
  deriving DecidableEq, Repr

def SpirvMemoryModelKind.toWord : SpirvMemoryModelKind → UInt32
  | .glsl450 => 1
  | .vulkan => 3

def SpirvMemoryModelKind.ofWord? (w : UInt32) : Option SpirvMemoryModelKind :=
  if w == 1 then some .glsl450
  else if w == 3 then some .vulkan
  else none

theorem SpirvMemoryModelKind.ofWord?_toWord (m : SpirvMemoryModelKind) :
    SpirvMemoryModelKind.ofWord? m.toWord = some m := by
  cases m <;> decide

/-- Compute execution modes (`LocalSize = 17`, `SubgroupSize = 35`). -/
inductive SpirvExecutionMode where
  | localSize (x y z : UInt32)
  | subgroupSize (sz : UInt32)
  deriving DecidableEq, Repr

/-- SPIR-V storage classes (`Input = 1`, `Workgroup = 4`, `Function = 7`, `PushConstant = 9`, `StorageBuffer = 12`). -/
inductive SpirvStorageClass where
  | input
  | workgroup
  | function
  | pushConstant
  | storageBuffer
  deriving DecidableEq, Repr

def SpirvStorageClass.toWord : SpirvStorageClass → UInt32
  | .input => 1
  | .workgroup => 4
  | .function => 7
  | .pushConstant => 9
  | .storageBuffer => 12

def SpirvStorageClass.ofWord? (w : UInt32) : Option SpirvStorageClass :=
  if w == 1 then some .input
  else if w == 4 then some .workgroup
  else if w == 7 then some .function
  else if w == 9 then some .pushConstant
  else if w == 12 then some .storageBuffer
  else none

theorem SpirvStorageClass.ofWord?_toWord (sc : SpirvStorageClass) :
    SpirvStorageClass.ofWord? sc.toWord = some sc := by
  cases sc <;> decide

/-- Built-in compute invocation identifiers (`OpDecorate BuiltIn`). -/
inductive SpirvBuiltIn where
  | workgroupId
  | localInvocationId
  | globalInvocationId
  | localInvocationIndex
  | subgroupSize
  | subgroupId
  | subgroupLocalInvocationId
  deriving DecidableEq, Repr

def SpirvBuiltIn.toWord : SpirvBuiltIn → UInt32
  | .workgroupId => 26
  | .localInvocationId => 27
  | .globalInvocationId => 28
  | .localInvocationIndex => 29
  | .subgroupSize => 36
  | .subgroupId => 40
  | .subgroupLocalInvocationId => 41

def SpirvBuiltIn.ofWord? (w : UInt32) : Option SpirvBuiltIn :=
  if w == 26 then some .workgroupId
  else if w == 27 then some .localInvocationId
  else if w == 28 then some .globalInvocationId
  else if w == 29 then some .localInvocationIndex
  else if w == 36 then some .subgroupSize
  else if w == 40 then some .subgroupId
  else if w == 41 then some .subgroupLocalInvocationId
  else none

theorem SpirvBuiltIn.ofWord?_toWord (b : SpirvBuiltIn) :
    SpirvBuiltIn.ofWord? b.toWord = some b := by
  cases b <;> decide

/-- Decorations (`OpDecorate = 71`). -/
inductive SpirvDecoration where
  | block
  | arrayStride (byteStride : UInt32)
  | builtIn (b : SpirvBuiltIn)
  | binding (slot : UInt32)
  | descriptorSet (setIdx : UInt32)
  deriving DecidableEq, Repr

structure SpirvDecorateDecl where
  targetId : UInt32
  dec : SpirvDecoration
  deriving DecidableEq, Repr

/-- SPIR-V execution/memory scopes (`Device = 1`, `Workgroup = 2`, `Subgroup = 3`, `Invocation = 4`). -/
inductive SpirvScope where
  | device
  | workgroup
  | subgroup
  | invocation
  deriving DecidableEq, Repr

def SpirvScope.toWord : SpirvScope → UInt32
  | .device => 1
  | .workgroup => 2
  | .subgroup => 3
  | .invocation => 4

def SpirvScope.ofWord? (w : UInt32) : Option SpirvScope :=
  if w == 1 then some .device
  else if w == 2 then some .workgroup
  else if w == 3 then some .subgroup
  else if w == 4 then some .invocation
  else none

theorem SpirvScope.ofWord?_toWord (s : SpirvScope) :
    SpirvScope.ofWord? s.toWord = some s := by
  cases s <;> decide

/-- Integer widths supported by `OpTypeInt` in compute kernels (`32` and `64` bits). -/
inductive SpirvIntWidth where
  | w32
  | w64
  deriving DecidableEq, Repr

def SpirvIntWidth.toWord : SpirvIntWidth → UInt32
  | .w32 => 32
  | .w64 => 64

def SpirvIntWidth.ofWord? (w : UInt32) : Option SpirvIntWidth :=
  if w == 32 then some .w32
  else if w == 64 then some .w64
  else none

theorem SpirvIntWidth.ofWord?_toWord (w : SpirvIntWidth) :
    SpirvIntWidth.ofWord? w.toWord = some w := by
  cases w <;> decide

/-- Type declarations (`OpTypeVoid = 19`, `OpTypeBool = 20`, `OpTypeInt = 21`, `OpTypeArray = 28`,
    `OpTypeRuntimeArray = 29`, `OpTypeStruct = 30`, `OpTypePointer = 32`, `OpTypeFunction = 33`). -/
inductive SpirvTypeDecl where
  | typeVoid (resId : UInt32)
  | typeBool (resId : UInt32)
  | typeInt (resId : UInt32) (width : SpirvIntWidth) (signed : Bool)
  | typeArray (resId elemTyId lenConstId : UInt32)
  | typeRuntimeArray (resId elemTyId : UInt32)
  | typeStruct (resId : UInt32) (fieldTyIds : List UInt32)
  | typePointer (resId : UInt32) (sc : SpirvStorageClass) (pointeeTyId : UInt32)
  | typeFunctionVoid (resId voidTyId : UInt32)
  deriving DecidableEq, Repr

/-- Constants & module-scope variables (`OpConstantTrue = 41`, `OpConstantFalse = 42`,
    `OpConstant = 43`, `OpVariable = 59`). -/
inductive SpirvGlobalDecl where
  | constTrue (tyId resId : UInt32)
  | constFalse (tyId resId : UInt32)
  | const32 (tyId resId val : UInt32)
  | const64 (tyId resId : UInt32) (val : UInt64)
  | variable (tyId resId : UInt32) (sc : SpirvStorageClass)
  deriving DecidableEq, Repr

/-- Compute function body SSA instructions with exact Khronos `SPIR-V 1.6` opcodes. -/
inductive SpirvInst where
  | opLoad (tyId resId ptrId : UInt32)
  | opStore (ptrId valId : UInt32)
  | opAccessChain (tyId resId baseId : UInt32) (indices : List UInt32)
  | opCompositeExtract (tyId resId compId fieldIdx : UInt32)
  | opUConvert (tyId resId valId : UInt32)
  | opIAdd (tyId resId aId bId : UInt32)
  | opISub (tyId resId aId bId : UInt32)
  | opIMul (tyId resId aId bId : UInt32)
  | opUMulExtended (tyId resId aId bId : UInt32)
  | opSelect (tyId resId condId trueId falseId : UInt32)
  | opIEqual (tyId resId aId bId : UInt32)
  | opUGreaterThanEqual (tyId resId aId bId : UInt32)
  | opULessThan (tyId resId aId bId : UInt32)
  | opShiftRightLogical (tyId resId baseId shiftId : UInt32)
  | opShiftLeftLogical (tyId resId baseId shiftId : UInt32)
  | opBitwiseXor (tyId resId aId bId : UInt32)
  | opBitwiseOr (tyId resId aId bId : UInt32)
  | opBitwiseAnd (tyId resId aId bId : UInt32)
  | opControlBarrier (execScope memScope : SpirvScope) (semanticsMask : UInt32)
  | opLoopMerge (mergeLabelId contLabelId loopCtrl : UInt32)
  | opSelectionMerge (mergeLabelId selectionCtrl : UInt32)
  | opLabel (labelId : UInt32)
  | opBranch (targetLabelId : UInt32)
  | opBranchConditional (condId trueLabelId falseLabelId : UInt32)
  deriving DecidableEq, Repr

/-- Complete structured `SPIR-V 1.6` compute module. -/
structure SpirvModule where
  generator : UInt32
  idBound : UInt32
  capabilities : List SpirvCapability
  addrModel : SpirvAddressingModel
  memModel : SpirvMemoryModelKind
  entryFuncId : UInt32
  interfaceIds : List UInt32
  execModes : List SpirvExecutionMode
  decorations : List SpirvDecorateDecl
  types : List SpirvTypeDecl
  globals : List SpirvGlobalDecl
  voidTypeId : UInt32
  funcTypeId : UInt32
  entryLabelId : UInt32
  body : List SpirvInst
  deriving DecidableEq, Repr

/-- Decidable well-formedness of a `SpirvModule` for lossless 16-bit word-count framing. -/
def SpirvTypeDecl.wf : SpirvTypeDecl → Bool
  | .typeStruct _ fields => decide (fields.length + 2 < 65536)
  | _ => true

def SpirvInst.wf : SpirvInst → Bool
  | .opAccessChain _ _ _ indices => decide (indices.length + 4 < 65536)
  | _ => true

def WellFormedSpirvModule (m : SpirvModule) : Bool :=
  decide (0 < m.idBound.toNat) &&
  decide (m.interfaceIds.length + 5 < 65536) &&
  m.types.all SpirvTypeDecl.wf &&
  m.body.all SpirvInst.wf

/-- Raw framed SPIR-V instruction (`opcode < 65536` and `operands`). -/
structure RawSpirvInst where
  opcode : Nat
  operands : List UInt32
  deriving DecidableEq, Repr

def RawSpirvInst.wf (r : RawSpirvInst) : Bool :=
  decide (r.opcode < 65536) && decide (r.operands.length + 1 < 65536)

def encodeRawInst (r : RawSpirvInst) : List UInt32 :=
  packSpirvWord0 (r.operands.length + 1) r.opcode :: r.operands

def encodeRawInstList : List RawSpirvInst → List UInt32
  | [] => []
  | r :: rs => encodeRawInst r ++ encodeRawInstList rs

theorem encodeRawInstList_append (xs ys : List RawSpirvInst) :
    encodeRawInstList (xs ++ ys) = encodeRawInstList xs ++ encodeRawInstList ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeRawInstList, ih, List.append_assoc]

/-- Errors returned by the binary `SPIR-V 1.6` decoder. -/
inductive SpirvDecodeError where
  | truncatedHeader
  | badMagic (got : UInt32)
  | badVersion (got : UInt32)
  | badSchema (got : UInt32)
  | zeroIdBound
  | zeroWordCount
  | truncatedInstruction
  | malformedSection (msg : String)
  deriving DecidableEq, Repr

/-- Fuel-totalized word-stream splitter into `RawSpirvInst`s. -/
def parseRawInstStreamAux : Nat → List UInt32 → Except SpirvDecodeError (List RawSpirvInst)
  | _, [] => .ok []
  | 0, _ :: _ => .error .truncatedInstruction
  | fuel + 1, w0 :: rest =>
    let wc := unpackSpirvWordCount w0
    let op := unpackSpirvOpcode w0
    if wc == 0 then
      .error .zeroWordCount
    else if rest.length < wc - 1 then
      .error .truncatedInstruction
    else
      let args := rest.take (wc - 1)
      let rem := rest.drop (wc - 1)
      match parseRawInstStreamAux fuel rem with
      | .ok tail => .ok (⟨op, args⟩ :: tail)
      | .error e => .error e

def parseRawInstStream (words : List UInt32) : Except SpirvDecodeError (List RawSpirvInst) :=
  parseRawInstStreamAux words.length words

private theorem parseRawInstStreamAux_fuel_mono :
    ∀ {f1 f2 : Nat} {ws : List UInt32},
      ws.length ≤ f1 → ws.length ≤ f2 →
      parseRawInstStreamAux f1 ws = parseRawInstStreamAux f2 ws
  | _, _, [], _, _ => by
    cases f1 <;> cases f2 <;> rfl
  | 0, _, _ :: _, h1, _ => by simp at h1
  | _, 0, _ :: _, _, h2 => by simp at h2
  | f1 + 1, f2 + 1, w0 :: rest, h1, h2 => by
    simp only [parseRawInstStreamAux]
    by_cases hwc0 : (unpackSpirvWordCount w0 == 0) = true
    · simp [hwc0]
    · simp only [hwc0, Bool.false_eq_true, ↓reduceIte]
      by_cases hlt : rest.length < unpackSpirvWordCount w0 - 1
      · simp [hlt]
      · simp only [hlt, ↓reduceIte]
        have hrem1 : (rest.drop (unpackSpirvWordCount w0 - 1)).length ≤ f1 := by
          rw [List.length_drop]; simp at h1; omega
        have hrem2 : (rest.drop (unpackSpirvWordCount w0 - 1)).length ≤ f2 := by
          rw [List.length_drop]; simp at h2; omega
        rw [parseRawInstStreamAux_fuel_mono hrem1 hrem2]

private theorem parseRawInstStream_cons {r : RawSpirvInst} {more : List UInt32}
    (hr : r.wf = true) :
    parseRawInstStream (encodeRawInst r ++ more) =
      (parseRawInstStream more).map (r :: ·) := by
  unfold RawSpirvInst.wf at hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  rcases hr with ⟨hop, hwc⟩
  unfold parseRawInstStream encodeRawInst
  simp only [List.cons_append, List.length_cons, List.length_append]
  dsimp only [parseRawInstStreamAux]
  obtain ⟨hUnpackWc, hUnpackOp⟩ := unpack_packSpirvWord0 hwc hop
  rw [hUnpackWc, hUnpackOp]
  have hNe0 : (r.operands.length + 1 == 0) = false := by simp
  have hNotLt : ¬ ((r.operands ++ more).length < r.operands.length + 1 - 1) := by simp
  have hSub : r.operands.length + 1 - 1 = r.operands.length := by omega
  simp only [hNe0, Bool.false_eq_true, ↓reduceIte, hNotLt, hSub,
    List.take_left, List.drop_left]
  rw [parseRawInstStreamAux_fuel_mono (f2 := more.length) (by omega) (Nat.le_refl _)]
  cases parseRawInstStreamAux more.length more <;> rfl

theorem parseRawInstStream_encodeRawInstList {rs : List RawSpirvInst}
    (hrs : rs.all RawSpirvInst.wf = true) :
    parseRawInstStream (encodeRawInstList rs) = .ok rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hrs
    unfold encodeRawInstList
    rw [parseRawInstStream_cons hrs.1, ih hrs.2]
    rfl

/-! ### Per-Section Instruction Encoders & Decoders -/

def encodeCapabilityRaw (c : SpirvCapability) : RawSpirvInst :=
  ⟨17, [c.toWord]⟩

def decodeCapabilityRaw (r : RawSpirvInst) : Except SpirvDecodeError SpirvCapability :=
  match r.opcode, r.operands with
  | 17, [w] =>
    match SpirvCapability.ofWord? w with
    | some c => .ok c
    | none => .error (.malformedSection "unknown capability")
  | _, _ => .error (.malformedSection "expected OpCapability")

theorem decodeCapabilityRaw_encode (c : SpirvCapability) :
    decodeCapabilityRaw (encodeCapabilityRaw c) = .ok c := by
  simp [encodeCapabilityRaw, decodeCapabilityRaw, SpirvCapability.ofWord?_toWord]

def encodeExecModeRaw (entryId : UInt32) : SpirvExecutionMode → RawSpirvInst
  | .localSize x y z => ⟨16, [entryId, 17, x, y, z]⟩
  | .subgroupSize sz => ⟨16, [entryId, 35, sz]⟩

def decodeExecModeRaw (entryId : UInt32) (r : RawSpirvInst) :
    Except SpirvDecodeError SpirvExecutionMode :=
  match r.opcode, r.operands with
  | 16, [ep, m, x, y, z] =>
    if ep == entryId && m == 17 then .ok (.localSize x y z)
    else .error (.malformedSection "bad LocalSize")
  | 16, [ep, m, sz] =>
    if ep == entryId && m == 35 then .ok (.subgroupSize sz)
    else .error (.malformedSection "bad SubgroupSize")
  | _, _ => .error (.malformedSection "expected OpExecutionMode")

theorem decodeExecModeRaw_encode (entryId : UInt32) (em : SpirvExecutionMode) :
    decodeExecModeRaw entryId (encodeExecModeRaw entryId em) = .ok em := by
  cases em <;> simp [encodeExecModeRaw, decodeExecModeRaw]

def encodeDecorateRaw (d : SpirvDecorateDecl) : RawSpirvInst :=
  match d.dec with
  | .block => ⟨71, [d.targetId, 2]⟩
  | .arrayStride s => ⟨71, [d.targetId, 6, s]⟩
  | .builtIn b => ⟨71, [d.targetId, 11, b.toWord]⟩
  | .binding slot => ⟨71, [d.targetId, 33, slot]⟩
  | .descriptorSet setIdx => ⟨71, [d.targetId, 34, setIdx]⟩

def decodeDecorateRaw (r : RawSpirvInst) : Except SpirvDecodeError SpirvDecorateDecl :=
  match r.opcode, r.operands with
  | 71, [tgt, dtag] =>
    if dtag == 2 then .ok ⟨tgt, .block⟩
    else .error (.malformedSection "bad flag decoration")
  | 71, [tgt, dtag, arg] =>
    if dtag == 6 then .ok ⟨tgt, .arrayStride arg⟩
    else if dtag == 11 then
      match SpirvBuiltIn.ofWord? arg with
      | some b => .ok ⟨tgt, .builtIn b⟩
      | none => .error (.malformedSection "bad BuiltIn")
    else if dtag == 33 then .ok ⟨tgt, .binding arg⟩
    else if dtag == 34 then .ok ⟨tgt, .descriptorSet arg⟩
    else .error (.malformedSection "unknown decoration")
  | _, _ => .error (.malformedSection "expected OpDecorate")

theorem decodeDecorateRaw_encode (d : SpirvDecorateDecl) :
    decodeDecorateRaw (encodeDecorateRaw d) = .ok d := by
  rcases d with ⟨tgt, dec⟩
  cases dec <;> simp [encodeDecorateRaw, decodeDecorateRaw, SpirvBuiltIn.ofWord?_toWord]

def encodeTypeRaw : SpirvTypeDecl → RawSpirvInst
  | .typeVoid res => ⟨19, [res]⟩
  | .typeBool res => ⟨20, [res]⟩
  | .typeInt res w signed => ⟨21, [res, w.toWord, if signed then 1 else 0]⟩
  | .typeArray res elem lenId => ⟨28, [res, elem, lenId]⟩
  | .typeRuntimeArray res elem => ⟨29, [res, elem]⟩
  | .typeStruct res fields => ⟨30, res :: fields⟩
  | .typePointer res sc pointee => ⟨32, [res, sc.toWord, pointee]⟩
  | .typeFunctionVoid res voidTy => ⟨33, [res, voidTy]⟩

def isTypeOpcode (op : Nat) : Bool :=
  op == 19 || op == 20 || op == 21 || op == 28 || op == 29 || op == 30 || op == 32 || op == 33

def decodeTypeRaw (r : RawSpirvInst) : Except SpirvDecodeError SpirvTypeDecl :=
  match r.opcode, r.operands with
  | 19, [res] => .ok (.typeVoid res)
  | 20, [res] => .ok (.typeBool res)
  | 21, [res, wWord, sWord] =>
    match SpirvIntWidth.ofWord? wWord with
    | some w =>
      if sWord == 0 then .ok (.typeInt res w false)
      else if sWord == 1 then .ok (.typeInt res w true)
      else .error (.malformedSection "bad OpTypeInt signedness")
    | none => .error (.malformedSection "bad OpTypeInt width")
  | 28, [res, elem, lenId] => .ok (.typeArray res elem lenId)
  | 29, [res, elem] => .ok (.typeRuntimeArray res elem)
  | 30, res :: fields => .ok (.typeStruct res fields)
  | 32, [res, scWord, pointee] =>
    match SpirvStorageClass.ofWord? scWord with
    | some sc => .ok (.typePointer res sc pointee)
    | none => .error (.malformedSection "bad OpTypePointer storage class")
  | 33, [res, voidTy] => .ok (.typeFunctionVoid res voidTy)
  | _, _ => .error (.malformedSection "malformed type declaration")

theorem decodeTypeRaw_encode (t : SpirvTypeDecl) :
    decodeTypeRaw (encodeTypeRaw t) = .ok t := by
  cases t with
  | typeInt res w signed =>
    cases signed <;> simp [encodeTypeRaw, decodeTypeRaw, SpirvIntWidth.ofWord?_toWord]
  | typePointer res sc pointee =>
    simp [encodeTypeRaw, decodeTypeRaw, SpirvStorageClass.ofWord?_toWord]
  | _ => simp [encodeTypeRaw, decodeTypeRaw]

def encodeGlobalRaw : SpirvGlobalDecl → RawSpirvInst
  | .constTrue ty res => ⟨41, [ty, res]⟩
  | .constFalse ty res => ⟨42, [ty, res]⟩
  | .const32 ty res val => ⟨43, [ty, res, val]⟩
  | .const64 ty res val => ⟨43, [ty, res, u64Lo32 val, u64Hi32 val]⟩
  | .variable ty res sc => ⟨59, [ty, res, sc.toWord]⟩

def isGlobalOpcode (op : Nat) : Bool :=
  op == 41 || op == 42 || op == 43 || op == 59

def decodeGlobalRaw (r : RawSpirvInst) : Except SpirvDecodeError SpirvGlobalDecl :=
  match r.opcode, r.operands with
  | 41, [ty, res] => .ok (.constTrue ty res)
  | 42, [ty, res] => .ok (.constFalse ty res)
  | 43, [ty, res, val] => .ok (.const32 ty res val)
  | 43, [ty, res, lo, hi] => .ok (.const64 ty res (u64OfLoHi32 lo hi))
  | 59, [ty, res, scWord] =>
    match SpirvStorageClass.ofWord? scWord with
    | some sc => .ok (.variable ty res sc)
    | none => .error (.malformedSection "bad OpVariable storage class")
  | _, _ => .error (.malformedSection "malformed global/constant declaration")

theorem decodeGlobalRaw_encode (g : SpirvGlobalDecl) :
    decodeGlobalRaw (encodeGlobalRaw g) = .ok g := by
  cases g with
  | const64 ty res val =>
    simp [encodeGlobalRaw, decodeGlobalRaw, u64OfLoHi32_lo_hi]
  | variable ty res sc =>
    simp [encodeGlobalRaw, decodeGlobalRaw, SpirvStorageClass.ofWord?_toWord]
  | _ => simp [encodeGlobalRaw, decodeGlobalRaw]

def encodeInstRaw : SpirvInst → RawSpirvInst
  | .opLoad ty res ptr => ⟨61, [ty, res, ptr]⟩
  | .opStore ptr val => ⟨62, [ptr, val]⟩
  | .opAccessChain ty res base indices => ⟨65, ty :: res :: base :: indices⟩
  | .opCompositeExtract ty res comp idx => ⟨81, [ty, res, comp, idx]⟩
  | .opUConvert ty res val => ⟨113, [ty, res, val]⟩
  | .opIAdd ty res a b => ⟨128, [ty, res, a, b]⟩
  | .opISub ty res a b => ⟨130, [ty, res, a, b]⟩
  | .opIMul ty res a b => ⟨132, [ty, res, a, b]⟩
  | .opUMulExtended ty res a b => ⟨151, [ty, res, a, b]⟩
  | .opSelect ty res cond t f => ⟨169, [ty, res, cond, t, f]⟩
  | .opIEqual ty res a b => ⟨170, [ty, res, a, b]⟩
  | .opUGreaterThanEqual ty res a b => ⟨173, [ty, res, a, b]⟩
  | .opULessThan ty res a b => ⟨177, [ty, res, a, b]⟩
  | .opShiftRightLogical ty res base sh => ⟨194, [ty, res, base, sh]⟩
  | .opShiftLeftLogical ty res base sh => ⟨196, [ty, res, base, sh]⟩
  | .opBitwiseXor ty res a b => ⟨197, [ty, res, a, b]⟩
  | .opBitwiseOr ty res a b => ⟨198, [ty, res, a, b]⟩
  | .opBitwiseAnd ty res a b => ⟨199, [ty, res, a, b]⟩
  | .opControlBarrier execS memS sem => ⟨224, [execS.toWord, memS.toWord, sem]⟩
  | .opLoopMerge mergeL contL ctrl => ⟨246, [mergeL, contL, ctrl]⟩
  | .opSelectionMerge mergeL ctrl => ⟨247, [mergeL, ctrl]⟩
  | .opLabel lbl => ⟨248, [lbl]⟩
  | .opBranch tgt => ⟨249, [tgt]⟩
  | .opBranchConditional cond tL fL => ⟨250, [cond, tL, fL]⟩

def isBodyOpcode (op : Nat) : Bool :=
  op == 61 || op == 62 || op == 65 || op == 81 || op == 113 ||
  op == 128 || op == 130 || op == 132 || op == 151 || op == 169 ||
  op == 170 || op == 173 || op == 177 || op == 194 || op == 196 ||
  op == 197 || op == 198 || op == 199 || op == 224 || op == 246 ||
  op == 247 || op == 248 || op == 249 || op == 250

def decodeInstRaw (r : RawSpirvInst) : Except SpirvDecodeError SpirvInst :=
  match r.opcode, r.operands with
  | 61, [ty, res, ptr] => .ok (.opLoad ty res ptr)
  | 62, [ptr, val] => .ok (.opStore ptr val)
  | 65, ty :: res :: base :: indices => .ok (.opAccessChain ty res base indices)
  | 81, [ty, res, comp, idx] => .ok (.opCompositeExtract ty res comp idx)
  | 113, [ty, res, val] => .ok (.opUConvert ty res val)
  | 128, [ty, res, a, b] => .ok (.opIAdd ty res a b)
  | 130, [ty, res, a, b] => .ok (.opISub ty res a b)
  | 132, [ty, res, a, b] => .ok (.opIMul ty res a b)
  | 151, [ty, res, a, b] => .ok (.opUMulExtended ty res a b)
  | 169, [ty, res, cond, t, f] => .ok (.opSelect ty res cond t f)
  | 170, [ty, res, a, b] => .ok (.opIEqual ty res a b)
  | 173, [ty, res, a, b] => .ok (.opUGreaterThanEqual ty res a b)
  | 177, [ty, res, a, b] => .ok (.opULessThan ty res a b)
  | 194, [ty, res, base, sh] => .ok (.opShiftRightLogical ty res base sh)
  | 196, [ty, res, base, sh] => .ok (.opShiftLeftLogical ty res base sh)
  | 197, [ty, res, a, b] => .ok (.opBitwiseXor ty res a b)
  | 198, [ty, res, a, b] => .ok (.opBitwiseOr ty res a b)
  | 199, [ty, res, a, b] => .ok (.opBitwiseAnd ty res a b)
  | 224, [es, ms, sem] =>
    match SpirvScope.ofWord? es, SpirvScope.ofWord? ms with
    | some eScope, some mScope => .ok (.opControlBarrier eScope mScope sem)
    | _, _ => .error (.malformedSection "bad OpControlBarrier scope")
  | 246, [mL, cL, ctrl] => .ok (.opLoopMerge mL cL ctrl)
  | 247, [mL, ctrl] => .ok (.opSelectionMerge mL ctrl)
  | 248, [lbl] => .ok (.opLabel lbl)
  | 249, [tgt] => .ok (.opBranch tgt)
  | 250, [cond, tL, fL] => .ok (.opBranchConditional cond tL fL)
  | _, _ => .error (.malformedSection "unknown body instruction")

theorem decodeInstRaw_encode (i : SpirvInst) :
    decodeInstRaw (encodeInstRaw i) = .ok i := by
  cases i with
  | opControlBarrier es ms sem =>
    simp [encodeInstRaw, decodeInstRaw, SpirvScope.ofWord?_toWord]
  | _ => simp [encodeInstRaw, decodeInstRaw]

/-- Lower a `SpirvModule` into its sequence of `RawSpirvInst`s following the 5-word header. -/
def moduleToRawInsts (m : SpirvModule) : List RawSpirvInst :=
  (m.capabilities.map encodeCapabilityRaw) ++
  [⟨14, [m.addrModel.toWord, m.memModel.toWord]⟩,
   ⟨15, [spirvExecModelGLCompute, m.entryFuncId, spirvMainWord0, spirvMainWord1] ++ m.interfaceIds⟩] ++
  (m.execModes.map (encodeExecModeRaw m.entryFuncId)) ++
  (m.decorations.map encodeDecorateRaw) ++
  (m.types.map encodeTypeRaw) ++
  (m.globals.map encodeGlobalRaw) ++
  [⟨54, [m.voidTypeId, m.entryFuncId, 0, m.funcTypeId]⟩,
   ⟨248, [m.entryLabelId]⟩] ++
  (m.body.map encodeInstRaw) ++
  [⟨253, []⟩,
   ⟨56, []⟩]

/-- Encode a `SpirvModule` into its exact binary `Array UInt32` SPIR-V 1.6 word stream. -/
def encodeSpirvModuleWords (m : SpirvModule) : List UInt32 :=
  [spirvMagic, spirvVersion16, m.generator, m.idBound, 0] ++
  encodeRawInstList (moduleToRawInsts m)

def encodeSpirvModule (m : SpirvModule) : Array UInt32 :=
  (encodeSpirvModuleWords m).toArray

private def splitByOp (pred : Nat → Bool) : List RawSpirvInst → List RawSpirvInst × List RawSpirvInst
  | [] => ([], [])
  | r :: rs =>
    if pred r.opcode then
      let (ys, zs) := splitByOp pred rs
      (r :: ys, zs)
    else
      ([], r :: rs)

private theorem splitByOp_append {pred : Nat → Bool} {xs ys : List RawSpirvInst}
    (hxs : ∀ x ∈ xs, pred x.opcode = true)
    (hys : match ys with | [] => True | y :: _ => pred y.opcode = false) :
    splitByOp pred (xs ++ ys) = (xs, ys) := by
  induction xs with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      simp only [List.nil_append, splitByOp]
      simp [hys]
  | cons x xs ih =>
    have hx : pred x.opcode = true := hxs x (.head _)
    have hrest : ∀ z ∈ xs, pred z.opcode = true := fun z hz => hxs z (.tail _ hz)
    simp only [List.cons_append, splitByOp, hx, ↓reduceIte, ih hrest hys]

private def mapExcept {α β : Type} (f : α → Except SpirvDecodeError β) :
    List α → Except SpirvDecodeError (List β)
  | [] => .ok []
  | x :: xs =>
    match f x, mapExcept f xs with
    | .ok y, .ok ys => .ok (y :: ys)
    | .error e, _ => .error e
    | .ok _, .error e => .error e

private theorem mapExcept_map_ok {α β : Type} (enc : β → α)
    (dec : α → Except SpirvDecodeError β) (hRound : ∀ b, dec (enc b) = .ok b) :
    ∀ bs : List β, mapExcept dec (bs.map enc) = .ok bs
  | [] => rfl
  | b :: bs => by
    simp [mapExcept, hRound b, mapExcept_map_ok enc dec hRound bs]

/-- Decode a `SpirvModule` from its binary `Array UInt32` SPIR-V 1.6 word stream. -/
def decodeSpirvModuleWords (words : List UInt32) : Except SpirvDecodeError SpirvModule :=
  match words with
  | magic :: ver :: gen :: bound :: schema :: instWords =>
    if magic != spirvMagic then
      .error (.badMagic magic)
    else if ver != spirvVersion16 then
      .error (.badVersion ver)
    else if schema != 0 then
      .error (.badSchema schema)
    else if bound.toNat == 0 then
      .error .zeroIdBound
    else
      match parseRawInstStream instWords with
      | .error e => .error e
      | .ok raws =>
        let (capRaws, r1) := splitByOp (· == 17) raws
        match r1 with
        | ⟨14, [addrW, memW]⟩ :: ⟨15, epModel :: entryFuncId :: m0 :: m1 :: ifaceIds⟩ :: r2 =>
          if epModel != spirvExecModelGLCompute || m0 != spirvMainWord0 || m1 != spirvMainWord1 then
            .error (.malformedSection "bad OpEntryPoint header")
          else
            match SpirvAddressingModel.ofWord? addrW, SpirvMemoryModelKind.ofWord? memW with
            | some addrM, some memM =>
              let (emRaws, r3) := splitByOp (· == 16) r2
              let (decRaws, r4) := splitByOp (· == 71) r3
              let (tyRaws, r5) := splitByOp isTypeOpcode r4
              let (globRaws, r6) := splitByOp isGlobalOpcode r5
              match r6 with
              | ⟨54, [voidTyId, fnId, fnCtrl, fnTyId]⟩ :: ⟨248, [entryLbl]⟩ :: r7 =>
                if fnId != entryFuncId || fnCtrl != 0 then
                  .error (.malformedSection "bad OpFunction header")
                else
                  let (bodyRaws, r8) := splitByOp isBodyOpcode r7
                  match r8 with
                  | [⟨253, []⟩, ⟨56, []⟩] =>
                    match mapExcept decodeCapabilityRaw capRaws,
                          mapExcept (decodeExecModeRaw entryFuncId) emRaws,
                          mapExcept decodeDecorateRaw decRaws,
                          mapExcept decodeTypeRaw tyRaws,
                          mapExcept decodeGlobalRaw globRaws,
                          mapExcept decodeInstRaw bodyRaws with
                    | .ok caps, .ok ems, .ok decs, .ok tys, .ok globs, .ok body =>
                      .ok {
                        generator := gen
                        idBound := bound
                        capabilities := caps
                        addrModel := addrM
                        memModel := memM
                        entryFuncId := entryFuncId
                        interfaceIds := ifaceIds
                        execModes := ems
                        decorations := decs
                        types := tys
                        globals := globs
                        voidTypeId := voidTyId
                        funcTypeId := fnTyId
                        entryLabelId := entryLbl
                        body := body
                      }
                    | .error e, _, _, _, _, _ => .error e
                    | _, .error e, _, _, _, _ => .error e
                    | _, _, .error e, _, _, _ => .error e
                    | _, _, _, .error e, _, _ => .error e
                    | _, _, _, _, .error e, _ => .error e
                    | _, _, _, _, _, .error e => .error e
                  | _ => .error (.malformedSection "expected OpReturn; OpFunctionEnd")
              | _ => .error (.malformedSection "expected OpFunction; OpLabel")
            | _, _ => .error (.malformedSection "bad OpMemoryModel operands")
        | _ => .error (.malformedSection "expected OpMemoryModel; OpEntryPoint")
  | _ => .error .truncatedHeader

def decodeSpirvModule (words : Array UInt32) : Except SpirvDecodeError SpirvModule :=
  decodeSpirvModuleWords words.toList

private theorem moduleToRawInsts_wf {m : SpirvModule} (hm : WellFormedSpirvModule m = true) :
    (moduleToRawInsts m).all RawSpirvInst.wf = true := by
  unfold WellFormedSpirvModule at hm
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hm
  rcases hm with ⟨⟨⟨_, hIface⟩, hTys⟩, hBody⟩
  rw [List.all_eq_true]
  intro r hr
  unfold moduleToRawInsts at hr
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (((((((⟨c, _, rfl⟩ | (rfl | rfl)) | ⟨em, _, rfl⟩) | ⟨d, _, rfl⟩) |
      ⟨t, ht, rfl⟩) | ⟨g, _, rfl⟩) | (rfl | rfl)) | ⟨i, hi, rfl⟩) | (rfl | rfl)
  · decide
  · decide
  · simp [RawSpirvInst.wf]; omega
  · cases em <;> decide
  · rcases d with ⟨_, dec⟩; cases dec <;> decide
  · specialize hTys t ht
    cases t <;> simp [SpirvTypeDecl.wf, RawSpirvInst.wf, encodeTypeRaw] at hTys ⊢ <;> omega
  · cases g <;> decide
  · decide
  · decide
  · specialize hBody i hi
    cases i <;> simp [SpirvInst.wf, RawSpirvInst.wf, encodeInstRaw] at hBody ⊢ <;> omega
  · decide
  · decide

private theorem head_not_op_16 (decs : List SpirvDecorateDecl) (tys : List SpirvTypeDecl)
    (globs : List SpirvGlobalDecl) (tail : List RawSpirvInst)
    (fnRaw : RawSpirvInst) (hfn : fnRaw.opcode = 54) :
    match (decs.map encodeDecorateRaw) ++ (tys.map encodeTypeRaw) ++
          (globs.map encodeGlobalRaw) ++ (fnRaw :: tail) with
    | [] => True
    | y :: _ => (y.opcode == 16) = false := by
  cases decs with
  | cons d _ => rcases d with ⟨_, dec⟩; cases dec <;> rfl
  | nil =>
    cases tys with
    | cons t _ => cases t <;> rfl
    | nil =>
      cases globs with
      | cons g _ => cases g <;> rfl
      | nil => simp [hfn]

private theorem head_not_op_71 (tys : List SpirvTypeDecl)
    (globs : List SpirvGlobalDecl) (tail : List RawSpirvInst)
    (fnRaw : RawSpirvInst) (hfn : fnRaw.opcode = 54) :
    match (tys.map encodeTypeRaw) ++ (globs.map encodeGlobalRaw) ++ (fnRaw :: tail) with
    | [] => True
    | y :: _ => (y.opcode == 71) = false := by
  cases tys with
  | cons t _ => cases t <;> rfl
  | nil =>
    cases globs with
    | cons g _ => cases g <;> rfl
    | nil => simp [hfn]

private theorem head_not_typeOp (globs : List SpirvGlobalDecl) (tail : List RawSpirvInst)
    (fnRaw : RawSpirvInst) (hfn : fnRaw.opcode = 54) :
    match (globs.map encodeGlobalRaw) ++ (fnRaw :: tail) with
    | [] => True
    | y :: _ => isTypeOpcode y.opcode = false := by
  cases globs with
  | cons g _ => cases g <;> rfl
  | nil => simp [hfn, isTypeOpcode]

/-- **Binary `SPIR-V 1.6` Encoder/Decoder Roundtrip Theorem (`decodeSpirvModule_encodeSpirvModule`)**:
    Every well-formed `SpirvModule` encodes to a valid `Array UInt32` binary word stream and decodes
    back to the exact AST `m`. -/
theorem decodeSpirvModule_encodeSpirvModule {m : SpirvModule}
    (hm : WellFormedSpirvModule m = true) :
    decodeSpirvModule (encodeSpirvModule m) = .ok m := by
  have hRawWf := moduleToRawInsts_wf hm
  unfold WellFormedSpirvModule at hm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
  have hBoundNe0 : (m.idBound.toNat == 0) = false := by
    have := hm.1.1.1; simp; omega
  unfold decodeSpirvModule encodeSpirvModule encodeSpirvModuleWords decodeSpirvModuleWords
  simp only [Array.toList_toArray, List.cons_append, bne_self_eq_false, Bool.false_eq_true,
    ↓reduceIte, hBoundNe0]
  rw [parseRawInstStream_encodeRawInstList hRawWf]
  dsimp only
  unfold moduleToRawInsts
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hSplitCap : splitByOp (· == 17)
      ((m.capabilities.map encodeCapabilityRaw) ++
       (⟨14, [m.addrModel.toWord, m.memModel.toWord]⟩ ::
        ⟨15, spirvExecModelGLCompute :: m.entryFuncId :: spirvMainWord0 :: spirvMainWord1 :: m.interfaceIds⟩ ::
        ((m.execModes.map (encodeExecModeRaw m.entryFuncId)) ++
         ((m.decorations.map encodeDecorateRaw) ++
          ((m.types.map encodeTypeRaw) ++
           ((m.globals.map encodeGlobalRaw) ++
            (⟨54, [m.voidTypeId, m.entryFuncId, 0, m.funcTypeId]⟩ ::
             ⟨248, [m.entryLabelId]⟩ ::
             ((m.body.map encodeInstRaw) ++ [⟨253, []⟩, ⟨56, []⟩])))))))) =
      (m.capabilities.map encodeCapabilityRaw,
       ⟨14, [m.addrModel.toWord, m.memModel.toWord]⟩ ::
        ⟨15, spirvExecModelGLCompute :: m.entryFuncId :: spirvMainWord0 :: spirvMainWord1 :: m.interfaceIds⟩ ::
        ((m.execModes.map (encodeExecModeRaw m.entryFuncId)) ++
         ((m.decorations.map encodeDecorateRaw) ++
          ((m.types.map encodeTypeRaw) ++
           ((m.globals.map encodeGlobalRaw) ++
            (⟨54, [m.voidTypeId, m.entryFuncId, 0, m.funcTypeId]⟩ ::
             ⟨248, [m.entryLabelId]⟩ ::
             ((m.body.map encodeInstRaw) ++ [⟨253, []⟩, ⟨56, []⟩]))))))) := by
    apply splitByOp_append
    · intro x hx; obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx; rfl
    · rfl
  rw [hSplitCap]
  simp only [bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte,
    SpirvAddressingModel.ofWord?_toWord, SpirvMemoryModelKind.ofWord?_toWord]
  have hSplitEm := splitByOp_append (pred := (· == 16))
    (xs := m.execModes.map (encodeExecModeRaw m.entryFuncId))
    (ys := (m.decorations.map encodeDecorateRaw) ++ (m.types.map encodeTypeRaw) ++
           (m.globals.map encodeGlobalRaw) ++
           (⟨54, [m.voidTypeId, m.entryFuncId, 0, m.funcTypeId]⟩ ::
            ⟨248, [m.entryLabelId]⟩ :: ((m.body.map encodeInstRaw) ++ [⟨253, []⟩, ⟨56, []⟩])))
    (by intro x hx; obtain ⟨em, _, rfl⟩ := List.mem_map.mp hx; cases em <;> rfl)
    (head_not_op_16 m.decorations m.types m.globals _ _ rfl)
  simp only [List.append_assoc] at hSplitEm
  rw [hSplitEm]
  dsimp only
  have hSplitDec := splitByOp_append (pred := (· == 71))
    (xs := m.decorations.map encodeDecorateRaw)
    (ys := (m.types.map encodeTypeRaw) ++ (m.globals.map encodeGlobalRaw) ++
           (⟨54, [m.voidTypeId, m.entryFuncId, 0, m.funcTypeId]⟩ ::
            ⟨248, [m.entryLabelId]⟩ :: ((m.body.map encodeInstRaw) ++ [⟨253, []⟩, ⟨56, []⟩])))
    (by intro x hx; obtain ⟨d, _, rfl⟩ := List.mem_map.mp hx; rcases d with ⟨_, dec⟩; cases dec <;> rfl)
    (head_not_op_71 m.types m.globals _ _ rfl)
  simp only [List.append_assoc] at hSplitDec
  rw [hSplitDec]
  dsimp only
  have hSplitTy := splitByOp_append (pred := isTypeOpcode)
    (xs := m.types.map encodeTypeRaw)
    (ys := (m.globals.map encodeGlobalRaw) ++
           (⟨54, [m.voidTypeId, m.entryFuncId, 0, m.funcTypeId]⟩ ::
            ⟨248, [m.entryLabelId]⟩ :: ((m.body.map encodeInstRaw) ++ [⟨253, []⟩, ⟨56, []⟩])))
    (by intro x hx; obtain ⟨t, _, rfl⟩ := List.mem_map.mp hx; cases t <;> rfl)
    (head_not_typeOp m.globals _ _ rfl)
  simp only [List.append_assoc] at hSplitTy
  rw [hSplitTy]
  dsimp only
  have hSplitGlob := splitByOp_append (pred := isGlobalOpcode)
    (xs := m.globals.map encodeGlobalRaw)
    (ys := ⟨54, [m.voidTypeId, m.entryFuncId, 0, m.funcTypeId]⟩ ::
           ⟨248, [m.entryLabelId]⟩ :: ((m.body.map encodeInstRaw) ++ [⟨253, []⟩, ⟨56, []⟩]))
    (by intro x hx; obtain ⟨g, _, rfl⟩ := List.mem_map.mp hx; cases g <;> rfl)
    rfl
  rw [hSplitGlob]
  simp only [bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte]
  have hSplitBody := splitByOp_append (pred := isBodyOpcode)
    (xs := m.body.map encodeInstRaw)
    (ys := [⟨253, []⟩, ⟨56, []⟩])
    (by intro x hx; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx; cases i <;> rfl)
    rfl
  rw [hSplitBody]
  dsimp only
  rw [mapExcept_map_ok _ _ decodeCapabilityRaw_encode,
      mapExcept_map_ok _ _ (decodeExecModeRaw_encode m.entryFuncId),
      mapExcept_map_ok _ _ decodeDecorateRaw_encode,
      mapExcept_map_ok _ _ decodeTypeRaw_encode,
      mapExcept_map_ok _ _ decodeGlobalRaw_encode,
      mapExcept_map_ok _ _ decodeInstRaw_encode]
  cases m; rfl

/-- Injectivity of `encodeSpirvModule` on well-formed SPIR-V 1.6 compute modules. -/
theorem encodeSpirvModule_injective {m₁ m₂ : SpirvModule}
    (h₁ : WellFormedSpirvModule m₁ = true) (h₂ : WellFormedSpirvModule m₂ = true)
    (hEq : encodeSpirvModule m₁ = encodeSpirvModule m₂) : m₁ = m₂ := by
  have d₁ := decodeSpirvModule_encodeSpirvModule h₁
  have d₂ := decodeSpirvModule_encodeSpirvModule h₂
  rw [hEq] at d₁
  have hOk : Except.ok m₁ = (Except.ok m₂ : Except SpirvDecodeError SpirvModule) :=
    d₁.symm.trans d₂
  injection hOk

/-- `#tooth` Corrupting the `0x07230203` SPIR-V magic header word is rejected by `decodeSpirvModule`. -/
theorem tooth_corrupted_spirv_magic_rejected (ver gen bound : UInt32) (rest : List UInt32) :
    decodeSpirvModule (#[0xDEADBEEF, ver, gen, bound, 0] ++ rest.toArray) =
      .error (.badMagic 0xDEADBEEF) := by
  unfold decodeSpirvModule
  simp [decodeSpirvModuleWords, spirvMagic]

/-- `#tooth` Downgrading or corrupting the `0x00010600` SPIR-V 1.6 version header is rejected. -/
theorem tooth_corrupted_spirv_version_rejected (gen bound : UInt32) (rest : List UInt32) :
    decodeSpirvModule (#[spirvMagic, 0x00010000, gen, bound, 0] ++ rest.toArray) =
      .error (.badVersion 0x00010000) := by
  unfold decodeSpirvModule
  simp [decodeSpirvModuleWords, spirvMagic, spirvVersion16]

/-! ## §2. Genuine Multi-Wave Wave32 Workgroup Operational Semantics (`64 KiB` Shared LDS) -/

/-- Native RDNA2 Wave32 subgroup width (`32` SIMD lanes per wave). -/
def wave32Lanes : Nat := 32

/-- Full RDNA2 WGP `Workgroup` LDS capacity: `65,536` bytes (`64 KiB` = `16,384` `UInt32` dwords). -/
def ldsCapacityBytes : Nat := 65536
def ldsCapacityDwords : Nat := 16384

theorem ldsCapacityBytes_eq_four_mul_dwords : ldsCapacityBytes = 4 * ldsCapacityDwords := rfl

/-- Multi-wave workgroup geometry (`numWaves * 32` threads, e.g. `numWaves = 8` -> `256` threads). -/
structure WorkgroupConfig where
  workgroupId : Nat
  numWaves : Nat
  wavesPos : 0 < numWaves

def WorkgroupConfig.totalThreads (cfg : WorkgroupConfig) : Nat :=
  cfg.numWaves * wave32Lanes

def WorkgroupConfig.localTid (_cfg : WorkgroupConfig) (wave lane : Nat) : Nat :=
  wave * wave32Lanes + lane

def WorkgroupConfig.globalTid (cfg : WorkgroupConfig) (wave lane : Nat) : Nat :=
  cfg.workgroupId * cfg.totalThreads + cfg.localTid wave lane

/-- Typed runtime SSA values per SIMT lane. -/
inductive SpirvVal where
  | vUndef
  | vBool (b : Bool)
  | vU32 (v : UInt32)
  | vU64 (v : UInt64)
  | vPair32 (lo hi : UInt32)
  | vPair64 (lo hi : UInt64)
  | vPtr (sc : SpirvStorageClass) (binding : Nat) (elemIdx : Nat) (width : SpirvIntWidth)
  deriving DecidableEq, Repr

/-- Shared memory state across ALL waves of a workgroup:
    - `lds` : persistent `64 KiB` (`16,384`-dword) `Workgroup` shared memory (never wiped between waves!)
    - `ssbo` : global `StorageBuffer` descriptor bindings (`binding -> dwordOffset -> UInt32`)
    - `pushConsts` : immutable public `PushConstant` dwords (`dwordOffset -> UInt32`). -/
structure GpuMemState where
  lds : Nat → UInt32
  ssbo : Nat → Nat → UInt32
  pushConsts : Nat → UInt32

def writeFn {α : Type} (m : Nat → α) (idx : Nat) (val : α) : Nat → α :=
  fun k => if k = idx then val else m k

def writeSsboDword (ssbo : Nat → Nat → UInt32) (binding addr : Nat) (val : UInt32) :
    Nat → Nat → UInt32 :=
  fun b k => if b = binding ∧ k = addr then val else ssbo b k

theorem writeFn_same {α : Type} (m : Nat → α) (idx : Nat) (val : α) :
    writeFn m idx val idx = val := by
  simp [writeFn]

theorem writeFn_other {α : Type} (m : Nat → α) {idx k : Nat} (val : α) (hne : k ≠ idx) :
    writeFn m idx val k = m k := by
  simp [writeFn, hne]

theorem writeFn_comm {α : Type} (m : Nat → α) {i₁ i₂ : Nat} (v₁ v₂ : α) (hne : i₁ ≠ i₂) :
    writeFn (writeFn m i₁ v₁) i₂ v₂ = writeFn (writeFn m i₂ v₂) i₁ v₁ := by
  funext k
  unfold writeFn
  by_cases h2 : k = i₂
  · subst h2; simp [hne.symm]
  · by_cases h1 : k = i₁
    · subst h1; simp [h2]
    · simp [h1, h2]

theorem writeSsboDword_comm (ssbo : Nat → Nat → UInt32) {b₁ a₁ b₂ a₂ : Nat} (v₁ v₂ : UInt32)
    (hne : (b₁, a₁) ≠ (b₂, a₂)) :
    writeSsboDword (writeSsboDword ssbo b₁ a₁ v₁) b₂ a₂ v₂ =
      writeSsboDword (writeSsboDword ssbo b₂ a₂ v₂) b₁ a₁ v₁ := by
  funext b k
  unfold writeSsboDword
  by_cases h2 : b = b₂ ∧ k = a₂
  · rcases h2 with ⟨rfl, rfl⟩
    have h1 : ¬ (b₂ = b₁ ∧ a₂ = a₁) := fun ⟨hb, ha⟩ => hne (Prod.ext hb.symm ha.symm)
    simp [h1]
  · by_cases h1 : b = b₁ ∧ k = a₁
    · simp [h1, h2]
    · simp [h1, h2]

def readU64Dwords (f : Nat → UInt32) (elemIdx : Nat) : UInt64 :=
  u64OfLoHi32 (f (2 * elemIdx)) (f (2 * elemIdx + 1))

def writeU64Dwords (f : Nat → UInt32) (elemIdx : Nat) (v : UInt64) : Nat → UInt32 :=
  writeFn (writeFn f (2 * elemIdx) (u64Lo32 v)) (2 * elemIdx + 1) (u64Hi32 v)

theorem readU64Dwords_writeU64Dwords_same (f : Nat → UInt32) (idx : Nat) (v : UInt64) :
    readU64Dwords (writeU64Dwords f idx v) idx = v := by
  unfold readU64Dwords writeU64Dwords
  rw [writeFn_other _ _ (by omega), writeFn_same, writeFn_same, u64OfLoHi32_lo_hi]

theorem readU64Dwords_writeU64Dwords_other (f : Nat → UInt32) {idx k : Nat} (v : UInt64)
    (hne : k ≠ idx) :
    readU64Dwords (writeU64Dwords f idx v) k = readU64Dwords f k := by
  unfold readU64Dwords writeU64Dwords
  rw [writeFn_other _ _ (by omega), writeFn_other _ _ (by omega),
      writeFn_other _ _ (by omega), writeFn_other _ _ (by omega)]

def writeSsboU64 (ssbo : Nat → Nat → UInt32) (binding elemIdx : Nat) (v : UInt64) :
    Nat → Nat → UInt32 :=
  writeSsboDword (writeSsboDword ssbo binding (2 * elemIdx) (u64Lo32 v))
    binding (2 * elemIdx + 1) (u64Hi32 v)

theorem readSsboU64_writeSsboU64_same (ssbo : Nat → Nat → UInt32) (b idx : Nat) (v : UInt64) :
    readU64Dwords (writeSsboU64 ssbo b idx v b) idx = v := by
  unfold readU64Dwords writeSsboU64 writeSsboDword
  have h1 : ¬ (b = b ∧ 2 * idx = 2 * idx + 1) := by omega
  simp [h1, u64OfLoHi32_lo_hi]

theorem readSsboU64_writeSsboU64_other_idx (ssbo : Nat → Nat → UInt32) (b : Nat) {idx k : Nat}
    (v : UInt64) (hne : k ≠ idx) :
    readU64Dwords (writeSsboU64 ssbo b idx v b) k = readU64Dwords (ssbo b) k := by
  unfold readU64Dwords writeSsboU64 writeSsboDword
  have h1 : ¬ (2 * k = 2 * idx + 1) := by omega
  have h2 : ¬ (2 * k = 2 * idx) := by omega
  have h3 : ¬ (2 * k + 1 = 2 * idx + 1) := by omega
  have h4 : ¬ (2 * k + 1 = 2 * idx) := by omega
  simp [h1, h2, h3, h4]

/-- Resolved static metadata of a `SpirvModule` for operational execution. -/
structure SpirvModuleEnv where
  intWidths : Nat → Option SpirvIntWidth
  ptrInfo : Nat → Option (SpirvStorageClass × Nat × SpirvIntWidth)
  initConst : Nat → SpirvVal
  builtIns : Nat → Option SpirvBuiltIn

/-- Initialize a lane's SSA register file with module constants and built-in invocation IDs. -/
def initLaneRegs (env : SpirvModuleEnv) (cfg : WorkgroupConfig) (wave lane : Nat) :
    Nat → SpirvVal :=
  fun ssaId =>
    match env.builtIns ssaId with
    | some .workgroupId => .vU32 (UInt32.ofNat cfg.workgroupId)
    | some .localInvocationId => .vU32 (UInt32.ofNat (cfg.localTid wave lane))
    | some .globalInvocationId => .vU32 (UInt32.ofNat (cfg.globalTid wave lane))
    | some .localInvocationIndex => .vU32 (UInt32.ofNat (cfg.localTid wave lane))
    | some .subgroupSize => .vU32 32
    | some .subgroupId => .vU32 (UInt32.ofNat wave)
    | some .subgroupLocalInvocationId => .vU32 (UInt32.ofNat lane)
    | none =>
      match env.ptrInfo ssaId with
      | some (sc, binding, w) => .vPtr sc binding 0 w
      | none => env.initConst ssaId

/-- Runtime errors during multi-wave `SPIR-V` execution. -/
