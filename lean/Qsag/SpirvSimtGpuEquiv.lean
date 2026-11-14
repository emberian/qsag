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
    have h16 : (16 : UInt32).toNat % 32 = 16 := rfl
    rw [h16]
    simp only [UInt32.toNat_ofNat', show (2 : Nat) ^ 32 = 4294967296 from rfl,
      Nat.mod_eq_of_lt hwc32, Nat.mod_eq_of_lt hsh32]
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
    have h16 : (16 : UInt32).toNat % 32 = 16 := rfl
    rw [h16]
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
  | f1, f2, [], _, _ => by
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
  rcases r with ⟨op, ops⟩
  unfold RawSpirvInst.wf at hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  rcases hr with ⟨hop, hwc⟩
  unfold parseRawInstStream encodeRawInst
  simp only [List.cons_append, List.length_cons, List.length_append]
  dsimp only [parseRawInstStreamAux]
  obtain ⟨hUnpackWc, hUnpackOp⟩ := unpack_packSpirvWord0 hwc hop
  rw [hUnpackWc, hUnpackOp]
  have hNe0 : (ops.length + 1 == 0) = false := by simp
  have hSub : ops.length + 1 - 1 = ops.length := by omega
  have hNotLt : ¬ ((ops ++ more).length < ops.length) := by simp
  simp only [hNe0, Bool.false_eq_true, ↓reduceIte, hSub, hNotLt,
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
  | «variable» ty res sc =>
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
    simp only [List.cons_append, splitByOp, hx, ↓reduceIte, ih hrest]

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
  · cases c <;> rfl
  · rfl
  · simp [RawSpirvInst.wf]; omega
  · cases em <;> rfl
  · rcases d with ⟨_, dec⟩; cases dec <;> rfl
  · specialize hTys t ht
    cases t <;> simp [SpirvTypeDecl.wf, RawSpirvInst.wf, encodeTypeRaw, List.length_cons] at hTys ⊢ <;> omega
  · cases g <;> rfl
  · rfl
  · rfl
  · specialize hBody i hi
    cases i <;> simp [SpirvInst.wf, RawSpirvInst.wf, encodeInstRaw, List.length_cons] at hBody ⊢ <;> omega
  · rfl
  · rfl

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
  change decodeSpirvModuleWords (encodeSpirvModuleWords m) = .ok m
  unfold encodeSpirvModuleWords decodeSpirvModuleWords
  simp only [List.cons_append, List.nil_append, bne_self_eq_false, Bool.false_eq_true,
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

theorem ldsCapacityBytes_eq_four_mul_dwords : ldsCapacityBytes = 4 * ldsCapacityDwords := by rfl

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
  · by_cases h1 : b = b₁ ∧ k = a₁
    · exact False.elim (hne (Prod.ext (h1.1.symm.trans h2.1) (h1.2.symm.trans h2.2)))
    · simp [h1, h2]
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
  simp [u64OfLoHi32_lo_hi]

theorem readSsboU64_writeSsboU64_other_idx (ssbo : Nat → Nat → UInt32) (b : Nat) {idx k : Nat}
    (v : UInt64) (hne : k ≠ idx) :
    readU64Dwords (writeSsboU64 ssbo b idx v b) k = readU64Dwords (ssbo b) k := by
  unfold readU64Dwords writeSsboU64 writeSsboDword
  have h1 : ¬ (2 * k = 2 * idx + 1) := by omega
  have h2 : ¬ (2 * k = 2 * idx) := by omega
  have h4 : ¬ (2 * k + 1 = 2 * idx) := by omega
  simp [h1, h2, h4]

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
inductive SimtExecError where
  | typeMismatch
  | ldsOutOfBounds (dwordAddr : Nat)
  | unexpectedBarrierInEpoch
  | barrierDivergence
  deriving DecidableEq, Repr

/-- Pure per-lane ALU + `OpAccessChain` + `OpLoad` evaluation (excluding `OpStore` / `OpControlBarrier`). -/
def evalLanePureInst (env : SpirvModuleEnv) (mem : GpuMemState) (regs : Nat → SpirvVal)
    (inst : SpirvInst) : Except SimtExecError (Nat × SpirvVal) :=
  match inst with
  | .opAccessChain tyId resId baseId [idxId] =>
    match regs baseId.toNat, regs idxId.toNat with
    | .vPtr sc binding baseOff elemW, .vU32 idx =>
      let w := (env.ptrInfo tyId.toNat).map (·.2.2) |>.getD elemW
      .ok (resId.toNat, .vPtr sc binding (baseOff + idx.toNat) w)
    | .vPtr sc binding baseOff elemW, .vU64 idx =>
      let w := (env.ptrInfo tyId.toNat).map (·.2.2) |>.getD elemW
      .ok (resId.toNat, .vPtr sc binding (baseOff + idx.toNat) w)
    | _, _ => .error .typeMismatch
  | .opLoad _ resId ptrId =>
    match regs ptrId.toNat with
    | .vPtr .workgroup _ elemIdx .w32 =>
      if elemIdx < ldsCapacityDwords then
        .ok (resId.toNat, .vU32 (mem.lds elemIdx))
      else
        .error (.ldsOutOfBounds elemIdx)
    | .vPtr .workgroup _ elemIdx .w64 =>
      if 2 * elemIdx + 1 < ldsCapacityDwords then
        .ok (resId.toNat, .vU64 (readU64Dwords mem.lds elemIdx))
      else
        .error (.ldsOutOfBounds (2 * elemIdx + 1))
    | .vPtr .storageBuffer binding elemIdx .w32 =>
      .ok (resId.toNat, .vU32 (mem.ssbo binding elemIdx))
    | .vPtr .storageBuffer binding elemIdx .w64 =>
      .ok (resId.toNat, .vU64 (readU64Dwords (mem.ssbo binding) elemIdx))
    | .vPtr .pushConstant _ elemIdx .w32 =>
      .ok (resId.toNat, .vU32 (mem.pushConsts elemIdx))
    | .vPtr .pushConstant _ elemIdx .w64 =>
      .ok (resId.toNat, .vU64 (readU64Dwords mem.pushConsts elemIdx))
    | _ => .error .typeMismatch
  | .opCompositeExtract _ resId compId fieldIdx =>
    match regs compId.toNat, fieldIdx.toNat with
    | .vPair32 lo _, 0 => .ok (resId.toNat, .vU32 lo)
    | .vPair32 _ hi, 1 => .ok (resId.toNat, .vU32 hi)
    | .vPair64 lo _, 0 => .ok (resId.toNat, .vU64 lo)
    | .vPair64 _ hi, 1 => .ok (resId.toNat, .vU64 hi)
    | _, _ => .error .typeMismatch
  | .opUConvert tyId resId valId =>
    match env.intWidths tyId.toNat, regs valId.toNat with
    | some .w64, .vU32 v => .ok (resId.toNat, .vU64 (UInt64.ofNat v.toNat))
    | some .w32, .vU64 v => .ok (resId.toNat, .vU32 (UInt32.ofNat (v.toNat % 4294967296)))
    | _, _ => .error .typeMismatch
  | .opIAdd _ resId aId bId =>
    match regs aId.toNat, regs bId.toNat with
    | .vU32 a, .vU32 b => .ok (resId.toNat, .vU32 (a + b))
    | .vU64 a, .vU64 b => .ok (resId.toNat, .vU64 (a + b))
    | _, _ => .error .typeMismatch
  | .opISub _ resId aId bId =>
    match regs aId.toNat, regs bId.toNat with
    | .vU32 a, .vU32 b => .ok (resId.toNat, .vU32 (a - b))
    | .vU64 a, .vU64 b => .ok (resId.toNat, .vU64 (a - b))
    | _, _ => .error .typeMismatch
  | .opIMul _ resId aId bId =>
    match regs aId.toNat, regs bId.toNat with
    | .vU32 a, .vU32 b => .ok (resId.toNat, .vU32 (a * b))
    | .vU64 a, .vU64 b => .ok (resId.toNat, .vU64 (a * b))
    | _, _ => .error .typeMismatch
  | .opUMulExtended _ resId aId bId =>
    match regs aId.toNat, regs bId.toNat with
    | .vU32 a, .vU32 b =>
      let prod := a.toNat * b.toNat
      .ok (resId.toNat, .vPair32 (UInt32.ofNat (prod % 4294967296)) (UInt32.ofNat (prod / 4294967296)))
    | .vU64 a, .vU64 b =>
      let prod := a.toNat * b.toNat
      .ok (resId.toNat, .vPair64 (UInt64.ofNat (prod % (2 ^ 64))) (UInt64.ofNat (prod / (2 ^ 64))))
    | _, _ => .error .typeMismatch
  | .opSelect _ resId condId tId fId =>
    match regs condId.toNat, regs tId.toNat, regs fId.toNat with
    | .vBool c, .vU32 t, .vU32 f => .ok (resId.toNat, .vU32 (if c then t else f))
    | .vBool c, .vU64 t, .vU64 f => .ok (resId.toNat, .vU64 (if c then t else f))
    | _, _, _ => .error .typeMismatch
  | .opIEqual _ resId aId bId =>
    match regs aId.toNat, regs bId.toNat with
    | .vU32 a, .vU32 b => .ok (resId.toNat, .vBool (a == b))
    | .vU64 a, .vU64 b => .ok (resId.toNat, .vBool (a == b))
    | _, _ => .error .typeMismatch
  | .opUGreaterThanEqual _ resId aId bId =>
    match regs aId.toNat, regs bId.toNat with
    | .vU32 a, .vU32 b => .ok (resId.toNat, .vBool (decide (b.toNat ≤ a.toNat)))
    | .vU64 a, .vU64 b => .ok (resId.toNat, .vBool (decide (b.toNat ≤ a.toNat)))
    | _, _ => .error .typeMismatch
  | .opULessThan _ resId aId bId =>
    match regs aId.toNat, regs bId.toNat with
    | .vU32 a, .vU32 b => .ok (resId.toNat, .vBool (decide (a.toNat < b.toNat)))
    | .vU64 a, .vU64 b => .ok (resId.toNat, .vBool (decide (a.toNat < b.toNat)))
    | _, _ => .error .typeMismatch
  | .opShiftRightLogical _ resId baseId shId =>
    match regs baseId.toNat, regs shId.toNat with
    | .vU32 a, .vU32 sh => .ok (resId.toNat, .vU32 (UInt32.ofNat (a.toNat / 2 ^ (sh.toNat % 32))))
    | .vU64 a, .vU64 sh => .ok (resId.toNat, .vU64 (UInt64.ofNat (a.toNat / 2 ^ (sh.toNat % 64))))
    | _, _ => .error .typeMismatch
  | .opShiftLeftLogical _ resId baseId shId =>
    match regs baseId.toNat, regs shId.toNat with
    | .vU32 a, .vU32 sh =>
      .ok (resId.toNat, .vU32 (UInt32.ofNat ((a.toNat * 2 ^ (sh.toNat % 32)) % 4294967296)))
    | .vU64 a, .vU64 sh =>
      .ok (resId.toNat, .vU64 (UInt64.ofNat ((a.toNat * 2 ^ (sh.toNat % 64)) % (2 ^ 64))))
    | _, _ => .error .typeMismatch
  | .opBitwiseXor _ resId aId bId =>
    match regs aId.toNat, regs bId.toNat with
    | .vU32 a, .vU32 b => .ok (resId.toNat, .vU32 (a ^^^ b))
    | .vU64 a, .vU64 b => .ok (resId.toNat, .vU64 (a ^^^ b))
    | _, _ => .error .typeMismatch
  | .opBitwiseOr _ resId aId bId =>
    match regs aId.toNat, regs bId.toNat with
    | .vU32 a, .vU32 b => .ok (resId.toNat, .vU32 (a ||| b))
    | .vU64 a, .vU64 b => .ok (resId.toNat, .vU64 (a ||| b))
    | _, _ => .error .typeMismatch
  | .opBitwiseAnd _ resId aId bId =>
    match regs aId.toNat, regs bId.toNat with
    | .vU32 a, .vU32 b => .ok (resId.toNat, .vU32 (a &&& b))
    | .vU64 a, .vU64 b => .ok (resId.toNat, .vU64 (a &&& b))
    | _, _ => .error .typeMismatch
  | _ => .error .typeMismatch

/-- Apply a single lane's `OpStore` to `GpuMemState` with `64 KiB` LDS bounds enforcement. -/
def applyLaneStore (mem : GpuMemState) (regs : Nat → SpirvVal) (ptrId valId : UInt32) :
    Except SimtExecError GpuMemState :=
  match regs ptrId.toNat, regs valId.toNat with
  | .vPtr .workgroup _ elemIdx .w32, .vU32 v =>
    if elemIdx < ldsCapacityDwords then
      .ok { mem with lds := writeFn mem.lds elemIdx v }
    else
      .error (.ldsOutOfBounds elemIdx)
  | .vPtr .workgroup _ elemIdx .w64, .vU64 v =>
    if 2 * elemIdx + 1 < ldsCapacityDwords then
      .ok { mem with lds := writeU64Dwords mem.lds elemIdx v }
    else
      .error (.ldsOutOfBounds (2 * elemIdx + 1))
  | .vPtr .storageBuffer binding elemIdx .w32, .vU32 v =>
    .ok { mem with ssbo := writeSsboDword mem.ssbo binding elemIdx v }
  | .vPtr .storageBuffer binding elemIdx .w64, .vU64 v =>
    .ok { mem with ssbo := writeSsboU64 mem.ssbo binding elemIdx v }
  | _, _ => .error .typeMismatch

/-- State of one Wave32 subgroup (`32` SIMD lanes + `EXEC_LO` active mask + barrier latch). -/
structure Wave32State where
  pc : Nat
  execMask : Nat → Bool
  laneRegs : Nat → Nat → SpirvVal
  atBarrier : Bool

def allActive32 : Nat → Bool := fun lane => decide (lane < wave32Lanes)

/-- Execute all active lanes `0 .. k - 1` of a Wave32 store instruction sequentially across active lanes. -/
def execWaveStoreLanes (execMask : Nat → Bool) (laneRegs : Nat → Nat → SpirvVal)
    (ptrId valId : UInt32) : Nat → GpuMemState → Except SimtExecError GpuMemState
  | 0, mem => .ok mem
  | k + 1, mem =>
    match execWaveStoreLanes execMask laneRegs ptrId valId k mem with
    | .error e => .error e
    | .ok mem' =>
      if execMask k then applyLaneStore mem' (laneRegs k) ptrId valId else .ok mem'

/-- Evaluate a pure instruction across lanes `0 .. k - 1` of a Wave32 subgroup. -/
def evalWavePureLanes (env : SpirvModuleEnv) (mem : GpuMemState) (execMask : Nat → Bool)
    (laneRegs : Nat → Nat → SpirvVal) (inst : SpirvInst) :
    Nat → Except SimtExecError (Nat → Nat → SpirvVal)
  | 0 => .ok laneRegs
  | k + 1 =>
    match evalWavePureLanes env mem execMask laneRegs inst k with
    | .error e => .error e
    | .ok regs' =>
      if execMask k then
        match evalLanePureInst env mem (laneRegs k) inst with
        | .error e => .error e
        | .ok (dst, v) =>
          .ok (fun l => if l = k then writeFn (regs' k) dst v else regs' l)
      else
        .ok regs'

/-- Step one Wave32 subgroup by one instruction inside a `SpirvInst` sequence.
    When a wave reaches `OpControlBarrier(.workgroup, .workgroup, spirvSemWorkgroupAcqRel)`,
    it sets `atBarrier := true` and blocks until all waves in the workgroup arrive. -/
def stepWave32One (env : SpirvModuleEnv) (prog : List SpirvInst) (wSt : Wave32State)
    (mem : GpuMemState) : Except SimtExecError (Wave32State × GpuMemState) :=
  if wSt.atBarrier then
    .ok (wSt, mem)
  else
    match prog[wSt.pc]? with
    | none => .ok (wSt, mem)
    | some (.opControlBarrier .workgroup .workgroup sem) =>
      if sem == spirvSemWorkgroupAcqRel then
        .ok ({ wSt with atBarrier := true }, mem)
      else
        .error .typeMismatch
    | some (.opControlBarrier _ _ _) => .error .typeMismatch
    | some (.opStore ptrId valId) =>
      match execWaveStoreLanes wSt.execMask wSt.laneRegs ptrId valId wave32Lanes mem with
      | .error e => .error e
      | .ok mem' => .ok ({ wSt with pc := wSt.pc + 1 }, mem')
    | some (.opLabel _) =>
      .ok ({ wSt with pc := wSt.pc + 1 }, mem)
    | some inst =>
      match evalWavePureLanes env mem wSt.execMask wSt.laneRegs inst wave32Lanes with
      | .error e => .error e
      | .ok regs' => .ok ({ wSt with pc := wSt.pc + 1, laneRegs := regs' }, mem)

/-- Multi-wave workgroup execution state: all `numWaves` Wave32 states + shared `64 KiB` LDS & SSBOs. -/
structure WorkgroupExecState where
  waves : Nat → Wave32State
  mem : GpuMemState

def initWorkgroupExecState (env : SpirvModuleEnv) (cfg : WorkgroupConfig) (initMem : GpuMemState) :
    WorkgroupExecState :=
  { waves := fun w =>
      { pc := 0
        execMask := allActive32
        laneRegs := fun lane => initLaneRegs env cfg w lane
        atBarrier := false }
    mem := initMem }

/-- Step wave `w` once inside the multi-wave workgroup (no-op if `w ≥ cfg.numWaves`). -/
def stepWorkgroupWave (env : SpirvModuleEnv) (cfg : WorkgroupConfig) (prog : List SpirvInst)
    (w : Nat) (st : WorkgroupExecState) : Except SimtExecError WorkgroupExecState :=
  if w < cfg.numWaves then
    match stepWave32One env prog (st.waves w) st.mem with
    | .error e => .error e
    | .ok (wSt', mem') => .ok { waves := writeFn st.waves w wSt', mem := mem' }
  else
    .ok st

/-- Execute an arbitrary cross-wave instruction-interleaving schedule `sched : List Nat` within one
    barrier epoch. -/
def runInterleavedSchedule (env : SpirvModuleEnv) (cfg : WorkgroupConfig) (prog : List SpirvInst) :
    List Nat → WorkgroupExecState → Except SimtExecError WorkgroupExecState
  | [], st => .ok st
  | w :: ws, st =>
    match stepWorkgroupWave env cfg prog w st with
    | .error e => .error e
    | .ok st' => runInterleavedSchedule env cfg prog ws st'

/-- Check whether all `numWaves` Wave32 subgroups have arrived at `OpControlBarrier`. -/
def allWavesAtBarrier (cfg : WorkgroupConfig) (waves : Nat → Wave32State) : Bool :=
  (List.range cfg.numWaves).all fun w => (waves w).atBarrier

/-- Lockstep workgroup-wide `OpControlBarrier` release: advances every wave past the barrier ONLY
    when all `numWaves` waves in the workgroup have reached the barrier, preserving 100% of shared
    `Workgroup` LDS and global `StorageBuffer` writes! -/
def releaseWorkgroupBarrier (cfg : WorkgroupConfig) (st : WorkgroupExecState) :
    Except SimtExecError WorkgroupExecState :=
  if allWavesAtBarrier cfg st.waves then
    .ok { waves := fun w =>
            if w < cfg.numWaves then
              let ws := st.waves w
              { ws with pc := ws.pc + 1, atBarrier := false }
            else
              st.waves w
          mem := st.mem }
  else
    .error .barrierDivergence

/-- A barrier-segmented kernel consists of barrier-free epochs `epochs : List (List SpirvInst)`,
    where adjacent epochs are separated by `OpControlBarrier(.workgroup, .workgroup, 0x108)`. -/
def BarrierEpoch := List SpirvInst

/-- Run one barrier epoch under wave schedule `sched : List Nat` (every wave steps through `epoch`
    and arrives at the trailing `OpControlBarrier`). -/
def runOneBarrierEpoch (env : SpirvModuleEnv) (cfg : WorkgroupConfig) (epoch : List SpirvInst)
    (hasTrailingBarrier : Bool) (sched : List Nat) (st : WorkgroupExecState) :
    Except SimtExecError WorkgroupExecState :=
  let prog := if hasTrailingBarrier then
      epoch ++ [.opControlBarrier .workgroup .workgroup spirvSemWorkgroupAcqRel]
    else
      epoch
  let resetWaves : WorkgroupExecState :=
    { waves := fun w => { (st.waves w) with pc := 0, atBarrier := false }, mem := st.mem }
  match runInterleavedSchedule env cfg prog sched resetWaves with
  | .error e => .error e
  | .ok stAfter =>
    if hasTrailingBarrier then releaseWorkgroupBarrier cfg stAfter else .ok stAfter

/-- Execute a multi-epoch multi-wave workgroup kernel across per-epoch schedules `scheds`.
    Shared `Workgroup` LDS (`st.mem.lds`) persists intact across ALL epochs and ALL waves! -/
def runMultiWaveEpochs (env : SpirvModuleEnv) (cfg : WorkgroupConfig) :
    List (List SpirvInst) → List (List Nat) → WorkgroupExecState →
    Except SimtExecError WorkgroupExecState
  | [], _, st => .ok st
  | [lastEpoch], scheds, st =>
    runOneBarrierEpoch env cfg lastEpoch false (scheds.headD []) st
  | ep :: nextEp :: rest, scheds, st =>
    match runOneBarrierEpoch env cfg ep true (scheds.headD []) st with
    | .error e => .error e
    | .ok st' => runMultiWaveEpochs env cfg (nextEp :: rest) (scheds.tail) st'

/-- Canonical wave schedule for an epoch of length `L` (with optional +1 barrier instruction):
    runs Wave `0` for `steps` instructions, then Wave `1`, ..., up to Wave `numWaves - 1`. -/
def canonicalEpochSchedule (numWaves steps : Nat) : List Nat :=
  (List.range numWaves).flatMap (fun w => List.replicate steps w)

/-! ## §3. Compositional `Faial` MAP Data-Race Freedom & `SIMT-CT` Side-Channel Immunity -/

/-- Per-thread (`tid = wave * 32 + lane`) memory footprint of one barrier epoch (`Faial` MAP). -/
structure EpochAccessProtocol where
  ldsRead : Nat → Nat → Bool
  ldsWrite : Nat → Nat → Bool
  ssboRead : Nat → Nat → Nat → Bool
  ssboWrite : Nat → Nat → Nat → Bool

/-- **`Faial` Memory-Access-Protocol Data-Race Freedom (`FaialMapRaceFree`)**:
    Within the barrier epoch, for every pair of distinct threads `t₁ ≠ t₂` in the workgroup,
    `t₁`'s shared `Workgroup` LDS and global `StorageBuffer` write sets are strictly disjoint
    from `t₂`'s write AND read sets (`W(t₁) ∩ (W(t₂) ∪ R(t₂)) = ∅`). -/
def FaialMapRaceFree (numThreads : Nat) (proto : EpochAccessProtocol) : Prop :=
  ∀ t₁ t₂ : Nat, t₁ < numThreads → t₂ < numThreads → t₁ ≠ t₂ →
    (∀ a : Nat, proto.ldsWrite t₁ a = true →
      proto.ldsWrite t₂ a = false ∧ proto.ldsRead t₂ a = false) ∧
    (∀ b a : Nat, proto.ssboWrite t₁ b a = true →
      proto.ssboWrite t₂ b a = false ∧ proto.ssboRead t₂ b a = false)

/-- Two `GpuMemState`s agree on all locations read by wave `w` under `proto`. -/
def MemAgreesOnWaveReads (w : Nat) (proto : EpochAccessProtocol) (m₁ m₂ : GpuMemState) : Prop :=
  m₁.pushConsts = m₂.pushConsts ∧
  (∀ lane a : Nat, lane < wave32Lanes → proto.ldsRead (w * wave32Lanes + lane) a = true →
    m₁.lds a = m₂.lds a) ∧
  (∀ lane b a : Nat, lane < wave32Lanes → proto.ssboRead (w * wave32Lanes + lane) b a = true →
    m₁.ssbo b a = m₂.ssbo b a)

/-- Semantic soundness of an `EpochAccessProtocol` on a program `prog`:
    1. Wave `w`'s step outcome (`wSt'`) and write footprint depend ONLY on `w`'s read set;
    2. Wave `w` modifies ONLY addresses inside `w`'s write set (`ldsWrite`, `ssboWrite`), and
       never modifies `pushConsts`. -/
structure WaveRespectsProtocol (env : SpirvModuleEnv) (cfg : WorkgroupConfig)
    (prog : List SpirvInst) (proto : EpochAccessProtocol) : Prop where
  read_locality :
    ∀ (w : Nat) (_hw : w < cfg.numWaves) (wSt : Wave32State) (m₁ m₂ : GpuMemState),
      MemAgreesOnWaveReads w proto m₁ m₂ →
      (match stepWave32One env prog wSt m₁, stepWave32One env prog wSt m₂ with
       | .error e₁, .error e₂ => e₁ = e₂
       | .ok (wSt₁, m₁'), .ok (wSt₂, m₂') =>
         wSt₁ = wSt₂ ∧
         m₁'.pushConsts = m₁.pushConsts ∧
         m₂'.pushConsts = m₂.pushConsts ∧
         (∀ a : Nat,
           (∃ lane < wave32Lanes, proto.ldsWrite (w * wave32Lanes + lane) a = true) →
             m₁'.lds a = m₂'.lds a) ∧
         (∀ a : Nat,
           (∀ lane < wave32Lanes, proto.ldsWrite (w * wave32Lanes + lane) a = false) →
             m₁'.lds a = m₁.lds a ∧ m₂'.lds a = m₂.lds a) ∧
         (∀ b a : Nat,
           (∃ lane < wave32Lanes, proto.ssboWrite (w * wave32Lanes + lane) b a = true) →
             m₁'.ssbo b a = m₂'.ssbo b a) ∧
         (∀ b a : Nat,
           (∀ lane < wave32Lanes, proto.ssboWrite (w * wave32Lanes + lane) b a = false) →
             m₁'.ssbo b a = m₁.ssbo b a ∧ m₂'.ssbo b a = m₂.ssbo b a)
       | _, _ => False)

private theorem wave_threads_ne {w₁ w₂ l₁ l₂ : Nat} (hw : w₁ ≠ w₂)
    (hl₁ : l₁ < wave32Lanes) (hl₂ : l₂ < wave32Lanes) :
    w₁ * wave32Lanes + l₁ ≠ w₂ * wave32Lanes + l₂ := by
  unfold wave32Lanes at *
  omega

/-- **Cross-Wave Diamond Commutativity Lemma (`stepWorkgroupWave_comm`)**:
    Under `FaialMapRaceFree`, stepping two distinct Wave32 subgroups `w₁ ≠ w₂` strictly commutes! -/
theorem stepWorkgroupWave_comm {env : SpirvModuleEnv} {cfg : WorkgroupConfig}
    {prog : List SpirvInst} {proto : EpochAccessProtocol}
    (hResp : WaveRespectsProtocol env cfg prog proto)
    (hDrf : FaialMapRaceFree cfg.totalThreads proto)
    {w₁ w₂ : Nat} (hne : w₁ ≠ w₂) (st : WorkgroupExecState)
    (hOk₁ : ∃ s₁, stepWorkgroupWave env cfg prog w₁ st = .ok s₁)
    (hOk₂ : ∃ s₂, stepWorkgroupWave env cfg prog w₂ st = .ok s₂) :
    (stepWorkgroupWave env cfg prog w₁ st >>= stepWorkgroupWave env cfg prog w₂) =
    (stepWorkgroupWave env cfg prog w₂ st >>= stepWorkgroupWave env cfg prog w₁) := by
  by_cases hw₁ : w₁ < cfg.numWaves
  · by_cases hw₂ : w₂ < cfg.numWaves
    · obtain ⟨s₁, hs₁⟩ := hOk₁
      obtain ⟨s₂, hs₂⟩ := hOk₂
      unfold stepWorkgroupWave at hs₁ hs₂ ⊢
      simp only [hw₁, hw₂, ↓reduceIte] at hs₁ hs₂ ⊢
      have hSelf₁ := hResp.read_locality w₁ hw₁ (st.waves w₁) st.mem st.mem
        ⟨rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
      have hSelf₂ := hResp.read_locality w₂ hw₂ (st.waves w₂) st.mem st.mem
        ⟨rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
      cases hStep1 : stepWave32One env prog (st.waves w₁) st.mem with
      | error e => rw [hStep1] at hs₁; cases hs₁
      | ok p1 =>
        rcases p1 with ⟨wSt₁, m₁⟩
        cases hStep2 : stepWave32One env prog (st.waves w₂) st.mem with
        | error e => rw [hStep2] at hs₂; cases hs₂
        | ok p2 =>
          rcases p2 with ⟨wSt₂, m₂⟩
          rw [hStep1] at hSelf₁
          rw [hStep2] at hSelf₂
          rcases hSelf₁ with ⟨_, hpc₁, _, _, hNoLds₁, _, hNoSsbo₁⟩
          rcases hSelf₂ with ⟨_, hpc₂, _, _, hNoLds₂, _, hNoSsbo₂⟩
          have hAgree2After1 : MemAgreesOnWaveReads w₂ proto st.mem m₁ := by
            refine ⟨hpc₁.symm, ?_, ?_⟩
            · intro l₂ a hl₂ hRead₂
              have hNoW₁ : ∀ l₁ < wave32Lanes, proto.ldsWrite (w₁ * wave32Lanes + l₁) a = false := by
                intro l₁ hl₁
                cases hW : proto.ldsWrite (w₁ * wave32Lanes + l₁) a with
                | false => rfl
                | true =>
                  have ht₁ : w₁ * wave32Lanes + l₁ < cfg.totalThreads := by
                    unfold WorkgroupConfig.totalThreads wave32Lanes at *; omega
                  have ht₂ : w₂ * wave32Lanes + l₂ < cfg.totalThreads := by
                    unfold WorkgroupConfig.totalThreads wave32Lanes at *; omega
                  have hDisj := (hDrf _ _ ht₁ ht₂ (wave_threads_ne hne hl₁ hl₂)).1 a hW
                  rw [hDisj.2] at hRead₂; cases hRead₂
              exact (hNoLds₁ a hNoW₁).1.symm
            · intro l₂ b a hl₂ hRead₂
              have hNoW₁ : ∀ l₁ < wave32Lanes, proto.ssboWrite (w₁ * wave32Lanes + l₁) b a = false := by
                intro l₁ hl₁
                cases hW : proto.ssboWrite (w₁ * wave32Lanes + l₁) b a with
                | false => rfl
                | true =>
                  have ht₁ : w₁ * wave32Lanes + l₁ < cfg.totalThreads := by
                    unfold WorkgroupConfig.totalThreads wave32Lanes at *; omega
                  have ht₂ : w₂ * wave32Lanes + l₂ < cfg.totalThreads := by
                    unfold WorkgroupConfig.totalThreads wave32Lanes at *; omega
                  have hDisj := (hDrf _ _ ht₁ ht₂ (wave_threads_ne hne hl₁ hl₂)).2 b a hW
                  rw [hDisj.2] at hRead₂; cases hRead₂
              exact (hNoSsbo₁ b a hNoW₁).1.symm
          have hAgree1After2 : MemAgreesOnWaveReads w₁ proto st.mem m₂ := by
            refine ⟨hpc₂.symm, ?_, ?_⟩
            · intro l₁ a hl₁ hRead₁
              have hNoW₂ : ∀ l₂ < wave32Lanes, proto.ldsWrite (w₂ * wave32Lanes + l₂) a = false := by
                intro l₂ hl₂
                cases hW : proto.ldsWrite (w₂ * wave32Lanes + l₂) a with
                | false => rfl
                | true =>
                  have ht₁ : w₁ * wave32Lanes + l₁ < cfg.totalThreads := by
                    unfold WorkgroupConfig.totalThreads wave32Lanes at *; omega
                  have ht₂ : w₂ * wave32Lanes + l₂ < cfg.totalThreads := by
                    unfold WorkgroupConfig.totalThreads wave32Lanes at *; omega
                  have hDisj := (hDrf _ _ ht₂ ht₁ (wave_threads_ne hne.symm hl₂ hl₁)).1 a hW
                  rw [hDisj.2] at hRead₁; cases hRead₁
              exact (hNoLds₂ a hNoW₂).1.symm
            · intro l₁ b a hl₁ hRead₁
              have hNoW₂ : ∀ l₂ < wave32Lanes, proto.ssboWrite (w₂ * wave32Lanes + l₂) b a = false := by
                intro l₂ hl₂
                cases hW : proto.ssboWrite (w₂ * wave32Lanes + l₂) b a with
                | false => rfl
                | true =>
                  have ht₁ : w₁ * wave32Lanes + l₁ < cfg.totalThreads := by
                    unfold WorkgroupConfig.totalThreads wave32Lanes at *; omega
                  have ht₂ : w₂ * wave32Lanes + l₂ < cfg.totalThreads := by
                    unfold WorkgroupConfig.totalThreads wave32Lanes at *; omega
                  have hDisj := (hDrf _ _ ht₂ ht₁ (wave_threads_ne hne.symm hl₂ hl₁)).2 b a hW
                  rw [hDisj.2] at hRead₁; cases hRead₁
              exact (hNoSsbo₂ b a hNoW₂).1.symm
          have hLoc2 := hResp.read_locality w₂ hw₂ (st.waves w₂) st.mem m₁ hAgree2After1
          have hLoc1 := hResp.read_locality w₁ hw₁ (st.waves w₁) st.mem m₂ hAgree1After2
          rw [hStep2] at hLoc2
          rw [hStep1] at hLoc1
          simp only [Bind.bind, Except.bind, hw₁, hw₂, ↓reduceIte,
            writeFn_other st.waves _ hne.symm, writeFn_other st.waves _ hne]
          cases hStep2_after1 : stepWave32One env prog (st.waves w₂) m₁ with
          | error e => rw [hStep2_after1] at hLoc2; cases hLoc2
          | ok p12 =>
            rcases p12 with ⟨wSt₂', m₁₂⟩
            cases hStep1_after2 : stepWave32One env prog (st.waves w₁) m₂ with
            | error e => rw [hStep1_after2] at hLoc1; cases hLoc1
            | ok p21 =>
              rcases p21 with ⟨wSt₁', m₂₁⟩
              rw [hStep2_after1] at hLoc2
              rw [hStep1_after2] at hLoc1
              rcases hLoc2 with ⟨hwSt₂Eq, _, hpc₁₂, hW₂Lds, hNoW₂Lds, hW₂Ssbo, hNoW₂Ssbo⟩
              rcases hLoc1 with ⟨hwSt₁Eq, _, hpc₂₁, hW₁Lds, hNoW₁Lds, hW₁Ssbo, hNoW₁Ssbo⟩
              subst hwSt₂Eq; subst hwSt₁Eq
              congr 1
              have hWavesEq := writeFn_comm st.waves wSt₁ wSt₂ hne
              have hMemEq : m₁₂ = m₂₁ := by
                cases m₁₂ with | mk lds12 ssbo12 pc12 =>
                cases m₂₁ with | mk lds21 ssbo21 pc21 =>
                simp only at hpc₁₂ hpc₂₁ hW₂Lds hNoW₂Lds hW₂Ssbo hNoW₂Ssbo hW₁Lds hNoW₁Lds hW₁Ssbo hNoW₁Ssbo ⊢
                refine ⟨?_, ?_, ?_⟩
                · funext a
                  by_cases hex₂ : ∃ l₂ < wave32Lanes, proto.ldsWrite (w₂ * wave32Lanes + l₂) a = true
                  · obtain ⟨l₂, hl₂, hw₂a⟩ := hex₂
                    have hNoW₁a : ∀ l₁ < wave32Lanes, proto.ldsWrite (w₁ * wave32Lanes + l₁) a = false := by
                      intro l₁ hl₁
                      have ht₁ : w₁ * wave32Lanes + l₁ < cfg.totalThreads := by
                        unfold WorkgroupConfig.totalThreads wave32Lanes at *; omega
                      have ht₂ : w₂ * wave32Lanes + l₂ < cfg.totalThreads := by
                        unfold WorkgroupConfig.totalThreads wave32Lanes at *; omega
                      exact (hDrf _ _ ht₂ ht₁ (wave_threads_ne hne.symm hl₂ hl₁)).1 a hw₂a |>.1
                    rw [← hW₂Lds a ⟨l₂, hl₂, hw₂a⟩, (hNoW₁Lds a hNoW₁a).2]
                  · have hAll₂ : ∀ l₂ < wave32Lanes, proto.ldsWrite (w₂ * wave32Lanes + l₂) a = false := by
                      intro l₂ hl₂
                      cases h : proto.ldsWrite (w₂ * wave32Lanes + l₂) a with
                      | false => rfl
                      | true => exact False.elim (hex₂ ⟨l₂, hl₂, h⟩)
                    by_cases hex₁ : ∃ l₁ < wave32Lanes, proto.ldsWrite (w₁ * wave32Lanes + l₁) a = true
                    · rw [(hNoW₂Lds a hAll₂).2, hW₁Lds a hex₁]
                    · have hAll₁ : ∀ l₁ < wave32Lanes, proto.ldsWrite (w₁ * wave32Lanes + l₁) a = false := by
                        intro l₁ hl₁
                        cases h : proto.ldsWrite (w₁ * wave32Lanes + l₁) a with
                        | false => rfl
                        | true => exact False.elim (hex₁ ⟨l₁, hl₁, h⟩)
                      rw [(hNoW₂Lds a hAll₂).2, (hNoW₁Lds a hAll₁).2,
                          (hNoLds₁ a hAll₁).1, (hNoLds₂ a hAll₂).1]
                · funext b a
                  by_cases hex₂ : ∃ l₂ < wave32Lanes, proto.ssboWrite (w₂ * wave32Lanes + l₂) b a = true
                  · obtain ⟨l₂, hl₂, hw₂a⟩ := hex₂
                    have hNoW₁a : ∀ l₁ < wave32Lanes, proto.ssboWrite (w₁ * wave32Lanes + l₁) b a = false := by
                      intro l₁ hl₁
                      have ht₁ : w₁ * wave32Lanes + l₁ < cfg.totalThreads := by
                        unfold WorkgroupConfig.totalThreads wave32Lanes at *; omega
                      have ht₂ : w₂ * wave32Lanes + l₂ < cfg.totalThreads := by
                        unfold WorkgroupConfig.totalThreads wave32Lanes at *; omega
                      exact (hDrf _ _ ht₂ ht₁ (wave_threads_ne hne.symm hl₂ hl₁)).2 b a hw₂a |>.1
                    rw [← hW₂Ssbo b a ⟨l₂, hl₂, hw₂a⟩, (hNoW₁Ssbo b a hNoW₁a).2]
                  · have hAll₂ : ∀ l₂ < wave32Lanes, proto.ssboWrite (w₂ * wave32Lanes + l₂) b a = false := by
                      intro l₂ hl₂
                      cases h : proto.ssboWrite (w₂ * wave32Lanes + l₂) b a with
                      | false => rfl
                      | true => exact False.elim (hex₂ ⟨l₂, hl₂, h⟩)
                    by_cases hex₁ : ∃ l₁ < wave32Lanes, proto.ssboWrite (w₁ * wave32Lanes + l₁) b a = true
                    · rw [(hNoW₂Ssbo b a hAll₂).2, hW₁Ssbo b a hex₁]
                    · have hAll₁ : ∀ l₁ < wave32Lanes, proto.ssboWrite (w₁ * wave32Lanes + l₁) b a = false := by
                        intro l₁ hl₁
                        cases h : proto.ssboWrite (w₁ * wave32Lanes + l₁) b a with
                        | false => rfl
                        | true => exact False.elim (hex₁ ⟨l₁, hl₁, h⟩)
                      rw [(hNoW₂Ssbo b a hAll₂).2, (hNoW₁Ssbo b a hAll₁).2,
                          (hNoSsbo₁ b a hAll₁).1, (hNoSsbo₂ b a hAll₂).1]
                · rw [hpc₁₂, hpc₁, hpc₂₁, hpc₂]
              rw [hWavesEq, hMemEq]
    · unfold stepWorkgroupWave
      simp only [Bind.bind, Except.bind, hw₂, ↓reduceIte]
      cases stepWave32One env prog (st.waves w₁) st.mem <;> simp [hw₁, hw₂]
  · unfold stepWorkgroupWave
    simp only [Bind.bind, Except.bind, hw₁, ↓reduceIte]
    cases stepWave32One env prog (st.waves w₂) st.mem <;> simp [hw₁, hw₂]

/-- Adjacent-swap equivalence of wave schedules (`w₁ :: w₂ :: ws ~ w₂ :: w₁ :: ws` for `w₁ ≠ w₂`). -/
inductive SchedPerm : List Nat → List Nat → Prop where
  | refl (s : List Nat) : SchedPerm s s
  | swap {w₁ w₂ : Nat} (hne : w₁ ≠ w₂) (rest : List Nat) :
      SchedPerm (w₁ :: w₂ :: rest) (w₂ :: w₁ :: rest)
  | cons (w : Nat) {s₁ s₂ : List Nat} : SchedPerm s₁ s₂ → SchedPerm (w :: s₁) (w :: s₂)
  | trans {s₁ s₂ s₃ : List Nat} : SchedPerm s₁ s₂ → SchedPerm s₂ s₃ → SchedPerm s₁ s₃

/-- **Multi-Wave Schedule Confluence Theorem (`multiWave_schedule_confluence`)**:
    Under `FaialMapRaceFree`, ANY two valid cross-wave instruction schedules related by
    arbitrary non-interfering wave reorderings (`SchedPerm`) produce the **exact same**
    multi-wave workgroup state (shared `64 KiB` LDS + global `StorageBuffer` + all Wave32 registers)! -/
theorem multiWave_schedule_confluence {env : SpirvModuleEnv} {cfg : WorkgroupConfig}
    {prog : List SpirvInst} {proto : EpochAccessProtocol}
    (hResp : WaveRespectsProtocol env cfg prog proto)
    (hDrf : FaialMapRaceFree cfg.totalThreads proto)
    (hTotal : ∀ (w : Nat) (st : WorkgroupExecState),
      ∃ st', stepWorkgroupWave env cfg prog w st = .ok st')
    {sched₁ sched₂ : List Nat} (hPerm : SchedPerm sched₁ sched₂) :
    ∀ st : WorkgroupExecState,
      runInterleavedSchedule env cfg prog sched₁ st =
      runInterleavedSchedule env cfg prog sched₂ st := by
  induction hPerm with
  | refl _ => intro _; rfl
  | @swap w₁ w₂ hne rest =>
    intro st
    have hComm := stepWorkgroupWave_comm hResp hDrf hne st (hTotal w₁ st) (hTotal w₂ st)
    obtain ⟨s₁, hs₁⟩ := hTotal w₁ st
    obtain ⟨s₂, hs₂⟩ := hTotal w₂ st
    obtain ⟨s₁₂, hs₁₂⟩ := hTotal w₂ s₁
    obtain ⟨s₂₁, hs₂₁⟩ := hTotal w₁ s₂
    dsimp only [runInterleavedSchedule]
    rw [hs₁, hs₂]
    dsimp only [runInterleavedSchedule]
    rw [hs₁₂, hs₂₁]
    have hEq12 : (Except.ok s₁₂ : Except SimtExecError WorkgroupExecState) = .ok s₂₁ := by
      simpa [Bind.bind, Except.bind, hs₁, hs₂, hs₁₂, hs₂₁] using hComm
    injection hEq12 with hStateEq
    rw [hStateEq]
  | cons w _ ih =>
    intro st
    dsimp only [runInterleavedSchedule]
    obtain ⟨st', hst'⟩ := hTotal w st
    rw [hst']
    exact ih st'
  | trans _ _ ih₁ ih₂ =>
    intro st
    exact (ih₁ st).trans (ih₂ st)

/-- Any schedule `sched` with identical per-wave step counts (`∀ w, sched.count w = ...`) reduces
    by `SchedPerm` to grouping waves in canonical order `0, 1, ..., numWaves - 1`! -/
private theorem schedPerm_bubble_front (w : Nat) :
    ∀ (xs ys : List Nat),
      (∀ x ∈ xs, x ≠ w) →
      SchedPerm (xs ++ w :: ys) (w :: xs ++ ys)
  | [], _, _ => .refl _
  | x :: xs, ys, hne =>
    have hx : x ≠ w := hne x (.head _)
    have hrest : ∀ z ∈ xs, z ≠ w := fun z hz => hne z (.tail _ hz)
    .trans (.cons x (schedPerm_bubble_front w xs ys hrest)) (.swap hx (xs ++ ys))

private def extractAllWave (w : Nat) : List Nat → List Nat × List Nat
  | [] => ([], [])
  | x :: xs =>
    let (ws, rest) := extractAllWave w xs
    if x = w then (w :: ws, rest) else (ws, x :: rest)

private theorem schedPerm_extractAllWave (w : Nat) :
    ∀ s : List Nat,
      SchedPerm s ((extractAllWave w s).1 ++ (extractAllWave w s).2)
  | [] => .refl []
  | x :: xs => by
    dsimp only [extractAllWave]
    by_cases hxw : x = w
    · subst hxw
      simp only [↓reduceIte, List.cons_append]
      exact .cons x (schedPerm_extractAllWave x xs)
    · simp only [hxw, ↓reduceIte]
      have hPermTail := schedPerm_extractAllWave w xs
      -- `x :: (ws ++ rest) ~ ws ++ (x :: rest)` since every element of `ws` equals `w ≠ x`
      have hAllW : ∀ z ∈ (extractAllWave w xs).1, z = w := by
        clear hPermTail hxw
        induction xs with
        | nil => intro _ h; cases h
        | cons y ys ih =>
          dsimp only [extractAllWave]
          split
          · intro z hz; rcases List.mem_cons.mp hz with rfl | hm
            · rfl
            · exact ih z hm
          · exact ih
      have hPushX : ∀ (ws rest : List Nat), (∀ z ∈ ws, z = w) →
          SchedPerm (x :: ws ++ rest) (ws ++ x :: rest) := by
        intro ws rest hws
        induction ws with
        | nil => exact .refl _
        | cons z ws ih =>
          have hzw : z = w := hws z (.head _)
          cases hzw
          exact .trans (.swap hxw (ws ++ rest))
            (.cons z (ih (fun u hu => hws u (.tail _ hu))))
      exact .trans (.cons x hPermTail) (hPushX _ _ hAllW)

private theorem extractAllWave_fst_eq_replicate (w : Nat) :
    ∀ s : List Nat, (extractAllWave w s).1 = List.replicate (s.count w) w
  | [] => rfl
  | x :: xs => by
    dsimp only [extractAllWave]
    by_cases hxw : x = w
    · subst hxw
      simp [List.count_cons_self, List.replicate_succ, extractAllWave_fst_eq_replicate x xs]
    · have hne : (x == w) = false := beq_false_of_ne hxw
      simp [hxw, List.count_cons, extractAllWave_fst_eq_replicate w xs]

private theorem extractAllWave_snd_count (w u : Nat) :
    ∀ s : List Nat, ((extractAllWave w s).2).count u = if u = w then 0 else s.count u
  | [] => by simp [extractAllWave]
  | x :: xs => by
    dsimp only [extractAllWave]
    by_cases hxw : x = w
    · subst hxw
      simp only [↓reduceIte, extractAllWave_snd_count x u xs]
      by_cases hux : u = x
      · subst hux; simp
      · have hne : (x == u) = false := beq_false_of_ne (Ne.symm hux)
        simp [hux, List.count_cons, hne]
    · simp only [hxw, ↓reduceIte, List.count_cons, extractAllWave_snd_count w u xs]
      by_cases hux : u = w
      · subst hux
        have hne : (x == u) = false := beq_false_of_ne hxw
        simp [hne]
      · simp [hux]

private theorem extractAllWave_snd_mem {w z : Nat} :
    ∀ {s : List Nat}, z ∈ (extractAllWave w s).2 → z ∈ s ∧ z ≠ w
  | [], h => by cases h
  | x :: xs, h => by
    dsimp only [extractAllWave] at h
    by_cases hxw : x = w
    · simp only [hxw, ↓reduceIte] at h
      obtain ⟨hm, hne⟩ := extractAllWave_snd_mem h
      exact ⟨.tail _ hm, hne⟩
    · simp only [hxw, ↓reduceIte, List.mem_cons] at h
      rcases h with rfl | hm
      · exact ⟨.head _, hxw⟩
      · obtain ⟨hm', hne⟩ := extractAllWave_snd_mem hm
        exact ⟨.tail _ hm', hne⟩

/-- Any two schedules `s₁, s₂` bounded by `< bound` with identical per-wave step counts (`count w`)
    are `SchedPerm`-equivalent! -/
theorem schedPerm_of_same_counts :
    ∀ (bound : Nat) {s₁ s₂ : List Nat},
      (∀ w ∈ s₁, w < bound) →
      (∀ w ∈ s₂, w < bound) →
      (∀ w < bound, s₁.count w = s₂.count w) →
      SchedPerm s₁ s₂
  | 0, s₁, s₂, h₁, h₂, _ => by
    cases s₁ with
    | nil =>
      cases s₂ with
      | nil => exact .refl []
      | cons y _ => exact absurd (h₂ y (.head _)) (by omega)
    | cons x _ => exact absurd (h₁ x (.head _)) (by omega)
  | b + 1, s₁, s₂, h₁, h₂, hCnt => by
    have p₁ := schedPerm_extractAllWave b s₁
    have p₂ := schedPerm_extractAllWave b s₂
    rw [extractAllWave_fst_eq_replicate b s₁] at p₁
    rw [extractAllWave_fst_eq_replicate b s₂, ← hCnt b (by omega)] at p₂
    have hSub₁ : ∀ w ∈ (extractAllWave b s₁).2, w < b := by
      intro w hw
      obtain ⟨hm, hne⟩ := extractAllWave_snd_mem hw
      have hlt := h₁ w hm
      omega
    have hSub₂ : ∀ w ∈ (extractAllWave b s₂).2, w < b := by
      intro w hw
      obtain ⟨hm, hne⟩ := extractAllWave_snd_mem hw
      have hlt := h₂ w hm
      omega
    have hSubCnt : ∀ w < b, ((extractAllWave b s₁).2).count w = ((extractAllWave b s₂).2).count w := by
      intro w hw
      have hne : w ≠ b := by omega
      rw [extractAllWave_snd_count b w s₁, extractAllWave_snd_count b w s₂]
      simp [hne, hCnt w (by omega)]
    have ih := schedPerm_of_same_counts b hSub₁ hSub₂ hSubCnt
    have hPrepend : ∀ (k : Nat) {u v : List Nat}, SchedPerm u v →
        SchedPerm (List.replicate k b ++ u) (List.replicate k b ++ v) := by
      intro k u v huv
      induction k with
      | zero => simpa using huv
      | succ k ihk => exact .cons b ihk
    have hSymm : ∀ {u v : List Nat}, SchedPerm u v → SchedPerm v u := by
      intro u v huv
      induction huv with
      | refl s => exact .refl s
      | swap hne rest => exact .swap hne.symm rest
      | cons w _ ihs => exact .cons w ihs
      | trans _ _ iha ihb => exact .trans ihb iha
    exact .trans p₁ (.trans (hPrepend (s₁.count b) ih) (hSymm p₂))

/-! ### `#tooth` Witnesses for Cross-Wave Synchronization & Persistent Shared `64 KiB` LDS -/

/-- Minimal 2-wave (`64`-thread = `2 × Wave32`) SPIR-V module environment for cross-wave LDS tree
    reduction:
    - `%1` : `LocalInvocationId` (`0 .. 63`)
    - `%2` : `Workgroup` LDS pointer (`u32[]`)
    - `%3` : `StorageBuffer` binding `0` (`u32[]` input)
    - `%4` : `StorageBuffer` binding `1` (`u32[]` output)
    - `%5` : constant `32 : u32` (cross-wave stride: Wave 0 reads `tid + 32` written by Wave 1!)
    - `%6` : pointer type `Workgroup u32*`
    - `%7` : pointer type `StorageBuffer u32*`
    - `%8` : `u32` type -/
def twoWaveReductionEnv : SpirvModuleEnv where
  intWidths id := if id == 8 then some .w32 else none
  ptrInfo id :=
    if id == 2 || id == 6 || id == 12 || id == 13 || id == 16 then some (.workgroup, 0, .w32)
    else if id == 3 || id == 7 || id == 10 then some (.storageBuffer, 0, .w32)
    else if id == 4 || id == 19 then some (.storageBuffer, 1, .w32)
    else none
  initConst id := if id == 5 then .vU32 32 else .vUndef
  builtIns id := if id == 1 then some .localInvocationId else none

def twoWavePhase0WriteLds : List SpirvInst :=
  [ -- %10 = &inBuf[tid]; %11 = inBuf[tid]; %12 = &lds[tid]; lds[tid] = %11
    .opAccessChain 7 10 3 [1],
    .opLoad 8 11 10,
    .opAccessChain 6 12 2 [1],
    .opStore 12 11
  ]

def twoWavePhase1CrossWaveRead : List SpirvInst :=
  [ -- %13 = &lds[tid]; %14 = lds[tid]; %15 = (tid + 32) & 63? Wait: (tid ^ 32) pairs Wave 0 <-> Wave 1!
    .opAccessChain 6 13 2 [1],
    .opLoad 8 14 13,
    .opBitwiseXor 8 15 1 5,
    .opAccessChain 6 16 2 [15],
    .opLoad 8 17 16,
    .opIAdd 8 18 14 17,
    .opAccessChain 7 19 4 [1],
    .opStore 19 18
  ]

def twoWaveCfg : WorkgroupConfig := ⟨0, 2, by decide⟩

/-- **`#tooth` Missing `OpControlBarrier` Causes Cross-Wave Shared-LDS Data Race
    (`tooth_missing_barrier_causes_cross_wave_lds_race`)**:
    In a 2-wave (`64`-thread) workgroup where Wave `0` and Wave `1` exchange values via `lds[tid ^ 32]`:
    1. **Without `OpControlBarrier`** (concatenating `Phase0 ++ Phase1` into a single epoch), running
       Wave `0` to completion before Wave `1` (`schedWave0First`) vs running both waves through
       `Phase0` before `Phase1` (`schedPhased`) yields **distinct global outputs** (`10 ≠ 52`)!
    2. **With `OpControlBarrier(.workgroup, .workgroup, spirvSemWorkgroupAcqRel)`** separating
       `Phase0` and `Phase1`, Wave `0` blocks at the barrier until Wave `1` finishes `Phase0`, so
       putting Wave `0` first in the schedule STILL produces the **exact cross-wave sum `52`**! -/
theorem tooth_missing_barrier_causes_cross_wave_lds_race :
    let initMem : GpuMemState :=
      { lds := fun _ => 0
        ssbo := fun b idx => if b == 0 then (if idx < 32 then 10 else 42) else 0
        pushConsts := fun _ => 0 }
    let buggyNoBarrierProg := twoWavePhase0WriteLds ++ twoWavePhase1CrossWaveRead
    let schedWave0First := List.replicate 12 0 ++ List.replicate 12 1
    let schedInterleaved := List.replicate 4 0 ++ List.replicate 4 1 ++
                            List.replicate 8 0 ++ List.replicate 8 1
    let initSt := initWorkgroupExecState twoWaveReductionEnv twoWaveCfg initMem
    -- 1. Without OpControlBarrier, two valid 12-step-per-wave schedules disagree on outBuf[0]:
    (runInterleavedSchedule twoWaveReductionEnv twoWaveCfg buggyNoBarrierProg schedWave0First initSt).map
      (fun s => s.mem.ssbo 1 0) = .ok 10 ∧
    (runInterleavedSchedule twoWaveReductionEnv twoWaveCfg buggyNoBarrierProg schedInterleaved initSt).map
      (fun s => s.mem.ssbo 1 0) = .ok 52 ∧
    (runInterleavedSchedule twoWaveReductionEnv twoWaveCfg buggyNoBarrierProg schedWave0First initSt).map
      (fun s => s.mem.ssbo 1 0) ≠
    (runInterleavedSchedule twoWaveReductionEnv twoWaveCfg buggyNoBarrierProg schedInterleaved initSt).map
      (fun s => s.mem.ssbo 1 0) ∧
    -- 2. With OpControlBarrier separating the two epochs, Wave-0-first schedule produces 52 on both waves:
    (runMultiWaveEpochs twoWaveReductionEnv twoWaveCfg
      [twoWavePhase0WriteLds, twoWavePhase1CrossWaveRead]
      [List.replicate 5 0 ++ List.replicate 5 1, List.replicate 8 0 ++ List.replicate 8 1]
      initSt).map (fun s => (s.mem.ssbo 1 0, s.mem.ssbo 1 32)) = .ok (52, 52) := by
  decide

/-- **`#tooth` Single-Wave Wiped-LDS Execution Corrupts Multi-Wave Barrier Reductions
    (`tooth_single_wave_lds_wipe_corrupts_multiwave_reduction`)**:
    Wiping `lds := fun _ => 0` between waves (as in broken 1-wave-per-workgroup simulators) loses
    Wave `0`'s shared-memory writes before Wave `1` runs (`42 ≠ 52`), whereas persistent multi-wave
    `Workgroup` LDS preserves `52` across both Wave32 subgroups. -/
theorem tooth_single_wave_lds_wipe_corrupts_multiwave_reduction :
    let initMem : GpuMemState :=
      { lds := fun _ => 0
        ssbo := fun b idx => if b == 0 then (if idx < 32 then 10 else 42) else 0
        pushConsts := fun _ => 0 }
    let initSt := initWorkgroupExecState twoWaveReductionEnv twoWaveCfg initMem
    let wipedWave1Prog := twoWavePhase0WriteLds ++ twoWavePhase1CrossWaveRead
    (runMultiWaveEpochs twoWaveReductionEnv twoWaveCfg
      [twoWavePhase0WriteLds, twoWavePhase1CrossWaveRead]
      [canonicalEpochSchedule 2 5, canonicalEpochSchedule 2 8] initSt).map
      (fun s => s.mem.ssbo 1 32) = .ok 52 ∧
    (runInterleavedSchedule twoWaveReductionEnv twoWaveCfg wipedWave1Prog
      (List.replicate 12 1) initSt).map (fun s => s.mem.ssbo 1 32) = .ok 42 ∧
    (runMultiWaveEpochs twoWaveReductionEnv twoWaveCfg
      [twoWavePhase0WriteLds, twoWavePhase1CrossWaveRead]
      [canonicalEpochSchedule 2 5, canonicalEpochSchedule 2 8] initSt).map
      (fun s => s.mem.ssbo 1 32) ≠
    (runInterleavedSchedule twoWaveReductionEnv twoWaveCfg wipedWave1Prog
      (List.replicate 12 1) initSt).map (fun s => s.mem.ssbo 1 32) := by
  decide

/-! ### `SIMT-CT` Constant-Time Side-Channel Model & 32-Bank RDNA2 LDS Conflict Freedom -/

/-- RDNA2 `64 KiB` LDS physical bank index (`32` banks × `4`-byte dwords):
    `ldsBank(byteAddr) = (byteAddr / 4) % 32`. -/
def ldsBank (byteAddr : Nat) : Nat :=
  (byteAddr / 4) % 32

/-- **`LdsBankConflictFree32`**: across all 32 lanes `lane ∈ [0, 32)` of a Wave32 subgroup,
    `ldsBank ∘ byteAddrFn` is injective (`32` lanes map to `32` distinct LDS banks -> `0` bank
    serialization!). -/
def LdsBankConflictFree32 (byteAddrFn : Nat → Nat) : Prop :=
  ∀ l₁ l₂ : Nat, l₁ < wave32Lanes → l₂ < wave32Lanes →
    ldsBank (byteAddrFn l₁) = ldsBank (byteAddrFn l₂) → l₁ = l₂

/-- Count how many lanes `l < 32` collide with lane `0` in the same LDS bank at distinct byte
    addresses (`1` = conflict-free; `32` = worst-case 32-way bank serialization). -/
def ldsLane0BankWays (byteAddrFn : Nat → Nat) : Nat :=
  ((List.range 32).filter fun l =>
    decide (ldsBank (byteAddrFn l) = ldsBank (byteAddrFn 0))).length

private theorem pow_two_dvd_of_odd :
    ∀ (k g c : Nat), c % 2 = 1 → 2 ^ k ∣ g * c → 2 ^ k ∣ g
  | 0, g, _, _, _ => Nat.one_dvd g
  | k + 1, g, c, hodd, hdvd => by
    have h2prime : IsPrimeNat 2 := ⟨by decide, fun d hd => by
      have hpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by decide)
      have hle : d ≤ 2 := Nat.le_of_dvd (by decide) hd
      omega⟩
    have hnc : ¬ (2 ∣ c) := fun hc => by obtain ⟨t, rfl⟩ := hc; omega
    have h2dvd : 2 ∣ g * c := by
      rw [Nat.pow_succ] at hdvd
      exact Nat.dvd_trans (Nat.dvd_mul_left 2 (2 ^ k)) hdvd
    obtain ⟨g', rfl⟩ := h2prime.dvd_mul (Nat.mul_comm g c ▸ h2dvd) hnc
    have hk : 2 ^ k ∣ g' * c := by
      obtain ⟨u, hu⟩ := hdvd
      refine ⟨u, ?_⟩
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2] at hu
      have hAssoc : 2 * (g' * c) = 2 * (2 ^ k * u) := by
        calc 2 * (g' * c) = 2 * g' * c := (Nat.mul_assoc 2 g' c).symm
        _ = 2 * 2 ^ k * u := hu
        _ = 2 * (2 ^ k * u) := Nat.mul_assoc 2 (2 ^ k) u
      exact (Nat.mul_right_inj (by decide : 2 ≠ 0)).mp hAssoc
    exact Nat.mul_dvd_mul_left 2 (pow_two_dvd_of_odd k g' c hodd hk)

private theorem odd_mul_sub_not_dvd_32 {s d : Nat} (hOdd : s % 2 = 1) (hdPos : 0 < d) (hdLt : d < 32) :
    (s * d) % 32 ≠ 0 := by
  intro hMod0
  have hdvd : 2 ^ 5 ∣ d * s := by
    rw [Nat.mul_comm]
    exact Nat.dvd_of_mod_eq_zero hMod0
  have hd32 : 32 ∣ d := pow_two_dvd_of_odd 5 d s hOdd hdvd
  have hle := Nat.le_of_dvd hdPos hd32
  omega

/-- **Universal Odd-Stride Wave32 LDS Bank-Conflict-Free Theorem (`odd_stride_lds_bank_conflict_free`)**:
    For **every** base dword offset `baseDword` and **every** odd dword stride `stride` (`stride % 2 = 1`,
    including unit stride `1`, `+1`-padded 32×32 transpose stride `33`, and `+1`-padded Poseidon2
    width-12 stride `13`), `byteAddr(lane) = 4 * (baseDword + stride * lane)` hits `32` pairwise
    distinct LDS banks across every Wave32 subgroup (`0` bank conflicts)! -/
theorem odd_stride_lds_bank_conflict_free (baseDword stride : Nat) (hOdd : stride % 2 = 1) :
    LdsBankConflictFree32 (fun lane => 4 * (baseDword + stride * lane)) := by
  intro l₁ l₂ hl₁ hl₂ hBank
  unfold wave32Lanes at hl₁ hl₂
  unfold ldsBank at hBank
  have hDiv1 : 4 * (baseDword + stride * l₁) / 4 = baseDword + stride * l₁ := by omega
  have hDiv2 : 4 * (baseDword + stride * l₂) / 4 = baseDword + stride * l₂ := by omega
  rw [hDiv1, hDiv2] at hBank
  by_cases hEq : l₁ = l₂
  · exact hEq
  · by_cases hlt : l₁ < l₂
    · have hdPos : 0 < l₂ - l₁ := by omega
      have hdLt : l₂ - l₁ < 32 := by omega
      have hDiff : baseDword + stride * l₂ = (baseDword + stride * l₁) + stride * (l₂ - l₁) := by
        rw [Nat.mul_sub_left_distrib]
        have hle : stride * l₁ ≤ stride * l₂ := Nat.mul_le_mul_left stride (by omega)
        omega
      have hMod0 : (stride * (l₂ - l₁)) % 32 = 0 := by
        have h1 := Nat.div_add_mod (baseDword + stride * l₁) 32
        have h2 := Nat.div_add_mod (baseDword + stride * l₂) 32
        have h3 := Nat.div_add_mod (stride * (l₂ - l₁)) 32
        omega
      exact False.elim (odd_mul_sub_not_dvd_32 hOdd hdPos hdLt hMod0)
    · have hgt : l₂ < l₁ := by omega
      have hdPos : 0 < l₁ - l₂ := by omega
      have hdLt : l₁ - l₂ < 32 := by omega
      have hDiff : baseDword + stride * l₁ = (baseDword + stride * l₂) + stride * (l₁ - l₂) := by
        rw [Nat.mul_sub_left_distrib]
        have hle : stride * l₂ ≤ stride * l₁ := Nat.mul_le_mul_left stride (by omega)
        omega
      have hMod0 : (stride * (l₁ - l₂)) % 32 = 0 := by
        have h1 := Nat.div_add_mod (baseDword + stride * l₁) 32
        have h2 := Nat.div_add_mod (baseDword + stride * l₂) 32
        have h3 := Nat.div_add_mod (stride * (l₁ - l₂)) 32
        omega
      exact False.elim (odd_mul_sub_not_dvd_32 hOdd hdPos hdLt hMod0)

/-- Bank-skewed shared-LDS dword offset for 2-level multi-wave Wave32 Merkle tree nodes (`8` dwords =
    `4 × u64` per node): `merkleSkewedLdsDword idx = 9 * idx + idx / 32`. -/
def merkleSkewedLdsDword (idx : Nat) : Nat :=
  9 * idx + idx / 32

theorem merkleSkewedLdsDword_slots_disjoint {i₁ i₂ d₁ d₂ : Nat}
    (hd₁ : d₁ < 8) (hd₂ : d₂ < 8) (hne : i₁ ≠ i₂) :
    merkleSkewedLdsDword i₁ + d₁ ≠ merkleSkewedLdsDword i₂ + d₂ := by
  unfold merkleSkewedLdsDword
  by_cases hlt : i₁ < i₂
  · have hDiv : i₁ / 32 ≤ i₂ / 32 := Nat.div_le_div_right (by omega)
    omega
  · have hgt : i₂ < i₁ := by omega
    have hDiv : i₂ / 32 ≤ i₁ / 32 := Nat.div_le_div_right (by omega)
    omega

/-- **2-Epoch Skewed Merkle LDS Bank-Conflict-Free Theorem (`merkle_skewed_lds_bank_conflict_free_both_epochs`)**:
    For **every** wave `w : Nat` and **every** dword sub-offset `d < 8`, `merkleSkewedLdsDword`:
    1. Is **32-bank conflict-free in Epoch 0** (`idx = 32 * w + lane`), AND
    2. Is **32-bank conflict-free in Epoch 1** (`idx = 2 * (32 * w + lane) + childBit` for BOTH
       left child `childBit = 0` and right child `childBit = 1`)! -/
theorem merkle_skewed_lds_bank_conflict_free_both_epochs (w d : Nat) :
    LdsBankConflictFree32 (fun lane => 4 * (merkleSkewedLdsDword (w * 32 + lane) + d)) ∧
    (∀ childBit : Nat, childBit < 2 →
      LdsBankConflictFree32 (fun lane => 4 * (merkleSkewedLdsDword (2 * (w * 32 + lane) + childBit) + d))) := by
  refine ⟨?_, ?_⟩
  · intro l₁ l₂ hl₁ hl₂ hBank
    unfold wave32Lanes at hl₁ hl₂
    dsimp only at hBank
    have hEqFn : ∀ l < 32, 4 * (merkleSkewedLdsDword (w * 32 + l) + d) =
        4 * ((289 * w + d) + 9 * l) := by
      intro l _; unfold merkleSkewedLdsDword
      have hDiv : (w * 32 + l) / 32 = w := by omega
      omega
    rw [hEqFn l₁ hl₁, hEqFn l₂ hl₂] at hBank
    exact odd_stride_lds_bank_conflict_free (289 * w + d) 9 rfl l₁ l₂ hl₁ hl₂ hBank
  · intro c hc l₁ l₂ hl₁ hl₂ hBank
    unfold wave32Lanes at hl₁ hl₂
    unfold ldsBank merkleSkewedLdsDword at hBank
    have h4_1 : 4 * (9 * (2 * (w * 32 + l₁) + c) + (2 * (w * 32 + l₁) + c) / 32 + d) / 4 =
        9 * (2 * (w * 32 + l₁) + c) + (2 * (w * 32 + l₁) + c) / 32 + d := by omega
    have h4_2 : 4 * (9 * (2 * (w * 32 + l₂) + c) + (2 * (w * 32 + l₂) + c) / 32 + d) / 4 =
        9 * (2 * (w * 32 + l₂) + c) + (2 * (w * 32 + l₂) + c) / 32 + d := by omega
    rw [h4_1, h4_2] at hBank
    -- Notice `(2 * (w * 32 + l) + c) / 32 = 2 * w + l / 16` since `c < 2`!
    have hDivL₁ : (2 * (w * 32 + l₁) + c) / 32 = 2 * w + l₁ / 16 := by omega
    have hDivL₂ : (2 * (w * 32 + l₂) + c) / 32 = 2 * w + l₂ / 16 := by omega
    rw [hDivL₁, hDivL₂] at hBank
    -- Now modulo 2, `(18 * l + l / 16)` has parity `l / 16 ∈ {0, 1}`, so `l₁ / 16 = l₂ / 16`!
    -- Once `l₁ / 16 = l₂ / 16`, `18 * l₁ ≡ 18 * l₂ (mod 32)` -> `9 * (l₁ % 16) ≡ 9 * (l₂ % 16) (mod 16)`!
    -- Since `l₁ < 32` and `l₂ < 32` are bounded, `omega` closes the linear/mod-32 case split directly!
    have hq₁ : l₁ / 16 = 0 ∨ l₁ / 16 = 1 := by omega
    have hq₂ : l₂ / 16 = 0 ∨ l₂ / 16 = 1 := by omega
    -- Check parity first: `(A + 18 * l₁ + l₁ / 16) % 2 = (A + 18 * l₂ + l₂ / 16) % 2`
    have hPar : (9 * (2 * (w * 32 + l₁) + c) + (2 * w + l₁ / 16) + d) % 2 =
                (9 * (2 * (w * 32 + l₂) + c) + (2 * w + l₂ / 16) + d) % 2 := by omega
    have hSameHalf : l₁ / 16 = l₂ / 16 := by omega
    rw [hSameHalf] at hBank
    -- Now `(base + 18 * l₁) % 32 = (base + 18 * l₂) % 32` with `|l₁ - l₂| < 16`!
    -- Since `9` is odd, `18 * k % 32 = 0` for `0 ≤ k < 16` implies `k = 0`!
    by_cases hEq : l₁ = l₂
    · exact hEq
    · by_cases hlt : l₁ < l₂
      · have hkLt : l₂ - l₁ < 16 := by omega
        have hMod32 : (18 * (l₂ - l₁)) % 32 = 0 := by
          have d1 := Nat.div_add_mod (9 * (2 * (w * 32 + l₁) + c) + (2 * w + l₂ / 16) + d) 32
          have d2 := Nat.div_add_mod (9 * (2 * (w * 32 + l₂) + c) + (2 * w + l₂ / 16) + d) 32
          have d3 := Nat.div_add_mod (18 * (l₂ - l₁)) 32
          have hSub : 9 * (2 * (w * 32 + l₂) + c) =
              9 * (2 * (w * 32 + l₁) + c) + 18 * (l₂ - l₁) := by
            rw [Nat.mul_sub_left_distrib]
            have : 18 * l₁ ≤ 18 * l₂ := Nat.mul_le_mul_left 18 (by omega)
            omega
          omega
        have hMod32' : (9 * (2 * (l₂ - l₁))) % 32 = 0 := by
          have : 9 * (2 * (l₂ - l₁)) = 18 * (l₂ - l₁) := by omega
          rwa [this]
        exact False.elim (odd_mul_sub_not_dvd_32 (s := 9) (d := 2 * (l₂ - l₁)) rfl (by omega) (by omega) hMod32')
      · have hkLt : l₁ - l₂ < 16 := by omega
        have hMod32 : (18 * (l₁ - l₂)) % 32 = 0 := by
          have d1 := Nat.div_add_mod (9 * (2 * (w * 32 + l₁) + c) + (2 * w + l₂ / 16) + d) 32
          have d2 := Nat.div_add_mod (9 * (2 * (w * 32 + l₂) + c) + (2 * w + l₂ / 16) + d) 32
          have d3 := Nat.div_add_mod (18 * (l₁ - l₂)) 32
          have hSub : 9 * (2 * (w * 32 + l₁) + c) =
              9 * (2 * (w * 32 + l₂) + c) + 18 * (l₁ - l₂) := by
            rw [Nat.mul_sub_left_distrib]
            have : 18 * l₂ ≤ 18 * l₁ := Nat.mul_le_mul_left 18 (by omega)
            omega
          omega
        have hMod32' : (9 * (2 * (l₁ - l₂))) % 32 = 0 := by
          have : 9 * (2 * (l₁ - l₂)) = 18 * (l₁ - l₂) := by omega
          rwa [this]
        exact False.elim (odd_mul_sub_not_dvd_32 (s := 9) (d := 2 * (l₁ - l₂)) rfl (by omega) (by omega) hMod32')

/-- **`#tooth` Unpadded Stride-32 LDS Access Causes Worst-Case 32-Way Bank Serialization
    (`tooth_stride32_lds_causes_32way_bank_conflict`)**:
    Accessing `byteAddr(lane) = 4 * (baseDword + 32 * lane)` across a Wave32 subgroup maps all `32`
    distinct lane addresses into the single LDS bank `baseDword % 32` (`ldsLane0BankWays = 32` and
    `¬ LdsBankConflictFree32`), whereas `+1` row padding (`stride = 33`) achieves `ldsLane0BankWays = 1`
    and `LdsBankConflictFree32`! -/
theorem tooth_stride32_lds_causes_32way_bank_conflict (baseDword : Nat) :
    let unpadded := fun lane => 4 * (baseDword + 32 * lane)
    let padded33 := fun lane => 4 * (baseDword + 33 * lane)
    (∀ lane < 32, ldsBank (unpadded lane) = baseDword % 32) ∧
    ldsLane0BankWays unpadded = 32 ∧
    ¬ LdsBankConflictFree32 unpadded ∧
    LdsBankConflictFree32 padded33 := by
  refine ⟨?_, ?_, ?_, odd_stride_lds_bank_conflict_free baseDword 33 rfl⟩
  · intro lane _
    unfold ldsBank
    have h4 : 4 * (baseDword + 32 * lane) / 4 = baseDword + 32 * lane := by omega
    rw [h4]
    omega
  · unfold ldsLane0BankWays
    have hAll : ∀ l ∈ List.range 32,
        decide (ldsBank (4 * (baseDword + 32 * l)) = ldsBank (4 * (baseDword + 32 * 0))) = true := by
      intro l _
      unfold ldsBank
      have h1 : 4 * (baseDword + 32 * l) / 4 = baseDword + 32 * l := by omega
      have h2 : 4 * (baseDword + 32 * 0) / 4 = baseDword := by omega
      rw [h1, h2]
      simp [Nat.add_mul_mod_self_left]
    rw [List.filter_eq_self.mpr hAll, List.length_range]
  · intro hFree
    have h01 := hFree 0 1 (by decide) (by decide) (by
      unfold ldsBank
      have h1 : 4 * (baseDword + 32 * 0) / 4 = baseDword := by omega
      have h2 : 4 * (baseDword + 32 * 1) / 4 = baseDword + 32 := by omega
      rw [h1, h2]; omega)
    omega

/-! ### Static `SIMT-CT` Information-Flow Type System & Leakage-Trace Noninterference -/

/-- Two-point information-flow lattice: `pub` (public dispatch geometry / constants) ≤ `sec` (witness). -/
inductive SecLabel where
  | pub
  | sec
  deriving DecidableEq, Repr

def SecLabel.join : SecLabel → SecLabel → SecLabel
  | .pub, .pub => .pub
  | _, _ => .sec

/-- Hardware side-channel observation emitted by one Wave32 instruction step:
    - `pc` : instruction address
    - `activeMask` : 32-lane `EXEC_LO` active predicate (`List Bool` of length 32)
    - `memTraces` : per-lane memory access descriptor `(storageClass, binding, elemIdx)` (exposes
      both global VMEM coalescing spread AND physical LDS bank `(4 * elemIdx / 4) % 32`!). -/
structure SimtWaveObs where
  pc : Nat
  activeMask : List Bool
  memTraces : List (Option (SpirvStorageClass × Nat × Nat))
  deriving DecidableEq, Repr

def observeLaneMem (regs : Nat → SpirvVal) : SpirvInst → Option (SpirvStorageClass × Nat × Nat)
  | .opLoad _ _ ptrId | .opStore ptrId _ =>
    match regs ptrId.toNat with
    | .vPtr sc binding elemIdx _ => some (sc, binding, elemIdx)
    | _ => none
  | _ => none

def stepWaveObs (wSt : Wave32State) (inst : SpirvInst) : SimtWaveObs :=
  { pc := wSt.pc
    activeMask := (List.range wave32Lanes).map wSt.execMask
    memTraces := (List.range wave32Lanes).map fun lane =>
      if wSt.execMask lane then observeLaneMem (wSt.laneRegs lane) inst else none }

/-- Collect the complete Wave32 hardware side-channel observation trace across a straight-line
    epoch `prog` starting from `(wSt, mem)`. -/
def runWaveWithObs (env : SpirvModuleEnv) (prog : List SpirvInst) :
    Nat → Wave32State → GpuMemState → List SimtWaveObs
  | 0, _, _ => []
  | fuel + 1, wSt, mem =>
    if wSt.atBarrier then []
    else
      match prog[wSt.pc]? with
      | none => []
      | some inst =>
        let obs := stepWaveObs wSt inst
        match stepWave32One env prog wSt mem with
        | .error _ => [obs]
        | .ok (wSt', mem') => obs :: runWaveWithObs env prog fuel wSt' mem'

/-- Static `SIMT-CT` typing environment:
    - `ssboSec binding` classifies each `StorageBuffer` as `pub` or `sec`
    - `ldsSec` classifies `Workgroup` LDS contents (`sec` when holding witness intermediates!)
    - `regSec ssaId` assigns a `SecLabel` to every SSA `%id` (`pub` values must match across
      all public-equivalent memories!). -/
structure SimtCtPolicy where
  ssboSec : Nat → SecLabel
  ldsSec : SecLabel
  regSec : Nat → SecLabel

/-- Static `SIMT-CT` instruction checker:
    1. Zero `EXEC`-mask divergence: no branches (`opBranchConditional`, `opBranch`) inside straight-line
       epochs; conditional selection uses branchless `OpSelect` (`v_cndmask_b32`)!
    2. Public-affine addressing: every `OpAccessChain` index `%idx` is `pub`, and every pointer
       register `%ptr` is `pub` (so `OpLoad` / `OpStore` addresses never depend on secrets!).
    3. Monotone label propagation on all fixed-latency VALU operations (`OpUMulExtended`, `OpIAdd`,
       `OpISub`, `OpIMul`, `OpBitwise*`, `OpShift*`, `OpSelect`, comparisons). -/
def checkInstSimtCt (pol : SimtCtPolicy) : SpirvInst → Bool
  | .opAccessChain _ resId baseId [idxId] =>
    (pol.regSec baseId.toNat == .pub) &&
    (pol.regSec idxId.toNat == .pub) &&
    (pol.regSec resId.toNat == .pub)
  | .opAccessChain _ _ _ _ => false
  | .opLoad _ _ ptrId =>
    pol.regSec ptrId.toNat == .pub
  | .opStore ptrId _ =>
    pol.regSec ptrId.toNat == .pub
  | .opCompositeExtract _ resId compId _ =>
    (pol.regSec resId.toNat == .sec) || (pol.regSec compId.toNat == .pub)
  | .opUConvert _ resId valId =>
    (pol.regSec resId.toNat == .sec) || (pol.regSec valId.toNat == .pub)
  | .opIAdd _ resId aId bId
  | .opISub _ resId aId bId
  | .opIMul _ resId aId bId
  | .opUMulExtended _ resId aId bId
  | .opIEqual _ resId aId bId
  | .opUGreaterThanEqual _ resId aId bId
  | .opULessThan _ resId aId bId
  | .opShiftRightLogical _ resId aId bId
  | .opShiftLeftLogical _ resId aId bId
  | .opBitwiseXor _ resId aId bId
  | .opBitwiseOr _ resId aId bId
  | .opBitwiseAnd _ resId aId bId =>
    (pol.regSec resId.toNat == .sec) ||
    ((pol.regSec aId.toNat == .pub) && (pol.regSec bId.toNat == .pub))
  | .opSelect _ resId cId tId fId =>
    (pol.regSec resId.toNat == .sec) ||
    ((pol.regSec cId.toNat == .pub) && (pol.regSec tId.toNat == .pub) && (pol.regSec fId.toNat == .pub))
  | .opControlBarrier .workgroup .workgroup sem => sem == spirvSemWorkgroupAcqRel
  | .opLabel _ => true
  | _ => false

/-- Strict `SIMT-CT` check refining `OpLoad`, `OpStore`, and `OpAccessChain` label soundness:
    - `OpLoad` into a `pub` register requires a `pub` source memory space;
    - `OpStore` of a `sec` register requires a `sec` target memory space (no `sec -> pub` flow);
    - `OpAccessChain` requires `pub` base pointer and `pub` index with consistent pointer metadata. -/
def checkInstSimtCtStrict (env : SpirvModuleEnv) (pol : SimtCtPolicy) (inst : SpirvInst) : Bool :=
  match inst with
  | .opLoad _ resId ptrId =>
    (pol.regSec ptrId.toNat == .pub) &&
    (match pol.regSec resId.toNat with
     | .sec => true
     | .pub =>
       match env.ptrInfo ptrId.toNat with
       | some (.pushConstant, _, _) => true
       | some (.storageBuffer, b, _) => pol.ssboSec b == .pub
       | some (.workgroup, _, _) => pol.ldsSec == .pub
       | _ => false)
  | .opStore ptrId valId =>
    (pol.regSec ptrId.toNat == .pub) &&
    (match pol.regSec valId.toNat with
     | .pub => true
     | .sec =>
       match env.ptrInfo ptrId.toNat with
       | some (.storageBuffer, b, _) => pol.ssboSec b == .sec
       | some (.workgroup, _, _) => pol.ldsSec == .sec
       | _ => false)
  | .opAccessChain tyId resId baseId [idxId] =>
    (pol.regSec baseId.toNat == .pub) &&
    (pol.regSec idxId.toNat == .pub) &&
    (pol.regSec resId.toNat == .pub) &&
    (match env.ptrInfo baseId.toNat, env.ptrInfo resId.toNat, env.ptrInfo tyId.toNat with
     | some (sc1, b1, w1), some (sc2, b2, w2), some (sc3, b3, w3) =>
       decide (sc1 = sc2 ∧ b1 = b2 ∧ w1 = w2 ∧ sc1 = sc3 ∧ b1 = b3 ∧ w1 = w3)
     | _, _, _ => false)
  | .opAccessChain _ _ _ _ => false
  | other => checkInstSimtCt pol other

def checkProgSimtCt (env : SpirvModuleEnv) (pol : SimtCtPolicy) (prog : List SpirvInst) : Bool :=
  prog.all (checkInstSimtCtStrict env pol)

/-- Two `SpirvVal`s have matching runtime tag/width shape (`vU32` vs `vU32`, `vU64` vs `vU64`, etc.)
    so secret data differences never induce type-error divergence! -/
def SpirvVal.SameShape : SpirvVal → SpirvVal → Prop
  | .vUndef, .vUndef => True
  | .vBool _, .vBool _ => True
  | .vU32 _, .vU32 _ => True
  | .vU64 _, .vU64 _ => True
  | .vPair32 _ _, .vPair32 _ _ => True
  | .vPair64 _ _, .vPair64 _ _ => True
  | .vPtr sc1 b1 i1 w1, .vPtr sc2 b2 i2 w2 => sc1 = sc2 ∧ b1 = b2 ∧ i1 = i2 ∧ w1 = w2
  | _, _ => False

theorem SpirvVal.sameShape_refl (v : SpirvVal) : SpirvVal.SameShape v v := by
  cases v <;> simp [SpirvVal.SameShape]

/-- Static consistency of scalar constants in `SpirvModuleEnv` (constants are scalar, never raw pointers). -/
def ScalarConstEnv (env : SpirvModuleEnv) : Prop :=
  ∀ id sc b off w, env.initConst id ≠ .vPtr sc b off w

/-- Low-equivalence (`pub`-indistinguishability) of memories and Wave32 states under `pol`. -/
def MemLowEq (pol : SimtCtPolicy) (m₁ m₂ : GpuMemState) : Prop :=
  m₁.pushConsts = m₂.pushConsts ∧
  (pol.ldsSec = .pub → m₁.lds = m₂.lds) ∧
  (∀ b : Nat, pol.ssboSec b = .pub → m₁.ssbo b = m₂.ssbo b)

def LaneRegsLowEq (env : SpirvModuleEnv) (pol : SimtCtPolicy) (r₁ r₂ : Nat → SpirvVal) : Prop :=
  (∀ id : Nat, SpirvVal.SameShape (r₁ id) (r₂ id)) ∧
  (∀ id : Nat, pol.regSec id = .pub → r₁ id = r₂ id) ∧
  (∀ id sc b off w, r₁ id = .vPtr sc b off w →
    pol.regSec id = .pub → env.ptrInfo id = some (sc, b, w))

def WaveLowEq (env : SpirvModuleEnv) (pol : SimtCtPolicy) (w₁ w₂ : Wave32State) : Prop :=
  w₁.pc = w₂.pc ∧
  w₁.atBarrier = w₂.atBarrier ∧
  w₁.execMask = w₂.execMask ∧
  (∀ lane < wave32Lanes, LaneRegsLowEq env pol (w₁.laneRegs lane) (w₂.laneRegs lane))

theorem initWave_lowEq (env : SpirvModuleEnv) (pol : SimtCtPolicy) (cfg : WorkgroupConfig)
    (hScalar : ScalarConstEnv env) :
    ∀ w : Nat,
      let wSt : Wave32State :=
        { pc := 0, execMask := allActive32, laneRegs := fun l => initLaneRegs env cfg w l, atBarrier := false }
      WaveLowEq env pol wSt wSt := by
  intro w
  refine ⟨rfl, rfl, rfl, fun lane _ => ⟨fun _ => SpirvVal.sameShape_refl _, fun _ _ => rfl, ?_⟩⟩
  intro id sc b off width hEq _
  dsimp only [initLaneRegs] at hEq
  cases hb : env.builtIns id with
  | some bi => rw [hb] at hEq; cases bi <;> cases hEq
  | none =>
    rw [hb] at hEq
    cases hp : env.ptrInfo id with
    | some info =>
      rw [hp] at hEq
      rcases info with ⟨sc', b', w'⟩
      cases hEq
      rfl
    | none =>
      rw [hp] at hEq
      exact False.elim (hScalar id sc b off width hEq)

private theorem writeFn_laneRegsLowEq {env : SpirvModuleEnv} {pol : SimtCtPolicy}
    {r₁ r₂ : Nat → SpirvVal} (hLow : LaneRegsLowEq env pol r₁ r₂)
    (dst : Nat) {v₁ v₂ : SpirvVal}
    (hShape : SpirvVal.SameShape v₁ v₂)
    (hPubEq : pol.regSec dst = .pub → v₁ = v₂)
    (hPtr : ∀ sc b off w, v₁ = .vPtr sc b off w → pol.regSec dst = .pub →
      env.ptrInfo dst = some (sc, b, w)) :
    LaneRegsLowEq env pol (writeFn r₁ dst v₁) (writeFn r₂ dst v₂) := by
  refine ⟨?_, ?_, ?_⟩
  · intro id
    unfold writeFn
    by_cases hid : id = dst
    · subst hid; simpa using hShape
    · simp [hid]; exact hLow.1 id
  · intro id hPub
    unfold writeFn
    by_cases hid : id = dst
    · subst hid; simp [hPubEq hPub]
    · simp [hid, hLow.2.1 id hPub]
  · intro id sc b off w hEq hPub
    unfold writeFn at hEq
    by_cases hid : id = dst
    · subst hid
      simp only [↓reduceIte] at hEq
      exact hPtr sc b off w hEq hPub
    · simp only [hid, ↓reduceIte] at hEq
      exact hLow.2.2 id sc b off w hEq hPub

private theorem evalBinU32U64_lowEq {env : SpirvModuleEnv} {pol : SimtCtPolicy}
    {r₁ r₂ : Nat → SpirvVal} (resId aId bId : UInt32)
    (f32 : UInt32 → UInt32 → SpirvVal) (f64 : UInt64 → UInt64 → SpirvVal)
    (hSh32 : ∀ x₁ y₁ x₂ y₂, SpirvVal.SameShape (f32 x₁ y₁) (f32 x₂ y₂))
    (hNoPtr32 : ∀ x y sc b o w, f32 x y ≠ .vPtr sc b o w)
    (hSh64 : ∀ x₁ y₁ x₂ y₂, SpirvVal.SameShape (f64 x₁ y₁) (f64 x₂ y₂))
    (hNoPtr64 : ∀ x y sc b o w, f64 x y ≠ .vPtr sc b o w)
    (hRegs : LaneRegsLowEq env pol r₁ r₂)
    (hCt : ((pol.regSec resId.toNat == .sec) ||
            ((pol.regSec aId.toNat == .pub) && (pol.regSec bId.toNat == .pub))) = true) :
    match (match r₁ aId.toNat, r₁ bId.toNat with
           | .vU32 a, .vU32 b => Except.ok (resId.toNat, f32 a b)
           | .vU64 a, .vU64 b => Except.ok (resId.toNat, f64 a b)
           | _, _ => Except.error SimtExecError.typeMismatch),
          (match r₂ aId.toNat, r₂ bId.toNat with
           | .vU32 a, .vU32 b => Except.ok (resId.toNat, f32 a b)
           | .vU64 a, .vU64 b => Except.ok (resId.toNat, f64 a b)
           | _, _ => Except.error SimtExecError.typeMismatch) with
    | .error e₁, .error e₂ => e₁ = e₂
    | .ok (d₁, v₁), .ok (d₂, v₂) =>
      d₁ = d₂ ∧
      SpirvVal.SameShape v₁ v₂ ∧
      (pol.regSec d₁ = .pub → v₁ = v₂) ∧
      (∀ sc b off w, v₁ = .vPtr sc b off w → pol.regSec d₁ = .pub →
        env.ptrInfo d₁ = some (sc, b, w))
    | _, _ => False := by
  have hShA := hRegs.1 aId.toNat
  have hShB := hRegs.1 bId.toNat
  have hPubOps : pol.regSec resId.toNat = .pub → r₁ aId.toNat = r₂ aId.toNat ∧ r₁ bId.toNat = r₂ bId.toNat := by
    intro hPub
    rw [hPub] at hCt
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hCt
    rcases hCt with hBad | ⟨ha, hb⟩
    · cases hBad
    · exact ⟨hRegs.2.1 _ ha, hRegs.2.1 _ hb⟩
  cases ha1 : r₁ aId.toNat <;> cases ha2 : r₂ aId.toNat <;>
    (rw [ha1, ha2] at hShA; try cases hShA) <;>
  cases hb1 : r₁ bId.toNat <;> cases hb2 : r₂ bId.toNat <;>
    (rw [hb1, hb2] at hShB; try cases hShB) <;>
  dsimp only
  · refine ⟨rfl, hSh32 _ _ _ _, fun hPub => ?_, fun sc b off w hPtr _ => False.elim (hNoPtr32 _ _ sc b off w hPtr)⟩
    obtain ⟨ea, eb⟩ := hPubOps hPub
    rw [ha1, ha2] at ea; cases ea
    rw [hb1, hb2] at eb; cases eb
    rfl
  · refine ⟨rfl, hSh64 _ _ _ _, fun hPub => ?_, fun sc b off w hPtr _ => False.elim (hNoPtr64 _ _ sc b off w hPtr)⟩
    obtain ⟨ea, eb⟩ := hPubOps hPub
    rw [ha1, ha2] at ea; cases ea
    rw [hb1, hb2] at eb; cases eb
    rfl
  all_goals rfl

private theorem evalLanePureInst_lowEq {env : SpirvModuleEnv} {pol : SimtCtPolicy}
    {m₁ m₂ : GpuMemState} {r₁ r₂ : Nat → SpirvVal} {inst : SpirvInst}
    (hMem : MemLowEq pol m₁ m₂)
    (hRegs : LaneRegsLowEq env pol r₁ r₂)
    (hCt : checkInstSimtCtStrict env pol inst = true)
    (hNotStore : ∀ p v, inst ≠ .opStore p v)
    (hNotBarrier : ∀ es ms sem, inst ≠ .opControlBarrier es ms sem)
    (hNotLabel : ∀ l, inst ≠ .opLabel l) :
    match evalLanePureInst env m₁ r₁ inst, evalLanePureInst env m₂ r₂ inst with
    | .error e₁, .error e₂ => e₁ = e₂
    | .ok (d₁, v₁), .ok (d₂, v₂) =>
      d₁ = d₂ ∧
      SpirvVal.SameShape v₁ v₂ ∧
      (pol.regSec d₁ = .pub → v₁ = v₂) ∧
      (∀ sc b off w, v₁ = .vPtr sc b off w → pol.regSec d₁ = .pub →
        env.ptrInfo d₁ = some (sc, b, w))
    | _, _ => False := by
  cases inst with
  | opStore p v => exact False.elim (hNotStore p v rfl)
  | opControlBarrier es ms sem => exact False.elim (hNotBarrier es ms sem rfl)
  | opLabel l => exact False.elim (hNotLabel l rfl)
  | opLoopMerge _ _ _ | opSelectionMerge _ _ | opBranch _ | opBranchConditional _ _ _ =>
    simp [checkInstSimtCtStrict, checkInstSimtCt] at hCt
  | opAccessChain tyId resId baseId indices =>
    cases indices with
    | nil => simp [checkInstSimtCtStrict] at hCt
    | cons idxId rest =>
      cases rest with
      | cons _ _ => simp [checkInstSimtCtStrict] at hCt
      | nil =>
        dsimp only [checkInstSimtCtStrict] at hCt
        simp only [Bool.and_eq_true, beq_iff_eq] at hCt
        rcases hCt with ⟨⟨⟨hBasePub, hIdxPub⟩, _⟩, hPtrMeta⟩
        have hBaseEq := hRegs.2.1 baseId.toNat hBasePub
        have hIdxEq := hRegs.2.1 idxId.toNat hIdxPub
        dsimp only [evalLanePureInst]
        rw [← hBaseEq, ← hIdxEq]
        cases hB : r₁ baseId.toNat with
        | vPtr sc binding baseOff elemW =>
          cases hI : r₁ idxId.toNat with
          | vU32 idx =>
            refine ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, fun _ => rfl, ?_⟩
            intro sc' b' off' w' hEq _
            injection hEq with hsc hb _ hw
            subst hsc; subst hb; subst hw
            have hInfoBase := hRegs.2.2 baseId.toNat _ _ _ _ hB hBasePub
            rw [hInfoBase] at hPtrMeta
            cases hResInfo : env.ptrInfo resId.toNat with
            | none => rw [hResInfo] at hPtrMeta; simp at hPtrMeta
            | some p2 =>
              cases hTyInfo : env.ptrInfo tyId.toNat with
              | none => rw [hResInfo, hTyInfo] at hPtrMeta; simp at hPtrMeta
              | some p3 =>
                rw [hResInfo, hTyInfo] at hPtrMeta
                rcases p2 with ⟨sc2, b2, w2⟩
                rcases p3 with ⟨sc3, b3, w3⟩
                simp only [decide_eq_true_eq] at hPtrMeta
                rcases hPtrMeta with ⟨rfl, rfl, rfl, _, _, rfl⟩
                simp [hTyInfo]
          | vU64 idx =>
            refine ⟨rfl, ⟨rfl, rfl, rfl, rfl⟩, fun _ => rfl, ?_⟩
            intro sc' b' off' w' hEq _
            injection hEq with hsc hb _ hw
            subst hsc; subst hb; subst hw
            have hInfoBase := hRegs.2.2 baseId.toNat _ _ _ _ hB hBasePub
            rw [hInfoBase] at hPtrMeta
            cases hResInfo : env.ptrInfo resId.toNat with
            | none => rw [hResInfo] at hPtrMeta; simp at hPtrMeta
            | some p2 =>
              cases hTyInfo : env.ptrInfo tyId.toNat with
              | none => rw [hResInfo, hTyInfo] at hPtrMeta; simp at hPtrMeta
              | some p3 =>
                rw [hResInfo, hTyInfo] at hPtrMeta
                rcases p2 with ⟨sc2, b2, w2⟩
                rcases p3 with ⟨sc3, b3, w3⟩
                simp only [decide_eq_true_eq] at hPtrMeta
                rcases hPtrMeta with ⟨rfl, rfl, rfl, _, _, rfl⟩
                simp [hTyInfo]
          | _ => rfl
        | _ => cases r₁ idxId.toNat <;> rfl
  | opLoad tyId resId ptrId =>
    dsimp only [checkInstSimtCtStrict] at hCt
    simp only [Bool.and_eq_true, beq_iff_eq] at hCt
    rcases hCt with ⟨hPtrPub, hDstChk⟩
    have hPtrEq := hRegs.2.1 ptrId.toNat hPtrPub
    dsimp only [evalLanePureInst]
    rw [← hPtrEq]
    cases hP : r₁ ptrId.toNat with
    | vPtr sc binding elemIdx width =>
      have hInfo := hRegs.2.2 ptrId.toNat sc binding elemIdx width hP hPtrPub
      cases sc with
      | workgroup =>
        cases width with
        | w32 =>
          dsimp only
          split
          · refine ⟨rfl, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
            rw [hPub, hInfo] at hDstChk
            simp only [beq_iff_eq] at hDstChk
            rw [hMem.2.1 hDstChk]
          · rfl
        | w64 =>
          dsimp only
          split
          · refine ⟨rfl, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
            rw [hPub, hInfo] at hDstChk
            simp only [beq_iff_eq] at hDstChk
            rw [hMem.2.1 hDstChk]
          · rfl
      | storageBuffer =>
        cases width with
        | w32 =>
          refine ⟨rfl, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
          rw [hPub, hInfo] at hDstChk
          simp only [beq_iff_eq] at hDstChk
          rw [hMem.2.2 binding hDstChk]
        | w64 =>
          refine ⟨rfl, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
          rw [hPub, hInfo] at hDstChk
          simp only [beq_iff_eq] at hDstChk
          rw [hMem.2.2 binding hDstChk]
      | pushConstant =>
        cases width with
        | w32 =>
          refine ⟨rfl, trivial, fun _ => ?_, fun _ _ _ _ h => by cases h⟩
          rw [hMem.1]
        | w64 =>
          refine ⟨rfl, trivial, fun _ => ?_, fun _ _ _ _ h => by cases h⟩
          rw [hMem.1]
      | input | function =>
        cases width <;> rfl
    | _ => rfl
  | opCompositeExtract tyId resId compId fieldIdx =>
    dsimp only [checkInstSimtCtStrict, checkInstSimtCt] at hCt
    have hSh := hRegs.1 compId.toNat
    dsimp only [evalLanePureInst]
    cases h1 : r₁ compId.toNat <;> cases h2 : r₂ compId.toNat <;>
      (rw [h1, h2] at hSh; try cases hSh)
    · rfl
    · rfl
    · rfl
    · rfl
    · cases hF : fieldIdx.toNat with
      | zero =>
        refine ⟨rfl, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
        rw [hPub] at hCt; simp only [Bool.or_eq_true, beq_iff_eq] at hCt
        rcases hCt with hBad | hCompPub
        · cases hBad
        · have hEq := hRegs.2.1 compId.toNat hCompPub; rw [h1, h2] at hEq; cases hEq; rfl
      | succ n =>
        cases n with
        | zero =>
          refine ⟨rfl, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
          rw [hPub] at hCt; simp only [Bool.or_eq_true, beq_iff_eq] at hCt
          rcases hCt with hBad | hCompPub
          · cases hBad
          · have hEq := hRegs.2.1 compId.toNat hCompPub; rw [h1, h2] at hEq; cases hEq; rfl
        | succ _ => rfl
    · cases hF : fieldIdx.toNat with
      | zero =>
        refine ⟨rfl, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
        rw [hPub] at hCt; simp only [Bool.or_eq_true, beq_iff_eq] at hCt
        rcases hCt with hBad | hCompPub
        · cases hBad
        · have hEq := hRegs.2.1 compId.toNat hCompPub; rw [h1, h2] at hEq; cases hEq; rfl
      | succ n =>
        cases n with
        | zero =>
          refine ⟨rfl, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
          rw [hPub] at hCt; simp only [Bool.or_eq_true, beq_iff_eq] at hCt
          rcases hCt with hBad | hCompPub
          · cases hBad
          · have hEq := hRegs.2.1 compId.toNat hCompPub; rw [h1, h2] at hEq; cases hEq; rfl
        | succ _ => rfl
    · cases fieldIdx.toNat with
      | zero => rfl
      | succ n => cases n <;> rfl
  | opUConvert tyId resId valId =>
    dsimp only [checkInstSimtCtStrict, checkInstSimtCt] at hCt
    have hSh := hRegs.1 valId.toNat
    dsimp only [evalLanePureInst]
    cases hw : env.intWidths tyId.toNat with
    | none => rfl
    | some w =>
      cases w with
      | w32 =>
        cases h1 : r₁ valId.toNat <;> cases h2 : r₂ valId.toNat <;>
          (rw [h1, h2] at hSh; try cases hSh)
        · rfl
        · rfl
        · rfl
        · refine ⟨rfl, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
          rw [hPub] at hCt; simp only [Bool.or_eq_true, beq_iff_eq] at hCt
          rcases hCt with hBad | hValPub
          · cases hBad
          · have hEq := hRegs.2.1 valId.toNat hValPub; rw [h1, h2] at hEq; cases hEq; rfl
        · rfl
        · rfl
        · rfl
      | w64 =>
        cases h1 : r₁ valId.toNat <;> cases h2 : r₂ valId.toNat <;>
          (rw [h1, h2] at hSh; try cases hSh)
        · rfl
        · rfl
        · refine ⟨rfl, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
          rw [hPub] at hCt; simp only [Bool.or_eq_true, beq_iff_eq] at hCt
          rcases hCt with hBad | hValPub
          · cases hBad
          · have hEq := hRegs.2.1 valId.toNat hValPub; rw [h1, h2] at hEq; cases hEq; rfl
        · rfl
        · rfl
        · rfl
        · rfl
  | opSelect tyId resId cId tId fId =>
    dsimp only [checkInstSimtCtStrict, checkInstSimtCt] at hCt
    have hShC := hRegs.1 cId.toNat
    have hShT := hRegs.1 tId.toNat
    have hShF := hRegs.1 fId.toNat
    dsimp only [evalLanePureInst]
    cases hc1 : r₁ cId.toNat <;> cases hc2 : r₂ cId.toNat <;>
      (rw [hc1, hc2] at hShC; try cases hShC)
    · rfl
    · cases ht1 : r₁ tId.toNat <;> cases ht2 : r₂ tId.toNat <;>
        (rw [ht1, ht2] at hShT; try cases hShT)
      · rfl
      · rfl
      · cases hf1 : r₁ fId.toNat <;> cases hf2 : r₂ fId.toNat <;>
          (rw [hf1, hf2] at hShF; try cases hShF)
        · rfl
        · rfl
        · refine ⟨rfl, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
          rw [hPub] at hCt; simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hCt
          rcases hCt with hBad | ⟨⟨hCPub, hTPub⟩, hFPub⟩
          · cases hBad
          · have ec := hRegs.2.1 cId.toNat hCPub; rw [hc1, hc2] at ec; cases ec
            have et := hRegs.2.1 tId.toNat hTPub; rw [ht1, ht2] at et; cases et
            have ef := hRegs.2.1 fId.toNat hFPub; rw [hf1, hf2] at ef; cases ef
            rfl
        · rfl
        · rfl
        · rfl
        · rfl
      · cases hf1 : r₁ fId.toNat <;> cases hf2 : r₂ fId.toNat <;>
          (rw [hf1, hf2] at hShF; try cases hShF)
        · rfl
        · rfl
        · rfl
        · refine ⟨rfl, trivial, fun hPub => ?_, fun _ _ _ _ h => by cases h⟩
          rw [hPub] at hCt; simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hCt
          rcases hCt with hBad | ⟨⟨hCPub, hTPub⟩, hFPub⟩
          · cases hBad
          · have ec := hRegs.2.1 cId.toNat hCPub; rw [hc1, hc2] at ec; cases ec
            have et := hRegs.2.1 tId.toNat hTPub; rw [ht1, ht2] at et; cases et
            have ef := hRegs.2.1 fId.toNat hFPub; rw [hf1, hf2] at ef; cases ef
            rfl
        · rfl
        · rfl
        · rfl
      · rfl
      · rfl
      · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  | opIAdd _ resId aId bId =>
    exact evalBinU32U64_lowEq resId aId bId _ _
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h) hRegs hCt
  | opISub _ resId aId bId =>
    exact evalBinU32U64_lowEq resId aId bId _ _
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h) hRegs hCt
  | opIMul _ resId aId bId =>
    exact evalBinU32U64_lowEq resId aId bId _ _
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h) hRegs hCt
  | opUMulExtended _ resId aId bId =>
    exact evalBinU32U64_lowEq resId aId bId _ _
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h) hRegs hCt
  | opIEqual _ resId aId bId =>
    exact evalBinU32U64_lowEq resId aId bId _ _
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h) hRegs hCt
  | opUGreaterThanEqual _ resId aId bId =>
    exact evalBinU32U64_lowEq resId aId bId _ _
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h) hRegs hCt
  | opULessThan _ resId aId bId =>
    exact evalBinU32U64_lowEq resId aId bId _ _
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h) hRegs hCt
  | opShiftRightLogical _ resId aId bId =>
    exact evalBinU32U64_lowEq resId aId bId _ _
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h) hRegs hCt
  | opShiftLeftLogical _ resId aId bId =>
    exact evalBinU32U64_lowEq resId aId bId _ _
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h) hRegs hCt
  | opBitwiseXor _ resId aId bId =>
    exact evalBinU32U64_lowEq resId aId bId _ _
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h) hRegs hCt
  | opBitwiseOr _ resId aId bId =>
    exact evalBinU32U64_lowEq resId aId bId _ _
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h) hRegs hCt
  | opBitwiseAnd _ resId aId bId =>
    exact evalBinU32U64_lowEq resId aId bId _ _
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ h => by cases h) hRegs hCt

private theorem applyLaneStore_lowEq {env : SpirvModuleEnv} {pol : SimtCtPolicy}
    {m₁ m₂ : GpuMemState} {r₁ r₂ : Nat → SpirvVal} {ptrId valId : UInt32}
    (hMem : MemLowEq pol m₁ m₂)
    (hRegs : LaneRegsLowEq env pol r₁ r₂)
    (hCt : checkInstSimtCtStrict env pol (.opStore ptrId valId) = true) :
    match applyLaneStore m₁ r₁ ptrId valId, applyLaneStore m₂ r₂ ptrId valId with
    | .error e₁, .error e₂ => e₁ = e₂
    | .ok m₁', .ok m₂' => MemLowEq pol m₁' m₂'
    | _, _ => False := by
  dsimp only [checkInstSimtCtStrict] at hCt
  simp only [Bool.and_eq_true, beq_iff_eq] at hCt
  rcases hCt with ⟨hPtrPub, hFlowChk⟩
  have hPtrEq := hRegs.2.1 ptrId.toNat hPtrPub
  have hValSh := hRegs.1 valId.toNat
  dsimp only [applyLaneStore]
  rw [← hPtrEq]
  cases hP : r₁ ptrId.toNat with
  | vPtr sc binding elemIdx width =>
    have hInfo := hRegs.2.2 ptrId.toNat sc binding elemIdx width hP hPtrPub
    cases sc with
    | workgroup =>
      cases width with
      | w32 =>
        cases hv1 : r₁ valId.toNat <;> cases hv2 : r₂ valId.toNat <;>
          (rw [hv1, hv2] at hValSh; try cases hValSh)
        · rfl
        · rfl
        · dsimp only
          split
          · refine ⟨hMem.1, fun hLdsPub => ?_, hMem.2.2⟩
            have hValPub : pol.regSec valId.toNat = .pub := by
              cases hSec : pol.regSec valId.toNat with
              | pub => rfl
              | sec => rw [hSec, hInfo, hLdsPub] at hFlowChk; simp at hFlowChk
            have hvEq := hRegs.2.1 valId.toNat hValPub
            rw [hv1, hv2] at hvEq; cases hvEq
            rw [hMem.2.1 hLdsPub]
          · rfl
        · rfl
        · rfl
        · rfl
        · rfl
      | w64 =>
        cases hv1 : r₁ valId.toNat <;> cases hv2 : r₂ valId.toNat <;>
          (rw [hv1, hv2] at hValSh; try cases hValSh)
        · rfl
        · rfl
        · rfl
        · dsimp only
          split
          · refine ⟨hMem.1, fun hLdsPub => ?_, hMem.2.2⟩
            have hValPub : pol.regSec valId.toNat = .pub := by
              cases hSec : pol.regSec valId.toNat with
              | pub => rfl
              | sec => rw [hSec, hInfo, hLdsPub] at hFlowChk; simp at hFlowChk
            have hvEq := hRegs.2.1 valId.toNat hValPub
            rw [hv1, hv2] at hvEq; cases hvEq
            rw [hMem.2.1 hLdsPub]
          · rfl
        · rfl
        · rfl
        · rfl
    | storageBuffer =>
      cases width with
      | w32 =>
        cases hv1 : r₁ valId.toNat <;> cases hv2 : r₂ valId.toNat <;>
          (rw [hv1, hv2] at hValSh; try cases hValSh)
        · rfl
        · rfl
        · refine ⟨hMem.1, hMem.2.1, fun b' hb' => ?_⟩
          by_cases hbb : b' = binding
          · subst hbb
            have hValPub : pol.regSec valId.toNat = .pub := by
              cases hSec : pol.regSec valId.toNat with
              | pub => rfl
              | sec => rw [hSec, hInfo, hb'] at hFlowChk; simp at hFlowChk
            have hvEq := hRegs.2.1 valId.toNat hValPub
            rw [hv1, hv2] at hvEq; cases hvEq
            funext k
            simp [writeSsboDword, hMem.2.2 b' hb']
          · funext k
            simp [writeSsboDword, hbb, hMem.2.2 b' hb']
        · rfl
        · rfl
        · rfl
        · rfl
      | w64 =>
        cases hv1 : r₁ valId.toNat <;> cases hv2 : r₂ valId.toNat <;>
          (rw [hv1, hv2] at hValSh; try cases hValSh)
        · rfl
        · rfl
        · rfl
        · refine ⟨hMem.1, hMem.2.1, fun b' hb' => ?_⟩
          by_cases hbb : b' = binding
          · subst hbb
            have hValPub : pol.regSec valId.toNat = .pub := by
              cases hSec : pol.regSec valId.toNat with
              | pub => rfl
              | sec => rw [hSec, hInfo, hb'] at hFlowChk; simp at hFlowChk
            have hvEq := hRegs.2.1 valId.toNat hValPub
            rw [hv1, hv2] at hvEq; cases hvEq
            funext k
            simp [writeSsboU64, writeSsboDword, hMem.2.2 b' hb']
          · funext k
            simp [writeSsboU64, writeSsboDword, hbb, hMem.2.2 b' hb']
        · rfl
        · rfl
        · rfl
    | input | function | pushConstant =>
      cases width <;> cases r₁ valId.toNat <;> cases r₂ valId.toNat <;> rfl
  | _ =>
    cases r₁ valId.toNat <;> cases r₂ valId.toNat <;> rfl

private theorem execWaveStoreLanes_lowEq {env : SpirvModuleEnv} {pol : SimtCtPolicy}
    {execMask : Nat → Bool} {lr₁ lr₂ : Nat → Nat → SpirvVal} {ptrId valId : UInt32}
    (hRegs : ∀ lane < wave32Lanes, LaneRegsLowEq env pol (lr₁ lane) (lr₂ lane))
    (hCt : checkInstSimtCtStrict env pol (.opStore ptrId valId) = true) :
    ∀ (k : Nat) (_hk : k ≤ wave32Lanes) {m₁ m₂ : GpuMemState} (_hMem : MemLowEq pol m₁ m₂),
      match execWaveStoreLanes execMask lr₁ ptrId valId k m₁,
            execWaveStoreLanes execMask lr₂ ptrId valId k m₂ with
      | .error e₁, .error e₂ => e₁ = e₂
      | .ok m₁', .ok m₂' => MemLowEq pol m₁' m₂'
      | _, _ => False
  | 0, _, _, _, hMem => hMem
  | k + 1, hk, m₁, m₂, hMem => by
    have ih := execWaveStoreLanes_lowEq hRegs hCt k (by omega) hMem
    dsimp only [execWaveStoreLanes]
    cases h1 : execWaveStoreLanes execMask lr₁ ptrId valId k m₁ with
    | error e₁ =>
      cases h2 : execWaveStoreLanes execMask lr₂ ptrId valId k m₂ with
      | error e₂ => rw [h1, h2] at ih; exact ih
      | ok _ => rw [h1, h2] at ih; cases ih
    | ok m₁' =>
      cases h2 : execWaveStoreLanes execMask lr₂ ptrId valId k m₂ with
      | error _ => rw [h1, h2] at ih; cases ih
      | ok m₂' =>
        rw [h1, h2] at ih
        by_cases hAct : execMask k = true
        · simp only [hAct, ↓reduceIte]
          exact applyLaneStore_lowEq ih (hRegs k (by omega)) hCt
        · simp [hAct]; exact ih

private theorem evalWavePureLanes_lowEq {env : SpirvModuleEnv} {pol : SimtCtPolicy}
    {m₁ m₂ : GpuMemState} {execMask : Nat → Bool} {lr₁ lr₂ : Nat → Nat → SpirvVal} {inst : SpirvInst}
    (hMem : MemLowEq pol m₁ m₂)
    (hRegs : ∀ lane < wave32Lanes, LaneRegsLowEq env pol (lr₁ lane) (lr₂ lane))
    (hCt : checkInstSimtCtStrict env pol inst = true)
    (hNotStore : ∀ p v, inst ≠ .opStore p v)
    (hNotBarrier : ∀ es ms sem, inst ≠ .opControlBarrier es ms sem)
    (hNotLabel : ∀ l, inst ≠ .opLabel l) :
    ∀ (k : Nat) (_hk : k ≤ wave32Lanes),
      match evalWavePureLanes env m₁ execMask lr₁ inst k,
            evalWavePureLanes env m₂ execMask lr₂ inst k with
      | .error e₁, .error e₂ => e₁ = e₂
      | .ok r₁', .ok r₂' => ∀ lane < wave32Lanes, LaneRegsLowEq env pol (r₁' lane) (r₂' lane)
      | _, _ => False
  | 0, _ => hRegs
  | k + 1, hk => by
    have ih := evalWavePureLanes_lowEq hMem hRegs hCt hNotStore hNotBarrier hNotLabel k (by omega)
    dsimp only [evalWavePureLanes]
    cases h1 : evalWavePureLanes env m₁ execMask lr₁ inst k with
    | error e₁ =>
      cases h2 : evalWavePureLanes env m₂ execMask lr₂ inst k with
      | error e₂ => rw [h1, h2] at ih; exact ih
      | ok _ => rw [h1, h2] at ih; cases ih
    | ok r₁' =>
      cases h2 : evalWavePureLanes env m₂ execMask lr₂ inst k with
      | error _ => rw [h1, h2] at ih; cases ih
      | ok r₂' =>
        rw [h1, h2] at ih
        by_cases hAct : execMask k = true
        · simp only [hAct, ↓reduceIte]
          have hLane := evalLanePureInst_lowEq hMem (hRegs k (by omega)) hCt hNotStore hNotBarrier hNotLabel
          cases e1 : evalLanePureInst env m₁ (lr₁ k) inst with
          | error err₁ =>
            cases e2 : evalLanePureInst env m₂ (lr₂ k) inst with
            | error err₂ => rw [e1, e2] at hLane; exact hLane
            | ok _ => rw [e1, e2] at hLane; cases hLane
          | ok dv₁ =>
            cases e2 : evalLanePureInst env m₂ (lr₂ k) inst with
            | error _ => rw [e1, e2] at hLane; cases hLane
            | ok dv₂ =>
              rw [e1, e2] at hLane
              rcases dv₁ with ⟨d₁, v₁⟩
              rcases dv₂ with ⟨d₂, v₂⟩
              rcases hLane with ⟨rfl, hShape, hPubEq, hPtr⟩
              intro lane hlt
              by_cases hlk : lane = k
              · subst hlk
                simp only [↓reduceIte]
                exact writeFn_laneRegsLowEq (ih lane hlt) d₁ hShape hPubEq hPtr
              · simp only [hlk, ↓reduceIte]
                exact ih lane hlt
        · simp [hAct]; exact ih

private theorem stepWaveObs_eq_of_lowEq {env : SpirvModuleEnv} {pol : SimtCtPolicy}
    {w₁ w₂ : Wave32State} {inst : SpirvInst}
    (hWave : WaveLowEq env pol w₁ w₂)
    (hCt : checkInstSimtCtStrict env pol inst = true) :
    stepWaveObs w₁ inst = stepWaveObs w₂ inst := by
  unfold stepWaveObs
  rcases hWave with ⟨hpc, _, hMask, hLanes⟩
  rw [hpc, hMask]
  congr 1
  apply List.map_congr_left
  intro lane hMemRange
  have hlt : lane < wave32Lanes := List.mem_range.mp hMemRange
  by_cases hAct : w₂.execMask lane = true
  · simp only [hAct, ↓reduceIte]
    cases inst with
    | opLoad _ _ ptrId =>
      unfold checkInstSimtCtStrict at hCt
      simp only [Bool.and_eq_true, beq_iff_eq] at hCt
      have hEq := (hLanes lane hlt).2.1 ptrId.toNat hCt.1
      simp [observeLaneMem, hEq]
    | opStore ptrId _ =>
      unfold checkInstSimtCtStrict at hCt
      simp only [Bool.and_eq_true, beq_iff_eq] at hCt
      have hEq := (hLanes lane hlt).2.1 ptrId.toNat hCt.1
      simp [observeLaneMem, hEq]
    | _ => rfl
  · simp [hAct]

private theorem stepWave32One_lowEq {env : SpirvModuleEnv} {pol : SimtCtPolicy}
    {prog : List SpirvInst} {w₁ w₂ : Wave32State} {m₁ m₂ : GpuMemState}
    (hProgCt : checkProgSimtCt env pol prog = true)
    (hWave : WaveLowEq env pol w₁ w₂)
    (hMem : MemLowEq pol m₁ m₂) :
    match stepWave32One env prog w₁ m₁, stepWave32One env prog w₂ m₂ with
    | .error e₁, .error e₂ => e₁ = e₂
    | .ok (w₁', m₁'), .ok (w₂', m₂') => WaveLowEq env pol w₁' w₂' ∧ MemLowEq pol m₁' m₂'
    | _, _ => False := by
  unfold stepWave32One
  have ⟨hpc, hBar, hMask, hLanes⟩ := hWave
  rw [hBar]
  by_cases hb : w₂.atBarrier = true
  · simp [hb]; exact ⟨hWave, hMem⟩
  · simp only [hb, Bool.false_eq_true, ↓reduceIte, hpc]
    cases hGet : prog[w₂.pc]? with
    | none => exact ⟨hWave, hMem⟩
    | some inst =>
      have hInstMem : inst ∈ prog := List.mem_of_getElem? hGet
      have hInstCt : checkInstSimtCtStrict env pol inst = true := by
        unfold checkProgSimtCt at hProgCt
        exact List.all_eq_true.mp hProgCt inst hInstMem
      cases inst with
      | opControlBarrier es ms sem =>
        cases es <;> cases ms <;> simp
        by_cases hSem : (sem == spirvSemWorkgroupAcqRel) = true
        · simp [hSem]
          exact ⟨⟨hpc, rfl, hMask, hLanes⟩, hMem⟩
        · simp [hSem]
      | opStore ptrId valId =>
        dsimp only
        rw [hMask]
        have hSt := execWaveStoreLanes_lowEq hLanes hInstCt wave32Lanes (Nat.le_refl _) hMem
        cases s1 : execWaveStoreLanes w₂.execMask w₁.laneRegs ptrId valId wave32Lanes m₁ with
        | error e₁ =>
          cases s2 : execWaveStoreLanes w₂.execMask w₂.laneRegs ptrId valId wave32Lanes m₂ with
          | error e₂ => rw [s1, s2] at hSt; exact hSt
          | ok _ => rw [s1, s2] at hSt; cases hSt
        | ok m₁' =>
          cases s2 : execWaveStoreLanes w₂.execMask w₂.laneRegs ptrId valId wave32Lanes m₂ with
          | error _ => rw [s1, s2] at hSt; cases hSt
          | ok m₂' =>
            rw [s1, s2] at hSt
            exact ⟨⟨by omega, hBar, hMask, hLanes⟩, hSt⟩
      | opLabel lbl =>
        exact ⟨⟨by omega, hBar, hMask, hLanes⟩, hMem⟩
      | opLoad _ _ _ | opAccessChain _ _ _ _ | opCompositeExtract _ _ _ _ | opUConvert _ _ _
      | opIAdd _ _ _ _ | opISub _ _ _ _ | opIMul _ _ _ _ | opUMulExtended _ _ _ _
      | opSelect _ _ _ _ _ | opIEqual _ _ _ _ | opUGreaterThanEqual _ _ _ _
      | opULessThan _ _ _ _ | opShiftRightLogical _ _ _ _ | opShiftLeftLogical _ _ _ _
      | opBitwiseXor _ _ _ _ | opBitwiseOr _ _ _ _ | opBitwiseAnd _ _ _ _
      | opLoopMerge _ _ _ | opSelectionMerge _ _ | opBranch _ | opBranchConditional _ _ _ =>
        dsimp only
        rw [hMask]
        have hPure := evalWavePureLanes_lowEq hMem hLanes hInstCt
          (by intro _ _ h; cases h) (by intro _ _ _ h; cases h) (by intro _ h; cases h)
          wave32Lanes (Nat.le_refl _)
        cases p1 : evalWavePureLanes env m₁ w₂.execMask w₁.laneRegs _ wave32Lanes with
        | error e₁ =>
          cases p2 : evalWavePureLanes env m₂ w₂.execMask w₂.laneRegs _ wave32Lanes with
          | error e₂ => rw [p1, p2] at hPure; exact hPure
          | ok _ => rw [p1, p2] at hPure; cases hPure
        | ok r₁' =>
          cases p2 : evalWavePureLanes env m₂ w₂.execMask w₂.laneRegs _ wave32Lanes with
          | error _ => rw [p1, p2] at hPure; cases hPure
          | ok r₂' =>
            rw [p1, p2] at hPure
            exact ⟨⟨by omega, hBar, hMask, hPure⟩, hMem⟩

/-- **`SIMT-CT` Hardware Leakage-Trace Noninterference Theorem (`simt_ct_noninterference`)**:
    For every SPIR-V compute epoch `prog` passing `checkProgSimtCt env pol prog = true`,
    any two Wave32 executions starting from public-equivalent registers (`WaveLowEq`) and
    public-equivalent memories (`MemLowEq` — differing arbitrarily on secret `StorageBuffer`
    witnesses and secret `Workgroup` LDS!) emit **identical hardware side-channel observation
    traces** (`PC` trajectory, 32-lane `EXEC` active masks, global coalescing addresses, AND
    physical 32-bank LDS access patterns)! -/
theorem simt_ct_noninterference {env : SpirvModuleEnv} {pol : SimtCtPolicy}
    {prog : List SpirvInst} (hProgCt : checkProgSimtCt env pol prog = true) :
    ∀ (fuel : Nat) {w₁ w₂ : Wave32State} {m₁ m₂ : GpuMemState},
      WaveLowEq env pol w₁ w₂ →
      MemLowEq pol m₁ m₂ →
      runWaveWithObs env prog fuel w₁ m₁ = runWaveWithObs env prog fuel w₂ m₂
  | 0, _, _, _, _, _, _ => rfl
  | fuel + 1, w₁, w₂, m₁, m₂, hWave, hMem => by
    unfold runWaveWithObs
    have ⟨hpc, hBar, _, _⟩ := hWave
    rw [hBar]
    by_cases hb : w₂.atBarrier = true
    · simp [hb]
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      cases hGet₁ : prog[w₁.pc]? with
      | none =>
        have hGet₂ : prog[w₂.pc]? = none := by rwa [← hpc]
        simp [hGet₂]
      | some inst =>
        have hGet₂ : prog[w₂.pc]? = some inst := by rwa [← hpc]
        simp only [hGet₂]
        have hInstCt : checkInstSimtCtStrict env pol inst = true :=
          List.all_eq_true.mp hProgCt inst (List.mem_of_getElem? hGet₁)
        have hObsEq := stepWaveObs_eq_of_lowEq hWave hInstCt
        have hStep := stepWave32One_lowEq hProgCt hWave hMem
        rw [hObsEq]
        cases s1 : stepWave32One env prog w₁ m₁ with
        | error _ =>
          cases s2 : stepWave32One env prog w₂ m₂ with
          | error _ => rfl
          | ok _ => rw [s1, s2] at hStep; cases hStep
        | ok wm₁ =>
          cases s2 : stepWave32One env prog w₂ m₂ with
          | error _ => rw [s1, s2] at hStep; cases hStep
          | ok wm₂ =>
            rw [s1, s2] at hStep
            rcases wm₁ with ⟨w₁', m₁'⟩
            rcases wm₂ with ⟨w₂', m₂'⟩
            rw [simt_ct_noninterference hProgCt fuel hStep.1 hStep.2]

/-- **Zero `EXEC`-Mask Divergence Theorem (`simt_ct_zero_exec_divergence`)**:
    Starting with all 32 Wave32 lanes active (`wSt.execMask = allActive32`), every observation
    emitted during a `SIMT-CT` epoch has `obs.activeMask = List.replicate 32 true` (`0` divergent
    lanes across the entire kernel execution). -/
theorem simt_ct_zero_exec_divergence (env : SpirvModuleEnv) (prog : List SpirvInst) :
    ∀ (fuel : Nat) (wSt : Wave32State) (mem : GpuMemState),
      wSt.execMask = allActive32 →
      ∀ obs ∈ runWaveWithObs env prog fuel wSt mem,
        obs.activeMask = List.replicate 32 true := by
  have hAllTrue : (List.range wave32Lanes).map allActive32 = List.replicate 32 true := by decide
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ hMem; cases hMem
  | succ fuel ih =>
    intro wSt mem hMask obs hIn
    unfold runWaveWithObs at hIn
    by_cases hb : wSt.atBarrier = true
    · simp [hb] at hIn
    · simp only [hb, Bool.false_eq_true, ↓reduceIte] at hIn
      cases hGet : prog[wSt.pc]? with
      | none => rw [hGet] at hIn; cases hIn
      | some inst =>
        rw [hGet] at hIn
        have hHeadMask : (stepWaveObs wSt inst).activeMask = List.replicate 32 true := by
          unfold stepWaveObs; rw [hMask, hAllTrue]
        cases hStep : stepWave32One env prog wSt mem with
        | error _ =>
          rw [hStep] at hIn
          rcases List.mem_singleton.mp hIn with rfl
          exact hHeadMask
        | ok wm =>
          rw [hStep] at hIn
          rcases wm with ⟨wSt', mem'⟩
          rcases List.mem_cons.mp hIn with rfl | hTail
          · exact hHeadMask
          · have hMaskPres : wSt'.execMask = allActive32 := by
              unfold stepWave32One at hStep
              simp only [hb, Bool.false_eq_true, ↓reduceIte, hGet] at hStep
              cases inst with
              | opControlBarrier es ms sem =>
                cases es <;> cases ms <;> simp at hStep
                split at hStep <;> simp_all
              | opStore ptrId valId =>
                dsimp only at hStep
                cases execWaveStoreLanes wSt.execMask wSt.laneRegs ptrId valId wave32Lanes mem <;> simp_all
              | opLabel _ => simp_all
              | _ =>
                dsimp only at hStep
                cases evalWavePureLanes env mem wSt.execMask wSt.laneRegs _ wave32Lanes <;> simp_all
            exact ih wSt' mem' hMaskPres obs hTail

/-- **`#tooth` Secret-Dependent LDS Indexing Rejected by `SIMT-CT` & Leaks Physical Bank Trace
    (`tooth_secret_index_leaks_lds_bank_trace`)**:
    A buggy lookup-table S-box kernel that loads `lds[%secWitness]` is rejected by `checkProgSimtCt`
    (`= false`) AND exhibits two `MemLowEq` secret witnesses (`sec = 0` vs `sec = 1` on lane `0`)
    whose Wave32 hardware observation traces differ (`ldsBank 0 = 0 ≠ 1 = ldsBank 4`)! -/
theorem tooth_secret_index_leaks_lds_bank_trace :
    let pol : SimtCtPolicy :=
      { ssboSec := fun b => if b == 0 then .sec else .pub
        ldsSec := .pub
        regSec := fun id => if id == 11 || id == 12 || id == 13 then .sec else .pub }
    let buggyLutProg : List SpirvInst :=
      [ .opAccessChain 7 10 3 [1],   -- %10 = &secIn[tid] (pub ptr)
        .opLoad 8 11 10,             -- %11 = secIn[tid]  (SECRET witness!)
        .opAccessChain 6 12 2 [11],  -- %12 = &lds[%11]   (ILLEGAL secret index!)
        .opLoad 8 13 12 ]            -- %13 = lds[%11]    (SECRET-DEPENDENT LDS BANK!)
    let m₀ : GpuMemState :=
      { lds := fun i => UInt32.ofNat i
        ssbo := fun b i => if b == 0 && i == 0 then 0 else 0
        pushConsts := fun _ => 0 }
    let m₁ : GpuMemState :=
      { lds := fun i => UInt32.ofNat i
        ssbo := fun b i => if b == 0 && i == 0 then 1 else 0
        pushConsts := fun _ => 0 }
    let w₀ := (initWorkgroupExecState twoWaveReductionEnv twoWaveCfg m₀).waves 0
    checkProgSimtCt twoWaveReductionEnv pol buggyLutProg = false ∧
    MemLowEq pol m₀ m₁ ∧
    runWaveWithObs twoWaveReductionEnv buggyLutProg 4 w₀ m₀ ≠
      runWaveWithObs twoWaveReductionEnv buggyLutProg 4 w₀ m₁ := by
  refine ⟨by decide, ⟨rfl, fun _ => rfl, fun b hb => ?_⟩, by decide⟩
  by_cases hb0 : b = 0
  · subst hb0; simp at hb
  · funext i; simp [hb0]

end Qsag
end
