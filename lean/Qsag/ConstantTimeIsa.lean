module

public import Qsag.Constructive

public section

/-!
# `Qsag.ConstantTimeIsa`: Machine-Code Constant-Time Timing-Noninterference & SIMD Kernel Proofs

Self-contained Lean 4.35 formalization of machine-code constant-time (CT) execution and functional
correctness for selected modeled platform assembly kernels in `crates/qsag-asm` across both `x86_64`
(`AVX2` + `GFNI` + `VPCLMULQDQ` + `BMI2` + Intel `DOIT`) and `aarch64` (`NEON` + `FEAT_SHA3` +
`PMULL` + ARMv8.4 `FEAT_DIT`).

The ISA programs are manually maintained abstractions, not verified binary decoding.
Broadcast setup combines `vmovq` and `vpbroadcastq`; public loops abstract counter
maintenance and guarded positive dispatch; ARM paired loads expand into scalar loads.

## Core Guarantees
1. **Microarchitectural Leakage Semantics (`LeakageEvent`)**: Models cycle-observable side channels
   at the ISA level: program-counter path (`pc`), conditional branch outcomes (`branchTaken`),
   effective virtual memory addresses (`memAddrs`), variable-latency execution unit operands
   (`varLatencyOperands` for `div`/`udiv`, unguarded `cmov`/`csel`, and ARM multiplication without `DIT`),
   and dirty upper-YMM return hazards (`dirtyUpperYmmOnRet` when `vzeroupper` is omitted).
2. **Sound Relational Information-Flow Checker (`x86_ct_checker_sound`, `arm_ct_checker_sound`)**:
   Proves that any assembly program accepted by the static taint analyzer produces **bit-identical**
   microarchitectural leakage traces across any two states agreeing on public (`SecLabel.pub`) inputs.
3. **Mutation-Sensitivity Witnesses (`tooth_*`)**: Proves both static rejection (`= none`) and
   concrete dynamic trace divergence (`leakageTrace s₁ ≠ leakageTrace s₂`) for secret conditional
   branches, secret table lookups, secret division (even under `DOIT`), omitted `vzeroupper`, and
   unguarded `csel`/`umulh` without `MSR DIT, #1`, and secret shift carry reaching a branch.
4. **Functional & Timing-Noninterference Theorems for Concrete `qsag-asm` Kernels**:
   - `keccakChiMpcAvx2Prog` & `keccakSha3NeonProg`: 256-way parallel 3-party RSS Keccak `χ` row +
     ARMv8.2-SHA3 `BCAX` equivalence + architectural YMM zeroization.
   - `gf256ShamirMulGfniProg`: Algebraic field isomorphism between Wiedemann tower `𝒯₃` (`GF(2^8)`)
     and Intel `GFNI` `𝔽₂[z]/(z⁸ + z⁴ + z³ + z + 1)` via `0x71500A8A86BE78CE` / `0xA1E4F8E072A2700C`
     (proved via `𝔽₂`-bilinearity + basis evaluation with `0 native_decide`).
   - `tower128BdozVpclmulProg`: 2-lane 128-bit carryless `vpclmulqdq` inner-product MAC and
     2-step `0x87` (`z¹²⁸ + z⁷ + z² + z + 1`) degree-bounded polynomial reduction.
   - `goldilocksMulCtX86Prog` & `goldilocksMulCtArmProg`: Zero-branch canonical Goldilocks
     (`p = 2⁶⁴ - 2³² + 1`) multiplication over **all** `(a, b) ∈ [0, 2⁶⁴ - 1]²` + cross-ISA equality.
   - `ctEq32X86Prog` & `ctEq32ArmProg`: Branchless, `cmov`/`csel`-free 256-bit BDOZ tag equality.
-/

attribute [-instance] BitVec.instLawfulEqOrd

set_option autoImplicit false

namespace Qsag.ConstantTimeIsa

/-! ## 1. Security Lattice (`Public ⊑ Secret`) -/

inductive SecLabel where
  | pub : SecLabel
  | sec : SecLabel
  deriving DecidableEq, Repr, Inhabited

@[expose]
def SecLabel.leq (a b : SecLabel) : Bool :=
  match a, b with
  | .sec, .pub => false
  | _, _ => true

@[expose]
def SecLabel.join (a b : SecLabel) : SecLabel :=
  match a, b with
  | .pub, .pub => .pub
  | _, _ => .sec

def SecLabel.meet (a b : SecLabel) : SecLabel :=
  match a, b with
  | .sec, .sec => .sec
  | _, _ => .pub

theorem SecLabel.leq_refl (a : SecLabel) : a.leq a = true := by
  cases a <;> rfl

theorem SecLabel.leq_trans {a b c : SecLabel}
    (hab : a.leq b = true) (hbc : b.leq c = true) : a.leq c = true := by
  cases a <;> cases b <;> cases c <;> simp_all [SecLabel.leq]

theorem SecLabel.leq_antisymm {a b : SecLabel}
    (hab : a.leq b = true) (hba : b.leq a = true) : a = b := by
  cases a <;> cases b <;> simp_all [SecLabel.leq]

theorem SecLabel.join_comm (a b : SecLabel) : a.join b = b.join a := by
  cases a <;> cases b <;> rfl

theorem SecLabel.join_assoc (a b c : SecLabel) :
    (a.join b).join c = a.join (b.join c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem SecLabel.join_idem (a : SecLabel) : a.join a = a := by
  cases a <;> rfl

theorem SecLabel.join_eq_pub_iff (a b : SecLabel) :
    a.join b = .pub ↔ a = .pub ∧ b = .pub := by
  cases a <;> cases b <;> simp [SecLabel.join]

/-! ## 2. SIMD Register Carriers & Microarchitectural Leakage Events -/

structure Vec128 where
  lo : BitVec 64
  hi : BitVec 64
  deriving DecidableEq, Repr, Inhabited

def Vec128.zero : Vec128 := ⟨0#64, 0#64⟩

def Vec128.xor (a b : Vec128) : Vec128 :=
  ⟨a.lo ^^^ b.lo, a.hi ^^^ b.hi⟩

def Vec128.and (a b : Vec128) : Vec128 :=
  ⟨a.lo &&& b.lo, a.hi &&& b.hi⟩

def Vec128.bcax (vn vm va : Vec128) : Vec128 :=
  ⟨vn.lo ^^^ (vm.lo &&& ~~~va.lo), vn.hi ^^^ (vm.hi &&& ~~~va.hi)⟩

def Vec128.eor3 (vn vm va : Vec128) : Vec128 :=
  ⟨vn.lo ^^^ vm.lo ^^^ va.lo, vn.hi ^^^ vm.hi ^^^ va.hi⟩

def rol64 (x : BitVec 64) (r : Nat) : BitVec 64 :=
  let s := r % 64
  if s == 0 then x else (x <<< s) ||| (x >>> (64 - s))

def Vec128.rax1 (vn vm : Vec128) : Vec128 :=
  ⟨vn.lo ^^^ rol64 vm.lo 1, vn.hi ^^^ rol64 vm.hi 1⟩

def Vec128.xar (vn vm : Vec128) (imm6 : Fin 64) : Vec128 :=
  let r := (64 - imm6.val) % 64
  ⟨rol64 (vn.lo ^^^ vm.lo) r, rol64 (vn.hi ^^^ vm.hi) r⟩

def Vec128.ext8 (vn vm : Vec128) : Vec128 :=
  ⟨vn.hi, vm.lo⟩

structure Vec256 where
  w0 : BitVec 64
  w1 : BitVec 64
  w2 : BitVec 64
  w3 : BitVec 64
  deriving DecidableEq, Repr, Inhabited

def Vec256.zero : Vec256 := ⟨0#64, 0#64, 0#64, 0#64⟩

def Vec256.xor (a b : Vec256) : Vec256 :=
  ⟨a.w0 ^^^ b.w0, a.w1 ^^^ b.w1, a.w2 ^^^ b.w2, a.w3 ^^^ b.w3⟩

def Vec256.and (a b : Vec256) : Vec256 :=
  ⟨a.w0 &&& b.w0, a.w1 &&& b.w1, a.w2 &&& b.w2, a.w3 &&& b.w3⟩

def Vec256.andNot (a b : Vec256) : Vec256 :=
  ⟨(~~~a.w0) &&& b.w0, (~~~a.w1) &&& b.w1, (~~~a.w2) &&& b.w2, (~~~a.w3) &&& b.w3⟩

def Vec256.or (a b : Vec256) : Vec256 :=
  ⟨a.w0 ||| b.w0, a.w1 ||| b.w1, a.w2 ||| b.w2, a.w3 ||| b.w3⟩

def Vec256.not (a : Vec256) : Vec256 :=
  ⟨~~~a.w0, ~~~a.w1, ~~~a.w2, ~~~a.w3⟩

def Vec256.sllq8 (a : Vec256) : Vec256 :=
  ⟨0#64, a.w0, 0#64, a.w2⟩

def Vec256.srlq8 (a : Vec256) : Vec256 :=
  ⟨a.w1, 0#64, a.w3, 0#64⟩

def Vec256.broadcastQ (q : BitVec 64) : Vec256 :=
  ⟨q, q, q, q⟩

def broadcastByte64 (b : BitVec 8) : BitVec 64 :=
  let v := b.zeroExtend 64
  v ||| (v <<< 8) ||| (v <<< 16) ||| (v <<< 24) |||
  v <<< 32 ||| (v <<< 40) ||| (v <<< 48) ||| (v <<< 56)

def Vec256.broadcastB (b : BitVec 8) : Vec256 :=
  Vec256.broadcastQ (broadcastByte64 b)

def extractByte64 (w : BitVec 64) (idx : Nat) : BitVec 8 :=
  (w >>> (idx * 8)).truncate 8

def packBytes64 (f : Fin 8 → BitVec 8) : BitVec 64 :=
  ((f ⟨0, by omega⟩).zeroExtend 64) |||
  (((f ⟨1, by omega⟩).zeroExtend 64) <<< 8) |||
  (((f ⟨2, by omega⟩).zeroExtend 64) <<< 16) |||
  (((f ⟨3, by omega⟩).zeroExtend 64) <<< 24) |||
  (((f ⟨4, by omega⟩).zeroExtend 64) <<< 32) |||
  (((f ⟨5, by omega⟩).zeroExtend 64) <<< 40) |||
  (((f ⟨6, by omega⟩).zeroExtend 64) <<< 48) |||
  (((f ⟨7, by omega⟩).zeroExtend 64) <<< 56)

def Vec256.getByte (v : Vec256) (idx : Fin 32) : BitVec 8 :=
  let q := idx.val / 8
  let r := idx.val % 8
  if q == 0 then extractByte64 v.w0 r
  else if q == 1 then extractByte64 v.w1 r
  else if q == 2 then extractByte64 v.w2 r
  else extractByte64 v.w3 r

def zipBytes64 (f : BitVec 8 → BitVec 8 → BitVec 8) (a b : BitVec 64) : BitVec 64 :=
  packBytes64 (fun i => f (extractByte64 a i.val) (extractByte64 b i.val))

theorem extractByte64_packBytes64 (f : Fin 8 → BitVec 8) (k : Fin 8) :
    extractByte64 (packBytes64 f) k.val = f k := by
  rcases k with ⟨kv, hk⟩
  have hkv : kv = 0 ∨ kv = 1 ∨ kv = 2 ∨ kv = 3 ∨ kv = 4 ∨ kv = 5 ∨ kv = 6 ∨ kv = 7 := by omega
  ext bit hbit
  have hb : bit = 0 ∨ bit = 1 ∨ bit = 2 ∨ bit = 3 ∨ bit = 4 ∨ bit = 5 ∨ bit = 6 ∨ bit = 7 := by
    omega
  rcases hkv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [extractByte64, packBytes64]

/-- Microarchitectural side-channel observation emitted per architectural step. -/
structure LeakageEvent where
  pc : Nat
  branchTaken : Option Bool
  memAddrs : List (BitVec 64)
  varLatencyOperands : List (BitVec 64)
  dirtyUpperYmmOnRet : Bool
  deriving DecidableEq, Repr, Inhabited

def LeakageEvent.clean (pc : Nat) (addrs : List (BitVec 64) := []) : LeakageEvent :=
  { pc := pc
    branchTaken := none
    memAddrs := addrs
    varLatencyOperands := []
    dirtyUpperYmmOnRet := false }

/-! ## 3. Algebraic Primitives (`GFNI` / Wiedemann `𝒯₃` & Carryless `GF(2)[z]`) -/

def parity8 (x : BitVec 8) : Bool :=
  xor (xor (xor (x.getLsbD 0) (x.getLsbD 1)) (xor (x.getLsbD 2) (x.getLsbD 3)))
      (xor (xor (x.getLsbD 4) (x.getLsbD 5)) (xor (x.getLsbD 6) (x.getLsbD 7)))

def packBits8 (f : Fin 8 → Bool) : BitVec 8 :=
  (if f ⟨0, by omega⟩ then 0x01#8 else 0#8) ^^^
  (if f ⟨1, by omega⟩ then 0x02#8 else 0#8) ^^^
  (if f ⟨2, by omega⟩ then 0x04#8 else 0#8) ^^^
  (if f ⟨3, by omega⟩ then 0x08#8 else 0#8) ^^^
  (if f ⟨4, by omega⟩ then 0x10#8 else 0#8) ^^^
  (if f ⟨5, by omega⟩ then 0x20#8 else 0#8) ^^^
  (if f ⟨6, by omega⟩ then 0x40#8 else 0#8) ^^^
  (if f ⟨7, by omega⟩ then 0x80#8 else 0#8)

/-- Exact Intel `VGF2P8AFFINEQB` byte semantics:
    `ret.bit[i] = parity(x & qword.byte[7 - i]) ^ imm8.bit[i]`. -/
def gfniAffineByte (mat : BitVec 64) (x imm8 : BitVec 8) : BitVec 8 :=
  packBits8 (fun i =>
    xor (parity8 (x &&& extractByte64 mat (7 - i.val))) (imm8.getLsbD i.val))

def gfniXtime (x : BitVec 8) : BitVec 8 :=
  (x <<< 1) ^^^ (if x.getLsbD 7 then 0x1B#8 else 0#8)

/-- Exact Intel `VGF2P8MULB` byte semantics in `𝔽₂[z]/(z⁸ + z⁴ + z³ + z + 1)` (`0x11B`). -/
def gfniPolyMul (a b : BitVec 8) : BitVec 8 :=
  let a0 := a
  let a1 := gfniXtime a0
  let a2 := gfniXtime a1
  let a3 := gfniXtime a2
  let a4 := gfniXtime a3
  let a5 := gfniXtime a4
  let a6 := gfniXtime a5
  let a7 := gfniXtime a6
  (if b.getLsbD 0 then a0 else 0#8) ^^^
  (if b.getLsbD 1 then a1 else 0#8) ^^^
  (if b.getLsbD 2 then a2 else 0#8) ^^^
  (if b.getLsbD 3 then a3 else 0#8) ^^^
  (if b.getLsbD 4 then a4 else 0#8) ^^^
  (if b.getLsbD 5 then a5 else 0#8) ^^^
  (if b.getLsbD 6 then a6 else 0#8) ^^^
  (if b.getLsbD 7 then a7 else 0#8)

def Vec256.gfniAffine0 (src mat : Vec256) : Vec256 :=
  ⟨ packBytes64 (fun i => gfniAffineByte mat.w0 (extractByte64 src.w0 i.val) 0#8)
  , packBytes64 (fun i => gfniAffineByte mat.w1 (extractByte64 src.w1 i.val) 0#8)
  , packBytes64 (fun i => gfniAffineByte mat.w2 (extractByte64 src.w2 i.val) 0#8)
  , packBytes64 (fun i => gfniAffineByte mat.w3 (extractByte64 src.w3 i.val) 0#8) ⟩

def Vec256.gfniMul (a b : Vec256) : Vec256 :=
  ⟨ zipBytes64 gfniPolyMul a.w0 b.w0
  , zipBytes64 gfniPolyMul a.w1 b.w1
  , zipBytes64 gfniPolyMul a.w2 b.w2
  , zipBytes64 gfniPolyMul a.w3 b.w3 ⟩

/-- Wiedemann tower `𝒯₁ = GF(2²)` multiplication (`x₀² + x₀ + 1 = 0`). -/
def gf4Mul (a b : BitVec 2) : BitVec 2 :=
  let a0 := a.getLsbD 0
  let a1 := a.getLsbD 1
  let b0 := b.getLsbD 0
  let b1 := b.getLsbD 1
  let p0 := and a0 b0
  let p1 := and a1 b1
  let pm := and (xor a0 a1) (xor b0 b1)
  let c0 := xor p0 p1
  let c1 := xor pm p0
  (if c0 then 1#2 else 0#2) ^^^ (if c1 then 2#2 else 0#2)

def gf4MulAlpha (a : BitVec 2) : BitVec 2 :=
  let a0 := a.getLsbD 0
  let a1 := a.getLsbD 1
  (if a1 then 1#2 else 0#2) ^^^ (if xor a0 a1 then 2#2 else 0#2)

/-- Wiedemann tower `𝒯₂ = GF(2⁴)` multiplication (`x₁² + x₀·x₁ + 1 = 0`). -/
def gf16Mul (a b : BitVec 4) : BitVec 4 :=
  let aLo : BitVec 2 := a.truncate 2
  let aHi : BitVec 2 := (a >>> 2).truncate 2
  let bLo : BitVec 2 := b.truncate 2
  let bHi : BitVec 2 := (b >>> 2).truncate 2
  let p0 := gf4Mul aLo bLo
  let p1 := gf4Mul aHi bHi
  let pm := gf4Mul (aLo ^^^ aHi) (bLo ^^^ bHi)
  let lo := p0 ^^^ p1
  let hi := pm ^^^ p0 ^^^ p1 ^^^ gf4MulAlpha p1
  lo.zeroExtend 4 ^^^ ((hi.zeroExtend 4) <<< 2)

def gf16MulAlpha (a : BitVec 4) : BitVec 4 :=
  let aLo : BitVec 2 := a.truncate 2
  let aHi : BitVec 2 := (a >>> 2).truncate 2
  let lo := aHi
  let hi := aLo ^^^ gf4MulAlpha aHi
  lo.zeroExtend 4 ^^^ ((hi.zeroExtend 4) <<< 2)

/-- Canonical Wiedemann tower `𝒯₃ = GF(2⁸)` multiplication (`x₂² + x₁·x₂ + 1 = 0`),
    matching `qsag_core::field::tower::TowerGf256::mul` bit-for-bit. -/
@[expose]
def towerGf256Mul (a b : BitVec 8) : BitVec 8 :=
  let aLo : BitVec 4 := a.truncate 4
  let aHi : BitVec 4 := (a >>> 4).truncate 4
  let bLo : BitVec 4 := b.truncate 4
  let bHi : BitVec 4 := (b >>> 4).truncate 4
  let p0 := gf16Mul aLo bLo
  let p1 := gf16Mul aHi bHi
  let pm := gf16Mul (aLo ^^^ aHi) (bLo ^^^ bHi)
  let lo := p0 ^^^ p1
  let hi := pm ^^^ p0 ^^^ p1 ^^^ gf16MulAlpha p1
  lo.zeroExtend 8 ^^^ ((hi.zeroExtend 8) <<< 4)

/-- 64×64 -> 128-bit carryless polynomial multiplication (`PCLMULQDQ` / `PMULL` lane primitive). -/
def clmul64Step (a b : BitVec 64) (k : Nat) (acc : Vec128) : Vec128 :=
  match k with
  | 0 => acc
  | n + 1 =>
    let acc' :=
      if b.getLsbD n then
        if n == 0 then
          ⟨acc.lo ^^^ a, acc.hi⟩
        else
          ⟨acc.lo ^^^ (a <<< n), acc.hi ^^^ (a >>> (64 - n))⟩
      else
        acc
    clmul64Step a b n acc'

def clmul64 (a b : BitVec 64) : Vec128 :=
  clmul64Step a b 64 Vec128.zero

def Vec256.vpclmulqdq (a b : Vec256) (imm8 : BitVec 8) : Vec256 :=
  let aLane0 := if imm8.getLsbD 0 then a.w1 else a.w0
  let bLane0 := if imm8.getLsbD 4 then b.w1 else b.w0
  let aLane1 := if imm8.getLsbD 0 then a.w3 else a.w2
  let bLane1 := if imm8.getLsbD 4 then b.w3 else b.w2
  let p0 := clmul64 aLane0 bLane0
  let p1 := clmul64 aLane1 bLane1
  ⟨p0.lo, p0.hi, p1.lo, p1.hi⟩

/-! ## 4. `x86_64` Constant-Time ISA Semantics & Relational Taint Checker -/

inductive X86Gpr where
  | rax | rbx | rcx | rdx | rsi | rdi | rbp | rsp
  | r8  | r9  | r10 | r11 | r12 | r13 | r14 | r15
  deriving DecidableEq, Repr, Inhabited

inductive YmmReg where
  | ymm0  | ymm1  | ymm2  | ymm3  | ymm4  | ymm5  | ymm6  | ymm7
  | ymm8  | ymm9  | ymm10 | ymm11 | ymm12 | ymm13 | ymm14 | ymm15
  deriving DecidableEq, Repr, Inhabited

structure X86Flags where
  cf : Bool
  of : Bool
  zf : Bool
  deriving DecidableEq, Repr, Inhabited

structure X86State where
  gpr : X86Gpr → BitVec 64
  ymm : YmmReg → Vec256
  flags : X86Flags
  mem : BitVec 64 → BitVec 64
  doitEnabled : Bool
  ymmUpperDirty : Bool

def X86State.setGpr (st : X86State) (r : X86Gpr) (v : BitVec 64) : X86State :=
  { st with gpr := fun q => if q == r then v else st.gpr q }

def X86State.setYmm (st : X86State) (r : YmmReg) (v : Vec256) : X86State :=
  { st with
    ymm := fun q => if q == r then v else st.ymm q
    ymmUpperDirty := true }

def X86State.writeMem64 (st : X86State) (addr val : BitVec 64) : X86State :=
  { st with mem := fun a => if a == addr then val else st.mem a }

def X86State.readMem256 (st : X86State) (addr : BitVec 64) : Vec256 :=
  ⟨ st.mem addr
  , st.mem (addr + 8#64)
  , st.mem (addr + 16#64)
  , st.mem (addr + 24#64) ⟩

def X86State.writeMem256 (st : X86State) (addr : BitVec 64) (v : Vec256) : X86State :=
  (((st.writeMem64 addr v.w0).writeMem64 (addr + 8#64) v.w1).writeMem64
    (addr + 16#64) v.w2).writeMem64 (addr + 24#64) v.w3

inductive X86Instr where
  | movImm64 (dst : X86Gpr) (imm : BitVec 64)
  | movReg64 (dst src : X86Gpr)
  | mov32Zext (dst src : X86Gpr)
  | xor64 (dst src : X86Gpr)
  | xorImm64 (dst : X86Gpr) (imm : BitVec 64)
  | or64 (dst src : X86Gpr)
  | and64 (dst src : X86Gpr)
  | xorMem64 (dst base : X86Gpr) (disp : BitVec 64)
  | shrImm64 (dst : X86Gpr) (sh : Nat)
  | shlImm64 (dst : X86Gpr) (sh : Nat)
  | rorImm64 (dst : X86Gpr) (sh : Nat)
  | mul64 (src : X86Gpr)
  | imul64 (dst src : X86Gpr)
  | neg64 (dst : X86Gpr)
  | add64 (dst src : X86Gpr)
  | addImm64 (dst : X86Gpr) (imm : BitVec 64)
  | sub64 (dst src : X86Gpr)
  | sbbSelf64 (dst : X86Gpr)
  | sbbSelf32Zext (dst : X86Gpr)
  | adcx64 (dst src : X86Gpr)
  | adox64 (dst src : X86Gpr)
  | mulx64 (hi dstLo src : X86Gpr)
  | load64 (dst base : X86Gpr) (disp : BitVec 64)
  | store64 (base : X86Gpr) (disp : BitVec 64) (src : X86Gpr)
  | vmovdquLoad (dst : YmmReg) (base : X86Gpr) (disp : BitVec 64)
  | vmovdquStore (base : X86Gpr) (disp : BitVec 64) (src : YmmReg)
  | vpxor (dst a b : YmmReg)
  | vpxorMem (dst a : YmmReg) (base : X86Gpr) (disp : BitVec 64)
  | vpand (dst a b : YmmReg)
  | vpandn (dst a b : YmmReg)
  | vpor (dst a b : YmmReg)
  | vpslldq8 (dst src : YmmReg)
  | vpsrldq8 (dst src : YmmReg)
  | vpbroadcastqGpr (dst : YmmReg) (src : X86Gpr)
  | vpbroadcastbGpr (dst : YmmReg) (src : X86Gpr)
  | vgf2p8affineqb0 (dst src mat : YmmReg)
  | vgf2p8mulb (dst a b : YmmReg)
  | vpclmulqdq (dst a b : YmmReg) (imm8 : BitVec 8)
  | vzeroupper
  | cmovnz64 (dst src : X86Gpr)
  | div64 (divisor : X86Gpr)
  | loadIndexed64 (dst base idx : X86Gpr) (scale : BitVec 64)
  | vpgatherqq (dst : YmmReg) (base : X86Gpr) (vidx : YmmReg)
  deriving DecidableEq, Repr

inductive X86Stmt where
  | instr (i : X86Instr)
  | jccNz (condReg : X86Gpr) (thenBody elseBody : List X86Instr)
  | pubLoop (trips : Nat) (body : List X86Instr)
  | ret
  deriving DecidableEq, Repr

def execX86Instr (ins : X86Instr) (pc : Nat) (st : X86State) : X86State × LeakageEvent :=
  match ins with
  | .movImm64 dst imm =>
    (st.setGpr dst imm, LeakageEvent.clean pc)
  | .movReg64 dst src =>
    (st.setGpr dst (st.gpr src), LeakageEvent.clean pc)
  | .mov32Zext dst src =>
    let v := ((st.gpr src).truncate 32).zeroExtend 64
    (st.setGpr dst v, LeakageEvent.clean pc)
  | .xor64 dst src =>
    if dst == src then
      ({ (st.setGpr dst 0#64) with flags := { cf := false, of := false, zf := true } },
       LeakageEvent.clean pc)
    else
      let v := st.gpr dst ^^^ st.gpr src
      ({ (st.setGpr dst v) with flags := { cf := false, of := false, zf := (v == 0#64) } },
       LeakageEvent.clean pc)
  | .xorImm64 dst imm =>
    let v := st.gpr dst ^^^ imm
    ({ (st.setGpr dst v) with flags := { cf := false, of := false, zf := (v == 0#64) } },
     LeakageEvent.clean pc)
  | .or64 dst src =>
    let v := st.gpr dst ||| st.gpr src
    ({ (st.setGpr dst v) with flags := { cf := false, of := false, zf := (v == 0#64) } },
     LeakageEvent.clean pc)
  | .and64 dst src =>
    let v := st.gpr dst &&& st.gpr src
    ({ (st.setGpr dst v) with flags := { cf := false, of := false, zf := (v == 0#64) } },
     LeakageEvent.clean pc)
  | .xorMem64 dst base disp =>
    let addr := st.gpr base + disp
    let v := st.gpr dst ^^^ st.mem addr
    ({ (st.setGpr dst v) with flags := { cf := false, of := false, zf := (v == 0#64) } },
      LeakageEvent.clean pc [addr])
  | .shrImm64 dst sh =>
    let x := st.gpr dst
    let c := sh % 64
    let v := x >>> c
    let cf := if c == 0 then st.flags.cf else x.getLsbD (c - 1)
    let flags := if c == 0 then st.flags else
      { cf := cf, of := if c == 1 then x.getLsbD 63 else false, zf := (v == 0#64) }
    ({ (st.setGpr dst v) with flags := flags }, LeakageEvent.clean pc)
  | .shlImm64 dst sh =>
    let x := st.gpr dst
    let c := sh % 64
    let v := x <<< c
    let cf := if c == 0 then st.flags.cf else x.getLsbD (64 - c)
    let flags := if c == 0 then st.flags else
      { cf := cf, of := if c == 1 then (v.getLsbD 63 != cf) else false, zf := (v == 0#64) }
    ({ (st.setGpr dst v) with flags := flags }, LeakageEvent.clean pc)
  | .rorImm64 dst sh =>
    let x := st.gpr dst
    let c := sh % 64
    let v := if c == 0 then x else (x >>> c) ||| (x <<< (64 - c))
    let flags := if c == 0 then st.flags else
      { cf := v.getLsbD 63, of := if c == 1 then (v.getLsbD 63 != v.getLsbD 62) else false, zf := st.flags.zf }
    ({ (st.setGpr dst v) with flags := flags }, LeakageEvent.clean pc)
  | .mul64 src =>
    let prod := (st.gpr .rax).toNat * (st.gpr src).toNat
    let loVal := BitVec.ofNat 64 prod
    let hiVal := BitVec.ofNat 64 (prod / (2 ^ 64))
    let ovf := hiVal != 0#64
    ({ ((st.setGpr .rax loVal).setGpr .rdx hiVal) with
       flags := { cf := ovf, of := ovf, zf := false } },
     LeakageEvent.clean pc)
  | .imul64 dst src =>
    let a := st.gpr dst
    let b := st.gpr src
    let v := a * b
    let ovf := decide (a.toInt * b.toInt != v.toInt)
    ({ (st.setGpr dst v) with flags := { cf := ovf, of := ovf, zf := false } },
     LeakageEvent.clean pc)
  | .neg64 dst =>
    let x := st.gpr dst
    let v := 0#64 - x
    ({ (st.setGpr dst v) with flags := { cf := (x != 0#64), of := (x == 0x8000000000000000#64), zf := (v == 0#64) } },
     LeakageEvent.clean pc)
  | .add64 dst src =>
    let a := st.gpr dst
    let b := st.gpr src
    let sumNat := a.toNat + b.toNat
    let v := a + b
    ({ (st.setGpr dst v) with
       flags := { cf := decide (sumNat ≥ 2 ^ 64), of := (!(a.msb != b.msb) && (v.msb != a.msb)), zf := (v == 0#64) } },
     LeakageEvent.clean pc)
  | .addImm64 dst imm =>
    let a := st.gpr dst
    let sumNat := a.toNat + imm.toNat
    let v := a + imm
    ({ (st.setGpr dst v) with
       flags := { cf := decide (sumNat ≥ 2 ^ 64), of := (!(a.msb != imm.msb) && (v.msb != a.msb)), zf := (v == 0#64) } },
     LeakageEvent.clean pc)
  | .sub64 dst src =>
    let a := st.gpr dst
    let b := st.gpr src
    let v := a - b
    ({ (st.setGpr dst v) with
       flags := { cf := decide (a.toNat < b.toNat), of := ((a.msb != b.msb) && (v.msb != a.msb)), zf := (v == 0#64) } },
     LeakageEvent.clean pc)
  | .sbbSelf64 dst =>
    let mask := if st.flags.cf then 0xFFFFFFFFFFFFFFFF#64 else 0#64
    ({ (st.setGpr dst mask) with flags := { cf := st.flags.cf, of := false, zf := !st.flags.cf } },
     LeakageEvent.clean pc)
  | .sbbSelf32Zext dst =>
    let mask := if st.flags.cf then 0x00000000FFFFFFFF#64 else 0#64
    ({ (st.setGpr dst mask) with flags := { cf := st.flags.cf, of := false, zf := !st.flags.cf } },
     LeakageEvent.clean pc)
  | .adcx64 dst src =>
    let cIn := if st.flags.cf then 1 else 0
    let sumNat := (st.gpr dst).toNat + (st.gpr src).toNat + cIn
    let v := BitVec.ofNat 64 sumNat
    ({ (st.setGpr dst v) with flags := { st.flags with cf := decide (sumNat ≥ 2 ^ 64) } },
     LeakageEvent.clean pc)
  | .adox64 dst src =>
    let oIn := if st.flags.of then 1 else 0
    let sumNat := (st.gpr dst).toNat + (st.gpr src).toNat + oIn
    let v := BitVec.ofNat 64 sumNat
    ({ (st.setGpr dst v) with flags := { st.flags with of := decide (sumNat ≥ 2 ^ 64) } },
     LeakageEvent.clean pc)
  | .mulx64 hi dstLo src =>
    let prod := (st.gpr .rdx).toNat * (st.gpr src).toNat
    let loVal := BitVec.ofNat 64 prod
    let hiVal := BitVec.ofNat 64 (prod / (2 ^ 64))
    ((st.setGpr dstLo loVal).setGpr hi hiVal, LeakageEvent.clean pc)
  | .load64 dst base disp =>
    let addr := st.gpr base + disp
    (st.setGpr dst (st.mem addr), LeakageEvent.clean pc [addr])
  | .store64 base disp src =>
    let addr := st.gpr base + disp
    (st.writeMem64 addr (st.gpr src), LeakageEvent.clean pc [addr])
  | .vmovdquLoad dst base disp =>
    let addr := st.gpr base + disp
    (st.setYmm dst (st.readMem256 addr),
     LeakageEvent.clean pc [addr, addr + 8#64, addr + 16#64, addr + 24#64])
  | .vmovdquStore base disp src =>
    let addr := st.gpr base + disp
    (st.writeMem256 addr (st.ymm src),
     LeakageEvent.clean pc [addr, addr + 8#64, addr + 16#64, addr + 24#64])
  | .vpxor dst a b =>
    if a == b then
      (st.setYmm dst Vec256.zero, LeakageEvent.clean pc)
    else
      (st.setYmm dst (Vec256.xor (st.ymm a) (st.ymm b)), LeakageEvent.clean pc)
  | .vpxorMem dst a base disp =>
    let addr := st.gpr base + disp
    (st.setYmm dst (Vec256.xor (st.ymm a) (st.readMem256 addr)),
     LeakageEvent.clean pc [addr, addr + 8#64, addr + 16#64, addr + 24#64])
  | .vpand dst a b =>
    (st.setYmm dst (Vec256.and (st.ymm a) (st.ymm b)), LeakageEvent.clean pc)
  | .vpandn dst a b =>
    (st.setYmm dst (Vec256.andNot (st.ymm a) (st.ymm b)), LeakageEvent.clean pc)
  | .vpor dst a b =>
    (st.setYmm dst (Vec256.or (st.ymm a) (st.ymm b)), LeakageEvent.clean pc)
  | .vpslldq8 dst src =>
    (st.setYmm dst (Vec256.sllq8 (st.ymm src)), LeakageEvent.clean pc)
  | .vpsrldq8 dst src =>
    (st.setYmm dst (Vec256.srlq8 (st.ymm src)), LeakageEvent.clean pc)
  | .vpbroadcastqGpr dst src =>
    (st.setYmm dst (Vec256.broadcastQ (st.gpr src)), LeakageEvent.clean pc)
  | .vpbroadcastbGpr dst src =>
    (st.setYmm dst (Vec256.broadcastB ((st.gpr src).truncate 8)), LeakageEvent.clean pc)
  | .vgf2p8affineqb0 dst src mat =>
    (st.setYmm dst (Vec256.gfniAffine0 (st.ymm src) (st.ymm mat)), LeakageEvent.clean pc)
  | .vgf2p8mulb dst a b =>
    (st.setYmm dst (Vec256.gfniMul (st.ymm a) (st.ymm b)), LeakageEvent.clean pc)
  | .vpclmulqdq dst a b imm8 =>
    (st.setYmm dst (Vec256.vpclmulqdq (st.ymm a) (st.ymm b) imm8), LeakageEvent.clean pc)
  | .vzeroupper =>
    ({ st with ymm := (fun r => { (st.ymm r) with w2 := 0#64, w3 := 0#64 }), ymmUpperDirty := false }, LeakageEvent.clean pc)
  | .cmovnz64 dst src =>
    let v := if !st.flags.zf then st.gpr src else st.gpr dst
    let varOps :=
      if st.doitEnabled then []
      else [if st.flags.zf then 0#64 else 1#64, st.gpr dst, st.gpr src]
    (st.setGpr dst v,
     { pc := pc
       branchTaken := none
       memAddrs := []
       varLatencyOperands := varOps
       dirtyUpperYmmOnRet := false })
  | .div64 divisor =>
    let d := st.gpr divisor
    let q := if d == 0#64 then 0#64 else BitVec.ofNat 64 ((st.gpr .rax).toNat / d.toNat)
    let r := if d == 0#64 then 0#64 else BitVec.ofNat 64 ((st.gpr .rax).toNat % d.toNat)
    ((st.setGpr .rax q).setGpr .rdx r,
     { pc := pc
       branchTaken := none
       memAddrs := []
       varLatencyOperands := [st.gpr .rax, st.gpr .rdx, d]
       dirtyUpperYmmOnRet := false })
  | .loadIndexed64 dst base idx scale =>
    let addr := st.gpr base + st.gpr idx * scale
    (st.setGpr dst (st.mem addr), LeakageEvent.clean pc [addr])
  | .vpgatherqq dst base vidx =>
    let b := st.gpr base
    let vi := st.ymm vidx
    let a0 := b + vi.w0 * 8#64
    let a1 := b + vi.w1 * 8#64
    let a2 := b + vi.w2 * 8#64
    let a3 := b + vi.w3 * 8#64
    (st.setYmm dst ⟨st.mem a0, st.mem a1, st.mem a2, st.mem a3⟩,
     LeakageEvent.clean pc [a0, a1, a2, a3])

def execX86Block (blk : List X86Instr) (pc : Nat) (st : X86State) :
    X86State × List LeakageEvent :=
  match blk with
  | [] => (st, [])
  | ins :: rest =>
    let (st1, ev) := execX86Instr ins pc st
    let (st2, evs) := execX86Block rest (pc + 1) st1
    (st2, ev :: evs)

/-- Compose certified blocks at the advanced PC, preserving the full leakage trace. -/
theorem execX86Block_append (a b : List X86Instr) (pc : Nat) (st : X86State) :
    execX86Block (a ++ b) pc st =
      let first := execX86Block a pc st
      let second := execX86Block b (pc + a.length) first.1
      (second.1, first.2 ++ second.2) := by
  induction a generalizing pc st with
  | nil => simp only [List.nil_append, execX86Block, List.length_nil, Nat.add_zero]
  | cons ins rest ih =>
    simp only [List.cons_append, execX86Block, ih, List.length_cons,
      List.cons_append, Nat.add_assoc, Nat.add_comm 1]

/-- Regression: concatenation must not reset the suffix program counter. -/
theorem execX86Block_suffix_pc_not_reset (st : X86State) :
    (execX86Block [.movImm64 .rax 0#64, .movImm64 .rax 1#64] 0 st).2 ≠
      [LeakageEvent.clean 0 [], LeakageEvent.clean 0 []] := by
  intro h
  have hp := congrArg (List.map LeakageEvent.pc) h
  change [0, 1] = [0, 0] at hp
  contradiction

def execX86Loop (trips : Nat) (body : List X86Instr) (pc : Nat) (st : X86State) :
    X86State × List LeakageEvent :=
  match trips with
  | 0 => (st, [])
  | n + 1 =>
    let (st1, evs1) := execX86Block body pc st
    let (st2, evs2) := execX86Loop n body (pc + body.length) st1
    (st2, evs1 ++ evs2)

def execX86Prog (prog : List X86Stmt) (pc : Nat) (st : X86State) :
    X86State × List LeakageEvent :=
  match prog with
  | [] => (st, [])
  | stmt :: rest =>
    match stmt with
    | .instr ins =>
      let (st1, ev) := execX86Instr ins pc st
      let (st2, evs) := execX86Prog rest (pc + 1) st1
      (st2, ev :: evs)
    | .jccNz condReg thenBody elseBody =>
      let taken := st.gpr condReg != 0#64
      let brEv : LeakageEvent :=
        { pc := pc
          branchTaken := some taken
          memAddrs := []
          varLatencyOperands := []
          dirtyUpperYmmOnRet := false }
      let chosen := if taken then thenBody else elseBody
      let (st1, evs1) := execX86Block chosen (pc + 1) st
      let (st2, evs2) := execX86Prog rest (pc + 1 + chosen.length) st1
      (st2, brEv :: (evs1 ++ evs2))
    | .pubLoop trips body =>
      let (st1, evs1) := execX86Loop trips body pc st
      let (st2, evs2) := execX86Prog rest (pc + trips * body.length) st1
      (st2, evs1 ++ evs2)
    | .ret =>
      let retEv : LeakageEvent :=
        { pc := pc
          branchTaken := none
          memAddrs := []
          varLatencyOperands := []
          dirtyUpperYmmOnRet := st.ymmUpperDirty }
      (st, [retEv])

structure X86TaintState where
  gpr : X86Gpr → SecLabel
  ymm : YmmReg → SecLabel
  cf : SecLabel
  of : SecLabel
  zf : SecLabel
  doitAssumed : Bool
  upperYmmClean : Bool

def X86TaintState.setGpr (τ : X86TaintState) (r : X86Gpr) (l : SecLabel) : X86TaintState :=
  { τ with gpr := fun q => if q == r then l else τ.gpr q }

def X86TaintState.setYmm (τ : X86TaintState) (r : YmmReg) (l : SecLabel) : X86TaintState :=
  { τ with
    ymm := fun q => if q == r then l else τ.ymm q
    upperYmmClean := false }

@[expose]
def X86LowEq (memPol : BitVec 64 → SecLabel) (τ : X86TaintState) (s₁ s₂ : X86State) : Prop :=
  (∀ r, τ.gpr r = .pub → s₁.gpr r = s₂.gpr r) ∧
  (∀ y, τ.ymm y = .pub → s₁.ymm y = s₂.ymm y) ∧
  (τ.cf = .pub → s₁.flags.cf = s₂.flags.cf) ∧
  (τ.of = .pub → s₁.flags.of = s₂.flags.of) ∧
  (τ.zf = .pub → s₁.flags.zf = s₂.flags.zf) ∧
  (∀ addr, memPol addr = .pub → s₁.mem addr = s₂.mem addr) ∧
  (s₁.doitEnabled = s₂.doitEnabled) ∧
  (τ.doitAssumed = true → s₁.doitEnabled = true) ∧
  (s₁.ymmUpperDirty = s₂.ymmUpperDirty) ∧
  (τ.upperYmmClean = true → s₁.ymmUpperDirty = false)

def checkX86Instr (secHeap : Bool) (τ : X86TaintState) (ins : X86Instr) :
    Option X86TaintState :=
  match ins with
  | .movImm64 dst _ => some (τ.setGpr dst .pub)
  | .movReg64 dst src => some (τ.setGpr dst (τ.gpr src))
  | .mov32Zext dst src => some (τ.setGpr dst (τ.gpr src))
  | .xor64 dst src =>
    if dst == src then
      some { (τ.setGpr dst .pub) with cf := .pub, of := .pub, zf := .pub }
    else
      let l := (τ.gpr dst).join (τ.gpr src)
      some { (τ.setGpr dst l) with cf := .pub, of := .pub, zf := l }
  | .xorImm64 dst _ =>
    let l := τ.gpr dst
    some { (τ.setGpr dst l) with cf := .pub, of := .pub, zf := l }
  | .or64 dst src =>
    let l := (τ.gpr dst).join (τ.gpr src)
    some { (τ.setGpr dst l) with cf := .pub, of := .pub, zf := l }
  | .and64 dst src =>
    let l := (τ.gpr dst).join (τ.gpr src)
    some { (τ.setGpr dst l) with cf := .pub, of := .pub, zf := l }
  | .xorMem64 dst base _ =>
    if τ.gpr base == .pub then
      some { (τ.setGpr dst .sec) with cf := .pub, of := .pub, zf := .sec }
    else none
  | .shrImm64 dst sh =>
    let l := τ.gpr dst
    let c := sh % 64
    if c == 0 then some (τ.setGpr dst l)
    else some { (τ.setGpr dst l) with cf := l, of := if c == 1 then l else .sec, zf := l }
  | .shlImm64 dst sh =>
    let l := τ.gpr dst
    let c := sh % 64
    if c == 0 then some (τ.setGpr dst l)
    else some { (τ.setGpr dst l) with cf := l, of := if c == 1 then l else .sec, zf := l }
  | .rorImm64 dst sh =>
    let l := τ.gpr dst
    let c := sh % 64
    if c == 0 then some (τ.setGpr dst l)
    else some { (τ.setGpr dst l) with cf := l, of := if c == 1 then l else .sec }
  | .mul64 src =>
    let l := (τ.gpr .rax).join (τ.gpr src)
    some { ((τ.setGpr .rax l).setGpr .rdx l) with cf := l, of := l, zf := .sec }
  | .imul64 dst src =>
    let l := (τ.gpr dst).join (τ.gpr src)
    some { (τ.setGpr dst l) with cf := l, of := l, zf := .sec }
  | .neg64 dst =>
    let l := τ.gpr dst
    some { (τ.setGpr dst l) with cf := l, of := l, zf := l }
  | .add64 dst src =>
    let l := (τ.gpr dst).join (τ.gpr src)
    some { (τ.setGpr dst l) with cf := l, of := l, zf := l }
  | .addImm64 dst _ =>
    let l := τ.gpr dst
    some { (τ.setGpr dst l) with cf := l, of := l, zf := l }
  | .sub64 dst src =>
    let l := (τ.gpr dst).join (τ.gpr src)
    some { (τ.setGpr dst l) with cf := l, of := l, zf := l }
  | .sbbSelf64 dst =>
    let l := τ.cf
    some { (τ.setGpr dst l) with of := .pub, zf := l }
  | .sbbSelf32Zext dst =>
    let l := τ.cf
    some { (τ.setGpr dst l) with of := .pub, zf := l }
  | .adcx64 dst src =>
    let l := ((τ.gpr dst).join (τ.gpr src)).join τ.cf
    some { (τ.setGpr dst l) with cf := l }
  | .adox64 dst src =>
    let l := ((τ.gpr dst).join (τ.gpr src)).join τ.of
    some { (τ.setGpr dst l) with of := l }
  | .mulx64 hi dstLo src =>
    let l := (τ.gpr .rdx).join (τ.gpr src)
    some ((τ.setGpr dstLo l).setGpr hi l)
  | .load64 dst base _ =>
    if τ.gpr base == .pub then some (τ.setGpr dst .sec) else none
  | .store64 base _ src =>
    if τ.gpr base == .pub && (secHeap || τ.gpr src == .pub) then some τ else none
  | .vmovdquLoad dst base _ =>
    if τ.gpr base == .pub then some (τ.setYmm dst .sec) else none
  | .vmovdquStore base _ src =>
    if τ.gpr base == .pub && (secHeap || τ.ymm src == .pub) then some τ else none
  | .vpxor dst a b =>
    if a == b then some (τ.setYmm dst .pub)
    else some (τ.setYmm dst ((τ.ymm a).join (τ.ymm b)))
  | .vpxorMem dst a base _ =>
    if τ.gpr base == .pub then some (τ.setYmm dst ((τ.ymm a).join .sec)) else none
  | .vpand dst a b => some (τ.setYmm dst ((τ.ymm a).join (τ.ymm b)))
  | .vpandn dst a b => some (τ.setYmm dst ((τ.ymm a).join (τ.ymm b)))
  | .vpor dst a b => some (τ.setYmm dst ((τ.ymm a).join (τ.ymm b)))
  | .vpslldq8 dst src => some (τ.setYmm dst (τ.ymm src))
  | .vpsrldq8 dst src => some (τ.setYmm dst (τ.ymm src))
  | .vpbroadcastqGpr dst src => some (τ.setYmm dst (τ.gpr src))
  | .vpbroadcastbGpr dst src => some (τ.setYmm dst (τ.gpr src))
  | .vgf2p8affineqb0 dst src mat => some (τ.setYmm dst ((τ.ymm src).join (τ.ymm mat)))
  | .vgf2p8mulb dst a b => some (τ.setYmm dst ((τ.ymm a).join (τ.ymm b)))
  | .vpclmulqdq dst a b _ => some (τ.setYmm dst ((τ.ymm a).join (τ.ymm b)))
  | .vzeroupper => some { τ with upperYmmClean := true }
  | .cmovnz64 dst src =>
    let l := (τ.zf.join (τ.gpr dst)).join (τ.gpr src)
    if l == .pub then some (τ.setGpr dst .pub)
    else if τ.doitAssumed then some (τ.setGpr dst .sec)
    else none
  | .div64 divisor =>
    if τ.gpr .rax == .pub && τ.gpr .rdx == .pub && τ.gpr divisor == .pub then
      some ((τ.setGpr .rax .pub).setGpr .rdx .pub)
    else
      none
  | .loadIndexed64 dst base idx _ =>
    if τ.gpr base == .pub && τ.gpr idx == .pub then some (τ.setGpr dst .sec) else none
  | .vpgatherqq dst base vidx =>
    if τ.gpr base == .pub && τ.ymm vidx == .pub then some (τ.setYmm dst .sec) else none

def checkX86Block (secHeap : Bool) (τ : X86TaintState) (blk : List X86Instr) :
    Option X86TaintState :=
  match blk with
  | [] => some τ
  | ins :: rest =>
    match checkX86Instr secHeap τ ins with
    | none => none
    | some τ1 => checkX86Block secHeap τ1 rest

def checkX86Loop (secHeap : Bool) (trips : Nat) (τ : X86TaintState) (body : List X86Instr) :
    Option X86TaintState :=
  match trips with
  | 0 => some τ
  | n + 1 =>
    match checkX86Block secHeap τ body with
    | none => none
    | some τ1 => checkX86Loop secHeap n τ1 body

def checkX86Prog (secHeap : Bool) (τ : X86TaintState) (prog : List X86Stmt) :
    Option X86TaintState :=
  match prog with
  | [] => some τ
  | stmt :: rest =>
    match stmt with
    | .instr ins =>
      match checkX86Instr secHeap τ ins with
      | none => none
      | some τ1 => checkX86Prog secHeap τ1 rest
    | .jccNz condReg thenBody elseBody =>
      if τ.gpr condReg == .pub then
        match checkX86Block secHeap τ thenBody, checkX86Block secHeap τ elseBody with
        | some τT, some τE =>
          let τJoin : X86TaintState :=
            { gpr := fun r => (τT.gpr r).join (τE.gpr r)
              ymm := fun y => (τT.ymm y).join (τE.ymm y)
              cf := τT.cf.join τE.cf
              of := τT.of.join τE.of
              zf := τT.zf.join τE.zf
              doitAssumed := τ.doitAssumed
              upperYmmClean := τT.upperYmmClean && τE.upperYmmClean }
          checkX86Prog secHeap τJoin rest
        | _, _ => none
      else
        none
    | .pubLoop trips body =>
      match checkX86Loop secHeap trips τ body with
      | none => none
      | some τ1 => checkX86Prog secHeap τ1 rest
    | .ret =>
      if τ.upperYmmClean then some τ else none

theorem x86_setGpr_lowEq (memPol : BitVec 64 → SecLabel) (τ : X86TaintState)
    (s₁ s₂ : X86State) (r : X86Gpr) (l : SecLabel) (v₁ v₂ : BitVec 64)
    (hLow : X86LowEq memPol τ s₁ s₂) (hv : l = .pub → v₁ = v₂) :
    X86LowEq memPol (τ.setGpr r l) (s₁.setGpr r v₁) (s₂.setGpr r v₂) := by
  rcases hLow with ⟨hgpr, hymm, hcf, hof, hzf, hmem, hdoitEq, hdoitReq, hymmEq, hymmClean⟩
  refine ⟨?_, hymm, hcf, hof, hzf, hmem, hdoitEq, hdoitReq, hymmEq, hymmClean⟩
  intro q hq
  simp only [X86TaintState.setGpr, X86State.setGpr] at hq ⊢
  split at hq
  · rename_i heq; simp [heq, hv hq]
  · rename_i hne; simp [hne, hgpr q hq]

theorem x86_setYmm_lowEq (memPol : BitVec 64 → SecLabel) (τ : X86TaintState)
    (s₁ s₂ : X86State) (y : YmmReg) (l : SecLabel) (v₁ v₂ : Vec256)
    (hLow : X86LowEq memPol τ s₁ s₂) (hv : l = .pub → v₁ = v₂) :
    X86LowEq memPol (τ.setYmm y l) (s₁.setYmm y v₁) (s₂.setYmm y v₂) := by
  rcases hLow with ⟨hgpr, hymm, hcf, hof, hzf, hmem, hdoitEq, hdoitReq, _, _⟩
  refine ⟨hgpr, ?_, hcf, hof, hzf, hmem, hdoitEq, hdoitReq, rfl, ?_⟩
  · intro q hq
    simp only [X86TaintState.setYmm, X86State.setYmm] at hq ⊢
    split at hq
    · rename_i heq; simp [heq, hv hq]
    · rename_i hne; simp [hne, hymm q hq]
  · intro h; simp [X86TaintState.setYmm] at h

theorem x86_writeMem64_lowEq (memPol : BitVec 64 → SecLabel) (secHeap : Bool)
    (τ : X86TaintState) (s₁ s₂ : X86State) (addr v₁ v₂ : BitVec 64)
    (hPol : secHeap = true → ∀ a, memPol a = .sec)
    (hLow : X86LowEq memPol τ s₁ s₂) (hv : secHeap = false → v₁ = v₂) :
    X86LowEq memPol τ (s₁.writeMem64 addr v₁) (s₂.writeMem64 addr v₂) := by
  rcases hLow with ⟨hgpr, hymm, hcf, hof, hzf, hmem, hdoitEq, hdoitReq, hymmEq, hymmClean⟩
  refine ⟨hgpr, hymm, hcf, hof, hzf, ?_, hdoitEq, hdoitReq, hymmEq, hymmClean⟩
  intro a ha
  simp only [X86State.writeMem64]
  split
  · cases hsh : secHeap
    · exact hv hsh
    · have hsec := hPol hsh a
      rw [ha] at hsec
      cases hsec
  · exact hmem a ha

theorem checkX86Instr_doitAssumed (secHeap : Bool) (τ τ' : X86TaintState) (ins : X86Instr)
    (h : checkX86Instr secHeap τ ins = some τ') : τ'.doitAssumed = τ.doitAssumed := by
  cases ins <;> simp only [checkX86Instr] at h
  all_goals
    try (split at h <;> try (split at h))
    all_goals (simp_all [X86TaintState.setGpr, X86TaintState.setYmm]; try (subst h; rfl))

theorem checkX86Block_doitAssumed (secHeap : Bool) (blk : List X86Instr) (τ τ' : X86TaintState)
    (h : checkX86Block secHeap τ blk = some τ') : τ'.doitAssumed = τ.doitAssumed := by
  induction blk generalizing τ with
  | nil => simp [checkX86Block] at h; subst h; rfl
  | cons ins rest ih =>
    simp only [checkX86Block] at h
    cases h1 : checkX86Instr secHeap τ ins with
    | none => simp [h1] at h
    | some τ1 =>
      simp [h1] at h
      exact (ih τ1 h).trans (checkX86Instr_doitAssumed secHeap τ τ1 ins h1)

theorem checkX86Instr_sound
    (memPol : BitVec 64 → SecLabel) (secHeap : Bool)
    (hPol : secHeap = true → ∀ a, memPol a = .sec)
    (τ τ' : X86TaintState) (ins : X86Instr) (pc : Nat)
    (hCheck : checkX86Instr secHeap τ ins = some τ')
    (s₁ s₂ : X86State) (hLow : X86LowEq memPol τ s₁ s₂) :
    (execX86Instr ins pc s₁).2 = (execX86Instr ins pc s₂).2 ∧
    X86LowEq memPol τ' (execX86Instr ins pc s₁).1 (execX86Instr ins pc s₂).1 := by
  rcases hLow with ⟨hgpr, hymm, hcf, hof, hzf, hmem, hdoitEq, hdoitReq, hymmEq, hymmClean⟩
  have hLowOrig : X86LowEq memPol τ s₁ s₂ :=
    ⟨hgpr, hymm, hcf, hof, hzf, hmem, hdoitEq, hdoitReq, hymmEq, hymmClean⟩
  cases ins with
  | movImm64 dst imm =>
    simp [checkX86Instr] at hCheck; subst hCheck
    exact ⟨rfl, x86_setGpr_lowEq memPol τ s₁ s₂ dst .pub imm imm hLowOrig (fun _ => rfl)⟩
  | movReg64 dst src =>
    simp [checkX86Instr] at hCheck; subst hCheck
    exact ⟨rfl, x86_setGpr_lowEq memPol τ s₁ s₂ dst (τ.gpr src) _ _ hLowOrig (hgpr src)⟩
  | mov32Zext dst src =>
    simp [checkX86Instr] at hCheck; subst hCheck
    exact ⟨rfl, x86_setGpr_lowEq memPol τ s₁ s₂ dst (τ.gpr src) _ _ hLowOrig
      (fun hp => by rw [hgpr src hp])⟩
  | xor64 dst src =>
    simp only [checkX86Instr, execX86Instr] at hCheck ⊢
    by_cases hds : (dst == src) = true
    · simp [hds] at hCheck ⊢; subst hCheck
      have hSet := x86_setGpr_lowEq memPol τ s₁ s₂ dst .pub 0#64 0#64 hLowOrig (fun _ => rfl)
      rcases hSet with ⟨hg1, hy1, _, _, _, hm1, hd1, hdr1, hyEq1, hyCl1⟩
      exact ⟨hg1, hy1, fun _ => rfl, fun _ => rfl, fun _ => rfl, hm1, hd1, hdr1, hyEq1, hyCl1⟩
    · simp [hds] at hCheck ⊢; subst hCheck
      let l := (τ.gpr dst).join (τ.gpr src)
      have hv : l = .pub → s₁.gpr dst ^^^ s₁.gpr src = s₂.gpr dst ^^^ s₂.gpr src := by
        intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h1, h2⟩
        rw [hgpr dst h1, hgpr src h2]
      have hSet := x86_setGpr_lowEq memPol τ s₁ s₂ dst l _ _ hLowOrig hv
      rcases hSet with ⟨hg1, hy1, _, _, _, hm1, hd1, hdr1, hyEq1, hyCl1⟩
      exact ⟨hg1, hy1, fun _ => rfl, fun _ => rfl, fun hl => by rw [hv hl],
             hm1, hd1, hdr1, hyEq1, hyCl1⟩
  | xorImm64 dst imm =>
    simp [checkX86Instr, execX86Instr] at hCheck ⊢; subst hCheck
    have hv : τ.gpr dst = .pub → s₁.gpr dst ^^^ imm = s₂.gpr dst ^^^ imm := by
      intro hl; rw [hgpr dst hl]
    have hSet := x86_setGpr_lowEq memPol τ s₁ s₂ dst (τ.gpr dst) _ _ hLowOrig hv
    rcases hSet with ⟨hg1, hy1, _, _, _, hm1, hd1, hdr1, hyEq1, hyCl1⟩
    exact ⟨hg1, hy1, fun _ => rfl, fun _ => rfl, fun hl => by rw [hv hl],
           hm1, hd1, hdr1, hyEq1, hyCl1⟩
  | or64 dst src =>
    simp [checkX86Instr, execX86Instr] at hCheck ⊢; subst hCheck
    let l := (τ.gpr dst).join (τ.gpr src)
    have hv : l = .pub → s₁.gpr dst ||| s₁.gpr src = s₂.gpr dst ||| s₂.gpr src := by
      intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h1, h2⟩
      rw [hgpr dst h1, hgpr src h2]
    have hSet := x86_setGpr_lowEq memPol τ s₁ s₂ dst l _ _ hLowOrig hv
    rcases hSet with ⟨hg1, hy1, _, _, _, hm1, hd1, hdr1, hyEq1, hyCl1⟩
    exact ⟨hg1, hy1, fun _ => rfl, fun _ => rfl, fun hl => by rw [hv hl],
           hm1, hd1, hdr1, hyEq1, hyCl1⟩
  | and64 dst src =>
    simp [checkX86Instr, execX86Instr] at hCheck ⊢; subst hCheck
    let l := (τ.gpr dst).join (τ.gpr src)
    have hv : l = .pub → s₁.gpr dst &&& s₁.gpr src = s₂.gpr dst &&& s₂.gpr src := by
      intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h1, h2⟩
      rw [hgpr dst h1, hgpr src h2]
    have hSet := x86_setGpr_lowEq memPol τ s₁ s₂ dst l _ _ hLowOrig hv
    rcases hSet with ⟨hg1, hy1, _, _, _, hm1, hd1, hdr1, hyEq1, hyCl1⟩
    exact ⟨hg1, hy1, fun _ => rfl, fun _ => rfl, fun hl => by rw [hv hl],
           hm1, hd1, hdr1, hyEq1, hyCl1⟩
  | xorMem64 dst base disp =>
    simp only [checkX86Instr] at hCheck
    split at hCheck <;> simp_all
    rename_i hb; subst hCheck
    refine ⟨by simp [execX86Instr, LeakageEvent.clean, hgpr base hb], ?_⟩
    have hs := x86_setGpr_lowEq memPol τ s₁ s₂ dst .sec
      (s₁.gpr dst ^^^ s₁.mem (s₁.gpr base + disp))
      (s₂.gpr dst ^^^ s₂.mem (s₂.gpr base + disp)) hLowOrig (by intro h; cases h)
    rcases hs with ⟨hg, hy, _, _, _, hm, hd, hdr, he, hc⟩
    exact ⟨hg, hy, fun _ => rfl, fun _ => rfl, (by intro h; cases h), hm, hd, hdr, he, hc⟩
  | shrImm64 dst sh =>
    by_cases hz : (sh % 64 == 0) = true
    · simp [checkX86Instr, hz] at hCheck; subst hCheck
      refine ⟨by simp [execX86Instr, hz], ?_⟩
      simpa [execX86Instr, hz, X86State.setGpr] using
        (x86_setGpr_lowEq memPol τ s₁ s₂ dst (τ.gpr dst)
          (s₁.gpr dst >>> (sh % 64)) (s₂.gpr dst >>> (sh % 64)) hLowOrig
          (fun hl => by rw [hgpr dst hl]))
    · simp [checkX86Instr, hz] at hCheck; subst hCheck
      have hSet := x86_setGpr_lowEq memPol τ s₁ s₂ dst (τ.gpr dst)
        (s₁.gpr dst >>> (sh % 64)) (s₂.gpr dst >>> (sh % 64)) hLowOrig
        (fun hl => by rw [hgpr dst hl])
      rcases hSet with ⟨hg, hy, _, _, _, hm, hd, hdr, he, hc⟩
      simp only [execX86Instr, hz, Bool.false_eq_true, ↓reduceIte]
      exact ⟨True.intro, hg, hy, (fun hl => by rw [hgpr dst hl]),
        (fun hl => by
          by_cases h1 : (sh % 64 == 1) = true
          · simp [h1] at hl ⊢; rw [hgpr dst hl]
          · simp [h1] at hl),
        (fun hl => by rw [hgpr dst hl]),
        hm, hd, hdr, he, hc⟩
  | shlImm64 dst sh =>
    by_cases hz : (sh % 64 == 0) = true
    · simp [checkX86Instr, hz] at hCheck; subst hCheck
      refine ⟨by simp [execX86Instr, hz], ?_⟩
      simpa [execX86Instr, hz, X86State.setGpr] using
        (x86_setGpr_lowEq memPol τ s₁ s₂ dst (τ.gpr dst)
          (s₁.gpr dst <<< (sh % 64)) (s₂.gpr dst <<< (sh % 64)) hLowOrig
          (fun hl => by rw [hgpr dst hl]))
    · simp [checkX86Instr, hz] at hCheck; subst hCheck
      have hSet := x86_setGpr_lowEq memPol τ s₁ s₂ dst (τ.gpr dst)
        (s₁.gpr dst <<< (sh % 64)) (s₂.gpr dst <<< (sh % 64)) hLowOrig
        (fun hl => by rw [hgpr dst hl])
      rcases hSet with ⟨hg, hy, _, _, _, hm, hd, hdr, he, hc⟩
      simp only [execX86Instr, hz, Bool.false_eq_true, ↓reduceIte]
      exact ⟨True.intro, hg, hy, (fun hl => by rw [hgpr dst hl]),
        (fun hl => by
          by_cases h1 : (sh % 64 == 1) = true
          · simp [h1] at hl ⊢; rw [hgpr dst hl]
          · simp [h1] at hl),
        (fun hl => by rw [hgpr dst hl]),
        hm, hd, hdr, he, hc⟩
  | rorImm64 dst sh =>
    by_cases hz : (sh % 64 == 0) = true
    · simp [checkX86Instr, hz] at hCheck; subst hCheck
      refine ⟨by simp [execX86Instr, hz], ?_⟩
      simpa [execX86Instr, hz, X86State.setGpr] using
        (x86_setGpr_lowEq memPol τ s₁ s₂ dst (τ.gpr dst)
          (s₁.gpr dst) (s₂.gpr dst) hLowOrig
          (fun hl => by rw [hgpr dst hl]))
    · simp [checkX86Instr, hz] at hCheck; subst hCheck
      have hSet := x86_setGpr_lowEq memPol τ s₁ s₂ dst (τ.gpr dst)
        ((s₁.gpr dst >>> (sh % 64)) ||| (s₁.gpr dst <<< (64 - sh % 64)))
        ((s₂.gpr dst >>> (sh % 64)) ||| (s₂.gpr dst <<< (64 - sh % 64))) hLowOrig
        (fun hl => by rw [hgpr dst hl])
      rcases hSet with ⟨hg, hy, _, _, hzOld, hm, hd, hdr, he, hc⟩
      simp only [execX86Instr, hz, Bool.false_eq_true, ↓reduceIte]
      exact ⟨True.intro, hg, hy, (fun hl => by rw [hgpr dst hl]),
        (fun hl => by
          by_cases h1 : (sh % 64 == 1) = true
          · simp [h1] at hl ⊢; rw [hgpr dst hl]
          · simp [h1] at hl),
        hzOld, hm, hd, hdr, he, hc⟩
  | mul64 src =>
    simp [checkX86Instr, execX86Instr] at hCheck ⊢; subst hCheck
    let l := (τ.gpr .rax).join (τ.gpr src)
    have hOps : l = .pub → s₁.gpr .rax = s₂.gpr .rax ∧ s₁.gpr src = s₂.gpr src := by
      intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h1, h2⟩
      exact ⟨hgpr .rax h1, hgpr src h2⟩
    have hSet1 := x86_setGpr_lowEq memPol τ s₁ s₂ .rax l
      (BitVec.ofNat 64 ((s₁.gpr .rax).toNat * (s₁.gpr src).toNat))
      (BitVec.ofNat 64 ((s₂.gpr .rax).toNat * (s₂.gpr src).toNat))
      hLowOrig (fun hl => by rcases hOps hl with ⟨e1, e2⟩; rw [e1, e2])
    have hSet2 := x86_setGpr_lowEq memPol _ _ _ .rdx l
      (BitVec.ofNat 64 (((s₁.gpr .rax).toNat * (s₁.gpr src).toNat) / (2 ^ 64)))
      (BitVec.ofNat 64 (((s₂.gpr .rax).toNat * (s₂.gpr src).toNat) / (2 ^ 64)))
      hSet1 (fun hl => by rcases hOps hl with ⟨e1, e2⟩; rw [e1, e2])
    rcases hSet2 with ⟨hg2, hy2, _, _, _, hm2, hd2, hdr2, hyEq2, hyCl2⟩
    exact ⟨hg2, hy2,
      (fun hl => by rcases hOps hl with ⟨e1, e2⟩; rw [e1, e2]),
      (fun hl => by rcases hOps hl with ⟨e1, e2⟩; rw [e1, e2]),
      (by intro h; cases h), hm2, hd2, hdr2, hyEq2, hyCl2⟩
  | imul64 dst src =>
    simp [checkX86Instr, execX86Instr] at hCheck ⊢; subst hCheck
    let l := (τ.gpr dst).join (τ.gpr src)
    have hOps : l = .pub → s₁.gpr dst = s₂.gpr dst ∧ s₁.gpr src = s₂.gpr src := by
      intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h1, h2⟩
      exact ⟨hgpr dst h1, hgpr src h2⟩
    have hSet := x86_setGpr_lowEq memPol τ s₁ s₂ dst l
      (s₁.gpr dst * s₁.gpr src) (s₂.gpr dst * s₂.gpr src)
      hLowOrig (fun hl => by rcases hOps hl with ⟨e1, e2⟩; rw [e1, e2])
    rcases hSet with ⟨hg1, hy1, _, _, _, hm1, hd1, hdr1, hyEq1, hyCl1⟩
    exact ⟨hg1, hy1,
      (fun hl => by rcases hOps hl with ⟨e1, e2⟩; rw [e1, e2]),
      (fun hl => by rcases hOps hl with ⟨e1, e2⟩; rw [e1, e2]),
      (by intro h; cases h), hm1, hd1, hdr1, hyEq1, hyCl1⟩
  | neg64 dst =>
    simp [checkX86Instr, execX86Instr] at hCheck ⊢; subst hCheck
    have hSet := x86_setGpr_lowEq memPol τ s₁ s₂ dst (τ.gpr dst)
      (0#64 - s₁.gpr dst) (0#64 - s₂.gpr dst) hLowOrig (fun hl => by rw [hgpr dst hl])
    rcases hSet with ⟨hg1, hy1, _, _, _, hm1, hd1, hdr1, hyEq1, hyCl1⟩
    exact ⟨hg1, hy1, fun hl => by rw [hgpr dst hl], fun hl => by rw [hgpr dst hl], fun hl => by rw [hgpr dst hl],
           hm1, hd1, hdr1, hyEq1, hyCl1⟩
  | add64 dst src =>
    simp [checkX86Instr, execX86Instr] at hCheck ⊢; subst hCheck
    let l := (τ.gpr dst).join (τ.gpr src)
    have hOps : l = .pub → s₁.gpr dst = s₂.gpr dst ∧ s₁.gpr src = s₂.gpr src := by
      intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h1, h2⟩
      exact ⟨hgpr dst h1, hgpr src h2⟩
    have hSet := x86_setGpr_lowEq memPol τ s₁ s₂ dst l
      (s₁.gpr dst + s₁.gpr src) (s₂.gpr dst + s₂.gpr src) hLowOrig
      (fun hl => by rcases hOps hl with ⟨e1, e2⟩; rw [e1, e2])
    rcases hSet with ⟨hg1, hy1, _, _, _, hm1, hd1, hdr1, hyEq1, hyCl1⟩
    exact ⟨hg1, hy1, fun hl => by rcases hOps hl with ⟨e1, e2⟩; rw [e1, e2],
           (fun hl => by rcases hOps hl with ⟨e1, e2⟩; rw [e1, e2]), fun hl => by rcases hOps hl with ⟨e1, e2⟩; rw [e1, e2],
           hm1, hd1, hdr1, hyEq1, hyCl1⟩
  | addImm64 dst imm =>
    simp [checkX86Instr, execX86Instr] at hCheck ⊢; subst hCheck
    have hSet := x86_setGpr_lowEq memPol τ s₁ s₂ dst (τ.gpr dst)
      (s₁.gpr dst + imm) (s₂.gpr dst + imm) hLowOrig
      (fun hl => by rw [hgpr dst hl])
    rcases hSet with ⟨hg1, hy1, _, _, _, hm1, hd1, hdr1, hyEq1, hyCl1⟩
    exact ⟨hg1, hy1, fun hl => by rw [hgpr dst hl], fun hl => by rw [hgpr dst hl], fun hl => by rw [hgpr dst hl],
           hm1, hd1, hdr1, hyEq1, hyCl1⟩
  | sub64 dst src =>
    simp [checkX86Instr, execX86Instr] at hCheck ⊢; subst hCheck
    let l := (τ.gpr dst).join (τ.gpr src)
    have hOps : l = .pub → s₁.gpr dst = s₂.gpr dst ∧ s₁.gpr src = s₂.gpr src := by
      intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h1, h2⟩
      exact ⟨hgpr dst h1, hgpr src h2⟩
    have hSet := x86_setGpr_lowEq memPol τ s₁ s₂ dst l
      (s₁.gpr dst - s₁.gpr src) (s₂.gpr dst - s₂.gpr src) hLowOrig
      (fun hl => by rcases hOps hl with ⟨e1, e2⟩; rw [e1, e2])
    rcases hSet with ⟨hg1, hy1, _, _, _, hm1, hd1, hdr1, hyEq1, hyCl1⟩
    exact ⟨hg1, hy1, fun hl => by rcases hOps hl with ⟨e1, e2⟩; rw [e1, e2],
           (fun hl => by rcases hOps hl with ⟨e1, e2⟩; rw [e1, e2]), fun hl => by rcases hOps hl with ⟨e1, e2⟩; rw [e1, e2],
           hm1, hd1, hdr1, hyEq1, hyCl1⟩
  | sbbSelf64 dst =>
    simp [checkX86Instr, execX86Instr] at hCheck ⊢; subst hCheck
    have hSet := x86_setGpr_lowEq memPol τ s₁ s₂ dst τ.cf
      (if s₁.flags.cf then 0xFFFFFFFFFFFFFFFF#64 else 0#64)
      (if s₂.flags.cf then 0xFFFFFFFFFFFFFFFF#64 else 0#64)
      hLowOrig (fun hl => by rw [hcf hl])
    rcases hSet with ⟨hg1, hy1, hc1, _, _, hm1, hd1, hdr1, hyEq1, hyCl1⟩
    exact ⟨hg1, hy1, hc1, fun _ => rfl, fun hl => by rw [hcf hl], hm1, hd1, hdr1, hyEq1, hyCl1⟩
  | sbbSelf32Zext dst =>
    simp [checkX86Instr, execX86Instr] at hCheck ⊢; subst hCheck
    have hSet := x86_setGpr_lowEq memPol τ s₁ s₂ dst τ.cf
      (if s₁.flags.cf then 0x00000000FFFFFFFF#64 else 0#64)
      (if s₂.flags.cf then 0x00000000FFFFFFFF#64 else 0#64)
      hLowOrig (fun hl => by rw [hcf hl])
    rcases hSet with ⟨hg1, hy1, hc1, _, _, hm1, hd1, hdr1, hyEq1, hyCl1⟩
    exact ⟨hg1, hy1, hc1, fun _ => rfl, fun hl => by rw [hcf hl], hm1, hd1, hdr1, hyEq1, hyCl1⟩
  | adcx64 dst src =>
    simp [checkX86Instr, execX86Instr] at hCheck ⊢; subst hCheck
    let l := ((τ.gpr dst).join (τ.gpr src)).join τ.cf
    have hOps : l = .pub →
        s₁.gpr dst = s₂.gpr dst ∧ s₁.gpr src = s₂.gpr src ∧ s₁.flags.cf = s₂.flags.cf := by
      intro hl
      rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h12, hc⟩
      rcases (SecLabel.join_eq_pub_iff _ _).mp h12 with ⟨h1, h2⟩
      exact ⟨hgpr dst h1, hgpr src h2, hcf hc⟩
    have hSet := x86_setGpr_lowEq memPol τ s₁ s₂ dst l
      (BitVec.ofNat 64 ((s₁.gpr dst).toNat + (s₁.gpr src).toNat + if s₁.flags.cf then 1 else 0))
      (BitVec.ofNat 64 ((s₂.gpr dst).toNat + (s₂.gpr src).toNat + if s₂.flags.cf then 1 else 0))
      hLowOrig (fun hl => by rcases hOps hl with ⟨e1, e2, ec⟩; rw [e1, e2, ec])
    rcases hSet with ⟨hg1, hy1, _, ho1, hz1, hm1, hd1, hdr1, hyEq1, hyCl1⟩
    exact ⟨hg1, hy1, fun hl => by rcases hOps hl with ⟨e1, e2, ec⟩; rw [e1, e2, ec],
           ho1, hz1, hm1, hd1, hdr1, hyEq1, hyCl1⟩
  | adox64 dst src =>
    simp [checkX86Instr, execX86Instr] at hCheck ⊢; subst hCheck
    let l := ((τ.gpr dst).join (τ.gpr src)).join τ.of
    have hOps : l = .pub →
        s₁.gpr dst = s₂.gpr dst ∧ s₁.gpr src = s₂.gpr src ∧ s₁.flags.of = s₂.flags.of := by
      intro hl
      rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h12, ho⟩
      rcases (SecLabel.join_eq_pub_iff _ _).mp h12 with ⟨h1, h2⟩
      exact ⟨hgpr dst h1, hgpr src h2, hof ho⟩
    have hSet := x86_setGpr_lowEq memPol τ s₁ s₂ dst l
      (BitVec.ofNat 64 ((s₁.gpr dst).toNat + (s₁.gpr src).toNat + if s₁.flags.of then 1 else 0))
      (BitVec.ofNat 64 ((s₂.gpr dst).toNat + (s₂.gpr src).toNat + if s₂.flags.of then 1 else 0))
      hLowOrig (fun hl => by rcases hOps hl with ⟨e1, e2, eo⟩; rw [e1, e2, eo])
    rcases hSet with ⟨hg1, hy1, hc1, _, hz1, hm1, hd1, hdr1, hyEq1, hyCl1⟩
    exact ⟨hg1, hy1, hc1, fun hl => by rcases hOps hl with ⟨e1, e2, eo⟩; rw [e1, e2, eo],
           hz1, hm1, hd1, hdr1, hyEq1, hyCl1⟩
  | mulx64 hi dstLo src =>
    simp [checkX86Instr, execX86Instr] at hCheck ⊢; subst hCheck
    let l := (τ.gpr .rdx).join (τ.gpr src)
    have hOps : l = .pub → s₁.gpr .rdx = s₂.gpr .rdx ∧ s₁.gpr src = s₂.gpr src := by
      intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h1, h2⟩
      exact ⟨hgpr .rdx h1, hgpr src h2⟩
    have hSet1 := x86_setGpr_lowEq memPol τ s₁ s₂ dstLo l
      (BitVec.ofNat 64 ((s₁.gpr .rdx).toNat * (s₁.gpr src).toNat))
      (BitVec.ofNat 64 ((s₂.gpr .rdx).toNat * (s₂.gpr src).toNat))
      hLowOrig (fun hl => by rcases hOps hl with ⟨e1, e2⟩; rw [e1, e2])
    exact x86_setGpr_lowEq memPol _ _ _ hi l
      (BitVec.ofNat 64 (((s₁.gpr .rdx).toNat * (s₁.gpr src).toNat) / (2 ^ 64)))
      (BitVec.ofNat 64 (((s₂.gpr .rdx).toNat * (s₂.gpr src).toNat) / (2 ^ 64)))
      hSet1 (fun hl => by rcases hOps hl with ⟨e1, e2⟩; rw [e1, e2])
  | load64 dst base disp =>
    simp only [checkX86Instr] at hCheck
    split at hCheck <;> simp_all
    rename_i hbase; subst hCheck
    refine ⟨by simp [execX86Instr, LeakageEvent.clean, hgpr base hbase], ?_⟩
    exact x86_setGpr_lowEq memPol τ s₁ s₂ dst .sec _ _ hLowOrig (by intro h; cases h)
  | store64 base disp src =>
    simp only [checkX86Instr] at hCheck
    split at hCheck <;> simp_all
    rename_i hcond; rcases hcond with ⟨hbase, hsrcOr⟩; subst hCheck
    have hAddr : s₁.gpr base + disp = s₂.gpr base + disp := by rw [hgpr base hbase]
    refine ⟨by simp [execX86Instr, LeakageEvent.clean, hAddr], ?_⟩
    simp only [execX86Instr]; rw [hAddr]
    exact x86_writeMem64_lowEq memPol secHeap τ s₁ s₂ (s₂.gpr base + disp)
      (s₁.gpr src) (s₂.gpr src) hPol hLowOrig
      (fun hsh => by simp [hsh] at hsrcOr; exact hgpr src hsrcOr)
  | vmovdquLoad dst base disp =>
    simp only [checkX86Instr] at hCheck
    split at hCheck <;> simp_all
    rename_i hbase; subst hCheck
    have hAddr : s₁.gpr base + disp = s₂.gpr base + disp := by rw [hgpr base hbase]
    refine ⟨by simp [execX86Instr, LeakageEvent.clean, hAddr], ?_⟩
    exact x86_setYmm_lowEq memPol τ s₁ s₂ dst .sec _ _ hLowOrig (by intro h; cases h)
  | vmovdquStore base disp src =>
    simp only [checkX86Instr] at hCheck
    split at hCheck <;> simp_all
    rename_i hcond; rcases hcond with ⟨hbase, hsrcOr⟩; subst hCheck
    have hAddr : s₁.gpr base + disp = s₂.gpr base + disp := by rw [hgpr base hbase]
    refine ⟨by simp [execX86Instr, LeakageEvent.clean, hAddr], ?_⟩
    simp only [execX86Instr, X86State.writeMem256]; rw [hAddr]
    have hvEq : secHeap = false → s₁.ymm src = s₂.ymm src := by
      intro hsh; simp [hsh] at hsrcOr; exact hymm src hsrcOr
    have hw0 := x86_writeMem64_lowEq memPol secHeap τ s₁ s₂ (s₂.gpr base + disp)
      (s₁.ymm src).w0 (s₂.ymm src).w0 hPol hLowOrig (fun h => by rw [hvEq h])
    have hw1 := x86_writeMem64_lowEq memPol secHeap τ _ _ (s₂.gpr base + disp + 8#64)
      (s₁.ymm src).w1 (s₂.ymm src).w1 hPol hw0 (fun h => by rw [hvEq h])
    have hw2 := x86_writeMem64_lowEq memPol secHeap τ _ _ (s₂.gpr base + disp + 16#64)
      (s₁.ymm src).w2 (s₂.ymm src).w2 hPol hw1 (fun h => by rw [hvEq h])
    exact x86_writeMem64_lowEq memPol secHeap τ _ _ (s₂.gpr base + disp + 24#64)
      (s₁.ymm src).w3 (s₂.ymm src).w3 hPol hw2 (fun h => by rw [hvEq h])
  | vpxor dst a b =>
    simp only [checkX86Instr, execX86Instr] at hCheck ⊢
    by_cases hab : (a == b) = true
    · simp [hab] at hCheck ⊢; subst hCheck
      exact x86_setYmm_lowEq memPol τ s₁ s₂ dst .pub Vec256.zero Vec256.zero hLowOrig (fun _ => rfl)
    · simp [hab] at hCheck ⊢; subst hCheck
      refine x86_setYmm_lowEq memPol τ s₁ s₂ dst ((τ.ymm a).join (τ.ymm b)) _ _ hLowOrig ?_
      intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h1, h2⟩
      rw [hymm a h1, hymm b h2]
  | vpxorMem dst a base disp =>
    simp only [checkX86Instr] at hCheck
    split at hCheck <;> simp_all
    rename_i hbase; subst hCheck
    have hAddr : s₁.gpr base + disp = s₂.gpr base + disp := by rw [hgpr base hbase]
    refine ⟨by simp [execX86Instr, LeakageEvent.clean, hAddr], ?_⟩
    refine x86_setYmm_lowEq memPol τ s₁ s₂ dst ((τ.ymm a).join .sec) _ _ hLowOrig ?_
    intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨_, hsec⟩; cases hsec
  | vpand dst a b =>
    simp [checkX86Instr] at hCheck; subst hCheck
    refine ⟨rfl, x86_setYmm_lowEq memPol τ s₁ s₂ dst ((τ.ymm a).join (τ.ymm b)) _ _ hLowOrig ?_⟩
    intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h1, h2⟩
    rw [hymm a h1, hymm b h2]
  | vpandn dst a b =>
    simp [checkX86Instr] at hCheck; subst hCheck
    refine ⟨rfl, x86_setYmm_lowEq memPol τ s₁ s₂ dst ((τ.ymm a).join (τ.ymm b)) _ _ hLowOrig ?_⟩
    intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h1, h2⟩
    rw [hymm a h1, hymm b h2]
  | vpor dst a b =>
    simp [checkX86Instr] at hCheck; subst hCheck
    refine ⟨rfl, x86_setYmm_lowEq memPol τ s₁ s₂ dst ((τ.ymm a).join (τ.ymm b)) _ _ hLowOrig ?_⟩
    intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h1, h2⟩
    rw [hymm a h1, hymm b h2]
  | vpslldq8 dst src =>
    simp [checkX86Instr] at hCheck; subst hCheck
    exact ⟨rfl, x86_setYmm_lowEq memPol τ s₁ s₂ dst (τ.ymm src) _ _ hLowOrig
      (fun hl => by rw [hymm src hl])⟩
  | vpsrldq8 dst src =>
    simp [checkX86Instr] at hCheck; subst hCheck
    exact ⟨rfl, x86_setYmm_lowEq memPol τ s₁ s₂ dst (τ.ymm src) _ _ hLowOrig
      (fun hl => by rw [hymm src hl])⟩
  | vpbroadcastqGpr dst src =>
    simp [checkX86Instr] at hCheck; subst hCheck
    exact ⟨rfl, x86_setYmm_lowEq memPol τ s₁ s₂ dst (τ.gpr src) _ _ hLowOrig
      (fun hl => by rw [hgpr src hl])⟩
  | vpbroadcastbGpr dst src =>
    simp [checkX86Instr] at hCheck; subst hCheck
    exact ⟨rfl, x86_setYmm_lowEq memPol τ s₁ s₂ dst (τ.gpr src) _ _ hLowOrig
      (fun hl => by rw [hgpr src hl])⟩
  | vgf2p8affineqb0 dst src mat =>
    simp [checkX86Instr] at hCheck; subst hCheck
    refine ⟨rfl, x86_setYmm_lowEq memPol τ s₁ s₂ dst ((τ.ymm src).join (τ.ymm mat)) _ _ hLowOrig ?_⟩
    intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h1, h2⟩
    rw [hymm src h1, hymm mat h2]
  | vgf2p8mulb dst a b =>
    simp [checkX86Instr] at hCheck; subst hCheck
    refine ⟨rfl, x86_setYmm_lowEq memPol τ s₁ s₂ dst ((τ.ymm a).join (τ.ymm b)) _ _ hLowOrig ?_⟩
    intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h1, h2⟩
    rw [hymm a h1, hymm b h2]
  | vpclmulqdq dst a b imm8 =>
    simp [checkX86Instr] at hCheck; subst hCheck
    refine ⟨rfl, x86_setYmm_lowEq memPol τ s₁ s₂ dst ((τ.ymm a).join (τ.ymm b)) _ _ hLowOrig ?_⟩
    intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h1, h2⟩
    rw [hymm a h1, hymm b h2]
  | vzeroupper =>
    simp [checkX86Instr] at hCheck; subst hCheck
    exact ⟨rfl, hgpr, (fun r hr => by change { (s₁.ymm r) with w2 := 0#64, w3 := 0#64 } = { (s₂.ymm r) with w2 := 0#64, w3 := 0#64 }; rw [hymm r hr]), hcf, hof, hzf, hmem, hdoitEq, hdoitReq, rfl, fun _ => rfl⟩
  | cmovnz64 dst src =>
    simp only [checkX86Instr] at hCheck
    by_cases hpub : (((τ.zf.join (τ.gpr dst)).join (τ.gpr src)) == .pub) = true
    · simp [hpub] at hCheck; subst hCheck
      have hpubEq : (τ.zf.join (τ.gpr dst)).join (τ.gpr src) = .pub := by simpa using hpub
      rcases (SecLabel.join_eq_pub_iff _ _).mp hpubEq with ⟨hzDst, hsrcP⟩
      rcases (SecLabel.join_eq_pub_iff _ _).mp hzDst with ⟨hzP, hdstP⟩
      refine ⟨?_, x86_setGpr_lowEq memPol τ s₁ s₂ dst .pub
        (if !s₁.flags.zf then s₁.gpr src else s₁.gpr dst)
        (if !s₂.flags.zf then s₂.gpr src else s₂.gpr dst) hLowOrig ?_⟩
      · simp [execX86Instr, hdoitEq, hzf hzP, hgpr dst hdstP, hgpr src hsrcP]
      · intro _; simp [hzf hzP, hgpr dst hdstP, hgpr src hsrcP]
    · simp [hpub] at hCheck
      rcases hCheck with ⟨hreqDoit, rfl⟩
      have hd1 : s₁.doitEnabled = true := hdoitReq hreqDoit
      have hd2 : s₂.doitEnabled = true := hdoitEq.symm.trans hd1
      refine ⟨by simp [execX86Instr, hd1, hd2], ?_⟩
      exact x86_setGpr_lowEq memPol τ s₁ s₂ dst .sec _ _ hLowOrig (by intro h; cases h)
  | div64 divisor =>
    simp only [checkX86Instr] at hCheck
    split at hCheck <;> simp_all
    rename_i hdivPub; rcases hdivPub with ⟨⟨hrax, hrdx⟩, hdiv⟩; subst hCheck
    have eRax := hgpr .rax hrax
    have eRdx := hgpr .rdx hrdx
    have eDiv := hgpr divisor hdiv
    refine ⟨by simp [execX86Instr, eRax, eRdx, eDiv], ?_⟩
    simp only [execX86Instr]
    have hSet1 := x86_setGpr_lowEq memPol τ s₁ s₂ .rax .pub
      (if s₁.gpr divisor == 0#64 then 0#64 else BitVec.ofNat 64 ((s₁.gpr .rax).toNat / (s₁.gpr divisor).toNat))
      (if s₂.gpr divisor == 0#64 then 0#64 else BitVec.ofNat 64 ((s₂.gpr .rax).toNat / (s₂.gpr divisor).toNat))
      hLowOrig (fun _ => by rw [eRax, eDiv])
    exact x86_setGpr_lowEq memPol _ _ _ .rdx .pub
      (if s₁.gpr divisor == 0#64 then 0#64 else BitVec.ofNat 64 ((s₁.gpr .rax).toNat % (s₁.gpr divisor).toNat))
      (if s₂.gpr divisor == 0#64 then 0#64 else BitVec.ofNat 64 ((s₂.gpr .rax).toNat % (s₂.gpr divisor).toNat))
      hSet1 (fun _ => by rw [eRax, eDiv])
  | loadIndexed64 dst base idx scale =>
    simp only [checkX86Instr] at hCheck
    split at hCheck <;> simp_all
    rename_i hbi; rcases hbi with ⟨hb, hi⟩; subst hCheck
    refine ⟨by simp [execX86Instr, LeakageEvent.clean, hgpr base hb, hgpr idx hi], ?_⟩
    exact x86_setGpr_lowEq memPol τ s₁ s₂ dst .sec _ _ hLowOrig (by intro h; cases h)
  | vpgatherqq dst base vidx =>
    simp only [checkX86Instr] at hCheck
    split at hCheck <;> simp_all
    rename_i hbvi; rcases hbvi with ⟨hb, hvi⟩; subst hCheck
    refine ⟨by simp [execX86Instr, LeakageEvent.clean, hgpr base hb, hymm vidx hvi], ?_⟩
    exact x86_setYmm_lowEq memPol τ s₁ s₂ dst .sec _ _ hLowOrig (by intro h; cases h)

theorem checkX86Block_sound
    (memPol : BitVec 64 → SecLabel) (secHeap : Bool)
    (hPol : secHeap = true → ∀ a, memPol a = .sec)
    (blk : List X86Instr) (τ τ' : X86TaintState) (pc : Nat)
    (hCheck : checkX86Block secHeap τ blk = some τ')
    (s₁ s₂ : X86State) (hLow : X86LowEq memPol τ s₁ s₂) :
    (execX86Block blk pc s₁).2 = (execX86Block blk pc s₂).2 ∧
    X86LowEq memPol τ' (execX86Block blk pc s₁).1 (execX86Block blk pc s₂).1 := by
  induction blk generalizing τ pc s₁ s₂ with
  | nil =>
    simp [checkX86Block] at hCheck; subst hCheck; exact ⟨rfl, hLow⟩
  | cons ins rest ih =>
    simp only [checkX86Block] at hCheck
    cases hIns : checkX86Instr secHeap τ ins with
    | none => simp [hIns] at hCheck
    | some τ1 =>
      simp [hIns] at hCheck
      obtain ⟨hEv, hLow1⟩ := checkX86Instr_sound memPol secHeap hPol τ τ1 ins pc hIns s₁ s₂ hLow
      obtain ⟨hEvs, hLow2⟩ :=
        ih τ1 (pc + 1) hCheck (execX86Instr ins pc s₁).1 (execX86Instr ins pc s₂).1 hLow1
      simp only [execX86Block]
      exact ⟨by rw [hEv, hEvs], hLow2⟩

theorem checkX86Loop_sound
    (memPol : BitVec 64 → SecLabel) (secHeap : Bool)
    (hPol : secHeap = true → ∀ a, memPol a = .sec)
    (trips : Nat) (body : List X86Instr) (τ τ' : X86TaintState) (pc : Nat)
    (hCheck : checkX86Loop secHeap trips τ body = some τ')
    (s₁ s₂ : X86State) (hLow : X86LowEq memPol τ s₁ s₂) :
    (execX86Loop trips body pc s₁).2 = (execX86Loop trips body pc s₂).2 ∧
    X86LowEq memPol τ' (execX86Loop trips body pc s₁).1 (execX86Loop trips body pc s₂).1 := by
  induction trips generalizing τ pc s₁ s₂ with
  | zero =>
    simp [checkX86Loop] at hCheck; subst hCheck; exact ⟨rfl, hLow⟩
  | succ n ih =>
    simp only [checkX86Loop] at hCheck
    cases hBlk : checkX86Block secHeap τ body with
    | none => simp [hBlk] at hCheck
    | some τ1 =>
      simp [hBlk] at hCheck
      obtain ⟨hEv1, hLow1⟩ := checkX86Block_sound memPol secHeap hPol body τ τ1 pc hBlk s₁ s₂ hLow
      obtain ⟨hEv2, hLow2⟩ :=
        ih τ1 (pc + body.length) hCheck
          (execX86Block body pc s₁).1 (execX86Block body pc s₂).1 hLow1
      simp only [execX86Loop]
      exact ⟨by rw [hEv1, hEv2], hLow2⟩

theorem x86LowEq_join_left (memPol : BitVec 64 → SecLabel)
    (τ τT τE : X86TaintState) (s₁ s₂ : X86State)
    (hDoit : τT.doitAssumed = τ.doitAssumed)
    (hLow : X86LowEq memPol τT s₁ s₂) :
    X86LowEq memPol
      { gpr := fun r => (τT.gpr r).join (τE.gpr r)
        ymm := fun y => (τT.ymm y).join (τE.ymm y)
        cf := τT.cf.join τE.cf
        of := τT.of.join τE.of
        zf := τT.zf.join τE.zf
        doitAssumed := τ.doitAssumed
        upperYmmClean := τT.upperYmmClean && τE.upperYmmClean } s₁ s₂ := by
  rcases hLow with ⟨hg, hy, hc, ho, hz, hm, hdEq, hdReq, hyEq, hyCl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, hm, hdEq, ?_, hyEq, ?_⟩
  · intro r hr; exact hg r ((SecLabel.join_eq_pub_iff _ _).mp hr).1
  · intro y hyP; exact hy y ((SecLabel.join_eq_pub_iff _ _).mp hyP).1
  · intro hP; exact hc ((SecLabel.join_eq_pub_iff _ _).mp hP).1
  · intro hP; exact ho ((SecLabel.join_eq_pub_iff _ _).mp hP).1
  · intro hP; exact hz ((SecLabel.join_eq_pub_iff _ _).mp hP).1
  · intro hD; exact hdReq (hDoit.trans hD)
  · intro hC; simp at hC; exact hyCl hC.1

theorem x86LowEq_join_right (memPol : BitVec 64 → SecLabel)
    (τ τT τE : X86TaintState) (s₁ s₂ : X86State)
    (hDoit : τE.doitAssumed = τ.doitAssumed)
    (hLow : X86LowEq memPol τE s₁ s₂) :
    X86LowEq memPol
      { gpr := fun r => (τT.gpr r).join (τE.gpr r)
        ymm := fun y => (τT.ymm y).join (τE.ymm y)
        cf := τT.cf.join τE.cf
        of := τT.of.join τE.of
        zf := τT.zf.join τE.zf
        doitAssumed := τ.doitAssumed
        upperYmmClean := τT.upperYmmClean && τE.upperYmmClean } s₁ s₂ := by
  rcases hLow with ⟨hg, hy, hc, ho, hz, hm, hdEq, hdReq, hyEq, hyCl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, hm, hdEq, ?_, hyEq, ?_⟩
  · intro r hr; exact hg r ((SecLabel.join_eq_pub_iff _ _).mp hr).2
  · intro y hyP; exact hy y ((SecLabel.join_eq_pub_iff _ _).mp hyP).2
  · intro hP; exact hc ((SecLabel.join_eq_pub_iff _ _).mp hP).2
  · intro hP; exact ho ((SecLabel.join_eq_pub_iff _ _).mp hP).2
  · intro hP; exact hz ((SecLabel.join_eq_pub_iff _ _).mp hP).2
  · intro hD; exact hdReq (hDoit.trans hD)
  · intro hC; simp at hC; exact hyCl hC.2

/-- **Master `x86_64` Constant-Time Timing-Noninterference Soundness Theorem**:
    Any `x86_64` assembly program accepted by `checkX86Prog` produces **identical**
    microarchitectural leakage traces (`branchTaken`, `memAddrs`, `varLatencyOperands`,
    and `dirtyUpperYmmOnRet = false`) on all secret-varying states `s₁, s₂` satisfying `X86LowEq`. -/
theorem x86_ct_checker_sound
    (memPol : BitVec 64 → SecLabel) (secHeap : Bool)
    (hPol : secHeap = true → ∀ a, memPol a = .sec)
    (prog : List X86Stmt) (τ τ' : X86TaintState) (pc : Nat)
    (hCheck : checkX86Prog secHeap τ prog = some τ')
    (s₁ s₂ : X86State) (hLow : X86LowEq memPol τ s₁ s₂) :
    (execX86Prog prog pc s₁).2 = (execX86Prog prog pc s₂).2 ∧
    X86LowEq memPol τ' (execX86Prog prog pc s₁).1 (execX86Prog prog pc s₂).1 := by
  induction prog generalizing τ pc s₁ s₂ with
  | nil =>
    simp [checkX86Prog] at hCheck; subst hCheck; exact ⟨rfl, hLow⟩
  | cons stmt rest ih =>
    cases stmt with
    | instr ins =>
      simp only [checkX86Prog] at hCheck
      cases hIns : checkX86Instr secHeap τ ins with
      | none => simp [hIns] at hCheck
      | some τ1 =>
        simp [hIns] at hCheck
        obtain ⟨hEv, hLow1⟩ := checkX86Instr_sound memPol secHeap hPol τ τ1 ins pc hIns s₁ s₂ hLow
        obtain ⟨hEvs, hLow2⟩ :=
          ih τ1 (pc + 1) hCheck (execX86Instr ins pc s₁).1 (execX86Instr ins pc s₂).1 hLow1
        simp only [execX86Prog]
        exact ⟨by rw [hEv, hEvs], hLow2⟩
    | jccNz condReg thenBody elseBody =>
      simp only [checkX86Prog] at hCheck
      by_cases hCond : (τ.gpr condReg == .pub) = true
      · simp [hCond] at hCheck
        cases hT : checkX86Block secHeap τ thenBody with
        | none => simp [hT] at hCheck
        | some τT =>
          cases hE : checkX86Block secHeap τ elseBody with
          | none => simp [hT, hE] at hCheck
          | some τE =>
            simp [hT, hE] at hCheck
            have hCondPub : τ.gpr condReg = .pub := by simpa using hCond
            have hCondEq : s₁.gpr condReg = s₂.gpr condReg := hLow.1 condReg hCondPub
            simp only [execX86Prog, hCondEq]
            by_cases hTaken : (s₂.gpr condReg != 0#64) = true
            · simp only [hTaken, ↓reduceIte]
              obtain ⟨hEv1, hLowT⟩ :=
                checkX86Block_sound memPol secHeap hPol thenBody τ τT (pc + 1) hT s₁ s₂ hLow
              have hJoinLow := x86LowEq_join_left memPol τ τT τE _ _
                (checkX86Block_doitAssumed secHeap thenBody τ τT hT) hLowT
              obtain ⟨hEv2, hLowRest⟩ :=
                ih _ (pc + 1 + thenBody.length) hCheck _ _ hJoinLow
              exact ⟨by rw [hEv1, hEv2], hLowRest⟩
            · simp only [hTaken, Bool.false_eq_true, ↓reduceIte]
              obtain ⟨hEv1, hLowE⟩ :=
                checkX86Block_sound memPol secHeap hPol elseBody τ τE (pc + 1) hE s₁ s₂ hLow
              have hJoinLow := x86LowEq_join_right memPol τ τT τE _ _
                (checkX86Block_doitAssumed secHeap elseBody τ τE hE) hLowE
              obtain ⟨hEv2, hLowRest⟩ :=
                ih _ (pc + 1 + elseBody.length) hCheck _ _ hJoinLow
              exact ⟨by rw [hEv1, hEv2], hLowRest⟩
      · simp [hCond] at hCheck
    | pubLoop trips body =>
      simp only [checkX86Prog] at hCheck
      cases hLp : checkX86Loop secHeap trips τ body with
      | none => simp [hLp] at hCheck
      | some τ1 =>
        simp [hLp] at hCheck
        obtain ⟨hEv1, hLow1⟩ :=
          checkX86Loop_sound memPol secHeap hPol trips body τ τ1 pc hLp s₁ s₂ hLow
        obtain ⟨hEv2, hLow2⟩ :=
          ih τ1 (pc + trips * body.length) hCheck
            (execX86Loop trips body pc s₁).1 (execX86Loop trips body pc s₂).1 hLow1
        simp only [execX86Prog]
        exact ⟨by rw [hEv1, hEv2], hLow2⟩
    | ret =>
      simp only [checkX86Prog] at hCheck
      split at hCheck <;> simp_all
      rename_i hClean; subst hCheck
      have hd1 : s₁.ymmUpperDirty = false := hLow.2.2.2.2.2.2.2.2.2 hClean
      have hd2 : s₂.ymmUpperDirty = false := hLow.2.2.2.2.2.2.2.2.1.symm.trans hd1
      exact ⟨by simp [execX86Prog, hd1, hd2], hLow⟩

/-! ## 5. `aarch64` (`NEON` + `FEAT_SHA3` + `PMULL` + `FEAT_DIT`) Semantics & Soundness -/

inductive ArmGpr where
  | x0  | x1  | x2  | x3  | x4  | x5  | x6  | x7
  | x8  | x9  | x10 | x11 | x12 | x13 | x14 | x15
  | x16 | x17 | x19 | x20 | sp
  deriving DecidableEq, Repr, Inhabited

inductive NeonReg where
  | v0  | v1  | v2  | v3  | v4  | v5  | v6  | v7
  | v16 | v17 | v18 | v19 | v20 | v21
  deriving DecidableEq, Repr, Inhabited

structure ArmFlags where
  z : Bool
  c : Bool
  deriving DecidableEq, Repr, Inhabited

structure ArmState where
  gpr : ArmGpr → BitVec 64
  neon : NeonReg → Vec128
  flags : ArmFlags
  mem : BitVec 64 → BitVec 64
  ditEnabled : Bool

def ArmState.setGpr (st : ArmState) (r : ArmGpr) (v : BitVec 64) : ArmState :=
  { st with gpr := fun q => if q == r then v else st.gpr q }

def ArmState.setNeon (st : ArmState) (r : NeonReg) (v : Vec128) : ArmState :=
  { st with neon := fun q => if q == r then v else st.neon q }

def ArmState.writeMem64 (st : ArmState) (addr val : BitVec 64) : ArmState :=
  { st with mem := fun a => if a == addr then val else st.mem a }

def ArmState.readMem128 (st : ArmState) (addr : BitVec 64) : Vec128 :=
  ⟨st.mem addr, st.mem (addr + 8#64)⟩

def ArmState.writeMem128 (st : ArmState) (addr : BitVec 64) (v : Vec128) : ArmState :=
  (st.writeMem64 addr v.lo).writeMem64 (addr + 8#64) v.hi

inductive ArmInstr where
  | msrDit1
  | movImm64 (dst : ArmGpr) (imm : BitVec 64)
  | movReg64 (dst src : ArmGpr)
  | eor64 (dst a b : ArmGpr)
  | eorImm64 (dst a : ArmGpr) (imm : BitVec 64)
  | orr64 (dst a b : ArmGpr)
  | and64 (dst a b : ArmGpr)
  | andImm64 (dst a : ArmGpr) (imm : BitVec 64)
  | lsrImm64 (dst src : ArmGpr) (sh : Nat)
  | lslImm64 (dst src : ArmGpr) (sh : Nat)
  | add64 (dst a b : ArmGpr)
  | addImm64 (dst src : ArmGpr) (imm : BitVec 64)
  | sub64 (dst a b : ArmGpr)
  | neg64 (dst src : ArmGpr)
  | adds64 (dst a b : ArmGpr)
  | adcZero64 (dst : ArmGpr)
  | subs64 (dst a b : ArmGpr)
  | sbcMask64 (dst : ArmGpr)
  | mulLo64 (dst a b : ArmGpr)
  | umulh64 (dst a b : ArmGpr)
  | ldr64 (dst base : ArmGpr) (disp : BitVec 64)
  | str64 (src base : ArmGpr) (disp : BitVec 64)
  | ldrQ (dst : NeonReg) (base : ArmGpr) (disp : BitVec 64)
  | strQ (src : NeonReg) (base : ArmGpr) (disp : BitVec 64)
  | eorV16b (dst a b : NeonReg)
  | bcaxV16b (dst vn vm va : NeonReg)
  | eor3V16b (dst vn vm va : NeonReg)
  | rax1V2d (dst vn vm : NeonReg)
  | xarV2d (dst vn vm : NeonReg) (imm6 : Fin 64)
  | pmull1q (dst a b : NeonReg)
  | pmull2_1q (dst a b : NeonReg)
  | extV16b8 (dst a b : NeonReg)
  | cselEq64 (dst a b : ArmGpr)
  | udiv64 (dst a b : ArmGpr)
  | ldrIndexed64 (dst base idx : ArmGpr)
  deriving DecidableEq, Repr

inductive ArmStmt where
  | instr (i : ArmInstr)
  | cbnz (condReg : ArmGpr) (thenBody elseBody : List ArmInstr)
  | pubLoop (trips : Nat) (body : List ArmInstr)
  | ret
  deriving DecidableEq, Repr

def execArmInstr (ins : ArmInstr) (pc : Nat) (st : ArmState) : ArmState × LeakageEvent :=
  match ins with
  | .msrDit1 =>
    ({ st with ditEnabled := true }, LeakageEvent.clean pc)
  | .movImm64 dst imm =>
    (st.setGpr dst imm, LeakageEvent.clean pc)
  | .movReg64 dst src =>
    (st.setGpr dst (st.gpr src), LeakageEvent.clean pc)
  | .eor64 dst a b =>
    (st.setGpr dst (st.gpr a ^^^ st.gpr b), LeakageEvent.clean pc)
  | .eorImm64 dst a imm =>
    (st.setGpr dst (st.gpr a ^^^ imm), LeakageEvent.clean pc)
  | .orr64 dst a b =>
    (st.setGpr dst (st.gpr a ||| st.gpr b), LeakageEvent.clean pc)
  | .and64 dst a b =>
    (st.setGpr dst (st.gpr a &&& st.gpr b), LeakageEvent.clean pc)
  | .andImm64 dst a imm =>
    (st.setGpr dst (st.gpr a &&& imm), LeakageEvent.clean pc)
  | .lsrImm64 dst src sh =>
    (st.setGpr dst (st.gpr src >>> sh), LeakageEvent.clean pc)
  | .lslImm64 dst src sh =>
    (st.setGpr dst (st.gpr src <<< sh), LeakageEvent.clean pc)
  | .add64 dst a b =>
    (st.setGpr dst (st.gpr a + st.gpr b), LeakageEvent.clean pc)
  | .addImm64 dst src imm =>
    (st.setGpr dst (st.gpr src + imm), LeakageEvent.clean pc)
  | .sub64 dst a b =>
    (st.setGpr dst (st.gpr a - st.gpr b), LeakageEvent.clean pc)
  | .neg64 dst src =>
    (st.setGpr dst (0#64 - st.gpr src), LeakageEvent.clean pc)
  | .adds64 dst a b =>
    let va := st.gpr a
    let vb := st.gpr b
    let sumNat := va.toNat + vb.toNat
    let res := va + vb
    ({ (st.setGpr dst res) with
       flags := { z := (res == 0#64), c := decide (sumNat ≥ 2 ^ 64) } },
     LeakageEvent.clean pc)
  | .adcZero64 dst =>
    let res := if st.flags.c then 1#64 else 0#64
    (st.setGpr dst res, LeakageEvent.clean pc)
  | .subs64 dst a b =>
    let va := st.gpr a
    let vb := st.gpr b
    let res := va - vb
    -- ARM64 `SUBS` sets `PSTATE.C = 1` iff NO unsigned borrow (`va.toNat ≥ vb.toNat`)!
    ({ (st.setGpr dst res) with
       flags := { z := (res == 0#64), c := decide (va.toNat ≥ vb.toNat) } },
     LeakageEvent.clean pc)
  | .sbcMask64 dst =>
    -- ARM64 `SBC dst, xzr, xzr` computes `0 - 0 - (1 - C)`: `0` if `C = 1`, `-1` if `C = 0`!
    let mask := if st.flags.c then 0#64 else 0xFFFFFFFFFFFFFFFF#64
    (st.setGpr dst mask, LeakageEvent.clean pc)
  | .mulLo64 dst a b =>
    let prod := (st.gpr a).toNat * (st.gpr b).toNat
    (st.setGpr dst (BitVec.ofNat 64 prod),
      { LeakageEvent.clean pc with
        varLatencyOperands := if st.ditEnabled then [] else [st.gpr a, st.gpr b] })
  | .umulh64 dst a b =>
    let prod := (st.gpr a).toNat * (st.gpr b).toNat
    (st.setGpr dst (BitVec.ofNat 64 (prod / (2 ^ 64))),
      { LeakageEvent.clean pc with
        varLatencyOperands := if st.ditEnabled then [] else [st.gpr a, st.gpr b] })
  | .ldr64 dst base disp =>
    let addr := st.gpr base + disp
    (st.setGpr dst (st.mem addr), LeakageEvent.clean pc [addr])
  | .str64 src base disp =>
    let addr := st.gpr base + disp
    (st.writeMem64 addr (st.gpr src), LeakageEvent.clean pc [addr])
  | .ldrQ dst base disp =>
    let addr := st.gpr base + disp
    (st.setNeon dst (st.readMem128 addr), LeakageEvent.clean pc [addr, addr + 8#64])
  | .strQ src base disp =>
    let addr := st.gpr base + disp
    (st.writeMem128 addr (st.neon src), LeakageEvent.clean pc [addr, addr + 8#64])
  | .eorV16b dst a b =>
    if a == b then
      (st.setNeon dst Vec128.zero, LeakageEvent.clean pc)
    else
      (st.setNeon dst (Vec128.xor (st.neon a) (st.neon b)), LeakageEvent.clean pc)
  | .bcaxV16b dst vn vm va =>
    (st.setNeon dst (Vec128.bcax (st.neon vn) (st.neon vm) (st.neon va)), LeakageEvent.clean pc)
  | .eor3V16b dst vn vm va =>
    (st.setNeon dst (Vec128.eor3 (st.neon vn) (st.neon vm) (st.neon va)), LeakageEvent.clean pc)
  | .rax1V2d dst vn vm =>
    (st.setNeon dst (Vec128.rax1 (st.neon vn) (st.neon vm)), LeakageEvent.clean pc)
  | .xarV2d dst vn vm imm6 =>
    (st.setNeon dst (Vec128.xar (st.neon vn) (st.neon vm) imm6), LeakageEvent.clean pc)
  | .pmull1q dst a b =>
    (st.setNeon dst (clmul64 (st.neon a).lo (st.neon b).lo),
      { LeakageEvent.clean pc with
        varLatencyOperands := if st.ditEnabled then [] else [(st.neon a).lo, (st.neon b).lo] })
  | .pmull2_1q dst a b =>
    (st.setNeon dst (clmul64 (st.neon a).hi (st.neon b).hi),
      { LeakageEvent.clean pc with
        varLatencyOperands := if st.ditEnabled then [] else [(st.neon a).hi, (st.neon b).hi] })
  | .extV16b8 dst a b =>
    (st.setNeon dst (Vec128.ext8 (st.neon a) (st.neon b)), LeakageEvent.clean pc)
  | .cselEq64 dst a b =>
    let res := if st.flags.z then st.gpr a else st.gpr b
    let varOps :=
      if st.ditEnabled then []
      else [if st.flags.z then 1#64 else 0#64, st.gpr a, st.gpr b]
    (st.setGpr dst res,
     { pc := pc
       branchTaken := none
       memAddrs := []
       varLatencyOperands := varOps
       dirtyUpperYmmOnRet := false })
  | .udiv64 dst a b =>
    -- Per ARM DDI 0487, `UDIV`/`SDIV` latency is NOT data-independent even when `PSTATE.DIT = 1`!
    let va := st.gpr a
    let vb := st.gpr b
    let q := if vb == 0#64 then 0#64 else BitVec.ofNat 64 (va.toNat / vb.toNat)
    (st.setGpr dst q,
     { pc := pc
       branchTaken := none
       memAddrs := []
       varLatencyOperands := [va, vb]
       dirtyUpperYmmOnRet := false })
  | .ldrIndexed64 dst base idx =>
    let addr := st.gpr base + st.gpr idx
    (st.setGpr dst (st.mem addr), LeakageEvent.clean pc [addr])

def execArmBlock (blk : List ArmInstr) (pc : Nat) (st : ArmState) :
    ArmState × List LeakageEvent :=
  match blk with
  | [] => (st, [])
  | ins :: rest =>
    let (st1, ev) := execArmInstr ins pc st
    let (st2, evs) := execArmBlock rest (pc + 1) st1
    (st2, ev :: evs)

/-- Compose certified blocks at the advanced PC, preserving the full leakage trace. -/
theorem execArmBlock_append (a b : List ArmInstr) (pc : Nat) (st : ArmState) :
    execArmBlock (a ++ b) pc st =
      let first := execArmBlock a pc st
      let second := execArmBlock b (pc + a.length) first.1
      (second.1, first.2 ++ second.2) := by
  induction a generalizing pc st with
  | nil => simp only [List.nil_append, execArmBlock, List.length_nil, Nat.add_zero]
  | cons ins rest ih =>
    simp only [List.cons_append, execArmBlock, ih, List.length_cons,
      List.cons_append, Nat.add_assoc, Nat.add_comm 1]

/-- Regression: concatenation must not reset the suffix program counter. -/
theorem execArmBlock_suffix_pc_not_reset (st : ArmState) :
    (execArmBlock [.movImm64 .x0 0#64, .movImm64 .x0 1#64] 0 st).2 ≠
      [LeakageEvent.clean 0 [], LeakageEvent.clean 0 []] := by
  intro h
  have hp := congrArg (List.map LeakageEvent.pc) h
  change [0, 1] = [0, 0] at hp
  contradiction

def execArmLoop (trips : Nat) (body : List ArmInstr) (pc : Nat) (st : ArmState) :
    ArmState × List LeakageEvent :=
  match trips with
  | 0 => (st, [])
  | n + 1 =>
    let (st1, evs1) := execArmBlock body pc st
    let (st2, evs2) := execArmLoop n body (pc + body.length) st1
    (st2, evs1 ++ evs2)

def execArmProg (prog : List ArmStmt) (pc : Nat) (st : ArmState) :
    ArmState × List LeakageEvent :=
  match prog with
  | [] => (st, [])
  | stmt :: rest =>
    match stmt with
    | .instr ins =>
      let (st1, ev) := execArmInstr ins pc st
      let (st2, evs) := execArmProg rest (pc + 1) st1
      (st2, ev :: evs)
    | .cbnz condReg thenBody elseBody =>
      let taken := st.gpr condReg != 0#64
      let brEv : LeakageEvent :=
        { pc := pc
          branchTaken := some taken
          memAddrs := []
          varLatencyOperands := []
          dirtyUpperYmmOnRet := false }
      let chosen := if taken then thenBody else elseBody
      let (st1, evs1) := execArmBlock chosen (pc + 1) st
      let (st2, evs2) := execArmProg rest (pc + 1 + chosen.length) st1
      (st2, brEv :: (evs1 ++ evs2))
    | .pubLoop trips body =>
      let (st1, evs1) := execArmLoop trips body pc st
      let (st2, evs2) := execArmProg rest (pc + trips * body.length) st1
      (st2, evs1 ++ evs2)
    | .ret =>
      (st, [LeakageEvent.clean pc])

structure ArmTaintState where
  gpr : ArmGpr → SecLabel
  neon : NeonReg → SecLabel
  z : SecLabel
  c : SecLabel
  ditAssumed : Bool

def ArmTaintState.setGpr (τ : ArmTaintState) (r : ArmGpr) (l : SecLabel) : ArmTaintState :=
  { τ with gpr := fun q => if q == r then l else τ.gpr q }

def ArmTaintState.setNeon (τ : ArmTaintState) (r : NeonReg) (l : SecLabel) : ArmTaintState :=
  { τ with neon := fun q => if q == r then l else τ.neon q }

@[expose]
def ArmLowEq (memPol : BitVec 64 → SecLabel) (τ : ArmTaintState) (s₁ s₂ : ArmState) : Prop :=
  (∀ r, τ.gpr r = .pub → s₁.gpr r = s₂.gpr r) ∧
  (∀ v, τ.neon v = .pub → s₁.neon v = s₂.neon v) ∧
  (τ.z = .pub → s₁.flags.z = s₂.flags.z) ∧
  (τ.c = .pub → s₁.flags.c = s₂.flags.c) ∧
  (∀ addr, memPol addr = .pub → s₁.mem addr = s₂.mem addr) ∧
  (s₁.ditEnabled = s₂.ditEnabled) ∧
  (τ.ditAssumed = true → s₁.ditEnabled = true)

def checkArmInstr (secHeap : Bool) (τ : ArmTaintState) (ins : ArmInstr) :
    Option ArmTaintState :=
  match ins with
  | .msrDit1 => some { τ with ditAssumed := true }
  | .movImm64 dst _ => some (τ.setGpr dst .pub)
  | .movReg64 dst src => some (τ.setGpr dst (τ.gpr src))
  | .eor64 dst a b =>
    if a == b then some (τ.setGpr dst .pub)
    else some (τ.setGpr dst ((τ.gpr a).join (τ.gpr b)))
  | .eorImm64 dst a _ => some (τ.setGpr dst (τ.gpr a))
  | .orr64 dst a b => some (τ.setGpr dst ((τ.gpr a).join (τ.gpr b)))
  | .and64 dst a b => some (τ.setGpr dst ((τ.gpr a).join (τ.gpr b)))
  | .andImm64 dst a _ => some (τ.setGpr dst (τ.gpr a))
  | .lsrImm64 dst src _ => some (τ.setGpr dst (τ.gpr src))
  | .lslImm64 dst src _ => some (τ.setGpr dst (τ.gpr src))
  | .add64 dst a b => some (τ.setGpr dst ((τ.gpr a).join (τ.gpr b)))
  | .addImm64 dst src _ => some (τ.setGpr dst (τ.gpr src))
  | .sub64 dst a b => some (τ.setGpr dst ((τ.gpr a).join (τ.gpr b)))
  | .neg64 dst src => some (τ.setGpr dst (τ.gpr src))
  | .adds64 dst a b =>
    let l := (τ.gpr a).join (τ.gpr b)
    some { (τ.setGpr dst l) with z := l, c := l }
  | .adcZero64 dst => some (τ.setGpr dst τ.c)
  | .subs64 dst a b =>
    let l := (τ.gpr a).join (τ.gpr b)
    some { (τ.setGpr dst l) with z := l, c := l }
  | .sbcMask64 dst => some (τ.setGpr dst τ.c)
  | .mulLo64 dst a b =>
    let l := (τ.gpr a).join (τ.gpr b)
    if l == .pub || τ.ditAssumed then some (τ.setGpr dst l) else none
  | .umulh64 dst a b =>
    let l := (τ.gpr a).join (τ.gpr b)
    if l == .pub || τ.ditAssumed then some (τ.setGpr dst l) else none
  | .ldr64 dst base _ =>
    if τ.gpr base == .pub then some (τ.setGpr dst .sec) else none
  | .str64 src base _ =>
    if τ.gpr base == .pub && (secHeap || τ.gpr src == .pub) then some τ else none
  | .ldrQ dst base _ =>
    if τ.gpr base == .pub then some (τ.setNeon dst .sec) else none
  | .strQ src base _ =>
    if τ.gpr base == .pub && (secHeap || τ.neon src == .pub) then some τ else none
  | .eorV16b dst a b =>
    if a == b then some (τ.setNeon dst .pub)
    else some (τ.setNeon dst ((τ.neon a).join (τ.neon b)))
  | .bcaxV16b dst vn vm va =>
    some (τ.setNeon dst (((τ.neon vn).join (τ.neon vm)).join (τ.neon va)))
  | .eor3V16b dst vn vm va =>
    some (τ.setNeon dst (((τ.neon vn).join (τ.neon vm)).join (τ.neon va)))
  | .rax1V2d dst vn vm =>
    some (τ.setNeon dst ((τ.neon vn).join (τ.neon vm)))
  | .xarV2d dst vn vm _ =>
    some (τ.setNeon dst ((τ.neon vn).join (τ.neon vm)))
  | .pmull1q dst a b =>
    let l := (τ.neon a).join (τ.neon b)
    if l == .pub || τ.ditAssumed then some (τ.setNeon dst l) else none
  | .pmull2_1q dst a b =>
    let l := (τ.neon a).join (τ.neon b)
    if l == .pub || τ.ditAssumed then some (τ.setNeon dst l) else none
  | .extV16b8 dst a b =>
    some (τ.setNeon dst ((τ.neon a).join (τ.neon b)))
  | .cselEq64 dst a b =>
    let l := (τ.z.join (τ.gpr a)).join (τ.gpr b)
    if l == .pub then some (τ.setGpr dst .pub)
    else if τ.ditAssumed then some (τ.setGpr dst .sec)
    else none
  | .udiv64 dst a b =>
    if τ.gpr a == .pub && τ.gpr b == .pub then some (τ.setGpr dst .pub) else none
  | .ldrIndexed64 dst base idx =>
    if τ.gpr base == .pub && τ.gpr idx == .pub then some (τ.setGpr dst .sec) else none

def checkArmBlock (secHeap : Bool) (τ : ArmTaintState) (blk : List ArmInstr) :
    Option ArmTaintState :=
  match blk with
  | [] => some τ
  | ins :: rest =>
    match checkArmInstr secHeap τ ins with
    | none => none
    | some τ1 => checkArmBlock secHeap τ1 rest

def checkArmLoop (secHeap : Bool) (trips : Nat) (τ : ArmTaintState) (body : List ArmInstr) :
    Option ArmTaintState :=
  match trips with
  | 0 => some τ
  | n + 1 =>
    match checkArmBlock secHeap τ body with
    | none => none
    | some τ1 => checkArmLoop secHeap n τ1 body

def checkArmProg (secHeap : Bool) (τ : ArmTaintState) (prog : List ArmStmt) :
    Option ArmTaintState :=
  match prog with
  | [] => some τ
  | stmt :: rest =>
    match stmt with
    | .instr ins =>
      match checkArmInstr secHeap τ ins with
      | none => none
      | some τ1 => checkArmProg secHeap τ1 rest
    | .cbnz condReg thenBody elseBody =>
      if τ.gpr condReg == .pub then
        match checkArmBlock secHeap τ thenBody, checkArmBlock secHeap τ elseBody with
        | some τT, some τE =>
          let τJoin : ArmTaintState :=
            { gpr := fun r => (τT.gpr r).join (τE.gpr r)
              neon := fun v => (τT.neon v).join (τE.neon v)
              z := τT.z.join τE.z
              c := τT.c.join τE.c
              ditAssumed := τT.ditAssumed && τE.ditAssumed }
          checkArmProg secHeap τJoin rest
        | _, _ => none
      else
        none
    | .pubLoop trips body =>
      match checkArmLoop secHeap trips τ body with
      | none => none
      | some τ1 => checkArmProg secHeap τ1 rest
    | .ret => some τ

theorem arm_setGpr_lowEq (memPol : BitVec 64 → SecLabel) (τ : ArmTaintState)
    (s₁ s₂ : ArmState) (r : ArmGpr) (l : SecLabel) (v₁ v₂ : BitVec 64)
    (hLow : ArmLowEq memPol τ s₁ s₂) (hv : l = .pub → v₁ = v₂) :
    ArmLowEq memPol (τ.setGpr r l) (s₁.setGpr r v₁) (s₂.setGpr r v₂) := by
  rcases hLow with ⟨hgpr, hneon, hz, hc, hmem, hditEq, hditReq⟩
  refine ⟨?_, hneon, hz, hc, hmem, hditEq, hditReq⟩
  intro q hq
  simp only [ArmTaintState.setGpr, ArmState.setGpr] at hq ⊢
  split at hq
  · rename_i heq; simp [heq, hv hq]
  · rename_i hne; simp [hne, hgpr q hq]

theorem arm_setNeon_lowEq (memPol : BitVec 64 → SecLabel) (τ : ArmTaintState)
    (s₁ s₂ : ArmState) (r : NeonReg) (l : SecLabel) (v₁ v₂ : Vec128)
    (hLow : ArmLowEq memPol τ s₁ s₂) (hv : l = .pub → v₁ = v₂) :
    ArmLowEq memPol (τ.setNeon r l) (s₁.setNeon r v₁) (s₂.setNeon r v₂) := by
  rcases hLow with ⟨hgpr, hneon, hz, hc, hmem, hditEq, hditReq⟩
  refine ⟨hgpr, ?_, hz, hc, hmem, hditEq, hditReq⟩
  intro q hq
  simp only [ArmTaintState.setNeon, ArmState.setNeon] at hq ⊢
  split at hq
  · rename_i heq; simp [heq, hv hq]
  · rename_i hne; simp [hne, hneon q hq]

theorem arm_writeMem64_lowEq (memPol : BitVec 64 → SecLabel) (secHeap : Bool)
    (τ : ArmTaintState) (s₁ s₂ : ArmState) (addr v₁ v₂ : BitVec 64)
    (hPol : secHeap = true → ∀ a, memPol a = .sec)
    (hLow : ArmLowEq memPol τ s₁ s₂) (hv : secHeap = false → v₁ = v₂) :
    ArmLowEq memPol τ (s₁.writeMem64 addr v₁) (s₂.writeMem64 addr v₂) := by
  rcases hLow with ⟨hgpr, hneon, hz, hc, hmem, hditEq, hditReq⟩
  refine ⟨hgpr, hneon, hz, hc, ?_, hditEq, hditReq⟩
  intro a ha
  simp only [ArmState.writeMem64]
  split
  · cases hsh : secHeap
    · exact hv hsh
    · have hsec := hPol hsh a; rw [ha] at hsec; cases hsec
  · exact hmem a ha

theorem checkArmInstr_sound
    (memPol : BitVec 64 → SecLabel) (secHeap : Bool)
    (hPol : secHeap = true → ∀ a, memPol a = .sec)
    (τ τ' : ArmTaintState) (ins : ArmInstr) (pc : Nat)
    (hCheck : checkArmInstr secHeap τ ins = some τ')
    (s₁ s₂ : ArmState) (hLow : ArmLowEq memPol τ s₁ s₂) :
    (execArmInstr ins pc s₁).2 = (execArmInstr ins pc s₂).2 ∧
    ArmLowEq memPol τ' (execArmInstr ins pc s₁).1 (execArmInstr ins pc s₂).1 := by
  rcases hLow with ⟨hgpr, hneon, hz, hc, hmem, hditEq, hditReq⟩
  have hLowOrig : ArmLowEq memPol τ s₁ s₂ := ⟨hgpr, hneon, hz, hc, hmem, hditEq, hditReq⟩
  cases ins with
  | msrDit1 =>
    simp [checkArmInstr] at hCheck; subst hCheck
    exact ⟨rfl, hgpr, hneon, hz, hc, hmem, rfl, fun _ => rfl⟩
  | movImm64 dst imm =>
    simp [checkArmInstr] at hCheck; subst hCheck
    exact ⟨rfl, arm_setGpr_lowEq memPol τ s₁ s₂ dst .pub imm imm hLowOrig (fun _ => rfl)⟩
  | movReg64 dst src =>
    simp [checkArmInstr] at hCheck; subst hCheck
    exact ⟨rfl, arm_setGpr_lowEq memPol τ s₁ s₂ dst (τ.gpr src) (s₁.gpr src) (s₂.gpr src)
      hLowOrig (hgpr src)⟩
  | eor64 dst a b =>
    simp only [checkArmInstr] at hCheck
    by_cases hab : (a == b) = true
    · simp [hab] at hCheck; subst hCheck
      have hEq : a = b := by simpa using hab
      subst hEq
      exact ⟨rfl, arm_setGpr_lowEq memPol τ s₁ s₂ dst .pub
        (s₁.gpr a ^^^ s₁.gpr a) (s₂.gpr a ^^^ s₂.gpr a) hLowOrig (fun _ => by simp)⟩
    · simp [hab] at hCheck; subst hCheck
      refine ⟨rfl, arm_setGpr_lowEq memPol τ s₁ s₂ dst ((τ.gpr a).join (τ.gpr b))
        (s₁.gpr a ^^^ s₁.gpr b) (s₂.gpr a ^^^ s₂.gpr b) hLowOrig ?_⟩
      intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h1, h2⟩
      rw [hgpr a h1, hgpr b h2]
  | eorImm64 dst a imm =>
    simp [checkArmInstr] at hCheck; subst hCheck
    exact ⟨rfl, arm_setGpr_lowEq memPol τ s₁ s₂ dst (τ.gpr a)
      (s₁.gpr a ^^^ imm) (s₂.gpr a ^^^ imm) hLowOrig (fun hl => by rw [hgpr a hl])⟩
  | orr64 dst a b =>
    simp [checkArmInstr] at hCheck; subst hCheck
    refine ⟨rfl, arm_setGpr_lowEq memPol τ s₁ s₂ dst ((τ.gpr a).join (τ.gpr b))
      (s₁.gpr a ||| s₁.gpr b) (s₂.gpr a ||| s₂.gpr b) hLowOrig ?_⟩
    intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h1, h2⟩
    rw [hgpr a h1, hgpr b h2]
  | and64 dst a b =>
    simp [checkArmInstr] at hCheck; subst hCheck
    refine ⟨rfl, arm_setGpr_lowEq memPol τ s₁ s₂ dst ((τ.gpr a).join (τ.gpr b))
      (s₁.gpr a &&& s₁.gpr b) (s₂.gpr a &&& s₂.gpr b) hLowOrig ?_⟩
    intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h1, h2⟩
    rw [hgpr a h1, hgpr b h2]
  | andImm64 dst a imm =>
    simp [checkArmInstr] at hCheck; subst hCheck
    exact ⟨rfl, arm_setGpr_lowEq memPol τ s₁ s₂ dst (τ.gpr a)
      (s₁.gpr a &&& imm) (s₂.gpr a &&& imm) hLowOrig (fun hl => by rw [hgpr a hl])⟩
  | lsrImm64 dst src sh =>
    simp [checkArmInstr] at hCheck; subst hCheck
    exact ⟨rfl, arm_setGpr_lowEq memPol τ s₁ s₂ dst (τ.gpr src)
      (s₁.gpr src >>> sh) (s₂.gpr src >>> sh) hLowOrig (fun hl => by rw [hgpr src hl])⟩
  | lslImm64 dst src sh =>
    simp [checkArmInstr] at hCheck; subst hCheck
    exact ⟨rfl, arm_setGpr_lowEq memPol τ s₁ s₂ dst (τ.gpr src)
      (s₁.gpr src <<< sh) (s₂.gpr src <<< sh) hLowOrig (fun hl => by rw [hgpr src hl])⟩
  | add64 dst a b =>
    simp [checkArmInstr] at hCheck; subst hCheck
    refine ⟨rfl, arm_setGpr_lowEq memPol τ s₁ s₂ dst ((τ.gpr a).join (τ.gpr b))
      (s₁.gpr a + s₁.gpr b) (s₂.gpr a + s₂.gpr b) hLowOrig ?_⟩
    intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h1, h2⟩
    rw [hgpr a h1, hgpr b h2]
  | addImm64 dst src imm =>
    simp [checkArmInstr] at hCheck; subst hCheck
    exact ⟨rfl, arm_setGpr_lowEq memPol τ s₁ s₂ dst (τ.gpr src)
      (s₁.gpr src + imm) (s₂.gpr src + imm) hLowOrig (fun hl => by rw [hgpr src hl])⟩
  | sub64 dst a b =>
    simp [checkArmInstr] at hCheck; subst hCheck
    refine ⟨rfl, arm_setGpr_lowEq memPol τ s₁ s₂ dst ((τ.gpr a).join (τ.gpr b))
      (s₁.gpr a - s₁.gpr b) (s₂.gpr a - s₂.gpr b) hLowOrig ?_⟩
    intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h1, h2⟩
    rw [hgpr a h1, hgpr b h2]
  | neg64 dst src =>
    simp [checkArmInstr] at hCheck; subst hCheck
    exact ⟨rfl, arm_setGpr_lowEq memPol τ s₁ s₂ dst (τ.gpr src)
      (0#64 - s₁.gpr src) (0#64 - s₂.gpr src) hLowOrig (fun hl => by rw [hgpr src hl])⟩
  | adds64 dst a b =>
    simp [checkArmInstr, execArmInstr] at hCheck ⊢; subst hCheck
    let l := (τ.gpr a).join (τ.gpr b)
    have hOps : l = .pub → s₁.gpr a = s₂.gpr a ∧ s₁.gpr b = s₂.gpr b := by
      intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h1, h2⟩
      exact ⟨hgpr a h1, hgpr b h2⟩
    have hSet := arm_setGpr_lowEq memPol τ s₁ s₂ dst l
      (s₁.gpr a + s₁.gpr b) (s₂.gpr a + s₂.gpr b) hLowOrig
      (fun hl => by rcases hOps hl with ⟨e1, e2⟩; rw [e1, e2])
    rcases hSet with ⟨hg1, hn1, _, _, hm1, hd1, hdr1⟩
    exact ⟨hg1, hn1, fun hl => by rcases hOps hl with ⟨e1, e2⟩; rw [e1, e2],
           fun hl => by rcases hOps hl with ⟨e1, e2⟩; rw [e1, e2], hm1, hd1, hdr1⟩
  | adcZero64 dst =>
    simp [checkArmInstr] at hCheck; subst hCheck
    exact ⟨rfl, arm_setGpr_lowEq memPol τ s₁ s₂ dst τ.c
      (if s₁.flags.c then 1#64 else 0#64) (if s₂.flags.c then 1#64 else 0#64)
      hLowOrig (fun hl => by rw [hc hl])⟩
  | subs64 dst a b =>
    simp [checkArmInstr, execArmInstr] at hCheck ⊢; subst hCheck
    let l := (τ.gpr a).join (τ.gpr b)
    have hOps : l = .pub → s₁.gpr a = s₂.gpr a ∧ s₁.gpr b = s₂.gpr b := by
      intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h1, h2⟩
      exact ⟨hgpr a h1, hgpr b h2⟩
    have hSet := arm_setGpr_lowEq memPol τ s₁ s₂ dst l
      (s₁.gpr a - s₁.gpr b) (s₂.gpr a - s₂.gpr b) hLowOrig
      (fun hl => by rcases hOps hl with ⟨e1, e2⟩; rw [e1, e2])
    rcases hSet with ⟨hg1, hn1, _, _, hm1, hd1, hdr1⟩
    exact ⟨hg1, hn1, fun hl => by rcases hOps hl with ⟨e1, e2⟩; rw [e1, e2],
           fun hl => by rcases hOps hl with ⟨e1, e2⟩; rw [e1, e2], hm1, hd1, hdr1⟩
  | sbcMask64 dst =>
    simp [checkArmInstr] at hCheck; subst hCheck
    exact ⟨rfl, arm_setGpr_lowEq memPol τ s₁ s₂ dst τ.c
      (if s₁.flags.c then 0#64 else 0xFFFFFFFFFFFFFFFF#64)
      (if s₂.flags.c then 0#64 else 0xFFFFFFFFFFFFFFFF#64)
      hLowOrig (fun hl => by rw [hc hl])⟩
  | mulLo64 dst a b =>
    simp only [checkArmInstr] at hCheck
    split at hCheck
    rotate_left
    · cases hCheck
    simp only [Option.some.injEq, Bool.or_eq_true, beq_iff_eq] at *
    subst τ'
    have hv : (τ.gpr a).join (τ.gpr b) = .pub → s₁.gpr a = s₂.gpr a ∧ s₁.gpr b = s₂.gpr b := by
      intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨ha, hb⟩
      exact ⟨hgpr a ha, hgpr b hb⟩
    refine ⟨?_, arm_setGpr_lowEq memPol τ s₁ s₂ dst ((τ.gpr a).join (τ.gpr b)) _ _ hLowOrig ?_⟩
    · rename_i hgate
      rcases hgate with hp | hd
      · obtain ⟨ha, hb⟩ := hv hp
        simp [execArmInstr, hditEq, ha, hb]
      · have hd1 := hditReq hd
        have hd2 := hditEq.symm.trans hd1
        simp [execArmInstr, hd1, hd2]
    · intro hl; obtain ⟨ha, hb⟩ := hv hl
      simp [ha, hb]
  | umulh64 dst a b =>
    simp only [checkArmInstr] at hCheck
    split at hCheck
    rotate_left
    · cases hCheck
    simp only [Option.some.injEq, Bool.or_eq_true, beq_iff_eq] at *
    subst τ'
    have hv : (τ.gpr a).join (τ.gpr b) = .pub → s₁.gpr a = s₂.gpr a ∧ s₁.gpr b = s₂.gpr b := by
      intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨ha, hb⟩
      exact ⟨hgpr a ha, hgpr b hb⟩
    refine ⟨?_, arm_setGpr_lowEq memPol τ s₁ s₂ dst ((τ.gpr a).join (τ.gpr b)) _ _ hLowOrig ?_⟩
    · rename_i hgate
      rcases hgate with hp | hd
      · obtain ⟨ha, hb⟩ := hv hp
        simp [execArmInstr, hditEq, ha, hb]
      · have hd1 := hditReq hd
        have hd2 := hditEq.symm.trans hd1
        simp [execArmInstr, hd1, hd2]
    · intro hl; obtain ⟨ha, hb⟩ := hv hl
      simp [ha, hb]
  | ldr64 dst base disp =>
    simp only [checkArmInstr] at hCheck
    split at hCheck <;> simp_all
    rename_i hbase; subst hCheck
    refine ⟨by simp [execArmInstr, LeakageEvent.clean, hgpr base hbase], ?_⟩
    exact arm_setGpr_lowEq memPol τ s₁ s₂ dst .sec _ _ hLowOrig (by intro h; cases h)
  | str64 src base disp =>
    simp only [checkArmInstr] at hCheck
    split at hCheck <;> simp_all
    rename_i hcond; rcases hcond with ⟨hbase, hsrcOr⟩; subst hCheck
    have hAddr : s₁.gpr base + disp = s₂.gpr base + disp := by rw [hgpr base hbase]
    refine ⟨by simp [execArmInstr, LeakageEvent.clean, hAddr], ?_⟩
    simp only [execArmInstr]; rw [hAddr]
    exact arm_writeMem64_lowEq memPol secHeap τ s₁ s₂ (s₂.gpr base + disp)
      (s₁.gpr src) (s₂.gpr src) hPol hLowOrig
      (fun hsh => by simp [hsh] at hsrcOr; exact hgpr src hsrcOr)
  | ldrQ dst base disp =>
    simp only [checkArmInstr] at hCheck
    split at hCheck <;> simp_all
    rename_i hbase; subst hCheck
    have hAddr : s₁.gpr base + disp = s₂.gpr base + disp := by rw [hgpr base hbase]
    refine ⟨by simp [execArmInstr, LeakageEvent.clean, hAddr], ?_⟩
    exact arm_setNeon_lowEq memPol τ s₁ s₂ dst .sec _ _ hLowOrig (by intro h; cases h)
  | strQ src base disp =>
    simp only [checkArmInstr] at hCheck
    split at hCheck <;> simp_all
    rename_i hcond; rcases hcond with ⟨hbase, hsrcOr⟩; subst hCheck
    have hAddr : s₁.gpr base + disp = s₂.gpr base + disp := by rw [hgpr base hbase]
    refine ⟨by simp [execArmInstr, LeakageEvent.clean, hAddr], ?_⟩
    simp only [execArmInstr, ArmState.writeMem128]; rw [hAddr]
    have hvEq : secHeap = false → s₁.neon src = s₂.neon src := by
      intro hsh; simp [hsh] at hsrcOr; exact hneon src hsrcOr
    have hw0 := arm_writeMem64_lowEq memPol secHeap τ s₁ s₂ (s₂.gpr base + disp)
      (s₁.neon src).lo (s₂.neon src).lo hPol hLowOrig (fun h => by rw [hvEq h])
    exact arm_writeMem64_lowEq memPol secHeap τ _ _ (s₂.gpr base + disp + 8#64)
      (s₁.neon src).hi (s₂.neon src).hi hPol hw0 (fun h => by rw [hvEq h])
  | eorV16b dst a b =>
    simp only [checkArmInstr, execArmInstr] at hCheck ⊢
    by_cases hab : (a == b) = true
    · simp [hab] at hCheck ⊢; subst hCheck
      exact arm_setNeon_lowEq memPol τ s₁ s₂ dst .pub Vec128.zero Vec128.zero hLowOrig
        (fun _ => rfl)
    · simp [hab] at hCheck ⊢; subst hCheck
      refine arm_setNeon_lowEq memPol τ s₁ s₂ dst ((τ.neon a).join (τ.neon b))
        (Vec128.xor (s₁.neon a) (s₁.neon b)) (Vec128.xor (s₂.neon a) (s₂.neon b)) hLowOrig ?_
      intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h1, h2⟩
      rw [hneon a h1, hneon b h2]
  | bcaxV16b dst vn vm va =>
    simp [checkArmInstr] at hCheck; subst hCheck
    refine ⟨rfl, arm_setNeon_lowEq memPol τ s₁ s₂ dst
      (((τ.neon vn).join (τ.neon vm)).join (τ.neon va))
      (Vec128.bcax (s₁.neon vn) (s₁.neon vm) (s₁.neon va))
      (Vec128.bcax (s₂.neon vn) (s₂.neon vm) (s₂.neon va)) hLowOrig ?_⟩
    intro hl
    rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h12, h3⟩
    rcases (SecLabel.join_eq_pub_iff _ _).mp h12 with ⟨h1, h2⟩
    rw [hneon vn h1, hneon vm h2, hneon va h3]
  | eor3V16b dst vn vm va =>
    simp [checkArmInstr] at hCheck; subst hCheck
    refine ⟨rfl, arm_setNeon_lowEq memPol τ s₁ s₂ dst
      (((τ.neon vn).join (τ.neon vm)).join (τ.neon va))
      (Vec128.eor3 (s₁.neon vn) (s₁.neon vm) (s₁.neon va))
      (Vec128.eor3 (s₂.neon vn) (s₂.neon vm) (s₂.neon va)) hLowOrig ?_⟩
    intro hl
    rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h12, h3⟩
    rcases (SecLabel.join_eq_pub_iff _ _).mp h12 with ⟨h1, h2⟩
    rw [hneon vn h1, hneon vm h2, hneon va h3]
  | rax1V2d dst vn vm =>
    simp [checkArmInstr] at hCheck; subst hCheck
    refine ⟨rfl, arm_setNeon_lowEq memPol τ s₁ s₂ dst ((τ.neon vn).join (τ.neon vm))
      (Vec128.rax1 (s₁.neon vn) (s₁.neon vm)) (Vec128.rax1 (s₂.neon vn) (s₂.neon vm)) hLowOrig ?_⟩
    intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h1, h2⟩
    rw [hneon vn h1, hneon vm h2]
  | xarV2d dst vn vm imm6 =>
    simp [checkArmInstr] at hCheck; subst hCheck
    refine ⟨rfl, arm_setNeon_lowEq memPol τ s₁ s₂ dst ((τ.neon vn).join (τ.neon vm))
      (Vec128.xar (s₁.neon vn) (s₁.neon vm) imm6)
      (Vec128.xar (s₂.neon vn) (s₂.neon vm) imm6) hLowOrig ?_⟩
    intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h1, h2⟩
    rw [hneon vn h1, hneon vm h2]
  | pmull1q dst a b =>
    simp only [checkArmInstr] at hCheck
    split at hCheck
    rotate_left
    · cases hCheck
    simp only [Option.some.injEq, Bool.or_eq_true, beq_iff_eq] at *
    subst τ'
    have hv : (τ.neon a).join (τ.neon b) = .pub → s₁.neon a = s₂.neon a ∧ s₁.neon b = s₂.neon b := by
      intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨ha, hb⟩
      exact ⟨hneon a ha, hneon b hb⟩
    refine ⟨?_, arm_setNeon_lowEq memPol τ s₁ s₂ dst ((τ.neon a).join (τ.neon b)) _ _ hLowOrig ?_⟩
    · rename_i hgate
      rcases hgate with hp | hd
      · obtain ⟨ha, hb⟩ := hv hp
        simp [execArmInstr, hditEq, ha, hb]
      · have hd1 := hditReq hd
        have hd2 := hditEq.symm.trans hd1
        simp [execArmInstr, hd1, hd2]
    · intro hl; obtain ⟨ha, hb⟩ := hv hl
      simp [ha, hb]
  | pmull2_1q dst a b =>
    simp only [checkArmInstr] at hCheck
    split at hCheck
    rotate_left
    · cases hCheck
    simp only [Option.some.injEq, Bool.or_eq_true, beq_iff_eq] at *
    subst τ'
    have hv : (τ.neon a).join (τ.neon b) = .pub → s₁.neon a = s₂.neon a ∧ s₁.neon b = s₂.neon b := by
      intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨ha, hb⟩
      exact ⟨hneon a ha, hneon b hb⟩
    refine ⟨?_, arm_setNeon_lowEq memPol τ s₁ s₂ dst ((τ.neon a).join (τ.neon b)) _ _ hLowOrig ?_⟩
    · rename_i hgate
      rcases hgate with hp | hd
      · obtain ⟨ha, hb⟩ := hv hp
        simp [execArmInstr, hditEq, ha, hb]
      · have hd1 := hditReq hd
        have hd2 := hditEq.symm.trans hd1
        simp [execArmInstr, hd1, hd2]
    · intro hl; obtain ⟨ha, hb⟩ := hv hl
      simp [ha, hb]
  | extV16b8 dst a b =>
    simp [checkArmInstr] at hCheck; subst hCheck
    refine ⟨rfl, arm_setNeon_lowEq memPol τ s₁ s₂ dst ((τ.neon a).join (τ.neon b))
      (Vec128.ext8 (s₁.neon a) (s₁.neon b)) (Vec128.ext8 (s₂.neon a) (s₂.neon b)) hLowOrig ?_⟩
    intro hl; rcases (SecLabel.join_eq_pub_iff _ _).mp hl with ⟨h1, h2⟩
    rw [hneon a h1, hneon b h2]
  | cselEq64 dst a b =>
    simp only [checkArmInstr] at hCheck
    by_cases hpub : (((τ.z.join (τ.gpr a)).join (τ.gpr b)) == .pub) = true
    · simp [hpub] at hCheck; subst hCheck
      have hpubEq : (τ.z.join (τ.gpr a)).join (τ.gpr b) = .pub := by simpa using hpub
      rcases (SecLabel.join_eq_pub_iff _ _).mp hpubEq with ⟨hzA, hbP⟩
      rcases (SecLabel.join_eq_pub_iff _ _).mp hzA with ⟨hzP, haP⟩
      refine ⟨?_, arm_setGpr_lowEq memPol τ s₁ s₂ dst .pub
        (if s₁.flags.z then s₁.gpr a else s₁.gpr b)
        (if s₂.flags.z then s₂.gpr a else s₂.gpr b) hLowOrig ?_⟩
      · simp [execArmInstr, hditEq, hz hzP, hgpr a haP, hgpr b hbP]
      · intro _; simp [hz hzP, hgpr a haP, hgpr b hbP]
    · simp [hpub] at hCheck
      rcases hCheck with ⟨hditAct, rfl⟩
      have hd1 : s₁.ditEnabled = true := hditReq hditAct
      have hd2 : s₂.ditEnabled = true := hditEq.symm.trans hd1
      refine ⟨by simp [execArmInstr, hd1, hd2], ?_⟩
      exact arm_setGpr_lowEq memPol τ s₁ s₂ dst .sec _ _ hLowOrig (by intro h; cases h)
  | udiv64 dst a b =>
    simp only [checkArmInstr] at hCheck
    split at hCheck <;> simp_all
    rename_i habP; rcases habP with ⟨haP, hbP⟩; subst hCheck
    have ea := hgpr a haP
    have eb := hgpr b hbP
    refine ⟨by simp [execArmInstr, ea, eb], ?_⟩
    exact arm_setGpr_lowEq memPol τ s₁ s₂ dst .pub
      (if s₁.gpr b == 0#64 then 0#64 else BitVec.ofNat 64 ((s₁.gpr a).toNat / (s₁.gpr b).toNat))
      (if s₂.gpr b == 0#64 then 0#64 else BitVec.ofNat 64 ((s₂.gpr a).toNat / (s₂.gpr b).toNat))
      hLowOrig (fun _ => by rw [ea, eb])
  | ldrIndexed64 dst base idx =>
    simp only [checkArmInstr] at hCheck
    split at hCheck <;> simp_all
    rename_i hbi; rcases hbi with ⟨hbP, hiP⟩; subst hCheck
    refine ⟨by simp [execArmInstr, LeakageEvent.clean, hgpr base hbP, hgpr idx hiP], ?_⟩
    exact arm_setGpr_lowEq memPol τ s₁ s₂ dst .sec _ _ hLowOrig (by intro h; cases h)

theorem checkArmBlock_sound
    (memPol : BitVec 64 → SecLabel) (secHeap : Bool)
    (hPol : secHeap = true → ∀ a, memPol a = .sec)
    (blk : List ArmInstr) (τ τ' : ArmTaintState) (pc : Nat)
    (hCheck : checkArmBlock secHeap τ blk = some τ')
    (s₁ s₂ : ArmState) (hLow : ArmLowEq memPol τ s₁ s₂) :
    (execArmBlock blk pc s₁).2 = (execArmBlock blk pc s₂).2 ∧
    ArmLowEq memPol τ' (execArmBlock blk pc s₁).1 (execArmBlock blk pc s₂).1 := by
  induction blk generalizing τ pc s₁ s₂ with
  | nil => simp [checkArmBlock] at hCheck; subst hCheck; exact ⟨rfl, hLow⟩
  | cons ins rest ih =>
    simp only [checkArmBlock] at hCheck
    cases hIns : checkArmInstr secHeap τ ins with
    | none => simp [hIns] at hCheck
    | some τ1 =>
      simp [hIns] at hCheck
      obtain ⟨hEv, hLow1⟩ := checkArmInstr_sound memPol secHeap hPol τ τ1 ins pc hIns s₁ s₂ hLow
      obtain ⟨hEvs, hLow2⟩ :=
        ih τ1 (pc + 1) hCheck (execArmInstr ins pc s₁).1 (execArmInstr ins pc s₂).1 hLow1
      simp only [execArmBlock]
      exact ⟨by rw [hEv, hEvs], hLow2⟩

theorem checkArmLoop_sound
    (memPol : BitVec 64 → SecLabel) (secHeap : Bool)
    (hPol : secHeap = true → ∀ a, memPol a = .sec)
    (trips : Nat) (body : List ArmInstr) (τ τ' : ArmTaintState) (pc : Nat)
    (hCheck : checkArmLoop secHeap trips τ body = some τ')
    (s₁ s₂ : ArmState) (hLow : ArmLowEq memPol τ s₁ s₂) :
    (execArmLoop trips body pc s₁).2 = (execArmLoop trips body pc s₂).2 ∧
    ArmLowEq memPol τ' (execArmLoop trips body pc s₁).1 (execArmLoop trips body pc s₂).1 := by
  induction trips generalizing τ pc s₁ s₂ with
  | zero => simp [checkArmLoop] at hCheck; subst hCheck; exact ⟨rfl, hLow⟩
  | succ n ih =>
    simp only [checkArmLoop] at hCheck
    cases hBlk : checkArmBlock secHeap τ body with
    | none => simp [hBlk] at hCheck
    | some τ1 =>
      simp [hBlk] at hCheck
      obtain ⟨hEv1, hLow1⟩ := checkArmBlock_sound memPol secHeap hPol body τ τ1 pc hBlk s₁ s₂ hLow
      obtain ⟨hEv2, hLow2⟩ :=
        ih τ1 (pc + body.length) hCheck
          (execArmBlock body pc s₁).1 (execArmBlock body pc s₂).1 hLow1
      simp only [execArmLoop]
      exact ⟨by rw [hEv1, hEv2], hLow2⟩

theorem armLowEq_join_left (memPol : BitVec 64 → SecLabel)
    (τT τE : ArmTaintState) (s₁ s₂ : ArmState)
    (hLow : ArmLowEq memPol τT s₁ s₂) :
    ArmLowEq memPol
      { gpr := fun r => (τT.gpr r).join (τE.gpr r)
        neon := fun v => (τT.neon v).join (τE.neon v)
        z := τT.z.join τE.z
        c := τT.c.join τE.c
        ditAssumed := τT.ditAssumed && τE.ditAssumed } s₁ s₂ := by
  rcases hLow with ⟨hg, hn, hz, hc, hm, hdEq, hdReq⟩
  refine ⟨?_, ?_, ?_, ?_, hm, hdEq, ?_⟩
  · intro r hr; exact hg r ((SecLabel.join_eq_pub_iff _ _).mp hr).1
  · intro v hv; exact hn v ((SecLabel.join_eq_pub_iff _ _).mp hv).1
  · intro hP; exact hz ((SecLabel.join_eq_pub_iff _ _).mp hP).1
  · intro hP; exact hc ((SecLabel.join_eq_pub_iff _ _).mp hP).1
  · intro hD; simp at hD; exact hdReq hD.1

theorem armLowEq_join_right (memPol : BitVec 64 → SecLabel)
    (τT τE : ArmTaintState) (s₁ s₂ : ArmState)
    (hLow : ArmLowEq memPol τE s₁ s₂) :
    ArmLowEq memPol
      { gpr := fun r => (τT.gpr r).join (τE.gpr r)
        neon := fun v => (τT.neon v).join (τE.neon v)
        z := τT.z.join τE.z
        c := τT.c.join τE.c
        ditAssumed := τT.ditAssumed && τE.ditAssumed } s₁ s₂ := by
  rcases hLow with ⟨hg, hn, hz, hc, hm, hdEq, hdReq⟩
  refine ⟨?_, ?_, ?_, ?_, hm, hdEq, ?_⟩
  · intro r hr; exact hg r ((SecLabel.join_eq_pub_iff _ _).mp hr).2
  · intro v hv; exact hn v ((SecLabel.join_eq_pub_iff _ _).mp hv).2
  · intro hP; exact hz ((SecLabel.join_eq_pub_iff _ _).mp hP).2
  · intro hP; exact hc ((SecLabel.join_eq_pub_iff _ _).mp hP).2
  · intro hD; simp at hD; exact hdReq hD.2

/-- **Master `aarch64` Constant-Time Timing-Noninterference Soundness Theorem**:
    Any `aarch64` assembly program accepted by `checkArmProg` emits identical microarchitectural
    leakage traces across all secret-varying states `s₁, s₂` satisfying `ArmLowEq`. -/
theorem arm_ct_checker_sound
    (memPol : BitVec 64 → SecLabel) (secHeap : Bool)
    (hPol : secHeap = true → ∀ a, memPol a = .sec)
    (prog : List ArmStmt) (τ τ' : ArmTaintState) (pc : Nat)
    (hCheck : checkArmProg secHeap τ prog = some τ')
    (s₁ s₂ : ArmState) (hLow : ArmLowEq memPol τ s₁ s₂) :
    (execArmProg prog pc s₁).2 = (execArmProg prog pc s₂).2 ∧
    ArmLowEq memPol τ' (execArmProg prog pc s₁).1 (execArmProg prog pc s₂).1 := by
  induction prog generalizing τ pc s₁ s₂ with
  | nil => simp [checkArmProg] at hCheck; subst hCheck; exact ⟨rfl, hLow⟩
  | cons stmt rest ih =>
    cases stmt with
    | instr ins =>
      simp only [checkArmProg] at hCheck
      cases hIns : checkArmInstr secHeap τ ins with
      | none => simp [hIns] at hCheck
      | some τ1 =>
        simp [hIns] at hCheck
        obtain ⟨hEv, hLow1⟩ := checkArmInstr_sound memPol secHeap hPol τ τ1 ins pc hIns s₁ s₂ hLow
        obtain ⟨hEvs, hLow2⟩ :=
          ih τ1 (pc + 1) hCheck (execArmInstr ins pc s₁).1 (execArmInstr ins pc s₂).1 hLow1
        simp only [execArmProg]
        exact ⟨by rw [hEv, hEvs], hLow2⟩
    | cbnz condReg thenBody elseBody =>
      simp only [checkArmProg] at hCheck
      by_cases hCond : (τ.gpr condReg == .pub) = true
      · simp [hCond] at hCheck
        cases hT : checkArmBlock secHeap τ thenBody with
        | none => simp [hT] at hCheck
        | some τT =>
          cases hE : checkArmBlock secHeap τ elseBody with
          | none => simp [hT, hE] at hCheck
          | some τE =>
            simp [hT, hE] at hCheck
            have hCondPub : τ.gpr condReg = .pub := by simpa using hCond
            have hCondEq : s₁.gpr condReg = s₂.gpr condReg := hLow.1 condReg hCondPub
            simp only [execArmProg, hCondEq]
            by_cases hTaken : (s₂.gpr condReg != 0#64) = true
            · simp only [hTaken, ↓reduceIte]
              obtain ⟨hEv1, hLowT⟩ :=
                checkArmBlock_sound memPol secHeap hPol thenBody τ τT (pc + 1) hT s₁ s₂ hLow
              obtain ⟨hEv2, hLowRest⟩ :=
                ih _ (pc + 1 + thenBody.length) hCheck _ _ (armLowEq_join_left memPol τT τE _ _ hLowT)
              exact ⟨by rw [hEv1, hEv2], hLowRest⟩
            · simp only [hTaken, Bool.false_eq_true, ↓reduceIte]
              obtain ⟨hEv1, hLowE⟩ :=
                checkArmBlock_sound memPol secHeap hPol elseBody τ τE (pc + 1) hE s₁ s₂ hLow
              obtain ⟨hEv2, hLowRest⟩ :=
                ih _ (pc + 1 + elseBody.length) hCheck _ _ (armLowEq_join_right memPol τT τE _ _ hLowE)
              exact ⟨by rw [hEv1, hEv2], hLowRest⟩
      · simp [hCond] at hCheck
    | pubLoop trips body =>
      simp only [checkArmProg] at hCheck
      cases hLp : checkArmLoop secHeap trips τ body with
      | none => simp [hLp] at hCheck
      | some τ1 =>
        simp [hLp] at hCheck
        obtain ⟨hEv1, hLow1⟩ :=
          checkArmLoop_sound memPol secHeap hPol trips body τ τ1 pc hLp s₁ s₂ hLow
        obtain ⟨hEv2, hLow2⟩ :=
          ih τ1 (pc + trips * body.length) hCheck
            (execArmLoop trips body pc s₁).1 (execArmLoop trips body pc s₂).1 hLow1
        simp only [execArmProg]
        exact ⟨by rw [hEv1, hEv2], hLow2⟩
    | ret =>
      simp [checkArmProg] at hCheck; subst hCheck
      exact ⟨rfl, hLow⟩

/-! ## 6. Negative `#tooth` Mutation-Sensitivity & Concrete Leakage Witnesses -/

def defaultX86State (secVal : BitVec 64) : X86State :=
  { gpr := fun r => if r == .rdi then secVal else 0x1000#64
    ymm := fun _ => Vec256.zero
    flags := { cf := false, of := false, zf := false }
    mem := fun _ => 0#64
    doitEnabled := false
    ymmUpperDirty := false }

def defaultX86Taint : X86TaintState :=
  { gpr := fun r => if r == .rdi then .sec else .pub
    ymm := fun _ => .pub
    cf := .pub
    of := .pub
    zf := .pub
    doitAssumed := false
    upperYmmClean := true }

/-- **Tooth 1 (`jcc` on secret register)**: Rejected statically (`= none`) AND exhibits concrete
    branch-predictor trace divergence on `rdi = 0` vs `rdi = 1`. -/
theorem tooth_secret_jcc_leaks_and_rejected :
    let leakyProg : List X86Stmt := [.jccNz .rdi [.movImm64 .rax 1#64] [.movImm64 .rax 0#64], .ret]
    checkX86Prog true defaultX86Taint leakyProg = none ∧
    X86LowEq (fun _ => .sec) defaultX86Taint (defaultX86State 0#64) (defaultX86State 1#64) ∧
    (execX86Prog leakyProg 0 (defaultX86State 0#64)).2 ≠
      (execX86Prog leakyProg 0 (defaultX86State 1#64)).2 := by
  refine ⟨rfl, ?_, by decide⟩
  refine ⟨?_, fun _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
          ?_, rfl, ?_, rfl, fun _ => rfl⟩
  · intro r hr
    cases r <;> simp [defaultX86Taint, defaultX86State] at hr ⊢
  · intro _ h; cases h
  · intro h; cases h

/-- Secret shift carry reaches a branch through SBB: rejection and concrete trace divergence. -/
theorem tooth_secret_shr_cf_sbb_rejected :
    let p : List X86Stmt := [.instr (.shrImm64 .rdi 1), .instr (.sbbSelf64 .rax),
      .jccNz .rax [.movImm64 .rcx 1#64] [.movImm64 .rcx 0#64], .ret]
    checkX86Prog true defaultX86Taint p = none ∧
    (execX86Prog p 0 (defaultX86State 0#64)).2 ≠
      (execX86Prog p 0 (defaultX86State 1#64)).2 := by
  exact ⟨rfl, by decide⟩

/-- **Tooth 2 (`[base + secret_idx * 8]` S-box / LUT memory access)**: Rejected statically (`= none`)
    AND leaks distinct effective virtual cache addresses (`0x1000` vs `0x1040`). -/
theorem tooth_secret_mem_index_leaks_and_rejected :
    let leakyLut : List X86Stmt := [.instr (.loadIndexed64 .rax .rsi .rdi 8#64), .ret]
    checkX86Prog true defaultX86Taint leakyLut = none ∧
    (execX86Prog leakyLut 0 (defaultX86State 0#64)).2 ≠
      (execX86Prog leakyLut 0 (defaultX86State 8#64)).2 := by
  exact ⟨rfl, by decide⟩

/-- **Tooth 3 (`div` on secret operand, EVEN with hardware `DOIT` enabled!)**: Rejected statically
    (`= none`) AND leaks secret dividend/divisor in `varLatencyOperands`. -/
theorem tooth_secret_div64_leaks_even_under_doit :
    let leakyDiv : List X86Stmt := [.instr (.div64 .rdi), .ret]
    let τDoit := { defaultX86Taint with doitAssumed := true }
    let s₁ := { defaultX86State 3#64 with doitEnabled := true }
    let s₂ := { defaultX86State 17#64 with doitEnabled := true }
    checkX86Prog true τDoit leakyDiv = none ∧
    (execX86Prog leakyDiv 0 s₁).2 ≠ (execX86Prog leakyDiv 0 s₂).2 := by
  exact ⟨rfl, by decide⟩

/-- **Tooth 4 (Omitted `vzeroupper` before `ret` after touching `YMM`)**: Rejected statically
    (`= none`) AND triggers `dirtyUpperYmmOnRet = true` AVX-SSE transition penalty. -/
theorem tooth_dirty_ymm_ret_rejected_and_flagged :
    let missingVzeroupper : List X86Stmt := [.instr (.vpxor .ymm0 .ymm0 .ymm0), .ret]
    let cleanWithVzeroupper : List X86Stmt :=
      [.instr (.vpxor .ymm0 .ymm0 .ymm0), .instr .vzeroupper, .ret]
    checkX86Prog true defaultX86Taint missingVzeroupper = none ∧
    (checkX86Prog true defaultX86Taint cleanWithVzeroupper).isSome = true ∧
    (execX86Prog missingVzeroupper 0 (defaultX86State 0#64)).2 =
      [LeakageEvent.clean 0,
       { pc := 1, branchTaken := none, memAddrs := [], varLatencyOperands := [],
         dirtyUpperYmmOnRet := true }] := by
  exact ⟨rfl, rfl, rfl⟩

/-- **Tooth 5 (`aarch64` `csel` without `MSR DIT, #1` vs with `MSR DIT, #1`)**:
    Unguarded secret `csel` is rejected statically (`= none`) and leaks in `varLatencyOperands`
    when `ditEnabled = false`, whereas prepending `MSR DIT, #1` enables hardware `FEAT_DIT` and is
    accepted with identical leakage traces! -/
theorem tooth_arm_csel_requires_msr_dit1 :
    let τArm : ArmTaintState :=
      { gpr := fun r => if r == .x0 then .sec else .pub
        neon := fun _ => .pub, z := .sec, c := .pub, ditAssumed := false }
    let sArm (b : Bool) : ArmState :=
      { gpr := fun r => if r == .x0 then (if b then 99#64 else 11#64) else 0#64
        neon := fun _ => Vec128.zero, flags := { z := b, c := false }
        mem := fun _ => 0#64, ditEnabled := false }
    let unguardedProg : List ArmStmt := [.instr (.cselEq64 .x1 .x0 .x2), .ret]
    let ditGuardedProg : List ArmStmt := [.instr .msrDit1, .instr (.cselEq64 .x1 .x0 .x2), .ret]
    checkArmProg true τArm unguardedProg = none ∧
    (execArmProg unguardedProg 0 (sArm false)).2 ≠ (execArmProg unguardedProg 0 (sArm true)).2 ∧
    (checkArmProg true τArm ditGuardedProg).isSome = true ∧
    (execArmProg ditGuardedProg 0 (sArm false)).2 = (execArmProg ditGuardedProg 0 (sArm true)).2 := by
  exact ⟨rfl, by decide, rfl, rfl⟩

/-! ## 7. Concrete `qsag-asm` Kernel ASTs: Timing-Noninterference & Functional Correctness -/

def sysvPtrArgs4Taint : X86TaintState :=
  { gpr := fun r =>
      match r with
      | .rdi | .rsi | .rdx | .rcx | .rsp => .pub
      | _ => .sec
    ymm := fun _ => .sec
    cf := .sec
    of := .sec
    zf := .sec
    doitAssumed := false
    upperYmmClean := true }

def aapcsPtrArgs3Taint : ArmTaintState :=
  { gpr := fun r =>
      match r with
      | .x0 | .x1 | .x2 | .sp => .pub
      | _ => .sec
    neon := fun _ => .sec
    z := .sec
    c := .sec
    ditAssumed := false }

/-! ### 7.1 `keccak_chi_mpc_avx2` & `keccak_sha3_neon` (256-Way 3-Party RSS `χ` + `BCAX`) -/

@[expose]
def keccakChiLane (a0 a1 a2 : BitVec 64) : BitVec 64 :=
  a0 ^^^ ((~~~a1) &&& a2)

def keccakChiVec256 (a0 a1 a2 : Vec256) : Vec256 :=
  ⟨ keccakChiLane a0.w0 a1.w0 a2.w0
  , keccakChiLane a0.w1 a1.w1 a2.w1
  , keccakChiLane a0.w2 a1.w2 a2.w2
  , keccakChiLane a0.w3 a1.w3 a2.w3 ⟩

def keccakChiMpcShareLane
    (s0_x s0_x1 s0_x2 s1_x1 s1_x2 mask_x : BitVec 64) : BitVec 64 :=
  (((s0_x1 &&& (s0_x2 ^^^ s1_x2)) ^^^ (s1_x1 &&& s0_x2)) ^^^ (s0_x ^^^ s0_x2)) ^^^ mask_x

def keccakChiMpcShareVec256
    (s0_x s0_x1 s0_x2 s1_x1 s1_x2 mask_x : Vec256) : Vec256 :=
  Vec256.xor
    (Vec256.xor
      (Vec256.xor
        (Vec256.and s0_x1 (Vec256.xor s0_x2 s1_x2))
        (Vec256.and s1_x1 s0_x2))
      (Vec256.xor s0_x s0_x2))
    mask_x

private theorem keccak_chi_rss_core_bool (b0 b1 b2 c0 c1 c2 : Bool) :
    xor (xor
      (xor (xor (and b0 (xor c0 c1)) (and b1 c0)) c0)
      (xor (xor (and b1 (xor c1 c2)) (and b2 c1)) c1))
      (xor (xor (and b2 (xor c2 c0)) (and b0 c2)) c2) =
    and (not (xor (xor b0 b1) b2)) (xor (xor c0 c1) c2) := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases c0 <;> cases c1 <;> cases c2 <;> rfl

private theorem keccak_chi_rss_full_bool
    (a0 a1 a2 b0 b1 b2 c0 c1 c2 m0 m1 m2 : Bool)
    (hm : xor (xor m0 m1) m2 = false) :
    xor (xor
      (xor (xor (xor (and b0 (xor c0 c1)) (and b1 c0)) (xor a0 c0)) m0)
      (xor (xor (xor (and b1 (xor c1 c2)) (and b2 c1)) (xor a1 c1)) m1))
      (xor (xor (xor (and b2 (xor c2 c0)) (and b0 c2)) (xor a2 c2)) m2) =
    xor (xor (xor a0 a1) a2) (and (not (xor (xor b0 b1) b2)) (xor (xor c0 c1) c2)) := by
  revert a0 a1 a2 b0 b1 b2 c0 c1 c2 m0 m1 m2
  decide +kernel

/-- **3-Party Replicated Secret Sharing (`RSS`) Keccak `χ` Gate Reconstruction Theorem**:
    For any 3-party RSS sharing `(a0, a1, a2)`, `(b0, b1, b2)`, `(c0, c1, c2)` and zero-sum
    correlated randomness `m0 ^^^ m1 ^^^ m2 = 0`, the bitwise XOR of the three parties' local
    `keccakChiMpcShareLane` outputs reconstructs `keccakChiLane (a0^^^a1^^^a2) (b0^^^b1^^^b2) (c0^^^c1^^^c2)`. -/
theorem keccakChiMpc_3party_rss_sound
    (a0 a1 a2 b0 b1 b2 c0 c1 c2 m0 m1 m2 : BitVec 64)
    (hm : m0 ^^^ m1 ^^^ m2 = 0#64) :
    keccakChiMpcShareLane a0 b0 c0 b1 c1 m0 ^^^
    keccakChiMpcShareLane a1 b1 c1 b2 c2 m1 ^^^
    keccakChiMpcShareLane a2 b2 c2 b0 c0 m2 =
    keccakChiLane (a0 ^^^ a1 ^^^ a2) (b0 ^^^ b1 ^^^ b2) (c0 ^^^ c1 ^^^ c2) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hmi : xor (xor (m0.getLsbD i) (m1.getLsbD i)) (m2.getLsbD i) = false := by
    have h0 := congrArg (fun v => v.getLsbD i) hm
    simpa [hi] using h0
  simp only [keccakChiMpcShareLane, keccakChiLane, BitVec.getLsbD_xor, BitVec.getLsbD_and,
             Constructive.getLsbD_not, hi, decide_true, Bool.true_and]
  exact keccak_chi_rss_full_bool
    (a0.getLsbD i) (a1.getLsbD i) (a2.getLsbD i)
    (b0.getLsbD i) (b1.getLsbD i) (b2.getLsbD i)
    (c0.getLsbD i) (c1.getLsbD i) (c2.getLsbD i)
    (m0.getLsbD i) (m1.getLsbD i) (m2.getLsbD i) hmi

/-- Exact 65-instruction `qsag_asm_keccak_chi_mpc_avx2` program (`x86_64_asm.rs:467-542`). -/
def keccakChiMpcAvx2Prog : List X86Stmt :=
  [ -- Load s0[0..4] -> ymm0..ymm4 and s1[0..4] -> ymm5..ymm9
    .instr (.vmovdquLoad .ymm0 .rsi 0#64)
  , .instr (.vmovdquLoad .ymm1 .rsi 32#64)
  , .instr (.vmovdquLoad .ymm2 .rsi 64#64)
  , .instr (.vmovdquLoad .ymm3 .rsi 96#64)
  , .instr (.vmovdquLoad .ymm4 .rsi 128#64)
  , .instr (.vmovdquLoad .ymm5 .rdx 0#64)
  , .instr (.vmovdquLoad .ymm6 .rdx 32#64)
  , .instr (.vmovdquLoad .ymm7 .rdx 64#64)
  , .instr (.vmovdquLoad .ymm8 .rdx 96#64)
  , .instr (.vmovdquLoad .ymm9 .rdx 128#64)
    -- Lane x = 0 (x1 = 1, x2 = 2)
  , .instr (.vpxor .ymm10 .ymm2 .ymm7)
  , .instr (.vpand .ymm10 .ymm1 .ymm10)
  , .instr (.vpand .ymm11 .ymm6 .ymm2)
  , .instr (.vpxor .ymm10 .ymm10 .ymm11)
  , .instr (.vpxor .ymm11 .ymm0 .ymm2)
  , .instr (.vpxor .ymm10 .ymm10 .ymm11)
  , .instr (.vpxorMem .ymm10 .ymm10 .rcx 0#64)
  , .instr (.vmovdquStore .rdi 0#64 .ymm10)
    -- Lane x = 1 (x1 = 2, x2 = 3)
  , .instr (.vpxor .ymm10 .ymm3 .ymm8)
  , .instr (.vpand .ymm10 .ymm2 .ymm10)
  , .instr (.vpand .ymm11 .ymm7 .ymm3)
  , .instr (.vpxor .ymm10 .ymm10 .ymm11)
  , .instr (.vpxor .ymm11 .ymm1 .ymm3)
  , .instr (.vpxor .ymm10 .ymm10 .ymm11)
  , .instr (.vpxorMem .ymm10 .ymm10 .rcx 32#64)
  , .instr (.vmovdquStore .rdi 32#64 .ymm10)
    -- Lane x = 2 (x1 = 3, x2 = 4)
  , .instr (.vpxor .ymm10 .ymm4 .ymm9)
  , .instr (.vpand .ymm10 .ymm3 .ymm10)
  , .instr (.vpand .ymm11 .ymm8 .ymm4)
  , .instr (.vpxor .ymm10 .ymm10 .ymm11)
  , .instr (.vpxor .ymm11 .ymm2 .ymm4)
  , .instr (.vpxor .ymm10 .ymm10 .ymm11)
  , .instr (.vpxorMem .ymm10 .ymm10 .rcx 64#64)
  , .instr (.vmovdquStore .rdi 64#64 .ymm10)
    -- Lane x = 3 (x1 = 4, x2 = 0)
  , .instr (.vpxor .ymm10 .ymm0 .ymm5)
  , .instr (.vpand .ymm10 .ymm4 .ymm10)
  , .instr (.vpand .ymm11 .ymm9 .ymm0)
  , .instr (.vpxor .ymm10 .ymm10 .ymm11)
  , .instr (.vpxor .ymm11 .ymm3 .ymm0)
  , .instr (.vpxor .ymm10 .ymm10 .ymm11)
  , .instr (.vpxorMem .ymm10 .ymm10 .rcx 96#64)
  , .instr (.vmovdquStore .rdi 96#64 .ymm10)
    -- Lane x = 4 (x1 = 0, x2 = 1)
  , .instr (.vpxor .ymm10 .ymm1 .ymm6)
  , .instr (.vpand .ymm10 .ymm0 .ymm10)
  , .instr (.vpand .ymm11 .ymm5 .ymm1)
  , .instr (.vpxor .ymm10 .ymm10 .ymm11)
  , .instr (.vpxor .ymm11 .ymm4 .ymm1)
  , .instr (.vpxor .ymm10 .ymm10 .ymm11)
  , .instr (.vpxorMem .ymm10 .ymm10 .rcx 128#64)
  , .instr (.vmovdquStore .rdi 128#64 .ymm10)
    -- Wipe all 12 YMM share/scratch registers + vzeroupper + ret
  , .instr (.vpxor .ymm0 .ymm0 .ymm0)
  , .instr (.vpxor .ymm1 .ymm1 .ymm1)
  , .instr (.vpxor .ymm2 .ymm2 .ymm2)
  , .instr (.vpxor .ymm3 .ymm3 .ymm3)
  , .instr (.vpxor .ymm4 .ymm4 .ymm4)
  , .instr (.vpxor .ymm5 .ymm5 .ymm5)
  , .instr (.vpxor .ymm6 .ymm6 .ymm6)
  , .instr (.vpxor .ymm7 .ymm7 .ymm7)
  , .instr (.vpxor .ymm8 .ymm8 .ymm8)
  , .instr (.vpxor .ymm9 .ymm9 .ymm9)
  , .instr (.vpxor .ymm10 .ymm10 .ymm10)
  , .instr (.vpxor .ymm11 .ymm11 .ymm11)
  , .instr .vzeroupper
  , .ret ]

/-- **Timing-Noninterference & Upper-YMM Hygiene of `qsag_asm_keccak_chi_mpc_avx2`**:
    Produces bit-identical leakage traces on all secret-varying states agreeing on public buffer
    pointers `(rdi, rsi, rdx, rcx)` and returns with `ymmUpperDirty = false` and wiped `ymm0..ymm11`. -/
theorem keccakChiMpcAvx2_constant_time
    (s₁ s₂ : X86State)
    (hLow : X86LowEq (fun _ => .sec) sysvPtrArgs4Taint s₁ s₂) :
    (execX86Prog keccakChiMpcAvx2Prog 0 s₁).2 = (execX86Prog keccakChiMpcAvx2Prog 0 s₂).2 ∧
    (execX86Prog keccakChiMpcAvx2Prog 0 s₁).1.ymmUpperDirty = false ∧
    (execX86Prog keccakChiMpcAvx2Prog 0 s₁).1.ymm .ymm0 = Vec256.zero ∧
    (execX86Prog keccakChiMpcAvx2Prog 0 s₁).1.ymm .ymm1 = Vec256.zero ∧
    (execX86Prog keccakChiMpcAvx2Prog 0 s₁).1.ymm .ymm2 = Vec256.zero ∧
    (execX86Prog keccakChiMpcAvx2Prog 0 s₁).1.ymm .ymm3 = Vec256.zero ∧
    (execX86Prog keccakChiMpcAvx2Prog 0 s₁).1.ymm .ymm4 = Vec256.zero ∧
    (execX86Prog keccakChiMpcAvx2Prog 0 s₁).1.ymm .ymm5 = Vec256.zero ∧
    (execX86Prog keccakChiMpcAvx2Prog 0 s₁).1.ymm .ymm6 = Vec256.zero ∧
    (execX86Prog keccakChiMpcAvx2Prog 0 s₁).1.ymm .ymm7 = Vec256.zero ∧
    (execX86Prog keccakChiMpcAvx2Prog 0 s₁).1.ymm .ymm8 = Vec256.zero ∧
    (execX86Prog keccakChiMpcAvx2Prog 0 s₁).1.ymm .ymm9 = Vec256.zero ∧
    (execX86Prog keccakChiMpcAvx2Prog 0 s₁).1.ymm .ymm10 = Vec256.zero ∧
    (execX86Prog keccakChiMpcAvx2Prog 0 s₁).1.ymm .ymm11 = Vec256.zero := by
  have hChk : (checkX86Prog true sysvPtrArgs4Taint keccakChiMpcAvx2Prog).isSome = true := rfl
  rcases hOpt : checkX86Prog true sysvPtrArgs4Taint keccakChiMpcAvx2Prog with _ | τOut
  · simp [hOpt] at hChk
  · obtain ⟨hTrace, hLowOut⟩ :=
      x86_ct_checker_sound (fun _ => .sec) true (fun _ _ => rfl)
        keccakChiMpcAvx2Prog sysvPtrArgs4Taint τOut 0 hOpt s₁ s₂ hLow
    have hClean : τOut.upperYmmClean = true := by
      have : (checkX86Prog true sysvPtrArgs4Taint keccakChiMpcAvx2Prog).map
          (fun t => t.upperYmmClean) = some true := rfl
      rw [hOpt] at this; exact Option.some.inj this
    exact ⟨hTrace, hLowOut.2.2.2.2.2.2.2.2.2 hClean, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Exact 39-instruction `qsag_asm_keccak_sha3_neon` program (`aarch64_kernels.s:32-74`). -/
def keccakSha3NeonProg : List ArmStmt :=
  [ .instr (.ldrQ .v0 .x1 0#64)
  , .instr (.ldrQ .v1 .x1 16#64)
  , .instr (.ldrQ .v2 .x1 32#64)
  , .instr (.ldrQ .v3 .x1 48#64)
  , .instr (.ldrQ .v4 .x1 64#64)
  , .instr (.ldrQ .v5 .x2 0#64)
  , .instr (.ldrQ .v6 .x2 16#64)
  , .instr (.ldrQ .v7 .x2 32#64)
  , .instr (.eorV16b .v0 .v0 .v5)
  , .instr (.eorV16b .v1 .v1 .v6)
  , .instr (.eorV16b .v2 .v2 .v7)
  , .instr (.ldrQ .v5 .x2 48#64)
  , .instr (.ldrQ .v6 .x2 64#64)
  , .instr (.eorV16b .v3 .v3 .v5)
  , .instr (.eorV16b .v4 .v4 .v6)
  , .instr (.bcaxV16b .v16 .v0 .v2 .v1)
  , .instr (.bcaxV16b .v17 .v1 .v3 .v2)
  , .instr (.bcaxV16b .v18 .v2 .v4 .v3)
  , .instr (.bcaxV16b .v19 .v3 .v0 .v4)
  , .instr (.bcaxV16b .v20 .v4 .v1 .v0)
  , .instr (.strQ .v16 .x0 0#64)
  , .instr (.strQ .v17 .x0 16#64)
  , .instr (.strQ .v18 .x0 32#64)
  , .instr (.strQ .v19 .x0 48#64)
  , .instr (.strQ .v20 .x0 64#64)
  , .instr (.eorV16b .v0 .v0 .v0)
  , .instr (.eorV16b .v1 .v1 .v1)
  , .instr (.eorV16b .v2 .v2 .v2)
  , .instr (.eorV16b .v3 .v3 .v3)
  , .instr (.eorV16b .v4 .v4 .v4)
  , .instr (.eorV16b .v5 .v5 .v5)
  , .instr (.eorV16b .v6 .v6 .v6)
  , .instr (.eorV16b .v7 .v7 .v7)
  , .instr (.eorV16b .v16 .v16 .v16)
  , .instr (.eorV16b .v17 .v17 .v17)
  , .instr (.eorV16b .v18 .v18 .v18)
  , .instr (.eorV16b .v19 .v19 .v19)
  , .instr (.eorV16b .v20 .v20 .v20)
  , .ret ]

theorem bcax_eq_keccakChiLane (a0 a1 a2 : Vec128) :
    Vec128.bcax a0 a2 a1 = ⟨keccakChiLane a0.lo a1.lo a2.lo, keccakChiLane a0.hi a1.hi a2.hi⟩ := by
  simp only [Vec128.bcax, keccakChiLane]
  congr 1 <;> rw [BitVec.and_comm]

theorem keccakSha3Neon_constant_time
    (s₁ s₂ : ArmState)
    (hLow : ArmLowEq (fun _ => .sec) aapcsPtrArgs3Taint s₁ s₂) :
    (execArmProg keccakSha3NeonProg 0 s₁).2 = (execArmProg keccakSha3NeonProg 0 s₂).2 ∧
    (execArmProg keccakSha3NeonProg 0 s₁).1.neon .v0 = Vec128.zero ∧
    (execArmProg keccakSha3NeonProg 0 s₁).1.neon .v1 = Vec128.zero ∧
    (execArmProg keccakSha3NeonProg 0 s₁).1.neon .v2 = Vec128.zero ∧
    (execArmProg keccakSha3NeonProg 0 s₁).1.neon .v3 = Vec128.zero ∧
    (execArmProg keccakSha3NeonProg 0 s₁).1.neon .v4 = Vec128.zero ∧
    (execArmProg keccakSha3NeonProg 0 s₁).1.neon .v5 = Vec128.zero ∧
    (execArmProg keccakSha3NeonProg 0 s₁).1.neon .v6 = Vec128.zero ∧
    (execArmProg keccakSha3NeonProg 0 s₁).1.neon .v7 = Vec128.zero ∧
    (execArmProg keccakSha3NeonProg 0 s₁).1.neon .v16 = Vec128.zero ∧
    (execArmProg keccakSha3NeonProg 0 s₁).1.neon .v17 = Vec128.zero ∧
    (execArmProg keccakSha3NeonProg 0 s₁).1.neon .v18 = Vec128.zero ∧
    (execArmProg keccakSha3NeonProg 0 s₁).1.neon .v19 = Vec128.zero ∧
    (execArmProg keccakSha3NeonProg 0 s₁).1.neon .v20 = Vec128.zero := by
  have hChk : (checkArmProg true aapcsPtrArgs3Taint keccakSha3NeonProg).isSome = true := rfl
  rcases hOpt : checkArmProg true aapcsPtrArgs3Taint keccakSha3NeonProg with _ | τOut
  · simp [hOpt] at hChk
  · obtain ⟨hTrace, _⟩ :=
      arm_ct_checker_sound (fun _ => .sec) true (fun _ _ => rfl)
        keccakSha3NeonProg aapcsPtrArgs3Taint τOut 0 hOpt s₁ s₂ hLow
    exact ⟨hTrace, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ### 7.2 `gf256_shamir_mul_gfni`: Wiedemann `𝒯₃ ↔ GFNI` Field Isomorphism & 32-Lane SIMD -/

def gfniTowerToPolyMat : BitVec 64 := 0x71500A8A86BE78CE#64
def gfniPolyToTowerMat : BitVec 64 := 0xA1E4F8E072A2700C#64

def gfniPhi (x : BitVec 8) : BitVec 8 :=
  gfniAffineByte gfniTowerToPolyMat x 0#8

def gfniPhiInv (y : BitVec 8) : BitVec 8 :=
  gfniAffineByte gfniPolyToTowerMat y 0#8

@[expose]
def gfniT3MulByte (a b : BitVec 8) : BitVec 8 :=
  gfniPhiInv (gfniPolyMul (gfniPhi a) (gfniPhi b))

private theorem getElem_ite_zero {n : Nat} (b : Bool) (c : BitVec n) (i : Nat) (hi : i < n) :
    (if b then c else 0#n)[i] = (b && c[i]) := by
  cases b <;> simp

private theorem ite_xor_zero {n : Nat} (p q : Bool) (c : BitVec n) :
    (if xor p q then c else 0#n) = (if p then c else 0#n) ^^^ (if q then c else 0#n) := by
  cases p <;> cases q <;> simp

private theorem bv_xor4 {n : Nat} (a b c d : BitVec n) :
    (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_xor]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> cases d.getLsbD i <;> rfl

private theorem bv_xor_group4 {n : Nat} (a0 b0 a1 b1 a2 b2 a3 b3 : BitVec n) :
    (a0 ^^^ b0) ^^^ (a1 ^^^ b1) ^^^ (a2 ^^^ b2) ^^^ (a3 ^^^ b3) =
    (a0 ^^^ a1 ^^^ a2 ^^^ a3) ^^^ (b0 ^^^ b1 ^^^ b2 ^^^ b3) := by
  rw [bv_xor4 a0 b0 a1 b1, bv_xor4 (a0 ^^^ a1) (b0 ^^^ b1) a2 b2,
      bv_xor4 (a0 ^^^ a1 ^^^ a2) (b0 ^^^ b1 ^^^ b2) a3 b3]

private theorem bv_xor_group8 {n : Nat}
    (a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7 : BitVec n) :
    (a0 ^^^ b0) ^^^ (a1 ^^^ b1) ^^^ (a2 ^^^ b2) ^^^ (a3 ^^^ b3) ^^^
    (a4 ^^^ b4) ^^^ (a5 ^^^ b5) ^^^ (a6 ^^^ b6) ^^^ (a7 ^^^ b7) =
    (a0 ^^^ a1 ^^^ a2 ^^^ a3 ^^^ a4 ^^^ a5 ^^^ a6 ^^^ a7) ^^^
    (b0 ^^^ b1 ^^^ b2 ^^^ b3 ^^^ b4 ^^^ b5 ^^^ b6 ^^^ b7) := by
  rw [bv_xor_group4 a0 b0 a1 b1 a2 b2 a3 b3,
      bv_xor4 _ _ a4 b4, bv_xor4 _ _ a5 b5, bv_xor4 _ _ a6 b6, bv_xor4 _ _ a7 b7]

private theorem bv_zext_xor {m n : Nat} (u v : BitVec m) :
    (u ^^^ v).zeroExtend n = u.zeroExtend n ^^^ v.zeroExtend n := by
  ext i hi; simp

private theorem bv_trunc_xor {m n : Nat} (u v : BitVec m) :
    (u ^^^ v).truncate n = u.truncate n ^^^ v.truncate n :=
  bv_zext_xor u v

private theorem bv_shl_xor {n : Nat} (u v : BitVec n) (s : Nat) :
    (u ^^^ v) <<< s = (u <<< s) ^^^ (v <<< s) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_xor, hi, decide_true, Bool.true_and]
  cases decide (i < s) <;> cases u.getLsbD (i - s) <;> cases v.getLsbD (i - s) <;> rfl

private theorem bv_shr_xor {n : Nat} (u v : BitVec n) (s : Nat) :
    (u ^^^ v) >>> s = (u >>> s) ^^^ (v >>> s) := by
  ext i hi; simp

private theorem basis8_decomp (x : BitVec 8) :
    x =
      (if x.getLsbD 0 then 0x01#8 else 0#8) ^^^
      (if x.getLsbD 1 then 0x02#8 else 0#8) ^^^
      (if x.getLsbD 2 then 0x04#8 else 0#8) ^^^
      (if x.getLsbD 3 then 0x08#8 else 0#8) ^^^
      (if x.getLsbD 4 then 0x10#8 else 0#8) ^^^
      (if x.getLsbD 5 then 0x20#8 else 0#8) ^^^
      (if x.getLsbD 6 then 0x40#8 else 0#8) ^^^
      (if x.getLsbD 7 then 0x80#8 else 0#8) := by
  have h : ∀ i : Fin (2 ^ 8),
      BitVec.ofFin i =
        (if (BitVec.ofFin i).getLsbD 0 then 0x01#8 else 0#8) ^^^
        (if (BitVec.ofFin i).getLsbD 1 then 0x02#8 else 0#8) ^^^
        (if (BitVec.ofFin i).getLsbD 2 then 0x04#8 else 0#8) ^^^
        (if (BitVec.ofFin i).getLsbD 3 then 0x08#8 else 0#8) ^^^
        (if (BitVec.ofFin i).getLsbD 4 then 0x10#8 else 0#8) ^^^
        (if (BitVec.ofFin i).getLsbD 5 then 0x20#8 else 0#8) ^^^
        (if (BitVec.ofFin i).getLsbD 6 then 0x40#8 else 0#8) ^^^
        (if (BitVec.ofFin i).getLsbD 7 then 0x80#8 else 0#8) := by
    decide +kernel
  exact h x.toFin

private theorem f2_linear8_ite (f : BitVec 8 → BitVec 8) (hf0 : f 0#8 = 0#8)
    (b : Bool) (c : BitVec 8) :
    f (if b then c else 0#8) = (if b then f c else 0#8) := by
  cases b <;> simp [hf0]

theorem eq_of_f2_linear8 (f g : BitVec 8 → BitVec 8)
    (hf0 : f 0#8 = 0#8) (hg0 : g 0#8 = 0#8)
    (hfx : ∀ x y, f (x ^^^ y) = f x ^^^ f y)
    (hgx : ∀ x y, g (x ^^^ y) = g x ^^^ g y)
    (hb0 : f 0x01#8 = g 0x01#8) (hb1 : f 0x02#8 = g 0x02#8)
    (hb2 : f 0x04#8 = g 0x04#8) (hb3 : f 0x08#8 = g 0x08#8)
    (hb4 : f 0x10#8 = g 0x10#8) (hb5 : f 0x20#8 = g 0x20#8)
    (hb6 : f 0x40#8 = g 0x40#8) (hb7 : f 0x80#8 = g 0x80#8)
    (x : BitVec 8) : f x = g x := by
  conv => lhs; rw [basis8_decomp x]
  conv => rhs; rw [basis8_decomp x]
  simp only [hfx, hgx, f2_linear8_ite f hf0, f2_linear8_ite g hg0,
             hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7]

private theorem bool_xor_group8
    (a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7 : Bool) :
    xor (xor (xor (xor a0 b0) (xor a1 b1)) (xor (xor a2 b2) (xor a3 b3)))
        (xor (xor (xor a4 b4) (xor a5 b5)) (xor (xor a6 b6) (xor a7 b7))) =
    xor (xor (xor (xor a0 a1) (xor a2 a3)) (xor (xor a4 a5) (xor a6 a7)))
        (xor (xor (xor b0 b1) (xor b2 b3)) (xor (xor b4 b5) (xor b6 b7))) := by
  have g2 (u0 v0 u1 v1 : Bool) : xor (xor u0 v0) (xor u1 v1) = xor (xor u0 u1) (xor v0 v1) := by
    cases u0 <;> cases v0 <;> cases u1 <;> cases v1 <;> rfl
  rw [g2 a0 b0 a1 b1, g2 a2 b2 a3 b3, g2 a4 b4 a5 b5, g2 a6 b6 a7 b7,
      g2 (xor a0 a1) (xor b0 b1) (xor a2 a3) (xor b2 b3),
      g2 (xor a4 a5) (xor b4 b5) (xor a6 a7) (xor b6 b7),
      g2 (xor (xor a0 a1) (xor a2 a3)) (xor (xor b0 b1) (xor b2 b3))]

private theorem parity8_and_xor (x y m : BitVec 8) :
    parity8 ((x ^^^ y) &&& m) = xor (parity8 (x &&& m)) (parity8 (y &&& m)) := by
  have bit_lem (a b c : Bool) : and (xor a b) c = xor (and a c) (and b c) := by
    cases a <;> cases b <;> cases c <;> rfl
  dsimp only [parity8]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor, bit_lem]
  exact bool_xor_group8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

private theorem packBits8_xor (f g : Fin 8 → Bool) :
    packBits8 (fun i => xor (f i) (g i)) = packBits8 f ^^^ packBits8 g := by
  simp only [packBits8, ite_xor_zero, bv_xor_group8]

theorem gfniAffine0_xor (mat : BitVec 64) (x y : BitVec 8) :
    gfniAffineByte mat (x ^^^ y) 0#8 =
      gfniAffineByte mat x 0#8 ^^^ gfniAffineByte mat y 0#8 := by
  simp only [gfniAffineByte, BitVec.getLsbD_zero, Bool.xor_false]
  rw [← packBits8_xor]
  congr 1; ext i; exact parity8_and_xor x y (extractByte64 mat (7 - i.val))

theorem gfniXtime_xor (x y : BitVec 8) :
    gfniXtime (x ^^^ y) = gfniXtime x ^^^ gfniXtime y := by
  simp only [gfniXtime, bv_shl_xor, BitVec.getLsbD_xor, ite_xor_zero]
  exact bv_xor4 _ _ _ _

theorem gfniPolyMul_xor_left (x y b : BitVec 8) :
    gfniPolyMul (x ^^^ y) b = gfniPolyMul x b ^^^ gfniPolyMul y b := by
  have ite_bv_xor (p : Bool) (u v : BitVec 8) :
      (if p then u ^^^ v else 0#8) = (if p then u else 0#8) ^^^ (if p then v else 0#8) := by
    cases p <;> simp
  simp only [gfniPolyMul, gfniXtime_xor, ite_bv_xor, bv_xor_group8]

theorem gfniPolyMul_xor_right (a x y : BitVec 8) :
    gfniPolyMul a (x ^^^ y) = gfniPolyMul a x ^^^ gfniPolyMul a y := by
  simp only [gfniPolyMul, BitVec.getLsbD_xor, ite_xor_zero, bv_xor_group8]

private theorem gf4Mul_xor_left (x y b : BitVec 2) :
    gf4Mul (x ^^^ y) b = gf4Mul x b ^^^ gf4Mul y b := by
  simp only [gf4Mul, BitVec.getLsbD_xor]
  generalize x.getLsbD 0 = x0; generalize x.getLsbD 1 = x1
  generalize y.getLsbD 0 = y0; generalize y.getLsbD 1 = y1
  generalize b.getLsbD 0 = b0; generalize b.getLsbD 1 = b1
  cases x0 <;> cases x1 <;> cases y0 <;> cases y1 <;> cases b0 <;> cases b1 <;> rfl

private theorem gf4Mul_xor_right (a x y : BitVec 2) :
    gf4Mul a (x ^^^ y) = gf4Mul a x ^^^ gf4Mul a y := by
  simp only [gf4Mul, BitVec.getLsbD_xor]
  generalize a.getLsbD 0 = a0; generalize a.getLsbD 1 = a1
  generalize x.getLsbD 0 = x0; generalize x.getLsbD 1 = x1
  generalize y.getLsbD 0 = y0; generalize y.getLsbD 1 = y1
  cases a0 <;> cases a1 <;> cases x0 <;> cases x1 <;> cases y0 <;> cases y1 <;> rfl

private theorem gf4MulAlpha_xor (x y : BitVec 2) :
    gf4MulAlpha (x ^^^ y) = gf4MulAlpha x ^^^ gf4MulAlpha y := by
  simp only [gf4MulAlpha, BitVec.getLsbD_xor]
  generalize x.getLsbD 0 = x0; generalize x.getLsbD 1 = x1
  generalize y.getLsbD 0 = y0; generalize y.getLsbD 1 = y1
  cases x0 <;> cases x1 <;> cases y0 <;> cases y1 <;> rfl

private theorem karatsuba_expanded_xor {n : Nat}
    (p0x p0y p1x p1y pm0x pm0y pm1x pm1y sp1x sp1y : BitVec n) (s : Nat) :
    (p0x ^^^ p0y) ^^^ (p1x ^^^ p1y) ^^^
      ((((pm0x ^^^ pm0y) ^^^ (pm1x ^^^ pm1y)) ^^^
        (p0x ^^^ p0y) ^^^ (p1x ^^^ p1y) ^^^ (sp1x ^^^ sp1y)) <<< s) =
    (p0x ^^^ p1x ^^^ (((pm0x ^^^ pm1x) ^^^ p0x ^^^ p1x ^^^ sp1x) <<< s)) ^^^
    (p0y ^^^ p1y ^^^ (((pm0y ^^^ pm1y) ^^^ p0y ^^^ p1y ^^^ sp1y) <<< s)) := by
  rw [bv_xor4 pm0x pm0y pm1x pm1y,
      bv_xor_group4 (pm0x ^^^ pm1x) (pm0y ^^^ pm1y) p0x p0y p1x p1y sp1x sp1y,
      bv_shl_xor,
      bv_xor4 p0x p0y p1x p1y,
      bv_xor4 (p0x ^^^ p1x) (p0y ^^^ p1y)]

private theorem mulAlpha_expanded_xor {n : Nat}
    (ax ay bx by_ cx cy : BitVec n) (s : Nat) :
    (ax ^^^ ay) ^^^ (((bx ^^^ by_) ^^^ (cx ^^^ cy)) <<< s) =
    (ax ^^^ ((bx ^^^ cx) <<< s)) ^^^ (ay ^^^ ((by_ ^^^ cy) <<< s)) := by
  rw [bv_xor4 bx by_ cx cy, bv_shl_xor, bv_xor4 ax ay]

private theorem gf16Mul_xor_left (x y b : BitVec 4) :
    gf16Mul (x ^^^ y) b = gf16Mul x b ^^^ gf16Mul y b := by
  dsimp only [gf16Mul]
  simp only [bv_trunc_xor, bv_shr_xor, gf4Mul_xor_left, gf4MulAlpha_xor]
  exact karatsuba_expanded_xor _ _ _ _ _ _ _ _ _ _ 2

private theorem gf16Mul_xor_right (a x y : BitVec 4) :
    gf16Mul a (x ^^^ y) = gf16Mul a x ^^^ gf16Mul a y := by
  dsimp only [gf16Mul]
  simp only [bv_trunc_xor, bv_shr_xor, gf4Mul_xor_right, gf4MulAlpha_xor]
  exact karatsuba_expanded_xor _ _ _ _ _ _ _ _ _ _ 2

private theorem gf16MulAlpha_xor (x y : BitVec 4) :
    gf16MulAlpha (x ^^^ y) = gf16MulAlpha x ^^^ gf16MulAlpha y := by
  dsimp only [gf16MulAlpha]
  simp only [bv_trunc_xor, bv_shr_xor, gf4MulAlpha_xor]
  exact mulAlpha_expanded_xor _ _ _ _ _ _ 2

theorem towerGf256Mul_xor_left (x y b : BitVec 8) :
    towerGf256Mul (x ^^^ y) b = towerGf256Mul x b ^^^ towerGf256Mul y b := by
  dsimp only [towerGf256Mul]
  simp only [bv_trunc_xor, bv_shr_xor, gf16Mul_xor_left, gf16MulAlpha_xor]
  exact karatsuba_expanded_xor _ _ _ _ _ _ _ _ _ _ 4

theorem towerGf256Mul_xor_right (a x y : BitVec 8) :
    towerGf256Mul a (x ^^^ y) = towerGf256Mul a x ^^^ towerGf256Mul a y := by
  dsimp only [towerGf256Mul]
  simp only [bv_trunc_xor, bv_shr_xor, gf16Mul_xor_right, gf16MulAlpha_xor]
  exact karatsuba_expanded_xor _ _ _ _ _ _ _ _ _ _ 4

theorem gfni_phi_left_inv (x : BitVec 8) : gfniPhiInv (gfniPhi x) = x := by
  apply eq_of_f2_linear8 (fun z => gfniPhiInv (gfniPhi z)) id rfl rfl
  · intro u v; simp only [gfniPhi, gfniPhiInv, gfniAffine0_xor]
  · intro _ _; rfl
  all_goals rfl

theorem gfni_phi_right_inv (y : BitVec 8) : gfniPhi (gfniPhiInv y) = y := by
  apply eq_of_f2_linear8 (fun z => gfniPhi (gfniPhiInv z)) id rfl rfl
  · intro u v; simp only [gfniPhi, gfniPhiInv, gfniAffine0_xor]
  · intro _ _; rfl
  all_goals rfl

/-- **Exact Algebraic Field Isomorphism (`𝒯₃ ≃ 𝔽₂[z]/(z⁸ + z⁴ + z³ + z + 1)`)**:
    For **all** 65,536 byte pairs `(a, b) : BitVec 8 × BitVec 8`, conjugating Intel `VGF2P8MULB`
    by `VGF2P8AFFINEQB` matrices `0x71500A8A86BE78CE` and `0xA1E4F8E072A2700C` is bit-identical
    to Wiedemann tower `𝒯₃` multiplication (`towerGf256Mul`), proved with `0 native_decide`! -/
theorem gfni_isomorphism_homomorphic (a b : BitVec 8) :
    gfniT3MulByte a b = towerGf256Mul a b := by
  have hT3ZeroL : towerGf256Mul 0#8 b = 0#8 := by
    have h := towerGf256Mul_xor_left 0#8 0#8 b
    simpa using h
  have hGfniZeroL : gfniT3MulByte 0#8 b = 0#8 := by
    have h0 : gfniPhi 0#8 = 0#8 := rfl
    have hM0 : gfniPolyMul 0#8 (gfniPhi b) = 0#8 := by
      have hm := gfniPolyMul_xor_left 0#8 0#8 (gfniPhi b)
      simpa using hm
    simp [gfniT3MulByte, h0, hM0, show gfniPhiInv 0#8 = 0#8 from rfl]
  apply eq_of_f2_linear8 (fun x => gfniT3MulByte x b) (fun x => towerGf256Mul x b)
    hGfniZeroL hT3ZeroL
  · intro x y
    simp only [gfniT3MulByte, gfniPhi, gfniPhiInv, gfniAffine0_xor, gfniPolyMul_xor_left]
  · intro x y; exact towerGf256Mul_xor_left x y b
  all_goals
    apply eq_of_f2_linear8 _ _ rfl rfl
      (fun u v => by
        simp only [gfniT3MulByte, gfniPhi, gfniPhiInv, gfniAffine0_xor, gfniPolyMul_xor_right])
      (fun u v => towerGf256Mul_xor_right _ u v) <;> rfl

/-- Exact `qsag_asm_gf256_shamir_mul_gfni` program (`x86_64_asm.rs:550-576`) for `blocks` × 32B.
    `.pubLoop blocks` models the lib.rs dispatch guard `blocks >= 1`. -/
def gf256ShamirMulGfniProg (blocks : Nat) : List X86Stmt :=
  [ .instr (.movImm64 .rax gfniTowerToPolyMat)
  , .instr (.vpbroadcastqGpr .ymm14 .rax)
  , .instr (.movImm64 .rax gfniPolyToTowerMat)
  , .instr (.vpbroadcastqGpr .ymm15 .rax)
  , .pubLoop blocks
      [ .vmovdquLoad .ymm0 .rsi 0#64
      , .vmovdquLoad .ymm1 .rdx 0#64
      , .vgf2p8affineqb0 .ymm0 .ymm0 .ymm14
      , .vgf2p8affineqb0 .ymm1 .ymm1 .ymm14
      , .vgf2p8mulb .ymm2 .ymm0 .ymm1
      , .vgf2p8affineqb0 .ymm2 .ymm2 .ymm15
      , .vmovdquStore .rdi 0#64 .ymm2
      , .addImm64 .rsi 32#64
      , .addImm64 .rdx 32#64
      , .addImm64 .rdi 32#64 ]
  , .instr (.vpxor .ymm0 .ymm0 .ymm0)
  , .instr (.vpxor .ymm1 .ymm1 .ymm1)
  , .instr (.vpxor .ymm2 .ymm2 .ymm2)
  , .instr (.vpxor .ymm14 .ymm14 .ymm14)
  , .instr (.vpxor .ymm15 .ymm15 .ymm15)
  , .instr .vzeroupper
  , .ret ]

private theorem x86_taint_setYmm_gpr (τ : X86TaintState) (y : YmmReg) (l : SecLabel) (r : X86Gpr) :
    (τ.setYmm y l).gpr r = τ.gpr r := rfl

private theorem x86_taint_setGpr_gpr (τ : X86TaintState) (r q : X86Gpr) (l : SecLabel) :
    (τ.setGpr r l).gpr q = if q == r then l else τ.gpr q := rfl

private theorem checkX86Block_cons {secHeap : Bool} {τ τ1 : X86TaintState}
    {ins : X86Instr} {rest : List X86Instr}
    (h1 : checkX86Instr secHeap τ ins = some τ1) :
    checkX86Block secHeap τ (ins :: rest) = checkX86Block secHeap τ1 rest := by
  simp [checkX86Block, h1]

theorem checkX86Loop_gfni_invariant (blocks : Nat) (τ : X86TaintState)
    (hRsi : τ.gpr .rsi = .pub) (hRdx : τ.gpr .rdx = .pub) (hRdi : τ.gpr .rdi = .pub) :
    ∃ τ', checkX86Loop true blocks τ
      [ .vmovdquLoad .ymm0 .rsi 0#64
      , .vmovdquLoad .ymm1 .rdx 0#64
      , .vgf2p8affineqb0 .ymm0 .ymm0 .ymm14
      , .vgf2p8affineqb0 .ymm1 .ymm1 .ymm14
      , .vgf2p8mulb .ymm2 .ymm0 .ymm1
      , .vgf2p8affineqb0 .ymm2 .ymm2 .ymm15
      , .vmovdquStore .rdi 0#64 .ymm2
      , .addImm64 .rsi 32#64
      , .addImm64 .rdx 32#64
      , .addImm64 .rdi 32#64 ] = some τ' := by
  induction blocks generalizing τ with
  | zero => exact ⟨τ, rfl⟩
  | succ n ih =>
    let τ1 := τ.setYmm .ymm0 .sec
    let τ2 := τ1.setYmm .ymm1 .sec
    let τ3 := τ2.setYmm .ymm0 ((τ2.ymm .ymm0).join (τ2.ymm .ymm14))
    let τ4 := τ3.setYmm .ymm1 ((τ3.ymm .ymm1).join (τ3.ymm .ymm14))
    let τ5 := τ4.setYmm .ymm2 ((τ4.ymm .ymm0).join (τ4.ymm .ymm1))
    let τ6 := τ5.setYmm .ymm2 ((τ5.ymm .ymm2).join (τ5.ymm .ymm15))
    let τ7 : X86TaintState := { (τ6.setGpr .rsi (τ6.gpr .rsi)) with cf := τ6.gpr .rsi, of := τ6.gpr .rsi, zf := τ6.gpr .rsi }
    let τ8 : X86TaintState := { (τ7.setGpr .rdx (τ7.gpr .rdx)) with cf := τ7.gpr .rdx, of := τ7.gpr .rdx, zf := τ7.gpr .rdx }
    let τ9 : X86TaintState := { (τ8.setGpr .rdi (τ8.gpr .rdi)) with cf := τ8.gpr .rdi, of := τ8.gpr .rdi, zf := τ8.gpr .rdi }
    have s1 : checkX86Instr true τ (.vmovdquLoad .ymm0 .rsi 0#64) = some τ1 := by
      dsimp only [checkX86Instr]; rw [hRsi]; rfl
    have s2 : checkX86Instr true τ1 (.vmovdquLoad .ymm1 .rdx 0#64) = some τ2 := by
      dsimp only [checkX86Instr]; change (if τ.gpr .rdx == .pub then some τ2 else none) = some τ2
      rw [hRdx]; rfl
    have s7 : checkX86Instr true τ6 (.vmovdquStore .rdi 0#64 .ymm2) = some τ6 := by
      dsimp only [checkX86Instr]
      change (if (τ.gpr .rdi == .pub && (true || τ6.ymm .ymm2 == .pub)) then some τ6 else none) = some τ6
      rw [hRdi]; rfl
    have hBlk : checkX86Block true τ
        [ .vmovdquLoad .ymm0 .rsi 0#64
        , .vmovdquLoad .ymm1 .rdx 0#64
        , .vgf2p8affineqb0 .ymm0 .ymm0 .ymm14
        , .vgf2p8affineqb0 .ymm1 .ymm1 .ymm14
        , .vgf2p8mulb .ymm2 .ymm0 .ymm1
        , .vgf2p8affineqb0 .ymm2 .ymm2 .ymm15
        , .vmovdquStore .rdi 0#64 .ymm2
        , .addImm64 .rsi 32#64
        , .addImm64 .rdx 32#64
        , .addImm64 .rdi 32#64 ] = some τ9 := by
      rw [checkX86Block_cons s1, checkX86Block_cons s2,
          checkX86Block_cons (rfl : checkX86Instr true τ2 _ = some τ3),
          checkX86Block_cons (rfl : checkX86Instr true τ3 _ = some τ4),
          checkX86Block_cons (rfl : checkX86Instr true τ4 _ = some τ5),
          checkX86Block_cons (rfl : checkX86Instr true τ5 _ = some τ6),
          checkX86Block_cons s7,
          checkX86Block_cons (rfl : checkX86Instr true τ6 _ = some τ7),
          checkX86Block_cons (rfl : checkX86Instr true τ7 _ = some τ8),
          checkX86Block_cons (rfl : checkX86Instr true τ8 _ = some τ9)]
      rfl
    dsimp only [checkX86Loop]
    rw [hBlk]
    exact ih τ9 hRsi hRdx hRdi

/-- **Timing-Noninterference of `qsag_asm_gf256_shamir_mul_gfni` for ALL `blocks : Nat`**: -/
theorem gf256ShamirMulGfni_constant_time
    (blocks : Nat) (s₁ s₂ : X86State)
    (hLow : X86LowEq (fun _ => .sec) sysvPtrArgs4Taint s₁ s₂) :
    (execX86Prog (gf256ShamirMulGfniProg blocks) 0 s₁).2 =
      (execX86Prog (gf256ShamirMulGfniProg blocks) 0 s₂).2 := by
  let τPre := ((((sysvPtrArgs4Taint.setGpr .rax .pub).setYmm .ymm14 .pub).setGpr
    .rax .pub).setYmm .ymm15 .pub)
  obtain ⟨τLoop, hLoop⟩ := checkX86Loop_gfni_invariant blocks τPre rfl rfl rfl
  have hSome : (checkX86Prog true sysvPtrArgs4Taint (gf256ShamirMulGfniProg blocks)).isSome = true := by
    dsimp only [gf256ShamirMulGfniProg, checkX86Prog, checkX86Instr]
    change (match checkX86Loop true blocks τPre _ with
      | none => none
      | some τ1 => _).isSome = true
    rw [hLoop]
    rfl
  rcases hOpt : checkX86Prog true sysvPtrArgs4Taint (gf256ShamirMulGfniProg blocks) with _ | τEnd
  · simp [hOpt] at hSome
  · exact (x86_ct_checker_sound (fun _ => .sec) true (fun _ _ => rfl)
      (gf256ShamirMulGfniProg blocks) sysvPtrArgs4Taint τEnd 0 hOpt s₁ s₂ hLow).1

private theorem gfni_word64_correct (wa wb : BitVec 64) (r : Fin 8) :
    let aFwd := packBytes64 (fun i => gfniAffineByte gfniTowerToPolyMat (extractByte64 wa i.val) 0#8)
    let bFwd := packBytes64 (fun i => gfniAffineByte gfniTowerToPolyMat (extractByte64 wb i.val) 0#8)
    let prod := zipBytes64 gfniPolyMul aFwd bFwd
    let res  := packBytes64 (fun i => gfniAffineByte gfniPolyToTowerMat (extractByte64 prod i.val) 0#8)
    extractByte64 res r.val = towerGf256Mul (extractByte64 wa r.val) (extractByte64 wb r.val) := by
  dsimp only [zipBytes64]
  rw [extractByte64_packBytes64, extractByte64_packBytes64,
      extractByte64_packBytes64, extractByte64_packBytes64]
  exact gfni_isomorphism_homomorphic _ _

/-- **32-Lane SIMD Functional Correctness of `vgf2p8affineqb + vgf2p8mulb` Block**:
    Every byte lane `idx : Fin 32` of the SIMD GFNI pipeline equals `towerGf256Mul (a[idx]) (b[idx])`. -/
theorem gf256ShamirMulGfni_32lane_correct (va vb : Vec256) (idx : Fin 32) :
    let mFwd := Vec256.broadcastQ gfniTowerToPolyMat
    let mInv := Vec256.broadcastQ gfniPolyToTowerMat
    let res := Vec256.gfniAffine0
      (Vec256.gfniMul (Vec256.gfniAffine0 va mFwd) (Vec256.gfniAffine0 vb mFwd)) mInv
    res.getByte idx = towerGf256Mul (va.getByte idx) (vb.getByte idx) := by
  rcases idx with ⟨k, hk⟩
  have hq : k / 8 = 0 ∨ k / 8 = 1 ∨ k / 8 = 2 ∨ k / 8 = 3 := by omega
  let rFin : Fin 8 := ⟨k % 8, by omega⟩
  dsimp only [Vec256.getByte, Vec256.gfniAffine0, Vec256.gfniMul, Vec256.broadcastQ]
  rcases hq with h0 | h1 | h2 | h3
  · simp only [h0, beq_self_eq_true, ↓reduceIte]
    exact gfni_word64_correct va.w0 vb.w0 rFin
  · simp only [h1]; split <;> try contradiction
    split <;> try contradiction
    exact gfni_word64_correct va.w1 vb.w1 rFin
  · simp only [h2]; split <;> try contradiction
    split <;> try contradiction
    split <;> try contradiction
    exact gfni_word64_correct va.w2 vb.w2 rFin
  · simp only [h3]; split <;> try contradiction
    split <;> try contradiction
    split <;> try contradiction
    exact gfni_word64_correct va.w3 vb.w3 rFin

/-! ### 7.3 `tower128_bdoz_mac_vpclmul`: 2-Lane `VPCLMULQDQ` BDOZ MAC & `0x87` Reduction -/

/-- Exact `qsag_asm_tower128_bdoz_mac_vpclmul` program (`x86_64_asm.rs:881-925`). -/
-- `.pubLoop count` models the lib.rs dispatch guard `count >= 1`.
def tower128BdozVpclmulProg (count : Nat) : List X86Stmt :=
  [ .instr (.vpxor .ymm0 .ymm0 .ymm0)
  , .instr (.vpxor .ymm1 .ymm1 .ymm1)
  , .pubLoop count
      [ .vmovdquLoad .ymm2 .rsi 0#64
      , .vmovdquLoad .ymm3 .rdx 0#64
      , .vpclmulqdq .ymm4 .ymm2 .ymm3 0x00#8
      , .vpclmulqdq .ymm5 .ymm2 .ymm3 0x11#8
      , .vpclmulqdq .ymm6 .ymm2 .ymm3 0x01#8
      , .vpclmulqdq .ymm7 .ymm2 .ymm3 0x10#8
      , .vpxor .ymm6 .ymm6 .ymm7
      , .vpslldq8 .ymm7 .ymm6
      , .vpsrldq8 .ymm6 .ymm6
      , .vpxor .ymm4 .ymm4 .ymm7
      , .vpxor .ymm5 .ymm5 .ymm6
      , .vpxor .ymm0 .ymm0 .ymm4
      , .vpxor .ymm1 .ymm1 .ymm5
      , .addImm64 .rsi 32#64
      , .addImm64 .rdx 32#64 ]
  , .instr (.movImm64 .rax 0x87#64)
  , .instr (.vpbroadcastqGpr .ymm8 .rax)
  , .instr (.vpclmulqdq .ymm4 .ymm1 .ymm8 0x01#8)
  , .instr (.vpslldq8 .ymm5 .ymm4)
  , .instr (.vpsrldq8 .ymm6 .ymm4)
  , .instr (.vpxor .ymm0 .ymm0 .ymm5)
  , .instr (.vpxor .ymm1 .ymm1 .ymm6)
  , .instr (.vpclmulqdq .ymm4 .ymm1 .ymm8 0x00#8)
  , .instr (.vpxor .ymm0 .ymm0 .ymm4)
  , .instr (.vmovdquStore .rdi 0#64 .ymm0)
  , .instr (.vpxor .ymm0 .ymm0 .ymm0)
  , .instr (.vpxor .ymm1 .ymm1 .ymm1)
  , .instr (.vpxor .ymm2 .ymm2 .ymm2)
  , .instr (.vpxor .ymm3 .ymm3 .ymm3)
  , .instr (.vpxor .ymm4 .ymm4 .ymm4)
  , .instr (.vpxor .ymm5 .ymm5 .ymm5)
  , .instr (.vpxor .ymm6 .ymm6 .ymm6)
  , .instr (.vpxor .ymm7 .ymm7 .ymm7)
  , .instr (.vpxor .ymm8 .ymm8 .ymm8)
  , .instr (.xor64 .rax .rax)
  , .instr .vzeroupper
  , .ret ]

theorem checkX86Loop_vpclmul_invariant (count : Nat) (τ : X86TaintState)
    (hRsi : τ.gpr .rsi = .pub) (hRdx : τ.gpr .rdx = .pub) :
    ∃ τ', checkX86Loop true count τ
      [ .vmovdquLoad .ymm2 .rsi 0#64
      , .vmovdquLoad .ymm3 .rdx 0#64
      , .vpclmulqdq .ymm4 .ymm2 .ymm3 0x00#8
      , .vpclmulqdq .ymm5 .ymm2 .ymm3 0x11#8
      , .vpclmulqdq .ymm6 .ymm2 .ymm3 0x01#8
      , .vpclmulqdq .ymm7 .ymm2 .ymm3 0x10#8
      , .vpxor .ymm6 .ymm6 .ymm7
      , .vpslldq8 .ymm7 .ymm6
      , .vpsrldq8 .ymm6 .ymm6
      , .vpxor .ymm4 .ymm4 .ymm7
      , .vpxor .ymm5 .ymm5 .ymm6
      , .vpxor .ymm0 .ymm0 .ymm4
      , .vpxor .ymm1 .ymm1 .ymm5
      , .addImm64 .rsi 32#64
      , .addImm64 .rdx 32#64 ] = some τ' ∧ τ'.gpr .rdi = τ.gpr .rdi := by
  induction count generalizing τ with
  | zero => exact ⟨τ, rfl, rfl⟩
  | succ n ih =>
    let τ1 := τ.setYmm .ymm2 .sec
    let τ2 := τ1.setYmm .ymm3 .sec
    let τ3 := τ2.setYmm .ymm4 ((τ2.ymm .ymm2).join (τ2.ymm .ymm3))
    let τ4 := τ3.setYmm .ymm5 ((τ3.ymm .ymm2).join (τ3.ymm .ymm3))
    let τ5 := τ4.setYmm .ymm6 ((τ4.ymm .ymm2).join (τ4.ymm .ymm3))
    let τ6 := τ5.setYmm .ymm7 ((τ5.ymm .ymm2).join (τ5.ymm .ymm3))
    let τ7 := τ6.setYmm .ymm6 ((τ6.ymm .ymm6).join (τ6.ymm .ymm7))
    let τ8 := τ7.setYmm .ymm7 (τ7.ymm .ymm6)
    let τ9 := τ8.setYmm .ymm6 (τ8.ymm .ymm6)
    let τ10 := τ9.setYmm .ymm4 ((τ9.ymm .ymm4).join (τ9.ymm .ymm7))
    let τ11 := τ10.setYmm .ymm5 ((τ10.ymm .ymm5).join (τ10.ymm .ymm6))
    let τ12 := τ11.setYmm .ymm0 ((τ11.ymm .ymm0).join (τ11.ymm .ymm4))
    let τ13 := τ12.setYmm .ymm1 ((τ12.ymm .ymm1).join (τ12.ymm .ymm5))
    let τ14 : X86TaintState := { (τ13.setGpr .rsi (τ13.gpr .rsi)) with cf := τ13.gpr .rsi, of := τ13.gpr .rsi, zf := τ13.gpr .rsi }
    let τ15 : X86TaintState := { (τ14.setGpr .rdx (τ14.gpr .rdx)) with cf := τ14.gpr .rdx, of := τ14.gpr .rdx, zf := τ14.gpr .rdx }
    have s1 : checkX86Instr true τ (.vmovdquLoad .ymm2 .rsi 0#64) = some τ1 := by
      dsimp only [checkX86Instr]; rw [hRsi]; rfl
    have s2 : checkX86Instr true τ1 (.vmovdquLoad .ymm3 .rdx 0#64) = some τ2 := by
      dsimp only [checkX86Instr]; change (if τ.gpr .rdx == .pub then some τ2 else none) = some τ2
      rw [hRdx]; rfl
    have hBlk : checkX86Block true τ
        [ .vmovdquLoad .ymm2 .rsi 0#64
        , .vmovdquLoad .ymm3 .rdx 0#64
        , .vpclmulqdq .ymm4 .ymm2 .ymm3 0x00#8
        , .vpclmulqdq .ymm5 .ymm2 .ymm3 0x11#8
        , .vpclmulqdq .ymm6 .ymm2 .ymm3 0x01#8
        , .vpclmulqdq .ymm7 .ymm2 .ymm3 0x10#8
        , .vpxor .ymm6 .ymm6 .ymm7
        , .vpslldq8 .ymm7 .ymm6
        , .vpsrldq8 .ymm6 .ymm6
        , .vpxor .ymm4 .ymm4 .ymm7
        , .vpxor .ymm5 .ymm5 .ymm6
        , .vpxor .ymm0 .ymm0 .ymm4
        , .vpxor .ymm1 .ymm1 .ymm5
        , .addImm64 .rsi 32#64
        , .addImm64 .rdx 32#64 ] = some τ15 := by
      rw [checkX86Block_cons s1, checkX86Block_cons s2,
          checkX86Block_cons (rfl : checkX86Instr true τ2 _ = some τ3),
          checkX86Block_cons (rfl : checkX86Instr true τ3 _ = some τ4),
          checkX86Block_cons (rfl : checkX86Instr true τ4 _ = some τ5),
          checkX86Block_cons (rfl : checkX86Instr true τ5 _ = some τ6),
          checkX86Block_cons (rfl : checkX86Instr true τ6 _ = some τ7),
          checkX86Block_cons (rfl : checkX86Instr true τ7 _ = some τ8),
          checkX86Block_cons (rfl : checkX86Instr true τ8 _ = some τ9),
          checkX86Block_cons (rfl : checkX86Instr true τ9 _ = some τ10),
          checkX86Block_cons (rfl : checkX86Instr true τ10 _ = some τ11),
          checkX86Block_cons (rfl : checkX86Instr true τ11 _ = some τ12),
          checkX86Block_cons (rfl : checkX86Instr true τ12 _ = some τ13),
          checkX86Block_cons (rfl : checkX86Instr true τ13 _ = some τ14),
          checkX86Block_cons (rfl : checkX86Instr true τ14 _ = some τ15)]
      rfl
    dsimp only [checkX86Loop]
    rw [hBlk]
    obtain ⟨τ', h1, h2⟩ := ih τ15 hRsi hRdx
    exact ⟨τ', h1, h2⟩

/-- **Timing-Noninterference of `qsag_asm_tower128_bdoz_mac_vpclmul` for ALL `count : Nat`**: -/
theorem tower128BdozVpclmul_constant_time
    (count : Nat) (s₁ s₂ : X86State)
    (hLow : X86LowEq (fun _ => .sec) sysvPtrArgs4Taint s₁ s₂) :
    (execX86Prog (tower128BdozVpclmulProg count) 0 s₁).2 =
      (execX86Prog (tower128BdozVpclmulProg count) 0 s₂).2 := by
  let τPre := (sysvPtrArgs4Taint.setYmm .ymm0 .pub).setYmm .ymm1 .pub
  obtain ⟨τLoop, hLoop, hRdi⟩ := checkX86Loop_vpclmul_invariant count τPre rfl rfl
  have hRdiPub : τLoop.gpr .rdi = .pub := hRdi
  have hSome : (checkX86Prog true sysvPtrArgs4Taint (tower128BdozVpclmulProg count)).isSome = true := by
    dsimp only [tower128BdozVpclmulProg, checkX86Prog, checkX86Instr]
    change (match checkX86Loop true count τPre _ with
      | none => none
      | some τ1 => _).isSome = true
    rw [hLoop]
    simp [X86TaintState.setGpr, X86TaintState.setYmm, hRdiPub]
  rcases hOpt : checkX86Prog true sysvPtrArgs4Taint (tower128BdozVpclmulProg count) with _ | τEnd
  · simp [hOpt] at hSome
  · exact (x86_ct_checker_sound (fun _ => .sec) true (fun _ _ => rfl)
      (tower128BdozVpclmulProg count) sysvPtrArgs4Taint τEnd 0 hOpt s₁ s₂ hLow).1

private theorem bv64_shr_ge64_zero (x : BitVec 64) (s : Nat) (hs : s ≥ 64) :
    x >>> s = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hPow : 2 ^ 64 ≤ 2 ^ s := Nat.pow_le_pow_right (by omega) hs
  have hLt : x.toNat < 2 ^ s := Nat.lt_of_lt_of_le x.isLt hPow
  simp [Nat.div_eq_of_lt hLt]

/-- **Closed-Form Carryless `0x87` (`z⁷ + z² + z + 1`) Reduction Lemma & `< 128`-Bit Degree Bound**:
    Proves that `(clmul64 c3 0x87#64).hi` equals `(c3 >>> 57) ^^^ (c3 >>> 62) ^^^ (c3 >>> 63)`
    and strictly vanishes above bit 6 (`>>> 7 = 0#64`), guaranteeing that the 2-step `VPCLMULQDQ`
    `0x87` modular fold produces a canonical `< 128`-bit remainder with zero high overflow! -/
theorem clmul64_0x87_hi_degree_bound (c3 : BitVec 64) :
    (clmul64 c3 0x87#64).hi = (c3 >>> 57) ^^^ (c3 >>> 62) ^^^ (c3 >>> 63) ∧
    (clmul64 c3 0x87#64).hi >>> 7 = 0#64 := by
  have hHi : (clmul64 c3 0x87#64).hi = (c3 >>> 57) ^^^ (c3 >>> 62) ^^^ (c3 >>> 63) := by
    simp [clmul64, clmul64Step, Vec128.zero, BitVec.xor_assoc]
  refine ⟨hHi, ?_⟩
  have hShrShr (x : BitVec 64) (a b : Nat) : (x >>> a) >>> b = x >>> (a + b) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight, BitVec.toNat_ushiftRight,
        Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
        Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rw [hHi, bv_shr_xor, bv_shr_xor, hShrShr, hShrShr, hShrShr,
      bv64_shr_ge64_zero c3 64 (by omega),
      bv64_shr_ge64_zero c3 69 (by omega),
      bv64_shr_ge64_zero c3 70 (by omega)]
  rfl

/-! ### 7.4 `goldilocks_mul_ct` (`x86_64` & `aarch64`): Universal `< p` Canonical Proof -/

@[expose]
def goldilocksPrime : Nat := 0xFFFFFFFF00000001

/-- Goldilocks x86 kernel including its four-register scratch wipe. -/
def goldilocksMulCtX86Prog : List X86Stmt :=
  [ .instr (.movReg64 .rdx .rdi)
  , .instr (.mulx64 .rcx .rax .rsi)
  , .instr (.movReg64 .rdx .rcx)
  , .instr (.shrImm64 .rcx 32)
  , .instr (.mov32Zext .rdx .rdx)
  , .instr (.sub64 .rax .rcx)
  , .instr (.sbbSelf32Zext .r8)
  , .instr (.sub64 .rax .r8)
  , .instr (.movReg64 .r9 .rdx)
  , .instr (.shlImm64 .r9 32)
  , .instr (.sub64 .r9 .rdx)
  , .instr (.add64 .rax .r9)
  , .instr (.sbbSelf32Zext .r8)
  , .instr (.add64 .rax .r8)
  , .instr (.movImm64 .r9 0x00000000FFFFFFFF#64)
  , .instr (.movReg64 .r8 .rax)
  , .instr (.add64 .r8 .r9)
  , .instr (.sbbSelf64 .rcx)
  , .instr (.and64 .rcx .r9)
  , .instr (.add64 .rax .rcx)
  , .instr (.xor64 .rcx .rcx)
  , .instr (.xor64 .rdx .rdx)
  , .instr (.xor64 .r8 .r8)
  , .instr (.xor64 .r9 .r9)
  , .ret ]

/-- Goldilocks ARM instruction stream, entered under the caller's DIT guard. -/
def goldilocksMulCtArmProg : List ArmStmt :=
  [ .instr (.mulLo64 .x2 .x0 .x1)
  , .instr (.umulh64 .x3 .x0 .x1)
  , .instr (.lsrImm64 .x4 .x3 32)
  , .instr (.andImm64 .x5 .x3 0x00000000FFFFFFFF#64)
  , .instr (.movImm64 .x6 0x00000000FFFFFFFF#64)
  , .instr (.subs64 .x2 .x2 .x4)
  , .instr (.sbcMask64 .x7)
  , .instr (.and64 .x7 .x7 .x6)
  , .instr (.sub64 .x2 .x2 .x7)
  , .instr (.lslImm64 .x8 .x5 32)
  , .instr (.sub64 .x8 .x8 .x5)
  , .instr (.adds64 .x2 .x2 .x8)
  , .instr (.adcZero64 .x7)
  , .instr (.neg64 .x7 .x7)
  , .instr (.and64 .x7 .x7 .x6)
  , .instr (.add64 .x2 .x2 .x7)
  , .instr (.adds64 .x8 .x2 .x6)
  , .instr (.adcZero64 .x7)
  , .instr (.neg64 .x7 .x7)
  , .instr (.and64 .x7 .x7 .x6)
  , .instr (.add64 .x0 .x2 .x7)
  , .instr (.movImm64 .x2 0#64)
  , .instr (.movImm64 .x3 0#64)
  , .instr (.movImm64 .x4 0#64)
  , .instr (.movImm64 .x5 0#64)
  , .instr (.movImm64 .x6 0#64)
  , .instr (.movImm64 .x7 0#64)
  , .instr (.movImm64 .x8 0#64)
  , .ret ]

def glAllSecretX86Taint : X86TaintState :=
  { gpr := fun _ => .sec
    ymm := fun _ => .pub
    cf := .sec, of := .sec, zf := .sec
    doitAssumed := false, upperYmmClean := true }

def glAllSecretArmTaint : ArmTaintState :=
  { gpr := fun _ => .sec
    neon := fun _ => .pub
    z := .sec, c := .sec
    ditAssumed := true }

theorem goldilocksMulCtX86_constant_time
    (s₁ s₂ : X86State)
    (hLow : X86LowEq (fun _ => .sec) glAllSecretX86Taint s₁ s₂) :
    (execX86Prog goldilocksMulCtX86Prog 0 s₁).2 = (execX86Prog goldilocksMulCtX86Prog 0 s₂).2 := by
  have hChk : ∃ τOut, checkX86Prog true glAllSecretX86Taint goldilocksMulCtX86Prog = some τOut :=
    ⟨_, rfl⟩
  rcases hChk with ⟨τOut, hOpt⟩
  exact (x86_ct_checker_sound (fun _ => .sec) true (fun _ _ => rfl)
    goldilocksMulCtX86Prog glAllSecretX86Taint τOut 0 hOpt s₁ s₂ hLow).1

theorem goldilocksMulCtArm_constant_time
    (s₁ s₂ : ArmState)
    (hLow : ArmLowEq (fun _ => .sec) glAllSecretArmTaint s₁ s₂) :
    (execArmProg goldilocksMulCtArmProg 0 s₁).2 = (execArmProg goldilocksMulCtArmProg 0 s₂).2 := by
  have hChk : ∃ τOut, checkArmProg true glAllSecretArmTaint goldilocksMulCtArmProg = some τOut :=
    ⟨_, rfl⟩
  rcases hChk with ⟨τOut, hOpt⟩
  exact (arm_ct_checker_sound (fun _ => .sec) true (fun _ _ => rfl)
    goldilocksMulCtArmProg glAllSecretArmTaint τOut 0 hOpt s₁ s₂ hLow).1

private theorem bitvec64_and_mask32_toNat (x : BitVec 64) :
    (x &&& 0x00000000FFFFFFFF#64).toNat = x.toNat % 4294967296 := by
  change (x &&& BitVec.ofNat 64 (2 ^ 32 - 1)).toNat = x.toNat % 4294967296
  rw [BitVec.toNat_and]
  exact Constructive.and_mask x.toNat 32

private theorem bitvec64_zext32_toNat (x : BitVec 64) :
    ((x.truncate 32).zeroExtend 64).toNat = x.toNat % 4294967296 := by
  simp; omega

private theorem bitvec64_shl32_sub_self_toNat (u : BitVec 64) (hu : u.toNat < 4294967296) :
    ((u <<< 32) - u).toNat = 4294967295 * u.toNat := by
  have hShl : (u <<< 32).toNat = u.toNat * 4294967296 := by
    rw [BitVec.toNat_shiftLeft]
    have : u.toNat <<< 32 = u.toNat * 4294967296 := by
      rw [Nat.shiftLeft_eq]
    rw [this, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_sub, hShl]
  omega

/-- Pure arithmetic soundness of the 3-step `sbb`/`sbc` Goldilocks reduction over **all**
    `(a, b) ∈ [0, 2⁶⁴ - 1]²`, including `a = b = 2⁶⁴ - 1` (`0xFFFFFFFFFFFFFFFF`)! -/
theorem goldilocks_reduce128_nat_sound (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    let p := goldilocksPrime
    let prod := a * b
    let lo := prod % (2 ^ 64)
    let hi := prod / (2 ^ 64)
    let hiHi := hi / 4294967296
    let hiLo := hi % 4294967296
    let t1 := if lo < hiHi then lo + (2 ^ 64) - hiHi - 4294967295 else lo - hiHi
    let mid := 4294967295 * hiLo
    let t2 := if t1 + mid ≥ 2 ^ 64 then t1 + mid - (2 ^ 64) + 4294967295 else t1 + mid
    let res := if t2 + 4294967295 ≥ 2 ^ 64 then t2 + 4294967295 - (2 ^ 64) else t2
    res < p ∧ res = prod % p := by
  have hProdBound : a * b ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  dsimp only [goldilocksPrime]
  generalize hProdEq : a * b = prod at hProdBound ⊢
  generalize hLoEq : prod % (2 ^ 64) = lo
  generalize hHiEq : prod / (2 ^ 64) = hi
  have hLoLt : lo < 18446744073709551616 := by subst hLoEq; omega
  have hHiLt : hi < 18446744073709551615 := by subst hHiEq; omega
  have hProdDecomp : prod = lo + 18446744073709551616 * hi := by subst hLoEq hHiEq; omega
  generalize hHiHiEq : hi / 4294967296 = hiHi
  generalize hHiLoEq : hi % 4294967296 = hiLo
  have hHiLoLt : hiLo < 4294967296 := by subst hHiLoEq; omega
  have hHiHiLt : hiHi < 4294967296 := by subst hHiHiEq; omega
  have hHiDecomp : hi = hiLo + 4294967296 * hiHi := by subst hHiLoEq hHiHiEq; omega
  have hMidBound : 4294967295 * hiLo ≤ 4294967295 * 4294967295 := by omega
  have hBoth :
      let t1 := if lo < hiHi then lo + (2 ^ 64) - hiHi - 4294967295 else lo - hiHi
      let mid := 4294967295 * hiLo
      let t2 := if t1 + mid ≥ 2 ^ 64 then t1 + mid - (2 ^ 64) + 4294967295 else t1 + mid
      let res := if t2 + 4294967295 ≥ 2 ^ 64 then t2 + 4294967295 - (2 ^ 64) else t2
      res < 18446744069414584321 ∧ ∃ q : Nat, prod = 18446744069414584321 * q + res := by
    dsimp only
    by_cases h1 : lo < hiHi <;> simp only [h1, ↓reduceIte]
    · by_cases h2 : lo + 2 ^ 64 - hiHi - 4294967295 + 4294967295 * hiLo ≥ 2 ^ 64 <;>
        simp only [h2, ↓reduceIte]
      · by_cases h3 : lo + 2 ^ 64 - hiHi - 4294967295 + 4294967295 * hiLo - 2 ^ 64 + 4294967295 +
            4294967295 ≥ 2 ^ 64 <;> simp only [h3, ↓reduceIte]
        · refine ⟨by omega, hiLo + 4294967297 * hiHi + 1, by omega⟩
        · refine ⟨by omega, hiLo + 4294967297 * hiHi, by omega⟩
      · by_cases h3 : lo + 2 ^ 64 - hiHi - 4294967295 + 4294967295 * hiLo + 4294967295 ≥ 2 ^ 64 <;>
          simp only [h3, ↓reduceIte]
        · refine ⟨by omega, hiLo + 4294967297 * hiHi, by omega⟩
        · refine ⟨by omega, hiLo + 4294967297 * hiHi - 1, by omega⟩
    · by_cases h2 : lo - hiHi + 4294967295 * hiLo ≥ 2 ^ 64 <;>
        simp only [h2, ↓reduceIte]
      · by_cases h3 : lo - hiHi + 4294967295 * hiLo - 2 ^ 64 + 4294967295 + 4294967295 ≥ 2 ^ 64 <;>
          simp only [h3, ↓reduceIte]
        · refine ⟨by omega, hiLo + 4294967297 * hiHi + 2, by omega⟩
        · refine ⟨by omega, hiLo + 4294967297 * hiHi + 1, by omega⟩
      · by_cases h3 : lo - hiHi + 4294967295 * hiLo + 4294967295 ≥ 2 ^ 64 <;>
          simp only [h3, ↓reduceIte]
        · refine ⟨by omega, hiLo + 4294967297 * hiHi + 1, by omega⟩
        · refine ⟨by omega, hiLo + 4294967297 * hiHi, by omega⟩
  rcases hBoth with ⟨hResLt, q, hq⟩
  refine ⟨hResLt, ?_⟩
  rw [hq, Nat.mul_add_mod, Nat.mod_eq_of_lt hResLt]

def initGlX86State (a b : BitVec 64) : X86State :=
  { gpr := fun r => if r == .rdi then a else if r == .rsi then b else 0#64
    ymm := fun _ => Vec256.zero
    flags := { cf := false, of := false, zf := false }
    mem := fun _ => 0#64
    doitEnabled := false
    ymmUpperDirty := false }

def initGlArmState (a b : BitVec 64) : ArmState :=
  { gpr := fun r => if r == .x0 then a else if r == .x1 then b else 0#64
    neon := fun _ => Vec128.zero
    flags := { z := false, c := false }
    mem := fun _ => 0#64
    ditEnabled := false }

private theorem x86_state_setGpr_gpr (s : X86State) (r q : X86Gpr) (v : BitVec 64) :
    (s.setGpr r v).gpr q = if q == r then v else s.gpr q := rfl

private theorem x86_state_setGpr_flags (s : X86State) (r : X86Gpr) (v : BitVec 64) :
    (s.setGpr r v).flags = s.flags := rfl

private theorem arm_state_setGpr_gpr (s : ArmState) (r q : ArmGpr) (v : BitVec 64) :
    (s.setGpr r v).gpr q = if q == r then v else s.gpr q := rfl

private theorem gl_step1_toNat (u v : BitVec 64) (hv : v.toNat < 4294967296) :
    ((u - v) - (if decide (u.toNat < v.toNat) then 0x00000000FFFFFFFF#64 else 0#64)).toNat =
    if u.toNat < v.toNat then u.toNat + (2 ^ 64) - v.toNat - 4294967295
    else u.toNat - v.toNat := by
  have hu : u.toNat < 2 ^ 64 := u.isLt
  have hd : (0x00000000FFFFFFFF#64 : BitVec 64).toNat = 4294967295 := rfl
  by_cases h : u.toNat < v.toNat <;>
    simp only [h, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
  · rw [BitVec.toNat_sub, BitVec.toNat_sub, hd]; omega
  · rw [BitVec.sub_zero, BitVec.toNat_sub]; omega

private theorem gl_step2_toNat (t1 mid : BitVec 64) (hMid : mid.toNat ≤ 4294967295 * 4294967295) :
    ((t1 + mid) +
      (if decide (t1.toNat + mid.toNat ≥ 2 ^ 64) then 0x00000000FFFFFFFF#64 else 0#64)).toNat =
    if t1.toNat + mid.toNat ≥ 2 ^ 64 then t1.toNat + mid.toNat - (2 ^ 64) + 4294967295
    else t1.toNat + mid.toNat := by
  have ht1 : t1.toNat < 2 ^ 64 := t1.isLt
  have hd : (0x00000000FFFFFFFF#64 : BitVec 64).toNat = 4294967295 := rfl
  by_cases h : t1.toNat + mid.toNat ≥ 2 ^ 64 <;>
    simp only [h, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
  · rw [BitVec.toNat_add, BitVec.toNat_add, hd]; omega
  · rw [BitVec.add_zero, BitVec.toNat_add]; omega

private theorem gl_step3_toNat (t2 : BitVec 64) :
    (t2 + ((if decide (t2.toNat + (0x00000000FFFFFFFF#64 : BitVec 64).toNat ≥ 2 ^ 64)
            then 0xFFFFFFFFFFFFFFFF#64 else 0#64) &&& 0x00000000FFFFFFFF#64)).toNat =
    if t2.toNat + 4294967295 ≥ 2 ^ 64 then t2.toNat + 4294967295 - (2 ^ 64)
    else t2.toNat := by
  have ht2 : t2.toNat < 2 ^ 64 := t2.isLt
  have hd : (0x00000000FFFFFFFF#64 : BitVec 64).toNat = 4294967295 := rfl
  have hmT : (0xFFFFFFFFFFFFFFFF#64 &&& 0x00000000FFFFFFFF#64 : BitVec 64) = 0x00000000FFFFFFFF#64 := rfl
  have hmF : (0#64 &&& 0x00000000FFFFFFFF#64 : BitVec 64) = 0#64 := rfl
  rw [hd]
  by_cases h : t2.toNat + 4294967295 ≥ 2 ^ 64 <;>
    simp only [h, decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
  · rw [hmT, BitVec.toNat_add, hd]; omega
  · rw [hmF, BitVec.add_zero]

/-- **Universal Functional Correctness of `qsag_asm_goldilocks_mul_ct_x86_64`**:
    For **all** `(a, b) : BitVec 64 × BitVec 64` (`[0, 2⁶⁴ - 1]²`), `rax` on return is strictly
    canonical (`< p`) and equals `(a.toNat * b.toNat) % p`. -/
theorem goldilocksMulCtX86_canonical_correct (a b : BitVec 64) :
    let out := (execX86Prog goldilocksMulCtX86Prog 0 (initGlX86State a b)).1.gpr .rax
    out.toNat < goldilocksPrime ∧ out.toNat = (a.toNat * b.toNat) % goldilocksPrime := by
  have hArith := goldilocks_reduce128_nat_sound a.toNat b.toNat a.isLt b.isLt
  have hProdBound : a.toNat * b.toNat ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  let prod := a.toNat * b.toNat
  let loBv := BitVec.ofNat 64 prod
  let hiBv := BitVec.ofNat 64 (prod / (2 ^ 64))
  have hLo : loBv.toNat = prod % (2 ^ 64) := BitVec.toNat_ofNat prod 64
  have hHi : hiBv.toNat = prod / (2 ^ 64) := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hHiHi : (hiBv >>> 32).toNat = hiBv.toNat / 4294967296 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hHiLo : ((hiBv.truncate 32).zeroExtend 64).toNat = hiBv.toNat % 4294967296 :=
    bitvec64_zext32_toNat hiBv
  have hMid : ((((hiBv.truncate 32).zeroExtend 64) <<< 32) - ((hiBv.truncate 32).zeroExtend 64)).toNat =
      4294967295 * (hiBv.toNat % 4294967296) := by
    rw [bitvec64_shl32_sub_self_toNat _ (by rw [hHiLo]; omega), hHiLo]
  have hMidLe : ((((hiBv.truncate 32).zeroExtend 64) <<< 32) - ((hiBv.truncate 32).zeroExtend 64)).toNat ≤
      4294967295 * 4294967295 := by
    rw [hMid]; have := Nat.mod_lt hiBv.toNat (by omega : 0 < 4294967296); omega
  have hHiHiLt : (hiBv >>> 32).toNat < 4294967296 := by
    rw [hHiHi]; have := hiBv.isLt; omega
  have hEqNat :
      ((execX86Prog goldilocksMulCtX86Prog 0 (initGlX86State a b)).1.gpr .rax).toNat =
      (let lo := prod % (2 ^ 64)
       let hi := prod / (2 ^ 64)
       let hiHi := hi / 4294967296
       let hiLo := hi % 4294967296
       let t1 := if lo < hiHi then lo + (2 ^ 64) - hiHi - 4294967295 else lo - hiHi
       let mid := 4294967295 * hiLo
       let t2 := if t1 + mid ≥ 2 ^ 64 then t1 + mid - (2 ^ 64) + 4294967295 else t1 + mid
       if t2 + 4294967295 ≥ 2 ^ 64 then t2 + 4294967295 - (2 ^ 64) else t2) := by
    dsimp only [goldilocksMulCtX86Prog, execX86Prog, execX86Instr, initGlX86State]
    simp only [x86_state_setGpr_gpr, beq_iff_eq, reduceCtorEq, ↓reduceIte]
    change (
      let s1 := loBv - (hiBv >>> 32)
      let b1 := decide (loBv.toNat < (hiBv >>> 32).toNat)
      let m1 : BitVec 64 := if b1 then 0x00000000FFFFFFFF#64 else 0#64
      let t1Bv := s1 - m1
      let rdxZ := (hiBv.truncate 32).zeroExtend 64
      let midBv := (rdxZ <<< 32) - rdxZ
      let s2 := t1Bv + midBv
      let c2 := decide (t1Bv.toNat + midBv.toNat ≥ 2 ^ 64)
      let m2 : BitVec 64 := if c2 then 0x00000000FFFFFFFF#64 else 0#64
      let t2Bv := s2 + m2
      let c3 := decide (t2Bv.toNat + (0x00000000FFFFFFFF#64 : BitVec 64).toNat ≥ 2 ^ 64)
      let m3 : BitVec 64 := (if c3 then 0xFFFFFFFFFFFFFFFF#64 else 0#64) &&& 0x00000000FFFFFFFF#64
      (t2Bv + m3).toNat) = _
    dsimp only
    rw [gl_step3_toNat, gl_step2_toNat _ _ hMidLe, hMid, gl_step1_toNat _ _ hHiHiLt, hLo, hHiHi, hHi]
  dsimp only at hEqNat ⊢
  rw [hEqNat]
  exact hArith

/-- **Universal Functional Correctness & Cross-ISA Equivalence of `qsag_asm_goldilocks_mul_ct_aarch64`**:
    Proves that the `aarch64` `mul + umulh + subs/sbc + adds/adc` kernel (with ARM64 inverted
    `PSTATE.C = !borrow` semantics!) returns the **exact same canonical `< p` field element** as
    `qsag_asm_goldilocks_mul_ct_x86_64` across all $2^{128}$ input pairs `(a, b) : BitVec 64 × BitVec 64`! -/
theorem goldilocksMulCt_x86_eq_arm (a b : BitVec 64) :
    (execArmProg goldilocksMulCtArmProg 0 (initGlArmState a b)).1.gpr .x0 =
      (execX86Prog goldilocksMulCtX86Prog 0 (initGlX86State a b)).1.gpr .rax := by
  apply BitVec.eq_of_toNat_eq
  let prod := a.toNat * b.toNat
  let loBv := BitVec.ofNat 64 prod
  let hiBv := BitVec.ofNat 64 (prod / (2 ^ 64))
  have hAndEqZext : hiBv &&& 0x00000000FFFFFFFF#64 = (hiBv.truncate 32).zeroExtend 64 := by
    apply BitVec.eq_of_toNat_eq
    rw [bitvec64_and_mask32_toNat, bitvec64_zext32_toNat]
  have hSbcMask (p : Bool) :
      ((if p then 0#64 else 0xFFFFFFFFFFFFFFFF#64) &&& 0x00000000FFFFFFFF#64) =
      (if !p then 0x00000000FFFFFFFF#64 else 0#64) := by
    cases p <;> rfl
  have hX86Mask (p : Bool) :
      ((if p then 0xFFFFFFFFFFFFFFFF#64 else 0#64) &&& 0x00000000FFFFFFFF#64) =
      (if p then 0x00000000FFFFFFFF#64 else 0#64) := by
    cases p <;> rfl
  have hAdcNegMask (p : Bool) :
      ((0#64 - (if p then 1#64 else 0#64)) &&& 0x00000000FFFFFFFF#64) =
      (if p then 0x00000000FFFFFFFF#64 else 0#64) := by
    cases p <;> rfl
  have hBorrowCmp :
      (!decide (loBv.toNat ≥ (hiBv >>> 32).toNat)) = decide (loBv.toNat < (hiBv >>> 32).toNat) := by
    generalize loBv.toNat = u
    generalize (hiBv >>> 32).toNat = v
    by_cases h : u < v
    · have hge : ¬(u ≥ v) := by omega
      simp only [h, hge, decide_true, decide_false]; rfl
    · have hge : u ≥ v := by omega
      simp only [h, hge, decide_true, decide_false]; rfl
  dsimp only [goldilocksMulCtArmProg, execArmProg, execArmInstr, initGlArmState,
              goldilocksMulCtX86Prog, execX86Prog, execX86Instr, initGlX86State]
  simp only [arm_state_setGpr_gpr,
             x86_state_setGpr_gpr,
             beq_iff_eq, reduceCtorEq, ↓reduceIte]
  change (
    let s1 := loBv - (hiBv >>> 32)
    let c1 := decide (loBv.toNat ≥ (hiBv >>> 32).toNat)
    let m1 := (if c1 then 0#64 else 0xFFFFFFFFFFFFFFFF#64) &&& 0x00000000FFFFFFFF#64
    let t1 := s1 - m1
    let r5 := hiBv &&& 0x00000000FFFFFFFF#64
    let mid := (r5 <<< 32) - r5
    let s2 := t1 + mid
    let c2 := decide (t1.toNat + mid.toNat ≥ 2 ^ 64)
    let m2 := (0#64 - (if c2 then 1#64 else 0#64)) &&& 0x00000000FFFFFFFF#64
    let t2 := s2 + m2
    let c3 := decide (t2.toNat + (0x00000000FFFFFFFF#64 : BitVec 64).toNat ≥ 2 ^ 64)
    let m3 := (0#64 - (if c3 then 1#64 else 0#64)) &&& 0x00000000FFFFFFFF#64
    (t2 + m3).toNat) =
    (let s1 := loBv - (hiBv >>> 32)
     let b1 := decide (loBv.toNat < (hiBv >>> 32).toNat)
     let m1 : BitVec 64 := if b1 then 0x00000000FFFFFFFF#64 else 0#64
     let t1 := s1 - m1
     let rdxZ := (hiBv.truncate 32).zeroExtend 64
     let mid := (rdxZ <<< 32) - rdxZ
     let s2 := t1 + mid
     let c2 := decide (t1.toNat + mid.toNat ≥ 2 ^ 64)
     let m2 : BitVec 64 := if c2 then 0x00000000FFFFFFFF#64 else 0#64
     let t2 := s2 + m2
     let c3 := decide (t2.toNat + (0x00000000FFFFFFFF#64 : BitVec 64).toNat ≥ 2 ^ 64)
     let m3 : BitVec 64 := (if c3 then 0xFFFFFFFFFFFFFFFF#64 else 0#64) &&& 0x00000000FFFFFFFF#64
     (t2 + m3).toNat)
  dsimp only
  rw [hSbcMask, hBorrowCmp, hAndEqZext, hAdcNegMask, hAdcNegMask, hX86Mask]

/-! ### 7.5 `ct_eq_32` (`x86_64` & `aarch64`): Branchless 256-Bit BDOZ Tag Comparison -/

/-- Branchless `((d ||| -d) >>> 63) ^^^ 1` zero-detection identity over **all** `d : BitVec 64`. -/
theorem or_neg_shr63_xor1_eq_beq_zero (d : BitVec 64) :
    (((d ||| (0#64 - d)) >>> 63) ^^^ 1#64) = (if d == 0#64 then 1#64 else 0#64) := by
  by_cases hd : d = 0#64
  · subst hd; rfl
  · have hdBeq : (d == 0#64) = false := beq_false_of_ne hd
    rw [hdBeq]; simp only [Bool.false_eq_true, ↓reduceIte]
    have hdPos : 0 < d.toNat := by
      have : d.toNat ≠ 0 := fun h0 => hd (BitVec.eq_of_toNat_eq h0)
      omega
    have hdLt : d.toNat < 2 ^ 64 := d.isLt
    have hNegNat : (0#64 - d).toNat = 2 ^ 64 - d.toNat := by
      rw [BitVec.toNat_sub]
      change (18446744073709551616 - d.toNat + 0) % 18446744073709551616 = _
      omega
    have hOrGe : (d ||| (0#64 - d)).toNat ≥ 2 ^ 63 := by
      rw [BitVec.toNat_or]
      by_cases hHalf : d.toNat ≥ 2 ^ 63
      · exact Nat.le_trans hHalf (Nat.left_le_or)
      · have hNegHalf : (0#64 - d).toNat ≥ 2 ^ 63 := by omega
        exact Nat.le_trans hNegHalf (Nat.right_le_or)
    have hOrLt : (d ||| (0#64 - d)).toNat < 2 ^ 64 := (d ||| (0#64 - d)).isLt
    have hShr1 : (d ||| (0#64 - d)) >>> 63 = 1#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      change (d ||| (0#64 - d)).toNat / (2 ^ 63) = 1
      omega
    rw [hShr1]; rfl

/-- Straight-line 32-byte tag comparison program on `x86_64` (`qsag_asm_ct_eq_32_x86_64`). -/
def ctEq32X86Prog : List X86Stmt :=
  [ .instr (.load64 .rax .rdi 0#64)
  , .instr (.xorMem64 .rax .rsi 0#64)
  , .instr (.load64 .rcx .rdi 8#64)
  , .instr (.xorMem64 .rcx .rsi 8#64)
  , .instr (.load64 .rdx .rdi 16#64)
  , .instr (.xorMem64 .rdx .rsi 16#64)
  , .instr (.load64 .r8 .rdi 24#64)
  , .instr (.xorMem64 .r8 .rsi 24#64)
  , .instr (.or64 .rax .rcx)
  , .instr (.or64 .rdx .r8)
  , .instr (.or64 .rax .rdx)
  , .instr (.movReg64 .rcx .rax)
  , .instr (.neg64 .rcx)
  , .instr (.or64 .rax .rcx)
  , .instr (.shrImm64 .rax 63)
  , .instr (.xorImm64 .rax 1#64)
  , .instr (.xor64 .rcx .rcx)
  , .instr (.xor64 .rdx .rdx)
  , .instr (.xor64 .r8 .r8)
  , .ret ]

/-- ARM 32-byte equality model: the 22-instruction kernel with four paired loads
    expanded into eight scalar loads (26 model statements). -/
def ctEq32ArmProg : List ArmStmt :=
  [ .instr (.ldr64 .x2 .x0 0#64)
  , .instr (.ldr64 .x3 .x0 8#64)
  , .instr (.ldr64 .x4 .x1 0#64)
  , .instr (.ldr64 .x5 .x1 8#64)
  , .instr (.eor64 .x2 .x2 .x4)
  , .instr (.eor64 .x3 .x3 .x5)
  , .instr (.orr64 .x2 .x2 .x3)
  , .instr (.ldr64 .x4 .x0 16#64)
  , .instr (.ldr64 .x5 .x0 24#64)
  , .instr (.ldr64 .x6 .x1 16#64)
  , .instr (.ldr64 .x7 .x1 24#64)
  , .instr (.eor64 .x4 .x4 .x6)
  , .instr (.eor64 .x5 .x5 .x7)
  , .instr (.orr64 .x4 .x4 .x5)
  , .instr (.orr64 .x2 .x2 .x4)
  , .instr (.neg64 .x3 .x2)
  , .instr (.orr64 .x2 .x2 .x3)
  , .instr (.lsrImm64 .x0 .x2 63)
  , .instr (.eorImm64 .x0 .x0 1#64)
  , .instr (.movImm64 .x2 0#64)
  , .instr (.movImm64 .x3 0#64)
  , .instr (.movImm64 .x4 0#64)
  , .instr (.movImm64 .x5 0#64)
  , .instr (.movImm64 .x6 0#64)
  , .instr (.movImm64 .x7 0#64)
  , .ret ]

theorem ctEq32X86_constant_time
    (s₁ s₂ : X86State)
    (hLow : X86LowEq (fun _ => .sec) sysvPtrArgs4Taint s₁ s₂) :
    (execX86Prog ctEq32X86Prog 0 s₁).2 = (execX86Prog ctEq32X86Prog 0 s₂).2 := by
  have hChk : ∃ τOut, checkX86Prog true sysvPtrArgs4Taint ctEq32X86Prog = some τOut := ⟨_, rfl⟩
  rcases hChk with ⟨τOut, hOpt⟩
  exact (x86_ct_checker_sound (fun _ => .sec) true (fun _ _ => rfl)
    ctEq32X86Prog sysvPtrArgs4Taint τOut 0 hOpt s₁ s₂ hLow).1

theorem ctEq32Arm_constant_time
    (s₁ s₂ : ArmState)
    (hLow : ArmLowEq (fun _ => .sec) aapcsPtrArgs3Taint s₁ s₂) :
    (execArmProg ctEq32ArmProg 0 s₁).2 = (execArmProg ctEq32ArmProg 0 s₂).2 := by
  have hChk : ∃ τOut, checkArmProg true aapcsPtrArgs3Taint ctEq32ArmProg = some τOut := ⟨_, rfl⟩
  rcases hChk with ⟨τOut, hOpt⟩
  exact (arm_ct_checker_sound (fun _ => .sec) true (fun _ _ => rfl)
    ctEq32ArmProg aapcsPtrArgs3Taint τOut 0 hOpt s₁ s₂ hLow).1

private theorem arm_setGpr_gpr (s : ArmState) (r q : ArmGpr) (v : BitVec 64) :
    (s.setGpr r v).gpr q = if q == r then v else s.gpr q := rfl

private theorem arm_setGpr_mem (s : ArmState) (r : ArmGpr) (v : BitVec 64) :
    (s.setGpr r v).mem = s.mem := rfl

/-- **256-Bit Functional Soundness of `ctEq32ArmProg`**:
    Returns `1#64` iff all four 64-bit limbs of `[x0 + 0..24]` equal `[x1 + 0..24]`, `0#64` otherwise,
    and wipes all scratch registers `x2..x7` to `0#64`! -/
theorem ctEq32Arm_functional_correct (st : ArmState) :
    let outSt := (execArmProg ctEq32ArmProg 0 st).1
    let pA := st.gpr .x0
    let pB := st.gpr .x1
    let eqAll :=
      (st.mem pA == st.mem pB) &&
      (st.mem (pA + 8#64) == st.mem (pB + 8#64)) &&
      (st.mem (pA + 16#64) == st.mem (pB + 16#64)) &&
      (st.mem (pA + 24#64) == st.mem (pB + 24#64))
    outSt.gpr .x0 = (if eqAll then 1#64 else 0#64) ∧
    outSt.gpr .x2 = 0#64 ∧ outSt.gpr .x7 = 0#64 := by
  have hOrZero (u v : BitVec 64) : ((u ||| v) == 0#64) = ((u == 0#64) && (v == 0#64)) := by
    by_cases hu : u = 0#64 <;> by_cases hv : v = 0#64
    · subst hu hv; rfl
    · subst hu; simp [beq_false_of_ne hv]
    · subst hv; simp [beq_false_of_ne hu]
    · have huv : u ||| v ≠ 0#64 := by
        intro h0
        apply hu
        apply BitVec.eq_of_getLsbD_eq
        intro i _
        have := congrArg (fun z => z.getLsbD i) h0
        simp at this; simp [this.1]
      simp [beq_false_of_ne hu, beq_false_of_ne hv, beq_false_of_ne huv]
  have hXorZero (u v : BitVec 64) : ((u ^^^ v) == 0#64) = (u == v) := by
    by_cases h : u = v
    · subst h; simp
    · have hne : u ^^^ v ≠ 0#64 := by
        intro h0; apply h
        have := congrArg (fun z => z ^^^ v) h0
        simpa [BitVec.xor_assoc] using this
      have hb : (u == v) = false := beq_false_of_ne h
      simp [hb, beq_false_of_ne hne]
  dsimp only [ctEq32ArmProg, execArmProg, execArmInstr]
  simp only [arm_setGpr_gpr, arm_setGpr_mem, beq_iff_eq, reduceCtorEq, ↓reduceIte]
  refine ⟨?_, trivial, trivial⟩
  rw [or_neg_shr63_xor1_eq_beq_zero]
  simp only [BitVec.add_zero, hOrZero, hXorZero, Bool.and_assoc]


/-- Secret UMULH requires DIT; without it both operands enter the leakage trace. -/
theorem tooth_arm_umulh_requires_dit (st : ArmState) (h : st.ditEnabled = false) :
    checkArmInstr true { glAllSecretArmTaint with ditAssumed := false }
      (.umulh64 .x2 .x0 .x1) = none ∧
    (execArmInstr (.umulh64 .x2 .x0 .x1) 0 st).2.varLatencyOperands =
      [st.gpr .x0, st.gpr .x1] := by
  exact ⟨rfl, by simp [execArmInstr, h]⟩

/-- The actual kernel stream cannot manufacture its caller's DIT guard. -/
theorem tooth_goldilocks_arm_entry_requires_dit :
    checkArmProg true { glAllSecretArmTaint with ditAssumed := false }
      goldilocksMulCtArmProg = none := by rfl

theorem tooth_secret_pmull_requires_dit :
    checkArmInstr true
      { glAllSecretArmTaint with neon := fun _ => .sec, ditAssumed := false }
      (.pmull1q .v0 .v1 .v2) = none := by rfl

private theorem x86_state_setGpr_mem (s : X86State) (r : X86Gpr) (v : BitVec 64) :
    (s.setGpr r v).mem = s.mem := rfl

theorem ctEq32X86_functional_correct (st : X86State) :
    let outSt := (execX86Prog ctEq32X86Prog 0 st).1
    let pA := st.gpr .rdi
    let pB := st.gpr .rsi
    let eqAll :=
      (st.mem pA == st.mem pB) &&
      (st.mem (pA + 8#64) == st.mem (pB + 8#64)) &&
      (st.mem (pA + 16#64) == st.mem (pB + 16#64)) &&
      (st.mem (pA + 24#64) == st.mem (pB + 24#64))
    outSt.gpr .rax = (if eqAll then 1#64 else 0#64) ∧
    outSt.gpr .rcx = 0#64 ∧ outSt.gpr .rdx = 0#64 ∧
    outSt.gpr .r8 = 0#64 ∧ outSt.gpr .r9 = st.gpr .r9 := by
  have hOrZero (u v : BitVec 64) : ((u ||| v) == 0#64) = ((u == 0#64) && (v == 0#64)) := by
    by_cases hu : u = 0#64 <;> by_cases hv : v = 0#64
    · subst hu hv; rfl
    · subst hu; simp [beq_false_of_ne hv]
    · subst hv; simp [beq_false_of_ne hu]
    · have huv : u ||| v ≠ 0#64 := by
        intro h0
        apply hu
        apply BitVec.eq_of_getLsbD_eq
        intro i _
        have := congrArg (fun z => z.getLsbD i) h0
        simp at this; simp [this.1]
      simp [beq_false_of_ne hu, beq_false_of_ne hv, beq_false_of_ne huv]
  have hXorZero (u v : BitVec 64) : ((u ^^^ v) == 0#64) = (u == v) := by
    by_cases h : u = v
    · subst h; simp
    · have hne : u ^^^ v ≠ 0#64 := by
        intro h0; apply h
        have := congrArg (fun z => z ^^^ v) h0
        simpa [BitVec.xor_assoc] using this
      have hb : (u == v) = false := beq_false_of_ne h
      simp [hb, beq_false_of_ne hne]
  dsimp only [ctEq32X86Prog, execX86Prog, execX86Instr]
  simp only [x86_state_setGpr_gpr, x86_state_setGpr_mem, beq_iff_eq, reduceCtorEq, ↓reduceIte]
  refine ⟨?_, trivial, trivial, trivial, trivial⟩
  rw [or_neg_shr63_xor1_eq_beq_zero]
  simp only [BitVec.add_zero, hOrZero, hXorZero, Bool.and_assoc]



/-- Every x86 Goldilocks scratch register is wiped, for arbitrary initial state. -/
theorem goldilocksMulCtX86_scratch_zero (st : X86State) :
    (execX86Prog goldilocksMulCtX86Prog 0 st).1.gpr .rcx = 0#64 ∧
    (execX86Prog goldilocksMulCtX86Prog 0 st).1.gpr .rdx = 0#64 ∧
    (execX86Prog goldilocksMulCtX86Prog 0 st).1.gpr .r8 = 0#64 ∧
    (execX86Prog goldilocksMulCtX86Prog 0 st).1.gpr .r9 = 0#64 := ⟨rfl, rfl, rfl, rfl⟩

/-- Every ARM Goldilocks scratch register is wiped, for arbitrary initial state. -/
theorem goldilocksMulCtArm_scratch_zero (st : ArmState) :
    (execArmProg goldilocksMulCtArmProg 0 st).1.gpr .x2 = 0#64 ∧
    (execArmProg goldilocksMulCtArmProg 0 st).1.gpr .x3 = 0#64 ∧
    (execArmProg goldilocksMulCtArmProg 0 st).1.gpr .x4 = 0#64 ∧
    (execArmProg goldilocksMulCtArmProg 0 st).1.gpr .x5 = 0#64 ∧
    (execArmProg goldilocksMulCtArmProg 0 st).1.gpr .x6 = 0#64 ∧
    (execArmProg goldilocksMulCtArmProg 0 st).1.gpr .x7 = 0#64 ∧
    (execArmProg goldilocksMulCtArmProg 0 st).1.gpr .x8 = 0#64 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Address cancellation, including wrapping 64-bit address arithmetic. -/
private theorem addr_eq_offset (a i j : BitVec 64) :
    ((a + i) == (a + j)) = (i == j) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro h
    have := congrArg (fun x => x - a) h
    simpa [BitVec.add_comm, BitVec.add_sub_cancel] using this
  · intro h; rw [h]

private theorem readMem256_writeMem256 (st : X86State) (a : BitVec 64) (v : Vec256) :
    (st.writeMem256 a v).readMem256 a = v := by
  have h0 : a = a + 0#64 := by simp
  simp only [X86State.readMem256, X86State.writeMem256, X86State.writeMem64]
  conv => lhs; rw [h0]
  simp only [BitVec.add_assoc, addr_eq_offset]
  rfl

set_option maxRecDepth 8192 in
/-- Executing one guarded GFNI block writes all 32 tower-field products.
    All inputs are loaded before the store, so this also holds for aliased buffers. -/
theorem gf256ShamirMulGfni_exec_1block_correct (st : X86State) (idx : Fin 32) :
    ((execX86Prog (gf256ShamirMulGfniProg 1) 0 st).1.readMem256 (st.gpr .rdi)).getByte idx =
      towerGf256Mul ((st.readMem256 (st.gpr .rsi)).getByte idx)
        ((st.readMem256 (st.gpr .rdx)).getByte idx) := by
  let va := st.readMem256 (st.gpr .rsi)
  let vb := st.readMem256 (st.gpr .rdx)
  let result := Vec256.gfniAffine0
      (Vec256.gfniMul (Vec256.gfniAffine0 va (Vec256.broadcastQ gfniTowerToPolyMat))
        (Vec256.gfniAffine0 vb (Vec256.broadcastQ gfniTowerToPolyMat)))
      (Vec256.broadcastQ gfniPolyToTowerMat)
  have hm : (execX86Prog (gf256ShamirMulGfniProg 1) 0 st).1.mem =
      (st.writeMem256 (st.gpr .rdi) result).mem := by
    simp only [gf256ShamirMulGfniProg, execX86Prog, execX86Loop, execX86Block, execX86Instr,
      X86State.setGpr, X86State.setYmm, X86State.writeMem256, X86State.writeMem64,
      beq_self_eq_true, ↓reduceIte, BitVec.add_zero]
    rfl
  change (X86State.readMem256 _ _).getByte idx = _
  have hr : (execX86Prog (gf256ShamirMulGfniProg 1) 0 st).1.readMem256 (st.gpr .rdi) = result := by
    change (⟨_, _, _, _⟩ : Vec256) = _
    simp only [hm]
    exact readMem256_writeMem256 st (st.gpr .rdi) result
  rw [hr]
  exact gf256ShamirMulGfni_32lane_correct va vb idx

/-- The 256-bit RSS share-lane expression computed by the AVX2 kernel. -/
abbrev keccakChiMpcLane256 := keccakChiMpcShareVec256

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
/-- The actual program stores the RSS chi result in output lane zero.
    Later stores use distinct offsets even under wrapping address arithmetic;
    no disjointness assumption on input and output buffers is needed for this lane. -/
theorem keccakChiMpcAvx2_exec_lane0_correct (st : X86State) :
    (execX86Prog keccakChiMpcAvx2Prog 0 st).1.readMem256 (st.gpr .rdi) =
      keccakChiMpcLane256
        (st.readMem256 (st.gpr .rsi))
        (st.readMem256 (st.gpr .rsi + 32#64))
        (st.readMem256 (st.gpr .rsi + 64#64))
        (st.readMem256 (st.gpr .rdx + 32#64))
        (st.readMem256 (st.gpr .rdx + 64#64))
        (st.readMem256 (st.gpr .rcx)) := by
  let a := st.gpr .rdi
  let v0 := (execX86Prog (keccakChiMpcAvx2Prog.take 17) 0 st).1.ymm .ymm10
  let v1 := (execX86Prog (keccakChiMpcAvx2Prog.take 25) 0 st).1.ymm .ymm10
  let v2 := (execX86Prog (keccakChiMpcAvx2Prog.take 33) 0 st).1.ymm .ymm10
  let v3 := (execX86Prog (keccakChiMpcAvx2Prog.take 41) 0 st).1.ymm .ymm10
  let v4 := (execX86Prog (keccakChiMpcAvx2Prog.take 49) 0 st).1.ymm .ymm10
  have hm : (execX86Prog keccakChiMpcAvx2Prog 0 st).1.mem =
      (((((st.writeMem256 (a + 0#64) v0).writeMem256 (a + 32#64) v1).writeMem256
        (a + 64#64) v2).writeMem256 (a + 96#64) v3).writeMem256 (a + 128#64) v4).mem := by
    rfl
  have frame (u0 u1 u2 u3 u4 : Vec256) :
      (((((st.writeMem256 (a + 0#64) u0).writeMem256 (a + 32#64) u1).writeMem256
        (a + 64#64) u2).writeMem256 (a + 96#64) u3).writeMem256 (a + 128#64) u4).readMem256 a = u0 := by
    simp [X86State.readMem256, X86State.writeMem256, X86State.writeMem64,
      BitVec.add_assoc, BitVec.self_eq_add_right]
  have hr : (execX86Prog keccakChiMpcAvx2Prog 0 st).1.readMem256 a = v0 := by
    change (⟨_, _, _, _⟩ : Vec256) = _
    simp only [hm]
    exact frame v0 v1 v2 v3 v4
  rw [hr]
  simp only [v0, keccakChiMpcAvx2Prog, List.take, execX86Prog, execX86Instr,
    X86State.setYmm, beq_iff_eq, reduceCtorEq, ↓reduceIte, BitVec.add_zero]
  rfl

/-! ### 8. Architectural Scalar `RFLAGS` Parity (`MUL`/`IMUL`/`SHL`/`SHR`/`ROR`/`SBB`) -/

private def mkRflagsTestState (rax rcx : BitVec 64) (cf of zf : Bool) : X86State :=
  { gpr := fun r => if r == .rax then rax else if r == .rcx then rcx else 0#64
    ymm := fun _ => Vec256.zero
    flags := { cf := cf, of := of, zf := zf }
    mem := fun _ => 0#64
    doitEnabled := false
    ymmUpperDirty := false }

/-- 6-bit shift-count masking (`COUNT & 63`): `SHR r64, 64` is a hardware no-op preserving both
    destination GPR and all `RFLAGS` (`CF`, `OF`, `ZF`). -/
theorem shrImm64_cnt64_noop (st : X86State) (dst : X86Gpr) (pc : Nat) :
    (execX86Instr (.shrImm64 dst 64) pc st).1.gpr dst = st.gpr dst ∧
    (execX86Instr (.shrImm64 dst 64) pc st).1.flags = st.flags := by
  simp [execX86Instr, X86State.setGpr]

/-- 6-bit shift-count masking (`COUNT & 63`): `SHL r64, 64` is a hardware no-op preserving both
    destination GPR and all `RFLAGS` (`CF`, `OF`, `ZF`). -/
theorem shlImm64_cnt64_noop (st : X86State) (dst : X86Gpr) (pc : Nat) :
    (execX86Instr (.shlImm64 dst 64) pc st).1.gpr dst = st.gpr dst ∧
    (execX86Instr (.shlImm64 dst 64) pc st).1.flags = st.flags := by
  simp [execX86Instr, X86State.setGpr]

/-- `SBB r, r` (`r - (r + CF) = -CF`) never signed-overflows on x86-64 and always clears `OF = false`. -/
theorem sbbSelf_clears_of (st : X86State) (dst : X86Gpr) (pc : Nat) :
    (execX86Instr (.sbbSelf64 dst) pc st).1.flags.of = false ∧
    (execX86Instr (.sbbSelf32Zext dst) pc st).1.flags.of = false := by
  exact ⟨rfl, rfl⟩

/-- All 8 `seed=0x51a` `MUL`/`SHL`/`SHR`/`ROR` `RFLAGS` edge cases plus signed `IMUL` `-1 * -1`,
    `MIN_INT * -1`, and `count = 65` 6-bit shift-count masking match physical x86-64 silicon. -/
theorem constantTimeIsa_rflags_regressions_verified :
    let c37 := (execX86Instr (.mul64 .rcx) 0 (mkRflagsTestState 0xffffffffffffffff#64 0x8000000000000000#64 true false false)).1
    let c38 := (execX86Instr (.shlImm64 .rax 1) 0 (mkRflagsTestState 0x8000000000000000#64 0xffffffff00000000#64 false true true)).1
    let c39 := (execX86Instr (.shrImm64 .rax 1) 0 (mkRflagsTestState 0xffffffff00000000#64 0xffffffff00000001#64 false false false)).1
    let c40 := (execX86Instr (.rorImm64 .rax 1) 0 (mkRflagsTestState 0xffffffff00000001#64 1#64 false true false)).1
    let c78 := (execX86Instr (.mul64 .rcx) 0 (mkRflagsTestState 0#64 0xffffffffffffffff#64 false true true)).1
    let c79 := (execX86Instr (.shlImm64 .rax 1) 0 (mkRflagsTestState 0xffffffffffffffff#64 0x8000000000000000#64 false false true)).1
    let c80 := (execX86Instr (.shrImm64 .rax 1) 0 (mkRflagsTestState 0x8000000000000000#64 0xffffffff00000000#64 true false true)).1
    let c81 := (execX86Instr (.rorImm64 .rax 1) 0 (mkRflagsTestState 0xffffffff00000000#64 0xffffffff00000001#64 true false true)).1
    let imulNoOvf := (execX86Instr (.imul64 .rax .rcx) 0 (mkRflagsTestState 0xffffffffffffffff#64 0xffffffffffffffff#64 true true true)).1
    let imulOvf := (execX86Instr (.imul64 .rax .rcx) 0 (mkRflagsTestState 0x8000000000000000#64 0xffffffffffffffff#64 false false false)).1
    let shl65 := (execX86Instr (.shlImm64 .rax 65) 0 (mkRflagsTestState 0x4000000000000000#64 0#64 false false false)).1
    c37.gpr .rax = 0x8000000000000000#64 ∧ c37.gpr .rdx = 0x7fffffffffffffff#64 ∧ c37.flags.cf = true ∧ c37.flags.of = true ∧
    c38.gpr .rax = 0#64 ∧ c38.flags = { cf := true, of := true, zf := true } ∧
    c39.gpr .rax = 0x7fffffff80000000#64 ∧ c39.flags = { cf := false, of := true, zf := false } ∧
    c40.gpr .rax = 0xffffffff80000000#64 ∧ c40.flags = { cf := true, of := false, zf := false } ∧
    c78.gpr .rax = 0#64 ∧ c78.gpr .rdx = 0#64 ∧ c78.flags.cf = false ∧ c78.flags.of = false ∧
    c79.gpr .rax = 0xfffffffffffffffe#64 ∧ c79.flags = { cf := true, of := false, zf := false } ∧
    c80.gpr .rax = 0x4000000000000000#64 ∧ c80.flags = { cf := false, of := true, zf := false } ∧
    c81.gpr .rax = 0x7fffffff80000000#64 ∧ c81.flags = { cf := false, of := true, zf := true } ∧
    imulNoOvf.gpr .rax = 1#64 ∧ imulNoOvf.flags.cf = false ∧ imulNoOvf.flags.of = false ∧
    imulOvf.gpr .rax = 0x8000000000000000#64 ∧ imulOvf.flags.cf = true ∧ imulOvf.flags.of = true ∧
    shl65.gpr .rax = 0x8000000000000000#64 ∧ shl65.flags = { cf := false, of := true, zf := false } := by
  decide +kernel

/-- **Tooth (`ROR` preserves secret `ZF` taint)**: Rotating a public register cannot launder a
    previously secret `ZF` into `.pub` for a subsequent `cmovnz64`. -/
theorem tooth_rorImm64_cannot_launder_secret_zf :
    let τSecretZf : X86TaintState :=
      { gpr := fun _ => .pub, ymm := fun _ => .pub,
        cf := .pub, of := .pub, zf := .sec, doitAssumed := false, upperYmmClean := true }
    checkX86Block true τSecretZf [.rorImm64 .rax 1, .cmovnz64 .rcx .rdx] = none := by
  rfl

/-- **Tooth (Multi-bit shift `OF` architecturally undefined)**: `SHR` with masked count `> 1`
    marks `OF` taint `.sec` even on a `.pub` register, preventing `adox64` from treating
    architecturally undefined `OF` as public! -/
theorem tooth_shrImm64_cnt2_undef_of_tainted_sec :
    let τAllPub : X86TaintState :=
      { gpr := fun _ => .pub, ymm := fun _ => .pub,
        cf := .pub, of := .pub, zf := .pub, doitAssumed := false, upperYmmClean := true }
    (checkX86Instr true τAllPub (.shrImm64 .rax 2)).map X86TaintState.of = some .sec := by
  rfl

end Qsag.ConstantTimeIsa
