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
    let v := x >>> sh
    let cf := if sh <= 64 then x.getLsbD (sh - 1) else false
    let flags := if sh == 0 then st.flags else
      { cf := cf, of := if sh == 1 then x.getLsbD 63 else false, zf := (v == 0#64) }
    ({ (st.setGpr dst v) with flags := flags }, LeakageEvent.clean pc)
  | .shlImm64 dst sh =>
    let x := st.gpr dst
    let v := x <<< sh
    let cf := if sh <= 64 then x.getLsbD (64 - sh) else false
    let flags := if sh == 0 then st.flags else
      { cf := cf, of := if sh == 1 then (v.getLsbD 63 != cf) else false, zf := (v == 0#64) }
    ({ (st.setGpr dst v) with flags := flags }, LeakageEvent.clean pc)
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
    ({ (st.setGpr dst mask) with flags := { st.flags with zf := !st.flags.cf } },
     LeakageEvent.clean pc)
  | .sbbSelf32Zext dst =>
    let mask := if st.flags.cf then 0x00000000FFFFFFFF#64 else 0#64
    ({ (st.setGpr dst mask) with flags := { st.flags with zf := !st.flags.cf } },
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
    if sh == 0 then some (τ.setGpr dst l)
    else some { (τ.setGpr dst l) with cf := l, of := l, zf := l }
  | .shlImm64 dst sh =>
    let l := τ.gpr dst
    if sh == 0 then some (τ.setGpr dst l)
    else some { (τ.setGpr dst l) with cf := l, of := l, zf := l }
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
    some { (τ.setGpr dst l) with zf := l }
  | .sbbSelf32Zext dst =>
    let l := τ.cf
    some { (τ.setGpr dst l) with zf := l }
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
    by_cases hz : (sh == 0) = true
    · simp [checkX86Instr, hz] at hCheck; subst hCheck
      refine ⟨by simp [execX86Instr, hz], ?_⟩
      simpa [execX86Instr, hz, X86State.setGpr] using
        (x86_setGpr_lowEq memPol τ s₁ s₂ dst (τ.gpr dst)
          (s₁.gpr dst >>> sh) (s₂.gpr dst >>> sh) hLowOrig
          (fun hl => by rw [hgpr dst hl]))
    · simp [checkX86Instr, hz] at hCheck; subst hCheck
      have hSet := x86_setGpr_lowEq memPol τ s₁ s₂ dst (τ.gpr dst)
        (s₁.gpr dst >>> sh) (s₂.gpr dst >>> sh) hLowOrig
        (fun hl => by rw [hgpr dst hl])
      rcases hSet with ⟨hg, hy, _, _, _, hm, hd, hdr, he, hc⟩
      simp only [execX86Instr, hz, Bool.false_eq_true, ↓reduceIte]
      exact ⟨True.intro, hg, hy, (fun hl => by rw [hgpr dst hl]),
        (fun hl => by rw [hgpr dst hl]), (fun hl => by rw [hgpr dst hl]),
        hm, hd, hdr, he, hc⟩
  | shlImm64 dst sh =>
    by_cases hz : (sh == 0) = true
    · simp [checkX86Instr, hz] at hCheck; subst hCheck
      refine ⟨by simp [execX86Instr, hz], ?_⟩
      simpa [execX86Instr, hz, X86State.setGpr] using
        (x86_setGpr_lowEq memPol τ s₁ s₂ dst (τ.gpr dst)
          (s₁.gpr dst <<< sh) (s₂.gpr dst <<< sh) hLowOrig
          (fun hl => by rw [hgpr dst hl]))
    · simp [checkX86Instr, hz] at hCheck; subst hCheck
      have hSet := x86_setGpr_lowEq memPol τ s₁ s₂ dst (τ.gpr dst)
        (s₁.gpr dst <<< sh) (s₂.gpr dst <<< sh) hLowOrig
        (fun hl => by rw [hgpr dst hl])
      rcases hSet with ⟨hg, hy, _, _, _, hm, hd, hdr, he, hc⟩
      simp only [execX86Instr, hz, Bool.false_eq_true, ↓reduceIte]
      exact ⟨True.intro, hg, hy, (fun hl => by rw [hgpr dst hl]),
        (fun hl => by rw [hgpr dst hl]), (fun hl => by rw [hgpr dst hl]),
        hm, hd, hdr, he, hc⟩
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
    rcases hSet with ⟨hg1, hy1, hc1, ho1, _, hm1, hd1, hdr1, hyEq1, hyCl1⟩
    exact ⟨hg1, hy1, hc1, ho1, fun hl => by rw [hcf hl], hm1, hd1, hdr1, hyEq1, hyCl1⟩
  | sbbSelf32Zext dst =>
    simp [checkX86Instr, execX86Instr] at hCheck ⊢; subst hCheck
    have hSet := x86_setGpr_lowEq memPol τ s₁ s₂ dst τ.cf
      (if s₁.flags.cf then 0x00000000FFFFFFFF#64 else 0#64)
      (if s₂.flags.cf then 0x00000000FFFFFFFF#64 else 0#64)
      hLowOrig (fun hl => by rw [hcf hl])
    rcases hSet with ⟨hg1, hy1, hc1, ho1, _, hm1, hd1, hdr1, hyEq1, hyCl1⟩
    exact ⟨hg1, hy1, hc1, ho1, fun hl => by rw [hcf hl], hm1, hd1, hdr1, hyEq1, hyCl1⟩
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

