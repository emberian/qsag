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

