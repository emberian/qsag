module
public import Qsag.Machine.SpirvKernelSem
public import Qsag.Oracle.Poseidon2
import Qsag.Machine.Tactic.KernelRfl
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag.Spv

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

private abbrev wordBase : Nat := 18446744073709551616
private abbrev limbBase : Nat := 4294967296
private abbrev prime : Nat := 18446744069414584321
def clip (x : Nat) := x % wordBase
private def clip32 (x : Nat) := x % limbBase

/-- Straight-line normal forms. The subscripts are the SSA result IDs. Each load
    and integer operation retains its SPIR-V width conversion. -/
def reduceWord (x : Nat) : Nat :=
  let v67 := decide (18446744069414584321 ≤ (clip x))
  let v69 := bif v67 then 1 else 0
  let v70 := clip (0 + wordBase - clip v69)
  let v71 := 18446744069414584321 &&& v70
  let v72 := clip ((clip x) + wordBase - clip v71)
  v72

def addWords (a b : Nat) : Nat :=
  let v78 := reduceWord (clip a)
  let v82 := reduceWord (clip b)
  let v85 := clip (18446744069414584321 + wordBase - clip (clip v82))
  let v89 := decide ((clip v78) < (clip v85))
  let v90 := bif v89 then 1 else 0
  let v91 := clip (0 + wordBase - clip v90)
  let v94 := clip ((clip v78) + (clip v82))
  let v96 := v94 &&& (clip v91)
  let v99 := clip ((clip v78) + wordBase - clip (clip v85))
  let v101 := wordBase - 1 - clip (clip v91)
  let v102 := v99 &&& v101
  let v103 := v96 ||| v102
  v103

private def subWords (a b : Nat) : Nat :=
  let v109 := reduceWord (clip a)
  let v113 := reduceWord (clip b)
  let v117 := clip ((clip v109) + wordBase - clip (clip v113))
  let v121 := decide ((clip v109) < (clip v113))
  let v122 := bif v121 then 1 else 0
  let v123 := clip (0 + wordBase - clip v122)
  let v124 := 18446744069414584321 &&& v123
  let v125 := clip ((clip v117) + v124)
  v125

def negWord (a : Nat) : Nat :=
  let v131 := subWords 0 (clip a)
  v131

private def reducePair (lo hi : Nat) : Nat :=
  let v137 := (clip hi) &&& 4294967295
  let v142 := (clip hi) >>> 32
  let v145 := clip ((clip v137) <<< 32)
  let v147 := clip (v145 + wordBase - clip (clip v137))
  let v151 := reduceWord (clip lo)
  let v156 := addWords (clip v151) (clip v147)
  let v160 := subWords v156 (clip v142)
  v160

private def wide (a b : Nat) : Nat × Nat :=
  let v173 := (clip a) &&& 4294967295
  let v176 := (clip a) >>> 32
  let v179 := (clip b) &&& 4294967295
  let v182 := (clip b) >>> 32
  let v186 := clip ((clip v173) * (clip v179))
  let v190 := clip ((clip v173) * (clip v182))
  let v194 := clip ((clip v176) * (clip v179))
  let v198 := clip ((clip v176) * (clip v182))
  let v201 := (clip v186) >>> 32
  let v203 := (clip v190) &&& 4294967295
  let v204 := clip (v201 + v203)
  let v206 := (clip v194) &&& 4294967295
  let v207 := clip (v204 + v206)
  let v210 := (clip v186) &&& 4294967295
  let v212 := clip ((clip v207) <<< 32)
  let v213 := v210 ||| v212
  let v217 := (clip v190) >>> 32
  let v218 := clip ((clip v198) + v217)
  let v220 := (clip v194) >>> 32
  let v221 := clip (v218 + v220)
  let v223 := (clip v207) >>> 32
  let v224 := clip (v221 + v223)
  (clip v213, clip v224)

private def multiplyWords (a b : Nat) : Nat :=
  let limbs := wide (reduceWord (clip a)) (reduceWord (clip b))
  reducePair limbs.1 limbs.2

private def squareWord (a : Nat) : Nat :=
  let v236 := multiplyWords (clip a) (clip a)
  v236

def shiftWord (x k : Nat) : Nat :=
  let v241 := clip ((clip x) <<< (clip32 k))
  let v245 := clip32 (64 + limbBase - clip32 (clip32 k))
  let v246 := (clip x) >>> v245
  let v249 := reducePair v241 v246
  v249

def seventhWord (x : Nat) : Nat :=
  let v255 := squareWord (clip x)
  let v261 := multiplyWords (clip v255) (clip x)
  let v265 := squareWord (clip v255)
  let v270 := multiplyWords (clip v261) (clip v265)
  v270

/-- Return projection of an actual invocation of a scalar function. -/
def scalarResult (id : Nat) (args : List Nat) : Option Nat := do
  let w : World Unit := ⟨fun _ _ _ _ => (), fun _ _ _ => (), fun _ _ _ => (),
    fun _ => (), [], fun _ => .undef, fun _ _ _ => .undef⟩
  let (some (.n x), _, _) ← callFn p2 w 0 8 id (args.map Val.n) ⟨[], [], 0⟩ | none
  return x

private theorem reducePair_run (a b : Nat) :
    scalarResult 26 [a,b] = some (reducePair a b) := by kernel_rfl

private theorem multiply_run (a b : Nat) :
    scalarResult 30 [a,b] = some (multiplyWords a b) := by kernel_rfl

private theorem square_run (a : Nat) :
    scalarResult 33 [a] = some (squareWord a) := by kernel_rfl

private theorem shift_run (a k : Nat) :
    scalarResult 40 [a,k] = some (shiftWord a k) := by kernel_rfl

private theorem seventh_run (a : Nat) :
    scalarResult 43 [a] = some (seventhWord a) := by kernel_rfl

private theorem clip_clip (x : Nat) : clip (clip x) = clip x := Nat.mod_mod _ _
private theorem clip_small {x : Nat} (h : x < wordBase) : clip x = x := Nat.mod_eq_of_lt h
private theorem clip_p (x : Nat) : clip (x % prime) = x % prime :=
  clip_small (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide))

local macro "word_omega" : tactic =>
  `(tactic| (simp only [wordBase, prime, limbBase] at *; omega))

private theorem reduceWord_eq (x : Nat) : reduceWord x = clip x % prime := by
  let a := clip x
  have ha : a < wordBase := Nat.mod_lt _ (by decide)
  change clip (a + wordBase - clip (prime &&& clip (0 + wordBase -
    clip (bif decide (prime ≤ a) then 1 else 0)))) = a % prime
  by_cases h : prime ≤ a
  · rw [decide_eq_true h]
    change (a + wordBase - prime) % wordBase = a % prime
    word_omega
  · rw [decide_eq_false h]
    change (a + wordBase - 0) % wordBase = a % prime
    word_omega

private theorem maskWord (x : Nat) : clip x &&& 18446744073709551615 = clip x :=
  (Constructive.and_mask (clip x) 64).trans (clip_clip x)

private theorem addWords_eq (a b : Nat) : addWords a b = (clip a + clip b) % prime := by
  unfold addWords
  simp only [reduceWord_eq, clip_clip, clip_p]
  let x := clip a % prime
  let y := clip b % prime
  have hx : x < prime := Nat.mod_lt _ (by decide)
  have hy : y < prime := Nat.mod_lt _ (by decide)
  have hrem : clip (prime + wordBase - y) = prime - y := by unfold clip; word_omega
  rw [hrem]
  change (clip (x+y) &&& clip (0 + wordBase - clip (bif decide (x < prime - y) then 1 else 0))) |||
    (clip (x + wordBase - (prime-y)) &&& (wordBase - 1 -
    clip (0 + wordBase - clip (bif decide (x < prime - y) then 1 else 0)))) = _
  rw [Nat.add_mod]
  change _ = (x + y) % prime
  by_cases h : x < prime - y
  · rw [decide_eq_true h]
    change (clip (x + y) &&& 18446744073709551615) ||| (_ &&& 0) = _
    rw [maskWord, Nat.and_zero, Nat.or_zero]; unfold clip; word_omega
  · rw [decide_eq_false h]
    change (_ &&& 0) ||| (clip (x + wordBase - (prime-y)) &&& 18446744073709551615) = _
    rw [Nat.and_zero, Nat.zero_or, maskWord]
    unfold clip; word_omega

private theorem subWords_eq (a b : Nat) : subWords a b =
    (clip a % prime + prime - clip b % prime) % prime := by
  unfold subWords
  simp only [reduceWord_eq, clip_clip, clip_p]
  let x := clip a % prime
  let y := clip b % prime
  have hx : x < prime := Nat.mod_lt _ (by decide)
  have hy : y < prime := Nat.mod_lt _ (by decide)
  change clip (clip (x + wordBase - y) +
    (prime &&& clip (0 + wordBase - clip (bif decide (x < y) then 1 else 0)))) = (x + prime - y) % prime
  by_cases h : x < y
  · rw [decide_eq_true h]; change clip (clip (x + wordBase - y) + prime) = _
    unfold clip; word_omega
  · rw [decide_eq_false h]; change clip (clip (x + wordBase - y) + 0) = _
    unfold clip; word_omega


private theorem lowMask (x : Nat) : x &&& 4294967295 = x % limbBase :=
  Constructive.and_mask x 32

private theorem shr (x : Nat) : x >>> 32 = x / limbBase := Nat.shiftRight_eq_div_pow _ _
private theorem shl (x : Nat) : x <<< 32 = x * limbBase := Nat.shiftLeft_eq _ _

private theorem reducePair_eq {lo hi : Nat} (hl : lo < wordBase) (hh : hi < wordBase) :
    reducePair lo hi = (lo + wordBase * hi) % prime := by
  let l := hi % limbBase
  let h := hi / limbBase
  let mid := l * limbBase - l
  have hL : l < limbBase := Nat.mod_lt _ (by decide)
  have hH : h < limbBase := by dsimp [h]; word_omega
  have hmid : mid < wordBase := by dsimp [mid]; word_omega
  have midEq : clip (clip ((clip l) * limbBase) + wordBase - clip (clip l)) = mid := by
    rw [clip_small (show l < wordBase by word_omega)]
    unfold clip mid; word_omega
  unfold reducePair
  simp only [clip_small hh, lowMask, shr, shl]
  change subWords (addWords (clip (reduceWord (clip lo)))
    (clip (clip (clip ((clip l) * limbBase) + wordBase - clip (clip l))))) (clip h) = _
  rw [midEq, subWords_eq, addWords_eq, reduceWord_eq]
  simp only [clip_small hl, clip_p, clip_small hmid,
    clip_small (show h < wordBase by word_omega), Nat.mod_mod]
  rw [Nat.mod_eq_of_lt (show h < prime by word_omega)]
  rw [Nat.mod_add_mod]
  let t := (lo + mid) % prime
  let q := (lo + mid) / prime
  have decomp : t + prime * q = lo + mid := Nat.mod_add_div _ _
  have splitHi : l + limbBase * h = hi := Nat.mod_add_div _ _
  have key : lo + wordBase * hi + prime * 1 =
      (t + prime - h) + prime * (q + l + 4294967297*h) := by
    dsimp only [mid] at decomp; word_omega
  change (t + prime - h) % prime = _
  rw [← Nat.add_mul_mod_self_left (lo + wordBase * hi) prime 1, key, Nat.add_mul_mod_self_left]

private theorem expandProduct (a b c d : Nat) :
    (a + limbBase*b) * (c + limbBase*d) =
      a*c + limbBase*(a*d) + limbBase*(b*c) + wordBase*(b*d) := by
  change _ = a*c + limbBase*(a*d) + limbBase*(b*c) + (limbBase*limbBase)*(b*d)
  simp only [Nat.add_mul, Nat.mul_add]
  ac_rfl

private theorem joinLow {x : Nat} (hx : x < limbBase) (y : Nat) :
    x ||| clip (y * limbBase) = x + limbBase * (y % limbBase) := by
  have e : clip (y * limbBase) = (y % limbBase) <<< 32 := by
    rw [shl, Nat.mul_comm y, Nat.mul_comm (y % limbBase)]
    exact Nat.mul_mod_mul_left limbBase y limbBase
  rw [e, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (i := 32) hx, shl]
  ac_rfl

private theorem wide_exact {a b : Nat} (ha : a < wordBase) (hb : b < wordBase) :
    (wide a b).1 + wordBase * (wide a b).2 = a*b := by
  let al := a % limbBase
  let ah := a / limbBase
  let bl := b % limbBase
  let bh := b / limbBase
  have h0 : al < limbBase := Nat.mod_lt _ (by decide)
  have h1 : ah < limbBase := by dsimp [ah]; word_omega
  have h2 : bl < limbBase := Nat.mod_lt _ (by decide)
  have h3 : bh < limbBase := by dsimp [bh]; word_omega
  have limbClip {n : Nat} (h : n < limbBase) : clip n = n := clip_small (by word_omega)
  let p0 := al*bl
  let p1 := al*bh
  let p2 := ah*bl
  let p3 := ah*bh
  have hp0 : p0 < wordBase := Nat.mul_lt_mul'' h0 h2
  have hp1 : p1 < wordBase := Nat.mul_lt_mul'' h0 h3
  have hp2 : p2 < wordBase := Nat.mul_lt_mul'' h1 h2
  have hp3 : p3 < wordBase := Nat.mul_lt_mul'' h1 h3
  have bound : a*b < wordBase*wordBase := Nat.mul_lt_mul'' ha hb
  have product : a*b = p0 + limbBase*p1 + limbBase*p2 + wordBase*p3 := by
    calc a*b = (al + limbBase*ah)*(bl + limbBase*bh) :=
           by rw [show al + limbBase*ah = a from Nat.mod_add_div _ _, show bl + limbBase*bh = b from Nat.mod_add_div _ _]
         _ = _ := expandProduct _ _ _ _
  let m := p0 / limbBase + p1 % limbBase + p2 % limbBase
  let high := p3 + p1 / limbBase + p2 / limbBase + m / limbBase
  let low := p0 % limbBase + limbBase*(m % limbBase)
  have recombine : low + wordBase*high = a*b := by
    dsimp only [low,high,m]; word_omega
  have hhi : high < wordBase := by word_omega
  have hlo : low < wordBase := by dsimp only [low]; word_omega
  have hm : m < wordBase := by dsimp only [m]; word_omega
  have pstep : p0 / limbBase + p1 % limbBase < wordBase := by dsimp only [m] at hm; omega
  have hstep : p3 + p1 / limbBase < wordBase := by dsimp only [high] at hhi; word_omega
  have hstep' : p3 + p1 / limbBase + p2 / limbBase < wordBase := by dsimp only [high] at hhi; word_omega
  dsimp only [al,ah,bl,bh] at h0 h1 h2 h3
  dsimp only [p0,p1,p2,p3,al,ah,bl,bh] at hp0 hp1 hp2 hp3
  dsimp only [low,high,m,p0,p1,p2,p3,al,ah,bl,bh] at hlo hhi hm hstep hstep' pstep
  unfold wide
  simp only [clip_small ha, clip_small hb, lowMask, shr, shl,
    limbClip h0, limbClip h1, limbClip h2, limbClip h3, clip_small hp0,
    clip_small hp1, clip_small hp2, clip_small hp3, clip_small pstep, clip_small hm,
    clip_small hstep, clip_small hstep', clip_small hhi]
  change clip (p0 % limbBase ||| clip (m * limbBase)) + wordBase*high = _
  rw [joinLow (Nat.mod_lt _ (by decide : 0 < limbBase)), clip_small (show p0 % limbBase + limbBase*(m%limbBase) < wordBase from hlo)]
  exact recombine

/-- Run the inline multiply slice starting at the loads of the two reduced operands
    (%163 and %167). Intercept its final call to reduce128 and return both arguments. -/
def inlineWideOperands (a b : UInt64) : Option (Nat × Nat) := do
  let f ← callBody.findFn 30 p2.functions
  let (_, code) ← f.blocks.head?
  let slots := code.filterMap fun i => match i.op, i.args with
    | 59, [_, k, 7] => some (k, (Val.undef : Val Unit))
    | _, _ => none
  let fr : Frame Unit := ⟨put 163 (.n a.toNat) (put 167 (.n b.toNat) slots), []⟩
  let w : World Unit := ⟨fun _ _ _ _ => (), fun _ _ _ => (), fun _ _ _ => (),
    fun _ => (), [], fun _ => .undef, fun _ _ _ => .undef⟩
  let capture : CallFn Unit := fun id args g =>
    if id = 26 then some (some (.arr args), args, g) else none
  let code := code.dropWhile fun i => !(i.op == 61 && i.args == [6,172,163])
  let (some (.arr [.n lo, .n hi]), _, _) ←
    run p2 w capture (fun _ _ _ => none) code fr ⟨[], [], 0⟩ | none
  return (lo, hi)

theorem spirv_u64_mul_hilo_exact (a b : UInt64) :
    ∃ lo hi, inlineWideOperands a b = some (lo,hi) ∧ lo + 2^64*hi = a.toNat*b.toNat := by
  refine ⟨(wide a.toNat b.toNat).1, (wide a.toNat b.toNat).2, ?_, wide_exact a.toNat_lt b.toNat_lt⟩
  kernel_rfl

theorem spirv_fp_reduce128_refines_goldilocks (lo hi : UInt64) :
    scalarResult 26 [lo.toNat,hi.toNat] =
      some (Goldilocks.ofNat (lo.toNat + 2^64 * hi.toNat)).val := by
  rw [reducePair_run, reducePair_eq lo.toNat_lt hi.toNat_lt, Goldilocks.ofNat_val]
  rfl

private theorem mul_eq (a b : Nat) : multiplyWords a b = (clip a * clip b) % prime := by
  unfold multiplyWords
  simp only [reduceWord_eq, clip_clip]
  let x := clip a % prime
  let y := clip b % prime
  have hx : x < wordBase := Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide : prime < wordBase)
  have hy : y < wordBase := Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide : prime < wordBase)
  have hl : (wide x y).1 < wordBase := Nat.mod_lt _ (by decide)
  have hh : (wide x y).2 < wordBase := Nat.mod_lt _ (by decide)
  rw [reducePair_eq hl hh, wide_exact hx hy, ← Nat.mul_mod]

theorem spirv_fp_mul_refines_goldilocks (a b : UInt64) :
    scalarResult 30 [a.toNat,b.toNat] =
      some (Goldilocks.mul (Goldilocks.ofNat a.toNat) (Goldilocks.ofNat b.toNat)).val := by
  rw [multiply_run, mul_eq, clip_small a.toNat_lt, clip_small b.toNat_lt, Goldilocks.mul_val,
      Goldilocks.ofNat_val, Goldilocks.ofNat_val, ← Nat.mul_mod]
  rfl

theorem spirv_fp_sq_refines_goldilocks (a : UInt64) :
    scalarResult 33 [a.toNat] = some ((a.toNat * a.toNat) % goldilocksPrime) := by
  rw [square_run]; unfold squareWord
  rw [mul_eq, clip_clip, clip_small a.toNat_lt]; rfl

/-- The two shifts in %40 are defined for 1 through 63; the shader uses this
    helper to multiply a field element by a small power of two. -/
theorem spirv_fp_shift_refines_goldilocks (a : UInt64) (k : Fin 63) :
    scalarResult 40 [a.toNat,k.val+1] = some ((a.toNat * 2^(k.val+1)) % goldilocksPrime) := by
  generalize h : k.val+1 = shift
  have hk' : shift < 64 := by have := k.isLt; omega
  rw [shift_run]
  unfold shiftWord
  dsimp only
  have k32 : clip32 shift = shift := Nat.mod_eq_of_lt (by word_omega)
  have ks : clip32 (64 + limbBase - shift) = 64 - shift := by unfold clip32; word_omega
  rw [clip_small a.toNat_lt, k32, k32, ks, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have hh : a.toNat / 2^(64-shift) < wordBase := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) a.toNat_lt
  rw [reducePair_eq (show clip (a.toNat * 2^shift) < wordBase from Nat.mod_lt _ (by decide)) hh]
  have base : wordBase = 2^(64-shift) * 2^shift := by
    rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hk')]
  have div : (a.toNat * 2^shift) / wordBase = a.toNat / 2^(64-shift) := by
    rw [base, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos shift)]
  rw [← div]
  change some (((a.toNat * 2^shift) % wordBase + wordBase * ((a.toNat * 2^shift) / wordBase)) % prime) = _
  rw [Nat.mod_add_div]; rfl

private theorem pow7 (x : Nat) :
    ((x*x*x)*(x*x*(x*x))) = x^7 := by simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]; ac_rfl

private theorem seventh_eq (x : Nat) : seventhWord x = ((clip x)^7) % prime := by
  unfold seventhWord squareWord
  simp only [mul_eq, clip_clip, clip_p, Nat.mod_mul_mod, Nat.mul_mod_mod, pow7]

theorem spirv_sbox7_refines_goldilocks (x : UInt64) :
    scalarResult 43 [x.toNat] = some (x.toNat ^ 7 % goldilocksPrime) := by
  rw [seventh_run, seventh_eq, clip_small x.toNat_lt]; rfl


-- Scalar call acceleration preserves the return value, copy-out parameters and entire log.
-- Each clause below is a conversion theorem on the actual instruction stream.
private def recordCall (ls : List Nat) (r : Nat) (args : List (Val Unit)) (g : Glob Unit) :
    Option (Option (Val Unit) × List (Val Unit) × Glob Unit) :=
  some (some (.n r), args, {g with evs := ls.map Ev.blk ++ g.evs})

private def scalarFast (fallback : CallFn Unit) : CallFn Unit := fun id args g =>
  match id, args with
  | 10, [.n x] => recordCall [11] (reduceWord x) [.n x] g
  | 15, [.n x, .n y] => recordCall [11,11,16] (addWords x y) [.n x, .n y] g
  | 19, [.n x, .n y] => recordCall [11,11,20] (subWords x y) [.n x, .n y] g
  | 22, [.n x] => recordCall [11,11,20,23] (negWord x) [.n x] g
  | 26, [.n x, .n y] => recordCall [11,11,20,11,11,16,11,27] (reducePair x y) [.n x, .n y] g
  | 30, [.n x, .n y] => recordCall [11,11,20,11,11,16,11,27,11,11,31] (multiplyWords x y) [.n x, .n y] g
  | 33, [.n x] => recordCall [11,11,20,11,11,16,11,27,11,11,31,34] (squareWord x) [.n x] g
  | 40, [.n x, .n y] => recordCall [11,11,20,11,11,16,11,27,41] (shiftWord x y) [.n x, .n y] g
  | 43, [.n x] => recordCall [11,11,20,11,11,16,11,27,11,11,31,11,11,20,11,11,16,11,27,11,11,31,34,11,11,20,11,11,16,11,27,11,11,31,11,11,20,11,11,16,11,27,11,11,31,34,44] (seventhWord x) [.n x] g
  | _, _ => fallback id args g

private theorem scalarFast_correct (w : World Unit) (bf depth : Nat) :
    scalarFast (callFn p2 w bf (depth + 8)) = callFn p2 w bf (depth + 8) := by
  funext fid args g
  unfold scalarFast
  split <;> kernel_rfl

private def fastCalls (w : World Unit) (bf : Nat) : Nat → CallFn Unit
  | 0 => scalarFast (callFn p2 w bf 8)
  | d+1 => scalarFast (callBody p2 w bf (fastCalls w bf d))

private theorem fastCalls_correct (w : World Unit) (bf d : Nat) :
    fastCalls w bf d = callFn p2 w bf (d + 8) := by
  induction d with
  | zero => exact scalarFast_correct w bf 0
  | succ d ih =>
    unfold fastCalls
    rw [ih]
    exact scalarFast_correct w bf (d+1)

private def katWorld (input : Nat → Nat) : World Unit where
  secBin _ _ _ _ := ()
  secUn _ _ _ := ()
  secSel _ _ _ := ()
  inj _ := ()
  pc := [.n 1, .n 0, .n 0, .n 0]
  builtin k := if k = 28 then .arr [.n 0, .n 0, .n 0] else .undef
  load r path _ := match r, path with
    | 601, [0, k] => .n (input k)
    | _, _ => .undef

/-- Preserve the root, full access path, value, order and multiplicity of every store. -/
private def stores (result : Option (Option (Val Unit) × List (Val Unit) × Glob Unit)) :
    Option (List (Nat × List Nat × Nat)) := do
  let (_, _, g) ← result
  g.outs.reverse.mapM fun (r,p,v) => match v with
    | .n x => some (r,p,x)
    | _ => none

def expectedStores (xs : List Nat) := xs.zipIdx.map fun (x,k) => (601, [0,k], x)

def katWords : List Nat :=
  [17528629447354354351,5014055130248055117,10679077121839038553,431078547345611051,
   7807009921345120310,2413869689279715014,11875300792986830377,1872634884137602556,
   15069512080271275672,14253608580209913153,14550618143248480092,107036164978639472]

private def zeroKat := katWorld (fun _ => 0)

private def countingWords : List Nat :=
  [13782584570844608145,13136387643152332171,7171133015474200819,7643370872200861694,
   14144755201299840503,16470027036684692562,1748465969625202405,1718729118078964347,
   6141020819996733037,16322330185628708898,11650380702735067362,2734959974607798415]

def countingState : Poseidon2State12 :=
  ⟨⟨Goldilocks.ofNat 0, Goldilocks.ofNat 1, Goldilocks.ofNat 2, Goldilocks.ofNat 3⟩,
   ⟨Goldilocks.ofNat 4, Goldilocks.ofNat 5, Goldilocks.ofNat 6, Goldilocks.ofNat 7⟩,
   ⟨Goldilocks.ofNat 8, Goldilocks.ofNat 9, Goldilocks.ofNat 10, Goldilocks.ofNat 11⟩⟩

private theorem fastKat : stores (fastCalls zeroKat 1100 4 p2.entry [] ⟨[], [], 0⟩) =
    some (expectedStores katWords) := by kernel_rfl

private theorem fastCounting : stores (fastCalls (katWorld id) 1100 4 p2.entry [] ⟨[], [], 0⟩) =
    some (expectedStores countingWords) := by kernel_rfl

/-- Observe every destination and value in store order. -/
def poseidonEntryStores (img : Image) (input : Nat → Nat) :=
  stores (callFn img (katWorld input) 1100 12 img.entry [] ⟨[], [], 0⟩)

private theorem zeroOracle : (poseidon2Perm12 state12Zero).toList.map (·.val) = katWords :=
  poseidon2Perm12_zero_kat

private theorem entry_eq_fast (input : Nat → Nat) :
    poseidonEntryStores p2 input = stores (fastCalls (katWorld input) 1100 4 p2.entry [] ⟨[], [], 0⟩) :=
  (congrArg (fun call : CallFn Unit => stores (call p2.entry [] ⟨[],[],0⟩))
    (fastCalls_correct (katWorld input) 1100 4)).symm

theorem spirv_poseidon2_perm12_entry_kat_and_equiv :
    decode poseidon2Perm12SpvWords = some p2 ∧
    poseidonEntryStores p2 (fun _ => 0) =
      some (expectedStores ((poseidon2Perm12 state12Zero).toList.map (·.val))) ∧
    poseidonEntryStores p2 id =
      some (expectedStores ((poseidon2Perm12 countingState).toList.map (·.val))) := by
  have counting : (poseidon2Perm12 countingState).toList.map (·.val) = countingWords :=
    poseidon2Perm12_counting_kat
  let want := fun xs => some (expectedStores xs)
  exact ⟨p2_decoded, (entry_eq_fast _).trans (fastKat.trans (congrArg want zeroOracle.symm)),
    (entry_eq_fast _).trans (fastCounting.trans (congrArg want counting.symm))⟩

/-- A consumer expecting the twelve outputs at the wrong storage root fails the KAT. -/
theorem poseidon_wrong_binding_rejected :
    ¬ poseidonEntryStores p2 (fun _ => 0) = some (katWords.zipIdx.map fun (x,k) => (600,[0,k],x)) := by
  intro wrong
  have correct := spirv_poseidon2_perm12_entry_kat_and_equiv.2.1.trans
    (congrArg (fun xs => some (expectedStores xs)) zeroOracle)
  have mismatch : some (expectedStores katWords) ≠
      some (katWords.zipIdx.map fun (x,k) => (600,[0,k],x)) := by decide
  exact mismatch (correct.symm.trans wrong)

#tooth_pair spirv_poseidon2_perm12_entry_kat_and_equiv vs poseidon_wrong_binding_rejected

#print axioms p2_decoded
#print axioms spirv_u64_mul_hilo_exact
#print axioms spirv_fp_reduce128_refines_goldilocks
#print axioms spirv_fp_mul_refines_goldilocks
#print axioms spirv_fp_sq_refines_goldilocks
#print axioms spirv_fp_shift_refines_goldilocks
#print axioms spirv_sbox7_refines_goldilocks
#print axioms spirv_poseidon2_perm12_entry_kat_and_equiv
#print axioms poseidon_wrong_binding_rejected

namespace Universal
-- Serialize the large kernel reductions for the decoded round path.
set_option Elab.async false
set_option maxHeartbeats 8000000

/- Fixed-width register tuples. Making each projection explicit keeps symbolic
   reduction of the evaluator independent of the field arithmetic. -/
structure W4 where
  w0 : Nat
  w1 : Nat
  w2 : Nat
  w3 : Nat
def W4.vals (x : W4) : List (Val Unit) :=
  [.n x.w0, .n x.w1, .n x.w2, .n x.w3]
structure W12 where
  w0 : Nat
  w1 : Nat
  w2 : Nat
  w3 : Nat
  w4 : Nat
  w5 : Nat
  w6 : Nat
  w7 : Nat
  w8 : Nat
  w9 : Nat
  w10 : Nat
  w11 : Nat
private def W12.vals (x : W12) : List (Val Unit) :=
  [.n x.w0, .n x.w1, .n x.w2, .n x.w3, .n x.w4, .n x.w5, .n x.w6, .n x.w7, .n x.w8, .n x.w9, .n x.w10, .n x.w11]
def W12.words (x : W12) : List Nat :=
  [x.w0, x.w1, x.w2, x.w3, x.w4, x.w5, x.w6, x.w7, x.w8, x.w9, x.w10, x.w11]

/-- Word operations and pointer copy-outs of %50, in instruction order. -/
def matrix4 (add : Nat → Nat → Nat) (x : W4) : W4 :=
  let addOut1 := add (clip x.w0) (clip x.w1)
  let addOut2 := add (clip x.w2) (clip x.w3)
  let addOut3 := add addOut1 addOut2
  let addOut4 := add (clip x.w1) (clip x.w1)
  let addOut5 := add (clip x.w0) addOut4
  let addOut6 := add (clip addOut3) addOut5
  let addOut7 := add (clip x.w2) (clip x.w2)
  let addOut8 := add (clip x.w1) addOut7
  let addOut9 := add (clip addOut3) addOut8
  let addOut10 := add (clip x.w3) (clip x.w3)
  let addOut11 := add (clip x.w2) addOut10
  let addOut12 := add (clip addOut3) addOut11
  let addOut13 := add (clip x.w0) (clip x.w0)
  let addOut14 := add (clip x.w3) addOut13
  let addOut15 := add (clip addOut3) addOut14
  ⟨(clip addOut6), (clip addOut9), (clip addOut12), (clip addOut15)⟩

/-- Word operations and pointer copy-outs of %57, in instruction order. -/
def externalLayer (red : Nat → Nat) (add : Nat → Nat → Nat) (m4 : W4 → W4) (x : W12) : W12 :=
  let redOut1 := red (clip x.w0)
  let redOut2 := red (clip x.w1)
  let redOut3 := red (clip x.w2)
  let redOut4 := red (clip x.w3)
  let redOut5 := red (clip x.w4)
  let redOut6 := red (clip x.w5)
  let redOut7 := red (clip x.w6)
  let redOut8 := red (clip x.w7)
  let redOut9 := red (clip x.w8)
  let redOut10 := red (clip x.w9)
  let redOut11 := red (clip x.w10)
  let redOut12 := red (clip x.w11)
  let b13 := m4 ⟨(clip redOut1), (clip redOut4), (clip redOut7), (clip redOut10)⟩
  let b14 := m4 ⟨(clip redOut2), (clip redOut5), (clip redOut8), (clip redOut11)⟩
  let b15 := m4 ⟨(clip redOut3), (clip redOut6), (clip redOut9), (clip redOut12)⟩
  let addOut16 := add (clip (clip b13.w0)) (clip (clip b14.w0))
  let addOut17 := add addOut16 (clip (clip b15.w0))
  let addOut18 := add (clip (clip b13.w0)) (clip addOut17)
  let addOut19 := add (clip (clip b14.w0)) (clip addOut17)
  let addOut20 := add (clip (clip b15.w0)) (clip addOut17)
  let addOut21 := add (clip (clip b13.w1)) (clip (clip b14.w1))
  let addOut22 := add addOut21 (clip (clip b15.w1))
  let addOut23 := add (clip (clip b13.w1)) (clip addOut22)
  let addOut24 := add (clip (clip b14.w1)) (clip addOut22)
  let addOut25 := add (clip (clip b15.w1)) (clip addOut22)
  let addOut26 := add (clip (clip b13.w2)) (clip (clip b14.w2))
  let addOut27 := add addOut26 (clip (clip b15.w2))
  let addOut28 := add (clip (clip b13.w2)) (clip addOut27)
  let addOut29 := add (clip (clip b14.w2)) (clip addOut27)
  let addOut30 := add (clip (clip b15.w2)) (clip addOut27)
  let addOut31 := add (clip (clip b13.w3)) (clip (clip b14.w3))
  let addOut32 := add addOut31 (clip (clip b15.w3))
  let addOut33 := add (clip (clip b13.w3)) (clip addOut32)
  let addOut34 := add (clip (clip b14.w3)) (clip addOut32)
  let addOut35 := add (clip (clip b15.w3)) (clip addOut32)
  ⟨addOut18, addOut19, addOut20, addOut23, addOut24, addOut25, addOut28, addOut29, addOut30, addOut33, addOut34, addOut35⟩

/-- Word operations and pointer copy-outs of %60, in instruction order. -/
def internalLayer (add shift : Nat → Nat → Nat) (neg : Nat → Nat) (x : W12) : W12 :=
  let addOut1 := add 0 (clip x.w0)
  let addOut2 := add (clip addOut1) (clip x.w1)
  let addOut3 := add (clip addOut2) (clip x.w2)
  let addOut4 := add (clip addOut3) (clip x.w3)
  let addOut5 := add (clip addOut4) (clip x.w4)
  let addOut6 := add (clip addOut5) (clip x.w5)
  let addOut7 := add (clip addOut6) (clip x.w6)
  let addOut8 := add (clip addOut7) (clip x.w7)
  let addOut9 := add (clip addOut8) (clip x.w8)
  let addOut10 := add (clip addOut9) (clip x.w9)
  let addOut11 := add (clip addOut10) (clip x.w10)
  let addOut12 := add (clip addOut11) (clip x.w11)
  let shiftOut13 := shift (clip x.w0) 6
  let negOut14 := neg shiftOut13
  let addOut15 := add negOut14 (clip addOut12)
  let addOut16 := add (clip x.w1) (clip addOut12)
  let shiftOut17 := shift (clip x.w2) 1
  let addOut18 := add shiftOut17 (clip addOut12)
  let shiftOut19 := shift (clip x.w3) 2
  let addOut20 := add shiftOut19 (clip addOut12)
  let shiftOut21 := shift (clip x.w4) 3
  let addOut22 := add shiftOut21 (clip addOut12)
  let shiftOut23 := shift (clip x.w5) 4
  let addOut24 := add shiftOut23 (clip addOut12)
  let shiftOut25 := shift (clip x.w6) 5
  let addOut26 := add shiftOut25 (clip addOut12)
  let shiftOut27 := shift (clip x.w7) 6
  let addOut28 := add shiftOut27 (clip addOut12)
  let shiftOut29 := shift (clip x.w8) 7
  let addOut30 := add shiftOut29 (clip addOut12)
  let shiftOut31 := shift (clip x.w9) 8
  let addOut32 := add shiftOut31 (clip addOut12)
  let shiftOut33 := shift (clip x.w10) 9
  let addOut34 := add shiftOut33 (clip addOut12)
  let shiftOut35 := shift (clip x.w11) 10
  let addOut36 := add shiftOut35 (clip addOut12)
  ⟨addOut15, addOut16, addOut18, addOut20, addOut22, addOut24, addOut26, addOut28, addOut30, addOut32, addOut34, addOut36⟩

abbrev rawM4 := matrix4 addWords
abbrev rawME := externalLayer reduceWord addWords rawM4
abbrev rawMI := internalLayer addWords shiftWord negWord

/-- Static block traces in execution order. Helper summaries prepend
    them in reverse order because the evaluator stores the newest event first. -/
private def addTrace := [16,11,11]
private def shiftTrace := [41,27,11,16,11,11,20,11,11]
private def repeated (n : Nat) (ls : List Nat) := (List.replicate n ls).flatten
private def matrixTrace := [51] ++ repeated 15 addTrace
private def prependTrace (ls : List Nat) (es : List Ev) := ls.reverse.map Ev.blk ++ es
private abbrev log50 := prependTrace matrixTrace
private theorem call50 (w : World Unit) (depth : Nat) (x : W4) (g : Glob Unit) :
  callFn p2 w 1100 (depth + 8) 50 x.vals g =
    some (none, (rawM4 x).vals, {g with evs := log50 g.evs}) := by kernel_rfl
private def log57 := prependTrace
  ([58] ++ repeated 12 [349,353,350,11,352] ++ [349,353,351] ++ repeated 3 matrixTrace ++
    repeated 4 ([441,445,442] ++ repeated 5 addTrace ++ [444]) ++ [441,445,443])
private theorem call57 (w : World Unit) (depth : Nat) (x : W12) (g : Glob Unit) :
  callFn p2 w 1100 (depth + 8) 57 [.arr x.vals] g =
    some (none, [.arr (rawME x).vals], {g with evs := log57 g.evs}) := by kernel_rfl
private def log60 := prependTrace
  ([61] ++ repeated 12 ([504,508,505] ++ addTrace ++ [507]) ++ [504,508,506] ++
    shiftTrace ++ [23,20,11,11] ++ repeated 2 addTrace ++
    repeated 10 ([541,545,542] ++ shiftTrace ++ addTrace ++ [544]) ++ [541,545,543])
private theorem call60 (w : World Unit) (depth : Nat) (x : W12) (g : Glob Unit) :
  callFn p2 w 1100 (depth + 8) 60 [.arr x.vals] g =
    some (none, [.arr (rawMI x).vals], {g with evs := log60 g.evs}) := by kernel_rfl

def laneWords (b : Lane4) : W4 := ⟨b.x0.val, b.x1.val, b.x2.val, b.x3.val⟩
def stateWords (s : Poseidon2State12) : W12 :=
  ⟨s.b0.x0.val, s.b0.x1.val, s.b0.x2.val, s.b0.x3.val,
   s.b1.x0.val, s.b1.x1.val, s.b1.x2.val, s.b1.x3.val,
   s.b2.x0.val, s.b2.x1.val, s.b2.x2.val, s.b2.x3.val⟩

private def entryCalls (fallback : CallFn Unit) (add : Nat → Nat → Nat)
    (box : Nat → Nat) (me mi : W12 → W12) : CallFn Unit := fun fid args g =>
  match fid, args with
  | 15, [.n x,.n y] => recordCall [11,11,16] (add x y) [.n x,.n y] g
  | 43, [.n x] => recordCall
    [11,11,20,11,11,16,11,27,11,11,31,11,11,20,11,11,16,11,27,11,11,31,34,
     11,11,20,11,11,16,11,27,11,11,31,11,11,20,11,11,16,11,27,11,11,31,34,44]
    (box x) [.n x] g
  | 57, [.arr [.n x0, .n x1, .n x2, .n x3, .n x4, .n x5, .n x6, .n x7, .n x8, .n x9, .n x10, .n x11]] =>
    some (none, [.arr (me ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11⟩).vals], {g with evs := log57 g.evs})
  | 60, [.arr [.n x0, .n x1, .n x2, .n x3, .n x4, .n x5, .n x6, .n x7, .n x8, .n x9, .n x10, .n x11]] =>
    some (none, [.arr (mi ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11⟩).vals], {g with evs := log60 g.evs})
  | _, _ => fallback fid args g

private theorem entryCalls_eq (w : World Unit) :
    entryCalls (callFn p2 w 1100 11) addWords seventhWord rawME rawMI = callFn p2 w 1100 11 := by
  funext fid args g
  unfold entryCalls
  split
  · kernel_rfl
  · kernel_rfl
  · exact (call57 w 3 _ g).symm
  · exact (call60 w 3 _ g).symm
  · rfl

def wordExternal (add : Nat → Nat → Nat) (box : Nat → Nat) (me : W12 → W12)
    (rc : Poseidon2State12) (x : W12) : W12 :=
  let r := stateWords rc
  me
    ⟨box (add (clip x.w0) r.w0), box (add (clip x.w1) r.w1),
     box (add (clip x.w2) r.w2), box (add (clip x.w3) r.w3),
     box (add (clip x.w4) r.w4), box (add (clip x.w5) r.w5),
     box (add (clip x.w6) r.w6), box (add (clip x.w7) r.w7),
     box (add (clip x.w8) r.w8), box (add (clip x.w9) r.w9),
     box (add (clip x.w10) r.w10), box (add (clip x.w11) r.w11)⟩

def wordInternal (add : Nat → Nat → Nat) (box : Nat → Nat) (mi : W12 → W12)
    (rc : Goldilocks) (x : W12) : W12 :=
  mi { x with w0 := box (add (clip x.w0) rc.val) }

def wordRounds (add : Nat → Nat → Nat) (box : Nat → Nat) (me mi : W12 → W12)
    (input : Nat → Nat) : W12 :=
  let start := me
    ⟨clip (input 0), clip (input 1), clip (input 2), clip (input 3),
     clip (input 4), clip (input 5), clip (input 6), clip (input 7),
     clip (input 8), clip (input 9), clip (input 10), clip (input 11)⟩
  let initial := runRounds (wordExternal add box me) poseidon2InitialExtConsts start
  let middle := runRounds (wordInternal add box mi) poseidon2InternalConsts initial
  runRounds (wordExternal add box me) poseidon2TerminalExtConsts middle

/-- Kernel-computable round constants certified by the oracle's public equations. -/
private def constantEvaluator :
    { f : Nat → Nat → Nat → Goldilocks // ∀ t r i, poseidon2ConstAt t r i = f t r i } :=
  ⟨_, fun t r i => by simp only [poseidon2ConstAt_eq, splitMix64Mix_eq]; rfl⟩

private def externalConstantEvaluator :
    { f : Nat → Nat → Poseidon2State12 // ∀ t r, poseidon2ExtRoundConst t r = f t r } :=
  ⟨_, fun t r => by simp only [poseidon2ExtRoundConst.public_eqs, constantEvaluator.property]; rfl⟩

/-- Keep the fold intact while checking the decoded control flow on symbolic words. -/
private def evaluatedRounds (add : Nat → Nat → Nat) (box : Nat → Nat) (me mi : W12 → W12)
    (input : Nat → Nat) : { x : W12 // wordRounds add box me mi input = x } :=
  ⟨_, by
    have extEq : poseidon2ExtRoundConst = externalConstantEvaluator.val :=
      funext fun t => funext (externalConstantEvaluator.property t)
    simp only [wordRounds, runRounds_eq_foldl, poseidon2InitialExtConsts.public_eqs,
      poseidon2InternalConsts.public_eqs, poseidon2TerminalExtConsts.public_eqs, extEq,
      constantEvaluator.property]
    rfl⟩

/-- Symbolic control-flow reduction of %4. The four call results are variables
    while the kernel checks every branch, round constant, array subscript and store. -/
private theorem entryControl (input : Nat → Nat) (fallback : CallFn Unit)
    (add : Nat → Nat → Nat) (box : Nat → Nat) (me mi : W12 → W12) :
    stores (callBody p2 (katWorld input) 1100 (entryCalls fallback add box me mi)
      p2.entry [] ⟨[],[],0⟩) =
    some (expectedStores ((wordRounds add box me mi input).words.map clip)) := by
  let result := evaluatedRounds add box me mi input
  let observed := fun x : W12 => some (expectedStores (x.words.map clip))
  have control : stores (callBody p2 (katWorld input) 1100 (entryCalls fallback add box me mi)
      p2.entry [] ⟨[],[],0⟩) = observed result.val := by kernel_rfl
  exact control.trans (congrArg observed result.property.symm)

theorem clipField (x : Goldilocks) : clip x.val = x.val :=
  Nat.mod_eq_of_lt x.val_lt_two_pow_64

private theorem primeEq : prime = goldilocksPrime := rfl

theorem redField (x : Goldilocks) : reduceWord x.val = x.val := by
  rw [reduceWord_eq, clipField, primeEq, Nat.mod_eq_of_lt x.isLt]

theorem addField (x y : Goldilocks) : addWords x.val y.val = (x.add y).val := by
  rw [addWords_eq, clipField, clipField, primeEq, Goldilocks.add_val]

theorem addZero (x : Goldilocks) : addWords 0 x.val = x.val := by
  rw [addWords_eq, clipField, primeEq]
  change (0 + x.val) % goldilocksPrime = x.val
  rw [Nat.zero_add, Nat.mod_eq_of_lt x.isLt]

theorem negField (x : Goldilocks) : negWord x.val = x.neg.val := by
  change subWords 0 (clip x.val) = x.neg.val
  rw [subWords_eq, clipField, clipField, primeEq, Nat.mod_eq_of_lt x.isLt, Goldilocks.neg_val]
  rfl

theorem boxField (x : Goldilocks) : seventhWord x.val = (sbox7 x).val := by
  rw [seventh_eq, clipField, primeEq, sbox7_val]

theorem shiftField (x : Goldilocks) (k : Nat) (hk : 1 ≤ k ∧ k ≤ 63) :
    shiftWord x.val k = ((Goldilocks.ofNat (2^k)).mul x).val := by
  let u := UInt64.ofNat x.val
  have hu : u.toNat = x.val := Nat.mod_eq_of_lt x.val_lt_two_pow_64
  let i : Fin 63 := ⟨k-1, by omega⟩
  have hi : i.val + 1 = k := by dsimp [i]; omega
  have h := spirv_fp_shift_refines_goldilocks u i
  rw [shift_run, hu, hi] at h
  rw [Option.some.inj h, Goldilocks.mul_val, Goldilocks.ofNat_val, Nat.mod_mul_mod, Nat.mul_comm]


theorem call_m4_words (w : World Unit) (b : Lane4) (g : Glob Unit) :
    (callFn p2 w 1100 8 50 [.n b.x0.val,.n b.x1.val,.n b.x2.val,.n b.x3.val] g).map
      (fun r => r.2.1) = some (rawM4 (laneWords b)).vals := by
  let project (result : Option (Option (Val Unit) × List (Val Unit) × Glob Unit)) :=
    result.map (fun r => r.2.1)
  have h := congrArg project (call50 w 0 (laneWords b) g)
  exact h

theorem entry_word_rounds (input : Nat → Nat) :
    poseidonEntryStores p2 input =
      some (expectedStores ((wordRounds addWords seventhWord rawME rawMI input).words.map clip)) := by
  let w := katWorld input
  let observe (call : CallFn Unit) := stores (callBody p2 w 1100 call p2.entry [] ⟨[],[],0⟩)
  have control := entryControl input (callFn p2 w 1100 11) addWords seventhWord rawME rawMI
  have folded := (congrArg observe (entryCalls_eq w).symm).trans control
  exact folded

#export_eqns W4.vals W12.words matrix4 externalLayer internalLayer laneWords stateWords
#export_eqns wordExternal wordInternal wordRounds

end Universal
end Qsag.Spv
end
