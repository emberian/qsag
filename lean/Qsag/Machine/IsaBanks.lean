module
public import Qsag.Spec.Refines
public import Qsag.Math.Goldilocks
public import Qsag.Oracle.Keccak
public import Qsag.Math.Gf2Pow128
import Qsag.Tactic.AssuranceKit
public section
namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe
set_option autoImplicit false
set_option maxRecDepth 65536

structure Bank16 (α : Type) where
  r0  : α
  r1  : α
  r2  : α
  r3  : α
  r4  : α
  r5  : α
  r6  : α
  r7  : α
  r8  : α
  r9  : α
  r10 : α
  r11 : α
  r12 : α
  r13 : α
  r14 : α
  r15 : α
  deriving @[expose] DecidableEq, Repr

@[expose] def Bank16.const {α : Type} (v : α) : Bank16 α :=
  ⟨v, v, v, v, v, v, v, v, v, v, v, v, v, v, v, v⟩

@[expose] def Bank16.ofFn {α : Type} (f : Nat → α) : Bank16 α :=
  ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15⟩

@[expose] def Bank16.get {α : Type} (b : Bank16 α) : Nat → α
  | 0  => b.r0  | 1  => b.r1  | 2  => b.r2  | 3  => b.r3
  | 4  => b.r4  | 5  => b.r5  | 6  => b.r6  | 7  => b.r7
  | 8  => b.r8  | 9  => b.r9  | 10 => b.r10 | 11 => b.r11
  | 12 => b.r12 | 13 => b.r13 | 14 => b.r14 | _  => b.r15

@[expose] def Bank16.set {α : Type} (b : Bank16 α) (idx : Nat) (v : α) : Bank16 α :=
  match idx with
  | 0  => { b with r0  := v } | 1  => { b with r1  := v }
  | 2  => { b with r2  := v } | 3  => { b with r3  := v }
  | 4  => { b with r4  := v } | 5  => { b with r5  := v }
  | 6  => { b with r6  := v } | 7  => { b with r7  := v }
  | 8  => { b with r8  := v } | 9  => { b with r9  := v }
  | 10 => { b with r10 := v } | 11 => { b with r11 := v }
  | 12 => { b with r12 := v } | 13 => { b with r13 := v }
  | 14 => { b with r14 := v } | _  => { b with r15 := v }

@[expose] def Bank16.allIdx {α : Type} (p : Nat → α → Bool) (b : Bank16 α) : Bool :=
  p 0 b.r0 && p 1 b.r1 && p 2 b.r2 && p 3 b.r3 &&
  p 4 b.r4 && p 5 b.r5 && p 6 b.r6 && p 7 b.r7 &&
  p 8 b.r8 && p 9 b.r9 && p 10 b.r10 && p 11 b.r11 &&
  p 12 b.r12 && p 13 b.r13 && p 14 b.r14 && p 15 b.r15

/-- Flat 32-slot register bank for `AArch64` `x0..x30` and `v0..v31`. -/
structure Bank32 (α : Type) where
  lo : Bank16 α
  hi : Bank16 α
  deriving @[expose] DecidableEq, Repr

@[expose] def Bank32.const {α : Type} (v : α) : Bank32 α :=
  ⟨Bank16.const v, Bank16.const v⟩

@[expose] def Bank32.ofFn {α : Type} (f : Nat → α) : Bank32 α :=
  ⟨Bank16.ofFn f, Bank16.ofFn (fun i => f (i + 16))⟩

@[expose] def Bank32.get {α : Type} (b : Bank32 α) (idx : Nat) : α :=
  if idx < 16 then b.lo.get idx else b.hi.get (idx - 16)

@[expose] def Bank32.set {α : Type} (b : Bank32 α) (idx : Nat) (v : α) : Bank32 α :=
  if idx < 16 then { b with lo := b.lo.set idx v } else { b with hi := b.hi.set (idx - 16) v }

@[expose] def Bank32.allIdx {α : Type} (p : Nat → α → Bool) (b : Bank32 α) : Bool :=
  b.lo.allIdx p && b.hi.allIdx (fun i v => p (i + 16) v)

/- 128-bit SIMD register (`xmm` / NEON `q` / `v.16b`). -/
end Qsag
