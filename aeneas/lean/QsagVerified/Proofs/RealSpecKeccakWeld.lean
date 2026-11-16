module
import all QsagVerified.Funs
public import QsagVerified.Proofs.Sponge
public import Qsag.Oracle.Keccak

/-!
The universal theorem here covers the extracted 24-round permutation. The phase laws
below cover actual streaming entry points, but do not yet identify emitted bytes with
`Qsag.shake256Xof`: rate-block XOR, padding, and arbitrary squeeze-loop invariants remain
necessary. Absorption after squeezing fails with `.fail .assertionFailure` in the
generated API; repeated finalization after squeezing leaves the state unchanged.
-/

public section
namespace qsag_verified.proofs
open Aeneas Aeneas.Std Result
open qsag_verified
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- Exact lane order shared by the extracted array and the canonical Keccak state. -/
def keccakArrayOfState (s : Qsag.KState) : Array Std.U64 25#usize :=
  Array.make 25#usize [⟨s.a0.toBitVec⟩, ⟨s.a1.toBitVec⟩, ⟨s.a2.toBitVec⟩, ⟨s.a3.toBitVec⟩, ⟨s.a4.toBitVec⟩, ⟨s.a5.toBitVec⟩, ⟨s.a6.toBitVec⟩, ⟨s.a7.toBitVec⟩, ⟨s.a8.toBitVec⟩, ⟨s.a9.toBitVec⟩, ⟨s.a10.toBitVec⟩, ⟨s.a11.toBitVec⟩, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]

/-- Pure symbolic round used to keep the monadic reduction linear in the MIR size. -/
@[expose] def keccakRoundRaw (s : Qsag.KState) (rc : Std.U64) : Array Std.U64 25#usize :=
  let i : Std.U64 := ⟨s.a0.toBitVec⟩
  let i1 : Std.U64 := ⟨s.a5.toBitVec⟩
  let i2 : Std.U64 := (i ^^^ i1)
  let i3 : Std.U64 := ⟨s.a10.toBitVec⟩
  let i4 : Std.U64 := (i2 ^^^ i3)
  let i5 : Std.U64 := ⟨s.a15.toBitVec⟩
  let i6 : Std.U64 := (i4 ^^^ i5)
  let i7 : Std.U64 := ⟨s.a20.toBitVec⟩
  let c0 : Std.U64 := (i6 ^^^ i7)
  let i8 : Std.U64 := ⟨s.a1.toBitVec⟩
  let i9 : Std.U64 := ⟨s.a6.toBitVec⟩
  let i10 : Std.U64 := (i8 ^^^ i9)
  let i11 : Std.U64 := ⟨s.a11.toBitVec⟩
  let i12 : Std.U64 := (i10 ^^^ i11)
  let i13 : Std.U64 := ⟨s.a16.toBitVec⟩
  let i14 : Std.U64 := (i12 ^^^ i13)
  let i15 : Std.U64 := ⟨s.a21.toBitVec⟩
  let c1 : Std.U64 := (i14 ^^^ i15)
  let i16 : Std.U64 := ⟨s.a2.toBitVec⟩
  let i17 : Std.U64 := ⟨s.a7.toBitVec⟩
  let i18 : Std.U64 := (i16 ^^^ i17)
  let i19 : Std.U64 := ⟨s.a12.toBitVec⟩
  let i20 : Std.U64 := (i18 ^^^ i19)
  let i21 : Std.U64 := ⟨s.a17.toBitVec⟩
  let i22 : Std.U64 := (i20 ^^^ i21)
  let i23 : Std.U64 := ⟨s.a22.toBitVec⟩
  let c2 : Std.U64 := (i22 ^^^ i23)
  let i24 : Std.U64 := ⟨s.a3.toBitVec⟩
  let i25 : Std.U64 := ⟨s.a8.toBitVec⟩
  let i26 : Std.U64 := (i24 ^^^ i25)
  let i27 : Std.U64 := ⟨s.a13.toBitVec⟩
  let i28 : Std.U64 := (i26 ^^^ i27)
  let i29 : Std.U64 := ⟨s.a18.toBitVec⟩
  let i30 : Std.U64 := (i28 ^^^ i29)
  let i31 : Std.U64 := ⟨s.a23.toBitVec⟩
  let c3 : Std.U64 := (i30 ^^^ i31)
  let i32 : Std.U64 := ⟨s.a4.toBitVec⟩
  let i33 : Std.U64 := ⟨s.a9.toBitVec⟩
  let i34 : Std.U64 := (i32 ^^^ i33)
  let i35 : Std.U64 := ⟨s.a14.toBitVec⟩
  let i36 : Std.U64 := (i34 ^^^ i35)
  let i37 : Std.U64 := ⟨s.a19.toBitVec⟩
  let i38 : Std.U64 := (i36 ^^^ i37)
  let i39 : Std.U64 := ⟨s.a24.toBitVec⟩
  let c4 : Std.U64 := (i38 ^^^ i39)
  let i40 : Std.U64 := (core.num.U64.rotate_left c1 1#u32)
  let d0 : Std.U64 := (c4 ^^^ i40)
  let i41 : Std.U64 := (core.num.U64.rotate_left c2 1#u32)
  let d1 : Std.U64 := (c0 ^^^ i41)
  let i42 : Std.U64 := (core.num.U64.rotate_left c3 1#u32)
  let d2 : Std.U64 := (c1 ^^^ i42)
  let i43 : Std.U64 := (core.num.U64.rotate_left c4 1#u32)
  let d3 : Std.U64 := (c2 ^^^ i43)
  let i44 : Std.U64 := (core.num.U64.rotate_left c0 1#u32)
  let d4 : Std.U64 := (c3 ^^^ i44)
  let a0 : Std.U64 := (i ^^^ d0)
  let a1 : Std.U64 := (i8 ^^^ d1)
  let a2 : Std.U64 := (i16 ^^^ d2)
  let a3 : Std.U64 := (i24 ^^^ d3)
  let a4 : Std.U64 := (i32 ^^^ d4)
  let a5 : Std.U64 := (i1 ^^^ d0)
  let a6 : Std.U64 := (i9 ^^^ d1)
  let a7 : Std.U64 := (i17 ^^^ d2)
  let a8 : Std.U64 := (i25 ^^^ d3)
  let a9 : Std.U64 := (i33 ^^^ d4)
  let a10 : Std.U64 := (i3 ^^^ d0)
  let a11 : Std.U64 := (i11 ^^^ d1)
  let a12 : Std.U64 := (i19 ^^^ d2)
  let a13 : Std.U64 := (i27 ^^^ d3)
  let a14 : Std.U64 := (i35 ^^^ d4)
  let a15 : Std.U64 := (i5 ^^^ d0)
  let a16 : Std.U64 := (i13 ^^^ d1)
  let a17 : Std.U64 := (i21 ^^^ d2)
  let a18 : Std.U64 := (i29 ^^^ d3)
  let a19 : Std.U64 := (i37 ^^^ d4)
  let a20 : Std.U64 := (i7 ^^^ d0)
  let a21 : Std.U64 := (i15 ^^^ d1)
  let a22 : Std.U64 := (i23 ^^^ d2)
  let a23 : Std.U64 := (i31 ^^^ d3)
  let a24 : Std.U64 := (i39 ^^^ d4)
  let b10 : Std.U64 := (core.num.U64.rotate_left a1 1#u32)
  let b20 : Std.U64 := (core.num.U64.rotate_left a2 62#u32)
  let b5 : Std.U64 := (core.num.U64.rotate_left a3 28#u32)
  let b15 : Std.U64 := (core.num.U64.rotate_left a4 27#u32)
  let b16 : Std.U64 := (core.num.U64.rotate_left a5 36#u32)
  let b1 : Std.U64 := (core.num.U64.rotate_left a6 44#u32)
  let b11 : Std.U64 := (core.num.U64.rotate_left a7 6#u32)
  let b21 : Std.U64 := (core.num.U64.rotate_left a8 55#u32)
  let b6 : Std.U64 := (core.num.U64.rotate_left a9 20#u32)
  let b7 : Std.U64 := (core.num.U64.rotate_left a10 3#u32)
  let b17 : Std.U64 := (core.num.U64.rotate_left a11 10#u32)
  let b2 : Std.U64 := (core.num.U64.rotate_left a12 43#u32)
  let b12 : Std.U64 := (core.num.U64.rotate_left a13 25#u32)
  let b22 : Std.U64 := (core.num.U64.rotate_left a14 39#u32)
  let b23 : Std.U64 := (core.num.U64.rotate_left a15 41#u32)
  let b8 : Std.U64 := (core.num.U64.rotate_left a16 45#u32)
  let b18 : Std.U64 := (core.num.U64.rotate_left a17 15#u32)
  let b3 : Std.U64 := (core.num.U64.rotate_left a18 21#u32)
  let b13 : Std.U64 := (core.num.U64.rotate_left a19 8#u32)
  let b14 : Std.U64 := (core.num.U64.rotate_left a20 18#u32)
  let b24 : Std.U64 := (core.num.U64.rotate_left a21 2#u32)
  let b9 : Std.U64 := (core.num.U64.rotate_left a22 61#u32)
  let b19 : Std.U64 := (core.num.U64.rotate_left a23 56#u32)
  let b4 : Std.U64 := (core.num.U64.rotate_left a24 14#u32)
  let i45 : Std.U64 := (~~~ b1)
  let i46 : Std.U64 := (i45 &&& b2)
  let i47 : Std.U64 := (a0 ^^^ i46)
  let i48 : Std.U64 := (i47 ^^^ rc)
  let state1 : Array Std.U64 25#usize := Array.make 25#usize [i48, ⟨s.a1.toBitVec⟩, ⟨s.a2.toBitVec⟩, ⟨s.a3.toBitVec⟩, ⟨s.a4.toBitVec⟩, ⟨s.a5.toBitVec⟩, ⟨s.a6.toBitVec⟩, ⟨s.a7.toBitVec⟩, ⟨s.a8.toBitVec⟩, ⟨s.a9.toBitVec⟩, ⟨s.a10.toBitVec⟩, ⟨s.a11.toBitVec⟩, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i49 : Std.U64 := (~~~ b2)
  let i50 : Std.U64 := (i49 &&& b3)
  let i51 : Std.U64 := (b1 ^^^ i50)
  let state2 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, ⟨s.a2.toBitVec⟩, ⟨s.a3.toBitVec⟩, ⟨s.a4.toBitVec⟩, ⟨s.a5.toBitVec⟩, ⟨s.a6.toBitVec⟩, ⟨s.a7.toBitVec⟩, ⟨s.a8.toBitVec⟩, ⟨s.a9.toBitVec⟩, ⟨s.a10.toBitVec⟩, ⟨s.a11.toBitVec⟩, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i52 : Std.U64 := (~~~ b3)
  let i53 : Std.U64 := (i52 &&& b4)
  let i54 : Std.U64 := (b2 ^^^ i53)
  let state3 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, ⟨s.a3.toBitVec⟩, ⟨s.a4.toBitVec⟩, ⟨s.a5.toBitVec⟩, ⟨s.a6.toBitVec⟩, ⟨s.a7.toBitVec⟩, ⟨s.a8.toBitVec⟩, ⟨s.a9.toBitVec⟩, ⟨s.a10.toBitVec⟩, ⟨s.a11.toBitVec⟩, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i55 : Std.U64 := (~~~ b4)
  let i56 : Std.U64 := (i55 &&& a0)
  let i57 : Std.U64 := (b3 ^^^ i56)
  let state4 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, ⟨s.a4.toBitVec⟩, ⟨s.a5.toBitVec⟩, ⟨s.a6.toBitVec⟩, ⟨s.a7.toBitVec⟩, ⟨s.a8.toBitVec⟩, ⟨s.a9.toBitVec⟩, ⟨s.a10.toBitVec⟩, ⟨s.a11.toBitVec⟩, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i58 : Std.U64 := (~~~ a0)
  let i59 : Std.U64 := (i58 &&& b1)
  let i60 : Std.U64 := (b4 ^^^ i59)
  let state5 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, ⟨s.a5.toBitVec⟩, ⟨s.a6.toBitVec⟩, ⟨s.a7.toBitVec⟩, ⟨s.a8.toBitVec⟩, ⟨s.a9.toBitVec⟩, ⟨s.a10.toBitVec⟩, ⟨s.a11.toBitVec⟩, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i61 : Std.U64 := (~~~ b6)
  let i62 : Std.U64 := (i61 &&& b7)
  let i63 : Std.U64 := (b5 ^^^ i62)
  let state6 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, ⟨s.a6.toBitVec⟩, ⟨s.a7.toBitVec⟩, ⟨s.a8.toBitVec⟩, ⟨s.a9.toBitVec⟩, ⟨s.a10.toBitVec⟩, ⟨s.a11.toBitVec⟩, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i64 : Std.U64 := (~~~ b7)
  let i65 : Std.U64 := (i64 &&& b8)
  let i66 : Std.U64 := (b6 ^^^ i65)
  let state7 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, ⟨s.a7.toBitVec⟩, ⟨s.a8.toBitVec⟩, ⟨s.a9.toBitVec⟩, ⟨s.a10.toBitVec⟩, ⟨s.a11.toBitVec⟩, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i67 : Std.U64 := (~~~ b8)
  let i68 : Std.U64 := (i67 &&& b9)
  let i69 : Std.U64 := (b7 ^^^ i68)
  let state8 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, ⟨s.a8.toBitVec⟩, ⟨s.a9.toBitVec⟩, ⟨s.a10.toBitVec⟩, ⟨s.a11.toBitVec⟩, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i70 : Std.U64 := (~~~ b9)
  let i71 : Std.U64 := (i70 &&& b5)
  let i72 : Std.U64 := (b8 ^^^ i71)
  let state9 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, ⟨s.a9.toBitVec⟩, ⟨s.a10.toBitVec⟩, ⟨s.a11.toBitVec⟩, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i73 : Std.U64 := (~~~ b5)
  let i74 : Std.U64 := (i73 &&& b6)
  let i75 : Std.U64 := (b9 ^^^ i74)
  let state10 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, ⟨s.a10.toBitVec⟩, ⟨s.a11.toBitVec⟩, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i76 : Std.U64 := (~~~ b11)
  let i77 : Std.U64 := (i76 &&& b12)
  let i78 : Std.U64 := (b10 ^^^ i77)
  let state11 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, ⟨s.a11.toBitVec⟩, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i79 : Std.U64 := (~~~ b12)
  let i80 : Std.U64 := (i79 &&& b13)
  let i81 : Std.U64 := (b11 ^^^ i80)
  let state12 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, i81, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i82 : Std.U64 := (~~~ b13)
  let i83 : Std.U64 := (i82 &&& b14)
  let i84 : Std.U64 := (b12 ^^^ i83)
  let state13 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, i81, i84, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i85 : Std.U64 := (~~~ b14)
  let i86 : Std.U64 := (i85 &&& b10)
  let i87 : Std.U64 := (b13 ^^^ i86)
  let state14 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, i81, i84, i87, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i88 : Std.U64 := (~~~ b10)
  let i89 : Std.U64 := (i88 &&& b11)
  let i90 : Std.U64 := (b14 ^^^ i89)
  let state15 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, i81, i84, i87, i90, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i91 : Std.U64 := (~~~ b16)
  let i92 : Std.U64 := (i91 &&& b17)
  let i93 : Std.U64 := (b15 ^^^ i92)
  let state16 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, i81, i84, i87, i90, i93, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i94 : Std.U64 := (~~~ b17)
  let i95 : Std.U64 := (i94 &&& b18)
  let i96 : Std.U64 := (b16 ^^^ i95)
  let state17 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, i81, i84, i87, i90, i93, i96, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i97 : Std.U64 := (~~~ b18)
  let i98 : Std.U64 := (i97 &&& b19)
  let i99 : Std.U64 := (b17 ^^^ i98)
  let state18 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, i81, i84, i87, i90, i93, i96, i99, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i100 : Std.U64 := (~~~ b19)
  let i101 : Std.U64 := (i100 &&& b15)
  let i102 : Std.U64 := (b18 ^^^ i101)
  let state19 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, i81, i84, i87, i90, i93, i96, i99, i102, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i103 : Std.U64 := (~~~ b15)
  let i104 : Std.U64 := (i103 &&& b16)
  let i105 : Std.U64 := (b19 ^^^ i104)
  let state20 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, i81, i84, i87, i90, i93, i96, i99, i102, i105, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i106 : Std.U64 := (~~~ b21)
  let i107 : Std.U64 := (i106 &&& b22)
  let i108 : Std.U64 := (b20 ^^^ i107)
  let state21 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, i81, i84, i87, i90, i93, i96, i99, i102, i105, i108, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i109 : Std.U64 := (~~~ b22)
  let i110 : Std.U64 := (i109 &&& b23)
  let i111 : Std.U64 := (b21 ^^^ i110)
  let state22 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, i81, i84, i87, i90, i93, i96, i99, i102, i105, i108, i111, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i112 : Std.U64 := (~~~ b23)
  let i113 : Std.U64 := (i112 &&& b24)
  let i114 : Std.U64 := (b22 ^^^ i113)
  let state23 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, i81, i84, i87, i90, i93, i96, i99, i102, i105, i108, i111, i114, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i115 : Std.U64 := (~~~ b24)
  let i116 : Std.U64 := (i115 &&& b20)
  let i117 : Std.U64 := (b23 ^^^ i116)
  let state24 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, i81, i84, i87, i90, i93, i96, i99, i102, i105, i108, i111, i114, i117, ⟨s.a24.toBitVec⟩]
  let i118 : Std.U64 := (~~~ b20)
  let i119 : Std.U64 := (i118 &&& b21)
  let i120 : Std.U64 := (b24 ^^^ i119)
  let finalState : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, i81, i84, i87, i90, i93, i96, i99, i102, i105, i108, i111, i114, i117, i120]
  finalState

theorem keccak_round_eq_raw (s : Qsag.KState) (rc : Std.U64) :
    keccak.keccak_f1600_round (keccakArrayOfState s) rc = .ok (keccakRoundRaw s rc) := by
  let state := keccakArrayOfState s
  let i : Std.U64 := ⟨s.a0.toBitVec⟩
  let i1 : Std.U64 := ⟨s.a5.toBitVec⟩
  let i2 : Std.U64 := (i ^^^ i1)
  let i3 : Std.U64 := ⟨s.a10.toBitVec⟩
  let i4 : Std.U64 := (i2 ^^^ i3)
  let i5 : Std.U64 := ⟨s.a15.toBitVec⟩
  let i6 : Std.U64 := (i4 ^^^ i5)
  let i7 : Std.U64 := ⟨s.a20.toBitVec⟩
  let c0 : Std.U64 := (i6 ^^^ i7)
  let i8 : Std.U64 := ⟨s.a1.toBitVec⟩
  let i9 : Std.U64 := ⟨s.a6.toBitVec⟩
  let i10 : Std.U64 := (i8 ^^^ i9)
  let i11 : Std.U64 := ⟨s.a11.toBitVec⟩
  let i12 : Std.U64 := (i10 ^^^ i11)
  let i13 : Std.U64 := ⟨s.a16.toBitVec⟩
  let i14 : Std.U64 := (i12 ^^^ i13)
  let i15 : Std.U64 := ⟨s.a21.toBitVec⟩
  let c1 : Std.U64 := (i14 ^^^ i15)
  let i16 : Std.U64 := ⟨s.a2.toBitVec⟩
  let i17 : Std.U64 := ⟨s.a7.toBitVec⟩
  let i18 : Std.U64 := (i16 ^^^ i17)
  let i19 : Std.U64 := ⟨s.a12.toBitVec⟩
  let i20 : Std.U64 := (i18 ^^^ i19)
  let i21 : Std.U64 := ⟨s.a17.toBitVec⟩
  let i22 : Std.U64 := (i20 ^^^ i21)
  let i23 : Std.U64 := ⟨s.a22.toBitVec⟩
  let c2 : Std.U64 := (i22 ^^^ i23)
  let i24 : Std.U64 := ⟨s.a3.toBitVec⟩
  let i25 : Std.U64 := ⟨s.a8.toBitVec⟩
  let i26 : Std.U64 := (i24 ^^^ i25)
  let i27 : Std.U64 := ⟨s.a13.toBitVec⟩
  let i28 : Std.U64 := (i26 ^^^ i27)
  let i29 : Std.U64 := ⟨s.a18.toBitVec⟩
  let i30 : Std.U64 := (i28 ^^^ i29)
  let i31 : Std.U64 := ⟨s.a23.toBitVec⟩
  let c3 : Std.U64 := (i30 ^^^ i31)
  let i32 : Std.U64 := ⟨s.a4.toBitVec⟩
  let i33 : Std.U64 := ⟨s.a9.toBitVec⟩
  let i34 : Std.U64 := (i32 ^^^ i33)
  let i35 : Std.U64 := ⟨s.a14.toBitVec⟩
  let i36 : Std.U64 := (i34 ^^^ i35)
  let i37 : Std.U64 := ⟨s.a19.toBitVec⟩
  let i38 : Std.U64 := (i36 ^^^ i37)
  let i39 : Std.U64 := ⟨s.a24.toBitVec⟩
  let c4 : Std.U64 := (i38 ^^^ i39)
  let i40 : Std.U64 := (core.num.U64.rotate_left c1 1#u32)
  let d0 : Std.U64 := (c4 ^^^ i40)
  let i41 : Std.U64 := (core.num.U64.rotate_left c2 1#u32)
  let d1 : Std.U64 := (c0 ^^^ i41)
  let i42 : Std.U64 := (core.num.U64.rotate_left c3 1#u32)
  let d2 : Std.U64 := (c1 ^^^ i42)
  let i43 : Std.U64 := (core.num.U64.rotate_left c4 1#u32)
  let d3 : Std.U64 := (c2 ^^^ i43)
  let i44 : Std.U64 := (core.num.U64.rotate_left c0 1#u32)
  let d4 : Std.U64 := (c3 ^^^ i44)
  let a0 : Std.U64 := (i ^^^ d0)
  let a1 : Std.U64 := (i8 ^^^ d1)
  let a2 : Std.U64 := (i16 ^^^ d2)
  let a3 : Std.U64 := (i24 ^^^ d3)
  let a4 : Std.U64 := (i32 ^^^ d4)
  let a5 : Std.U64 := (i1 ^^^ d0)
  let a6 : Std.U64 := (i9 ^^^ d1)
  let a7 : Std.U64 := (i17 ^^^ d2)
  let a8 : Std.U64 := (i25 ^^^ d3)
  let a9 : Std.U64 := (i33 ^^^ d4)
  let a10 : Std.U64 := (i3 ^^^ d0)
  let a11 : Std.U64 := (i11 ^^^ d1)
  let a12 : Std.U64 := (i19 ^^^ d2)
  let a13 : Std.U64 := (i27 ^^^ d3)
  let a14 : Std.U64 := (i35 ^^^ d4)
  let a15 : Std.U64 := (i5 ^^^ d0)
  let a16 : Std.U64 := (i13 ^^^ d1)
  let a17 : Std.U64 := (i21 ^^^ d2)
  let a18 : Std.U64 := (i29 ^^^ d3)
  let a19 : Std.U64 := (i37 ^^^ d4)
  let a20 : Std.U64 := (i7 ^^^ d0)
  let a21 : Std.U64 := (i15 ^^^ d1)
  let a22 : Std.U64 := (i23 ^^^ d2)
  let a23 : Std.U64 := (i31 ^^^ d3)
  let a24 : Std.U64 := (i39 ^^^ d4)
  let b10 : Std.U64 := (core.num.U64.rotate_left a1 1#u32)
  let b20 : Std.U64 := (core.num.U64.rotate_left a2 62#u32)
  let b5 : Std.U64 := (core.num.U64.rotate_left a3 28#u32)
  let b15 : Std.U64 := (core.num.U64.rotate_left a4 27#u32)
  let b16 : Std.U64 := (core.num.U64.rotate_left a5 36#u32)
  let b1 : Std.U64 := (core.num.U64.rotate_left a6 44#u32)
  let b11 : Std.U64 := (core.num.U64.rotate_left a7 6#u32)
  let b21 : Std.U64 := (core.num.U64.rotate_left a8 55#u32)
  let b6 : Std.U64 := (core.num.U64.rotate_left a9 20#u32)
  let b7 : Std.U64 := (core.num.U64.rotate_left a10 3#u32)
  let b17 : Std.U64 := (core.num.U64.rotate_left a11 10#u32)
  let b2 : Std.U64 := (core.num.U64.rotate_left a12 43#u32)
  let b12 : Std.U64 := (core.num.U64.rotate_left a13 25#u32)
  let b22 : Std.U64 := (core.num.U64.rotate_left a14 39#u32)
  let b23 : Std.U64 := (core.num.U64.rotate_left a15 41#u32)
  let b8 : Std.U64 := (core.num.U64.rotate_left a16 45#u32)
  let b18 : Std.U64 := (core.num.U64.rotate_left a17 15#u32)
  let b3 : Std.U64 := (core.num.U64.rotate_left a18 21#u32)
  let b13 : Std.U64 := (core.num.U64.rotate_left a19 8#u32)
  let b14 : Std.U64 := (core.num.U64.rotate_left a20 18#u32)
  let b24 : Std.U64 := (core.num.U64.rotate_left a21 2#u32)
  let b9 : Std.U64 := (core.num.U64.rotate_left a22 61#u32)
  let b19 : Std.U64 := (core.num.U64.rotate_left a23 56#u32)
  let b4 : Std.U64 := (core.num.U64.rotate_left a24 14#u32)
  let i45 : Std.U64 := (~~~ b1)
  let i46 : Std.U64 := (i45 &&& b2)
  let i47 : Std.U64 := (a0 ^^^ i46)
  let i48 : Std.U64 := (i47 ^^^ rc)
  let state1 : Array Std.U64 25#usize := Array.make 25#usize [i48, ⟨s.a1.toBitVec⟩, ⟨s.a2.toBitVec⟩, ⟨s.a3.toBitVec⟩, ⟨s.a4.toBitVec⟩, ⟨s.a5.toBitVec⟩, ⟨s.a6.toBitVec⟩, ⟨s.a7.toBitVec⟩, ⟨s.a8.toBitVec⟩, ⟨s.a9.toBitVec⟩, ⟨s.a10.toBitVec⟩, ⟨s.a11.toBitVec⟩, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i49 : Std.U64 := (~~~ b2)
  let i50 : Std.U64 := (i49 &&& b3)
  let i51 : Std.U64 := (b1 ^^^ i50)
  let state2 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, ⟨s.a2.toBitVec⟩, ⟨s.a3.toBitVec⟩, ⟨s.a4.toBitVec⟩, ⟨s.a5.toBitVec⟩, ⟨s.a6.toBitVec⟩, ⟨s.a7.toBitVec⟩, ⟨s.a8.toBitVec⟩, ⟨s.a9.toBitVec⟩, ⟨s.a10.toBitVec⟩, ⟨s.a11.toBitVec⟩, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i52 : Std.U64 := (~~~ b3)
  let i53 : Std.U64 := (i52 &&& b4)
  let i54 : Std.U64 := (b2 ^^^ i53)
  let state3 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, ⟨s.a3.toBitVec⟩, ⟨s.a4.toBitVec⟩, ⟨s.a5.toBitVec⟩, ⟨s.a6.toBitVec⟩, ⟨s.a7.toBitVec⟩, ⟨s.a8.toBitVec⟩, ⟨s.a9.toBitVec⟩, ⟨s.a10.toBitVec⟩, ⟨s.a11.toBitVec⟩, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i55 : Std.U64 := (~~~ b4)
  let i56 : Std.U64 := (i55 &&& a0)
  let i57 : Std.U64 := (b3 ^^^ i56)
  let state4 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, ⟨s.a4.toBitVec⟩, ⟨s.a5.toBitVec⟩, ⟨s.a6.toBitVec⟩, ⟨s.a7.toBitVec⟩, ⟨s.a8.toBitVec⟩, ⟨s.a9.toBitVec⟩, ⟨s.a10.toBitVec⟩, ⟨s.a11.toBitVec⟩, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i58 : Std.U64 := (~~~ a0)
  let i59 : Std.U64 := (i58 &&& b1)
  let i60 : Std.U64 := (b4 ^^^ i59)
  let state5 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, ⟨s.a5.toBitVec⟩, ⟨s.a6.toBitVec⟩, ⟨s.a7.toBitVec⟩, ⟨s.a8.toBitVec⟩, ⟨s.a9.toBitVec⟩, ⟨s.a10.toBitVec⟩, ⟨s.a11.toBitVec⟩, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i61 : Std.U64 := (~~~ b6)
  let i62 : Std.U64 := (i61 &&& b7)
  let i63 : Std.U64 := (b5 ^^^ i62)
  let state6 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, ⟨s.a6.toBitVec⟩, ⟨s.a7.toBitVec⟩, ⟨s.a8.toBitVec⟩, ⟨s.a9.toBitVec⟩, ⟨s.a10.toBitVec⟩, ⟨s.a11.toBitVec⟩, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i64 : Std.U64 := (~~~ b7)
  let i65 : Std.U64 := (i64 &&& b8)
  let i66 : Std.U64 := (b6 ^^^ i65)
  let state7 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, ⟨s.a7.toBitVec⟩, ⟨s.a8.toBitVec⟩, ⟨s.a9.toBitVec⟩, ⟨s.a10.toBitVec⟩, ⟨s.a11.toBitVec⟩, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i67 : Std.U64 := (~~~ b8)
  let i68 : Std.U64 := (i67 &&& b9)
  let i69 : Std.U64 := (b7 ^^^ i68)
  let state8 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, ⟨s.a8.toBitVec⟩, ⟨s.a9.toBitVec⟩, ⟨s.a10.toBitVec⟩, ⟨s.a11.toBitVec⟩, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i70 : Std.U64 := (~~~ b9)
  let i71 : Std.U64 := (i70 &&& b5)
  let i72 : Std.U64 := (b8 ^^^ i71)
  let state9 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, ⟨s.a9.toBitVec⟩, ⟨s.a10.toBitVec⟩, ⟨s.a11.toBitVec⟩, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i73 : Std.U64 := (~~~ b5)
  let i74 : Std.U64 := (i73 &&& b6)
  let i75 : Std.U64 := (b9 ^^^ i74)
  let state10 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, ⟨s.a10.toBitVec⟩, ⟨s.a11.toBitVec⟩, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i76 : Std.U64 := (~~~ b11)
  let i77 : Std.U64 := (i76 &&& b12)
  let i78 : Std.U64 := (b10 ^^^ i77)
  let state11 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, ⟨s.a11.toBitVec⟩, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i79 : Std.U64 := (~~~ b12)
  let i80 : Std.U64 := (i79 &&& b13)
  let i81 : Std.U64 := (b11 ^^^ i80)
  let state12 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, i81, ⟨s.a12.toBitVec⟩, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i82 : Std.U64 := (~~~ b13)
  let i83 : Std.U64 := (i82 &&& b14)
  let i84 : Std.U64 := (b12 ^^^ i83)
  let state13 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, i81, i84, ⟨s.a13.toBitVec⟩, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i85 : Std.U64 := (~~~ b14)
  let i86 : Std.U64 := (i85 &&& b10)
  let i87 : Std.U64 := (b13 ^^^ i86)
  let state14 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, i81, i84, i87, ⟨s.a14.toBitVec⟩, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i88 : Std.U64 := (~~~ b10)
  let i89 : Std.U64 := (i88 &&& b11)
  let i90 : Std.U64 := (b14 ^^^ i89)
  let state15 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, i81, i84, i87, i90, ⟨s.a15.toBitVec⟩, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i91 : Std.U64 := (~~~ b16)
  let i92 : Std.U64 := (i91 &&& b17)
  let i93 : Std.U64 := (b15 ^^^ i92)
  let state16 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, i81, i84, i87, i90, i93, ⟨s.a16.toBitVec⟩, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i94 : Std.U64 := (~~~ b17)
  let i95 : Std.U64 := (i94 &&& b18)
  let i96 : Std.U64 := (b16 ^^^ i95)
  let state17 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, i81, i84, i87, i90, i93, i96, ⟨s.a17.toBitVec⟩, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i97 : Std.U64 := (~~~ b18)
  let i98 : Std.U64 := (i97 &&& b19)
  let i99 : Std.U64 := (b17 ^^^ i98)
  let state18 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, i81, i84, i87, i90, i93, i96, i99, ⟨s.a18.toBitVec⟩, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i100 : Std.U64 := (~~~ b19)
  let i101 : Std.U64 := (i100 &&& b15)
  let i102 : Std.U64 := (b18 ^^^ i101)
  let state19 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, i81, i84, i87, i90, i93, i96, i99, i102, ⟨s.a19.toBitVec⟩, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i103 : Std.U64 := (~~~ b15)
  let i104 : Std.U64 := (i103 &&& b16)
  let i105 : Std.U64 := (b19 ^^^ i104)
  let state20 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, i81, i84, i87, i90, i93, i96, i99, i102, i105, ⟨s.a20.toBitVec⟩, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i106 : Std.U64 := (~~~ b21)
  let i107 : Std.U64 := (i106 &&& b22)
  let i108 : Std.U64 := (b20 ^^^ i107)
  let state21 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, i81, i84, i87, i90, i93, i96, i99, i102, i105, i108, ⟨s.a21.toBitVec⟩, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i109 : Std.U64 := (~~~ b22)
  let i110 : Std.U64 := (i109 &&& b23)
  let i111 : Std.U64 := (b21 ^^^ i110)
  let state22 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, i81, i84, i87, i90, i93, i96, i99, i102, i105, i108, i111, ⟨s.a22.toBitVec⟩, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i112 : Std.U64 := (~~~ b23)
  let i113 : Std.U64 := (i112 &&& b24)
  let i114 : Std.U64 := (b22 ^^^ i113)
  let state23 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, i81, i84, i87, i90, i93, i96, i99, i102, i105, i108, i111, i114, ⟨s.a23.toBitVec⟩, ⟨s.a24.toBitVec⟩]
  let i115 : Std.U64 := (~~~ b24)
  let i116 : Std.U64 := (i115 &&& b20)
  let i117 : Std.U64 := (b23 ^^^ i116)
  let state24 : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, i81, i84, i87, i90, i93, i96, i99, i102, i105, i108, i111, i114, i117, ⟨s.a24.toBitVec⟩]
  let i118 : Std.U64 := (~~~ b20)
  let i119 : Std.U64 := (i118 &&& b21)
  let i120 : Std.U64 := (b24 ^^^ i119)
  let finalState : Array Std.U64 25#usize := Array.make 25#usize [i48, i51, i54, i57, i60, i63, i66, i69, i72, i75, i78, i81, i84, i87, i90, i93, i96, i99, i102, i105, i108, i111, i114, i117, i120]
  unfold keccak.keccak_f1600_round
  apply bind_ok_step (show Array.index_usize state 0#usize = .ok i from rfl)
  apply bind_ok_step (show Array.index_usize state 5#usize = .ok i1 from rfl)
  apply bind_ok_step (show lift (i ^^^ i1) = .ok i2 from rfl)
  apply bind_ok_step (show Array.index_usize state 10#usize = .ok i3 from rfl)
  apply bind_ok_step (show lift (i2 ^^^ i3) = .ok i4 from rfl)
  apply bind_ok_step (show Array.index_usize state 15#usize = .ok i5 from rfl)
  apply bind_ok_step (show lift (i4 ^^^ i5) = .ok i6 from rfl)
  apply bind_ok_step (show Array.index_usize state 20#usize = .ok i7 from rfl)
  apply bind_ok_step (show lift (i6 ^^^ i7) = .ok c0 from rfl)
  apply bind_ok_step (show Array.index_usize state 1#usize = .ok i8 from rfl)
  apply bind_ok_step (show Array.index_usize state 6#usize = .ok i9 from rfl)
  apply bind_ok_step (show lift (i8 ^^^ i9) = .ok i10 from rfl)
  apply bind_ok_step (show Array.index_usize state 11#usize = .ok i11 from rfl)
  apply bind_ok_step (show lift (i10 ^^^ i11) = .ok i12 from rfl)
  apply bind_ok_step (show Array.index_usize state 16#usize = .ok i13 from rfl)
  apply bind_ok_step (show lift (i12 ^^^ i13) = .ok i14 from rfl)
  apply bind_ok_step (show Array.index_usize state 21#usize = .ok i15 from rfl)
  apply bind_ok_step (show lift (i14 ^^^ i15) = .ok c1 from rfl)
  apply bind_ok_step (show Array.index_usize state 2#usize = .ok i16 from rfl)
  apply bind_ok_step (show Array.index_usize state 7#usize = .ok i17 from rfl)
  apply bind_ok_step (show lift (i16 ^^^ i17) = .ok i18 from rfl)
  apply bind_ok_step (show Array.index_usize state 12#usize = .ok i19 from rfl)
  apply bind_ok_step (show lift (i18 ^^^ i19) = .ok i20 from rfl)
  apply bind_ok_step (show Array.index_usize state 17#usize = .ok i21 from rfl)
  apply bind_ok_step (show lift (i20 ^^^ i21) = .ok i22 from rfl)
  apply bind_ok_step (show Array.index_usize state 22#usize = .ok i23 from rfl)
  apply bind_ok_step (show lift (i22 ^^^ i23) = .ok c2 from rfl)
  apply bind_ok_step (show Array.index_usize state 3#usize = .ok i24 from rfl)
  apply bind_ok_step (show Array.index_usize state 8#usize = .ok i25 from rfl)
  apply bind_ok_step (show lift (i24 ^^^ i25) = .ok i26 from rfl)
  apply bind_ok_step (show Array.index_usize state 13#usize = .ok i27 from rfl)
  apply bind_ok_step (show lift (i26 ^^^ i27) = .ok i28 from rfl)
  apply bind_ok_step (show Array.index_usize state 18#usize = .ok i29 from rfl)
  apply bind_ok_step (show lift (i28 ^^^ i29) = .ok i30 from rfl)
  apply bind_ok_step (show Array.index_usize state 23#usize = .ok i31 from rfl)
  apply bind_ok_step (show lift (i30 ^^^ i31) = .ok c3 from rfl)
  apply bind_ok_step (show Array.index_usize state 4#usize = .ok i32 from rfl)
  apply bind_ok_step (show Array.index_usize state 9#usize = .ok i33 from rfl)
  apply bind_ok_step (show lift (i32 ^^^ i33) = .ok i34 from rfl)
  apply bind_ok_step (show Array.index_usize state 14#usize = .ok i35 from rfl)
  apply bind_ok_step (show lift (i34 ^^^ i35) = .ok i36 from rfl)
  apply bind_ok_step (show Array.index_usize state 19#usize = .ok i37 from rfl)
  apply bind_ok_step (show lift (i36 ^^^ i37) = .ok i38 from rfl)
  apply bind_ok_step (show Array.index_usize state 24#usize = .ok i39 from rfl)
  apply bind_ok_step (show lift (i38 ^^^ i39) = .ok c4 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left c1 1#u32) = .ok i40 from rfl)
  apply bind_ok_step (show lift (c4 ^^^ i40) = .ok d0 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left c2 1#u32) = .ok i41 from rfl)
  apply bind_ok_step (show lift (c0 ^^^ i41) = .ok d1 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left c3 1#u32) = .ok i42 from rfl)
  apply bind_ok_step (show lift (c1 ^^^ i42) = .ok d2 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left c4 1#u32) = .ok i43 from rfl)
  apply bind_ok_step (show lift (c2 ^^^ i43) = .ok d3 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left c0 1#u32) = .ok i44 from rfl)
  apply bind_ok_step (show lift (c3 ^^^ i44) = .ok d4 from rfl)
  apply bind_ok_step (show lift (i ^^^ d0) = .ok a0 from rfl)
  apply bind_ok_step (show lift (i8 ^^^ d1) = .ok a1 from rfl)
  apply bind_ok_step (show lift (i16 ^^^ d2) = .ok a2 from rfl)
  apply bind_ok_step (show lift (i24 ^^^ d3) = .ok a3 from rfl)
  apply bind_ok_step (show lift (i32 ^^^ d4) = .ok a4 from rfl)
  apply bind_ok_step (show lift (i1 ^^^ d0) = .ok a5 from rfl)
  apply bind_ok_step (show lift (i9 ^^^ d1) = .ok a6 from rfl)
  apply bind_ok_step (show lift (i17 ^^^ d2) = .ok a7 from rfl)
  apply bind_ok_step (show lift (i25 ^^^ d3) = .ok a8 from rfl)
  apply bind_ok_step (show lift (i33 ^^^ d4) = .ok a9 from rfl)
  apply bind_ok_step (show lift (i3 ^^^ d0) = .ok a10 from rfl)
  apply bind_ok_step (show lift (i11 ^^^ d1) = .ok a11 from rfl)
  apply bind_ok_step (show lift (i19 ^^^ d2) = .ok a12 from rfl)
  apply bind_ok_step (show lift (i27 ^^^ d3) = .ok a13 from rfl)
  apply bind_ok_step (show lift (i35 ^^^ d4) = .ok a14 from rfl)
  apply bind_ok_step (show lift (i5 ^^^ d0) = .ok a15 from rfl)
  apply bind_ok_step (show lift (i13 ^^^ d1) = .ok a16 from rfl)
  apply bind_ok_step (show lift (i21 ^^^ d2) = .ok a17 from rfl)
  apply bind_ok_step (show lift (i29 ^^^ d3) = .ok a18 from rfl)
  apply bind_ok_step (show lift (i37 ^^^ d4) = .ok a19 from rfl)
  apply bind_ok_step (show lift (i7 ^^^ d0) = .ok a20 from rfl)
  apply bind_ok_step (show lift (i15 ^^^ d1) = .ok a21 from rfl)
  apply bind_ok_step (show lift (i23 ^^^ d2) = .ok a22 from rfl)
  apply bind_ok_step (show lift (i31 ^^^ d3) = .ok a23 from rfl)
  apply bind_ok_step (show lift (i39 ^^^ d4) = .ok a24 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left a1 1#u32) = .ok b10 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left a2 62#u32) = .ok b20 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left a3 28#u32) = .ok b5 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left a4 27#u32) = .ok b15 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left a5 36#u32) = .ok b16 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left a6 44#u32) = .ok b1 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left a7 6#u32) = .ok b11 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left a8 55#u32) = .ok b21 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left a9 20#u32) = .ok b6 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left a10 3#u32) = .ok b7 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left a11 10#u32) = .ok b17 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left a12 43#u32) = .ok b2 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left a13 25#u32) = .ok b12 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left a14 39#u32) = .ok b22 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left a15 41#u32) = .ok b23 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left a16 45#u32) = .ok b8 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left a17 15#u32) = .ok b18 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left a18 21#u32) = .ok b3 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left a19 8#u32) = .ok b13 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left a20 18#u32) = .ok b14 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left a21 2#u32) = .ok b24 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left a22 61#u32) = .ok b9 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left a23 56#u32) = .ok b19 from rfl)
  apply bind_ok_step (show lift (core.num.U64.rotate_left a24 14#u32) = .ok b4 from rfl)
  apply bind_ok_step (show lift (~~~ b1) = .ok i45 from rfl)
  apply bind_ok_step (show lift (i45 &&& b2) = .ok i46 from rfl)
  apply bind_ok_step (show lift (a0 ^^^ i46) = .ok i47 from rfl)
  apply bind_ok_step (show lift (i47 ^^^ rc) = .ok i48 from rfl)
  apply bind_ok_step (show Array.update state 0#usize i48 = .ok state1 from rfl)
  apply bind_ok_step (show lift (~~~ b2) = .ok i49 from rfl)
  apply bind_ok_step (show lift (i49 &&& b3) = .ok i50 from rfl)
  apply bind_ok_step (show lift (b1 ^^^ i50) = .ok i51 from rfl)
  apply bind_ok_step (show Array.update state1 1#usize i51 = .ok state2 from rfl)
  apply bind_ok_step (show lift (~~~ b3) = .ok i52 from rfl)
  apply bind_ok_step (show lift (i52 &&& b4) = .ok i53 from rfl)
  apply bind_ok_step (show lift (b2 ^^^ i53) = .ok i54 from rfl)
  apply bind_ok_step (show Array.update state2 2#usize i54 = .ok state3 from rfl)
  apply bind_ok_step (show lift (~~~ b4) = .ok i55 from rfl)
  apply bind_ok_step (show lift (i55 &&& a0) = .ok i56 from rfl)
  apply bind_ok_step (show lift (b3 ^^^ i56) = .ok i57 from rfl)
  apply bind_ok_step (show Array.update state3 3#usize i57 = .ok state4 from rfl)
  apply bind_ok_step (show lift (~~~ a0) = .ok i58 from rfl)
  apply bind_ok_step (show lift (i58 &&& b1) = .ok i59 from rfl)
  apply bind_ok_step (show lift (b4 ^^^ i59) = .ok i60 from rfl)
  apply bind_ok_step (show Array.update state4 4#usize i60 = .ok state5 from rfl)
  apply bind_ok_step (show lift (~~~ b6) = .ok i61 from rfl)
  apply bind_ok_step (show lift (i61 &&& b7) = .ok i62 from rfl)
  apply bind_ok_step (show lift (b5 ^^^ i62) = .ok i63 from rfl)
  apply bind_ok_step (show Array.update state5 5#usize i63 = .ok state6 from rfl)
  apply bind_ok_step (show lift (~~~ b7) = .ok i64 from rfl)
  apply bind_ok_step (show lift (i64 &&& b8) = .ok i65 from rfl)
  apply bind_ok_step (show lift (b6 ^^^ i65) = .ok i66 from rfl)
  apply bind_ok_step (show Array.update state6 6#usize i66 = .ok state7 from rfl)
  apply bind_ok_step (show lift (~~~ b8) = .ok i67 from rfl)
  apply bind_ok_step (show lift (i67 &&& b9) = .ok i68 from rfl)
  apply bind_ok_step (show lift (b7 ^^^ i68) = .ok i69 from rfl)
  apply bind_ok_step (show Array.update state7 7#usize i69 = .ok state8 from rfl)
  apply bind_ok_step (show lift (~~~ b9) = .ok i70 from rfl)
  apply bind_ok_step (show lift (i70 &&& b5) = .ok i71 from rfl)
  apply bind_ok_step (show lift (b8 ^^^ i71) = .ok i72 from rfl)
  apply bind_ok_step (show Array.update state8 8#usize i72 = .ok state9 from rfl)
  apply bind_ok_step (show lift (~~~ b5) = .ok i73 from rfl)
  apply bind_ok_step (show lift (i73 &&& b6) = .ok i74 from rfl)
  apply bind_ok_step (show lift (b9 ^^^ i74) = .ok i75 from rfl)
  apply bind_ok_step (show Array.update state9 9#usize i75 = .ok state10 from rfl)
  apply bind_ok_step (show lift (~~~ b11) = .ok i76 from rfl)
  apply bind_ok_step (show lift (i76 &&& b12) = .ok i77 from rfl)
  apply bind_ok_step (show lift (b10 ^^^ i77) = .ok i78 from rfl)
  apply bind_ok_step (show Array.update state10 10#usize i78 = .ok state11 from rfl)
  apply bind_ok_step (show lift (~~~ b12) = .ok i79 from rfl)
  apply bind_ok_step (show lift (i79 &&& b13) = .ok i80 from rfl)
  apply bind_ok_step (show lift (b11 ^^^ i80) = .ok i81 from rfl)
  apply bind_ok_step (show Array.update state11 11#usize i81 = .ok state12 from rfl)
  apply bind_ok_step (show lift (~~~ b13) = .ok i82 from rfl)
  apply bind_ok_step (show lift (i82 &&& b14) = .ok i83 from rfl)
  apply bind_ok_step (show lift (b12 ^^^ i83) = .ok i84 from rfl)
  apply bind_ok_step (show Array.update state12 12#usize i84 = .ok state13 from rfl)
  apply bind_ok_step (show lift (~~~ b14) = .ok i85 from rfl)
  apply bind_ok_step (show lift (i85 &&& b10) = .ok i86 from rfl)
  apply bind_ok_step (show lift (b13 ^^^ i86) = .ok i87 from rfl)
  apply bind_ok_step (show Array.update state13 13#usize i87 = .ok state14 from rfl)
  apply bind_ok_step (show lift (~~~ b10) = .ok i88 from rfl)
  apply bind_ok_step (show lift (i88 &&& b11) = .ok i89 from rfl)
  apply bind_ok_step (show lift (b14 ^^^ i89) = .ok i90 from rfl)
  apply bind_ok_step (show Array.update state14 14#usize i90 = .ok state15 from rfl)
  apply bind_ok_step (show lift (~~~ b16) = .ok i91 from rfl)
  apply bind_ok_step (show lift (i91 &&& b17) = .ok i92 from rfl)
  apply bind_ok_step (show lift (b15 ^^^ i92) = .ok i93 from rfl)
  apply bind_ok_step (show Array.update state15 15#usize i93 = .ok state16 from rfl)
  apply bind_ok_step (show lift (~~~ b17) = .ok i94 from rfl)
  apply bind_ok_step (show lift (i94 &&& b18) = .ok i95 from rfl)
  apply bind_ok_step (show lift (b16 ^^^ i95) = .ok i96 from rfl)
  apply bind_ok_step (show Array.update state16 16#usize i96 = .ok state17 from rfl)
  apply bind_ok_step (show lift (~~~ b18) = .ok i97 from rfl)
  apply bind_ok_step (show lift (i97 &&& b19) = .ok i98 from rfl)
  apply bind_ok_step (show lift (b17 ^^^ i98) = .ok i99 from rfl)
  apply bind_ok_step (show Array.update state17 17#usize i99 = .ok state18 from rfl)
  apply bind_ok_step (show lift (~~~ b19) = .ok i100 from rfl)
  apply bind_ok_step (show lift (i100 &&& b15) = .ok i101 from rfl)
  apply bind_ok_step (show lift (b18 ^^^ i101) = .ok i102 from rfl)
  apply bind_ok_step (show Array.update state18 18#usize i102 = .ok state19 from rfl)
  apply bind_ok_step (show lift (~~~ b15) = .ok i103 from rfl)
  apply bind_ok_step (show lift (i103 &&& b16) = .ok i104 from rfl)
  apply bind_ok_step (show lift (b19 ^^^ i104) = .ok i105 from rfl)
  apply bind_ok_step (show Array.update state19 19#usize i105 = .ok state20 from rfl)
  apply bind_ok_step (show lift (~~~ b21) = .ok i106 from rfl)
  apply bind_ok_step (show lift (i106 &&& b22) = .ok i107 from rfl)
  apply bind_ok_step (show lift (b20 ^^^ i107) = .ok i108 from rfl)
  apply bind_ok_step (show Array.update state20 20#usize i108 = .ok state21 from rfl)
  apply bind_ok_step (show lift (~~~ b22) = .ok i109 from rfl)
  apply bind_ok_step (show lift (i109 &&& b23) = .ok i110 from rfl)
  apply bind_ok_step (show lift (b21 ^^^ i110) = .ok i111 from rfl)
  apply bind_ok_step (show Array.update state21 21#usize i111 = .ok state22 from rfl)
  apply bind_ok_step (show lift (~~~ b23) = .ok i112 from rfl)
  apply bind_ok_step (show lift (i112 &&& b24) = .ok i113 from rfl)
  apply bind_ok_step (show lift (b22 ^^^ i113) = .ok i114 from rfl)
  apply bind_ok_step (show Array.update state22 22#usize i114 = .ok state23 from rfl)
  apply bind_ok_step (show lift (~~~ b24) = .ok i115 from rfl)
  apply bind_ok_step (show lift (i115 &&& b20) = .ok i116 from rfl)
  apply bind_ok_step (show lift (b23 ^^^ i116) = .ok i117 from rfl)
  apply bind_ok_step (show Array.update state23 23#usize i117 = .ok state24 from rfl)
  apply bind_ok_step (show lift (~~~ b20) = .ok i118 from rfl)
  apply bind_ok_step (show lift (i118 &&& b21) = .ok i119 from rfl)
  apply bind_ok_step (show lift (b24 ^^^ i119) = .ok i120 from rfl)
  rfl

/-- One complete extracted round against the canonical Keccak round. -/
theorem keccak_round_refines_qsag (s : Qsag.KState) (rc : Std.U64) :
    keccak.keccak_f1600_round (keccakArrayOfState s) rc =
      .ok (keccakArrayOfState (Qsag.roundS s (UInt64.ofBitVec rc.bv))) := by
  rw [keccak_round_eq_raw]
  simp (config := { zeta := false }) only [Qsag.roundS_eq, Qsag.chiS_eq, Qsag.rhoPiS_eq, Qsag.thetaS_eq, Qsag.rotlK_eq]
  rfl

/-- All 24 extracted rounds with the canonical round-constant schedule. -/
theorem keccak_f1600_refines_qsag (s : Qsag.KState) :
    keccak.keccak_f1600 (keccakArrayOfState s) =
      .ok (keccakArrayOfState (Qsag.keccakF1600 s)) := by
  rw [Qsag.keccakF1600_eq, Qsag.keccakRoundConstants_eq]
  let s1 := Qsag.roundS s 1
  let s2 := Qsag.roundS s1 32898
  let s3 := Qsag.roundS s2 9223372036854808714
  let s4 := Qsag.roundS s3 9223372039002292224
  let s5 := Qsag.roundS s4 32907
  let s6 := Qsag.roundS s5 2147483649
  let s7 := Qsag.roundS s6 9223372039002292353
  let s8 := Qsag.roundS s7 9223372036854808585
  let s9 := Qsag.roundS s8 138
  let s10 := Qsag.roundS s9 136
  let s11 := Qsag.roundS s10 2147516425
  let s12 := Qsag.roundS s11 2147483658
  let s13 := Qsag.roundS s12 2147516555
  let s14 := Qsag.roundS s13 9223372036854775947
  let s15 := Qsag.roundS s14 9223372036854808713
  let s16 := Qsag.roundS s15 9223372036854808579
  let s17 := Qsag.roundS s16 9223372036854808578
  let s18 := Qsag.roundS s17 9223372036854775936
  let s19 := Qsag.roundS s18 32778
  let s20 := Qsag.roundS s19 9223372039002259466
  let s21 := Qsag.roundS s20 9223372039002292353
  let s22 := Qsag.roundS s21 9223372036854808704
  let s23 := Qsag.roundS s22 2147483649
  let s24 := Qsag.roundS s23 9223372039002292232
  unfold keccak.keccak_f1600
  apply bind_ok_step (keccak_round_refines_qsag s 1#u64)
  apply bind_ok_step (keccak_round_refines_qsag s1 32898#u64)
  apply bind_ok_step (keccak_round_refines_qsag s2 9223372036854808714#u64)
  apply bind_ok_step (keccak_round_refines_qsag s3 9223372039002292224#u64)
  apply bind_ok_step (keccak_round_refines_qsag s4 32907#u64)
  apply bind_ok_step (keccak_round_refines_qsag s5 2147483649#u64)
  apply bind_ok_step (keccak_round_refines_qsag s6 9223372039002292353#u64)
  apply bind_ok_step (keccak_round_refines_qsag s7 9223372036854808585#u64)
  apply bind_ok_step (keccak_round_refines_qsag s8 138#u64)
  apply bind_ok_step (keccak_round_refines_qsag s9 136#u64)
  apply bind_ok_step (keccak_round_refines_qsag s10 2147516425#u64)
  apply bind_ok_step (keccak_round_refines_qsag s11 2147483658#u64)
  apply bind_ok_step (keccak_round_refines_qsag s12 2147516555#u64)
  apply bind_ok_step (keccak_round_refines_qsag s13 9223372036854775947#u64)
  apply bind_ok_step (keccak_round_refines_qsag s14 9223372036854808713#u64)
  apply bind_ok_step (keccak_round_refines_qsag s15 9223372036854808579#u64)
  apply bind_ok_step (keccak_round_refines_qsag s16 9223372036854808578#u64)
  apply bind_ok_step (keccak_round_refines_qsag s17 9223372036854775936#u64)
  apply bind_ok_step (keccak_round_refines_qsag s18 32778#u64)
  apply bind_ok_step (keccak_round_refines_qsag s19 9223372039002259466#u64)
  apply bind_ok_step (keccak_round_refines_qsag s20 9223372039002292353#u64)
  apply bind_ok_step (keccak_round_refines_qsag s21 9223372036854808704#u64)
  apply bind_ok_step (keccak_round_refines_qsag s22 2147483649#u64)
  exact keccak_round_refines_qsag s23 9223372039002292232#u64

/-- Abstraction of every extracted array, including arbitrary nonzero states. -/
def keccakStateOfArray (a : Array Std.U64 25#usize) : Qsag.KState :=
  ⟨UInt64.ofBitVec (a.val.getD 0 0#u64).bv, UInt64.ofBitVec (a.val.getD 1 0#u64).bv, UInt64.ofBitVec (a.val.getD 2 0#u64).bv, UInt64.ofBitVec (a.val.getD 3 0#u64).bv, UInt64.ofBitVec (a.val.getD 4 0#u64).bv, UInt64.ofBitVec (a.val.getD 5 0#u64).bv, UInt64.ofBitVec (a.val.getD 6 0#u64).bv, UInt64.ofBitVec (a.val.getD 7 0#u64).bv, UInt64.ofBitVec (a.val.getD 8 0#u64).bv, UInt64.ofBitVec (a.val.getD 9 0#u64).bv, UInt64.ofBitVec (a.val.getD 10 0#u64).bv, UInt64.ofBitVec (a.val.getD 11 0#u64).bv, UInt64.ofBitVec (a.val.getD 12 0#u64).bv, UInt64.ofBitVec (a.val.getD 13 0#u64).bv, UInt64.ofBitVec (a.val.getD 14 0#u64).bv, UInt64.ofBitVec (a.val.getD 15 0#u64).bv, UInt64.ofBitVec (a.val.getD 16 0#u64).bv, UInt64.ofBitVec (a.val.getD 17 0#u64).bv, UInt64.ofBitVec (a.val.getD 18 0#u64).bv, UInt64.ofBitVec (a.val.getD 19 0#u64).bv, UInt64.ofBitVec (a.val.getD 20 0#u64).bv, UInt64.ofBitVec (a.val.getD 21 0#u64).bv, UInt64.ofBitVec (a.val.getD 22 0#u64).bv, UInt64.ofBitVec (a.val.getD 23 0#u64).bv, UInt64.ofBitVec (a.val.getD 24 0#u64).bv⟩

theorem keccakArrayOfState_roundtrip (a : Array Std.U64 25#usize) :
    keccakArrayOfState (keccakStateOfArray a) = a := by
  rcases a with ⟨xs, h⟩
  change xs.length = 25 at h
  cases xs with
  | nil => cases h
  | cons x0 xs =>
    cases xs with
    | nil => cases h
    | cons x1 xs =>
      cases xs with
      | nil => cases h
      | cons x2 xs =>
        cases xs with
        | nil => cases h
        | cons x3 xs =>
          cases xs with
          | nil => cases h
          | cons x4 xs =>
            cases xs with
            | nil => cases h
            | cons x5 xs =>
              cases xs with
              | nil => cases h
              | cons x6 xs =>
                cases xs with
                | nil => cases h
                | cons x7 xs =>
                  cases xs with
                  | nil => cases h
                  | cons x8 xs =>
                    cases xs with
                    | nil => cases h
                    | cons x9 xs =>
                      cases xs with
                      | nil => cases h
                      | cons x10 xs =>
                        cases xs with
                        | nil => cases h
                        | cons x11 xs =>
                          cases xs with
                          | nil => cases h
                          | cons x12 xs =>
                            cases xs with
                            | nil => cases h
                            | cons x13 xs =>
                              cases xs with
                              | nil => cases h
                              | cons x14 xs =>
                                cases xs with
                                | nil => cases h
                                | cons x15 xs =>
                                  cases xs with
                                  | nil => cases h
                                  | cons x16 xs =>
                                    cases xs with
                                    | nil => cases h
                                    | cons x17 xs =>
                                      cases xs with
                                      | nil => cases h
                                      | cons x18 xs =>
                                        cases xs with
                                        | nil => cases h
                                        | cons x19 xs =>
                                          cases xs with
                                          | nil => cases h
                                          | cons x20 xs =>
                                            cases xs with
                                            | nil => cases h
                                            | cons x21 xs =>
                                              cases xs with
                                              | nil => cases h
                                              | cons x22 xs =>
                                                cases xs with
                                                | nil => cases h
                                                | cons x23 xs =>
                                                  cases xs with
                                                  | nil => cases h
                                                  | cons x24 xs =>
                                                    cases xs with
                                                    | nil => rfl
                                                    | cons x xs => cases h

/-- Universal real-MIR permutation weld, with no condition on the input lanes. -/
theorem keccak_f1600_array_refines_qsag (a : Array Std.U64 25#usize) :
    keccak.keccak_f1600 a =
      .ok (keccakArrayOfState (Qsag.keccakF1600 (keccakStateOfArray a))) := by
  have h := keccak_f1600_refines_qsag (keccakStateOfArray a)
  rw [keccakArrayOfState_roundtrip] at h
  exact h

/-- The inverse representation round trip, complementary to the arbitrary-array law. -/
theorem keccakStateOfArray_roundtrip (s : Qsag.KState) :
    keccakStateOfArray (keccakArrayOfState s) = s := by
  cases s
  rfl

/-- Observation of the actual permutation result is exactly the canonical state. -/
theorem keccak_f1600_result_iff (a b : Array Std.U64 25#usize) :
    keccak.keccak_f1600 a = .ok b ↔
      b = keccakArrayOfState (Qsag.keccakF1600 (keccakStateOfArray a)) := by
  rw [keccak_f1600_array_refines_qsag, Result.ok.injEq]
  exact eq_comm

/-- The streaming API rejects absorption once squeezing has started: the extracted `absorb`
fails its phase assertion for every input, as production `Cshake256Xof::absorb` panics. No
state is returned, so a late absorb can never be mistaken for a successful no-op. -/
theorem shake256_absorb_after_squeezing_fails (s : keccak.Shake256Sponge)
    (data : Slice Std.U8) (hs : s.squeezing = true) :
    keccak.Shake256Sponge.absorb s data = .fail .assertionFailure := by
  simp only [keccak.Shake256Sponge.absorb, massert_not_of_eq_true hs, bind_eq_result_bind]
  rfl

/-- Absorption succeeds exactly in the absorbing phase. -/
theorem shake256_absorb_ok_iff_absorbing (s : keccak.Shake256Sponge) (data : Slice Std.U8) :
    (∃ out, keccak.Shake256Sponge.absorb s data = .ok out) → s.squeezing = false := by
  intro ⟨out, h⟩
  cases hs : s.squeezing with
  | false => rfl
  | true =>
    rw [shake256_absorb_after_squeezing_fails s data hs] at h
    cases h

/-- Finalization is idempotent on the squeezing phase, including its offset and buffer. -/
theorem shake256_finalize_after_squeezing (s : keccak.Shake256Sponge)
    (hs : s.squeezing = true) :
    keccak.Shake256Sponge.finalize s = .ok s := by
  simp [keccak.Shake256Sponge.finalize, hs]

end qsag_verified.proofs
