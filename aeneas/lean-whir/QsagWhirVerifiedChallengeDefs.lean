module
public import Qsag.Math.QuinticExt5
public import Qsag.Math.Poseidon2Gl24
public import Qsag.Protocol.Aggregation.HemRbrSoundness
public import Qsag.Protocol.Aggregation.PublicHemQuintic128
public import Qsag.Protocol.Aggregation.QuinticMultiStageWhir
public import Aeneas
public import QsagWhirVerified.Types
public import QsagWhirVerified.Funs

public section
open Aeneas Aeneas.Std
namespace qsag_whir_verified.proofs

abbrev goldilocksMod : Nat := 18446744069414584321

abbrev IsCanonical (x : U64) : Prop := x.val < 18446744069414584321

abbrev IsCanonicalFp5 (x : Fp5) : Prop :=
  IsCanonical x.c0 ∧ IsCanonical x.c1 ∧ IsCanonical x.c2 ∧ IsCanonical x.c3 ∧ IsCanonical x.c4

abbrev IsCanonicalGl24 (d : Gl24Digest) : Prop :=
  IsCanonical d.l0 ∧ IsCanonical d.l1 ∧ IsCanonical d.l2 ∧ IsCanonical d.l3 ∧
  IsCanonical d.l4 ∧ IsCanonical d.l5 ∧ IsCanonical d.l6

@[expose] def lePackU64At (bs : List U8) (off : Nat) : U64 :=
  ⟨(UScalar.cast .U64 (bs.getD off 0#u8)).bv |||
    ((UScalar.cast .U64 (bs.getD (off + 1) 0#u8)).bv <<< 8) |||
    ((UScalar.cast .U64 (bs.getD (off + 2) 0#u8)).bv <<< 16) |||
    ((UScalar.cast .U64 (bs.getD (off + 3) 0#u8)).bv <<< 24) |||
    ((UScalar.cast .U64 (bs.getD (off + 4) 0#u8)).bv <<< 32) |||
    ((UScalar.cast .U64 (bs.getD (off + 5) 0#u8)).bv <<< 40) |||
    ((UScalar.cast .U64 (bs.getD (off + 6) 0#u8)).bv <<< 48) |||
    ((UScalar.cast .U64 (bs.getD (off + 7) 0#u8)).bv <<< 56)⟩

@[expose] def fieldAdd (a b : U64) : U64 :=
  UScalar.ofNat .U64 ((a.val + b.val) % 18446744069414584321)

@[expose] def fieldSub (a b : U64) : U64 :=
  UScalar.ofNat .U64 ((a.val + (18446744069414584321 - b.val % 18446744069414584321)) % 18446744069414584321)

@[expose] def fieldMul (a b : U64) : U64 :=
  UScalar.ofNat .U64 ((a.val * b.val) % 18446744069414584321)

abbrev fp5Zero : Fp5 := ⟨0#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩
abbrev fp5One : Fp5 := ⟨1#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩
abbrev fp5FromBase (x : U64) : Fp5 :=
  ⟨UScalar.ofNat .U64 (x.val % 18446744069414584321), 0#u64, 0#u64, 0#u64, 0#u64⟩
abbrev fp5X : Fp5 := ⟨0#u64, 1#u64, 0#u64, 0#u64, 0#u64⟩
abbrev fp5Three : Fp5 := ⟨3#u64, 0#u64, 0#u64, 0#u64, 0#u64⟩

@[expose] def fp5Add (x y : Fp5) : Fp5 :=
  ⟨fieldAdd x.c0 y.c0, fieldAdd x.c1 y.c1, fieldAdd x.c2 y.c2, fieldAdd x.c3 y.c3, fieldAdd x.c4 y.c4⟩

@[expose] def fp5Sub (x y : Fp5) : Fp5 :=
  ⟨fieldSub x.c0 y.c0, fieldSub x.c1 y.c1, fieldSub x.c2 y.c2, fieldSub x.c3 y.c3, fieldSub x.c4 y.c4⟩

abbrev fp5Neg (x : Fp5) : Fp5 := fp5Sub fp5Zero x

@[expose] def fp5Scale (x : Fp5) (s : U64) : Fp5 :=
  ⟨fieldMul x.c0 s, fieldMul x.c1 s, fieldMul x.c2 s, fieldMul x.c3 s, fieldMul x.c4 s⟩

@[expose] def fp5Mul (x y : Fp5) : Fp5 :=
  ⟨fieldAdd (fieldMul x.c0 y.c0)
     (fieldMul 3#u64
       (fieldAdd (fieldAdd (fieldMul x.c1 y.c4) (fieldMul x.c2 y.c3))
                 (fieldAdd (fieldMul x.c3 y.c2) (fieldMul x.c4 y.c1)))),
   fieldAdd (fieldAdd (fieldMul x.c0 y.c1) (fieldMul x.c1 y.c0))
     (fieldMul 3#u64
       (fieldAdd (fieldAdd (fieldMul x.c2 y.c4) (fieldMul x.c3 y.c3))
                 (fieldMul x.c4 y.c2))),
   fieldAdd (fieldAdd (fieldAdd (fieldMul x.c0 y.c2) (fieldMul x.c1 y.c1)) (fieldMul x.c2 y.c0))
     (fieldMul 3#u64 (fieldAdd (fieldMul x.c3 y.c4) (fieldMul x.c4 y.c3))),
   fieldAdd (fieldAdd (fieldAdd (fieldMul x.c0 y.c3) (fieldMul x.c1 y.c2))
                      (fieldAdd (fieldMul x.c2 y.c1) (fieldMul x.c3 y.c0)))
     (fieldMul 3#u64 (fieldMul x.c4 y.c4)),
   fieldAdd (fieldAdd (fieldAdd (fieldMul x.c0 y.c4) (fieldMul x.c1 y.c3))
                      (fieldAdd (fieldMul x.c2 y.c2) (fieldMul x.c3 y.c1)))
     (fieldMul x.c4 y.c0)⟩

@[expose] def fp5Frob (x : Fp5) : Fp5 :=
  ⟨UScalar.ofNat .U64 (x.c0.val % 18446744069414584321),
   fieldMul x.c1 1041288259238279555#u64,
   fieldMul x.c2 15820824984080659046#u64,
   fieldMul x.c3 211587555138949697#u64,
   fieldMul x.c4 1373043270956696022#u64⟩

@[expose] def hornerSpec (coeffs : List Fp5) (z : U64) (init : Fp5 := fp5Zero) : Fp5 :=
  coeffs.foldr (fun c acc => fp5Add (fp5Scale acc z) c) init

@[expose] def evalPolyAscending : List Fp5 → U64 → Fp5
  | [], _ => fp5Zero
  | c :: rest, z => fp5Add c (fp5Scale (evalPolyAscending rest z) z)

end qsag_whir_verified.proofs
end
