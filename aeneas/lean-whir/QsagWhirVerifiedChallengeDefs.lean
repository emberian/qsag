module
public import Aeneas
public import QsagWhirVerified.Types
public import QsagWhirVerified.Funs

public section
open Aeneas Aeneas.Std
namespace qsag_whir_verified.proofs

abbrev goldilocksMod : Nat := 18446744069414584321

abbrev IsCanonical (x : U64) : Prop := x.val < 18446744069414584321

abbrev IsCanonicalExt4 (x : Ext4) : Prop :=
  IsCanonical x.a ∧ IsCanonical x.b ∧ IsCanonical x.c ∧ IsCanonical x.d

@[expose] def fieldAdd (a b : U64) : U64 :=
  UScalar.ofNat .U64 ((a.val + b.val) % 18446744069414584321)

@[expose] def fieldSub (a b : U64) : U64 :=
  UScalar.ofNat .U64 ((a.val + (18446744069414584321 - b.val % 18446744069414584321)) % 18446744069414584321)

@[expose] def fieldMul (a b : U64) : U64 :=
  UScalar.ofNat .U64 ((a.val * b.val) % 18446744069414584321)

@[expose] def extZero : Ext4 := ⟨0#u64, 0#u64, 0#u64, 0#u64⟩
@[expose] def extOne : Ext4 := ⟨1#u64, 0#u64, 0#u64, 0#u64⟩

@[expose] def extAdd (x y : Ext4) : Ext4 :=
  ⟨fieldAdd x.a y.a, fieldAdd x.b y.b, fieldAdd x.c y.c, fieldAdd x.d y.d⟩

@[expose] def extSub (x y : Ext4) : Ext4 :=
  ⟨fieldSub x.a y.a, fieldSub x.b y.b, fieldSub x.c y.c, fieldSub x.d y.d⟩

@[expose] def extScale (x : Ext4) (s : U64) : Ext4 :=
  ⟨fieldMul x.a s, fieldMul x.b s, fieldMul x.c s, fieldMul x.d s⟩

@[expose] def extMul (x y : Ext4) : Ext4 :=
  ⟨fieldAdd (fieldMul x.a y.a) (fieldMul 7#u64 (fieldAdd (fieldAdd (fieldMul x.b y.d) (fieldMul x.c y.c)) (fieldMul x.d y.b))),
   fieldAdd (fieldAdd (fieldMul x.a y.b) (fieldMul x.b y.a)) (fieldMul 7#u64 (fieldAdd (fieldMul x.c y.d) (fieldMul x.d y.c))),
   fieldAdd (fieldAdd (fieldAdd (fieldMul x.a y.c) (fieldMul x.b y.b)) (fieldMul x.c y.a)) (fieldMul 7#u64 (fieldMul x.d y.d)),
   fieldAdd (fieldAdd (fieldMul x.a y.d) (fieldMul x.b y.c)) (fieldAdd (fieldMul x.c y.b) (fieldMul x.d y.a))⟩

@[expose] def hornerSpec (coeffs : List Ext4) (z : U64) (init : Ext4 := extZero) : Ext4 :=
  coeffs.foldr (fun c acc => extAdd (extScale acc z) c) init

@[expose] def evalPolyAscending : List Ext4 → U64 → Ext4
  | [], _ => extZero
  | c :: rest, z => extAdd c (extScale (evalPolyAscending rest z) z)

end qsag_whir_verified.proofs
