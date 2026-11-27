module
public import QsagWhirVerified.Types
public section
namespace qsag_whir_verified
@[ext]
theorem Fp5.ext {x y : Fp5}
    (h0 : x.c0 = y.c0) (h1 : x.c1 = y.c1) (h2 : x.c2 = y.c2)
    (h3 : x.c3 = y.c3) (h4 : x.c4 = y.c4) : x = y := by
  cases x; cases y; subst h0 h1 h2 h3 h4; rfl

instance : DecidableEq Fp5 := fun x y =>
  match decEq x.c0 y.c0 with
  | isFalse h => isFalse (fun e => h (congrArg Fp5.c0 e))
  | isTrue h0 =>
    match decEq x.c1 y.c1 with
    | isFalse h => isFalse (fun e => h (congrArg Fp5.c1 e))
    | isTrue h1 =>
      match decEq x.c2 y.c2 with
      | isFalse h => isFalse (fun e => h (congrArg Fp5.c2 e))
      | isTrue h2 =>
        match decEq x.c3 y.c3 with
        | isFalse h => isFalse (fun e => h (congrArg Fp5.c3 e))
        | isTrue h3 =>
          match decEq x.c4 y.c4 with
          | isFalse h => isFalse (fun e => h (congrArg Fp5.c4 e))
          | isTrue h4 => isTrue (Fp5.ext h0 h1 h2 h3 h4)

end qsag_whir_verified
end
