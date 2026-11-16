module
public import Qsag.Machine.ElfFixtures
import Qsag.Tactic.AssuranceKit
public section
namespace Qsag
attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe
set_option autoImplicit false
set_option maxRecDepth 65536
/-! ## §0. Tail-recursive list helpers (shared with the instruction decoders) -/

/-- Tail-recursive list length (`O(1)` WHNF stack depth on multi-kilobyte binary streams). -/
@[expose] def lenTRLoop : List UInt8 → Nat → Nat
  | [], acc => acc
  | _ :: xs, acc => lenTRLoop xs (acc + 1)

@[expose] def lenTR (xs : List UInt8) : Nat :=
  lenTRLoop xs 0

private theorem lenTRLoop_eq : ∀ (xs : List UInt8) (acc : Nat),
    lenTRLoop xs acc = acc + xs.length
  | [], acc => by simp [lenTRLoop]
  | _ :: xs, acc => by
    simp only [lenTRLoop, lenTRLoop_eq xs (acc + 1), List.length_cons]
    omega

theorem lenTR_eq (xs : List UInt8) : lenTR xs = xs.length := by
  simpa [lenTR] using lenTRLoop_eq xs 0

/-- Tail-recursive prefix slice (`O(1)` WHNF stack depth on multi-kilobyte `.text` sections). -/
@[expose] def takeTRLoop : Nat → List UInt8 → List UInt8 → List UInt8
  | 0, _, acc => acc.reverse
  | _ + 1, [], acc => acc.reverse
  | n + 1, x :: xs, acc => takeTRLoop n xs (x :: acc)

@[expose] def takeTR (n : Nat) (xs : List UInt8) : List UInt8 :=
  takeTRLoop n xs []

private theorem takeTRLoop_eq : ∀ (n : Nat) (xs acc : List UInt8),
    takeTRLoop n xs acc = acc.reverse ++ xs.take n
  | 0, _, acc => by simp [takeTRLoop]
  | _ + 1, [], acc => by simp [takeTRLoop]
  | n + 1, x :: xs, acc => by
    simp [takeTRLoop, takeTRLoop_eq n xs (x :: acc), List.append_assoc]

theorem takeTR_eq (n : Nat) (xs : List UInt8) : takeTR n xs = xs.take n := by
  simpa [takeTR] using takeTRLoop_eq n xs []

/-! ## §1. Indexed byte source -/

/-- A byte string presented as its length and an index function. Reads at `i ≥ len` are
    unspecified; every parser read below is bounds-checked first. -/
structure Bytes where
  len : Nat
  get : Nat → UInt8

namespace Bytes

/-- Little-endian natural number as bytes: byte `i` is `(n >>> (8 * i)) % 256`. -/
@[expose] def ofNat (len n : Nat) : Bytes :=
  ⟨len, fun i => UInt8.ofNat (n >>> (8 * i))⟩

@[expose] def ofList (l : List UInt8) : Bytes :=
  ⟨l.length, fun i => l.getD i 0⟩

@[expose] def drop (k : Nat) (b : Bytes) : Bytes :=
  ⟨b.len - k, fun i => b.get (k + i)⟩

@[expose] def take (n : Nat) (b : Bytes) : Bytes :=
  ⟨if n ≤ b.len then n else b.len, b.get⟩

/-- `n` consecutive bytes starting at index `i`, produced front to back. -/
@[expose] def listFrom (get : Nat → UInt8) : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, i => get i :: listFrom get n (i + 1)

@[expose] def toList (b : Bytes) : List UInt8 :=
  listFrom b.get b.len 0

/-- The `n` bytes at `[off, off + n)`. -/
@[expose] def slice (b : Bytes) (off n : Nat) : List UInt8 :=
  listFrom b.get n off

theorem listFrom_length (get : Nat → UInt8) : ∀ (n i : Nat), (listFrom get n i).length = n
  | 0, _ => rfl
  | n + 1, i => by simp only [listFrom, List.length_cons, listFrom_length get n (i + 1)]

theorem listFrom_congr {g h : Nat → UInt8} : ∀ (n i : Nat),
    (∀ j, i ≤ j → j < i + n → g j = h j) → listFrom g n i = listFrom h n i
  | 0, _, _ => rfl
  | n + 1, i, hEq => by
    simp only [listFrom]
    rw [hEq i (Nat.le_refl i) (by omega),
      listFrom_congr n (i + 1) (fun j h1 h2 => hEq j (by omega) (by omega))]

theorem slice_length (b : Bytes) (off n : Nat) : (b.slice off n).length = n :=
  listFrom_length b.get n off

private theorem listFrom_ofList : ∀ (l : List UInt8) (n i : Nat), i + n ≤ l.length →
    listFrom (fun j => l.getD j 0) n i = (l.drop i).take n
  | _, 0, _, _ => by simp [listFrom]
  | l, n + 1, i, h => by
    have hi : i < l.length := by omega
    have hd : l.drop i = l[i] :: l.drop (i + 1) := List.drop_eq_getElem_cons hi
    simp only [listFrom]
    rw [hd, List.take_succ_cons, listFrom_ofList l n (i + 1) (by omega)]
    congr 1
    simp [List.getD, List.getElem?_eq_getElem hi]

/-- The list view of `ofList` is the original list. -/
theorem toList_ofList (l : List UInt8) : (ofList l).toList = l := by
  have h := listFrom_ofList l l.length 0 (by omega)
  simpa [toList, ofList] using h

/-- On a list-backed source, `slice` is `drop` then `take`. -/
theorem slice_ofList (l : List UInt8) (off n : Nat) (h : off + n ≤ l.length) :
    (ofList l).slice off n = (l.drop off).take n :=
  listFrom_ofList l n off h

end Bytes


end Qsag
