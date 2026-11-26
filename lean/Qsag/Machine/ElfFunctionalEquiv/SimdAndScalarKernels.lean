module

public import Qsag.Machine.ElfFunctionalEquiv.ScalarAndArchive
import Qsag.Tactic.Prelude
import Qsag.Tactic.AssuranceKit

public section

namespace Qsag

attribute [-instance] UInt8.instLawfulEqOrd UInt64.instLawfulEqOrd BitVec.instLawfulEqOrd
  UInt64.instLawfulOrderOrd String.instLawfulEqOrd
  Std.instLawfulEqOrdOfLawfulOrderOrdOfAntisymmLe
set_option autoImplicit false
set_option maxRecDepth 65536

attribute [local simp]
  X86BvState.ofX86State Arm64BvState.ofArm64State bank16OfU64 bank32OfU64
  b16get_0 b16get_1 b16get_2 b16get_3 b16get_4 b16get_5 b16get_6 b16get_7
  b16get_8 b16get_9 b16get_10 b16get_11 b16get_12 b16get_13 b16get_14 b16get_15
  b32get_0 b32get_1 b32get_2


/-! ## §5. Real `.rlib` SIMD & Architectural-Control Kernels (`DIT`, `GFNI ↔ BinaryTower`, `SHA3 NEON ↔ Keccak`) -/

/-! ### §5.1 Byte-Memory Framing & `GFNI ↔ BinaryTower` $\mathbb{F}_2$-Bilinear Refinement -/

private theorem u8_toU64_bv (b : UInt8) : b.toUInt64.toBitVec = b.toBitVec.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq; simp [UInt8.toNat_toBitVec]

private theorem u64_toU8_bv (w : UInt64) : w.toUInt8.toBitVec = w.toBitVec.setWidth 8 := by
  apply BitVec.eq_of_toNat_eq; simp [UInt64.toNat_toBitVec]

theorem getByte64_bv (w : UInt64) (i : Nat) (hi : i < 8) :
    (getByte64 w i).toBitVec = (w.toBitVec >>> (i * 8)).setWidth 8 := by
  unfold getByte64
  rw [u64_toU8_bv]
  congr 1
  have hsh : (UInt64.ofNat (i * 8)).toNat % 64 = i * 8 := by
    match i, hi with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => decide
    | n + 8, h => exact absurd h (by omega)
  change (w.toBitVec >>> ((UInt64.ofNat (i * 8)).toNat % 64)) = w.toBitVec >>> (i * 8)
  rw [hsh]

private theorem u8_shl_bit (b : UInt8) (sh : UInt64) (j : Nat) (_hj : j < 64)
    (hsh : sh.toNat ≤ 56) :
    ((b.toUInt64 <<< sh).toBitVec)[j] =
      if sh.toNat ≤ j ∧ j < sh.toNat + 8 then b.toBitVec.getLsbD (j - sh.toNat) else false := by
  have hmod : sh.toNat % 64 = sh.toNat := by omega
  change ((b.toUInt64.toBitVec <<< (sh.toNat % 64)))[j] = _
  rw [hmod, u8_toU64_bv, BitVec.getElem_shiftLeft, BitVec.getElem_setWidth]
  by_cases h1 : j < sh.toNat
  · have h2 : ¬ (sh.toNat ≤ j ∧ j < sh.toNat + 8) := fun h => by omega
    simp [h1, h2]
  · simp only [h1, decide_false, Bool.not_false, Bool.true_and]
    by_cases h2 : j - sh.toNat < 8
    · have h3 : sh.toNat ≤ j ∧ j < sh.toNat + 8 := ⟨by omega, by omega⟩
      simp [h3]
    · have h3 : ¬ (sh.toNat ≤ j ∧ j < sh.toNat + 8) := fun h => by omega
      have hge : b.toBitVec.getLsbD (j - sh.toNat) = false :=
        BitVec.getLsbD_of_ge b.toBitVec (j - sh.toNat) (by omega)
      simp [h3, hge]

theorem getByte64_mapBytes64 (f : Nat → UInt8) (i : Nat) (hi : i < 8) :
    getByte64 (mapBytes64 f) i = f i := by
  apply UInt8.eq_of_toBitVec_eq
  rw [getByte64_bv _ i hi]
  ext r hr
  simp only [BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight]
  have hjr : i * 8 + r < 64 := by omega
  rw [BitVec.getLsbD_eq_getElem hjr]
  unfold mapBytes64
  have h0 : ∀ (b : UInt8) (j : Nat) (hj : j < 64), (b.toUInt64.toBitVec)[j] =
      if j < 8 then b.toBitVec.getLsbD j else false := by
    intro b j _hj
    rw [u8_toU64_bv, BitVec.getElem_setWidth]
    by_cases h : j < 8
    · simp [h]
    · simp [h, BitVec.getLsbD_of_ge b.toBitVec j (by omega)]
  simp only [UInt64.toBitVec_or, BitVec.getElem_or, h0,
    u8_shl_bit _ 8 _ _ (by decide), u8_shl_bit _ 16 _ _ (by decide),
    u8_shl_bit _ 24 _ _ (by decide), u8_shl_bit _ 32 _ _ (by decide),
    u8_shl_bit _ 40 _ _ (by decide), u8_shl_bit _ 48 _ _ (by decide),
    u8_shl_bit _ 56 _ _ (by decide)]
  have hsh8 : (8 : UInt64).toNat = 8 := rfl
  have hsh16 : (16 : UInt64).toNat = 16 := rfl
  have hsh24 : (24 : UInt64).toNat = 24 := rfl
  have hsh32 : (32 : UInt64).toNat = 32 := rfl
  have hsh40 : (40 : UInt64).toNat = 40 := rfl
  have hsh48 : (48 : UInt64).toNat = 48 := rfl
  have hsh56 : (56 : UInt64).toNat = 56 := rfl
  simp only [hsh8, hsh16, hsh24, hsh32, hsh40, hsh48, hsh56, ← BitVec.getLsbD_eq_getElem hr]
  match i, hi, r, hr with
  | 0, _, 0, _ | 0, _, 1, _ | 0, _, 2, _ | 0, _, 3, _ | 0, _, 4, _ | 0, _, 5, _ | 0, _, 6, _ | 0, _, 7, _
  | 1, _, 0, _ | 1, _, 1, _ | 1, _, 2, _ | 1, _, 3, _ | 1, _, 4, _ | 1, _, 5, _ | 1, _, 6, _ | 1, _, 7, _
  | 2, _, 0, _ | 2, _, 1, _ | 2, _, 2, _ | 2, _, 3, _ | 2, _, 4, _ | 2, _, 5, _ | 2, _, 6, _ | 2, _, 7, _
  | 3, _, 0, _ | 3, _, 1, _ | 3, _, 2, _ | 3, _, 3, _ | 3, _, 4, _ | 3, _, 5, _ | 3, _, 6, _ | 3, _, 7, _
  | 4, _, 0, _ | 4, _, 1, _ | 4, _, 2, _ | 4, _, 3, _ | 4, _, 4, _ | 4, _, 5, _ | 4, _, 6, _ | 4, _, 7, _
  | 5, _, 0, _ | 5, _, 1, _ | 5, _, 2, _ | 5, _, 3, _ | 5, _, 4, _ | 5, _, 5, _ | 5, _, 6, _ | 5, _, 7, _
  | 6, _, 0, _ | 6, _, 1, _ | 6, _, 2, _ | 6, _, 3, _ | 6, _, 4, _ | 6, _, 5, _ | 6, _, 6, _ | 6, _, 7, _
  | 7, _, 0, _ | 7, _, 1, _ | 7, _, 2, _ | 7, _, 3, _ | 7, _, 4, _ | 7, _, 5, _ | 7, _, 6, _ | 7, _, 7, _ =>
    simp
  | n + 8, h, _, _ => exact absurd h (by omega)
  | _, _, n + 8, h => exact absurd h (by omega)

theorem mapBytes64_getByte64 (w : UInt64) : mapBytes64 (getByte64 w) = w := by
  apply UInt64.eq_of_toBitVec_eq
  ext j hj
  have hq : j / 8 < 8 := by omega
  have hr : j % 8 < 8 := by omega
  have h1 := congrArg (fun b : UInt8 => b.toBitVec[j % 8]'hr)
    (getByte64_mapBytes64 (getByte64 w) (j / 8) hq)
  simp only [getByte64_bv _ (j / 8) hq, BitVec.getElem_setWidth, BitVec.getLsbD_ushiftRight] at h1
  rw [← BitVec.getLsbD_eq_getElem hj, ← BitVec.getLsbD_eq_getElem hj,
    show j = j / 8 * 8 + j % 8 by omega]
  exact h1

theorem u64_add_ofNat_inj {addr : UInt64} {i j : Nat}
    (hi : i < 0x10000000000000000) (hj : j < 0x10000000000000000)
    (h : addr + UInt64.ofNat i = addr + UInt64.ofNat j) : i = j := by
  have hsub : (addr + UInt64.ofNat i) - addr = (addr + UInt64.ofNat j) - addr :=
    congrArg (· - addr) h
  have hcancel : ∀ x : UInt64, (addr + x) - addr = x := fun x => by
    apply UInt64.eq_of_toBitVec_eq
    change (addr.toBitVec + x.toBitVec) - addr.toBitVec = x.toBitVec
    rw [BitVec.add_comm, BitVec.add_sub_cancel]
  rw [hcancel, hcancel] at hsub
  have hn := congrArg UInt64.toNat hsub
  have hmod1 : (UInt64.ofNat i).toNat = i := Nat.mod_eq_of_lt hi
  have hmod2 : (UInt64.ofNat j).toNat = j := Nat.mod_eq_of_lt hj
  omega

theorem u64_add_ofNat_assoc (addr : UInt64) (a b : Nat)
    (hab : a + b < 0x10000000000000000) :
    (addr + UInt64.ofNat a) + UInt64.ofNat b = addr + UInt64.ofNat (a + b) := by
  apply UInt64.eq_of_toBitVec_eq
  simp only [UInt64.toBitVec_add, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  have ha : (UInt64.ofNat a).toNat = a := Nat.mod_eq_of_lt (by omega)
  have hb : (UInt64.ofNat b).toNat = b := Nat.mod_eq_of_lt (by omega)
  simp [UInt64.toNat_toBitVec, ha, hb, Nat.mod_eq_of_lt hab]

theorem readMem64_eq_mapBytes64 (mem : UInt64 → UInt8) (addr : UInt64) :
    readMem64 mem addr = mapBytes64 (fun i => mem (addr + UInt64.ofNat i)) := by
  unfold readMem64 mapBytes64
  dsimp only
  have h0 : addr + UInt64.ofNat 0 = addr := by apply UInt64.eq_of_toBitVec_eq; simp
  rw [h0]
  rfl

theorem getByte64_readMem64 (mem : UInt64 → UInt8) (addr : UInt64) (i : Nat) (hi : i < 8) :
    getByte64 (readMem64 mem addr) i = mem (addr + UInt64.ofNat i) := by
  rw [readMem64_eq_mapBytes64, getByte64_mapBytes64 _ i hi]

theorem writeMem64_at (mem : UInt64 → UInt8) (addr : UInt64) (v : UInt64) (i : Nat) (hi : i < 8) :
    writeMem64 mem addr v (addr + UInt64.ofNat i) = getByte64 v i := by
  unfold writeMem64 writeMem8 getByte64
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => simp
  | n + 8, h => exact absurd h (by omega)

theorem writeMem64_outside (mem : UInt64 → UInt8) (addr : UInt64) (v : UInt64) (a : UInt64)
    (ha : ∀ i : Nat, i < 8 → a ≠ addr + UInt64.ofNat i) :
    writeMem64 mem addr v a = mem a := by
  have ha0 : a ≠ addr := by
    have h0 : addr + UInt64.ofNat 0 = addr := by apply UInt64.eq_of_toBitVec_eq; simp
    simpa [h0] using ha 0 (by decide)
  have ha1 : a ≠ addr + 1 := ha 1 (by decide)
  have ha2 : a ≠ addr + 2 := ha 2 (by decide)
  have ha3 : a ≠ addr + 3 := ha 3 (by decide)
  have ha4 : a ≠ addr + 4 := ha 4 (by decide)
  have ha5 : a ≠ addr + 5 := ha 5 (by decide)
  have ha6 : a ≠ addr + 6 := ha 6 (by decide)
  have ha7 : a ≠ addr + 7 := ha 7 (by decide)
  unfold writeMem64 writeMem8
  simp [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7]

theorem readMem64_writeMem64_same (mem : UInt64 → UInt8) (addr v : UInt64) :
    readMem64 (writeMem64 mem addr v) addr = v := by
  rw [readMem64_eq_mapBytes64]
  conv => rhs; rw [← mapBytes64_getByte64 v]
  unfold mapBytes64
  simp only [writeMem64_at mem addr v 0 (by decide), writeMem64_at mem addr v 1 (by decide),
    writeMem64_at mem addr v 2 (by decide), writeMem64_at mem addr v 3 (by decide),
    writeMem64_at mem addr v 4 (by decide), writeMem64_at mem addr v 5 (by decide),
    writeMem64_at mem addr v 6 (by decide), writeMem64_at mem addr v 7 (by decide)]

theorem readMem64_writeMem64_disjoint (mem : UInt64 → UInt8) (a1 a2 v : UInt64)
    (hd : ∀ i j : Nat, i < 8 → j < 8 → a1 + UInt64.ofNat i ≠ a2 + UInt64.ofNat j) :
    readMem64 (writeMem64 mem a2 v) a1 = readMem64 mem a1 := by
  rw [readMem64_eq_mapBytes64, readMem64_eq_mapBytes64]
  unfold mapBytes64
  simp only [writeMem64_outside mem a2 v _ (hd 0 · (by decide)),
    writeMem64_outside mem a2 v _ (hd 1 · (by decide)),
    writeMem64_outside mem a2 v _ (hd 2 · (by decide)),
    writeMem64_outside mem a2 v _ (hd 3 · (by decide)),
    writeMem64_outside mem a2 v _ (hd 4 · (by decide)),
    writeMem64_outside mem a2 v _ (hd 5 · (by decide)),
    writeMem64_outside mem a2 v _ (hd 6 · (by decide)),
    writeMem64_outside mem a2 v _ (hd 7 · (by decide))]

theorem writeMem256_at (mem : UInt64 → UInt8) (addr : UInt64) (v : Vec256) (k : Nat) (hk : k < 32) :
    writeMem256 mem addr v (addr + UInt64.ofNat k) =
      if k < 8 then getByte64 v.w0 k
      else if k < 16 then getByte64 v.w1 (k - 8)
      else if k < 24 then getByte64 v.w2 (k - 16)
      else getByte64 v.w3 (k - 24) := by
  unfold writeMem256
  change writeMem64 (writeMem64 (writeMem64 (writeMem64 mem addr v.w0)
    (addr + UInt64.ofNat 8) v.w1) (addr + UInt64.ofNat 16) v.w2)
    (addr + UInt64.ofNat 24) v.w3 (addr + UInt64.ofNat k) = _
  have hout : ∀ (base : Nat) (_hbase : base ≤ 24) (_hlt : k < base)
      (m : UInt64 → UInt8) (w : UInt64),
      writeMem64 m (addr + UInt64.ofNat base) w (addr + UInt64.ofNat k) = m (addr + UInt64.ofNat k) := by
    intro base _hbase _hlt m w
    apply writeMem64_outside
    intro i _hi heq
    rw [u64_add_ofNat_assoc addr base i (by omega)] at heq
    have := u64_add_ofNat_inj (by omega) (by omega) heq
    omega
  by_cases h0 : k < 8
  · rw [hout 24 (by decide) (by omega), hout 16 (by decide) (by omega), hout 8 (by decide) (by omega)]
    rw [writeMem64_at mem addr v.w0 k h0]
    simp [h0]
  · by_cases h1 : k < 16
    · rw [hout 24 (by decide) (by omega), hout 16 (by decide) (by omega)]
      have hk8 : addr + UInt64.ofNat k = (addr + UInt64.ofNat 8) + UInt64.ofNat (k - 8) := by
        rw [u64_add_ofNat_assoc addr 8 (k - 8) (by omega), show 8 + (k - 8) = k by omega]
      rw [hk8, writeMem64_at _ (addr + UInt64.ofNat 8) v.w1 (k - 8) (by omega)]
      simp [h0, h1]
    · by_cases h2 : k < 24
      · rw [hout 24 (by decide) (by omega)]
        have hk16 : addr + UInt64.ofNat k = (addr + UInt64.ofNat 16) + UInt64.ofNat (k - 16) := by
          rw [u64_add_ofNat_assoc addr 16 (k - 16) (by omega), show 16 + (k - 16) = k by omega]
        rw [hk16, writeMem64_at _ (addr + UInt64.ofNat 16) v.w2 (k - 16) (by omega)]
        simp [h0, h1, h2]
      · have hk24 : addr + UInt64.ofNat k = (addr + UInt64.ofNat 24) + UInt64.ofNat (k - 24) := by
          rw [u64_add_ofNat_assoc addr 24 (k - 24) (by omega), show 24 + (k - 24) = k by omega]
        rw [hk24, writeMem64_at _ (addr + UInt64.ofNat 24) v.w3 (k - 24) (by omega)]
        simp [h0, h1, h2]

theorem writeMem256_outside (mem : UInt64 → UInt8) (addr : UInt64) (v : Vec256) (a : UInt64)
    (ha : ∀ k : Nat, k < 32 → a ≠ addr + UInt64.ofNat k) :
    writeMem256 mem addr v a = mem a := by
  unfold writeMem256
  change writeMem64 (writeMem64 (writeMem64 (writeMem64 mem addr v.w0)
    (addr + UInt64.ofNat 8) v.w1) (addr + UInt64.ofNat 16) v.w2)
    (addr + UInt64.ofNat 24) v.w3 a = mem a
  have hout : ∀ (base : Nat) (_hb : base ≤ 24) (m : UInt64 → UInt8) (w : UInt64),
      writeMem64 m (addr + UInt64.ofNat base) w a = m a := by
    intro base _hb m w
    apply writeMem64_outside
    intro i _hi heq
    rw [u64_add_ofNat_assoc addr base i (by omega)] at heq
    exact ha (base + i) (by omega) heq
  rw [hout 24 (by decide), hout 16 (by decide), hout 8 (by decide)]
  exact writeMem64_outside mem addr v.w0 a (fun i hi => ha i (by omega))

theorem writeMem128_outside (mem : UInt64 → UInt8) (addr : UInt64) (v : Vec128) (a : UInt64)
    (ha : ∀ k : Nat, k < 16 → a ≠ addr + UInt64.ofNat k) :
    writeMem128 mem addr v a = mem a := by
  unfold writeMem128
  rw [writeMem64_outside _ (addr + 8) v.w1 a (fun i _hi heq => by
    change a = (addr + UInt64.ofNat 8) + UInt64.ofNat i at heq
    rw [u64_add_ofNat_assoc addr 8 i (by omega)] at heq
    exact ha (8 + i) (by omega) heq)]
  exact writeMem64_outside mem addr v.w0 a (fun i hi => ha i (by omega))

theorem readMem64_writeMem128_lo (mem : UInt64 → UInt8) (addr : UInt64) (v : Vec128) :
    readMem64 (writeMem128 mem addr v) addr = v.w0 := by
  unfold writeMem128
  rw [readMem64_writeMem64_disjoint _ addr (addr + 8) v.w1 (fun i j _hi _hj heq => by
    change addr + UInt64.ofNat i = (addr + UInt64.ofNat 8) + UInt64.ofNat j at heq
    rw [u64_add_ofNat_assoc addr 8 j (by omega)] at heq
    have := u64_add_ofNat_inj (by omega) (by omega) heq
    omega)]
  exact readMem64_writeMem64_same mem addr v.w0

theorem readMem64_writeMem128_hi (mem : UInt64 → UInt8) (addr : UInt64) (v : Vec128) :
    readMem64 (writeMem128 mem addr v) (addr + 8) = v.w1 := by
  unfold writeMem128
  exact readMem64_writeMem64_same _ (addr + 8) v.w1

theorem readMem64_writeMem128_disjoint (mem : UInt64 → UInt8) (a1 a2 : UInt64) (v : Vec128)
    (hd : ∀ i k : Nat, i < 8 → k < 16 → a1 + UInt64.ofNat i ≠ a2 + UInt64.ofNat k) :
    readMem64 (writeMem128 mem a2 v) a1 = readMem64 mem a1 := by
  rw [readMem64_eq_mapBytes64, readMem64_eq_mapBytes64]
  unfold mapBytes64
  simp only [writeMem128_outside mem a2 v _ (hd 0 · (by decide)),
    writeMem128_outside mem a2 v _ (hd 1 · (by decide)),
    writeMem128_outside mem a2 v _ (hd 2 · (by decide)),
    writeMem128_outside mem a2 v _ (hd 3 · (by decide)),
    writeMem128_outside mem a2 v _ (hd 4 · (by decide)),
    writeMem128_outside mem a2 v _ (hd 5 · (by decide)),
    writeMem128_outside mem a2 v _ (hd 6 · (by decide)),
    writeMem128_outside mem a2 v _ (hd 7 · (by decide))]

/-- Forward basis-change matrix $T \in \mathbb{F}_2^{8 \times 8}$ mapping Wiedemann tower
    `GF(2^8)` (`BinaryTower` level `3`) into Intel GFNI Rijndael $\mathbb{F}_2[z]/(z^8+z^4+z^3+z+1)$. -/
@[expose] def gfniTowerToRijndaelMat : UInt64 := 0x71500a8a86be78ce

/-- Inverse basis-change matrix $T^{-1} \in \mathbb{F}_2^{8 \times 8}$ mapping Intel GFNI Rijndael
    back into Wiedemann tower `GF(2^8)` (`BinaryTower` level `3`). -/
@[expose] def gfniRijndaelToTowerMat : UInt64 := 0xa1e4f8e072a2700c

/-- Single-lane GFNI Wiedemann tower multiplication $T^{-1}(T(x) \cdot_{\text{Rijndael}} T(y))$. -/
@[expose] def gfniTowerMulByte (x y : UInt8) : UInt8 :=
  gfniAffineByte
    (gfniMulByte (gfniAffineByte x gfniTowerToRijndaelMat 0)
                 (gfniAffineByte y gfniTowerToRijndaelMat 0))
    gfniRijndaelToTowerMat 0

theorem u8_and_xor_left (a b m : UInt8) : (a ^^^ b) &&& m = (a &&& m) ^^^ (b &&& m) := by
  apply UInt8.eq_of_toBitVec_eq
  ext i hi
  simp only [UInt8.toBitVec_and, UInt8.toBitVec_xor, BitVec.getElem_and, BitVec.getElem_xor]
  cases m.toBitVec[i] <;> simp

private theorem u8_and_xor_right (x m1 m2 : UInt8) : x &&& (m1 ^^^ m2) = (x &&& m1) ^^^ (x &&& m2) := by
  apply UInt8.eq_of_toBitVec_eq
  ext i hi
  simp only [UInt8.toBitVec_and, UInt8.toBitVec_xor, BitVec.getElem_and, BitVec.getElem_xor]
  cases x.toBitVec[i] <;> simp

private theorem u8_ushr_xor (a b k : UInt8) : (a ^^^ b) >>> k = (a >>> k) ^^^ (b >>> k) := by
  apply UInt8.eq_of_toBitVec_eq
  change (a.toBitVec ^^^ b.toBitVec) >>> (k.toNat % 8) =
    (a.toBitVec >>> (k.toNat % 8)) ^^^ (b.toBitVec >>> (k.toNat % 8))
  exact BitVec.ushiftRight_xor_distrib a.toBitVec b.toBitVec (k.toNat % 8)

private theorem u8_shl_xor_fwd (a b k : UInt8) : (a ^^^ b) <<< k = (a <<< k) ^^^ (b <<< k) := by
  apply UInt8.eq_of_toBitVec_eq
  change (a.toBitVec ^^^ b.toBitVec) <<< (k.toNat % 8) =
    (a.toBitVec <<< (k.toNat % 8)) ^^^ (b.toBitVec <<< (k.toNat % 8))
  exact BitVec.shiftLeft_xor_distrib a.toBitVec b.toBitVec (k.toNat % 8)

private theorem elf_u8_xor_assoc (a b c : UInt8) : (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c) := by
  apply UInt8.eq_of_toBitVec_eq; simp [BitVec.xor_assoc]

theorem u8_xor_four (a b c d : UInt8) : (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  apply UInt8.eq_of_toBitVec_eq
  ext i hi
  simp only [UInt8.toBitVec_xor, BitVec.getElem_xor]
  cases a.toBitVec[i] <;> cases b.toBitVec[i] <;> cases c.toBitVec[i] <;> cases d.toBitVec[i] <;> rfl

private theorem u8_xor8_pair (a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    (a0 ^^^ b0) ^^^ (a1 ^^^ b1) ^^^ (a2 ^^^ b2) ^^^ (a3 ^^^ b3) ^^^
    (a4 ^^^ b4) ^^^ (a5 ^^^ b5) ^^^ (a6 ^^^ b6) ^^^ (a7 ^^^ b7) =
      (a0 ^^^ a1 ^^^ a2 ^^^ a3 ^^^ a4 ^^^ a5 ^^^ a6 ^^^ a7) ^^^
      (b0 ^^^ b1 ^^^ b2 ^^^ b3 ^^^ b4 ^^^ b5 ^^^ b6 ^^^ b7) := by
  rw [u8_xor_four a0 b0 a1 b1]
  rw [u8_xor_four (a0 ^^^ a1) (b0 ^^^ b1) a2 b2]
  rw [u8_xor_four (a0 ^^^ a1 ^^^ a2) (b0 ^^^ b1 ^^^ b2) a3 b3]
  rw [u8_xor_four (a0 ^^^ a1 ^^^ a2 ^^^ a3) (b0 ^^^ b1 ^^^ b2 ^^^ b3) a4 b4]
  rw [u8_xor_four (a0 ^^^ a1 ^^^ a2 ^^^ a3 ^^^ a4) (b0 ^^^ b1 ^^^ b2 ^^^ b3 ^^^ b4) a5 b5]
  rw [u8_xor_four (a0 ^^^ a1 ^^^ a2 ^^^ a3 ^^^ a4 ^^^ a5) (b0 ^^^ b1 ^^^ b2 ^^^ b3 ^^^ b4 ^^^ b5) a6 b6]
  rw [u8_xor_four (a0 ^^^ a1 ^^^ a2 ^^^ a3 ^^^ a4 ^^^ a5 ^^^ a6)
      (b0 ^^^ b1 ^^^ b2 ^^^ b3 ^^^ b4 ^^^ b5 ^^^ b6) a7 b7]

private theorem elf_u8_xor_self (a : UInt8) : a ^^^ a = 0 := by
  apply UInt8.eq_of_toBitVec_eq; simp

private theorem u8_and_ff (x : UInt8) : x &&& 0xFF = x := by
  rcases x with ⟨⟨n⟩⟩; revert n; decide +kernel

theorem u8_basis_decomp (x : UInt8) :
    x = (x &&& 0x01) ^^^ (x &&& 0x02) ^^^ (x &&& 0x04) ^^^ (x &&& 0x08) ^^^
        (x &&& 0x10) ^^^ (x &&& 0x20) ^^^ (x &&& 0x40) ^^^ (x &&& 0x80) := by
  have hff : (0xFF : UInt8) = 0x01 ^^^ 0x02 ^^^ 0x04 ^^^ 0x08 ^^^ 0x10 ^^^ 0x20 ^^^ 0x40 ^^^ 0x80 := by decide
  have hx := (u8_and_ff x).symm
  rw [hff] at hx
  simpa only [u8_and_xor_right] using hx

theorem u8_bit_cases (x m : UInt8)
    (hm : m = 0x01 ∨ m = 0x02 ∨ m = 0x04 ∨ m = 0x08 ∨ m = 0x10 ∨ m = 0x20 ∨ m = 0x40 ∨ m = 0x80) :
    x &&& m = 0 ∨ x &&& m = m := by
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (rcases x with ⟨⟨n⟩⟩; revert n; decide +kernel)

private theorem parityByte_xor (a b : UInt8) : parityByte (a ^^^ b) = parityByte a ^^^ parityByte b := by
  have hy : (a ^^^ b) ^^^ ((a ^^^ b) >>> 4) = (a ^^^ (a >>> 4)) ^^^ (b ^^^ (b >>> 4)) := by
    rw [u8_ushr_xor, u8_xor_four]
  let ya := a ^^^ (a >>> 4); let yb := b ^^^ (b >>> 4)
  have hz : (ya ^^^ yb) ^^^ ((ya ^^^ yb) >>> 2) = (ya ^^^ (ya >>> 2)) ^^^ (yb ^^^ (yb >>> 2)) := by
    rw [u8_ushr_xor, u8_xor_four]
  let za := ya ^^^ (ya >>> 2); let zb := yb ^^^ (yb >>> 2)
  have hw : (za ^^^ zb) ^^^ ((za ^^^ zb) >>> 1) = (za ^^^ (za >>> 1)) ^^^ (zb ^^^ (zb >>> 1)) := by
    rw [u8_ushr_xor, u8_xor_four]
  unfold parityByte; dsimp only
  rw [hy, hz, hw, u8_and_xor_left]

private theorem gfniAffine_t2r_eq (x : UInt8) :
    gfniAffineByte x gfniTowerToRijndaelMat 0 =
      ((parityByte (x &&& 0x71)) <<< 0) ^^^ ((parityByte (x &&& 0x50)) <<< 1) ^^^
      ((parityByte (x &&& 0x0a)) <<< 2) ^^^ ((parityByte (x &&& 0x8a)) <<< 3) ^^^
      ((parityByte (x &&& 0x86)) <<< 4) ^^^ ((parityByte (x &&& 0xbe)) <<< 5) ^^^
      ((parityByte (x &&& 0x78)) <<< 6) ^^^ ((parityByte (x &&& 0xce)) <<< 7) := by
  rcases x with ⟨⟨n⟩⟩; revert n; decide +kernel

private theorem gfniAffine_r2t_eq (x : UInt8) :
    gfniAffineByte x gfniRijndaelToTowerMat 0 =
      ((parityByte (x &&& 0xa1)) <<< 0) ^^^ ((parityByte (x &&& 0xe4)) <<< 1) ^^^
      ((parityByte (x &&& 0xf8)) <<< 2) ^^^ ((parityByte (x &&& 0xe0)) <<< 3) ^^^
      ((parityByte (x &&& 0x72)) <<< 4) ^^^ ((parityByte (x &&& 0xa2)) <<< 5) ^^^
      ((parityByte (x &&& 0x70)) <<< 6) ^^^ ((parityByte (x &&& 0x0c)) <<< 7) := by
  rcases x with ⟨⟨n⟩⟩; revert n; decide +kernel

private theorem gfniAffine_t2r_xor (a b : UInt8) :
    gfniAffineByte (a ^^^ b) gfniTowerToRijndaelMat 0 =
      gfniAffineByte a gfniTowerToRijndaelMat 0 ^^^ gfniAffineByte b gfniTowerToRijndaelMat 0 := by
  simp only [gfniAffine_t2r_eq, u8_and_xor_left, parityByte_xor, u8_shl_xor_fwd]
  exact u8_xor8_pair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

private theorem gfniAffine_r2t_xor (a b : UInt8) :
    gfniAffineByte (a ^^^ b) gfniRijndaelToTowerMat 0 =
      gfniAffineByte a gfniRijndaelToTowerMat 0 ^^^ gfniAffineByte b gfniRijndaelToTowerMat 0 := by
  simp only [gfniAffine_r2t_eq, u8_and_xor_left, parityByte_xor, u8_shl_xor_fwd]
  exact u8_xor8_pair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem xtimeRijndael_xor (a b : UInt8) :
    xtimeRijndael (a ^^^ b) = xtimeRijndael a ^^^ xtimeRijndael b := by
  unfold xtimeRijndael; dsimp only
  rw [u8_shl_xor_fwd, u8_and_xor_left]
  rcases u8_bit_cases a 0x80 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))) with ha | ha <;>
  rcases u8_bit_cases b 0x80 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))) with hb | hb
  · rw [ha, hb]; simp
  · rw [ha, hb]; simp; exact elf_u8_xor_assoc _ _ _
  · rw [ha, hb]; simp
    apply UInt8.eq_of_toBitVec_eq; ext i hi; simp only [UInt8.toBitVec_xor, BitVec.getElem_xor]
    cases (a <<< 1).toBitVec[i] <;> cases (b <<< 1).toBitVec[i] <;> cases (0x1B : UInt8).toBitVec[i] <;> rfl
  · rw [ha, hb, elf_u8_xor_self]; simp
    rw [u8_xor_four, elf_u8_xor_self]; apply UInt8.eq_of_toBitVec_eq; simp

theorem gfniMulByte_xor_left (a1 a2 b : UInt8) :
    gfniMulByte (a1 ^^^ a2) b = gfniMulByte a1 b ^^^ gfniMulByte a2 b := by
  have hIf : ∀ (c : Bool) (u v : UInt8),
      (if c then u ^^^ v else 0) = (if c then u else 0) ^^^ (if c then v else 0) := by
    intro c u v; cases c <;> simp
  unfold gfniMulByte
  simp only [xtimeRijndael_xor, hIf]
  exact u8_xor8_pair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

private theorem gfniMulByte_xor_right (a b1 b2 : UInt8) :
    gfniMulByte a (b1 ^^^ b2) = gfniMulByte a b1 ^^^ gfniMulByte a b2 := by
  have hPick : ∀ (i : UInt8) (ai : UInt8),
      (if ((((b1 ^^^ b2) >>> i) &&& 1) != 0) then ai else 0) =
        (if (((b1 >>> i) &&& 1) != 0) then ai else 0) ^^^ (if (((b2 >>> i) &&& 1) != 0) then ai else 0) := by
    intro i ai
    rw [u8_ushr_xor, u8_and_xor_left]
    rcases u8_bit_cases (b1 >>> i) 0x01 (Or.inl rfl) with h1 | h1 <;>
    rcases u8_bit_cases (b2 >>> i) 0x01 (Or.inl rfl) with h2 | h2 <;>
    (rw [h1, h2]; simp)
  unfold gfniMulByte
  simp only [hPick]
  exact u8_xor8_pair _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

private theorem gfniTowerMulByte_zero_left (y : UInt8) : gfniTowerMulByte 0 y = 0 := by
  rcases y with ⟨⟨n⟩⟩; revert n; decide +kernel

private theorem gfniTowerMulByte_zero_right (x : UInt8) : gfniTowerMulByte x 0 = 0 := by
  rcases x with ⟨⟨n⟩⟩; revert n; decide +kernel

theorem gfniTowerMulByte_xor_left (x1 x2 y : UInt8) :
    gfniTowerMulByte (x1 ^^^ x2) y = gfniTowerMulByte x1 y ^^^ gfniTowerMulByte x2 y := by
  unfold gfniTowerMulByte
  rw [gfniAffine_t2r_xor, gfniMulByte_xor_left, gfniAffine_r2t_xor]

private theorem gfniTowerMulByte_xor_right (x y1 y2 : UInt8) :
    gfniTowerMulByte x (y1 ^^^ y2) = gfniTowerMulByte x y1 ^^^ gfniTowerMulByte x y2 := by
  unfold gfniTowerMulByte
  rw [gfniAffine_t2r_xor, gfniMulByte_xor_right, gfniAffine_r2t_xor]

private theorem unpackTower_xor (k : Nat) (x y : TowerBitVec k) :
    unpackTower k (x ^^^ y) = towerAdd k (unpackTower k x) (unpackTower k y) := by
  apply packTower_injective k
  rw [packTower_unpackTower, packTower_add, packTower_unpackTower, packTower_unpackTower]

theorem mulExec_eq_pack_towerMul (k : Nat) (x y : TowerBitVec k) :
    mulExec k x y = packTower k (towerMul k (unpackTower k x) (unpackTower k y)) := by
  have hx := (packTower_unpackTower k x).symm
  have hy := (packTower_unpackTower k y).symm
  conv => lhs; rw [hx, hy, mulExec_refines]

private theorem mulExec3_zero_left (y : BitVec 8) : mulExec 3 0#8 y = 0#8 := by
  change mulExec 3 (0 : TowerBitVec 3) y = 0
  rw [mulExec_eq_pack_towerMul, unpackTower_zero, towerMul_comm, towerMul_zero, packTower_zero]

private theorem mulExec3_zero_right (x : BitVec 8) : mulExec 3 x 0#8 = 0#8 := by
  change mulExec 3 x (0 : TowerBitVec 3) = 0
  rw [mulExec_eq_pack_towerMul, unpackTower_zero, towerMul_zero, packTower_zero]

private theorem mulExec3_xor_left (x1 x2 y : BitVec 8) :
    mulExec 3 (x1 ^^^ x2) y = mulExec 3 x1 y ^^^ mulExec 3 x2 y := by
  rw [mulExec_eq_pack_towerMul, unpackTower_xor, towerAdd_mul_distrib, packTower_add,
      ← mulExec_eq_pack_towerMul, ← mulExec_eq_pack_towerMul]

private theorem mulExec3_xor_right (x y1 y2 : BitVec 8) :
    mulExec 3 x (y1 ^^^ y2) = mulExec 3 x y1 ^^^ mulExec 3 x y2 := by
  rw [mulExec_eq_pack_towerMul, unpackTower_xor, towerMul_add_distrib, packTower_add,
      ← mulExec_eq_pack_towerMul, ← mulExec_eq_pack_towerMul]

private theorem gfniTowerMulByte_gen_eq (mx : UInt8)
    (hmx : mx = 0x01 ∨ mx = 0x02 ∨ mx = 0x04 ∨ mx = 0x08 ∨ mx = 0x10 ∨ mx = 0x20 ∨ mx = 0x40 ∨ mx = 0x80)
    (y : UInt8) :
    (gfniTowerMulByte mx y).toBitVec = mulExec 3 mx.toBitVec y.toBitVec := by
  have hBit : ∀ (my : UInt8),
      my = 0x01 ∨ my = 0x02 ∨ my = 0x04 ∨ my = 0x08 ∨ my = 0x10 ∨ my = 0x20 ∨ my = 0x40 ∨ my = 0x80 →
      (gfniTowerMulByte mx (y &&& my)).toBitVec = mulExec 3 mx.toBitVec (y &&& my).toBitVec := by
    intro my hmy
    rcases u8_bit_cases y my hmy with h0 | h1
    · rw [h0, gfniTowerMulByte_zero_right]; simp [mulExec3_zero_right]
    · rw [h1]
      rcases hmx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hmy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (rw [mulExec_eq_pack_towerMul]
       simp only [unpackTower, packTower, lowBits.public_eq_1, highBits.public_eq_1, joinBits_eq_append]
       decide +kernel)
  conv => lhs; rw [u8_basis_decomp y]
  conv => rhs; rw [u8_basis_decomp y]
  simp only [gfniTowerMulByte_xor_right, UInt8.toBitVec_xor, mulExec3_xor_right,
    hBit 0x01 (Or.inl rfl),
    hBit 0x02 (Or.inr (Or.inl rfl)),
    hBit 0x04 (Or.inr (Or.inr (Or.inl rfl))),
    hBit 0x08 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
    hBit 0x10 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
    hBit 0x20 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))),
    hBit 0x40 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))),
    hBit 0x80 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))]

/-- Exact $\mathbb{F}_2$-bilinear isomorphism theorem (`0 native_decide`, `0 bv_decide`):
    Intel GFNI Rijndael multiplication conjugated by `gfniTowerToRijndaelMat` /
    `gfniRijndaelToTowerMat` equals `BinaryTower.mulExec 3` for every byte pair `(x, y)`. -/
theorem gfniTowerMulByte_eq_mulExec (x y : UInt8) :
    (gfniTowerMulByte x y).toBitVec = mulExec 3 x.toBitVec y.toBitVec := by
  have hBit : ∀ (mx : UInt8),
      mx = 0x01 ∨ mx = 0x02 ∨ mx = 0x04 ∨ mx = 0x08 ∨ mx = 0x10 ∨ mx = 0x20 ∨ mx = 0x40 ∨ mx = 0x80 →
      (gfniTowerMulByte (x &&& mx) y).toBitVec = mulExec 3 (x &&& mx).toBitVec y.toBitVec := by
    intro mx hmx
    rcases u8_bit_cases x mx hmx with h0 | h1
    · rw [h0, gfniTowerMulByte_zero_left]; simp [mulExec3_zero_left]
    · rw [h1]; exact gfniTowerMulByte_gen_eq mx hmx y
  conv => lhs; rw [u8_basis_decomp x]
  conv => rhs; rw [u8_basis_decomp x]
  simp only [gfniTowerMulByte_xor_left, UInt8.toBitVec_xor, mulExec3_xor_left,
    hBit 0x01 (Or.inl rfl),
    hBit 0x02 (Or.inr (Or.inl rfl)),
    hBit 0x04 (Or.inr (Or.inr (Or.inl rfl))),
    hBit 0x08 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
    hBit 0x10 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
    hBit 0x20 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))),
    hBit 0x40 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))),
    hBit 0x80 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))]

theorem elfSimulates_unpack (k : Nat) (x : TowerBitVec k) : Simulates k (unpackTower k x) x := by
  rw [Simulates.public_eq_1]; exact packTower_unpackTower k x

theorem elfSimulates_pack_eq {k : Nat} {a : TowerElem k} {x : TowerBitVec k}
    (h : Simulates k a x) : packTower k a = x := by
  rw [Simulates.public_eq_1] at h; exact h

/-- `Spec ↔ Exec` refinement connecting GFNI machine instructions directly to `BinaryTower.towerMul 3`. -/
theorem gfniTowerMulByte_simulates_binaryTower (x y : UInt8) :
    Simulates 3 (towerMul 3 (unpackTower 3 x.toBitVec) (unpackTower 3 y.toBitVec))
      (gfniTowerMulByte x y).toBitVec := by
  rw [gfniTowerMulByte_eq_mulExec]
  exact Simulates.mul 3 (elfSimulates_unpack 3 x.toBitVec) (elfSimulates_unpack 3 y.toBitVec)

/-! ### §5.2 `qsag_asm_enable_dit_aarch64` (`N = 3`, `retPc = 8`) -/

def enableDitArmProg : List (DecodedInstr Arm64Instr) := [
  ⟨0, 4, .msrDit 1⟩,
  ⟨4, 4, .isb⟩,
  ⟨8, 4, .ret⟩
]

private theorem enableDitArm_reaches (g : Bank32 UInt64) (v : Bank32 Vec128)
    (cf zf dit : Bool) (m : UInt64 → UInt8) :
    ExecReachesArm64 enableDitArmProg 2
      ⟨0, g, v, cf, zf, dit, false, m⟩
      ⟨8, g, v, cf, zf, true, false, m⟩ := by
  apply StepsArm64.toExecReaches
  exact StepsArm64.cons rfl rfl rfl (StepsArm64.cons rfl rfl rfl (StepsArm64.zero _))


/-! ### §5.3 `qsag_asm_gf256_shamir_mul_gfni` (`x86_64` AVX2 + GFNI `BinaryTower` Shamir Multiplication & Loop) -/

def gf256MulGfniProg : List (DecodedInstr X86Instr) := [
  ⟨0, 10, .movImm true 0 0x71500a8a86be78ce⟩,
  ⟨10, 5, .vmovGprToXmm true 14 0⟩,
  ⟨15, 5, .vpbroadcast true true 14 14⟩,
  ⟨20, 10, .movImm true 0 0xa1e4f8e072a2700c⟩,
  ⟨30, 5, .vmovGprToXmm true 15 0⟩,
  ⟨35, 5, .vpbroadcast true true 15 15⟩,
  ⟨40, 4, .vload true 0 (.baseDisp 6 0)⟩,
  ⟨44, 4, .vload true 1 (.baseDisp 2 0)⟩,
  ⟨48, 6, .vgf2p8affineqb true 0 0 14 0⟩,
  ⟨54, 6, .vgf2p8affineqb true 1 1 14 0⟩,
  ⟨60, 5, .vbinOp .vgf2p8mulb true 2 0 1⟩,
  ⟨65, 6, .vgf2p8affineqb true 2 2 15 0⟩,
  ⟨71, 4, .vstore true 2 (.baseDisp 7 0)⟩,
  ⟨75, 4, .aluImm .add true 6 32⟩,
  ⟨79, 4, .aluImm .add true 2 32⟩,
  ⟨83, 4, .aluImm .add true 7 32⟩,
  ⟨87, 3, .incDec false true 1⟩,
  ⟨90, 2, .jcc 5 40⟩,
  ⟨92, 4, .vbinOp .vpxor true 0 0 0⟩,
  ⟨96, 4, .vbinOp .vpxor true 1 1 1⟩,
  ⟨100, 4, .vbinOp .vpxor true 2 2 2⟩,
  ⟨104, 5, .vbinOp .vpxor true 14 14 14⟩,
  ⟨109, 5, .vbinOp .vpxor true 15 15 15⟩,
  ⟨114, 3, .vzeroupper⟩,
  ⟨117, 1, .ret⟩
]

def gf256MulGfniCoreProg : List (DecodedInstr X86Instr) :=
  gf256MulGfniProg.take 23

@[expose] def gf256MulGfniVec (vA vB : Vec256) : Vec256 :=
  let mT2R : Vec256 := ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩
  let mR2T : Vec256 := ⟨gfniRijndaelToTowerMat, gfniRijndaelToTowerMat, gfniRijndaelToTowerMat, gfniRijndaelToTowerMat⟩
  gfniAffineVec256 (mapBytesVec256 (gfniAffineVec256 vA mT2R 0) (gfniAffineVec256 vB mT2R 0) gfniMulByte) mR2T 0

@[expose] def gf256MulGfniStepMem (mem : UInt64 → UInt8) (dst srcA srcB : UInt64) : UInt64 → UInt8 :=
  writeMem256 mem dst (gf256MulGfniVec (readMem256 mem srcA) (readMem256 mem srcB))

@[expose] def gf256MulGfniIterMem : Nat → (UInt64 → UInt8) → UInt64 → UInt64 → UInt64 → (UInt64 → UInt8)
  | 0, mem, _, _, _ => mem
  | k + 1, mem, dst, srcA, srcB =>
    gf256MulGfniIterMem k (gf256MulGfniStepMem mem dst srcA srcB) (dst + 32) (srcA + 32) (srcB + 32)

theorem gf256MulGfniVec_lane_byte (vA vB : Vec256) (r : Nat) (hr : r < 8) :
    getByte64 (gf256MulGfniVec vA vB).w0 r =
        gfniTowerMulByte (getByte64 vA.w0 r) (getByte64 vB.w0 r) ∧
    getByte64 (gf256MulGfniVec vA vB).w1 r =
        gfniTowerMulByte (getByte64 vA.w1 r) (getByte64 vB.w1 r) ∧
    getByte64 (gf256MulGfniVec vA vB).w2 r =
        gfniTowerMulByte (getByte64 vA.w2 r) (getByte64 vB.w2 r) ∧
    getByte64 (gf256MulGfniVec vA vB).w3 r =
        gfniTowerMulByte (getByte64 vA.w3 r) (getByte64 vB.w3 r) := by
  unfold gf256MulGfniVec gfniAffineVec256 mapBytesVec256 gfniTowerMulByte
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    rw [getByte64_mapBytes64 _ r hr, getByte64_mapBytes64 _ r hr,
        getByte64_mapBytes64 _ r hr, getByte64_mapBytes64 _ r hr]

theorem gf256MulGfniStepMem_at (mem : UInt64 → UInt8) (dst srcA srcB : UInt64) (k : Nat) (hk : k < 32) :
    gf256MulGfniStepMem mem dst srcA srcB (dst + UInt64.ofNat k) =
      gfniTowerMulByte (mem (srcA + UInt64.ofNat k)) (mem (srcB + UInt64.ofNat k)) := by
  unfold gf256MulGfniStepMem
  rw [writeMem256_at _ dst _ k hk]
  by_cases h0 : k < 8
  · simp only [h0, ↓reduceIte]
    rw [(gf256MulGfniVec_lane_byte _ _ k h0).1]
    unfold readMem256; dsimp only
    rw [getByte64_readMem64 mem srcA k h0, getByte64_readMem64 mem srcB k h0]
  · by_cases h1 : k < 16
    · simp only [h0, h1, ↓reduceIte]
      rw [(gf256MulGfniVec_lane_byte _ _ (k - 8) (by omega)).2.1]
      unfold readMem256; dsimp only
      rw [getByte64_readMem64 mem (srcA + 8) (k - 8) (by omega),
          getByte64_readMem64 mem (srcB + 8) (k - 8) (by omega)]
      have ha : (srcA + 8) + UInt64.ofNat (k - 8) = srcA + UInt64.ofNat k := by
        change (srcA + UInt64.ofNat 8) + UInt64.ofNat (k - 8) = srcA + UInt64.ofNat k
        rw [u64_add_ofNat_assoc srcA 8 (k - 8) (by omega), show 8 + (k - 8) = k by omega]
      have hb : (srcB + 8) + UInt64.ofNat (k - 8) = srcB + UInt64.ofNat k := by
        change (srcB + UInt64.ofNat 8) + UInt64.ofNat (k - 8) = srcB + UInt64.ofNat k
        rw [u64_add_ofNat_assoc srcB 8 (k - 8) (by omega), show 8 + (k - 8) = k by omega]
      rw [ha, hb]
    · by_cases h2 : k < 24
      · simp only [h0, h1, h2, ↓reduceIte]
        rw [(gf256MulGfniVec_lane_byte _ _ (k - 16) (by omega)).2.2.1]
        unfold readMem256; dsimp only
        rw [getByte64_readMem64 mem (srcA + 16) (k - 16) (by omega),
            getByte64_readMem64 mem (srcB + 16) (k - 16) (by omega)]
        have ha : (srcA + 16) + UInt64.ofNat (k - 16) = srcA + UInt64.ofNat k := by
          change (srcA + UInt64.ofNat 16) + UInt64.ofNat (k - 16) = srcA + UInt64.ofNat k
          rw [u64_add_ofNat_assoc srcA 16 (k - 16) (by omega), show 16 + (k - 16) = k by omega]
        have hb : (srcB + 16) + UInt64.ofNat (k - 16) = srcB + UInt64.ofNat k := by
          change (srcB + UInt64.ofNat 16) + UInt64.ofNat (k - 16) = srcB + UInt64.ofNat k
          rw [u64_add_ofNat_assoc srcB 16 (k - 16) (by omega), show 16 + (k - 16) = k by omega]
        rw [ha, hb]
      · simp only [h0, h1, h2, ↓reduceIte]
        rw [(gf256MulGfniVec_lane_byte _ _ (k - 24) (by omega)).2.2.2]
        unfold readMem256; dsimp only
        rw [getByte64_readMem64 mem (srcA + 24) (k - 24) (by omega),
            getByte64_readMem64 mem (srcB + 24) (k - 24) (by omega)]
        have ha : (srcA + 24) + UInt64.ofNat (k - 24) = srcA + UInt64.ofNat k := by
          change (srcA + UInt64.ofNat 24) + UInt64.ofNat (k - 24) = srcA + UInt64.ofNat k
          rw [u64_add_ofNat_assoc srcA 24 (k - 24) (by omega), show 24 + (k - 24) = k by omega]
        have hb : (srcB + 24) + UInt64.ofNat (k - 24) = srcB + UInt64.ofNat k := by
          change (srcB + UInt64.ofNat 24) + UInt64.ofNat (k - 24) = srcB + UInt64.ofNat k
          rw [u64_add_ofNat_assoc srcB 24 (k - 24) (by omega), show 24 + (k - 24) = k by omega]
        rw [ha, hb]

theorem gf256MulGfniStepMem_outside (mem : UInt64 → UInt8) (dst srcA srcB a : UInt64)
    (ha : ∀ k : Nat, k < 32 → a ≠ dst + UInt64.ofNat k) :
    gf256MulGfniStepMem mem dst srcA srcB a = mem a :=
  writeMem256_outside mem dst _ a ha

theorem gf256MulGfniIterMem_outside (n : Nat) (mem : UInt64 → UInt8) (dst srcA srcB a : UInt64)
    (hn : 32 * n ≤ 0x10000000000000000)
    (ha : ∀ idx : Nat, idx < 32 * n → a ≠ dst + UInt64.ofNat idx) :
    gf256MulGfniIterMem n mem dst srcA srcB a = mem a := by
  induction n generalizing mem dst srcA srcB with
  | zero => rfl
  | succ k ih =>
    unfold gf256MulGfniIterMem
    rw [ih _ (dst + 32) (srcA + 32) (srcB + 32) (by omega) (fun idx hidx heq => by
      change a = (dst + UInt64.ofNat 32) + UInt64.ofNat idx at heq
      rw [u64_add_ofNat_assoc dst 32 idx (by omega)] at heq
      exact ha (32 + idx) (by omega) heq)]
    exact gf256MulGfniStepMem_outside mem dst srcA srcB a (fun j hj => ha j (by omega))

theorem gf256MulGfniIterMem_at (n : Nat) (mem : UInt64 → UInt8) (dst srcA srcB : UInt64)
    (hn : 32 * n ≤ 0x10000000000000000)
    (hDisjA : ∀ i j : Nat, i < 32 * n → j < 32 * n → dst + UInt64.ofNat i ≠ srcA + UInt64.ofNat j)
    (hDisjB : ∀ i j : Nat, i < 32 * n → j < 32 * n → dst + UInt64.ofNat i ≠ srcB + UInt64.ofNat j)
    (idx : Nat) (hidx : idx < 32 * n) :
    gf256MulGfniIterMem n mem dst srcA srcB (dst + UInt64.ofNat idx) =
      gfniTowerMulByte (mem (srcA + UInt64.ofNat idx)) (mem (srcB + UInt64.ofNat idx)) := by
  induction n generalizing mem dst srcA srcB idx with
  | zero => exact absurd hidx (by omega)
  | succ k ih =>
    unfold gf256MulGfniIterMem
    by_cases hFirst : idx < 32
    · rw [gf256MulGfniIterMem_outside k _ (dst + 32) (srcA + 32) (srcB + 32) _ (by omega)
        (fun j hj heq => by
          change dst + UInt64.ofNat idx = (dst + UInt64.ofNat 32) + UInt64.ofNat j at heq
          rw [u64_add_ofNat_assoc dst 32 j (by omega)] at heq
          have := u64_add_ofNat_inj (by omega) (by omega) heq
          omega)]
      exact gf256MulGfniStepMem_at mem dst srcA srcB idx hFirst
    · have hAddr : dst + UInt64.ofNat idx = (dst + 32) + UInt64.ofNat (idx - 32) := by
        change dst + UInt64.ofNat idx = (dst + UInt64.ofNat 32) + UInt64.ofNat (idx - 32)
        rw [u64_add_ofNat_assoc dst 32 (idx - 32) (by omega), show 32 + (idx - 32) = idx by omega]
      rw [hAddr, ih (gf256MulGfniStepMem mem dst srcA srcB) (dst + 32) (srcA + 32) (srcB + 32) (by omega)
        (fun i j hi hj heq => by
          change (dst + UInt64.ofNat 32) + UInt64.ofNat i = (srcA + UInt64.ofNat 32) + UInt64.ofNat j at heq
          rw [u64_add_ofNat_assoc dst 32 i (by omega), u64_add_ofNat_assoc srcA 32 j (by omega)] at heq
          exact hDisjA (32 + i) (32 + j) (by omega) (by omega) heq)
        (fun i j hi hj heq => by
          change (dst + UInt64.ofNat 32) + UInt64.ofNat i = (srcB + UInt64.ofNat 32) + UInt64.ofNat j at heq
          rw [u64_add_ofNat_assoc dst 32 i (by omega), u64_add_ofNat_assoc srcB 32 j (by omega)] at heq
          exact hDisjB (32 + i) (32 + j) (by omega) (by omega) heq)
        (idx - 32) (by omega)]
      have hA : (srcA + 32) + UInt64.ofNat (idx - 32) = srcA + UInt64.ofNat idx := by
        change (srcA + UInt64.ofNat 32) + UInt64.ofNat (idx - 32) = srcA + UInt64.ofNat idx
        rw [u64_add_ofNat_assoc srcA 32 (idx - 32) (by omega), show 32 + (idx - 32) = idx by omega]
      have hB : (srcB + 32) + UInt64.ofNat (idx - 32) = srcB + UInt64.ofNat idx := by
        change (srcB + UInt64.ofNat 32) + UInt64.ofNat (idx - 32) = srcB + UInt64.ofNat idx
        rw [u64_add_ofNat_assoc srcB 32 (idx - 32) (by omega), show 32 + (idx - 32) = idx by omega]
      rw [hA, hB,
          gf256MulGfniStepMem_outside mem dst srcA srcB (srcA + UInt64.ofNat idx)
            (fun j hj heq => hDisjA j idx (by omega) hidx heq.symm),
          gf256MulGfniStepMem_outside mem dst srcA srcB (srcB + UInt64.ofNat idx)
            (fun j hj heq => hDisjB j idx (by omega) hidx heq.symm)]

theorem stepX86_addImm64 (off len pc dst : Nat) (imm : UInt64)
    (g : Bank16 UInt64) (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    (stepX86 ⟨off, len, .aluImm .add true dst imm⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (g.get dst + imm), y,
        decide ((g.get dst).toNat + imm.toNat ≥ 0x10000000000000000),
        evalX86AluOf .add true (g.get dst) imm cf,
        (g.get dst + imm) == 0, dy, false, m⟩ := by
  have h : (stepX86 ⟨off, len, .aluImm .add true dst imm⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len,
        g.set dst (UInt64.ofNat (((g.get dst).toNat + imm.toNat) % 0x10000000000000000)), y,
        decide ((g.get dst).toNat + imm.toNat ≥ 0x10000000000000000),
        evalX86AluOf .add true (g.get dst) imm cf,
        UInt64.ofNat (((g.get dst).toNat + imm.toNat) % 0x10000000000000000) == 0,
        dy, false, m⟩ := by rfl
  rw [h, uint64_evalAdd_eq]

theorem stepX86_dec64 (off len pc dst : Nat)
    (g : Bank16 UInt64) (y : Bank16 Vec256) (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    (stepX86 ⟨off, len, .incDec false true dst⟩ ⟨pc, g, y, cf, o, zf, dy, false, m⟩).1 =
      ⟨off + len, g.set dst (g.get dst - 1), y, cf, evalX86IncDecOf false true (g.get dst),
        (g.get dst - 1) == 0, dy, false, m⟩ := by
  have hsub : g.get dst + (0 - 1) = g.get dst - 1 := by
    apply UInt64.eq_of_toBitVec_eq; simp [BitVec.sub_eq_add_neg]
  simp only [stepX86_dec, maskGprWidth_true, hsub]

theorem elf_u64_xor_self (x : UInt64) : x ^^^ x = 0 := by
  apply UInt64.eq_of_toBitVec_eq; simp

theorem u64_add_zero (x : UInt64) : x + 0 = x := by
  apply UInt64.eq_of_toBitVec_eq; simp

private theorem gf256MulGfniBody_one_iter
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 : Vec256)
    (cf o zf : Bool) (m : UInt64 → UInt8) :
    let mT2R : Vec256 := ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩
    let mR2T : Vec256 := ⟨gfniRijndaelToTowerMat, gfniRijndaelToTowerMat, gfniRijndaelToTowerMat, gfniRijndaelToTowerMat⟩
    StepsX86 gf256MulGfniCoreProg 12
      ⟨40, ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, mT2R, mR2T⟩,
        cf, o, zf, true, false, m⟩
      ⟨jccPc (!((r1 - 1) == 0)) 40 92,
        ⟨r0, r1 - 1, r2 + 32, r3, r4, r5, r6 + 32, r7 + 32, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨gfniAffineVec256 (readMem256 m r6) mT2R 0,
          gfniAffineVec256 (readMem256 m r2) mT2R 0,
          gf256MulGfniVec (readMem256 m r6) (readMem256 m r2),
          y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, mT2R, mR2T⟩,
        decide (r7.toNat + (32 : UInt64).toNat ≥ 0x10000000000000000),
        evalX86IncDecOf false true r1,
        (r1 - 1) == 0, true, false, gf256MulGfniStepMem m r7 r6 r2⟩ := by
  dsimp only
  iterate 7
    apply StepsX86.cons rfl rfl
    · simp only [stepX86, evalX86Addr, clampVecWidth, evalVecBin256,
        u64_add_zero, b16get_2, b16get_6, b16get_7]
      rfl
  iterate 3
    apply StepsX86.cons rfl rfl
    · rw [stepX86_addImm64]
  apply StepsX86.cons rfl rfl
  · rw [stepX86_dec64]
  apply StepsX86.cons rfl rfl
  · rw [stepX86_jnz]
  exact StepsX86.zero _

theorem StepsX86_trans {prog : List (DecodedInstr X86Instr)} {m n : Nat}
    {s0 s1 s2 : X86State} (h1 : StepsX86 prog m s0 s1) (h2 : StepsX86 prog n s1 s2) :
    StepsX86 prog (m + n) s0 s2 := by
  induction h1 with
  | zero _ => simpa using h2
  | cons hh hf hs1 _ ih =>
    rw [Nat.succ_add]
    exact StepsX86.cons hh hf hs1 (ih h2)

private theorem gf256MulGfniLoop_steps (k : Nat) (hk : k + 1 < 0x10000000000000000)
    (r0 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 : Vec256)
    (cf o zf : Bool) (m : UInt64 → UInt8) :
    let mT2R : Vec256 := ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩
    let mR2T : Vec256 := ⟨gfniRijndaelToTowerMat, gfniRijndaelToTowerMat, gfniRijndaelToTowerMat, gfniRijndaelToTowerMat⟩
    ∃ cf' o' zf',
      StepsX86 gf256MulGfniCoreProg (17 + 12 * k)
        ⟨40, ⟨r0, UInt64.ofNat (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
          ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, mT2R, mR2T⟩,
          cf, o, zf, true, false, m⟩
        ⟨114,
          ⟨r0, 0, r2 + UInt64.ofNat (32 * (k + 1)), r3, r4, r5,
            r6 + UInt64.ofNat (32 * (k + 1)), r7 + UInt64.ofNat (32 * (k + 1)),
            r8, r9, r10, r11, r12, r13, r14, r15⟩,
          ⟨Vec256.zero, Vec256.zero, Vec256.zero, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13,
            Vec256.zero, Vec256.zero⟩,
          cf', o', zf', true, false, gf256MulGfniIterMem (k + 1) m r7 r6 r2⟩ := by
  induction k generalizing r2 r6 r7 y0 y1 y2 cf o zf m with
  | zero =>
    dsimp only
    have h1 : UInt64.ofNat 1 - 1 = 0 := by decide
    have hIter := gf256MulGfniBody_one_iter r0 (UInt64.ofNat 1) r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
      y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 cf o zf m
    dsimp only at hIter
    rw [h1, u64_zero_beq_zero] at hIter
    rw [show jccPc (!true) 40 92 = 92 from rfl] at hIter
    have hEpi : StepsX86 gf256MulGfniCoreProg 5
        ⟨92, ⟨r0, 0, r2 + 32, r3, r4, r5, r6 + 32, r7 + 32, r8, r9, r10, r11, r12, r13, r14, r15⟩,
          ⟨gfniAffineVec256 (readMem256 m r6) ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩ 0,
            gfniAffineVec256 (readMem256 m r2) ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩ 0,
            gf256MulGfniVec (readMem256 m r6) (readMem256 m r2),
            y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13,
            ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩,
            ⟨gfniRijndaelToTowerMat, gfniRijndaelToTowerMat, gfniRijndaelToTowerMat, gfniRijndaelToTowerMat⟩⟩,
          decide (r7.toNat + (32 : UInt64).toNat ≥ 0x10000000000000000),
          evalX86IncDecOf false true (UInt64.ofNat 1),
          true, true, false, gf256MulGfniStepMem m r7 r6 r2⟩
        ⟨114, ⟨r0, 0, r2 + 32, r3, r4, r5, r6 + 32, r7 + 32, r8, r9, r10, r11, r12, r13, r14, r15⟩,
          ⟨Vec256.zero, Vec256.zero, Vec256.zero, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13,
            Vec256.zero, Vec256.zero⟩,
          decide (r7.toNat + (32 : UInt64).toNat ≥ 0x10000000000000000),
          evalX86IncDecOf false true (UInt64.ofNat 1),
          true, true, false, gf256MulGfniStepMem m r7 r6 r2⟩ := by
      iterate 5
        apply StepsX86.cons rfl rfl
        · simp only [stepX86, clampVecWidth, evalVecBin256, elf_u64_xor_self]
          rfl
      exact StepsX86.zero _
    have hComb := StepsX86_trans hIter hEpi
    exact ⟨_, _, _, hComb⟩
  | succ j ih =>
    dsimp only
    have hDec : UInt64.ofNat (j + 1 + 1) - 1 = UInt64.ofNat (j + 1) := by
      apply UInt64.eq_of_toBitVec_eq
      apply BitVec.eq_of_toNat_eq
      have hlt2 : j + 1 < 0x10000000000000000 := by omega
      simp [UInt64.toNat_toBitVec, Nat.mod_eq_of_lt hlt2]
    have hNz : (UInt64.ofNat (j + 1) == 0) = false := by
      cases h : UInt64.ofNat (j + 1) == 0
      · rfl
      · have hn := congrArg UInt64.toNat (beq_iff_eq.mp h)
        have hlt : j + 1 < 0x10000000000000000 := by omega
        rw [show (UInt64.ofNat (j + 1)).toNat = j + 1 from Nat.mod_eq_of_lt hlt] at hn
        exact absurd hn (Nat.succ_ne_zero j)
    have hIter := gf256MulGfniBody_one_iter r0 (UInt64.ofNat (j + 1 + 1)) r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
      y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 cf o zf m
    dsimp only at hIter
    rw [hDec, hNz] at hIter
    rw [show jccPc (!false) 40 92 = 40 from rfl] at hIter
    obtain ⟨cf', o', zf', hRest⟩ := ih (by omega) (r2 + 32) (r6 + 32) (r7 + 32)
      (gfniAffineVec256 (readMem256 m r6) ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩ 0)
      (gfniAffineVec256 (readMem256 m r2) ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩ 0)
      (gf256MulGfniVec (readMem256 m r6) (readMem256 m r2))
      (decide (r7.toNat + (32 : UInt64).toNat ≥ 0x10000000000000000))
      (evalX86IncDecOf false true (UInt64.ofNat (j + 1 + 1))) false (gf256MulGfniStepMem m r7 r6 r2)
    have hComb := StepsX86_trans hIter hRest
    have hStepEq : 12 + (17 + 12 * j) = 17 + 12 * (j + 1) := by omega
    have hAddPtr : ∀ p : UInt64, (p + 32) + UInt64.ofNat (32 * (j + 1)) = p + UInt64.ofNat (32 * (j + 1 + 1)) := by
      intro p
      apply UInt64.eq_of_toBitVec_eq
      simp only [UInt64.toBitVec_add, BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp [UInt64.toNat_toBitVec]
      omega
    rw [hStepEq, hAddPtr r2, hAddPtr r6, hAddPtr r7] at hComb
    exact ⟨cf', o', zf', hComb⟩

private theorem gf256MulGfniCore_reaches (k : Nat) (hk : k + 1 < 0x10000000000000000)
    (r0 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64)
    (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 : Vec256)
    (cf o zf dy : Bool) (m : UInt64 → UInt8) :
    ∃ cf' o' zf',
      StepsX86 gf256MulGfniCoreProg (23 + 12 * k)
        ⟨0, ⟨r0, UInt64.ofNat (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
          ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
          cf, o, zf, dy, false, m⟩
        ⟨114,
          ⟨gfniRijndaelToTowerMat, 0, r2 + UInt64.ofNat (32 * (k + 1)), r3, r4, r5,
            r6 + UInt64.ofNat (32 * (k + 1)), r7 + UInt64.ofNat (32 * (k + 1)),
            r8, r9, r10, r11, r12, r13, r14, r15⟩,
          ⟨Vec256.zero, Vec256.zero, Vec256.zero, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13,
            Vec256.zero, Vec256.zero⟩,
          cf', o', zf', true, false, gf256MulGfniIterMem (k + 1) m r7 r6 r2⟩ := by
  have hPrologue : StepsX86 gf256MulGfniCoreProg 6
      ⟨0, ⟨r0, UInt64.ofNat (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15⟩,
        cf, o, zf, dy, false, m⟩
      ⟨40, ⟨gfniRijndaelToTowerMat, UInt64.ofNat (k + 1), r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩,
        ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13,
          ⟨gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat, gfniTowerToRijndaelMat⟩,
          ⟨gfniRijndaelToTowerMat, gfniRijndaelToTowerMat, gfniRijndaelToTowerMat, gfniRijndaelToTowerMat⟩⟩,
        cf, o, zf, true, false, m⟩ := by
    iterate 6
      apply StepsX86.cons rfl rfl
      · simp only [stepX86, maskGprWidth_true, b16get_0, b16set_0, Bool.or_true]
        rfl
    exact StepsX86.zero _
  obtain ⟨cf', o', zf', hLoop⟩ := gf256MulGfniLoop_steps k hk gfniRijndaelToTowerMat
    r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
    y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 cf o zf m
  have hComb := StepsX86_trans hPrologue hLoop
  have hEq : 6 + (17 + 12 * k) = 23 + 12 * k := by omega
  rw [hEq] at hComb
  exact ⟨cf', o', zf', hComb⟩

@[expose] def progPreservesNonRet (prog1 prog2 : List (DecodedInstr X86Instr)) : Bool :=
  prog1.all fun d => d.instr == .ret || findInstrAtPc d.offset prog2 == some d

private theorem findInstrAtPc_mem_and_offset {I : Type} {pc : Nat} {prog : List (DecodedInstr I)}
    {d : DecodedInstr I} (h : findInstrAtPc pc prog = some d) :
    d ∈ prog ∧ d.offset = pc := by
  induction prog with
  | nil => simp [findInstrAtPc] at h
  | cons hd tl ih =>
    unfold findInstrAtPc at h
    by_cases hpc : hd.offset == pc
    · rw [ite_eq_left hpc] at h
      cases h
      exact ⟨List.Mem.head _, beq_iff_eq.mp hpc⟩
    · rw [ite_eq_right hpc] at h
      obtain ⟨hm, ho⟩ := ih h
      exact ⟨List.Mem.tail _ hm, ho⟩

theorem ExecReachesX86_transfer_nonret {prog1 prog2 : List (DecodedInstr X86Instr)} {k : Nat}
    {s sRet : X86State}
    (hPres : progPreservesNonRet prog1 prog2 = true)
    (hReach : ExecReachesX86 prog1 k s sRet)
    (hhRet : sRet.halted = false) :
    ExecReachesX86 prog2 k s sRet := by
  rw [ExecReachesX86.public_eq_1] at hReach
  induction k generalizing s with
  | zero =>
    have h0 := (hReach 0).1
    simp only [runX86] at h0
    subst h0
    exact ExecReachesX86_zero prog2 _
  | succ k ih =>
    have hh : s.halted = false := by
      cases hs : s.halted
      · rfl
      · have h0 := (hReach 0).1
        rw [Nat.add_zero, runX86_halted_fst prog1 (k + 1) s hs] at h0
        change s = sRet at h0
        rw [← h0, hs] at hhRet
        cases hhRet
    cases hf1 : findInstrAtPc s.pc prog1 with
    | none =>
      have h0 := (hReach 0).1
      simp only [runX86, hh, hf1] at h0
      rw [← h0] at hhRet
      cases hhRet
    | some d =>
      have hNotRet : d.instr ≠ .ret := by
        intro hIr
        rcases d with ⟨off, len, instr⟩
        dsimp only at hIr; subst hIr
        have h0 := (hReach 0).1
        simp only [runX86, hh, hf1, stepX86] at h0
        rw [runX86_halted_fst prog1 k _ rfl] at h0
        rw [← h0] at hhRet
        cases hhRet
      obtain ⟨hdMem, hdOff⟩ := findInstrAtPc_mem_and_offset hf1
      have hAll := List.all_eq_true.mp hPres d hdMem
      have hBeqFalse : (d.instr == .ret) = false := by
        cases h : d.instr == .ret
        · rfl
        · exact absurd (beq_iff_eq.mp h) hNotRet
      rw [hBeqFalse, Bool.false_or] at hAll
      have hf2 : findInstrAtPc s.pc prog2 = some d := by
        rw [← hdOff]; exact beq_iff_eq.mp hAll
      have hRest : ExecReachesX86 prog1 k (stepX86 d s).1 sRet := by
        rw [ExecReachesX86.public_eq_1]
        intro extra
        have ⟨he, hl⟩ := hReach extra
        rw [Nat.add_right_comm k 1 extra] at he hl
        simp only [runX86, hh, hf1] at he hl
        exact ⟨he, by simp at hl; omega⟩
      exact ExecReachesX86_cons hh hf2 rfl (ih (ExecReachesX86.public_eq_1 .. ▸ hRest))


/-! ### §5.4 `qsag_asm_keccak_sha3_neon` (`AArch64` SHA3 NEON `EOR` + `BCAX` 2-Share Keccak $\chi$ Rows 0 & 1) -/

def keccakSha3NeonProg : List (DecodedInstr Arm64Instr) := [
  ⟨0, 4, .ldrQ 0 1 0⟩, ⟨4, 4, .ldrQ 1 1 16⟩, ⟨8, 4, .ldrQ 2 1 32⟩,
  ⟨12, 4, .ldrQ 3 1 48⟩, ⟨16, 4, .ldrQ 4 1 64⟩,
  ⟨20, 4, .ldrQ 5 2 0⟩, ⟨24, 4, .ldrQ 6 2 16⟩, ⟨28, 4, .ldrQ 7 2 32⟩,
  ⟨32, 4, .veor16b 0 0 5⟩, ⟨36, 4, .veor16b 1 1 6⟩, ⟨40, 4, .veor16b 2 2 7⟩,
  ⟨44, 4, .ldrQ 5 2 48⟩, ⟨48, 4, .ldrQ 6 2 64⟩,
  ⟨52, 4, .veor16b 3 3 5⟩, ⟨56, 4, .veor16b 4 4 6⟩,
  ⟨60, 4, .vbcax16b 16 0 2 1⟩, ⟨64, 4, .vbcax16b 17 1 3 2⟩,
  ⟨68, 4, .vbcax16b 18 2 4 3⟩, ⟨72, 4, .vbcax16b 19 3 0 4⟩, ⟨76, 4, .vbcax16b 20 4 1 0⟩,
  ⟨80, 4, .strQ 16 0 0⟩, ⟨84, 4, .strQ 17 0 16⟩, ⟨88, 4, .strQ 18 0 32⟩,
  ⟨92, 4, .strQ 19 0 48⟩, ⟨96, 4, .strQ 20 0 64⟩,
  ⟨100, 4, .veor16b 0 0 0⟩, ⟨104, 4, .veor16b 1 1 1⟩, ⟨108, 4, .veor16b 2 2 2⟩,
  ⟨112, 4, .veor16b 3 3 3⟩, ⟨116, 4, .veor16b 4 4 4⟩, ⟨120, 4, .veor16b 5 5 5⟩,
  ⟨124, 4, .veor16b 6 6 6⟩, ⟨128, 4, .veor16b 7 7 7⟩,
  ⟨132, 4, .veor16b 16 16 16⟩, ⟨136, 4, .veor16b 17 17 17⟩, ⟨140, 4, .veor16b 18 18 18⟩,
  ⟨144, 4, .veor16b 19 19 19⟩, ⟨148, 4, .veor16b 20 20 20⟩,
  ⟨152, 4, .ret⟩
]

def keccakNeonOutMem (mem : UInt64 → UInt8) (outPtr s0Ptr s1Ptr : UInt64) : UInt64 → UInt8 :=
  let u0 := readMem128 mem s0Ptr
  let u1 := readMem128 mem (s0Ptr + 16)
  let u2 := readMem128 mem (s0Ptr + 32)
  let u3 := readMem128 mem (s0Ptr + 48)
  let u4 := readMem128 mem (s0Ptr + 64)
  let w0 := readMem128 mem s1Ptr
  let w1 := readMem128 mem (s1Ptr + 16)
  let w2 := readMem128 mem (s1Ptr + 32)
  let w3 := readMem128 mem (s1Ptr + 48)
  let w4 := readMem128 mem (s1Ptr + 64)
  let a0 : Vec128 := ⟨u0.w0 ^^^ w0.w0, u0.w1 ^^^ w0.w1⟩
  let a1 : Vec128 := ⟨u1.w0 ^^^ w1.w0, u1.w1 ^^^ w1.w1⟩
  let a2 : Vec128 := ⟨u2.w0 ^^^ w2.w0, u2.w1 ^^^ w2.w1⟩
  let a3 : Vec128 := ⟨u3.w0 ^^^ w3.w0, u3.w1 ^^^ w3.w1⟩
  let a4 : Vec128 := ⟨u4.w0 ^^^ w4.w0, u4.w1 ^^^ w4.w1⟩
  let c0 : Vec128 := ⟨a0.w0 ^^^ (a2.w0 &&& (~~~a1.w0)), a0.w1 ^^^ (a2.w1 &&& (~~~a1.w1))⟩
  let c1 : Vec128 := ⟨a1.w0 ^^^ (a3.w0 &&& (~~~a2.w0)), a1.w1 ^^^ (a3.w1 &&& (~~~a2.w1))⟩
  let c2 : Vec128 := ⟨a2.w0 ^^^ (a4.w0 &&& (~~~a3.w0)), a2.w1 ^^^ (a4.w1 &&& (~~~a3.w1))⟩
  let c3 : Vec128 := ⟨a3.w0 ^^^ (a0.w0 &&& (~~~a4.w0)), a3.w1 ^^^ (a0.w1 &&& (~~~a4.w1))⟩
  let c4 : Vec128 := ⟨a4.w0 ^^^ (a1.w0 &&& (~~~a0.w0)), a4.w1 ^^^ (a1.w1 &&& (~~~a0.w1))⟩
  let m0 := writeMem128 mem outPtr c0
  let m1 := writeMem128 m0 (outPtr + 16) c1
  let m2 := writeMem128 m1 (outPtr + 32) c2
  let m3 := writeMem128 m2 (outPtr + 48) c3
  writeMem128 m3 (outPtr + 64) c4

private theorem keccakSha3Neon_reaches
    (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 : UInt64) (hi : Bank16 UInt64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : Vec128)
    (v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 : Vec128)
    (cf zf dit : Bool) (m : UInt64 → UInt8) :
    ExecReachesArm64 keccakSha3NeonProg 38
      ⟨0, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        ⟨⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15⟩,
         ⟨v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31⟩⟩,
        cf, zf, dit, false, m⟩
      ⟨152, ⟨⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15⟩, hi⟩,
        ⟨⟨Vec128.zero, Vec128.zero, Vec128.zero, Vec128.zero,
          Vec128.zero, Vec128.zero, Vec128.zero, Vec128.zero,
          v8, v9, v10, v11, v12, v13, v14, v15⟩,
         ⟨Vec128.zero, Vec128.zero, Vec128.zero, Vec128.zero, Vec128.zero,
          v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31⟩⟩,
        cf, zf, dit, false, keccakNeonOutMem m r0 r1 r2⟩ := by
  apply StepsArm64.toExecReaches
  iterate 38
    apply StepsArm64.cons rfl rfl
    · simp only [stepArm64, getArmGpr, u64_add_zero, elf_u64_xor_self]
      rfl
  exact StepsArm64.zero _

private theorem u64_bcax_eq_chi (x z y : UInt64) :
    x ^^^ (z &&& (~~~y)) = x ^^^ ((~~~y) &&& z) := by
  apply UInt64.eq_of_toBitVec_eq; simp [BitVec.and_comm]

theorem keccakNeonOutMem_lanes (mem : UInt64 → UInt8) (outPtr s0Ptr s1Ptr : UInt64)
    (K : KState)
    (ha0 : K.a0 = readMem64 mem s0Ptr ^^^ readMem64 mem s1Ptr)
    (ha1 : K.a1 = readMem64 mem (s0Ptr + 16) ^^^ readMem64 mem (s1Ptr + 16))
    (ha2 : K.a2 = readMem64 mem (s0Ptr + 32) ^^^ readMem64 mem (s1Ptr + 32))
    (ha3 : K.a3 = readMem64 mem (s0Ptr + 48) ^^^ readMem64 mem (s1Ptr + 48))
    (ha4 : K.a4 = readMem64 mem (s0Ptr + 64) ^^^ readMem64 mem (s1Ptr + 64))
    (ha5 : K.a5 = readMem64 mem (s0Ptr + 8) ^^^ readMem64 mem (s1Ptr + 8))
    (ha6 : K.a6 = readMem64 mem (s0Ptr + 24) ^^^ readMem64 mem (s1Ptr + 24))
    (ha7 : K.a7 = readMem64 mem (s0Ptr + 40) ^^^ readMem64 mem (s1Ptr + 40))
    (ha8 : K.a8 = readMem64 mem (s0Ptr + 56) ^^^ readMem64 mem (s1Ptr + 56))
    (ha9 : K.a9 = readMem64 mem (s0Ptr + 72) ^^^ readMem64 mem (s1Ptr + 72)) :
    let m' := keccakNeonOutMem mem outPtr s0Ptr s1Ptr
    readMem64 m' outPtr = (chiS K).a0 ∧
    readMem64 m' (outPtr + 16) = (chiS K).a1 ∧
    readMem64 m' (outPtr + 32) = (chiS K).a2 ∧
    readMem64 m' (outPtr + 48) = (chiS K).a3 ∧
    readMem64 m' (outPtr + 64) = (chiS K).a4 ∧
    readMem64 m' (outPtr + 8) = (chiS K).a5 ∧
    readMem64 m' (outPtr + 24) = (chiS K).a6 ∧
    readMem64 m' (outPtr + 40) = (chiS K).a7 ∧
    readMem64 m' (outPtr + 56) = (chiS K).a8 ∧
    readMem64 m' (outPtr + 72) = (chiS K).a9 := by
  dsimp only
  have hDisj : ∀ (off1 off2 : Nat) (a1 a2 : UInt64) (_h1 : off1 ≤ 72) (_h2 : off2 ≤ 64)
      (_hd : off1 + 8 ≤ off2 ∨ off2 + 16 ≤ off1)
      (_e1 : a1 = outPtr + UInt64.ofNat off1) (_e2 : a2 = outPtr + UInt64.ofNat off2)
      (m : UInt64 → UInt8) (v : Vec128),
      readMem64 (writeMem128 m a2 v) a1 = readMem64 m a1 := by
    intro off1 off2 a1 a2 _h1 _h2 _hd e1 e2 m v
    subst e1 e2
    apply readMem64_writeMem128_disjoint
    intro i k _hi _hk heq
    rw [u64_add_ofNat_assoc outPtr off1 i (by omega),
        u64_add_ofNat_assoc outPtr off2 k (by omega)] at heq
    have := u64_add_ofNat_inj (by omega) (by omega) heq
    omega
  have hp0 : outPtr = outPtr + UInt64.ofNat 0 := by apply UInt64.eq_of_toBitVec_eq; simp
  have h16_8 : (outPtr + 16) + 8 = outPtr + 24 := by
    change (outPtr + UInt64.ofNat 16) + UInt64.ofNat 8 = outPtr + UInt64.ofNat 24
    exact u64_add_ofNat_assoc outPtr 16 8 (by decide)
  have h32_8 : (outPtr + 32) + 8 = outPtr + 40 := by
    change (outPtr + UInt64.ofNat 32) + UInt64.ofNat 8 = outPtr + UInt64.ofNat 40
    exact u64_add_ofNat_assoc outPtr 32 8 (by decide)
  have h48_8 : (outPtr + 48) + 8 = outPtr + 56 := by
    change (outPtr + UInt64.ofNat 48) + UInt64.ofNat 8 = outPtr + UInt64.ofNat 56
    exact u64_add_ofNat_assoc outPtr 48 8 (by decide)
  have h64_8 : (outPtr + 64) + 8 = outPtr + 72 := by
    change (outPtr + UInt64.ofNat 64) + UInt64.ofNat 8 = outPtr + UInt64.ofNat 72
    exact u64_add_ofNat_assoc outPtr 64 8 (by decide)
  have hs16_8 : ∀ p : UInt64, (p + 16) + 8 = p + 24 := fun p => by
    change (p + UInt64.ofNat 16) + UInt64.ofNat 8 = p + UInt64.ofNat 24
    exact u64_add_ofNat_assoc p 16 8 (by decide)
  have hs32_8 : ∀ p : UInt64, (p + 32) + 8 = p + 40 := fun p => by
    change (p + UInt64.ofNat 32) + UInt64.ofNat 8 = p + UInt64.ofNat 40
    exact u64_add_ofNat_assoc p 32 8 (by decide)
  have hs48_8 : ∀ p : UInt64, (p + 48) + 8 = p + 56 := fun p => by
    change (p + UInt64.ofNat 48) + UInt64.ofNat 8 = p + UInt64.ofNat 56
    exact u64_add_ofNat_assoc p 48 8 (by decide)
  have hs64_8 : ∀ p : UInt64, (p + 64) + 8 = p + 72 := fun p => by
    change (p + UInt64.ofNat 64) + UInt64.ofNat 8 = p + UInt64.ofNat 72
    exact u64_add_ofNat_assoc p 64 8 (by decide)
  unfold keccakNeonOutMem chiS readMem128
  dsimp only
  simp only [hs16_8, hs32_8, hs48_8, hs64_8,
    ← ha0, ← ha1, ← ha2, ← ha3, ← ha4, ← ha5, ← ha6, ← ha7, ← ha8, ← ha9,
    u64_bcax_eq_chi]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hDisj 0 64 outPtr (outPtr + 64) (by decide) (by decide) (by omega) hp0 rfl,
        hDisj 0 48 outPtr (outPtr + 48) (by decide) (by decide) (by omega) hp0 rfl,
        hDisj 0 32 outPtr (outPtr + 32) (by decide) (by decide) (by omega) hp0 rfl,
        hDisj 0 16 outPtr (outPtr + 16) (by decide) (by decide) (by omega) hp0 rfl,
        readMem64_writeMem128_lo]
  · rw [hDisj 16 64 (outPtr + 16) (outPtr + 64) (by decide) (by decide) (by omega) rfl rfl,
        hDisj 16 48 (outPtr + 16) (outPtr + 48) (by decide) (by decide) (by omega) rfl rfl,
        hDisj 16 32 (outPtr + 16) (outPtr + 32) (by decide) (by decide) (by omega) rfl rfl,
        readMem64_writeMem128_lo]
  · rw [hDisj 32 64 (outPtr + 32) (outPtr + 64) (by decide) (by decide) (by omega) rfl rfl,
        hDisj 32 48 (outPtr + 32) (outPtr + 48) (by decide) (by decide) (by omega) rfl rfl,
        readMem64_writeMem128_lo]
  · rw [hDisj 48 64 (outPtr + 48) (outPtr + 64) (by decide) (by decide) (by omega) rfl rfl,
        readMem64_writeMem128_lo]
  · exact readMem64_writeMem128_lo _ (outPtr + 64) _
  · rw [hDisj 8 64 (outPtr + 8) (outPtr + 64) (by decide) (by decide) (by omega) rfl rfl,
        hDisj 8 48 (outPtr + 8) (outPtr + 48) (by decide) (by decide) (by omega) rfl rfl,
        hDisj 8 32 (outPtr + 8) (outPtr + 32) (by decide) (by decide) (by omega) rfl rfl,
        hDisj 8 16 (outPtr + 8) (outPtr + 16) (by decide) (by decide) (by omega) rfl rfl]
    exact readMem64_writeMem128_hi _ outPtr _
  · rw [hDisj 24 64 (outPtr + 24) (outPtr + 64) (by decide) (by decide) (by omega) rfl rfl,
        hDisj 24 48 (outPtr + 24) (outPtr + 48) (by decide) (by decide) (by omega) rfl rfl,
        hDisj 24 32 (outPtr + 24) (outPtr + 32) (by decide) (by decide) (by omega) rfl rfl,
        ← h16_8]
    exact readMem64_writeMem128_hi _ (outPtr + 16) _
  · rw [hDisj 40 64 (outPtr + 40) (outPtr + 64) (by decide) (by decide) (by omega) rfl rfl,
        hDisj 40 48 (outPtr + 40) (outPtr + 48) (by decide) (by decide) (by omega) rfl rfl,
        ← h32_8]
    exact readMem64_writeMem128_hi _ (outPtr + 32) _
  · rw [hDisj 56 64 (outPtr + 56) (outPtr + 64) (by decide) (by decide) (by omega) rfl rfl,
        ← h48_8]
    exact readMem64_writeMem128_hi _ (outPtr + 48) _
  · rw [← h64_8]
    exact readMem64_writeMem128_hi _ (outPtr + 64) _

