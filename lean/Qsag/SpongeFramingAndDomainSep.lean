module
/-
# Qsag.SpongeFramingAndDomainSep — Multi-Block Sponge Padding, SP 800-185 Framing & Midstate Laws

Self-contained Lean 4.35 cryptographic sponge and domain-separation foundation over `Qsag.Keccak`
(`0 sorry`, `0 Classical.choice`, `0 native_decide`, `0 bv_decide`, `0 grind`):
1. **Multi-Block Rate-$r$ Sponge Specification & Cross-Domain Padding Injectivity
   (`pad10star1_joint_injective`, `pad10star1_injective`, `absorbPayload_cross_domain_disjoint`)**:
   Exact byte-level rate-$r$ (`r = 136` for `SHAKE256` / `cSHAKE256` / `TurboSHAKE256` / `SHA3-256`,
   `r = 64` for 8-limb `Poseidon2` byte rate) multi-block XOR absorption, `pad10*1` padding, and
   arbitrary-length multi-block squeezing over any permutation `π`, proved bit-exact against
   `Keccak.shake256Xof` (`evalSponge_keccak_eq_shake256Xof`). Proves both single-domain message
   injectivity and cross-domain sponge-block disjointness (`0x1F`, `0x04`, `0x06` never collide).
2. **NIST SP 800-185 Self-Delimiting Prefix Injectivity (`leftEncode_prefix_inj`,
   `encodeString_prefix_inj`, `cshakePrefix_prefix_free`, `cshakePrefix_injective`)**:
   Proves `bytepad(encodeString(N) || encodeString(S), 136)` is prefix-free across arbitrary
   message suffixes (`cshakePrefix N₁ S₁ ++ m₁ = cshakePrefix N₂ S₂ ++ m₂ → N₁ = N₂ ∧ S₁ = S₂ ∧ m₁ = m₂`),
   placing all `QSAG.*` customization tags in pairwise disjoint permutation input domains.
3. **Precomputed-Midstate Equivalence (`cshake_precomputed_midstate_eq`,
   `keccak_cshake256_precomputed_midstate_eq`)**:
   Certifies that whenever `encodeString(N) ++ encodeString(S)` fits in a single `136`-byte
   `bytepad` block (`≤ 134` payload bytes, satisfied by every `QSAG.*` tag), absorbing `m` from
   `midstate := π (xorBlock zeroState (cshakePrefix N S))` produces bit-for-bit identical output
   for all `m` and all `outLen` as full from-scratch `cSHAKE256`.
-/

public import Qsag.Keccak
import all Qsag.Keccak
import Qsag.Tactic.AssuranceKit

public section
namespace Qsag

set_option autoImplicit false

/-! ## 1. Multi-Rate `pad10*1`, Multi-Block Absorption & Arbitrary-Length Squeezing -/

/-- Canonical sponge byte rates (`r = 136` for `SHAKE256`/`cSHAKE256`/`TurboSHAKE256`/`SHA3-256`, `r = 64` for `Poseidon2`) and FIPS-202/SP 800-185 domain bytes. -/
def shakeRateBytes : Nat := 136
def poseidon2RateBytes : Nat := 64
def domShake256 : UInt8 := 0x1F
def domTurboShake256 : UInt8 := 0x1F
def domCshake256 : UInt8 := 0x04
def domSha3_256 : UInt8 := 0x06

/-- Valid FIPS-202 / SP 800-185 domain byte: nonzero with high padding bit `0x80` clear. -/
@[expose] def ValidDomByte (domByte : UInt8) : Prop := 0 < domByte.toNat ∧ domByte.toNat < 128
instance (d : UInt8) : Decidable (ValidDomByte d) := by unfold ValidDomByte; exact inferInstance

/-- Multi-rate `pad10*1(r, domByte, msg)` byte padding. -/
@[expose] def pad10star1 (r : Nat) (domByte : UInt8) (msg : List UInt8) : List UInt8 :=
  if r = 0 then msg else
    let rem := r - msg.length % r
    if rem = 1 then msg ++ [domByte ^^^ (0x80 : UInt8)]
    else msg ++ [domByte] ++ List.replicate (rem - 2) 0 ++ [0x80]

theorem pad10star1_136_eq_padForRate (domByte : UInt8) (msg : List UInt8) :
    pad10star1 136 domByte msg = padForRate msg domByte := by rfl

theorem pad10star1_length {r : Nat} (hr : 0 < r) (domByte : UInt8) (msg : List UInt8) :
    (pad10star1 r domByte msg).length = msg.length + (r - msg.length % r) ∧
    (pad10star1 r domByte msg).length % r = 0 ∧
    r ≤ (pad10star1 r domByte msg).length := by
  have hrNe : r ≠ 0 := by omega
  have hModLt : msg.length % r < r := Nat.mod_lt msg.length hr
  unfold pad10star1
  simp only [hrNe, ↓reduceIte]
  have hLen : (let rem := r - msg.length % r
      if rem = 1 then msg ++ [domByte ^^^ (0x80 : UInt8)]
      else msg ++ [domByte] ++ List.replicate (rem - 2) 0 ++ [0x80]).length =
      msg.length + (r - msg.length % r) := by
    dsimp only
    split
    · rename_i h1; simp [h1]
    · simp only [List.length_append, List.length_singleton, List.length_replicate]; omega
  have hModLe : msg.length % r ≤ msg.length := Nat.mod_le msg.length r
  refine ⟨hLen, ?_, by rw [hLen]; omega⟩
  rw [hLen]
  have hDiv := Nat.div_add_mod msg.length r
  have hSum : msg.length + (r - msg.length % r) = r * (msg.length / r) + r := by omega
  rw [hSum, ← Nat.mul_succ, Nat.mul_mod_right]

/-- Slice a byte stream into `numBlocks` consecutive `r`-byte blocks. -/
@[expose] def sliceBlocks (r : Nat) : Nat → List UInt8 → List (List UInt8)
  | 0, _ => []
  | k + 1, bytes => bytes.take r :: sliceBlocks r k (bytes.drop r)

/-- Exact multi-block `r`-byte padded sponge input blocks for `(r, domByte, msg)`. -/
@[expose] def absorbPayload (r : Nat) (domByte : UInt8) (msg : List UInt8) : List (List UInt8) :=
  let padded := pad10star1 r domByte msg
  sliceBlocks r (padded.length / r) padded

private theorem sliceBlocks_flatten :
    ∀ (k : Nat) {r : Nat} {bytes : List UInt8},
      bytes.length = r * k →
      (sliceBlocks r k bytes).flatten = bytes ∧
      ∀ blk ∈ sliceBlocks r k bytes, blk.length = r
  | 0, _, bytes, hLen => by
    simp only [Nat.mul_zero, List.length_eq_zero_iff] at hLen
    subst hLen; exact ⟨rfl, fun _ h => by cases h⟩
  | k + 1, r, bytes, hLen => by
    have hGe : r ≤ bytes.length := by rw [Nat.mul_succ] at hLen; omega
    have hDropLen : (bytes.drop r).length = r * k := by
      rw [List.length_drop, hLen, Nat.mul_succ]; omega
    obtain ⟨hFlat, hLens⟩ := sliceBlocks_flatten k hDropLen
    refine ⟨by simp only [sliceBlocks, List.flatten_cons, hFlat, List.take_append_drop], ?_⟩
    intro blk hMem
    rcases List.mem_cons.mp hMem with rfl | hTail
    · rw [List.length_take]; omega
    · exact hLens blk hTail

theorem absorbPayload_flatten {r : Nat} (hr : 0 < r) (domByte : UInt8) (msg : List UInt8) :
    (absorbPayload r domByte msg).flatten = pad10star1 r domByte msg ∧
    ∀ blk ∈ absorbPayload r domByte msg, blk.length = r := by
  dsimp only [absorbPayload]
  obtain ⟨_, hMod0, _⟩ := pad10star1_length hr domByte msg
  have hDiv := Nat.div_add_mod (pad10star1 r domByte msg).length r
  rw [hMod0, Nat.add_zero] at hDiv
  exact sliceBlocks_flatten _ hDiv.symm

private theorem uint8_xor_80_inj {a b : UInt8} (h : (a ^^^ (0x80 : UInt8)) = (b ^^^ (0x80 : UInt8))) :
    a = b := by
  have hbv : a.toBitVec ^^^ (0x80 : UInt8).toBitVec = b.toBitVec ^^^ (0x80 : UInt8).toBitVec :=
    congrArg UInt8.toBitVec h
  have h1 := congrArg (· ^^^ (0x80 : UInt8).toBitVec) hbv
  simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] at h1
  exact UInt8.eq_of_toBitVec_eq h1

private theorem uint8_xor_80_ne_80 {d : UInt8} (hd : 0 < d.toNat) :
    (d ^^^ (0x80 : UInt8)) ≠ (0x80 : UInt8) := by
  intro hEq
  have h0 : (0 : UInt8) ^^^ (0x80 : UInt8) = (0x80 : UInt8) := by decide
  have hdEq0 : d = 0 := uint8_xor_80_inj (hEq.trans h0.symm)
  subst hdEq0; exact absurd hd (by decide)

private theorem strip_zero_replicate_inj :
    ∀ (k₁ k₂ : Nat) {d₁ d₂ : UInt8} {r₁ r₂ : List UInt8},
      0 < d₁.toNat → 0 < d₂.toNat →
      List.replicate k₁ (0 : UInt8) ++ (d₁ :: r₁) = List.replicate k₂ (0 : UInt8) ++ (d₂ :: r₂) →
      d₁ = d₂ ∧ r₁ = r₂
  | 0, 0, _, _, _, _, _, _, h => ⟨(List.cons.inj h).1, (List.cons.inj h).2⟩
  | 0, _ + 1, d₁, _, _, _, hd₁, _, h => by
    have hHead : d₁ = 0 := (List.cons.inj h).1
    subst hHead; exact absurd hd₁ (by decide)
  | _ + 1, 0, _, d₂, _, _, _, hd₂, h => by
    have hHead : (0 : UInt8) = d₂ := (List.cons.inj h).1
    subst hHead; exact absurd hd₂ (by decide)
  | k₁ + 1, k₂ + 1, _, _, _, _, hd₁, hd₂, h =>
    strip_zero_replicate_inj k₁ k₂ hd₁ hd₂ (List.cons.inj h).2

private theorem reverse_pad_long (m : List UInt8) (d : UInt8) (k : Nat) :
    (m ++ [d] ++ List.replicate k 0 ++ [0x80]).reverse =
      (0x80 : UInt8) :: (List.replicate k 0 ++ (d :: m.reverse)) := by
  rw [List.reverse_append, List.reverse_append, List.reverse_append,
      List.reverse_singleton, List.reverse_replicate, List.reverse_singleton]
  simp only [List.singleton_append]

/-- **Unified Multi-Rate `pad10*1` Joint Message & Domain Injectivity (`pad10star1_joint_injective`)**:
    For any rate `r > 0` and valid domain bytes `d₁, d₂`, `pad10star1 r d₁ m₁ = pad10star1 r d₂ m₂`
    implies BOTH `d₁ = d₂` AND `m₁ = m₂`! -/
theorem pad10star1_joint_injective {r : Nat} {d₁ d₂ : UInt8} {m₁ m₂ : List UInt8}
    (hr : 0 < r) (hd₁ : ValidDomByte d₁) (hd₂ : ValidDomByte d₂)
    (hEq : pad10star1 r d₁ m₁ = pad10star1 r d₂ m₂) :
    d₁ = d₂ ∧ m₁ = m₂ := by
  have hrNe : r ≠ 0 := by omega
  unfold pad10star1 at hEq
  simp only [hrNe, ↓reduceIte] at hEq
  have hRev := congrArg List.reverse hEq
  split at hRev <;> split at hRev
  · simp only [List.reverse_append, List.reverse_singleton, List.singleton_append] at hRev
    exact ⟨uint8_xor_80_inj (List.cons.inj hRev).1, List.reverse_inj.mp (List.cons.inj hRev).2⟩
  · rw [List.reverse_append, List.reverse_singleton, List.singleton_append, reverse_pad_long] at hRev
    exact False.elim (uint8_xor_80_ne_80 hd₁.1 (List.cons.inj hRev).1)
  · rw [reverse_pad_long, List.reverse_append, List.reverse_singleton, List.singleton_append] at hRev
    exact False.elim (uint8_xor_80_ne_80 hd₂.1 (List.cons.inj hRev).1.symm)
  · rw [reverse_pad_long, reverse_pad_long] at hRev
    obtain ⟨hdEq, hmRev⟩ := strip_zero_replicate_inj _ _ hd₁.1 hd₂.1 (List.cons.inj hRev).2
    exact ⟨hdEq, List.reverse_inj.mp hmRev⟩

/-- **`pad10star1_injective`**: within any fixed valid domain byte `domByte`, distinct messages
    produce strictly distinct `r`-byte sponge block sequences. -/
theorem pad10star1_injective {r : Nat} {domByte : UInt8} {m₁ m₂ : List UInt8}
    (hr : 0 < r) (hDom : ValidDomByte domByte)
    (hBlocks : absorbPayload r domByte m₁ = absorbPayload r domByte m₂) :
    m₁ = m₂ := by
  have hFlat : pad10star1 r domByte m₁ = pad10star1 r domByte m₂ := by
    rw [← (absorbPayload_flatten hr domByte m₁).1, ← (absorbPayload_flatten hr domByte m₂).1, hBlocks]
  exact (pad10star1_joint_injective hr hDom hDom hFlat).2

/-- **Cross-Domain Sponge Block Separation (`absorbPayload_cross_domain_disjoint`)**:
    Distinct valid domain bytes (`d₁ ≠ d₂`) NEVER collide on `absorbPayload` for ANY `m₁, m₂`. -/
theorem absorbPayload_cross_domain_disjoint {r : Nat} {d₁ d₂ : UInt8} (m₁ m₂ : List UInt8)
    (hr : 0 < r) (hNe : d₁ ≠ d₂) (hd₁ : ValidDomByte d₁) (hd₂ : ValidDomByte d₂) :
    absorbPayload r d₁ m₁ ≠ absorbPayload r d₂ m₂ := by
  intro hEq
  have hFlat : pad10star1 r d₁ m₁ = pad10star1 r d₂ m₂ := by
    rw [← (absorbPayload_flatten hr d₁ m₁).1, ← (absorbPayload_flatten hr d₂ m₂).1, hEq]
  exact hNe (pad10star1_joint_injective hr hd₁ hd₂ hFlat).1

/-- Explicit cross-domain separation across `SHAKE256` (`0x1F`), `cSHAKE256` (`0x04`), and `SHA3-256` (`0x06`). -/
theorem fips202_shake_cshake_sha3_domains_disjoint (m₁ m₂ : List UInt8) :
    absorbPayload 136 domShake256 m₁ ≠ absorbPayload 136 domCshake256 m₂ ∧
    absorbPayload 136 domShake256 m₁ ≠ absorbPayload 136 domSha3_256 m₂ ∧
    absorbPayload 136 domCshake256 m₁ ≠ absorbPayload 136 domSha3_256 m₂ :=
  ⟨absorbPayload_cross_domain_disjoint m₁ m₂ (by decide) (by decide) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩,
   absorbPayload_cross_domain_disjoint m₁ m₂ (by decide) (by decide) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩,
   absorbPayload_cross_domain_disjoint m₁ m₂ (by decide) (by decide) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩⟩
/-- Generic multi-block sponge absorption over arbitrary permutation `π : σ → σ`. -/
@[expose] def spongeAbsorbBlocks {σ : Type} (π : σ → σ) (xorBlk : σ → List UInt8 → σ) (s : σ) : List (List UInt8) → σ
  | [] => s
  | blk :: rest => spongeAbsorbBlocks π xorBlk (π (xorBlk s blk)) rest
theorem spongeAbsorbBlocks_append {σ : Type} (π : σ → σ) (xorBlk : σ → List UInt8 → σ) (s : σ) (xs ys : List (List UInt8)) :
    spongeAbsorbBlocks π xorBlk s (xs ++ ys) = spongeAbsorbBlocks π xorBlk (spongeAbsorbBlocks π xorBlk s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons blk rest ih => exact ih (π (xorBlk s blk))

/-- Fuel-driven generic multi-block sponge squeezing parameterized by rate `r` and permutation `π`. -/
@[expose] def spongeSqueezeFuel {σ : Type} (r : Nat) (π : σ → σ)
    (extractRate : σ → List UInt8) : Nat → Nat → σ → List UInt8
  | 0, _, _ => []
  | _ + 1, 0, _ => []
  | fuel + 1, outLen + 1, s =>
    let blk := extractRate s
    if outLen + 1 ≤ r then blk.take (outLen + 1)
    else blk ++ spongeSqueezeFuel r π extractRate fuel (outLen + 1 - r) (π s)

/-- Arbitrary-length generic multi-block sponge squeeze. -/
@[expose] def spongeSqueeze {σ : Type} (r : Nat) (π : σ → σ)
    (extractRate : σ → List UInt8) (outLen : Nat) (s : σ) : List UInt8 :=
  spongeSqueezeFuel r π extractRate outLen outLen s

/-- Full multi-block absorb–pad–squeeze sponge parameterized by `(r, domByte, π, s0, xorBlk, extractRate)`. -/
@[expose] def evalSponge {σ : Type} (r : Nat) (domByte : UInt8) (π : σ → σ) (s0 : σ)
    (xorBlk : σ → List UInt8 → σ) (extractRate : σ → List UInt8)
    (msg : List UInt8) (outLen : Nat) : List UInt8 :=
  let absorbed := spongeAbsorbBlocks π xorBlk s0 (absorbPayload r domByte msg)
  spongeSqueeze r π extractRate outLen absorbed

private theorem spongeSqueezeFuel_length {σ : Type} {r : Nat} (hr : 0 < r) (π : σ → σ)
    (extractRate : σ → List UInt8) (hRate : ∀ s, (extractRate s).length = r) :
    ∀ (fuel outLen : Nat) (s : σ), outLen ≤ r * fuel →
      (spongeSqueezeFuel r π extractRate fuel outLen s).length = outLen
  | 0, outLen, _, h => by
    obtain rfl : outLen = 0 := by omega
    rfl
  | _ + 1, 0, _, _ => rfl
  | fuel + 1, outLen + 1, s, h => by
    simp only [spongeSqueezeFuel]
    if hle : outLen + 1 ≤ r then
      simp only [hle, ↓reduceIte, List.length_take, hRate]; omega
    else
      have hSub : outLen + 1 - r ≤ r * fuel := by rw [Nat.mul_succ] at h; omega
      simp only [hle, ↓reduceIte, List.length_append, hRate,
        spongeSqueezeFuel_length hr π extractRate hRate fuel (outLen + 1 - r) (π s) hSub]
      omega

theorem spongeSqueeze_length {σ : Type} {r : Nat} (hr : 0 < r) (π : σ → σ)
    (extractRate : σ → List UInt8) (hRate : ∀ s, (extractRate s).length = r)
    (outLen : Nat) (s : σ) :
    (spongeSqueeze r π extractRate outLen s).length = outLen :=
  spongeSqueezeFuel_length hr π extractRate hRate outLen outLen s
    (by simpa [Nat.one_mul] using Nat.mul_le_mul_right outLen hr)

/-- Concrete 64-byte (`poseidon2RateBytes = 64`) byte-state sponge instantiation. -/
def xorByteBlock (r : Nat) (state blk : List UInt8) : List UInt8 :=
  List.zipWith (· ^^^ ·) (state.take r) (blk.take r) ++ state.drop r

def evalRate64Sponge (π64 : List UInt8 → List UInt8) (msg : List UInt8) (outLen : Nat) : List UInt8 :=
  evalSponge poseidon2RateBytes domShake256 π64 (List.replicate 96 0)
    (xorByteBlock 64) (fun s => (s ++ List.replicate 64 0).take 64) msg outLen

theorem evalRate64Sponge_length (π64 : List UInt8 → List UInt8) (msg : List UInt8) (outLen : Nat) :
    (evalRate64Sponge π64 msg outLen).length = outLen :=
  spongeSqueeze_length (by decide) π64 _
    (fun s => by simp [poseidon2RateBytes, List.length_take]) outLen _

private theorem spongeAbsorb_keccak_eq_absorbBlocks :
    ∀ (k : Nat) (s : KState) (bytes : List UInt8),
      spongeAbsorbBlocks keccakF1600 xorRate136 s (sliceBlocks 136 k bytes) =
        absorbBlocks k s bytes
  | 0, _, _ => rfl
  | k + 1, s, bytes =>
    spongeAbsorb_keccak_eq_absorbBlocks k
      (keccakF1600 (xorRate136 s (bytes.take 136))) (bytes.drop 136)

private theorem spongeSqueezeFuel_136_eq :
    ∀ (fuel outLen : Nat) (s : KState),
      spongeSqueezeFuel 136 keccakF1600 rateBlockBytes fuel outLen s =
        squeezeXofFuel fuel outLen s
  | 0, _, _ => rfl
  | _ + 1, 0, _ => rfl
  | fuel + 1, outLen + 1, s => by
    simp only [spongeSqueezeFuel, squeezeXofFuel_succ_succ]
    split
    · rfl
    · exact congrArg (rateBlockBytes s ++ ·) (spongeSqueezeFuel_136_eq fuel (outLen + 1 - 136) _)

/-- **Exact Refinement (`evalSponge_keccak_eq_shake256Xof`)**:
    Generic `evalSponge` at `(136, 0x1F, keccakF1600, zeroKState, xorRate136, rateBlockBytes)` is
    extensionally identical to `Keccak.shake256Xof` for ALL `msg` and `outLen`. -/
theorem evalSponge_keccak_eq_shake256Xof (msg : List UInt8) (outLen : Nat) :
    evalSponge 136 domShake256 keccakF1600 zeroKState xorRate136 rateBlockBytes msg outLen =
      shake256Xof outLen msg := by
  unfold evalSponge absorbPayload spongeSqueeze shake256Xof
  dsimp only [domShake256]
  rw [pad10star1_136_eq_padForRate, spongeAbsorb_keccak_eq_absorbBlocks,
      spongeSqueezeFuel_136_eq, ← squeezeXofAux_eq]
  rw [absorbPadded_eq, shake256RateBytes_eq]

/-! ## 2. NIST SP 800-185 `leftEncode`, `encodeString`, `bytepad` Injectivity & Prefix-Freeness -/

private theorem append_left_cancel_local {α : Type} :
    ∀ (xs : List α) {ys zs : List α}, xs ++ ys = xs ++ zs → ys = zs
  | [], _, _, h => h
  | _ :: xs, _, _, h => append_left_cancel_local xs (List.cons.inj h).2

private theorem ofBE_natBytesLEAux :
    ∀ (fuel x : Nat), x ≤ fuel → ofBE (natBytesLEAux fuel x).reverse = x
  | 0, x, hx => by
    obtain rfl : x = 0 := Nat.eq_zero_of_le_zero hx
    rfl
  | fuel + 1, x, hx => by
    unfold natBytesLEAux
    if hx0 : x = 0 then subst hx0; rfl
    else
      simp only [hx0, ↓reduceIte, List.reverse_cons, ofBE_append_single, UInt8.toNat_ofNat']
      have hDivLe : x / 256 ≤ fuel :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (Nat.div_lt_self (Nat.pos_of_ne_zero hx0) (by decide)) hx)
      rw [ofBE_natBytesLEAux fuel (x / 256) hDivLe]
      have h8 : (2 : Nat) ^ 8 = 256 := rfl
      rw [h8, Nat.mod_mod, Nat.mul_comm, Nat.div_add_mod]

private theorem natBytesLEAux_last_nonzero :
    ∀ (fuel x : Nat), 0 < x → x ≤ fuel →
      ∃ b rest, (natBytesLEAux fuel x).reverse = b :: rest ∧ 0 < b.toNat
  | 0, _, hxPos, hxLe => False.elim (Nat.not_lt_of_ge hxLe hxPos)
  | fuel + 1, x, hxPos, hxLe => by
    have hxNe : x ≠ 0 := Nat.ne_of_gt hxPos
    unfold natBytesLEAux
    simp only [hxNe, ↓reduceIte, List.reverse_cons]
    if hq : x / 256 = 0 then
      have hNil : natBytesLEAux fuel (x / 256) = [] := by
        rw [hq]; cases fuel <;> simp [natBytesLEAux]
      rw [hNil]
      refine ⟨UInt8.ofNat (x % 256), [], rfl, ?_⟩
      simp only [UInt8.toNat_ofNat']
      have h8 : (2 : Nat) ^ 8 = 256 := rfl
      have hDiv := Nat.div_add_mod x 256
      rw [hq, Nat.mul_zero, Nat.zero_add] at hDiv
      rw [h8, Nat.mod_mod, hDiv]; exact hxPos
    else
      have hDivLe : x / 256 ≤ fuel :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (Nat.div_lt_self hxPos (by decide)) hxLe)
      obtain ⟨b, rest, hRev, hbPos⟩ := natBytesLEAux_last_nonzero fuel (x / 256) (Nat.pos_of_ne_zero hq) hDivLe
      exact ⟨b, rest ++ [UInt8.ofNat (x % 256)], by rw [hRev, List.cons_append], hbPos⟩

private theorem ofBE_foldl_ge :
    ∀ (xs : List UInt8) (acc : Nat),
      acc * 256 ^ xs.length ≤ xs.foldl (fun a u => a * 256 + u.toNat) acc
  | [], _ => by simp
  | u :: us, acc => by
    simp only [List.foldl_cons, List.length_cons]
    have h1 := Nat.mul_le_mul_right (256 ^ us.length) (Nat.le_add_right (acc * 256) u.toNat)
    have h2 := ofBE_foldl_ge us (acc * 256 + u.toNat)
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ us.length) 256, ← Nat.mul_assoc]
    exact Nat.le_trans h1 h2

private theorem ofBE_cons_ge {b : UInt8} (hb : 0 < b.toNat) (rest : List UInt8) :
    256 ^ rest.length ≤ ofBE (b :: rest) := by
  unfold ofBE
  simp only [List.foldl_cons, Nat.zero_mul, Nat.zero_add]
  have h1 : 1 * 256 ^ rest.length ≤ b.toNat * 256 ^ rest.length :=
    Nat.mul_le_mul_right (256 ^ rest.length) hb
  rw [Nat.one_mul] at h1
  exact Nat.le_trans h1 (ofBE_foldl_ge rest b.toNat)

theorem ofBE_natBytesBE (x : Nat) : ofBE (natBytesBE x) = x := by
  unfold natBytesBE
  dsimp only
  if hNil : natBytesLEAux x x = [] then
    simp only [hNil, ↓reduceIte]
    have hx0 : x = 0 := by
      have h := ofBE_natBytesLEAux x x (Nat.le_refl x)
      simpa [hNil, ofBE] using h.symm
    subst hx0; rfl
  else
    simp only [hNil, ↓reduceIte]
    exact ofBE_natBytesLEAux x x (Nat.le_refl x)

private theorem append_inj_local {α : Type} :
    ∀ {xs₁ xs₂ ys₁ ys₂ : List α},
      xs₁ ++ ys₁ = xs₂ ++ ys₂ → xs₁.length = xs₂.length → xs₁ = xs₂ ∧ ys₁ = ys₂
  | [], [], _, _, hEq, _ => ⟨rfl, hEq⟩
  | _ :: _, [], _, _, _, hLen => by cases hLen
  | [], _ :: _, _, _, _, hLen => by cases hLen
  | x₁ :: xs₁, x₂ :: xs₂, _, _, hEq, hLen => by
    obtain ⟨hx, hTail⟩ := List.cons.inj hEq
    obtain ⟨hxs, hys⟩ := append_inj_local hTail (Nat.succ.inj hLen)
    exact ⟨hx ▸ congrArg (x₁ :: ·) hxs, hys⟩

private theorem pow_le_pow_right_local {b : Nat} (hb : 0 < b) :
    ∀ {m n : Nat}, m ≤ n → b ^ m ≤ b ^ n
  | _, _, h => by
    induction h with
    | refl => exact Nat.le_refl _
    | step _ ih =>
      rw [Nat.pow_succ]
      exact Nat.le_trans (by simpa [Nat.mul_one] using ih) (Nat.mul_le_mul_left _ hb)

private theorem lt_of_pow_lt_pow_256 :
    ∀ (m n : Nat), 256 ^ m < 256 ^ n → m < n
  | m, 0, h => False.elim (Nat.not_lt_of_ge (Nat.one_le_pow m 256 (by decide)) (by rw [Nat.pow_zero] at h; exact h))
  | 0, n + 1, _ => Nat.zero_lt_succ n
  | m + 1, n + 1, h => by
    rw [Nat.pow_succ, Nat.pow_succ] at h
    have hlt : 256 ^ m < 256 ^ n :=
      if hm : 256 ^ m < 256 ^ n then hm
      else False.elim (Nat.not_lt_of_ge (Nat.mul_le_mul_right 256 (Nat.le_of_not_lt hm)) h)
    exact Nat.succ_lt_succ (lt_of_pow_lt_pow_256 m n hlt)

private theorem natBytesBE_length_le_255 {x : Nat} (hx : x < 256 ^ 255) :
    (natBytesBE x).length ≤ 255 := by
  if hx0 : x = 0 then
    subst hx0; decide
  else
    obtain ⟨b, rest, hRev, hbPos⟩ := natBytesLEAux_last_nonzero x x (Nat.pos_of_ne_zero hx0) (Nat.le_refl x)
    have hNonNil : natBytesLEAux x x ≠ [] := fun hNil => by rw [hNil] at hRev; cases hRev
    have hEq : natBytesBE x = b :: rest := by unfold natBytesBE; simp [hNonNil, hRev]
    have hPowLe : 256 ^ rest.length ≤ x := by
      rw [← ofBE_natBytesBE x, hEq]; exact ofBE_cons_ge hbPos rest
    have hRestLt : rest.length < 255 := lt_of_pow_lt_pow_256 rest.length 255 (Nat.lt_of_le_of_lt hPowLe hx)
    rw [hEq, List.length_cons]
    exact hRestLt

/-- Fast SP 800-185 bit-length bound witness avoiding kernel expansion of `256 ^ 255`. -/
theorem bitlen_lt_sp800_bound {s : List UInt8} (h : s.length ≤ 65536) :
    8 * s.length < 256 ^ 255 := by
  have h1 : 8 * s.length ≤ 8 * 65536 := Nat.mul_le_mul_left 8 h
  have h2 : 8 * 65536 < 256 ^ 3 := by decide
  have h3 : 256 ^ 3 ≤ 256 ^ 255 := pow_le_pow_right_local (by decide) (by decide)
  exact Nat.lt_of_le_of_lt h1 (Nat.lt_of_lt_of_le h2 h3)

/-- **SP 800-185 `leftEncode` Prefix Injectivity (`leftEncode_prefix_inj`)**:
    For all `x₁, x₂ < 256 ^ 255`, `leftEncode` is strictly left-self-delimiting. -/
theorem leftEncode_prefix_inj {x₁ x₂ : Nat} {r₁ r₂ : List UInt8}
    (hx₁ : x₁ < 256 ^ 255) (hx₂ : x₂ < 256 ^ 255)
    (hEq : leftEncode x₁ ++ r₁ = leftEncode x₂ ++ r₂) :
    x₁ = x₂ ∧ r₁ = r₂ := by
  unfold leftEncode at hEq
  simp only [List.cons_append, List.cons.injEq] at hEq
  have hLen₁ := natBytesBE_length_le_255 hx₁
  have hLen₂ := natBytesBE_length_le_255 hx₂
  have hByte := congrArg UInt8.toNat hEq.1
  simp only [UInt8.toNat_ofNat'] at hByte
  have h8 : (2 : Nat) ^ 8 = 256 := rfl
  rw [h8] at hByte
  have hMod₁ : (natBytesBE x₁).length % 256 = (natBytesBE x₁).length :=
    Nat.mod_eq_of_lt (Nat.lt_succ_of_le hLen₁)
  have hMod₂ : (natBytesBE x₂).length % 256 = (natBytesBE x₂).length :=
    Nat.mod_eq_of_lt (Nat.lt_succ_of_le hLen₂)
  rw [hMod₁, hMod₂] at hByte
  obtain ⟨hBytes, hRest⟩ := append_inj_local hEq.2 hByte
  have hxEq : x₁ = x₂ := by rw [← ofBE_natBytesBE x₁, ← ofBE_natBytesBE x₂, hBytes]
  exact ⟨hxEq, hRest⟩

/-- **SP 800-185 `encodeString` Prefix Injectivity (`encodeString_prefix_inj`)**. -/
theorem encodeString_prefix_inj {s₁ s₂ r₁ r₂ : List UInt8}
    (hs₁ : 8 * s₁.length < 256 ^ 255) (hs₂ : 8 * s₂.length < 256 ^ 255)
    (hEq : encodeString s₁ ++ r₁ = encodeString s₂ ++ r₂) :
    s₁ = s₂ ∧ r₁ = r₂ := by
  unfold encodeString at hEq
  rw [List.append_assoc, List.append_assoc] at hEq
  obtain ⟨hBitLen, hTail⟩ := leftEncode_prefix_inj hs₁ hs₂ hEq
  exact append_inj_local hTail (Nat.eq_of_mul_eq_mul_left (by decide) hBitLen)

/-- Full NIST SP 800-185 customization prefix `bytepad(encodeString(N) || encodeString(S), 136)`. -/
@[expose] def cshakePrefix (N S : List UInt8) : List UInt8 :=
  bytepad (encodeString N ++ encodeString S) 136

theorem cshakePrefix_empty_name_eq (S : List UInt8) :
    cshakePrefix [] S = customizationPrefix S := by rfl

private theorem pad_align_arith (L w : Nat) (hw : 0 < w) (hL : 1 ≤ L) :
    (L + (w - L % w) % w) % w = 0 ∧ w ≤ L + (w - L % w) % w := by
  have hDiv := Nat.div_add_mod L w
  have hModLt : L % w < w := Nat.mod_lt L hw
  if hRem0 : L % w = 0 then
    rw [hRem0, Nat.sub_zero, Nat.mod_self, Nat.add_zero]
    rw [hRem0, Nat.add_zero] at hDiv
    cases hq : L / w with
    | zero => rw [hq, Nat.mul_zero] at hDiv; exact False.elim (Nat.not_le_of_gt hL (Nat.le_of_eq hDiv.symm))
    | succ k =>
      rw [hq, Nat.mul_succ] at hDiv
      exact ⟨hRem0, hDiv ▸ Nat.le_add_left w (w * k)⟩
  else
    rw [Nat.mod_eq_of_lt (Nat.sub_lt hw (Nat.pos_of_ne_zero hRem0))]
    have hEq : L + (w - L % w) = w * (L / w) + w := by
      conv => lhs; arg 1; rw [← hDiv]
      rw [Nat.add_assoc, Nat.add_sub_of_le (Nat.le_of_lt hModLt)]
    rw [hEq, ← Nat.mul_succ, Nat.mul_mod_right]
    exact ⟨rfl, Nat.le_add_left w (w * (L / w))⟩

theorem bytepad_length_mod (bytes : List UInt8) {w : Nat} (hw : 0 < w) :
    (bytepad bytes w).length % w = 0 ∧ w ≤ (bytepad bytes w).length := by
  have hwNe : w ≠ 0 := Nat.ne_of_gt hw
  unfold bytepad
  simp only [hwNe, ↓reduceIte, List.length_append, List.length_replicate]
  exact pad_align_arith ((leftEncode w).length + bytes.length) w hw
    (by unfold leftEncode; simp only [List.length_cons, Nat.add_right_comm, Nat.add_assoc]; exact Nat.le_add_left 1 _)

/-- **Prefix-Free `cshakePrefix` Theorem (`cshakePrefix_prefix_free`)**:
    Even across arbitrary message suffixes `m₁, m₂`, `cshakePrefix N₁ S₁ ++ m₁ = cshakePrefix N₂ S₂ ++ m₂`
    forces `N₁ = N₂ ∧ S₁ = S₂ ∧ m₁ = m₂`! -/
theorem cshakePrefix_prefix_free {N₁ S₁ N₂ S₂ m₁ m₂ : List UInt8}
    (hN₁ : 8 * N₁.length < 256 ^ 255) (hS₁ : 8 * S₁.length < 256 ^ 255)
    (hN₂ : 8 * N₂.length < 256 ^ 255) (hS₂ : 8 * S₂.length < 256 ^ 255)
    (hEq : cshakePrefix N₁ S₁ ++ m₁ = cshakePrefix N₂ S₂ ++ m₂) :
    N₁ = N₂ ∧ S₁ = S₂ ∧ m₁ = m₂ := by
  have hUnfold : ∀ (N S : List UInt8),
      cshakePrefix N S = leftEncode 136 ++ encodeString N ++ encodeString S ++
        List.replicate ((136 - (leftEncode 136 ++ (encodeString N ++ encodeString S)).length % 136) % 136) 0 := by
    intro N S; unfold cshakePrefix bytepad; simp [List.append_assoc]
  have hEq' := hEq
  rw [hUnfold N₁ S₁, hUnfold N₂ S₂] at hEq'
  simp only [List.append_assoc] at hEq'
  have hBound136 : 136 < 256 ^ 255 := bitlen_lt_sp800_bound (s := List.replicate 17 0) (by decide)
  have hAfter136 : encodeString N₁ ++ (encodeString S₁ ++ _) = encodeString N₂ ++ (encodeString S₂ ++ _) :=
    (leftEncode_prefix_inj hBound136 hBound136 hEq').2
  obtain ⟨hNEq, hAfterN⟩ := encodeString_prefix_inj hN₁ hN₂ hAfter136
  obtain ⟨hSEq, _⟩ := encodeString_prefix_inj hS₁ hS₂ hAfterN
  subst hNEq hSEq
  exact ⟨rfl, rfl, append_left_cancel_local (cshakePrefix N₁ S₁) hEq⟩

/-- **`cshakePrefix_injective`**: distinct `(N, S)` pairs produce strictly distinct `bytepad` prefixes. -/
theorem cshakePrefix_injective {N₁ S₁ N₂ S₂ : List UInt8}
    (hN₁ : 8 * N₁.length < 256 ^ 255) (hS₁ : 8 * S₁.length < 256 ^ 255)
    (hN₂ : 8 * N₂.length < 256 ^ 255) (hS₂ : 8 * S₂.length < 256 ^ 255)
    (hEq : cshakePrefix N₁ S₁ = cshakePrefix N₂ S₂) :
    N₁ = N₂ ∧ S₁ = S₂ := by
  have h := cshakePrefix_prefix_free (m₁ := []) (m₂ := []) hN₁ hS₁ hN₂ hS₂ (by simpa using hEq)
  exact ⟨h.1, h.2.1⟩

/-- **Universal `cSHAKE256` Input-Domain Disjointness (`cshake256_domains_disjoint`)**:
    For ANY distinct `(N₁, S₁) ≠ (N₂, S₂)` (including when one pair is `([], [])`), their
    padded 136-byte sponge block sequences NEVER collide for ANY messages `m₁, m₂`! -/
theorem cshake256_domains_disjoint {N₁ S₁ N₂ S₂ : List UInt8} (m₁ m₂ : List UInt8)
    (hN₁ : 8 * N₁.length < 256 ^ 255) (hS₁ : 8 * S₁.length < 256 ^ 255)
    (hN₂ : 8 * N₂.length < 256 ^ 255) (hS₂ : 8 * S₂.length < 256 ^ 255)
    (hNe : (N₁, S₁) ≠ (N₂, S₂)) :
    let b₁ := if N₁ = [] ∧ S₁ = [] then absorbPayload 136 domShake256 m₁
              else absorbPayload 136 domCshake256 (cshakePrefix N₁ S₁ ++ m₁)
    let b₂ := if N₂ = [] ∧ S₂ = [] then absorbPayload 136 domShake256 m₂
              else absorbPayload 136 domCshake256 (cshakePrefix N₂ S₂ ++ m₂)
    b₁ ≠ b₂ := by
  dsimp only
  split <;> split
  · rename_i hEmpty₁ hEmpty₂
    exact False.elim (hNe (Prod.ext (hEmpty₁.1.trans hEmpty₂.1.symm) (hEmpty₁.2.trans hEmpty₂.2.symm)))
  · exact absorbPayload_cross_domain_disjoint _ _ (by decide) (by decide) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
  · exact fun h => absorbPayload_cross_domain_disjoint _ _ (by decide) (by decide) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩ h.symm
  · intro hBlocks
    have hMsg := pad10star1_injective (by decide) ⟨by decide, by decide⟩ hBlocks
    obtain ⟨hNEq, hSEq, _⟩ := cshakePrefix_prefix_free hN₁ hS₁ hN₂ hS₂ hMsg
    exact hNe (Prod.ext hNEq hSEq)

/-- Canonical `QSAG.*` customization tags (ASCII byte literals: `CANOPY.LEAF/v1`, `CANOPY.NODE/v1`, `FS/v1`, `FTS.OT.PAD.V1`). -/
def qsagTagCanopyLeaf : List UInt8 := [81, 83, 65, 71, 46, 87, 72, 73, 82, 46, 67, 65, 78, 79, 80, 89, 46, 76, 69, 65, 70, 47, 118, 49]
def qsagTagCanopyNode : List UInt8 := [81, 83, 65, 71, 46, 87, 72, 73, 82, 46, 67, 65, 78, 79, 80, 89, 46, 78, 79, 68, 69, 47, 118, 49]
def qsagTagFiatShamir : List UInt8 := [81, 83, 65, 71, 46, 70, 83, 47, 118, 49]
def qsagTagFtsOtPad   : List UInt8 := [81, 83, 65, 71, 46, 70, 84, 83, 46, 79, 84, 46, 80, 65, 68, 46, 86, 49]

theorem qsag_tags_sponge_domains_disjoint (m₁ m₂ : List UInt8) :
    absorbPayload 136 domCshake256 (cshakePrefix [] qsagTagCanopyLeaf ++ m₁) ≠
      absorbPayload 136 domCshake256 (cshakePrefix [] qsagTagCanopyNode ++ m₂) ∧
    absorbPayload 136 domCshake256 (cshakePrefix [] qsagTagCanopyLeaf ++ m₁) ≠
      absorbPayload 136 domCshake256 (cshakePrefix [] qsagTagFiatShamir ++ m₂) ∧
    absorbPayload 136 domCshake256 (cshakePrefix [] qsagTagFiatShamir ++ m₁) ≠
      absorbPayload 136 domCshake256 (cshakePrefix [] qsagTagFtsOtPad ++ m₂) := by
  have b0 : 8 * ([] : List UInt8).length < 256 ^ 255 := bitlen_lt_sp800_bound (by decide)
  have b1 : 8 * qsagTagCanopyLeaf.length < 256 ^ 255 := bitlen_lt_sp800_bound (by decide)
  have b2 : 8 * qsagTagCanopyNode.length < 256 ^ 255 := bitlen_lt_sp800_bound (by decide)
  have b3 : 8 * qsagTagFiatShamir.length < 256 ^ 255 := bitlen_lt_sp800_bound (by decide)
  have b4 : 8 * qsagTagFtsOtPad.length < 256 ^ 255 := bitlen_lt_sp800_bound (by decide)
  exact ⟨fun h => absurd (cshakePrefix_prefix_free b0 b1 b0 b2 (pad10star1_injective (by decide) ⟨by decide, by decide⟩ h)).2.1 (by decide),
         fun h => absurd (cshakePrefix_prefix_free b0 b1 b0 b3 (pad10star1_injective (by decide) ⟨by decide, by decide⟩ h)).2.1 (by decide),
         fun h => absurd (cshakePrefix_prefix_free b0 b3 b0 b4 (pad10star1_injective (by decide) ⟨by decide, by decide⟩ h)).2.1 (by decide)⟩

/-! ## 3. Precomputed-Midstate `cSHAKE256` Equivalence Theorem -/

/-- `leftEncode 136 = [1, 136]` uses 2 bytes, so any `(N, S)` with
    `(encodeString N ++ encodeString S).length ≤ 134` produces an exact single 136-byte `bytepad` block. -/
theorem cshakePrefix_single_block_length {N S : List UInt8}
    (hFit : (encodeString N ++ encodeString S).length ≤ 134) :
    (cshakePrefix N S).length = 136 := by
  rw [List.length_append] at hFit
  unfold cshakePrefix bytepad
  have h136Ne : (136 : Nat) ≠ 0 := by decide
  simp only [h136Ne, ↓reduceIte, List.length_append, List.length_replicate]
  have hLeLen : (leftEncode 136).length = 2 := by decide
  rw [hLeLen]
  let L := 2 + ((encodeString N).length + (encodeString S).length)
  change L + (136 - L % 136) % 136 = 136
  if hEq136 : L = 136 then
    rw [hEq136]
  else
    have hMod : L % 136 = L := Nat.mod_eq_of_lt (by omega)
    rw [hMod, Nat.mod_eq_of_lt (by omega)]; omega

theorem qsag_all_tags_single_block :
    (cshakePrefix [] qsagTagCanopyLeaf).length = 136 ∧ (cshakePrefix [] qsagTagCanopyNode).length = 136 ∧
    (cshakePrefix [] qsagTagFiatShamir).length = 136 ∧ (cshakePrefix [] qsagTagFtsOtPad).length = 136 :=
  ⟨cshakePrefix_single_block_length (by decide), cshakePrefix_single_block_length (by decide),
   cshakePrefix_single_block_length (by decide), cshakePrefix_single_block_length (by decide)⟩

private theorem pad10star1_block_aligned_prefix {r : Nat} (hr : 0 < r) (domByte : UInt8)
    (pfx msg : List UInt8) (hAligned : pfx.length % r = 0) :
    pad10star1 r domByte (pfx ++ msg) = pfx ++ pad10star1 r domByte msg := by
  have hrNe : r ≠ 0 := by omega
  have hModEq : (pfx ++ msg).length % r = msg.length % r := by
    rw [List.length_append, Nat.add_mod, hAligned, Nat.zero_add, Nat.mod_mod]
  unfold pad10star1
  simp only [hrNe, ↓reduceIte, hModEq]
  split <;> simp only [List.append_assoc]

private theorem absorbPayload_single_block_prefix {r : Nat} (hr : 0 < r) (domByte : UInt8)
    (blk msg : List UInt8) (hBlk : blk.length = r) :
    absorbPayload r domByte (blk ++ msg) = blk :: absorbPayload r domByte msg := by
  dsimp only [absorbPayload]
  have hAligned : blk.length % r = 0 := by rw [hBlk, Nat.mod_self]
  rw [pad10star1_block_aligned_prefix hr domByte blk msg hAligned]
  let pm := pad10star1 r domByte msg
  have hDiv : (blk ++ pm).length / r = pm.length / r + 1 := by
    rw [List.length_append, hBlk, Nat.add_comm r pm.length, Nat.add_div_right pm.length hr]
  change sliceBlocks r ((blk ++ pm).length / r) (blk ++ pm) = blk :: sliceBlocks r (pm.length / r) pm
  rw [hDiv]
  simp only [sliceBlocks]
  rw [← hBlk, List.take_left, List.drop_left]

/-- Full from-scratch SP 800-185 `cSHAKE256` parameterized over permutation `π`. -/
@[expose] def evalCshake256Sponge {σ : Type} (π : σ → σ) (zeroState : σ)
    (xorBlock : σ → List UInt8 → σ) (extractRate : σ → List UInt8)
    (N S msg : List UInt8) (outLen : Nat) : List UInt8 :=
  if N = [] ∧ S = [] then
    evalSponge 136 domShake256 π zeroState xorBlock extractRate msg outLen
  else
    evalSponge 136 domCshake256 π zeroState xorBlock extractRate (cshakePrefix N S ++ msg) outLen

/-- Precomputed-midstate `cSHAKE256` starting directly from `midstate := π (xorBlock zeroState (cshakePrefix N S))`. -/
@[expose] def evalCshake256FromMidstate {σ : Type} (π : σ → σ)
    (xorBlock : σ → List UInt8 → σ) (extractRate : σ → List UInt8)
    (midstate : σ) (msg : List UInt8) (outLen : Nat) : List UInt8 :=
  evalSponge 136 domCshake256 π midstate xorBlock extractRate msg outLen

/-- **Precomputed-Midstate Equivalence Theorem (`cshake_precomputed_midstate_eq`)**:
    Whenever `(N, S) ≠ ([], [])` and `(encodeString N ++ encodeString S).length ≤ 134` (single
    136-byte `bytepad` block), absorbing `msg` from
    `midstate := π (xorBlock zeroState (bytepad (encodeString N ++ encodeString S) 136))` produces
    **bit-for-bit identical squeezed output** for ALL `msg` and ALL `outLen` as full `cSHAKE256`! -/
theorem cshake_precomputed_midstate_eq {σ : Type} (π : σ → σ) (zeroState : σ)
    (xorBlock : σ → List UInt8 → σ) (extractRate : σ → List UInt8)
    (N S msg : List UInt8) (outLen : Nat)
    (hNonEmpty : ¬ (N = [] ∧ S = []))
    (hFit : (encodeString N ++ encodeString S).length ≤ 134) :
    let midstate := π (xorBlock zeroState (bytepad (encodeString N ++ encodeString S) 136))
    evalCshake256FromMidstate π xorBlock extractRate midstate msg outLen =
      evalCshake256Sponge π zeroState xorBlock extractRate N S msg outLen := by
  dsimp only
  unfold evalCshake256FromMidstate evalCshake256Sponge
  simp only [hNonEmpty, ↓reduceIte]
  unfold evalSponge
  have hLen136 : (cshakePrefix N S).length = 136 := cshakePrefix_single_block_length hFit
  rw [absorbPayload_single_block_prefix (by decide) domCshake256 (cshakePrefix N S) msg hLen136]
  rfl

/-- **Concrete `Keccak-f[1600]` Precomputed-Midstate Equivalence (`keccak_cshake256_precomputed_midstate_eq`)**:
    Directly certifies fast-hash midstate caching against `Keccak.cshake256Xof`! -/
theorem keccak_cshake256_precomputed_midstate_eq
    (S msg : List UInt8) (outLen : Nat)
    (hNonEmpty : S ≠ [])
    (hFit : (encodeString [] ++ encodeString S).length ≤ 134) :
    let midstate := keccakF1600 (xorRate136 zeroKState (customizationPrefix S))
    let paddedMsg := padForRate msg 0x04
    squeezeXofAux outLen (absorbBlocks (paddedMsg.length / 136) midstate paddedMsg) =
      cshake256Xof outLen S msg := by
  dsimp only
  have hGen := cshake_precomputed_midstate_eq keccakF1600 zeroKState xorRate136 rateBlockBytes
    [] S msg outLen (fun h => hNonEmpty h.2) hFit
  dsimp only at hGen
  unfold evalCshake256FromMidstate evalCshake256Sponge at hGen
  rw [ite_eq_right_iff.mpr (fun h : ([] : List UInt8) = [] ∧ S = [] => False.elim (hNonEmpty h.2))] at hGen
  unfold evalSponge absorbPayload spongeSqueeze at hGen
  dsimp only [domCshake256] at hGen
  have hCust : bytepad (encodeString [] ++ encodeString S) 136 = customizationPrefix S := rfl
  rw [hCust, cshakePrefix_empty_name_eq, pad10star1_136_eq_padForRate, pad10star1_136_eq_padForRate,
      spongeAbsorb_keccak_eq_absorbBlocks, spongeAbsorb_keccak_eq_absorbBlocks,
      spongeSqueezeFuel_136_eq, spongeSqueezeFuel_136_eq,
      ← squeezeXofAux_eq, ← squeezeXofAux_eq] at hGen
  unfold cshake256Xof
  simp only [hNonEmpty, ↓reduceIte, absorbPadded_eq, shake256RateBytes_eq]
  exact hGen

/-! ## 4. `#tooth` Cryptanalytic Refutations & Assurance Gates -/

/-- **`#tooth` Unframed Concatenation Collision (`tooth_unframed_concat_collides`)**:
    Without SP 800-185 `encodeString` length-framing, naive `S ++ m` collides immediately on
    `("AB", "C")` vs `("A", "BC")`, whereas `cshakePrefix` separates them! -/
theorem tooth_unframed_concat_collides :
    ∃ (S₁ m₁ S₂ m₂ : List UInt8),
      S₁ = [0x41, 0x42] ∧ m₁ = [0x43] ∧ S₂ = [0x41] ∧ m₂ = [0x42, 0x43] ∧
      S₁ ≠ S₂ ∧ S₁ ++ m₁ = S₂ ++ m₂ ∧
      cshakePrefix [] S₁ ++ m₁ ≠ cshakePrefix [] S₂ ++ m₂ := by
  refine ⟨[0x41, 0x42], [0x43], [0x41], [0x42, 0x43], rfl, rfl, rfl, rfl, by decide, rfl, ?_⟩
  intro hEq
  have hS := (cshakePrefix_prefix_free
    (bitlen_lt_sp800_bound (by decide)) (bitlen_lt_sp800_bound (by decide))
    (bitlen_lt_sp800_bound (by decide)) (bitlen_lt_sp800_bound (by decide)) hEq).2.1
  exact absurd hS (by decide)

/-- **`#tooth` Zero Domain-Byte Padding Collision (`tooth_zero_domByte_pad10star1_collides`)**:
    Omitting `ValidDomByte` (`domByte = 0x00`) causes `[]` and `[0x00]` to collide identically! -/
theorem tooth_zero_domByte_pad10star1_collides :
    ∃ (m₁ m₂ : List UInt8), ¬ ValidDomByte 0x00 ∧ m₁ ≠ m₂ ∧
      absorbPayload 136 0x00 m₁ = absorbPayload 136 0x00 m₂ := by
  refine ⟨[], [0x00], by decide, by decide, ?_⟩
  have hPad : pad10star1 136 0x00 [] = pad10star1 136 0x00 [0x00] := by
    unfold pad10star1
    change ([] ++ [0] ++ List.replicate 134 0 ++ [0x80] : List UInt8) = ([0] ++ [0] ++ List.replicate 133 0 ++ [0x80] : List UInt8)
    have hRep : (List.replicate 134 0 : List UInt8) = 0 :: List.replicate 133 0 := rfl
    rw [hRep]; rfl
  unfold absorbPayload; rw [hPad]

/-- **`#tooth` Multi-Block Customization Overflow (`tooth_oversized_tag_midstate_single_block_fails`)**:
    When `(encodeString [] ++ encodeString S).length > 134` (`|S| = 131` bytes), `cshakePrefix [] S`
    spans 2 blocks (`272 ≠ 136` bytes), refuting single-block midstate truncation! -/
theorem tooth_oversized_tag_midstate_single_block_fails :
    ∃ S : List UInt8,
      S = List.replicate 131 0x41 ∧
      ¬ ((encodeString [] ++ encodeString S).length ≤ 134) ∧
      (cshakePrefix [] S).length = 272 ∧ (cshakePrefix [] S).length ≠ 136 := by
  have hB0 : natBytesBE 0 = [0] := by decide
  have hB136 : natBytesBE 136 = [136] := by decide
  have hB1048 : natBytesBE 1048 = [4, 24] := by decide
  have hEncLen : (encodeString [] ++ encodeString (List.replicate 131 0x41)).length = 136 := by
    simp only [encodeString, leftEncode, List.length_append, List.length_replicate,
      List.length_nil, Nat.mul_zero, hB0, hB1048, List.length_cons]
  have hPfxLen : (cshakePrefix [] (List.replicate 131 0x41)).length = 272 := by
    unfold cshakePrefix bytepad
    simp only [show (136 : Nat) ≠ 0 from by decide, ↓reduceIte, List.length_append,
      List.length_replicate, hEncLen, leftEncode, hB136, List.length_cons, List.length_nil]
  exact ⟨List.replicate 131 0x41, rfl, by rw [hEncLen]; decide, hPfxLen, by rw [hPfxLen]; decide⟩

theorem witness_pad10star1_valid_domain :
    ∃ (r : Nat) (d : UInt8) (m₁ m₂ : List UInt8),
      0 < r ∧ ValidDomByte d ∧ absorbPayload r d m₁ = absorbPayload r d m₂ :=
  ⟨136, domShake256, [0x61, 0x62], [0x61, 0x62], by decide, ⟨by decide, by decide⟩, rfl⟩

theorem witness_cross_domain_pair :
    ∃ (r : Nat) (d₁ d₂ : UInt8) (m₁ m₂ : List UInt8),
      m₁ = [0x01] ∧ m₂ = [0x02] ∧
      0 < r ∧ ValidDomByte d₁ ∧ ValidDomByte d₂ ∧ d₁ ≠ d₂ :=
  ⟨136, domShake256, domCshake256, [0x01], [0x02], rfl, rfl,
   by decide, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, by decide⟩

theorem witness_cshakePrefix_canopy :
    ∃ (N₁ S₁ N₂ S₂ m₁ m₂ : List UInt8),
      8 * N₁.length < 256 ^ 255 ∧ 8 * S₁.length < 256 ^ 255 ∧
      8 * N₂.length < 256 ^ 255 ∧ 8 * S₂.length < 256 ^ 255 ∧
      cshakePrefix N₁ S₁ ++ m₁ = cshakePrefix N₂ S₂ ++ m₂ :=
  ⟨[], qsagTagCanopyLeaf, [], qsagTagCanopyLeaf, [0x01], [0x01],
   bitlen_lt_sp800_bound (by decide), bitlen_lt_sp800_bound (by decide),
   bitlen_lt_sp800_bound (by decide), bitlen_lt_sp800_bound (by decide), rfl⟩

theorem witness_keccak_midstate_canopy :
    ∃ (S msg : List UInt8) (outLen : Nat),
      S ≠ [] ∧ (encodeString [] ++ encodeString S).length ≤ 134 ∧
      (cshake256Xof outLen S msg).length = 32 :=
  ⟨qsagTagCanopyLeaf, [0xde, 0xad, 0xbe, 0xef], 32, by decide, by decide, by simp⟩

#verify_constructive Qsag.pad10star1_joint_injective Qsag.pad10star1_injective
  Qsag.absorbPayload_cross_domain_disjoint Qsag.evalSponge_keccak_eq_shake256Xof
  Qsag.leftEncode_prefix_inj Qsag.encodeString_prefix_inj Qsag.cshakePrefix_prefix_free
  Qsag.cshakePrefix_injective Qsag.cshake256_domains_disjoint
  Qsag.cshake_precomputed_midstate_eq Qsag.keccak_cshake256_precomputed_midstate_eq

#verify_inhabited Qsag.pad10star1_injective Qsag.witness_pad10star1_valid_domain
#verify_inhabited Qsag.absorbPayload_cross_domain_disjoint Qsag.witness_cross_domain_pair
#verify_inhabited Qsag.cshakePrefix_prefix_free Qsag.witness_cshakePrefix_canopy
#verify_inhabited Qsag.keccak_cshake256_precomputed_midstate_eq Qsag.witness_keccak_midstate_canopy

#tooth_pair Qsag.pad10star1_injective vs Qsag.tooth_zero_domByte_pad10star1_collides
#tooth_pair Qsag.cshakePrefix_prefix_free vs Qsag.tooth_unframed_concat_collides
#tooth_pair Qsag.cshakePrefix_single_block_length vs Qsag.tooth_oversized_tag_midstate_single_block_fails

end Qsag
end
