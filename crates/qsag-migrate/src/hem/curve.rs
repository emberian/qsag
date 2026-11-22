//! Non-native field arithmetic and fixed-base scalar multiplication for secp256k1, Ed25519
//! and BLS12-381 G1 over the Goldilocks constraint system of
//! `qsag_agg::zk_hem::relation`.
//!
//! # Representation
//!
//! An integer is a polynomial in `t = 2^8` whose coefficients are linear forms, each with a
//! proven integer interval `[lo, hi]` (`Coef`). A fresh witness is 8-bit limbs, one row per
//! bit. Sums and differences are free and only widen the intervals. A product of two such
//! polynomials costs one row per coefficient (`mul_poly`): the coefficient variables are
//! fixed by evaluating both sides at as many points as there are coefficients.
//!
//! # Reduction and its overflow bound
//!
//! `x = 0 (mod p)` is proved in three steps (`enforce_zero_mod`).
//!
//! 1. Fold. A coefficient `c_k` at a limb position `k >= limbs(p)` is replaced by
//!    `c_k d_(k,j)` added at the positions `j < limbs(p)`, where `d_(k,j)` are public
//!    signed digits with `sum_j d_(k,j) 2^(8j) = 2^(8k) mod p` (asserted when the modulus
//!    is built, by construction from the native reduction). The folded integer is congruent
//!    to `x`, its intervals follow by interval arithmetic, and it costs no rows.
//! 2. Quotient. The folded integer `x'` satisfies `x' + K p - q p = 0` with `q` a
//!    bit-decomposed witness and `K` a public offset that makes `q` non-negative. Because
//!    `x'` is at most a few dozen bits longer than `p`, `q` has 14 to 30 bits rather than
//!    the bit length of `p`.
//! 3. Carries. The identity is checked limb group by limb group. Every carry is
//!    range-checked to an interval derived from the coefficient intervals, and the builder
//!    asserts, for every group equation, that the absolute value of its left side over all
//!    admitted values is below the Goldilocks prime. A group equation that holds in the
//!    field therefore holds over the integers.
//!
//! No step relies on a wrap not happening by accident: if an interval is too wide,
//! synthesis panics.
//!
//! This is the single-auxiliary-modulus-free end of the design space described in
//! `paperbin/foreign-field-plonk.pdf` (Ambrona, Firsov, Querejeta-Azurmendi, Section 1 and
//! the discussion of [LB22]): they check the integer identity modulo the native modulus
//! and auxiliary moduli and bound its magnitude. That residue-number variant was costed
//! for this system and not adopted. With 64-bit Goldilocks, residues modulo auxiliary
//! moduli near `2^35` (the largest for which a 32-term sum of 2^22-bounded coefficients
//! cannot wrap) need a 27-bit range-checked quotient each, and six of them to cover a
//! 256-bit identity: about 160 range rows against about 125 for the carry chain here.
//! The folding step is this module's own; the papers do not claim it.
//!
//! # Scalar multiplication
//!
//! `[k]G = [2k]H` with `H = [1/2]G`. The scalar bits below the last 6 are cut into signed
//! windows of 11 bits (one shorter window closes the gap). A window with value `u`
//! contributes the odd multiple `(2u + 1 - 2^w) 2^lo` of `H`, so its table holds `2^(w-1)`
//! points and the top window bit selects the sign of `y`. The last window (6 bits) is
//! unsigned and carries the constant `2^lo - 1` that the signed windows leave over. Every
//! partial sum `S` of signed windows is an odd integer with `|S| < 2^lo <= |T|` for the
//! next addend `T`, and `|S| + |T| < 2^250 <` group order, so `S != +-T` and neither is
//! zero: the incomplete chord formula is exact there for every Boolean input. The last
//! addition can meet `S = T` or `S = -T`; it carries the extra tangent-compatible equation
//! of `add_step`, which makes doubling exact and leaves `S = -T` (scalar `= 0 mod` order)
//! unsatisfiable.
//!
//! The accumulator keeps `y` unreduced, as `lambda (x_T - x_3) - y_T`, so one addition
//! costs two reduced witnesses (`lambda`, `x_3`) and two quotients.
//!
//! A table lookup resolves the low 8 index bits through their 247 subset products, where
//! every table column is a linear form, and the high 2 bits by 3 rows per output. No table
//! entry is addressed by a witness value: the assignment is computed by evaluating those
//! forms.
//!
//! # Point additions with a variable point
//!
//! `P + [k]G` (`secp256k1_add_fixed_base`, `secp256k1_taproot_tweak`,
//! `ed25519_add_fixed_base`) is one ladder and one `complete` addition. It is not cheaper
//! than the scalar route `[(k_P + k) mod n]G`: both need one multiplication, because
//! `[k]G` has to be formed either way. A BIP32 path with three public keys on it needs
//! three multiplications by either route.
//!
//! # Hints, for a prover that holds the witness in shares
//!
//! A variable is a *hint* when it is neither a linear form nor a product of earlier
//! variables. [`HintCount`] counts them per gadget (wrap the constraint system in
//! [`Metered`]). They are:
//!
//! * element bits: the bit decomposition of a residue (a slope, a coordinate, a reduced
//!   product). From shares: compute the residue in the foreign field (`divisions` counts
//!   those that are a quotient, which needs one shared inversion), then a shared bit
//!   decomposition of a value below `2^bits`;
//! * quotient bits: `(x + K p) / p` for the folded integer `x`, 14 to 30 bits. From
//!   shares: the integer `x` is a public linear form of earlier limbs and product
//!   coefficients, so `x mod p` is known from the element it is compared with and the
//!   quotient is a shared exact division by a public constant, then a bit decomposition;
//! * carry bits: each carry is a public linear form of earlier variables divided by a
//!   power of two (exactly); only its bit decomposition is needed;
//! * zero tests: the inverse-or-zero of a small sum of bits, in comparisons with constants.
//!   [`Options::product_only_comparisons`] replaces them by product chains (about 3 % more
//!   rows in a scalar multiplication), leaving bit decompositions as the only hints.
//!
//! Everything else (limb variables, product coefficients, subset products, table outputs,
//! selected signs) is a product of two linear forms or a public linear image of such
//! products. Bit decompositions cannot be avoided in this row format: a range check is
//! one row per bit and the bits are its witnesses.
//!
//! # Wanted from the constraint system: a range row type
//!
//! Within `a * b = c` rows a range check is one row per bit, and those rows are 59 % of a
//! scalar multiplication (18,669 of 31,785 for secp256k1). Limb width, carry grouping,
//! window width (10, 11 and 12 bits with last windows of 3 to 8 were measured; 11 and 6 is
//! the minimum) and the table layout are at their optimum for this row format; what is left
//! is the row format. The interface below is what this module would call. Nothing here
//! depends on how the argument is realised (LogUp over the committed assignment is the
//! obvious candidate); the counts are exact, from [`HintCount::range_lookups`].
//!
//! ```text
//! impl ConstraintSystem {
//!     /// Enforce `0 <= value < 256` as an integer, for the canonical representative of
//!     /// the linear form. One lookup into the fixed table `{0, .., 255}`; no row.
//!     pub fn enforce_byte(&mut self, value: &Lc);
//!     /// How many lookups the relation holds (the cost metric beside `num_rows`).
//!     pub fn num_lookups(&self) -> usize;
//! }
//! ```
//!
//! That single primitive is enough. A limb of `w < 8` bits is `enforce_byte(v)` and
//! `enforce_byte(2^(8 - w) v)`; a carry in `[lo, lo + 2^n)` is the same on `carry - lo`,
//! limb by limb. The soundness requirement is the one bit rows meet today: the looked-up
//! value is a single field element, so `value < 256` must hold for the field element
//! itself, with no reduction modulo anything smaller than the Goldilocks prime.
//!
//! Where the lookups go, per gadget (`alloc_bits` is the only caller that changes; bits
//! stay as rows only where a consumer needs them: the scalar, and the two output
//! coordinates that are hashed):
//!
//! | gadget | rows now | rows then | byte lookups |
//! |---|---|---|---|
//! | non-native multiplication | 440 | 64 | 121 |
//! | secp256k1 fixed-base multiplication | 31,785 | about 13,650 | about 2,760 |
//! | Ed25519 fixed-base multiplication | 32,066 | about 13,750 | about 2,780 |
//! | BLS12-381 G1 fixed-base multiplication | 52,346 | about 18,050 | about 5,120 |
//! | secp256k1 Taproot tweak (after the internal key) | 33,136 | about 14,050 | about 3,010 |
//!
//! "Rows then" keeps the 512 output bits (768 for BLS12-381) as rows. A secp256k1
//! multiplication spends its lookups on 47 elements of 32 limbs (1,504), 48 quotients of
//! 15 bits (144) and 312 carries of two to three limbs (1,178), less the 64 of the
//! outputs that stay bits.
//!
//! A second primitive would remove most of what is left:
//!
//! ```text
//!     /// Register a public table of `width`-tuples; returns its handle.
//!     pub fn table(&mut self, width: usize, rows: Vec<F>) -> TableId;
//!     /// Enforce that `tuple` is a row of the table. One lookup; no row.
//!     pub fn enforce_in_table(&mut self, table: TableId, tuple: &[Lc]);
//! ```
//!
//! A window lookup is then one tuple `(index, x limbs.., y chunks..)` of width 39 (55 for
//! BLS12-381) into a table of 1,024 rows instead of 378 rows, and the same call with the
//! table `{0, .., 255}` is `enforce_byte`. That brings a secp256k1 multiplication to about
//! 5,300 rows, 23 tuple lookups and 2,760 byte lookups. The window tables hold 22,720
//! points per curve; they are public and fixed, so they belong in the relation's digest
//! like every other constant.
//!
//! # Witness handling
//!
//! Native arithmetic on witness values is branch-free with fixed iteration counts. Its
//! stack temporaries are not erased. Without `std` the window tables (about 23,000 points
//! per curve) are rebuilt on every call.

use alloc::vec;
use alloc::vec::Vec;

use qsag_agg::field::Goldilocks;
use qsag_agg::zk_hem::relation::{ConstraintSystem, Def, IntCoef, Lc, Source, SourceId};

type F = Goldilocks;
/// Words of a native integer: enough for the 381-bit BLS12-381 base field.
const NW: usize = 6;
type Big = [u64; NW];
const WIDE: usize = 9;
type Wide = [u64; WIDE];

/// The Goldilocks prime.
const PG: i128 = 0xFFFF_FFFF_0000_0001;
/// Largest absolute coefficient bound a polynomial may carry.
const COEF_BOUND: i128 = 1 << 62;
/// Signed windows are this wide (sign bit included); a shorter one closes the gap to the
/// last window.
const SIGNED_WINDOW: usize = 11;
/// Width of the last, unsigned window.
const LAST_WINDOW: usize = 6;
/// Table index bits resolved by subset products; the rest select among sub-tables.
const LOW_INDEX_BITS: usize = 8;
/// A looked-up `y` is delivered in chunks of this many limbs.
const Y_CHUNK_LIMBS: usize = 6;

// ============================================================================
// Hosts, options and hint accounting
// ============================================================================

/// Choices that trade rows for a simpler witness.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Options {
    /// Comparisons with constants use product chains only (no zero-test hints). A
    /// canonical check then costs about one row per bit instead of about three per run of
    /// equal bits of the bound.
    pub product_only_comparisons: bool,
}

/// Variables whose values are neither linear forms nor products of earlier variables.
///
/// Every other variable these gadgets allocate is a product of two linear forms, or a
/// fixed linear combination of such products (the coefficients of a limb product are the
/// interpolation of its evaluation rows; a table output is a sum of selector products).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct HintCount {
    /// Bit-decomposed residues: slopes, coordinates, reduced products.
    pub elements: usize,
    /// Their bits.
    pub element_bits: usize,
    /// Elements that are a quotient in the foreign field (a slope, an Edwards coordinate).
    pub divisions: usize,
    /// Quotients `(x + K p) / p` of reductions.
    pub quotients: usize,
    pub quotient_bits: usize,
    /// Carries of reductions and integer normalisations.
    pub carries: usize,
    pub carry_bits: usize,
    /// `inverse-or-zero` hints of constant comparisons and non-zero checks.
    pub zero_tests: usize,
    /// 8-bit range lookups that would replace every bit row counted above, were a range
    /// row type available (see "Wanted" in the module documentation): one per full limb,
    /// and for a partial limb of `w` bits the cheaper of `w` bit rows and two lookups.
    pub range_lookups: usize,
}

/// See [`HintCount::range_lookups`].
fn range_lookups(bits: usize) -> usize {
    bits / 8 + (bits % 8).min(2)
}

impl HintCount {
    fn add(&mut self, rhs: &HintCount) {
        self.elements += rhs.elements;
        self.element_bits += rhs.element_bits;
        self.divisions += rhs.divisions;
        self.quotients += rhs.quotients;
        self.quotient_bits += rhs.quotient_bits;
        self.carries += rhs.carries;
        self.carry_bits += rhs.carry_bits;
        self.zero_tests += rhs.zero_tests;
        self.range_lookups += rhs.range_lookups;
    }

    /// All hint variables (bits and zero-test inverses).
    pub fn variables(&self) -> usize {
        self.element_bits + self.quotient_bits + self.carry_bits + self.zero_tests
    }
}

/// What a gadget is synthesised into: a [`ConstraintSystem`], or one wrapped in
/// [`Metered`] to pick [`Options`] and collect the [`HintCount`].
pub trait Host {
    fn constraint_system(&mut self) -> &mut ConstraintSystem;
    fn options(&self) -> Options {
        Options::default()
    }
    fn record(&mut self, _hints: &HintCount) {}
}

impl Host for ConstraintSystem {
    fn constraint_system(&mut self) -> &mut ConstraintSystem {
        self
    }
}

/// A constraint system with options and a running hint count.
pub struct Metered<'a> {
    pub cs: &'a mut ConstraintSystem,
    pub options: Options,
    pub hints: HintCount,
}

impl<'a> Metered<'a> {
    pub fn new(cs: &'a mut ConstraintSystem, options: Options) -> Self {
        Self {
            cs,
            options,
            hints: HintCount::default(),
        }
    }
}

impl Host for Metered<'_> {
    fn constraint_system(&mut self) -> &mut ConstraintSystem {
        self.cs
    }
    fn options(&self) -> Options {
        self.options
    }
    fn record(&mut self, hints: &HintCount) {
        self.hints.add(hints);
    }
}

struct Ctx<'a> {
    cs: &'a mut ConstraintSystem,
    options: Options,
    hints: HintCount,
}

impl core::ops::Deref for Ctx<'_> {
    type Target = ConstraintSystem;
    fn deref(&self) -> &ConstraintSystem {
        self.cs
    }
}

impl core::ops::DerefMut for Ctx<'_> {
    fn deref_mut(&mut self) -> &mut ConstraintSystem {
        self.cs
    }
}

fn run<H: Host + ?Sized, R>(host: &mut H, body: impl FnOnce(&mut Ctx) -> R) -> R {
    let options = host.options();
    let mut cx = Ctx {
        cs: host.constraint_system(),
        options,
        hints: HintCount::default(),
    };
    let out = body(&mut cx);
    let hints = cx.hints;
    host.record(&hints);
    out
}

// ============================================================================
// Fixed-width integers (branch-free where a witness can reach them)
// ============================================================================

#[inline(always)]
fn adc(a: u64, b: u64, c: u64) -> (u64, u64) {
    let t = a as u128 + b as u128 + c as u128;
    (t as u64, (t >> 64) as u64)
}

#[inline(always)]
fn sbb(a: u64, b: u64, borrow: u64) -> (u64, u64) {
    let t = (a as u128).wrapping_sub(b as u128 + borrow as u128);
    (t as u64, ((t >> 64) as u64) & 1)
}

#[inline(always)]
fn mac(acc: u64, a: u64, b: u64, c: u64) -> (u64, u64) {
    let t = acc as u128 + (a as u128) * (b as u128) + c as u128;
    (t as u64, (t >> 64) as u64)
}

fn big(v: u64) -> Big {
    let mut out = [0u64; NW];
    out[0] = v;
    out
}

fn big4(a: &[u64; 4]) -> Big {
    let mut out = [0u64; NW];
    out[..4].copy_from_slice(a);
    out
}

fn big_add(a: &Big, b: &Big) -> (Big, u64) {
    let mut out = [0u64; NW];
    let mut c = 0;
    for i in 0..NW {
        (out[i], c) = adc(a[i], b[i], c);
    }
    (out, c)
}

fn big_sub(a: &Big, b: &Big) -> (Big, u64) {
    let mut out = [0u64; NW];
    let mut c = 0;
    for i in 0..NW {
        (out[i], c) = sbb(a[i], b[i], c);
    }
    (out, c)
}

/// `a` where `mask` is all ones, `b` where it is zero.
#[inline(always)]
fn big_select(mask: u64, a: &Big, b: &Big) -> Big {
    core::array::from_fn(|i| (a[i] & mask) | (b[i] & !mask))
}

/// All ones if `a == 0`.
#[inline(always)]
fn big_zero_mask(a: &Big) -> u64 {
    let or = a.iter().fold(0, |acc, &w| acc | w);
    ((or | or.wrapping_neg()) >> 63).wrapping_sub(1)
}

/// Little-endian bytes, at most `8 * NW` of them.
fn big_from_bytes(bytes: &[u8]) -> Big {
    assert!(bytes.len() <= 8 * NW);
    let mut out = [0u64; NW];
    for (i, &b) in bytes.iter().enumerate() {
        out[i / 8] |= (b as u64) << (8 * (i % 8));
    }
    out
}

fn big_to_bytes(a: &Big) -> [u8; 8 * NW] {
    let mut out = [0u8; 8 * NW];
    for i in 0..NW {
        out[8 * i..8 * i + 8].copy_from_slice(&a[i].to_le_bytes());
    }
    out
}

fn big_bitlen(a: &Big) -> usize {
    for i in (0..NW).rev() {
        if a[i] != 0 {
            return 64 * i + 64 - a[i].leading_zeros() as usize;
        }
    }
    0
}

fn wide_from(a: &Big) -> Wide {
    let mut out = [0u64; WIDE];
    out[..NW].copy_from_slice(a);
    out
}

fn wide_add(a: &Wide, b: &Wide) -> Wide {
    let mut out = [0u64; WIDE];
    let mut c = 0;
    for i in 0..WIDE {
        (out[i], c) = adc(a[i], b[i], c);
    }
    out
}

fn wide_sub(a: &Wide, b: &Wide) -> Wide {
    let mut out = [0u64; WIDE];
    let mut c = 0;
    for i in 0..WIDE {
        (out[i], c) = sbb(a[i], b[i], c);
    }
    out
}

/// Low `64 * WIDE` bits of the product.
fn wide_mul_lo(a: &Wide, b: &Wide) -> Wide {
    let mut out = [0u64; WIDE];
    for i in 0..WIDE {
        let mut c = 0;
        for j in 0..WIDE - i {
            (out[i + j], c) = mac(out[i + j], a[i], b[j], c);
        }
    }
    out
}

/// `w += v << (8 * byte_pos)` for `v < 2^64`.
fn wide_add_shifted(w: &mut Wide, v: u128, byte_pos: usize) {
    debug_assert!(v < 1 << 64);
    let word = byte_pos / 8;
    let x = v << (8 * (byte_pos % 8));
    let parts = [x as u64, (x >> 64) as u64];
    let mut c = 0;
    for i in word..WIDE {
        let add = if i - word < 2 { parts[i - word] } else { 0 };
        (w[i], c) = adc(w[i], add, c);
    }
}

fn wide_bitlen(a: &Wide) -> usize {
    for i in (0..WIDE).rev() {
        if a[i] != 0 {
            return 64 * i + 64 - a[i].leading_zeros() as usize;
        }
    }
    0
}

/// Quotient and remainder by a 256-bit divisor. Public operands only.
fn wide_divrem(n: &Wide, d: &Big) -> (Wide, Big) {
    let mut q = [0u64; WIDE];
    let mut r = [0u64; NW + 1];
    for bit in (0..64 * WIDE).rev() {
        for i in (1..=NW).rev() {
            r[i] = (r[i] << 1) | (r[i - 1] >> 63);
        }
        r[0] = (r[0] << 1) | ((n[bit / 64] >> (bit % 64)) & 1);
        let mut t = [0u64; NW + 1];
        let mut borrow = 0;
        for i in 0..=NW {
            let di = if i < NW { d[i] } else { 0 };
            (t[i], borrow) = sbb(r[i], di, borrow);
        }
        if borrow == 0 {
            r = t;
            q[bit / 64] |= 1 << (bit % 64);
        }
    }
    (q, core::array::from_fn(|i| r[i]))
}

fn wide_to_bytes(a: &Wide) -> [u8; 8 * WIDE] {
    let mut out = [0u8; 8 * WIDE];
    for i in 0..WIDE {
        out[8 * i..8 * i + 8].copy_from_slice(&a[i].to_le_bytes());
    }
    out
}

/// Field element of a small signed public integer.
fn f_int(v: i128) -> F {
    let m = F::from_u128_reduced(v.unsigned_abs());
    if v < 0 { -m } else { m }
}

// ============================================================================
// Modulus: native arithmetic and reduction data
// ============================================================================

/// An odd modulus below `2^256` with its native (Montgomery) arithmetic and the data the
/// reduction gadget needs.
#[derive(Clone)]
pub struct Modulus {
    p: Big,
    bits: usize,
    n0: u64,
    r2: Big,
    one: Big,
    m256: Big,
    /// `p^-1 mod 2^(64 * WIDE)`.
    pinv: Wide,
    /// `p = sum coeff * 2^(8 * position)`, with few terms for the pseudo-Mersenne moduli.
    sparse: Vec<(usize, i64)>,
    /// Limbs of a reduced element.
    limbs: usize,
    /// 64-bit words of the Montgomery radix.
    words: usize,
    /// `fold[k - limbs]`: signed digits `(position, digit)` of `2^(8k) mod p` for the limb
    /// positions `k >= limbs` that a product can reach.
    fold: Vec<Vec<(usize, i64)>>,
}

impl Modulus {
    fn build(p: Big, sparse: Vec<(usize, i64)>) -> Self {
        assert!(p[0] & 1 == 1 && big_bitlen(&p) > 128, "unsupported modulus");
        let mut inv = 1u64;
        for _ in 0..6 {
            inv = inv.wrapping_mul(2u64.wrapping_sub(p[0].wrapping_mul(inv)));
        }
        let mut m = Self {
            p,
            bits: big_bitlen(&p),
            n0: inv.wrapping_neg(),
            r2: [0; NW],
            one: [0; NW],
            m256: [0; NW],
            pinv: [0; WIDE],
            sparse,
            limbs: big_bitlen(&p).div_ceil(8),
            words: big_bitlen(&p).div_ceil(64),
            fold: Vec::new(),
        };
        let mut r = big(1);
        for _ in 0..64 * m.words {
            r = m.madd(&r, &r);
        }
        m.one = r;
        for _ in 0..64 * m.words {
            r = m.madd(&r, &r);
        }
        m.r2 = r;
        m.m256 = m.mont(&big(256));

        let pw = wide_from(&p);
        let mut x = [0u64; WIDE];
        x[0] = inv;
        let mut two = [0u64; WIDE];
        two[0] = 2;
        for _ in 0..4 {
            x = wide_mul_lo(&x, &wide_sub(&two, &wide_mul_lo(&pw, &x)));
        }
        let mut unit = [0u64; WIDE];
        unit[0] = 1;
        assert_eq!(wide_mul_lo(&pw, &x), unit);
        m.pinv = x;

        let (mut pos, mut neg) = ([0u64; WIDE], [0u64; WIDE]);
        for &(k, c) in &m.sparse {
            let target = if c >= 0 { &mut pos } else { &mut neg };
            wide_add_shifted(target, c.unsigned_abs() as u128, k);
        }
        assert_eq!(
            wide_sub(&pos, &neg),
            pw,
            "sparse form does not evaluate to p"
        );

        // Digits of 2^(8k) mod p, centred to [-128, 127] below the top limb.
        let mut v = big(1);
        for _ in 0..8 * m.limbs {
            v = m.madd(&v, &v);
        }
        for _ in 0..m.limbs + 8 {
            let bytes = big_to_bytes(&v);
            let mut digits = Vec::new();
            let mut carry = 0i64;
            for (i, &b) in bytes.iter().enumerate().take(m.limbs) {
                let mut d = b as i64 + carry;
                carry = 0;
                if d >= 128 && i + 1 < m.limbs {
                    d -= 256;
                    carry = 1;
                }
                if d != 0 {
                    digits.push((i, d));
                }
            }
            m.fold.push(digits);
            for _ in 0..8 {
                v = m.madd(&v, &v);
            }
        }
        m
    }

    /// Any odd modulus of more than 128 bits, given little-endian.
    pub fn new(p_le: &[u8]) -> Self {
        let sparse = p_le
            .iter()
            .enumerate()
            .filter(|&(_, &b)| b != 0)
            .map(|(k, &b)| (k, b as i64))
            .collect();
        Self::build(big_from_bytes(p_le), sparse)
    }

    /// `2^256 - 2^32 - 977`.
    pub fn secp256k1_base() -> Self {
        Self::build(
            big4(&crate::secp256k1_ct::SECP_P),
            vec![(32, 1), (4, -1), (1, -3), (0, -209)],
        )
    }

    /// The secp256k1 group order.
    pub fn secp256k1_order() -> Self {
        Self::new(&big_to_bytes(&big4(&crate::secp256k1_ct::SECP_N)))
    }

    /// `2^255 - 19`.
    pub fn curve25519_base() -> Self {
        Self::build(big4(&ED_P), vec![(31, 128), (0, -19)])
    }

    /// The order of the Ed25519 base point.
    pub fn ed25519_order() -> Self {
        Self::new(&big_to_bytes(&big4(&ED_L)))
    }

    /// Bit length of the modulus; every [`Element`] has this many bits.
    pub fn bits(&self) -> usize {
        self.bits
    }

    /// Montgomery product for the radix `2^(64 words)`.
    fn mmul(&self, a: &Big, b: &Big) -> Big {
        let (p, n) = (&self.p, self.words);
        let mut t = [0u64; NW + 2];
        for &ai in &a[..n] {
            let mut c = 0;
            for j in 0..n {
                (t[j], c) = mac(t[j], ai, b[j], c);
            }
            let (s, c2) = adc(t[n], c, 0);
            t[n] = s;
            t[n + 1] = c2;
            let m = t[0].wrapping_mul(self.n0);
            let (_, mut c) = mac(t[0], m, p[0], 0);
            for j in 1..n {
                (t[j - 1], c) = mac(t[j], m, p[j], c);
            }
            let (s, c2) = adc(t[n], c, 0);
            t[n - 1] = s;
            t[n] = t[n + 1] + c2;
        }
        let mut r = [0u64; NW];
        r[..n].copy_from_slice(&t[..n]);
        let (d, borrow) = big_sub(&r, p);
        // `r < 2p`; with the overflow word set, `r - p` wraps to the right value.
        let take = (t[n] | (1 - borrow)).wrapping_neg();
        let mut out = big_select(take, &d, &r);
        for w in out.iter_mut().skip(n) {
            *w = 0;
        }
        out
    }

    fn madd(&self, a: &Big, b: &Big) -> Big {
        let (s, c) = big_add(a, b);
        let (d, borrow) = big_sub(&s, &self.p);
        big_select((c | (1 - borrow)).wrapping_neg(), &d, &s)
    }

    fn msub(&self, a: &Big, b: &Big) -> Big {
        let (d, borrow) = big_sub(a, b);
        let (e, _) = big_add(&d, &self.p);
        big_select(borrow.wrapping_neg(), &e, &d)
    }

    fn mont(&self, a: &Big) -> Big {
        self.mmul(a, &self.r2)
    }

    fn canon(&self, a: &Big) -> Big {
        self.mmul(a, &big(1))
    }

    /// `a^(p-2)`: the inverse, or zero for zero. The exponent is public.
    fn inv(&self, a: &Big) -> Big {
        let (e, _) = big_sub(&self.p, &big(2));
        let mut acc = self.one;
        for i in (0..64 * NW).rev() {
            acc = self.mmul(&acc, &acc);
            if (e[i / 64] >> (i % 64)) & 1 == 1 {
                acc = self.mmul(&acc, a);
            }
        }
        acc
    }

    /// An integer congruent to `d` with at most `limbs` coefficients: every coefficient at
    /// a position `k >= limbs` is replaced by itself times the digits of `2^(8k) mod p`.
    /// No rows; the intervals follow by interval arithmetic.
    fn fold(&self, d: &Poly) -> Poly {
        let mut out = Poly(d.0[..self.limbs.min(d.0.len())].to_vec());
        out.0.resize(self.limbs, Coef::zero());
        for (k, c) in d.0.iter().enumerate().skip(self.limbs) {
            let digits = self
                .fold
                .get(k - self.limbs)
                .expect("operand too long to fold");
            for &(j, digit) in digits {
                let slot = &mut out.0[j];
                let digit = digit as i128;
                slot.lc = slot.lc.plus(&c.lc.scaled(f_int(digit)));
                slot.lo += (c.lo * digit).min(c.hi * digit);
                slot.hi += (c.lo * digit).max(c.hi * digit);
            }
        }
        out
    }

    fn small(&self, v: u64) -> Big {
        self.mont(&big(v))
    }

    /// Residue (Montgomery form) of the integer a polynomial holds under the current
    /// assignment.
    fn poly_value(&self, cs: &ConstraintSystem, poly: &Poly) -> Big {
        let mut acc = [0u64; NW];
        for c in poly.0.iter().rev() {
            let v = coef_value(cs, c);
            let sign = v >> 127;
            let mag = ((v ^ sign) - sign) as u64;
            let m = self.mont(&big(mag));
            let term = big_select(sign as u64, &self.msub(&[0; NW], &m), &m);
            acc = self.madd(&self.mmul(&acc, &self.m256), &term);
        }
        acc
    }
}

const ED_P: [u64; 4] = [
    0xffff_ffff_ffff_ffed,
    0xffff_ffff_ffff_ffff,
    0xffff_ffff_ffff_ffff,
    0x7fff_ffff_ffff_ffff,
];
const ED_L: [u64; 4] = [
    0x5812_631a_5cf5_d3ed,
    0x14de_f9de_a2f7_9cd6,
    0,
    0x1000_0000_0000_0000,
];
/// `v` of the Montgomery base point `(9, v)` that maps to the RFC 8032 base point.
const ED_BASE_V: [u64; 4] = [
    0xd616_3a5d_8131_2c14,
    0x6dc2_b281_9283_9e4d,
    0x1fe1_22d3_88b7_2eb3,
    0x5f51_e65e_475f_794b,
];
/// The square root of `-486664` with `x = c u / v` on the Edwards curve.
const ED_SQRT_M486664: [u64; 4] = [
    0xcc6e_04aa_ff45_7e06,
    0xc5a1_d3d1_4b7d_1a82,
    0xd27b_08dc_03fc_4f7e,
    0x0f26_edf4_60a0_06bb,
];
const ED_MONT_A: u64 = 486662;

// ============================================================================
// Bounded polynomials
// ============================================================================

/// A linear form with a proven integer interval for its value.
#[derive(Clone)]
struct Coef {
    lc: Lc,
    lo: i128,
    hi: i128,
}

impl Coef {
    fn constant(v: i128) -> Self {
        Self {
            lc: Lc::constant(f_int(v)),
            lo: v,
            hi: v,
        }
    }

    fn zero() -> Self {
        Self {
            lc: Lc::zero(),
            lo: 0,
            hi: 0,
        }
    }
}

/// The integer of a coefficient under the current assignment: the representative of its
/// field value that lies in the coefficient's interval.
fn coef_value(cs: &ConstraintSystem, c: &Coef) -> i128 {
    let x = cs.eval(&c.lc).to_canonical_u64() as i128;
    let wrap = (c.hi - x) >> 127;
    x - (wrap & PG)
}

/// The integer `sum coef_k 2^(8k)`.
#[derive(Clone, Default)]
struct Poly(Vec<Coef>);

impl Poly {
    fn constant_bytes(bytes: &[u8]) -> Self {
        Self(bytes.iter().map(|&b| Coef::constant(b as i128)).collect())
    }

    fn zip(&self, rhs: &Poly, sign: i128) -> Poly {
        let n = self.0.len().max(rhs.0.len());
        let mut out = Vec::with_capacity(n);
        for k in 0..n {
            let a = self.0.get(k).cloned().unwrap_or_else(Coef::zero);
            out.push(match rhs.0.get(k) {
                None => a,
                Some(b) if sign > 0 => Coef {
                    lc: a.lc.plus(&b.lc),
                    lo: a.lo + b.lo,
                    hi: a.hi + b.hi,
                },
                Some(b) => Coef {
                    lc: a.lc.minus(&b.lc),
                    lo: a.lo - b.hi,
                    hi: a.hi - b.lo,
                },
            });
        }
        Poly(out)
    }

    fn add(&self, rhs: &Poly) -> Poly {
        self.zip(rhs, 1)
    }

    fn sub(&self, rhs: &Poly) -> Poly {
        self.zip(rhs, -1)
    }

    fn scale(&self, k: i64) -> Poly {
        let kf = f_int(k as i128);
        let k = k as i128;
        Poly(
            self.0
                .iter()
                .map(|c| Coef {
                    lc: c.lc.scaled(kf),
                    lo: (c.lo * k).min(c.hi * k),
                    hi: (c.lo * k).max(c.hi * k),
                })
                .collect(),
        )
    }

    /// Product with a public non-negative integer given in bytes: no rows.
    fn mul_const(&self, bytes: &[u8]) -> Poly {
        let n = self.0.len() + bytes.len() - 1;
        let mut out = Vec::with_capacity(n);
        for k in 0..n {
            let mut parts: Vec<(F, &Lc)> = Vec::new();
            let (mut lo, mut hi) = (0i128, 0i128);
            for (j, &b) in bytes.iter().enumerate() {
                if b == 0 || j > k || k - j >= self.0.len() {
                    continue;
                }
                let c = &self.0[k - j];
                parts.push((F::from_u64_reduced(b as u64), &c.lc));
                lo += c.lo * b as i128;
                hi += c.hi * b as i128;
            }
            out.push(Coef {
                lc: Lc::combine(&parts),
                lo,
                hi,
            });
        }
        Poly(out)
    }

    /// Whether every coefficient fits a (possibly negated) limb, so the value can be a
    /// factor of a product as it is.
    fn is_narrow(&self) -> bool {
        self.0.iter().all(|c| c.lo >= -255 && c.hi <= 255)
    }
}

/// `a(t) b(t)` with one fresh variable and one row per coefficient.
///
/// The rows state `a(s) b(s) = c(s)` at `deg + 1` points `s` (zero, infinity and small
/// integers of both signs), so `c = a b` as polynomials over the field. Each coefficient
/// interval is the interval sum of the term products and is asserted to stay below
/// [`COEF_BOUND`], which is where the field value pins the integer.
fn mul_poly(cs: &mut Ctx, a: &Poly, b: &Poly) -> Poly {
    let (la, lb) = (a.0.len(), b.0.len());
    assert!(la > 0 && lb > 0);
    let n = la + lb - 1;
    for c in a.0.iter().chain(&b.0) {
        assert!(c.lo > -(1 << 40) && c.hi < (1 << 40), "factor too wide");
    }
    let mut av: Vec<F> = a.0.iter().map(|c| cs.eval(&c.lc)).collect();
    let mut bv: Vec<F> = b.0.iter().map(|c| cs.eval(&c.lc)).collect();
    let mut out = Vec::with_capacity(n);
    let source = cs.source(|| Source::PolyProduct {
        a: a.0.iter().map(|c| c.lc.clone()).collect(),
        b: b.0.iter().map(|c| c.lc.clone()).collect(),
    });
    for k in 0..n {
        let mut v = F::ZERO;
        let (mut lo, mut hi) = (0i128, 0i128);
        for i in k.saturating_sub(lb - 1)..=k.min(la - 1) {
            let (x, y) = (&a.0[i], &b.0[k - i]);
            v += av[i].const_mul(bv[k - i]);
            let c = [x.lo * y.lo, x.lo * y.hi, x.hi * y.lo, x.hi * y.hi];
            lo += c.iter().copied().min().unwrap();
            hi += c.iter().copied().max().unwrap();
        }
        assert!(lo > -COEF_BOUND && hi < COEF_BOUND, "product too wide");
        out.push(Coef {
            lc: cs
                .alloc_defined(v, || Def::Coefficient {
                    product: source,
                    index: k as u32,
                })
                .into(),
            lo,
            hi,
        });
    }
    qsag_core::wipe::wipe_goldilocks(&mut av);
    qsag_core::wipe::wipe_goldilocks(&mut bv);

    cs.enforce_mul(a.0[0].lc.clone(), b.0[0].lc.clone(), out[0].lc.clone());
    if n >= 2 {
        cs.enforce_mul(
            a.0[la - 1].lc.clone(),
            b.0[lb - 1].lc.clone(),
            out[n - 1].lc.clone(),
        );
    }
    for e in 0..n.saturating_sub(2) {
        let s = f_int(if e % 2 == 0 {
            (e / 2 + 1) as i128
        } else {
            -((e / 2 + 1) as i128)
        });
        let mut pows = Vec::with_capacity(n);
        let mut acc = F::ONE;
        for _ in 0..n {
            pows.push(acc);
            acc = acc.const_mul(s);
        }
        let at = |p: &[Coef]| {
            let parts: Vec<(F, &Lc)> = pows.iter().copied().zip(p.iter().map(|c| &c.lc)).collect();
            Lc::combine(&parts)
        };
        cs.enforce_mul(at(&a.0), at(&b.0), at(&out));
    }
    Poly(out)
}

// ============================================================================
// Bit-decomposed witnesses
// ============================================================================

/// A witness in `[0, 2^bits)`: 8-bit limbs and their bits, one row per bit.
///
/// It is a residue representative, not necessarily the canonical one; see
/// [`Modulus::enforce_canonical`].
#[derive(Clone)]
pub struct Element {
    /// Little-endian limbs; limb `i` holds bits `8i..8i+8`.
    pub bytes_le: Vec<Lc>,
    /// Little-endian bits.
    pub bits_le: Vec<Lc>,
}

impl Element {
    fn poly(&self) -> Poly {
        let nbits = self.bits_le.len();
        Poly(
            self.bytes_le
                .iter()
                .enumerate()
                .map(|(i, lc)| Coef {
                    lc: lc.clone(),
                    lo: 0,
                    hi: (1i128 << (nbits - 8 * i).min(8)) - 1,
                })
                .collect(),
        )
    }

    /// The value as an unreduced operand.
    pub fn lazy(&self) -> Lazy {
        Lazy(self.poly())
    }
}

/// The coefficients of `p` for a recorded definition.
fn int_coefs(p: &Poly) -> Vec<IntCoef> {
    p.0.iter()
        .map(|c| IntCoef {
            lc: c.lc.clone(),
            lo: c.lo,
            hi: c.hi,
        })
        .collect()
}

/// The source of the canonical residue of `(sum of products + linear) / den` modulo `m`.
fn residue_source(
    cs: &mut Ctx,
    m: &Modulus,
    products: &[(&Poly, &Poly)],
    linear: &Poly,
    den: Option<&Poly>,
) -> SourceId {
    cs.source(|| Source::Residue {
        products: products
            .iter()
            .map(|(a, b)| (int_coefs(a), int_coefs(b)))
            .collect(),
        linear: int_coefs(linear),
        den: den.map(int_coefs).unwrap_or_default(),
        modulus: big_to_bytes(&m.p)[..m.limbs].to_vec(),
    })
}

/// Allocate `value mod 2^nbits`. Each limb is one variable; its low bits are variables and
/// its top bit is the linear form that completes it, so a limb costs as many rows as bits.
fn alloc_int(cs: &mut Ctx, source: SourceId, value_le: &[u8], nbits: usize) -> Element {
    cs.hints.elements += 1;
    cs.hints.element_bits += nbits;
    cs.hints.range_lookups += range_lookups(nbits);
    alloc_bits(cs, source, value_le, nbits)
}

fn alloc_bits(cs: &mut Ctx, source: SourceId, value_le: &[u8], nbits: usize) -> Element {
    let part = |lo: usize, width: usize| Def::Bits {
        source,
        lo: lo as u32,
        width: width as u32,
    };
    let mut bytes_le = Vec::with_capacity(nbits.div_ceil(8));
    let mut bits_le = Vec::with_capacity(nbits);
    for i in 0..nbits.div_ceil(8) {
        let width = (nbits - 8 * i).min(8);
        let byte = value_le.get(i).copied().unwrap_or(0) & (0xffu16 >> (8 - width)) as u8;
        if width == 1 {
            let bit: Lc = cs
                .alloc_defined(F::from_u64_reduced(byte as u64), || part(8 * i, 1))
                .into();
            cs.enforce_boolean(&bit);
            bits_le.push(bit.clone());
            bytes_le.push(bit);
            continue;
        }
        let limb: Lc = cs
            .alloc_defined(F::from_u64_reduced(byte as u64), || part(8 * i, width))
            .into();
        let mut top = limb.clone();
        for k in 0..width - 1 {
            let bit = cs.alloc_defined(F::from_u64_reduced(((byte >> k) & 1) as u64), || {
                part(8 * i + k, 1)
            });
            cs.enforce_boolean(&bit.into());
            top = top.minus(&Lc::term(bit, F::from_u64_reduced(1 << k)));
            bits_le.push(bit.into());
        }
        let top = top.scaled(F::from_u64_reduced(1 << (width - 1)).inv());
        cs.enforce_boolean(&top);
        bits_le.push(top);
        bytes_le.push(limb);
    }
    Element { bytes_le, bits_le }
}

/// An unreduced integer operand: sums, differences and constants are free.
#[derive(Clone)]
pub struct Lazy(Poly);

impl Lazy {
    /// A public constant, little-endian.
    pub fn constant(value_le: &[u8]) -> Self {
        Self(Poly::constant_bytes(value_le))
    }

    /// Bits the caller has constrained Boolean, little-endian.
    pub fn from_bits(bits_le: &[Lc]) -> Self {
        Self(Poly(
            bits_le
                .chunks(8)
                .map(|chunk| {
                    let parts: Vec<(F, &Lc)> = chunk
                        .iter()
                        .enumerate()
                        .map(|(k, b)| (F::from_u64_reduced(1 << k), b))
                        .collect();
                    Coef {
                        lc: Lc::combine(&parts),
                        lo: 0,
                        hi: (1 << chunk.len()) - 1,
                    }
                })
                .collect(),
        ))
    }

    pub fn add(&self, rhs: &Lazy) -> Lazy {
        Lazy(self.0.add(&rhs.0))
    }

    pub fn sub(&self, rhs: &Lazy) -> Lazy {
        Lazy(self.0.sub(&rhs.0))
    }

    /// Multiply by a small public integer.
    pub fn scale(&self, k: i32) -> Lazy {
        Lazy(self.0.scale(k as i64))
    }
}

fn reduce_poly(cs: &mut Ctx, m: &Modulus, a: &Poly) -> Element {
    let value = big_to_bytes(&m.canon(&m.poly_value(cs, a)));
    let source = residue_source(cs, m, &[], a, None);
    let out = alloc_int(cs, source, &value, m.bits);
    enforce_zero_mod(cs, m, &out.poly().sub(a));
    out
}

impl Modulus {
    /// A fresh witness of [`Self::bits`] bits holding `value_le mod 2^bits`.
    pub fn alloc(&self, cs: &mut impl Host, value_le: &[u8]) -> Element {
        run(cs, |cs| {
            let source = cs.source(|| Source::Input {
                bits: self.bits as u32,
            });
            alloc_int(cs, source, value_le, self.bits)
        })
    }

    /// The canonical residue of `a` under the current assignment, little-endian, one byte
    /// per limb of the modulus.
    pub fn value(&self, cs: &ConstraintSystem, a: &Lazy) -> Vec<u8> {
        big_to_bytes(&self.canon(&self.poly_value(cs, &a.0)))[..self.limbs].to_vec()
    }

    /// A fresh element congruent to `a`.
    pub fn reduce(&self, cs: &mut impl Host, a: &Lazy) -> Element {
        run(cs, |cs| reduce_poly(cs, self, &a.0))
    }

    /// A fresh element congruent to `a b`.
    pub fn mul(&self, cs: &mut impl Host, a: &Lazy, b: &Lazy) -> Element {
        run(cs, |cs| {
            let product = mul_poly(cs, &a.0, &b.0);
            reduce_poly(cs, self, &product)
        })
    }

    /// `a = 0 (mod p)`.
    pub fn enforce_zero(&self, cs: &mut impl Host, a: &Lazy) {
        run(cs, |cs| {
            enforce_zero_mod(cs, self, &a.0);
        })
    }

    /// `a = b (mod p)`.
    pub fn enforce_equal(&self, cs: &mut impl Host, a: &Lazy, b: &Lazy) {
        run(cs, |cs| {
            enforce_zero_mod(cs, self, &a.0.sub(&b.0));
        })
    }

    /// `a <= p - 1`, which makes `a` the unique representative of its residue.
    pub fn enforce_canonical(&self, cs: &mut impl Host, a: &Element) {
        run(cs, |cs| canonical(cs, self, a))
    }
}

fn canonical(cs: &mut Ctx, m: &Modulus, a: &Element) {
    let (pm1, _) = big_sub(&m.p, &big(1));
    enforce_le_const(cs, &a.bits_le, &big_to_bytes(&pm1));
}

/// The integer `a` as a fresh witness of `bits` bits: an exact equality, with no modulus.
/// Unsatisfiable when `a` is negative or does not fit. Use it for the integer sums of
/// BIP32-Ed25519 (`k_L + 8 Z_L`, and `k_R + Z_R` whose low 256 of 257 bits are the sum
/// modulo `2^256`).
pub fn integer_bits(cs: &mut impl Host, a: &Lazy, bits: usize) -> Element {
    run(cs, |cs| {
        assert!(a.0.0.len() <= 8 * WIDE - 8 && bits <= 64 * (WIDE - 1));
        let value = wide_to_bytes(&signed_value(cs, &a.0));
        let source = cs.source(|| Source::Integer {
            products: Vec::new(),
            linear: int_coefs(&a.0),
            bits: bits as u32,
        });
        let out = alloc_int(cs, source, &value, bits);
        let diff = a.0.sub(&out.poly());
        for c in &diff.0 {
            assert!(c.lo > -COEF_BOUND && c.hi < COEF_BOUND);
        }
        enforce_integer_zero(cs, &diff.0);
        out
    })
}

/// The integer of a polynomial under the current assignment, modulo `2^(64 WIDE)`.
fn signed_value(cs: &ConstraintSystem, d: &Poly) -> Wide {
    let (mut vpos, mut vneg) = ([0u64; WIDE], [0u64; WIDE]);
    for (k, c) in d.0.iter().enumerate() {
        let v = coef_value(cs, c);
        let sign = v >> 127;
        let mag = ((v ^ sign) - sign) as u128;
        wide_add_shifted(&mut vpos, mag & !(sign as u128) & (u64::MAX as u128), k);
        wide_add_shifted(&mut vneg, mag & (sign as u128) & (u64::MAX as u128), k);
    }
    wide_sub(&vpos, &vneg)
}

// ============================================================================
// Reduction
// ============================================================================

/// Enforce that the integer `d` is a multiple of the modulus. Returns the quotient witness
/// (shifted by the public offset that makes it non-negative).
///
/// With `[lo_k, hi_k]` the coefficient intervals, `K = ceil(sum max(-lo_k, 0) 2^(8k) / p)`
/// and the quotient is range-checked to the bit length of `K + floor(sum hi_k 2^(8k) / p)`.
/// The identity `d + K p - q p = 0` is then split into groups of consecutive coefficients.
/// Group `g` with value `V_g` and incoming carry `c_(g-1)` defines the outgoing carry as the
/// linear form `(V_g + c_(g-1)) / 2^(8 len)`, which is range-checked by bits to an interval
/// that contains every integer the quotient `(V_g + c_(g-1)) / 2^(8 len)` can take. The
/// group length is the largest for which
/// `|V_g + c_(g-1) - 2^(8 len) c_g| < 2^64 - 2^32 + 1` over the admitted intervals, so the
/// range check on the form implies the integer equation. The last group must be zero.
fn enforce_zero_mod(cs: &mut Ctx, m: &Modulus, d: &Poly) -> Element {
    let folded;
    let d = if d.0.len() > m.limbs {
        folded = m.fold(d);
        &folded
    } else {
        d
    };
    assert!(d.0.len() <= 8 * WIDE - 6, "operand too long");
    let (mut pos, mut neg) = ([0u64; WIDE], [0u64; WIDE]);
    for (k, c) in d.0.iter().enumerate() {
        assert!(c.lo <= c.hi && c.lo > -COEF_BOUND && c.hi < COEF_BOUND);
        if c.hi > 0 {
            wide_add_shifted(&mut pos, c.hi as u128, k);
        }
        if c.lo < 0 {
            wide_add_shifted(&mut neg, (-c.lo) as u128, k);
        }
    }
    let pw = wide_from(&m.p);
    let mut pm1 = pw;
    pm1[0] -= 1;
    let (offset, _) = wide_divrem(&wide_add(&neg, &pm1), &m.p);
    let (qpos, _) = wide_divrem(&pos, &m.p);
    let qbits = wide_bitlen(&wide_add(&offset, &qpos)).max(1);
    let offset_p = wide_mul_lo(&offset, &pw);
    assert!(qbits + 264 <= 64 * WIDE, "quotient too wide");

    // Witness: q = (d + K p) / p by multiplication with p^-1 mod 2^576 (exact when d is a
    // multiple of p; any other assignment is rejected by the rows below).
    let numer = wide_add(&signed_value(cs, d), &offset_p);
    let q_bytes = wide_to_bytes(&wide_mul_lo(&numer, &m.pinv));
    cs.hints.quotients += 1;
    cs.hints.quotient_bits += qbits;
    let source = cs.source(|| {
        let offset_bytes = wide_to_bytes(&offset_p);
        let mut num = int_coefs(d);
        num.resize(
            num.len().max(wide_bitlen(&offset_p).div_ceil(8)),
            int_coefs(&Poly(vec![Coef::zero()])).remove(0),
        );
        for (k, c) in num.iter_mut().enumerate() {
            let b = offset_bytes[k] as i128;
            c.lc = c.lc.plus_const(f_int(b));
            c.lo += b;
            c.hi += b;
        }
        Source::Quotient {
            num,
            divisor: big_to_bytes(&m.p)[..m.limbs].to_vec(),
            bits: qbits as u32,
        }
    });
    cs.hints.range_lookups += range_lookups(qbits);
    let q = alloc_bits(cs, source, &q_bytes, qbits);
    let qp = q.poly();

    // e = d + K p - q p, coefficient by coefficient.
    let offset_bytes = wide_to_bytes(&offset_p);
    let offset_len = wide_bitlen(&offset_p).div_ceil(8);
    let top = m.sparse.iter().map(|&(k, _)| k).max().unwrap();
    let len = d.0.len().max(offset_len).max(qp.0.len() + top);
    let mut e: Vec<Coef> = (0..len)
        .map(|k| d.0.get(k).cloned().unwrap_or_else(Coef::zero))
        .collect();
    for (k, slot) in e.iter_mut().enumerate().take(offset_len) {
        let b = offset_bytes[k] as i128;
        slot.lc = slot.lc.plus_const(f_int(b));
        slot.lo += b;
        slot.hi += b;
    }
    for (i, qc) in qp.0.iter().enumerate() {
        for &(k, c) in &m.sparse {
            let c = -(c as i128);
            let slot = &mut e[i + k];
            slot.lc = slot.lc.plus(&qc.lc.scaled(f_int(c)));
            slot.lo += (qc.lo * c).min(qc.hi * c);
            slot.hi += (qc.lo * c).max(qc.hi * c);
        }
    }

    enforce_integer_zero(cs, &e);
    q
}

/// The integer `sum e_k 2^(8k)` is zero: the carry chain described on
/// [`enforce_zero_mod`]. Every coefficient interval must lie within [`COEF_BOUND`].
fn enforce_integer_zero(cs: &mut Ctx, e: &[Coef]) {
    let len = e.len();
    let mut at = 0;
    let mut carry = Coef::zero();
    let mut carry_value = 0i128;
    while at < len {
        // (group length, carry interval and bit count); `None` for the closing group.
        let mut choice: Option<(usize, Option<(i128, u32)>)> = None;
        for g in (1..=(len - at).min(8)).rev() {
            let (mut lo, mut hi) = (carry.lo, carry.hi);
            for i in 0..g {
                lo += e[at + i].lo << (8 * i);
                hi += e[at + i].hi << (8 * i);
            }
            if at + g == len {
                if lo > -PG && hi < PG {
                    choice = Some((g, None));
                    break;
                }
                continue;
            }
            let weight = 1i128 << (8 * g);
            let clo = lo.div_euclid(weight) + (lo.rem_euclid(weight) != 0) as i128;
            // An empty interval means no assignment can satisfy the identity; the carry is
            // then pinned to one value and its row cannot hold.
            let chi = hi.div_euclid(weight).max(clo);
            let nbits = 128 - ((chi - clo) as u128).leading_zeros();
            let admitted_hi = clo + (1i128 << nbits) - 1;
            if lo - weight * admitted_hi > -PG && hi - weight * clo < PG {
                choice = Some((g, Some((clo, nbits))));
                break;
            }
        }
        let (g, out) = choice.expect("no carry group fits the field");

        let mut parts: Vec<(F, &Lc)> = vec![(F::ONE, &carry.lc)];
        let mut value = carry_value;
        for i in 0..g {
            parts.push((F::TWO.pow(8 * i as u64), &e[at + i].lc));
            value = value.wrapping_add(coef_value(cs, &e[at + i]).wrapping_shl(8 * i as u32));
        }
        let group = Lc::combine(&parts);
        at += g;
        let Some((clo, nbits)) = out else {
            cs.enforce_zero(group);
            break;
        };
        let next = group.scaled(F::TWO.pow(8 * g as u64).inv());
        carry_value = value >> (8 * g);
        if nbits == 0 {
            cs.enforce_zero(next.plus_const(f_int(-clo)));
        } else {
            let shifted = (carry_value.wrapping_sub(clo)) as u128;
            let mut top = next.plus_const(f_int(-clo));
            cs.hints.carries += 1;
            cs.hints.carry_bits += nbits as usize;
            let source = cs.source(|| Source::Form {
                lc: top.clone(),
                bits: nbits,
            });
            cs.hints.range_lookups += range_lookups(nbits as usize);
            for k in 0..nbits - 1 {
                let bit =
                    cs.alloc_defined(F::from_u64_reduced(((shifted >> k) & 1) as u64), || {
                        Def::Bits {
                            source,
                            lo: k,
                            width: 1,
                        }
                    });
                cs.enforce_boolean(&bit.into());
                top = top.minus(&Lc::term(bit, F::from_u64_reduced(1 << k)));
            }
            cs.enforce_boolean(&top.scaled(F::from_u64_reduced(1 << (nbits - 1)).inv()));
        }
        carry = Coef {
            lc: next,
            lo: clo,
            hi: clo + (1i128 << nbits) - 1,
        };
    }
}

// ============================================================================
// Comparisons with public constants
// ============================================================================

/// `1` iff every bit is one, as a linear form: two rows (none for one bit, one for two),
/// or a product chain under [`Options::product_only_comparisons`].
fn all_ones(cs: &mut Ctx, bits: &[Lc]) -> Lc {
    match bits {
        [one] => one.clone(),
        [a, b] => cs.mul(a, b).into(),
        // Three bits cost two rows either way; the chain leaves no free inverse.
        _ if bits.len() == 3 || cs.options.product_only_comparisons => {
            let mut acc = bits[0].clone();
            for b in &bits[1..] {
                acc = cs.mul(&acc, b).into();
            }
            acc
        }
        _ => {
            let parts: Vec<(F, &Lc)> = bits.iter().map(|b| (F::NEG_ONE, b)).collect();
            let missing = Lc::combine(&parts).plus_const(F::from_u64_reduced(bits.len() as u64));
            cs.hints.zero_tests += 1;
            let inverse = cs.eval(&missing).inv_or_zero();
            let inv = cs.alloc_defined(inverse, || Def::InverseOrZero {
                of: missing.clone(),
                max: bits.len() as u32,
            });
            let nonzero = cs.mul(&missing, &inv.into());
            let flag = Lc::constant(F::ONE).minus(&nonzero.into());
            cs.enforce_mul(missing, flag.clone(), Lc::zero());
            flag
        }
    }
}

/// `sum bits_i 2^i <= bound` for Boolean `bits` and a public `bound` (little-endian bytes).
///
/// Scanning from the top, `run` is one while every bit seen under a one of `bound` was one.
/// Under a zero of `bound` the bit must then be zero. A block of ones of `bound` costs at
/// most three rows and a block of zeros one row.
fn enforce_le_const(cs: &mut Ctx, bits_le: &[Lc], bound_le: &[u8]) {
    let n = bits_le.len();
    let bound_bit = |i: usize| (bound_le.get(i / 8).copied().unwrap_or(0) >> (i % 8)) & 1 == 1;
    assert!((n..8 * bound_le.len()).all(|i| !bound_bit(i)));
    let Some(lowest_zero) = (0..n).find(|&i| !bound_bit(i)) else {
        return;
    };
    let mut run: Option<Lc> = None;
    let mut hi = n;
    while hi > lowest_zero {
        let ones = bound_bit(hi - 1);
        let mut lo = hi - 1;
        while lo > lowest_zero && bound_bit(lo - 1) == ones {
            lo -= 1;
        }
        let block = &bits_le[lo..hi];
        if ones {
            let all = all_ones(cs, block);
            run = Some(match run {
                None => all,
                Some(r) => cs.mul(&r, &all).into(),
            });
        } else {
            let parts: Vec<(F, &Lc)> = block.iter().map(|b| (F::ONE, b)).collect();
            let sum = Lc::combine(&parts);
            match &run {
                None => cs.enforce_zero(sum),
                Some(r) => cs.enforce_mul(r.clone(), sum, Lc::zero()),
            }
        }
        hi = lo;
    }
}

/// At least one of the Boolean `bits` is one: one row, or a product chain under
/// [`Options::product_only_comparisons`].
fn enforce_nonzero(cs: &mut Ctx, bits: &[Lc]) {
    if cs.options.product_only_comparisons {
        let one = Lc::constant(F::ONE);
        let (last, rest) = bits.split_last().expect("at least one bit");
        let mut acc = one.clone();
        for b in rest {
            acc = cs.mul(&acc, &one.minus(b)).into();
        }
        cs.enforce_mul(acc, one.minus(last), Lc::zero());
        return;
    }
    let parts: Vec<(F, &Lc)> = bits.iter().map(|b| (F::ONE, b)).collect();
    let sum = Lc::combine(&parts);
    cs.hints.zero_tests += 1;
    let inverse = cs.eval(&sum).inv_or_zero();
    let inv = cs.alloc_defined(inverse, || Def::InverseOrZero {
        of: sum.clone(),
        max: bits.len() as u32,
    });
    cs.enforce_mul(sum, inv.into(), Lc::constant(F::ONE));
}

// ============================================================================
// Public-table lookup
// ============================================================================

/// Products of every subset of `bits`, indexed by the subset mask: `2^k - k - 1` rows.
fn monomials(cs: &mut Ctx, bits: &[Lc]) -> Vec<Lc> {
    let mut out: Vec<Lc> = Vec::with_capacity(1 << bits.len());
    out.push(Lc::constant(F::ONE));
    for mask in 1usize..1 << bits.len() {
        let top = usize::BITS as usize - 1 - mask.leading_zeros() as usize;
        let rest = mask ^ (1 << top);
        let lc = if rest == 0 {
            bits[top].clone()
        } else {
            cs.mul(&out[rest], &bits[top]).into()
        };
        out.push(lc);
    }
    out
}

/// `outputs` values of the public table row selected by the Boolean `index_bits`
/// (little-endian). The low [`LOW_INDEX_BITS`] bits are resolved through their subset
/// products, where every table column is a linear form; the high bits pick among those
/// forms with one row per form but the first. Each output is a single variable, or the
/// linear form itself when there are no high bits.
fn lookup(
    cs: &mut Ctx,
    index_bits: &[Lc],
    outputs: usize,
    entry: &dyn Fn(usize, usize) -> u64,
) -> Vec<Lc> {
    let low = index_bits.len().min(LOW_INDEX_BITS);
    let high = index_bits.len() - low;
    let low_monos = monomials(cs, &index_bits[..low]);
    let high_monos = monomials(cs, &index_bits[low..]);
    // One-hot selectors of the high index, as linear forms of its subset products.
    let selectors: Vec<Lc> = (0..1usize << high)
        .map(|h| {
            let parts: Vec<(F, &Lc)> = (0..1usize << high)
                .filter(|s| s & h == h)
                .map(|s| {
                    let sign = if (s ^ h).count_ones() % 2 == 0 {
                        F::ONE
                    } else {
                        F::NEG_ONE
                    };
                    (sign, &high_monos[s])
                })
                .collect();
            Lc::combine(&parts)
        })
        .collect();

    let mut out = Vec::with_capacity(outputs);
    let mut column = vec![F::ZERO; 1 << low];
    for o in 0..outputs {
        let forms: Vec<Lc> = (0..1usize << high)
            .map(|h| {
                for (l, slot) in column.iter_mut().enumerate() {
                    *slot = F::from_u64_reduced(entry((h << low) | l, o));
                }
                // Subset-sum inversion: column[l] = sum over S subset of l of coefficient[S].
                for i in 0..low {
                    for mask in 0..1usize << low {
                        if mask >> i & 1 == 1 {
                            let below = column[mask ^ (1 << i)];
                            column[mask] -= below;
                        }
                    }
                }
                let parts: Vec<(F, &Lc)> = column.iter().copied().zip(&low_monos).collect();
                Lc::combine(&parts)
            })
            .collect();
        if high == 0 {
            out.push(forms.into_iter().next().unwrap());
            continue;
        }
        // out = form_0 + sum over h >= 1 of selector_h (form_h - form_0); the last product
        // is the row that defines the output variable.
        let mut value = F::ZERO;
        for (sel, form) in selectors.iter().zip(&forms) {
            value += cs.eval(sel).const_mul(cs.eval(form));
        }
        let var: Lc = cs
            .alloc_defined(value, || Def::SumOfProducts {
                base: forms[0].clone(),
                products: selectors
                    .iter()
                    .zip(&forms)
                    .skip(1)
                    .map(|(sel, form)| (sel.clone(), form.minus(&forms[0])))
                    .collect(),
            })
            .into();
        let mut rest = var.minus(&forms[0]);
        let last = forms.len() - 1;
        for h in 1..last {
            rest = rest.minus(&cs.mul(&selectors[h], &forms[h].minus(&forms[0])).into());
        }
        cs.enforce_mul(selectors[last].clone(), forms[last].minus(&forms[0]), rest);
        out.push(var);
    }
    out
}

// ============================================================================
// Curves and window tables
// ============================================================================

/// Affine point in Montgomery-form coordinates.
type Pt = (Big, Big);

struct WindowTable {
    lo: usize,
    width: usize,
    signed: bool,
    limbs: usize,
    /// Canonical little-endian `(x, y)` per table index.
    points: Vec<[[u8; 8 * NW]; 2]>,
}

impl WindowTable {
    fn outputs(&self) -> usize {
        if self.signed {
            self.limbs + self.limbs.div_ceil(Y_CHUNK_LIMBS)
        } else {
            2 * self.limbs
        }
    }

    /// Output `o` of a table row: the bytes of `x`, then `y` in 48-bit chunks (signed
    /// windows) or in bytes (the unsigned window, whose outputs cost no rows).
    fn entry(&self, index: usize, o: usize) -> u64 {
        let [x, y] = &self.points[index];
        if o < self.limbs {
            return x[o] as u64;
        }
        if !self.signed {
            return y[o - self.limbs] as u64;
        }
        let from = Y_CHUNK_LIMBS * (o - self.limbs);
        let mut v = 0u64;
        for (k, &b) in y[from..(from + Y_CHUNK_LIMBS).min(self.limbs)]
            .iter()
            .enumerate()
        {
            v |= (b as u64) << (8 * k);
        }
        v
    }
}

/// `y^2 = x^3 + a2 x^2 + a4 x + a6` with the window tables of its base point.
struct Curve {
    f: Modulus,
    a2: u64,
    a4: u64,
    scalar_bits: usize,
    windows: Vec<WindowTable>,
}

impl Curve {
    fn double(&self, p: &Pt) -> Pt {
        let f = &self.f;
        let xx = f.mmul(&p.0, &p.0);
        let num = f.madd(
            &f.madd(
                &f.mmul(&f.small(3), &xx),
                &f.mmul(&f.small(2 * self.a2), &p.0),
            ),
            &f.small(self.a4),
        );
        let lam = f.mmul(&num, &f.inv(&f.madd(&p.1, &p.1)));
        self.chord(p, p, &lam)
    }

    fn chord(&self, p: &Pt, q: &Pt, lam: &Big) -> Pt {
        let f = &self.f;
        let x3 = f.msub(
            &f.msub(&f.msub(&f.mmul(lam, lam), &f.small(self.a2)), &p.0),
            &q.0,
        );
        let y3 = f.msub(&f.mmul(lam, &f.msub(&p.0, &x3)), &p.1);
        (x3, y3)
    }

    /// Group law on public points.
    fn add(&self, p: &Option<Pt>, q: &Option<Pt>) -> Option<Pt> {
        let f = &self.f;
        let (Some(p), Some(q)) = (p, q) else {
            return p.or(*q);
        };
        if p.0 == q.0 {
            if p.1 == q.1 && p.1 != [0; NW] {
                return Some(self.double(p));
            }
            return None;
        }
        let lam = f.mmul(&f.msub(&q.1, &p.1), &f.inv(&f.msub(&q.0, &p.0)));
        Some(self.chord(p, q, &lam))
    }

    fn scalar_mul(&self, k: &Big, p: &Pt) -> Option<Pt> {
        let mut acc = None;
        for i in (0..64 * NW).rev() {
            acc = self.add(&acc, &acc);
            if (k[i / 64] >> (i % 64)) & 1 == 1 {
                acc = self.add(&acc, &Some(*p));
            }
        }
        acc
    }

    /// `base_i + q` for every `i`, with one field inversion. No sum may be exceptional.
    fn batch_add(&self, base: &[Pt], q: &Pt) -> Vec<Pt> {
        let f = &self.f;
        let dx: Vec<Big> = base.iter().map(|p| f.msub(&q.0, &p.0)).collect();
        let mut prefix = Vec::with_capacity(dx.len());
        let mut acc = f.one;
        for d in &dx {
            assert!(*d != [0; NW], "exceptional table addition");
            prefix.push(acc);
            acc = f.mmul(&acc, d);
        }
        let mut inv = f.inv(&acc);
        let mut out = vec![([0u64; NW], [0u64; NW]); base.len()];
        for i in (0..base.len()).rev() {
            let dinv = f.mmul(&inv, &prefix[i]);
            inv = f.mmul(&inv, &dx[i]);
            let lam = f.mmul(&f.msub(&q.1, &base[i].1), &dinv);
            out[i] = self.chord(&base[i], q, &lam);
        }
        out
    }

    fn build(
        f: Modulus,
        a2: u64,
        a4: u64,
        base: (Big, Big),
        order: Big,
        scalar_bits: usize,
    ) -> Self {
        let mut curve = Self {
            f,
            a2,
            a4,
            scalar_bits,
            windows: Vec::new(),
        };
        let f = &curve.f;
        let g: Pt = (f.mont(&base.0), f.mont(&base.1));
        // H = [1/2] G, and its doublings.
        let mut half = order;
        for i in 0..NW {
            half[i] = (order[i] >> 1) | if i + 1 < NW { order[i + 1] << 63 } else { 0 };
        }
        let (half, _) = big_add(&half, &big(1));
        let h = curve.scalar_mul(&half, &g).expect("base point order");
        assert_eq!(curve.add(&Some(h), &Some(h)), Some(g));

        // The signed windows cover the bits below `last_lo`. Their partial sums are odd
        // integers of absolute value below 2^last_lo, which must not wrap modulo the order.
        let last_lo = scalar_bits - LAST_WINDOW;
        assert!(big_bitlen(&order) > last_lo, "signed windows would wrap");
        let mut pow2 = Vec::with_capacity(last_lo + 2);
        pow2.push(h);
        for i in 0..=last_lo {
            let next = curve.double(&pow2[i]);
            pow2.push(next);
        }

        let canonical = |p: &Pt| [big_to_bytes(&f.canon(&p.0)), big_to_bytes(&f.canon(&p.1))];
        let mut windows = Vec::new();
        let mut lo = 0;
        while lo < last_lo {
            let width = SIGNED_WINDOW.min(last_lo - lo);
            assert!(width >= 2);
            // Index r holds [(2r + 1) 2^lo] H.
            let mut pts = vec![pow2[lo]];
            for k in 0..width - 1 {
                let more = curve.batch_add(&pts, &pow2[lo + k + 1]);
                pts.extend(more);
            }
            windows.push(WindowTable {
                lo,
                width,
                signed: true,
                limbs: f.limbs,
                points: pts.iter().map(canonical).collect(),
            });
            lo += width;
        }
        // Index v holds [2 v 2^last_lo + 2^last_lo - 1] H.
        let neg_h = (h.0, f.msub(&[0; NW], &h.1));
        let mut pt = curve.add(&Some(pow2[last_lo]), &Some(neg_h));
        let mut pts = Vec::new();
        for _ in 0..1usize << LAST_WINDOW {
            pts.push(canonical(&pt.expect("table point at infinity")));
            pt = curve.add(&pt, &Some(pow2[last_lo + 1]));
        }
        windows.push(WindowTable {
            lo: last_lo,
            width: LAST_WINDOW,
            signed: false,
            limbs: f.limbs,
            points: pts,
        });
        curve.windows = windows;
        curve
    }

    fn secp256k1() -> Self {
        use crate::secp256k1_ct::{SECP_GX, SECP_GY, SECP_N};
        Self::build(
            Modulus::secp256k1_base(),
            0,
            0,
            (big4(&SECP_GX), big4(&SECP_GY)),
            big4(&SECP_N),
            256,
        )
    }

    /// Curve25519 in Montgomery form `v^2 = u^3 + 486662 u^2 + u`, base point `u = 9`.
    fn curve25519() -> Self {
        Self::build(
            Modulus::curve25519_base(),
            ED_MONT_A,
            1,
            (big(9), big4(&ED_BASE_V)),
            big4(&ED_L),
            256,
        )
    }

    /// BLS12-381 G1, `y^2 = x^3 + 4`, with 255-bit scalars.
    fn bls12_381_g1() -> Self {
        Self::build(
            Modulus::bls12_381_base(),
            0,
            0,
            (BLS_G1_X, BLS_G1_Y),
            big4(&BLS_R),
            255,
        )
    }
}

const BLS_P: Big = [
    0xb9feffffffffaaab,
    0x1eabfffeb153ffff,
    0x6730d2a0f6b0f624,
    0x64774b84f38512bf,
    0x4b1ba7b6434bacd7,
    0x1a0111ea397fe69a,
];
const BLS_R: [u64; 4] = [
    0xffffffff00000001,
    0x53bda402fffe5bfe,
    0x3339d80809a1d805,
    0x73eda753299d7d48,
];
const BLS_G1_X: Big = [
    0xfb3af00adb22c6bb,
    0x6c55e83ff97a1aef,
    0xa14e3a3f171bac58,
    0xc3688c4f9774b905,
    0x2695638c4fa9ac0f,
    0x17f1d3a73197d794,
];
const BLS_G1_Y: Big = [
    0x0caa232946c5e7e1,
    0xd03cc744a2888ae4,
    0x00db18cb2c04b3ed,
    0xfcf5e095d5d00af6,
    0xa09e30ed741d8ae4,
    0x08b3f481e3aaa0f1,
];

impl Modulus {
    /// The BLS12-381 base field (381 bits).
    pub fn bls12_381_base() -> Self {
        Self::new(&big_to_bytes(&BLS_P))
    }

    /// The BLS12-381 scalar field (255 bits), the order of G1.
    pub fn bls12_381_order() -> Self {
        Self::new(&big_to_bytes(&big4(&BLS_R)))
    }
}

macro_rules! cached_curve {
    ($name:ident, $build:path) => {
        fn $name<R>(run: impl FnOnce(&Curve) -> R) -> R {
            #[cfg(any(feature = "std", test))]
            {
                static CURVE: std::sync::OnceLock<Curve> = std::sync::OnceLock::new();
                run(CURVE.get_or_init($build))
            }
            #[cfg(not(any(feature = "std", test)))]
            {
                run(&$build())
            }
        }
    };
}

cached_curve!(with_secp256k1, Curve::secp256k1);
cached_curve!(with_curve25519, Curve::curve25519);
cached_curve!(with_bls12_381_g1, Curve::bls12_381_g1);

// ============================================================================
// Point addition and the fixed-base ladder
// ============================================================================

/// Accumulator: `x` in limbs, `y` as an unreduced integer.
struct Acc {
    x: Poly,
    y: Poly,
    x_element: Option<Element>,
}

fn byte_poly(bytes: &[Lc]) -> Poly {
    Poly(
        bytes
            .iter()
            .map(|lc| Coef {
                lc: lc.clone(),
                lo: 0,
                hi: 255,
            })
            .collect(),
    )
}

/// The table point a scalar window selects, as `(x limbs, y)`.
fn window_point(cs: &mut Ctx, table: &WindowTable, bits: &[Lc]) -> (Poly, Poly) {
    assert_eq!(bits.len(), table.width);
    let limbs = table.limbs;
    if !table.signed {
        assert!(table.width <= LOW_INDEX_BITS);
        let out = lookup(cs, bits, table.outputs(), &|i, o| table.entry(i, o));
        return (byte_poly(&out[..limbs]), byte_poly(&out[limbs..]));
    }
    // Window value u = 2^(w-1) s + r selects (2u + 1 - 2^w): index r with sign + when the
    // top bit s is set, index (complement of r) with sign - otherwise.
    let s = &bits[table.width - 1];
    let flip = Lc::constant(F::ONE).minus(s);
    let index: Vec<Lc> = bits[..table.width - 1]
        .iter()
        .map(|b| {
            let both = cs.mul(b, &flip);
            b.plus(&flip).minus(&Lc::from(both).scaled(F::TWO))
        })
        .collect();
    let out = lookup(cs, &index, table.outputs(), &|i, o| table.entry(i, o));
    let sign = s.scaled(F::TWO).plus_const(F::NEG_ONE);
    let mut y = vec![Coef::zero(); limbs];
    for (c, lc) in out[limbs..].iter().enumerate() {
        let width = 8 * (limbs - Y_CHUNK_LIMBS * c).min(Y_CHUNK_LIMBS);
        let max = (1i128 << width) - 1;
        y[Y_CHUNK_LIMBS * c] = Coef {
            lc: cs.mul(&sign, lc).into(),
            lo: -max,
            hi: max,
        };
    }
    (byte_poly(&out[..limbs]), Poly(y))
}

/// `acc + (xt, yt)` in affine coordinates.
///
/// Rows: `lambda (xt - x1) = yt - y1` and `lambda^2 = a2 + x1 + xt + x3`, both modulo `p`,
/// with `lambda` and `x3` fresh. The new `y` is the integer `lambda (xt - x3) - yt`.
///
/// These two equations fix the sum when `x1 != xt`. With `complete`, the further equation
/// `2 lambda y1 + x3 xt - x1 (x3 + 2 x1 + xt) - 2 a2 x1 - a4 = 0` is enforced. It follows
/// from the first two and the curve equation when `x1 != xt`, and for `(xt, yt) = (x1, y1)`
/// it reads `2 lambda y1 = 3 x1^2 + 2 a2 x1 + a4`, the tangent slope. For
/// `(xt, yt) = (x1, -y1)` the first equation reads `0 = 2 yt`, which no point of odd order
/// satisfies. So a `complete` step is exact for every pair of points of odd order whose sum
/// is not the identity, and unsatisfiable when it is.
fn add_step(cs: &mut Ctx, curve: &Curve, acc: &Acc, xt: &Poly, yt: &Poly, complete: bool) -> Acc {
    let f = &curve.f;
    let x1 = f.poly_value(cs, &acc.x);
    let y1 = f.poly_value(cs, &acc.y);
    let x2 = f.poly_value(cs, xt);
    let y2 = f.poly_value(cs, yt);
    let dx = f.msub(&x2, &x1);
    let mut lam = f.mmul(&f.msub(&y2, &y1), &f.inv(&dx));
    if complete {
        let num = f.madd(
            &f.madd(
                &f.mmul(&f.small(3), &f.mmul(&x1, &x1)),
                &f.mmul(&f.small(2 * curve.a2), &x1),
            ),
            &f.small(curve.a4),
        );
        let tangent = f.mmul(&num, &f.inv(&f.madd(&y1, &y1)));
        lam = big_select(big_zero_mask(&dx), &tangent, &lam);
    }
    let x3 = f.msub(
        &f.msub(&f.msub(&f.mmul(&lam, &lam), &f.small(curve.a2)), &x1),
        &x2,
    );
    cs.hints.divisions += 1;
    let a2 = Poly::constant_bytes(&curve.a2.to_le_bytes()[..3]);
    let source = if complete {
        // Where the two points share `x` the slope is the tangent at the accumulator.
        let tangent_linear = acc
            .x
            .mul_const(&(2 * curve.a2).to_le_bytes()[..3])
            .add(&Poly::constant_bytes(&curve.a4.to_le_bytes()[..1]));
        cs.source(|| Source::Slope {
            num: int_coefs(&yt.sub(&acc.y)),
            den: int_coefs(&xt.sub(&acc.x)),
            tangent_products: vec![(int_coefs(&acc.x.scale(3)), int_coefs(&acc.x))],
            tangent_linear: int_coefs(&tangent_linear),
            tangent_den: int_coefs(&acc.y.scale(2)),
            modulus: big_to_bytes(&f.p)[..f.limbs].to_vec(),
        })
    } else {
        residue_source(cs, f, &[], &yt.sub(&acc.y), Some(&xt.sub(&acc.x)))
    };
    let lam = alloc_int(cs, source, &big_to_bytes(&f.canon(&lam)), f.bits);
    let lam_p = lam.poly();
    let source = residue_source(
        cs,
        f,
        &[(&lam_p, &lam_p)],
        &acc.x.scale(-1).sub(xt).sub(&a2),
        None,
    );
    let x3 = alloc_int(cs, source, &big_to_bytes(&f.canon(&x3)), f.bits);
    let x3_p = x3.poly();

    let chord = mul_poly(cs, &lam_p, &xt.sub(&acc.x));
    enforce_zero_mod(cs, f, &chord.sub(yt).add(&acc.y));
    let square = mul_poly(cs, &lam_p, &lam_p);
    enforce_zero_mod(cs, f, &square.sub(&acc.x).sub(xt).sub(&x3_p).sub(&a2));

    if complete {
        let y1_p = if acc.y.is_narrow() {
            acc.y.clone()
        } else {
            reduce_poly(cs, f, &acc.y).poly()
        };
        let t1 = mul_poly(cs, &lam_p, &y1_p);
        let t2 = mul_poly(cs, &x3_p, xt);
        let t3 = mul_poly(cs, &acc.x, &x3_p.add(&acc.x.scale(2)).add(xt));
        let linear = acc
            .x
            .mul_const(&(2 * curve.a2).to_le_bytes()[..3])
            .add(&Poly::constant_bytes(&curve.a4.to_le_bytes()[..1]));
        enforce_zero_mod(cs, f, &t1.scale(2).add(&t2).sub(&t3).sub(&linear));
    }

    let back = mul_poly(cs, &lam_p, &xt.sub(&x3_p));
    Acc {
        x: x3_p,
        y: back.sub(yt),
        x_element: Some(x3),
    }
}

/// `[k] G` for the Boolean little-endian scalar bits: the final `x` (a reduced witness) and
/// the unreduced `y`. Unsatisfiable when `k` is a multiple of the group order.
fn fixed_base_mul(cs: &mut Ctx, curve: &Curve, scalar_bits_le: &[Lc]) -> Acc {
    assert_eq!(scalar_bits_le.len(), curve.scalar_bits, "scalar width");
    let mut acc: Option<Acc> = None;
    for table in &curve.windows {
        let bits = &scalar_bits_le[table.lo..table.lo + table.width];
        let (xt, yt) = window_point(cs, table, bits);
        acc = Some(match acc {
            None => Acc {
                x: xt,
                y: yt,
                x_element: None,
            },
            Some(prev) if table.signed => add_step(cs, curve, &prev, &xt, &yt, false),
            // The unsigned window's point has `y` in limbs, so it takes the accumulator
            // role and the tangent equation needs no reduction of the running `y`.
            Some(prev) => {
                let last = Acc {
                    x: xt,
                    y: yt,
                    x_element: None,
                };
                add_step(cs, curve, &last, &prev.x, &prev.y, true)
            }
        });
    }
    acc.expect("at least one window")
}

/// `P + [k] G` for a point `P` of the curve given in limbs (possibly negated limbs for
/// `y`): one ladder and one complete addition with `P` in the accumulator role.
fn add_to_fixed_base(
    cs: &mut Ctx,
    curve: &Curve,
    px: &Poly,
    py: &Poly,
    scalar_bits_le: &[Lc],
) -> Acc {
    assert!(px.is_narrow() && py.is_narrow());
    let multiple = fixed_base_mul(cs, curve, scalar_bits_le);
    let point = Acc {
        x: px.clone(),
        y: py.clone(),
        x_element: None,
    };
    add_step(cs, curve, &point, &multiple.x, &multiple.y, true)
}

/// A field element in its canonical representation.
#[derive(Clone)]
pub struct CanonicalCoordinate {
    /// Little-endian bytes, one per limb of the field (32, or 48 for BLS12-381).
    pub bytes_le: Vec<Lc>,
    /// Little-endian bits (bit `8i + k` is bit `k` of byte `i`); bits above the field's
    /// width are the constant zero.
    pub bits_le: Vec<Lc>,
}

impl CanonicalCoordinate {
    fn from_element(mut e: Element) -> Self {
        e.bits_le.resize(8 * e.bytes_le.len(), Lc::zero());
        Self {
            bytes_le: e.bytes_le,
            bits_le: e.bits_le,
        }
    }

    /// The eight bits of byte `i`, least significant first.
    pub fn byte_bits(&self, i: usize) -> [Lc; 8] {
        core::array::from_fn(|k| self.bits_le[8 * i + k].clone())
    }
}

fn canonical_x(cs: &mut Ctx, f: &Modulus, acc: &Acc) -> CanonicalCoordinate {
    let x = acc.x_element.clone().expect("at least one addition");
    canonical(cs, f, &x);
    CanonicalCoordinate::from_element(x)
}

fn canonical_y(cs: &mut Ctx, f: &Modulus, acc: &Acc) -> CanonicalCoordinate {
    let y = reduce_poly(cs, f, &acc.y);
    canonical(cs, f, &y);
    CanonicalCoordinate::from_element(y)
}

fn enforce_scalar_range(cs: &mut Ctx, bits_le: &[Lc], order: &Big) {
    let (max, _) = big_sub(order, &big(1));
    enforce_le_const(cs, bits_le, &big_to_bytes(&max));
    enforce_nonzero(cs, bits_le);
}

// ============================================================================
// secp256k1
// ============================================================================

/// An affine point with unreduced coordinates.
#[derive(Clone)]
pub struct AffinePoint {
    pub x: Lazy,
    pub y: Lazy,
}

/// `p + q` on secp256k1 for two points of the curve with `p != -q` (which is
/// unsatisfiable); `p = q` is handled. Both coordinates of the result are fresh elements.
pub fn secp256k1_point_add(cs: &mut impl Host, p: &AffinePoint, q: &AffinePoint) -> AffinePoint {
    run(cs, |cs| {
        with_secp256k1(|curve| {
            let f = &curve.f;
            let narrow = |cs: &mut Ctx, a: &Lazy| {
                if a.0.is_narrow() && a.0.0.len() <= f.limbs {
                    a.0.clone()
                } else {
                    reduce_poly(cs, f, &a.0).poly()
                }
            };
            let acc = Acc {
                x: narrow(cs, &p.x),
                y: narrow(cs, &p.y),
                x_element: None,
            };
            let (qx, qy) = (narrow(cs, &q.x), narrow(cs, &q.y));
            let sum = add_step(cs, curve, &acc, &qx, &qy, true);
            AffinePoint {
                x: Lazy(sum.x),
                y: reduce_poly(cs, f, &sum.y).lazy(),
            }
        })
    })
}

/// A secp256k1 point with canonical affine coordinates.
#[derive(Clone)]
pub struct Secp256k1PublicKey {
    pub x: CanonicalCoordinate,
    pub y: CanonicalCoordinate,
}

impl Secp256k1PublicKey {
    /// Parity of `y`.
    pub fn y_is_odd(&self) -> Lc {
        self.y.bits_le[0].clone()
    }

    /// The point as an operand of [`secp256k1_point_add`].
    pub fn point(&self) -> AffinePoint {
        AffinePoint {
            x: Lazy(byte_poly(&self.x.bytes_le)),
            y: Lazy(byte_poly(&self.y.bytes_le)),
        }
    }

    /// SEC1 compressed encoding: `02 | parity(y)`, then `x` big-endian (33 bytes).
    pub fn compressed_bytes(&self) -> Vec<Lc> {
        let mut out = vec![self.y_is_odd().plus_const(F::TWO)];
        out.extend(self.x.bytes_le.iter().rev().cloned());
        out
    }

    /// Bits of [`Self::compressed_bytes`], per byte and least significant first.
    pub fn compressed_bits(&self) -> Vec<[Lc; 8]> {
        let mut prefix: [Lc; 8] = core::array::from_fn(|_| Lc::zero());
        prefix[0] = self.y_is_odd();
        prefix[1] = Lc::constant(F::ONE);
        let mut out = vec![prefix];
        out.extend((0..32).rev().map(|i| self.x.byte_bits(i)));
        out
    }

    /// `x || y`, both big-endian (64 bytes).
    pub fn uncompressed_bytes(&self) -> Vec<Lc> {
        let mut out: Vec<Lc> = self.x.bytes_le.iter().rev().cloned().collect();
        out.extend(self.y.bytes_le.iter().rev().cloned());
        out
    }

    /// Bits of [`Self::uncompressed_bytes`], per byte and least significant first.
    pub fn uncompressed_bits(&self) -> Vec<[Lc; 8]> {
        let mut out: Vec<[Lc; 8]> = (0..32).rev().map(|i| self.x.byte_bits(i)).collect();
        out.extend((0..32).rev().map(|i| self.y.byte_bits(i)));
        out
    }

    /// BIP340 x-only encoding: `x` big-endian (32 bytes). It names the point of this `x`
    /// with even `y`; see [`Self::enforce_even_y`].
    pub fn x_only_bytes(&self) -> Vec<Lc> {
        self.x.bytes_le.iter().rev().cloned().collect()
    }

    /// Bits of [`Self::x_only_bytes`], per byte and least significant first.
    pub fn x_only_bits(&self) -> Vec<[Lc; 8]> {
        (0..32).rev().map(|i| self.x.byte_bits(i)).collect()
    }

    /// Require `y` even, so that the scalar itself is the BIP340 secret key of
    /// [`Self::x_only_bytes`].
    pub fn enforce_even_y(&self, cs: &mut impl Host) {
        cs.constraint_system().enforce_zero(self.y_is_odd());
    }
}

fn secp_key(cs: &mut Ctx, curve: &Curve, acc: &Acc) -> Secp256k1PublicKey {
    Secp256k1PublicKey {
        x: canonical_x(cs, &curve.f, acc),
        y: canonical_y(cs, &curve.f, acc),
    }
}

/// `[k] G` on secp256k1 for the 256 little-endian scalar bits, which the caller has
/// constrained Boolean. The result is `[k mod n] G`; the rows are unsatisfiable when
/// `k = 0 (mod n)`. Use [`secp256k1_enforce_scalar_range`] where `1 <= k < n` is part of
/// the statement.
pub fn secp256k1_fixed_base_mul(cs: &mut impl Host, scalar_bits_le: &[Lc]) -> Secp256k1PublicKey {
    run(cs, |cs| {
        with_secp256k1(|curve| {
            let acc = fixed_base_mul(cs, curve, scalar_bits_le);
            secp_key(cs, curve, &acc)
        })
    })
}

/// The canonical `x` of `[k] G` only (BIP340 public key bytes are its big-endian bytes),
/// without materialising `y`. Same contract as [`secp256k1_fixed_base_mul`].
pub fn secp256k1_fixed_base_mul_x_only(
    cs: &mut impl Host,
    scalar_bits_le: &[Lc],
) -> CanonicalCoordinate {
    run(cs, |cs| {
        with_secp256k1(|curve| {
            let acc = fixed_base_mul(cs, curve, scalar_bits_le);
            canonical_x(cs, &curve.f, &acc)
        })
    })
}

/// `1 <= k <= n - 1` for Boolean little-endian scalar bits.
pub fn secp256k1_enforce_scalar_range(cs: &mut impl Host, scalar_bits_le: &[Lc]) {
    assert_eq!(scalar_bits_le.len(), 256);
    run(cs, |cs| {
        enforce_scalar_range(cs, scalar_bits_le, &big4(&crate::secp256k1_ct::SECP_N))
    })
}

/// A witness point of secp256k1: both coordinates canonical and `y^2 = x^3 + 7` enforced.
/// The curve has prime order, so every such point is a valid operand of the additions
/// here. For points that do not come out of a multiplication in the same relation (an
/// extended public key, an internal key with unknown discrete logarithm).
pub fn secp256k1_alloc_point(
    cs: &mut impl Host,
    x_le: &[u8; 32],
    y_le: &[u8; 32],
) -> Secp256k1PublicKey {
    run(cs, |cs| {
        let f = Modulus::secp256k1_base();
        let input = |cs: &mut Ctx| {
            cs.source(|| Source::Input {
                bits: f.bits as u32,
            })
        };
        let source = input(cs);
        let x = alloc_int(cs, source, x_le, f.bits);
        let source = input(cs);
        let y = alloc_int(cs, source, y_le, f.bits);
        canonical(cs, &f, &x);
        canonical(cs, &f, &y);
        let xx = mul_poly(cs, &x.poly(), &x.poly());
        let xx = reduce_poly(cs, &f, &xx);
        let xxx = mul_poly(cs, &xx.poly(), &x.poly());
        let yy = mul_poly(cs, &y.poly(), &y.poly());
        enforce_zero_mod(cs, &f, &yy.sub(&xxx).sub(&Poly::constant_bytes(&[7])));
        Secp256k1PublicKey {
            x: CanonicalCoordinate::from_element(x),
            y: CanonicalCoordinate::from_element(y),
        }
    })
}

/// `point + [k] G` on secp256k1: the BIP32 public child `K_child = K_par + [I_L] G`.
///
/// Costs one fixed-base multiplication and one complete addition. It does not save a
/// multiplication over the scalar route (`[(k_par + I_L) mod n] G`); it is the route for
/// a parent whose secret scalar is not in the relation.
///
/// `point` must be a point of the curve: an output of a gadget here or of
/// [`secp256k1_alloc_point`]. Exactly two cases are unsatisfiable: `k = 0 (mod n)`, and
/// `point = -[k] G` (the sum is the identity; BIP32 declares that child invalid).
/// `point = [k] G` is handled by the tangent equation.
pub fn secp256k1_add_fixed_base(
    cs: &mut impl Host,
    point: &Secp256k1PublicKey,
    scalar_bits_le: &[Lc],
) -> Secp256k1PublicKey {
    run(cs, |cs| {
        with_secp256k1(|curve| {
            let (px, py) = (byte_poly(&point.x.bytes_le), byte_poly(&point.y.bytes_le));
            let acc = add_to_fixed_base(cs, curve, &px, &py, scalar_bits_le);
            secp_key(cs, curve, &acc)
        })
    })
}

fn taproot(
    cs: &mut Ctx,
    curve: &Curve,
    internal: &Secp256k1PublicKey,
    tweak_bits_le: &[Lc],
) -> Acc {
    // lift_x: the point of the internal key's x with even y is (x, y) or (x, p - y).
    let sign = Lc::constant(F::ONE).minus(&internal.y_is_odd().scaled(F::TWO));
    let px = byte_poly(&internal.x.bytes_le);
    let py = Poly(
        internal
            .y
            .bytes_le
            .iter()
            .map(|b| Coef {
                lc: cs.mul(&sign, b).into(),
                lo: -255,
                hi: 255,
            })
            .collect(),
    );
    add_to_fixed_base(cs, curve, &px, &py, tweak_bits_le)
}

/// BIP341 output key `Q = lift_x(x(P)) + [t] G` for the internal key `P` and the tweak
/// `t` (256 Boolean little-endian bits; the caller hashes them and, as BIP341 requires,
/// rejects `t >= n` with [`secp256k1_enforce_scalar_range`]).
///
/// `lift_x` is applied here: `P` is negated when its `y` is odd. The output key is
/// `Q.x_only_bytes()`; `Q.y_is_odd()` is the parity bit of the control block.
///
/// Unsatisfiable exactly when `t = 0 (mod n)` or `Q` is the identity (`lift_x(P) = -[t] G`,
/// which BIP341 also rejects). `lift_x(P) = [t] G` is handled by the tangent equation.
pub fn secp256k1_taproot_tweak(
    cs: &mut impl Host,
    internal: &Secp256k1PublicKey,
    tweak_bits_le: &[Lc],
) -> Secp256k1PublicKey {
    run(cs, |cs| {
        with_secp256k1(|curve| {
            let acc = taproot(cs, curve, internal, tweak_bits_le);
            secp_key(cs, curve, &acc)
        })
    })
}

/// The canonical `x` of [`secp256k1_taproot_tweak`] only: the 32-byte output key, without
/// materialising `y(Q)`. Same contract.
pub fn secp256k1_taproot_tweak_x_only(
    cs: &mut impl Host,
    internal: &Secp256k1PublicKey,
    tweak_bits_le: &[Lc],
) -> CanonicalCoordinate {
    run(cs, |cs| {
        with_secp256k1(|curve| {
            let acc = taproot(cs, curve, internal, tweak_bits_le);
            canonical_x(cs, &curve.f, &acc)
        })
    })
}

// ============================================================================
// Ed25519
// ============================================================================

/// An Ed25519 point `[k] B` in its RFC 8032 encoding.
#[derive(Clone)]
pub struct Ed25519PublicKey {
    /// Canonical Edwards `y` (bit 255 is the constant zero).
    pub y: CanonicalCoordinate,
    /// Parity of the canonical Edwards `x`.
    pub x_is_odd: Lc,
    /// The same point on the Montgomery model `v^2 = u^3 + 486662 u^2 + u`, in limbs; the
    /// operand of [`ed25519_add_fixed_base`].
    pub montgomery: AffinePoint,
}

impl Ed25519PublicKey {
    /// The 32-byte encoding: `y` little-endian with the parity of `x` in the top bit.
    pub fn encoding_bytes(&self) -> Vec<Lc> {
        let mut out = self.y.bytes_le.clone();
        out[31] = out[31].plus(&self.x_is_odd.scaled(F::from_u64_reduced(128)));
        out
    }

    /// The 256 bits of the encoding, little-endian.
    pub fn encoding_bits(&self) -> Vec<Lc> {
        let mut out = self.y.bits_le.clone();
        out[255] = self.x_is_odd.clone();
        out
    }
}

/// Map a Montgomery point of order `l` to its Edwards encoding:
/// `y = (u - 1) / (u + 1)`, `x = sqrt(-486664) u / v`. Such a point has `u != -1` and
/// `v != 0`, so both quotients are determined.
fn ed_key(cs: &mut Ctx, curve: &Curve, acc: Acc) -> Ed25519PublicKey {
    let f = &curve.f;
    let u = acc.x;
    let v = reduce_poly(cs, f, &acc.y).poly();
    let (un, vn) = (f.poly_value(cs, &u), f.poly_value(cs, &v));
    let yn = f.mmul(&f.msub(&un, &f.one), &f.inv(&f.madd(&un, &f.one)));
    let root = big4(&ED_SQRT_M486664);
    let xn = f.mmul(&f.mmul(&f.mont(&root), &un), &f.inv(&vn));
    cs.hints.divisions += 2;
    let one = Poly::constant_bytes(&[1]);
    let source = residue_source(cs, f, &[], &u.sub(&one), Some(&u.add(&one)));
    let y = alloc_int(cs, source, &big_to_bytes(&f.canon(&yn)), f.bits);
    let source = residue_source(
        cs,
        f,
        &[],
        &u.mul_const(&big_to_bytes(&root)[..32]),
        Some(&v),
    );
    let x = alloc_int(cs, source, &big_to_bytes(&f.canon(&xn)), f.bits);

    let yu = mul_poly(cs, &y.poly(), &u.add(&one));
    enforce_zero_mod(cs, f, &yu.sub(&u).add(&one));
    let xv = mul_poly(cs, &x.poly(), &v);
    enforce_zero_mod(cs, f, &xv.sub(&u.mul_const(&big_to_bytes(&root)[..32])));
    canonical(cs, f, &y);
    canonical(cs, f, &x);
    Ed25519PublicKey {
        x_is_odd: x.bits_le[0].clone(),
        y: CanonicalCoordinate::from_element(y),
        montgomery: AffinePoint {
            x: Lazy(u),
            y: Lazy(v),
        },
    }
}

/// `[k] B` on Ed25519 for the 256 little-endian scalar bits, which the caller has
/// constrained Boolean. The result is `[k mod l] B`; the rows are unsatisfiable when
/// `k = 0 (mod l)`, which no clamped scalar is.
///
/// The ladder runs on the Montgomery model; the result is mapped to Edwards coordinates.
pub fn ed25519_fixed_base_mul(cs: &mut impl Host, scalar_bits_le: &[Lc]) -> Ed25519PublicKey {
    run(cs, |cs| {
        with_curve25519(|curve| {
            let acc = fixed_base_mul(cs, curve, scalar_bits_le);
            ed_key(cs, curve, acc)
        })
    })
}

/// `point + [k] B` on Ed25519: the BIP32-Ed25519 public child `A_child = A_par + [8 Z_L] B`
/// (pass the bits of `8 Z_L`, i.e. three zero bits below those of `Z_L`).
///
/// `point` must come out of a gadget here (it is a point of order `l`). Unsatisfiable
/// exactly when `k = 0 (mod l)` or the sum is the identity; `point = [k] B` is handled.
/// Like its secp256k1 counterpart it costs a full multiplication plus one addition.
pub fn ed25519_add_fixed_base(
    cs: &mut impl Host,
    point: &Ed25519PublicKey,
    scalar_bits_le: &[Lc],
) -> Ed25519PublicKey {
    run(cs, |cs| {
        with_curve25519(|curve| {
            let (px, py) = (&point.montgomery.x.0, &point.montgomery.y.0);
            let acc = add_to_fixed_base(cs, curve, px, py, scalar_bits_le);
            ed_key(cs, curve, acc)
        })
    })
}

/// RFC 8032 clamping of 256 little-endian bits: clear bits 0, 1, 2 and 255, set bit 254.
pub fn ed25519_clamp(bits_le: &[Lc]) -> Vec<Lc> {
    assert_eq!(bits_le.len(), 256);
    let mut out = bits_le.to_vec();
    for i in [0, 1, 2, 255] {
        out[i] = Lc::zero();
    }
    out[254] = Lc::constant(F::ONE);
    out
}

/// `1 <= k <= l - 1` for Boolean little-endian scalar bits.
pub fn ed25519_enforce_scalar_range(cs: &mut impl Host, scalar_bits_le: &[Lc]) {
    assert_eq!(scalar_bits_le.len(), 256);
    run(cs, |cs| {
        enforce_scalar_range(cs, scalar_bits_le, &big4(&ED_L))
    })
}

// ============================================================================
// BLS12-381 G1
// ============================================================================

/// A BLS12-381 G1 point `[k] G` with canonical affine coordinates.
#[derive(Clone)]
pub struct Bls12381G1PublicKey {
    pub x: CanonicalCoordinate,
    pub y: CanonicalCoordinate,
    /// The sign flag of the compressed encoding: `y > (p - 1) / 2`.
    pub y_is_largest: Lc,
}

impl Bls12381G1PublicKey {
    /// The 48-byte compressed encoding (ZCash / IETF): `x` big-endian, with the
    /// compression flag (bit 7 of the first byte) set, the infinity flag (bit 6) clear and
    /// the sign flag (bit 5) set when `y` is the lexicographically larger root.
    pub fn compressed_bytes(&self) -> Vec<Lc> {
        let mut out: Vec<Lc> = self.x.bytes_le.iter().rev().cloned().collect();
        out[0] = out[0]
            .plus(&self.y_is_largest.scaled(F::from_u64_reduced(32)))
            .plus_const(F::from_u64_reduced(128));
        out
    }

    /// Bits of [`Self::compressed_bytes`], per byte and least significant first.
    pub fn compressed_bits(&self) -> Vec<[Lc; 8]> {
        let mut out: Vec<[Lc; 8]> = (0..48).rev().map(|i| self.x.byte_bits(i)).collect();
        out[0][5] = self.y_is_largest.clone();
        out[0][7] = Lc::constant(F::ONE);
        out
    }
}

/// `[k] G` on BLS12-381 G1 for the 255 little-endian scalar bits, which the caller has
/// constrained Boolean. The result is `[k mod r] G`; the rows are unsatisfiable when
/// `k = 0 (mod r)`. Use [`bls12_381_enforce_scalar_range`] where `1 <= k < r` is part of
/// the statement.
///
/// The sign flag is the low bit of the canonical `z = 2 y mod p`: with `y` and `z`
/// canonical, `2 y - z` is `0` (then `z` is even and `y <= (p - 1) / 2`) or `p` (then `z`
/// is odd and `y > (p - 1) / 2`).
pub fn bls12_381_g1_fixed_base_mul(
    cs: &mut impl Host,
    scalar_bits_le: &[Lc],
) -> Bls12381G1PublicKey {
    run(cs, |cs| {
        with_bls12_381_g1(|curve| {
            let f = &curve.f;
            let acc = fixed_base_mul(cs, curve, scalar_bits_le);
            let x = canonical_x(cs, f, &acc);
            let y = reduce_poly(cs, f, &acc.y);
            canonical(cs, f, &y);
            let twice = y.poly().scale(2);
            let z = reduce_poly(cs, f, &twice);
            canonical(cs, f, &z);
            Bls12381G1PublicKey {
                x,
                y_is_largest: z.bits_le[0].clone(),
                y: CanonicalCoordinate::from_element(y),
            }
        })
    })
}

/// `1 <= k <= r - 1` for 255 Boolean little-endian scalar bits.
pub fn bls12_381_enforce_scalar_range(cs: &mut impl Host, scalar_bits_le: &[Lc]) {
    assert_eq!(scalar_bits_le.len(), 255);
    run(cs, |cs| {
        enforce_scalar_range(cs, scalar_bits_le, &big4(&BLS_R))
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ed25519_ct::public_key_from_clamped_scalar;
    use crate::secp256k1_ct::{Fp256, SECP_N, SECP_P, SecpPoint};
    use qsag_agg::zk_hem::relation::Shape;
    use std::println;

    type U256 = [u64; 4];

    fn u256_add(a: &U256, b: &U256) -> (U256, u64) {
        let (s, _) = big_add(&big4(a), &big4(b));
        ([s[0], s[1], s[2], s[3]], s[4])
    }

    fn u256_sub(a: &U256, b: &U256) -> (U256, u64) {
        let (d, _) = big_sub(&big4(a), &big4(b));
        ([d[0], d[1], d[2], d[3]], d[4] & 1)
    }

    fn u256_from_bytes(bytes: &[u8; 32]) -> U256 {
        let b = big_from_bytes(bytes);
        [b[0], b[1], b[2], b[3]]
    }

    fn u256_to_bytes(a: &U256) -> [u8; 32] {
        big_to_bytes(&big4(a))[..32].try_into().unwrap()
    }

    fn narrow(a: &Big) -> U256 {
        assert_eq!(a[4] | a[5], 0);
        [a[0], a[1], a[2], a[3]]
    }

    /// A context over a plain constraint system, for the internal gadgets.
    fn ctx(cs: &mut ConstraintSystem) -> Ctx<'_> {
        Ctx {
            cs,
            options: Options::default(),
            hints: HintCount::default(),
        }
    }

    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        }

        fn bytes(&mut self) -> [u8; 32] {
            u256_to_bytes(&core::array::from_fn(|_| self.next()))
        }
    }

    fn bit_vars(cs: &mut ConstraintSystem, le: &[u8; 32]) -> Vec<Lc> {
        (0..256)
            .map(|i| {
                let bit: Lc = cs
                    .alloc(F::from_u64_reduced(((le[i / 8] >> (i % 8)) & 1) as u64))
                    .into();
                cs.enforce_boolean(&bit);
                bit
            })
            .collect()
    }

    fn eval_bytes(cs: &ConstraintSystem, lcs: &[Lc]) -> Vec<u8> {
        lcs.iter()
            .map(|lc| {
                let v = cs.eval(lc).to_canonical_u64();
                assert!(v < 256, "byte out of range");
                v as u8
            })
            .collect()
    }

    fn eval_bit_bytes(cs: &ConstraintSystem, bits: &[[Lc; 8]]) -> Vec<u8> {
        bits.iter()
            .map(|byte| {
                byte.iter().enumerate().fold(0u8, |acc, (k, lc)| {
                    let v = cs.eval(lc).to_canonical_u64();
                    assert!(v < 2, "bit out of range");
                    acc | ((v as u8) << k)
                })
            })
            .collect()
    }

    fn var_of(lc: &Lc) -> usize {
        assert_eq!(lc.terms().len(), 1);
        lc.terms()[0].0 as usize
    }

    /// Violated rows as `(range rows, other rows)`. A range row is `v (1 - v) = 0`: an
    /// empty right side and a second factor of more than one term. Product rows have a
    /// right side and the closing row of a reduction has the constant one as second factor.
    fn violated_rows(shape: &Shape, z: &[F]) -> (usize, usize) {
        assert_eq!(shape.num_sbox, 0);
        let (mut range, mut other) = (0, 0);
        for i in 0..shape.num_rows() {
            if shape.a.row_dot(i, z).const_mul(shape.b.row_dot(i, z)) != shape.c.row_dot(i, z) {
                if shape.c.row(i).count() == 0 && shape.b.row(i).count() > 1 {
                    range += 1;
                } else {
                    other += 1;
                }
            }
        }
        (range, other)
    }

    fn le(a: &U256) -> [u8; 32] {
        u256_to_bytes(a)
    }

    fn be(le: &[u8; 32]) -> [u8; 32] {
        let mut out = *le;
        out.reverse();
        out
    }

    /// Shift-and-add reference, independent of the Montgomery code under test.
    fn ref_mulmod(a: &U256, b: &U256, p: &U256) -> U256 {
        let reduce = |x: U256, carry: u64| {
            let (d, borrow) = u256_sub(&x, p);
            if carry == 1 || borrow == 0 { d } else { x }
        };
        let a = reduce(*a, 0);
        let mut acc = [0u64; 4];
        for i in (0..256).rev() {
            let (s, c) = u256_add(&acc, &acc);
            acc = reduce(s, c);
            if (b[i / 64] >> (i % 64)) & 1 == 1 {
                let (s, c) = u256_add(&acc, &a);
                acc = reduce(s, c);
            }
        }
        acc
    }

    #[test]
    fn field_mul_matches_references_for_four_moduli() {
        let mut rng = Rng(1);
        let moduli = [
            (Modulus::secp256k1_base(), SECP_P),
            (Modulus::curve25519_base(), ED_P),
            (Modulus::secp256k1_order(), SECP_N),
            (Modulus::ed25519_order(), ED_L),
        ];
        for (m, p) in &moduli {
            for round in 0..3 {
                let (mut a, mut b) = (rng.bytes(), rng.bytes());
                if round == 0 {
                    // Largest representable operands.
                    a = [0xff; 32];
                    b = [0xff; 32];
                }
                let mut cs = ConstraintSystem::new();
                let (ea, eb) = (m.alloc(&mut cs, &a), m.alloc(&mut cs, &b));
                let c = m.mul(&mut cs, &ea.lazy(), &eb.lazy());
                m.enforce_canonical(&mut cs, &c);
                // `alloc` keeps the low `bits` bits.
                let mask = |x: &[u8; 32]| {
                    let mut v = u256_from_bytes(x);
                    if m.bits() < 256 {
                        v[3] &= (1u64 << (m.bits() - 192)) - 1;
                    }
                    v
                };
                let want = ref_mulmod(&mask(&a), &mask(&b), p);
                assert_eq!(eval_bytes(&cs, &c.bytes_le), le(&want));
                assert_eq!(m.value(&cs, &c.lazy()), le(&want));
                if *p == SECP_P {
                    let native = Fp256(ref_mulmod(&mask(&a), &[1, 0, 0, 0], p))
                        * Fp256(ref_mulmod(&mask(&b), &[1, 0, 0, 0], p));
                    assert_eq!(native.normalize().0, want);
                }
                let (shape, z) = cs.finish();
                assert!(shape.is_satisfied(&z));
                for lc in [
                    &c.bytes_le[0],
                    &c.bytes_le[17],
                    &c.bits_le[9],
                    &ea.bytes_le[31],
                ] {
                    let mut bad = z.clone();
                    bad[var_of(lc)] += F::ONE;
                    assert!(!shape.is_satisfied(&bad));
                }
            }
        }
    }

    #[test]
    fn lazy_sums_and_differences_reduce_correctly() {
        let m = Modulus::secp256k1_base();
        let mut rng = Rng(2);
        let (a, b, c) = (rng.bytes(), rng.bytes(), rng.bytes());
        let mut cs = ConstraintSystem::new();
        let (ea, eb, ec) = (
            m.alloc(&mut cs, &a),
            m.alloc(&mut cs, &b),
            m.alloc(&mut cs, &c),
        );
        // (a - b + 3c + 5) * (b - a)
        let left = ea
            .lazy()
            .sub(&eb.lazy())
            .add(&ec.lazy().scale(3))
            .add(&Lazy::constant(&[5]));
        let right = eb.lazy().sub(&ea.lazy());
        let out = m.mul(&mut cs, &left, &right);
        m.enforce_canonical(&mut cs, &out);
        let (fa, fb, fc) = (
            Fp256(u256_from_bytes(&a)).normalize(),
            Fp256(u256_from_bytes(&b)).normalize(),
            Fp256(u256_from_bytes(&c)).normalize(),
        );
        let three_c = fc + fc + fc;
        let want = (fa - fb + three_c + Fp256([5, 0, 0, 0])) * (fb - fa);
        assert_eq!(eval_bytes(&cs, &out.bytes_le), le(&want.normalize().0));
        let (shape, z) = cs.finish();
        assert!(shape.is_satisfied(&z));
    }

    #[test]
    fn non_canonical_limbs_and_out_of_range_quotients_are_rejected_by_range_rows_alone() {
        let m = Modulus::secp256k1_base();
        let mut rng = Rng(3);
        let (a, b) = (rng.bytes(), rng.bytes());
        let mut cs = ConstraintSystem::new();
        let (ea, eb) = (m.alloc(&mut cs, &a), m.alloc(&mut cs, &b));
        let product = mul_poly(&mut ctx(&mut cs), &ea.poly(), &eb.poly());
        let value = m.value(&cs, &Lazy(product.clone()));
        let mut c = ctx(&mut cs);
        let source = c.source(|| Source::Input {
            bits: m.bits() as u32,
        });
        let r = alloc_int(&mut c, source, &value, m.bits());
        let q = enforce_zero_mod(&mut ctx(&mut cs), &m, &r.poly().sub(&product));
        let (shape, z) = cs.finish();
        assert!(shape.is_satisfied(&z));
        assert_eq!(violated_rows(&shape, &z), (0, 0));

        // Move 256 from one limb into the next: the represented integer, and with it every
        // product row and the closing row, is unchanged. Only range rows can object: the two
        // limbs, and a carry whose integer value moved while its bits did not.
        for (element, most) in [(&r, 2), (&q, 3)] {
            let mut bad = z.clone();
            bad[var_of(&element.bytes_le[0])] += F::from_u64_reduced(256);
            bad[var_of(&element.bytes_le[1])] -= F::ONE;
            let (range, other) = violated_rows(&shape, &bad);
            assert!((2..=most).contains(&range), "{range} range rows");
            assert_eq!(other, 0);
        }
        // A forged carry: every variable after the quotient is a carry bit, and each one is
        // pinned.
        let first_carry = var_of(&q.bits_le[q.bits_le.len() - 2]) + 1;
        assert!(shape.mask_var_base - first_carry > 60);
        for i in first_carry..shape.mask_var_base {
            let mut bad = z.clone();
            bad[i] = F::ONE - bad[i];
            assert!(!shape.is_satisfied(&bad), "carry bit {i} is free");
        }
        // The reduction no longer needs a wide quotient: the high limbs are folded first.
        assert!(q.bits_le.len() < 48, "quotient of {} bits", q.bits_le.len());
        assert!(q.bytes_le.len() >= 2);
        // A quotient that is off by one breaks the identity itself.
        let mut bad = z.clone();
        let bit = var_of(&q.bits_le[0]);
        let delta = F::ONE - bad[bit] - bad[bit];
        bad[bit] += delta;
        bad[var_of(&q.bytes_le[0])] += delta;
        assert!(!shape.is_satisfied(&bad));
    }

    #[test]
    fn enforce_zero_accepts_exactly_the_multiples_of_p() {
        let m = Modulus::curve25519_base();
        let twice = u256_add(&ED_P, &ED_P).0;
        for (value, ok) in [
            ([0u64; 4], true),
            (ED_P, true),
            (twice, true),
            ([1, 0, 0, 0], false),
            (u256_sub(&ED_P, &[1, 0, 0, 0]).0, false),
            (u256_add(&ED_P, &[1, 0, 0, 0]).0, false),
            (u256_add(&twice, &[1 << 40, 0, 0, 0]).0, false),
        ] {
            // As a constant, and as a witness minus zero.
            let mut cs = ConstraintSystem::new();
            m.enforce_zero(&mut cs, &Lazy::constant(&le(&value)));
            let bits = bit_vars(&mut cs, &le(&value));
            m.enforce_equal(&mut cs, &Lazy::from_bits(&bits), &Lazy::constant(&[0]));
            let (shape, z) = cs.finish();
            assert_eq!(shape.is_satisfied(&z), ok);
        }
    }

    #[test]
    #[should_panic(expected = "factor too wide")]
    fn operands_too_wide_for_the_field_are_refused_at_synthesis() {
        let m = Modulus::secp256k1_base();
        let mut cs = ConstraintSystem::new();
        let a = m.alloc(&mut cs, &[7; 32]);
        let wide = a.lazy().scale(1 << 20).scale(1 << 20);
        let _ = m.mul(&mut cs, &wide, &a.lazy());
    }

    #[test]
    fn canonical_check_separates_p_minus_one_from_p() {
        for (m, p) in [
            (Modulus::secp256k1_base(), SECP_P),
            (Modulus::curve25519_base(), ED_P),
        ] {
            let (pm1, _) = u256_sub(&p, &[1, 0, 0, 0]);
            let (pp1, _) = u256_add(&p, &[1, 0, 0, 0]);
            let top = if m.bits() == 256 {
                [u64::MAX; 4]
            } else {
                [u64::MAX, u64::MAX, u64::MAX, u64::MAX >> 1]
            };
            for (value, ok) in [
                ([0u64; 4], true),
                ([5, 0, 0, 0], true),
                (pm1, true),
                (p, false),
                (pp1, false),
                (top, false),
            ] {
                let mut cs = ConstraintSystem::new();
                let e = m.alloc(&mut cs, &le(&value));
                assert_eq!(eval_bytes(&cs, &e.bytes_le), le(&value));
                m.enforce_canonical(&mut cs, &e);
                let (shape, z) = cs.finish();
                assert_eq!(shape.is_satisfied(&z), ok);
            }
        }
    }

    #[test]
    fn le_const_agrees_with_integer_comparison() {
        for bound in [
            0u8, 1, 2, 0b011_1000, 0b101_0101, 0b111_0111, 63, 64, 77, 126, 127,
        ] {
            for x in 0u8..128 {
                let mut cs = ConstraintSystem::new();
                let bits: Vec<Lc> = (0..7)
                    .map(|i| cs.alloc(F::from_u64_reduced(((x >> i) & 1) as u64)).into())
                    .collect();
                enforce_le_const(&mut ctx(&mut cs), &bits, &[bound]);
                let (shape, z) = cs.finish();
                assert_eq!(shape.is_satisfied(&z), x <= bound, "x={x} bound={bound}");
            }
        }
    }

    #[test]
    fn scalar_range_gadgets_accept_exactly_one_to_order_minus_one() {
        let run = |secp: bool, k: U256| {
            let mut cs = ConstraintSystem::new();
            let bits = bit_vars(&mut cs, &le(&k));
            if secp {
                secp256k1_enforce_scalar_range(&mut cs, &bits);
            } else {
                ed25519_enforce_scalar_range(&mut cs, &bits);
            }
            let (shape, z) = cs.finish();
            shape.is_satisfied(&z)
        };
        let mut rng = Rng(4);
        for (secp, order) in [(true, SECP_N), (false, ED_L)] {
            let minus = |d: u64| u256_sub(&order, &[d, 0, 0, 0]).0;
            let plus = |d: u64| u256_add(&order, &[d, 0, 0, 0]).0;
            assert!(!run(secp, [0; 4]));
            assert!(run(secp, [1, 0, 0, 0]));
            assert!(run(secp, minus(2)));
            assert!(run(secp, minus(1)));
            assert!(!run(secp, order));
            assert!(!run(secp, plus(1)));
            assert!(!run(secp, [u64::MAX; 4]));
            for _ in 0..20 {
                let k = u256_from_bytes(&rng.bytes());
                let (_, borrow) = u256_sub(&k, &order);
                assert_eq!(run(secp, k), borrow == 1);
                // Values within a few low bits of the order.
                let near = [
                    order[0] ^ (rng.next() & 0xffff),
                    order[1],
                    order[2],
                    order[3],
                ];
                let (_, borrow) = u256_sub(&near, &order);
                assert_eq!(run(secp, near), borrow == 1);
            }
        }
    }

    fn secp_scalars() -> Vec<U256> {
        let mut rng = Rng(5);
        let n = SECP_N;
        let mut out = vec![
            [1, 0, 0, 0],
            [2, 0, 0, 0],
            u256_sub(&n, &[1, 0, 0, 0]).0,
            u256_sub(&n, &[2, 0, 0, 0]).0,
            // Zero windows almost everywhere.
            [0, 0, 0, 1 << 8],
            [0, 1 << 12, 0, 0],
            [0x0000_0fff_0000_0000, 0, 0, 0xf000_0000_0000_0000],
            // Above the order: the result is [k - n] G.
            [u64::MAX; 4],
            u256_add(&n, &[7, 0, 0, 0]).0,
            secp_doubling_scalar(),
        ];
        out.extend((0..4).map(|_| u256_from_bytes(&rng.bytes())));
        out
    }

    /// The scalar whose last addition has equal operands: `k_low = 2^256 - 1 - n` under the
    /// top window value 63.
    fn secp_doubling_scalar() -> U256 {
        let n = SECP_N;
        let low: U256 = core::array::from_fn(|i| !n[i]);
        u256_add(&low, &[0, 0, 0, 0xfc00_0000_0000_0000]).0
    }

    #[test]
    fn doubling_scalars_really_double_the_last_table_point() {
        with_secp256k1(|curve| {
            let f = &curve.f;
            let [tx, ty] = curve.windows.last().unwrap().points[63];
            let t = (f.mont(&big_from_bytes(&tx)), f.mont(&big_from_bytes(&ty)));
            let twice = curve.double(&t);
            let native = SecpPoint::generator_mul_ct(&be(&le(&secp_doubling_scalar())))
                .to_affine()
                .unwrap();
            assert_eq!(narrow(&f.canon(&twice.0)), native.0.normalize().0);
            assert_eq!(narrow(&f.canon(&twice.1)), native.1.normalize().0);
        });
    }

    #[test]
    fn secp256k1_fixed_base_matches_native_encodings() {
        for k in secp_scalars() {
            let native = SecpPoint::generator_mul_ct(&be(&le(&k)));
            let mut cs = ConstraintSystem::new();
            let bits = bit_vars(&mut cs, &le(&k));
            let pk = secp256k1_fixed_base_mul(&mut cs, &bits);
            let compressed = native.to_compressed_bytes().unwrap();
            let uncompressed = native.to_uncompressed_64().unwrap();
            assert_eq!(eval_bytes(&cs, &pk.compressed_bytes()), compressed);
            assert_eq!(eval_bit_bytes(&cs, &pk.compressed_bits()), compressed);
            assert_eq!(eval_bytes(&cs, &pk.uncompressed_bytes()), uncompressed);
            assert_eq!(eval_bit_bytes(&cs, &pk.uncompressed_bits()), uncompressed);
            assert_eq!(eval_bytes(&cs, &pk.x_only_bytes()), compressed[1..]);
            assert_eq!(eval_bit_bytes(&cs, &pk.x_only_bits()), compressed[1..]);
            let odd = cs.eval(&pk.y_is_odd()).to_canonical_u64();
            assert_eq!(odd as u8, compressed[0] & 1);
            pk.enforce_even_y(&mut cs);
            let (shape, z) = cs.finish();
            assert_eq!(shape.is_satisfied(&z), odd == 0, "k = {k:x?}");
        }
    }

    #[test]
    fn secp256k1_x_only_matches_native() {
        for k in [secp_scalars()[2], secp_scalars()[9], secp_scalars()[11]] {
            let native = SecpPoint::generator_mul_ct(&be(&le(&k)));
            let mut cs = ConstraintSystem::new();
            let bits = bit_vars(&mut cs, &le(&k));
            let x = secp256k1_fixed_base_mul_x_only(&mut cs, &bits);
            let mut got = eval_bytes(&cs, &x.bytes_le);
            got.reverse();
            assert_eq!(got, native.to_compressed_bytes().unwrap()[1..]);
            let (shape, z) = cs.finish();
            assert!(shape.is_satisfied(&z));
        }
    }

    /// Every private variable of the relation is pinned: changing any single one breaks it.
    fn assert_single_changes_rejected(shape: &Shape, z: &[F], seed: u64, samples: usize) {
        let mut rng = Rng(seed);
        for _ in 0..samples {
            let i = 1 + (rng.next() as usize) % (shape.mask_var_base - 1);
            let mut bad = z.to_vec();
            bad[i] += F::from_u64_reduced(1 + rng.next() % 3);
            assert!(!shape.is_satisfied(&bad), "variable {i} is free");
        }
    }

    #[test]
    fn secp256k1_rejects_tampered_witnesses_and_multiples_of_the_order() {
        let k = secp_scalars()[12];
        let mut cs = ConstraintSystem::new();
        let bits = bit_vars(&mut cs, &le(&k));
        let pk = secp256k1_fixed_base_mul(&mut cs, &bits);
        let outputs = [
            var_of(&pk.x.bits_le[0]),
            var_of(&pk.x.bits_le[100]),
            var_of(&pk.y.bits_le[0]),
            var_of(&pk.y.bytes_le[31]),
            var_of(&pk.x.bytes_le[0]),
        ];
        let (shape, z) = cs.finish();
        assert!(shape.is_satisfied(&z));
        for i in outputs {
            let mut bad = z.clone();
            bad[i] += F::ONE;
            assert!(!shape.is_satisfied(&bad));
            // A flipped bit that stays Boolean.
            let mut bad = z.clone();
            bad[i] = F::ONE - bad[i];
            assert!(!shape.is_satisfied(&bad));
        }
        assert_single_changes_rejected(&shape, &z, 6, 600);

        for k in [[0u64; 4], SECP_N] {
            let mut cs = ConstraintSystem::new();
            let bits = bit_vars(&mut cs, &le(&k));
            let _ = secp256k1_fixed_base_mul(&mut cs, &bits);
            let (other, z) = cs.finish();
            assert_eq!(other, shape, "row structure depends on the witness");
            assert!(!other.is_satisfied(&z));
        }
    }

    #[test]
    fn secp256k1_point_add_matches_native_including_doubling() {
        let m = Modulus::secp256k1_base();
        let affine = |k: u64| {
            let (x, y) = SecpPoint::generator_mul_ct(&be(&le(&[k, 0, 0, 0])))
                .to_affine()
                .unwrap();
            (x.normalize().0, y.normalize().0)
        };
        let neg = |p: (U256, U256)| (p.0, (-Fp256(p.1)).normalize().0);
        for (a, b, sum) in [
            (affine(5), affine(11), Some(affine(16))),
            (affine(9), affine(9), Some(affine(18))),
            (affine(3), neg(affine(1)), Some(affine(2))),
            (affine(7), neg(affine(7)), None),
        ] {
            let mut cs = ConstraintSystem::new();
            let point = |cs: &mut ConstraintSystem, p: (U256, U256)| AffinePoint {
                x: m.alloc(cs, &le(&p.0)).lazy(),
                y: m.alloc(cs, &le(&p.1)).lazy(),
            };
            let (pa, pb) = (point(&mut cs, a), point(&mut cs, b));
            let out = secp256k1_point_add(&mut cs, &pa, &pb);
            let got = (m.value(&cs, &out.x), m.value(&cs, &out.y));
            let (shape, z) = cs.finish();
            match sum {
                Some(want) => {
                    assert_eq!(got, (le(&want.0).to_vec(), le(&want.1).to_vec()));
                    assert!(shape.is_satisfied(&z));
                }
                None => assert!(!shape.is_satisfied(&z)),
            }
        }
    }

    fn ed_scalars() -> Vec<U256> {
        let mut rng = Rng(7);
        let mut out = vec![
            [1, 0, 0, 0],
            [8, 0, 0, 0],
            u256_sub(&ED_L, &[1, 0, 0, 0]).0,
            u256_add(&ED_L, &[1, 0, 0, 0]).0,
            // The last addition doubles: k_low = 2^250 - 1 under the top window value 0.
            [u64::MAX, u64::MAX, u64::MAX, u64::MAX >> 6],
            [0, 0, 1 << 20, 1 << 62],
            [u64::MAX; 4],
        ];
        out.extend((0..3).map(|_| u256_from_bytes(&rng.bytes())));
        out
    }

    #[test]
    fn ed25519_fixed_base_matches_native_encoding() {
        for k in ed_scalars() {
            let want = public_key_from_clamped_scalar(&le(&k));
            let mut cs = ConstraintSystem::new();
            let bits = bit_vars(&mut cs, &le(&k));
            let pk = ed25519_fixed_base_mul(&mut cs, &bits);
            assert_eq!(eval_bytes(&cs, &pk.encoding_bytes()), want);
            let enc_bits = pk.encoding_bits();
            let per_byte: Vec<[Lc; 8]> = (0..32)
                .map(|i| core::array::from_fn(|j| enc_bits[8 * i + j].clone()))
                .collect();
            assert_eq!(eval_bit_bytes(&cs, &per_byte), want);
            let (shape, z) = cs.finish();
            assert!(shape.is_satisfied(&z), "k = {k:x?}");
        }
    }

    #[test]
    fn ed25519_clamped_keys_match_native_and_tampering_is_rejected() {
        let mut rng = Rng(8);
        let mut shapes = Vec::new();
        for round in 0..3 {
            let raw = rng.bytes();
            let mut clamped = raw;
            clamped[0] &= 248;
            clamped[31] &= 127;
            clamped[31] |= 64;
            let want = public_key_from_clamped_scalar(&clamped);
            let mut cs = ConstraintSystem::new();
            let bits = ed25519_clamp(&bit_vars(&mut cs, &raw));
            let pk = ed25519_fixed_base_mul(&mut cs, &bits);
            assert_eq!(eval_bytes(&cs, &pk.encoding_bytes()), want);
            let outputs = [
                var_of(&pk.x_is_odd),
                var_of(&pk.y.bits_le[3]),
                var_of(&pk.y.bytes_le[31]),
            ];
            let (shape, z) = cs.finish();
            assert!(shape.is_satisfied(&z));
            if round == 0 {
                for i in outputs {
                    let mut bad = z.clone();
                    bad[i] = F::ONE - bad[i];
                    assert!(!shape.is_satisfied(&bad));
                }
                // Skip the scalar bits the clamp discards (variables 1..=256).
                let mut rng = Rng(9);
                for _ in 0..400 {
                    let i = 257 + (rng.next() as usize) % (shape.mask_var_base - 257);
                    let mut bad = z.clone();
                    bad[i] += F::ONE;
                    assert!(!shape.is_satisfied(&bad), "variable {i} is free");
                }
            }
            shapes.push(shape);
        }
        assert!(shapes.windows(2).all(|w| w[0] == w[1]));

        for k in [[0u64; 4], ED_L, u256_add(&ED_L, &ED_L).0] {
            let mut cs = ConstraintSystem::new();
            let bits = bit_vars(&mut cs, &le(&k));
            let _ = ed25519_fixed_base_mul(&mut cs, &bits);
            let (shape, z) = cs.finish();
            assert!(!shape.is_satisfied(&z));
        }
    }

    // ---- BLS12-381 G1 ------------------------------------------------------

    fn bls_scalars() -> Vec<U256> {
        let mut rng = Rng(11);
        let r = BLS_R;
        // The last addition doubles: k_low = 58 * 2^249 - 1 - r under the top window value 57.
        let doubling = u256_sub(&[u64::MAX, u64::MAX, u64::MAX, (115 << 57) - 1], &r).0;
        let mut out = vec![
            [1, 0, 0, 0],
            [2, 0, 0, 0],
            u256_sub(&r, &[1, 0, 0, 0]).0,
            doubling,
            [0, 0, 1 << 20, 1 << 60],
        ];
        out.extend((0..3).map(|_| {
            let mut k = u256_from_bytes(&rng.bytes());
            k[3] &= (1 << 62) - 1;
            k
        }));
        out
    }

    /// Compressed public keys of [`bls_scalars`], recorded from the constant-time native
    /// implementation `crate::bls12_381::BlsG1Point::generator_mul_ct(..).to_compressed_48()`
    /// (commit 661e5a8), which this module does not depend on.
    const BLS_VECTORS: [&str; 8] = [
        "97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb",
        "a572cbea904d67468808c8eb50a9450c9721db309128012543902d0ac358a62ae28f75bb8f1c7c42c39a8c5529bf0f4e",
        "b7f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb",
        "83abcb46d14b9b55848c30bc7b8afba5bd023ab3c2be1434b64b28df5acfceb6bf55bb8c02ef4adb0b781fef2c19747c",
        "965ca2ee2d4a16bb7894c9f1a93754fc4f8e3f5f0d0044148d52c365922982fdfcfbf5b5f4945b80fb41570afe3889a1",
        "a3011056d0cb7b38ed291a2c396c1fed3acb496c6aed45ff4474974a3ee8f519ff8239b200c228bb9426fc020b2b0c21",
        "b4b9d9caaba9000db3d2f077010c6eb827d1eaacb35edbc1b60755923511c2a34b9f8073d45d6885e0f0f60d44df359e",
        "80f1b9b03db910e1fbf1e29126270d11136b6cc640f6fbd5b66f78dc1be547a55b5f348d928e65eb3abe2a49427403a6",
    ];

    fn hex(bytes: &[u8]) -> std::string::String {
        bytes.iter().map(|b| std::format!("{b:02x}")).collect()
    }

    fn bits255(cs: &mut ConstraintSystem, k: &U256) -> Vec<Lc> {
        let mut bits = bit_vars(cs, &le(k));
        bits.truncate(255);
        bits
    }

    #[test]
    fn bls12_381_g1_matches_recorded_native_encodings() {
        assert_eq!(
            BLS_VECTORS[0],
            "97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb",
            "the generator's standard encoding"
        );
        let mut signs = [0usize; 2];
        for (k, want) in bls_scalars().iter().zip(BLS_VECTORS) {
            let mut cs = ConstraintSystem::new();
            let bits = bits255(&mut cs, k);
            let pk = bls12_381_g1_fixed_base_mul(&mut cs, &bits);
            assert_eq!(hex(&eval_bytes(&cs, &pk.compressed_bytes())), want);
            assert_eq!(hex(&eval_bit_bytes(&cs, &pk.compressed_bits())), want);
            // Double-and-add on the table-free group law, and the sign by comparison.
            with_bls12_381_g1(|curve| {
                let f = &curve.f;
                let g = (f.mont(&BLS_G1_X), f.mont(&BLS_G1_Y));
                let (x, y) = curve.scalar_mul(&big4(k), &g).unwrap();
                let (x, y) = (f.canon(&x), f.canon(&y));
                assert_eq!(eval_bytes(&cs, &pk.x.bytes_le), big_to_bytes(&x));
                assert_eq!(eval_bytes(&cs, &pk.y.bytes_le), big_to_bytes(&y));
                let (neg, _) = big_sub(&f.p, &y);
                let largest = big_sub(&neg, &y).1;
                assert_eq!(cs.eval(&pk.y_is_largest).to_canonical_u64(), largest);
                signs[largest as usize] += 1;
            });
            let outputs = [
                var_of(&pk.y_is_largest),
                var_of(&pk.x.bits_le[6]),
                var_of(&pk.x.bytes_le[47]),
            ];
            let (shape, z) = cs.finish();
            assert!(shape.is_satisfied(&z), "k = {k:x?}");
            for i in outputs {
                let mut bad = z.clone();
                bad[i] = F::ONE - bad[i];
                assert!(!shape.is_satisfied(&bad));
            }
        }
        assert!(signs[0] > 0 && signs[1] > 0, "both sign flags must occur");

        for k in [[0u64; 4], BLS_R] {
            let mut cs = ConstraintSystem::new();
            let bits = bits255(&mut cs, &k);
            let _ = bls12_381_g1_fixed_base_mul(&mut cs, &bits);
            let (shape, z) = cs.finish();
            assert!(!shape.is_satisfied(&z));
        }
    }

    #[test]
    fn bls12_381_scalar_range_accepts_exactly_one_to_r_minus_one() {
        let run = |k: U256| {
            let mut cs = ConstraintSystem::new();
            let bits = bits255(&mut cs, &k);
            bls12_381_enforce_scalar_range(&mut cs, &bits);
            let (shape, z) = cs.finish();
            shape.is_satisfied(&z)
        };
        let r = BLS_R;
        assert!(!run([0; 4]));
        assert!(run([1, 0, 0, 0]));
        assert!(run(u256_sub(&r, &[1, 0, 0, 0]).0));
        assert!(!run(r));
        assert!(!run(u256_add(&r, &[1, 0, 0, 0]).0));
        assert!(!run([u64::MAX, u64::MAX, u64::MAX, u64::MAX >> 1]));
        let mut rng = Rng(12);
        for _ in 0..20 {
            let near = [r[0] ^ (rng.next() & 0xffff), r[1], r[2], r[3]];
            assert_eq!(run(near), u256_sub(&near, &r).1 == 1);
        }
    }

    /// Shift-and-add reference on six words.
    fn ref_mulmod_big(a: &Big, b: &Big, p: &Big) -> Big {
        let reduce = |x: Big| {
            let (d, borrow) = big_sub(&x, p);
            if borrow == 0 { d } else { x }
        };
        let mut acc = [0u64; NW];
        for i in (0..64 * NW).rev() {
            acc = reduce(big_add(&acc, &acc).0);
            if (b[i / 64] >> (i % 64)) & 1 == 1 {
                acc = reduce(big_add(&acc, a).0);
            }
        }
        acc
    }

    #[test]
    fn field_mul_matches_reference_for_the_381_bit_field() {
        let m = Modulus::bls12_381_base();
        assert_eq!(m.bits(), 381);
        let mut rng = Rng(13);
        for round in 0..3 {
            let bytes = |rng: &mut Rng| {
                let mut v = [0u8; 48];
                v[..32].copy_from_slice(&rng.bytes());
                v[32..].copy_from_slice(&rng.bytes()[..16]);
                if round == 0 {
                    v = [0xff; 48];
                }
                v[47] &= 0x1f;
                v
            };
            let (a, b) = (bytes(&mut rng), bytes(&mut rng));
            let mut cs = ConstraintSystem::new();
            let (ea, eb) = (m.alloc(&mut cs, &a), m.alloc(&mut cs, &b));
            let c = m.mul(&mut cs, &ea.lazy(), &eb.lazy());
            m.enforce_canonical(&mut cs, &c);
            let reduced = |x: &[u8; 48]| ref_mulmod_big(&big_from_bytes(x), &big(1), &BLS_P);
            let want = ref_mulmod_big(&reduced(&a), &reduced(&b), &BLS_P);
            assert_eq!(eval_bytes(&cs, &c.bytes_le), big_to_bytes(&want));
            let (shape, z) = cs.finish();
            assert!(shape.is_satisfied(&z));
            for lc in [&c.bytes_le[0], &c.bytes_le[47], &c.bits_le[200]] {
                let mut bad = z.clone();
                bad[var_of(lc)] += F::ONE;
                assert!(!shape.is_satisfied(&bad));
            }
        }
    }

    // ---- Taproot and child keys ----------------------------------------------

    use crate::secp256k1_ct::{secp_scalar_add_mod_n, secp_scalar_neg_mod_n};

    fn native_affine(k_be: &[u8; 32]) -> ([u8; 32], [u8; 32]) {
        let (x, y) = SecpPoint::generator_mul_ct(k_be).to_affine().unwrap();
        (le(&x.normalize().0), le(&y.normalize().0))
    }

    #[test]
    fn taproot_tweak_matches_native_for_both_parities_and_the_exceptional_cases() {
        let mut rng = Rng(14);
        let mut parities = [0usize; 2];
        let mut cases: Vec<([u8; 32], [u8; 32], bool)> = Vec::new();
        for _ in 0..4 {
            let mut d = rng.bytes();
            let mut t = rng.bytes();
            d[31] &= 0x7f;
            t[31] &= 0x7f;
            cases.push((d, t, true));
        }
        // lift_x(P) = [t] G (a doubling) and lift_x(P) = -[t] G (the identity).
        let d = cases[0].0;
        let odd = native_affine(&be(&d)).1[0] & 1 == 1;
        let lifted_be = if odd {
            secp_scalar_neg_mod_n(&be(&d))
        } else {
            be(&d)
        };
        cases.push((d, be(&lifted_be), true));
        cases.push((d, be(&secp_scalar_neg_mod_n(&lifted_be)), false));
        cases.push((d, [0; 32], false));

        for (d, t, satisfiable) in cases {
            let (px, py) = native_affine(&be(&d));
            let odd = py[0] & 1 == 1;
            parities[odd as usize] += 1;
            let lifted = if odd {
                secp_scalar_neg_mod_n(&be(&d))
            } else {
                be(&d)
            };
            let q_scalar = secp_scalar_add_mod_n(&lifted, &be(&t));

            let mut cs = ConstraintSystem::new();
            let d_bits = bit_vars(&mut cs, &d);
            let t_bits = bit_vars(&mut cs, &t);
            let internal = secp256k1_fixed_base_mul(&mut cs, &d_bits);
            assert_eq!(eval_bytes(&cs, &internal.x.bytes_le), px);
            let q = secp256k1_taproot_tweak(&mut cs, &internal, &t_bits);
            let qx = secp256k1_taproot_tweak_x_only(&mut cs, &internal, &t_bits);
            if satisfiable {
                let want = SecpPoint::generator_mul_ct(&q_scalar)
                    .to_compressed_bytes()
                    .unwrap();
                assert_eq!(eval_bytes(&cs, &q.x_only_bytes()), want[1..]);
                assert_eq!(cs.eval(&q.y_is_odd()).to_canonical_u64() as u8, want[0] & 1);
                let mut x_only = eval_bytes(&cs, &qx.bytes_le);
                x_only.reverse();
                assert_eq!(x_only, want[1..]);
            }
            let out = var_of(&q.x.bits_le[1]);
            let (shape, z) = cs.finish();
            assert_eq!(shape.is_satisfied(&z), satisfiable);
            if satisfiable {
                let mut bad = z.clone();
                bad[out] = F::ONE - bad[out];
                assert!(!shape.is_satisfied(&bad));
            }
        }
        assert!(
            parities[0] > 0 && parities[1] > 0,
            "both parities of P must occur"
        );
    }

    #[test]
    fn add_fixed_base_matches_native_and_alloc_point_rejects_points_off_the_curve() {
        let mut rng = Rng(15);
        let mut k = rng.bytes();
        k[31] &= 0x7f;
        let mut i = rng.bytes();
        i[31] &= 0x7f;
        let minus_k = be(&secp_scalar_neg_mod_n(&be(&k)));
        for (step, satisfiable) in [(i, true), (k, true), (minus_k, false), ([0; 32], false)] {
            let (px, py) = native_affine(&be(&k));
            let mut cs = ConstraintSystem::new();
            let parent = secp256k1_alloc_point(&mut cs, &px, &py);
            let bits = bit_vars(&mut cs, &step);
            let child = secp256k1_add_fixed_base(&mut cs, &parent, &bits);
            if satisfiable {
                let sum = secp_scalar_add_mod_n(&be(&k), &be(&step));
                let want = SecpPoint::generator_mul_ct(&sum)
                    .to_compressed_bytes()
                    .unwrap();
                assert_eq!(eval_bytes(&cs, &child.compressed_bytes()), want);
            }
            let (shape, z) = cs.finish();
            assert_eq!(shape.is_satisfied(&z), satisfiable);
        }

        let (px, py) = native_affine(&be(&k));
        let mut off = py;
        off[0] ^= 1;
        let mut swapped = px;
        swapped[3] ^= 0x10;
        for (x, y, ok) in [
            (px, py, true),
            (px, off, false),
            (swapped, py, false),
            (py, px, false),
        ] {
            let mut cs = ConstraintSystem::new();
            let _ = secp256k1_alloc_point(&mut cs, &x, &y);
            let (shape, z) = cs.finish();
            assert_eq!(shape.is_satisfied(&z), ok);
        }
    }

    #[test]
    fn ed25519_add_fixed_base_matches_native_including_doubling() {
        let mut rng = Rng(16);
        let mut a = rng.bytes();
        a[31] &= 0x03;
        // BIP32-Ed25519 shape: the step is 8 Z_L for a 224-bit Z_L.
        let mut step = rng.bytes();
        step[0] &= 0xf8;
        step[28] &= 0x07;
        step[29..].fill(0);
        for b in [step, a] {
            let sum = u256_add(&u256_from_bytes(&a), &u256_from_bytes(&b)).0;
            let want = public_key_from_clamped_scalar(&le(&sum));
            let mut cs = ConstraintSystem::new();
            let (a_bits, b_bits) = (bit_vars(&mut cs, &a), bit_vars(&mut cs, &b));
            let parent = ed25519_fixed_base_mul(&mut cs, &a_bits);
            let child = ed25519_add_fixed_base(&mut cs, &parent, &b_bits);
            assert_eq!(eval_bytes(&cs, &child.encoding_bytes()), want);
            let out = var_of(&child.x_is_odd);
            let (shape, z) = cs.finish();
            assert!(shape.is_satisfied(&z));
            let mut bad = z.clone();
            bad[out] = F::ONE - bad[out];
            assert!(!shape.is_satisfied(&bad));
        }
        // a + (l - a) is the identity.
        let minus_a = u256_sub(&ED_L, &u256_from_bytes(&a)).0;
        let mut cs = ConstraintSystem::new();
        let (a_bits, b_bits) = (bit_vars(&mut cs, &a), bit_vars(&mut cs, &le(&minus_a)));
        let parent = ed25519_fixed_base_mul(&mut cs, &a_bits);
        let _ = ed25519_add_fixed_base(&mut cs, &parent, &b_bits);
        let (shape, z) = cs.finish();
        assert!(!shape.is_satisfied(&z));
    }

    #[test]
    fn integer_bits_is_an_exact_sum_and_rejects_overflow_and_forged_carries() {
        let mut rng = Rng(17);
        let (a, b) = (rng.bytes(), [0xff; 32]);
        let build = |width: usize| {
            let mut cs = ConstraintSystem::new();
            let (a_bits, b_bits) = (bit_vars(&mut cs, &a), bit_vars(&mut cs, &b));
            // a + 8 b, the shape of k_L + 8 Z_L.
            let sum = Lazy::from_bits(&a_bits).add(&Lazy::from_bits(&b_bits).scale(8));
            let mut metered = Metered::new(&mut cs, Options::default());
            let out = integer_bits(&mut metered, &sum, width);
            let hints = metered.hints;
            let value = eval_bytes(&cs, &out.bytes_le);
            let limb = var_of(&out.bytes_le[5]);
            let (shape, z) = cs.finish();
            (shape, z, value, limb, hints)
        };
        let (shape, z, value, limb, hints) = build(260);
        assert!(shape.is_satisfied(&z));
        let (lo, carry) = u256_add(&u256_from_bytes(&a), &[!7, u64::MAX, u64::MAX, u64::MAX]);
        // 8 * (2^256 - 1) = 2^259 - 8: low 256 bits are 2^256 - 8, plus 7 * 2^256.
        assert_eq!(value[..32], le(&lo));
        assert_eq!(value[32] as u64, 7 + carry);
        assert!(hints.carries > 0 && hints.quotients == 0);
        // Limb moved by one, with the neighbour compensating: only range rows object.
        let mut bad = z.clone();
        bad[limb] += F::from_u64_reduced(256);
        bad[limb + 8] -= F::ONE;
        let (range, other) = violated_rows(&shape, &bad);
        assert!(
            range >= 2 && other == 0,
            "{range} range rows, {other} others"
        );
        // A changed limb alone breaks the chain.
        let mut bad = z.clone();
        bad[limb] += F::ONE;
        assert!(!shape.is_satisfied(&bad));
        // Too narrow an output cannot hold the sum.
        let (shape, z, ..) = build(256);
        assert!(!shape.is_satisfied(&z));
    }

    #[test]
    fn hint_counts_and_product_only_comparisons() {
        let k = secp_scalars()[11];
        let build = |options: Options| {
            let mut cs = ConstraintSystem::new();
            let bits = bit_vars(&mut cs, &le(&k));
            let mut metered = Metered::new(&mut cs, options);
            secp256k1_enforce_scalar_range(&mut metered, &bits);
            let pk = secp256k1_fixed_base_mul(&mut metered, &bits);
            let hints = metered.hints;
            let bytes = eval_bytes(&cs, &pk.compressed_bytes());
            let rows = cs.num_rows();
            let (shape, z) = cs.finish();
            assert!(shape.is_satisfied(&z));
            (hints, bytes, rows, shape.num_vars)
        };
        let (plain, bytes, rows, vars) = build(Options::default());
        let (strict, strict_bytes, strict_rows, _) = build(Options {
            product_only_comparisons: true,
        });
        assert_eq!(bytes, strict_bytes);
        // 24 windows: 23 additions with a slope and an x each, plus the final y.
        assert_eq!((plain.elements, plain.divisions), (47, 23));
        assert_eq!(plain.element_bits, 47 * 256);
        // Two reductions per addition, the tangent equation, the final y.
        assert_eq!(plain.quotients, 48);
        assert!(plain.zero_tests > 0);
        assert_eq!(strict.zero_tests, 0);
        assert_eq!(
            (strict.elements, strict.quotient_bits, strict.carry_bits),
            (plain.elements, plain.quotient_bits, plain.carry_bits)
        );
        assert!(strict_rows > rows && strict_rows * 2 < rows * 3);
        // Every variable that is not a hint is a product or a linear image of products.
        assert!(plain.variables() < vars);
        println!("secp256k1 mul + range: {plain:?}; product-only rows {strict_rows} vs {rows}");
    }

    #[test]
    #[ignore = "measurement"]
    fn row_census() {
        let mut rng = Rng(10);
        let report = |name: &str, build: &dyn Fn(&mut ConstraintSystem)| {
            let mut cs = ConstraintSystem::new();
            let start = std::time::Instant::now();
            build(&mut cs);
            let synthesis = start.elapsed();
            let rows = cs.num_rows();
            let (shape, z) = cs.finish();
            assert!(shape.is_satisfied(&z));
            println!(
                "{name}: rows={rows} vars={} nnz={} synthesis={synthesis:?}",
                shape.num_vars,
                shape.a.nnz() + shape.b.nnz() + shape.c.nnz(),
            );
        };
        let (a, b) = (rng.bytes(), rng.bytes());
        let k = rng.bytes();
        let m = Modulus::secp256k1_base();
        let operands = |cs: &mut ConstraintSystem| {
            // Operand allocation, subtracted below.
            (m.alloc(cs, &a), m.alloc(cs, &b))
        };
        report("two operand allocations (overhead)", &|cs| {
            let _ = operands(cs);
        });
        report("non-native mul incl. operand allocations", &|cs| {
            let (ea, eb) = operands(cs);
            let _ = m.mul(cs, &ea.lazy(), &eb.lazy());
        });
        let affine = |s: u64| {
            let (x, y) = SecpPoint::generator_mul_ct(&be(&le(&[s, 0, 0, 0])))
                .to_affine()
                .unwrap();
            (le(&x.normalize().0), le(&y.normalize().0))
        };
        let (p, q) = (affine(5), affine(11));
        report("four coordinate allocations (overhead)", &|cs| {
            for v in [&p.0, &p.1, &q.0, &q.1] {
                let _ = m.alloc(cs, v);
            }
        });
        report(
            "complete point addition incl. coordinate allocations",
            &|cs| {
                let pa = AffinePoint {
                    x: m.alloc(cs, &p.0).lazy(),
                    y: m.alloc(cs, &p.1).lazy(),
                };
                let pb = AffinePoint {
                    x: m.alloc(cs, &q.0).lazy(),
                    y: m.alloc(cs, &q.1).lazy(),
                };
                let _ = secp256k1_point_add(cs, &pa, &pb);
            },
        );
        report("256 scalar bits (overhead)", &|cs| {
            let _ = bit_vars(cs, &k);
        });
        report(
            "secp256k1 fixed-base mul, x and y, incl. scalar bits",
            &|cs| {
                let bits = bit_vars(cs, &k);
                let _ = secp256k1_fixed_base_mul(cs, &bits);
            },
        );
        report(
            "secp256k1 fixed-base mul, x only, incl. scalar bits",
            &|cs| {
                let bits = bit_vars(cs, &k);
                let _ = secp256k1_fixed_base_mul_x_only(cs, &bits);
            },
        );
        report("ed25519 fixed-base mul incl. scalar bits", &|cs| {
            let bits = ed25519_clamp(&bit_vars(cs, &k));
            let _ = ed25519_fixed_base_mul(cs, &bits);
        });
        report("255 scalar bits (overhead)", &|cs| {
            let _ = bits255(cs, &u256_from_bytes(&k));
        });
        report("bls12-381 g1 fixed-base mul incl. scalar bits", &|cs| {
            let mut scalar = u256_from_bytes(&k);
            scalar[3] &= (1 << 62) - 1;
            let bits = bits255(cs, &scalar);
            let _ = bls12_381_g1_fixed_base_mul(cs, &bits);
        });
        let (px, py) = native_affine(&be(&[9; 32]));
        report("secp256k1 alloc_point (curve membership)", &|cs| {
            let _ = secp256k1_alloc_point(cs, &px, &py);
        });
        report(
            "secp256k1 add_fixed_base incl. alloc_point and scalar bits",
            &|cs| {
                let parent = secp256k1_alloc_point(cs, &px, &py);
                let bits = bit_vars(cs, &k);
                let _ = secp256k1_add_fixed_base(cs, &parent, &bits);
            },
        );
        report(
            "secp256k1 taproot_tweak incl. alloc_point and tweak bits",
            &|cs| {
                let internal = secp256k1_alloc_point(cs, &px, &py);
                let bits = bit_vars(cs, &k);
                let _ = secp256k1_taproot_tweak(cs, &internal, &bits);
            },
        );
        report(
            "secp256k1 taproot_tweak_x_only incl. alloc_point and tweak bits",
            &|cs| {
                let internal = secp256k1_alloc_point(cs, &px, &py);
                let bits = bit_vars(cs, &k);
                let _ = secp256k1_taproot_tweak_x_only(cs, &internal, &bits);
            },
        );
        report(
            "ed25519 parent mul + add_fixed_base incl. 512 scalar bits",
            &|cs| {
                let a = ed25519_clamp(&bit_vars(cs, &k));
                let b = ed25519_clamp(&bit_vars(cs, &k));
                let parent = ed25519_fixed_base_mul(cs, &a);
                let _ = ed25519_add_fixed_base(cs, &parent, &b);
            },
        );
        let hints = |name: &str, build: &dyn Fn(&mut Metered)| {
            let mut cs = ConstraintSystem::new();
            let mut metered = Metered::new(&mut cs, Options::default());
            build(&mut metered);
            let hints = metered.hints;
            let rows = cs.num_rows();
            let bit_rows = hints.element_bits + hints.quotient_bits + hints.carry_bits;
            println!(
                "hints {name}: {hints:?}; with a range row type: {} rows + {} lookups (now {rows} rows)",
                rows - bit_rows,
                hints.range_lookups,
            );
        };
        hints("non-native mul", &|m| {
            let (ea, eb) = (
                Modulus::secp256k1_base().alloc(m, &a),
                Modulus::secp256k1_base().alloc(m, &b),
            );
            let before = m.hints;
            let _ = Modulus::secp256k1_base().mul(m, &ea.lazy(), &eb.lazy());
            m.hints.elements -= before.elements;
            m.hints.element_bits -= before.element_bits;
        });
        hints("secp256k1 fixed-base mul", &|m| {
            let bits = bit_vars(m.cs, &k);
            let _ = secp256k1_fixed_base_mul(m, &bits);
        });
        hints("ed25519 fixed-base mul", &|m| {
            let bits = bit_vars(m.cs, &k);
            let _ = ed25519_fixed_base_mul(m, &ed25519_clamp(&bits));
        });
        hints("bls12-381 g1 fixed-base mul", &|m| {
            let mut scalar = u256_from_bytes(&k);
            scalar[3] &= (1 << 62) - 1;
            let bits = bits255(m.cs, &scalar);
            let _ = bls12_381_g1_fixed_base_mul(m, &bits);
        });
        hints("secp256k1 taproot_tweak", &|m| {
            let internal = secp256k1_alloc_point(m, &px, &py);
            let before = m.hints;
            let bits = bit_vars(m.cs, &k);
            let _ = secp256k1_taproot_tweak(m, &internal, &bits);
            m.hints.elements -= before.elements;
            m.hints.element_bits -= before.element_bits;
            m.hints.quotients -= before.quotients;
        });

        let start = std::time::Instant::now();
        let fresh = Curve::secp256k1();
        println!(
            "secp256k1 window tables: {} points, built in {:?}",
            fresh.windows.iter().map(|w| w.points.len()).sum::<usize>(),
            start.elapsed()
        );
        with_secp256k1(|curve| {
            let mut cs = ConstraintSystem::new();
            let bits = bit_vars(&mut cs, &k);
            let before = cs.num_rows();
            let table = &curve.windows[1];
            let _ = window_point(
                &mut ctx(&mut cs),
                table,
                &bits[table.lo..table.lo + table.width],
            );
            println!(
                "one 11-bit signed window lookup: rows={}",
                cs.num_rows() - before
            );
        });
    }
}
