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

