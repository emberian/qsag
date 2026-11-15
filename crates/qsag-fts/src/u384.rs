//! Constant-time fixed-width 384-bit unsigned integer (`U384`, six `u64` little-endian limbs)
//! supporting DP combinatorics up to 384 bits without heap allocation or data-dependent branches.

use qsag_accel::ct::{ct_eq_u64, ct_select_u64};

/// Fixed-width 384-bit unsigned integer in little-endian `u64` limb order.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct U384(pub [u64; 6]);

impl U384 {
    pub const ZERO: Self = Self([0; 6]);
    pub const ONE: Self = Self([1, 0, 0, 0, 0, 0]);

    #[inline]
    pub const fn from_u64(v: u64) -> Self {
        Self([v, 0, 0, 0, 0, 0])
    }

    #[inline]
    pub const fn from_u128(v: u128) -> Self {
        Self([v as u64, (v >> 64) as u64, 0, 0, 0, 0])
    }

    #[inline]
    pub const fn low_u128(self) -> u128 {
        (self.0[0] as u128) | ((self.0[1] as u128) << 64)
    }

    #[inline]
    pub fn is_zero(self) -> bool {
        let folded = self.0[0] | self.0[1] | self.0[2] | self.0[3] | self.0[4] | self.0[5];
        ct_eq_u64(folded, 0)
    }

    /// Constant-time branchless conditional select: `choice ? if_true : if_false`.
    #[inline]
    pub const fn ct_select(choice: bool, if_true: Self, if_false: Self) -> Self {
        Self([
            ct_select_u64(choice, if_true.0[0], if_false.0[0]),
            ct_select_u64(choice, if_true.0[1], if_false.0[1]),
            ct_select_u64(choice, if_true.0[2], if_false.0[2]),
            ct_select_u64(choice, if_true.0[3], if_false.0[3]),
            ct_select_u64(choice, if_true.0[4], if_false.0[4]),
            ct_select_u64(choice, if_true.0[5], if_false.0[5]),
        ])
    }

    /// Checked addition returning `(sum, carry_out)`.
    #[inline]
    pub const fn overflowing_add(self, rhs: Self) -> (Self, bool) {
        let mut out = [0u64; 6];
        let mut carry = 0u128;
        let mut i = 0usize;
        while i < 6 {
            let s = (self.0[i] as u128) + (rhs.0[i] as u128) + carry;
            out[i] = s as u64;
            carry = s >> 64;
            i += 1;
        }
        (Self(out), carry != 0)
    }

    #[inline]
    pub const fn checked_add(self, rhs: Self) -> Option<Self> {
        let (res, over) = self.overflowing_add(rhs);
        if over { None } else { Some(res) }
    }

    /// Branchless subtraction returning `(diff, borrow_out)`. `borrow_out == true` iff `self < rhs`.
    #[inline]
    pub const fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
        let mut ct_out = [0u64; 6];
        let mut br = 0u64;
        let mut k = 0usize;
        while k < 6 {
            let (d1, b1) = self.0[k].overflowing_sub(rhs.0[k]);
            let (d2, b2) = d1.overflowing_sub(br);
            ct_out[k] = d2;
            br = (b1 as u64) | (b2 as u64);
            k += 1;
        }
        (Self(ct_out), br != 0)
    }

    /// Branchless strict less-than `self < rhs`.
    #[inline]
    pub const fn ct_lt(self, rhs: Self) -> bool {
        self.overflowing_sub(rhs).1
    }

    /// Branchless `self <= rhs`.
    #[inline]
    pub const fn ct_le(self, rhs: Self) -> bool {
        !rhs.ct_lt(self)
    }

    /// Checked 384x384 -> 384 multiplication (ensuring high limbs 6..12 are zero).
    pub const fn checked_mul(self, rhs: Self) -> Option<Self> {
        let mut prod = [0u64; 12];
        let mut i = 0usize;
        while i < 6 {
            let mut carry = 0u128;
            let mut j = 0usize;
            while j < 6 {
                let cur = (prod[i + j] as u128) + (self.0[i] as u128) * (rhs.0[j] as u128) + carry;
                prod[i + j] = cur as u64;
                carry = cur >> 64;
                j += 1;
            }
            prod[i + 6] = prod[i + 6].wrapping_add(carry as u64);
            i += 1;
        }
        let mut k = 6usize;
        while k < 12 {
            if prod[k] != 0 {
                return None;
            }
            k += 1;
        }
        Some(Self([prod[0], prod[1], prod[2], prod[3], prod[4], prod[5]]))
    }

    /// Wrapping 384x384 -> 384 multiplication (branchless).
    #[inline]
    pub const fn wrapping_mul(self, rhs: Self) -> Self {
        let mut prod = [0u64; 6];
        let mut i = 0usize;
        while i < 6 {
            let mut carry = 0u128;
            let mut j = 0usize;
            while i + j < 6 {
                let cur = (prod[i + j] as u128) + (self.0[i] as u128) * (rhs.0[j] as u128) + carry;
                prod[i + j] = cur as u64;
                carry = cur >> 64;
                j += 1;
            }
            i += 1;
        }
        Self(prod)
    }

    #[inline]
    const fn shl1_with_lsb(self, lsb: bool) -> Self {
        let mut out = [0u64; 6];
        let mut carry = lsb as u64;
        let mut i = 0usize;
        while i < 6 {
            let next_carry = self.0[i] >> 63;
            out[i] = (self.0[i] << 1) | carry;
            carry = next_carry;
            i += 1;
        }
        Self(out)
    }

    #[inline]
    const fn bit_at(self, bit_idx: usize) -> bool {
        let limb = bit_idx / 64;
        let off = bit_idx % 64;
        ((self.0[limb] >> off) & 1) == 1
    }

    #[inline]
    const fn set_bit(mut self, bit_idx: usize, val: bool) -> Self {
        let limb = bit_idx / 64;
        let off = bit_idx % 64;
        let mask = 1u64 << off;
        let cleared = self.0[limb] & !mask;
        let set = self.0[limb] | mask;
        self.0[limb] = ct_select_u64(val, set, cleared);
        self
    }

    /// 100% constant-time fixed-384-iteration restoring binary `divmod(self, divisor)`.
    /// Performs zero data-dependent branches and zero hardware `div` instructions!
    pub fn ct_divmod(self, divisor: Self) -> (Self, Self) {
        assert!(!divisor.is_zero(), "U384 division by zero");
        let mut quot = Self::ZERO;
        let mut rem = Self::ZERO;
        let mut bit = 384usize;
        while bit > 0 {
            bit -= 1;
            let in_bit = self.bit_at(bit);
            rem = rem.shl1_with_lsb(in_bit);
            let (diff, borrow) = rem.overflowing_sub(divisor);
            let ge = !borrow;
            rem = Self::ct_select(ge, diff, rem);
            quot = quot.set_bit(bit, ge);
        }
        (quot, rem)
    }

    /// Read the top `r_bits` (`1 <= r_bits <= 384`) from big-endian byte stream `bytes`.
    pub fn from_top_bits_be(bytes: &[u8], r_bits: usize) -> Self {
        assert!((1..=384).contains(&r_bits));
        let needed_bytes = r_bits.div_ceil(8);
        assert!(bytes.len() >= needed_bytes);
        let mut acc = Self::ZERO;
        for bit_pos in 0..r_bits {
            let byte_idx = bit_pos / 8;
            let bit_in_byte = 7 - (bit_pos % 8);
            let b = ((bytes[byte_idx] >> bit_in_byte) & 1) == 1;
            acc = acc.shl1_with_lsb(b);
        }
        acc
    }

    /// Bit length (`0` for `ZERO`, `1..=384` otherwise; used on public DP cardinality `M`).
    pub fn public_bit_len(self) -> usize {
        for limb_idx in (0..6).rev() {
            let v = self.0[limb_idx];
            if v != 0 {
                return limb_idx * 64 + (64 - v.leading_zeros() as usize);
            }
        }
        0
    }
}
