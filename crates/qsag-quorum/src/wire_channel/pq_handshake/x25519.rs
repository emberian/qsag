//! RFC 7748 Montgomery ladder over five radix-2^51 limbs.

use super::TransportError;
use qsag_core::wipe::{SecretBuffer, SecretBytes, ct_eq_bytes32};

type Field = [u64; 5];
const MASK: u64 = (1 << 51) - 1;
const ONE: Field = [1, 0, 0, 0, 0];
pub(super) const BASE: [u8; 32] = {
    let mut u = [0; 32];
    u[0] = 9;
    u
};

fn reduce(mut t: [u128; 5]) -> Field {
    for _ in 0..3 {
        for i in 0..4 {
            t[i + 1] += t[i] >> 51;
            t[i] &= u128::from(MASK);
        }
        t[0] += 19 * (t[4] >> 51);
        t[4] &= u128::from(MASK);
    }
    t.map(|x| x as u64)
}

fn add(a: Field, b: Field) -> Field {
    reduce(core::array::from_fn(|i| u128::from(a[i] + b[i])))
}

fn sub(a: Field, b: Field) -> Field {
    let twice_p = [2 * (MASK - 18), 2 * MASK, 2 * MASK, 2 * MASK, 2 * MASK];
    reduce(core::array::from_fn(|i| {
        u128::from(a[i] + twice_p[i] - b[i])
    }))
}

fn mul(a: Field, b: Field) -> Field {
    let mut t = [0u128; 5];
    for (i, x) in a.into_iter().enumerate() {
        for (j, y) in b.into_iter().enumerate() {
            let k = i + j;
            let term = u128::from(x) * u128::from(y);
            if k >= 5 {
                t[k - 5] += 19 * term;
            } else {
                t[k] += term;
            }
        }
    }
    reduce(t)
}

fn swap(a: &mut Field, b: &mut Field, bit: u8) {
    let mask = 0u64.wrapping_sub(core::hint::black_box(u64::from(bit)));
    for (x, y) in a.iter_mut().zip(b) {
        let change = mask & (*x ^ *y);
        *x ^= change;
        *y ^= change;
    }
}

fn encode(mut x: Field) -> [u8; 32] {
    // Carry from x + 19 selects x - p for the noncanonical representatives.
    let mut reduced = x;
    let mut carry = 19;
    for limb in &mut reduced {
        let v = *limb + carry;
        *limb = v & MASK;
        carry = v >> 51;
    }
    swap(&mut x, &mut reduced, carry as u8);
    let mut out = [0; 32];
    for i in 0..255 {
        out[i >> 3] |= (((x[i / 51] >> (i % 51)) & 1) as u8) << (i & 7);
    }
    out
}

pub(super) fn exchange(
    private: &[u8; 32],
    public: &[u8; 32],
) -> Result<SecretBytes<32>, TransportError> {
    let mut k = SecretBuffer(*private);
    k[0] &= 248;
    k[31] &= 127;
    k[31] |= 64;
    let mut u = [0; 5];
    for i in 0..255 {
        u[i / 51] |= u64::from((public[i >> 3] >> (i & 7)) & 1) << (i % 51);
    }
    let (mut x2, mut z2, mut x3, mut z3) = (ONE, [0; 5], u, ONE);
    let mut last = 0;
    for i in (0..255).rev() {
        let bit = (k[i >> 3] >> (i & 7)) & 1;
        swap(&mut x2, &mut x3, last ^ bit);
        swap(&mut z2, &mut z3, last ^ bit);
        last = bit;
        let a = add(x2, z2);
        let aa = mul(a, a);
        let b = sub(x2, z2);
        let bb = mul(b, b);
        let e = sub(aa, bb);
        let da = mul(sub(x3, z3), a);
        let cb = mul(add(x3, z3), b);
        let sum = add(da, cb);
        let diff = sub(da, cb);
        x3 = mul(sum, sum);
        z3 = mul(u, mul(diff, diff));
        x2 = mul(aa, bb);
        z2 = mul(e, add(aa, mul([121665, 0, 0, 0, 0], e)));
    }
    swap(&mut x2, &mut x3, last);
    swap(&mut z2, &mut z3, last);
    let mut inv = ONE;
    // Public exponent 2^255 - 21 has all bits set except bits two and four.
    for i in (0..255).rev() {
        inv = mul(inv, inv);
        if i != 2 && i != 4 {
            inv = mul(inv, z2);
        }
    }
    let out = SecretBuffer(encode(mul(x2, inv)));
    for limb in [&mut x2, &mut z2, &mut x3, &mut z3, &mut inv] {
        qsag_core::wipe::wipe_u64s(limb);
    }
    if ct_eq_bytes32(&out, &[0; 32]) {
        Err(TransportError::AuthenticationFailed)
    } else {
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn hex(s: &str) -> [u8; 32] {
        core::array::from_fn(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap())
    }

    #[test]
    fn rfc7748_alice_and_bob() {
        let alice = hex("77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a");
        let bob = hex("5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb");
        let ap = exchange(&alice, &BASE).unwrap();
        let bp = exchange(&bob, &BASE).unwrap();
        assert_eq!(
            *ap,
            hex("8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a")
        );
        let expected = hex("4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742");
        assert_eq!(*exchange(&alice, &bp).unwrap(), expected);
        assert_eq!(*exchange(&bob, &ap).unwrap(), expected);
        assert!(matches!(
            exchange(&alice, &[0; 32]),
            Err(TransportError::AuthenticationFailed)
        ));
    }
}
