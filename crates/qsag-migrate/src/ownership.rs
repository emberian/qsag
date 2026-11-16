//! Ownership of the canonical spending scalar, including Taproot output scalars.
use crate::{
    boolean_hash,
    circuit::{Builder, Circuit, Domain, Value, Wire, ZERO},
    legacy::LegacyCommitmentKind,
    scalar::{self, ScalarGroup},
    zk_engine::MigrationStatement,
};
use alloc::vec::Vec;
use qsag_accel::poseidon2::{POSEIDON2_CONST_IV, poseidon2_const_at};

type Point = [Wire; 4];
fn secp_add(c: &Builder, a: Point, b: Point) -> Point {
    let mut t0 = c.mul(a[0], b[0]);
    let mut t1 = c.mul(a[1], b[1]);
    let zz = c.mul(a[2], b[2]);
    let t2 = c.scale(zz, 21);
    let t3 = c.sub(c.mul(c.add(a[0], a[1]), c.add(b[0], b[1])), c.add(t0, t1));
    let t4 = c.sub(c.mul(c.add(a[1], a[2]), c.add(b[1], b[2])), c.add(t1, zz));
    let cross = c.scale(
        c.sub(c.mul(c.add(a[0], a[2]), c.add(b[0], b[2])), c.add(t0, zz)),
        21,
    );
    t0 = c.scale(t0, 3);
    let z = c.add(t1, t2);
    t1 = c.sub(t1, t2);
    [
        c.sub(c.mul(t3, t1), c.mul(t4, cross)),
        c.add(c.mul(t1, z), c.mul(cross, t0)),
        c.add(c.mul(z, t4), c.mul(t0, t3)),
        a[3],
    ]
}
fn ed_add(c: &Builder, a: Point, b: Point) -> Point {
    let aa = c.mul(c.sub(a[1], a[0]), c.sub(b[1], b[0]));
    let bb = c.mul(c.add(a[1], a[0]), c.add(b[1], b[0]));
    let twice_d = c.constant(
        Domain::Ed,
        [
            0xebd6_9b94_26b2_f159,
            0x00e0_149a_8283_b156,
            0x198e_80f2_eef3_d130,
            0x2406_d9dc_56df_fce7,
        ],
    );
    let cc = c.mul(c.mul(a[3], b[3]), twice_d);
    let dd = c.scale(c.mul(a[2], b[2]), 2);
    let e = c.sub(bb, aa);
    let f = c.sub(dd, cc);
    let g = c.add(dd, cc);
    let h = c.add(bb, aa);
    [c.mul(e, f), c.mul(g, h), c.mul(f, g), c.mul(e, h)]
}
/// Public fixed-base tables, built outside all repetition simulations. A single
/// batch inversion normalizes all nonidentity entries to affine/extended form.
fn window_tables(ed: bool) -> Vec<[[Value; 4]; 16]> {
    let d = if ed { Domain::Ed } else { Domain::Secp };
    let native = if ed {
        crate::ed25519_ct::circuit_base_table()
    } else {
        crate::secp256k1_ct::GENERATOR_TABLE.map(|p| [p[0], p[1], p[2], ZERO])
    };
    let constants = Builder::default();
    let add = |a, b| {
        if ed {
            ed_add(&constants, a, b)
        } else {
            secp_add(&constants, a, b)
        }
    };
    let identity = native[0].map(|v| constants.constant(d, v));
    let mut base = native[1].map(|v| constants.constant(d, v));
    let mut tables = Vec::with_capacity(64);
    for _ in 0..64 {
        let mut p = identity;
        let table = core::array::from_fn(|v| {
            if v != 0 {
                p = add(p, base);
            }
            p.map(|w| constants.value(w))
        });
        tables.push(table);
        for _ in 0..4 {
            base = add(base, base);
        }
    }
    let mut prefixes = Vec::with_capacity(64 * 15);
    let mut product = [1, 0, 0, 0];
    for table in &tables {
        for p in &table[1..] {
            prefixes.push(product);
            product = d.mul(product, p[2]);
        }
    }
    let mut inverse = d.inverse(product);
    for table in tables.iter_mut().rev() {
        for p in table[1..].iter_mut().rev() {
            let z_inv = d.mul(inverse, prefixes.pop().unwrap());
            inverse = d.mul(inverse, p[2]);
            p[0] = d.mul(p[0], z_inv);
            p[1] = d.mul(p[1], z_inv);
            p[2] = [1, 0, 0, 0];
            if ed {
                p[3] = d.mul(p[0], p[1]);
            }
        }
    }
    tables
}
fn curve(c: &Builder, bits: &[Wire], ed: bool) -> (Vec<Wire>, Vec<Wire>) {
    let domain = if ed { Domain::Ed } else { Domain::Secp };
    let tables = window_tables(ed);
    let one = c.small(domain, 1);
    let pairs = |a, b| {
        let ab = c.mul(a, b);
        let a_only = c.sub(a, ab);
        let b_only = c.sub(b, ab);
        [c.sub(c.sub(one, a_only), b), a_only, b_only, ab]
    };
    let mut acc = None;
    for (nibble, table) in bits.chunks_exact(4).zip(tables) {
        let b: [Wire; 4] = core::array::from_fn(|i| c.lift(nibble[i], domain));
        let lo = pairs(b[0], b[1]);
        let hi = pairs(b[2], b[3]);
        let mut sel = [c.small(domain, 0); 16];
        // Nine outer products suffice: each row/column sums to its pair basis.
        for j in 0..3 {
            for i in 0..3 {
                sel[j * 4 + i] = c.mul(lo[i], hi[j]);
            }
            sel[j * 4 + 3] = c.sub(
                hi[j],
                c.add(c.add(sel[j * 4], sel[j * 4 + 1]), sel[j * 4 + 2]),
            );
        }
        for i in 0..4 {
            sel[12 + i] = c.sub(lo[i], c.add(c.add(sel[i], sel[4 + i]), sel[8 + i]));
        }
        let point = core::array::from_fn(|i| {
            if i == 2 {
                if ed {
                    debug_assert!(table.iter().all(|p| p[2] == [1, 0, 0, 0]));
                    return one;
                }
                debug_assert!(
                    table[0][2] == ZERO && table[1..].iter().all(|p| p[2] == [1, 0, 0, 0])
                );
                return c.sub(one, sel[0]);
            }
            if !ed && i == 3 {
                return c.small(domain, 0);
            }
            sel.iter()
                .zip(&table)
                .fold(c.small(domain, 0), |sum, (&w, p)| {
                    c.add(sum, c.mul(w, c.constant(domain, p[i])))
                })
        });
        acc = Some(match acc {
            None => point,
            Some(a) => {
                if ed {
                    ed_add(c, a, point)
                } else {
                    secp_add(c, a, point)
                }
            }
        });
    }
    let acc = acc.unwrap();
    let inv = c.inverse(acc[2]);
    let mut x = c.bits(c.mul(acc[0], inv));
    let mut y = c.bits(c.mul(acc[1], inv));
    x.resize(256, c.small(Domain::Bit, 0));
    y.resize(256, c.small(Domain::Bit, 0));
    (x, y)
}
fn big_endian(bits: &[Wire]) -> Vec<Wire> {
    bits.chunks_exact(8).rev().flatten().copied().collect()
}
fn me(c: &Builder, st: &mut [Wire; 12]) {
    // M4 tensor P3: transpose lanes, apply P3 tensor M4, transpose back.
    *st = [
        st[0], st[3], st[6], st[9], st[1], st[4], st[7], st[10], st[2], st[5], st[8], st[11],
    ];
    let mut ys = *st;
    for row in ys.chunks_exact_mut(4) {
        let old: [Wire; 4] = core::array::from_fn(|i| row[i]);
        let s = old.iter().copied().reduce(|a, b| c.add(a, b)).unwrap();
        for (i, x) in row.iter_mut().enumerate() {
            *x = c.add(s, c.add(old[i], c.scale(old[(i + 1) % 4], 2)));
        }
    }
    for (i, x) in st.iter_mut().enumerate() {
        *x = c.add(ys[i], c.add(c.add(ys[i % 4], ys[i % 4 + 4]), ys[i % 4 + 8]));
    }
    *st = [
        st[0], st[4], st[8], st[1], st[5], st[9], st[2], st[6], st[10], st[3], st[7], st[11],
    ];
}
fn mi(c: &Builder, st: &mut [Wire; 12]) {
    let s = st.iter().copied().reduce(|a, b| c.add(a, b)).unwrap();
    st[0] = c.sub(s, c.scale(st[0], 64));
    st[1] = c.add(s, st[1]);
    for (i, x) in st.iter_mut().enumerate().skip(2) {
        *x = c.add(s, c.scale(*x, 1 << (i - 1)));
    }
}
fn sbox(c: &Builder, x: Wire, rc: u64) -> Wire {
    let x = c.add(x, c.small(Domain::Gold, rc));
    let x2 = c.mul(x, x);
    let x3 = c.mul(x2, x);
    let x4 = c.mul(x2, x2);
    c.mul(x3, x4)
}
fn perm(c: &Builder, st: &mut [Wire; 12]) {
    me(c, st);
    for r in 0..4 {
        for (i, x) in st.iter_mut().enumerate() {
            *x = sbox(c, *x, poseidon2_const_at(0, r, i as u64));
        }
        me(c, st);
    }
    for r in 0..22 {
        st[0] = sbox(c, st[0], poseidon2_const_at(1, r, 0));
        mi(c, st);
    }
    for r in 0..4 {
        for (i, x) in st.iter_mut().enumerate() {
            *x = sbox(c, *x, poseidon2_const_at(2, r, i as u64));
        }
        me(c, st);
    }
}
fn sponge(c: &Builder, domain: u64, input: &[Wire]) -> [Wire; 4] {
    let mut st = [c.small(Domain::Gold, 0); 12];
    for (i, v) in [(8, 8), (9, 4), (10, domain), (11, POSEIDON2_CONST_IV)] {
        st[i] = c.small(Domain::Gold, v);
    }
    let mut pos = 0;
    for &x in input {
        st[pos] = c.add(st[pos], x);
        pos += 1;
        if pos == 8 {
            perm(c, &mut st);
            pos = 0;
        }
    }
    st[pos] = c.add(st[pos], c.small(Domain::Gold, 1));
    st[7] = c.add(st[7], c.small(Domain::Gold, 1 << 56));
    perm(c, &mut st);
    [st[0], st[1], st[2], st[3]]
}
fn pack56(c: &Builder, bytes: &[Wire]) -> Vec<Wire> {
    let mut marked = bytes.to_vec();
    marked.extend(boolean_hash::bytes(c, &[1, 0, 0]));
    marked
        .chunks_exact(56)
        .map(|chunk| {
            let little: Vec<_> = chunk.chunks_exact(8).rev().flatten().copied().collect();
            c.pack(&little, Domain::Gold)
        })
        .collect()
}
pub(crate) fn build(statement: &MigrationStatement, secret: &[u8; 32]) -> Circuit {
    let c = Builder::default();
    let bits: Vec<_> = secret
        .iter()
        .flat_map(|&b| (0..8).map(move |i| (b >> i) & 1))
        .map(|b| c.input(b))
        .collect();
    let ed = matches!(
        statement.legacy_commitment,
        LegacyCommitmentKind::Slip0010Ed25519(_)
    );
    let group = if ed {
        ScalarGroup::Ed25519
    } else {
        ScalarGroup::Secp256k1
    };
    c.require_scalar(&bits, group.order());
    let (x, y) = curve(&c, &bits, ed);
    let (actual, expected) = match statement.legacy_commitment {
        LegacyCommitmentKind::BitcoinHash160(h) => {
            let mut compressed = boolean_hash::bytes(&c, &[2]);
            compressed[0] = y[0];
            compressed.extend(big_endian(&x));
            (
                boolean_hash::ripemd160(&c, &boolean_hash::sha256(&c, &compressed)),
                h.to_vec(),
            )
        }
        LegacyCommitmentKind::EthereumKeccak20(h) => {
            let mut input = big_endian(&x);
            input.extend(big_endian(&y));
            (
                boolean_hash::keccak256(&c, &input)[96..].to_vec(),
                h.to_vec(),
            )
        }
        LegacyCommitmentKind::BitcoinTaprootXOnly(h) => {
            c.output(y[0]);
            (big_endian(&x), h.to_vec())
        }
        LegacyCommitmentKind::Slip0010Ed25519(h) => {
            let mut encoded = y;
            encoded[255] = x[0];
            (encoded, h.to_vec())
        }
    };
    for (&a, b) in actual.iter().zip(boolean_hash::bytes(&c, &expected)) {
        c.equal(a, b);
    }
    let mut input = alloc::vec![c.small(Domain::Gold, if ed { 2 } else { 1 })];
    input.extend(pack56(&c, &big_endian(&bits)));
    input.extend(
        qsag_accel::goldilocks::pack_bytes32_to_limbs56(&statement.migration_domain)
            .map(|v| c.small(Domain::Gold, v)),
    );
    let nullifier = sponge(&c, scalar::NULLIFIER_DOMAIN, &input);
    for (w, v) in nullifier.into_iter().zip(statement.migration_nullifier) {
        c.equal(w, c.small(Domain::Gold, v));
    }
    // The public statement digest binds destination and epoch in Fiat-Shamir.
    c.finish()
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn complete_curve_circuits_match_native_including_zero() {
        for n in [
            ZERO,
            [1, 0, 0, 0],
            [2, 0, 0, 0],
            [15, 0, 0, 0],
            [16, 0, 0, 0],
            [17, 0, 0, 0],
            [
                0x0123_4567_89ab_cdef,
                0xfedc_ba98_7654_3210,
                u64::MAX,
                0x0800_0000_0000_0000,
            ],
            [0, 0, 0, 0x8000_0000_0000_0000],
        ] {
            for ed in [false, true] {
                let c = Builder::default();
                let b = c.constant_bits(n, 256);
                c.require_scalar(
                    &b,
                    if ed {
                        ScalarGroup::Ed25519
                    } else {
                        ScalarGroup::Secp256k1
                    }
                    .order(),
                );
                let (x, y) = curve(&c, &b, ed);
                if n == ZERO {
                    let circuit = c.finish();
                    assert!(
                        circuit
                            .outputs
                            .iter()
                            .any(|&w| circuit.nodes[w].value != ZERO)
                    );
                    continue;
                }
                let encode = |ws: &[Wire]| -> Vec<u8> {
                    ws.chunks_exact(8)
                        .map(|bs| {
                            bs.iter()
                                .enumerate()
                                .fold(0, |v, (i, &w)| v | ((c.value(w)[0] as u8) << i))
                        })
                        .collect()
                };
                let mut scalar = scalar::encode(n);
                if ed {
                    let mut enc = encode(&y);
                    enc[31] |= (c.value(x[0])[0] as u8) << 7;
                    assert_eq!(
                        enc,
                        crate::ed25519_ct::public_key_from_clamped_scalar(&scalar)
                    );
                } else {
                    scalar.reverse();
                    let point = crate::secp256k1_ct::SecpPoint::generator_mul_ct(&scalar);
                    let (nx, ny) = point.to_affine().unwrap();
                    let mut xb = encode(&x);
                    let mut yb = encode(&y);
                    xb.reverse();
                    yb.reverse();
                    assert_eq!(xb, nx.to_be_bytes());
                    assert_eq!(yb, ny.to_be_bytes());
                }
            }
        }
    }
}

#[cfg(test)]
mod poseidon2_canonical_kat {
    use super::*;
    #[test]
    fn migration_poseidon2_circuit_matches_canonical_kat() {
        let c = Builder::default();
        let mut st = core::array::from_fn(|i| c.small(Domain::Gold, i as u64));
        perm(&c, &mut st);
        assert_eq!(
            st.map(|w| c.value(w)[0]),
            [
                13782584570844608145,
                13136387643152332171,
                7171133015474200819,
                7643370872200861694,
                14144755201299840503,
                16470027036684692562,
                1748465969625202405,
                1718729118078964347,
                6141020819996733037,
                16322330185628708898,
                11650380702735067362,
                2734959974607798415
            ]
        );
    }
}
