use qsag_agg::field::Goldilocks;
use qsag_agg::sponge::{turboshake256_from_midstate_into, turboshake256_static_midstate};
use qsag_agg::zk_hem::v2::{
    field5::Fp5,
    hash::Hasher,
    params::Profile,
    port::{Port, words},
};
const DOMAINS: [&[u8]; 8] = [
    b"QSAG.ZKHEM2.TRANSCRIPT",
    b"QSAG.ZKHEM2.CANOPY.LEAF",
    b"QSAG.ZKHEM2.CANOPY.NODE",
    b"QSAG.ZKHEM2.WHIR.FOLD",
    b"QSAG.ZKHEM2.OOD",
    b"QSAG.HEM.QUINTIC.V2",
    b"QSAG.ZKHEM2.TREE/v1",
    b"QSAG.ZKHEM2.FS/v1",
];
fn status(p: &mut Port, pass: bool, checks: u64) {
    p.expect(0xb, 0, 0, 0, ((pass as u64) << 32) | checks);
}
fn domains(p: &mut Port) {
    for (d, name) in DOMAINS.iter().enumerate() {
        let init = turboshake256_static_midstate(name);
        p.cmd(0x3a, d, 0, 0);
        for (i, &lane) in init.iter().enumerate() {
            p.expect(0x32, i, 0, 0, lane);
        }
        p.cmd(0x35, 0, 0, 0);
        p.cmd(0x3a, (d + 1) % 8, 0, 0);
        p.cmd(0x36, 0, 0, 0);
        for (i, &lane) in init.iter().enumerate() {
            p.expect(0x32, i, 0, 0, lane);
        }
        let msg: Vec<u8> = (0..165).map(|i| (i * 37) as u8).collect();
        let mut out = [0; 136];
        turboshake256_from_midstate_into(&init, &msg, &mut out);
        p.absorb(d, &msg, None);
        for n in 1..=17 {
            let addr = 0x3ff8;
            p.cmd(3, 0, addr + n, 0xdeadbeef);
            p.cmd(8, 0, addr, 0);
            p.cmd(0x39, n % 2, if n % 2 == 1 { 300 } else { addr }, n as u64);
            for (i, &v) in words(&out).iter().take(n).enumerate() {
                p.expect(4, 0, addr + i, 0, v);
            }
            p.expect(4, 0, addr + n, 0, 0xdeadbeef);
            p.cmd(9, 0, 0, 0xfeed);
            p.expect(4, 0, addr + if n % 2 == 1 { n } else { 0 }, 0, 0xfeed);
        }
    }
}
fn paths(p: &mut Port) {
    let h = Hasher::new(Profile::TurboShakeJohnson400);
    let salt: [u8; 32] = std::array::from_fn(|i| (i * 11 + 7) as u8);
    let tree_nonce: [u8; 32] = std::array::from_fn(|i| (i * 47 + 31) as u8);
    let z: Vec<_> = (0..8)
        .map(|i| Goldilocks::from_u64_reduced(i * 17))
        .collect();
    let r = Fp5::X.pow(9) + Fp5::from_u64(11);
    let index = 5;
    let depth = 3;
    let leaf = h.leaf_stage0(&tree_nonce, index, &salt, &z, r);
    let mut msg = vec![0x10, 3];
    msg.extend(index.to_le_bytes());
    msg.extend(tree_nonce);
    msg.extend(salt);
    for x in &z {
        msg.extend(x.to_le_bytes());
    }
    msg.extend(r.to_le_bytes());
    let siblings: [[u8; 50]; 3] =
        std::array::from_fn(|k| std::array::from_fn(|i| (i * 13 + k * 37) as u8));
    let mut node = leaf;
    let mut heap = (1 << depth) + index;
    for sib in &siblings {
        node = if heap & 1 == 0 {
            h.node(heap >> 1, &node, sib)
        } else {
            h.node(heap >> 1, sib, &node)
        };
        heap >>= 1;
    }
    let root = h.root(0, depth, &node);
    // Valid, bit 399, tree nonce bit 0, then every sibling byte at every level.
    for fault in 0..153 {
        let mut nonce = tree_nonce;
        let mut expected = root;
        let mut path = siblings;
        if fault == 1 {
            expected[49] ^= 0x80;
        }
        if fault == 2 {
            nonce[0] ^= 1;
        }
        if fault >= 3 {
            path[(fault - 3) / 50][(fault - 3) % 50] ^= 1;
        }
        p.cmd(8, 1, 0, 0);
        p.absorb(6, &msg, Some(&nonce));
        for (i, s) in path.iter().enumerate() {
            p.write(3, 0, 64 + i * 7, &words(s));
        }
        let mut target = words(&expected);
        target[6] |= 0xdead_beef_1234_0000;
        p.write(3, 0, 300, &target);
        p.cmd(0x16, depth as usize, 64, index as u64);
        p.expect(0xa, 2, 300, 0, (fault == 0) as u64);
        status(p, fault == 0, 1);
        // A successful later comparison cannot clear a previous sticky failure.
        p.cmd(0x39, 0, 400, 7);
        p.expect(0xa, 2, 400, 0, 1);
        status(p, fault == 0, 2);
    }
    p.cmd(8, 1, 0, 0);
    p.write(0x31, 0, 0, &words(&leaf));
    p.cmd(0x16, 0, 0, 9 << 32);
    p.write(3, 0, 300, &words(&h.root(9, 0, &leaf)));
    p.expect(0xa, 2, 300, 0, 1);
    let limbs = words(&qsag_core::sponge::poseidon2::poseidon2_gl24_hash56(
        17,
        b"QSAG-NI equality",
    ));
    p.write(1, 0, 0, &limbs);
    for k in 0..=7 {
        p.cmd(8, 1, 0, 0);
        p.write(3, 0, 300, &limbs);
        if k < 7 {
            p.cmd(3, 0, 300 + k, limbs[k] ^ 0x8000);
        }
        p.expect(0xa, 3, 300, 0, (k == 7) as u64);
        status(p, k == 7, 1);
    }
}
fn quintics(p: &mut Port) {
    let mut seed: u64 = 812391;
    let mut elt = || {
        Fp5(std::array::from_fn(|_| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            Goldilocks::from_u64_reduced(seed)
        }))
    };
    let a = elt();
    let r = elt();
    let c: Vec<_> = (0..10).map(|_| elt()).collect();
    let flip = |mut x: Fp5, i: usize| {
        x.0[i] += Goldilocks::ONE;
        x
    };
    for op in [0x28, 0x29, 0x2a, 0x2b] {
        for degree in if op == 0x2b {
            vec![2, 3, 4, 9]
        } else {
            vec![3]
        } {
            let coeffs = &c[..=degree];
            let claim = coeffs.iter().fold(c[0], |sum, &x| sum + x);
            let result = match op {
                0x28 => a * r + c[0],
                0x29 => c.iter().fold(a, |v, &x| v * r + x),
                0x2a => c[2] + r * (c[3] - c[2]),
                _ => coeffs.iter().rev().fold(Fp5::ZERO, |v, &x| v * r + x),
            };
            for fault in 0..=5 {
                p.cmd(8, 1, 0, 0);
                let mut input = c.clone();
                if fault < 5 {
                    let k = if op == 0x2a { 3 } else { 0 };
                    input[k] = flip(input[k], fault);
                }
                p.polynomial(300, &input);
                p.state(0, if op == 0x2b { claim } else { a });
                p.state(5, r);
                let wptr = op == 0x2a && fault % 2 == 0;
                p.cmd(8, 0, 500, 0);
                let count = match op {
                    0x28 => 1,
                    0x29 => 10,
                    0x2a => 2,
                    _ => degree,
                };
                p.cmd(op, wptr as usize, 300, count as u64);
                if op == 0x2a && fault == 5 {
                    for (i, v) in words(&(c[0] + r * (c[1] - c[0])).to_le_bytes())
                        .into_iter()
                        .enumerate()
                    {
                        p.expect(4, 0, 300 + i, 0, v);
                    }
                }
                if wptr {
                    p.cmd(9, 0, 0, 0xfeed);
                    p.expect(4, 0, 510, 0, 0xfeed);
                    for (i, v) in words(&(c[0] + r * (c[1] - c[0])).to_le_bytes())
                        .into_iter()
                        .enumerate()
                    {
                        p.expect(4, 0, 500 + i, 0, v);
                    }
                }
                if op == 0x2b {
                    status(p, fault == 5, 1);
                }
                p.mem(600, result);
                p.expect(0xa, 4, 600, 0, (fault == 5) as u64);
                status(p, fault == 5, 1 + (op == 0x2b) as u64);
            }
        }
    }
}
fn main() {
    let mut p = Port::open(&std::env::args().nth(1).unwrap(), None);
    domains(&mut p);
    paths(&mut p);
    quintics(&mut p);
    p.finish();
}
