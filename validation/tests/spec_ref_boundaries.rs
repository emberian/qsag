// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Boundary checks on the reference oracles themselves, using native integers,
//! exhaustive sets/words, and RustCrypto rather than production QSAG helpers.

use qsag_external_validation::spec_ref::{
    ExactNat, cshake256_framed_32_nist_ref, cshake256_framed_nist_ref,
    exact_neg_log2_floor_bits, exact_neg_log2_floor_millibits, ff_top_exact,
    frontier_fts_cardinalities_ref, octopus_cover_ref, rational_at_least_bits,
};
use qsag_external_validation::{cshake256_nist_sp800_185_ref, nist_left_encode};
use sha3::digest::{ExtendableOutput, Update, XofReader};

fn nat(n: u128) -> ExactNat {
    ExactNat::from_u64_limbs_le(&[n as u64, (n >> 64) as u64])
}

#[test]
fn exact_nat_normalization_carries_shifts_and_division() {
    assert_eq!(ExactNat::from_u64_limbs_le(&[0, 0, 0]), ExactNat::zero());
    assert_eq!(ExactNat::from_u64_limbs_le(&[7, 0, 0]), nat(7));
    assert_eq!(nat(0).bit_len(), 0);
    for a in [0, 1, 2, u32::MAX as u64, 1 << 32, 1 << 63, u64::MAX - 1, u64::MAX] {
        for b in [0, 1, 3, 1 << 32, u64::MAX] {
            assert_eq!(nat(a as u128).add(&nat(b as u128)), nat(a as u128 + b as u128));
            let product = nat(a as u128 * b as u128);
            assert_eq!(nat(a as u128).mul(&nat(b as u128)), product);
            assert_eq!(nat(a as u128).mul_u64(b), product);
        }
    }
    for a in [0, 1, 1 << 64, (1 << 127) + 17, u128::MAX] {
        assert_eq!(nat(a).to_decimal_string(), a.to_string());
        assert_eq!(nat(a).bit_len(), 128 - a.leading_zeros() as usize);
        for d in [1, 2, 3, 1_000_000_000, u32::MAX] {
            assert_eq!(nat(a).div_rem_u32(d), Some((nat(a / d as u128), (a % d as u128) as u32)));
        }
        assert_eq!(nat(a).div_rem_u32(0), None);
    }
    // (B^n - 1)^2 = B^(2n) - 2 B^n + 1, B = 2^64. This reaches
    // maximal inner products and carry propagation well beyond native u128.
    for n in 2..=8 {
        let a = ExactNat::from_u64_limbs_le(&vec![u64::MAX; n]);
        assert_eq!(a.add(&nat(1)), nat(1).shl_bits(64 * n));
        let mut square = vec![0; 2 * n];
        square[0] = 1;
        square[n] = u64::MAX - 1;
        square[n + 1..].fill(u64::MAX);
        assert_eq!(a.mul(&a), ExactNat::from_u64_limbs_le(&square));
        for d in [3, 1_000_000_000, u32::MAX] {
            let (q, r) = a.div_rem_u32(d).unwrap();
            assert!(r < d);
            assert!(q < a);
            assert_eq!(q.mul_u64(d as u64).add(&nat(r as u128)), a);
        }
    }
    for shift in [0, 1, 63, 64, 65, 127, 128, 255] {
        let shifted = nat(3).shl_bits(shift);
        assert_eq!(shifted.bit_len(), shift + 2);
        assert_eq!(shifted, nat(1).shl_bits(shift).add(&nat(1).shl_bits(shift + 1)));
        assert_eq!(nat(0).shl_bits(shift), nat(0));
    }
    assert_eq!(nat(0).pow_u32(0), nat(1));
    assert_eq!(nat(0).pow_u32(7), nat(0));
    assert_eq!(ff_top_exact(0, 0), nat(1));
    assert_eq!(ff_top_exact(3, 4), nat(0));
    assert_eq!(ff_top_exact(10, 4), nat(5040));
}

#[test]
fn rational_floors_are_sound_at_zero_and_power_boundaries() {
    for (n, d) in [(0, 0), (0, 1), (1, 0), (2, 1)] {
        assert_eq!(exact_neg_log2_floor_bits(&nat(n), &nat(d)), None);
        assert_eq!(exact_neg_log2_floor_millibits(&nat(n), &nat(d)), None);
        assert!(!rational_at_least_bits(0, &nat(n), &nat(d)));
    }
    for k in [0, 1, 63, 64, 65, 127] {
        let num = nat(3);
        let den = num.shl_bits(k);
        assert_eq!(exact_neg_log2_floor_bits(&num, &den), Some(k));
        assert_eq!(exact_neg_log2_floor_millibits(&num, &den), Some(1000 * k));
    }
    for (n, d, expected) in [(1, 3, 1584), (2, 3, 584), (5, 8, 678), (1023, 1024, 1), (1024, 1025, 1)] {
        let (num, den) = (nat(n), nat(d));
        let m = exact_neg_log2_floor_millibits(&num, &den).unwrap();
        assert_eq!(m, expected);
        // The floor's defining two inequalities also reject one-millibit overstatement.
        let a = num.pow_u32(1000);
        let b = den.pow_u32(1000);
        assert!(a.shl_bits(m) <= b);
        assert!(a.shl_bits(m + 1) > b);
    }
    for k in [1, 63, 64, 127] {
        let boundary = 1u128 << k;
        assert_eq!(exact_neg_log2_floor_bits(&nat(1), &nat(boundary - 1)), Some(k - 1));
        assert_eq!(exact_neg_log2_floor_bits(&nat(1), &nat(boundary + 1)), Some(k));
    }
}

#[test]
fn frontier_cardinalities_match_exhaustive_leaf_partitions_and_digit_words() {
    for h in 0..=3usize {
        let leaves = 1usize << h;
        // Enumerate subsets of every non-root heap node. Accept precisely disjoint
        // leaf-interval covers, without the production/reference DP recurrence.
        let mut counts = vec![0u64; leaves + 1];
        for mask in 0usize..(1 << (2 * leaves - 2)) {
            let mut covered = 0usize;
            let mut count = 0;
            let mut overlaps = false;
            for node in 2..2 * leaves {
                if mask & (1 << (node - 2)) == 0 {
                    continue;
                }
                let depth = node.ilog2() as usize;
                let width = 1 << (h - depth);
                let offset = node * width - leaves;
                let interval = ((1 << width) - 1) << offset;
                overlaps |= covered & interval != 0;
                covered |= interval;
                count += 1;
            }
            if !overlaps && covered == (1 << leaves) - 1 {
                counts[count] += 1;
            }
        }
        for (l, &frontiers) in counts.iter().enumerate() {
            for w in 0..=3usize {
                let mut words_by_sum = vec![0u64; 3 * l + 2];
                for mut word in 0..w.pow(l as u32) {
                    let mut sum = 0;
                    for _ in 0..l {
                        sum += word % w;
                        word /= w;
                    }
                    words_by_sum[sum] += 1;
                }
                for (s, &decorations) in words_by_sum.iter().enumerate() {
                    let (n, d, total) = frontier_fts_cardinalities_ref(h, w, l, s);
                    assert_eq!(n, nat(frontiers as u128), "h={h}, l={l}");
                    assert_eq!(d, nat(decorations as u128), "w={w}, l={l}, s={s}");
                    assert_eq!(total, nat(frontiers as u128 * decorations as u128));
                }
            }
        }
    }
}

#[test]
fn octopus_root_and_maximum_height_boundaries() {
    assert_eq!(octopus_cover_ref(0, &[0]), Some(vec![]));
    assert_eq!(octopus_cover_ref(0, &[1]), None);
    assert_eq!(octopus_cover_ref(31, &[1 << 31]), None);
    assert_eq!(octopus_cover_ref(32, &[0]), None);
    let cover = octopus_cover_ref(31, &[(1 << 31) - 1]).unwrap();
    let expected: Vec<_> = (0..31).map(|h| (h, ((1u32 << (31 - h)) - 1) ^ 1)).collect();
    assert_eq!(cover, expected);
}

#[test]
fn nist_integer_width_bytepad_and_framing_boundaries() {
    for (x, expected) in [
        (0, vec![1, 0]), (255, vec![1, 255]), (256, vec![2, 1, 0]),
        (65535, vec![2, 255, 255]), (65536, vec![3, 1, 0, 0]),
    ] {
        assert_eq!(nist_left_encode(x), expected);
    }
    let mut max_encoded = vec![std::mem::size_of::<usize>() as u8];
    max_encoded.extend_from_slice(&usize::MAX.to_be_bytes());
    assert_eq!(nist_left_encode(usize::MAX), max_encoded);

    // Literal QSAG framing of ["a", "bc"]: count and byte lengths are u64 LE,
    // independent of NIST's bit-length left_encode inside cSHAKE customization.
    let framed = hex::decode("020000000000000001000000000000006102000000000000006263").unwrap();
    for custom_len in [0, 1, 31, 32, 128, 129, 130, 265, 266, 8191, 8192] {
        let custom = vec![0x53; custom_len];
        for out_len in [0, 32, 135, 136, 137, 273] {
            let mut expected = vec![0; out_len];
            if custom.is_empty() {
                let mut sponge = sha3::Shake256::default();
                sponge.update(&framed);
                sponge.finalize_xof().read(&mut expected);
            } else {
                // RustCrypto implements its own bytepad, including exact-rate prefixes.
                let mut sponge = sha3::CShake256::from_core(sha3::CShake256Core::new(&custom));
                sponge.update(&framed);
                sponge.finalize_xof().read(&mut expected);
            }
            assert_eq!(cshake256_framed_nist_ref(&custom, &[b"a", b"bc"], out_len), expected);
        }
    }
    // Both name and customization contribute separate encode_string values.
    let name = vec![0x4e; 32];
    let custom = vec![0x53; 129];
    for input_len in [0, 135, 136, 137, 272] {
        let input = vec![0x58; input_len];
        let mut sponge = sha3::CShake256::from_core(
            sha3::CShake256Core::new_with_function_name(&name, &custom),
        );
        sponge.update(&input);
        let mut expected = [0; 273];
        sponge.finalize_xof().read(&mut expected);
        assert_eq!(cshake256_nist_sp800_185_ref(&name, &custom, &input, 273), expected);
    }
    let custom = b"framing-boundaries";
    let cases: &[&[&[u8]]] = &[&[], &[b""], &[b"", b""], &[b"a", b"bc"], &[b"ab", b"c"], &[b"abc"]];
    let outputs: Vec<_> = cases.iter().map(|fields| cshake256_framed_32_nist_ref(custom, fields)).collect();
    for i in 0..outputs.len() {
        for j in 0..i {
            assert_ne!(outputs[i], outputs[j], "field count/length must be bound");
        }
    }
}
