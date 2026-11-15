use qsag_asm::{SimdBackend, goldilocks_mul_ct_with_backend, goldilocks_pow7_ct_with_backend};

#[test]
fn portable_dispatch_matches_integer_modular_arithmetic() {
    const P: u128 = 0xffff_ffff_0000_0001;
    let edges = [
        0,
        1,
        2,
        (1 << 32) - 1,
        1 << 32,
        P as u64 - 1,
        P as u64,
        u64::MAX,
    ];
    let check = |a: u64, b: u64| {
        assert_eq!(
            goldilocks_mul_ct_with_backend(a, b, SimdBackend::Portable),
            ((a as u128 * b as u128) % P) as u64
        );
        let mut expected = 1u128;
        for _ in 0..7 {
            expected = expected * a as u128 % P;
        }
        assert_eq!(
            goldilocks_pow7_ct_with_backend(a, SimdBackend::Portable),
            expected as u64
        );
    };
    for a in edges {
        for b in edges {
            check(a, b);
        }
    }
    let mut state = 0x82a9_c678_d35b_904du64;
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for _ in 0..100_000 {
        check(next(), next());
    }
}
