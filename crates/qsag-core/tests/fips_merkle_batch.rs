use qsag_core::fips205::{
    Fips205Adrs, Fips205AdrsType, SlhBlock, build_fips205_merkle_from_leaves, fips205_h,
};

#[test]
fn batched_merkle_matches_scalar_for_tails_and_address_domains() {
    for n in [16, 24, 32] {
        let seed = vec![0x71; n];
        for height in 1..=4 {
            for preserve in [false, true] {
                let leaves: Vec<_> = (0..1usize << height)
                    .map(|i| SlhBlock::from_slice(&vec![i as u8; n]).unwrap())
                    .collect();
                let mut base = Fips205Adrs::ZERO;
                base.layer = 3;
                base.key_pair = 7;
                base.set_tree_address(0x1873);
                let kind = Fips205AdrsType::Tree;
                let (root, auth) = build_fips205_merkle_from_leaves(
                    n, &seed, base, kind, preserve, &leaves, height, 32, 0,
                );
                let mut cur = leaves.clone();
                let mut reference_auth = Vec::new();
                for level in 1..=height {
                    reference_auth.push(cur[1]);
                    cur = cur
                        .as_chunks::<2>()
                        .0
                        .iter()
                        .enumerate()
                        .map(|(i, pair)| {
                            let mut adrs = base.with_type_and_clear(kind);
                            if preserve {
                                adrs.key_pair = base.key_pair;
                            }
                            adrs.f5 = level as u32;
                            adrs.f6 = (32 >> level) + i as u32;
                            fips205_h(n, &seed, &adrs, &pair[0], &pair[1])
                        })
                        .collect();
                }
                assert_eq!(root, cur[0]);
                assert_eq!(auth, reference_auth);
                let mut wrong_base = base;
                wrong_base.layer ^= 1;
                let (wrong, _) = build_fips205_merkle_from_leaves(
                    n, &seed, wrong_base, kind, preserve, &leaves, height, 32, 0,
                );
                assert_ne!(root, wrong);
            }
        }
    }
}
