//! Remote-only microbenchmark of the exact basis map, including dispatch and packing.
use std::{hint::black_box, time::Instant};
fn main() {
    let input: [u128; 64] =
        core::array::from_fn(|i| (i as u128 + 1).wrapping_mul(0x9e3779b97f4a7c15));
    let expected = input.map(qsag_asm::portable::tower128_to_poly128_portable);
    let mut actual = input;
    qsag_asm::tower128_to_poly128_batch_ct(&mut actual);
    assert_eq!(actual, expected);
    qsag_asm::poly128_to_tower128_batch_ct(&mut actual);
    assert_eq!(actual, input);
    for (name, map) in [
        (
            "portable",
            (|v: &mut [u128; 64]| {
                for x in v {
                    *x = qsag_asm::portable::tower128_to_poly128_portable(*x);
                }
            }) as fn(&mut [u128; 64]),
        ),
        (
            "dispatched",
            (|v: &mut [u128; 64]| qsag_asm::tower128_to_poly128_batch_ct(v)) as fn(&mut [u128; 64]),
        ),
    ] {
        let start = Instant::now();
        for _ in 0..100_000 {
            let mut values = black_box(input);
            map(&mut values);
            black_box(values);
        }
        println!(
            "{name}: {:.1} ns / 64 elements",
            start.elapsed().as_nanos() as f64 / 100_000.0
        );
    }
}
