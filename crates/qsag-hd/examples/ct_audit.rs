//! Retain full-width reduction entry points in a final ThinLTO ELF for auditing.
//! Build with `cargo build -p qsag-hd --release --example ct_audit` and strip=none.
use core::hint::black_box;
use qsag_hd::linear_module::{ct_reduce_mod_q_u64, ct_reduce_mod_q_u128, mod_q_mul};

fn main() {
    let reduce64 = black_box(ct_reduce_mod_q_u64 as fn(u64) -> u32);
    let reduce128 = black_box(ct_reduce_mod_q_u128 as fn(u128) -> u32);
    let multiply = black_box(mod_q_mul as fn(u32, u32) -> u32);
    black_box(reduce64(black_box(u64::MAX)));
    black_box(reduce128(black_box(u128::MAX)));
    black_box(multiply(black_box(8_380_416), black_box(8_380_416)));
}
