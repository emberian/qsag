// Runs against the source overlay with no hardware hooks installed.
mod proof_fixture;
use qsag_agg::zk_hem::v2::{
    params::Profile,
    protocol::{ZkHemV2Proof, verify},
};

fn main() {
    let bytes = std::fs::read(std::env::args().nth(1).unwrap()).unwrap();
    let (shape, z) = proof_fixture::relation();
    let proof = ZkHemV2Proof::from_bytes(&bytes, &shape).unwrap();
    assert!(verify(
        &shape,
        &z[1..=shape.num_public],
        proof_fixture::STATEMENT,
        Profile::TurboShakeJohnson400,
        &proof
    ));
    println!(
        "Uninstrumented Rust verifier accepted {} bytes, tag {}",
        bytes.len(),
        bytes[8]
    );
}
