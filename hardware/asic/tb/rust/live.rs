use qsag_agg::field::Goldilocks as F;
use qsag_agg::zk_hem::{
    relation::{ConstraintSystem, Lc},
    v2::{
        params::Profile,
        port,
        protocol::{ZkHemV2Proof, prove, verify},
    },
};

fn main() {
    let args: Vec<_> = std::env::args().collect();
    let mut cs = ConstraintSystem::new();
    let x = F::from_u64_reduced(3);
    let xv = cs.public_input(x);
    let yv = cs.public_input(x.pow(7) * F::from_u64_reduced(5));
    let w = cs.alloc(F::from_u64_reduced(5));
    let s = cs.sbox7(&xv.into());
    let prod = cs.mul(&s.into(), &w.into());
    cs.enforce_equal(&Lc::from(prod), &yv.into());
    let (shape, z) = cs.finish_v2();
    let public = z[1..=shape.num_public].to_vec();
    let profile = Profile::TurboShakeJohnson400;
    let statement = b"QSAG-NI command-port verification";
    let bytes = prove(&shape, z, statement, profile, &[19; 32])
        .unwrap()
        .to_bytes();
    std::fs::write("vec/proof_v2.bin", &bytes).unwrap();
    let proof = ZkHemV2Proof::from_bytes(&bytes, &shape).unwrap();
    assert!(verify(&shape, &public, statement, profile, &proof));
    println!(
        "Rust verified {} proof bytes, tag {}",
        bytes.len(),
        bytes[8]
    );
    port::connect(&args[1], &args[2]);
    assert!(verify(&shape, &public, statement, profile, &proof));
    let status = port::with(|p| p.status()).unwrap();
    assert_eq!(status >> 32, 1);
    assert!(status as u32 > 0);
    println!("RTL accepted full proof, {} sticky checks", status as u32);
    port::with(|p| p.coverage());
    let mut bad = proof.clone();
    bad.row_rounds[0][0].0[4] += F::ONE;
    assert!(!verify(&shape, &public, statement, profile, &bad));
    assert_eq!(port::with(|p| p.status()).unwrap() >> 32, 0);
    println!("RTL rejected row round 0 coefficient 0 limb 4");
    port::with(|p| p.cmd(8, 1, 0, 0));
    let mut bad_nonce = proof;
    bad_nonce.tree_nonce[0] ^= 1;
    assert!(!verify(&shape, &public, statement, profile, &bad_nonce));
    assert_eq!(port::with(|p| p.status()).unwrap() >> 32, 0);
    println!("RTL rejected tree nonce bit 0");
    port::with(|p| p.finish());
}
