//! Regenerate the valid proof used by the structured capability fuzzer.
//! Run from fuzz/: cargo run --locked --release --example capability_seed
use qsag_agg::field::Goldilocks;
use qsag_agg::pcs::WhirSecurityRegime;
use qsag_agg::zk_hem::capability::{
    BearerCapability, CapCaveat, CapabilityBatchStatement, CapabilityIssuerDirectory,
    CapabilityParams, CapabilityPresentationInput, CapabilityRelation, CapabilityRequest,
    SortedRevocationTree,
};

fn main() {
    let f = Goldilocks::from_u64_reduced;
    let relation = CapabilityRelation::new(CapabilityParams {
        batch_size: 1, max_hops: 2, issuer_depth: 2, revocation_depth: 2,
    }).unwrap();
    let mut cap = BearerCapability::issue(&[f(7); 4], [f(1); 4], [f(0x33); 4]).unwrap();
    cap.attenuate(CapCaveat::Actions(1)).unwrap();
    let directory = CapabilityIssuerDirectory::new(2, &[cap.mint_leaf()]).unwrap();
    let revocations = SortedRevocationTree::new(2, 1, &[]).unwrap();
    let non_membership = revocations.prove_non_membership(cap.token_id()).unwrap();
    let mut inputs = [CapabilityPresentationInput {
        capability: cap, issuer_index: 0,
        issuer_siblings: directory.opening(0).unwrap(), non_membership,
    }];
    let statement = CapabilityBatchStatement::prepare_sorted(directory.root(), revocations.root(), 1,
        CapabilityRequest { audience: [f(0x33); 4], resource: [f(0x44); 4],
            actions: 1, amount: 100, now: 1_700_000_000 }, &mut inputs, b"fuzz-cap").unwrap();
    let regime = WhirSecurityRegime::Poseidon2Cdhz25JohnsonQrom128;
    let proof = relation.prove(&statement, &inputs, b"fuzz-cap", regime, &[0x42; 32]).unwrap();
    assert!(relation.verify(&statement, b"fuzz-cap", regime, &proof));
    std::fs::create_dir_all("seeds").unwrap();
    std::fs::write("seeds/capability.bin", proof.to_bytes()).unwrap();
}
