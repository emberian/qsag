#[path = "../proof_fixture.rs"]
mod proof_fixture;
use qsag_agg::zk_hem::v2::{
    params::Profile,
    protocol::{ZkHemV2Proof, layout_of, verify},
};
use std::fs;
fn u32le(dst: &mut Vec<u8>, n: usize) {
    dst.extend(u32::try_from(n).unwrap().to_le_bytes());
}
fn blob(dst: &mut Vec<u8>, v: &[u8]) {
    u32le(dst, v.len());
    dst.extend(v);
}
fn main() {
    let bytes = fs::read("vec/proof_v2.bin").unwrap();
    let (s, z) = proof_fixture::relation();
    let public = &z[1..=s.num_public];
    let proof = ZkHemV2Proof::from_bytes(&bytes, &s).unwrap();
    assert!(verify(
        &s,
        public,
        proof_fixture::STATEMENT,
        Profile::TurboShakeJohnson400,
        &proof
    ));
    let desc = descriptor(&s, public, proof_fixture::STATEMENT);
    fs::write("vec/statement_v2.bin", &desc).unwrap();
    println!(
        "Rust reference accepted proof={} descriptor={} stages={:?}",
        bytes.len(),
        desc.len(),
        layout_of(&s).unwrap().schedule
    );
}

pub fn descriptor(
    s: &qsag_agg::zk_hem::relation::Shape,
    public: &[qsag_agg::field::Goldilocks],
    statement: &[u8],
) -> Vec<u8> {
    assert!(s.lookups().is_none());
    assert_eq!(public.len(), s.num_public);
    let l = layout_of(s).unwrap();
    let mut layout = Vec::new();
    for n in [
        s.log_rows,
        s.num_vars,
        s.num_public,
        l.log_cells,
        l.var_bits,
        l.var_cells,
        l.var_align,
        l.mask_base,
        l.blind_cells,
        l.schedule.early_stop_vars,
        l.schedule.stages.len(),
    ] {
        layout.extend((n as u64).to_le_bytes());
    }
    for stage in &l.schedule.stages {
        for n in [stage.blowup, stage.step_vars, stage.num_queries] {
            layout.extend((n as u64).to_le_bytes());
        }
    }
    let mut desc = vec![0; 4];
    desc.extend(b"ZKD1");
    desc.extend(s.digest());
    blob(&mut desc, &layout);
    blob(&mut desc, statement);
    blob(
        &mut desc,
        &public
            .iter()
            .flat_map(|v| v.to_le_bytes())
            .collect::<Vec<_>>(),
    );
    u32le(&mut desc, s.num_sbox);
    for matrix in [&s.a, &s.b, &s.c] {
        for i in 0..s.num_rows() {
            let row: Vec<_> = matrix.row(i).collect();
            u32le(&mut desc, row.len());
            for (j, v) in row {
                u32le(&mut desc, j);
                desc.extend(v.to_le_bytes());
            }
        }
    }
    let len = desc.len() as u32;
    desc[..4].copy_from_slice(&len.to_le_bytes());
    desc
}
