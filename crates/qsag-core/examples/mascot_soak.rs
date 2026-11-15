//! Bounded dealerless MASCOT timing with reproducible demonstration seeds.
use qsag_core::field::tower::TowerGf256;
use qsag_core::preprocessing::{OtMesh, PartyPrivateRng, run_dealerless_pi_triple_f2};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let words: usize = std::env::args()
        .nth(1)
        .map(|arg| arg.parse())
        .transpose()?
        .unwrap_or(64);
    let iterations: usize = std::env::args()
        .nth(2)
        .map(|arg| arg.parse())
        .transpose()?
        .unwrap_or(3);
    let mut rngs: Vec<_> = (0..3)
        .map(|party| PartyPrivateRng::from_seed([0x31 + party; 32], b"mascot-benchmark"))
        .collect();
    let points = [TowerGf256(1), TowerGf256(2), TowerGf256(3)];
    let start = std::time::Instant::now();
    let mut mesh = OtMesh::try_establish([0x91; 32], &mut rngs)?;
    println!("bootstrap: {:?}", start.elapsed());
    for iteration in 0..iterations {
        let start = std::time::Instant::now();
        let mut session = [0x92; 32];
        session[..8].copy_from_slice(&(iteration as u64).to_le_bytes());
        let vaults = run_dealerless_pi_triple_f2(session, 2, &points, words, &mut mesh, &mut rngs)?;
        assert_eq!(vaults.len(), 3);
        println!(
            "iteration {iteration}: {words} authenticated triple words in {:?}",
            start.elapsed()
        );
    }
    Ok(())
}
