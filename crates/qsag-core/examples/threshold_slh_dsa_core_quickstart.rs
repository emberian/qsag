//! Reproducible threshold SLH-DSA keygen and signing with public demonstration seeds.
//! Enable `std` for scoped CPU workers; pass `--gpu` to require Vulkan kernel parity first.
use qsag_core::fips205::{Fips205Params, SlhPublicKey, slh_keygen_mpc, slh_sign_mpc, slh_verify};
use qsag_core::keccak_mpc::{RssSlhMpcCluster, run_dealerless_rss_dkg_2of3};
use qsag_core::preprocessing::PartyPrivateRng;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    if std::env::args().any(|arg| arg == "--gpu") {
        compare_backends()?;
    }
    run_rss_example()
}

fn compare_backends() -> Result<(), Box<dyn std::error::Error>> {
    use qsag_accel::vulkan::VulkanSpirvBackend;
    use qsag_accel::{AcceleratorBackend, CpuReferenceBackend};
    let gpu = VulkanSpirvBackend::try_new()?;
    let input: Vec<[u64; 25]> = (0..8192)
        .map(|i| core::array::from_fn(|j| (i * 25 + j) as u64))
        .collect();
    let shares: Vec<[u128; 2]> = (0..8192).map(|i| [i as u128, (i as u128) << 64]).collect();
    let weights: Vec<[u128; 2]> = (0..8192)
        .map(|i| [(i + 31) as u128, (i + 19) as u128])
        .collect();
    let run = |backend: &dyn AcceleratorBackend| -> Result<_, qsag_accel::AccelError> {
        let start = std::time::Instant::now();
        let mut states = input.clone();
        backend.try_batch_keccak_f1600_pinned(&mut states)?;
        let dot = qsag_core::preprocessing::batch_bdoz_gf2128_dot(backend, &shares, &weights)?;
        Ok((states, dot, start.elapsed()))
    };
    let cpu = run(&CpuReferenceBackend)?;
    let accelerated = run(&gpu)?;
    assert_eq!(cpu.0, accelerated.0);
    assert_eq!(cpu.1, accelerated.1);
    assert_eq!(gpu.cpu_fallback_count(), 0);
    println!(
        "{}: bulk Keccak + tower BDOZ CPU {:?}, GPU {:?}; exact parity",
        gpu.device_name(),
        cpu.2,
        accelerated.2
    );
    Ok(())
}

fn run_rss_example() -> Result<(), Box<dyn std::error::Error>> {
    let started = std::time::Instant::now();
    println!("=== Stage 1: Full NIST SLH-DSA-SHAKE-128f (2-of-3 RSS MPC) ===");
    let params = Fips205Params::SLH_DSA_SHAKE_128F;
    let msg = b"Transfer 250,000 QSAG from treasury vault #7";
    let ctx = b"qsag:treasury:v1";

    let mut rss_dkg_rngs = [
        PartyPrivateRng::from_seed([0x11; 32], b"example.rss.dkg.p0"),
        PartyPrivateRng::from_seed([0x22; 32], b"example.rss.dkg.p1"),
        PartyPrivateRng::from_seed([0x33; 32], b"example.rss.dkg.p2"),
    ];
    let (rss_keys, pk_seed_full) =
        run_dealerless_rss_dkg_2of3([0xA0; 32], params.n, &mut rss_dkg_rngs)?;

    let rss_sign_rngs = [
        PartyPrivateRng::from_seed([0x44; 32], b"example.rss.sign.p0"),
        PartyPrivateRng::from_seed([0x55; 32], b"example.rss.sign.p1"),
        PartyPrivateRng::from_seed([0x66; 32], b"example.rss.sign.p2"),
    ];
    let mut rss_cluster = RssSlhMpcCluster::new([0xA1; 32], rss_keys, rss_sign_rngs)?;

    eprintln!("RSS DKG: {:?}", started.elapsed());
    let pk = slh_keygen_mpc(&params, &mut rss_cluster, &pk_seed_full[..params.n])?;
    eprintln!("RSS root: {:?}", started.elapsed());
    let sig = slh_sign_mpc(&params, &mut rss_cluster, msg, ctx, &pk, None)?;

    assert_eq!(sig.len(), params.sig_bytes()); // 17,088 bytes
    assert!(
        slh_verify(&params, msg, &sig, ctx, &pk),
        "stock FIPS 205 verifier must accept threshold signature"
    );
    assert!(
        !slh_verify(&params, b"tampered payload", &sig, ctx, &pk),
        "tampered message must be rejected"
    );

    let spki_der = pk.to_spki_der(&params)?;
    let (decoded_params, decoded_pk) = SlhPublicKey::from_spki_der(&spki_der)?;
    assert_eq!(decoded_params, params);
    assert_eq!(decoded_pk, pk);
    println!(
        "  [ok] SLH-DSA-SHAKE-128f pk={} B (SPKI={} B), sig={} B verified by stock slh_verify",
        pk.to_bytes().len(),
        spki_der.len(),
        sig.len(),
    );

    eprintln!("Stage 1 elapsed: {:?}", started.elapsed());
    Ok(())
}
