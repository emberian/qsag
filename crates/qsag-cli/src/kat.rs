//! `kat`: known-answer and self-consistency checks across the workspace crates.
//!
//! Vectors marked *external* come from published standards or from the Lean reference model
//! (`tests/kat_vectors.json`, embedded at build time). Vectors marked *regression* were produced
//! by this implementation and pin its current behaviour.

use qsag_accel::CpuReferenceBackend;
use qsag_accel::goldilocks::{ext2_inv_or_zero, ext2_mul, gl_add, gl_inv_or_zero, gl_mul, gl_sub};
use qsag_accel::keccak::{finalize_cshake256, init_cshake256, shake256_xof};
use qsag_accel::poseidon2::{poseidon2_perm12, poseidon2_sbox7};
use qsag_accel::sha2::sha256;
use qsag_addr::{AddrError, QsagAddress, bech32m_decode_5bit};
use qsag_core::fips205::{Fips205Params, slh_keygen_internal, slh_sign, slh_verify};
use qsag_fts::{FrontierDpTable, FrontierFtsProfile, FrontierFtsSigningKey, verify_frontier_fts};

use crate::cli::{Args, CliError};
use crate::codec::{Json, to_hex};

const KAT_JSON: &str = include_str!("../../../tests/kat_vectors.json");

const KAT_HELP: &str = "\
qsag kat [--json]

Run the built-in known-answer tests: FIPS 202 / SP 800-185 hashing, SHA-256, Goldilocks field
and Poseidon2 vectors from the reference model, a full FIPS 205 SLH-DSA-SHAKE-128f signature,
few-time signatures, K-to-1 aggregation, Bech32m addresses, and the custody policy.
Exit code 0 means every check passed; exit code 2 means at least one failed.
";

struct Report {
    rows: Vec<(String, &'static str, &'static str, bool, String)>,
}

impl Report {
    fn check(
        &mut self,
        group: &'static str,
        origin: &'static str,
        name: &str,
        pass: bool,
        detail: String,
    ) {
        self.rows
            .push((name.to_string(), group, origin, pass, detail));
    }
    fn eq_hex(
        &mut self,
        group: &'static str,
        origin: &'static str,
        name: &str,
        got: &[u8],
        expected_hex: &str,
    ) {
        let got = to_hex(got);
        self.check(
            group,
            origin,
            name,
            got == expected_hex,
            if got == expected_hex {
                String::new()
            } else {
                format!("got {got}")
            },
        );
    }
    fn eq_u64(&mut self, group: &'static str, name: &str, got: u64, expected: &str) {
        let pass = got.to_string() == expected;
        self.check(
            group,
            "external",
            name,
            pass,
            if pass {
                String::new()
            } else {
                format!("got {got}, expected {expected}")
            },
        );
    }
}

fn accel_checks(report: &mut Report, kat: &Json) -> Result<(), CliError> {
    let keccak = kat
        .get("keccak")
        .ok_or_else(|| CliError::input("KAT file lacks keccak"))?;
    let mut out32 = [0u8; 32];
    shake256_xof(b"", &mut out32);
    report.eq_hex(
        "accel",
        "external",
        "SHAKE256(\"\")",
        &out32,
        keccak.field_str("shake256_empty_32")?,
    );
    shake256_xof(b"abc", &mut out32);
    report.eq_hex(
        "accel",
        "external",
        "SHAKE256(\"abc\")",
        &out32,
        keccak.field_str("shake256_abc_32")?,
    );
    let sequence: Vec<u8> = (0..64).collect();
    let mut out64 = [0u8; 64];
    shake256_xof(&sequence, &mut out64);
    report.eq_hex(
        "accel",
        "external",
        "SHAKE256(0..64), 64 bytes",
        &out64,
        keccak.field_str("shake256_seq64_64")?,
    );
    let mut sponge = init_cshake256(b"", b"QSAG.KAT.v1");
    sponge.absorb(b"quantum-signature-aggregation");
    finalize_cshake256(&mut sponge, true);
    sponge.squeeze(&mut out32);
    report.eq_hex(
        "accel",
        "external",
        "cSHAKE256 with customization",
        &out32,
        keccak.field_str("cshake256_custom_32")?,
    );
    report.eq_hex(
        "accel",
        "external",
        "SHA-256(\"abc\")",
        &sha256(b"abc"),
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
    );

    let field = kat
        .get("goldilocks")
        .ok_or_else(|| CliError::input("KAT file lacks goldilocks"))?;
    let (a, b) = (0xFFFF_FFFF_0000_0000u64, 0x1234_5678_9ABC_DEF0u64);
    report.eq_u64(
        "accel",
        "Goldilocks add",
        gl_add(a, b),
        field.field_str("add_ab")?,
    );
    report.eq_u64(
        "accel",
        "Goldilocks sub",
        gl_sub(a, b),
        field.field_str("sub_ab")?,
    );
    report.eq_u64(
        "accel",
        "Goldilocks mul",
        gl_mul(a, b),
        field.field_str("mul_ab")?,
    );
    report.eq_u64(
        "accel",
        "Goldilocks inverse",
        gl_inv_or_zero(b),
        field.field_str("inv_b")?,
    );
    report.eq_u64(
        "accel",
        "Poseidon2 S-box x^7",
        poseidon2_sbox7(b),
        field.field_str("sbox7_b")?,
    );
    let ea = [0xCAFE_BABE_1234_5678u64, 0x0FED_CBA9_8765_4321];
    let eb = [0x1122_3344_5566_7788u64, 0x99AA_BBCC_DDEE_FF00];
    let product = ext2_mul(ea, eb);
    report.eq_u64(
        "accel",
        "quadratic extension mul c0",
        product[0],
        field.field_str("ext2_mul_c0")?,
    );
    report.eq_u64(
        "accel",
        "quadratic extension mul c1",
        product[1],
        field.field_str("ext2_mul_c1")?,
    );
    let inverse = ext2_inv_or_zero(ea);
    report.eq_u64(
        "accel",
        "quadratic extension inverse c0",
        inverse[0],
        field.field_str("ext2_inv_a_c0")?,
    );
    report.eq_u64(
        "accel",
        "quadratic extension inverse c1",
        inverse[1],
        field.field_str("ext2_inv_a_c1")?,
    );

    let poseidon = kat
        .get("poseidon2_goldilocks_12")
        .ok_or_else(|| CliError::input("KAT file lacks poseidon2"))?;
    for (name, key, mut state) in [
        ("Poseidon2 permutation of zero", "perm_zero", [0u64; 12]),
        (
            "Poseidon2 permutation of 0..12",
            "perm_seq_0_11",
            core::array::from_fn(|i| i as u64),
        ),
    ] {
        poseidon2_perm12(&mut state);
        let expected: Vec<&str> = poseidon
            .get(key)
            .and_then(Json::as_array)
            .unwrap_or(&[])
            .iter()
            .filter_map(Json::as_str)
            .collect();
        let got: Vec<String> = state.iter().map(u64::to_string).collect();
        report.check(
            "accel",
            "external",
            name,
            expected.len() == 12 && got.iter().map(String::as_str).eq(expected),
            String::new(),
        );
    }
    Ok(())
}

fn agg_checks(report: &mut Report, kat: &Json) -> Result<(), CliError> {
    use qsag_agg::sponge::poseidon2_hash32;
    use qsag_agg::{
        HemQuinticProfile, SignerBitmap, SigningMode, ValidatorKeypair, prove_hem_quintic_128,
        verify_hem_quintic_128,
    };

    let poseidon = kat
        .get("poseidon2_goldilocks_12")
        .ok_or_else(|| CliError::input("KAT file lacks poseidon2"))?;
    for (name, key, input) in [
        ("Poseidon2 hash of empty input", "hash32_empty", &b""[..]),
        ("Poseidon2 hash of 0x00", "hash32_00", &[0u8][..]),
        (
            "Poseidon2 hash of 0x010203",
            "hash32_010203",
            &[1, 2, 3][..],
        ),
        (
            "Poseidon2 hash of a label",
            "hash32_label",
            &b"qsag-poseidon2-kat"[..],
        ),
    ] {
        report.eq_hex(
            "agg",
            "external",
            name,
            &poseidon2_hash32(input),
            poseidon.field_str(key)?,
        );
    }
    let mut abc = [0u8; 32];
    shake256_xof(b"abc", &mut abc);
    let limbs: Vec<String> = qsag_agg::bytes32_to_limbs56(&abc)
        .iter()
        .map(|l| l.to_canonical_u64().to_string())
        .collect();
    let expected: Vec<&str> = kat
        .get("aggregation")
        .and_then(|a| a.get("digest5_shake256_abc_le"))
        .and_then(Json::as_array)
        .unwrap_or(&[])
        .iter()
        .filter_map(Json::as_str)
        .collect();
    report.check(
        "agg",
        "external",
        "56-bit limb packing of a digest",
        limbs.iter().map(String::as_str).eq(expected),
        String::new(),
    );

    // Two validators sign one message; the aggregate must verify for that message only.
    let seed = [0x4B; 32];
    let message = b"qsag kat aggregate";
    let mut keys: Vec<ValidatorKeypair> = (0..2).map(|i| crate::agg::validator(&seed, i)).collect();
    let committee: Vec<_> = keys.iter().map(|k| k.pk).collect();
    let kat_dir = std::env::temp_dir().join(format!(
        "qsag-agg-kat-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir(&kat_dir).map_err(|e| CliError::io("creating KAT directory", e))?;
    let mut signatures = Vec::new();
    for (i, key) in keys.iter_mut().enumerate() {
        let (mut wal, _) = qsag_agg::FsWalEpochSink::create_new_for_fresh_key(
            kat_dir.join(format!("{i}.wal")),
            &qsag_agg::sig::digest4_to_bytes(&key.pk.pk_root),
            [0x91; 32],
        )
        .map_err(|e| CliError::state(format!("KAT journal: {e:?}")))?;
        signatures.push(key.sign_stateful(message, 0, &mut wal));
    }
    let signatures: Result<Vec<_>, _> = signatures.into_iter().collect();
    std::fs::remove_dir_all(&kat_dir).map_err(|e| CliError::io("removing own KAT directory", e))?;
    let roundtrip = signatures.ok().and_then(|sigs| {
        let bitmap = SignerBitmap::from_active_indices(2, &[0, 1])?;
        let proof = prove_hem_quintic_128(
            HemQuinticProfile::TurboShake400,
            &committee,
            &bitmap,
            &SigningMode::SharedMessage(message),
            &sigs,
        )
        .ok()?;
        Some(
            verify_hem_quintic_128(
                HemQuinticProfile::TurboShake400,
                &committee,
                &SigningMode::SharedMessage(message),
                &proof,
            ) && !verify_hem_quintic_128(
                HemQuinticProfile::TurboShake400,
                &committee,
                &SigningMode::SharedMessage(b"other"),
                &proof,
            ),
        )
    });
    report.check(
        "agg",
        "self-check",
        "2-to-1 aggregate verifies and binds its message",
        roundtrip == Some(true),
        String::new(),
    );
    Ok(())
}

fn core_checks(report: &mut Report, kat: &Json) -> Result<(), CliError> {
    let v = kat
        .get("fips205_slh_dsa_shake_128f")
        .ok_or_else(|| CliError::input("KAT file lacks fips205"))?;
    let params = Fips205Params::SLH_DSA_SHAKE_128F;
    let keygen = slh_keygen_internal(
        &params,
        &v.field_hex("sk_seed_hex")?,
        &v.field_hex("sk_prf_hex")?,
        &v.field_hex("pk_seed_hex")?,
    );
    let Ok((sk, pk)) = keygen else {
        report.check(
            "core",
            "external",
            "SLH-DSA-SHAKE-128f key generation",
            false,
            "keygen failed".into(),
        );
        return Ok(());
    };
    report.eq_hex(
        "core",
        "external",
        "SLH-DSA-SHAKE-128f public key",
        &pk.to_bytes(),
        v.field_str("pk_hex")?,
    );
    let message = v.field_str("msg_ascii")?.as_bytes();
    let ctx = v.field_hex("ctx_hex")?;
    let Ok(signature) = slh_sign(&params, message, &ctx, &sk, None) else {
        report.check(
            "core",
            "external",
            "SLH-DSA-SHAKE-128f deterministic signature",
            false,
            "signing failed".into(),
        );
        return Ok(());
    };
    let mut digest = [0u8; 32];
    shake256_xof(&signature, &mut digest);
    report.check(
        "core",
        "external",
        "SLH-DSA-SHAKE-128f signature length",
        signature.len() as u64 == v.field_u64("sig_bytes")?,
        String::new(),
    );
    report.eq_hex(
        "core",
        "external",
        "SLH-DSA-SHAKE-128f signature digest",
        &digest,
        v.field_str("sig_shake256_32")?,
    );
    report.eq_hex(
        "core",
        "external",
        "SLH-DSA-SHAKE-128f signature head",
        &signature[..64],
        v.field_str("sig_head_64_hex")?,
    );
    report.eq_hex(
        "core",
        "external",
        "SLH-DSA-SHAKE-128f signature tail",
        &signature[signature.len() - 64..],
        v.field_str("sig_tail_64_hex")?,
    );
    let mut tampered = signature.clone();
    tampered[signature.len() / 2] ^= 1;
    report.check(
        "core",
        "self-check",
        "SLH-DSA-SHAKE-128f verifies and rejects a flipped bit",
        slh_verify(&params, message, &signature, &ctx, &pk)
            && !slh_verify(&params, message, &tampered, &ctx, &pk),
        String::new(),
    );
    Ok(())
}

fn fts_checks(report: &mut Report) {
    for (profile, bytes) in [
        (FrontierFtsProfile::Compact1122, 1122),
        (FrontierFtsProfile::Full256Bit, 2338),
    ] {
        report.check(
            "fts",
            "self-check",
            &format!("{profile:?} signature is {bytes} bytes"),
            profile.signature_bytes() == bytes,
            String::new(),
        );
    }
    let profile = FrontierFtsProfile::Full256Bit;
    let mut key = FrontierFtsSigningKey::keygen(
        profile,
        [1; 32],
        [2; 32],
        [3; 32],
        true,
        &CpuReferenceBackend,
    );
    let journal_path = std::env::temp_dir().join(format!(
        "qsag-frontier-check-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    let wal = qsag_fts::FsWalFtsEpochLatch::create(&journal_path, key.wal_key(), [0x91; 32])
        .expect("create fresh test journal");
    key = key.attach_wal(Box::new(wal)).expect("attach test journal");
    let dp = FrontierDpTable::build(profile);
    let message = b"qsag kat few-time signature";
    let Ok(signature) = key.sign(&dp, message, &[0; 32]) else {
        report.check(
            "fts",
            "self-check",
            "Full256Bit signs",
            false,
            "signing failed".into(),
        );
        return;
    };
    let bytes = signature.to_bytes(profile);
    report.eq_hex(
        "fts",
        "regression",
        "Full256Bit public root",
        &key.pk.root,
        FTS_ROOT_HEX,
    );
    report.eq_hex(
        "fts",
        "regression",
        "Full256Bit signature digest",
        &sha256(&bytes),
        FTS_SIGNATURE_SHA256_HEX,
    );
    let other = verify_frontier_fts(&key.pk, &dp, b"another message", &signature);
    report.check(
        "fts",
        "self-check",
        "Full256Bit verifies and binds its message",
        verify_frontier_fts(&key.pk, &dp, message, &signature).is_ok() && other.is_err(),
        String::new(),
    );
    report.check(
        "fts",
        "self-check",
        "second signature is refused",
        key.sign(&dp, message, &[0; 32]).is_err(),
        String::new(),
    );
    drop(key);
    let _ = std::fs::remove_file(journal_path);
}

// Full256Bit (height 8, 72 frontier nodes), seeds [1; 32], [2; 32], [3; 32].
const FTS_ROOT_HEX: &str = "4c70f6f5579e3dc11c288dbf05174d791b992e2455dbd838a435f96e4cc7cd6d";
const FTS_SIGNATURE_SHA256_HEX: &str =
    "977e8805ea075ec406ddb7f1edead18228482d8df8a9db37dcd560b0bfe0c5e3";
const ADDRESS_REGRESSION: &str =
    "qsp1pqgpqzhcl2ngfursac8pe7cpd9e0302h5ged5cu5s8yha0lyq09vz2dxf08uvp4";

fn addr_checks(report: &mut Report) {
    // BIP-350 reference strings: valid Bech32m, and a valid legacy Bech32 string that must be refused.
    for valid in [
        "A1LQFN3A",
        "a1lqfn3a",
        "abcdef1l7aum6echk45nj3s0wdvt2fg8x9yrzpqzd3ryx",
    ] {
        report.check(
            "addr",
            "external",
            &format!("Bech32m accepts {valid}"),
            bech32m_decode_5bit(valid).is_ok(),
            String::new(),
        );
    }
    report.check(
        "addr",
        "external",
        "legacy Bech32 A12UEL5L is refused",
        bech32m_decode_5bit("A12UEL5L") == Err(AddrError::LegacyBech32Rejected),
        String::new(),
    );
    let address = QsagAddress::from_pubkey_cshake256(
        "qsp",
        qsag_addr::WitnessSuiteTag::SlhDsa128f,
        qsag_addr::KeyIdentityKind::SingleOrThreshold,
        &[0x42; 32],
    )
    .and_then(|a| a.encode());
    let encoded = address.unwrap_or_default();
    report.check(
        "addr",
        "regression",
        "address of a fixed public key",
        encoded == ADDRESS_REGRESSION,
        format!("got {encoded}"),
    );
    let mut corrupted = encoded.clone().into_bytes();
    if let Some(last) = corrupted.last_mut() {
        *last = if *last == b'q' { b'p' } else { b'q' };
    }
    let corrupted = String::from_utf8(corrupted).unwrap_or_default();
    report.check(
        "addr",
        "self-check",
        "address round-trips and a changed character is refused",
        QsagAddress::decode(&encoded)
            .and_then(|a| a.encode())
            .as_deref()
            == Ok(encoded.as_str())
            && QsagAddress::decode(&corrupted).is_err(),
        String::new(),
    );
}

pub fn run(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(raw, &[], &["json", "help"])?;
    if args.flag("help") {
        print!("{KAT_HELP}");
        return Ok(());
    }
    args.no_positionals()?;
    let kat = Json::parse(KAT_JSON)?;
    let mut report = Report { rows: Vec::new() };
    accel_checks(&mut report, &kat)?;
    core_checks(&mut report, &kat)?;
    fts_checks(&mut report);
    agg_checks(&mut report, &kat)?;
    addr_checks(&mut report);
    let policy_ok = crate::policy::evaluate_all().is_ok_and(|(_, _, all_match)| all_match);
    report.check(
        "policy",
        "self-check",
        "custody policy scenarios match expected outcomes",
        policy_ok,
        String::new(),
    );

    let failed = report.rows.iter().filter(|row| !row.3).count();
    if args.flag("json") {
        let rows = report
            .rows
            .iter()
            .map(|(name, group, origin, pass, detail)| {
                Json::object(vec![
                    ("crate", Json::str(*group)),
                    ("check", Json::str(name.clone())),
                    ("origin", Json::str(*origin)),
                    ("pass", Json::Bool(*pass)),
                    ("detail", Json::str(detail.clone())),
                ])
            })
            .collect();
        print!(
            "{}",
            Json::object(vec![
                ("passed", Json::num(report.rows.len() - failed)),
                ("failed", Json::num(failed)),
                ("checks", Json::Array(rows))
            ])
            .to_pretty()
        );
    } else {
        for (name, group, origin, pass, detail) in &report.rows {
            println!(
                "{} {group:<6} {origin:<10} {name}{}",
                if *pass { "ok  " } else { "FAIL" },
                if detail.is_empty() || *pass {
                    String::new()
                } else {
                    format!(" [{detail}]")
                }
            );
        }
        println!("{} passed, {failed} failed", report.rows.len() - failed);
    }
    if failed == 0 {
        Ok(())
    } else {
        Err(CliError::verify(format!(
            "{failed} known-answer checks failed"
        )))
    }
}
