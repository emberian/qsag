//! The signature schemes the command line can drive, and the `info` table.

use qsag_addr::WitnessSuiteTag;
use qsag_agg::AggSigProfile;
use qsag_core::fips205::Fips205Params;
use qsag_fts::{FrontierFtsProfile, ParallelSeededParams, ParallelSeededSignature};

use crate::cli::CliError;
use crate::codec::Json;

/// Production custody parameters: 1,024 one-time epochs.
pub const THRESHOLD_FTS_PARAMS: ParallelSeededParams = ParallelSeededParams::CUSTODY_H10_W5;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Scheme {
    /// FIPS 205 SLH-DSA-SHAKE, single signer, stateless.
    Slh(Fips205Params),
    /// FrontierSumFts few-time signature, single signer, stateful (profile-specific use limit).
    Frontier(FrontierFtsProfile),
    /// ParallelSeededFts threshold few-time signature; one signature per epoch.
    ThresholdFts,
    /// Validator committee for succinct aggregation (stateful, one signature per epoch).
    AggCommittee,
}

const FRONTIER: [(&str, FrontierFtsProfile); 5] = [
    ("fts-frontier-514", FrontierFtsProfile::Compact514),
    ("fts-frontier-770", FrontierFtsProfile::Compact770),
    ("fts-frontier-1314", FrontierFtsProfile::Compact1314),
    ("fts-compact-1122", FrontierFtsProfile::Compact1122),
    ("fts-frontier-2338", FrontierFtsProfile::Full256Bit),
];

impl Scheme {
    pub fn all() -> Vec<Scheme> {
        let mut all: Vec<Scheme> = Fips205Params::ALL_OFFICIAL
            .into_iter()
            .map(Scheme::Slh)
            .collect();
        all.extend(
            FRONTIER
                .iter()
                .map(|(_, profile)| Scheme::Frontier(*profile)),
        );
        all.extend([Scheme::ThresholdFts, Scheme::AggCommittee]);
        all
    }

    pub fn name(&self) -> String {
        match self {
            Scheme::Slh(params) => params.name.to_ascii_lowercase(),
            Scheme::Frontier(profile) => FRONTIER
                .iter()
                .find(|(_, p)| p == profile)
                .map_or("fts-frontier", |(name, _)| name)
                .to_string(),
            Scheme::ThresholdFts => "fts-threshold".to_string(),
            Scheme::AggCommittee => "agg-jorts-poseidon2".to_string(),
        }
    }

    pub fn by_name(name: &str) -> Result<Scheme, CliError> {
        // Historical misnomer: this profile has always emitted 2,338 bytes.
        if name.eq_ignore_ascii_case("fts-frontier-1058") {
            return Ok(Scheme::Frontier(FrontierFtsProfile::Full256Bit));
        }
        Scheme::all()
            .into_iter()
            .find(|s| s.name() == name.to_ascii_lowercase())
            .ok_or_else(|| {
                let known: Vec<String> = Scheme::all().iter().map(Scheme::name).collect();
                CliError::usage(format!(
                    "unknown scheme '{name}'; known schemes: {}",
                    known.join(", ")
                ))
            })
    }

    /// Address suite tag, for schemes whose public key has an address encoding.
    pub fn suite_tag(&self) -> Option<WitnessSuiteTag> {
        match self {
            Scheme::Slh(params) => Some(match params.name {
                "SLH-DSA-SHAKE-128s" => WitnessSuiteTag::SlhDsa128s,
                "SLH-DSA-SHAKE-128f" => WitnessSuiteTag::SlhDsa128f,
                "SLH-DSA-SHAKE-192s" => WitnessSuiteTag::SlhDsa192s,
                "SLH-DSA-SHAKE-192f" => WitnessSuiteTag::SlhDsa192f,
                "SLH-DSA-SHAKE-256s" => WitnessSuiteTag::SlhDsa256s,
                "SLH-DSA-SHAKE-256f" => WitnessSuiteTag::SlhDsa256f,
                _ => return None,
            }),
            Scheme::Frontier(_) => Some(WitnessSuiteTag::FrontierSumFts),
            Scheme::ThresholdFts => Some(WitnessSuiteTag::ParallelSeededFts),
            Scheme::AggCommittee => None,
        }
    }

    fn info(&self) -> Json {
        let (family, security, public_key_bytes, signature_bytes, state) = match self {
            Scheme::Slh(p) => (
                "FIPS 205 SLH-DSA (stateless hash-based)",
                format!(
                    "NIST category {}",
                    match p.n {
                        16 => 1,
                        24 => 3,
                        _ => 5,
                    }
                ),
                p.pk_bytes(),
                p.sig_bytes(),
                "stateless",
            ),
            Scheme::Frontier(profile) => {
                let p = profile.params();
                (
                    "FrontierSumFts (few-time hash-based)",
                    format!(
                        "{}-bit generic Grover preimage ceiling; {}-byte hash nodes, at most {} signatures per key",
                        p.node_bytes * 4,
                        p.node_bytes,
                        p.max_safe_uses
                    ),
                    32 + p.node_bytes,
                    profile.signature_bytes(),
                    "stateful: use counter persisted before each signature",
                )
            }
            Scheme::ThresholdFts => (
                "ParallelSeededFts (threshold few-time, in-process ceremony with dealer setup)",
                format!(
                    "32-byte chain nodes, {} one-time epochs per key",
                    1u32 << THRESHOLD_FTS_PARAMS.tree_height
                ),
                64,
                ParallelSeededSignature::encoded_len(&THRESHOLD_FTS_PARAMS),
                "stateful: epoch burn journal persisted before each signature",
            ),
            Scheme::AggCommittee => (
                "Jorts-Poseidon2 validator committee for succinct K-to-1 aggregation",
                format!(
                    "{} one-time epochs per validator key",
                    1u32 << qsag_agg::sig::JORTS_XMSS_HEIGHT
                ),
                65,
                AggSigProfile::JortsPoseidon2.raw_signature_bytes(),
                "stateful: per-validator epoch write-ahead log",
            ),
        };
        Json::object(vec![
            ("scheme", Json::str(self.name())),
            ("family", Json::str(family)),
            ("security", Json::str(security)),
            ("public_key_bytes", Json::num(public_key_bytes)),
            ("signature_bytes", Json::num(signature_bytes)),
            ("state", Json::str(state)),
        ])
    }
}

pub fn info_json() -> Json {
    Json::object(vec![
        ("tool", Json::str("qsag")),
        ("version", Json::str(env!("CARGO_PKG_VERSION"))),
        (
            "schemes",
            Json::Array(Scheme::all().iter().map(Scheme::info).collect()),
        ),
        (
            "aggregation",
            Json::object(vec![
                (
                    "proof_system",
                    Json::str(
                        "multilinear sumcheck over GoldilocksExt4 with multi-stage WHIR and Steiner CanopyMultiProof",
                    ),
                ),
                ("rs_blowup", Json::num(qsag_agg::RS_BLOWUP)),
                ("pow_bits", Json::num(qsag_agg::PCS_POW_BITS)),
            ]),
        ),
        (
            "address",
            Json::object(vec![
                (
                    "encoding",
                    Json::str(
                        "Bech32m, 35-byte program: suite tag, identity kind, 256-bit commitment",
                    ),
                ),
                (
                    "hybrid_suites",
                    Json::Array(vec![
                        Json::str("hybrid-secp256k1-mldsa44"),
                        Json::str("hybrid-ed25519-mldsa65"),
                    ]),
                ),
            ]),
        ),
    ])
}

pub fn info_text() -> String {
    let mut out = format!(
        "qsag {}\n\n{:<24} {:>9} {:>9}  security / state\n",
        env!("CARGO_PKG_VERSION"),
        "scheme",
        "pk bytes",
        "sig bytes"
    );
    for scheme in Scheme::all() {
        let info = scheme.info();
        let field = |key: &str| match info.get(key) {
            Some(Json::Str(s)) | Some(Json::Number(s)) => s.clone(),
            _ => String::new(),
        };
        out.push_str(&format!(
            "{:<24} {:>9} {:>9}  {}; {}\n",
            field("scheme"),
            field("public_key_bytes"),
            field("signature_bytes"),
            field("security"),
            field("state"),
        ));
    }
    out.push_str(&format!(
        "\naggregation: GoldilocksExt4 multi-stage WHIR with Steiner CanopyMultiProof, blowup {}, {} proof-of-work bits\n",
        qsag_agg::RS_BLOWUP,
        qsag_agg::PCS_POW_BITS
    ));
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn frontier_names_and_legacy_alias_match_wire_sizes() {
        let compact = Scheme::by_name("fts-compact-1122").unwrap();
        let full = Scheme::by_name("fts-frontier-2338").unwrap();
        assert_eq!(Scheme::by_name("fts-frontier-1058").unwrap(), full);
        assert_eq!(compact.info().field_u64("signature_bytes").unwrap(), 1122);
        assert_eq!(full.info().field_u64("signature_bytes").unwrap(), 2338);
    }
}
