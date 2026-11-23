//! `qsag`: key generation, signing, verification, succinct aggregation, addresses, a
//! persistent custody policy ledger, and known-answer tests for the qsag workspace.

#![forbid(unsafe_code)]

mod addr;
mod agg;
mod anchor;
mod cli;
mod codec;
mod cred;
// Trusted-dealer builds provision `fts-threshold` without the dealerless FTS ceremony.
#[cfg_attr(any(test, feature = "test-dealer"), allow(dead_code))]
mod dealerless_ceremony;
mod envelope;
mod hd;
mod kat;
mod keys;
mod migrate;
mod persist;
mod policy;
mod policy_caps;
mod policy_ledger;
mod quorum;
mod quorum_coupon;
mod quorum_hem;
mod quorum_wire;
mod schemes;
mod vault;

use std::process::ExitCode;

use cli::{Args, CliError, exit};

const HELP: &str = "\
qsag - post-quantum hash-based signatures, threshold quorum-switching, and succinct aggregation

usage: qsag <command> [options]        (every command accepts --help)

commands:
  info              list schemes with their security level and key, signature, and proof sizes
  keygen            generate a key pair (SLH-DSA, few-time, threshold few-time, or a committee)
  sign              sign a message file
  verify            verify a signature
  addr              encode or decode addresses; derive a hybrid classical + post-quantum identity
  quorum            dealerless threshold signing & (t, n) -> (t', n') quorum-switching (sign/reshare/refresh)
  aggregate         untrusted public or committee signature aggregation (`QSAGHQM2` Quintic Fp5)
  verify-aggregate  verify an aggregate proof (alias: verify-agg)
  cred              dealerless Poseidon2 TOPRF (replicated or Shamir-SPDZ) & threshold FIPS 204 ML-DSA ceremonies
  hd                dealerless post-quantum HD inventory & 0-round watch-only child derivation
  migrate           prove that a legacy key (Bitcoin, Ethereum, Ed25519, BIP-32) authorises a
                    post-quantum address; verify; one-way migration registry
  policy            persistent custody policy ledger (init, propose, approve, status) and
                    attenuated capabilities (macaroon, biscuit)
  kat               run the built-in known-answer tests

exit codes:
  0  success                     3  denied by policy
  1  usage or malformed input    4  stateful key or registry refused (budget, epoch, journal,
  2  verification failed            rollback, or a migration already recorded differently)
                                 5  file system or entropy failure

Secret keys are only ever read from files, never from the command line.
";

fn info(raw: &[String]) -> Result<(), CliError> {
    let args = Args::parse(raw, &[], &["json", "help"])?;
    if args.flag("help") {
        println!(
            "qsag info [--json]\n\nList every supported scheme with its security level and sizes."
        );
        return Ok(());
    }
    args.no_positionals()?;
    if args.flag("json") {
        print!("{}", schemes::info_json().to_pretty());
    } else {
        print!("{}", schemes::info_text());
    }
    Ok(())
}

fn run(raw: &[String]) -> Result<(), CliError> {
    let Some((command, rest)) = raw.split_first() else {
        eprint!("{HELP}");
        return Err(CliError::usage("no command given"));
    };
    match command.as_str() {
        "--help" | "-h" | "help" => {
            print!("{HELP}");
            Ok(())
        }
        "--version" | "-V" => {
            println!("qsag {}", env!("CARGO_PKG_VERSION"));
            Ok(())
        }
        "info" => info(rest),
        "keygen" => keys::keygen(rest),
        "sign" => keys::sign(rest),
        "verify" => keys::verify(rest),
        "addr" => addr::run(rest),
        "quorum" => quorum::run(rest),
        "aggregate" => agg::aggregate(rest),
        "verify-agg" | "verify-aggregate" => agg::verify_agg(rest),
        "cred" => cred::run(rest),
        "hd" => hd::run(rest),
        "migrate" => migrate::run(rest),
        "policy" | "policy-demo" => policy::run(rest),
        "kat" => kat::run(rest),
        other => Err(CliError::usage(format!(
            "unknown command '{other}' (try --help)"
        ))),
    }
}

fn main() -> ExitCode {
    let mut raw = cli::SecretArgs(Vec::new());
    for arg in std::env::args_os().skip(1) {
        match arg.into_string() {
            Ok(arg) => raw.0.push(arg),
            Err(arg) => {
                drop(cli::ZeroizingBuf::new(arg.into_encoded_bytes()));
                eprintln!("qsag: error: arguments must be valid UTF-8");
                return ExitCode::from(exit::USAGE);
            }
        }
    }
    match run(&raw.0) {
        Ok(()) => ExitCode::from(exit::OK),
        Err(err) => {
            eprintln!("qsag: error: {err}");
            ExitCode::from(err.code)
        }
    }
}
