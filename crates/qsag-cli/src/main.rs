//! `qsag`: key generation, signing, verification, succinct aggregation, addresses, a custody
//! policy demonstration, and known-answer tests for the qsag workspace.

#![forbid(unsafe_code)]

mod addr;
mod agg;
mod cli;
mod codec;
mod kat;
mod keys;
mod policy;
mod schemes;
mod vault;

use std::process::ExitCode;

use cli::{Args, CliError, exit};

const HELP: &str = "\
qsag - post-quantum hash-based signatures, threshold few-time signatures, and succinct aggregation

usage: qsag <command> [options]        (every command accepts --help)

commands:
  info          list schemes with their security level and key, signature, and proof sizes
  keygen        generate a key pair (SLH-DSA, few-time, threshold few-time, or a committee)
  sign          sign a message file
  verify        verify a signature
  addr          encode or decode addresses; derive a hybrid classical + post-quantum identity
  aggregate     aggregate committee signatures into one succinct proof, or merge two proofs
  verify-agg    verify an aggregate proof
  policy-demo   evaluate a custody policy against transfer scenarios
  kat           run the built-in known-answer tests

exit codes:
  0  success                     3  denied by policy
  1  usage or malformed input    4  stateful key refused (budget, epoch, or journal conflict)
  2  verification failed         5  file system or entropy failure

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
        "aggregate" => agg::aggregate(rest),
        "verify-agg" => agg::verify_agg(rest),
        "policy-demo" => policy::run(rest),
        "kat" => kat::run(rest),
        other => Err(CliError::usage(format!(
            "unknown command '{other}' (try --help)"
        ))),
    }
}

fn main() -> ExitCode {
    let raw: Vec<String> = match std::env::args_os()
        .skip(1)
        .map(|a| a.into_string())
        .collect()
    {
        Ok(raw) => raw,
        Err(_) => {
            eprintln!("qsag: error: arguments must be valid UTF-8");
            return ExitCode::from(exit::USAGE);
        }
    };
    match run(&raw) {
        Ok(()) => ExitCode::from(exit::OK),
        Err(err) => {
            eprintln!("qsag: error: {err}");
            ExitCode::from(err.code)
        }
    }
}
