#!/usr/bin/env bash
set -euo pipefail
[[ $(uname -s) == Linux ]] || { echo "Run on bb2" >&2; exit 2; }
here=$(cd "$(dirname "$0")" && pwd)
crate=$(cd "${ASS2_CRATE:-$here/../../../crates/qsag-ass2}" && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/ass2-rust.XXXXXXXX")
trap 'rm -rf "$work"' EXIT
cp "$here/check_vm.rs" "$work/main.rs"
cat > "$work/Cargo.toml" <<TOML
[workspace]
[package]
name = "ass2-vector-replay"
version = "0.1.0"
edition = "2024"
[[bin]]
name = "ass2-vector-replay"
path = "main.rs"
[dependencies]
qsag-ass2 = { path = "$crate" }
TOML
CARGO_TARGET_DIR="$work/target" cargo run --quiet --manifest-path "$work/Cargo.toml" -- "${1:?vector file}"
