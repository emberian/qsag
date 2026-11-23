#!/usr/bin/env bash
# Map and time both verifier configurations on the two 130 nm foundry libraries.
set -euo pipefail
cd "$(dirname "$0")/.."
exec bash tb/verify_auto.sh foundry
