#!/usr/bin/env python3
"""Generate the Quintic Hem wire-size, consensus and synthesized verifier tables."""

import argparse
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DOC = ROOT / "docs/QUORUM_AND_CONSENSUS_SCALING.md"
BEGIN = "<!-- BEGIN GENERATED SCALING TABLES -->"
END = "<!-- END GENERATED SCALING TABLES -->"
IVC_BYTES = 639_673
SPARSE_VECTORS = (("TurboShake400", 50, 360_391), ("Poseidon2Gl24", 56, 381_661))
COMPACT_VOTE_BYTES = 1122
WOTS_CHAINS = 128
JORTS_HEIGHT = 6
JORTS_MAX_HEIGHT = 20
ALPENGLOW_VOTES = 64
FINALITY_REGIONS = 2
VALIDATORS_PER_REGION = 32
STAGE0_QUERIES = {n: 267 if n <= 23 else 266 for n in range(16, 29)}


def jorts_bytes(height):
    return 32 + 4 + 4 + 32 * (WOTS_CHAINS + height)


def bitmap_certificate_bytes(validators):
    """Comparison format with one 96-byte signature and an N-bit bitmap."""
    return 96 + (validators + 7) // 8


def table(headers, rows):
    def line(row):
        return "| " + " | ".join(str(cell) for cell in row) + " |"

    return "\n".join([line(headers), line(["---"] * len(headers)), *map(line, rows)])


def ivc_table(link_mbps):
    transfer_ms = IVC_BYTES * 8 / (link_mbps * 1000)
    return table(
        ("Binary depth", "Leaf shards", "Internal merges", "Root bytes",
         f"Root transfer at {link_mbps:g} Mbit/s (ms)"),
        [(depth, f"{2**depth:,}", f"{2**depth - 1:,}", f"{IVC_BYTES:,}", f"{transfer_ms:.2f}")
         for depth in (1, 2, 3, 4, 8, 12, 16)],
    )


def generated(link_mbps=100):
    signers = FINALITY_REGIONS * VALIDATORS_PER_REGION
    return "\n\n".join([
        BEGIN,
        "### Sparse HemQuintic128 wire vectors (`QSAGHQM2`)",
        table(("Canopy", "Digest bytes", "Encoded bytes, 3 of 4 active"),
              [(name, digest, f"{size:,}") for name, digest, size in SPARSE_VECTORS]),
        "### [DKT26] packed-fiber schedules",
        table(("log₂ cells", "Stage-0 fiber queries"), [("16–23", STAGE0_QUERIES[16]), ("24–28", STAGE0_QUERIES[24])]),
        "### Binary IVC (`QSAGIVC1`)",
        ivc_table(link_mbps),
        "### Signature payloads in the Alpenglow example",
        table(("Workload", "Signatures", "Bytes per signature", "Raw signature bytes"),
              [("Votor Compact1122", ALPENGLOW_VOTES, f"{COMPACT_VOTE_BYTES:,}",
                f"{ALPENGLOW_VOTES * COMPACT_VOTE_BYTES:,}"),
               (f"Jorts finality, {FINALITY_REGIONS} regions × {VALIDATORS_PER_REGION}", signers,
                f"{jorts_bytes(JORTS_HEIGHT):,}", f"{signers * jorts_bytes(JORTS_HEIGHT):,}")]),
        "### Validator-set payload arithmetic",
        table(("Validators", "Raw Jorts signatures at height 20 (MiB)", "96 B signature + bitmap (B)"),
              [(f"{n:,}", f"{n * jorts_bytes(JORTS_MAX_HEIGHT) / 2**20:,.2f}",
                f"{bitmap_certificate_bytes(n):,}") for n in (1_500, 9_088, 10_000, 100_000, 1_048_576)]),
        "### Synthesized Verifier Hardware (`QSAG-NI v2`, measured)",
        table(("Target and configuration", "Mapped area or FPGA resources", "Routed clock"),
              [("IHP SG13G2, autonomous", "709.61 kGE", "—"),
               ("Sky130 HD, autonomous", "784.54 kGE", "—"),
               ("ECP5-85F, compact", "23,576 LUT4", "33.62 MHz"),
               ("ECP5-85F, full rate", "35,153 LUT4", "29.86 MHz"),
               ("`CL_QSAG_F2`, VU47P wrapper", "314,047 LUT1–6, 290 DSP48E2, 315 RAMB36E2", "—")]),
        END,
    ])


def check_sources():
    agg = Path("crates/qsag-agg")
    checks = {
        agg / "src/hem_quintic.rs": ['b"QSAGHQM2"', "TurboShake400 = 1", "Poseidon2Gl24 = 2",
                                     "tree::Hash<50>", "tree::Hash<56>", "params::schedule(log)"],
        agg / "src/hem_quintic/tests.rs": ["let active = [0, 2, 3]", "from_active_indices(4,",
                                          *(f"HemQuinticProfile::{name}, {size}," for name, _, size in SPARSE_VECTORS)],
        agg / "src/zk_hem/v2/params.rs": ["MIN_LOG_CELLS: usize = 16", "MAX_LOG_CELLS: usize = 28",
                                         str(list(STAGE0_QUERIES.values()))],
        agg / "src/recursive.rs": [r'b"QSAGHEM\x04"', "pub struct PreparedPolicyRegistry",
                                   "policy_registry_root: [u8; 32]"],
        agg / "src/zk_hem/recursive_ivc.rs": ["pub struct IvcSubtreeStatement", "shard_hi: u64"],
        agg / "src/zk_hem/recursive_ivc/wire.rs": ['b"QSAGIVC1"', "impl SuccinctIvcProof",
                                                   "PRODUCTION_TAG: u8 = 0"],
        agg / "src/zk_hem/recursive_ivc/tests.rs": [f"assert_eq!(SuccinctIvcProof::encoded_len(), {IVC_BYTES:_})"],
        agg / "src/sig.rs": [f"WOTS_CHAINS: usize = {WOTS_CHAINS}", f"JORTS_XMSS_HEIGHT: usize = {JORTS_HEIGHT}",
                             f"JORTS_MAX_XMSS_HEIGHT: usize = {JORTS_MAX_HEIGHT}",
                             "32 + 4 + 4 + WOTS_CHAINS * 32 + height * 32"],
        agg / "examples/mock_solana_alpenglow.rs": ["FrontierFtsProfile::Compact1122", f"run_votor_fts_section({ALPENGLOW_VOTES})",
                                                    f"run_hem_finality_section({FINALITY_REGIONS}, {VALIDATORS_PER_REGION})", "AggSigProfile::JortsPoseidon2"],
        Path("crates/qsag-fts/src/lib.rs"): [f"Compact1122.signature_bytes(), {COMPACT_VOTE_BYTES}"],
    }
    for path, tokens in checks.items():
        source = " ".join((ROOT / path).read_text().split())
        for token in tokens:
            if token not in source:
                raise ValueError(f"{path}: expected {token!r}")


def check_arithmetic():
    if (jorts_bytes(6), jorts_bytes(20)) != (4328, 4776):
        raise ValueError("Jorts signature-size mismatch")
    if (bitmap_certificate_bytes(9088), bitmap_certificate_bytes(9089)) != (1232, 1233):
        raise ValueError("bitmap byte-boundary mismatch")


def table_span(content):
    if content.count(BEGIN) != 1 or content.count(END) != 1:
        raise ValueError("expected one marked section in the scaling report")
    start = content.index(BEGIN)
    return start, content.index(END, start) + len(END)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true", help="check Rust sources and generated tables")
    parser.add_argument("--write-tables", action="store_true", help="refresh the companion report")
    parser.add_argument("--ivc", "--subtree-hologram", action="store_true", help="print only the binary IVC table")
    parser.add_argument("-o", "--output", type=Path, help="write the requested tables to a file")
    parser.add_argument("--link-mbps", type=float, default=100, help="link rate for payload transfer time")
    args = parser.parse_args()
    if not math.isfinite(args.link_mbps) or args.link_mbps <= 0:
        parser.error("--link-mbps must be finite and positive")
    if args.write_tables and args.link_mbps != 100:
        parser.error("--write-tables uses the default link rate")
    if args.output and args.output.resolve() in (DOC, Path(__file__).resolve()):
        parser.error("choose a separate output file")
    if args.self_test or args.write_tables:
        check_sources()
        check_arithmetic()
        content = DOC.read_text()
        start, end = table_span(content)
        if args.write_tables:
            DOC.write_text(content[:start] + generated() + content[end:])
        if args.self_test:
            content = DOC.read_text()
            start, end = table_span(content)
            if content[start:end] != generated():
                parser.exit(1, "scaling table drift: regenerate with --write-tables\n")
            print("PASS: live source guards and generated scaling tables")
    report = ivc_table(args.link_mbps) if args.ivc else generated(args.link_mbps)
    if args.output:
        args.output.write_text(report + "\n")
    if not (args.self_test or args.write_tables or args.output):
        print(report)


if __name__ == "__main__":
    main()
