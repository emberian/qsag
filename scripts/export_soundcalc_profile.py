#!/usr/bin/env python3
"""Export HemQuintic128 and zk-Hem v2 [DKT26] schedules and packed-fiber QROM bounds.

The schedule rows come from the Lean packed-fiber certificates. The calculator
evaluates packedProdQromError + merkleProfileQromBound at Q = 2^64 using exact
fractions. PublicHemQuintic128.lean separately accounts for the public transcript.
"""

import argparse
import json
import re
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CERT = Path("lean/Qsag/Protocol/Aggregation/ZkHemV2PackedFiberCerts.lean")
PARAMS = Path("crates/qsag-agg/src/zk_hem/v2/params.rs")
GOLDILOCKS_P = 2**64 - 2**32 + 1
FIELD_CARD = GOLDILOCKS_P**5
QUERY_CAP = 2**64
SEEDS = 2**400


@dataclass(frozen=True)
class Stage:
    # WhirStage in ClosedWhirSchedule.lean, in constructor order.
    folds: int
    log_domain: int
    log_blowup: int
    ood: int
    queries: int
    degree: int
    agreement: int
    eta_num: int
    eta_den: int
    list_size: int
    sumcheck_degree: int
    mca_num: int

    def round_error_sum(self):
        fold = Fraction(self.list_size * self.sumcheck_degree + self.mca_num, FIELD_CARD)
        pairs = self.list_size * (self.list_size - 1) // 2
        ood = Fraction((SEEDS // FIELD_CARD + 1) * pairs * self.degree, SEEDS)
        shift = (Fraction(self.agreement + self.folds, 2**self.log_domain) ** self.queries
                 + Fraction(self.list_size * (self.queries + self.ood), FIELD_CARD))
        return self.folds * fold + ood + shift


def load_stages(repo):
    source = (repo / CERT).read_text()
    body = source.split("def packedProdStages :", 1)[1].split("| _ => []", 1)[0]
    schedules = {}
    for n, row in re.findall(r"\|\s*(\d+)\s*=>\s*\[([^\]]+)\]", body):
        stages = [Stage(*map(int, values.split(","))) for values in re.findall(r"⟨([^⟩]+)⟩", row)]
        if not stages or int(n) in schedules:
            raise ValueError(f"empty or repeated packed-fiber schedule {n}")
        schedules[int(n)] = stages
    if sorted(schedules) != list(range(16, 29)):
        raise ValueError(f"expected all 13 schedules in {CERT}")
    return schedules


def packed_error_bits(schedule_error, digest_card):
    error = schedule_error + Fraction(6680 * QUERY_CAP**3, digest_card)
    if error >= Fraction(1, 2**128):
        raise ValueError("packed-fiber QROM budget exceeds the certified threshold")
    # floor(-log2(error)), without floating-point rounding
    return (error.denominator // error.numerator).bit_length() - 1


def build(repo):
    circuits = []
    for n, stages in load_stages(repo).items():
        schedule_error = (2 * QUERY_CAP + 1)**2 * sum(s.round_error_sum() for s in stages)
        circuits.append({
            "num_variables": n,
            "whir_stage_log_blowups": [s.log_blowup for s in stages],
            "whir_stage_fold_vars": [s.folds for s in stages],
            "whir_num_queries": [s.queries for s in stages],
            "log_final_poly_len": n - sum(s.folds for s in stages),
            "packed_qrom_bits_400": packed_error_bits(schedule_error, SEEDS),
            "packed_qrom_bits_gl24": packed_error_bits(schedule_error, GOLDILOCKS_P**7),
        })
    return {
        "zkevm": {
            "name": "HemQuintic128 / zk-Hem v2",
            "field": "Fp5 = F_p[X]/(X^5 - 3)",
            "field_cardinality": str(FIELD_CARD),
            "public_wire": "QSAGHQM2",
            "public_canopies": ["TurboSHAKE256 (400 bits)", "Poseidon2-GL-w24 (448 bits)"],
            "committed_mask_wires": ["QSAGZKH2", "QSAGZKS2"],
            "committed_mask_canopies": ["cSHAKE256 (400 bits)", "TurboSHAKE256 (400 bits)"],
            "log2_qrom_queries": 64,
            "line_folding": "[DKT26] Theorem 5.12",
        },
        "circuits": circuits,
    }


def verify(repo, circuits):
    params = (repo / PARAMS).read_text()
    counts = re.search(r"pub const STAGE0_QUERIES:[^=]*=\s*\[([\d,\s]+)\]", params)
    if not counts:
        raise ValueError(f"missing Stage-0 query table in {PARAMS}")
    rust_counts = [int(n) for n in counts[1].split(",") if n.strip()]
    if rust_counts != [267] * 8 + [266] * 5 or rust_counts != [c["whir_num_queries"][0] for c in circuits]:
        raise ValueError("Stage-0 query counts differ from the deployed schedules")
    if "(532usize).div_ceil(blowup.trailing_zeros() as usize) + 3" not in params:
        raise ValueError("later-stage query rule changed")
    for c in circuits:
        logs = c["whir_stage_log_blowups"]
        if c["whir_num_queries"][1:] != [(532 + k - 1) // k + 3 for k in logs[1:]]:
            raise ValueError(f"later-stage queries disagree at log_cells={c['num_variables']}")
        if not 1 <= c["log_final_poly_len"] <= 8 or len(logs) != (3 if c["num_variables"] <= 22 else 4):
            raise ValueError(f"invalid schedule envelope at log_cells={c['num_variables']}")


def render_toml(doc):
    # All exported values are strings, integers or homogeneous arrays of either.
    sections = [("[zkevm]", doc["zkevm"])] + [("[[circuits]]", c) for c in doc["circuits"]]
    return "\n\n".join("\n".join([header, *(f"{k} = {json.dumps(v)}" for k, v in row.items())])
                       for header, row in sections)


def render_markdown(doc):
    meta = doc["zkevm"]
    lines = [
        f"# {meta['name']} [DKT26] schedules",
        "",
        f"`{meta['field']}` over the Goldilocks prime. Public `QSAGHQM2` Canopies use "
        + " or ".join(meta["public_canopies"]) + ".",
        "Committed-mask `QSAGZKH2` and `QSAGZKS2` use " + " or ".join(meta["committed_mask_canopies"]) + ".",
        "The last two columns evaluate the packed-fiber certificate at Q = 2^64, in whole bits.",
        "",
        "| log₂ cells | Fold variables per stage | Fiber queries per stage | Terminal variables | 400-bit | GL24 |",
        "| ---: | --- | --- | ---: | ---: | ---: |",
    ]
    for c in doc["circuits"]:
        folds = "/".join(map(str, c["whir_stage_fold_vars"]))
        queries = "/".join(map(str, c["whir_num_queries"]))
        lines.append(f"| {c['num_variables']} | {folds} | {queries} | {c['log_final_poly_len']} | "
                     f"{c['packed_qrom_bits_400']} | {c['packed_qrom_bits_gl24']} |")
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    formats = parser.add_mutually_exclusive_group()
    formats.add_argument("--json", action="store_true", help="emit JSON")
    formats.add_argument("--toml", action="store_true", help="emit soundcalc-style circuit parameters")
    formats.add_argument("--verify", action="store_true", help="check Rust schedules and both commitment bounds")
    parser.add_argument("--repo", type=Path, default=ROOT, help="QSAG repository root")
    args = parser.parse_args()
    doc = build(args.repo)
    verify(args.repo, doc["circuits"])
    if args.verify:
        print("PASS: 13 [DKT26] schedules, Rust query counts and both packed-fiber QROM budgets")
    elif args.json:
        print(json.dumps(doc, indent=2))
    elif args.toml:
        print(render_toml(doc))
    else:
        print(render_markdown(doc))


if __name__ == "__main__":
    main()
