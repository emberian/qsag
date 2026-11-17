#!/usr/bin/env python3
"""Export the Hem WHIR PCS soundness profile in `ethereum/soundcalc` style.

Covers both aggregate signature profiles (`JortsPoseidon2`, `CorduroyPoseidon2`) under the
default `BciksJohnsonQrom128` schedule for `num_vars = 14..28`, over Goldilocks^4.

Two accountings are reported side by side, both in exact rational arithmetic (every blowup is
a power of four, so sqrt(rho) is rational; no floating point enters any bit count):

* `JBR(m)`: the soundcalc Johnson Bound Regime parameterization with an explicit multiplicity
  `m` (BCIKS20): proximity `1 - delta = sqrt(rho) (1 + 1/(2m))`, list size
  `L = (m + 1/2) / sqrt(rho)`, correlated-agreement error
  `(m + 1/2)^7 n^2 / (3 rho^(3/2) |F|)` per folded coordinate. Columns follow soundcalc's
  WHIR report (`whir_query`, `whir_proximity_gaps`, `whir_ood_rbr`, `whir_fold_rbr`,
  `whir_shift_rbr`, `whir_gamma_batching`). soundcalc uses one `m` per circuit; `--m` picks it,
  and `--m best` searches `1..=512` for the largest round-by-round total.
* `exact-witness`: the deployed finite witnesses of `crates/qsag-agg/src/pcs/affine_schedule.rs`
  (CWYZ26 Theorem 4.8 interpolation, exact Johnson list bounds, hypergeometric query error with
  the fold-coordinate loss, affine-combiner error), re-derived here exactly.

Security bits follow soundcalc's convention `bits(eps) = floor(-log2 eps)`; the circuit total
is the minimum over rounds (round-by-round soundness). The union-bound total over every round
of every stage is reported as well. `qrom` halves each round's bits (Grover search over
Fiat-Shamir challenges, including grinding), matching `WhirSecurityRegime::qrom_grover_round_bits`.
None of this is a complete Fiat-Shamir/QROM proof of the aggregate protocol: the row sumcheck,
constraint batching, Merkle hashing and cross-shard batching are accounted elsewhere.

    python3 scripts/export_soundcalc_profile.py            # Markdown tables to stdout
    python3 scripts/export_soundcalc_profile.py --json     # JSON document to stdout
    python3 scripts/export_soundcalc_profile.py --toml     # soundcalc-style circuit config
    python3 scripts/export_soundcalc_profile.py --verify   # self-test against the repository
"""

from __future__ import annotations

import argparse
import json
import math
import re
import sys
from fractions import Fraction
from pathlib import Path

GOLDILOCKS_P = 2**64 - 2**32 + 1
FIELD_SIZE = GOLDILOCKS_P**4  # Goldilocks^4 (`GoldilocksExt4`)
FIELD_NAME = "Goldilocks^4"
PCS_POW_BITS = 16
PCS_FOLD_POW_BITS = 16
OOD_SAMPLES = 2
MAX_BATCH_POLYS = 16
MAX_PCS_NUM_VARS = 28
LEAN_CERTIFIED_MAX_NUM_VARS = 24  # `hemJohnsonQromWitnessTable` stops here
LOG_TRACE_COLS = 8
HASH_SIZE_BITS = 256  # cSHAKE256 Merkle digests
NUM_VARS_RANGE = range(14, MAX_PCS_NUM_VARS + 1)
ROWS_PER_SIGNER = {"JortsPoseidon2": 512, "CorduroyPoseidon2": 8192}

# Verbatim copy of `crates/qsag-agg/src/pcs/affine_schedule.rs::WITNESSES`:
# (num_vars, stage, A, m, D). `--verify` checks it against the Rust and Lean sources.
WITNESSES = [
    (9, 1, 127, 1, 20), (10, 0, 329, 1, 14), (10, 1, 126, 1, 20), (11, 0, 328, 1, 14),
    (11, 1, 126, 1, 20), (12, 0, 579, 4, 75), (12, 1, 310, 4, 59), (12, 2, 174, 8, 139),
    (13, 0, 1091, 8, 143), (13, 1, 570, 16, 351), (13, 2, 173, 8, 135),
    (14, 0, 2119, 32, 863), (14, 1, 1092, 32, 860), (14, 2, 308, 32, 706),
    (15, 0, 4178, 64, 2079), (15, 1, 1091, 32, 844), (15, 2, 308, 32, 706),
    (16, 0, 8296, 128, 5567), (16, 1, 2137, 64, 2392), (16, 2, 580, 64, 1921),
    (17, 0, 8295, 128, 5503), (17, 1, 2137, 64, 2392), (17, 2, 307, 32, 691),
    (18, 0, 16531, 128, 7295), (18, 1, 4229, 64, 3418), (18, 2, 579, 64, 1890),
    (19, 0, 33003, 128, 10879), (19, 1, 8413, 64, 5471), (19, 2, 1124, 32, 1305),
    (20, 0, 65948, 128, 18111), (20, 1, 16782, 32, 3286), (20, 2, 2215, 32, 2149),
    (21, 0, 65947, 128, 18047), (21, 1, 16782, 32, 3286), (21, 2, 2215, 32, 2149),
    (22, 0, 131836, 128, 32511), (22, 1, 16781, 32, 3270), (22, 2, 2215, 32, 2149),
    (23, 0, 263614, 64, 14494), (23, 1, 33518, 32, 5870), (23, 2, 8759, 16, 2733),
    (23, 3, 2254, 32, 2672), (24, 0, 527170, 64, 27164), (24, 1, 66992, 32, 11069),
    (24, 2, 17484, 16, 5228), (24, 3, 4482, 16, 2067),
]

# Verbatim copy of `affine_schedule.rs::HIGH_CAPACITY_WITNESSES` (`num_vars = 25..28`). `--verify`
# checks it against the Rust source. These rows have no Lean certificate; every circuit reports
# `lean_witness_table` so the two populations are never merged silently.
HIGH_CAPACITY_WITNESSES = [
    (25, 0, 1054283, 128, 6353), (25, 1, 133941, 32, 1732), (25, 2, 17483, 16, 586),
    (25, 3, 4482, 16, 1049), (26, 0, 2108508, 128, 6359), (26, 1, 133940, 32, 1734),
    (26, 2, 17483, 16, 586), (26, 3, 4482, 16, 1049), (27, 0, 4216959, 128, 6361),
    (27, 1, 267837, 32, 1724), (27, 2, 34932, 16, 581), (27, 3, 4481, 16, 1056),
    (28, 0, 8433861, 128, 6362), (28, 1, 267836, 32, 1724), (28, 2, 34932, 16, 581),
    (28, 3, 4481, 16, 1056),
]

INF = None  # an error of exactly zero (exhaustively queried stage)


# --------------------------------------------------------------------------------------------
# Schedule (mirror of `stage_geometry` + `WhirSecurityRegime::BciksJohnsonQrom128`)
# --------------------------------------------------------------------------------------------

def qrom_min_queries(log_b: int) -> int:
    return -(-512 // log_b) + 2


def stage_geometry(nv: int) -> tuple[int, list[tuple[int, int]]]:
    """(early_stop_vars, [(blowup, step_vars), ...]) for `2 <= nv <= 28`."""
    if not 2 <= nv <= MAX_PCS_NUM_VARS:
        raise ValueError(f"unsupported num_vars={nv}")
    if nv <= 6:
        es = 1 if nv <= 3 else 2
        return es, [(16, nv - es)]
    if nv <= 11:
        es = 3 if nv <= 8 else 4
        rem = nv - es
        s0 = -(-rem // 2)
        return es, [(4, s0), (16, rem - s0)]
    if nv <= 16:
        es = 4 if nv <= 13 else (5 if nv <= 15 else 6)
        rem = nv - es
        s0 = min(4, rem - 4)
        s1 = (rem - s0) // 2
        return es, [(4, s0), (16, s1), (64, rem - s0 - s1)]
    if nv <= 20:
        return nv - 12, [(4, 5), (16, 3), (64, 4)]
    return {
        21: (8, [(4, 6), (16, 3), (64, 4)]),
        22: (8, [(4, 6), (16, 4), (64, 4)]),
        23: (7, [(4, 6), (16, 4), (64, 3), (256, 3)]),
        24: (8, [(4, 6), (16, 4), (64, 3), (256, 3)]),
        25: (8, [(4, 6), (16, 4), (64, 4), (256, 3)]),
        26: (8, [(4, 6), (16, 5), (64, 4), (256, 3)]),
        27: (8, [(4, 6), (16, 5), (64, 4), (256, 4)]),
        28: (8, [(4, 6), (16, 6), (64, 4), (256, 4)]),
    }[nv]


def stages(nv: int) -> list[dict]:
    es, geo = stage_geometry(nv)
    rem, out = nv, []
    for index, (blowup, step) in enumerate(geo):
        rem -= step
        n = blowup << rem
        queries = qrom_min_queries(blowup.bit_length() - 1)
        out.append({
            "stage": index,
            "blowup": blowup,
            "log_blowup": blowup.bit_length() - 1,
            "step_vars": step,
            "remaining_vars": rem,
            "domain": n,
            "degree_bound": n // blowup + 2,
            "num_queries": queries,
            "exhaustive": queries >= n,
        })
    assert rem == es
    return out


# --------------------------------------------------------------------------------------------
# Exact bit accounting
# --------------------------------------------------------------------------------------------

def sec_bits(eps: Fraction | None) -> int | None:
    """Largest k with eps <= 2^-k (soundcalc's integer convention); None for eps == 0."""
    if eps is None or eps == 0:
        return None
    if eps >= 1:
        return 0
    num, den = eps.denominator, eps.numerator  # 1/eps = num/den > 1
    k = num.bit_length() - den.bit_length()
    while k > 0 and (den << k) > num:
        k -= 1
    while (den << (k + 1)) <= num:
        k += 1
    return k


def bits_float(eps: Fraction | None) -> float | None:
    if eps is None or eps == 0:
        return None
    # log2 of big integers is exact up to double rounding; display only.
    return round(math.log2(eps.denominator) - math.log2(eps.numerator), 2)


def pow2(k: int) -> Fraction:
    return Fraction(1, 1 << k)


def jbr_stage_errors(st: dict, m: int, batch: int) -> dict[str, Fraction | None]:
    """soundcalc-style JBR(m) round errors of one WHIR stage (BCIKS20 Johnson regime)."""
    if st["exhaustive"]:
        # Every fiber is opened: the folded oracle is checked exactly.
        return {k: None for k in ("whir_query", "whir_proximity_gaps", "whir_ood_rbr",
                                  "whir_fold_rbr", "whir_shift_rbr", "whir_gamma_batching")}
    rho = Fraction(1, st["blowup"])
    sqrt_rho = Fraction(1, math.isqrt(st["blowup"]))
    assert sqrt_rho * sqrt_rho == rho
    n, d, k, t = st["domain"], st["degree_bound"], st["step_vars"], st["num_queries"]
    big_f = Fraction(FIELD_SIZE)
    mh = Fraction(2 * m + 1, 2)
    agreement = sqrt_rho * (1 + Fraction(1, 2 * m))
    list_size = mh / sqrt_rho
    ca = mh**7 * n * n / (3 * rho * sqrt_rho * big_f)  # BCIKS20 Thm 1.2 (affine line)
    return {
        "whir_query": agreement**t * pow2(PCS_POW_BITS),
        "whir_proximity_gaps": min(Fraction(1), k * ca) * pow2(PCS_FOLD_POW_BITS),
        "whir_ood_rbr": min(Fraction(1), list_size * list_size / 2 * (Fraction(d) / big_f) ** OOD_SAMPLES),
        "whir_fold_rbr": min(Fraction(1), k * list_size * 3 / big_f) * pow2(PCS_FOLD_POW_BITS),
        "whir_shift_rbr": min(Fraction(1), list_size * (t + OOD_SAMPLES) / big_f),
        "whir_gamma_batching": (min(Fraction(1), (batch - 1) * ca) * pow2(PCS_FOLD_POW_BITS)
                                if st["stage"] == 0 and batch > 1 else None),
    }


def bits_le_bound(n: int) -> int:
    return n.bit_length()


def exact_witness_stage(nv: int, st: dict) -> dict:
    """Exact re-derivation of the deployed `finite_johnson_witnesses_cover_every_canonical_stage`."""
    if st["exhaustive"]:
        return {"witness": None, "checks": {}, "errors": {"query": None, "combiner": None}}
    row = next((w for w in WITNESSES + HIGH_CAPACITY_WITNESSES
                if w[0] == nv and w[1] == st["stage"]), None)
    if row is None:
        raise AssertionError(f"missing finite affine witness nv={nv} stage={st['stage']}")
    _, _, a, m, big_d = row
    n, d, loss, t = st["domain"], st["degree_bound"], st["step_vars"], st["num_queries"]
    b = a - 1
    big_m = min(big_d, (m * a - big_d - 1) // d)
    checks = {"parameters": big_m >= 1 and b < a and b * b > n * (d + 1)}
    lhs = sum((m * a - big_d - d * j) * (big_d - j + 1) for j in range(big_m + 1))
    rhs = n * sum((m - s) * (big_d - s + 1) for s in range(min(big_m, m - 1) + 1))
    checks["interpolation_eq_4_5"] = lhs > rhs
    # Hypergeometric all-hit probability for agreement a + loss, exact.
    agree = a + loss
    q_err = Fraction(1)
    if agree < t:
        q_err = Fraction(0)
    else:
        for i in range(t):
            q_err *= Fraction(agree - i, n - i)
    checks["query_error_below_2^-256"] = q_err <= pow2(256)
    list_b = n * (b - d - 1) // (b * b - n * (d + 1))
    list0 = n * (a - 1 - d) // ((a - 1) * (a - 1) - n * d)
    numerator_bits = max(
        2 * bits_le_bound(big_d),
        2 + 2 * bits_le_bound(d) + 2 * bits_le_bound(big_m) + 3 * bits_le_bound(big_d)
        + 2 * bits_le_bound(n),
    ) + 1
    checks["nonpersistent_numerator_below_2^255"] = bits_le_bound(loss) + numerator_bits < 255
    combiner_units = loss * (list_b + 2 * list0 + 1) + 1
    checks["combiner_units_below_2000"] = combiner_units < 2000
    return {
        "witness": {"A": a, "m": m, "D": big_d, "B": b, "M": big_m,
                    "list_B": list_b, "list_A": list0, "combiner_units": combiner_units},
        "checks": checks,
        "errors": {
            "query": (q_err * pow2(PCS_POW_BITS)) if q_err else None,
            # combiner_units / p^4 plus < 1/p^4 from the nonpersistent numerator,
            # multiplied by 2^-PCS_FOLD_POW_BITS from per-fold WHIR_FOLD_POW grinding.
            "combiner": Fraction(combiner_units + 1, FIELD_SIZE) * pow2(PCS_FOLD_POW_BITS),
        },
    }


def summarize(round_errors: dict[str, Fraction | None]) -> dict:
    live = {k: v for k, v in round_errors.items() if v}
    rbr = min((sec_bits(v) for v in live.values()), default=None)
    union = sum(live.values(), Fraction(0)) if live else None
    return {
        "rbr_total_bits": rbr,
        "union_bound_bits": sec_bits(union),
        "qrom_rbr_bits": None if rbr is None else rbr // 2,
    }


def circuit(profile: str, nv: int, m_choice: str, batch: int) -> dict:
    sts = stages(nv)
    slots_log = nv - LOG_TRACE_COLS - (ROWS_PER_SIGNER[profile].bit_length() - 1)
    reachable = 1 <= slots_log and nv <= MAX_PCS_NUM_VARS

    def jbr(m: int) -> dict:
        per_round: dict[str, Fraction | None] = {}
        per_stage = []
        for st in sts:
            errs = jbr_stage_errors(st, m, batch)
            per_stage.append({k: sec_bits(v) for k, v in errs.items()})
            for key, eps in errs.items():
                per_round[f"{key}[{st['stage']}]"] = eps
        cols: dict[str, int | None] = {}
        for key in ("whir_query", "whir_proximity_gaps", "whir_ood_rbr", "whir_fold_rbr",
                    "whir_shift_rbr", "whir_gamma_batching"):
            vals = [b for s in per_stage if (b := s[key]) is not None]
            cols[key] = min(vals) if vals else None
        return {"m": m, "columns": cols, "stages": per_stage, **summarize(per_round)}

    if m_choice == "best":
        best = max((jbr(m) for m in range(1, 513)),
                   key=lambda r: (r["rbr_total_bits"] or 0, r["union_bound_bits"] or 0, -r["m"]))
        jbr_rows = [jbr(2), best] if best["m"] != 2 else [best]
    else:
        jbr_rows = [jbr(int(m_choice))]

    exact_rounds: dict[str, Fraction | None] = {}
    exact_stages = []
    for st in sts:
        ex = exact_witness_stage(nv, st)
        exact_stages.append({
            "stage": st["stage"],
            "witness": ex["witness"],
            "checks": ex["checks"],
            "query_bits": sec_bits(ex["errors"]["query"]),
            "query_bits_float": bits_float(ex["errors"]["query"]),
            "combiner_bits": sec_bits(ex["errors"]["combiner"]),
        })
        exact_rounds[f"query[{st['stage']}]"] = ex["errors"]["query"]
        exact_rounds[f"combiner[{st['stage']}]"] = ex["errors"]["combiner"]

    return {
        "name": f"hem_{profile}_nv{nv}",
        "profile": profile,
        "num_vars": nv,
        "reachable_by_profile": reachable,
        "signers_per_shard": (1 << slots_log) if reachable else None,
        "field": FIELD_NAME,
        "field_bits": round(math.log2(FIELD_SIZE), 6),
        "hash_size_bits": HASH_SIZE_BITS,
        "pcs": "WHIR (affine monomial combiner, rate escalation)",
        "regime": "BciksJohnsonQrom128",
        "early_stop_vars": stage_geometry(nv)[0],
        "stages": sts,
        "pow_bits_per_stage": PCS_POW_BITS,
        "pow_bits_per_fold": PCS_FOLD_POW_BITS,
        "ood_samples": OOD_SAMPLES,
        "batch_polys": batch,
        "jbr": jbr_rows,
        "exact_witness": {"stages": exact_stages, **summarize(exact_rounds),
                          "lean_witness_table": nv <= LEAN_CERTIFIED_MAX_NUM_VARS,
                          "all_checks_pass": all(all(s["checks"].values()) for s in exact_stages)},
    }


def build(m_choice: str, batch: int) -> dict:
    return {
        "zkevm": {"name": "Hem", "version": "affine-monomial-v1", "field": FIELD_NAME,
                  "hash_size_bits": HASH_SIZE_BITS,
                  "bit_convention": "floor(-log2 eps); total = min over rounds (round-by-round)"},
        "circuits": [circuit(p, nv, m_choice, batch)
                     for p in ROWS_PER_SIGNER for nv in NUM_VARS_RANGE],
    }


# --------------------------------------------------------------------------------------------
# Renderers
# --------------------------------------------------------------------------------------------

def fmt(v) -> str:
    return "∞" if v is None else str(v)


def render_markdown(doc: dict) -> str:
    out = ["# 📊 Hem (WHIR over Goldilocks⁴, `BciksJohnsonQrom128`)", "",
           "Cells are bits of security (`floor(-log2 eps)`); ∞ marks exhaustively queried stages.",
           "`qrom` halves round-by-round bits (Grover). Rows marked † are not reachable by the",
           "profile's shard geometry (`num_vars = 8 + log2(slots) + log2(rows_per_signer)`, slots >= 2).",
           "In `exact-witness` rows, `whir_query` is the hypergeometric query error with the",
           "fold-coordinate loss plus PoW and `whir_proximity_gaps` is the affine-combiner error.",
           ""]
    for profile in ROWS_PER_SIGNER:
        out += [f"## {profile}", "",
                "| num_vars | signers/shard | queries/stage | regime | total | union | qrom | "
                "whir_query | whir_proximity_gaps | whir_ood_rbr | whir_fold_rbr | "
                "whir_shift_rbr | whir_gamma_batching |",
                "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |"]
        for c in doc["circuits"]:
            if c["profile"] != profile:
                continue
            nv = f"{c['num_vars']}" + ("" if c["reachable_by_profile"] else " †")
            sig = fmt(c["signers_per_shard"]) if c["reachable_by_profile"] else "—"
            qs = "/".join(("∀" if s["exhaustive"] else str(s["num_queries"])) for s in c["stages"])
            for r in c["jbr"]:
                col = r["columns"]
                out.append(
                    f"| {nv} | {sig} | {qs} | JBR(m={r['m']}) | {fmt(r['rbr_total_bits'])} | "
                    f"{fmt(r['union_bound_bits'])} | {fmt(r['qrom_rbr_bits'])} | "
                    + " | ".join(fmt(col[k]) for k in ("whir_query", "whir_proximity_gaps",
                                                       "whir_ood_rbr", "whir_fold_rbr",
                                                       "whir_shift_rbr", "whir_gamma_batching"))
                    + " |")
            ex = c["exact_witness"]
            qmin = min((s["query_bits"] for s in ex["stages"] if s["query_bits"] is not None),
                       default=None)
            cmin = min((s["combiner_bits"] for s in ex["stages"] if s["combiner_bits"] is not None),
                       default=None)
            out.append(f"| {nv} | {sig} | {qs} | exact-witness | {fmt(ex['rbr_total_bits'])} | "
                       f"{fmt(ex['union_bound_bits'])} | {fmt(ex['qrom_rbr_bits'])} | {fmt(qmin)} | "
                       f"{fmt(cmin)} | — | — | — | — |")
        out.append("")
    return "\n".join(out)


def render_toml(doc: dict) -> str:
    out = ["# Hem soundness model in soundcalc circuit style. Per-stage blowups escalate",
           "# (WHIR rate escalation), so `whir_stage_log_blowups` extends soundcalc's single",
           "# `log_blowup`; `whir_stage_fold_vars` lists the variables folded per stage.", "",
           "[zkevm]", 'name = "Hem"', f'field = "{FIELD_NAME}"', 'version = "affine-monomial-v1"',
           f"hash_size_bits = {HASH_SIZE_BITS}", ""]
    for c in doc["circuits"]:
        if not c["reachable_by_profile"]:
            continue
        m = c["jbr"][-1]["m"]
        out += ["[[circuits]]", f'name = "{c["name"]}"', 'protocol_family = "WHIR"',
                f"num_variables = {c['num_vars']}",
                f"whir_stage_log_blowups = {[s['log_blowup'] for s in c['stages']]}",
                f"whir_stage_fold_vars = {[s['step_vars'] for s in c['stages']]}",
                f"whir_num_queries = {[s['num_queries'] for s in c['stages']]}",
                f"whir_query_pow_bits = {PCS_POW_BITS}", f"whir_folding_pow_bits = {PCS_FOLD_POW_BITS}",
                f"whir_ood_samples = {OOD_SAMPLES}", f"log_final_poly_len = {c['early_stop_vars']}",
                f"batch_size = {c['batch_polys']}", 'explicit_regime = "list"',
                f"explicit_m = {m}", ""]
    return "\n".join(out)


def to_json(doc: dict) -> str:
    return json.dumps(doc, indent=2, sort_keys=True, ensure_ascii=False)


# --------------------------------------------------------------------------------------------
# Self-test
# --------------------------------------------------------------------------------------------

def verify(root: Path) -> None:
    failures: list[str] = []

    def check(ok: bool, what: str) -> None:
        print(("PASS " if ok else "FAIL ") + what)
        if not ok:
            failures.append(what)

    check([qrom_min_queries(lb) for lb in (2, 4, 6, 8)] == [258, 130, 88, 66],
          "QROM schedule (258,130,88,66) at blowups (4,16,64,256)")
    check(sec_bits(pow2(128)) == 128 and sec_bits(Fraction(3, 1 << 130)) == 128
          and sec_bits(Fraction(1, 3)) == 1 and sec_bits(Fraction(1)) == 0,
          "sec_bits integer convention")

    geometry_ok, seen, keys = True, 0, set()
    for nv in range(2, MAX_PCS_NUM_VARS + 1):
        es, geo = stage_geometry(nv)
        geometry_ok &= 1 <= es <= 8 and es + sum(s for _, s in geo) == nv and len(geo) <= 4
        geometry_ok &= all(1 <= s <= 6 for _, s in geo)
        for st in stages(nv):
            geometry_ok &= st["domain"] <= 1 << 31
            if st["exhaustive"]:
                continue
            seen += 1
            keys.add((nv, st["stage"]))
            ex = exact_witness_stage(nv, st)
            check(all(ex["checks"].values()), f"exact witness nv={nv} stage={st['stage']}")
    check(geometry_ok, "stage geometry invariants for num_vars 2..28")
    every = WITNESSES + HIGH_CAPACITY_WITNESSES
    check(len(WITNESSES) == 46 and len(HIGH_CAPACITY_WITNESSES) == 16
          and all(w[0] <= LEAN_CERTIFIED_MAX_NUM_VARS for w in WITNESSES)
          and all(w[0] > LEAN_CERTIFIED_MAX_NUM_VARS for w in HIGH_CAPACITY_WITNESSES)
          and seen == len(every) and keys == {(w[0], w[1]) for w in every},
          "every non-exhaustive canonical stage has exactly one witness (46 Lean-backed + 16 Rust-only)")
    check(FIELD_SIZE > 127**2 * 2**242 and FIELD_SIZE > 2000 * 2**245,
          "p^4 > 2000 * 2^245 (combiner bits > 245)")

    pattern = r"\(\s*(\d+),\s*(\d+),\s*(\d+),\s*(\d+),\s*(\d+)\s*\)"
    table = [tuple(int(x) for x in w) for w in WITNESSES]
    rust_path = root / "crates/qsag-agg/src/pcs/affine_schedule.rs"
    if rust_path.exists():
        rust = rust_path.read_text().split("const WITNESSES:", 1)[1].split("];", 1)[0]
        rows = [tuple(int(x) for x in r) for r in re.findall(pattern, rust)]
        check(rows == table, "embedded witness table matches affine_schedule.rs")
        rust = rust_path.read_text().split("const HIGH_CAPACITY_WITNESSES:", 1)[1].split("];", 1)[0]
        rows = [tuple(int(x) for x in r) for r in re.findall(pattern, rust)]
        check(rows == [tuple(w) for w in HIGH_CAPACITY_WITNESSES],
              "embedded high-capacity witness table matches affine_schedule.rs")
    else:
        check(False, f"missing {rust_path}")
    lean_path = root / "lean/Qsag/Coding/Cwyz26.lean"
    if lean_path.exists():
        lean = lean_path.read_text().split("def hemJohnsonQromWitnessTable :", 1)[1]
        lean = lean.split("def hemJohnsonQromTableRow", 1)[0]
        rows = [tuple(int(x) for x in r) for r in re.findall(pattern, lean)]
        check(rows == table, "embedded witness table matches hemJohnsonQromWitnessTable")
    else:
        check(False, f"missing {lean_path}")
    pcs_path = root / "crates/qsag-agg/src/pcs.rs"
    affine_path = root / "crates/qsag-agg/src/pcs/affine.rs"
    trace_path = root / "crates/qsag-agg/src/trace.rs"
    sig_path = root / "crates/qsag-agg/src/sig.rs"
    for required in (pcs_path, affine_path, trace_path, sig_path):
        check(required.exists(), f"source cross-check input exists: {required.relative_to(root)}")
    if pcs_path.exists() and affine_path.exists():
        pcs = pcs_path.read_text()
        affine = affine_path.read_text()
        check("512usize.div_ceil(log_b) + 2" in pcs and "PCS_POW_BITS: u32 = 16" in pcs
              and f"MAX_PCS_NUM_VARS: usize = {MAX_PCS_NUM_VARS}" in pcs
              and "PCS_BATCH_POW" in pcs and "WHIR_FOLD_POW" in affine,
              "pcs.rs + pcs/affine.rs query budget, fold/batch/query PoW and num_vars cap match")
    if trace_path.exists() and sig_path.exists():
        trace = trace_path.read_text()
        sig = sig_path.read_text()
        rps_match = re.search(
            r"pub\s+const\s+fn\s+rows_per_signer\s*\(\s*profile\s*:\s*AggSigProfile\s*\)\s*->\s*usize\s*\{\s*"
            r"if\s+profile\.is_jorts\(\)\s*\{\s*(\d+)\s*\}\s*else\s*\{\s*(\d+)\s*\}",
            trace,
        )
        jorts_ok = (
            rps_match is not None
            and int(rps_match.group(1)) == ROWS_PER_SIGNER["JortsPoseidon2"]
            and int(rps_match.group(2)) == ROWS_PER_SIGNER["CorduroyPoseidon2"]
            and "Self::JortsPoseidon2 => Some(JORTS_XMSS_HEIGHT)" in sig
            and "Self::CorduroyPoseidon2 => None" in sig
            and "self.jorts_xmss_height().is_some()" in sig
        )
        check(jorts_ok and "LOG_TRACE_COLS: usize = 8" in trace and "NUM_TRACE_COLS: usize = 256" in trace,
              "trace.rs + sig.rs profile.is_jorts() rows_per_signer and trace width match this model")

    doc = build("best", MAX_BATCH_POLYS)
    check(to_json(doc) == to_json(build("best", MAX_BATCH_POLYS)), "deterministic JSON output")
    reach = {p: [c["num_vars"] for c in doc["circuits"]
                 if c["profile"] == p and c["reachable_by_profile"]] for p in ROWS_PER_SIGNER}
    check(reach == {"JortsPoseidon2": list(range(18, 29)), "CorduroyPoseidon2": list(range(22, 29))},
          "profile reachability (Jorts 18..28, Corduroy 22..28)")
    ex_stages = [s for c in doc["circuits"] for s in c["exact_witness"]["stages"]
                 if s["witness"] is not None]
    check(all(s["query_bits"] >= 256 + PCS_POW_BITS for s in ex_stages),
          "exact-witness query rounds: >= 272 classical bits (136 after Grover halving)")
    check(all(s["combiner_bits"] >= 245 + PCS_FOLD_POW_BITS for s in ex_stages),
          "exact-witness combiner rounds: >= 261 classical bits (130 after Grover halving)")
    reach_ex = [c["exact_witness"]["qrom_rbr_bits"] for c in doc["circuits"]
                if c["reachable_by_profile"]]
    check(all(b is not None and b >= 130 for b in reach_ex),
          "all reachable Jorts/Corduroy exact-witness circuits: >= 130 QROM bits")
    if failures:
        sys.exit(f"{len(failures)} check(s) failed")
    print("all checks passed")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    fmt_group = ap.add_mutually_exclusive_group()
    fmt_group.add_argument("--json", action="store_true", help="emit JSON")
    fmt_group.add_argument("--toml", action="store_true", help="emit soundcalc-style config")
    fmt_group.add_argument("--verify", action="store_true", help="run the self-test")
    ap.add_argument("--m", default="best", help="JBR multiplicity: integer or 'best' (default)")
    ap.add_argument("--batch", type=int, default=MAX_BATCH_POLYS,
                    help=f"jointly committed polynomials (default {MAX_BATCH_POLYS})")
    ap.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1])
    args = ap.parse_args()
    if args.verify:
        verify(args.repo)
        return
    if not 1 <= args.batch <= MAX_BATCH_POLYS:
        ap.error(f"--batch must be in 1..={MAX_BATCH_POLYS}")
    if args.m != "best" and not (args.m.isdigit() and int(args.m) >= 1):
        ap.error("--m must be a positive integer or 'best'")
    doc = build(args.m, args.batch)
    if args.json:
        print(to_json(doc))
    elif args.toml:
        print(render_toml(doc))
    else:
        print(render_markdown(doc))


if __name__ == "__main__":
    main()
