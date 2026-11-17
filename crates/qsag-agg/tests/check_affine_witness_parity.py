"""Check the deployed Rust witness table against its Lean certificate (no build)."""
from pathlib import Path
import re

root = Path(__file__).resolve().parents[3]
rust = (root / "crates/qsag-agg/src/pcs/affine_schedule.rs").read_text()
lean = (root / "lean/Qsag/Coding/Cwyz26.lean").read_text()
rust_table = rust.split("const WITNESSES:", 1)[1].split("];", 1)[0]
lean_table = lean.split("def hemJohnsonQromWitnessTable :", 1)[1].split(
    "def hemJohnsonQromTableRow", 1
)[0]
pattern = r"\(\s*(\d+),\s*(\d+),\s*(\d+),\s*(\d+),\s*(\d+)\s*\)"
rust_rows = re.findall(pattern, rust_table)
lean_rows = re.findall(pattern, lean_table)
assert rust_rows and rust_rows == lean_rows, "Rust/Lean witness table drift"
assert "whirAffineStageSimpleNum w + 1 < 2000" in lean
assert "loss * (list + 2 * list0 + 1) + 1 < 2000" in rust
print(f"PASS: {len(rust_rows)} deployed witness rows and folding thresholds match")
