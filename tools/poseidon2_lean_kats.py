"""Refresh kernel-checked canonical Poseidon2 KATs from the independent dense reference."""
from pathlib import Path
from poseidon2_canonical_reference import *
root=Path(__file__).resolve().parents[1]
p=root/'lean/Qsag/Oracle/Poseidon2.lean'
if not p.exists(): p=root/'lean/Qsag/Poseidon2.lean'
t=p.read_text();t=t[:t.index('/-! ## 5.')]
t+="/-! ## 5. Build-Time Conformance Vectors Matching Rust and SPIR-V -/\n\n"
def state(x):return '⟨'+', '.join('⟨'+', '.join('Goldilocks.ofNat '+str(v) for v in x[i:i+4])+'⟩' for i in range(0,12,4))+'⟩'
for x in [[0]*12,list(range(12))]:
 t+=f'example : (poseidon2Perm12 {state(x)}).toList.map (·.val) =\n    {perm(x)} := by decide +kernel\n\n'
for msg in [b'',b'\0',bytes([1,2,3]),b'qsag-poseidon2-kat']:
 t+=f'example : poseidon2Hash32 {list(msg)} =\n    {list(hash32(msg))} := by decide +kernel\n\n'
t+=f'example : (let out := poseidon2CompressWeighted {state(list(range(12)))};\n    [out.x0.val, out.x1.val, out.x2.val, out.x3.val]) =\n    {compress(list(range(12)))} := by decide +kernel\n\nend Qsag\nend\n'
p.write_text(t)
