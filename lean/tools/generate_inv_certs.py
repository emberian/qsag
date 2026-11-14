"""Turn the output of tools/GenInvCerts.lean into Qsag/ElfInvCerts.lean.
The certificates are untrusted proposals; Lean checks each one in ElfFixtureVerify.

  lake env lean tools/GenInvCerts.lean | python3 tools/generate_inv_certs.py
"""
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parents[1]
certs = {'x86': [], 'aarch64': []}
for line in sys.stdin:
    if not line.startswith('CERT '):
        continue
    _, arch, name, body = line.rstrip('\n').split(' ', 3)
    assert body != 'FAIL', name
    body = body.replace('Qsag.', '')
    body = re.sub(r'\b[A-Za-z_][A-Za-z0-9_]* := ', '', body)
    body = body.replace('{ ', '⟨').replace(' }', '⟩').replace('{', '⟨').replace('}', '⟩')
    body = body.replace(', some', ',\n  some')
    certs[arch].append((name, body))
assert len(certs['x86']) == 16 and len(certs['aarch64']) == 7, {k: len(v) for k, v in certs.items()}

out = '''module
/- Invariant certificates proposed by tools/GenInvCerts.lean (untrusted fixpoint inference run
outside the kernel). Each one is checked against its symbol's decoded bytes in ElfFixtureVerify. -/
public import Qsag.ElfBinaryVerify
public section
namespace Qsag
set_option autoImplicit false
set_option maxRecDepth 65536

'''
for arch, ty, ctor in [('x86', 'X86AbsState', 'x86'), ('aarch64', 'Arm64AbsState', 'arm')]:
    for i, (name, body) in enumerate(certs[arch]):
        out += f'/-- Proposed invariant for `{name}`. -/\ndef {arch}InvCert{i:02d} : PcMap {ty} :=\n  ⟨{body}⟩\n\n'
    items = ', '.join(f'.{ctor} {arch}InvCert{i:02d}' for i in range(len(certs[arch])))
    out += f'def {arch}InvCerts : List InvCert :=\n  [{items}]\n\n'
out += 'end Qsag\n'
(root / 'Qsag/ElfInvCerts.lean').write_text(out)
