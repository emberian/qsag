"""Propose normalized ELF slices; Lean proves correspondence with archive bytes.
This generator is not trusted and does not invoke any compiler or prover.
"""
from pathlib import Path
import re
import struct

root = Path(__file__).resolve().parents[1]
source = (root / 'Qsag/CompiledRlibFixtures.lean').read_text()

def slices(arch):
    length = int(re.search(rf'def {arch}RlibArchiveLen : Nat := (\d+)', source).group(1))
    literal = re.search(rf'def {arch}RlibArchiveNat : Nat :=\s+0x([0-9a-fA-F]+)', source).group(1)
    archive = int(literal, 16).to_bytes(length, 'little')
    assert archive[:8] == b'!<arch>\n'
    pos = 8
    result = []
    while pos < len(archive):
        size = int(archive[pos+48:pos+58])
        elf = archive[pos+60:pos+60+size]
        pos += 60 + size + size % 2
        if elf[:4] != b'\x7fELF':
            continue
        machine = struct.unpack_from('<H', elf, 18)[0]
        shoff = struct.unpack_from('<Q', elf, 40)[0]
        shnum, shstridx = struct.unpack_from('<HH', elf, 60)
        sections = [struct.unpack_from('<IIQQQQIIQQ', elf, shoff+64*i) for i in range(shnum)]
        def data(sh): return elf[sh[4]:sh[4]+sh[5]]
        names = data(sections[shstridx])
        ti, text = next((i, sh) for i, sh in enumerate(sections) if names[sh[0]:].split(b'\0', 1)[0] == b'.text')
        symtab = next(sh for sh in sections if sh[1] == 2)
        strings = data(sections[symtab[6]])
        for off in range(0, symtab[5], 24):
            name, info, _, section, value, size = struct.unpack_from('<IBBHQQ', data(symtab), off)
            if info >> 4 < 1 or info & 15 != 2 or section != ti or not size:
                continue
            assert value + size <= text[5]
            raw = strings[name:].split(b'\0', 1)[0]
            if raw.startswith(b'_'): raw = raw[1:]
            result.append((raw, machine, text[4], text[5], value, size, data(text)[value:value+size]))
    return result

def byte_list(bs): return '[' + ', '.join(f'0x{x:02x}' for x in bs) + ']'

out = '''module
/- Normalized fixture slices proposed by tools/generate_fixture_slices.py.
Their equality to extraction from the original archives is proved in ElfParse. -/
public section
namespace Qsag

structure ElfFuncSlice where
  name : String
  nameBytes : List UInt8
  machine : Nat
  textFileOffset : Nat
  textSize : Nat
  symValue : Nat
  symSize : Nat
  code : List UInt8
  deriving DecidableEq, Repr

'''
for arch, count in [('x86', 16), ('aarch64', 7)]:
    fs = slices(arch)
    assert len(fs) == count
    out += f'@[expose] def {arch}ExtractedSlices : List ElfFuncSlice := [\n'
    records = []
    for name, machine, offset, textsize, value, size, code in fs:
        records.append(f'''  {{ name := "{name.decode('ascii')}", nameBytes := {byte_list(name)}
    machine := {machine}, textFileOffset := {offset}, textSize := {textsize}
    symValue := {value}, symSize := {size}
    code := {byte_list(code)} }}''')
    out += ',\n'.join(records) + '\n]\n\n'
out += 'end Qsag\n'
(root / 'Qsag/ElfFixtureSlices.lean').write_text(out)
