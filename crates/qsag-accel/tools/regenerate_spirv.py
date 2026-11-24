#!/usr/bin/env python3
"""Regenerate pinned modules on Linux using glslangValidator 14.3.0 (or validate under 15.x); no Rust build."""
import argparse
import platform
from pathlib import Path
import re
import struct
import subprocess
import tempfile

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check', action='store_true', help='validate shaders and embedded words without rewriting')
args = parser.parse_args()
if platform.system() != 'Linux':
    raise SystemExit('Shader compilation requires Linux')
version_out = subprocess.check_output(['/usr/bin/glslangValidator', '--version'], text=True)
first_line = version_out.splitlines()[0] if version_out.splitlines() else ''
ver_match = re.search(r'\b(14\.3\.0|15\.\d+\.\d+)\b', first_line)
if not ver_match:
    raise SystemExit(f'Expected glslangValidator 14.3.0 or 15.x, got: {first_line}')
glslang_ver = ver_match.group(1)
if not args.check and glslang_ver != '14.3.0':
    raise SystemExit(f'Rewriting pinned SPIR-V requires glslangValidator 14.3.0, got {glslang_ver}')

root = Path(__file__).resolve().parents[1]
path = root / 'src/spirv_kernels.rs'
original = source = path.read_text()
shaders = sorted((root / 'shaders').glob('*.comp'))
assert len(shaders) == 10, f'expected 10 compute shaders, found {len(shaders)}'
with tempfile.TemporaryDirectory(prefix='qsag-spirv-') as directory:
    for shader in shaders:
        name = shader.stem.upper()
        output = Path(directory) / (shader.stem + '.spv')
        subprocess.run(['/usr/bin/glslangValidator', '-V', '--target-env', 'vulkan1.2', str(shader), '-o', str(output)], check=True)
        subprocess.run(['spirv-val', '--target-env', 'vulkan1.2', str(output)], check=True)
        data = output.read_bytes()
        words = struct.unpack('<' + 'I' * (len(data) // 4), data)
        lines = ['    ' + ', '.join(f'0x{x:08x}' for x in words[i:i+8]) + ',' for i in range(0, len(words), 8)]
        pattern = rf'pub static {name}_SPV_WORDS: \[u32; \d+\] = \[.*?\];'
        replacement = f'pub static {name}_SPV_WORDS: [u32; {len(words)}] = [\n' + '\n'.join(lines) + '\n];'
        source, count = re.subn(pattern, lambda _: replacement, source, flags=re.S)
        assert count == 1, shader
        source = re.sub(rf'({name}_SPV_BYTES: \[u8; )\d+', rf'\g<1>{len(data)}', source)
        source = re.sub(rf'(shaders/{shader.name}` \()\d+( words\))', rf'\g<1>{len(words)}\2', source)
if args.check:
    if glslang_ver == '14.3.0':
        if re.sub(r'\s+', '', original) != re.sub(r'\s+', '', source):
            raise SystemExit('Embedded SPIR-V differs from shader regeneration')
        print('All ten embedded SPIR-V modules match glslangValidator 14.3.0 output')
    else:
        print(f'All ten compute shaders compiled with glslangValidator {glslang_ver} and passed spirv-val --target-env vulkan1.2')
else:
    path.write_text(source)
