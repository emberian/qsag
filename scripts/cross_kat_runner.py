#!/usr/bin/env python3
"""Live Lean/Rust KATs; Linux only. No checked-in golden answers or crate edits.

Usage on Linux: SWARM_MEM_MAX=8G python3 scripts/cross_kat_runner.py --build
Builds the canonical qsag-kat Lake target and executes its --cross-kat mode
twice, comparing all 277 records against linked production Rust.

Negative checks corrupt every result independently, remove/append records, and
exercise WOTS+C rejection of digest mutations in both languages. These are
comparator/behavior checks, not claims of production-source mutation coverage.
Rust Ext4 and Merkle compression use qsag-agg (not present in qsag-core).
--isolate-agg-modules explicitly compiles its unmodified field/sponge/sig/pcs
modules under a minimal no_std facade; this bypasses unrelated crate-root errors
and does not certify that the full crate builds. The default always builds the unmodified crate.
Intermediate tower inverses use Tower128's subfield embedding, independently
of Lean's recursive norm inversion. Zero inverse is normalized to zero.
Temporary sources/build products are owned by this process and cleaned on exit.
"""
import argparse
from collections import Counter
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import tomllib

RUST = r'''
use std::io::{self, BufRead};
use qsag_core::field::goldilocks::{Goldilocks as G, GoldilocksExt2 as E2};
use qsag_core::field::tower::{tower_mul_bits, Tower128};
use qsag_core::sponge::{keccak::*, poseidon2::*};
use qsag_core::fips205::*;
use qsag_agg::field::{Goldilocks as A, GoldilocksExt4 as E4};
fn nums(s:&str)->Vec<u64>{s.split(',').map(|x|x.parse().unwrap()).collect()}
fn csv(xs:impl IntoIterator<Item=u64>)->String{xs.into_iter().map(|x|x.to_string()).collect::<Vec<_>>().join(",")}
fn hex(bs:&[u8])->String{bs.iter().map(|b|format!("{b:02x}")).collect()}
fn bytes(s:&str)->Vec<u8>{(0..s.len()).step_by(2).map(|i|u8::from_str_radix(&s[i..i+2],16).unwrap()).collect()}
fn e2(s:&str)->E2{let v=nums(s);E2::new(G::from_u64_reduced(v[0]),G::from_u64_reduced(v[1]))}
fn e4(s:&str)->E4{E4::from_limbs(nums(s).into_iter().map(A::from_u64_reduced).collect::<Vec<_>>().try_into().unwrap())}
fn eval(a:&[&str])->String{
 match a[0] {
  "gold"=>{let x=G::from_u64_reduced(a[2].parse().unwrap());let y=G::from_u64_reduced(a[3].parse().unwrap());
   let z=match a[1]{"add"=>x+y,"sub"=>x-y,"mul"=>x*y,"inv"=>x.inv(),_=>panic!()}; z.to_canonical_u64().to_string()},
  "ext2"=>{let x=e2(a[2]);let y=e2(a[3]);let z=match a[1]{"add"=>x+y,"sub"=>x-y,"mul"=>x*y,"inv"=>x.inv().unwrap_or(E2::ZERO),_=>panic!()};csv([z.c0.to_canonical_u64(),z.c1.to_canonical_u64()])},
  "ext4"=>{let x=e4(a[2]);let y=e4(a[3]);let z=match a[1]{"add"=>x+y,"sub"=>x-y,"mul"=>x*y,"inv"=>x.inv(),_=>panic!()};csv(z.to_limbs().map(|x|x.to_canonical_u64()))},
  "tower"=>{let k:u32=a[2].parse().unwrap();let x:u128=a[3].parse().unwrap();let y:u128=a[4].parse().unwrap();
   let z=match a[1]{"mul"=>tower_mul_bits(k,x,y),"inv"=>Tower128(x).ct_inv().0,_=>panic!()};z.to_string()},
  "shake"=>hex(&shake256_xof(a[1].parse().unwrap(),&bytes(a[2]))),
  "cshake"=>hex(&cshake256_xof(a[1].parse().unwrap(),&bytes(a[2]),&bytes(a[3]))),
  "keccak"=>{let n:u64=a[1].parse().unwrap();let mut s=core::array::from_fn(|i|if n==0{0}else{n+i as u64});keccak_f1600(&mut s);csv(s)},
  "poseidon"=>{let n:u64=a[1].parse().unwrap();let mut s=core::array::from_fn(|i|G::from_u64_reduced(n+i as u64));poseidon2_perm12(&mut s);csv(s.map(|x|x.to_canonical_u64()))},
  "compress"|"tree"=>{let n:u64=a[1].parse().unwrap();let l=core::array::from_fn(|i|A::from_u64_reduced(n+i as u64));let r=core::array::from_fn(|i|A::from_u64_reduced(n+4+i as u64));let t=core::array::from_fn(|i|A::from_u64_reduced(n+8+i as u64));
   let z=if a[0]=="compress"{qsag_agg::sponge::poseidon2_compress12_ff(l,r,t)}else{qsag_agg::sig::merkle_node_hash(42,t,qsag_agg::sig::MerkleNodeAddr{layer:1,tree_idx:0x123456789abcdef0,level:3,node_idx:7},l,r)};csv(z.map(|x|x.to_canonical_u64()))},
  "wotsplus"=>{let m=vec![a[2].parse().unwrap();a[1].parse().unwrap()];let (d,n)=try_wots_base16_digits_and_csum(&m).unwrap();csv(d[..n].iter().map(|&x|x as u64))},
  "wotsc"=>{let m=[a[1].parse().unwrap();32];let digits=qsag_core::tsw_baggy::extract_base_w_digits_checked(4,128,&m).unwrap();format!("{};{}",csv(digits.iter().map(|&x|x as u64)),qsag_core::wots_c::WotsCParams::V128.digits(&m).is_some())},
  "adrs"=>{let ty=match a[1]{"0"=>Fips205AdrsType::WotsHash,"1"=>Fips205AdrsType::WotsPk,"2"=>Fips205AdrsType::Tree,"3"=>Fips205AdrsType::ForsTree,"4"=>Fips205AdrsType::ForsRoots,"5"=>Fips205AdrsType::WotsPrf,"6"=>Fips205AdrsType::ForsPrf,_=>panic!()};hex(&Fips205Adrs{layer:0x12345678,tree:a[2].parse().unwrap(),adrs_type:ty,key_pair:0x87654321,f5:0xffffffff,f6:0xabcdef01}.to_bytes())},
  _=>panic!("unknown request")
 }
}
fn main(){for line in io::stdin().lock().lines(){let line=line.unwrap();println!("{}",eval(&line.split(' ').collect::<Vec<_>>()));}}
'''

EXPECTED = {"gold": 24, "ext2": 25, "ext4": 25, "tower": 60,
            "shake": 24, "cshake": 72, "keccak": 4, "poseidon": 3,
            "compress": 3, "tree": 3, "wotsplus": 9, "wotsc": 4, "adrs": 21}


def bounded(command, cwd, **kwargs):
    wrapper = ["swarm-build"] if shutil.which("swarm-build") else []
    return subprocess.run(["timeout", "--kill-after=10s", "600s", *wrapper, *command],
                          cwd=cwd, check=True, text=True,
                          env={**os.environ,
                               "SWARM_MEM_MAX": os.environ.get("SWARM_MEM_MAX", "8G"),
                               "CARGO_BUILD_JOBS": os.environ.get("CARGO_BUILD_JOBS", "4")},
                          **kwargs)


def build_lean(root):
    bounded(["lake", "build", "--wfail", "qsag-kat"], root / "lean",
            stdout=sys.stderr)


def parse_vectors(output):
    rows = [json.loads(line) for line in output.splitlines()]
    if any(not isinstance(r, list) or len(r) != 2 or
           any(not isinstance(x, str) for x in r) for r in rows):
        raise ValueError("invalid KAT JSON record")
    requests = [r[0] for r in rows]
    if len(set(requests)) != len(requests):
        raise ValueError("duplicate KAT request")
    counts = Counter(r.split(' ')[0] for r in requests)
    if counts != EXPECTED:
        raise ValueError(f"KAT coverage changed: {dict(counts)} != {EXPECTED}")
    return rows


def compare(rows, results):
    if len(rows) != len(results):
        raise ValueError(f"record count mismatch: Lean {len(rows)}, Rust {len(results)}")
    for (request, expected), actual in zip(rows, results):
        if expected != actual:
            raise ValueError(f"mismatch at {request!r}: Lean={expected!r}, Rust={actual!r}")


def negative_checks(rows, results):
    rejected = 0
    # Flip one output bit in each independent result; every row must participate
    # in the comparator, including all limbs and bytes (full-string equality).
    for i, result in enumerate(results):
        bad = results.copy()
        bad[i] = chr(ord(result[0]) ^ 1) + result[1:]
        try:
            compare(rows, bad)
        except ValueError:
            rejected += 1
        else:
            raise ValueError(f"undetected output mutation at {rows[i][0]}")
    for bad in [results[:-1], results + [results[0]]]:
        try:
            compare(rows, bad)
        except ValueError:
            rejected += 1
        else:
            raise ValueError("undetected record-count mutation")
    values = dict(rows)
    if not values['wotsc 27'].endswith(';true') or any(
            not values[f'wotsc {v}'].endswith(';false') for v in [0,26,255]):
        raise ValueError("WOTS+C valid/invalid digest mutation checks failed")
    return rejected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build', action='store_true', help='build Main as qsag-kat first')
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--isolate-agg-modules', action='store_true',
                        help='compile unmodified agg primitive modules under a minimal no_std facade')
    args = parser.parse_args()
    if platform.system() != 'Linux':
        parser.error('run on Linux; Lean and Cargo builds are forbidden on macOS')
    root = args.root.resolve()
    if args.build:
        build_lean(root)
    exe = root / 'lean/.lake/build/bin/qsag-kat'
    first = bounded([str(exe), "--cross-kat"], root, capture_output=True).stdout
    rows = parse_vectors(first)
    if first != bounded([str(exe), "--cross-kat"], root, capture_output=True).stdout:
        raise ValueError('Lean output is nondeterministic')
    # Use on-disk temporary storage; never /dev/shm, even if TMPDIR points there.
    with tempfile.TemporaryDirectory(prefix='cross-kat-', dir=root / 'scripts') as tmp:
        work = Path(tmp)
        (work / 'src').mkdir()
        agg = root / 'crates/qsag-agg'
        if args.isolate_agg_modules:
            # Compile complete production modules, not reimplementations or
            # extracted function bodies. Only the crate-root wiring is replaced.
            staged = work / 'agg'
            shutil.copytree(agg / 'src', staged / 'src')
            shutil.copytree(agg / 'examples', staged / 'examples')
            lib = (agg / 'src/lib.rs').read_text()
            error_type = re.search(r'pub enum HemAggError \{[^}]+\}', lib)
            if error_type is None:
                raise ValueError('cannot identify agg error type')
            facade = ('#![no_std]\nextern crate alloc;\n'
                      'pub mod field; pub mod sponge; pub mod sig; pub mod pcs;\n'
                      '#[derive(Clone, Copy, Debug, PartialEq, Eq)]\n' + error_type[0] +
                      '\npub type AggError = HemAggError;\n')
            (staged / 'src/lib.rs').write_text(facade)
            # Preserve the original manifest, resolving only workspace/path fields.
            manifest = (agg / 'Cargo.toml').read_text()
            workspace = tomllib.loads((root / 'Cargo.toml').read_text())['workspace']['package']
            for key in ['rust-version', 'version', 'edition', 'license']:
                manifest = manifest.replace(f'{key}.workspace = true',
                                            f'{key} = {json.dumps(workspace[key])}')
            manifest = re.sub(r'path = "([^"]+)"',
                              lambda m: 'path = ' + json.dumps(str((agg / m[1]).resolve())), manifest)
            manifest = manifest.replace('default = ["std"]', 'default = []')
            (staged / 'Cargo.toml').write_text(manifest)
            agg = staged
            print('NOTE: using unmodified qsag-agg primitive modules with a temporary no_std facade', file=sys.stderr)
        deps = '\n'.join(f'{name} = {{ path = {json.dumps(str(agg if name == "qsag-agg" else root / "crates" / name))} }}'
                         for name in ['qsag-core', 'qsag-agg'])
        (work / 'Cargo.toml').write_text('[workspace]\n[package]\nname="cross-kat-driver"\n'
                                       'version="0.0.0"\nedition="2024"\n[dependencies]\n' + deps + '\n')
        (work / 'src/main.rs').write_text(RUST)
        # Explicit target path prevents an inherited CARGO_TARGET_DIR from writing
        # into another lane's build tree or selecting an unrelated executable.
        bounded(['cargo', 'build', '--release', '--offline', '--target-dir', str(work / 'target')],
                work, stdout=sys.stderr)
        rust = work / 'target/release/cross-kat-driver'
        results = bounded([str(rust)], root, input='\n'.join(r[0] for r in rows)+'\n',
                          capture_output=True).stdout.splitlines()
        compare(rows, results)
        mutations = negative_checks(rows, results)
    print(json.dumps({'status': 'PASS', 'vectors': len(rows), 'coverage': EXPECTED,
                      'output_and_count_mutations_rejected': mutations,
                      'wotsc_invalid_digests_rejected': 3, 'lean_deterministic': True,
                      'isolated_agg_modules': args.isolate_agg_modules}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        print(f'cross-kat: FAIL: {error}', file=sys.stderr)
        sys.exit(1)
