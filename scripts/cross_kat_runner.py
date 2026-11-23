#!/usr/bin/env python3
"""Live Lean/Rust KATs; Linux only. No checked-in golden answers or crate edits.

Usage on Linux: python3 scripts/cross_kat_runner.py --build
Builds the canonical qsag-kat Lake target and executes its --cross-kat mode
twice, comparing all 317 non-legacy records against linked production Rust.

Negative checks corrupt every result independently, remove/append records, and
exercise WOTS+C rejection of digest mutations in both languages (legacy V128 and
ASS2 base-256 WOTS+C). These are
comparator/behavior checks, not claims of production-source mutation coverage.
Rust Fp5, TurboShake400, HemQuintic128, and Merkle compression use qsag-agg;
Poseidon2-GL-w24 and ASS2 WOTS+C cross-check qsag-agg, qsag-accel, and qsag-ass2.
--isolate-agg-modules explicitly compiles its unmodified field/sponge/sig/pcs
modules under a minimal no_std facade; this bypasses unrelated crate-root errors
and does not certify that the full crate builds. The default always builds the unmodified crate.
Intermediate tower inverses use Tower128's subfield embedding, independently
of Lean's recursive norm inversion. Zero inverse is normalized to zero.
Temporary sources/build products are owned by this process and cleaned on exit.

Poseidon2-12 and Poseidon2-GL-w24 are checked three ways: every Lean `poseidon`/`compress`
and `p2gl24` row and the committed KAT fixtures are also compared with independent
dense-matrix references of the canonical profiles.
`--check-poseidon2-fixtures` runs the fixture half alone, with no build, on any OS.
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
use qsag_agg::field::Goldilocks as A;
use qsag_agg::zk_hem::v2::{field5::Fp5, hash::Hasher as V2Hasher, params::Profile as V2Profile};
use qsag_agg::{AggSigProfile, HemQuinticProfile, SignerBitmap, SigningMode, ValidatorPublicKey};
fn nums(s:&str)->Vec<u64>{if s.is_empty(){vec![]}else{s.split(',').map(|x|x.parse().unwrap()).collect()}}
fn csv(xs:impl IntoIterator<Item=u64>)->String{xs.into_iter().map(|x|x.to_string()).collect::<Vec<_>>().join(",")}
fn hex(bs:&[u8])->String{bs.iter().map(|b|format!("{b:02x}")).collect()}
fn bytes(s:&str)->Vec<u8>{(0..s.len()).step_by(2).map(|i|u8::from_str_radix(&s[i..i+2],16).unwrap()).collect()}
fn e2(s:&str)->E2{let v=nums(s);E2::new(G::from_u64_reduced(v[0]),G::from_u64_reduced(v[1]))}
fn e5(s:&str)->Fp5{Fp5::from_limbs(nums(s).into_iter().map(A::from_u64_reduced).collect::<Vec<_>>().try_into().unwrap())}
fn eval(a:&[&str])->String{
 match a[0] {
  "gold"=>{let x=G::from_u64_reduced(a[2].parse().unwrap());let y=G::from_u64_reduced(a[3].parse().unwrap());
   let z=match a[1]{"add"=>x+y,"sub"=>x-y,"mul"=>x*y,"inv"=>x.inv(),_=>panic!()}; z.to_canonical_u64().to_string()},
  "ext2"=>{let x=e2(a[2]);let y=e2(a[3]);let z=match a[1]{"add"=>x+y,"sub"=>x-y,"mul"=>x*y,"inv"=>x.inv().unwrap_or(E2::ZERO),_=>panic!()};csv([z.c0.to_canonical_u64(),z.c1.to_canonical_u64()])},
  "fp5"=>{let x=e5(a[2]);let y=e5(a[3]);
   match a[1]{
    "norm"=>x.norm().to_canonical_u64().to_string(),
    op=>{let z=match op{"add"=>x+y,"sub"=>x-y,"mul"=>x*y,"frob"=>x.frobenius(),"inv"=>x.inverse(),_=>panic!()};csv(z.to_limbs().map(|l|l.to_canonical_u64()))}
   }},
  "tower"=>{let k:u32=a[2].parse().unwrap();let x:u128=a[3].parse().unwrap();let y:u128=a[4].parse().unwrap();
   let z=match a[1]{"mul"=>tower_mul_bits(k,x,y),"inv"=>Tower128(x).ct_inv().0,_=>panic!()};z.to_string()},
  "shake"=>hex(&shake256_xof(a[1].parse().unwrap(),&bytes(a[2]))),
  "cshake"=>hex(&cshake256_xof(a[1].parse().unwrap(),&bytes(a[2]),&bytes(a[3]))),
  "keccak"=>{let n:u64=a[1].parse().unwrap();let mut s=core::array::from_fn(|i|if n==0{0}else{n+i as u64});keccak_f1600(&mut s);csv(s)},
  "poseidon"=>{let n:u64=a[1].parse().unwrap();let mut s=core::array::from_fn(|i|G::from_u64_reduced(n+i as u64));poseidon2_perm12(&mut s);csv(s.map(|x|x.to_canonical_u64()))},
  "compress"|"tree"=>{let n:u64=a[1].parse().unwrap();let l=core::array::from_fn(|i|A::from_u64_reduced(n+i as u64));let r=core::array::from_fn(|i|A::from_u64_reduced(n+4+i as u64));let t=core::array::from_fn(|i|A::from_u64_reduced(n+8+i as u64));
   let z=if a[0]=="compress"{qsag_agg::sponge::poseidon2_compress12_ff(l,r,t)}else{qsag_agg::sig::merkle_node_hash(42,t,qsag_agg::sig::MerkleNodeAddr{layer:1,tree_idx:0x123456789abcdef0,level:3,node_idx:7},l,r)};csv(z.map(|x|x.to_canonical_u64()))},
  "p2gl24"=>match a[1]{
   "perm"=>{let n:u64=a[2].parse().unwrap();let mut s_acc:[u64;24]=core::array::from_fn(|i|G::from_u64_reduced(n+i as u64).to_canonical_u64());let mut s_agg:[A;24]=core::array::from_fn(|i|A::from_u64_reduced(n+i as u64));
    qsag_accel::poseidon2::poseidon2_gl24_perm(&mut s_acc);qsag_agg::sponge::poseidon2_gl24_perm(&mut s_agg);
    let agg_u64=s_agg.map(|x|x.to_canonical_u64());assert_eq!(s_acc,agg_u64);csv(s_acc)},
   "jive"=>{let n:u64=a[2].parse().unwrap();
    let l_acc:[u64;7]=core::array::from_fn(|i|G::from_u64_reduced(n+i as u64).to_canonical_u64());
    let r_acc:[u64;7]=core::array::from_fn(|i|G::from_u64_reduced(n+7+i as u64).to_canonical_u64());
    let t_acc:[u64;2]=[G::from_u64_reduced(n+14).to_canonical_u64(),G::from_u64_reduced(n+15).to_canonical_u64()];
    let z_acc=qsag_accel::poseidon2::poseidon2_gl24_compress_merkle(&l_acc,&r_acc,&t_acc);
    let l_agg=l_acc.map(A::from_u64_reduced);let r_agg=r_acc.map(A::from_u64_reduced);let t_agg=t_acc.map(A::from_u64_reduced);
    let z_agg=qsag_agg::sponge::poseidon2_gl24_compress_merkle(&l_agg,&r_agg,&t_agg).map(|x|x.to_canonical_u64());
    assert_eq!(z_acc,z_agg);csv(z_acc)},
   "hash56"=>{let dom:u64=a[2].parse().unwrap();let m=bytes(a[3]);
    let h_acc=qsag_accel::poseidon2::poseidon2_gl24_hash56(dom,&m);
    let h_agg=qsag_agg::sponge::poseidon2_gl24_hash56(dom,&m);
    assert_eq!(h_acc,h_agg);hex(&h_acc)},
   _=>panic!()
  },
  "turbo400"=>match a[1]{
   "perm12"=>{let n:u64=a[2].parse().unwrap();let mut s1=core::array::from_fn(|i|if n==0{0}else{n.wrapping_add(i as u64)});let mut s2=s1;
    qsag_agg::sponge::keccak_p1600_12(&mut s1);qsag_ass2::wire::keccak_p1600_12(&mut s2);assert_eq!(s1,s2);csv(s1)},
   "zkh2_salt"=>{let h=V2Hasher::new(V2Profile::TurboShakeJohnson400);let seed:[u8;32]=core::array::from_fn(|i|i as u8);hex(&h.salt(&seed,a[2].parse().unwrap()))},
   "zkh2_leaf_ext"=>{let h=V2Hasher::new(V2Profile::TurboShakeJohnson400);hex(&h.leaf_ext(a[2].parse().unwrap(),a[3].parse().unwrap(),&[Fp5::ONE,Fp5::X]))},
   "zkh2_node"=>{let h=V2Hasher::new(V2Profile::TurboShakeJohnson400);let l:[u8;50]=core::array::from_fn(|i|i as u8);let r:[u8;50]=core::array::from_fn(|i|(100+i) as u8);hex(&h.node(a[2].parse().unwrap(),&l,&r))},
   "zkh2_root"=>{let h=V2Hasher::new(V2Profile::TurboShakeJohnson400);let top:[u8;50]=core::array::from_fn(|i|i as u8);hex(&h.root(a[2].parse().unwrap(),a[3].parse().unwrap(),&top))},
   "hqm2_leaf"=>{let sym:[u8;40]=core::array::from_fn(|i|i as u8);hex(&HemQuinticProfile::turbo_canopy_leaf(a[2].parse().unwrap(),a[3].parse().unwrap(),&sym))},
   "hqm2_node"=>{let l:[u8;50]=core::array::from_fn(|i|i as u8);let r:[u8;50]=core::array::from_fn(|i|(50+i) as u8);hex(&HemQuinticProfile::turbo_canopy_node(a[2].parse().unwrap(),&l,&r))},
   "hqm2_root"=>{let top:[u8;50]=core::array::from_fn(|i|i as u8);hex(&HemQuinticProfile::turbo_canopy_root(a[2].parse().unwrap(),a[3].parse().unwrap(),&top))},
   "hqm2_gl24_leaf"=>{let sym:[u8;40]=core::array::from_fn(|i|i as u8);hex(&HemQuinticProfile::gl24_canopy_leaf(a[2].parse().unwrap(),a[3].parse().unwrap(),&sym))},
   "hqm2_gl24_node"=>{
    let pack=|base:u64|{let mut b=[0u8;56];for i in 0..7{b[8*i..8*(i+1)].copy_from_slice(&(base+i as u64).to_le_bytes());}b};
    hex(&HemQuinticProfile::gl24_canopy_node(a[2].parse().unwrap(),&pack(1),&pack(8)))},
   _=>panic!()
  },
  "hqm2fs"=>{
   let prof=match a[2]{"1"=>HemQuinticProfile::TurboShake400,"2"=>HemQuinticProfile::Poseidon2Gl24,_=>panic!()};
   let mk_pk=|base:u64|ValidatorPublicKey{
    profile:AggSigProfile::JortsPoseidon2,
    pk_seed:core::array::from_fn(|i|A::from_u64_reduced(base+i as u64)),
    pk_root:core::array::from_fn(|i|A::from_u64_reduced(base+4+i as u64)),
   };
   let pks=[mk_pk(1),mk_pk(9)];
   match a[1]{
    "shared_chain"|"shared_fp5"=>{
     let bm=SignerBitmap::from_active_indices(2,&[0]).unwrap();
     let mut tr=prof.open_transcript(&pks,&bm,&SigningMode::SharedMessage(b"hqm2-shared")).unwrap();
     if a[1]=="shared_chain"{hex(&tr.digest())}else{csv(tr.squeeze_fp5(b"OOD").to_limbs().map(|l|l.to_canonical_u64()))}
    },
    "persig_chain"|"persig_idx"=>{
     let bm=SignerBitmap::from_active_indices(2,&[0,1]).unwrap();
     let msgs:[&[u8];2]=[b"sig-a",b"sig-bb"];
     let mut tr=prof.open_transcript(&pks,&bm,&SigningMode::PerSignerMessages(&msgs)).unwrap();
     if a[1]=="persig_chain"{hex(&tr.digest())}else{csv(tr.squeeze_distinct_indices(b"QUERY",64,6).into_iter().map(|i|i as u64))}
    },
    _=>panic!()
   }
  },
  "ass2wotsc"=>match a[1]{
   "ts256"=>{let mut out=vec![0u8;a[2].parse().unwrap()];qsag_ass2::wire::turboshake256(&bytes(a[3]),&mut out);hex(&out)},
   "step"=>{let n:[u8;16]=bytes(a[4]).try_into().unwrap();hex(&qsag_ass2::wire::wotsc_step(&n,a[2].parse().unwrap(),a[3].parse().unwrap()))},
   "pubkey"=>{let sk:[u8;32]=bytes(a[2]).try_into().unwrap();hex(&qsag_ass2::wire::owner_wotsc_pubkey(&sk))},
   "cap_code"=>{let img:[u8;16]=bytes(a[2]).try_into().unwrap();let sib:[u8;16]=bytes(a[3]).try_into().unwrap();hex(&qsag_ass2::wire::capability_commit_code(&img,&sib))},
   "cap_cth"=>{let sib:[u8;16]=bytes(a[2]).try_into().unwrap();let req:[u8;16]=bytes(a[3]).try_into().unwrap();hex(&qsag_ass2::wire::capability_commit_cth(&sib,&req))},
   "img_id"=>{let enc:[u8;32]=bytes(a[2]).try_into().unwrap();let ws:Vec<u32>=nums(a[3]).into_iter().map(|x|x as u32).collect();hex(&qsag_ass2::wire::compute_image_id(&enc,&ws))},
   "chal"=>{
    let salt:u64=a[2].parse().unwrap();
    let enc=[0xa5u8;32];let nonce:[u8;16]=core::array::from_fn(|i|(i+1) as u8);let cap=[0x33u8;16];let next=[0x77u8;32];
    let d=qsag_ass2::wire::wotsc_challenge_digest(&enc,0x12,0,&nonce,0,&cap,&next,salt);
    let ok=d.iter().map(|&b|u32::from(b)).sum::<u32>()==qsag_ass2::wire::WOTSC_TARGET_SUM;
    format!("{};{}",hex(&d),ok)},
   _=>panic!()
  },
  "wotsplus"=>{let m=vec![a[2].parse().unwrap();a[1].parse().unwrap()];let (d,n)=try_wots_base16_digits_and_csum(&m).unwrap();csv(d[..n].iter().map(|&x|x as u64))},
  "wotsc"=>{let m=[a[1].parse().unwrap();32];let digits=qsag_core::tsw_baggy::extract_base_w_digits_checked(4,128,&m).unwrap();format!("{};{}",csv(digits.iter().map(|&x|x as u64)),qsag_core::wots_c::WotsCParams::V128.digits(&m).is_some())},
  "adrs"=>{let ty=match a[1]{"0"=>Fips205AdrsType::WotsHash,"1"=>Fips205AdrsType::WotsPk,"2"=>Fips205AdrsType::Tree,"3"=>Fips205AdrsType::ForsTree,"4"=>Fips205AdrsType::ForsRoots,"5"=>Fips205AdrsType::WotsPrf,"6"=>Fips205AdrsType::ForsPrf,_=>panic!()};hex(&Fips205Adrs{layer:0x12345678,tree:a[2].parse().unwrap(),adrs_type:ty,key_pair:0x87654321,f5:0xffffffff,f6:0xabcdef01}.to_bytes())},
  _=>panic!("unknown request")
 }
}
fn main(){for line in io::stdin().lock().lines(){let line=line.unwrap();println!("{}",eval(&line.split(' ').collect::<Vec<_>>()));}}
'''

EXPECTED = {"gold": 24, "ext2": 25, "fp5": 25, "tower": 60,
            "shake": 24, "cshake": 72, "keccak": 4, "poseidon": 3,
            "compress": 3, "tree": 3, "p2gl24": 9, "turbo400": 12,
            "hqm2fs": 8, "ass2wotsc": 11, "wotsplus": 9, "wotsc": 4, "adrs": 21}


# Independent reference for the canonical Poseidon2-12 profile over Goldilocks, as dense matrices:
#   M_E = M_4 (x) P_3 in flattened lane order (lane 3a+b pairs M_4 row a with P_3 row b),
#         M_4 = circ(2,3,1,1), P_3 = circ(2,1,1);
#   M_I = J + diag(-64, 1, 2, 4, ..., 1024);
#   4 + 22 + 4 rounds of x^7 with the POS2_GL1 round-constant generator;
#   compress(in0, in1, tweak) = perm(in0 || in1 || tweak)[0..4] + in0 + 2*in1 + 4*tweak.
# It shares no code with the Lean specification or the Rust kernels it is compared against.
P2_P = 2**64 - 2**32 + 1
P2_IV = 0x504f53325f474c31  # "POS2_GL1"
P2_M4 = [[2, 3, 1, 1], [1, 2, 3, 1], [1, 1, 2, 3], [3, 1, 1, 2]]
P2_ME = [[P2_M4[i // 3][j // 3] * (2 if i % 3 == j % 3 else 1) for j in range(12)] for i in range(12)]
P2_MI = [[1 + ((-64 if i == 0 else 1 << (i - 1)) if i == j else 0) for j in range(12)] for i in range(12)]
P2_EMPTY_HASH32 = "b6a8416a0036177c167477c74bfdca917b0d73c8ba8fcf42a2a1c609dc25b0a2"


def p2_mul(matrix, x):
    return [sum(a * b for a, b in zip(row, x)) % P2_P for row in matrix]


def p2_mix(x):
    x = (x + 0x9e3779b97f4a7c15) & (2**64 - 1)
    x = ((x ^ (x >> 30)) * 0xbf58476d1ce4e5b9) & (2**64 - 1)
    x = ((x ^ (x >> 27)) * 0x94d049bb133111eb) & (2**64 - 1)
    return x ^ (x >> 31)


def p2_rc(phase, rnd, lane):
    return p2_mix(p2_mix(p2_mix(P2_IV ^ phase) ^ rnd) ^ lane) % P2_P


def p2_perm(x):
    x = p2_mul(P2_ME, [v % P2_P for v in x])
    for phase, rounds in ((0, 4), (1, 22), (2, 4)):
        for rnd in range(rounds):
            if phase == 1:
                x[0] = pow((x[0] + p2_rc(1, rnd, 0)) % P2_P, 7, P2_P)
                x = p2_mul(P2_MI, x)
            else:
                x = p2_mul(P2_ME, [pow((v + p2_rc(phase, rnd, i)) % P2_P, 7, P2_P) for i, v in enumerate(x)])
    return x


def p2_compress(x):
    x = [v % P2_P for v in x]
    return [(v + x[i] + 2 * x[4 + i] + 4 * x[8 + i]) % P2_P for i, v in enumerate(p2_perm(x)[:4])]


def p2_hash32(msg):
    msg = msg + b"\x01"
    msg += b"\0" * (-len(msg) % 7)
    limbs = [int.from_bytes(msg[i:i + 7], "big") for i in range(0, len(msg), 7)]
    pad = (8 - (len(limbs) + 1) % 8) % 8
    limbs += [2**56 + 1] if pad == 0 else [1] + [0] * (pad - 1) + [2**56]
    x = [0] * 8 + [8, 4, 32, P2_IV]
    for i in range(0, len(limbs), 8):
        x = p2_perm([(x[j] + limbs[i + j]) % P2_P for j in range(8)] + x[8:])
    return b"".join(v.to_bytes(8, "big") for v in x[:4]).hex()


def poseidon2_reference_checks(rows):
    """Compare every Lean `poseidon`/`compress` row with the reference; returns the count."""
    if p2_hash32(b"") != P2_EMPTY_HASH32:
        raise ValueError("Poseidon2 reference does not reproduce the canonical empty hash32")
    checked = 0
    for request, lean in rows:
        op, _, arg = request.partition(" ")
        if op in ("poseidon", "compress"):
            state = [int(arg) + i for i in range(12)]
            want = ",".join(map(str, (p2_perm if op == "poseidon" else p2_compress)(state)))
            if lean != want:
                raise ValueError(f"Lean is off the canonical Poseidon2-12 profile at {request!r}: "
                                 f"Lean={lean!r}, reference={want!r}")
            checked += 1
    if checked != EXPECTED["poseidon"] + EXPECTED["compress"]:
        raise ValueError(f"Poseidon2 reference covered {checked} rows")
    return checked


def poseidon2_fixture_checks(root):
    """Check the committed Poseidon2 KAT fixtures against the reference. Needs no build."""
    failures, checked = [], 0

    def expect(where, got, want):
        nonlocal checked
        checked += 1
        if got != want:
            failures.append(f"{where}: fixture={got!r}, canonical={want!r}")

    label = b"qsag-poseidon2-kat"
    for path in ("tests/kat_vectors.json", "validation/tests/fixtures/lean_kat_snapshot.json"):
        kat = json.loads((root / path).read_text())["poseidon2_goldilocks_12"]
        expect(f"{path}: perm_zero", kat["perm_zero"], [str(v) for v in p2_perm([0] * 12)])
        expect(f"{path}: perm_seq_0_11", kat["perm_seq_0_11"], [str(v) for v in p2_perm(list(range(12)))])
        for key, msg in (("hash32_empty", b""), ("hash32_00", b"\0"),
                         ("hash32_010203", b"\x01\x02\x03"), ("hash32_label", label)):
            expect(f"{path}: {key}", kat[key], p2_hash32(msg))
    path = "validation/tests/fixtures/lean_external_oracle_vectors.json"
    oracle = json.loads((root / path).read_text())
    for i, row in enumerate(oracle["poseidon2_12"]):
        expect(f"{path}: poseidon2_12[{i}].perm", row["perm"],
               [str(v) for v in p2_perm([int(v) for v in row["input"]])])
    for i, row in enumerate(oracle["poseidon2_hash32"]):
        expect(f"{path}: poseidon2_hash32[{i}]", row["poseidon2_hash32_hex"],
               p2_hash32(bytes.fromhex(row["msg_hex"])))
    if failures:
        raise ValueError("Poseidon2 fixtures are off the canonical profile:\n  " + "\n  ".join(failures))
    return checked


def bounded(command, cwd, **kwargs):
    wrap_env = os.environ.get("QSAG_BUILD_WRAPPER", "").strip()
    wrapper = wrap_env.split() if wrap_env else []
    limit = os.environ.get("CROSS_KAT_TIMEOUT", "1200s")
    return subprocess.run(["timeout", "--kill-after=10s", limit, *wrapper, *command],
                          cwd=cwd, check=True, text=True,
                          env={**os.environ,
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
    rows = [r for r in rows if not r[0].startswith("ext4 ")]
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
    ass2_chals = [v for k, v in rows if k.startswith('ass2wotsc chal ')]
    if (len(ass2_chals) != 2 or not values['ass2wotsc chal 0'].endswith(';false')
            or sum(x.endswith(';true') for x in ass2_chals) != 1):
        raise ValueError("ASS2 WOTS+C valid/invalid challenge sum checks failed")
    return rejected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build', action='store_true', help='build Main as qsag-kat first')
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--isolate-agg-modules', action='store_true',
                        help='compile unmodified agg primitive modules under a minimal no_std facade')
    parser.add_argument('--check-poseidon2-fixtures', action='store_true',
                        help='only check committed Poseidon2 KAT fixtures against the reference (no build, any OS)')
    parser.add_argument('--target-dir', type=Path, default=None,
                        help='optional explicit Cargo target directory for incremental cross-KAT driver builds')
    args = parser.parse_args()
    if args.check_poseidon2_fixtures:
        if p2_hash32(b"") != P2_EMPTY_HASH32:
            raise ValueError("Poseidon2 reference does not reproduce the canonical empty hash32")
        checked = poseidon2_fixture_checks(args.root.resolve())
        print(json.dumps({'status': 'PASS', 'poseidon2_fixture_values': checked}, sort_keys=True))
        return
    if platform.system() != 'Linux':
        parser.error('run on Linux; Lean and Cargo builds are forbidden on macOS')
    root = args.root.resolve()
    if args.build:
        build_lean(root)
    exe = root / 'lean/.lake/build/bin/qsag-kat'
    first = bounded([str(exe), "--cross-kat"], root, capture_output=True).stdout
    rows = parse_vectors(first)
    reference_rows = poseidon2_reference_checks(rows)
    reference_fixtures = poseidon2_fixture_checks(root)
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
                         for name in ['qsag-core', 'qsag-agg', 'qsag-accel', 'qsag-ass2'])
        (work / 'Cargo.toml').write_text('[workspace]\n[package]\nname="cross-kat-driver"\n'
                                       'version="0.0.0"\nedition="2024"\n[dependencies]\n' + deps + '\n')
        (work / 'src/main.rs').write_text(RUST)
        # Explicit target path prevents an inherited CARGO_TARGET_DIR from writing
        # into another lane's build tree or selecting an unrelated executable.
        target_dir = args.target_dir.resolve() if args.target_dir is not None else (work / 'target')
        bounded(['cargo', 'build', '--release', '--offline', '--target-dir', str(target_dir)],
                work, stdout=sys.stderr)
        rust = target_dir / 'release/cross-kat-driver'
        results = bounded([str(rust)], root, input='\n'.join(r[0] for r in rows)+'\n',
                          capture_output=True).stdout.splitlines()
        compare(rows, results)
        mutations = negative_checks(rows, results)
    print(json.dumps({'status': 'PASS', 'vectors': len(rows), 'coverage': EXPECTED,
                      'output_and_count_mutations_rejected': mutations,
                      'wotsc_invalid_digests_rejected': 3, 'lean_deterministic': True,
                      'poseidon2_reference_rows': reference_rows,
                      'poseidon2_fixture_values': reference_fixtures,
                      'isolated_agg_modules': args.isolate_agg_modules}, sort_keys=True))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, subprocess.CalledProcessError) as error:
        print(f'cross-kat: FAIL: {error}', file=sys.stderr)
        sys.exit(1)
