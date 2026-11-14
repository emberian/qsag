#!/usr/bin/env python3
"""Executable live-spec differential tests. Run on Linux, never builds on Darwin.

Protocol is documented by the dispatch in SpecOracle.lean. Each generated request
is sent to both independent processes. A mismatch is fatal unless its *exact*
request/output triple is listed in KNOWN_MISMATCHES; --strict-all fails those too.
Temporary Rust sources and build products are removed even after test failure.
Mutation tests compile production-source clause drops; they are not security proofs.
"""
import argparse
from collections import Counter
import itertools
import json
import os
from pathlib import Path
import platform
import random
import select
import shutil
import subprocess
import tempfile
import time

P = 18446744069414584321
KNOWN_MISMATCHES = {}  # Never classify a whole operation as an expected failure.
RUST = r'''
extern crate alloc;
use qsag_core::{sponge, wipe};
use std::io::{self, BufRead, Write};
use qsag_core::{sponge::*, tsw_baggy::*, fips205::*};
use qsag_agg::field::{Goldilocks as G, GoldilocksExt4 as E};
fn bytes(s: &str) -> Vec<u8> { (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i+2],16).unwrap()).collect() }
fn hex(b: &[u8]) -> String { b.iter().map(|x| format!("{x:02x}")).collect() }
fn nums(s: &str) -> Vec<u64> { if s.is_empty() {vec![]} else {s.split(',').map(|x|x.parse().unwrap()).collect()} }
fn csv(v: &[u64]) -> String { v.iter().map(|x|x.to_string()).collect::<Vec<_>>().join(",") }
fn arr(s: &str) -> [u8;32] { bytes(s).try_into().unwrap() }
fn ext(s: &str) -> E { E::from_le_bytes_canonical(arr(s)).unwrap() }
fn sha3_512(m: &[u8]) -> [u8; 64] {
    let mut sp = qsag_accel::keccak::KeccakSponge::<72>::new();
    sp.absorb(m);
    sp.finalize(0x06);
    let mut out = [0u8; 64];
    sp.squeeze(&mut out);
    out
}
fn format_quorum(res: Result<qsag_quorum::quorum_jorts::QuorumConfig, qsag_quorum::quorum_jorts::QuorumError>) -> String {
    match res {
        Ok(c) => format!("{},{},{},{}", c.threshold(), c.parties(), c.max_faults(), c.quorum()),
        Err(_) => "reject".into(),
    }
}
fn sbox7_g(x: G) -> G {
    G::from_u64_reduced(qsag_accel::poseidon2::poseidon2_sbox7(x.to_canonical_u64()))
}
fn sbox7_inv_g(x: G) -> G {
    let mut exp: u64 = 10540996611094048183;
    let mut base = x;
    let mut acc = G::ONE;
    while exp > 0 {
        if exp & 1 == 1 { acc = acc * base; }
        base = base.square();
        exp >>= 1;
    }
    acc
}
fn m4_fwd(b: [G; 4]) -> [G; 4] {
    let s = b[0] + b[1] + b[2] + b[3];
    let two = G::from_u64_reduced(2);
    [
        s + b[0] + two * b[1],
        s + b[1] + two * b[2],
        s + b[2] + two * b[3],
        s + b[3] + two * b[0],
    ]
}
fn m4_inv(y: [G; 4]) -> [G; 4] {
    let inv7 = G::from_u64_reduced(7).inv();
    let inv15 = G::from_u64_reduced(15).inv();
    let t = inv7 * (y[0] + y[1] + y[2] + y[3]);
    let u0 = y[0] - t;
    let u1 = y[1] - t;
    let u2 = y[2] - t;
    let u3 = y[3] - t;
    let g2 = G::from_u64_reduced(2);
    let g4 = G::from_u64_reduced(4);
    let g8 = G::from_u64_reduced(8);
    [
        inv15 * (g8 * u3 - g4 * u2 + g2 * u1 - u0),
        inv15 * (g8 * u0 - g4 * u3 + g2 * u2 - u1),
        inv15 * (g8 * u1 - g4 * u0 + g2 * u3 - u2),
        inv15 * (g8 * u2 - g4 * u1 + g2 * u0 - u3),
    ]
}
fn me16_fwd(st: &mut [G; 16]) {
    let y0 = m4_fwd([st[0], st[1], st[2], st[3]]);
    let y1 = m4_fwd([st[4], st[5], st[6], st[7]]);
    let y2 = m4_fwd([st[8], st[9], st[10], st[11]]);
    let y3 = m4_fwd([st[12], st[13], st[14], st[15]]);
    for i in 0..4 {
        let col = y0[i] + y1[i] + y2[i] + y3[i];
        st[i] = y0[i] + col;
        st[4 + i] = y1[i] + col;
        st[8 + i] = y2[i] + col;
        st[12 + i] = y3[i] + col;
    }
}
fn me16_inv(st: &mut [G; 16]) {
    let inv5 = G::from_u64_reduced(5).inv();
    let mut y0 = [G::ZERO; 4];
    let mut y1 = [G::ZERO; 4];
    let mut y2 = [G::ZERO; 4];
    let mut y3 = [G::ZERO; 4];
    for i in 0..4 {
        let col = inv5 * (st[i] + st[4 + i] + st[8 + i] + st[12 + i]);
        y0[i] = st[i] - col;
        y1[i] = st[4 + i] - col;
        y2[i] = st[8 + i] - col;
        y3[i] = st[12 + i] - col;
    }
    let b0 = m4_inv(y0);
    let b1 = m4_inv(y1);
    let b2 = m4_inv(y2);
    let b3 = m4_inv(y3);
    st[0..4].copy_from_slice(&b0);
    st[4..8].copy_from_slice(&b1);
    st[8..12].copy_from_slice(&b2);
    st[12..16].copy_from_slice(&b3);
}
fn mi16_fwd(st: &mut [G; 16]) {
    let mut s = G::ZERO;
    for &x in st.iter() { s = s + x; }
    st[0] = s - G::from_u64_reduced(2) * st[0];
    st[1] = s + st[1];
    for k in 2..16 {
        st[k] = s + G::from_u64_reduced(1u64 << (k - 1)) * st[k];
    }
}
fn mi16_inv(st: &mut [G; 16]) {
    let mut w = [G::ZERO; 16];
    w[0] = G::ZERO - G::from_u64_reduced(8192);
    w[1] = G::from_u64_reduced(16384);
    for k in 2..16 {
        w[k] = G::from_u64_reduced(1u64 << (15 - k));
    }
    let mut ws = G::ZERO;
    for i in 0..16 { ws = ws + w[i] * st[i]; }
    let s = G::from_u64_reduced(40959).inv() * ws;
    let inv16384 = G::from_u64_reduced(16384).inv();
    for i in 0..16 {
        st[i] = inv16384 * (w[i] * (st[i] - s));
    }
}
fn perm16_fwd(st: &mut [G; 16]) {
    me16_fwd(st);
    for r in 0..4u64 {
        for l in 0..16usize {
            let rc = G::from_u64_reduced(qsag_accel::poseidon2::poseidon2_const_at(0, r, l as u64));
            st[l] = sbox7_g(st[l] + rc);
        }
        me16_fwd(st);
    }
    for r in 0..22u64 {
        let rc = G::from_u64_reduced(qsag_accel::poseidon2::poseidon2_const_at(1, r, 0));
        st[0] = sbox7_g(st[0] + rc);
        mi16_fwd(st);
    }
    for r in 0..4u64 {
        for l in 0..16usize {
            let rc = G::from_u64_reduced(qsag_accel::poseidon2::poseidon2_const_at(2, r, l as u64));
            st[l] = sbox7_g(st[l] + rc);
        }
        me16_fwd(st);
    }
}
fn perm16_inv(st: &mut [G; 16]) {
    for r in (0..4u64).rev() {
        me16_inv(st);
        for l in 0..16usize {
            let rc = G::from_u64_reduced(qsag_accel::poseidon2::poseidon2_const_at(2, r, l as u64));
            st[l] = sbox7_inv_g(st[l]) - rc;
        }
    }
    for r in (0..22u64).rev() {
        mi16_inv(st);
        let rc = G::from_u64_reduced(qsag_accel::poseidon2::poseidon2_const_at(1, r, 0));
        st[0] = sbox7_inv_g(st[0]) - rc;
    }
    for r in (0..4u64).rev() {
        me16_inv(st);
        for l in 0..16usize {
            let rc = G::from_u64_reduced(qsag_accel::poseidon2::poseidon2_const_at(0, r, l as u64));
            st[l] = sbox7_inv_g(st[l]) - rc;
        }
    }
    me16_inv(st);
}
fn eval(a: &[&str]) -> String {
    match a[0] {
        "certificates" => certificates(&arr(a[1]),&bytes(a[2])),
        "latchtrace" => latch_trace(a[1]),
        "posixburn" => posix_burn_trace(a[1]),
        "fsbeltwal" => fs_belt_wal_trace(a[1]),
        "mutation" => mutation(a[1]),
        "ledger" => ledger_case(a[1].parse().unwrap(), a[2].parse().unwrap(), a[3].parse().unwrap()),
        "poseidonhash" => hex(&poseidon2_hash32(&bytes(a[1]))),
        "rounding" => {
            use qsag_cred::fips204_ntt::*;
            let r:u32=a[1].parse().unwrap(); let z:u32=a[2].parse().unwrap();
            let (hi,lo)=power2round(r); let lo=if lo>4190208 {lo as i32-8380417} else {lo as i32};
            let (dh,dl)=decompose_ct(r,95232);
            format!("{hi},{lo},{dh},{dl},{},{}",make_hint_ct(z,r,95232)!=0,use_hint(a[3].parse().unwrap(),r,95232))
        },
        "hem" => {
            let x=G::from_u64_reduced(a[3].parse().unwrap());
            let half=G::from_u64_reduced(2).inv();
            let out=qsag_whir_verified::fold_duet_affine_ext4(
                to_verified_ext4(ext(a[1])),
                to_verified_ext4(ext(a[2])),
                (half*x.inv()).to_canonical_u64(),
                half.to_canonical_u64(),
                (x*x).to_canonical_u64(),
                to_verified_ext4(ext(a[4])),
                to_verified_ext4(ext(a[5])),
                to_verified_ext4(ext(a[6])),
            );
            hex(&from_verified_ext4(out).to_le_bytes())
        },
        "cosetfold" => {
            let inv_two_y0=G::from_u64_reduced(a[3].parse().unwrap()).to_canonical_u64();
            let inv_two=G::from_u64_reduced(a[4].parse().unwrap()).to_canonical_u64();
            let out=qsag_whir_verified::duet_fold(
                to_verified_ext4(ext(a[1])),
                to_verified_ext4(ext(a[2])),
                inv_two_y0,
                inv_two,
                to_verified_ext4(ext(a[5])),
            );
            hex(&from_verified_ext4(out).to_le_bytes())
        },
        "cwyzbridge" => {
            let out=qsag_whir_verified::cwyz_bridge_claim_step(
                to_verified_ext4(ext(a[1])),
                to_verified_ext4(ext(a[2])),
                to_verified_ext4(ext(a[3])),
                to_verified_ext4(ext(a[4])),
                to_verified_ext4(ext(a[5])),
                to_verified_ext4(ext(a[6])),
                to_verified_ext4(ext(a[7])),
                to_verified_ext4(ext(a[8])),
                to_verified_ext4(ext(a[9])),
                to_verified_ext4(ext(a[10])),
            );
            hex(&from_verified_ext4(out).to_le_bytes())
        },
        "binary" => {
            use qsag_core::field::tower::{TowerGf256,Tower128};
            if a[1]=="3" {let x=TowerGf256(a[3].parse().unwrap());let y=TowerGf256(a[4].parse().unwrap());
                (match a[2] {"add"=>x.add(y),"mul"=>x.mul(y),"square"=>x.mul(x),"inv"=>x.ct_inv(),_=>panic!("binary op")}).0.to_string()
            } else {let x=Tower128(a[3].parse().unwrap());let y=Tower128(a[4].parse().unwrap());
                (match a[2] {"add"=>x.add(y),"mul"=>x.mul(y),"square"=>x.mul(x),"inv"=>x.ct_inv(),_=>panic!("binary op")}).0.to_string()}
        },
        "shake" => hex(&shake256_xof(a[1].parse().unwrap(), &bytes(a[2]))),
        "cshake" => hex(&cshake256_xof(a[1].parse().unwrap(), &bytes(a[2]), &bytes(a[3]))),
        "sha3" => hex(&qsag_accel::keccak::sha3_256(&bytes(a[1]))),
        "sha3_512" => hex(&sha3_512(&bytes(a[1]))),
        "keccak256" => hex(&qsag_accel::keccak::keccak256(&bytes(a[1]))),
        "keccak" => { let mut s:[u64;25]=nums(a[1]).try_into().unwrap(); keccak_f1600(&mut s); csv(&s) },
        "poseidon" => { let mut s:Poseidon2State12=nums(a[1]).iter().map(|x|qsag_core::field::goldilocks::Goldilocks::from_u64_reduced(*x)).collect::<Vec<_>>().try_into().unwrap(); poseidon2_perm12(&mut s); csv(&s.iter().map(|x|x.to_canonical_u64()).collect::<Vec<_>>()) },
        "poseidon16" => {
            let mut s:[G;16]=nums(a[1]).into_iter().map(G::from_u64_reduced).collect::<Vec<_>>().try_into().unwrap();
            perm16_fwd(&mut s);
            csv(&s.iter().map(|x|x.to_canonical_u64()).collect::<Vec<_>>())
        },
        "poseidon16inv" => {
            let mut s:[G;16]=nums(a[1]).into_iter().map(G::from_u64_reduced).collect::<Vec<_>>().try_into().unwrap();
            perm16_inv(&mut s);
            csv(&s.iter().map(|x|x.to_canonical_u64()).collect::<Vec<_>>())
        },
        "poseidon16me" => {
            let mut s:[G;16]=nums(a[2]).into_iter().map(G::from_u64_reduced).collect::<Vec<_>>().try_into().unwrap();
            match a[1] { "fwd" => me16_fwd(&mut s), "inv" => me16_inv(&mut s), _ => panic!("me16 op") }
            csv(&s.iter().map(|x|x.to_canonical_u64()).collect::<Vec<_>>())
        },
        "gold" => {let x=G::from_u64_reduced(a[2].parse().unwrap()); let y=G::from_u64_reduced(a[3].parse().unwrap());
            let z=match a[1] {"add"=>x+y,"sub"=>x-y,"mul"=>x*y,"inv"=>x.inv(),"square"=>x.square(),_=>panic!("op")};
            let cx=qsag_core::field::goldilocks::Goldilocks::from_u64_reduced(a[2].parse().unwrap());
            let cy=qsag_core::field::goldilocks::Goldilocks::from_u64_reduced(a[3].parse().unwrap());
            let cz=match a[1] {"add"=>cx+cy,"sub"=>cx-cy,"mul"=>cx*cy,"inv"=>cx.inv(),"square"=>cx.square(),_=>panic!("op")};
            assert_eq!(z.to_canonical_u64(),cz.to_canonical_u64()); z.to_canonical_u64().to_string()},
        "extdecode" => { let v=bytes(a[1]); match <[u8;32]>::try_from(v).ok().and_then(E::from_le_bytes_canonical) {Some(x)=>hex(&x.to_le_bytes()),None=>"reject".into()} },
        "ext" => { let x=ext(a[2]); let y=ext(a[3]); hex(&(match a[1] {"add"=>x+y,"sub"=>x-y,"mul"=>x*y,"inv"=>x.inv(),"square"=>x.square(),"frobenius"=>x.frobenius(),_=>panic!("extension op")}).to_le_bytes()) },
        "tower" => qsag_core::field::tower::tower_mul_t7(a[1].parse().unwrap(),a[2].parse().unwrap()).to_string(),
        "wotsgeneric" => if a.len() == 2 {
            qsag_core::wots_c::WotsCParams {chains:127,zero_digits:1,target_sum:192}.digits(&arr(a[1])).is_some().to_string()
        } else {
            qsag_core::wots_c::WotsCParams {chains:a[1].parse().unwrap(),zero_digits:a[2].parse().unwrap(),target_sum:a[3].parse().unwrap()}.digits(&arr(a[4])).is_some().to_string()
        },
        "wots" => {let m=bytes(a[1]); let d=extract_base_w_digits_checked(4,128,&m).unwrap();
            format!("{};{}", d.iter().map(|x|x.to_string()).collect::<Vec<_>>().join(","), qsag_core::wots_c::WotsCParams::V128.digits(&m.try_into().unwrap()).is_some())},
        "hybrid" => {let q=bytes(a[3]); let pk=PqPublicKey{pk_seed:q[..32].try_into().unwrap(),pk_root:q[32..].try_into().unwrap()}; hex(&build_hybrid_bound_message(&arr(a[1]),&bytes(a[2]),&pk,&bytes(a[4])))},
        "fors" => hex(&fors_leaf_hash_from_secret(Cshake256Suite,&arr(a[1]),a[2].parse().unwrap(),a[3].parse().unwrap(),a[4].parse().unwrap(),a[5].parse().unwrap(),&arr(a[6]))),
        "forsnode" => hex(&th_node_h(Cshake256Suite,&bytes(a[1]),&HashAdrs{layer:0,tree:a[2].parse().unwrap(),kind:AdrsKind::ForsTree,key_pair:a[3].parse().unwrap(),chain_idx:a[4].parse().unwrap(),hash_step:a[5].parse().unwrap()},&arr(a[6]),&arr(a[7]))),
        "adrs" => hex(&Fips205Adrs{layer:a[1].parse().unwrap(),tree:a[2].parse().unwrap(),adrs_type:Fips205AdrsType::from_u32(a[3].parse().unwrap()).unwrap(),key_pair:a[4].parse().unwrap(),f5:a[5].parse().unwrap(),f6:a[6].parse().unwrap()}.to_bytes()),
        "canopy" => {use qsag_agg::pcs::*;
            let indices=nums(a[3]); let hs:Vec<[u8;32]>=if a[4].is_empty(){vec![]}else{a[4].split(',').map(arr).collect()};
            let leaves:Vec<_>=indices.iter().zip(hs).map(|(i,h)|(*i as usize,h)).collect();
            let proof=CanopyMultiProof{auth_siblings:if a[5].is_empty(){vec![]}else{a[5].split(',').map(arr).collect()}};
            verify_canopy_multiproof(&CanopyCommitment{root:arr(a[2]),log_leaves:a[1].parse().unwrap()},&leaves,&proof).to_string()},
        "subset" => subset(&arr(a[1]),&bytes(a[2]),a[3].parse().unwrap()),
        "latch" => latch(a[1]),
        "quorum" => qsag_quorum::quorum_jorts::QuorumConfig::with_quorum(a[1].parse().unwrap(),a[2].parse().unwrap(),a[3].parse().unwrap(),a[4].parse().unwrap()).is_ok().to_string(),
        "quorumnew" => format_quorum(qsag_quorum::quorum_jorts::QuorumConfig::new(a[1].parse().unwrap(),a[2].parse().unwrap(),a[3].parse().unwrap())),
        "quorumtight" => format_quorum(qsag_quorum::quorum_jorts::QuorumConfig::tight(a[1].parse().unwrap())),
        "metamorphic" => metamorphic(&arr(a[1]),&bytes(a[2])),
        _ => panic!("unknown operation")
    }
}
fn posix_burn_trace(events: &str) -> String {
    use qsag_fts::wal::DurableBurnJournal;
    if events.is_empty() { return String::new(); }
    static NEXT_BURN: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let dir = std::env::temp_dir().join(format!(
        "oracle-burn-{}-{}",
        std::process::id(),
        NEXT_BURN.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    std::fs::create_dir(&dir).unwrap();
    let mut cur_path = dir.join("burn-0");
    let mut copy_idx = 0usize;
    let mut journal = Some(DurableBurnJournal::create(&cur_path, [1; 32], [2; 32]).unwrap());
    let mut retained: Option<qsag_core::LedgerCheckpoint> = None;
    let reopen = |p: &std::path::Path, ret: Option<qsag_core::LedgerCheckpoint>, j: &mut Option<DurableBurnJournal>| -> String {
        *j = None;
        let res = match ret {
            Some(r) => DurableBurnJournal::open_at_least(p, [1; 32], [2; 32], r),
            None => DurableBurnJournal::open_existing(p, [1; 32], [2; 32]),
        };
        match res {
            Ok(jr) => {
                let n = jr.checkpoint().generation;
                *j = Some(jr);
                format!("ok:{n}")
            }
            Err(_) => "err".into(),
        }
    };
    let mut out = Vec::new();
    for ev in events.split(',') {
        let parts: Vec<&str> = ev.split(':').collect();
        let res = match parts.as_slice() {
            ["retain"] => match &journal {
                Some(jr) => { retained = Some(jr.checkpoint()); "ok".into() }
                None => "err".into(),
            },
            ["reopen"] => reopen(&cur_path, retained, &mut journal),
            ["trunc"] => {
                journal = None;
                let len = std::fs::metadata(&cur_path).unwrap().len();
                let f = std::fs::OpenOptions::new().write(true).open(&cur_path).unwrap();
                f.set_len(len.min(104)).unwrap();
                f.sync_all().unwrap();
                reopen(&cur_path, retained, &mut journal)
            }
            ["flip"] => {
                use std::io::{Read, Seek, SeekFrom, Write};
                journal = None;
                let mut f = std::fs::OpenOptions::new().read(true).write(true).open(&cur_path).unwrap();
                if f.metadata().unwrap().len() > 0 {
                    f.seek(SeekFrom::End(-1)).unwrap();
                    let mut b = [0u8; 1];
                    f.read_exact(&mut b).unwrap();
                    b[0] ^= 1;
                    f.seek(SeekFrom::End(-1)).unwrap();
                    f.write_all(&b).unwrap();
                    f.sync_all().unwrap();
                }
                reopen(&cur_path, retained, &mut journal)
            }
            ["copy"] => {
                journal = None;
                copy_idx += 1;
                let next_path = dir.join(format!("burn-{copy_idx}"));
                std::fs::copy(&cur_path, &next_path).unwrap();
                cur_path = next_path;
                reopen(&cur_path, retained, &mut journal)
            }
            ["tear", k_str] => {
                use std::io::Write;
                journal = None;
                let k: usize = k_str.parse().unwrap();
                let len = if k == 0 { 1 } else if k >= 42 { 41 } else { k };
                let mut f = std::fs::OpenOptions::new().append(true).open(&cur_path).unwrap();
                f.write_all(&vec![0xaau8; len]).unwrap();
                f.sync_all().unwrap();
                reopen(&cur_path, retained, &mut journal)
            }
            ["res", p_str, e_str] => {
                let p: u16 = p_str.parse().unwrap();
                let e: u64 = e_str.parse().unwrap();
                match &mut journal {
                    None => "err".into(),
                    Some(jr) => {
                        if jr.reserve(&[1; 32], p, e).is_ok() {
                            if retained.is_some() {
                                retained = Some(jr.checkpoint());
                            }
                            "ok".into()
                        } else {
                            "err".into()
                        }
                    }
                }
            }
            _ => panic!("unknown posixburn event"),
        };
        out.push(res);
    }
    drop(journal);
    std::fs::remove_dir_all(&dir).unwrap();
    out.join(",")
}
fn fs_belt_wal_trace(events: &str) -> String {
    use qsag_core::belt_latch::{BeltLatch, FsBeltWal};
    if events.is_empty() { return String::new(); }
    static NEXT_BELT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let dir = std::env::temp_dir().join(format!(
        "oracle-belt-{}-{}",
        std::process::id(),
        NEXT_BELT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ));
    std::fs::create_dir(&dir).unwrap();
    let path = dir.join("belt");
    let wal = FsBeltWal::provision_genesis(&path, [5; 32]).unwrap();
    let mut snapshot = std::fs::read(&path).unwrap();
    let mut corrupted = false;
    let mut latch = Some(BeltLatch::recover(wal, 12).unwrap());
    let mut retained: Option<qsag_core::LedgerCheckpoint> = None;
    let reopen = |ret: Option<qsag_core::LedgerCheckpoint>, l: &mut Option<BeltLatch<FsBeltWal>>| -> String {
        *l = None;
        let opened = match ret {
            Some(r) => FsBeltWal::open_existing_at_least(&path, [5; 32], r),
            None => FsBeltWal::open_existing(&path, [5; 32]),
        };
        match opened.and_then(|w| BeltLatch::recover(w, 12).map_err(|_| std::io::Error::other("recover"))) {
            Ok(rec) => {
                let ep = rec.next_epoch();
                let g = rec.wal().checkpoint().generation;
                *l = Some(rec);
                format!("ok:{ep}:{g}")
            }
            Err(_) => "err".into(),
        }
    };
    let mut out = Vec::new();
    for ev in events.split(',') {
        let res = match ev {
            "retain" => match &latch {
                None => "closed".into(),
                Some(l) => {
                    retained = Some(l.wal().checkpoint());
                    snapshot = std::fs::read(&path).unwrap();
                    "ok".into()
                }
            },
            "crash" => reopen(retained, &mut latch),
            "rollback" => {
                latch = None;
                std::fs::write(&path, &snapshot).unwrap();
                corrupted = false;
                reopen(retained, &mut latch)
            }
            "corrupt" => {
                latch = None;
                if !corrupted {
                    let mut raw = std::fs::read(&path).unwrap();
                    if let Some(last) = raw.last_mut() { *last ^= 1; }
                    std::fs::write(&path, raw).unwrap();
                    corrupted = true;
                }
                reopen(retained, &mut latch)
            }
            "rmlock" => {
                latch = None;
                let _ = std::fs::remove_file(dir.join("belt.lock"));
                reopen(retained, &mut latch)
            }
            _ => {
                let v: Vec<u64> = ev.split(':').map(|x| x.parse().unwrap()).collect();
                match &mut latch {
                    None => "closed".into(),
                    Some(l) => {
                        if l.bind(v[0], &[v[1] as u8; 32], &[v[2] as u8; 32], &[v[3] as u8]).is_ok() {
                            if let Some(r) = &mut retained {
                                if l.wal().checkpoint().generation > r.generation {
                                    *r = l.wal().checkpoint();
                                }
                            }
                            "true".into()
                        } else {
                            "false".into()
                        }
                    }
                }
            }
        };
        out.push(res);
    }
    drop(latch);
    std::fs::remove_dir_all(&dir).unwrap();
    out.join(",")
}
fn subset(seed: &[u8;32], msg: &[u8], which: usize) -> String {
    use qsag_quorum::quorum_jorts::*;
    let mut signer=CommitteePartitionedJorts::stage(2,3,2,seed).unwrap();
    let members=[[0,1],[1,2],[0,2]][which%3];
    let committee=signer.layout.committee_index(&members).unwrap();
    let leaf=signer.layout.leaf_of(committee,0);
    let pk=*signer.public_key();
    let record=LeafRecord::derive(&pk,leaf,msg).unwrap();
    let nodes=(0..WOTS_CHAINS).map(|chain| {
        let secret=qsag_quorum::hash::h32(b"QSAG.QUORUM.STAGE.SK/v1", &[seed,&leaf.to_be_bytes(),&(chain as u32).to_be_bytes()]);
        chain_walk(&pk.pk_seed,leaf,chain,0,record.digits[chain] as usize,&secret)
    }).collect();
    let reference=QuorumJortsSig{leaf,counter:record.counter,nodes,auth_path:signer.tree.auth_path(leaf)};
    let sig=signer.sign(&members,msg).unwrap();
    let wire=|x:&QuorumJortsSig| {
        let mut b=x.leaf.to_be_bytes().to_vec();b.extend(x.counter.to_be_bytes());
        for node in x.nodes.iter().chain(&x.auth_path) {b.extend(node)} b
    };
    assert_eq!(wire(&sig),wire(&reference));
    assert!(quorum_jorts_verify(&pk,msg,&sig));
    // Duplicated authentic acknowledgement must not authorize an opening.
    let echo=signer.custodians[members[1]].echo_for(committee,members[0]).unwrap();
    assert!(signer.custodians[members[0]].verify_echoes(committee,&[echo.clone(),echo]).is_err());
    "true".into()
}
fn latch_trace(events: &str) -> String {
    use qsag_core::belt_latch::{BeltLatch,BeltLatchError,BindOutcome,MemoryWal,DurableWal};
    let mut latch=BeltLatch::recover(MemoryWal::new(),12).unwrap();
    let mut out=Vec::new();
    for event in events.split(',') {
        if event=="crash" {
            // A process restart retains durable contents, not a pending test fault.
            let old=latch.into_wal(); let snapshot=old.load().unwrap(); drop(old);
            let mut restarted=MemoryWal::new();
            if let Some(state)=snapshot {restarted.sync_persist(&state).unwrap();}
            latch=BeltLatch::recover(restarted,12).unwrap();
        }
        else if event=="fail" {latch.wal_mut().fail_next_persist();}
        else {let v:Vec<u64>=event.split(':').map(|x|x.parse().unwrap()).collect();
            let tag = match latch.bind(v[0],&[v[1] as u8;32],&[v[2] as u8;32],&[v[3] as u8]) {
                Ok(BindOutcome::Fresh) => "fresh",
                Ok(BindOutcome::Replay) => "replay",
                Err(BeltLatchError::WalPoisoned) => "poisoned",
                Err(BeltLatchError::EpochAlreadyBound) => "bound",
                Err(BeltLatchError::RetrySaltMismatch) => "salt",
                Err(BeltLatchError::DigitsMismatch) => "digits",
                Err(BeltLatchError::EpochConsumed) => "consumed",
                Err(BeltLatchError::Exhausted) => "exhausted",
                Err(BeltLatchError::EpochJumpTooLarge) => "jump",
                Err(BeltLatchError::Wal(_)) => "wal",
                Err(_) => "other",
            };
            out.push(tag.to_string());
        }
    }
    format!("{};{};{}",out.join(","),latch.next_epoch(),latch.is_wal_poisoned())
}
// Real authenticated two-slot storage, accessed through its public consumer.
fn ledger_case(a:usize,b:usize,anchor:usize)->String {
    use qsag_core::baggy::{FsFirstSignedLedger,FirstSignedLedger};
    static NEXT:std::sync::atomic::AtomicU64=std::sync::atomic::AtomicU64::new(0);
    let dir=std::env::temp_dir().join(format!("oracle-ledger-{}-{}",std::process::id(),NEXT.fetch_add(1,std::sync::atomic::Ordering::Relaxed)));
    std::fs::create_dir(&dir).unwrap();
    let path=dir.join("snapshot");
    let mut ledger=FsFirstSignedLedger::provision_genesis(&path,[7;32]).unwrap();
    let mut anchors=vec![ledger.checkpoint()];
    for _ in 0..2 {ledger.sync_record(&[]).unwrap();anchors.push(ledger.checkpoint());}
    let mut future=anchors[2];future.generation=3;anchors.push(future);
    drop(ledger);
    for (suffix,damage) in [(".slot_a",a),(".slot_b",b)] {
        let file=dir.join(format!("snapshot{suffix}"));
        let mut bytes=std::fs::read(&file).unwrap();
        match damage {
            0=>{},
            1=>{bytes.truncate(bytes.len()/2);std::fs::write(&file,bytes).unwrap();},
            2=>{let n=bytes.len();bytes[n-1]^=1;std::fs::write(&file,bytes).unwrap();},
            3=>{std::fs::remove_file(&file).unwrap();},
            _=>panic!("damage")
        }
    }
    let result=match FsFirstSignedLedger::open_existing(&path,[7;32],anchors[anchor]) {
        Ok(ledger)=>ledger.checkpoint().generation.to_string(),Err(_)=>"reject".into()
    };
    std::fs::remove_dir_all(&dir).unwrap();
    result
}
fn certificates(seed:&[u8;32],msg:&[u8])->String {
    use qsag_quorum::quorum_jorts::*;
    let mut b=BftShamirJorts::stage(QuorumConfig::with_quorum(2,4,1,3).unwrap(),1,seed).unwrap();
    let (_,cert)=b.certify(&[0,1,2],0,msg).unwrap();
    assert!(b.custodians[3].verify_certificate(&cert).is_ok());
    for fault in 0..6 {
        let mut bad=cert.clone();
        match fault {
            0=>{bad.acks.pop();},
            1=>{bad.acks[2]=bad.acks[1].clone();},
            2=>{bad.acks[2].macs[3][0]^=1;},
            3=>{bad.acks[2].leaf^=1;},
            4=>{bad.acks[2].binding[0]^=1;},
            _=>{bad.acks[2].from=4;}
        }
        assert!(b.custodians[3].verify_certificate(&bad).is_err());
    }
    let mut a=CommitteePartitionedJorts::stage(2,3,2,seed).unwrap();
    let members=a.layout.committees()[0].clone();
    a.sign(&members,msg).unwrap();
    let echo=a.custodians[members[1]].echo_for(0,members[0]).unwrap();
    assert!(a.custodians[members[0]].verify_echoes(0,&[echo.clone()]).is_ok());
    for fault in 0..6 {
        let mut bad=echo.clone();
        match fault {
            0=>bad.mac[0]^=1,
            1=>bad.binding[0]^=1,
            2=>bad.epoch^=1,
            3=>bad.committee+=1,
            4=>bad.from=members[0],
            _=>{}
        }
        let echoes=if fault==5 {vec![bad.clone(),bad]} else {vec![bad]};
        assert!(a.custodians[members[0]].verify_echoes(0,&echoes).is_err());
    }
    "14".into()
}
fn latch(events: &str) -> String {
    use qsag_core::belt_latch::{BeltLatch,MemoryWal,DurableWal};
    let mut latch=BeltLatch::recover(MemoryWal::new(),12).unwrap();
    let mut seen=std::collections::BTreeMap::new();
    let mut high=0;
    for event in events.split(',') {
        if event=="crash" {
            // A process restart retains durable contents, not a pending test fault.
            let old=latch.into_wal(); let snapshot=old.load().unwrap(); drop(old);
            let mut restarted=MemoryWal::new();
            if let Some(state)=snapshot {restarted.sync_persist(&state).unwrap();}
            latch=BeltLatch::recover(restarted,12).unwrap();
        }
        else if event=="fail" {latch.wal_mut().fail_next_persist();}
        else {
            let v:Vec<_>=event.split(':').collect(); let epoch:u64=v[0].parse().unwrap();let m:u8=v[1].parse().unwrap();
            if latch.bind(epoch,&[m;32],&[0;32],&[1,2]).is_ok() {
                if let Some(old)=seen.insert(epoch,m) {assert_eq!(old,m);}
                assert!(epoch+1<=latch.next_epoch());
            }
        }
        assert!(latch.next_epoch()>=high); high=latch.next_epoch();
    }
    "true".into()
}
fn metamorphic(seed: &[u8;32], msg: &[u8]) -> String {
    use qsag_core::{baggy::*, preprocessing::PartyPrivateRng, rss256::Rss256Engine, keccak_mpc::run_dealerless_rss_dkg_2of3};
    let make_rngs=|| std::array::from_fn(|i| {let mut s=*seed;s[0]^=i as u8;PartyPrivateRng::from_seed(s,b"oracle-dkg")});
    let mut ref_rngs:[PartyPrivateRng;3]=make_rngs();
    let mut sk=PqSecretKey{sk_seed:[0;32],sk_prf:[0;32],pk_seed:[0;32]};
    // Replay known deterministic DKG entropy ONLY in the reference test driver.
    // The production signer receives exclusively the real DKG shares.
    for r in &mut ref_rngs {
        let pk=r.next_bytes32(); let _salt=r.next_bytes32();
        let mut ss=[0;32];let mut sp=[0;32];r.fill_bytes(&mut ss);r.fill_bytes(&mut sp);
        for j in 0..32 {sk.pk_seed[j]^=pk[j];sk.sk_seed[j]^=ss[j];sk.sk_prf[j]^=sp[j];}
    }
    let (keys,pkseed)=run_dealerless_rss_dkg_2of3(*seed,32,&mut make_rngs()).unwrap();
    assert_eq!(pkseed,sk.pk_seed);
    let rngs=std::array::from_fn(|i| {let mut s=*seed;s[31]^=i as u8;PartyPrivateRng::from_seed(s,b"oracle-sign")});
    let mut engine=Rss256Engine::new(*seed,keys,rngs).unwrap();
    let params=BaggyParams{num_layers:1,subtree_height:1,fors_trees:2,fors_height:1,..BaggyParams::TEST_SMALL};
    let pk=baggy_reference_keygen(&params,&sk).unwrap();
    let binding=BaggyKeyBinding::new(&params,&pk);engine.bind_key_identity(&binding.identity()).unwrap();
    let sig=baggy_sign_mpc(&mut engine,&params,&pk,&binding,&mut WaistbandCache::disabled(),&mut MemoryFirstSigned::new(),msg).unwrap();
    let reference=baggy_reference_sign(&params,&sk,&pk,msg).unwrap();
    assert_eq!(sig,reference); assert!(baggy_verify(&params,&pk,msg,&sig));
    // Equality covers every signature byte field, including randomizer and counters.
    "true".into()
}
fn main() {
    let stdout=io::stdout(); let mut out=stdout.lock();
    for line in io::stdin().lock().lines() {
        let l=line.unwrap();let a:Vec<_>=l.split('\t').collect();
        writeln!(out,"{}",eval(&a)).unwrap();out.flush().unwrap();
    }
}
'''


class Oracle:
    def __init__(self, binary):
        self.p = subprocess.Popen([str(binary)], stdin=subprocess.PIPE,
                                  stdout=subprocess.PIPE, text=True, bufsize=1)

    def ask(self, args):
        line = "\t".join(map(str, args))
        self.p.stdin.write(line + "\n")
        self.p.stdin.flush()
        if not select.select([self.p.stdout], [], [], 120)[0]:
            raise TimeoutError(f"oracle response timed out on {line}")
        result = self.p.stdout.readline()
        if not result:
            raise RuntimeError(f"oracle exited {self.p.poll()} on {line}")
        return result.rstrip("\r\n")

    def close(self):
        self.p.stdin.close()
        try:
            self.p.wait(timeout=10)
        except subprocess.TimeoutExpired:
            self.p.kill()
            self.p.wait()


def rust_function(source, signature):
    start = source.index(signature)
    opening = source.index("{", start)
    depth = 1
    end = opening + 1
    while depth:
        depth += (source[end] == "{") - (source[end] == "}")
        end += 1
    return source[start:end]


LATCH_MUTANTS = [
    ("poison_check", "belt", "if self.wal_poisoned {", "if false {", "fail,0:0:0:1,1:0:0:1"),
    ("poison_set", "belt", "self.wal_poisoned = true;", "self.wal_poisoned = false;", "fail,0:0:0:1,1:0:0:1"),
    ("epoch_consumed", "kernel", "if req.epoch < self.next_epoch {", "if false {", "2:0:0:1,1:0:0:1"),
    ("epoch_capacity", "kernel", "if req.epoch >= self.capacity_limit {", "if false {", "0:0:0:1"),
    ("epoch_jump", "kernel", "if req.epoch - self.next_epoch > BELT_LATCH_MAX_EPOCH_JUMP {", "if false {", "65:0:0:1"),
    ("retry_salt", "kernel", "if !ct_eq_bytes32(&self.in_flight.retry_salt, &req.retry_salt) {", "if false {", "0:0:0:1,0:0:1:1"),
    ("digits_binding", "kernel", "if !belt_latch_digits_eq(&self.in_flight.digits, &req.digits) {", "if false {", "0:0:0:1,0:0:0:2"),
]
# Walk to the capacity without violating the separate jump guard.
LATCH_MUTANTS[3] = (*LATCH_MUTANTS[3][:4], ",".join(f"{i}:0:0:1" for i in range(0, 4097, 64)))
QUORUM_MUTANTS = [
    ("privacy_threshold", "f >= t", [1, 4, 1, 3]),
    ("honest_reconstruction", "t > q", [4, 4, 1, 3]),
    ("honest_intersection", "two_q <= n_plus_f", [2, 4, 1, 2]),
    ("honest_availability", "require_global_liveness && ((n as u64) < 3 * (f as u64) + 1 || q > n - f)", [2, 4, 1, 4]),
]
BURN_WAL_MUTANTS = [
    ("burn_wal_rollback_guard", "current.generation < minimum.generation", "false", "res:0:0,retain,trunc"),
    ("burn_wal_inode_mac", "!ct_eq_bytes(&journal.last_tag, &bytes[72..104])", "false", "copy"),
]


def driver_source(root):
    source = RUST
    pcs = (root / "crates/qsag-agg/src/pcs.rs").read_text()
    for function in ["fn to_verified_ext4(", "fn from_verified_ext4("]:
        extracted = rust_function(pcs, function)
        source += "\n" + extracted.replace("GoldilocksExt4", "E").replace("Goldilocks", "G")
    belt = (root / "crates/qsag-core/src/belt_latch.rs").read_text()
    # Exclude unit tests, preserve production code verbatim except the named guard.
    belt = belt[:belt.index("#[cfg(test)]")].replace("qsag_verified::BeltLatch", "kernel_mod::BeltLatch")
    latch_kernel = (root / "aeneas/qsag-verified/src/belt_latch_kernel.rs").read_text()
    latch_kernel = "\n".join(line for line in latch_kernel.splitlines() if not line.startswith("//!"))
    latch_kernel = latch_kernel.replace("use crate::tower::ct_eq_bytes32;", "use qsag_verified::ct_eq_bytes32;")
    trace = rust_function(RUST, "fn latch_trace(").replace(
        "use qsag_core::belt_latch::{BeltLatch,BeltLatchError,BindOutcome,MemoryWal,DurableWal};", "")
    arms = []
    for i, (name, target_kind, old, new, _) in enumerate(LATCH_MUTANTS):
        if target_kind == "belt":
            if old not in belt:
                raise RuntimeError(f"mutation anchor disappeared: {name}")
            mutated_belt = belt.replace(old, new)
            mutated_kernel = latch_kernel
        else:
            if latch_kernel.count(old) != 1:
                raise RuntimeError(f"mutation anchor disappeared: {name}")
            mutated_belt = belt
            mutated_kernel = latch_kernel.replace(old, new)
        source += f"\n#[allow(dead_code, unused_variables, unexpected_cfgs)] mod mutant_{i} {{\n" + mutated_belt
        source += "\npub mod kernel_mod {\n" + mutated_kernel + "\n}\n"
        source += "\npub " + trace + "\n}\n"
        arms.append(f'"{name}" => mutant_{i}::latch_trace(a[2]),')
    quorum = (root / "crates/qsag-quorum/src/quorum_jorts.rs").read_text()
    config = rust_function(quorum, "pub fn with_quorum(")
    config = config.replace("Result<Self, QuorumError>", "Result<(), QuorumError>")
    config = config.replace("Ok(Self { t, n, f, q })", "Ok(())")
    kernel = rust_function((root / "aeneas/qsag-verified/src/pants_and_quorum_guards.rs").read_text(),
                           "pub const fn validate_belt_quorum_config(")
    for i, (name, guard, _) in enumerate(QUORUM_MUTANTS):
        assert kernel.count("if " + guard + " {") == 1, name
        mutant = kernel.replace("validate_belt_quorum_config", f"quorum_kernel_{i}").replace("if " + guard + " {", "if false {")
        source += "\n#[allow(unused_variables)]\n" + mutant
        fn = config.replace("with_quorum", f"quorum_mutant_{i}").replace(
            "qsag_verified::validate_belt_quorum_config", f"quorum_kernel_{i}")
        source += "\n" + fn
        arms.append(f'"{name}" => quorum_mutant_{i}(a[2].parse().unwrap(),a[3].parse().unwrap(),a[4].parse().unwrap(),a[5].parse().unwrap()).is_ok().to_string(),')

    # Production SHA3-256 domain-padding mutant (`0x06` -> `0x01`).
    keccak_src = (root / "crates/qsag-accel/src/keccak.rs").read_text()
    sha3_fn = rust_function(keccak_src, "pub fn sha3_256(")
    assert sha3_fn.count("sp.finalize(0x06);") == 1
    sha3_mut = (sha3_fn.replace("pub fn sha3_256(", "fn mutant_sha3_256(")
                       .replace("sp.finalize(0x06);", "sp.finalize(0x01);")
                       .replace("KeccakSponge::<136>", "qsag_accel::keccak::KeccakSponge::<136>"))
    source += "\n" + sha3_mut + "\n"
    arms.append('"sha3_domain_pad" => hex(&mutant_sha3_256(&bytes(a[2]))),')

    # Production Poseidon2 S-box degree drop (`x^7` -> `x^3`).
    pos_src = (root / "crates/qsag-accel/src/poseidon2.rs").read_text()
    pos_head = pos_src[:pos_src.index("/// Stack-allocated zeroizing Width-12")]
    pos_head = "\n".join(line for line in pos_head.splitlines() if not line.startswith("//!"))
    assert pos_head.count("gl_mul(x3, x4)") == 1
    pos_mut = (pos_head.replace("use crate::AccelError;\n", "")
                       .replace("use crate::ct::ct_zeroize_u64s;\n", "")
                       .replace("crate::goldilocks", "qsag_accel::goldilocks")
                       .replace("gl_mul(x3, x4)", "x3"))
    source += "\n#[allow(dead_code, unused_variables)] mod poseidon_mut {\n" + pos_mut + "\n}\n"
    arms.append('"poseidon_sbox_deg3" => { let mut s:[u64;12]=nums(a[2]).try_into().unwrap(); poseidon_mut::poseidon2_perm12(&mut s); csv(&s) },')

    # Production extracted CWYZ duet fold `theta` drop (`theta` -> `0`).
    whir_src = (root / "aeneas/qsag-whir-verified/src/lib.rs").read_text()
    cwyz_fn = rust_function(whir_src, "pub fn cwyz_duet_fold(")
    assert cwyz_fn.count("theta,\n") == 1
    cwyz_mut = (cwyz_fn.replace("pub fn cwyz_duet_fold(", "pub fn mutant_cwyz_duet_fold(")
                       .replace("theta,\n", "Ext4 { a: 0, b: 0, c: 0, d: 0 },\n"))
    source += "\n#[allow(unused_variables)] mod whir_mut {\nuse qsag_whir_verified::*;\n" + cwyz_mut + "\n}\n"
    arms.append(
        '"cwyz_theta_drop" => { let x=G::from_u64_reduced(a[4].parse().unwrap()); let half=G::from_u64_reduced(2).inv(); '
        'let out=whir_mut::mutant_cwyz_duet_fold(to_verified_ext4(ext(a[2])),to_verified_ext4(ext(a[3])),(half*x.inv()).to_canonical_u64(),'
        'half.to_canonical_u64(),(x*x).to_canonical_u64(),to_verified_ext4(ext(a[5])),to_verified_ext4(ext(a[6])),to_verified_ext4(ext(a[7]))); '
        'hex(&from_verified_ext4(out).to_le_bytes()) },'
    )

    # Production POSIX burn WAL (`crates/qsag-fts/src/wal.rs`) clause drops.
    wal_src = (root / "crates/qsag-fts/src/wal.rs").read_text()
    wal_head = wal_src[:wal_src.index("/// A successful reservation")]
    wal_head = "\n".join(line for line in wal_head.splitlines() if not line.startswith("//!"))
    burn_runner = rust_function(RUST, "fn posix_burn_trace(").replace(
        "use qsag_fts::wal::DurableBurnJournal;", "")
    for idx, (mname, old, new, _) in enumerate(BURN_WAL_MUTANTS):
        assert wal_head.count(old) == 1, mname
        mutated = wal_head.replace(old, new)
        source += f"\n#[allow(dead_code, unused_variables)] mod burn_mut_{idx} {{\n" + mutated + "\npub " + burn_runner + "\n}\n"
        arms.append(f'"{mname}" => burn_mut_{idx}::posix_burn_trace(a[2]),')

    source += "\nuse qsag_quorum::quorum_jorts::QuorumError;\nconst MAX_QUORUM_PARTIES:usize=255;\n"
    source += "fn mutation_args(a:&[&str])->String {match a[1] {" + "".join(arms) + '_=>panic!("mutant")}}'
    source = source.replace('"mutation" => mutation(a[1]),', '"mutation" => mutation_args(a),')
    guards = (root / "aeneas/qsag-verified/src/pants_and_quorum_guards.rs").read_text()
    verify = rust_function(guards, "pub fn verified_wotsc256_verify_sum(")
    assert verify.count("sum == WOTSC256_TARGET_SUM") == 1
    verify = verify.replace("verified_wotsc256_verify_sum", "mutant_verify_sum").replace(
        "sum == WOTSC256_TARGET_SUM", "true")
    source += "\nuse qsag_verified::{wotsc256_extract_digit, WOTSC256_CHAINS};\n" + verify
    digits = rust_function((root / "crates/qsag-core/src/wots_c.rs").read_text(), "pub fn digits(")
    assert digits.count("if !self.is_well_formed() {") == 1
    digits = digits.replace("pub fn digits(&self,", "fn mutant_digits(params: &qsag_core::wots_c::WotsCParams,")
    digits = digits.replace("self.", "params.").replace("*self", "*params").replace(
        "Self::V128", "qsag_core::wots_c::WotsCParams::V128")
    digits = digits.replace("qsag_verified::verified_wotsc256_verify_sum(hash)", "mutant_verify_sum(hash)")
    source += "\n" + digits
    generic = digits.replace("mutant_digits", "mutant_generic_digits").replace(
        "mutant_verify_sum(hash)", "qsag_verified::verified_wotsc256_verify_sum(hash)").replace(
        "if !params.is_well_formed() {", "if false {")
    source += "\n#[allow(unused_variables)]\n" + generic
    source = source.replace('fn mutation_args(a:&[&str])->String {match a[1] {',
        'fn mutation_args(a:&[&str])->String {match a[1] {"target_sum"=>mutant_digits(&qsag_core::wots_c::WotsCParams::V128,&arr(a[2])).is_some().to_string(),')
    source = source.replace('fn mutation_args(a:&[&str])->String {match a[1] {',
        'fn mutation_args(a:&[&str])->String {match a[1] {"generic_target_sum"=>mutant_generic_digits(&qsag_core::wots_c::WotsCParams {chains:127,zero_digits:1,target_sum:192},&arr(a[2])).is_some().to_string(),')
    return source


def build_driver(root, directory):
    if platform.system() != "Linux":
        raise RuntimeError("Rust driver builds require Linux")
    directory.mkdir()
    (directory / "src").mkdir()
    deps = "\n".join(
        f'{name} = {{ path = {json.dumps(str(root / "crates" / name))} }}'
        for name in ["qsag-accel", "qsag-core", "qsag-fts", "qsag-agg", "qsag-cred", "qsag-policy", "qsag-quorum"]
    )
    # Volatile WALs are intentional test fixtures for schedule and mutation checks.
    deps = deps.replace('qsag-accel = {', 'qsag-accel = { features = ["std"],')
    deps = deps.replace('qsag-core = {', 'qsag-core = { features = ["std", "testing-ephemeral"],')
    deps = deps.replace('qsag-fts = {', 'qsag-fts = { features = ["std"],')
    deps = deps.replace('qsag-quorum = {', 'qsag-quorum = { features = ["testing-ephemeral"],')
    deps += '\nqsag-whir-verified = { path = ' + json.dumps(str(root / "aeneas/qsag-whir-verified")) + ' }'
    deps += '\nqsag-verified = { path = ' + json.dumps(str(root / "aeneas/qsag-verified")) + ' }'
    (directory / "Cargo.toml").write_text(
        '[workspace]\n[package]\nname="spec-driver"\nversion="0.0.0"\nedition="2024"\n'
        '[features]\ndefault=["testing-ephemeral"]\ntesting-ephemeral=[]\n[dependencies]\n'
        + deps + '\n[profile.release]\nopt-level=2\n'
    )
    (directory / "src/main.rs").write_text(driver_source(root))
    command = ["timeout", "--kill-after=10s", "600s", *(["swarm-build"] if shutil.which("swarm-build") else []), "cargo", "build",
               "--release", "--manifest-path", str(directory / "Cargo.toml"), "-j", "4"]
    subprocess.run(command, check=True, env={**os.environ, "SWARM_MEM_MAX": "10G", "CARGO_BUILD_JOBS": "4",
                                             "CARGO_TARGET_DIR": str((directory / "target").resolve())})
    return directory / "target/release/spec-driver"


def requests(rng, count, rust, surfaces=None):
    def b(n): return rng.randbytes(n).hex()
    def u(): return rng.choice([0, 1, P - 1, P, 2**64 - 1, rng.getrandbits(64)])
    def e(): return b"".join(rng.randrange(P).to_bytes(8, "little") for _ in range(4)).hex()
    operations = [
        "shake", "cshake", "sha3", "sha3_512", "keccak256", "keccak",
        "poseidon", "poseidon16", "poseidon16inv", "poseidon16me",
        "gold", "extdecode", "ext", "tower", "wots", "hybrid", "fors",
        "forsnode", "adrs", "canopy", "binary", "rounding", "poseidonhash",
        "hem", "cosetfold", "cwyzbridge", "quorumnew", "quorumtight",
        "latchtrace", "posixburn", "fsbeltwal",
    ]
    if surfaces is not None:
        unknown = set(surfaces) - set(operations)
        if unknown or not surfaces:
            raise ValueError(f"invalid surfaces: {surfaces}")
        operations = [op for op in operations if op in surfaces]
    for i in range(count):
        op = operations[i % len(operations)]
        n = rng.choice([0, 1, 71, 72, 73, 135, 136, 137, 167, 168, 169, 271, 272, 512, rng.randrange(513)])
        if op == "binary":
            k = rng.choice([3, 7]); bits = 2**k
            yield [op, k, rng.choice(["add", "mul", "square", "inv"]), rng.getrandbits(bits), rng.getrandbits(bits)]
        elif op == "rounding":
            boundary = [0, 1, 4095, 4096, 4097, 8191, 8192, 95231, 95232, 95233, 8380415, 8380416]
            yield [op, rng.choice(boundary + [rng.randrange(8380417)]), rng.randrange(8380417), rng.randrange(2)]
        elif op == "poseidonhash":
            yield [op, b(n)]
        elif op == "hem":
            yield [op, e(), e(), rng.randrange(1, P), e(), e(), e()]
        elif op == "cosetfold":
            yield [op, e(), e(), rng.randrange(1, P), pow(2, -1, P), e()]
        elif op == "cwyzbridge":
            yield [op, *(e() for _ in range(10))]
        elif op == "quorumnew":
            t = rng.randrange(0, 12)
            parties = rng.choice([0, 1, 2, 3, 4, 7, 10, 255, 256, rng.randrange(1, 30)])
            f = rng.randrange(0, 10)
            yield [op, t, parties, f]
        elif op == "quorumtight":
            yield [op, rng.choice([0, 1, 2, 3, 5, 84, 85, 86, 255, 256, rng.randrange(0, 100)])]
        elif op == "latchtrace":
            yield [op, ",".join(rng.choice(["crash", "fail", f"{rng.randrange(80)}:{rng.randrange(3)}:{rng.randrange(3)}:{rng.randrange(3)}"]) for _ in range(20))]
        elif op == "posixburn":
            yield [op, ",".join(rng.choice([
                f"res:{rng.randrange(3)}:{rng.randrange(5)}",
                "retain", "reopen", "trunc", "flip", "copy",
                f"tear:{rng.randrange(1, 42)}",
            ]) for _ in range(rng.randrange(4, 11)))]
        elif op == "fsbeltwal":
            yield [op, ",".join(rng.choice([
                f"{rng.randrange(10)}:{rng.randrange(3)}:{rng.randrange(3)}:{rng.randrange(1, 3)}",
                "retain", "crash", "rollback", "corrupt", "rmlock",
            ]) for _ in range(rng.randrange(4, 11)))]
        elif op == "shake":
            yield [op, rng.randrange(513), b(n)]
        elif op == "cshake":
            yield [op, rng.randrange(513), b(rng.choice([0, 1, 32, 136, 168])), b(n)]
        elif op in ("sha3", "sha3_512", "keccak256"):
            yield [op, b(n)]
        elif op == "keccak":
            yield [op, ",".join(str(u()) for _ in range(25))]
        elif op == "poseidon":
            yield [op, ",".join(str(u()) for _ in range(12))]
        elif op in ("poseidon16", "poseidon16inv"):
            yield [op, ",".join(str(u()) for _ in range(16))]
        elif op == "poseidon16me":
            yield [op, rng.choice(["fwd", "inv"]), ",".join(str(u()) for _ in range(16))]
        elif op == "gold":
            yield [op, rng.choice(["add", "sub", "mul", "inv", "square"]), u(), u()]
        elif op == "extdecode":
            raw = bytes.fromhex(e()) if rng.random() < .5 else b"".join(u().to_bytes(8, "little") for _ in range(4))
            if rng.random() < .2:
                raw = raw[:rng.randrange(32)]
            yield [op, raw.hex()]
        elif op == "ext":
            yield [op, rng.choice(["add", "sub", "mul", "inv", "square", "frobenius"]), e(), e()]
        elif op == "tower":
            yield [op, rng.getrandbits(128), rng.getrandbits(128)]
        elif op == "wots":
            if rng.random() < .5:
                digits = [0, 1, 2, 3] * 32
                rng.shuffle(digits)
                digest = bytes(sum(digits[4 * j + k] << (6 - 2 * k) for k in range(4)) for j in range(32))
                yield [op, digest.hex()]
            else:
                yield [op, b(32)]
        elif op == "hybrid":
            yield [op, b(32), b(n), b(64), b(n)]
        elif op == "fors":
            yield [op, b(32), u(), rng.getrandbits(32), rng.randrange(33), rng.randrange(64), b(32)]
        elif op == "forsnode":
            yield [op, b(32), u(), rng.getrandbits(32), rng.randrange(1, 7), rng.randrange(64), b(32), b(32)]
        elif op == "adrs":
            yield [op, rng.getrandbits(32), rng.getrandbits(96), rng.randrange(7), rng.getrandbits(32), rng.getrandbits(32), rng.getrandbits(32)]
        else:
            depth = rng.randrange(1, 6)
            size = 1 << depth
            nodes = {size + j: b(32) for j in range(size)}
            domain = b"QSAG.PCS.CANOPY/v2".hex()
            for j in range(size - 1, 0, -1):
                frame = "00" + j.to_bytes(4, "little").hex() + nodes[2 * j] + nodes[2 * j + 1]
                nodes[j] = rust.ask(["cshake", 32, domain, frame])
            root = rust.ask(["cshake", 32, domain, "01" + bytes([depth]).hex() + nodes[1]])
            indices = sorted(rng.sample(range(size), rng.randrange(1, size + 1)))
            active = [size + j for j in indices]
            proof = []
            while active != [1]:
                parents = []
                for j in active:
                    if (j ^ 1) not in active:
                        proof.append(nodes[j ^ 1])
                    if j // 2 not in parents:
                        parents.append(j // 2)
                active = parents
            mutation = rng.randrange(5)
            if mutation == 1:
                proof.append(b(32))
            if mutation == 2 and proof:
                proof.pop()
            if mutation == 3:
                indices.reverse()
            if mutation == 4:
                root = b(32)
            yield [op, depth, root, ",".join(map(str, indices)), ",".join(nodes[size + j] for j in indices), ",".join(proof)]


def boundary_requests():
    """Mandatory cases do not depend on random operation selection."""
    for op in ["add", "sub", "mul", "inv", "square"]:
        for a in [0, 1, P - 1, P, 2**64 - 1]:
            for b in [0, 1, P - 1]:
                yield ["gold", op, a, b]
    zero = "00" * 32
    one = (1).to_bytes(8, "little").hex() + "00" * 24
    basis = "00" * 16 + (1).to_bytes(8, "little").hex() + "00" * 8
    for op in ["add", "sub", "mul", "inv", "square", "frobenius"]:
        for a in [zero, one, basis]:
            yield ["ext", op, a, one]
    for k in [3, 7]:
        for op in ["add", "mul", "square", "inv"]:
            for a in [0, 1, 2, 2**(2**k) - 1]:
                yield ["binary", k, op, a, 1]
    for b in range(256):
        yield ["wots", (bytes([b]) * 32).hex()]
    for k in range(44):
        for delta in [-1, 0, 1]:
            r = (k * 190464 + 95232 + delta) % 8380417
            for h in [0, 1]:
                yield ["rounding", r, 1, h]
    for r in [0, 4095, 4096, 4097, 8191, 8192, 8380415, 8380416]:
        for z in [0, 1, 8380416]:
            for h in [0, 1]:
                yield ["rounding", r, z, h]
    for n in [0, 1, 55, 56, 57, 111, 112, 113]:
        yield ["poseidonhash", bytes(range(n)).hex()]
    for n in [0, 1, 135, 136, 137, 271, 272]:
        for out in [0, 1, 135, 136, 137, 272]:
            yield ["shake", out, bytes(i % 256 for i in range(n)).hex()]
    for n in [0, 1, 71, 72, 73, 135, 136, 137, 144]:
        msg = bytes(i % 256 for i in range(n)).hex()
        yield ["sha3", msg]
        yield ["sha3_512", msg]
        yield ["keccak256", msg]
    for s16 in [
        ",".join(["0"] * 16),
        ",".join(str(i + 1) for i in range(16)),
        ",".join([str(P - 1)] * 16),
    ]:
        yield ["poseidon16", s16]
        yield ["poseidon16inv", s16]
        yield ["poseidon16me", "fwd", s16]
        yield ["poseidon16me", "inv", s16]
    yield ["hem", one, zero, 1, one, one, zero]
    yield ["cosetfold", one, basis, pow(2, -1, P), pow(2, -1, P), one]
    yield ["cwyzbridge", one, basis, zero, one, basis, one, basis, one, basis, one]
    for trace in ["fail,crash,1:0:0:1", "1:0:0:1,fail,crash,2:0:0:1"]:
        yield ["latchtrace", trace]
    for _, _, values in QUORUM_MUTANTS:
        yield ["quorum", *values]
    yield ["quorum", 2, 4, 1, 3]
    for t, n, f in [(1, 1, 0), (2, 4, 1), (3, 7, 2), (2, 3, 1), (0, 4, 1), (2, 256, 1)]:
        yield ["quorumnew", t, n, f]
    for t in [0, 1, 2, 3, 5, 85, 86, 255, 256]:
        yield ["quorumtight", t]
    for trace in [
        "res:0:0,reopen",
        "res:0:0,res:0:0",
        "res:0:0,tear:7",
        "res:0:0,trunc",
        "res:0:0,retain,trunc",
        "res:0:0,flip",
        "copy",
    ]:
        yield ["posixburn", trace]
    for trace in [
        "0:1:2:3,crash",
        "0:1:2:3,0:1:2:3,crash",
        "retain,0:1:2:3,rollback",
        "0:1:2:3,rollback",
        "0:1:2:3,corrupt,0:2:2:3",
        "0:1:2:3,rmlock",
    ]:
        yield ["fsbeltwal", trace]
    for digest in [bytes(32), bytes([0x66]) * 32, bytes([0xff]) * 32,
                   bytes([0xff]) * 16 + bytes(16)]:
        yield ["wotsgeneric", digest.hex()]
        yield ["wotsgeneric", 128, 0, 192, digest.hex()]
        yield ["wotsgeneric", 128, 0, 128, digest.hex()]
    for _, _, _, _, trace in LATCH_MUTANTS:
        yield ["latchtrace", trace]


def field_metamorphic(oracle, rng):
    """Relationships are checked separately in both executables."""
    def enc(v): return b"".join(x.to_bytes(8, "little") for x in v).hex()
    a = enc([rng.randrange(P) for _ in range(4)])
    b = enc([rng.randrange(P) for _ in range(4)])
    c = enc([rng.randrange(P) for _ in range(4)])
    zero = enc([0] * 4); one = enc([1, 0, 0, 0])
    ask = lambda op, x, y=zero: oracle.ask(["ext", op, x, y])
    assert ask("sub", ask("add", a, b), b) == a
    assert ask("square", a) == ask("mul", a, a)
    assert ask("mul", a, ask("inv", a)) == one
    f = a
    for _ in range(4):
        f = ask("frobenius", f)
    assert f == a
    assert ask("frobenius", ask("mul", a, b)) == ask("mul", ask("frobenius", a), ask("frobenius", b))
    for k in [3, 7]:
        x = rng.randrange(1, 2**(2**k))
        inv = oracle.ask(["binary", k, "inv", x, 0])
        assert oracle.ask(["binary", k, "mul", x, inv]) == "1"
    m = rng.randbytes(137).hex()
    assert oracle.ask(["shake", 137, m]).startswith(oracle.ask(["shake", 136, m]))
    x = rng.randrange(1, P)
    xi = oracle.ask(["gold", "inv", x, 0])
    assert oracle.ask(["gold", "mul", x, xi]) == "1"
    # With alpha=beta=0 the affine fold is exactly the odd component.
    xbase = enc([x, 0, 0, 0])
    odd = ask("mul", ask("sub", a, b), enc([pow(2 * x, -1, P), 0, 0, 0]))
    assert oracle.ask(["hem", a, b, x, one, zero, zero]) == odd
    # v0=v1 eliminates the odd component; theta becomes irrelevant.
    scale = ask("add", one, ask("square", xbase))
    assert oracle.ask(["hem", a, a, x, b, one, one]) == ask("mul", scale, a)
    # With theta=beta=0, hem reduces identically to duet_fold (`cosetfold`).
    assert oracle.ask(["hem", a, b, x, zero, c, zero]) == oracle.ask(
        ["cosetfold", a, b, pow(2 * x, -1, P), pow(2, -1, P), c]
    )
    # Width-16 Poseidon2 permutation & external MDS layer two-sided invertibility.
    s16 = ",".join(str(rng.randrange(P)) for _ in range(16))
    assert oracle.ask(["poseidon16inv", oracle.ask(["poseidon16", s16])]) == s16
    assert oracle.ask(["poseidon16me", "inv", oracle.ask(["poseidon16me", "fwd", s16])]) == s16
    return 14


def mutation_search(rust, lean=None):
    """Execute independently compiled single-fault production-source mutants.

    Compilation is outside this timer. Every witness rejects on the production
    baseline, differs on the mutant, and agrees with live Lean when supplied.
    The redundant n >= 3f+1 check is deliberately not counted: intersection plus
    honest availability already imply it, so dropping it is an equivalent mutant.
    """
    start = time.perf_counter()
    found = {}
    for name, _, _, _, trace in LATCH_MUTANTS:
        request = ["latchtrace", trace]
        baseline = rust.ask(request)
        if lean is not None:
            assert baseline == lean.ask(request), (name, baseline)
        mutant = rust.ask(["mutation", name, trace])
        assert mutant != baseline, (name, baseline, mutant)
        found[name] = {"request": request, "baseline": baseline, "mutant": mutant, "lean_crosschecked": lean is not None}
    for name, _, values in QUORUM_MUTANTS:
        baseline = rust.ask(["quorum", *values])
        if lean is not None:
            assert baseline == lean.ask(["quorum", *values]), (name, baseline)
        mutant = rust.ask(["mutation", name, *values])
        assert baseline == "false" and mutant == "true", (name, baseline, mutant)
        found[name] = {"request": ["quorum", *values], "baseline": baseline, "mutant": mutant, "lean_crosschecked": lean is not None}
    digest = "00" * 32
    baseline = rust.ask(["wots", digest])
    assert baseline.endswith(";false")
    if lean is not None:
        assert baseline == lean.ask(["wots", digest])
    mutant = rust.ask(["mutation", "target_sum", digest])
    assert mutant == "true"
    found["target_sum"] = {"request": ["wots", digest], "baseline": baseline, "mutant": mutant, "lean_crosschecked": lean is not None}
    valid_v128_digest = "66" * 32
    generic_baseline = rust.ask(["wotsgeneric", valid_v128_digest])
    if lean is not None:
        assert generic_baseline == lean.ask(["wotsgeneric", valid_v128_digest])
    generic_mutant = rust.ask(["mutation", "generic_target_sum", valid_v128_digest])
    assert generic_baseline == "false" and generic_mutant == "true"
    found["generic_target_sum"] = {"request": ["wotsgeneric", valid_v128_digest],
                                   "baseline": generic_baseline, "mutant": generic_mutant,
                                   "lean_crosschecked": lean is not None}

    sha3_req = ["sha3", ""]
    sha3_base = rust.ask(sha3_req)
    if lean is not None:
        assert sha3_base == lean.ask(sha3_req), sha3_base
    sha3_mut = rust.ask(["mutation", "sha3_domain_pad", ""])
    assert sha3_mut != sha3_base and sha3_mut == rust.ask(["keccak256", ""])
    found["sha3_domain_pad"] = {"request": sha3_req, "baseline": sha3_base, "mutant": sha3_mut, "lean_crosschecked": lean is not None}

    pos_state = ",".join(["0"] * 12)
    pos_req = ["poseidon", pos_state]
    pos_base = rust.ask(pos_req)
    if lean is not None:
        assert pos_base == lean.ask(pos_req), pos_base
    pos_mut = rust.ask(["mutation", "poseidon_sbox_deg3", pos_state])
    assert pos_mut != pos_base
    found["poseidon_sbox_deg3"] = {"request": pos_req, "baseline": pos_base, "mutant": pos_mut, "lean_crosschecked": lean is not None}

    zero_ext = "00" * 32
    one_ext = (1).to_bytes(8, "little").hex() + "00" * 24
    hem_args = [one_ext, zero_ext, 1, one_ext, one_ext, zero_ext]
    hem_req = ["hem", *hem_args]
    hem_base = rust.ask(hem_req)
    if lean is not None:
        assert hem_base == lean.ask(hem_req), hem_base
    hem_mut = rust.ask(["mutation", "cwyz_theta_drop", *hem_args])
    assert hem_mut != hem_base
    found["cwyz_theta_drop"] = {"request": hem_req, "baseline": hem_base, "mutant": hem_mut, "lean_crosschecked": lean is not None}

    for name, _, _, trace in BURN_WAL_MUTANTS:
        req = ["posixburn", trace]
        base = rust.ask(req)
        if lean is not None:
            assert base == lean.ask(req), (name, base)
        mut = rust.ask(["mutation", name, trace])
        assert mut != base, (name, base, mut)
        found[name] = {"request": req, "baseline": base, "mutant": mut, "lean_crosschecked": lean is not None}

    elapsed = time.perf_counter() - start
    assert len(found) == 18 and elapsed < 10, (len(found), elapsed)
    if lean is not None:
        assert all(w["lean_crosschecked"] for w in found.values())
    return {
        "caught": len(found),
        "total": 18,
        "elapsed_ms": elapsed * 1000,
        "kind": "compiled production-source clause drops",
        "lean_crosschecked_count": sum(bool(w.get("lean_crosschecked", lean is not None)) for w in found.values()),
        "witnesses": found,
    }


def run(args, rust):
    started = time.perf_counter()
    lean = Oracle(args.oracle_bin)
    counts = Counter()
    mismatches = []
    differential_passed = 0
    rng = random.Random(args.seed)
    try:
        mandatory = [r for r in boundary_requests() if not args.surfaces or r[0] in args.surfaces]
        for request in itertools.chain(mandatory, requests(rng, args.cases, rust, args.surfaces)):
            actual = lean.ask(request)
            expected = rust.ask(request)
            if actual != expected:
                case = {"request": request, "lean": actual, "rust": expected}
                print(json.dumps({"mismatch": case}), flush=True)
                mismatches.append(case)
                key = "\t".join(map(str, request))
                if args.strict_all or KNOWN_MISMATCHES.get(key) != (actual, expected):
                    counts["unexpected_mismatches"] += 1
            else:
                counts[request[0]] += 1
                differential_passed += 1
        for _ in range(args.schedules):
            events = [rng.choice(["sign", "hold", "finish", "contend", "panic", "power", "unlink", "delete"])
                      for _ in range(rng.randrange(5, 35))]
            result = lean.ask(["wal", ",".join(events)])
            accepted, receipts, watermark, held = result.split(";")
            epochs = list(map(int, receipts.split(","))) if receipts else []
            assert len(accepted.split(",")) == len(events)
            assert len(epochs) == len(set(epochs)), (events, result)
            assert epochs == sorted(epochs), (events, result)
            assert all(e < int(watermark) for e in epochs), (events, result)
            assert sum(x == "true" for x in accepted.split(",")) == len(epochs)
            assert held in ["true", "false"]
            counts["wal_schedules"] += 1
            latch_events = [rng.choice(["crash", "fail", f"{rng.randrange(12)}:{rng.randrange(4)}"])
                            for _ in range(rng.randrange(5, 35))]
            assert rust.ask(["latch", ",".join(latch_events)]) == "true"
            counts["rust_latch_schedules"] += 1
            n = rng.randrange(2, 10); f = rng.randrange(n); t = rng.randrange(1, n + 1); q = rng.randrange(1, n + 1)
            expected = f < t <= q and n >= 3 * f + 1 and 2 * q > n + f and q <= n - f
            actual = rust.ask(["quorum", t, n, f, q])
            assert actual == str(expected).lower(), (t, n, f, q, expected, actual)
            assert actual == lean.ask(["quorum", t, n, f, q]), (t, n, f, q, actual)
            new_actual = rust.ask(["quorumnew", t, n, f])
            assert new_actual == lean.ask(["quorumnew", t, n, f]), (t, n, f, new_actual)
            tight_t = rng.randrange(0, 90)
            tight_actual = rust.ask(["quorumtight", tight_t])
            assert tight_actual == lean.ask(["quorumtight", tight_t]), (tight_t, tight_actual)
            counts["lean_rust_quorum_guards"] += 1
        for iteration in range(args.metamorphic):
            assert rust.ask(["certificates", rng.randbytes(32).hex(), rng.randbytes(32).hex()]) == "14"
            counts["rust_certificate_cases"] += 14
            state = rng.getstate()
            counts["lean_field_metamorphic"] += field_metamorphic(lean, rng)
            rng.setstate(state)
            counts["rust_field_metamorphic"] += field_metamorphic(rust, rng)
            assert rust.ask(["metamorphic", rng.randbytes(32).hex(), rng.randbytes(rng.randrange(513)).hex()]) == "true"
            counts["metamorphic_all_three_rss"] += 1
            assert rust.ask(["subset", rng.randbytes(32).hex(), rng.randbytes(rng.randrange(513)).hex(), iteration % 3]) == "true"
            counts["metamorphic_two_party_subsets"] += 1
        for damage_a in range(4):
            for damage_b in range(4):
                for anchor in range(4):
                    request = ["ledger", damage_a, damage_b, anchor]
                    actual = rust.ask(request)
                    expected = lean.ask(request)
                    assert actual == expected, (request, actual, expected)
                    counts["ledger_recovery"] += 1
        mutation = mutation_search(rust, lean)
        report = {
            "seed": args.seed,
            "differential": {
                "vectors": len(mandatory) + args.cases,
                "passed": differential_passed,
                "failed": len(mismatches),
            },
            "selected_surfaces": args.surfaces or "all",
            "passes": dict(counts),
            "total": sum(v for k, v in counts.items() if k != "unexpected_mismatches"),
            "mismatches": mismatches,
            "production_mutations": mutation,
            "runtime_seconds": time.perf_counter() - started,
            "limitations": [
                "Width-12 Poseidon2 calls qsag_accel::poseidon2::poseidon2_perm12; width-16 Poseidon2 cross-checks Lean poseidon2Perm16/poseidon2Perm16Inv against shared poseidon2_const_at/poseidon2_sbox7 primitives.",
                "SHA3-256 and Keccak-256 call exported qsag_accel::keccak::{sha3_256, keccak256}; SHA3-512 exercises exported KeccakSponge::<72>.",
                "POSIX crash WAL schedules (posixburn, fsbeltwal) assert outcome-trace equivalence on DurableBurnJournal and BeltLatch<FsBeltWal>, while power-loss NAND buffer replay (wal) remains a Lean-side state-machine check.",
                "Ledger fixtures exercise Lean authenticated snapshot decoding and Rust filesystem recovery; device/inode identities are OS-assigned on Rust.",
                "Hem, cosetfold, and cwyzbridge call the Aeneas-extracted qsag_whir_verified kernels against theorem-backed Qsag.SpecOracle specifications.",
                "Quorum configuration constructors (with_quorum, new, tight) are cross-checked; full certificate wire equivalence remains a Rust negative-fault check.",
            ],
        }
        print(json.dumps(report, indent=2), flush=True)
        assert counts["unexpected_mismatches"] == 0, mismatches
        return report
    finally:
        lean.close()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--oracle-bin", type=Path, default=Path("lean/.lake/build/bin/spec-oracle"))
    p.add_argument("--rust-bin", type=Path)
    p.add_argument("--seed", type=int, default=130008)
    p.add_argument("--cases", type=int, default=1200)
    p.add_argument("--schedules", type=int, default=500)
    p.add_argument("--metamorphic", type=int, default=50)
    p.add_argument("--surfaces", type=lambda s: s.split(","),
                   help="explicit diagnostic subset; omitted means every surface")
    p.add_argument("--strict-all", action="store_true")
    p.add_argument("--mutations-only", action="store_true",
                   help="run compiled Rust mutations without requiring a Lean executable")
    args = p.parse_args()
    if min(args.cases, args.schedules, args.metamorphic) < 0:
        p.error("counts must be nonnegative")
    if args.strict_all and args.mutations_only:
        p.error("--strict-all cannot be combined with --mutations-only")
    if args.strict_all and (args.surfaces or args.cases < 1200 or args.schedules < 500 or args.metamorphic < 50):
        p.error("--strict-all requires every surface and the full default case counts")
    if platform.system() != "Linux":
        p.error("oracle execution requires Linux")
    root = Path(__file__).resolve().parents[1]
    os.environ["TMPDIR"] = str(root)  # Filesystem fault cases stay on the checkout volume.
    if args.rust_bin:
        rust = Oracle(args.rust_bin)
        try:
            print(json.dumps(mutation_search(rust), indent=2)) if args.mutations_only else run(args, rust)
        finally:
            rust.close()
    else:
        # Unique child avoids overwriting or deleting any other run's files.
        driver_root = root / ".spec-oracle-work"
        driver_root.mkdir(exist_ok=True)
        try:
            with tempfile.TemporaryDirectory(prefix="run-", dir=driver_root) as tmp:
                binary = build_driver(root, Path(tmp) / "driver")
                rust = Oracle(binary)
                try:
                    print(json.dumps(mutation_search(rust), indent=2)) if args.mutations_only else run(args, rust)
                finally:
                    rust.close()
        finally:
            try:
                driver_root.rmdir()  # Only succeeds if empty; preserves concurrent runs.
            except OSError:
                pass


if __name__ == "__main__":
    main()
