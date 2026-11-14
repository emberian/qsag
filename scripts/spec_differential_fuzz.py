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
import json
import itertools
import os
from pathlib import Path
import platform
import select
import random
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
fn sha3(m: &[u8]) -> Vec<u8> {
    // SHA3-256 framing around the production Keccak permutation (rate 136).
    let mut b=m.to_vec(); b.push(6); while b.len()%136!=0 {b.push(0)}
    *b.last_mut().unwrap() |= 128;
    let mut s=[0u64;25];
    for block in b.chunks_exact(136) {
        for (i,w) in block.chunks_exact(8).enumerate() {s[i]^=u64::from_le_bytes(w.try_into().unwrap());}
        keccak_f1600(&mut s);
    }
    s[..4].iter().flat_map(|w|w.to_le_bytes()).collect()
}
fn eval(a: &[&str]) -> String {
    match a[0] {
        "certificates" => certificates(&arr(a[1]),&bytes(a[2])),
        "latchtrace" => latch_trace(a[1]),
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
        "hem" => {let x=G::from_u64_reduced(a[3].parse().unwrap()); let half=G::from_u64_reduced(2).inv();
            hex(&fold_duet_affine_ext4(ext(a[1]),ext(a[2]),half*x.inv(),half,x*x,ext(a[4]),ext(a[5]),ext(a[6])).to_le_bytes())},
        "binary" => {
            use qsag_core::field::tower::{TowerGf256,Tower128};
            if a[1]=="3" {let x=TowerGf256(a[3].parse().unwrap());let y=TowerGf256(a[4].parse().unwrap());
                (match a[2] {"add"=>x.add(y),"mul"=>x.mul(y),"square"=>x.mul(x),"inv"=>x.ct_inv(),_=>panic!("binary op")}).0.to_string()
            } else {let x=Tower128(a[3].parse().unwrap());let y=Tower128(a[4].parse().unwrap());
                (match a[2] {"add"=>x.add(y),"mul"=>x.mul(y),"square"=>x.mul(x),"inv"=>x.ct_inv(),_=>panic!("binary op")}).0.to_string()}
        },
        "shake" => hex(&shake256_xof(a[1].parse().unwrap(), &bytes(a[2]))),
        "cshake" => hex(&cshake256_xof(a[1].parse().unwrap(), &bytes(a[2]), &bytes(a[3]))),
        "sha3" => hex(&sha3(&bytes(a[1]))),
        "keccak" => { let mut s:[u64;25]=nums(a[1]).try_into().unwrap(); keccak_f1600(&mut s); csv(&s) },
        "poseidon" => { let mut s:Poseidon2State12=nums(a[1]).iter().map(|x|qsag_core::field::goldilocks::Goldilocks::from_u64_reduced(*x)).collect::<Vec<_>>().try_into().unwrap(); poseidon2_perm12(&mut s); csv(&s.iter().map(|x|x.to_canonical_u64()).collect::<Vec<_>>()) },
        "gold" => {let x=G::from_u64_reduced(a[2].parse().unwrap()); let y=G::from_u64_reduced(a[3].parse().unwrap());
            let z=match a[1] {"add"=>x+y,"sub"=>x-y,"mul"=>x*y,"inv"=>x.inv(),"square"=>x.square(),_=>panic!("op")};
            let cx=qsag_core::field::goldilocks::Goldilocks::from_u64_reduced(a[2].parse().unwrap());
            let cy=qsag_core::field::goldilocks::Goldilocks::from_u64_reduced(a[3].parse().unwrap());
            let cz=match a[1] {"add"=>cx+cy,"sub"=>cx-cy,"mul"=>cx*cy,"inv"=>cx.inv(),"square"=>cx.square(),_=>panic!("op")};
            assert_eq!(z.to_canonical_u64(),cz.to_canonical_u64()); z.to_canonical_u64().to_string()},
        "extdecode" => { let v=bytes(a[1]); match <[u8;32]>::try_from(v).ok().and_then(E::from_le_bytes_canonical) {Some(x)=>hex(&x.to_le_bytes()),None=>"reject".into()} },
        "ext" => { let x=ext(a[2]); let y=ext(a[3]); hex(&(match a[1] {"add"=>x+y,"sub"=>x-y,"mul"=>x*y,"inv"=>x.inv(),"square"=>x.square(),"frobenius"=>x.frobenius(),_=>panic!("extension op")}).to_le_bytes()) },
        "tower" => qsag_core::field::tower::tower_mul_t7(a[1].parse().unwrap(),a[2].parse().unwrap()).to_string(),
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
        "metamorphic" => metamorphic(&arr(a[1]),&bytes(a[2])),
        _ => panic!("unknown operation")
    }
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
    use qsag_core::belt_latch::{BeltLatch,MemoryWal};
    let mut latch=BeltLatch::recover(MemoryWal::new(),12).unwrap();
    let mut out=Vec::new();
    for event in events.split(',') {
        if event=="crash" {latch=BeltLatch::recover(latch.into_wal(),12).unwrap();}
        else if event=="fail" {latch.wal_mut().fail_next_persist();}
        else {let v:Vec<u64>=event.split(':').map(|x|x.parse().unwrap()).collect();
            out.push(latch.bind(v[0],&[v[1] as u8;32],&[v[2] as u8;32],&[v[3] as u8]).is_ok().to_string());
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
    use qsag_core::belt_latch::{BeltLatch,MemoryWal};
    let mut latch=BeltLatch::recover(MemoryWal::new(),12).unwrap();
    let mut seen=std::collections::BTreeMap::new();
    let mut high=0;
    for event in events.split(',') {
        if event=="crash" {latch=BeltLatch::recover(latch.into_wal(),12).unwrap();}
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
    let pk=baggy_reference_keygen(&params,&sk);
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
    ("poison_check", "if self.wal_poisoned {", "if false {", "fail,0:0:0:1,1:0:0:1"),
    ("poison_set", "self.wal_poisoned = true;", "self.wal_poisoned = false;", "fail,0:0:0:1,1:0:0:1"),
    ("epoch_consumed", "if epoch < self.state.next_epoch {", "if false {", "2:0:0:1,1:0:0:1"),
    ("epoch_capacity", "if epoch >= 1u64 << self.capacity_log2 {", "if false {", "0:0:0:1"),
    ("epoch_jump", "if epoch > self.state.next_epoch + MAX_EPOCH_JUMP {", "if false {", "65:0:0:1"),
    ("retry_salt", "if !ct_eq_bytes32(&salt, retry_salt) {", "if false {", "0:0:0:1,0:0:1:1"),
    ("digits_binding", "if rec.target_sum_digits != target_sum_digits {", "if false {", "0:0:0:1,0:0:0:2"),
]
# Walk to the capacity without violating the separate jump guard.
LATCH_MUTANTS[3] = (*LATCH_MUTANTS[3][:3], ",".join(f"{i}:0:0:1" for i in range(0, 4097, 64)))
QUORUM_MUTANTS = [
    ("privacy_threshold", "f >= t", [1,4,1,3]),
    ("honest_reconstruction", "t > n - f", [4,4,1,3]),
    ("honest_intersection", "2 * q <= n + f", [2,4,1,2]),
    ("honest_availability", "q > n - f", [2,4,1,4]),
]


def driver_source(root):
    source = RUST
    pcs = (root / "crates/qsag-agg/src/pcs.rs").read_text()
    fold = rust_function(pcs, "fn fold_duet_affine_ext4(")
    source += "\n" + fold.replace("GoldilocksExt4", "E").replace("Goldilocks", "G")
    belt = (root / "crates/qsag-core/src/belt_latch.rs").read_text()
    # Exclude unit tests, preserve production code verbatim except the named guard.
    belt = belt[:belt.index("#[cfg(test)]")]
    trace = rust_function(RUST, "fn latch_trace(").replace(
        "use qsag_core::belt_latch::{BeltLatch,MemoryWal};", "")
    arms = []
    for i, (name, old, new, _) in enumerate(LATCH_MUTANTS):
        if old not in belt:
            raise RuntimeError(f"mutation anchor disappeared: {name}")
        mutated = belt.replace(old, new)
        source += f"\n#[allow(dead_code, unused_variables, unexpected_cfgs)] mod mutant_{i} {{\n" + mutated
        source += "\npub " + trace + "\n}\n"
        arms.append(f'"{name}" => mutant_{i}::latch_trace(a[2]),')
    quorum = (root / "crates/qsag-quorum/src/quorum_jorts.rs").read_text()
    config = rust_function(quorum, "pub fn with_quorum(")
    config = config.replace("Result<Self, QuorumError>", "Result<(), QuorumError>")
    config = config.replace("Ok(Self { t, n, f, q })", "Ok(())")
    for i, (name, guard, _) in enumerate(QUORUM_MUTANTS):
        assert config.count("if " + guard + " {") == 1, name
        fn = config.replace("with_quorum", f"quorum_mutant_{i}").replace("if " + guard + " {", "if false {")
        source += "\n" + fn
        arms.append(f'"{name}" => quorum_mutant_{i}(a[2].parse().unwrap(),a[3].parse().unwrap(),a[4].parse().unwrap(),a[5].parse().unwrap()).is_ok().to_string(),')
    source += "\nuse qsag_quorum::quorum_jorts::QuorumError;\nconst MAX_QUORUM_PARTIES:usize=255;\n"
    source += "fn mutation_args(a:&[&str])->String {match a[1] {" + "".join(arms) + '_=>panic!("mutant")}}'
    source = source.replace('"mutation" => mutation(a[1]),', '"mutation" => mutation_args(a),')
    digits = rust_function((root / "crates/qsag-core/src/wots_c.rs").read_text(), "pub fn digits(")
    assert digits.count("if sum != self.target_sum {") == 1
    digits = digits.replace("pub fn digits(&self,", "fn mutant_digits(params: &qsag_core::wots_c::WotsCParams,")
    digits = digits.replace("self.", "params.").replace("if sum != params.target_sum {", "if false {")
    source += "\n#[allow(unused_variables)]\n" + digits
    source = source.replace('fn mutation_args(a:&[&str])->String {match a[1] {',
        'fn mutation_args(a:&[&str])->String {match a[1] {"target_sum"=>mutant_digits(&qsag_core::wots_c::WotsCParams::V128,&arr(a[2])).is_some().to_string(),')
    source += "\nuse qsag_core::wots_c::WOTS_DIGEST_DIGITS;\n"
    return source


def build_driver(root, directory):
    if platform.system() != "Linux":
        raise RuntimeError("Rust driver builds require Linux")
    directory.mkdir()
    (directory / "src").mkdir()
    deps = "\n".join(f'{name} = {{ path = {json.dumps(str(root / "crates" / name))} }}'
                     for name in ["qsag-core", "qsag-agg", "qsag-cred", "qsag-policy", "qsag-quorum"])
    (directory / "Cargo.toml").write_text('[workspace]\n[package]\nname="spec-driver"\nversion="0.0.0"\nedition="2024"\n[dependencies]\n' + deps.replace('qsag-core = {', 'qsag-core = { features = ["std"],') + '\n[profile.release]\nopt-level=2\n')
    (directory / "src/main.rs").write_text(driver_source(root))
    command = ["timeout", "--kill-after=10s", "600s", "swarm-build", "cargo", "build",
               "--release", "--manifest-path", str(directory / "Cargo.toml"), "-j", "2"]
    subprocess.run(command, check=True, env={**os.environ, "SWARM_MEM_MAX": "12G",
                                                  "CARGO_TARGET_DIR": str((directory / "target").resolve())})
    return directory / "target/release/spec-driver"


def requests(rng, count, rust, surfaces=None):
    def b(n): return rng.randbytes(n).hex()
    def u(): return rng.choice([0, 1, P-1, P, 2**64-1, rng.getrandbits(64)])
    def e(): return b"".join(rng.randrange(P).to_bytes(8, "little") for _ in range(4)).hex()
    operations = ["shake", "cshake", "sha3", "keccak", "poseidon", "gold", "extdecode",
                  "ext", "tower", "wots", "hybrid", "fors", "forsnode", "adrs", "canopy",
                  "binary", "rounding", "poseidonhash", "hem", "latchtrace"]
    if surfaces is not None:
        unknown = set(surfaces) - set(operations)
        if unknown or not surfaces: raise ValueError(f"invalid surfaces: {surfaces}")
        operations = [op for op in operations if op in surfaces]
    for i in range(count):
        op = operations[i % len(operations)]
        n = rng.choice([0, 1, 135, 136, 137, 167, 168, 169, 271, 272, 512, rng.randrange(513)])
        if op == "binary":
            k = rng.choice([3,7]); bits = 2**k
            yield [op,k,rng.choice(["add","mul","square","inv"]),rng.getrandbits(bits),rng.getrandbits(bits)]
        elif op == "rounding":
            boundary = [0,1,4095,4096,4097,8191,8192,95231,95232,95233,8380415,8380416]
            yield [op,rng.choice(boundary+[rng.randrange(8380417)]),rng.randrange(8380417),rng.randrange(2)]
        elif op == "poseidonhash": yield [op,b(n)]
        elif op == "hem": yield [op,e(),e(),rng.randrange(1,P),e(),e(),e()]
        elif op == "latchtrace":
            yield [op, ",".join(rng.choice(["crash","fail",f"{rng.randrange(80)}:{rng.randrange(3)}:{rng.randrange(3)}:{rng.randrange(3)}"]) for _ in range(20))]
        elif op == "shake": yield [op, rng.randrange(513), b(n)]
        elif op == "cshake": yield [op, rng.randrange(513), b(rng.choice([0,1,32,136,168])), b(n)]
        elif op == "sha3": yield [op, b(n)]
        elif op == "keccak": yield [op, ",".join(str(u()) for _ in range(25))]
        elif op == "poseidon": yield [op, ",".join(str(u()) for _ in range(12))]
        elif op == "gold": yield [op, rng.choice(["add", "sub", "mul", "inv", "square"]), u(), u()]
        elif op == "extdecode":
            raw = bytes.fromhex(e()) if rng.random() < .5 else b"".join(u().to_bytes(8,"little") for _ in range(4))
            if rng.random() < .2: raw = raw[:rng.randrange(32)]
            yield [op, raw.hex()]
        elif op == "ext": yield [op, rng.choice(["add", "sub", "mul", "inv", "square", "frobenius"]), e(), e()]
        elif op == "tower": yield [op, rng.getrandbits(128), rng.getrandbits(128)]
        elif op == "wots":
            if rng.random() < .5:
                digits = [0,1,2,3]*32
                rng.shuffle(digits)
                digest = bytes(sum(digits[4*j+k] << (6-2*k) for k in range(4)) for j in range(32))
                yield [op, digest.hex()]
            else: yield [op, b(32)]
        elif op == "hybrid": yield [op, b(32), b(n), b(64), b(n)]
        elif op == "fors": yield [op, b(32), u(), rng.getrandbits(32), rng.randrange(33), rng.randrange(64), b(32)]
        elif op == "forsnode": yield [op, b(32), u(), rng.getrandbits(32), rng.randrange(1,7), rng.randrange(64), b(32), b(32)]
        elif op == "adrs": yield [op, rng.getrandbits(32), rng.getrandbits(96), rng.randrange(7), rng.getrandbits(32), rng.getrandbits(32), rng.getrandbits(32)]
        else:
            depth = rng.randrange(1, 6)
            size = 1 << depth
            nodes = {size+j: b(32) for j in range(size)}
            domain = b"QSAG.PCS.CANOPY/v2".hex()
            for j in range(size-1, 0, -1):
                frame = "00" + j.to_bytes(4,"little").hex() + nodes[2*j] + nodes[2*j+1]
                nodes[j] = rust.ask(["cshake",32,domain,frame])
            root = rust.ask(["cshake",32,domain,"01"+bytes([depth]).hex()+nodes[1]])
            indices = sorted(rng.sample(range(size), rng.randrange(1,size+1)))
            active = [size+j for j in indices]
            proof = []
            while active != [1]:
                parents = []
                for j in active:
                    if (j ^ 1) not in active: proof.append(nodes[j ^ 1])
                    if j//2 not in parents: parents.append(j//2)
                active = parents
            mutation = rng.randrange(5)
            if mutation == 1: proof.append(b(32))
            if mutation == 2 and proof: proof.pop()
            if mutation == 3: indices.reverse()
            if mutation == 4: root = b(32)
            yield [op, depth, root, ",".join(map(str,indices)), ",".join(nodes[size+j] for j in indices), ",".join(proof)]


def boundary_requests():
    """Mandatory cases do not depend on random operation selection."""
    for op in ["add", "sub", "mul", "inv", "square"]:
        for a in [0,1,P-1,P,2**64-1]:
            for b in [0,1,P-1]:
                yield ["gold", op, a, b]
    zero = "00"*32
    one = (1).to_bytes(8,"little").hex() + "00"*24
    basis = "00"*16 + (1).to_bytes(8,"little").hex() + "00"*8
    for op in ["add","sub","mul","inv","square","frobenius"]:
        for a in [zero,one,basis]:
            yield ["ext",op,a,one]
    for k in [3,7]:
        for op in ["add","mul","square","inv"]:
            for a in [0,1,2,2**(2**k)-1]:
                yield ["binary",k,op,a,1]
    for b in range(256):
        yield ["wots", (bytes([b])*32).hex()]
    for k in range(44):
        for delta in [-1,0,1]:
            r=(k*190464+95232+delta)%8380417
            for h in [0,1]:
                yield ["rounding",r,1,h]
    for r in [0,4095,4096,4097,8191,8192,8380415,8380416]:
        for z in [0,1,8380416]:
            for h in [0,1]:
                yield ["rounding",r,z,h]
    for n in [0,1,55,56,57,111,112,113]:
        yield ["poseidonhash",bytes(range(n)).hex()]
    for n in [0,1,135,136,137,271,272]:
        for out in [0,1,135,136,137,272]:
            yield ["shake",out,bytes(i%256 for i in range(n)).hex()]
    for _, _, _, trace in LATCH_MUTANTS:
        yield ["latchtrace",trace]


def field_metamorphic(oracle, rng):
    """Relationships are checked separately in both executables."""
    def enc(v): return b"".join(x.to_bytes(8,"little") for x in v).hex()
    a=enc([rng.randrange(P) for _ in range(4)])
    b=enc([rng.randrange(P) for _ in range(4)])
    zero=enc([0]*4); one=enc([1,0,0,0])
    ask=lambda op,x,y=zero: oracle.ask(["ext",op,x,y])
    assert ask("sub",ask("add",a,b),b)==a
    assert ask("square",a)==ask("mul",a,a)
    assert ask("mul",a,ask("inv",a))==one
    f=a
    for _ in range(4): f=ask("frobenius",f)
    assert f==a
    assert ask("frobenius",ask("mul",a,b))==ask("mul",ask("frobenius",a),ask("frobenius",b))
    for k in [3,7]:
        x=rng.randrange(1,2**(2**k))
        inv=oracle.ask(["binary",k,"inv",x,0])
        assert oracle.ask(["binary",k,"mul",x,inv])=="1"
    m=rng.randbytes(137).hex()
    assert oracle.ask(["shake",137,m]).startswith(oracle.ask(["shake",136,m]))
    x = rng.randrange(1,P)
    xi = oracle.ask(["gold","inv",x,0])
    assert oracle.ask(["gold","mul",x,xi]) == "1"
    # With alpha=beta=0 the affine fold is exactly the odd component.
    xbase=enc([x,0,0,0])
    odd=ask("mul",ask("sub",a,b),enc([pow(2*x,-1,P),0,0,0]))
    assert oracle.ask(["hem",a,b,x,one,zero,zero])==odd
    # v0=v1 eliminates the odd component; theta becomes irrelevant.
    scale=ask("add",one,ask("square",xbase))
    assert oracle.ask(["hem",a,a,x,b,one,one])==ask("mul",scale,a)
    return 11


def mutation_search(rust, lean=None):
    """Execute independently compiled single-fault production-source mutants.

    Compilation is outside this timer. Every witness rejects on the production
    baseline, differs on the mutant, and (for latch/WOTS) agrees with live Lean.
    The redundant n >= 3f+1 check is deliberately not counted: intersection plus
    honest availability already imply it, so dropping it is an equivalent mutant.
    """
    start = time.perf_counter()
    found = {}
    for name, _, _, trace in LATCH_MUTANTS:
        request = ["latchtrace", trace]
        baseline = rust.ask(request)
        if lean is not None:
            assert baseline == lean.ask(request), (name, baseline)
        mutant = rust.ask(["mutation", name, trace])
        assert mutant != baseline, (name, baseline, mutant)
        found[name] = {"request": request, "baseline": baseline, "mutant": mutant}
    for name, _, values in QUORUM_MUTANTS:
        baseline = rust.ask(["quorum", *values])
        mutant = rust.ask(["mutation", name, *values])
        assert baseline == "false" and mutant == "true", (name,baseline,mutant)
        found[name] = {"request": ["quorum", *values], "baseline": baseline, "mutant": mutant}
    digest = "00" * 32
    baseline = rust.ask(["wots", digest])
    assert baseline.endswith(";false")
    if lean is not None:
        assert baseline == lean.ask(["wots", digest])
    mutant = rust.ask(["mutation", "target_sum", digest])
    assert mutant == "true"
    found["target_sum"] = {"request": ["wots", digest], "baseline": baseline, "mutant": mutant}
    elapsed = time.perf_counter() - start
    assert len(found) == 12 and elapsed < 5, (len(found), elapsed)
    return {"caught": len(found), "total": 12, "elapsed_ms": elapsed*1000,
            "kind": "compiled production-source clause drops", "lean_crosschecked": lean is not None, "witnesses": found}



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
                case = {"request":request,"lean":actual,"rust":expected}
                print(json.dumps({"mismatch":case}), flush=True)
                mismatches.append(case)
                key = "\t".join(map(str,request))
                if args.strict_all or KNOWN_MISMATCHES.get(key) != (actual, expected):
                    counts["unexpected_mismatches"] += 1
            else:
                counts[request[0]] += 1
                differential_passed += 1
        for _ in range(args.schedules):
            events = [rng.choice(["sign","hold","finish","contend","panic","power","unlink","delete"])
                      for _ in range(rng.randrange(5,35))]
            result = lean.ask(["wal", ",".join(events)])
            accepted, receipts, watermark, held = result.split(";")
            epochs = list(map(int, receipts.split(","))) if receipts else []
            assert len(accepted.split(",")) == len(events)
            assert len(epochs) == len(set(epochs)), (events,result)
            assert epochs == sorted(epochs), (events,result)
            assert all(e < int(watermark) for e in epochs), (events,result)
            assert sum(x=="true" for x in accepted.split(",")) == len(epochs)
            assert held in ["true","false"]
            counts["wal_schedules"] += 1
            latch_events = [rng.choice(["crash", "fail", f"{rng.randrange(12)}:{rng.randrange(4)}"])
                            for _ in range(rng.randrange(5,35))]
            assert rust.ask(["latch", ",".join(latch_events)]) == "true"
            counts["rust_latch_schedules"] += 1
            n = rng.randrange(2,10); f = rng.randrange(n); t = rng.randrange(1,n+1); q = rng.randrange(1,n+1)
            expected = f < t and n >= 3*f+1 and t <= n-f and 2*q > n+f and q <= n-f
            assert rust.ask(["quorum", t, n, f, q]) == str(expected).lower()
            counts["rust_quorum_guards"] += 1
        for iteration in range(args.metamorphic):
            assert rust.ask(["certificates",rng.randbytes(32).hex(),rng.randbytes(32).hex()]) == "14"
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
        report = {"seed":args.seed,
                  "differential":{"vectors":len(mandatory)+args.cases,
                                  "passed":differential_passed,"failed":len(mismatches)},
                  "selected_surfaces":args.surfaces or "all","passes":dict(counts),"total":sum(v for k,v in counts.items() if k != "unexpected_mismatches"),
                  "mismatches":mismatches,"production_mutations":mutation, "runtime_seconds":time.perf_counter()-started,
                  "limitations":["Repository Poseidon2 is width 12, not width 16.",
                    "SHA3 is padding around live Keccak, not a separately exported digest API.",
                    "WAL schedules execute the Lean model; Rust POSIX crash equivalence is not asserted.",
                    "Ledger decision table is an oracle adapter; no two-slot Qsag definition currently exists.",
                    "Hem calls the extracted private Rust fold; its oracle formula composes live Qsag field operations.",
                    "Quorum configuration is Rust-only; certificate equivalence is not asserted."]}
        print(json.dumps(report,indent=2), flush=True)
        assert counts["unexpected_mismatches"] == 0, mismatches
        return report
    finally:
        lean.close()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--oracle-bin",type=Path,default=Path("lean/.lake/build/bin/spec-oracle"))
    p.add_argument("--rust-bin",type=Path)
    p.add_argument("--seed",type=int,default=130008)
    p.add_argument("--cases",type=int,default=1200)
    p.add_argument("--schedules",type=int,default=500)
    p.add_argument("--metamorphic",type=int,default=50)
    p.add_argument("--surfaces", type=lambda s:s.split(","),
                   help="explicit diagnostic subset; omitted means every surface")
    p.add_argument("--strict-all",action="store_true")
    p.add_argument("--mutations-only",action="store_true",
                   help="run compiled Rust mutations without requiring a Lean executable")
    args = p.parse_args()
    if min(args.cases,args.schedules,args.metamorphic)<0: p.error("counts must be nonnegative")
    if args.strict_all and args.mutations_only:
        p.error("--strict-all cannot be combined with --mutations-only")
    if args.strict_all and (args.surfaces or args.cases < 1200 or args.schedules < 500 or args.metamorphic < 50):
        p.error("--strict-all requires every surface and the full default case counts")
    if platform.system() != "Linux":
        p.error("oracle execution requires Linux")
    root = Path(__file__).resolve().parents[1]
    os.environ["TMPDIR"] = str(root)  # Filesystem fault cases stay on the checkout volume.
    if args.rust_bin:
        rust=Oracle(args.rust_bin)
        try: print(json.dumps(mutation_search(rust), indent=2)) if args.mutations_only else run(args,rust)
        finally: rust.close()
    else:
        # Unique child avoids overwriting or deleting any other run's files.
        driver_root = root / ".spec-oracle-work"
        driver_root.mkdir(exist_ok=True)
        try:
            with tempfile.TemporaryDirectory(prefix="run-", dir=driver_root) as tmp:
                binary=build_driver(root,Path(tmp)/"driver")
                rust=Oracle(binary)
                try: print(json.dumps(mutation_search(rust), indent=2)) if args.mutations_only else run(args,rust)
                finally: rust.close()
        finally:
            try: driver_root.rmdir()  # Only succeeds if empty; preserves concurrent runs.
            except OSError: pass

if __name__ == "__main__":
    main()
