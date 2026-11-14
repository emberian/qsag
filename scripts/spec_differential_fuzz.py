#!/usr/bin/env python3
"""Executable live-spec differential tests. Run on Linux, never builds on Darwin.

Protocol is documented by the dispatch in SpecOracle.lean. Each generated request
is sent to both independent processes. A mismatch is fatal unless its *exact*
request/output triple is listed in KNOWN_MISMATCHES; --strict-all fails those too.
Temporary Rust sources and build products are removed even after test failure.
Mutation tests are explicitly harness sensitivity tests, not library proofs.
"""
import argparse
from collections import Counter
import json
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
        "shake" => hex(&shake256_xof(a[1].parse().unwrap(), &bytes(a[2]))),
        "cshake" => hex(&cshake256_xof(a[1].parse().unwrap(), &bytes(a[2]), &bytes(a[3]))),
        "sha3" => hex(&sha3(&bytes(a[1]))),
        "keccak" => { let mut s:[u64;25]=nums(a[1]).try_into().unwrap(); keccak_f1600(&mut s); csv(&s) },
        "poseidon" => { let mut s:Poseidon2State12=nums(a[1]).iter().map(|x|qsag_core::field::goldilocks::Goldilocks::from_u64_reduced(*x)).collect::<Vec<_>>().try_into().unwrap(); poseidon2_perm12(&mut s); csv(&s.iter().map(|x|x.to_canonical_u64()).collect::<Vec<_>>()) },
        "gold" => {let x=G::from_u64_reduced(a[2].parse().unwrap()); let y=G::from_u64_reduced(a[3].parse().unwrap());
            let z=match a[1] {"add"=>x+y,"sub"=>x-y,"mul"=>x*y,"inv"=>x.inv(),_=>panic!("op")}; z.to_canonical_u64().to_string()},
        "extdecode" => { let v=bytes(a[1]); match <[u8;32]>::try_from(v).ok().and_then(E::from_le_bytes_canonical) {Some(x)=>hex(&x.to_le_bytes()),None=>"reject".into()} },
        "ext" => { let x=ext(a[2]); let y=ext(a[3]); hex(&(if a[1]=="inv" {x.inv()} else {x*y}).to_le_bytes()) },
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


def build_driver(root, directory):
    if platform.system() != "Linux":
        raise RuntimeError("Rust driver builds require Linux")
    directory.mkdir()
    (directory / "src").mkdir()
    deps = "\n".join(f'{name} = {{ path = {json.dumps(str(root / "crates" / name))} }}'
                     for name in ["qsag-core", "qsag-agg", "qsag-cred", "qsag-policy", "qsag-quorum"])
    (directory / "Cargo.toml").write_text('[package]\nname="spec-driver"\nversion="0.0.0"\nedition="2024"\n[dependencies]\n' + deps + '\n[profile.release]\nopt-level=2\n')
    (directory / "src/main.rs").write_text(RUST)
    command = ["timeout", "--kill-after=10s", "600s", "swarm-build", "cargo", "build",
               "--release", "--manifest-path", str(directory / "Cargo.toml"), "-j", "2"]
    subprocess.run(command, check=True, env={**os.environ, "SWARM_MEM_MAX": "12G"})
    return directory / "target/release/spec-driver"


def requests(rng, count, rust, surfaces=None):
    def b(n): return rng.randbytes(n).hex()
    def u(): return rng.choice([0, 1, P-1, P, 2**64-1, rng.getrandbits(64)])
    def e(): return b"".join(rng.randrange(P).to_bytes(8, "little") for _ in range(4)).hex()
    operations = ["shake", "cshake", "sha3", "keccak", "poseidon", "gold", "extdecode",
                  "ext", "tower", "wots", "hybrid", "fors", "forsnode", "adrs", "canopy"]
    if surfaces is not None:
        unknown = set(surfaces) - set(operations)
        if unknown or not surfaces: raise ValueError(f"invalid surfaces: {surfaces}")
        operations = [op for op in operations if op in surfaces]
    for i in range(count):
        op = operations[i % len(operations)]
        n = rng.choice([0, 1, 135, 136, 137, 167, 168, 169, 271, 272, 512, rng.randrange(513)])
        if op == "shake": yield [op, rng.randrange(513), b(n)]
        elif op == "cshake": yield [op, rng.randrange(513), b(rng.choice([0,1,32,136,168])), b(n)]
        elif op == "sha3": yield [op, b(n)]
        elif op == "keccak": yield [op, ",".join(str(u()) for _ in range(25))]
        elif op == "poseidon": yield [op, ",".join(str(u()) for _ in range(12))]
        elif op == "gold": yield [op, rng.choice(["add", "sub", "mul", "inv"]), u(), u()]
        elif op == "extdecode":
            raw = bytes.fromhex(e()) if rng.random() < .5 else b"".join(u().to_bytes(8,"little") for _ in range(4))
            if rng.random() < .2: raw = raw[:rng.randrange(32)]
            yield [op, raw.hex()]
        elif op == "ext": yield [op, rng.choice(["mul", "inv"]), e(), e()]
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


def mutation_search(rng):
    """Run identical random action traces through a guarded harness and five mutants.

    Observers inspect emitted effects, independently of acceptance predicates.
    These are harness mutants; production libraries are never rewritten.
    """
    guards = ["unique_custodian", "quorum_intersection", "epoch_monotonic", "target_sum", "canonical_limb"]
    found = {}
    start = time.perf_counter()

    def execute(trace, dropped):
        durable_epoch = -1
        emitted_epochs = set()
        for turn, action in enumerate(trace):
            kind, value = action
            violation = False
            if kind == "ack":
                votes = value if dropped == "unique_custodian" else set(value)
                if len(votes) >= 3:
                    # Observer counts the principals actually represented by a release.
                    violation = len({party for party in value}) < 3
            elif kind == "quorum":
                n, f, q, left, right = value
                if dropped == "quorum_intersection" or 2*q > n+f:
                    # Two independently sampled certificates must share an honest voter.
                    honest = set(range(f, n))
                    violation = not (set(left) & set(right) & honest)
            elif kind == "epoch":
                if dropped == "epoch_monotonic" or value > durable_epoch:
                    violation = value in emitted_epochs or value < durable_epoch
                    emitted_epochs.add(value)
                    durable_epoch = value
            elif kind == "crash":
                # Stable epoch survives; volatile request state is absent after reboot.
                pass
            elif kind == "digits":
                if dropped == "target_sum" or sum(value) == 192:
                    remaining_chain_steps = sum(3-d for d in value)
                    violation = remaining_chain_steps != 192
            elif kind == "limb":
                if dropped == "canonical_limb" or value < P:
                    decoded = value % P
                    violation = decoded.to_bytes(8,"little") != value.to_bytes(8,"little")
            if violation:
                return trace[:turn+1]
        return None

    for _ in range(500):
        trace = []
        for _ in range(rng.randrange(8,25)):
            kind = rng.choice(["ack","quorum","epoch","crash","digits","limb"])
            if kind == "ack": value = [rng.randrange(4) for _ in range(rng.randrange(1,7))]
            elif kind == "quorum":
                n = rng.randrange(2,9); f = rng.randrange((n-1)//3+1)
                q = rng.randrange(1,n-f+1)
                # Preserve the other production quorum constraints (choose t=f+1).
                value = [n,f,q,rng.sample(range(n),q),rng.sample(range(n),q)]
            elif kind == "epoch": value = rng.randrange(12)
            elif kind == "digits": value = [rng.randrange(4) for _ in range(128)]
            elif kind == "limb": value = rng.choice([P-1,P,P+1,2**64-1,rng.getrandbits(64)])
            else: value = None
            trace.append((kind,value))
        assert execute(trace,None) is None, trace
        for guard in guards:
            if guard not in found:
                witness = execute(trace,guard)
                if witness:
                    # Delete irrelevant turns while retaining the actual mutant violation.
                    j = 0
                    while j < len(witness):
                        candidate = witness[:j]+witness[j+1:]
                        if execute(candidate,guard): witness = candidate
                        else: j += 1
                    found[guard] = {"trace":witness,"discovery_ms":(time.perf_counter()-start)*1000}
    assert len(found) == len(guards), found
    return {"witnesses":found, "baseline_schedules":500,
            "elapsed_ms":(time.perf_counter()-start)*1000}


def run(args, rust):
    lean = Oracle(args.oracle_bin)
    counts = Counter()
    mismatches = []
    rng = random.Random(args.seed)
    try:
        for request in requests(rng, args.cases, rust, args.surfaces):
            actual = lean.ask(request)
            expected = rust.ask(request)
            if actual != expected:
                case = {"request":request,"lean":actual,"rust":expected}
                print(json.dumps({"mismatch":case}), flush=True)
                mismatches.append(case)
                key = "\t".join(map(str,request))
                if args.strict_all or KNOWN_MISMATCHES.get(key) != (actual, expected):
                    counts["unexpected_mismatches"] += 1
            else: counts[request[0]] += 1
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
            assert rust.ask(["metamorphic", rng.randbytes(32).hex(), rng.randbytes(rng.randrange(513)).hex()]) == "true"
            counts["metamorphic_all_three_rss"] += 1
            assert rust.ask(["subset", rng.randbytes(32).hex(), rng.randbytes(rng.randrange(513)).hex(), iteration % 3]) == "true"
            counts["metamorphic_two_party_subsets"] += 1
        mutation = mutation_search(rng)
        report = {"seed":args.seed,"selected_surfaces":args.surfaces or "all","passes":dict(counts),"total":sum(v for k,v in counts.items() if k != "unexpected_mismatches"),
                  "mismatches":mismatches,"harness_mutations":mutation,
                  "limitations":["Repository Poseidon2 is width 12, not width 16.",
                    "SHA3 is padding around live Keccak, not a separately exported digest API.",
                    "WAL schedules execute the Lean model; Rust POSIX crash equivalence is not asserted.",
                    "Clause-drop witnesses test harness predicates, not mutated library executables."]}
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
    args = p.parse_args()
    if min(args.cases,args.schedules,args.metamorphic)<0: p.error("counts must be nonnegative")
    if args.strict_all and (args.surfaces or args.cases < 1200 or args.schedules < 500 or args.metamorphic < 50):
        p.error("--strict-all requires every surface and the full default case counts")
    root = Path(__file__).resolve().parents[1]
    if args.rust_bin:
        rust=Oracle(args.rust_bin)
        try: run(args,rust)
        finally: rust.close()
    else:
        # Unique child avoids overwriting or deleting any other run's files.
        driver_root = Path(tempfile.gettempdir()) / "qsag_rust_spec_driver"
        driver_root.mkdir(exist_ok=True)
        try:
            with tempfile.TemporaryDirectory(prefix="run-", dir=driver_root) as tmp:
                binary=build_driver(root,Path(tmp)/"driver")
                rust=Oracle(binary)
                try: run(args,rust)
                finally: rust.close()
        finally:
            try: driver_root.rmdir()  # Only succeeds if empty; preserves concurrent runs.
            except OSError: pass

if __name__ == "__main__":
    main()
