//! Wall-clock latency and wire bytes of the isolated party nodes, one OS thread per party.
//!
//! Every party is its own value on its own thread and reaches its peers only through a
//! [`WireTransport`]: an in-process channel mesh or a loopback TCP mesh. A measured latency
//! is the time from a common start barrier until the slowest party has finished; the byte
//! counts are the frames the parties put on the wire, headers included.
//!
//! Run with `cargo run -p qsag-quorum --release --features std --example quorum_threaded_bench`.

use std::sync::{Arc, Barrier};
use std::time::{Duration, Instant};

use qsag_core::belt_latch::MemoryWal;
use qsag_quorum::hash::SeedRng;
use qsag_quorum::party_node::{
    IsolatedJortsParty, IsolatedQuorumParty, IsolatedRss256Party, MemoryPoisonJournal, ROUND_GATE,
    ROUND_OPEN, deal_keccak_shares, deal_rss256_keys,
};
use qsag_quorum::quorum_jorts::{
    CommitteeCustodian, CommitteePartitionedJorts, LeafRecord, QuorumConfig, ShamirCustodian,
    quorum_jorts_verify, stage_bft_shamir, stage_committee_partitioned,
};
use qsag_quorum::wire_channel::{InMemoryWireMesh, MeshStats, TcpWireMesh, WireTransport};

const SEED: [u8; 32] = [0x42; 32];
const SESSION: [u8; 32] = [0x17; 32];
const SIGNATURES: usize = 20;

fn median(mut samples: Vec<Duration>) -> Duration {
    samples.sort();
    samples[samples.len() / 2]
}

fn micros(d: Duration) -> f64 {
    d.as_secs_f64() * 1e6
}

/// Run `rounds` synchronised rounds of `step` on one thread per party. Returns, per round,
/// the time until the slowest party finished.
fn timed_rounds<P: Send>(
    parties: Vec<P>,
    rounds: usize,
    step: impl Fn(&mut P, usize) + Sync,
) -> Vec<Duration> {
    let start = Barrier::new(parties.len());
    let per_party: Vec<Vec<Duration>> = std::thread::scope(|scope| {
        let handles: Vec<_> = parties
            .into_iter()
            .map(|mut party| {
                let (start, step) = (&start, &step);
                scope.spawn(move || {
                    (0..rounds)
                        .map(|round| {
                            start.wait();
                            let begin = Instant::now();
                            step(&mut party, round);
                            begin.elapsed()
                        })
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().expect("party thread"))
            .collect()
    });
    (0..rounds)
        .map(|r| per_party.iter().map(|p| p[r]).max().expect("parties"))
        .collect()
}

fn committee_bench<T: WireTransport + Send>(
    label: &str,
    t: usize,
    n: usize,
    height: u8,
    members: &[usize],
    endpoints: Vec<T>,
    stats: &Arc<MeshStats>,
) {
    let staged = stage_committee_partitioned(t, n, height, &SEED).expect("staging");
    let pk = *staged.tree.public_key();
    let committee = staged.layout.committee_index(members).expect("committee");
    let nodes: Vec<_> = endpoints
        .into_iter()
        .zip(staged.parties)
        .filter(|(_, material)| members.contains(&material.party))
        .map(|(endpoint, material)| {
            let wals = vec![MemoryWal::new(); material.stores.len()];
            let custodian =
                CommitteeCustodian::new(staged.layout.clone(), staged.tree.clone(), material, wals)
                    .expect("custodian");
            IsolatedJortsParty::new(custodian, endpoint).expect("node")
        })
        .collect();
    let share_bytes = nodes[0].custodian().share_bytes();
    stats.reset();
    let times = timed_rounds(nodes, SIGNATURES, |node, round| {
        let msg = [round as u8; 8];
        let sig = node.sign(committee, round as u64, &msg).expect("signature");
        assert!(quorum_jorts_verify(&pk, &msg, &sig));
    });
    println!(
        "  {label:<34} {:>2} threads  median {:>9.1} us  min {:>9.1} us  wire {:>7} B/sig  {:>4} frames/sig  store {:>8} B/custodian",
        members.len(),
        micros(median(times.clone())),
        micros(*times.iter().min().expect("samples")),
        stats.total_bytes() / SIGNATURES as u64,
        stats.total_frames() / SIGNATURES,
        share_bytes,
    );
}

fn shamir_bench<T: WireTransport + Send>(
    label: &str,
    cfg: QuorumConfig,
    online: &[usize],
    endpoints: Vec<T>,
    stats: &Arc<MeshStats>,
) {
    let staged = stage_bft_shamir(cfg, 5, &SEED).expect("staging");
    let pk = *staged.tree.public_key();
    let mut openers = online.to_vec();
    openers.truncate(cfg.threshold());
    let nodes: Vec<_> = endpoints
        .into_iter()
        .zip(staged.parties)
        .filter(|(_, material)| online.contains(&material.party))
        .map(|(endpoint, material)| {
            let custodian =
                ShamirCustodian::new(cfg, staged.tree.clone(), material, MemoryWal::new())
                    .expect("custodian");
            IsolatedQuorumParty::new(custodian, endpoint).expect("node")
        })
        .collect();
    let share_bytes = nodes[0].custodian().share_bytes();
    stats.reset();
    let times = timed_rounds(nodes, SIGNATURES, |node, round| {
        let msg = [round as u8; 8];
        let outcome = node
            .sign(online, &openers, round as u64, &msg)
            .expect("signature");
        assert!(quorum_jorts_verify(&pk, &msg, &outcome.signature));
        assert!(outcome.blamed.is_empty());
    });
    println!(
        "  {label:<34} {:>2} threads  median {:>9.1} us  min {:>9.1} us  wire {:>7} B/sig  {:>4} frames/sig  store {:>8} B/custodian",
        online.len(),
        micros(median(times.clone())),
        micros(*times.iter().min().expect("samples")),
        stats.total_bytes() / SIGNATURES as u64,
        stats.total_frames() / SIGNATURES,
        share_bytes,
    );
}

fn rss_bench<T: WireTransport + Send>(
    label: &str,
    states: usize,
    endpoints: Vec<T>,
    stats: &Arc<MeshStats>,
) {
    let keys = deal_rss256_keys(&SEED);
    let mut rng = SeedRng::new(&SEED, b"bench shares");
    let secrets: Vec<[u64; 25]> = (0..states)
        .map(|s| {
            core::array::from_fn(|i| (s as u64 + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ i as u64)
        })
        .collect();
    let shares: Vec<_> = secrets
        .iter()
        .map(|s| deal_keccak_shares(s, &mut rng))
        .collect();
    let parties: Vec<_> = endpoints
        .into_iter()
        .zip(keys)
        .map(|(endpoint, keys)| {
            let p = keys.party;
            let mut party =
                IsolatedRss256Party::new(SESSION, keys, endpoint, MemoryPoisonJournal::new())
                    .expect("party");
            for share in &shares {
                party.load_shares(share[p].clone());
            }
            party
        })
        .collect();
    let mut reference = secrets.clone();
    qsag_asm::keccak_f1600_batch(&mut reference);
    stats.reset();
    // Three synchronised phases: the wave, the barrier, the opening of a 32-byte digest.
    let times = timed_rounds(parties, 3, |party, phase| match phase {
        0 => party.permute().expect("wave"),
        1 => party.check().expect("barrier"),
        _ => {
            let opened = party.open_prefix(4).expect("opening");
            for (got, want) in opened.iter().zip(&reference) {
                assert_eq!(got[..], want[..4]);
            }
        }
    });
    let frames = stats.frames();
    let class = |pick: &dyn Fn(u32) -> bool| -> u64 {
        frames
            .iter()
            .filter(|f| pick(f.round_tag))
            .map(|f| f.wire_bytes as u64)
            .sum()
    };
    let gate = class(&|tag| tag & 0xFF00_0000 == ROUND_GATE);
    let open = class(&|tag| tag == ROUND_OPEN);
    let barrier = stats.total_bytes() - gate - open;
    println!(
        "  {label:<26} {states} state(s), {:>6} AND gates: wave {:>9.1} us ({:>7} B)  barrier {:>10.1} us ({:>7} B)  open {:>7.1} us ({:>5} B)  frames {}",
        states * 24 * 1600,
        micros(times[0]),
        gate,
        micros(times[1]),
        barrier,
        micros(times[2]),
        open,
        frames.len(),
    );
}

/// Single-thread cost of the public parts: counter grinding and signature verification.
fn primitives() {
    let mut jorts = CommitteePartitionedJorts::stage(2, 3, 7, &SEED).expect("staging");
    let pk = *jorts.public_key();
    const SAMPLES: u32 = 2000;
    let begin = Instant::now();
    let mut tries = 0u64;
    let mut worst = 0u32;
    for i in 0..SAMPLES {
        let record = LeafRecord::derive(&pk, 0, &i.to_be_bytes()).expect("grind");
        tries += u64::from(record.counter) + 1;
        worst = worst.max(record.counter + 1);
    }
    let grind = begin.elapsed() / SAMPLES;
    let sig = jorts.sign(&[0, 1], b"primitive").expect("signature");
    let begin = Instant::now();
    for _ in 0..200 {
        assert!(quorum_jorts_verify(&pk, b"primitive", &sig));
    }
    let verify = begin.elapsed() / 200;
    println!(
        "\nWOTS+C (w = 4, 128 chains, digit sum 192), single thread:\n  grind: mean {:.1} counters, worst {} of {} messages, {:.1} us per message (message hash included)\n  verify: {:.1} us, signature {} B at height {}",
        tries as f64 / f64::from(SAMPLES),
        worst,
        SAMPLES,
        micros(grind),
        micros(verify),
        sig.wire_bytes(),
        pk.height,
    );
}

fn main() {
    println!(
        "quorum_threaded_bench: one OS thread per party, {} hardware threads available",
        std::thread::available_parallelism().map_or(0, usize::from)
    );

    primitives();

    println!("\nMode QS-A, committee-partitioned t-of-t ({SIGNATURES} signatures each):");
    let (endpoints, stats) = InMemoryWireMesh::connect(3, SESSION);
    committee_bench("2-of-3, channel mesh", 2, 3, 7, &[0, 2], endpoints, &stats);
    let (endpoints, stats) = InMemoryWireMesh::connect(5, SESSION);
    committee_bench(
        "3-of-5, channel mesh",
        3,
        5,
        8,
        &[0, 2, 4],
        endpoints,
        &stats,
    );
    let (endpoints, stats) = InMemoryWireMesh::connect(7, SESSION);
    committee_bench(
        "4-of-7, channel mesh",
        4,
        7,
        10,
        &[1, 2, 4, 6],
        endpoints,
        &stats,
    );
    let (endpoints, stats) = TcpWireMesh::loopback(5, SESSION).expect("loopback mesh");
    committee_bench(
        "3-of-5, loopback TCP",
        3,
        5,
        8,
        &[0, 2, 4],
        endpoints,
        &stats,
    );

    println!("\nMode QS-B, certified (t, n) Shamir ({SIGNATURES} signatures each):");
    let cfg = QuorumConfig::new(2, 4, 1).expect("config");
    let (endpoints, stats) = InMemoryWireMesh::connect(4, SESSION);
    shamir_bench(
        "(2,4,f=1) q=3, 3 online, channel",
        cfg,
        &[0, 1, 3],
        endpoints,
        &stats,
    );
    let cfg = QuorumConfig::new(3, 7, 2).expect("config");
    let (endpoints, stats) = InMemoryWireMesh::connect(7, SESSION);
    shamir_bench(
        "(3,7,f=2) q=5, 5 online, channel",
        cfg,
        &[0, 1, 3, 4, 6],
        endpoints,
        &stats,
    );
    let (endpoints, stats) = InMemoryWireMesh::connect(7, SESSION);
    shamir_bench(
        "(3,7,f=2) q=5, 7 online, channel",
        cfg,
        &[0, 1, 2, 3, 4, 5, 6],
        endpoints,
        &stats,
    );
    let (endpoints, stats) = TcpWireMesh::loopback(7, SESSION).expect("loopback mesh");
    shamir_bench(
        "(3,7,f=2) q=5, 5 online, TCP",
        cfg,
        &[0, 1, 3, 4, 6],
        endpoints,
        &stats,
    );
    let cfg = QuorumConfig::new(4, 10, 3).expect("config");
    let (endpoints, stats) = InMemoryWireMesh::connect(10, SESSION);
    shamir_bench(
        "(4,10,f=3) q=7, 7 online, channel",
        cfg,
        &[0, 1, 2, 4, 5, 7, 9],
        endpoints,
        &stats,
    );

    println!("\nReplicated Keccak-f[1600] engine, 3 threads (wave, barrier, 32-byte opening):");
    for states in [1usize, 4, 16] {
        let (endpoints, stats) = InMemoryWireMesh::connect(3, SESSION);
        rss_bench("channel mesh", states, endpoints, &stats);
    }
    let (endpoints, stats) = TcpWireMesh::loopback(3, SESSION).expect("loopback mesh");
    rss_bench("loopback TCP", 1, endpoints, &stats);
}
