//! Dealerless threshold few-time key setup with the active consistency check (`qsag-fts`).
//!
//! ```bash
//! cargo run --release -p qsag-cli --example dealerless_dkg_consistency_check
//! ```
//!
//! Three custodians run the commit-open-finalize setup over private channels, then the
//! five-message check (challenge coin, Beaver sacrifice, masked share opening, committed MAC
//! tags) that must pass before any key share is released.
//!
//! 1. An honest ceremony passes and every custodian activates the same public seed.
//! 2. A custodian that reports one wrong additive share in a single pairwise product is caught:
//!    every party's activation fails and no key share is released.
//!
//! The pairwise product backend here is a three-party helper protocol suitable only for a
//! demonstration; deployments supply an oblivious-transfer backend through
//! `ParallelSeededDkgOt` / `ParallelSeededGilboaProducts`.

use std::sync::mpsc::{Receiver, Sender, channel};

use qsag_accel::gf2_128::gf2_128_mul;
use qsag_accel::keccak::cshake256_framed_xof;
use qsag_fts::{
    ParallelSeededDkgConfig, ParallelSeededDkgOutput, ParallelSeededDkgProducts,
    ParallelSeededDkgRound1State, ParallelSeededDkgSharePackage, ParallelSeededDkgUnverifiedOutput,
    ParallelSeededError, ParallelSeededParams, finalize_parallel_seeded_dkg_party,
};

type Packet = ([u8; 32], Vec<u128>);

/// Pairwise products among parties `{0, 1, 2}`: the third party hands the two endpoints a
/// one-time multiplication triple and sees neither operand.
struct HelperProducts {
    id: u16,
    tx: Vec<Option<Sender<Packet>>>,
    rx: Vec<Option<Receiver<Packet>>>,
    entropy: [u8; 32],
    /// Endpoint product in which this party reports a wrong share (`None`: honest).
    cheat_at: Option<usize>,
    endpoint_calls: usize,
}

impl HelperProducts {
    fn send(&self, peer: u16, context: [u8; 32], values: Vec<u128>) {
        let channel = self.tx[peer as usize].as_ref().expect("channel to peer");
        channel.send((context, values)).expect("peer is running");
    }
    fn receive(&self, peer: u16, context: [u8; 32]) -> Vec<u128> {
        let channel = self.rx[peer as usize].as_ref().expect("channel from peer");
        let (got, values) = channel.recv().expect("peer is running");
        assert_eq!(
            got, context,
            "products run in the same public order at every party"
        );
        values
    }
}

impl ParallelSeededDkgProducts for HelperProducts {
    fn party_id(&self) -> u16 {
        self.id
    }

    fn product_shares(
        &mut self,
        context: [u8; 32],
        sender: u16,
        receiver: u16,
        operand: &[u128],
    ) -> Result<Vec<u128>, ParallelSeededError> {
        let helper = 3 - sender - receiver;
        if self.id == helper {
            let count = self.receive(sender, context)[0] as usize;
            let mut raw = vec![0u8; count * 48];
            cshake256_framed_xof(
                b"EXAMPLE.HELPER.TRIPLE",
                &[&self.entropy, &context],
                &mut raw,
            );
            let (mut left, mut right) = (Vec::new(), Vec::new());
            for chunk in raw.as_chunks::<16>().0.as_chunks::<3>().0 {
                let [a, b, r] = chunk.map(u128::from_le_bytes);
                left.extend_from_slice(&[a, r]);
                right.extend_from_slice(&[b, gf2_128_mul(a, b) ^ r]);
            }
            self.send(sender, context, left);
            self.send(receiver, context, right);
            return Ok(Vec::new());
        }
        if self.id == sender {
            self.send(helper, context, vec![operand.len() as u128]);
        }
        let pads = self.receive(helper, context);
        let peer = if self.id == sender { receiver } else { sender };
        let masked = operand
            .iter()
            .zip(pads.as_chunks::<2>().0)
            .map(|(&x, pad)| x ^ pad[0])
            .collect();
        self.send(peer, context, masked);
        let remote = self.receive(peer, context);
        let mut shares: Vec<u128> = operand
            .iter()
            .zip(pads.as_chunks::<2>().0)
            .zip(&remote)
            .map(|((&x, pad), &other)| {
                pad[1] ^ gf2_128_mul(if self.id == sender { x } else { pad[0] }, other)
            })
            .collect();
        if self.cheat_at == Some(self.endpoint_calls) {
            shares[0] ^= 1;
        }
        self.endpoint_calls += 1;
        Ok(shares)
    }
}

fn backends(cheat: Option<(u16, usize)>) -> Vec<HelperProducts> {
    let mut tx: Vec<Vec<Option<Sender<Packet>>>> =
        (0..3).map(|_| (0..3).map(|_| None).collect()).collect();
    let mut rx: Vec<Vec<Option<Receiver<Packet>>>> =
        (0..3).map(|_| (0..3).map(|_| None).collect()).collect();
    for from in 0..3 {
        for to in (0..3).filter(|&to| to != from) {
            let (sender, receiver) = channel();
            tx[from][to] = Some(sender);
            rx[to][from] = Some(receiver);
        }
    }
    tx.into_iter()
        .zip(rx)
        .enumerate()
        .map(|(id, (tx, rx))| HelperProducts {
            id: id as u16,
            tx,
            rx,
            entropy: [id as u8 + 91; 32],
            cheat_at: cheat
                .filter(|(party, _)| *party == id as u16)
                .map(|(_, call)| call),
            endpoint_calls: 0,
        })
        .collect()
}

/// Rounds 1-3 of the setup. Nothing is usable yet: each result still has to pass the check.
fn setup(cheat: Option<(u16, usize)>) -> Vec<ParallelSeededDkgUnverifiedOutput> {
    let config = ParallelSeededDkgConfig {
        params: ParallelSeededParams {
            tree_height: 2,
            winternitz_w: 5,
            num_chains: 68,
            target_sum: 136,
        },
        roster: vec![0, 1, 2],
        session: [51; 32],
        power_count: 4,
        beaver_count: 2,
    };
    let mut states: Vec<_> = (0..3u16)
        .map(|id| {
            ParallelSeededDkgRound1State::begin(config.clone(), id, [id as u8 + 13; 32])
                .expect("valid configuration")
        })
        .collect();
    let commits: Vec<_> = states
        .iter()
        .map(ParallelSeededDkgRound1State::commitment)
        .collect();
    let openings: Vec<_> = states
        .iter_mut()
        .map(|s| s.open(&commits).expect("frozen commitments"))
        .collect();
    let mut inboxes: Vec<Vec<ParallelSeededDkgSharePackage>> = (0..3).map(|_| Vec::new()).collect();
    for state in &mut states {
        for package in state.private_packages().expect("first and only delivery") {
            inboxes[package.recipient as usize].push(package);
        }
    }
    std::thread::scope(|scope| {
        let handles: Vec<_> = states
            .into_iter()
            .zip(inboxes)
            .zip(backends(cheat))
            .map(|((state, packages), mut backend)| {
                let openings = &openings;
                scope.spawn(move || {
                    finalize_parallel_seeded_dkg_party(state, openings, packages, &mut backend)
                        .expect("products complete")
                })
            })
            .collect();
        handles
            .into_iter()
            .map(|h| h.join().expect("custodian thread"))
            .collect()
    })
}

/// The five broadcast messages of the consistency check, then activation at every party.
fn check_and_activate(
    mut pending: Vec<ParallelSeededDkgUnverifiedOutput>,
) -> Vec<Result<ParallelSeededDkgOutput, ParallelSeededError>> {
    let commits: Vec<_> = pending.iter().map(|p| p.check_commitment()).collect();
    let coins: Vec<_> = pending
        .iter_mut()
        .map(|p| p.reveal_check_coin(&commits).expect("coin"))
        .collect();
    let shares: Vec<_> = pending
        .iter_mut()
        .map(|p| p.masked_shares(&coins).expect("shares"))
        .collect();
    let tag_commits: Vec<_> = pending
        .iter_mut()
        .map(|p| p.tag_commitment(&shares).expect("tag"))
        .collect();
    let tags: Vec<_> = pending
        .iter_mut()
        .map(|p| p.open_tags(&tag_commits).expect("open"))
        .collect();
    pending.into_iter().map(|p| p.activate(&tags)).collect()
}

fn main() {
    println!("=== 1. Honest ceremony ===");
    let outputs: Vec<_> = check_and_activate(setup(None))
        .into_iter()
        .map(|result| result.unwrap_or_else(|e| panic!("honest ceremony must activate: {e:?}")))
        .collect();
    assert!(
        outputs
            .iter()
            .all(|o| o.pk_seed_bytes == outputs[0].pk_seed_bytes && o.beaver_triples.len() == 2)
    );
    println!(
        "  [ok] 3 custodians activated shares of one key (public seed {:02x?}..)",
        &outputs[0].pk_seed_bytes[..4]
    );

    println!("\n=== 2. One custodian reports a wrong share in one pairwise product ===");
    // Endpoint products 0..12 build the power tuples, 12..16 the Beaver triples, 16..24 the MACs.
    for (what, call) in [
        ("power tuple", 1),
        ("Beaver triple", 13),
        ("MAC lane 0", 17),
        ("MAC lane 1", 22),
    ] {
        let results = check_and_activate(setup(Some((2, call))));
        assert!(
            results
                .iter()
                .all(|r| matches!(r, Err(ParallelSeededError::BdozMacCheckFailed))),
            "a wrong {what} share must abort every custodian"
        );
        println!("  [ok] wrong {what} share: all 3 activations refused, no key share released");
    }
}
