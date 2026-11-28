//! Two-party correlated-seed expansion for experimental preprocessing.
//!
//! In R = F_p[X]/(X^N - 1), choose four independent sparse polynomials s,e,t,f
//! and a public uniform a. The two masks are U = as+e and V = at+f. The third
//! polynomial is a²(st) + a(sf+et) + ef. Evaluation on the N roots of unity
//! turns this convolution into componentwise triples. Each point function
//! shares three coordinates: its coefficient and both global MACs on it.
//! This is the fully split univariate Ring-LPN specialization of the sparse
//! product expansion in Li et al., ePrint 2025/1223, §§3,5–6.
//!
//! Setup here knows all masks and keys. The experimental feature supports
//! testing the local expander and its consumer with dealer-generated keys.
//! Deployment needs maliciously secure distributed point-function key setup
//! and concrete Ring-LPN parameters for this field and quotient.
use super::engine::{Preprocessing, Sb};
use alloc::{vec, vec::Vec};
use qsag_agg::field::{Goldilocks as F, ntt_goldilocks};
use qsag_agg::sponge::cshake256_into;
use qsag_core::preprocessing::PartyPrivateRng;
use qsag_core::wipe::{SecretBuffer, SecretWipe};

#[derive(Clone, Copy)]
struct Node {
    seed: [u8; 32],
    bit: u8,
}
impl SecretWipe for Node {
    fn secret_wipe(&mut self) {
        qsag_asm::volatile_fill(
            core::slice::from_mut(self),
            Self {
                seed: [0; 32],
                bit: 0,
            },
        );
    }
}
impl Node {
    fn children(self) -> [Self; 2] {
        let mut raw = SecretBuffer::new([0; 66]);
        cshake256_into(b"QSAG.RLPN.DPF.EXPAND.V1", &self.seed, &mut raw[..]);
        core::array::from_fn(|i| Self {
            seed: raw[32 * i..32 * i + 32].try_into().unwrap(),
            bit: raw[64 + i] & 1,
        })
    }
    fn select(nodes: [Self; 2], index: u8) -> Self {
        let mask = 0u8.wrapping_sub(index);
        Self {
            seed: core::array::from_fn(|j| {
                nodes[0].seed[j] ^ ((nodes[0].seed[j] ^ nodes[1].seed[j]) & mask)
            }),
            bit: nodes[0].bit ^ ((nodes[0].bit ^ nodes[1].bit) & mask),
        }
    }
    fn value(self) -> Sb {
        let mut raw = SecretBuffer::new([0; 72]);
        cshake256_into(b"QSAG.RLPN.DPF.LEAF.V1", &self.seed, &mut raw[..]);
        let w = |i: usize| F::from_bytes24_unbiased(&raw.as_chunks::<24>().0[i]);
        Sb {
            v: w(0),
            m: [w(1), w(2)],
        }
    }
}
#[derive(Clone, Copy)]
struct Correction {
    seed: [u8; 32],
    bits: [u8; 2],
}
impl SecretWipe for Correction {
    fn secret_wipe(&mut self) {
        self.seed.secret_wipe();
        self.bits.secret_wipe();
    }
}
impl Correction {
    fn apply(self, mut child: Node, ctrl: u8, edge_bit: u8) -> Node {
        let mask = 0u8.wrapping_sub(ctrl);
        for (s, c) in child.seed.iter_mut().zip(self.seed) {
            *s ^= c & mask;
        }
        child.bit ^= ctrl & edge_bit;
        child
    }
}

/// One key of the two-party binary-tree DPF. Off the selected path both
/// parties reach identical nodes. On the path their control bits differ.
struct PointKey {
    root: SecretBuffer<Node>,
    path: SecretBuffer<Vec<Correction>>,
    leaf: SecretBuffer<Sb>,
}
impl PointKey {
    fn generate(rng: &mut PartyPrivateRng, depth: u32, index: usize, value: Sb) -> [Self; 2] {
        let roots = SecretBuffer::new(core::array::from_fn::<_, 2, _>(|i| Node {
            seed: rng.next_bytes32(),
            bit: i as u8,
        }));
        let mut current = SecretBuffer::new(*roots);
        let mut path = SecretBuffer::new(Vec::with_capacity(depth as usize));
        for level in (0..depth).rev() {
            let keep = ((index >> level) & 1) as u8;
            let children = SecretBuffer::new(current.map(Node::children));
            let [left, right] = children.map(|pair| Node::select(pair, 1 ^ keep));
            let correction = Correction {
                seed: core::array::from_fn(|j| left.seed[j] ^ right.seed[j]),
                bits: core::array::from_fn(|j| {
                    children[0][j].bit ^ children[1][j].bit ^ (1 ^ keep ^ j as u8)
                }),
            };
            let edge_bit = correction.bits[0]
                ^ ((correction.bits[0] ^ correction.bits[1]) & 0u8.wrapping_sub(keep));
            for i in 0..2 {
                current[i] =
                    correction.apply(Node::select(children[i], keep), current[i].bit, edge_bit);
            }
            path.push(correction);
        }
        let sign = F::from_u64_reduced(current[0].bit as u64) * F::TWO - F::ONE;
        let leaf = (value - current[0].value() + current[1].value()).scale(sign);
        core::array::from_fn(|i| Self {
            root: SecretBuffer::new(roots[i]),
            path: SecretBuffer::new(path.to_vec()),
            leaf: SecretBuffer::new(leaf),
        })
    }

    fn add_to(&self, party: usize, out: &mut [Sb]) {
        // Depth-first traversal uses logarithmic temporary space.
        fn visit(node: Node, path: &[Correction], last: Sb, sign: F, out: &mut [Sb]) {
            if let Some((cw, rest)) = path.split_first() {
                let children = SecretBuffer::new(node.children());
                let (left, right) = out.split_at_mut(out.len() / 2);
                for (i, part) in [left, right].into_iter().enumerate() {
                    visit(
                        cw.apply(children[i], node.bit, cw.bits[i]),
                        rest,
                        last,
                        sign,
                        part,
                    );
                }
            } else {
                let value = node.value() + last.scale(F::from_u64_reduced(node.bit as u64));
                out[0] += value.scale(sign);
            }
        }
        visit(
            *self.root,
            &self.path,
            *self.leaf,
            if party == 0 { F::ONE } else { F::ZERO - F::ONE },
            out,
        );
    }
}

#[derive(Clone, Copy)]
struct Term {
    power: usize,
    coefficient: F,
}
impl SecretWipe for Term {
    fn secret_wipe(&mut self) {
        qsag_asm::volatile_fill(
            core::slice::from_mut(self),
            Self {
                power: 0,
                coefficient: F::ZERO,
            },
        );
    }
}
fn uniform(rng: &mut PartyPrivateRng) -> F {
    loop {
        if let Ok(x) = F::from_canonical(rng.next_u64()) {
            return x;
        }
    }
}
fn sparse(rng: &mut PartyPrivateRng, n: usize, weight: usize) -> SecretBuffer<Vec<Term>> {
    let mut out = SecretBuffer::new(Vec::<Term>::with_capacity(weight));
    while out.len() < weight {
        let power = rng.next_u64() as usize & (n - 1);
        let coefficient = uniform(rng);
        if coefficient != F::ZERO && !out.iter().any(|t| t.power == power) {
            out.push(Term { power, coefficient });
        }
    }
    out
}

/// One party's one-use seed, with the public matrix seed and its two MAC-key shares.
pub struct TripleSeed {
    party: usize,
    n: usize,
    public: [u8; 32],
    key: SecretBuffer<[F; 2]>,
    polynomials: [Vec<PointKey>; 7],
}

impl TripleSeed {
    /// Expand locally with no peer messages. The resulting tape uses the
    /// ordinary engine's burn and MAC checks. No random-value tape is allocated.
    pub fn expand(self) -> Preprocessing {
        let mut public = PartyPrivateRng::from_seed(self.public, b"QSAG.RLPN.PUBLIC.NTT.V1");
        // A uniform vector in evaluation form is uniform in R by the CRT.
        let a: Vec<_> = (0..self.n).map(|_| uniform(&mut public)).collect();
        let mut triples = SecretBuffer::new(vec![[Sb::ZERO; 3]; self.n]);
        for (k, points) in self.polynomials.iter().enumerate() {
            let mut coefficients = SecretBuffer::new(vec![Sb::ZERO; self.n]);
            for point in points {
                point.add_to(self.party, &mut coefficients);
            }
            let output = match k {
                0 | 1 => 0,
                2 | 3 => 1,
                _ => 2,
            };
            // s,e,t,f,st,sf+et,ef respectively carry factors a,1,a,1,a²,a,1.
            for coord in 0..3 {
                let mut values = SecretBuffer::new(
                    coefficients
                        .iter()
                        .map(|x| if coord == 0 { x.v } else { x.m[coord - 1] })
                        .collect::<Vec<_>>(),
                );
                ntt_goldilocks(&mut values);
                for ((triple, &x), &a) in triples.iter_mut().zip(values.iter()).zip(&a) {
                    let v = match k {
                        0 | 2 | 5 => a * x,
                        4 => a * a * x,
                        _ => x,
                    };
                    let share = &mut triple[output];
                    if coord == 0 {
                        share.v += v;
                    } else {
                        share.m[coord - 1] += v;
                    }
                }
            }
        }
        Preprocessing {
            key: *self.key,
            triples: triples.into_inner(),
            randoms: Vec::new(),
        }
    }
}

/// Trusted experimental key generation. Both returned seeds belong to different
/// custodians. Each one expands N triples from 4t + 4t² binary point keys of
/// depth log₂ N. Parameters here specify algebraic dimensions only.
pub fn dealer_seeds(
    rng: &mut PartyPrivateRng,
    log_n: u32,
    weight: usize,
) -> Option<[TripleSeed; 2]> {
    let key_shares = SecretBuffer::new(core::array::from_fn::<_, 2, _>(|_| {
        [uniform(rng), uniform(rng)]
    }));
    dealer_seeds_for_keys(rng, log_n, weight, &key_shares)
}

fn dealer_seeds_for_keys(
    rng: &mut PartyPrivateRng,
    log_n: u32,
    weight: usize,
    key_shares: &[[F; 2]; 2],
) -> Option<[TripleSeed; 2]> {
    let n = 1usize.checked_shl(log_n)?;
    if log_n > 32 || weight == 0 || weight > n {
        return None;
    }
    weight
        .checked_mul(weight)?
        .checked_mul(4)?
        .checked_add(weight.checked_mul(4)?)?;
    let alpha = SecretBuffer::new(core::array::from_fn::<_, 2, _>(|j| {
        key_shares[0][j] + key_shares[1][j]
    }));
    let [s, e, t, f] = core::array::from_fn(|_| sparse(rng, n, weight));
    let public = rng.next_bytes32();
    let mut seeds = core::array::from_fn::<_, 2, _>(|party| TripleSeed {
        party,
        n,
        public,
        key: SecretBuffer::new(key_shares[party]),
        polynomials: core::array::from_fn(|_| Vec::new()),
    });
    let mut point = |k: usize, power: usize, v: F| {
        let mac = Sb {
            v,
            m: alpha.map(|a| a * v),
        };
        let keys = PointKey::generate(rng, log_n, power, mac);
        for (seed, key) in seeds.iter_mut().zip(keys) {
            seed.polynomials[k].push(key);
        }
    };
    for (k, support) in [&s, &e, &t, &f].into_iter().enumerate() {
        for term in support.iter() {
            point(k, term.power, term.coefficient);
        }
    }
    for (k, lhs, rhs) in [(4, &s, &t), (5, &s, &f), (5, &e, &t), (6, &e, &f)] {
        for l in lhs.iter() {
            for r in rhs.iter() {
                point(
                    k,
                    l.power.wrapping_add(r.power) & (n - 1),
                    l.coefficient * r.coefficient,
                );
            }
        }
    }
    Some(seeds)
}

#[cfg(test)]
mod tests {
    use super::super::engine::tests::run_parties;
    use super::*;
    use qsag_agg::zk_hem::v2::field5::Fp5;
    #[test]
    fn collab_ring_lpn_point_shares_match_at_every_leaf() {
        let mut rng = PartyPrivateRng::from_seed([73; 32], b"QSAG.TEST.DPF");
        let v = Sb {
            v: F::ONE,
            m: [F::TWO, F::ZERO - F::ONE],
        };
        for i in 0..16 {
            let keys = PointKey::generate(&mut rng, 4, i, v);
            let mut out = [Sb::ZERO; 16];
            for (party, key) in keys.iter().enumerate() {
                key.add_to(party, &mut out);
            }
            for (j, x) in out.into_iter().enumerate() {
                assert_eq!(x, if i == j { v } else { Sb::ZERO });
            }
        }
    }

    #[test]
    fn collab_ring_lpn_split_proof_consumes_expanded_tape() {
        use super::super::{
            engine::Dealer,
            prover::{prove_party, prover_demand, tests::small_relation},
        };
        use qsag_agg::zk_hem::v2::{params::Profile, protocol::verify_split};
        let (shape, z) = small_relation(5);
        let profile = Profile::default();
        let (triples, randoms) = prover_demand(&shape, profile).unwrap();
        let mut dealer = Dealer::new(2, &[59; 32]);
        let mut tapes = dealer.preprocessing(0, randoms);
        let inputs: Vec<_> = z.iter().map(|&v| dealer.share(v)).collect();
        let mut rng = PartyPrivateRng::from_seed([74; 32], b"QSAG.TEST.RLPN.SPLIT");
        let log = triples.next_power_of_two().ilog2();
        let start = std::time::Instant::now();
        let seeds = dealer_seeds_for_keys(&mut rng, log, 3, &[tapes[0].key, tapes[1].key]).unwrap();
        for (seed, tape) in seeds.into_iter().zip(&mut tapes) {
            let mut expanded = seed.expand();
            tape.triples = core::mem::take(&mut expanded.triples);
        }
        let prep = start.elapsed();
        let begin = std::time::Instant::now();
        let publics = &z[1..=shape.num_public];
        let out = run_parties(tapes, |mut e| {
            let me = e.me();
            let share = inputs.iter().map(|s| s[me]).collect();
            let proof = prove_party(&mut e, &shape, publics, b"RLPN test", profile, share).unwrap();
            assert_eq!(e.stats.triples_used, triples as u64);
            (proof, e.stats.bytes_sent)
        });
        let elapsed = begin.elapsed();
        assert_eq!(out[0].0, out[1].0);
        assert!(verify_split(
            &shape,
            publics,
            b"RLPN test",
            profile,
            &out[0].0
        ));
        std::println!(
            "two custodians, {triples} triples used, experiment setup and expansion {prep:?}, online {elapsed:?}, {} payload bytes",
            out[0].1 + out[1].1
        );
    }

    #[test]
    fn collab_ring_lpn_triples_authenticate_and_feed_quintic_products() {
        let mut rng = PartyPrivateRng::from_seed([91; 32], b"QSAG.TEST.RLPN");
        let [left, right] = dealer_seeds(&mut rng, 5, 3)
            .unwrap()
            .map(TripleSeed::expand);
        let alpha = core::array::from_fn::<_, 2, _>(|j| left.key[j] + right.key[j]);
        for (l, r) in left.triples.iter().zip(&right.triples) {
            let triple = core::array::from_fn::<_, 3, _>(|j| l[j] + r[j]);
            assert_eq!(triple[2].v, triple[0].v * triple[1].v);
            for x in triple {
                assert_eq!(x.m, alpha.map(|a| a * x.v));
            }
        }
        let x = Fp5(core::array::from_fn(|j| F::from_u64_reduced(11 + j as u64)));
        let all = run_parties(vec![left, right], |mut e| {
            let product = e.mul_ext(&[e.public_ext(x)], &[e.public_ext(x)]).unwrap();
            assert_eq!(e.stats.triples_used, 9);
            let opened = e.open_ext(&product).unwrap();
            e.check().unwrap();
            opened[0]
        });
        assert_eq!(all, vec![x * x; 2]);
    }
}
