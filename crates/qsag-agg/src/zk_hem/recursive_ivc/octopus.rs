//! Fixed-capacity octopus. At height h there are min(q, 2^(H-h))
//! distinct live nodes. If two queries meet, fill the vacant parent slot
//! with the lowest unused parent. Every filler digest participates in the root.
//! Proof length and switch topology therefore depend only on public geometry.
use super::*;
use alloc::collections::BTreeSet;

fn parents(indices: &[usize], width: usize) -> (Vec<usize>, Vec<usize>) {
    let mut parents: BTreeSet<_> = indices.iter().map(|i| i / 2).collect();
    let need = indices.len().min(width / 2);
    for i in 0..need {
        if parents.len() == need {
            break;
        }
        parents.insert(i);
    }
    let live: BTreeSet<_> = indices.iter().copied().collect();
    let missing = parents
        .iter()
        .flat_map(|p| [2 * p, 2 * p + 1])
        .filter(|i| !live.contains(i))
        .collect();
    (parents.into_iter().collect(), missing)
}

pub(super) fn build(stage: usize, leaves: Vec<Digest>) -> Vec<Vec<Digest>> {
    let mut tree = vec![leaves];
    while tree.last().unwrap().len() > 1 {
        let h = tree.len() - 1;
        let prev = &tree[h];
        let mut next = vec![[F::ZERO; 7]; prev.len() / 2];
        crate::pcs::fill_indexed(&mut next, |i| {
            crate::sponge::poseidon2_gl24_compress_merkle(
                &prev[2 * i],
                &prev[2 * i + 1],
                &[f(stage as u64), f(h as u64)],
            )
        });
        tree.push(next);
    }
    tree
}
pub(super) fn open(tree: &[Vec<Digest>], mut indices: Vec<usize>) -> Vec<Digest> {
    let mut frontier = Vec::new();
    for level in &tree[..tree.len() - 1] {
        let (next, missing) = parents(&indices, level.len());
        frontier.extend(missing.iter().map(|i| level[*i]));
        indices = next;
    }
    frontier
}
pub(super) fn frontier_len(mut width: usize, mut count: usize) -> usize {
    let mut total = 0;
    while width > 1 {
        width /= 2;
        let parents = count.min(width);
        total += 2 * parents - count;
        count = parents;
    }
    total
}

type Packet<W> = [W; 8]; // address and seven digest limbs
fn switch<B: Wide, const N: usize>(
    b: &mut B,
    pair: &[[B::W; N]],
    swap: bool,
) -> ([B::W; N], [B::W; N]) {
    let bit = b.alloc(f(swap as u64));
    b.product(
        &bit,
        &B::W::constant(F::ONE).minus(&bit),
        &B::W::constant(F::ZERO),
    );
    let diff: [B::W; N] = core::array::from_fn(|i| b.mul(&bit, &pair[1][i].minus(&pair[0][i])));
    (
        core::array::from_fn(|i| pair[0][i].plus(&diff[i])),
        core::array::from_fn(|i| pair[1][i].minus(&diff[i])),
    )
}

// Rearrangeable network with an unpaired upper wire at odd widths. The host
// 2-colours the input/output pair graph to supply switch hints. Only Boolean
// switch rows can move packets, and every packet reaches exactly one output.
pub(super) fn route<B: Wide, const N: usize>(
    b: &mut B,
    wires: Vec<[B::W; N]>,
    dest: &[usize],
) -> Vec<[B::W; N]> {
    let n = wires.len();
    if n <= 1 {
        return wires;
    }
    if n == 2 {
        let (a, c) = switch(b, &wires, dest[0] != 0);
        return vec![a, c];
    }
    let mut inv = vec![0; n];
    for (i, &j) in dest.iter().enumerate() {
        inv[j] = i;
    }
    let mut lower = vec![None; n];
    // Unpaired inputs and outputs lie at the two ends of the same even path.
    for start in core::iter::once(n - 1).chain(0..n) {
        if lower[start].is_some() {
            continue;
        }
        lower[start] = Some(false);
        let mut pending = vec![start];
        while let Some(i) = pending.pop() {
            let peer_out = dest[i] ^ 1;
            for j in [i ^ 1, if peer_out < n { inv[peer_out] } else { n }] {
                if j < n && lower[j].is_none() {
                    lower[j] = Some(!lower[i].unwrap());
                    pending.push(j);
                }
            }
        }
    }
    let mut halves = [Vec::new(), Vec::new()];
    let mut positions = [Vec::new(), Vec::new()];
    for (i, pair) in wires.chunks_exact(2).enumerate() {
        let j = 2 * i;
        let swap = lower[j].unwrap();
        let (a, c) = switch(b, pair, swap);
        halves[0].push(a);
        halves[1].push(c);
        positions[0].push(dest[j + usize::from(swap)] / 2);
        positions[1].push(dest[j + usize::from(!swap)] / 2);
    }
    if n % 2 == 1 {
        halves[0].push(wires[n - 1].clone());
        positions[0].push(dest[n - 1] / 2);
    }
    let [hi, lo] = halves;
    let mut hi = route(b, hi, &positions[0]).into_iter();
    let lo = route(b, lo, &positions[1]);
    let mut out = Vec::with_capacity(n);
    for (i, c) in lo.into_iter().enumerate() {
        let (a, c) = switch(b, &[hi.next().unwrap(), c], lower[inv[2 * i]].unwrap());
        out.extend([a, c]);
    }
    out.extend(hi);
    out
}
pub(super) fn verify<B: Wide>(
    b: &mut B,
    stage: usize,
    mut width: usize,
    queries: &[(B::W, Vec<B::W>)],
    hashes: Vec<[B::W; 7]>,
    siblings: &[Digest],
    root: &[B::W; 7],
) {
    let mut addresses: Vec<_> = queries
        .iter()
        .map(|(x, _)| b.value(x).to_canonical_u64() as usize)
        .collect();
    let mut packets: Vec<Packet<B::W>> = queries
        .iter()
        .zip(hashes)
        .map(|((index, _), hash)| {
            core::array::from_fn(|i| {
                if i == 0 {
                    index.clone()
                } else {
                    hash[i - 1].clone()
                }
            })
        })
        .collect();
    let mut siblings = siblings.iter();
    let mut level = 0;
    while width > 1 {
        let (next, missing) = parents(&addresses, width);
        for &i in &missing {
            let hash = siblings
                .next()
                .expect("validated frontier")
                .map(|v| b.alloc(v));
            let index = b.alloc(f(i as u64));
            packets.push(core::array::from_fn(|k| {
                if k == 0 {
                    index.clone()
                } else {
                    hash[k - 1].clone()
                }
            }));
        }
        addresses.extend(missing);
        let dest: Vec<_> = addresses
            .iter()
            .map(|&i| 2 * next.binary_search(&(i / 2)).unwrap() + (i & 1))
            .collect();
        let sorted = if level > 0 && width == queries.len().min(width) {
            packets
        } else {
            route(b, packets, &dest)
        };
        packets = sorted
            .chunks_exact(2)
            .map(|pair| {
                b.equal(&pair[1][0], &pair[0][0].plus(&B::W::constant(F::ONE)));
                let digest = compress(
                    b,
                    stage,
                    level,
                    &core::array::from_fn(|i| pair[0][i + 1].clone()),
                    &core::array::from_fn(|i| pair[1][i + 1].clone()),
                );
                let parent = pair[0][0].scale(F::TWO.inv());
                core::array::from_fn(|i| {
                    if i == 0 {
                        parent.clone()
                    } else {
                        digest[i - 1].clone()
                    }
                })
            })
            .collect();
        addresses = next;
        width /= 2;
        level += 1;
    }
    b.equal(&packets[0][0], &B::W::constant(F::ZERO));
    for (x, y) in packets[0][1..].iter().zip(root) {
        b.equal(x, y);
    }
}
