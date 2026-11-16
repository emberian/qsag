#!/usr/bin/env python3
"""Test script for the full-chip testbench (tb/sim_qsag_ni_180.cpp).

Usage: gen_script.py <fixture.json> <out.txt> [quick]

Each line is a directive:
  # text                 comment (printed)
  TX w0 w1 ...           send a request (64-bit hex words)
  RX w0 w1 ...           expect a response; '-' = word not checked
  PIN name value         expect a status pin (VERIFY_OK, FAULT)
  FRAMCHK slot hex       expect 24 bytes of an anchor record in the FRAM model
  FRAMSAVE / FRAMRESTORE snapshot / roll back the FRAM model (roll-back attack)
All expected values come from model/qsag_ni_model.py (hashlib, the Lean oracle fixture).
"""
import hashlib
import json
import os
import random
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "model"))
import qsag_prims as q  # noqa: E402
import qsag_ni_model as m  # noqa: E402

P = q.P
fx = json.load(open(sys.argv[1]))
quick = len(sys.argv) > 3 and sys.argv[3] == "quick"
rng = random.Random(0x180)
print("model selfcheck:", q.selfcheck(sys.argv[1]))
out = []


def note(s):
    out.append("# " + s)


def xfer(pair, name):
    req, rsp = pair
    note(name)
    out.append("TX " + " ".join(f"{w:016x}" for w in req))
    out.append("RX " + " ".join("-" if w is None else f"{w:016x}" for w in rsp))


def limb():
    return rng.randrange(P)


def e4():
    return [limb() for _ in range(4)]


# ---------------------------------------------------------------- telemetry and plain primitives
xfer(m.ping(), "PING")
for i, e in enumerate(fx["poseidon2_12"][:2 if quick else 4]):
    xfer(m.p2_raw([int(v) for v in e["input"]]), f"Poseidon2-12 permutation, Lean oracle vector {i}")
    assert m.p2_raw([int(v) for v in e["input"]])[1][1:] == [int(v) for v in e["perm"]]
for n in ((0, 7) if quick else (0, 3, 6, 7, 14, 21)):
    xfer(m.p2_hash(limb(), e4(), [limb() for _ in range(n)]), f"poseidon2_sponge_hash_limbs, {n} limbs")
# non-canonical input limbs are reduced (the Lean oracle's a_raw / a_canon edge cases)
edges = [int(e["a_raw"]) for e in fx["goldilocks_edges"]]
xfer(m.p2_hash(q.P2_DOMAIN_FS_ABSORB_LIMBS, e4(), edges), "sponge hash over the Goldilocks edge words")

# Canopy: one node, a valid path, a path against the wrong root
key3 = [limb() for _ in range(3)]
l4, r4 = e4(), e4()
node = q.p2_canopy_node(l4, r4, key3, 1)
xfer(m.merkle(key3, 0, l4, [r4], node), "Canopy node (depth 1, left child)")
xfer(m.merkle(key3, 1, r4, [l4], node), "Canopy node (depth 1, right child)")
depth = 3 if quick else 6
leaf, sibs, idx = e4(), [e4() for _ in range(depth)], rng.randrange(1 << depth)
root = q.p2_canopy_path(leaf, sibs, key3, idx)
xfer(m.merkle(key3, idx, leaf, sibs, root), f"Canopy path depth {depth}, accept")
out.append("PIN VERIFY_OK 1")
bad = list(root)
bad[2] ^= 1
xfer(m.merkle(key3, idx, leaf, sibs, bad), f"Canopy path depth {depth}, root with one flipped bit: reject")
out.append("PIN VERIFY_OK 0")

# Keccak sponge: TurboSHAKE256 (12 rounds), SHAKE256 and a cSHAKE-suffix stream (24 rounds)
msg = bytes(rng.randrange(256) for _ in range(400))
for n in ((0, 9, 136) if quick else (0, 1, 7, 8, 135, 136, 137, 300)):
    xfer(m.keccak(msg[:n], 4, 0x1F, True), f"TurboSHAKE256, {n} bytes")
xfer(m.keccak(b"", 8, 0x1F, True), "TurboSHAKE256 of the empty string (RFC 9861 vector)")
assert m.keccak(b"", 8, 0x1F, True)[1][1] == int.from_bytes(bytes.fromhex("367a329dafea871c"), "little")
for n in ((31,) if quick else (0, 31, 136, 200)):
    req, rsp = m.keccak(msg[:n], 4, 0x1F, False)
    assert m.bytes_of(rsp[1:]) == hashlib.shake_256(msg[:n]).digest(32)
    xfer((req, rsp), f"SHAKE256, {n} bytes (hashlib)")
if not quick:
    xfer(m.keccak(msg[:50], 20, 0x04, False), "24-round sponge, cSHAKE suffix 0x04, 160-byte squeeze")
    xfer(m.keccak(msg[:50], 20, 0x0B, True), "TurboSHAKE256, D = 0x0B, 160-byte squeeze (two rate blocks)")

# framing errors
note("bad magic")
out.append("TX " + f"{0x52 | (m.OP_PING << 8):016x}")
out.append("RX " + f"{m.rhdr(m.OP_PING, 0, False, m.E_MAGIC):016x}")
note("unknown opcode with two payload words (drained)")
out.append("TX " + f"{m.hdr(0x7E, 0, 16):016x} 1111111111111111 2222222222222222")
out.append("RX " + f"{m.rhdr(0x7E, 0, False, m.E_OPCODE):016x}")

# ---------------------------------------------------------------- enclave without a key
dev = m.Device()
f128s = fx["fips205_slh_dsa_shake_128s_hmsg"]
pk_seed = bytes.fromhex(f128s["pk_seed_hex"])
xfer(dev.prf_msg(b"abc"), "PRF_msg without a key: refused")
xfer(dev.cth(0, 0, 1, 0, 2, pk_seed, [1, 2, 3], 4), "Cut-the-Hash without a key: refused")


# ---------------------------------------------------------------- verifier VM programs
POW_BITS = 5


def fold_program(vm, ch=None):
    """One asymmetric duet fold step (qsag_whir_verified::verify_cwyz_duet_fold_step):
    out = odd + (alpha + beta * y0^2) * (even + theta * odd); challenges come from the chip's
    own transcript when a chain value `ch` is live, otherwise they are loaded as proof data."""
    v0, v1 = e4(), e4()
    y0 = limb()
    inv2, inv2y0, y0sq = pow(2, P - 2, P), pow(2 * y0, P - 2, P), y0 * y0 % P
    if ch is None:
        alpha, beta, theta = e4(), e4(), e4()
        vm.load(m.R_B, alpha)
        vm.load(m.R_X, beta)
    else:
        lab = q.pack_bytes_7_limbs(b"WHIR_FOLD_CHAL")
        alpha = q.p2_sponge_hash_limbs(q.P2_DOMAIN_FS_SQUEEZE_EXT4, ch, lab + [0])
        beta = q.p2_sponge_hash_limbs(q.P2_DOMAIN_FS_SQUEEZE_EXT4, ch, lab + [1])
        theta = q.p2_sponge_hash_limbs(q.P2_DOMAIN_FS_SQUEEZE_EXT4, ch, lab + [2])
        vm.squeeze_ext4(m.R_B, b"WHIR_FOLD_CHAL", 0)
        vm.squeeze_ext4(m.R_X, b"WHIR_FOLD_CHAL", 1)
    vm.load(m.R_Y, [y0sq, 0, 0, 0], imm=True)
    vm.emul(m.R_X, m.R_X, m.R_Y)
    vm.eadd(m.R_B, m.R_B, m.R_X)                      # B = gamma = alpha + beta * y0^2
    if ch is None:
        vm.load(m.R_X, theta)
    else:
        vm.squeeze_ext4(m.R_X, b"WHIR_FOLD_CHAL", 2)  # X = theta
    vm.load(m.R_T0, v0)
    vm.load(m.R_Y, v1)
    vm.eadd(m.R_T0, m.R_T0, m.R_Y)                    # T0 = v0 + v1
    vm.esub(m.R_Y, m.R_T0, m.R_Y)                     # Y = v0
    vm.eadd(m.R_Y, m.R_Y, m.R_Y)                      # Y = 2 v0
    vm.esub(m.R_Y, m.R_Y, m.R_T0)                     # Y = v0 - v1
    vm.load(m.R_A, [inv2, 0, 0, 0], imm=True)
    vm.emul(m.R_T0, m.R_T0, m.R_A)                    # even
    vm.load(m.R_A, [inv2y0, 0, 0, 0], imm=True)
    vm.emul(m.R_Y, m.R_Y, m.R_A)                      # odd
    vm.emul(m.R_A, m.R_X, m.R_Y)                      # theta * odd
    vm.eadd(m.R_T0, m.R_T0, m.R_A)                    # mixed
    vm.emul(m.R_T0, m.R_T0, m.R_B)                    # gamma * mixed
    vm.eadd(m.R_T0, m.R_T0, m.R_Y)                    # out
    even = q.ext4_scale(q.ext4_add(v0, v1), inv2)
    odd = q.ext4_scale(q.ext4_sub(v0, v1), inv2y0)
    mixed = q.ext4_add(even, q.ext4_mul(theta, odd))
    gamma = q.ext4_add(alpha, q.ext4_scale(beta, y0sq))
    folded = q.ext4_add(odd, q.ext4_mul(gamma, mixed))
    vm.load(m.R_A, folded)
    vm.assert_eq(m.R_T0, m.R_A)


def hem_program(vm, rounds):
    """A Hem-shaped streamed verification under the real Poseidon2 Fiat-Shamir transcript:
    relation and instance binding, Canopy commitment, proof of work, a query with its Merkle
    opening, a duet fold step, `rounds` quadratic sumcheck rounds and the final claim pin."""
    H = q.p2_sponge_hash_limbs
    pk7 = q.pack_bytes_7_limbs
    rel = pk7(b"QSAG.NI180.DEMO.RELATION/v1") + pk7(bytes(range(9))) + pk7(b"sched") + [POW_BITS]
    vm.hash(m.R_CH, "init", q.P2_DOMAIN_FS_BIND_REL, rel)
    ch = H(q.P2_DOMAIN_FS_BIND_REL, q.FS_INIT_CAP, rel)
    inst = [2] + pk7(b"committee-root-0123456789abcdef") + pk7(b"message")
    vm.hash(m.R_CH, m.R_CH, q.P2_DOMAIN_FS_BIND_INST, inst)   # the statement is part of the program
    ch = H(q.P2_DOMAIN_FS_BIND_INST, ch, inst)

    # Canopy tree of 16 Ext4 leaves
    logn = 4
    key4 = e4()
    leaves = [e4() for _ in range(1 << logn)]
    LEAF = 0x5032434E4C464501
    nodes = {(1 << logn) + i: H(LEAF, key4, v) for i, v in enumerate(leaves)}
    for i in range((1 << logn) - 1, 0, -1):
        nodes[i] = q.p2_canopy_node(nodes[2 * i], nodes[2 * i + 1], key4[:3], i)
    root = nodes[1]
    lab = pk7(b"PCS_ROOT")
    vm.absorb_limbs(b"PCS_ROOT", root + [logn], latch=m.R_B, skip=1)   # B = committed root
    ch = H(q.P2_DOMAIN_FS_ABSORB_LIMBS, ch, lab + root + [logn])

    # proof of work against the chain, then the nonce is absorbed
    nonce = 0
    while H(q.P2_DOMAIN_FS_POW, ch, [nonce & 0xFFFFFFFF, nonce >> 32])[0] & ((1 << POW_BITS) - 1):
        nonce += 1
    vm.hash(m.R_T0, m.R_CH, q.P2_DOMAIN_FS_POW, [], [nonce & 0xFFFFFFFF, nonce >> 32])
    vm.assert_pow(m.R_T0, POW_BITS)
    vm.absorb_limbs(b"PCS_POW_NONCE", [nonce & 0xFFFFFFFF, nonce >> 32])
    ch = H(q.P2_DOMAIN_FS_ABSORB_LIMBS, ch, pk7(b"PCS_POW_NONCE") + [nonce & 0xFFFFFFFF, nonce >> 32])

    # one query: index from the transcript, leaf opened against the committed root
    qlab = pk7(b"WHIR_QUERY") + [0, 0]
    idx = H(q.P2_DOMAIN_FS_SQUEEZE_IDX, ch, qlab)[0] & ((1 << logn) - 1)
    vm.load(m.R_A, key4)
    vm.hash(m.R_X, m.R_A, LEAF, [], leaves[idx])
    vm.hash(m.R_T0, m.R_CH, q.P2_DOMAIN_FS_SQUEEZE_IDX, qlab)
    vm.bind_idx(m.R_T0, 0, logn)
    sibs = [nodes[((1 << logn) + idx) >> lvl ^ 1] for lvl in range(logn)]
    vm.merkle(m.R_A, idx, sibs)
    vm.assert_eq(m.R_X, m.R_B)

    # fold step under transcript challenges
    fold_program(vm, ch)

    # sumcheck: wire [c0, c2], c1 = claim - 2 c0 - c2, claim <- g(r)
    claim = e4()
    vm.absorb_limbs(b"PCS_CLAIMED_EVAL", claim, latch=m.R_A)
    ch = H(q.P2_DOMAIN_FS_ABSORB_LIMBS, ch, pk7(b"PCS_CLAIMED_EVAL") + claim)
    for _ in range(rounds):
        c0, c2 = e4(), e4()
        vm.absorb_limbs(b"PCS_BATCH_SC_C0", c0, latch=m.R_X)
        ch = H(q.P2_DOMAIN_FS_ABSORB_LIMBS, ch, pk7(b"PCS_BATCH_SC_C0") + c0)
        vm.absorb_limbs(b"PCS_BATCH_SC_C2", c2, latch=m.R_Y)
        ch = H(q.P2_DOMAIN_FS_ABSORB_LIMBS, ch, pk7(b"PCS_BATCH_SC_C2") + c2)
        r = H(q.P2_DOMAIN_FS_SQUEEZE_EXT4, ch, pk7(b"PCS_BATCH_SC_CHAL") + [0])
        vm.squeeze_ext4(m.R_B, b"PCS_BATCH_SC_CHAL", 0)
        vm.esub(m.R_T0, m.R_A, m.R_X)
        vm.esub(m.R_T0, m.R_T0, m.R_X)
        vm.esub(m.R_T0, m.R_T0, m.R_Y)       # c1
        vm.emul(m.R_Y, m.R_Y, m.R_B)
        vm.eadd(m.R_Y, m.R_Y, m.R_T0)
        vm.emul(m.R_Y, m.R_Y, m.R_B)
        vm.eadd(m.R_A, m.R_Y, m.R_X)         # claim <- c0 + r (c1 + r c2)
        c1 = q.ext4_sub(q.ext4_sub(claim, q.ext4_add(c0, c0)), c2)
        claim = q.ext4_add(q.ext4_mul(q.ext4_add(q.ext4_mul(c2, r), c1), r), c0)
    vm.load(m.R_Y, claim)                    # terminal claim pinned
    vm.assert_eq(m.R_A, m.R_Y)


def run_vm(dev, op, builder, name):
    vm = m.Hvm(dev, op)
    builder(vm)
    req = vm.request()
    rsp = vm.run(req)
    assert rsp[1] & 1 == 1, (name, hex(rsp[1]))
    xfer((req, rsp), f"{name}: {len(vm.recs)} records, accept")
    out.append("PIN VERIFY_OK 1")
    # flip one bit of the last proof-data word of a LOAD record in the middle of the stream
    pos = [0]

    def mutate(ws):
        cand, i = [], 0
        for hop, a, b, c, data, k in vm.recs:
            if hop in (m.H_LOAD, m.H_HASH) and k < len(data):
                cand.append(i + len(data))
            i += 1 + len(data)
        pos[0] = cand[len(cand) // 2]
        ws[pos[0]] ^= 1 << 9
    req2 = vm.request(mutate)
    rsp2 = vm.run(req2)
    assert rsp2[1] & 1 == 0, name
    xfer((req2, rsp2), f"{name}: proof stream with one flipped bit (word {pos[0]}): reject")
    out.append("PIN VERIFY_OK 0")


run_vm(dev, m.OP_FOLD, lambda vm: fold_program(vm, None), "duet fold step, unkeyed receipt")

# ---------------------------------------------------------------- key load, PRF_msg, signing
sk_seed, sk_prf = bytes.fromhex(f128s["sk_seed_hex"]), bytes.fromhex(f128s["sk_prf_hex"])
k_mac = bytes(rng.randrange(256) for _ in range(16))
xfer(dev.keyload_host(sk_seed, sk_prf, k_mac), "key load (host-provisioned, anchor initialised)")
out.append("FRAMCHK 0 " + dev.fram_record(0).hex())
out.append("FRAMCHK 1 " + dev.fram_record(0).hex())
xfer(dev.keyload_host(sk_seed, sk_prf, k_mac), "second key load: refused")

ctx, msgb = bytes.fromhex(f128s["ctx_hex"]), bytes.fromhex(f128s["msg_hex"])
mprime = bytes([0, len(ctx)]) + ctx + msgb
req, rsp = dev.prf_msg(bytes.fromhex(f128s["opt_rand_hex"]) + mprime)
assert m.bytes_of(rsp[1:]).hex() == f128s["r_rand_hex"], "PRF_msg does not match the FIPS 205 oracle"
xfer((req, rsp), "PRF_msg = FIPS 205 SLH-DSA-SHAKE-128s randomizer R (Lean oracle r_rand)")

fors = [int(v) for v in f128s["fors_indices"]]
req, rsp = dev.cth(0, 0, int(f128s["idx_tree"]), 3, f128s["idx_leaf"], pk_seed, fors[:3 if quick else 14], 12, pubgen=True)
assert m.bytes_of(rsp[1:3]).hex() == f128s["fors_leaf0_hex"], "FORS leaf does not match the FIPS 205 oracle"
xfer((req, rsp), "FORS public leaves (PUBGEN); leaf 0 = Lean oracle fors_leaf0")
xfer(dev.cth(0, 0, int(f128s["idx_tree"]), 3, f128s["idx_leaf"], pk_seed, fors[:2 if quick else 5], 12),
     "FORS secret leaves released under a valid request tag")
digits = [0, 1, 15, 7] if quick else [0, 1, 15, 7, 3, 2]
xfer(dev.cth(0x1234, 3, 0x0123456789AB, 0, 7, pk_seed, digits, 4), "WOTS chain values, stateless, valid tag")
xfer(dev.cth(0x1234, 3, 0x0123456789AB, 0, 7, pk_seed, digits, 4, bad_tag=True), "same request, forged tag: refused")
out.append("PIN FAULT 1")
xfer(dev.cth(0x1234, 3, 0x0123456789AB, 0, 7, pk_seed, digits, 4, tamper_request=True),
     "same tag, one digit changed: refused")
xfer(dev.cth(0, 0, 9, 0, 0, pk_seed, [15, 15], 4, pubgen=True), "WOTS public chain ends (PUBGEN)")

# stateful signing against the FRAM anchor


def framchk():
    for slot in (0, 1):
        out.append(f"FRAMCHK {slot} " + bytes(dev.fram[32 * slot:32 * slot + 24]).hex())


xfer(dev.cth(0, 0, 9, 0, 0, pk_seed, [3, 1], 4, stateful=True), "stateful signature at leaf 0: counter advances first")
framchk()
xfer(dev.cth(0, 0, 9, 0, 0, pk_seed, [2, 2], 4, stateful=True), "leaf 0 again with other digits: refused (reuse)")
xfer(dev.cth(5, 0, 9, 0, 5, pk_seed, [9], 4, stateful=True), "leaf 5 (leaves 1..4 skipped)")
framchk()
out.append("FRAMSAVE")
saved = bytes(dev.fram)
xfer(dev.cth(6, 0, 9, 0, 6, pk_seed, [4], 4, stateful=True), "leaf 6")
framchk()
out.append("FRAMRESTORE")
note("FRAM rolled back to its image before leaf 6")
dev.fram[:] = saved
xfer(dev.cth(7, 0, 9, 0, 7, pk_seed, [4], 4, stateful=True), "leaf 7 after the roll-back: refused, anchor fault")
out.append("PIN FAULT 1")

# ---------------------------------------------------------------- keyed verification receipts
run_vm(dev, m.OP_HEM, lambda vm: hem_program(vm, 2 if quick else 3), "Hem-shaped streamed verification, keyed receipt")
xfer(m.ping(), "PING")
open(sys.argv[2], "w").write("\n".join(out) + "\n")
print("wrote", len(out), "script lines,", sum(len(l.split()) - 1 for l in out if l.startswith("TX")), "request words")
