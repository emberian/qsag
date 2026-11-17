"""Replay of the reference script on the v2 model.

The reference chip takes its signing keys from the host; the v2 chip derives them from its PUF. So the
values of signer transactions cannot be those of the reference model any more. Each reference transaction
is put in one of these classes:
  verbatim     request words sent unchanged, response compared word for word with the reference
  recomputed   signer transactions (CTH, PRF_MSG). CTH is rebuilt in the v2 request format from the
               reference request's fields. Where the reference refuses, the v2 model must refuse with the
               same code; where it serves, the values are compared with the hashlib FIPS 205 reference
               in host.py under the chip's own derived keys
  changed      the reference behaviour no longer exists, and the v2 answer is stated here:
                 KEYLOAD (0x40)                     E_OPCODE: there is no key import
                 CTH after the FRAM was rolled back  served: within a power session the chip does not
                                                    read the FRAM, so there is nothing to detect
  deferred     verifier-VM opcodes 0x30 / 0x31: not implemented; the v2 model must answer E_OPCODE
  absent       configuration S only: Poseidon2 / Merkle opcodes, which need the field unit

Inserted, and counted: at the reference's first key load, a chip that has been enrolled, committed, reset
and booted (uncounted); before the first stateful reference transaction, a second such chip with the
counted policy. In v2 that policy is fixed at COMMIT; the reference uses one key both ways.
A FRAMCHK directive names one anchor slot of the reference and its counter; the v2 slots alternate by
sequence number, not by the reference's rule, so the directive is checked as: an authentic lifecycle record
with that use counter is in the FRAM. (Which slot holds which record: test_commands.CountedKeys.)
"""
from common import match, new_chip, provisioned, reference_script, working_rows_clear

import host
import units

q = units.q
M32 = (1 << 32) - 1


def _old_tag_valid(k, req):
    """Does the reference request carry a valid reference tag (GHASH under K_MAC, masked)?"""
    delta = int.from_bytes(k, "little")
    acc = 0
    for w in req[:9]:
        acc = q.gf128_mul(acc ^ w, delta)
    mask = int.from_bytes(q.turboshake256(k + req[1].to_bytes(8, "little") + b"QSAGNIMK", 16), "little")
    return (req[9] | (req[10] << 64)) == acc ^ mask


def translate_cth(req, k_ref, k_host):
    """Reference CTH request -> v2 CTH request asking for the same positions, tagged under the chip's
    K_host (or not at all before the chip has one)."""
    h, s, flags = req[0], req[1:9], (req[0] >> 16) & 0xFF
    n, sw = (h >> 48) & 0xFF, (h >> 56) & 0x1F
    per_word = 64 // sw
    sym = [(s[5 + i // per_word] >> (sw * (i % per_word))) & ((1 << sw) - 1) for i in range(n)]
    typ = int.from_bytes((s[4] & M32).to_bytes(4, "little"), "big")
    body = [0, 0, 0, 0]
    if typ == 0:
        assert sw == 4
        digits = sym + [0] * (32 - n)
        body[:2] = host.words_of(bytes((digits[2 * k] << 4) | digits[2 * k + 1] for k in range(16)))
    else:
        for i, v in enumerate(sym):
            body[i // 4] |= ((i << sw) | v) << (16 * (i % 4))
    new = [host.hdr(host.OP_CTH, flags & 1, 88, n)] + s[:5] + body
    if k_host is None:
        return new + [0, 0]
    tag = host.request_tag(k_host, new)
    if not _old_tag_valid(k_ref, req):
        tag[1] ^= 1 << 17              # the reference request is one the reference chip refuses for its tag
    return new + tag


def cth_values(req, seed):
    """What FIPS 205 says a v2 CTH request returns under SK.seed = seed: response words."""
    n, pubgen = (req[0] >> 48) & 0xFF, (req[0] >> 16) & 1
    layer = (req[1] >> 32) & 0xFF
    pk = host.bytes_of(req[2:4])
    tree = int.from_bytes(req[4].to_bytes(8, "little"), "big")
    typ = int.from_bytes((req[5] & M32).to_bytes(4, "little"), "big")
    kp = int.from_bytes((req[5] >> 32).to_bytes(4, "little"), "big")
    if typ == 0:
        d = host.wots_digits(host.bytes_of(req[6:8]))
        vals = [host.wots_chain(pk, seed, layer, tree, kp, i, 15 if pubgen else d[i]) for i in range(n)]
    else:
        idx = [(req[6 + i // 4] >> (16 * (i % 4))) & 0xFFFF for i in range(n)]
        vals = [host.fors_leaf(pk, seed, layer, tree, kp, i, bool(pubgen)) for i in idx]
    return [host.rhdr(host.OP_CTH, 16 * n)] + host.words_of(b"".join(vals))


def use_counters(dev):
    """Use counters of the authentic lifecycle records in the two FRAM slots, newest first."""
    recs = []
    for slot in (1, 2):
        w = host.words_of(bytes(dev.chip.fram[128 * slot:128 * slot + 56]))
        if w[5:7] == host.record_tag(dev.k_dev, w[:5]):
            recs.append((w[0] & M32, w[1] & M32))
    return [u for _, u in sorted(recs, reverse=True)]


def replay(config, quick=False):
    """Returns (rows, failures, inserted). rows: dict(name, op, cls, cycles, keccak, field, fram, ok)."""
    import hashlib
    state = dict(chip=new_chip(config), dev=None, k_ref=None, counted=False, saved=None, rolled=False)
    rows, failures, inserted = [], [], []

    def record(name, op, cls, got, exp):
        chip = state["chip"]
        log = chip.log[-1]
        ok = match(got, exp) and not log["key_words_emitted"] and working_rows_clear(chip)
        rows.append(dict(name=name, op=op, cls=cls, ok=ok, cycles=log["cycles"], steps=log["steps"],
                         keccak=log["unit_calls"]["keccak"], field=log["unit_calls"]["field"],
                         fram=log["unit_cycles"]["fram"], words_out=len(got) - 1))
        if not ok:
            failures.append((name, [f"{w:016x}" for w in got], ["-" if w is None else f"{w:016x}" for w in exp]))

    for kind, p in reference_script(quick):
        chip, dev = state["chip"], state["dev"]
        if kind == "xfer":
            name, tx, rx = p
            op = (tx[0] >> 8) & 0xFF
            flags = (tx[0] >> 16) & 0xFF
            refused = bool(rx[0] is not None and rx[0] & 0x800000)
            if (tx[0] & 0xFF) != 0x51:
                record(name, op, "verbatim", chip.transact(tx), rx)
            elif op in (0x30, 0x31):
                record(name, op, "deferred", chip.transact(tx), host.err(op, host.E_OPCODE))
            elif op in (0x10, 0x11) and config == "S":
                record(name, op, "absent", chip.transact(tx), host.err(op, host.E_OPCODE))
            elif op == 0x40:
                if dev is None:
                    state["k_ref"] = host.bytes_of(tx[1:3])
                    state["dev"] = dev = provisioned(config=config)
                    state["chip"] = chip = dev.chip
                    inserted.append("an enrolled, committed and booted chip at: " + name)
                record(name, op, "changed", chip.transact(tx), host.err(op, host.E_OPCODE))
            elif op == host.OP_PRFMSG:
                exp = rx if refused or dev is None else [host.rhdr(op, 16)] + host.words_of(
                    hashlib.shake_256(dev.prf + host.bytes_of(tx[1:])[:(tx[0] >> 24) & 0xFFFFFF]).digest(16))
                record(name, op, "recomputed", chip.transact(tx), exp)
            elif op == host.OP_CTH:
                if flags & 2 and not flags & 1 and dev and not state["counted"]:
                    state["dev"] = dev = provisioned(host.F_COUNTED, config=config)
                    state["chip"] = chip = dev.chip
                    state["counted"] = True
                    inserted.append("a second chip, with the counted policy, at: " + name)
                req = translate_cth(tx, state["k_ref"], dev.k_host if dev else None)
                if refused and rx[0] >> 48 == 7 and state["rolled"]:        # the reference's roll-back refusal
                    record(name, op, "changed", chip.transact(req), cth_values(req, dev.seed))
                else:
                    record(name, op, "recomputed", chip.transact(req), rx if refused else cth_values(req, dev.seed))
            else:
                record(name, op, "verbatim", chip.transact(tx), rx)
        elif kind == "pin":
            # pins after a transaction the v2 model answers differently do not apply
            if rows[-1]["cls"] in ("verbatim", "recomputed") and chip.pins[p[0]] != p[1]:
                failures.append((f"PIN {p[0]} after {rows[-1]['name']}", chip.pins[p[0]], p[1]))
        elif kind == "framchk":
            slot, rec = p
            want = int.from_bytes(rec[:8], "little")
            have = use_counters(dev)
            if rows[-1]["cls"] == "recomputed" and want not in have:
                failures.append((f"FRAMCHK after {rows[-1]['name']}", have, want))
        elif kind == "framsave":
            state["saved"] = bytes(chip.fram)
        elif kind == "framrestore":
            chip.fram[:] = state["saved"]
            state["rolled"] = True
    return rows, failures, inserted
