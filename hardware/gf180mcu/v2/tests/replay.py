"""Replay of the reference script on the v2 model.

Each reference transaction is put in one of four classes:
  verbatim     request words sent unchanged, response compared word for word
  translated   the v2 request format differs (README, "Deliberate differences"); the request is rebuilt
               from the reference request's fields and the expected response is unchanged:
                 CTH      v2 layout, v2 tag, no STATEFUL flag
                 KEYLOAD  preceded by a nonce request and carrying the owner's authorisation
  deferred     verifier-VM opcodes 0x30 / 0x31: not in stage 1; the v2 model must answer E_OPCODE
  absent       configuration S only: Poseidon2 / Merkle opcodes, which need the field unit

Two things the reference script does not have are inserted, and counted:
  - one PROVISION_NONCE request before each key load that the chip will consider;
  - before the first stateful reference transaction, a reset and a second authorised key load of the
    same keys with the counted attribute. In v2 a key is counted or not from provisioning on; the
    reference uses one key both ways.
FRAMCHK directives compare the anchor record with one computed here under the device secret, for the
counter the reference record names (the reference tags records under the host's K_MAC).
"""
from common import DEV, match, new_chip, reference_script, working_rows_clear

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


def translate_cth(req, k_host):
    """Reference CTH request -> v2 CTH request asking for the same values."""
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
    if not _old_tag_valid(k_host, req):
        tag[1] ^= 1 << 17              # the reference request is one the reference chip refuses for its tag
    return new + tag


def replay(config, quick=False):
    """Returns (rows, failures, inserted). rows: dict(name, op, cls, cycles, keccak, field, fram, ok)."""
    chip = new_chip(config)
    keys = None                        # (k_host, sk_seed, sk_prf) once loaded
    counted = False
    saved = None
    rows, failures, inserted = [], [], []

    def record(name, op, cls, got, exp):
        log = chip.log[-1]
        ok = match(got, exp) and not log["key_words_emitted"] and working_rows_clear(chip)
        rows.append(dict(name=name, op=op, cls=cls, ok=ok, cycles=log["cycles"], steps=log["steps"],
                         keccak=log["unit_calls"]["keccak"], field=log["unit_calls"]["field"],
                         fram=log["unit_cycles"]["fram"], auth=log["unit_cycles"]["auth"], words_out=len(got) - 1))
        if not ok:
            failures.append((name, [f"{w:016x}" for w in got], ["-" if w is None else f"{w:016x}" for w in exp]))

    for kind, p in reference_script(quick):
        if kind == "xfer":
            name, tx, rx = p
            op = (tx[0] >> 8) & 0xFF
            flags = (tx[0] >> 16) & 0xFF
            if (tx[0] & 0xFF) != 0x51:
                record(name, op, "verbatim", chip.transact(tx), rx)
            elif op in (0x30, 0x31):
                record(name, op, "deferred", chip.transact(tx), [host.rhdr(op, 0, False, host.E_OPCODE)])
            elif op in (0x10, 0x11) and config == "S":
                record(name, op, "absent", chip.transact(tx), [host.rhdr(op, 0, False, host.E_OPCODE)])
            elif op == host.OP_KEYLOAD:
                k = [host.bytes_of(tx[i:i + 2]) for i in (1, 3, 5)]
                if keys is None:
                    got = host.provision(chip, chip.owner, k[0], k[1], k[2], anchor_init=bool(flags & 2))
                    inserted.append("PROVISION_NONCE before: " + name)
                else:                  # a key is valid: the chip refuses before it looks at any authorisation
                    got = chip.transact(host.keyload_body(k[0], k[1], k[2], anchor_init=bool(flags & 2)) + [0, 0])
                if got == [host.rhdr(op, 0)]:
                    keys, counted = k, False
                record(name, op, "translated", got, rx)
            elif op == host.OP_CTH:
                if flags & 2 and not flags & 1 and keys and not counted:
                    chip.reset()
                    again = host.provision(chip, chip.owner, *keys, anchor_init=False, counted=True)
                    if again != [host.rhdr(host.OP_KEYLOAD, 0)]:
                        failures.append(("inserted counted key load", again, None))
                    counted = True
                    inserted.append("reset, PROVISION_NONCE and counted KEYLOAD before: " + name)
                record(name, op, "translated", chip.transact(translate_cth(tx, keys[0] if keys else None)), rx)
            else:
                record(name, op, "verbatim", chip.transact(tx), rx)
        elif kind == "pin":
            # pins after a transaction the v2 model answers differently (deferred, absent) do not apply
            if rows[-1]["cls"] in ("verbatim", "translated") and chip.pins[p[0]] != p[1]:
                failures.append((f"PIN {p[0]} after {rows[-1]['name']}", chip.pins[p[0]], p[1]))
        elif kind == "framchk":
            slot, rec = p
            want = host.fram_record(DEV, int.from_bytes(rec[:8], "little"))
            have = bytes(chip.fram[32 * slot:32 * slot + 24])
            if have != want:
                failures.append((f"FRAMCHK {slot} after {rows[-1]['name']}", have.hex(), want.hex()))
        elif kind == "framsave":
            saved = bytes(chip.fram)
        elif kind == "framrestore":
            chip.fram[:] = saved
    return rows, failures, inserted
