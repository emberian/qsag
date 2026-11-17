#!/usr/bin/env python3
"""Record what the model does, for replay on the RTL.

    python3 record.py [--scratch N] [--propose name,...] <outdir> <scenario> [...]

Scenarios:  script   the 54-transaction reference script, configuration S (tests/replay.py)
            quick    the quick reference script
            tests    every unittest under v2/tests (132 tests; configuration L chips are skipped)
            extra    directed cases of this lane (KEYWR out of range after a valid authorisation; capacity
                     lane of a keyed state on a releasing path)
            gaps     cases where the RTL needs a clock the model does not count (not part of the gate)
            long     long signer runs on configuration S (35-chain WOTS public key and signatures, 14 FORS
                     leaves, counted signatures), each compared with the hashlib FIPS 205 reference

The model's Chip class is instrumented in place: every chip the scenario creates, every transact() and
every reset() is written to <outdir>/trace.txt with the chip state before and after it (register file,
flags, FRAM image), the response, the clock count, whether the model raised a control fault, and the
values the stage 3 / 4 stand-ins produced (nonces, owner verdicts). ROM images go to <outdir>/rom_<k>.txt.

--auth-verify N shortens the model's owner-verification stand-in (units.AUTH_VERIFY, 3.9 M clocks of
waiting per key load) for quick runs; the RTL bench takes the same number from the trace. The gate runs
use the model's own value.

--propose applies named model changes in memory (apply_proposals below): the changes this lane proposes
to the spec owner. Without it the model runs exactly as written.

Nothing in the model is edited. --scratch N runs the model on a row map with N scratch rows
(rtl/gen_defs.py model_isa); the RTL's 72-row configuration is --scratch 20.
"""
import io
import os
import sys
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
V2 = os.path.normpath(os.path.join(HERE, ".."))
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(V2, "rtl"))
sys.path.insert(0, HERE)
import gen_defs  # noqa: E402
import gen_rom  # noqa: E402


class Recorder:
    def __init__(self, outdir, isa):
        self.outdir, self.isa = outdir, isa
        self.out = open(os.path.join(outdir, "trace.txt"), "w")
        self.roms = {}
        self.keep = []                 # keep ROM objects alive so id() stays unique
        self.nchips = self.nx = self.nfault = self.skipped_l = self.nother = 0

    def w(self, s):
        self.out.write(s + "\n")

    def rom_id(self, rom):
        if id(rom) not in self.roms:
            k = len(self.roms)
            self.roms[id(rom)] = k
            self.keep.append(rom)
            with open(os.path.join(self.outdir, f"rom_{k}.txt"), "w") as fh:
                fh.write(gen_rom.rom_text(rom))
        return self.roms[id(rom)]

    def snap(self, c):
        m = c.m
        nonce = m.nonce or [0, 0]
        flags = (int(m.key_valid), m.key_attr & 15, int(m.fault_mac), int(m.fault_anchor), int(m.fault_control),
                 int(m.verify_ok), int(m.dev_ok), int(m.nonce is not None), nonce[0], nonce[1])
        mem = bytes(m.fram.mem[:64]).ljust(64, b"\0")
        return flags, tuple(m.rf.rows), mem

    @staticmethod
    def fmt(s):
        flags, rows, _ = s
        return " ".join(f"{v:x}" for v in flags) + " | " + " ".join(f"{v:x}" for v in rows)


def install(rec):
    import chip
    import framing
    from machine import ControlFault
    isa = rec.isa
    Chip = chip.Chip
    o_init, o_transact, o_reset = Chip.__init__, Chip.transact, Chip.reset

    def init(self, config="S", rom=None, fram=None, puf=None, entropy=None, owner=None):
        o_init(self, config, rom, fram, puf, entropy, owner)
        self._rec = None
        if config != "S":
            rec.skipped_l += 1
            return
        m = self.m
        assert m.rf.nrows == isa.ROWS_S
        self._rec = dict(cid=rec.nchips, ent=[], own=[], fram=[])
        rec.nchips += 1
        log = self._rec
        if m.entropy is not None:
            real_draw = m.entropy.draw

            def draw():
                v = real_draw()
                log["ent"].append(v)
                return v
            m.entropy.draw = draw           # on the instance: the object keeps its class
        if m.owner is not None:
            real_owner = m.owner

            def own(nonce, digest, sig):
                ok = bool(real_owner(nonce, digest, sig))
                log["own"].append((ok, list(sig), list(digest), list(nonce)))
                return ok
            m.owner = own
        fr = m.fram
        f_start, f_rword, f_wword = fr.start, fr.rword, fr.wword

        def start(slot, write):
            k = f_start(slot, write)
            log["fram"].append(f"s{slot & 1}{'w' if write else 'r'}")
            return k

        def rword():
            v, k = f_rword()
            log["fram"].append(f"r{v:x}")
            return v, k

        def wword(v):
            k = f_wword(v)
            log["fram"].append(f"w{v:x}")
            return k
        fr.start, fr.rword, fr.wword = start, rword, wword
        secret = "-" if m.puf is None else "".join(f"{w:016x}" for w in reversed(m.puf.reconstruct()))
        rec.w(f"CHIP {log['cid']} rom {rec.rom_id(self.rom)} puf {secret} ent {int(m.entropy is not None)} "
              f"own {int(m.owner is not None)}")
        log["last"] = rec.snap(self)

    def transact(self, words):
        log = self._rec
        if log is None:
            return o_transact(self, words)
        pre = rec.snap(self)
        log["ent"].clear()
        log["own"].clear()
        log["fram"].clear()
        fault = 0
        try:
            rsp = o_transact(self, words)
            cycles = self.m.cycles
        except ControlFault:
            fault, rsp, cycles = 1, list(self.m.response), 0
            raise
        except framing.LinkError:
            rec.nother += 1            # the request stream itself was malformed: nothing ran
            raise
        finally:
            if fault or "rsp" in dir():
                post = rec.snap(self)
                poked = int(pre[:2] != log["last"][:2])     # flags and rows; the FRAM is outside the chip
                rec.nx += 1
                rec.nfault += fault
                rec.w(f"X {log['cid']} {fault} {cycles} {poked}")
                rec.w("Q " + " ".join(f"{w:x}" for w in words))
                rec.w("R " + " ".join(f"{w:x}" for w in rsp))
                rec.w("F0 " + pre[2].hex())
                rec.w("F1 " + post[2].hex())
                rec.w("S0 " + rec.fmt(pre))
                rec.w("S1 " + rec.fmt(post))
                rec.w("M " + " ".join(log["fram"]))
                rec.w("E " + " ".join(f"{v[0]:x} {v[1]:x}" for v in log["ent"]))
                rec.w("O " + " ".join(f"{int(ok)} " + " ".join(f"{x:x}" for x in sig + dig + non)
                                      for ok, sig, dig, non in log["own"]))
                log["last"] = post
        return rsp

    def reset(self):
        o_reset(self)
        if self._rec is not None:
            rec.w(f"POR {self._rec['cid']}")
            self._rec["last"] = rec.snap(self)

    Chip.__init__, Chip.transact, Chip.reset = init, transact, reset


def apply_proposals(names, isa):
    """Model changes proposed to the spec owner, applied in memory so that the RTL can be compared with
    the model as it would be after them. The model's files are not touched.
      kec_last_w   after KEC the row the Keccak unit wrote last (lane 24) counts as just written, like any
                   other store: an instruction that reads it next waits one clock."""
    import machine
    if "kec_last_w" in names:
        o_step = machine.Machine._step

        def step(self):
            w = self.rom.words[self.pc] if self.pc < len(self.rom.words) else None
            more = o_step(self)
            if more and w is not None and isa.OPS[isa.decode(w)["op"]] == "KEC":
                self.last_w = isa.LANE0 + 24
            return more
        machine.Machine._step = step
    if "ir_stage" in names:
        # two-stage machine (rtl/dregg_seq.sv IR_STAGE = 1): an instruction whose successor is not the
        # next address is followed by one empty clock, which also absorbs the stall of a following read
        o_step2 = machine.Machine._step

        def step2(self):
            pc0 = self.pc
            more = o_step2(self)
            if more and self.pc != pc0 + 1:
                self.cycles += 1
                self.last_w = None          # the row written by that instruction has closed meanwhile
            return more
        machine.Machine._step = step2
    if "ra_stage" in names:
        # registered read address (rtl/dregg_seq.sv RA_STAGE = 1): every row read costs one clock, in
        # place of the conditional two-phase stall; KMOV reads its key row the same way
        o_rd = machine.Machine._rd

        def rd(self, row, same=None):
            r = o_rd(self, row, same)
            if row != self.last_w:
                self.cycles += 1
            return r
        machine.Machine._rd = rd
        o_step3 = machine.Machine._step

        def step3(self):
            w = self.rom.words[self.pc] if self.pc < len(self.rom.words) else None
            more = o_step3(self)
            if more and w is not None and isa.OPS[isa.decode(w)["op"]] == "KMOV":
                self.cycles += 1
            return more
        machine.Machine._step = step3
    if "opr_estimate" in names:
        # ESTIMATE ONLY, no RTL behind it: an operand register in front of the word unit, one more clock for
        # every instruction that goes through the word unit (two-operand functions, CMP, UN, LDF, LDC, DIN,
        # FRAM RWORD)
        o_step4 = machine.Machine._step
        wu_ops = set(isa.ALU2) | {"UN", "LDF", "LDC", "DIN"}

        def step4(self):
            w = self.rom.words[self.pc] if self.pc < len(self.rom.words) else None
            more = o_step4(self)
            if more and w is not None:
                d = isa.decode(w)
                mn = isa.OPS[d["op"]]
                if mn in wu_ops or (mn == "FRAM" and isa.FRAM[d["a"]] == "RWORD"):
                    self.cycles += 1
            return more
        machine.Machine._step = step4
    for n in names:
        if n not in ("kec_last_w", "ir_stage", "ra_stage", "opr_estimate"):
            raise SystemExit(f"unknown proposal {n}")


def main():
    args = sys.argv[1:]
    scratch = None
    proposals = []
    auth_verify = None
    while args and args[0].startswith("--"):
        if args[0] == "--scratch":
            scratch = int(args[1])
        elif args[0] == "--propose":
            proposals = args[1].split(",")
        elif args[0] == "--auth-verify":
            auth_verify = int(args[1])
        else:
            raise SystemExit(__doc__)
        args = args[2:]
    if len(args) < 2:
        raise SystemExit(__doc__)
    outdir, scenarios = args[0], args[1:]
    os.makedirs(outdir, exist_ok=True)
    isa = gen_defs.model_isa(scratch)
    tests_dir = os.path.join(gen_defs.V2REF, "tests")
    sys.path.insert(0, tests_dir)
    import units
    if auth_verify is not None:
        units.AUTH_VERIFY = auth_verify       # shorter owner-verification stand-in (quick runs only)
    apply_proposals(proposals, isa)
    rec = Recorder(outdir, isa)
    rec.w(f"MODEL rows {isa.ROWS_S} key0 {isa.KEY0} nonce_draw {units.NONCE_DRAW} auth_verify {units.AUTH_VERIFY}")
    install(rec)
    status = 0
    for sc in scenarios:
        rec.w(f"SCENARIO {sc}")
        if sc in ("script", "quick"):
            import replay
            rows, failures, inserted = replay.replay("S", quick=(sc == "quick"))
            print(f"{sc}: {len(rows)} reference transactions, {len(inserted)} inserted steps, {len(failures)} model failures")
            status |= bool(failures)
        elif sc == "tests":
            suite = unittest.defaultTestLoader.discover(tests_dir)
            buf = io.StringIO()
            res = unittest.TextTestRunner(stream=buf, verbosity=0).run(suite)
            bad = sorted(t.id() for t, _ in res.failures + res.errors)
            print(f"tests: {res.testsRun} run, {len(res.failures)} failures, {len(res.errors)} errors")
            for t in bad:
                print("  model test not passing on this row map:", t)
            # three tests assert the 64-row map itself; on another map exactly those may fail
            known = {"test_output_bound.KeyRows.test_out_and_work_rows_are_not_addressable",
                     "test_units.Registers.test_row_map", "test_units.Registers.test_wipe_classes"}
            if bad and not (scratch not in (None, 12) and set(bad) == known):
                print(buf.getvalue()[-3000:])
                status = 1
        elif sc in ("extra", "gaps"):
            # Directed microprograms of this lane, run on the model. "extra": cases the model's own tests
            # only tell apart by the fault message, which the RTL does not have; each must end in a control
            # fault in the model. "gaps": cases where the RTL needs a clock the model does not count
            # (reported to the spec owner; not part of the gate).
            import chip
            import common
            import fixtures
            import host
            import uasm
            from machine import ControlFault
            n = 0
            if sc == "extra":
                # KEYWR outside the key range with the authorisation latch set (AUTH in range, then a branch out)
                key_part = (f".entry {fixtures.TEST_OP} t_entry diag\nt_entry: CTL NONCE\n LD #1\n ST l0\n CTL AUTH\n"
                            " BR Z t_no\n BR t_out\nt_no: FAIL #12\n")
                rom_part = "t_out: LD #5\n KEYWR > k_seed0\n LD #0\n HDR #0\n END\n"
                src = [(nm, key_part if nm == "provision.uc" else t) for nm, t in chip.read_sources("S")] + [("extra", rom_part)]
                c = common.new_chip("S", rom=uasm.assemble(src))
                import units
                nonce = units.EntropyUnit(1).draw()
                sig = host.words_of(host.q.turboshake256(c.owner.key + host.bytes_of(nonce) + host.bytes_of([1, 0, 0, 0]), 16, 0x23))
                try:
                    c.transact([host.hdr(fixtures.TEST_OP, 0, 16)] + sig)
                    raise SystemExit("extra: KEYWR outside the key range was not refused by the model")
                except ControlFault as e:
                    assert "KEYWR outside the key range" in str(e), str(e)
                    n += 1
                # a capacity lane of a keyed state, on a path that would release it
                for lane in (17, 24):
                    try:
                        fixtures.run(f" KMOV k_seed0 > l0\n KEC 24\n LD #1\n HDR #1\n LD l{lane}\n ST l1\n REL l1")
                        raise SystemExit("extra: capacity lane read was not refused by the model")
                    except ControlFault as e:
                        assert "capacity lane" in str(e), str(e)
                        n += 1
                # the same path with a rate lane is legal and releases it (the positive twin)
                _, rsp = fixtures.run(" KMOV k_seed0 > l0\n KEC 24\n LD #1\n HDR #1\n LD l16\n ST l1\n REL l1")
                assert len(rsp) == 2
                n += 1
            else:
                _, rsp = fixtures.run(" LD #1\n HDR #1\n WIPE #3\n LD l0\n PUSH H", keys=False)      # read of a row a wipe has open
                assert rsp[1] == 0
                _, rsp = fixtures.run(" LD #1\n HDR #1\n KEC 12\n PUSH l24", keys=False)              # read of the unit's last write
                n += 2
            print(f"{sc}: {n} directed cases")
        elif sc == "long":
            # the long signer runs of tests/report.py, on configuration S, each checked against the
            # hashlib FIPS 205 reference of host.py
            import common
            import host
            K, SEED, PRF, PK = bytes(range(16)), bytes(range(16, 32)), bytes(range(32, 48)), bytes(range(48, 64))
            c = common.new_chip("S")
            assert host.provision(c, c.owner, K, SEED, PRF, True, False) == [host.rhdr(host.OP_KEYLOAD, 0)]
            assert c.transact(host.keccak(bytes(range(200)) * 3, 40, 0x1F, False))[0] == host.rhdr(host.OP_KECCAK, 320)
            assert c.transact(host.keccak(bytes(300), 21, 0x07, True))[0] == host.rhdr(host.OP_KECCAK, 168)
            for msg, kw in ((bytes(16), dict(pubgen=True)), (b"\xff" * 16, {}),
                            (bytes.fromhex("0123456789abcdeffedcba9876543210"), {})):
                rsp = c.transact(host.cth_wots(K, 0, 0, 1, 2, PK, msg, 35, 0, **kw))
                digits = [15] * 35 if kw else host.wots_digits(msg)
                want = [w for i in range(35) for w in host.words_of(host.wots_chain(PK, SEED, 0, 1, 2, i, digits[i]))]
                assert rsp == [host.rhdr(host.OP_CTH, 560)] + want, "WOTS values differ from the FIPS 205 reference"
            for pub in (False, True):
                rsp = c.transact(host.cth_fors(K, 0, 0, 1, 2, PK, list(range(14)), pubgen=pub))
                want = [w for i in range(14) for w in host.words_of(host.fors_leaf(PK, SEED, 0, 1, 2, i, pub))]
                assert rsp == [host.rhdr(host.OP_CTH, 224)] + want, "FORS values differ from the FIPS 205 reference"
            cc = common.new_chip("S")
            assert host.provision(cc, cc.owner, K, SEED, PRF, True, True) == [host.rhdr(host.OP_KEYLOAD, 0)]
            for leaf in (3, 4, 9):
                assert len(cc.transact(host.cth_wots(K, leaf, 0, 1, leaf, PK, bytes(16), 35))) == 71
            print("long: WOTS public key, two 35-chain signatures, FORS 14 secret and public, three counted signatures")
        else:
            raise SystemExit(f"unknown scenario {sc}")
    rec.w("END")
    rec.out.close()
    print(f"recorded: {rec.nchips} chips, {rec.nx} transactions ({rec.nfault} control faults), {len(rec.roms)} ROM images, "
          f"{rec.skipped_l} configuration-L chips skipped, {rec.nother} malformed requests not recorded")
    sys.exit(status)


if __name__ == "__main__":
    main()
