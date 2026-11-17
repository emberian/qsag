"""The reference golden model's 54-transaction script against the v2 model (replay.py states what can
still be compared with the reference and what is compared with FIPS 205 instead)."""
import collections
import unittest

import replay

import host


class ReferenceScript(unittest.TestCase):
    def test_full_script_configuration_L(self):
        rows, failures, inserted = replay.replay("L")
        self.assertEqual(failures, [])
        self.assertEqual(len(rows), 54)
        cls = collections.Counter(r["cls"] for r in rows)
        # 34 requests sent unchanged and answered as the reference answers; 11 CTH and 2 PRF_MSG answered as
        # FIPS 205 says under the chip's own keys (or refused with the reference's code); 2 key loads and the
        # roll-back refusal, which no longer exist; 4 verifier-VM requests
        self.assertEqual(cls, {"verbatim": 34, "recomputed": 13, "changed": 3, "deferred": 4})
        self.assertEqual(collections.Counter(r["op"] for r in rows if r["cls"] == "recomputed"),
                         {host.OP_CTH: 11, host.OP_PRFMSG: 2})
        self.assertEqual(collections.Counter(r["op"] for r in rows if r["cls"] == "changed"), {0x40: 2, host.OP_CTH: 1})
        self.assertEqual(len(inserted), 2)                 # a provisioned chip; a second one with the counted policy
        self.assertTrue(all(r["ok"] for r in rows))
        self.assertTrue(all(r["op"] in (0x30, 0x31) for r in rows if r["cls"] == "deferred"))

    def test_full_script_configuration_S(self):
        rows, failures, _ = replay.replay("S")
        self.assertEqual(failures, [])
        cls = collections.Counter(r["cls"] for r in rows)
        self.assertEqual(cls, {"verbatim": 19, "recomputed": 13, "changed": 3, "deferred": 4, "absent": 15})
        self.assertTrue(all(r["op"] in (0x10, 0x11) for r in rows if r["cls"] == "absent"))

    def test_quick_script(self):
        for cfg in "SL":
            rows, failures, _ = replay.replay(cfg, quick=True)
            self.assertEqual(failures, [])
            self.assertEqual(len(rows), 38)

    def test_comparison_can_fail(self):
        """The comparison is not vacuous: a signer that derives SK.seed under another label must show up,
        and so must a use counter that is written one too low."""
        import common
        import chip
        import uasm
        for old, new, needle in (('.const C_LSEED  "DREGGSKS"', '.const C_LSEED  "DREGGSKT"', "WOTS"),
                                 ("            ADD  #1\n            BR   CY e_reuse          ; counter would wrap",
                                  "            ADD  #0\n            BR   CY e_reuse          ; counter would wrap", "FRAMCHK")):
            src = chip.read_sources("S", common.SLH)
            self.assertEqual(sum(t.count(old) for _, t in src), 1)
            key = ("S", common.SLH, None)
            saved = chip.build_rom("S", common.SLH)
            chip._roms[key] = uasm.assemble([(n, t.replace(old, new)) for n, t in src])
            cache = dict(common._cache)
            common._cache.clear()
            try:
                _, failures, _ = replay.replay("S")
            finally:
                chip._roms[key] = saved
                common._cache.clear()
                common._cache.update(cache)
            self.assertTrue(any(needle in name for name, _, _ in failures), (needle, [f[0] for f in failures]))

    def test_verbatim_responses_are_compared_word_for_word(self):
        """The only unchecked words of the whole reference script are PING words 2..4."""
        import common
        wild = [(name, i) for kind, p in common.reference_script() if kind == "xfer"
                for name, tx, rx in [p] for i, w in enumerate(rx) if w is None]
        self.assertEqual(wild, [("PING", 2), ("PING", 3), ("PING", 4)] * 2)


if __name__ == "__main__":
    unittest.main()
