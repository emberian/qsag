"""Stage 1 exit: the reference golden model's 54-transaction script against the v2 model."""
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
        # 36 requests sent unchanged; 12 CTH and 2 KEYLOAD requests rebuilt in the v2 format (same expected
        # responses); 4 verifier-VM requests that stage 1 does not implement
        self.assertEqual(cls, {"verbatim": 36, "translated": 14, "deferred": 4})
        self.assertEqual(collections.Counter(r["op"] for r in rows if r["cls"] == "translated"),
                         {host.OP_CTH: 12, host.OP_KEYLOAD: 2})
        self.assertEqual(len(inserted), 2)                 # one nonce request; one reset + counted key load
        self.assertTrue(all(r["ok"] for r in rows))
        self.assertTrue(all(r["op"] in (0x30, 0x31) for r in rows if r["cls"] == "deferred"))

    def test_full_script_configuration_S(self):
        rows, failures, _ = replay.replay("S")
        self.assertEqual(failures, [])
        cls = collections.Counter(r["cls"] for r in rows)
        self.assertEqual(cls, {"verbatim": 21, "translated": 14, "deferred": 4, "absent": 15})
        self.assertTrue(all(r["op"] in (0x10, 0x11) for r in rows if r["cls"] == "absent"))

    def test_quick_script(self):
        for cfg in "SL":
            rows, failures, _ = replay.replay(cfg, quick=True)
            self.assertEqual(failures, [])
            self.assertEqual(len(rows), 38)

    def test_comparison_can_fail(self):
        """The comparison is not vacuous: one flipped bit in the anchor constant must show up."""
        import chip
        import uasm
        src = [(n, t.replace('"QSAGNIFR"', '"QSAGNIFS"')) for n, t in chip.read_sources("S")]
        saved = chip._roms["S"] if "S" in chip._roms else None
        chip._roms["S"] = uasm.assemble(src)
        try:
            _, failures, _ = replay.replay("S")
        finally:
            if saved is None:
                del chip._roms["S"]
            else:
                chip._roms["S"] = saved
        self.assertTrue(any(name.startswith("FRAMCHK") for name, _, _ in failures))

    def test_verbatim_responses_are_compared_word_for_word(self):
        """The only unchecked words of the whole reference script are PING words 2..4."""
        import common
        wild = [(name, i) for kind, p in common.reference_script() if kind == "xfer"
                for name, tx, rx in [p] for i, w in enumerate(rx) if w is None]
        self.assertEqual(wild, [("PING", 2), ("PING", 3), ("PING", 4)] * 2)


if __name__ == "__main__":
    unittest.main()
