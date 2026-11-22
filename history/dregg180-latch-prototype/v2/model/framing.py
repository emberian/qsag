"""QSAG-Wire word framing (link-independent): request header fields, payload accounting and the
response header. A link (link.py) moves 64-bit words; nothing here knows how.

Request header   [7:0] 0x51  [15:8] opcode  [23:16] flags  [47:24] payload length in bytes  [63:48] arg
Response header  [7:0] 0x51  [15:8] opcode | 0x80  [23:16] 0x80 on error, else bit 0 = ok
                 [47:24] payload length in bytes  [63:48] error code
"""
MAGIC = 0x51
M64 = (1 << 64) - 1


class LinkError(Exception):
    """The request stream itself is malformed (a real chip would wait for more words)."""


class Framer:
    def __init__(self):
        self.hdr = 0
        self.payload = []
        self.pos = 0

    def begin(self, words):
        if self.remaining:
            raise LinkError("the previous command left payload words undrained: the link is out of step")
        self.hdr = words[0] & M64
        self.magic_ok = (self.hdr & 0xFF) == MAGIC
        n = self.nwords_total if self.magic_ok else 0      # a bad header's length is not trusted
        if len(words) - 1 != n:
            raise LinkError(f"request carries {len(words) - 1} payload words, header says {n}")
        self.payload = [w & M64 for w in words[1:]]
        tail = self.length & 7
        if n and tail:                                      # bytes past the stated length never reach the core
            self.payload[-1] &= (1 << (8 * tail)) - 1
        self.pos = 0

    op = property(lambda s: (s.hdr >> 8) & 0xFF)
    flags = property(lambda s: (s.hdr >> 16) & 0xFF)
    length = property(lambda s: (s.hdr >> 24) & 0xFFFFFF)
    arg = property(lambda s: (s.hdr >> 48) & 0xFFFF)
    nwords_total = property(lambda s: (s.length + 7) >> 3)
    remaining = property(lambda s: len(s.payload) - s.pos)

    def din(self):
        v = self.payload[self.pos]
        self.pos += 1
        return v

    def drain(self):
        self.pos = len(self.payload)

    def response_header(self, nwords, ok, err):
        flags = 0x80 if err else int(bool(ok))
        return MAGIC | ((self.op | 0x80) << 8) | (flags << 16) | ((8 * nwords) << 24) | (err << 48)
