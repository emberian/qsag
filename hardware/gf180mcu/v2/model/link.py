"""Host links. The core and the framer see 64-bit words; a link turns its own transport into
words. Only SPI is modelled (ARCHITECTURE.md decision D4); another link is another class here."""


class SpiLink:
    """SPI target, mode 0: one chip-select frame carries one request, bytes least significant first
    within each 64-bit word; the response is clocked out the same way in a second frame."""

    def __init__(self, chip):
        self.chip = chip

    def exchange(self, mosi):
        if len(mosi) % 8:
            raise ValueError("a request frame is a whole number of 64-bit words")
        words = [int.from_bytes(mosi[i:i + 8], "little") for i in range(0, len(mosi), 8)]
        return b"".join(w.to_bytes(8, "little") for w in self.chip.transact(words))
