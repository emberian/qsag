"""Host links. The core and the framer see 64-bit words; a link turns its own transport into
words. Only SPI is modelled (ARCHITECTURE.md decision D4); another link is another class here.

Frame format. A request is one chip-select frame: the header word, then exactly the number of payload
words its length field states. The response is clocked out in a second frame: the response header,
whose length field states the number of words that follow, then those words. While the chip is idle a
word that is not the first of a frame is dropped.

A response frame can end short. The header and each word leave the chip as the microcode pushes them,
so on a control fault (machine.ControlFault) the words already pushed have been sent and the rest never
come: the frame holds fewer words than its header states, and FAULT is raised. A host must treat a
short frame as no response at all. The model reports the words that were sent in ControlFault.sent;
Chip.transact raises, and SpiLink.exchange returns the short frame."""


class SpiLink:
    """SPI target, mode 0: one chip-select frame carries one request, bytes least significant first
    within each 64-bit word; the response is clocked out the same way in a second frame."""

    def __init__(self, chip):
        self.chip = chip

    def exchange(self, mosi):
        if len(mosi) % 8:
            raise ValueError("a request frame is a whole number of 64-bit words")
        words = [int.from_bytes(mosi[i:i + 8], "little") for i in range(0, len(mosi), 8)]
        from machine import ControlFault
        try:
            rsp = self.chip.transact(words)
        except ControlFault as e:
            rsp = e.sent
        return b"".join(w.to_bytes(8, "little") for w in rsp)
