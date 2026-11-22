// Independent pin-level FM25W256 model. Storage persists across chip resets.
struct Fram {
    std::array<u8,32768> bytes;
    bool cs=true, sck=false, wren=false, write=false, miso=false;
    u8 op=0, shift=0; unsigned addr=0, bits=0;
    Fram() { bytes.fill(0xff); }
    void pins(bool select, bool clock, bool mosi) {
        if (select) {
            if (!cs && write) wren=false;
            bits=0; addr=0; shift=0; op=0; write=false; miso=false;
        } else if (clock && !sck) {
            shift=u8((shift<<1)|mosi);
            if (++bits%8 == 0) {
                if (bits==8) { op=shift; if (op==6) wren=true; }
                else if (bits<=24) addr=((addr<<8)|shift)&32767;
                else {
                    if (op==2 && wren) { bytes[addr]=shift; write=true; }
                    addr=(addr+1)&32767;
                }
            }
        } else if (!clock && sck && op==3 && bits>=24) {
            miso=(bytes[addr]>>(7-bits%8))&1;
        }
        cs=select; sck=clock;
    }
};
