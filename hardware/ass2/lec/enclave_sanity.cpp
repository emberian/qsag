#include "Vqsag_ass2_enclave_top.h"
#include <array>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

static void check(bool ok, const char* message) {
    if (!ok) { std::cerr << message << '\n'; std::exit(1); }
}

struct Host {
    Vqsag_ass2_enclave_top d;
    bool octal=false, clocked=false;
    std::vector<int> uart;
    void clocks(int n) {
        if (!clocked) return;
        while(n--) {
            d.clk=1;d.eval(); uart.push_back(d.bidir_out>>11 & 1);
            d.clk=0;d.eval();
        }
    }
    void select(bool active) {
        d.input_in=(d.input_in & ~3U) | (!active) | (octal<<1);
        d.eval();clocks(8);
    }
    uint8_t byte(uint8_t data, bool read=false) {
        uint8_t out=0;
        for(int bit=7;bit>=0;--bit) {
            auto drive=octal?data:(data>>bit & 1);
            d.bidir_in=(d.bidir_in & ~255ULL)|drive;
            d.eval();clocks(5);
            if (read) {
                if((d.bidir_oe&255)!=(octal?255:2)) {
                    std::cerr<<"DQ direction: octal="<<octal<<" bit="<<bit<<" clocks="<<uart.size()
                             <<" oe="<<std::hex<<d.bidir_oe<<'\n';
                    std::exit(1);
                }
                out=octal?(d.bidir_out&255):((out<<1)|(d.bidir_out>>1&1));
            } else check(!(d.bidir_oe&255),"DQ contention during command");
            d.bidir_in|=256;d.eval();clocks(5);
            d.bidir_in&=~256ULL;d.eval();
            if(octal) break;
        }
        return out;
    }
    void put(uint64_t word,int bytes) {
        for(int i=0;i<bytes;++i) {byte(word);word>>=8;}
    }
    uint64_t get(int bytes) {
        uint64_t word=0;
        for(int i=0;i<bytes;++i) word|=uint64_t(byte(0,true))<<(8*i);
        return word;
    }
    void header(int cmd,int addr,int count) {
        select(true);byte(cmd);put(addr,2);put(count,2);
    }
    void run(uint32_t pc,int flags) {
        select(true);byte(0x20);put(pc,4);byte(flags);select(false);
    }
    void wait_irq() {
        for(int i=0;i<10000;++i) {
            if(d.bidir_out>>10&1) return;
            clocks(1);
        }
        check(false,"RUN timed out");
    }
};

int main() {
    Host h;
    h.d.input_in=5;h.d.bidir_in=1ULL<<12;h.d.clk=0;
    h.d.rst_n=1;h.d.eval();h.d.rst_n=0;h.d.eval();h.d.rst_n=1;h.d.eval();
    for(bool mode:{false,true}) {
        h.octal=mode;
        h.select(true);h.byte(1);
        check(h.get(8)==0x4153533200000001ULL,"clockless PING");
        h.select(false);h.select(true);h.byte(5);
        uint64_t diag=h.get(5);
        check((diag>>32)==0x5a && uint16_t(diag)==0xa552,"clockless DIAG");
        h.select(false);
    }
    h.clocked=true;
    std::array<uint64_t,3> data={0x0102030405060708ULL,~0ULL,0xfedcba9876543210ULL};
    for(bool mode:{false,true}) {
        h.octal=mode;
        h.header(0x10,1021,3);
        for(auto w:data)h.put(w,8);
        h.select(false);
        h.header(0x11,1021,3);h.byte(0);
        for(auto w:data)check(h.get(8)==w,"SRAM readback mismatch");
        h.select(false);
        h.header(0x10,1021,1);h.put(0,7);h.select(false);
        h.header(0x10,1023,2);h.put(0,8);h.select(false);
        h.header(0x11,1021,3);h.byte(0);
        for(auto w:data)check(h.get(8)==w,"abort or out-of-range DMA modified SRAM");
        h.select(false);
    }
    // MOVZ20 R4,1; MOVZ20 R5,0xa5; CSRW DBG_OUT,R5 twice; HALT.
    h.header(0x10,0,3);
    h.put(0x4000a50540000104ULL,8);
    h.put(0x00a3005000a30050ULL,8);
    h.put(0x00050000ULL,8); h.select(false);
    h.run(0,3);h.wait_irq();
    check((h.d.bidir_out>>14&3)==1,"verification latch");
    h.select(true);h.byte(0x21);
    check(h.get(1)==5 && h.get(1)==0 && h.get(8)==1 && h.get(8)==0 &&
          h.get(8)==5 && h.get(8)==5,"status words");
    h.select(false);
    h.clocks(400); // Allow the final character to leave the TX pin after HALT.
    size_t start=0;
    for(int byte=0;byte<2;++byte) {
        while(start<h.uart.size() && h.uart[start]) ++start;
        check(start+380<h.uart.size(),"missing UART character");
        for(int bit=0;bit<10;++bit) {
            int want=(0x34a>>bit)&1; // {stop=1, 8'ha5, start=0}
            check(h.uart[start+20+40*bit]==want,"invalid 8N1 UART byte");
        }
        start+=400;
    }
    // Exercise the fixed-function pads through their firmware-facing MMIO words.
    h.d.bidir_in|=1ULL<<19;
    for(int bit=0;bit<10;++bit) {
        const unsigned frame=(1U<<9)|(0x69U<<1);
        h.d.bidir_in=(h.d.bidir_in&~(1ULL<<12))|(uint64_t(frame>>bit&1)<<12);
        h.clocks(40);
    }
    h.clocks(4);
    const uint32_t io_program[]={
        0x4fff0011, // MOVS20 R1,-256
        0x40000f02, 0x80001012, // GPIO direction = 0x0f
        0x4000a502, 0x80000012, // GPIO output = 0xa5
        0x40000602, 0x80002012, // FRAM CS asserted, SCK and MOSI high
        0x70002015, 0x80064005, // save FRAM pin readback at SRAM word 100
        0x70003014, 0x70003016, 0x80065006, // UART data/status before and after ack
        0x00050000, 0x00060000
    };
    h.header(0x10,16,7);
    for(auto w:io_program) h.put(w,4);
    h.select(false);h.run(128,2);h.wait_irq();
    check((h.d.bidir_oe>>20&255)==15 && (h.d.bidir_out>>20&255)==0xa5,"GPIO pads");
    check((h.d.bidir_out>>16&7)==6,"FRAM pads");
    h.header(0x11,100,2);h.byte(0);
    check(h.get(8)==14 && h.get(8)==0x69,"FRAM input or UART RX acknowledge");
    h.select(false);h.select(true);h.byte(0x21);
    check(h.get(1)==5 && h.get(1)==0 && h.get(8)==0x169,"UART RX status");
    h.select(false);
    h.clocked=false;h.d.input_in&=~4U;h.d.eval();
    check((h.d.bidir_out>>14&3)==2,"asynchronous tamper mask");
    h.d.input_in|=4U;h.d.eval();
    check((h.d.bidir_out>>14&3)==2,"tamper latch cleared without reset");
    check((h.d.bidir_oe>>28)==0 && (h.d.bidir_ie>>28)==1023 &&
          (h.d.bidir_pd>>28)==1023,"spare pad configuration");
    std::cout<<"Stopped-clock SPI/OSPI PING and DIAG, DMA, RUN, STATUS, UART TX/RX, GPIO, FRAM and tamper passed\n";
}
