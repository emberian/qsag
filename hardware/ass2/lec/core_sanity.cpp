#include "Vqsag_ass2_core.h"
#include "Vqsag_ass2_core___024root.h"
#include <array>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <vector>

static void check(bool ok, const char* why) {
    if (!ok) { std::cerr << why << '\n'; std::exit(1); }
}

static std::vector<unsigned> run(const char* path) {
    std::ifstream input(path);
    Vqsag_ass2_core d;
    std::array<uint64_t,1024> mem{};
    unsigned count;
    check(bool(input >> count), "missing vector header");
    input >> std::hex;
    for (unsigned i=0; i<count; ++i) {
        uint64_t w;
        check(bool(input >> w), "short program");
        mem.at(i/2) |= w << (32*(i%2));
    }
    auto tick = [&] {
        d.clk=0; d.eval();
        auto addr=d.mem_addr_o/8;
        d.mem_fault_i=addr>=mem.size(); d.eval();
        uint64_t response=d.mem_rdata_i;
        if (d.mem_en_o && !d.mem_fault_i) {
            response=mem[addr];
            for(unsigned i=0; i<8; ++i) if(d.mem_we_o && (d.mem_wstrb_o>>i & 1)) {
                uint64_t mask=uint64_t(255)<<(8*i);
                mem[addr]=(mem[addr]&~mask)|(d.mem_wdata_o&mask);
            }
        }
        d.clk=1; d.eval(); d.mem_rdata_i=response; d.eval();
    };
    d.tamper_zeroize_n=1; d.rst_n=0; tick(); d.rst_n=1;
    d.start_i=1; tick(); d.start_i=0;
    unsigned retired=0, previous=0;
    std::vector<unsigned> latencies;
    while(!d.halted_o) {
        tick();
        check(d.phys_cycles_o<200000, "timeout");
        if(!d.insn_retire_o) continue;
        std::vector<uint64_t> got={d.pc_o,d.instret_o,d.cycles_o};
        auto* r=d.rootp;
        for(unsigned j=0;j<16;++j) got.push_back(r->qsag_ass2_core__DOT__regs[j]);
        for(unsigned j=0;j<25;++j) got.push_back(r->qsag_ass2_core__DOT__spg[j]);
        for(unsigned i=0;i<got.size();i++) {
            uint64_t expect;
            check(bool(input>>expect),"short trace");
            if(expect!=got[i]) {
                std::cerr<<"retirement "<<retired<<" field "<<i<<std::hex<<" pc="<<d.pc_o
                         <<" expected="<<expect<<" actual="<<got[i]<<'\n';
                std::exit(1);
            }
        }
        latencies.push_back(d.phys_cycles_o-previous);
        previous=d.phys_cycles_o;
        ++retired;
    }
    check(retired==count, "early halt");
    // Reload nonzero state and remove the clock while the secret is live.
    mem[0]=0x00050000'c0000140ULL; // SPUT S0,R4; HALT
    d.arg_regs_we_i=1; d.arg_reg_addr_i=4; d.arg_reg_data_i=~uint64_t(0);tick();
    d.arg_regs_we_i=0; d.start_i=1;tick();d.start_i=0;
    while(!d.halted_o) tick();
    check(d.rootp->qsag_ass2_core__DOT__spg[0]==~uint64_t(0),"tamper precondition");
    d.tamper_zeroize_n=0; d.eval();
    for(unsigned j=0;j<16;++j) check(!d.rootp->qsag_ass2_core__DOT__regs[j],"tamper GPR");
    for(unsigned j=0;j<25;++j) check(!d.rootp->qsag_ass2_core__DOT__spg[j],"tamper sponge");
    d.tamper_zeroize_n=1;d.eval();
    check(d.tampered_o && d.halted_o,"tamper not sticky");
    std::cout<<retired<<" retirements matched all 41 registers, PC, INSTRET and CYCLES\n";
    return latencies;
}

int main(int argc,char** argv) {
    check(argc==3,"expected two vector files");
    auto first=run(argv[1]);
    check(first==run(argv[2]),"operand-dependent latency");
    std::cout<<"Physical clock counts matched for every retirement across both traces\n";
}
