// Replay gen_cosim_vectors.py records through a synchronous, byte-strobed SRAM.
#include "Vass2_cosim_top.h"
#include "verilated.h"
#if VM_COVERAGE
#include "verilated_cov.h"
#endif
#include <cstdint>
#include <fstream>
#include <iostream>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using Word = std::uint64_t;
using Bytes = std::vector<std::uint8_t>;
using Writes = std::vector<std::pair<Word, Word>>;

static Word number(std::istream &in) {
    Word x;
    if (!(in >> std::hex >> x)) throw std::runtime_error("missing hexadecimal field");
    return x;
}

static Bytes bytes(std::istream &in) {
    std::string s;
    if (!(in >> s) || (s.size() % 2) || s.find_first_not_of("0123456789abcdef") != s.npos)
        throw std::runtime_error("invalid byte string");
    Bytes result;
    result.reserve(s.size() / 2);
    for (size_t i = 0; i < s.size(); i += 2)
        result.push_back(std::stoul(s.substr(i, 2), nullptr, 16));
    return result;
}

struct Machine {
    Vass2_cosim_top dut;
    Bytes mem;
    Writes writes;
    bool started = false;
    explicit Machine(size_t size) : mem(size) {
        if (!size || size % 8) throw std::runtime_error("invalid SRAM size");
        dut.clk = 0;
        dut.rst_n = 0;
        dut.start_i = 0;
        dut.mem_rdata_i = 0;
        dut.mem_fault_i = 0;
        tick();
    }
    ~Machine() { dut.final(); }

    void tick() {
        dut.clk = 0;
        dut.eval();
        Word addr = dut.mem_addr_o & ~Word(7);
        bool fault = dut.mem_en_o && addr >= mem.size();
        dut.mem_fault_i = fault;
        dut.eval();
        Word next_data = dut.mem_rdata_i;
        if (dut.mem_en_o && !fault) {
            next_data = 0;
            for (unsigned i = 0; i < 8; ++i) {
                next_data |= Word(mem[addr+i]) << (8*i);
                if (dut.mem_we_o && ((dut.mem_wstrb_o >> i) & 1)) {
                    mem[addr+i] = dut.mem_wdata_o >> (8*i);
                    writes.emplace_back(addr+i, mem[addr+i]);
                }
            }
        }
        dut.clk = 1;
        dut.eval();
        // Registered read response changes after the sampling edge.
        dut.mem_rdata_i = next_data;
        dut.eval();
    }
    void start() {
        dut.rst_n = 1;
        dut.start_i = 1;
        tick();
        dut.start_i = 0;
        started = true;
    }
    static void check(const std::string &name, Word actual, Word expected) {
        if (actual == expected) return;
        std::ostringstream msg;
        msg << name << " expected 0x" << std::hex << expected << " got 0x" << actual;
        throw std::runtime_error(msg.str());
    }
    void step(std::istream &in) {
        if (!started) start();
        Word pc = number(in), insn = number(in), cause = number(in);
        check("pre-PC", dut.pc_o, pc);
        check("pre-halted", dut.halted_o, 0);
        Word fetched = 0;
        if (pc <= mem.size()-4 && !(pc & 3))
            for (unsigned i = 0; i < 4; ++i) fetched |= Word(mem[pc+i]) << (8*i);
        check("instruction", fetched, insn);
        writes.clear();
        unsigned clocks = 0;
        do {
            if (++clocks > 1000000) throw std::runtime_error("instruction timeout");
            tick();
        } while (!(dut.insn_retire_o || dut.trap_o));
        check("trap", dut.trap_o, cause != 0);
        check("retire", dut.insn_retire_o, cause == 0);
        check("PC", dut.pc_o, number(in));
        check("halted", dut.halted_o, number(in));
        check("ECAUSE", dut.ecause_o, number(in));
        check("INSTRET", dut.instret_o, number(in));
        check("CYCLES", dut.cycles_o, number(in));
        for (unsigned i = 0; i < 16; ++i) check("R"+std::to_string(i), dut.regs[i], number(in));
        for (unsigned i = 0; i < 25; ++i) check("S"+std::to_string(i), dut.spg[i], number(in));
        check("store byte count", writes.size(), number(in));
        for (const auto &w : writes) {
            check("store address", w.first, number(in));
            check("store data", w.second, number(in));
        }
    }
};

int main(int argc, char **argv) {
    Verilated::commandArgs(argc, argv);
    if (argc != 2) { std::cerr << "usage: sim_ass2_lockstep vectors\n"; return 2; }
    std::ifstream file(argv[1]);
    size_t declared = 0, cases = 0, steps = 0;
    std::string tag, name, line;
    std::unique_ptr<Machine> machine;
    try {
        if (!(file >> tag >> declared) || tag != "ASS2-V1" || !declared)
            throw std::runtime_error("invalid header");
        std::getline(file, line);
        while (std::getline(file, line)) {
            std::istringstream in(line);
            if (!(in >> tag) || tag == "#") continue;
            if (tag == "CASE" && !machine) {
                in >> name;
                machine = std::make_unique<Machine>(number(in));
            } else if (tag == "LOAD" && machine && !machine->started) {
                Word addr = number(in);
                for (auto b : bytes(in)) machine->mem.at(addr++) = b;
            } else if (tag == "STEP" && machine) {
                machine->step(in);
                ++steps;
            } else if (tag == "END" && machine && machine->started && machine->dut.halted_o) {
                if (machine->mem != bytes(in)) throw std::runtime_error("final SRAM mismatch");
                ++cases;
                machine.reset();
            } else throw std::runtime_error("unexpected record " + tag);
            if (in >> tag) throw std::runtime_error("trailing fields");
        }
        if (machine || cases != declared || file.bad()) throw std::runtime_error("incomplete corpus");
    } catch (const std::exception &err) {
        std::cerr << name << " at PC 0x" << std::hex << (machine ? machine->dut.pc_o : 0)
                  << ": " << err.what() << "\n";
        return 1;
    }
    std::cout << cases << " programs, " << steps << " RTL architectural steps passed\n";
#if VM_COVERAGE
    VerilatedCov::write("coverage.dat");
#endif
}
