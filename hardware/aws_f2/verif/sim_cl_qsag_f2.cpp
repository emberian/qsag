// Test traffic uses only the two shell buses. Golden NI vectors came from the Rust verifier.
#ifdef HDK_WRAPPER
#include "Vcl_qsag_f2.h"
using Dut = Vcl_qsag_f2;
constexpr uint32_t id0 = 0xf0211d0f;
#else
#include "Vcl_qsag_f2_top.h"
using Dut = Vcl_qsag_f2_top;
constexpr uint32_t id0 = 0x1d0ff201;
#endif
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>

#include <stdexcept>
#include <string>
#include <vector>
using u64 = uint64_t;
using Words = std::vector<u64>;
#include "owner_fixture.hpp"
using Beat = std::array<uint32_t, 16>;
using Beats = std::vector<Beat>;
void expect(u64 got, u64 want, const char *where) {
    if (got != want) {
        std::cerr << where << ": got " << std::hex << got << ", expected " << want << std::dec
                  << "\n";
        throw std::runtime_error(where);
    }
}
struct Bus {
    Dut d;
    unsigned transactions = 0;
    u64 clocks = 0;
    void tick(unsigned n = 1) {
        d.eval();
        for (unsigned i = 0; i < n; i++) {
            d.clk_main_a0 = 1;
            d.eval();
            d.clk_main_a0 = 0;
            d.eval();
            clocks++;
        }
    }
    template <class F> void wait(F f, unsigned limit = 100000) {
        d.eval();
        while (!f()) {
            if (!limit--)
                throw std::runtime_error("bus timeout");
            tick();
        }
    }
    void start() {
        d.rst_main_n = 0;
        d.sh_cl_flr_assert = 0;
        tick(4);
        d.rst_main_n = 1;
        tick(4);
        expect(rd(0x28), 1, "startup scrub active");
        tick(33000);
        expect(rd(0x28), 0, "startup scrub done");
    }
    void wr(uint32_t a, uint32_t v, unsigned resp = 0, unsigned strobe = 15) {
        d.ocl_cl_awaddr = a;
        d.ocl_cl_wdata = v;
        d.ocl_cl_wstrb = strobe;
        auto aw = [&]() {
            d.ocl_cl_awvalid = 1;
            wait([&]() { return d.cl_ocl_awready; });
            tick();
            d.ocl_cl_awvalid = 0;
        };
        auto w = [&]() {
            d.ocl_cl_wvalid = 1;
            wait([&]() { return d.cl_ocl_wready; });
            tick();
            d.ocl_cl_wvalid = 0;
        };
        if (transactions++ % 2) {
            aw();
            w();
        } else {
            w();
            aw();
        }
        wait([&]() { return d.cl_ocl_bvalid; });
        expect(d.cl_ocl_bresp, resp, "OCL B");
        d.ocl_cl_bready = 1;
        tick();
        d.ocl_cl_bready = 0;
    }
    uint32_t rd(uint32_t a, unsigned resp = 0) {
        d.ocl_cl_araddr = a;
        d.ocl_cl_arvalid = 1;
        wait([&]() { return d.cl_ocl_arready; });
        tick();
        d.ocl_cl_arvalid = 0;
        wait([&]() { return d.cl_ocl_rvalid; });
        expect(d.cl_ocl_rresp, resp, "OCL R");
        auto val = d.cl_ocl_rdata;
        d.ocl_cl_rready = 1;
        tick();
        d.ocl_cl_rready = 0;
        return val;
    }
    void write(u64 a, const Beats &beats, u64 mask = ~0ULL, unsigned resp = 0) {
        d.sh_cl_dma_pcis_awvalid = 1;
        d.sh_cl_dma_pcis_awsize = 6;
        d.sh_cl_dma_pcis_awburst = 1;
        d.sh_cl_dma_pcis_awlen = beats.size() - 1;
        d.sh_cl_dma_pcis_awaddr = a;
        d.sh_cl_dma_pcis_awid = 0xb63e;
        wait([&]() { return d.cl_sh_dma_pcis_awready; });
        tick();
        d.sh_cl_dma_pcis_awvalid = 0;
        for (size_t i = 0; i < beats.size(); ++i) {
            for (unsigned j = 0; j < 16; j++)
                d.sh_cl_dma_pcis_wdata[j] = beats[i][j];
            d.sh_cl_dma_pcis_wstrb = mask;
            d.sh_cl_dma_pcis_wvalid = 1;
            d.sh_cl_dma_pcis_wlast = i + 1 == beats.size();
            wait([&]() { return d.cl_sh_dma_pcis_wready; });
            tick();
        }
        d.sh_cl_dma_pcis_wvalid = 0;
        wait([&]() { return d.cl_sh_dma_pcis_bvalid; });
        tick(2);
        expect(d.cl_sh_dma_pcis_bid, 0xb63e, "BID");
        expect(d.cl_sh_dma_pcis_bresp, resp, "PCIS B");
        d.sh_cl_dma_pcis_bready = 1;
        tick();
        d.sh_cl_dma_pcis_bready = 0;
    }
    Beats read(u64 a, size_t n, unsigned resp = 0) {
        d.sh_cl_dma_pcis_arvalid = 1;
        d.sh_cl_dma_pcis_arsize = 6;
        d.sh_cl_dma_pcis_arburst = 1;
        d.sh_cl_dma_pcis_araddr = a;
        d.sh_cl_dma_pcis_arlen = n - 1;
        d.sh_cl_dma_pcis_arid = 0xe540;
        wait([&]() { return d.cl_sh_dma_pcis_arready; });
        tick();
        d.sh_cl_dma_pcis_arvalid = 0;
        Beats out(n);
        for (size_t i = 0; i < n; ++i) {
            wait([&]() { return d.cl_sh_dma_pcis_rvalid; });
            for (unsigned j = 0; j < 16; j++)
                out[i][j] = d.cl_sh_dma_pcis_rdata[j];
            if (i % 7 == 0)
                tick(3);
            expect(d.cl_sh_dma_pcis_rvalid, 1, "RVALID while stalled");
            for (unsigned j = 0; j < 16; j++)
                expect(d.cl_sh_dma_pcis_rdata[j], out[i][j], "stalled RDATA");
            expect(d.cl_sh_dma_pcis_rid, 0xe540, "RID");
            expect(d.cl_sh_dma_pcis_rlast, i + 1 == n, "RLAST");
            expect(d.cl_sh_dma_pcis_rresp, resp, "PCIS R");
            d.sh_cl_dma_pcis_rready = 1;
            tick();
            d.sh_cl_dma_pcis_rready = 0;
            if (i + 1 < n)
                expect(d.cl_sh_dma_pcis_rvalid, 1, "read throughput");
        }
        return out;
    }
    void idle(int e) {
        wait([&]() { return rd(4096 * (e + 1) + 16) & 1; });
    }
    u64 direct(int e, unsigned op, unsigned idx = 0, unsigned addr = 0, u64 data = 0) {
        unsigned base = 4096 * (e + 1);
        idle(e);
        wr(base, data);
        wr(base + 4, data >> 32);
        wr(base + 8, (op << 21) | (idx << 16) | addr);
        wr(base + 12, 1);
        idle(e);
        u64 lo = rd(base + 24);
        return lo | u64(rd(base + 28)) << 32;
    }
    void trace(int e, const char *name, bool ring = false) {
        std::ifstream in(std::string("verif/") + name + ".hex");
        unsigned op, idx, addr, mode;
        u64 data, want, last = 0;
        Beats beats;
        unsigned count = 0;
        while (in >> std::hex >> op >> idx >> addr >> data >> mode >> want) {
            if (count % 4 == 0)
                beats.emplace_back(Beat{});
            auto k = 4 * (count++ % 4);
            beats.back()[k] = data;
            beats.back()[k + 1] = data >> 32;
            beats.back()[k + 2] = addr | (idx << 16) | (op << 21);
            if (op == 11 && mode == 1)
                last = want;
        }
        if (!count || !in.eof() || !last)
            throw std::runtime_error("invalid trace");
        // Repeat RD_STATUS to fill the last beat, preserving observable reply.
        for (unsigned i = count % 4; i && i < 4; i++)
            beats.back()[4 * i + 2] = 11 << 21;
        auto before = rd(4096 * (e + 1) + 32);
        unsigned base = (e << 20) + (ring ? 0x80000 : 0xc0000);
        write(base, beats);
        if (ring) {
            wr(0x10, base);
            wr(0x14, beats.size());
            wr(0x18, 1);
        }
        idle(e);
        expect(rd(4096 * (e + 1) + 32) - before, beats.size() * 4, "retired commands");
        expect(direct(e, 11), last, name);
        expect(rd(4096 * (e + 1) + 20), uint32_t(last), "live checks");
        expect((rd(4096 * (e + 1) + 16) >> 1) & 1, (last >> 32) ^ 1, "live fail");
    }
    unsigned vat = 0;
    unsigned vbase() const { return (vat + 1) * 65536; }
    uint8_t shift(unsigned byte, unsigned mode) {
        wr(vbase() + 4, (mode << 8) | byte);
        wait([&]() { return !(rd(vbase() + 8) & 1); });
        return rd(vbase() + 12);
    }
    u64 diag() {
        wr(vbase(), 1);
        shift(5, 0);
        shift(0, 0);
        u64 out = 0;
        for (int i = 0; i < 8; i++)
            out = (out << 8) | shift(0, 0);
        wr(vbase(), 0);
        return out;
    }
    u64 transfer_word(u64 w, unsigned mode) {
        u64 result = 0;
        for (unsigned i=0; i<8; i++)
            result |= u64(shift(uint8_t(w >> (i*8)), mode)) << (i*8);
        return result;
    }
    void submit(unsigned op, const Words &payload, unsigned flags, unsigned mode, unsigned bytes) {
        if (std::getenv("QSAG_TRACE_ASS2"))
            std::cout << "cycle " << clocks << " vat " << vat << " op " << op << "\n";
        if (bytes == ~0u) bytes = payload.size()*8;
        auto header = u64(0x51) | (u64(op) << 8) | (u64(flags) << 16) | (u64(bytes) << 24);
        wr(vbase(), 1);
        shift(mode << 6, 0);
        transfer_word(header, mode);
        for (auto w : payload)
            transfer_word(w, mode);
        wr(vbase(), 0);
    }
    Words collect(unsigned op, unsigned expected_error, unsigned mode) {
        // Poll at coarse intervals during long resident microprograms.
        for (unsigned poll = 0; (rd(vbase() + 8) & 6) != 6; poll++) {
            if (poll == 140000)
                throw std::runtime_error("resident timeout at vat " + std::to_string(vat) +
                                         " opcode " + std::to_string(op));
            tick(512);
        }
        wr(vbase(), 1);
        shift((mode << 6) | 2, 0);
        shift(0, 0);
        u64 h = transfer_word(0, mode);
        expect(h & 65535, 0x8051 | (op << 8), "response opcode");
        expect(h >> 48, expected_error, "resident error");
        Words out;
        for (unsigned i = 0; i < ((h >> 24) & 255); i += 8)
            out.push_back(transfer_word(0, mode));
        wr(vbase(), 0);
        return out;
    }
    Words cmd(unsigned op, const Words &payload = {}, unsigned flags = 0,
              unsigned expected_error = 0, unsigned mode = 2, unsigned bytes = ~0u) {
        submit(op, payload, flags, mode, bytes);
        return collect(op, expected_error, mode);
    }
};
// Line protocol for the qsag-accel integration test. Each operation goes
// through the same ready/valid drivers used by the standalone test.
static void serve_sdk(Bus &tb) {
    char op;
    u64 addr;
    while (std::cin >> op >> std::hex >> addr) {
        if (op == 'r') {
            auto v = tb.rd(addr);
            if ((addr & 0xffff) == 8 && addr >= 0x10000 && (v & 7) == 0)
                tb.tick(512);
            if ((addr & 0xfff) == 16 && addr >= 0x1000 && addr < 0x5000 && (v & 1) == 0)
                tb.tick(16384);
            if (addr == 0x28 && (v & 1)) tb.tick(128);
            std::cout << std::hex << v;
        } else if (op == 'f') {
            tb.d.sh_cl_flr_assert = 1;
            tb.tick(2);
            expect(tb.d.cl_sh_flr_done, 0, "FLR early acknowledge");
            tb.wait([&]() { return tb.d.cl_sh_flr_done; });
            tb.d.sh_cl_flr_assert = 0;
            tb.tick(1400);
            std::cout << "ok";
        } else if (op == 'w') {
            uint32_t value;
            std::cin >> value;
            tb.wr(addr, value);
            std::cout << "ok";
        } else {
            size_t count;
            std::cin >> count;
            if (!count || count > 64)
                throw std::runtime_error("SDK burst length");
            if (op == 'W') {
                Beats beats(count);
                for (auto &b : beats)
                    for (auto &w : b)
                        std::cin >> w;
                tb.write(addr, beats);
                std::cout << "ok";
            } else if (op == 'R') {
                for (const auto &b : tb.read(addr, count))
                    for (auto w : b)
                        std::cout << std::hex << w << ' ';
            } else
                throw std::runtime_error("SDK operation");
        }
        if (!std::cin)
            throw std::runtime_error("truncated SDK request");
        std::cout << std::endl;
    }
}
struct EpochResult {
    std::array<Key32, 3> identities, elements, endpoints;
};
static Key32 four_words(const Words &words, unsigned offset) {
    return {words.at(offset), words.at(offset+1), words.at(offset+2), words.at(offset+3)};
}
static EpochResult custody(Bus &tb, unsigned epoch) {
    EpochResult result{};
    std::array<Owner,3> owners{Owner(epoch,0), Owner(epoch,1), Owner(epoch,2)};
    using Batch = std::array<Words,3>;
    // Each vat has its own SPI link, ROM execution and response latch.
    // Submit all frames, then collect replies in the same vat order.
    auto batch = [&](unsigned op, const Batch &payloads, unsigned flags=0, unsigned error=0) {
        Batch replies;
        for (tb.vat=0; tb.vat<3; ++tb.vat) tb.submit(op, payloads[tb.vat], flags, 2, ~0u);
        for (tb.vat=0; tb.vat<3; ++tb.vat) replies[tb.vat] = tb.collect(op, error, 2);
        return replies;
    };
    batch(0x10, {});
    Batch pk;
    for (tb.vat=0; tb.vat<3; ++tb.vat) {
        expect((tb.diag() >> 24) & 7, 1, "blank vat");
        pk[tb.vat] = owners[tb.vat].payload(0x11);
    }
    auto enrol = batch(0x11, pk);
    Batch proofs;
    for (unsigned i=0; i<3; ++i) {
        expect(enrol[i].size(), 20, "ENROL length");
        auto &owner = owners[i];
        owner.id = four_words(enrol[i], 2);
        result.identities[i] = owner.id;
        expect(owner.id != Key32{}, 1, "nonzero identity");
        for (unsigned j=0; j<i; ++j) expect(owner.id != owners[j].id, 1, "distinct vat identity");
        proofs[i] = owner.payload(0x12, {enrol[i][0], enrol[i][1]});
    }
    batch(0x12, proofs);
    for (tb.vat=0; tb.vat<3; ++tb.vat) tb.wr(tb.vbase(), 2);
    tb.tick(10);
    for (tb.vat=0; tb.vat<3; ++tb.vat) tb.wr(tb.vbase(), 0);
    tb.tick(1100);
    auto boot = batch(0x10, {});
    auto authorize = [&](unsigned op, const Batch &replies) {
        Batch frames;
        for (unsigned i=0; i<3; ++i) {
            auto &r = replies[i];
            frames[i] = owners[i].payload(op, {r.at(0), r.at(1)}, r.at(2));
        }
        return frames;
    };
    for (unsigned i=0; i<3; ++i) {
        expect(boot[i].at(2), 1ULL << 32, "recovered generation");
        expect(four_words(boot[i],4) == owners[i].id, 1, "reconstructed identity");
    }
    auto lease = batch(0x15, authorize(0x15, boot));
    for (auto &r : lease) expect(r.at(2), 2ULL << 32, "lease generation");
    Batch images;
    images.fill(Owner::cap_load());
    batch(0x30, images, 1);
    auto gate = batch(0x16, authorize(0x16, lease));
    Batch requests;
    for (unsigned i=0; i<3; ++i) {
        expect(gate[i].at(2), owners[i].gate_record(), "gated generation and state");
        requests[i] = owners[i].payload(0x20);
    }
    batch(0x30, authorize(0x30, gate), 2);
    auto sigs = batch(0x20, requests);
    for (unsigned i=0; i<3; ++i) {
        expect(sigs[i].size(), 20, "CTH response length");
        expect(sigs[i][2], owners[i].gate_record() + (2ULL << 32), "CTH journal advance");
        auto elem = four_words(sigs[i],4), endpoint = four_words(sigs[i],8);
        expect(public_endpoint(elem) == endpoint, 1, "public CTH chain verification");
        result.elements[i] = elem;
        result.endpoints[i] = endpoint;
    }
    batch(0x20, requests, 0, 5);
    std::cout << "PASS epoch " << epoch
              << " all three vats ENROL COMMIT BOOT LEASE GATE capability/inline LOAD_CODE public CTH and replay rejection\n";
    return result;
}
int main(int argc, char **argv) {
    std::cout.setf(std::ios::unitbuf);
    // Separate owner process for the SDK test. No DUT is constructed on this path.
    if (argc == 12 && std::string(argv[1]) == "--owner") {
        auto arg = [&](unsigned i) { return std::stoull(argv[i], nullptr, 16); };
        Owner owner(arg(2), arg(3));
        owner.id = {arg(5),arg(6),arg(7),arg(8)};
        for (u64 w : owner.payload(arg(4), {arg(9),arg(10)}, arg(11)))
            std::cout << std::hex << w << ' ';
        return 0;
    }
    Bus tb;
    tb.start();
    if (argc == 2 && std::string(argv[1]) == "--sdk") {
        serve_sdk(tb);
        return 0;
    }
    expect(tb.d.cl_sh_id0, id0, "ID0");
    expect(tb.d.cl_sh_id1, 0x51534147, "ID1");
    expect(tb.rd(0), 0x51534147, "magic");
    expect(tb.rd(4), 0x20000, "ABI");
    expect(tb.rd(8), 2, "engines");
    expect(tb.rd(0x54), 9, "full entropy startup window");
    tb.rd(0x5000, 2);
    tb.wr(0x10, 1, 2, 1);
    Beats preload(64);
    for (unsigned i = 0; i < 64; i++)
        for (unsigned j = 0; j < 16; j++)
            preload[i][j] = (i + 1) * 0x123400U + j;
    for (int e = 0; e < 2; e++) {
        auto base = e << 20;
        tb.write(base, preload);
        expect(tb.read(base, 64) == preload, 1, "4 KiB roundtrip");
        tb.write(base, {Beat{}}, 0x55);
        expect(tb.read(base, 1)[0][0], preload[0][0] & 0xff00ff00, "byte strobes");
        expect(tb.direct(e, 4, 0, 8), u64(preload[1][1]) << 32 | preload[1][0], "NI/DMA coherence");
        tb.direct(e, 3, 0, 8, 0x9876543210abcdefULL);
        expect(tb.read(base + 64, 1)[0][0], 0x10abcdef, "DMA/NI coherence");
        tb.trace(e, "path");
        tb.trace(e, "sumcheck");
        tb.trace(e, "fold", true);
        tb.trace(e, "bit399");
        tb.direct(e, 1, 3, 0, 0x12345678);
        tb.direct(e, 0x31, 4, 0, 0xa552);
    }
    tb.write(0, Beats(256), ~0ULL, 2);
    tb.read(0, 256, 2);
    tb.read(1ULL << 32, 1, 2);
    tb.write(0xc0000, {Beat{}}, 1, 2);
    // Model app-PF resource4 stores: each descriptor arrives as 16 separate
    // dword writes with shifted strobes and an unaligned single-beat AWADDR.
    Beat staged{};
    staged[0] = 0xface;
    staged[2] = 1u << 21;
    staged[14] = 2u << 21;
    for (unsigned k = 0; k < 16; k++)
        tb.write(0x80000 + 4 * k, {staged}, 15ULL << (4 * k));
    tb.wr(0x10, 0x80000);
    tb.wr(0x14, 1);
    tb.wr(0x18, 1);
    tb.idle(0);
    expect(tb.rd(4096 + 24), 0xface, "CPU BAR4 strobes and ring publication");
    std::cout << "PASS OCL, PCIS stalls, full-page bursts, WSTRB, IDs, ring, both NI proof paths "
                 "and bit 399\n";
    for (tb.vat = 0; tb.vat < 3; tb.vat++) {
        expect(tb.diag(), 0x5a0300000000a552ULL, "READ_DIAG");
        auto id = tb.cmd(1, {}, 0, 0, tb.vat);
        expect(id.at(0), 0x3038314432535341ULL, "banner");
        expect(id.at(1), 0x4153533200000001ULL, "IDENT");
    }
    std::cout << "PASS all three pad links, x1/x4/x8 IDENT\n";
    auto initial = custody(tb, 0);
    tb.wr(0x28, 1);
    tb.tick(33000);
    tb.wr(0x50, 1, 2); // partial mailbox
    for (unsigned i = 0; i < 8; ++i) {
        tb.wr(0x30 + 4*i, 0x03020100u + 0x04040404u*i);
        expect(tb.rd(0x30 + 4*i, 2), 0, "seed readback denied");
    }
    tb.wr(0x50, 1);
    tb.tick(1300);
    expect(tb.rd(0x54), 0x10019, "seed commit and health");
    tb.wr(0x50, 1, 2); // immutable until global wipe
    auto seeded = custody(tb, 1);
    for (unsigned i=0; i<3; ++i) {
        expect(seeded.identities[i] != initial.identities[i], 1, "epoch identity rotation");
        expect(seeded.elements[i] != initial.elements[i], 1, "epoch chain rotation");
        expect(seeded.endpoints[i] != initial.endpoints[i], 1, "epoch endpoint rotation");
    }
    // Interrupt a long NI command and an incomplete OCL write.
    tb.direct(0, 8, 1);
    tb.wr(4096, 100000);
    tb.wr(4100, 0);
    tb.wr(4104, 0x2au << 21);
    tb.wr(4108, 1);
    expect(tb.rd(4112) & 1, 0, "in-flight FOLD");
    tb.d.ocl_cl_awaddr = 0x10000;
    tb.d.ocl_cl_awvalid = 1;
    tb.tick();
    tb.d.ocl_cl_awvalid = 0;
    tb.d.sh_cl_flr_assert = 1;
    tb.d.eval();
    expect(tb.d.cl_sh_dma_pcis_awready, 0, "FLR admission");
    tb.tick(2);
    expect(tb.d.cl_sh_flr_done, 0, "FLR early ACK");
    tb.wait([&]() { return tb.d.cl_sh_flr_done; });
    tb.d.sh_cl_flr_assert = 0;
    tb.tick(1400);
    expect(tb.rd(0x54), 9, "FLR clears seed and epoch");
    for (int e = 0; e < 2; e++) {
        expect(tb.direct(e, 11), 1ULL << 32, "FLR status");
        expect(tb.direct(e, 2, 3), 0, "FLR state");
        expect(tb.direct(e, 0x32, 4), 0, "FLR Keccak");
        expect(tb.read(e << 20, 64) == Beats(64), 1, "FLR SRAM");
    }
    for (tb.vat = 0; tb.vat < 3; tb.vat++) {
        expect(tb.diag(), 0x5a0300000000a552ULL, "FLR DIAG");
        tb.cmd(0x10);
        expect((tb.diag() >> 24) & 7, 1, "FLR anchor erased");
    }
    tb.vat = 1;
    tb.wr(tb.vbase(), 4);
    tb.wait([&]() { return ((tb.rd(tb.vbase() + 8) >> 4) & 3) == 3; }, 8);
    tb.vat = 0;
    expect((tb.rd(tb.vbase() + 8) >> 4) & 3, 0, "tamper isolation");
    tb.direct(0, 1, 0, 0, 0xa55a);
    tb.wr(0x28, 1);
    expect(tb.rd(0x28), 1, "software zeroize");
    tb.write(0, {Beat{}}, ~0ULL, 2);
    tb.read(0, 1, 2);
    // W arrives under lock and AW only after unlock. The old WDATA must
    // neither be retained nor qualify as a word of the next seed mailbox.
    tb.d.ocl_cl_wdata = 0x11223344;
    tb.d.ocl_cl_wstrb = 15;
    tb.d.ocl_cl_wvalid = 1;
    tb.wait([&]() { return tb.d.cl_ocl_wready; });
    tb.tick();
    tb.d.ocl_cl_wvalid = 0;
    tb.tick(33000);
    tb.d.ocl_cl_awaddr = 0x30;
    tb.d.ocl_cl_awvalid = 1;
    tb.wait([&]() { return tb.d.cl_ocl_awready; });
    tb.tick();
    tb.d.ocl_cl_awvalid = 0;
    tb.wait([&]() { return tb.d.cl_ocl_bvalid; });
    expect(tb.d.cl_ocl_bresp, 2, "split seed write rejected across scrub");
    tb.d.ocl_cl_bready = 1;
    tb.tick();
    tb.d.ocl_cl_bready = 0;
    for (unsigned i = 1; i < 8; ++i) tb.wr(0x30 + 4*i, i);
    tb.wr(0x50, 1, 2);
    expect(tb.direct(0, 2), 0, "software wipe clears state");
    std::cout << "PASS FLR all five engines and anchor vaults in " << tb.clocks << " clocks\n";
}
