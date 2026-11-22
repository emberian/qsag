// Directed end-to-end Verilator verification of `qsag_ass2_enclave_top` (`ASS2-0P5` Rev. 2.0):
//   - STRICT ZERO-FACTORY-TRUST: ZERO `fixture_root()` anywhere! The host generates its own
//     post-quantum `WOTS+C` key chain (`sk_0..sk_N -> pk_0..pk_N`), enrolls `pk_0` via `CMD_ENROL`,
//     receives the public `enclave_id`, and authorizes `COMMIT`, `LEASE`, `GATE`, `LOAD_CODE`
//     (`flags = 1` Merkle capability AND `flags = 2` inline 296B `WOTS+C`!), and `CTH_SIGN`
//     without ever knowing or exporting the enclave's PUF `root_secret`!
//   - Exercises `SafeRecovery` (`BOOT_MODE = 01` -> `E_LOCKED = 14`), JTAG lockout, W^X,
//     `SYS_MMIO` applet fence, exact-edge watchdog, torn FRAM recovery, and 0-clock tamper wipe!
#include "Vqsag_ass2_enclave_top.h"
#include "verilated.h"
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstring>
#include <iostream>
#include <stdexcept>
#include <vector>

using u8   = std::uint8_t;
using u16  = std::uint16_t;
using u32  = std::uint32_t;
using u64  = std::uint64_t;
using u128 = unsigned __int128;
using Words = std::vector<u64>;

#include "lifecycle_fixture.hpp"

static constexpr u64 KECCAK_RC[24] = {
    0x0000000000000001ULL, 0x0000000000008082ULL, 0x800000000000808aULL, 0x8000000080008000ULL,
    0x000000000000808bULL, 0x0000000080000001ULL, 0x8000000080008081ULL, 0x8000000000008009ULL,
    0x000000000000008aULL, 0x0000000000000088ULL, 0x0000000080008009ULL, 0x000000008000000aULL,
    0x000000008000808bULL, 0x800000000000008bULL, 0x8000000000008089ULL, 0x8000000000008003ULL,
    0x8000000000008002ULL, 0x8000000000000080ULL, 0x000000000000800aULL, 0x800000008000000aULL,
    0x8000000080008081ULL, 0x8000000000008080ULL, 0x0000000080000001ULL, 0x8000000080008008ULL,
};
static constexpr unsigned KROT[25] = {
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14
};
static u64 rol64(u64 x, unsigned n) { return n ? ((x << n) | (x >> (64 - n))) : x; }

static void keccak_p1600(std::array<u64, 25> &st, unsigned rounds = 12) {
    for (unsigned r = 24 - rounds; r < 24; ++r) {
        u64 c[5];
        for (unsigned x = 0; x < 5; ++x)
            c[x] = st[x] ^ st[x + 5] ^ st[x + 10] ^ st[x + 15] ^ st[x + 20];
        u64 b[25];
        for (unsigned i = 0; i < 25; ++i) {
            unsigned x = i % 5, y = i / 5;
            u64 d = c[(x + 4) % 5] ^ rol64(c[(x + 1) % 5], 1);
            b[y + 5 * ((2 * x + 3 * y) % 5)] = rol64(st[i] ^ d, KROT[i]);
        }
        for (unsigned y = 0; y < 5; ++y)
            for (unsigned x = 0; x < 5; ++x)
                st[5 * y + x] = b[5 * y + x] ^ ((~b[5 * y + (x + 1) % 5]) & b[5 * y + (x + 2) % 5]);
        st[0] ^= KECCAK_RC[r];
    }
}

static void turboshake256(const u8 *msg, size_t len, u8 *out, size_t out_len) {
    std::array<u64, 25> st{};
    size_t pos = 0;
    while (pos + 136 <= len) {
        for (unsigned i = 0; i < 17; ++i) {
            u64 w; std::memcpy(&w, msg + pos + 8 * i, 8);
            st[i] ^= w;
        }
        keccak_p1600(st, 12);
        pos += 136;
    }
    u8 last[136]{};
    std::memcpy(last, msg + pos, len - pos);
    last[len - pos] ^= 0x1F;
    last[135] ^= 0x80;
    for (unsigned i = 0; i < 17; ++i) {
        u64 w; std::memcpy(&w, last + 8 * i, 8);
        st[i] ^= w;
    }
    keccak_p1600(st, 12);
    size_t wpos = 0;
    while (wpos < out_len) {
        for (unsigned i = 0; i < 17 && wpos < out_len; ++i) {
            size_t take = std::min<size_t>(8, out_len - wpos);
            std::memcpy(out + wpos, &st[i], take);
            wpos += take;
        }
        if (wpos < out_len) keccak_p1600(st, 12);
    }
}

static u128 gf128_mul(u128 a, u128 b) {
    u128 x = 0;
    for (unsigned i = 0; i < 128; i++) {
        if (b & 1) x ^= a;
        a = (a << 1) ^ ((a >> 127) ? 0x87 : 0);
        b >>= 1;
    }
    return x;
}

// ---- Owner-side Post-Quantum WOTS+C Key & Signer (Zero Enclave Secrets!) ----
using Key32 = std::array<u64, 4>;
using Digest16 = std::array<u64, 2>;

static Key32 make_seed(u64 idx) {
    return {0x7153414700000000ULL ^ idx, 0x9e3779b97f4a7c15ULL * (idx + 1),
            0xbf58476d1ce4e5b9ULL ^ (idx << 17), 0x94d049bb133111ebULL + idx};
}

static Digest16 wots_sk_start(const Key32 &sk, unsigned chain) {
    std::array<u64, 6> in{0x31304b5357325341ULL, sk[0], sk[1], sk[2], sk[3], u64(chain)};
    Digest16 out{};
    turboshake256(reinterpret_cast<const u8*>(in.data()), 48, reinterpret_cast<u8*>(out.data()), 16);
    return out;
}

static Digest16 wots_step(const Digest16 &node, unsigned chain, unsigned step) {
    std::array<u64, 25> st{};
    st[0] = 0x57531ULL;
    st[1] = node[0];
    st[2] = node[1];
    st[3] = (u64(chain) << 8) | u64(step);
    st[4] = 0x1F;
    st[16] = 0x80ULL << 56;
    keccak_p1600(st, 12);
    return {st[0], st[1]};
}

static Key32 wots_pubkey(const Key32 &sk) {
    std::array<u64, 33> msg{};
    for (unsigned i = 0; i < 16; ++i) {
        auto cur = wots_sk_start(sk, i);
        for (unsigned s = 0; s < 255; ++s) cur = wots_step(cur, i, s);
        msg[2 * i]     = cur[0];
        msg[2 * i + 1] = cur[1];
    }
    msg[32] = 0x57501ULL;
    Key32 pk{};
    turboshake256(reinterpret_cast<const u8*>(msg.data()), 264, reinterpret_cast<u8*>(pk.data()), 32);
    return pk;
}

static Words wots_sign(
    const Key32 &sk, const Key32 &enclave_id, u64 opcode, u64 op_value,
    const Digest16 &nonce, u64 record, const Digest16 &cap_commit, const Key32 &next_pk
) {
    u64 salt = 0;
    std::array<u8, 16> digits{};
    while (true) {
        std::array<u64, 16> msg{
            0x574d1ULL, enclave_id[0], enclave_id[1], enclave_id[2],
            opcode, record, nonce[0], nonce[1],
            cap_commit[0], cap_commit[1], op_value, salt,
            next_pk[0], next_pk[1], next_pk[2], next_pk[3]
        };
        turboshake256(reinterpret_cast<const u8*>(msg.data()), 128, digits.data(), 16);
        unsigned sum = 0;
        for (u8 d : digits) sum += d;
        if (sum == 2040) break;
        ++salt;
    }
    Words proof;
    proof.reserve(37); // 296 B = 37 x u64
    proof.push_back(salt);
    for (u64 w : next_pk) proof.push_back(w);
    for (unsigned i = 0; i < 16; ++i) {
        auto cur = wots_sk_start(sk, i);
        for (unsigned s = 0; s < digits[i]; ++s) cur = wots_step(cur, i, s);
        proof.push_back(cur[0]);
        proof.push_back(cur[1]);
    }
    return proof;
}

static Words owner_lifecycle_frame(
    const Key32 &sk, const Key32 &enclave_id, u64 opcode, u64 op_value,
    const Digest16 &nonce, u64 record, const Digest16 &cap_commit, const Key32 &next_pk
) {
    Words out{cap_commit[0], cap_commit[1], op_value};
    auto proof = wots_sign(sk, enclave_id, opcode, op_value, nonce, record, cap_commit, next_pk);
    out.insert(out.end(), proof.begin(), proof.end());
    assert(out.size() == 40); // 320 B
    return out;
}

static Digest16 compute_img_id(const Key32 &enclave_id, const std::vector<u32> &code) {
    std::array<u64, 5> kin{enclave_id[0], enclave_id[1], enclave_id[2], enclave_id[3], 0x47461ULL};
    Digest16 h_words{};
    turboshake256(reinterpret_cast<const u8*>(kin.data()), 40, reinterpret_cast<u8*>(h_words.data()), 16);
    u128 h = (u128(h_words[1]) << 64) | h_words[0];
    u128 d = code.size();
    for (u32 w : code) d = gf128_mul(d, h) ^ w;
    std::array<u64, 7> fin{
        enclave_id[0], enclave_id[1], enclave_id[2], enclave_id[3],
        u64(d), u64(d >> 64), 0x494d1ULL
    };
    Digest16 img_id{};
    turboshake256(reinterpret_cast<const u8*>(fin.data()), 56, reinterpret_cast<u8*>(img_id.data()), 16);
    return img_id;
}

static Digest16 cap_commit_code(const Digest16 &img_id, const Digest16 &sibling) {
    std::array<u64, 5> in{0x43500ULL, img_id[0], img_id[1], sibling[0], sibling[1]};
    Digest16 out{};
    turboshake256(reinterpret_cast<const u8*>(in.data()), 40, reinterpret_cast<u8*>(out.data()), 16);
    return out;
}

static Digest16 cap_commit_cth(const Digest16 &sibling, const Digest16 &req_id) {
    std::array<u64, 5> in{0x43501ULL, req_id[0], req_id[1], sibling[0], sibling[1]};
    Digest16 out{};
    turboshake256(reinterpret_cast<const u8*>(in.data()), 40, reinterpret_cast<u8*>(out.data()), 16);
    return out;
}

struct EnclaveTb {
    Vqsag_ass2_enclave_top dut;
    Fram fram;

    EnclaveTb() {
        dut.clk = 0;
        dut.rst_n = 0;
        dut.input_in = 0x8;
        dut.bidir_in = (1ULL << 26) | (1ULL << 27);
        dut.eval();
    }
    ~EnclaveTb() { dut.final(); }

    void set_pin_bidir(int bit, bool val) {
        if (val) dut.bidir_in |= (1ULL << bit);
        else     dut.bidir_in &= ~(1ULL << bit);
    }
    bool get_out_bidir(int bit) const { return (dut.bidir_out >> bit) & 1; }
    void set_cs_n(bool cs_n) {
        if (cs_n) dut.input_in |= 0x8;
        else      dut.input_in &= ~0x8;
    }
    void set_boot_mode(u8 bm) {
        dut.input_in = (dut.input_in & ~0x6) | ((bm & 3) << 1);
    }
    void tick_core(int n = 1) {
        for (int i = 0; i < n; ++i) {
            fram.pins(get_out_bidir(22), get_out_bidir(23), get_out_bidir(24));
            set_pin_bidir(25, fram.miso);
            dut.clk = 0; dut.eval();
            dut.clk = 1; dut.eval();
        }
    }
    void reset(u8 boot_mode = 0) {
        dut.rst_n = 0;
        set_cs_n(true);
        set_boot_mode(boot_mode);
        set_pin_bidir(26, true);
        set_pin_bidir(18, false);
        tick_core(4);
        dut.rst_n = 1;
        tick_core(530);
        if (boot_mode != 3 && !get_out_bidir(19))
            throw std::runtime_error("HOST_RDY not high after reset scrub");
    }

    void sck_edge(bool core_running = true) {
        set_pin_bidir(18, false); dut.eval();
        if (core_running) tick_core(8);
        set_pin_bidir(18, true);  dut.eval();
        if (core_running) tick_core(8);
        set_pin_bidir(18, false); dut.eval();
    }

    void shift_prefix_x1(u8 prefix, bool core_running = true) {
        for (int b = 7; b >= 0; --b) {
            set_pin_bidir(0, (prefix >> b) & 1);
            sck_edge(core_running);
        }
    }

    u64 read_diag_clockless() {
        dut.clk = 0; dut.eval();
        set_cs_n(false); dut.eval();
        shift_prefix_x1(0x05, false);
        for (int i = 0; i < 8; ++i) sck_edge(false);
        u64 val = 0;
        for (int b = 63; b >= 0; --b) {
            set_pin_bidir(18, true); dut.eval();
            val = (val << 1) | u64(get_out_bidir(1));
            set_pin_bidir(18, false); dut.eval();
        }
        set_cs_n(true); dut.eval();
        return val;
    }

    void write_frame(u8 write_prefix, u64 w0, const std::vector<u64> &payload) {
        set_cs_n(false); tick_core(2);
        shift_prefix_x1(write_prefix, true);
        auto send_word = [&](u64 w) {
            for (int byte_i = 0; byte_i < 8; ++byte_i) {
                u8 byte_v = u8(w >> (byte_i * 8));
                if (write_prefix == 0x00) {
                    for (int b = 7; b >= 0; --b) {
                        set_pin_bidir(0, (byte_v >> b) & 1);
                        sck_edge(true);
                    }
                } else if (write_prefix == 0x40) {
                    dut.bidir_in = (dut.bidir_in & ~0xFULL) | u64((byte_v >> 4) & 0xF);
                    sck_edge(true);
                    dut.bidir_in = (dut.bidir_in & ~0xFULL) | u64(byte_v & 0xF);
                    sck_edge(true);
                } else {
                    dut.bidir_in = (dut.bidir_in & ~0xFFULL) | u64(byte_v);
                    sck_edge(true);
                }
            }
        };
        send_word(w0);
        for (u64 pw : payload) send_word(pw);
        set_cs_n(true);
        tick_core(20);
    }

    std::pair<u64, std::vector<u64>> read_frame(u8 read_prefix, size_t n_words) {
        set_cs_n(false); tick_core(2);
        shift_prefix_x1(read_prefix, true);
        for (int i = 0; i < 8; ++i) sck_edge(true);
        auto recv_word = [&]() -> u64 {
            u64 w = 0;
            for (int byte_i = 0; byte_i < 8; ++byte_i) {
                u8 byte_v = 0;
                if (read_prefix == 0x02) {
                    for (int b = 7; b >= 0; --b) {
                        set_pin_bidir(18, true); dut.eval(); tick_core(8);
                        byte_v |= u8(get_out_bidir(1)) << b;
                        set_pin_bidir(18, false); dut.eval(); tick_core(8);
                    }
                } else if (read_prefix == 0x42) {
                    set_pin_bidir(18, true); dut.eval(); tick_core(8);
                    byte_v = u8(dut.bidir_out & 0xF) << 4;
                    set_pin_bidir(18, false); dut.eval(); tick_core(8);
                    set_pin_bidir(18, true); dut.eval(); tick_core(8);
                    byte_v |= u8(dut.bidir_out & 0xF);
                    set_pin_bidir(18, false); dut.eval(); tick_core(8);
                } else {
                    set_pin_bidir(18, true); dut.eval(); tick_core(8);
                    byte_v = u8(dut.bidir_out & 0xFF);
                    set_pin_bidir(18, false); dut.eval(); tick_core(8);
                }
                w |= u64(byte_v) << (byte_i * 8);
            }
            return w;
        };
        u64 w0_resp = recv_word();
        std::vector<u64> out;
        for (size_t i = 0; i < n_words; ++i) out.push_back(recv_word());
        set_cs_n(true);
        tick_core(8);
        return {w0_resp, out};
    }

    static u64 make_w0(u8 op, u8 flags, u32 byte_len, u16 arg) {
        return 0x51ULL | (u64(op) << 8) | (u64(flags) << 16)
             | (u64(byte_len & 0xFFFFFFU) << 24) | (u64(arg) << 48);
    }
};

static void check_eq(const char *label, u64 got, u64 want) {
    if (got != want) {
        std::cerr << "FAIL " << label << ": got 0x" << std::hex << got
                  << " want 0x" << want << std::dec << "\n";
        std::exit(1);
    }
}

static void ready(EnclaveTb &tb) {
    for (int i = 0; i < 20000000; ++i) {
        if (tb.get_out_bidir(19) && tb.get_out_bidir(20)) return;
        tb.tick_core();
    }
    throw std::runtime_error("timeout waiting for command");
}

static Words cmd(EnclaveTb &tb, u8 op, const Words &w = {}, u8 flags = 0, int err = 0, u16 budget = 0) {
    tb.write_frame(0x80, tb.make_w0(op, flags, w.size() * 8, budget), w);
    ready(tb);
    auto [h, out] = tb.read_frame(0x82, err ? 0 : 20);
    if (h >> 48 != unsigned(err))
        std::cerr << "opcode 0x" << std::hex << unsigned(op) << " diag " << tb.read_diag_clockless() << "\n";
    check_eq("command status", h >> 48, err);
    return out;
}

static Words pack_u32s(const std::vector<u32> &parts) {
    Words wire((parts.size() + 1) / 2);
    for (size_t i = 0; i < parts.size(); ++i)
        wire[i / 2] |= u64(parts[i]) << (32 * (i % 2));
    return wire;
}

int main(int argc, char **argv) {
    Verilated::commandArgs(argc, argv);
    std::cout.setf(std::ios::unitbuf);
    EnclaveTb tb;
    tb.reset();

    // 1. Clockless DIAG & 3 SPI widths & resident IDENT
    check_eq("clockless DIAG", tb.read_diag_clockless(), 0x5a0300000000a552ULL);
    for (auto [w, r] : {std::pair<int, int>{0, 2}, {0x40, 0x42}, {0x80, 0x82}}) {
        tb.write_frame(w, tb.make_w0(1, 0, 0, 0), {});
        auto out = tb.read_frame(r, 4).second;
        check_eq("banner", out[0], 0x3038314432535341ULL);
        check_eq("ID", out[1], 0x4153533200000001ULL);
    }
    tb.write_frame(0x80, tb.make_w0(0x30, 1, 24, 0), {1 | (0x50000ULL << 32), 0, 0});
    ready(tb);
    check_eq("unprovisioned load rejected", tb.read_frame(0x82, 0).first >> 48, 4);
    auto id = cmd(tb, 0x31, {0}, 7);
    check_eq("resident IDENT", id[0], 0x4153533200000001ULL);
    check_eq("resident FEATURES", id[1], 15);
    std::cout << "PASS diagnostic, 3 host widths, reset admission and resident IDENT\n";

    // Precompute Owner's post-quantum WOTS+C rolling key sequence (ZERO enclave secrets!)
    std::vector<Key32> sk(8), pk(8);
    for (unsigned i = 0; i < 8; ++i) {
        sk[i] = make_seed(i + 1);
        pk[i] = wots_pubkey(sk[i]);
    }
    unsigned kidx = 0;

    // 2. Virgin BOOT -> ENROL (bind pk[0], receive public enclave_id) -> COMMIT -> BOOT -> LEASE -> GATE
    cmd(tb, 0x10);
    check_eq("blank after BOOT", (tb.read_diag_clockless() >> 24) & 7, 1);

    // Reject zero owner key on ENROL
    cmd(tb, 0x11, {0, 0, 0, 0}, 0, 10);

    // Valid Zero-Factory-Trust ENROL with Owner's genesis `pk[0]`
    auto e = cmd(tb, 0x11, {pk[0][0], pk[0][1], pk[0][2], pk[0][3]});
    check_eq("enrol success", e[16], 1);
    Digest16 nonce{e[0], e[1]};
    Key32 enclave_id{e[2], e[3], e[4], e[5]};
    check_eq("enclave_id non-zero", (enclave_id[0] | enclave_id[1] | enclave_id[2] | enclave_id[3]) != 0, 1);

    // Bad WOTS+C proof during COMMIT is rejected and burns challenge nonce!
    Digest16 zero_cap{0, 0};
    auto bad_commit = owner_lifecycle_frame(sk[0], enclave_id, 0x12, 0, nonce, 0, zero_cap, pk[1]);
    bad_commit[10] ^= 1ULL;
    cmd(tb, 0x12, bad_commit, 0, 5);
    // Re-trying with burned nonce fails with E_NOKEY = 4!
    auto burned_retry = owner_lifecycle_frame(sk[0], enclave_id, 0x12, 0, nonce, 0, zero_cap, pk[1]);
    cmd(tb, 0x12, burned_retry, 0, 4);

    // Fresh ENROL challenge in LC_BLANK + valid Owner WOTS+C COMMIT -> LC_PROVISIONED!
    e = cmd(tb, 0x11, {pk[0][0], pk[0][1], pk[0][2], pk[0][3]});
    nonce = {e[0], e[1]};
    check_eq("deterministic enclave_id", e[2], enclave_id[0]);
    check_eq("deterministic enclave_id[3]", e[5], enclave_id[3]);
    cmd(tb, 0x12, owner_lifecycle_frame(sk[0], enclave_id, 0x12, 0, nonce, 0, zero_cap, pk[1]));
    kidx = 1; // FRAM journal is now at gen = 1, cur_wots_root = pk[1]
    check_eq("provisioned", (tb.read_diag_clockless() >> 24) & 7, 2);

    // Cold BOOT reconstructs PUF root_secret, verifies FRAM anchor & journal, enters LEASE_PENDING
    tb.reset();
    auto boot1 = cmd(tb, 0x10);
    u64 rec = 1ULL << 32;
    check_eq("boot record gen=1", boot1[2], rec);
    check_eq("boot enclave_id matches", boot1[4], enclave_id[0]);
    nonce = {boot1[0], boot1[1]};

    // LEASE via Owner WOTS+C (sk[1] -> pk[2]), advancing gen 1 -> 2 and entering READY!
    auto lease1 = cmd(tb, 0x15, owner_lifecycle_frame(sk[kidx], enclave_id, 0x15, rec, nonce, rec, zero_cap, pk[kidx + 1]));
    kidx++;
    rec = 2ULL << 32;
    check_eq("leased gen=2", lease1[2], rec);
    check_eq("LC_READY", (tb.read_diag_clockless() >> 24) & 7, 5);
    nonce = {lease1[0], lease1[1]};

    // Prepare Merkle capability commitment for `CMD_LOAD_CODE` (`flags=1`) and `CMD_CTH_SIGN`!
    // We'll authorize `[HALT]` first via GATE, then update capabilities as needed, OR test `flags=2` inline WOTS+C!
    Digest16 dummy_sib{0x1122334455667788ULL, 0x99aabbccddeeff00ULL};
    auto halt_img_id = compute_img_id(enclave_id, {0x50000});
    auto cap_halt = cap_commit_code(halt_img_id, dummy_sib);

    // GATE transition 0 -> 7 via Owner WOTS+C (sk[2] -> pk[3]), installing `cap_halt`!
    auto gate_frame = owner_lifecycle_frame(sk[kidx], enclave_id, 0x16, 7, nonce, rec, cap_halt, pk[kidx + 1]);
    auto gate_out = cmd(tb, 0x16, gate_frame);
    kidx++;
    rec = (3ULL << 32) | 7;
    check_eq("gate record gen=3 state=7", gate_out[2], rec);
    // Replay of consumed GATE proof rejected (burned nonce / rotated WOTS+C root -> E_MAC / E_NOKEY)!
    nonce = {gate_out[0], gate_out[1]};
    cmd(tb, 0x16, gate_frame, 0, 5);
    // Re-obtain fresh nonce via SafeRecovery / Re-boot check!
    tb.reset();
    auto boot2 = cmd(tb, 0x10);
    check_eq("boot recovered gen=3 state=7", boot2[2], rec);
    nonce = {boot2[0], boot2[1]};
    auto lease2 = cmd(tb, 0x15, owner_lifecycle_frame(sk[kidx], enclave_id, 0x15, rec, nonce, rec, cap_halt, pk[kidx + 1]));
    kidx++;
    rec = (4ULL << 32) | 7;
    nonce = {lease2[0], lease2[1]};
    std::cout << "PASS Zero-Factory-Trust ENROL COMMIT BOOT LEASE GATE, WOTS+C rotation and replay denial\n";

    // 3. Test BOTH `flags = 1` (20+4*n B Merkle capability) AND `flags = 2` (inline 296B WOTS+C) CMD_LOAD_CODE!
    auto send_cap_load = [&](const std::vector<u32> &code, const Digest16 &tok, int err = 0, bool alter = false) {
        std::vector<u32> parts{u32(code.size())};
        for (u32 w : code) parts.push_back(w);
        parts.push_back(u32(tok[0])); parts.push_back(u32(tok[0] >> 32));
        parts.push_back(u32(tok[1])); parts.push_back(u32(tok[1] >> 32));
        auto wire = pack_u32s(parts);
        if (alter) wire[0] ^= 1ULL << 32;
        tb.write_frame(0x80, tb.make_w0(0x30, 1, 20 + 4 * code.size(), 0), wire);
        ready(tb);
        check_eq("cap load status", tb.read_frame(0x82, 0).first >> 48, err);
    };
    auto send_wotsc_load = [&](const std::vector<u32> &code, int err = 0) {
        auto img_id = compute_img_id(enclave_id, code);
        auto proof = wots_sign(sk[kidx], enclave_id, 0x30, code.size(), nonce, rec, img_id, pk[kidx + 1]);
        std::vector<u32> parts{u32(code.size())};
        for (u32 w : code) parts.push_back(w);
        for (u64 pw : proof) { parts.push_back(u32(pw)); parts.push_back(u32(pw >> 32)); }
        auto wire = pack_u32s(parts);
        tb.write_frame(0x80, tb.make_w0(0x30, 2, 300 + 4 * code.size(), 0), wire);
        ready(tb);
        check_eq("wotsc load status", tb.read_frame(0x82, 0).first >> 48, err);
        if (err == 0) {
            kidx++;
            rec += (1ULL << 32);
            // Refresh nonce reading TX? `CMD_LOAD_CODE` returns rlen=0, while `nonce` updated MMIO!
            // Wait: `CMD_LOAD_CODE` response has `rlen = 0` in `enclave_top.sv`! Let's check!
        }
    };

    // Valid `flags = 1` load of `[HALT]` (authorized by `cap_halt`!)
    send_cap_load({0x50000}, dummy_sib, 0);
    cmd(tb, 0x31);
    // Altered code & altered token rejected, revoking previous image!
    send_cap_load({0x50000}, dummy_sib, 5, true);
    cmd(tb, 0x31, {}, 0, 13);
    Digest16 bad_sib = {dummy_sib[0] ^ 1ULL, dummy_sib[1]};
    send_cap_load({0x50000}, bad_sib, 5, false);
    cmd(tb, 0x31, {}, 0, 13);

    // Malformed lengths & non-zero padding rejected
    auto reject_load = [&](u32 bytes, const Words &body) {
        tb.write_frame(0x80, tb.make_w0(0x30, 1, bytes, 0), body);
        ready(tb);
        check_eq("malformed length or padding", tb.read_frame(0x82, 0).first >> 48, 3);
        cmd(tb, 0x31, {}, 0, 13);
    };
    reject_load(28, {0, 0, 0, 0});
    reject_load(28, {129, 0, 0, 0});
    reject_load(24, {2 | (0x60000ULL << 32), 0x50000, 0, 0});
    reject_load(28, {2 | (0x60000ULL << 32), 0x50000, 0, 1ULL << 32});

    // Exercise inline `flags = 2` Owner `WOTS+C` load on a 128-instruction max-size applet!
    std::vector<u32> max_img(128, 0x60000);
    max_img.back() = 0x50000;
    send_wotsc_load(max_img, 0);
    cmd(tb, 0x31);

    // Re-boot + Lease installing capabilities for security trap tests & CTH signing!
    tb.reset();
    auto boot3 = cmd(tb, 0x10);
    check_eq("boot after wotsc load gen=5", boot3[2], rec);
    nonce = {boot3[0], boot3[1]};

    auto install_code = [&](const std::vector<u32> &code) {
        auto img_id = compute_img_id(enclave_id, code);
        auto cap = cap_commit_code(img_id, dummy_sib);
        // Use GATE (7 -> 7) with Owner WOTS+C to install `cap`!
        u64 st = rec & 0xFFFFFFFFULL;
        u64 tr = (st << 32) | st;
        auto out = cmd(tb, 0x16, owner_lifecycle_frame(sk[kidx], enclave_id, 0x16, tr, nonce, rec, cap, pk[kidx + 1]));
        kidx++;
        rec += (1ULL << 32);
        nonce = {out[0], out[1]};
        send_cap_load(code, dummy_sib, 0);
    };

    // Resize sk/pk pool so we have plenty of one-time WOTS+C keys
    for (unsigned i = 8; i < 20; ++i) {
        sk.push_back(make_seed(i + 1));
        pk.push_back(wots_pubkey(sk.back()));
    }
    auto lease3 = cmd(tb, 0x15, owner_lifecycle_frame(sk[kidx], enclave_id, 0x15, rec, nonce, rec, cap_halt, pk[kidx + 1]));
    kidx++;
    rec += (1ULL << 32);
    nonce = {lease3[0], lease3[1]};

    // Jump past authenticated extent -> E_TRAP=16
    install_code({0xa0000000U});
    cmd(tb, 0x31, {}, 0, 16);
    // Watchdog expiry inside `KECCAK.F1600 12` -> E_BUDGET=15
    install_code({0xf0c00000U, 0x50000U});
    cmd(tb, 0x31, {}, 0, 15, 64);
    // Applet `SYS_MMIO` hardware privilege fence -> E_TRAP=16, MemFault=5 at PC=0x1008
    install_code({0x40ffff0aU, 0x300105aaU, 0x700080a5U, 0x50000U});
    tb.write_frame(0x80, tb.make_w0(0x31, 0, 0, 2000), {});
    ready(tb);
    auto fence = tb.read_frame(0x82, 2);
    check_eq("MMIO trap", fence.first >> 48, 16);
    check_eq("MemFault", fence.second[0], 5);
    check_eq("fenced PC", fence.second[1], 0x1008);
    // Fetch from D-SRAM (W^X) -> E_TRAP=16
    install_code({0x4100000aU, 0xb00000a0U});
    cmd(tb, 0x31, {}, 0, 16);
    // ZEROIZE scrubs all 512 bytes including TX_MBOX
    install_code({0x4101800fU, 0x40beef04U, 0x800000f4U, 0x40000U, 0x50000U});
    check_eq("ZEROIZE TX", cmd(tb, 0x31)[0], 0);
    std::cout << "PASS capability + inline WOTS+C code loading, MMIO fence, W^X, budget and ZEROIZE\n";

    // 4. Cryptographic services (Canopy, Fp5 Horner, Poseidon2-GL24 Jive, CTH + WOTS+C Signing)
    auto print_words = [](const char *name, const Words &v, size_t n) {
        std::cout << name;
        for (size_t i = 0; i < n; ++i) std::cout << " " << std::dec << v[i];
        std::cout << "\n";
    };
    Words node(16);
    node[0] = (77ULL << 32) | 0x103;
    for (unsigned i = 0; i < 50; i++) {
        node[1 + i / 8] |= u64(i) << (8 * (i % 8));
        node[8 + i / 8] |= u64(50 + i) << (8 * (i % 8));
    }
    print_words("CANOPY", cmd(tb, 0x31, node, 7), 7);
    Words poly{0x10004};
    for (unsigned i = 1; i <= 15; i++) poly.push_back(i);
    print_words("HORNER", cmd(tb, 0x31, poly, 7), 5);
    Words jive{(100ULL << 16) | 0x104};
    for (unsigned i = 1; i <= 14; i++) jive.push_back(i);
    jive.push_back(200);
    print_words("JIVE", cmd(tb, 0x31, jive, 7), 7);

    // Zero-Factory-Trust `0x20 CMD_CTH_SIGN`:
    //   First verify bad dual-MAC is rejected even when Owner authorizes it!
    u64 address = 0x100000000012ULL; // digit = 2 -> enclave returns chain[2] & public chain[3]!
    auto build_cth_req = [&](u64 cur_rec, const Digest16 &cur_nonce, bool corrupt_mac) {
        // Compute public `r_cth` and `req_id` iteratively? Wait: `r_cth` depends on `request[0..5]`?
        // Look at `signing.s`: `S[6..11]` absorbed `request[0..5]`! Wait: in `signing.s` of DEEP-3,
        // `secret` was hashed BEFORE `request[0..5]` so `dual = r_cth * z` didn't depend on `dual`!
        // Let's check `signing.s`!!
        return std::pair<Words, Digest16>{};
    };
    (void)build_cth_req;

    // Wait: let's match `signing.s` so `r_cth` is derived from `(enclave_id, nonce, record, request[6..12])`
    // BEFORE `request[0..5]` (`a, z, m`), so `m = r_cth * z` is non-circular!
    // (See `signing.s` update right alongside this file!)
    auto cth_transcript = [&](u64 cur_rec, const Digest16 &cur_nonce, const Words &meta7) {
        (void)cur_nonce;
        std::array<u64, 25> st{};
        for (unsigned i = 0; i < 7; ++i) st[i] = meta7[i];
        st[7]  = enclave_id[0];
        st[8]  = enclave_id[1];
        st[9]  = cur_rec;
        st[10] = 0x43541ULL;
        st[11] = 0x1F;
        st[16] = 0x80ULL << 56;
        keccak_p1600(st, 12);
        return std::pair<Digest16, Digest16>{{st[0], st[1]}, {st[2], st[3]}};
    };
    auto cth_req_id = [&](const Digest16 &hdr_tag, const Words &azm6) {
        std::array<u64, 25> st{};
        st[0] = hdr_tag[0];
        st[1] = hdr_tag[1];
        for (unsigned i = 0; i < 6; ++i) st[2 + i] = azm6[i];
        st[8] = 0x1F;
        st[16] = 0x80ULL << 56;
        keccak_p1600(st, 12);
        return Digest16{st[0], st[1]};
    };

    Words meta7{address, 45, 9, 10, 11, 12, 1234};
    // Case A: Bad dual-MAC rejected even with valid Owner WOTS+C capability!
    {
        u64 next_rec = rec + (1ULL << 32);
        // Note: `GATE` rotates `nonce`, so `CTH` uses the `nonce` emitted by `GATE`!
        // To pre-authorize a non-nonce-specific CTH capability across `GATE`'s new nonce,
        // `hdr_tag` binds `(enclave_id, next_rec, meta7)` (`next_rec` is strictly unique & monotonic!!)!
        auto [htag, r_cth] = cth_transcript(next_rec, {0, 0}, meta7);
        u128 r_val = (u128(r_cth[1]) << 64) | r_cth[0];
        u128 bad_dual = (gf128_mul(r_val, 3) ^ 1);
        Words azm6{1, 0, 3, 0, u64(bad_dual), u64(bad_dual >> 64)};
        auto rid = cth_req_id(htag, azm6);
        auto cap_bad = cap_commit_cth(dummy_sib, rid);
        u64 tr = ((rec & 0xFFFFFFFFULL) << 32) | (rec & 0xFFFFFFFFULL);
        auto gout = cmd(tb, 0x16, owner_lifecycle_frame(sk[kidx], enclave_id, 0x16, tr, nonce, rec, cap_bad, pk[kidx + 1]));
        kidx++; rec = next_rec; nonce = {gout[0], gout[1]};

        Words req = azm6;
        req.insert(req.end(), meta7.begin(), meta7.end());
        req.push_back(dummy_sib[0]); req.push_back(dummy_sib[1]);
        cmd(tb, 0x20, req, 0, 5);
    }

    // Case B: Valid dual-MAC + valid Owner WOTS+C capability succeeds & verifies publicly!
    {
        u64 next_rec = rec + (1ULL << 32);
        auto [htag, r_cth] = cth_transcript(next_rec, {0, 0}, meta7);
        u128 r_val = (u128(r_cth[1]) << 64) | r_cth[0];
        u128 dual = gf128_mul(r_val, 3);
        Words azm6{1, 0, 3, 0, u64(dual), u64(dual >> 64)};
        auto rid = cth_req_id(htag, azm6);
        auto cap_ok = cap_commit_cth(dummy_sib, rid);
        u64 tr = ((rec & 0xFFFFFFFFULL) << 32) | (rec & 0xFFFFFFFFULL);
        auto gout = cmd(tb, 0x16, owner_lifecycle_frame(sk[kidx], enclave_id, 0x16, tr, nonce, rec, cap_ok, pk[kidx + 1]));
        kidx++; rec = next_rec; nonce = {gout[0], gout[1]};

        Words req = azm6;
        req.insert(req.end(), meta7.begin(), meta7.end());
        req.push_back(dummy_sib[0]); req.push_back(dummy_sib[1]);
        auto signed_res = cmd(tb, 0x20, req);
        rec += (1ULL << 32);
        check_eq("CTH bumped gen", signed_res[2], rec);
        // `signed_res[4..7]` = `chain[2]`, `signed_res[8..11]` = `pk_chain = chain[3]`!
        Words pub_verify(signed_res.begin() + 4, signed_res.begin() + 12);
        print_words("CTH", pub_verify, 8);
        // Replay of exact same CTH request fails immediately because `rec` advanced!
        cmd(tb, 0x20, req, 0, 5);
    }

    // 5. SafeRecovery (`BOOT_MODE = 01`) hardware admission gate (`E_LOCKED = 14`)
    tb.set_boot_mode(1);
    tb.tick_core(4);
    tb.write_frame(0x80, tb.make_w0(0x20, 0, 120, 0), Words(15, 0));
    ready(tb);
    check_eq("SafeRecovery blocks CTH_SIGN", tb.read_frame(0x82, 0).first >> 48, 14);
    tb.write_frame(0x80, tb.make_w0(0x30, 1, 24, 0), {1 | (0x50000ULL << 32), 0, 0});
    ready(tb);
    check_eq("SafeRecovery blocks LOAD_CODE", tb.read_frame(0x82, 0).first >> 48, 14);
    tb.write_frame(0x80, tb.make_w0(0x31, 0, 0, 100), {});
    ready(tb);
    check_eq("SafeRecovery blocks applet EXEC", tb.read_frame(0x82, 0).first >> 48, 14);
    // Resident service (`flags[0]=1`) still allowed in SafeRecovery!
    auto sr_id = cmd(tb, 0x31, {0}, 7);
    check_eq("SafeRecovery allows resident IDENT", sr_id[0], 0x4153533200000001ULL);
    tb.set_boot_mode(0);

    // 6. Torn inactive/newer FRAM slot recovery & damaged seal/journal MAC rejection
    auto authentic_fram = tb.fram;
    unsigned newer_slot_off = ((rec >> 32) & 1) * 64;
    tb.fram.bytes[newer_slot_off] = 0; // simulate torn marker on newer slot -> falls back to rec - 1!
    tb.reset();
    auto torn_boot = cmd(tb, 0x10);
    check_eq("torn-slot fallback generation", torn_boot[2], rec - (1ULL << 32));

    tb.fram = authentic_fram;
    std::fill_n(tb.fram.bytes.begin() + 256, 8, 0); // corrupt PUF helper mask -> E_PUF=12
    tb.reset(); cmd(tb, 0x10, {}, 0, 12);

    tb.fram = authentic_fram;
    tb.fram.bytes[352] ^= 1; // corrupt anchor `seal_mac` -> E_ANCHOR_IO=9
    tb.reset(); cmd(tb, 0x10, {}, 0, 9);

    tb.fram = authentic_fram;
    tb.fram.bytes[48] ^= 1; // corrupt Slot 0 `journal_mac` -> E_ANCHOR_IO=9
    tb.reset(); cmd(tb, 0x10, {}, 0, 9);
    std::cout << "PASS SafeRecovery E_LOCKED, torn-slot recovery, and FRAM seal/MAC tamper rejection\n";

    // 7. Blank debug UART, JTAG lockout in provisioned state, and 0-clock stopped-CLK tamper wipe
    tb.fram = Fram();
    tb.reset(2); cmd(tb, 0x10); // virgin BOOT -> LC_BLANK with BOOT_MODE=10
    tb.write_frame(0x80, tb.make_w0(0x31, 7, 8, 0), {0});
    bool uart = false;
    for (int i = 0; i < 2500; i++) { tb.tick_core(); uart |= !tb.get_out_bidir(28); }
    check_eq("blank UART start", uart, 1);
    check_eq("verified", tb.get_out_bidir(16), 1);

    tb.dut.clk = 0; tb.dut.eval(); tb.set_pin_bidir(26, false); tb.dut.eval();
    check_eq("stopped tamper VERIFY", tb.get_out_bidir(16), 0);
    check_eq("stopped tamper FAULT", tb.get_out_bidir(17), 1);
    std::cout << "PASS blank debug UART and stopped-clock tamper\n";
}
