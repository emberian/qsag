// Directed end-to-end Verilator verification of `qsag_ass2_enclave_top` (`ASS2-0P5` Rev. 2.3):
//   - STRICT ZERO-FACTORY-TRUST: ZERO `fixture_root()` anywhere! The host generates its own
//     post-quantum `WOTS+C` key chain (`sk_0..sk_N -> pk_0..pk_N`), enrolls `pk_0` via `CMD_ENROL`,
//     receives the public `enclave_id`, and authorizes `COMMIT`, `LEASE`, `GATE`, `LOAD_CODE`
//     (`0x30`: `LC_BLANK` `flags = 0` open devkit, `LC_PROVISIONED`/`LC_READY` `!rom_lock` `flags = 2`
//     Owner `WOTS+C` signed applet with `cSHAKE256(K_root, "ASS2.APPLET" || code_hash)` in `R1..R2`,
//     and `rom_lock` / `SafeRecovery` hard-reject `E_LOCKED = 14`), and `CTH_SIGN`!
//   - Exercises Two-Ring Hardware W^X (`applet_exec_q`), `SYS_MMIO` & `I-ROM` Ring-3 fault containment,
//     exact-edge watchdog, torn FRAM recovery, JTAG lockout, and 0-clock stopped-CLK tamper wipe!
#include "Vqsag_ass2_enclave_top.h"
#include "Vqsag_ass2_enclave_top___024root.h"
#include "verilated.h"
#if VM_COVERAGE
#include "verilated_cov.h"
#endif
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstring>
#include <iostream>
#include <stdexcept>
#include <string_view>
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

using Key32 = std::array<u64, 4>;
using Digest16 = std::array<u64, 2>;

// NIST SP 800-185 `cSHAKE256("", S_cust, msg, 256)` (24-round Keccak-f[1600])
static Key32 cshake256_32(std::string_view cust, const u8 *msg, size_t len) {
    assert(cust.size() < 32);
    u8 pref[136]{};
    pref[0] = 1; pref[1] = 136;
    pref[2] = 1; pref[3] = 0;
    pref[4] = 1; pref[5] = u8(cust.size() * 8);
    std::memcpy(pref + 6, cust.data(), cust.size());
    std::array<u64, 25> st{};
    for (unsigned i = 0; i < 17; ++i) {
        u64 w; std::memcpy(&w, pref + 8 * i, 8);
        st[i] ^= w;
    }
    keccak_p1600(st, 24);
    size_t pos = 0;
    while (pos + 136 <= len) {
        for (unsigned i = 0; i < 17; ++i) {
            u64 w; std::memcpy(&w, msg + pos + 8 * i, 8);
            st[i] ^= w;
        }
        keccak_p1600(st, 24);
        pos += 136;
    }
    u8 last[136]{};
    std::memcpy(last, msg + pos, len - pos);
    last[len - pos] ^= 0x04;
    last[135] ^= 0x80;
    for (unsigned i = 0; i < 17; ++i) {
        u64 w; std::memcpy(&w, last + 8 * i, 8);
        st[i] ^= w;
    }
    keccak_p1600(st, 24);
    return {st[0], st[1], st[2], st[3]};
}

static Key32 compute_code_hash(const std::vector<u32> &words) {
    std::vector<u8> bytes(words.size() * 4);
    for (size_t i = 0; i < words.size(); ++i)
        std::memcpy(bytes.data() + 4 * i, &words[i], 4);
    return cshake256_32("ASS2.CODE", bytes.data(), bytes.size());
}

static Key32 derive_applet_key(const Key32 &k_root, const Key32 &code_hash) {
    constexpr std::string_view dom = "ASS2.APPLET";
    u8 in[32 + 11 + 32]{};
    std::memcpy(in, k_root.data(), 32);
    std::memcpy(in + 32, dom.data(), dom.size());
    std::memcpy(in + 32 + dom.size(), code_hash.data(), 32);
    return cshake256_32(dom, in, sizeof(in));
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

static Words pack_u32s(const std::vector<u32> &parts) {
    Words wire((parts.size() + 1) / 2, 0);
    for (size_t i = 0; i < parts.size(); ++i)
        wire[i / 2] |= u64(parts[i]) << (32 * (i % 2));
    return wire;
}

static std::pair<u32, Words> build_open_applet_payload(const std::vector<u32> &code) {
    std::vector<u32> parts;
    parts.reserve(1 + code.size());
    parts.push_back(u32(code.size()));
    parts.insert(parts.end(), code.begin(), code.end());
    return {u32(4 + 4 * code.size()), pack_u32s(parts)};
}

static std::pair<u32, Words> build_wotsc_applet_payload(
    const Key32 &sk, const Key32 &enclave_id, const Digest16 &nonce,
    u64 record, const Key32 &next_pk, const std::vector<u32> &code
) {
    auto ch = compute_code_hash(code);
    u64 salt = 0;
    std::array<u8, 16> digits{};
    while (true) {
        std::array<u64, 18> msg{
            0x574d2ULL, enclave_id[0], enclave_id[1], enclave_id[2], enclave_id[3],
            u64(code.size()), record, nonce[0], nonce[1],
            ch[0], ch[1], ch[2], ch[3],
            salt, next_pk[0], next_pk[1], next_pk[2], next_pk[3]
        };
        turboshake256(reinterpret_cast<const u8*>(msg.data()), 144, digits.data(), 16);
        unsigned sum = 0;
        for (u8 d : digits) sum += d;
        if (sum == 2040) break;
        ++salt;
    }
    std::vector<u32> parts;
    parts.reserve(1 + code.size() + 74);
    parts.push_back(u32(code.size()));
    parts.insert(parts.end(), code.begin(), code.end());
    auto push64 = [&](u64 v) {
        parts.push_back(u32(v));
        parts.push_back(u32(v >> 32));
    };
    push64(salt);
    for (u64 w : next_pk) push64(w);
    for (unsigned i = 0; i < 16; ++i) {
        auto cur = wots_sk_start(sk, i);
        for (unsigned s = 0; s < digits[i]; ++s) cur = wots_step(cur, i, s);
        push64(cur[0]);
        push64(cur[1]);
    }
    return {u32(300 + 4 * code.size()), pack_u32s(parts)};
}

static Digest16 cap_commit_cth(const Digest16 &sibling, const Digest16 &req_id) {
    std::array<u64, 5> in{0x43501ULL, req_id[0], req_id[1], sibling[0], sibling[1]};
    Digest16 out{};
    turboshake256(reinterpret_cast<const u8*>(in.data()), 40, reinterpret_cast<u8*>(out.data()), 16);
    return out;
}

// ---- Assembled Ring-3 Applets (`0x10000..0x100FF`, `<= 64` words each) ----
static const std::vector<u32> R3_OK{0x41000004U, 0x70000045U, 0x41018006U, 0x80000065U, 0x40000104U, 0x00050000U};
static const std::vector<u32> R3_WR_CODE64{0x41000004U, 0x80000040U, 0x00050000U};
static const std::vector<u32> R3_WR_CODE8{0x4100ff04U, 0x80000140U, 0x00050000U};
static const std::vector<u32> R3_CROSS_256B{0x4100fc04U, 0x70000045U, 0x00050000U};
static const std::vector<u32> R3_EXEC_DATA{0x41010004U, 0xb0000040U};
static const std::vector<u32> R3_RD_MMIO{0x40ffff05U, 0x30010555U, 0x70000056U, 0x00050000U};
static const std::vector<u32> R3_RD_VAULT{0x40ffff05U, 0x30010555U, 0x70050156U, 0x00050000U};
static const std::vector<u32> R3_MISALIGN_MMIO{0x40ffff05U, 0x30010555U, 0x30003055U, 0x70000056U, 0x00050000U};
static const std::vector<u32> R3_WR_MMIO{0x40ffff05U, 0x30010555U, 0x80000050U, 0x00050000U};
static const std::vector<u32> R3_RD_IROM{0x70000006U, 0x00050000U};
static const std::vector<u32> R3_EXEC_IROM{0xb0000000U};
static const std::vector<u32> R3_CSRW_EVEC{0x00230000U, 0x00050000U};
static const std::vector<u32> R3_CSRW_EXCEN{0x03f30000U, 0x00050000U};
static const std::vector<u32> R3_SPIN{0xaffffff0U};
static const std::vector<u32> R3_KEY_PROBE{
    0x4101800aU, 0x800000a1U, 0x800010a2U, 0x800020a3U, 0x800030afU, 0xc04005a0U, 0xc05185a0U, 0x40000104U, 0x00050000U
};

static const std::vector<u32> CANOPY_APPLET = {
    0x4101000eU, 0xc0d004e0U, 0xc0e014e0U, 0xc0f024e0U, 0x40003108U, 0xc0003180U, 0xf0c00000U, 0x700641e8U,
    0x700651e6U, 0x30008566U, 0x800100e6U, 0x4007000bU, 0x8001d0ebU, 0x4000320bU, 0x3ffff0bbU, 0x20000be4U,
    0x70000146U, 0x70032147U, 0x6000876cU, 0x60008677U, 0x8008514cU, 0x800b7147U, 0x9ffff71bU, 0x700100e8U,
    0xc0000280U, 0x700110e8U, 0xc0001280U, 0x700120e8U, 0xc0002280U, 0x700130e8U, 0xc0003280U, 0x700140e8U,
    0xc0004280U, 0x700150e8U, 0xc0005280U, 0x700160e8U, 0xc0006280U, 0x700170e8U, 0xc0007280U, 0x700180e8U,
    0xc0008280U, 0x700190e8U, 0xc0009280U, 0x7001a0e8U, 0xc000a280U, 0x7001b0e8U, 0xc000b280U, 0x7001c0e8U,
    0xc000c280U, 0x7001d0e8U, 0xc000d280U, 0x300375e8U, 0xc0010280U, 0xf0c00000U, 0xc10005e0U, 0xc11015e0U,
    0xc12025e0U, 0xc13035e0U, 0xc14045e0U, 0xc15055e0U, 0xc0006008U, 0x3ffff388U, 0x800160e8U, 0x00050000U,
};
static const std::vector<u32> HORNER_APPLET = {
    0x4101000eU, 0x700000e7U, 0xc01054e0U, 0xc02064e0U, 0xc03074e0U, 0xc04084e0U, 0xc05094e0U, 0x30010675U,
    0x30001355U, 0x300300e4U, 0x90000105U, 0x30028044U, 0xc0000440U, 0xc0101440U, 0xc0202440U, 0xc0303440U,
    0xc0404440U, 0x90000a05U, 0x3ffd8044U, 0xc000a440U, 0xc010b440U, 0xc020c440U, 0xc030d440U, 0xc040e440U,
    0xd0040100U, 0xd0050200U, 0x3ffff055U, 0x9ffff615U, 0xc10005e0U, 0xc11015e0U, 0xc12025e0U, 0xc13035e0U,
    0xc14045e0U, 0x40000104U, 0x00050000U,
};
static const std::vector<u32> JIVE_APPLET = {
    0x4101000eU, 0x700000e7U, 0x30010677U, 0x7000f0e8U, 0x300080e4U, 0xa00002e3U, 0xd0050200U, 0xd0050311U,
    0xc08074e0U, 0xc09084e0U, 0xc0a094e0U, 0xc0b0a4e0U, 0xc0c0b4e0U, 0xc0d0c4e0U, 0xc0e0d4e0U, 0xc000e170U,
    0xc000f180U, 0x40001009U, 0xc0010190U, 0x40000809U, 0xc0011190U, 0x40000709U, 0xc0012190U, 0xcfe134e0U,
    0xcff174e0U, 0xf0010000U, 0x300080e4U, 0xa0000183U, 0xd0050200U, 0xd0050311U, 0x300400e4U, 0xa0000143U,
    0xd0050222U, 0xd0050333U, 0xd0050200U, 0xd0050311U, 0x40000406U, 0xc0000009U, 0xd0009679U, 0xc0000190U,
    0xc0001009U, 0xd0009689U, 0xc0001190U, 0xc10005e0U, 0xc11015e0U, 0xc12025e0U, 0xc13035e0U, 0xc14045e0U,
    0xc15055e0U, 0xc16065e0U, 0x40000104U, 0x00050000U, 0xc000a440U, 0xc010b440U, 0xc020c440U, 0xc030d440U,
    0xc040e440U, 0xc050f440U, 0xc0610440U, 0xb0000030U, 0x474c3234U, 0x4d524b4cU, 0x474c3234U, 0x504f5332U,
};

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
        for (int c = 0; c < 200000; ++c) {
            if (boot_mode != 3 && c < 512 && get_out_bidir(19))
                throw std::runtime_error("HOST_RDY rose before 512-byte D-SRAM scrub & POST KAT completed");
            tick_core(1);
            if (boot_mode != 3 && get_out_bidir(19)) {
                if (get_out_bidir(17))
                    throw std::runtime_error("FAULT high after cold-boot POST KAT");
                return;
            }
        }
        if (boot_mode != 3 && !get_out_bidir(19))
            throw std::runtime_error("HOST_RDY not high after full FIPS 140-3 POST KAT & reset scrub");
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
    size_t n_read = err ? ((err == 15 || err == 16) ? 2 : 0) : 20;
    auto [h, out] = tb.read_frame(0x82, n_read);
    if (h >> 48 != unsigned(err))
        std::cerr << "opcode 0x" << std::hex << unsigned(op) << " diag " << tb.read_diag_clockless() << "\n";
    check_eq("command status", h >> 48, err);
    return out;
}

static Words cmd_load_open(EnclaveTb &tb, const std::vector<u32> &code, int err = 0) {
    auto [blen, body] = build_open_applet_payload(code);
    tb.write_frame(0x80, tb.make_w0(0x30, 0, blen, 0), body);
    ready(tb);
    size_t n_read = err ? ((err == 15 || err == 16) ? 2 : 0) : 20;
    auto [h, out] = tb.read_frame(0x82, n_read);
    check_eq("open 0x30 status", h >> 48, err);
    return out;
}

int main(int argc, char **argv) {
    Verilated::commandArgs(argc, argv);
    std::cout.setf(std::ios::unitbuf);
#ifdef TEST_POST_KAT_FAIL
    {
        EnclaveTb bad_tb;
        bad_tb.dut.rst_n = 0;
        bad_tb.set_cs_n(true);
        bad_tb.set_boot_mode(0);
        bad_tb.set_pin_bidir(26, true);
        bad_tb.set_pin_bidir(18, false);
        bad_tb.tick_core(4);
        bad_tb.dut.rst_n = 1;
        for (int c = 0; c < 200000; ++c) {
            if (bad_tb.get_out_bidir(19))
                throw std::runtime_error("FIPS POST KAT failure leaked HOST_RDY=1");
            bad_tb.tick_core(1);
            if (bad_tb.get_out_bidir(17)) break;
        }
        check_eq("POST KAT fail FAULT=1", bad_tb.get_out_bidir(17), 1);
        check_eq("POST KAT fail VERIFY_OK=0", bad_tb.get_out_bidir(16), 0);
        check_eq("POST KAT fail HOST_RDY=0", bad_tb.get_out_bidir(19), 0);
        bad_tb.tick_core(2048);
        check_eq("POST KAT permanent lockout HOST_RDY=0", bad_tb.get_out_bidir(19), 0);
        check_eq("POST KAT permanent lockout FAULT=1", bad_tb.get_out_bidir(17), 1);
        u64 d = bad_tb.read_diag_clockless();
        check_eq("POST KAT DIAG FAULT bit", (d >> 55) & 1ULL, 1);
        check_eq("POST KAT DIAG RDY bit", (d >> 49) & 1ULL, 0);
        std::cout << "PASS FIPS 140-3 §10.3.A Cold-Boot POST KAT mismatch permanent lockout\n";
#if VM_COVERAGE
        VerilatedCov::write("coverage.dat");
#endif
        return 0;
    }
#endif
    EnclaveTb tb;
    tb.reset();

    // 1. Clockless DIAG, 3 SPI widths, LC_RESET 0x30 rejection (`E_NO_IMAGE = 13`), & resident IDENT
    check_eq("clockless DIAG", tb.read_diag_clockless(), 0x5a0300000000a552ULL);
    for (auto [w, r] : {std::pair<int, int>{0, 2}, {0x40, 0x42}, {0x80, 0x82}}) {
        tb.write_frame(w, tb.make_w0(1, 0, 0, 0), {});
        auto out = tb.read_frame(r, 4).second;
        check_eq("banner", out[0], 0x3038314432535341ULL);
        check_eq("ID", out[1], 0x4153533200000001ULL);
    }
    tb.write_frame(0x80, tb.make_w0(0x30, 0, 8, 0), {1 | (0x50000ULL << 32)});
    ready(tb);
    check_eq("LC_RESET rejects 0x30 with E_NO_IMAGE=13", tb.read_frame(0x82, 0).first >> 48, 13);
    auto id = cmd(tb, 0x31, {0}, 7);
    check_eq("resident IDENT", id[0], 0x4153533200000001ULL);
    check_eq("resident FEATURES", id[1], 15);
    std::cout << "PASS diagnostic, 3 host widths, LC_RESET admission and resident IDENT\n";

    // 2. Policy 1 (`LC_BLANK`, `flags = 0` Open Ring-3 Devkit + Two-Ring Hardware W^X Trap Suite)
    cmd(tb, 0x10);
    check_eq("blank after BOOT", (tb.read_diag_clockless() >> 24) & 7, 1);

    // Reject non-zero flags, 0 words, 65 words, mismatched hdr_len, and non-zero even-n padding in LC_BLANK
    tb.write_frame(0x80, tb.make_w0(0x30, 2, 304, 0), Words(38, 0));
    ready(tb);
    check_eq("LC_BLANK rejects flags=2", tb.read_frame(0x82, 0).first >> 48, 13);
    tb.write_frame(0x80, tb.make_w0(0x30, 0, 8, 0), {0});
    ready(tb);
    check_eq("LC_BLANK rejects 0 words", tb.read_frame(0x82, 0).first >> 48, 3);
    tb.write_frame(0x80, tb.make_w0(0x30, 0, 264, 0), Words(33, 0));
    ready(tb);
    check_eq("LC_BLANK rejects 65 words", tb.read_frame(0x82, 0).first >> 48, 3);
    tb.write_frame(0x80, tb.make_w0(0x30, 0, 12, 0), {1 | (0x50000ULL << 32), 0});
    ready(tb);
    check_eq("LC_BLANK rejects mismatched exp_load_len", tb.read_frame(0x82, 0).first >> 48, 3);
    tb.write_frame(0x80, tb.make_w0(0x30, 0, 12, 0), {2 | (0x60000ULL << 32), 0x50000ULL | (1ULL << 32)});
    ready(tb);
    check_eq("LC_BLANK rejects non-zero pad", tb.read_frame(0x82, 0).first >> 48, 3);

    // Valid open Ring-3 applet (`R3_OK`, 6 words) reads lower 256B (`R+X`) and writes upper 256B (`R+W`)
    auto r3_res = cmd_load_open(tb, R3_OK);
    check_eq("R3_OK read own code word", u32(r3_res[0]), R3_OK[0]);
    check_eq("R3_OK r4=1", r3_res[16], 1);
    // Re-execute installed Ring-3 applet via CMD_EXEC (`0x31`, `flags = 2` -> sets VERIFY_OK = 1!)
    auto r3_reexec = cmd(tb, 0x31, {}, 2);
    check_eq("R3_OK re-exec via 0x31", u32(r3_reexec[0]), R3_OK[0]);
    check_eq("R3_OK VERIFY_OK=1", tb.get_out_bidir(16), 1);

    // 64-instruction boundary (`63` NOPs + `HALT` at `0x100FC`) succeeds cleanly
    std::vector<u32> max64(63, 0x00060000U);
    max64.push_back(0x00050000U);
    cmd_load_open(tb, max64);

    // Verify all Ring-3 Hardware W^X & Privilege Traps (`E_TRAP = 16`, Ring 0 stays alive in `LC_BLANK`!)
    for (auto &[name, prog, exp_cause] : std::vector<std::tuple<const char*, std::vector<u32>, u64>>{
        {"Ring3 ST64 [0x10000] !W",          R3_WR_CODE64,     5},
        {"Ring3 STB  [0x100FF] !W",          R3_WR_CODE8,      5},
        {"Ring3 LD64 [0x100FC] cross_256b",  R3_CROSS_256B,    5},
        {"Ring3 JALR [0x10100] !X",          R3_EXEC_DATA,     5},
        {"Ring3 LD64 [0xFFFF0000] MMIO",     R3_RD_MMIO,       5},
        {"Ring3 LDBU [0xFFFF0050] Vault",    R3_RD_VAULT,      5},
        {"Ring3 misaligned MMIO MemFault>4", R3_MISALIGN_MMIO, 5},
        {"Ring3 ST64 [0xFFFF0000] MMIO",     R3_WR_MMIO,       5},
        {"Ring3 LD64 [0x0000] I-ROM",        R3_RD_IROM,       5},
        {"Ring3 JALR [0x0000] I-ROM",        R3_EXEC_IROM,     5},
        {"Ring3 CSRW EVEC IllegalInsn",      R3_CSRW_EVEC,     1},
        {"Ring3 CSRW EXC_EN IllegalInsn",    R3_CSRW_EXCEN,    1},
    }) {
        auto tout = cmd_load_open(tb, prog, 16);
        check_eq(name, tout[0], exp_cause);
        check_eq("Ring3 trap preserves LC_BLANK", (tb.read_diag_clockless() >> 24) & 7, 1);
    }

    // Ring-3 cycle-budget expiry (`R3_SPIN` with `budget = 24` via `0x31` `flags = 0`) -> `E_BUDGET = 15`, Ring 0 stays in `LC_BLANK`!
    cmd_load_open(tb, {0x00050000U}); // install trivial applet, then overwrite with R3_SPIN? Wait: R3_SPIN spins on 0x30 too unless we branch on RX_MBOX!
    // Build 4-insn applet: `MOVZ20 R4, 0x10100; LD64 R5, [R4]; l: BNEZ R5, l; HALT`!
    // On `0x30` (`RX_MBOX == 0`), it halts immediately; on `0x31` with `{1}` and `budget = 32`, it spins and hits `E_BUDGET = 15`!
    cmd_load_open(tb, {0x41010004U, 0x70000045U, 0x90000015U, 0x00050000U});
    cmd(tb, 0x31, {1}, 0, 15, 32);
    check_eq("Ring3 budget expiry preserves LC_BLANK", (tb.read_diag_clockless() >> 24) & 7, 1);
    cmd(tb, 0x31, {}, 0, 13); // applet_valid_q cleared after fault!
    std::cout << "PASS LC_BLANK open Ring-3 devkit (1..64 insns) & Two-Ring Hardware W^X trap containment\n";

    // Precompute Owner's post-quantum WOTS+C rolling key sequence (ZERO enclave secrets!)
    std::vector<Key32> sk(24), pk(24);
    for (unsigned i = 0; i < sk.size(); ++i) {
        sk[i] = make_seed(i + 1);
        pk[i] = wots_pubkey(sk[i]);
    }
    unsigned kidx = 0;

    // 3. Zero-Factory-Trust ENROL -> COMMIT -> BOOT -> LEASE -> GATE
    cmd(tb, 0x11, {0, 0, 0, 0}, 0, 10); // reject zero owner key

    auto e = cmd(tb, 0x11, {pk[0][0], pk[0][1], pk[0][2], pk[0][3]});
    check_eq("enrol success", e[16], 1);
    Digest16 nonce{e[0], e[1]};
    Key32 enclave_id{e[2], e[3], e[4], e[5]};
    check_eq("enclave_id non-zero", (enclave_id[0] | enclave_id[1] | enclave_id[2] | enclave_id[3]) != 0, 1);

    // Capture internal Vault `K_root` strictly as whitebox testbench oracle to assert bit-exact `derive_applet_key`!
    Key32 vault_k_root{
        tb.dut.rootp->qsag_ass2_enclave_top__DOT__key_lo,
        tb.dut.rootp->qsag_ass2_enclave_top__DOT__key_hi,
        0ULL, 0ULL
    };
    check_eq("Vault K_root non-zero", (vault_k_root[0] | vault_k_root[1]) != 0, 1);

    // Bad WOTS+C proof during COMMIT is rejected and burns challenge nonce!
    Digest16 zero_cap{0, 0};
    auto bad_commit = owner_lifecycle_frame(sk[0], enclave_id, 0x12, 0, nonce, 0, zero_cap, pk[1]);
    bad_commit[10] ^= 1ULL;
    cmd(tb, 0x12, bad_commit, 0, 5);
    auto burned_retry = owner_lifecycle_frame(sk[0], enclave_id, 0x12, 0, nonce, 0, zero_cap, pk[1]);
    cmd(tb, 0x12, burned_retry, 0, 4);

    // Fresh ENROL challenge in LC_BLANK + valid Owner WOTS+C COMMIT -> LC_PROVISIONED!
    e = cmd(tb, 0x11, {pk[0][0], pk[0][1], pk[0][2], pk[0][3]});
    nonce = {e[0], e[1]};
    check_eq("deterministic enclave_id", e[2], enclave_id[0]);
    check_eq("deterministic enclave_id[3]", e[5], enclave_id[3]);
    auto commit_out = cmd(tb, 0x12, owner_lifecycle_frame(sk[0], enclave_id, 0x12, 0, nonce, 0, zero_cap, pk[1]));
    kidx = 1;
    u64 rec = 1ULL << 32;
    nonce = {commit_out[0], commit_out[1]};
    check_eq("provisioned", (tb.read_diag_clockless() >> 24) & 7, 2);

    // Cold BOOT reconstructs PUF root_secret, verifies FRAM anchor & journal, enters LEASE_PENDING
    tb.reset();
    auto boot1 = cmd(tb, 0x10);
    check_eq("boot record gen=1", boot1[2], rec);
    check_eq("boot enclave_id matches", boot1[4], enclave_id[0]);
    nonce = {boot1[0], boot1[1]};

    // LEASE via Owner WOTS+C (sk[1] -> pk[2]), advancing gen 1 -> 2 and entering LC_READY!
    auto lease1 = cmd(tb, 0x15, owner_lifecycle_frame(sk[kidx], enclave_id, 0x15, rec, nonce, rec, zero_cap, pk[kidx + 1]));
    kidx++;
    rec = 2ULL << 32;
    check_eq("leased gen=2", lease1[2], rec);
    check_eq("LC_READY", (tb.read_diag_clockless() >> 24) & 7, 5);
    nonce = {lease1[0], lease1[1]};

    // GATE transition 0 -> 7 via Owner WOTS+C (sk[2] -> pk[3]) + replay denial
    auto gate_frame = owner_lifecycle_frame(sk[kidx], enclave_id, 0x16, 7, nonce, rec, zero_cap, pk[kidx + 1]);
    auto gate_out = cmd(tb, 0x16, gate_frame);
    kidx++;
    rec = (3ULL << 32) | 7;
    check_eq("gate record gen=3 state=7", gate_out[2], rec);
    nonce = {gate_out[0], gate_out[1]};
    cmd(tb, 0x16, gate_frame, 0, 5);

    // Reboot + Lease to refresh burned nonce
    tb.reset();
    auto boot2 = cmd(tb, 0x10);
    check_eq("boot recovered gen=3 state=7", boot2[2], rec);
    nonce = {boot2[0], boot2[1]};
    auto lease2 = cmd(tb, 0x15, owner_lifecycle_frame(sk[kidx], enclave_id, 0x15, rec, nonce, rec, zero_cap, pk[kidx + 1]));
    kidx++;
    rec = (4ULL << 32) | 7;
    nonce = {lease2[0], lease2[1]};
    std::cout << "PASS Zero-Factory-Trust ENROL COMMIT BOOT LEASE GATE, WOTS+C rotation and replay denial\n";

    // 4. Policy 2 (`LC_READY` with `!rom_lock`: Owner `WOTS+C` Signed Applets + `applet_key` Injection in `R1..R2`)
    // Open `flags = 0` and legacy `flags = 1` are rejected in `LC_READY` (`E_NO_IMAGE = 13`)
    cmd_load_open(tb, R3_KEY_PROBE, 13);
    tb.write_frame(0x80, tb.make_w0(0x30, 1, 24, 0), {1 | (0x50000ULL << 32), 0, 0});
    ready(tb);
    check_eq("LC_READY rejects flags=1", tb.read_frame(0x82, 0).first >> 48, 13);

    // Forged `flags = 2` WOTS+C applet (code word mutated after signing `code_hash`) rejected (`E_MAC = 5`) without advancing `gen`!
    {
        auto [blen, forged_body] = build_wotsc_applet_payload(sk[kidx], enclave_id, nonce, rec, pk[kidx + 1], R3_KEY_PROBE);
        forged_body[1] ^= 0x04ULL;
        tb.write_frame(0x80, tb.make_w0(0x30, 2, blen, 0), forged_body);
        ready(tb);
        check_eq("forged WOTS+C applet rejected", tb.read_frame(0x82, 0).first >> 48, 5);
    }
    // Reboot + Lease proves `gen` did NOT advance on forged `0x30`!
    tb.reset();
    auto boot_after_forge = cmd(tb, 0x10);
    check_eq("gen unchanged after forged 0x30", boot_after_forge[2], rec);
    nonce = {boot_after_forge[0], boot_after_forge[1]};
    auto lease_after_forge = cmd(tb, 0x15, owner_lifecycle_frame(sk[kidx], enclave_id, 0x15, rec, nonce, rec, zero_cap, pk[kidx + 1]));
    kidx++;
    rec += (1ULL << 32);
    nonce = {lease_after_forge[0], lease_after_forge[1]};

    auto load_signed_applet = [&](const std::vector<u32> &code) -> Words {
        auto [blen, body] = build_wotsc_applet_payload(sk[kidx], enclave_id, nonce, rec, pk[kidx + 1], code);
        tb.write_frame(0x80, tb.make_w0(0x30, 2, blen, 0), body);
        ready(tb);
        auto [h, out] = tb.read_frame(0x82, 20);
        check_eq("signed 0x30 status", h >> 48, 0);
        kidx++;
        rec += (1ULL << 32);
        // Fetch fresh rotated `nonce` from Vault (`nonce_lo`, `nonce_hi`)? No! Wait:
        // When `0x30` drops into Ring 3, `TX_MBOX` (`out[0..15]`) is owned by the Ring-3 applet!
        // Where does the host get the next `nonce` if it wants to send another Owner command?
        // In hardware, `BOOT` / `LEASE` / `GATE` / `CTH_SIGN` return `nonce` in `TX_MBOX[0..1]`, OR if the Ring-3 applet doesn't overwrite `TX_MBOX[0..1]`, wait: `lifecycle.s` zeroed `TX_MBOX[24..127]` (`ADDI R5, R15, 24; MOVZ20 R6, 13; CALL zero_words`), preserving `TX_MBOX[0..2]` (`nonce[0..1]` + `record`) unless the Ring-3 applet overwrites `TX_MBOX[0..1]`!
        return out;
    };

    // Test odd-word (`9` words: `R3_KEY_PROBE`) AND even-word (`10` words: `NOP + R3_KEY_PROBE`) signed applets!
    // Verify exact `cSHAKE256("ASS2.APPLET", K_root || "ASS2.APPLET" || code_hash)` in `R1..R2` AND hardware scrub of `R3..R15` & `S0..S24`!
    {
        auto out_a = load_signed_applet(R3_KEY_PROBE);
        auto exp_key_a = derive_applet_key(vault_k_root, compute_code_hash(R3_KEY_PROBE));
        check_eq("applet_key_a R1 exact cSHAKE256", out_a[0], exp_key_a[0]);
        check_eq("applet_key_a R2 exact cSHAKE256", out_a[1], exp_key_a[1]);
        check_eq("Ring3 scrubbed R3 == 0",  out_a[2], 0);
        check_eq("Ring3 scrubbed R15 == 0", out_a[3], 0);
        check_eq("Ring3 scrubbed S0 == 0",  out_a[4], 0);
        check_eq("Ring3 scrubbed S24 == 0", out_a[5], 0);

        // Reboot + Lease to get fresh nonce (since `R3_KEY_PROBE` deliberately wrote `TX_MBOX[0..1]`), then load 10-word even applet!
        tb.reset();
        auto b = cmd(tb, 0x10);
        check_eq("gen bumped by signed 0x30", b[2], rec);
        nonce = {b[0], b[1]};
        auto l = cmd(tb, 0x15, owner_lifecycle_frame(sk[kidx], enclave_id, 0x15, rec, nonce, rec, zero_cap, pk[kidx + 1]));
        kidx++; rec += (1ULL << 32); nonce = {l[0], l[1]};

        std::vector<u32> probe_even{0x00060000U};
        probe_even.insert(probe_even.end(), R3_KEY_PROBE.begin(), R3_KEY_PROBE.end());
        auto out_b = load_signed_applet(probe_even);
        auto exp_key_b = derive_applet_key(vault_k_root, compute_code_hash(probe_even));
        check_eq("applet_key_b (even n=10) R1 exact", out_b[0], exp_key_b[0]);
        check_eq("applet_key_b (even n=10) R2 exact", out_b[1], exp_key_b[1]);
        check_eq("distinct code_hash -> distinct applet_key", (out_a[0] != out_b[0]) || (out_a[1] != out_b[1]), 1);
    }
    std::cout << "PASS LC_READY Owner WOTS+C signed applets, exact cSHAKE256 applet_key in R1..R2, and Ring-3 scrub\n";

    // 5. Header guards & Resident Ring-0 cycle-budget watchdog lockout (`LC_LOCKED_OUT = 6`)
    tb.write_frame(0x80, 0x50ULL | (0x01ULL << 8), {});
    ready(tb);
    check_eq("bad magic rejected", tb.read_frame(0x82, 0).first >> 48, 1);
    tb.write_frame(0x80, tb.make_w0(0x99, 0, 0, 0), {});
    ready(tb);
    check_eq("unknown opcode rejected", tb.read_frame(0x82, 0).first >> 48, 2);
    tb.write_frame(0x80, tb.make_w0(0x20, 0, 112, 0), Words(14, 0));
    ready(tb);
    check_eq("bad CTH_SIGN length rejected", tb.read_frame(0x82, 0).first >> 48, 3);
    tb.write_frame(0x80, tb.make_w0(0x31, 7, 136, 0), Words(17, 0));
    ready(tb);
    check_eq("oversized EXEC length rejected", tb.read_frame(0x82, 0).first >> 48, 3);
    tb.write_frame(0x80, tb.make_w0(0x11, 0, 32, 0), Words(6, 0));
    ready(tb);

    // Resident Ring-0 watchdog expiry -> `E_BUDGET = 15` + permanent sticky `LC_LOCKED_OUT = 6`!
    tb.write_frame(0x80, tb.make_w0(0x31, 7, 8, 20), {0});
    for (int i = 0; i < 2000; ++i) {
        if (tb.get_out_bidir(20)) break;
        tb.tick_core();
    }
    check_eq("watchdog IRQ=1", tb.get_out_bidir(20), 1);
    check_eq("watchdog FAULT=1", tb.get_out_bidir(17), 1);
    check_eq("watchdog VERIFY=0", tb.get_out_bidir(16), 0);
    tb.tick_core(600);
    check_eq("sticky lockout HOST_RDY=0", tb.get_out_bidir(19), 0);
    check_eq("sticky lockout LC_LOCKED_OUT=6", (tb.read_diag_clockless() >> 24) & 7, 6);
    auto bresp = tb.read_frame(0x82, 2);
    check_eq("watchdog E_BUDGET=15", bresp.first >> 48, 15);

    // Cold reset + BOOT + LEASE recovers authentic FRAM state cleanly
    tb.reset();
    auto boot3 = cmd(tb, 0x10);
    check_eq("boot after watchdog lockout", boot3[2], rec);
    nonce = {boot3[0], boot3[1]};
    auto lease3 = cmd(tb, 0x15, owner_lifecycle_frame(sk[kidx], enclave_id, 0x15, rec, nonce, rec, zero_cap, pk[kidx + 1]));
    kidx++;
    rec += (1ULL << 32);
    nonce = {lease3[0], lease3[1]};
    std::cout << "PASS header guards & sticky Ring-0 watchdog lockout recovery\n";

    // 6. Cryptographic services: Signed Ring-3 `CANOPY` (64w), `HORNER` (35w), `JIVE` (64w) + Ring-0 `CTH_SIGN`!
    auto print_words = [](const char *name, const Words &v, size_t n) {
        std::cout << name;
        for (size_t i = 0; i < n; ++i) std::cout << " " << std::dec << v[i];
        std::cout << "\n";
    };
    auto refresh_nonce = [&]() {
        tb.reset();
        auto b = cmd(tb, 0x10);
        check_eq("refresh boot rec", b[2], rec);
        nonce = {b[0], b[1]};
        auto l = cmd(tb, 0x15, owner_lifecycle_frame(sk[kidx], enclave_id, 0x15, rec, nonce, rec, zero_cap, pk[kidx + 1]));
        kidx++; rec += (1ULL << 32); nonce = {l[0], l[1]};
    };

    // 6a. Signed 64-word `CANOPY_APPLET` (`0x30` `flags = 2` -> `0x31` `flags = 0`)
    {
        auto load_out = load_signed_applet(CANOPY_APPLET);
        nonce = {load_out[0], load_out[1]}; // Wait: CANOPY_APPLET ran on zeroed RX_MBOX during 0x30 and wrote TX_MBOX[0..6], so refresh_nonce after!
        u8 rx_bytes[128]{};
        for (unsigned i = 0; i < 50; ++i) { rx_bytes[i] = u8(i); rx_bytes[50 + i] = u8(50 + i); }
        rx_bytes[100] = 1;
        rx_bytes[101] = 77;
        u64 k0 = 0x5351980100018801ULL, k1 = 0x4d45484b5a2e4741ULL, k2 = 0x762f454552542e32ULL;
        std::memcpy(rx_bytes + 104, &k0, 8);
        std::memcpy(rx_bytes + 112, &k1, 8);
        std::memcpy(rx_bytes + 120, &k2, 8);
        Words c_in(16, 0);
        std::memcpy(c_in.data(), rx_bytes, 128);
        print_words("CANOPY", cmd(tb, 0x31, c_in, 0), 7);
        refresh_nonce();
    }

    // 6b. Signed 35-word `HORNER_APPLET` (`0x30` `flags = 2` -> `0x31` `flags = 2`)
    {
        load_signed_applet(HORNER_APPLET);
        Words poly{0x10004};
        for (unsigned i = 1; i <= 15; i++) poly.push_back(i);
        print_words("HORNER", cmd(tb, 0x31, poly, 2), 5);
        check_eq("HORNER VERIFY_OK=1", tb.get_out_bidir(16), 1);
        refresh_nonce();
    }

    // 6c. Signed 64-word `JIVE_APPLET` (`0x30` `flags = 2` -> `0x31` `flags = 2`)
    {
        load_signed_applet(JIVE_APPLET);
        Words jive{(100ULL << 16) | 0x104};
        for (unsigned i = 1; i <= 14; i++) jive.push_back(i);
        jive.push_back(200);
        print_words("JIVE", cmd(tb, 0x31, jive, 2), 7);
        check_eq("JIVE VERIFY_OK=1", tb.get_out_bidir(16), 1);
        refresh_nonce();
    }

    // 6d. Zero-Factory-Trust `0x20 CMD_CTH_SIGN`
    Digest16 dummy_sib{0x1122334455667788ULL, 0x99aabbccddeeff00ULL};
    u64 address = 0x100000000012ULL; // digit = 2 -> enclave returns chain[2] & public chain[3]
    auto cth_transcript = [&](u64 cur_rec, const Words &meta7) {
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
    // Case A: Bad dual-MAC rejected (`E_MAC = 5`) even with valid Owner WOTS+C capability
    {
        u64 next_rec = rec + (1ULL << 32);
        auto [htag, r_cth] = cth_transcript(next_rec, meta7);
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
        refresh_nonce();
    }

    // Case B: Valid dual-MAC + valid Owner WOTS+C capability succeeds & verifies publicly
    {
        u64 next_rec = rec + (1ULL << 32);
        auto [htag, r_cth] = cth_transcript(next_rec, meta7);
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
        nonce = {signed_res[0], signed_res[1]};
        check_eq("CTH bumped gen", signed_res[2], rec);
        Words pub_verify(signed_res.begin() + 4, signed_res.begin() + 12);
        print_words("CTH", pub_verify, 8);
        cmd(tb, 0x20, req, 0, 4); // nonce consumed -> immediate E_NOKEY = 4!
        refresh_nonce();
    }

    // 7. Policy 3 (`SafeRecovery` `BOOT_MODE = 01` AND `rom_lock == 1` via `CMD_GATE` `state = 8`) -> `E_LOCKED = 14`!
    tb.set_boot_mode(1);
    tb.tick_core(4);
    tb.write_frame(0x80, tb.make_w0(0x20, 0, 120, 0), Words(15, 0));
    ready(tb);
    check_eq("SafeRecovery blocks CTH_SIGN", tb.read_frame(0x82, 0).first >> 48, 14);
    cmd_load_open(tb, R3_OK, 14);
    tb.write_frame(0x80, tb.make_w0(0x31, 0, 0, 100), {});
    ready(tb);
    check_eq("SafeRecovery blocks applet EXEC", tb.read_frame(0x82, 0).first >> 48, 14);
    auto sr_id = cmd(tb, 0x31, {0}, 7);
    check_eq("SafeRecovery allows resident IDENT", sr_id[0], 0x4153533200000001ULL);
    tb.set_boot_mode(0);
    tb.tick_core(4);

    // Snapshot authentic FRAM before permanent `rom_lock` transition (`state 7 -> 8`, `record[3] == 1`)!
    auto authentic_fram = tb.fram;
    u64 pre_lock_rec = rec;
    {
        u64 tr_lock = ((rec & 0xFFFFFFFFULL) << 32) | 8ULL;
        auto lock_out = cmd(tb, 0x16, owner_lifecycle_frame(sk[kidx], enclave_id, 0x16, tr_lock, nonce, rec, zero_cap, pk[kidx + 1]));
        kidx++;
        rec = (rec & ~0xFFFFFFFFULL) + (1ULL << 32) + 8ULL;
        nonce = {lock_out[0], lock_out[1]};
        check_eq("GATE transitioned to rom_lock state=8", lock_out[2], rec);

        // Both open (`flags = 0`) AND validly Owner-signed (`flags = 2`) `0x30` frames MUST hard-reject with `E_LOCKED = 14`!
        cmd_load_open(tb, R3_OK, 14);
        auto [blen, valid_signed] = build_wotsc_applet_payload(sk[kidx], enclave_id, nonce, rec, pk[kidx + 1], R3_OK);
        tb.write_frame(0x80, tb.make_w0(0x30, 2, blen, 0), valid_signed);
        ready(tb);
        check_eq("rom_lock hard-rejects valid signed 0x30 with E_LOCKED=14", tb.read_frame(0x82, 0).first >> 48, 14);
        cmd(tb, 0x31, {}, 0, 14);
    }

    // 8. Torn inactive/newer FRAM slot recovery & damaged seal/journal MAC rejection
    tb.fram = authentic_fram;
    unsigned newer_slot_off = ((pre_lock_rec >> 32) & 1) * 64;
    tb.fram.bytes[newer_slot_off] = 0; // simulate torn marker on newer slot -> falls back to pre_lock_rec - 1!
    tb.reset();
    auto torn_boot = cmd(tb, 0x10);
    check_eq("torn-slot fallback generation", torn_boot[2] >> 32, (pre_lock_rec >> 32) - 1);

    tb.fram = authentic_fram;
    std::fill_n(tb.fram.bytes.begin() + 256, 8, 0); // corrupt PUF helper mask -> E_PUF=12
    tb.reset(); cmd(tb, 0x10, {}, 0, 12);

    tb.fram = authentic_fram;
    tb.fram.bytes[352] ^= 1; // corrupt anchor `seal_mac` -> E_ANCHOR_IO=9
    tb.reset(); cmd(tb, 0x10, {}, 0, 9);

    tb.fram = authentic_fram;
    tb.fram.bytes[48] ^= 1; // corrupt Slot 0 `journal_mac` -> E_ANCHOR_IO=9
    tb.reset(); cmd(tb, 0x10, {}, 0, 9);
    std::cout << "PASS SafeRecovery & rom_lock E_LOCKED=14, torn-slot recovery, and FRAM seal/MAC tamper rejection\n";

    // 9. Blank debug UART, GPIO, NFC, DB, JTAG lockout in provisioned state, and 0-clock stopped-CLK tamper wipe
    tb.fram = Fram();
    tb.reset(2); cmd(tb, 0x10); // virgin BOOT -> LC_BLANK with BOOT_MODE=10
    tb.write_frame(0x80, tb.make_w0(0x31, 7, 8, 0), {0});
    bool uart = false;
    for (int i = 0; i < 2500; i++) { tb.tick_core(); uart |= !tb.get_out_bidir(28); }
    check_eq("blank UART start", uart, 1);
    check_eq("verified", tb.get_out_bidir(16), 1);

    tb.set_pin_bidir(30, true); tb.dut.eval();
    check_eq("DB rapid responder 1", tb.get_out_bidir(29), 1);
    tb.set_pin_bidir(30, false); tb.dut.eval();
    check_eq("DB rapid responder 0", tb.get_out_bidir(29), 0);

    tb.set_pin_bidir(32, true);
    tb.set_pin_bidir(33, false); tb.dut.eval();
    tb.set_pin_bidir(33, true);  tb.dut.eval();
    check_eq("NFC MOD follows ASK when VERIFY_OK=1", tb.get_out_bidir(31), 1);

    auto send_uart_rx = [&](u8 byte_v) {
        tb.set_pin_bidir(27, false); tb.tick_core(25);
        for (int b = 0; b < 8; ++b) {
            tb.set_pin_bidir(27, (byte_v >> b) & 1);
            tb.tick_core(25);
        }
        tb.set_pin_bidir(27, true); tb.tick_core(30);
    };
    send_uart_rx(0xA5);

    tb.set_boot_mode(3); tb.dut.eval();
    check_eq("blank JTAG TDO OE=1", (tb.dut.bidir_oe >> 34) & 1ULL, 1);
    tb.set_pin_bidir(35, true); tb.set_pin_bidir(36, false);
    tb.set_pin_bidir(37, true); tb.dut.eval();
    tb.set_pin_bidir(37, false); tb.dut.eval();
    check_eq("blank JTAG TDO=1", tb.get_out_bidir(34), 1);

    tb.fram = authentic_fram;
    tb.reset(0);
    cmd(tb, 0x10); // -> LC_LEASE_PENDING (`prov_lock_q = 1`)
    tb.set_boot_mode(3); tb.dut.eval();
    check_eq("provisioned JTAG TDO OE=0 lockout", (tb.dut.bidir_oe >> 34) & 1ULL, 0);
    check_eq("provisioned JTAG TDO=0 lockout", tb.get_out_bidir(34), 0);

    tb.fram = Fram();
    tb.set_boot_mode(2); tb.reset(2); cmd(tb, 0x10);
    cmd(tb, 0x31, {0}, 7);
    check_eq("pre-tamper VERIFY_OK=1", tb.get_out_bidir(16), 1);

    tb.dut.clk = 0; tb.set_pin_bidir(26, false); tb.dut.eval();
    check_eq("tamper drops VERIFY_OK", tb.get_out_bidir(16), 0);
    check_eq("tamper raises FAULT", tb.get_out_bidir(17), 1);
    check_eq("tamper wipes Vault key_lo in 0 clocks", tb.dut.rootp->qsag_ass2_enclave_top__DOT__key_lo, 0);
    check_eq("tamper wipes Vault key_hi in 0 clocks", tb.dut.rootp->qsag_ass2_enclave_top__DOT__key_hi, 0);
    std::cout << "PASS blank UART/NFC/DB/JTAG, provisioned JTAG lockout, and 0-clock tamper wipe\n";
#if VM_COVERAGE
    VerilatedCov::write("coverage.dat");
#endif
    return 0;
}
