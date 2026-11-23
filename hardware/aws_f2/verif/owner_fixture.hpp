// Test-only owner. Inputs are public ASS2 replies and deterministic owner test keys.
// TurboSHAKE and WOTS+C encoding follow hardware/ass2/sim/sim_enclave_top.cpp.
#pragma once
#include <cassert>
#include <cstring>
using u8 = uint8_t;
using u32 = uint32_t;
using u128 = unsigned __int128;
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

// A LEASE authorizes one HALT image. GATE installs the CTH capability for
// the generation reached after an inline WOTS+C LOAD_CODE advances the slot.
struct Owner {
    unsigned epoch, vat;
    Key32 id{};
    Owner(unsigned e, unsigned v) : epoch(e), vat(v) {}
    Key32 sk(unsigned index) const {
        return make_seed(index == 0 ? 0 : 1 + (epoch*3 + vat)*4 + index);
    }
    static constexpr u64 code = 0x50000;
    static constexpr Digest16 sibling{0x1122334455667788ULL, 0x99aabbccddeeff00ULL};
    u64 gate_record() const { return (3ULL << 32) | (7 + vat); }
    static Words cap_load() { return {1 | (code << 32), sibling[0], sibling[1]}; }

    Words payload(unsigned op, Digest16 nonce = {}, u64 record = 0) const {
        if (op == 0x11) {
            auto pk = wots_pubkey(sk(0));
            return Words(pk.begin(), pk.end());
        }
        if (op == 0x12)
            return owner_lifecycle_frame(sk(0), id, op, 0, nonce, record, {}, wots_pubkey(sk(1)));
        auto img = compute_img_id(id, {code});
        if (op == 0x15)
            return owner_lifecycle_frame(sk(1), id, op, record, nonce, record,
                                        cap_commit_code(img, sibling), wots_pubkey(sk(2)));
        if (op == 0x30) {
            Words image{1 | (code << 32)};
            auto proof = wots_sign(sk(3), id, op, 1, nonce, record, img, wots_pubkey(sk(4)));
            image.insert(image.end(), proof.begin(), proof.end());
            return image;
        }
        Words meta{0x100000000012ULL, 45, 9, 10, 11, 12, 1234};
        Words transcript(meta);
        transcript.insert(transcript.end(), {id[0], id[1], gate_record() + (1ULL << 32), 0x43541});
        Key32 header{};
        turboshake256(reinterpret_cast<const u8*>(transcript.data()), transcript.size()*8,
                      reinterpret_cast<u8*>(header.data()), 32);
        u128 dual = gf128_mul((u128(header[3]) << 64) | header[2], 3);
        Words request{1, 0, 3, 0, u64(dual), u64(dual >> 64)};
        if (op == 0x20) {
            request.insert(request.end(), meta.begin(), meta.end());
            request.insert(request.end(), sibling.begin(), sibling.end());
            return request;
        }
        if (op != 0x16) throw std::runtime_error("unknown owner fixture opcode");
        Words binding{header[0], header[1]};
        binding.insert(binding.end(), request.begin(), request.end());
        Digest16 req_id{};
        turboshake256(reinterpret_cast<const u8*>(binding.data()), binding.size()*8,
                      reinterpret_cast<u8*>(req_id.data()), 16);
        return owner_lifecycle_frame(sk(2), id, op, 7 + vat, nonce, record,
                                    cap_commit_cth(sibling, req_id), wots_pubkey(sk(3)));
    }
};

// Public Poseidon2-12 compression for the fixed digit-2 request above.
static constexpr u64 prime = 0xffffffff00000001ULL;
using State12 = std::array<u64, 12>;
static u64 mix_constant(u64 x) {
    x += 0x9e3779b97f4a7c15ULL;
    x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
    x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
    return x ^ (x >> 31);
}
static u64 sbox(u64 x, unsigned tag, unsigned round, unsigned lane) {
    u64 rc = mix_constant(mix_constant(mix_constant(0x504f53325f474c31ULL ^ tag) ^ round) ^ lane);
    u128 a = (u128(x) + rc) % prime, b = a*a % prime;
    return ((b*b % prime)*b % prime)*a % prime;
}
static void external_matrix(State12 &s) {
    State12 y{};
    for (unsigned c=0; c<3; ++c) {
        u128 sum = u128(s[c]) + s[c+3] + s[c+6] + s[c+9];
        for (unsigned i=0; i<4; ++i)
            y[c+3*i] = (sum + s[c+3*i] + 2*u128(s[c+3*((i+1)%4)])) % prime;
    }
    for (unsigned i=0; i<12; i+=3) {
        u128 sum = u128(y[i]) + y[i+1] + y[i+2];
        for (unsigned c=0; c<3; ++c) s[i+c] = (sum + y[i+c]) % prime;
    }
}
static Key32 public_endpoint(const Key32 &element) {
    State12 input{element[0],element[1],element[2],element[3], 9,10,11,12,
                  0x5153414757535450ULL,0x100000000012ULL,45,0};
    State12 s = input;
    external_matrix(s);
    for (unsigned phase=0; phase<3; ++phase) {
        for (unsigned r=0; r<(phase == 1 ? 22u : 4u); ++r) {
            if (phase == 1) {
                s[0] = sbox(s[0], phase, r, 0);
                u128 sum = 0;
                for (auto x : s) sum += x;
                for (unsigned i=0; i<12; ++i) {
                    u64 diag = i == 0 ? prime-64 : 1ULL << (i-1);
                    s[i] = (sum + (u128(diag)*s[i]) % prime) % prime;
                }
            } else {
                for (unsigned i=0; i<12; ++i) s[i] = sbox(s[i], phase, r, i);
                external_matrix(s);
            }
        }
    }
    Key32 pk{};
    for (unsigned i=0; i<4; ++i)
        pk[i] = (u128(s[i]) + element[i] + 2*u128(input[i+4]) + 4*u128(input[i+8])) % prime;
    return pk;
}
