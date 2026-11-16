// Software reference model for the QSAG-NI testbench. Written from the definitions in the qsag
// crates (qsag-accel goldilocks.rs / poseidon2.rs, qsag-agg field.rs / sponge.rs, qsag-core
// rss256.rs), with plain `%` reductions and bit-serial GF(2) arithmetic: nothing here shares a
// trick with the RTL. The model itself is checked against the Lean oracle vectors before use.
#pragma once
#include <cstdint>
#include <cstring>
#include <string>
#include <vector>
#include <array>
#include <functional>

typedef unsigned __int128 u128;
static const uint64_t GLP = 0xFFFFFFFF00000001ULL;

static inline uint64_t gl_red(uint64_t x) { return x >= GLP ? x - GLP : x; }
static inline uint64_t gl_add(uint64_t a, uint64_t b) { return (uint64_t)(((u128)gl_red(a) + gl_red(b)) % GLP); }
static inline uint64_t gl_sub(uint64_t a, uint64_t b) { return (uint64_t)(((u128)gl_red(a) + GLP - gl_red(b)) % GLP); }
static inline uint64_t gl_mul(uint64_t a, uint64_t b) { return (uint64_t)(((u128)a * b) % GLP); }
static inline uint64_t gl_pow7(uint64_t x) {
    uint64_t x2 = gl_mul(x, x), x3 = gl_mul(x2, x), x4 = gl_mul(x2, x2);
    return gl_mul(x3, x4);
}
// (t * 2^128 + lo) mod p for an 8-bit t.
static inline uint64_t gl_red136(uint8_t t, u128 lo) {
    uint64_t two128 = (uint64_t)((((u128)1 << 127) % GLP) * 2 % GLP);
    return (uint64_t)(((u128)(uint64_t)(lo % GLP) + (u128)gl_mul(t, two128)) % GLP);
}

// ---- GoldilocksExt4 = F_p[v]/(v^4 - 7); limbs [c0.c0, c0.c1, c1.c0, c1.c1] = [1, v^2, v, v^3].
typedef std::array<uint64_t, 4> E4;
static inline E4 e4_mul_add(const E4& a, const E4& b, const E4& c) {
    static const int PIDX[4] = {0, 2, 1, 3};
    uint64_t pa[4], pb[4], pc[4], po[4];
    for (int s = 0; s < 4; s++) { pa[PIDX[s]] = a[s]; pb[PIDX[s]] = b[s]; pc[PIDX[s]] = c[s]; }
    for (int k = 0; k < 4; k++) {
        uint64_t acc = gl_red(pc[k]);
        for (int i = 0; i < 4; i++) {
            if (i <= k) acc = gl_add(acc, gl_mul(pa[i], pb[k - i]));
            else        acc = gl_add(acc, gl_mul(7, gl_mul(pa[i], pb[k + 4 - i])));
        }
        po[k] = acc;
    }
    E4 o;
    for (int s = 0; s < 4; s++) o[s] = po[PIDX[s]];
    return o;
}
static inline E4 e4_add(const E4& a, const E4& b) { E4 o; for (int i = 0; i < 4; i++) o[i] = gl_add(a[i], b[i]); return o; }
static inline E4 e4_sub(const E4& a, const E4& b) { E4 o; for (int i = 0; i < 4; i++) o[i] = gl_sub(a[i], b[i]); return o; }
static inline E4 e4_mul(const E4& a, const E4& b) { return e4_mul_add(a, b, E4{0, 0, 0, 0}); }

// ---- Poseidon2 width 12 (qsag-accel poseidon2.rs).
typedef std::array<uint64_t, 12> St12;
static inline uint64_t p2_bij(uint64_t x) {
    uint64_t z0 = x + 0x9E3779B97F4A7C15ULL;
    uint64_t z1 = (z0 ^ (z0 >> 30)) * 0xBF58476D1CE4E5B9ULL;
    uint64_t z2 = (z1 ^ (z1 >> 27)) * 0x94D049BB133111EBULL;
    return z2 ^ (z2 >> 31);
}
static inline uint64_t p2_const_at(uint64_t tag, uint64_t round, uint64_t lane) {
    return gl_red(p2_bij(p2_bij(p2_bij(0x504F53325F474C31ULL ^ tag) ^ round) ^ lane));
}
static inline void p2_m4(uint64_t* b) {
    uint64_t s = gl_add(gl_add(b[0], b[1]), gl_add(b[2], b[3]));
    uint64_t r0 = gl_add(s, gl_add(b[0], gl_add(b[1], b[1])));
    uint64_t r1 = gl_add(s, gl_add(b[1], gl_add(b[2], b[2])));
    uint64_t r2 = gl_add(s, gl_add(b[2], gl_add(b[3], b[3])));
    uint64_t r3 = gl_add(s, gl_add(b[3], gl_add(b[0], b[0])));
    b[0] = r0; b[1] = r1; b[2] = r2; b[3] = r3;
}
static inline void p2_me(St12& st) {
    St12 t = {st[0], st[3], st[6], st[9], st[1], st[4], st[7], st[10], st[2], st[5], st[8], st[11]};
    for (auto& x : t) x = gl_red(x);
    p2_m4(&t[0]); p2_m4(&t[4]); p2_m4(&t[8]);
    for (int i = 0; i < 4; i++) {
        uint64_t y0 = t[i], y1 = t[4 + i], y2 = t[8 + i];
        uint64_t s = gl_add(gl_add(y0, y1), y2);
        t[i] = gl_add(y0, s); t[4 + i] = gl_add(y1, s); t[8 + i] = gl_add(y2, s);
    }
    st = {t[0], t[4], t[8], t[1], t[5], t[9], t[2], t[6], t[10], t[3], t[7], t[11]};
}
static inline void p2_mi(St12& st) {
    uint64_t s = 0;
    for (auto x : st) s = gl_add(s, x);
    st[0] = gl_add(gl_sub(0, gl_mul(64, st[0])), s);
    st[1] = gl_add(st[1], s);
    uint64_t d = 2;
    for (int i = 2; i < 12; i++) { st[i] = gl_add(gl_mul(d, st[i]), s); d = gl_add(d, d); }
}
static inline void p2_perm(St12& st) {
    p2_me(st);
    for (uint64_t r = 0; r < 4; r++) {
        for (int l = 0; l < 12; l++) st[l] = gl_pow7(gl_add(st[l], p2_const_at(0, r, l)));
        p2_me(st);
    }
    for (uint64_t r = 0; r < 22; r++) {
        st[0] = gl_pow7(gl_add(st[0], p2_const_at(1, r, 0)));
        p2_mi(st);
    }
    for (uint64_t r = 0; r < 4; r++) {
        for (int l = 0; l < 12; l++) st[l] = gl_pow7(gl_add(st[l], p2_const_at(2, r, l)));
        p2_me(st);
    }
}
// Weighted feed-forward node hash of [l, r, t] (merkle_layer_poseidon2_fixed_tweak_cpu).
typedef std::array<uint64_t, 4> D4;
static inline D4 p2_jive(const St12& in) {
    St12 st = in;
    p2_perm(st);
    D4 o;
    for (int i = 0; i < 4; i++)
        o[i] = gl_add(st[i], gl_add(gl_red(in[i]), gl_add(gl_mul(2, in[4 + i]), gl_mul(4, in[8 + i]))));
    return o;
}
static const uint64_t CANOPY_NODE_HI = 0x50324E4400000000ULL;
// merkle_layer_poseidon2_canopy_at_cpu for one parent.
static inline D4 p2_canopy_node(const D4& l, const D4& r, uint32_t node_idx, const uint64_t key[3]) {
    St12 in = {l[0], l[1], l[2], l[3], r[0], r[1], r[2], r[3], CANOPY_NODE_HI | node_idx, key[0], key[1], key[2]};
    return p2_jive(in);
}
// Blocks of poseidon2_sponge_hash_limbs_with_cap, as the host frames them for the chain engine.
static inline std::vector<std::array<uint64_t, 8>> p2_sponge_blocks(uint64_t domain, const std::vector<uint64_t>& limbs) {
    std::vector<std::array<uint64_t, 8>> blocks;
    std::array<uint64_t, 8> b{};
    b[0] = gl_red(domain); b[1] = gl_red(limbs.size());
    size_t head = limbs.size() < 6 ? limbs.size() : 6;
    for (size_t i = 0; i < head; i++) b[2 + i] = gl_red(limbs[i]);
    blocks.push_back(b);
    size_t pos = head;
    while (pos + 8 <= limbs.size()) {
        for (int i = 0; i < 8; i++) b[i] = gl_red(limbs[pos + i]);
        blocks.push_back(b); pos += 8;
    }
    if (pos < limbs.size()) {
        b.fill(0);
        for (size_t i = 0; pos + i < limbs.size(); i++) b[i] = gl_red(limbs[pos + i]);
        blocks.push_back(b);
    }
    return blocks;
}
static inline D4 p2_sponge_with_cap(uint64_t domain, const D4& cap, const std::vector<uint64_t>& limbs) {
    St12 st{};
    for (int i = 0; i < 4; i++) st[8 + i] = gl_red(cap[i]);
    for (auto& blk : p2_sponge_blocks(domain, limbs)) {
        for (int i = 0; i < 8; i++) st[i] = gl_add(st[i], blk[i]);
        p2_perm(st);
    }
    return D4{st[0], st[1], st[2], st[3]};
}

// ---- Keccak.
typedef std::array<uint64_t, 25> KState;
static const uint64_t KRC[24] = {
    0x0000000000000001ULL, 0x0000000000008082ULL, 0x800000000000808AULL, 0x8000000080008000ULL,
    0x000000000000808BULL, 0x0000000080000001ULL, 0x8000000080008081ULL, 0x8000000000008009ULL,
    0x000000000000008AULL, 0x0000000000000088ULL, 0x0000000080008009ULL, 0x000000008000000AULL,
    0x000000008000808BULL, 0x800000000000008BULL, 0x8000000000008089ULL, 0x8000000000008003ULL,
    0x8000000000008002ULL, 0x8000000000000080ULL, 0x000000000000800AULL, 0x800000008000000AULL,
    0x8000000080008081ULL, 0x8000000000008080ULL, 0x0000000080000001ULL, 0x8000000080008008ULL};
static inline uint64_t rotl64(uint64_t x, int n) { return n ? (x << n) | (x >> (64 - n)) : x; }
// nr12: rounds 12..23 only (Keccak-p[1600, 12]).
static inline void keccak_p(KState& a, bool nr12) {
    for (int rnd = nr12 ? 12 : 0; rnd < 24; rnd++) {
        uint64_t c[5], d[5];
        for (int x = 0; x < 5; x++) c[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
        for (int x = 0; x < 5; x++) d[x] = c[(x + 4) % 5] ^ rotl64(c[(x + 1) % 5], 1);
        for (int i = 0; i < 25; i++) a[i] ^= d[i % 5];
        // rho + pi along the (x, y) -> (y, 2x + 3y) orbit.
        int x = 1, y = 0;
        uint64_t cur = a[1];
        for (int t = 0; t < 24; t++) {
            int nx = y, ny = (2 * x + 3 * y) % 5;
            uint64_t tmp = a[nx + 5 * ny];
            a[nx + 5 * ny] = rotl64(cur, ((t + 1) * (t + 2) / 2) % 64);
            cur = tmp; x = nx; y = ny;
        }
        for (int yy = 0; yy < 5; yy++) {
            uint64_t row[5];
            for (int xx = 0; xx < 5; xx++) row[xx] = a[xx + 5 * yy];
            for (int xx = 0; xx < 5; xx++) a[xx + 5 * yy] = row[xx] ^ (~row[(xx + 1) % 5] & row[(xx + 2) % 5]);
        }
        a[0] ^= KRC[rnd];
    }
}
typedef std::function<void(KState&, bool)> KPerm;
// Sponge with capacity 512 (rate 136 bytes): SHAKE256 (ds 0x1F), cSHAKE256 (0x04),
// TurboSHAKE256 (nr12, any domain byte 0x01..0x7F), SHA3-256 uses rate 136 with ds 0x06.
static inline std::vector<uint8_t> keccak_sponge(const std::vector<uint8_t>& msg, uint8_t ds, size_t outlen,
                                                 bool nr12, const KPerm& perm) {
    const size_t rate = 136;
    KState st{};
    auto xor_byte = [&](size_t i, uint8_t v) { st[i / 8] ^= (uint64_t)v << (8 * (i % 8)); };
    size_t off = 0;
    for (uint8_t b : msg) {
        xor_byte(off++, b);
        if (off == rate) { perm(st, nr12); off = 0; }
    }
    xor_byte(off, ds);
    xor_byte(rate - 1, 0x80);
    perm(st, nr12);
    std::vector<uint8_t> out;
    while (out.size() < outlen) {
        for (size_t i = 0; i < rate && out.size() < outlen; i++) out.push_back((uint8_t)(st[i / 8] >> (8 * (i % 8))));
        if (out.size() < outlen) perm(st, nr12);
    }
    return out;
}
static inline std::vector<uint8_t> left_encode(uint64_t x) {
    std::vector<uint8_t> v;
    int n = 1;
    while (n < 8 && (x >> (8 * n)) != 0) n++;
    v.push_back((uint8_t)n);
    for (int i = n - 1; i >= 0; i--) v.push_back((uint8_t)(x >> (8 * i)));
    return v;
}
// cSHAKE256 with empty function name N and customization S (NIST SP 800-185).
static inline std::vector<uint8_t> cshake256(const std::vector<uint8_t>& msg, const std::string& custom,
                                             size_t outlen, const KPerm& perm) {
    std::vector<uint8_t> p = left_encode(136);
    auto app = [&](const std::vector<uint8_t>& v) { p.insert(p.end(), v.begin(), v.end()); };
    app(left_encode(0));
    app(left_encode(custom.size() * 8));
    p.insert(p.end(), custom.begin(), custom.end());
    while (p.size() % 136) p.push_back(0);
    p.insert(p.end(), msg.begin(), msg.end());
    return keccak_sponge(p, 0x04, outlen, false, perm);
}

// ---- GF(2^128) = GF(2)[x]/(x^128 + x^7 + x^2 + x + 1), bit j = coefficient of x^j.
static inline u128 gf128_mul(u128 a, u128 b) {
    u128 r = 0;
    for (int i = 127; i >= 0; i--) {
        bool carry = (r >> 127) & 1;
        r <<= 1;
        if (carry) r ^= 0x87;
        if ((b >> i) & 1) r ^= a;
    }
    return r;
}

// ---- helpers
static inline std::vector<uint8_t> from_hex(const std::string& h) {
    std::vector<uint8_t> v;
    for (size_t i = 0; i + 1 < h.size(); i += 2) v.push_back((uint8_t)std::stoul(h.substr(i, 2), nullptr, 16));
    return v;
}
static inline std::string to_hex(const std::vector<uint8_t>& v) {
    static const char* d = "0123456789abcdef";
    std::string s;
    for (uint8_t b : v) { s.push_back(d[b >> 4]); s.push_back(d[b & 15]); }
    return s;
}
struct Rng {
    uint64_t s;
    explicit Rng(uint64_t seed) : s(seed) {}
    uint64_t next() { s += 0x9E3779B97F4A7C15ULL; uint64_t z = s; z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL; z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL; return z ^ (z >> 31); }
    uint64_t gl() { return next() % GLP; }
    // Mix of uniform values and Goldilocks corner cases.
    uint64_t edge() {
        static const uint64_t E[] = {0, 1, 2, GLP - 1, GLP, GLP + 1, ~0ULL, 0xFFFFFFFFULL, 0x100000000ULL,
                                     0xFFFFFFFEFFFFFFFFULL, 0xFFFFFFFF00000000ULL, 0x8000000000000000ULL};
        uint64_t r = next();
        return (r & 7) == 0 ? E[(r >> 8) % 12] : next();
    }
    E4 e4() { return E4{gl(), gl(), gl(), gl()}; }
};
