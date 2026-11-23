// Fixed instruction interface to the shared Goldilocks, Fp5 and Keccak datapaths.
using U = unsigned long;
using I = unsigned;
using B = unsigned char;
static_assert(sizeof(U) == 8 && sizeof(I) == 4);
constexpr U P = 0xffffffff00000001ul;
template <int code> static inline U cop(U x = 0, U y = 0) {
    U z;
    asm volatile(".insn r 0x0b,0,%3,%0,%1,%2" : "=r"(z) : "r"(x), "r"(y), "i"(code) : "memory");
    return z;
}
[[noreturn]] static void reject() {
    cop<0>(0);
    __builtin_unreachable();
}
static void require(bool ok) {
    if (!ok)
        reject();
}
static void check(bool ok) {
    require(ok);
    cop<2>();
}
static inline U ld(const void *p) {
    U v;
    asm("ld %0,0(%1)" : "=r"(v) : "r"(p) : "memory");
    return v;
}
static inline void sd(void *p, U v) {
    asm volatile("sd %0,0(%1)" ::"r"(v), "r"(p) : "memory");
}
extern "C" void *memcpy(void *dst, const void *src, U n) {
    B *d = (B *)dst;
    const B *s = (const B *)src;
    // Scalar ROM loads are naturally aligned. SRAM loads can be unaligned.
    while (n >= 8 && ((U(s) & 7) == 0 || (U(s) < 0x200000 || U(s) >= 0x10000000))) {
        sd(d, ld(s));
        d += 8;
        s += 8;
        n -= 8;
    }
    while (n--)
        *d++ = *s++;
    return dst;
}
extern "C" void *memset(void *dst, int value, U n) {
    B *d = (B *)dst;
    U w = B(value);
    w |= w << 8;
    w |= w << 16;
    w |= w << 32;
    while (n >= 8) {
        sd(d, w);
        d += 8;
        n -= 8;
    }
    while (n--)
        *d++ = B(value);
    return dst;
}
extern "C" U __muldi3(U a, U b) {
    U r = 0;
    while (b) {
        if (b & 1)
            r += a;
        a <<= 1;
        b >>= 1;
    }
    return r;
}
static bool same(const B *a, const B *b, I n) {
    while (n--)
        if (*a++ != *b++)
            return false;
    return true;
}
struct E {
    U v[5];
};
static E base(U x) {
    return {{x, 0, 0, 0, 0}};
}
[[gnu::noinline]] static E operator+(const E &a, const E &b) {
    E z;
    for (I i = 0; i < 5; i++)
        z.v[i] = cop<3>(a.v[i], b.v[i]);
    return z;
}
[[gnu::noinline]] static E operator-(const E &a, const E &b) {
    E z;
    for (I i = 0; i < 5; i++)
        z.v[i] = cop<4>(a.v[i], b.v[i]);
    return z;
}
[[gnu::noinline]] static E scale(const E &a, U b) {
    E z;
    for (I i = 0; i < 5; i++)
        z.v[i] = cop<5>(a.v[i], b);
    return z;
}
[[gnu::noinline]] static E operator*(const E &a, const E &b) {
    E z;
    asm volatile(".insn r 0x0b,0,6,%0,%1,%2" ::"r"(&z), "r"(&a), "r"(&b) : "memory");
    return z;
}
[[gnu::noinline]] static bool operator==(const E &a, const E &b) {
    for (I i = 0; i < 5; i++)
        if (a.v[i] != b.v[i])
            return false;
    return true;
}
struct Slice {
    const B *p;
    I n;
};
struct Reader {
    const B *p;
    I n;
    Slice take(I size) {
        require(size <= n);
        Slice s{p, size};
        p += size;
        n -= size;
        return s;
    }
    U limb() {
        U v = ld(take(8).p);
        require(v < P);
        return v;
    }
    U u64() {
        return ld(take(8).p);
    }
    I u32() {
        const B *q = take(4).p;
        I v;
        asm("lwu %0,0(%1)" : "=r"(v) : "r"(q) : "memory");
        return v;
    }
    B byte() {
        return *take(1).p;
    }
    E ext() {
        E x;
        for (U &v : x.v)
            v = limb();
        return x;
    }
    Slice blob() {
        I size = u32();
        return take(size);
    }
};
static Slice bytes(const void *p, I n) {
    return {(const B *)p, n};
}
template <U N> static Slice label(const char (&s)[N]) {
    return bytes(s, N - 1);
}
static I minimum(I a, I b) {
    return a < b ? a : b;
}
struct Sponge {
    I lane, used;
    U partial;
    void init(I dom) {
        cop<7>(dom);
        lane = used = 0;
        partial = 0;
    }
    void word(U w) {
        cop<8>(lane, w);
        if (++lane == 17) {
            cop<9>();
            lane = 0;
        }
    }
    [[gnu::noinline]] void put(Slice s) {
        while (s.n >= 8 && ((U(s.p) < 0x200000 || U(s.p) >= 0x10000000) || !(U(s.p) & 7))) {
            U w = ld(s.p);
            word(partial | (w << (8 * used)));
            partial = used ? w >> (64 - 8 * used) : 0;
            s.p += 8;
            s.n -= 8;
        }
        while (s.n--) {
            partial |= U(*s.p++) << (used * 8);
            if (++used == 8) {
                word(partial);
                partial = 0;
                used = 0;
            }
        }
    }
    void length(U n) {
        put(bytes(&n, 8));
    }
    void field(Slice s) {
        length(s.n);
        put(s);
    }
    [[gnu::noinline]] void finish(void *out, I n) {
        cop<8>(lane, partial | (7ul << (8 * used)));
        cop<8>(16, 1ul << 63);
        cop<9>();
        B *p = (B *)out;
        I i = 0;
        while (n) {
            U w = cop<10>(i);
            I count = minimum(n, 8);
            if (count == 8)
                sd(p, w);
            else
                for (I k = 0; k < count; k++)
                    p[k] = B(w >> (k * 8));
            n -= count;
            p += count;
            if (++i == 17 && n) {
                cop<9>();
                i = 0;
            }
        }
    }
};
struct Transcript {
    B chain[50];
    U counter;
    I domain, remaining;
    void start(bool hqm, B tag, const Slice *bind, I n) {
        domain = hqm ? 8 : 7;
        remaining = hqm ? 4095 : 0xffffffff;
        counter = 0;
        Sponge h;
        h.init(domain);
        h.field(label("INIT"));
        h.field(bytes(&tag, 1));
        U total = 0;
        for (I i = 0; i < n; i++)
            total += 8 + bind[i].n;
        h.length(total);
        for (I i = 0; i < n; i++)
            h.field(bind[i]);
        h.finish(chain, 50);
    }
    void charge() {
        require(remaining);
        remaining--;
    }
    [[gnu::noinline]] void absorb(Slice name, Slice s) {
        charge();
        Sponge h;
        h.init(domain);
        h.field(label("ABSORB"));
        h.field(bytes(chain, 50));
        h.field(name);
        h.field(s);
        h.finish(chain, 50);
        counter = 0;
    }
    [[gnu::noinline]] void draw(Slice kind, Slice name, U attempt, void *out, I size) {
        charge();
        Sponge h;
        h.init(domain);
        h.field(kind);
        h.field(bytes(chain, 50));
        h.field(name);
        h.field(bytes(&counter, 8));
        h.field(bytes(&attempt, 8));
        h.finish(out, size);
    }
    [[gnu::noinline]] E squeeze(Slice name, bool nonzero = false) {
        for (;;) {
            E x;
            for (U attempt = 0;; attempt++) {
                draw(label("SQUEEZE_E"), name, attempt, &x, 40);
                bool ok = true;
                for (U v : x.v)
                    if (v >= P)
                        ok = false;
                if (ok)
                    break;
            }
            counter++;
            if (!nonzero || !(x == base(0)))
                return x;
        }
    }
};
