// The canonical Johnson schedule, with the same bounds as stage_dims().
constexpr I MAX_Q = 267;
struct Dims {
    I step, depth, count;
};
struct Geometry {
    I stages, stop;
    Dims d[4];
    void init(I log) {
        static const B steps[13][4] = {{4, 3, 3, 0}, {5, 3, 4, 0}, {5, 3, 4, 0}, {5, 3, 4, 0},
                                       {5, 3, 4, 0}, {6, 3, 4, 0}, {6, 4, 4, 0}, {6, 4, 3, 3},
                                       {6, 4, 3, 3}, {6, 4, 4, 3}, {6, 5, 4, 3}, {6, 5, 4, 4},
                                       {6, 6, 4, 4}};
        require(log >= 16 && log <= 28);
        I vars = log;
        stages = 0;
        for (I i = 0; i < 4; i++) {
            I step = steps[log - 16][i];
            if (!step)
                break;
            I domain = vars + 2 * (i + 1);
            require(domain <= 32 && domain - step <= 28);
            static const I queries[] = {0, 136, 92, 70};
            d[i] = {step, domain - step,
                    minimum(1u << (domain - step), i ? queries[i] : (log < 24 ? 267u : 266u))};
            stages++;
            vars -= step;
        }
        stop = vars;
    }
};
struct Challenge {
    E theta, alpha, beta;
};
struct Point {
    E w, x;
};
static E poly(const E *c, I n, const E &x) {
    E y = base(0);
    while (n)
        y = y * x + c[--n];
    return y;
}
struct Kernel {
    // Defer tensor terms to terminal evaluation. phi[] is all that folding
    // them needs. This avoids retaining a vector of full points for each mask.
    E phi[28];
    I used;
    Point points[MAX_Q + 136 + 92 + 12];
    I np;
    [[gnu::noinline]] void add(const E &w, const E &x) {
        require(np < sizeof(points) / sizeof(*points));
        points[np++] = {w, x};
    }
    [[gnu::noinline]] void fold(const E &r) {
        require(used < 28);
        phi[used++] = r;
        for (I i = 0; i < np; i++) {
            Point &p = points[i];
            p.w = p.w * (base(1) + r * p.x);
            p.x = p.x * p.x;
        }
    }
    [[gnu::noinline]] E tensor(const E &initial, const E *coords, I n, I block, const E *coeff, I size) const {
        E w = initial;
        for (I i = 0; i < used; i++) {
            if (i < n)
                w = w * (base(1) + phi[i] * coords[i]);
            else if ((block >> i) & 1)
                w = w * (base(1) + phi[i]);
        }
        // Evaluate the remaining multilinear monomials, padded with zeros.
        E v = base(0);
        for (I j = 0; j < size - 2; j++) {
            if (((j << used) & ~((1u << n) - 1) & ~block) != 0)
                continue;
            E t = coeff[j];
            for (I i = used; i < n; i++)
                if ((j >> (i - used)) & 1)
                    t = t * coords[i];
            v = v + t;
        }
        return w * v;
    }
    E univariate(const E *coeff, I size) const {
        E acc = base(0);
        for (I i = 0; i < np; i++)
            acc = acc + points[i].w * poly(coeff, size, points[i].x);
        return acc;
    }
};
static void read_ext(Reader &r, E *v, I n) {
    for (I i = 0; i < n; i++)
        v[i] = r.ext();
}
static void absorb(Transcript &t, Slice name, const E *v, I n) { t.absorb(name, bytes(v, 40 * n)); }
static Challenge fold_round(Reader &r, Transcript &t, Kernel &k, E &claim) {
    E a[5];
    read_ext(r, a, 5);
    absorb(t, label("FOLD_A"), a, 3);
    E phi = t.squeeze(label("FOLD_PHI"));
    absorb(t, label("FOLD_B"), a + 3, 2);
    Challenge c = {t.squeeze(label("FOLD_THETA")), t.squeeze(label("FOLD_ALPHA")),
                   t.squeeze(label("FOLD_BETA"))};
    E f = a[0] + phi * a[1], g = a[2] + phi * (claim - a[0]);
    claim = g + c.alpha * (f + c.theta * g) + c.beta * (a[3] + c.theta * a[4]);
    k.fold(phi);
    return c;
}
#include "roots.h"
static U power(U w, I j) {
    U a = 1;
    while (j) {
        if (j & 1)
            a = cop<5>(a, w);
        w = cop<5>(w, w);
        j >>= 1;
    }
    return a;
}
static E butterfly(const E &a, const E &b, U xt, U inv, const Challenge &c) {
    E slot[10] = {a, b, c.theta, c.alpha, c.beta, base(xt), base(inv), base((P >> 1) + 1)};
    for (I step = 0; step < 12; step++) {
        I op = I(cop<13>(step)), d = (op >> 8) & 15;
        const E &l = slot[(op >> 4) & 15], &r = slot[op & 15];
        switch (op >> 12) {
        case 0:
            slot[d] = l + r;
            break;
        case 1:
            slot[d] = l - r;
            break;
        case 2:
            slot[d] = l * r;
            break;
        default:
            slot[d] = scale(l, r.v[0]);
            break;
        }
    }
    return slot[0];
}
static E fiber(E *v, const Dims &d, I index, const Challenge *ch, U &image) {
    I log_domain = d.step + d.depth;
    U x = cop<5>(7, power(ROOT[log_domain], index)),
      inv = cop<5>(INV_SHIFT, power(INV_ROOT[log_domain], index));
    for (I s = 0; s < d.step; s++) {
        I log = d.step - s, half = 1u << (log - 1);
        U xt = x, xt_inv = inv;
        for (I j = 0; j < half; j++) {
            v[j] = butterfly(v[j], v[j + half], xt, xt_inv, ch[s]);
            xt = cop<5>(xt, ROOT[log]);
            xt_inv = cop<5>(xt_inv, INV_ROOT[log]);
        }
        x = cop<5>(x, x);
        inv = cop<5>(inv, inv);
    }
    image = x;
    return v[0];
}
struct Node {
    I index;
    B digest[50];
};
static void query_indices(Transcript &t, U *idx, const Dims &d) {
    U raw[MAX_Q];
    I n = 0;
    while (n < d.count) {
        I need = d.count - n;
        t.draw(label("SQUEEZE_IDX"), label("QUERY"), 0, raw, 8 * need);
        t.counter++;
        for (I j = 0; j < need; j++) {
            I key = I(raw[j]) & ((1u << d.depth) - 1);
            n = I(cop<11>(U(idx), (U(n) << 32) | key));
        }
    }
}
static void openings(Reader &r, Transcript &t, bool hqm, I stage, const Dims &d, Slice root, Slice nonce,
                     const Challenge *ch, const E &beta_r, U *images, E *values) {
    U idx[MAX_Q];
    query_indices(t, idx, d);
    Node frontier[2][MAX_Q];
    Node *curr = frontier[0], *next = frontier[1];
    I arity = 1u << d.step, dom = hqm ? 9 : 6;
    for (I j = 0; j < d.count; j++) {
        Node &leaf = curr[j];
        leaf.index = (1u << d.depth) + I(idx[j]);
        Sponge h;
        h.init(dom);
        B hdr[] = {B(hqm ? 0 : stage ? 0x12 : 0x10), B(hqm || stage ? stage : d.step), B(d.step)};
        h.put(bytes(hdr, !hqm && stage ? 3 : 2));
        h.put(bytes(&idx[j], 4));
        if (!stage && !hqm) {
            h.put(nonce);
            h.put(r.take(32));
        }
        E v[64], mask = base(0);
        if (stage) {
            read_ext(r, v, arity);
            h.put(bytes(v, 40 * arity));
        } else {
            U symbols[64];
            for (I k = 0; k < arity; k++) {
                symbols[k] = r.limb();
                v[k] = base(symbols[k]);
            }
            h.put(bytes(symbols, 8 * arity));
            if (!hqm) {
                mask = r.ext();
                h.put(bytes(&mask, 40));
            }
        }
        h.finish(leaf.digest, 50);
        values[j] = fiber(v, d, idx[j], ch, images[j]);
        if (!stage && !hqm)
            values[j] = values[j] + beta_r * mask;
    }
    I siblings = hqm ? 0 : r.u32(), cursor = 0, n = d.count;
    require(hqm || siblings <= n * d.depth);
    for (I level = 0; level < d.depth; level++) {
        I k = 0, write = 0;
        while (k < n) {
            Node &child = curr[k++];
            I u = child.index;
            Slice sibling;
            U ctrl = cop<12>(u, (U(hqm || cursor < siblings) << 32) | (k < n ? curr[k].index : 0));
            require(!(ctrl & 8));
            if (ctrl & 1)
                sibling = bytes(curr[k++].digest, 50);
            else {
                sibling = r.take(50);
                cursor += I((ctrl >> 1) & 1);
            }
            Slice own = bytes(child.digest, 50);
            Node &parent = next[write++];
            parent.index = I(ctrl >> 4);
            Sponge h;
            h.init(dom);
            B tag = B(hqm);
            h.put(bytes(&tag, 1));
            h.put(bytes(&parent.index, 4));
            h.put(ctrl & 4 ? sibling : own);
            h.put(ctrl & 4 ? own : sibling);
            h.finish(parent.digest, 50);
        }
        Node *tmp = curr;
        curr = next;
        next = tmp;
        n = write;
    }
    require(n == 1 && curr[0].index == 1 && (hqm || cursor == siblings));
    B hdr[] = {B(hqm ? 2 : 1), B(stage), B(d.depth)}, actual[50];
    Sponge h;
    h.init(dom);
    h.put(bytes(hdr, 3));
    h.put(bytes(curr[0].digest, 50));
    h.finish(actual, 50);
    check(same(actual, root.p, 50));
}
