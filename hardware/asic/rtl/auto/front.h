static E eq_index(const E *point, I n, I index) {
    E w = base(1);
    for (I i = 0; i < n; i++)
        w = w * ((index >> i) & 1 ? point[i] : base(1) - point[i]);
    return w;
}
static E prefix(const E *x, I n, I count) {
    if (count >> n)
        return base(1);
    E sum = base(0), w = base(1);
    while (n--) {
        E low = base(1) - x[n];
        if ((count >> n) & 1) {
            sum = sum + w * low;
            w = w * x[n];
        } else
            w = w * low;
    }
    return sum;
}
static E inverse(const E &x) {
    // Square and multiply with the fixed exponent p^5-2, most-significant bit first.
    static constexpr U exp[5] = {0xfffffffafffffffful, 0xffffffe20000000eul, 0xffffffcd0000002cul,
                                 0xffffffe20000002cul, 0xfffffffb0000000eul};
    E a = base(1);
    for (I i = 320; i--;) {
        a = a * a;
        if ((exp[i >> 6] >> (i & 63)) & 1)
            a = a * x;
    }
    return a;
}
static E sumcheck(Reader &r, Transcript &t, Slice name, I rounds, I degree, const E &initial, E *point) {
    E claim = initial;
    for (I i = 0; i < rounds; i++) {
        E c[10];
        read_ext(r, c, degree + 1);
        absorb(t, name, c, degree + 1);
        point[i] = t.squeeze(name);
        U coefficients = U(c) | U(degree == 9);
        asm volatile(".insn r 0x0b,0,14,%0,%1,%2" ::"r"(coefficients), "r"(&claim), "r"(&point[i])
                     : "memory");
    }
    return claim;
}
struct Front {
    E rx[28], ry[28], lambda, rho2, matrix, hpoint[28];
    I rows, vars, npublic, mask_base, var_cells;
    bool hqm;
    E apply(const Kernel &k, const E *poly, I size) const {
        if (hqm)
            return k.tensor(base(1), hpoint, rows + 8, 0, poly, size);
        E total = base(0), lam[5];
        lam[0] = base(1);
        for (I i = 1; i < 5; i++)
            lam[i] = lam[i - 1] * lambda;
        for (I part = 0; part < 2; part++) {
            I bits = part ? 2 : 4, n = part ? vars : rows, offset = mask_base + (part ? rows * 80 : 0);
            const E *point = part ? ry : rx;
            for (I i = 0; i < n; i++) {
                E pow[4];
                pow[0] = point[i];
                for (I m = 1; m < bits; m++)
                    pow[m] = pow[m - 1] * pow[m - 1];
                for (I j = 0; j < 5; j++) {
                    E limb = base(0);
                    limb.v[j] = 1;
                    I block = offset + ((i * 5 + j) << bits);
                    E w = scale(lam[part] * limb, 1ul << (n - 1));
                    total = total + k.tensor(w, nullptr, 0, block, poly, size) +
                            k.tensor(w, nullptr, 0, block + ((1u << bits) - 1), poly, size);
                    E weight = lam[2 + part] * limb;
                    if (part)
                        weight = weight * rho2;
                    total = total + k.tensor(weight, pow, bits, block, poly, size);
                }
            }
        }
        I count = minimum(var_cells, 1u << vars), start = 0;
        for (I a = vars + 1; a--;)
            if ((count >> a) & 1) {
                E w = lam[3] * matrix * eq_index(ry + a, vars - a, start >> a);
                total = total + k.tensor(w, ry, a, start, poly, size);
                start += 1u << a;
            }
        E w = lam[4];
        for (I i = 0; i <= npublic; i++) {
            total = total + k.tensor(w, nullptr, 0, i, poly, size);
            w = w * lambda;
        }
        return total;
    }
    E zk(Reader &r, Reader &desc, Transcript &t, Geometry &geometry, Slice magic, B *commitment) {
        B tag = r.byte();
        I log = r.byte();
        require(tag == 17);
        geometry.init(log);
        Slice digest = desc.take(32), layout = desc.blob(), message = desc.blob(), pub = desc.blob();
        Slice bind[] = {magic, digest, layout, message, pub};
        t.start(false, tag, bind, 5);
        Reader l{layout.p, layout.n};
        auto small = [&]() {
            U v = l.u64();
            require(v <= (1u << 28));
            return I(v);
        };
        rows = small();
        I nvars = small();
        npublic = small();
        require(small() == log);
        vars = small();
        var_cells = small();
        (void)small();
        mask_base = small();
        (void)small();
        require(rows >= 5 && rows <= 28 && vars > 0 && vars <= 28 && nvars <= (1u << vars) &&
                npublic < nvars && pub.n == U(npublic) * 8 && mask_base == var_cells &&
                U(mask_base) + 80 * U(rows) + 20 * U(vars) <= (1ul << log));
        require(small() == geometry.stop && small() == geometry.stages);
        for (I i = 0; i < geometry.stages; i++)
            require(small() == (1u << (2 * i + 2)) && small() == geometry.d[i].step &&
                    small() == geometry.d[i].count);
        require(!l.n);
        I sbox = desc.u32();
        require(sbox <= (1u << rows));
        memcpy(commitment, r.take(82).p, 82);
        t.absorb(label("STAGE0_ROOT"), bytes(commitment, 82));
        E tau[28];
        for (I i = 0; i < rows; i++)
            tau[i] = t.squeeze(label("TAU"));
        E rs = r.ext();
        absorb(t, label("ROW_MASK_SUM"), &rs, 1);
        E rho = t.squeeze(label("RHO1"), true);
        E row = sumcheck(r, t, label("ROW_ROUND"), rows, 9, rho * rs, rx);
        E v[3];
        read_ext(r, v, 3);
        absorb(t, label("ROW_VALUES"), v, 3);
        E eq = base(1);
        for (I i = 0; i < rows; i++)
            eq = eq * (scale(tau[i] * rx[i], 2) + base(1) - tau[i] - rx[i]);
        E ab = v[0] * v[1], a2 = v[0] * v[0];
        E gate = prefix(rx, rows, sbox) * (a2 * a2 * a2 * v[0] - ab) + ab - v[2];
        E mask = (row - eq * gate) * inverse(rho);
        E combine[3], col = base(0);
        for (I i = 0; i < 3; i++) {
            combine[i] = t.squeeze(label("COMBINE"));
            col = col + combine[i] * v[i];
        }
        E cs = r.ext();
        absorb(t, label("COL_MASK_SUM"), &cs, 1);
        rho2 = t.squeeze(label("RHO2"), true);
        col = sumcheck(r, t, label("COL_ROUND"), vars, 2, col + rho2 * cs, ry);
        lambda = t.squeeze(label("LAMBDA"));
        matrix = base(0);
        for (I m = 0; m < 3; m++)
            for (I i = 0; i < (1u << rows); i++) {
                I entries = desc.u32();
                if (!entries)
                    continue;
                E dot = base(0);
                while (entries--) {
                    I j = desc.u32();
                    require(j < nvars);
                    dot = dot + scale(eq_index(ry, vars, j), desc.limb());
                }
                matrix = matrix + eq_index(rx, rows, i) * combine[m] * dot;
            }
        Reader public_r{pub.p, pub.n};
        E vals[] = {rs, cs, mask, col, base(1)};
        E value = poly(vals, 5, lambda), w = base(1);
        for (I i = 0; i < 5; i++)
            w = w * lambda;
        for (I i = 0; i < npublic; i++) {
            value = value + scale(w, public_r.limb());
            w = w * lambda;
        }
        return value;
    }
};
