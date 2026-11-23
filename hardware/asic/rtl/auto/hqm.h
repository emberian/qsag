// Canonical unsigned LEB128 for lengths bounded by the 32-bit descriptor.
static I leb128(Reader &r) {
    I value = 0;
    for (I shift = 0;; shift += 7) {
        B b = r.byte();
        require(shift < 28 || b <= 15);
        value |= I(b & 127) << shift;
        if (!(b & 128)) {
            require(!shift || b);
            return value;
        }
    }
}

// Stream the framed bytes through slot zero. A full rate block is permuted
// before the next limb is added. Only the partial seven-byte limb is buffered.
struct MuSponge {
    I lane = 0, used = 0;
    U partial = 0;
    void limb(U v) {
        cop<15>(lane, cop<3>(cop<17>(lane), v));
        if (++lane == 8) {
            cop<16>();
            lane = 0;
        }
    }
    void byte(B b) {
        partial = (partial << 8) | b;
        if (++used == 7) {
            limb(partial);
            used = 0;
            partial = 0;
        }
    }
    void put(Slice s) {
        for (I i = 0; i < s.n; i++)
            byte(s.p[i]);
    }
};
static void compute_message_mu(const B *pk, Slice msg, U *mu) {
    static const U iv[12] = {0,0,0,0,0,0,0,0,8,4,32,0x504f53325f474c31ul};
    for (I i = 0; i < 12; i++)
        cop<15>(i, iv[i]);
    MuSponge h;
    h.put(label("\x03\x0a" "QSAG.MU/v2" "\x41"));
    h.put(bytes(pk, 65));
    I n = msg.n;
    do {
        B low = B(n & 127);
        n >>= 7;
        h.byte(n ? low | 128 : low);
    } while (n);
    h.put(msg);
    h.byte(1);
    while (h.used)
        h.byte(0);
    constexpr U end = 1ul << 56;
    if (h.lane == 7)
        h.limb(end + 1);
    else {
        h.limb(1);
        while (h.lane != 7)
            h.limb(0);
        h.limb(end);
    }
    B digest[35] = {};
    for (I i = 0; i < 4; i++) {
        U v = cop<17>(i);
        for (I k = 8; k--;) {
            digest[8 * i + k] = B(v);
            v >>= 8;
        }
    }
    for (I i = 0; i < 5; i++) {
        U v = 0;
        for (I k = 7; k--;)
            v = (v << 8) | digest[7 * i + k];
        mu[i] = v;
    }
}
// HQM2 row sumcheck sends evaluations at 0..8. Newton differences give an
// evaluation at r without inverting any proof-dependent denominator.
static E interpolate(E *v, const E &x) {
    static const U inv[] = {0,
                            0x1ul,
                            0x7fffffff80000001ul,
                            0xaaaaaaaa00000001ul,
                            0xbfffffff40000001ul,
                            0xcccccccc00000001ul,
                            0xd555555480000001ul,
                            0x249249246db6db6eul,
                            0xdfffffff20000001ul};
    for (I j = 1; j < 9; j++)
        for (I i = 9; i-- > j;)
            v[i] = scale(v[i] - v[i - 1], inv[j]);
    E y = v[8];
    for (I i = 8; i--;)
        y = v[i] + (x - base(i)) * y;
    return y;
}
static E hqm_front(Front &front, Reader &r, Reader &desc, Transcript &t, Geometry &geo, Slice magic,
                   B *root) {
    B tag = r.byte();
    require(tag == 1);
    Slice bitmap = desc.blob(), committee = desc.blob();
    B mode = desc.byte();
    Slice message = desc.blob();
    require(bitmap.n >= 12 && bitmap.n <= r.n && same(r.take(bitmap.n).p, bitmap.p, bitmap.n));
    Reader br{bitmap.p, bitmap.n};
    I count = br.u32(), active = 0;
    require(count > 0 && (U(count) + 63) / 64 * 8 == br.n);
    for (I i = 0; br.n; i += 64) {
        U word = br.u64();
        if (count - i < 64)
            require(!(word >> (count - i)));
        while (word) {
            active++;
            word &= word - 1;
        }
    }
    U payload = r.u64();
    require(active && payload == r.n && mode <= 1);
    Slice binding[] = {magic, bitmap, committee};
    t.start(true, tag, binding, 3);
    t.absorb(mode ? label("PER_SIGNER") : label("SHARED"), message);
    I local = desc.u32(), signers = desc.u32();
    require(local <= 20 && active == signers);
    I slots = 0;
    while ((1u << slots) < active)
        slots++;
    front.rows = local + slots;
    geo.init(front.rows + 8);
    require(committee.n == U(count) * 65);
    I ns = desc.u32(), nc = desc.u32();
    require(ns > 0 && ns <= 512 && nc <= 65536);
    Slice constants = desc.take(nc * 8), steps = desc.take(4u << local);
    I registers = desc.u32(), result = desc.u32();
    require(registers <= 1024 && registers >= 276 + ns && result < registers);
    I nconst = desc.u32();
    require(nconst <= desc.n / 8);
    Slice pool = desc.take(nconst * 8);
    I gates = desc.u32();
    require(gates <= desc.n / 4);
    Slice program = desc.take(gates * 4);
    memcpy(root, r.take(50).p, 50);
    t.absorb(label("ROOT"), bytes(root, 50));
    E tau[28];
    for (I i = 0; i < front.rows; i++)
        tau[i] = t.squeeze(label("TAU"));
    E reg[1024];
    reg[0] = t.squeeze(label("GAMMA"));
    E claim = base(0);
    E *rx = front.hpoint + 8;
    for (I i = 0; i < front.rows; i++) {
        E v[9];
        read_ext(r, v, 9);
        check(v[0] + v[1] == claim);
        absorb(t, label("ROW_VALUES"), v, 9);
        rx[i] = t.squeeze(label("ROW_POINT"));
        claim = interpolate(v, rx[i]);
    }
    read_ext(r, reg + 1, 256);
    // Capture column binding and claim before the row gate program reuses slots.
    E cols[256];
    memcpy(cols, reg + 1, sizeof(cols));
    for (I i = 257; i < 276 + ns; i++)
        reg[i] = base(0);
    E weight = base(0);
    Reader messages{message.p, message.n};
    if (mode)
        require(leb128(messages) == active);
    B profile = 0;
    I ordinal = 0;
    const B *bits = bitmap.p + 4;
    for (I i = 0; i < count; i++) {
        if (!(bits[i >> 3] & (1u << (i & 7))))
            continue;
        const B *pk = committee.p + 65 * i;
        if (!ordinal)
            profile = pk[0];
        require(pk[0] == profile && (profile == 1 || profile == 2 || (profile >= 7 && profile <= 20)));
        for (I k = 0; k < i; k++)
            if (bits[k >> 3] & (1u << (k & 7)))
                require(!same(pk, committee.p + 65 * k, 65));
        Reader key{pk + 1, 64};
        U inputs[13];
        for (I j = 0; j < 8; j++)
            inputs[j] = key.limb();
        Slice msg = mode ? messages.take(leb128(messages)) : message;
        compute_message_mu(pk, msg, inputs + 8);
        E w = eq_index(rx + local, slots, ordinal++);
        weight = weight + w;
        for (I j = 0; j < 13; j++)
            reg[257 + j] = reg[257 + j] + scale(w, inputs[j]);
    }
    require(!mode || !messages.n);
    Reader step{steps.p, steps.n};
    for (I i = 0; i < (1u << local); i++) {
        I code = step.u32(), id = code & 65535, c = code >> 16;
        require(id < ns && c < nc);
        E w = eq_index(rx, local, i);
        U value = ld(constants.p + 8 * c);
        require(value < P);
        reg[270] = reg[270] + scale(w, value);
        reg[276 + id] = reg[276 + id] + weight * w;
        if (!i)
            reg[271] = w;
        if (i + 1 == (1u << local))
            reg[272] = w;
    }
    E eq = base(1), carry = eq, shift = base(0), last = eq;
    for (I i = 0; i < front.rows; i++) {
        E a = tau[i], x = rx[i], product = a * x, s = product + (base(1) - a) * (base(1) - x);
        shift = shift * s + carry * (base(1) - a) * x;
        carry = carry * a * (base(1) - x);
        last = last * product;
        eq = eq * s;
    }
    reg[273] = eq;
    reg[274] = eq - last;
    reg[275] = shift;
    Reader instructions{program.p, program.n};
    while (instructions.n) {
        I op = instructions.u32(), d = (op >> 20) & 1023, a = (op >> 10) & 1023, b = op & 1023;
        require(d < registers);
        if (op >> 30 == 3) {
            I c = op & 0xfffff;
            require(c < nconst);
            U v = ld(pool.p + 8 * c);
            require(v < P);
            reg[d] = base(v);
        } else {
            require(a < registers && b < registers);
            switch (op >> 30) {
            case 0:
                reg[d] = reg[a] + reg[b];
                break;
            case 1:
                reg[d] = reg[a] - reg[b];
                break;
            default:
                reg[d] = reg[a] * reg[b];
            }
        }
    }
    check(reg[result] == claim);
    absorb(t, label("COLUMNS"), cols, 256);
    for (I i = 0; i < 8; i++) {
        E x = t.squeeze(label("COLUMN_POINT"));
        front.hpoint[i] = x;
        for (I j = 0; j < (128u >> i); j++)
            cols[j] = cols[2 * j] + x * (cols[2 * j + 1] - cols[2 * j]);
    }
    return cols[0];
}
