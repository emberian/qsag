#include "datapath.h"
#include "pcs.h"
#include "front.h"
#include "hqm.h"

extern "C" U verify(const B *proof, I size, const B *descriptor) {
    Reader r{proof, size}, desc{descriptor + 4, I(ld(descriptor)) - 4};
    U magic_word = r.u64();
    Slice magic = bytes(&magic_word, 8), kind = desc.take(4);
    B commitment[82];
    Slice nonce = bytes(commitment, 32), root = bytes(commitment + 32, 50);
    Geometry geo;
    Front front;
    Transcript tr;
    front.hqm = same(magic.p, (const B *)"QSAGHQM2", 8);
    E claim;
    if (front.hqm) {
        require(same(kind.p, (const B *)"HQD1", 4));
        claim = hqm_front(front, r, desc, tr, geo, magic, commitment + 32);
    } else {
        require(same(magic.p, (const B *)"QSAGZKH2", 8) && same(kind.p, (const B *)"ZKD1", 4));
        claim = front.zk(r, desc, tr, geo, magic, commitment);
    }
    require(!desc.n);
    Kernel kernel;
    kernel.np = kernel.used = 0;
    E points[5], values[5], beta_r = base(0);
    Challenge challenges[6];
    for (I i = 0; i < 5; i++)
        points[i] = tr.squeeze(front.hqm ? label("OOD_POINT") : label("MASK_POINT"));
    read_ext(r, values, 5);
    absorb(tr, front.hqm ? label("FIRST_OOD") : label("MASK_EVAL"), values, 5);
    for (I i = 0; i < 5; i++) {
        E w = tr.squeeze(front.hqm ? label("OOD_WEIGHT") : label("MASK_WEIGHT"));
        claim = claim + w * values[i];
        kernel.add(w, points[i]);
    }
    U image[MAX_Q];
    E shifts[MAX_Q];
    for (I i = 0; i < geo.stages; i++) {
        const Dims &d = geo.d[i];
        if (i) {
            B next_root[50];
            memcpy(next_root, r.take(50).p, 50);
            Slice next = bytes(next_root, 50);
            tr.absorb(front.hqm ? label("ROOT") : label("STAGE_ROOT"), next);
            for (I j = 0; j < 2; j++)
                points[j] = tr.squeeze(label("OOD_POINT"));
            read_ext(r, values, 2);
            absorb(tr, label("OOD_EVAL"), values, 2);
            const Dims &prev = geo.d[i - 1];
            openings(r, tr, front.hqm, i - 1, prev, root, nonce, challenges, beta_r, image, shifts);
            absorb(tr, label("QUERY_VALUES"), shifts, prev.count);
            for (I j = 0; j < 2; j++) {
                E w = tr.squeeze(label("OOD_WEIGHT"));
                kernel.add(w, points[j]);
                claim = claim + w * values[j];
            }
            E gamma = tr.squeeze(label("QUERY_GAMMA")), w = gamma;
            for (I j = 0; j < prev.count; j++) {
                kernel.add(w, base(image[j]));
                claim = claim + w * shifts[j];
                w = w * gamma;
            }
            memcpy(commitment + 32, next_root, 50);
        }
        for (I j = 0; j < d.step; j++)
            challenges[j] = fold_round(r, tr, kernel, claim);
        if (!i && !front.hqm) {
            E mask = r.ext();
            absorb(tr, label("MASK_CLAIM"), &mask, 1);
            beta_r = tr.squeeze(label("MASK_BETA"), true);
            claim = claim + beta_r * mask;
        }
    }
    I n = (1u << geo.stop) + 2;
    E coeff[258];
    require(n <= 258);
    read_ext(r, coeff, n);
    absorb(tr, label("FINAL_POLY"), coeff, n);
    check(front.apply(kernel, coeff, n) + kernel.univariate(coeff, n) == claim);
    I last = geo.stages - 1;
    Dims &d = geo.d[last];
    openings(r, tr, front.hqm, last, d, root, nonce, challenges, beta_r, image, shifts);
    for (I j = 0; j < d.count; j++) {
        E value = base(0);
        for (I i = n; i--;)
            value = scale(value, image[j]) + coeff[i];
        check(value == shifts[j]);
    }
    check(!r.n && tr.remaining);
    return 1;
}
