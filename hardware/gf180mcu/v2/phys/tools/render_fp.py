#!/usr/bin/env python3
"""Render a placed (or routed) Dregg-180 v2 proxy DEF: blocks coloured and labelled, floorplan regions,
pads, and a wire-demand map beside it.

usage: render_fp.py out.png title placed.def tech.tlef "lef1 lef2 ..." [regions.json] [congestion.json]

The wire-demand map is RUDY over 20 um bins (net bounding-box wire density over Metal2..Metal5 track
capacity) unless congestion.json (from tools/guides_congestion.py: global-route usage / capacity per
gcell) is given.
"""
import json
import re
import sys

from PIL import Image, ImageDraw, ImageFont

import deflib as dl

BLOCKS = [  # (instance prefix under i_chip_core, block, colour)
    ("u_rf", "register file 72x64", (60, 165, 110)),
    ("u_kec", "Keccak", (150, 200, 90)),
    ("u_wu", "word unit", (214, 120, 40)),
    ("u_rom", "microcode ROM", (95, 125, 190)),
    ("u_seq", "sequencer", (120, 190, 205)),
    ("u_spi", "SPI link", (170, 170, 170)),
    ("u_fram", "FRAM master", (170, 170, 60)),
    ("u_trng", "TRNG", (0, 150, 150)),
    ("u_nfc", "NFC front end", (250, 150, 190)),
    ("u_db", "distance + TDC", (255, 225, 0)),
    ("u_pufarr", "PUF ring array", (220, 60, 70)),
    ("u_pufcnt", "PUF decoder", (175, 100, 190)),
    ("u_puf", "PUF decoder", (175, 100, 190)),
    ("u_shield", "shield, canaries", (140, 100, 60)),
    ("u_clk", "clock, reset, tamper", (60, 90, 200)),
    ("u_ring", "clock, reset, tamper", (60, 90, 200)),
    ("u_oscbuf", "clock, reset, tamper", (60, 90, 200)),
]
EXTRA = {"added": ("repair / CTS / hold buffers", (255, 255, 255)), "top": ("glue", (90, 90, 90)),
         "decap": ("fillcap (decap)", (50, 60, 95))}
PADHL = {"bidir[13].pad": "DB_CHAL", "bidir[14].pad": "DB_RESP", "bidir[8].pad": "NFC_CLK",
         "bidir[9].pad": "NFC_ASK", "bidir[10].pad": "NFC_LM", "clk_pad": "CLK", "rst_n_pad": "RST_N",
         "bidir[0].pad": "SCK", "bidir[1].pad": "MOSI", "bidir[2].pad": "MISO", "bidir[3].pad": "CS_N",
         "bidir[22].pad": "F_CS", "bidir[23].pad": "F_SCK", "bidir[24].pad": "F_MOSI", "bidir[25].pad": "F_MISO",
         "bidir[26].pad": "TAMPER", "bidir[16].pad": "FAULT", "bidir[17].pad": "IRQ", "bidir[21].pad": "CLKMON",
         "inputs[0].pad": "STRAP0", "inputs[1].pad": "STRAP1"}
SUPPLY = re.compile(r"^(dvdd|dvss|vdd|vss)_pads")
S = 0.55   # px per um
BIN = 20.0
AUTO = re.compile(r"^(fanout|place|wire|rebuffer|split|clkbuf_|clkload|hold|input|output|max_cap|max_length|"
                  r"load_slew|use|gain|clone|delaybuf|ANTENNA|antenna)")


def font(sz):
    for p in ("/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf", "/System/Library/Fonts/Helvetica.ttc"):
        try:
            return ImageFont.truetype(p, sz)
        except OSError:
            pass
    try:
        return ImageFont.load_default(size=sz)
    except TypeError:
        return ImageFont.load_default()


def block_of(name, master):
    if master.startswith("gf180mcu_fd_io") or master.startswith("gf180mcu_ws_ip"):
        return "pad"
    if "__fillcap" in master:
        return "decap"
    if "__fill" in master or "__endcap" in master:
        return "physical"
    base = re.split(r"[./]", name)[-1]
    if AUTO.match(base) and not name.startswith("i_chip_core/u_"):
        return "added"
    n = name.replace("/", ".")
    if n.startswith("i_chip_core."):
        n = n[len("i_chip_core."):]
        for pre, blk, _ in BLOCKS:
            if n == pre or n.startswith(pre + ".") or n.startswith(pre + "_"):
                return blk
    if AUTO.match(base):
        return "added"
    return "top"


def heat(v):
    v = max(0.0, min(v, 1.2)) / 1.2
    stops = [(0.0, (12, 12, 40)), (0.25, (30, 70, 160)), (0.5, (40, 170, 120)), (0.75, (245, 200, 40)), (1.0, (230, 40, 30))]
    for (a, ca), (b, cb) in zip(stops, stops[1:]):
        if v <= b:
            t = (v - a) / (b - a)
            return tuple(int(ca[i] + t * (cb[i] - ca[i])) for i in range(3))
    return stops[-1][1]


def rudy(d):
    x0, y0, x1, y1 = d.die
    nx, ny = int((x1 - x0) / BIN) + 1, int((y1 - y0) / BIN) + 1
    g = [[0.0] * nx for _ in range(ny)]
    for net, pins in d.nets.items():
        pts = [dl.pin_xy(d, i) for i, _ in pins if i in d.comps and d.comps[i]["placed"]]
        if len(pts) < 2:
            continue
        xs = [p[0] for p in pts]
        ys = [p[1] for p in pts]
        ax, bx, ay, by = min(xs), max(xs), min(ys), max(ys)
        w, h = max(bx - ax, 0.56), max(by - ay, 3.92)
        dens = (w + h) / (w * h)
        for j in range(int((ay - y0) / BIN), int((ay + h - y0) / BIN) + 1):
            oy = min(ay + h, y0 + (j + 1) * BIN) - max(ay, y0 + j * BIN)
            if oy <= 0 or j >= ny:
                continue
            for i in range(int((ax - x0) / BIN), int((ax + w - x0) / BIN) + 1):
                ox = min(ax + w, x0 + (i + 1) * BIN) - max(ax, x0 + i * BIN)
                if ox > 0 and i < nx:
                    g[j][i] += dens * ox * oy
    cap = BIN * BIN * (3 / 0.56 + 1 / 0.9)
    vals = sorted(v / cap for row in g for v in row if v > 0)
    stats = dict(peak=vals[-1], p99=vals[int(0.99 * len(vals))], mean=sum(vals) / len(vals)) if vals else {}
    return [[v / cap for v in row] for row in g], nx, ny, BIN, x0, y0, stats


def main():
    out, title, defp, techlef, lefs = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5].split()
    regions = json.load(open(sys.argv[6])) if len(sys.argv) > 6 and sys.argv[6] else []
    cong = json.load(open(sys.argv[7])) if len(sys.argv) > 7 and sys.argv[7] else None
    macros = dl.read_lef([techlef] + lefs)
    d = dl.read_def(defp, macros)
    x0, y0, x1, y1 = d.die
    W, H = int((x1 - x0) * S), int((y1 - y0) * S)
    TOP = 40

    def box(ax, ay, bx, by):
        return [(ax - x0) * S, H - (by - y0) * S + TOP, (bx - x0) * S, H - (ay - y0) * S + TOP]

    col = {b: c for _, b, c in BLOCKS}
    col.update({k: v[1] for k, v in EXTRA.items()})
    area = {}
    cent = {}

    def base(dr, with_cells):
        for n, c in d.comps.items():
            if not c["placed"]:
                continue
            m = c["master"]
            blk = block_of(n, m)
            b = box(c["x"], c["y"], c["x"] + c["w"], c["y"] + c["h"])
            if blk == "pad":
                hl = n in PADHL
                sup = bool(SUPPLY.match(n))
                dr.rectangle(b, fill=(200, 60, 60) if sup else ((90, 200, 255) if hl else (52, 54, 68)), outline=(110, 112, 130))
            elif with_cells and blk != "physical":
                dr.rectangle(b, fill=col.get(blk, (90, 90, 90)))
                if with_cells == 1:
                    a = c["w"] * c["h"]
                    area[blk] = area.get(blk, 0.0) + a
                    sx, sy, sa = cent.get(blk, (0.0, 0.0, 0.0))
                    cent[blk] = (sx + (c["x"] + c["w"] / 2) * a, sy + (c["y"] + c["h"] / 2) * a, sa + a)
        f = font(12)
        for n, lab in PADHL.items():
            if n in d.comps:
                c = d.comps[n]
                b = box(c["x"], c["y"], c["x"] + c["w"], c["y"] + c["h"])
                dr.text((min(max(b[0] + 3, 2), W - 70), (b[1] + b[3]) / 2 - 7), lab, fill=(0, 0, 0), font=f)
        for n, c in d.comps.items():
            if SUPPLY.match(n):
                b = box(c["x"], c["y"], c["x"] + c["w"], c["y"] + c["h"])
                dr.text((min(max(b[0] + 3, 2), W - 70), (b[1] + b[3]) / 2 - 7), n.split("_pads")[0].upper(), fill=(255, 255, 255), font=f)

    im1 = Image.new("RGB", (W, H + TOP), (18, 18, 22))
    dr = ImageDraw.Draw(im1)
    base(dr, 1)
    fb = font(17)
    for r in regions:
        dr.rectangle(box(*r["box"]), outline=(255, 255, 255), width=2)
    for blk, (sx, sy, sa) in cent.items():
        if blk in ("added", "top", "decap") or sa < 3000:
            continue
        cx, cy = sx / sa, sy / sa
        b = box(cx, cy, cx, cy)
        lab = f"{blk}\n{area[blk] / 1000:.0f}k um2"
        tb = dr.multiline_textbbox((0, 0), lab, font=fb)
        tw, th = tb[2] - tb[0], tb[3] - tb[1]
        dr.rectangle([b[0] - tw / 2 - 4, b[1] - th / 2 - 4, b[0] + tw / 2 + 4, b[1] + th / 2 + 6], fill=(0, 0, 0))
        dr.multiline_text((b[0] - tw / 2, b[1] - th / 2), lab, fill=(255, 255, 255), font=fb, align="center")
    dr.text((8, 8), title, fill=(240, 240, 240), font=font(20))

    im2 = Image.new("RGB", (W, H + TOP), (18, 18, 22))
    dr2 = ImageDraw.Draw(im2)
    if cong:
        g, bn, gx0, gy0 = cong["grid"], cong["bin"], cong["x0"], cong["y0"]
        t2 = f"global-route usage / capacity per gcell: peak {cong['peak']:.2f}, p99 {cong['p99']:.2f}, mean {cong['mean']:.2f}"
    else:
        g, nx, ny, bn, gx0, gy0, st = rudy(d)
        t2 = f"RUDY wire demand / M2-M5 capacity: peak {st.get('peak', 0):.2f}, p99 {st.get('p99', 0):.2f}, mean {st.get('mean', 0):.2f}"
    for j, row in enumerate(g):
        for i, v in enumerate(row):
            if v > 0.02:
                dr2.rectangle(box(gx0 + i * bn, gy0 + j * bn, gx0 + (i + 1) * bn, gy0 + (j + 1) * bn), fill=heat(v))
    base(dr2, 0)
    for r in regions:
        dr2.rectangle(box(*r["box"]), outline=(255, 255, 255), width=1)
    dr2.text((8, 8), t2, fill=(240, 240, 240), font=font(16))

    LEG = 300
    im = Image.new("RGB", (2 * W + 36 + LEG, H + TOP + 24), (10, 10, 12))
    im.paste(im1, (12, 12))
    im.paste(im2, (24 + W, 12))
    dr = ImageDraw.Draw(im)
    f = font(15)
    x, y = 2 * W + 40, 30
    dr.text((x, y), "blocks (placed cell area)", fill=(240, 240, 240), font=f)
    y += 26
    seen = []
    for _, b, c in BLOCKS:
        if b in seen:
            continue
        seen.append(b)
        dr.rectangle([x, y, x + 18, y + 14], fill=c)
        dr.text((x + 26, y - 2), f"{b}  {area.get(b, 0) / 1000:.0f}k", fill=(230, 230, 230), font=f)
        y += 22
    for k, (lab, c) in EXTRA.items():
        dr.rectangle([x, y, x + 18, y + 14], fill=c)
        dr.text((x + 26, y - 2), f"{lab}  {area.get(k, 0) / 1000:.0f}k", fill=(230, 230, 230), font=f)
        y += 22
    tot = sum(v for k, v in area.items() if k != "decap")
    dr.text((x, y + 6), f"cells total {tot / 1000:.0f}k um2", fill=(240, 240, 240), font=f)
    y += 50
    dr.text((x, y), "wire demand / capacity", fill=(240, 240, 240), font=f)
    y += 26
    for v in (0.15, 0.3, 0.6, 0.9, 1.2):
        dr.rectangle([x, y, x + 18, y + 14], fill=heat(v))
        dr.text((x + 26, y - 2), f"{v:.2f}" + ("+" if v == 1.2 else ""), fill=(230, 230, 230), font=f)
        y += 22
    y += 20
    for lab, c in (("supply pad", (200, 60, 60)), ("used signal pad", (90, 200, 255)), ("unused pad", (52, 54, 68)), ("region / array outline", None)):
        if c:
            dr.rectangle([x, y, x + 18, y + 14], fill=c)
        else:
            dr.rectangle([x, y, x + 18, y + 14], outline=(255, 255, 255), width=2)
        dr.text((x + 26, y - 2), lab, fill=(230, 230, 230), font=f)
        y += 22
    im.save(out)
    print("wrote", out, im.size)
    print(json.dumps({k: round(v) for k, v in sorted(area.items())}))


if __name__ == "__main__":
    main()
