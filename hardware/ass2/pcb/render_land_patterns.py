"""Plot actual KiCad copper, die windows and bond destinations. Emit assembly coordinates."""

import csv
import math
from html import escape
from verify_carrier_erc import children, one, xy, parse, PRETTY
from geometry import ROOT, SRC, DIE, COIL, padmap


def draw():
    rows = padmap(SRC / "slot_0p5x0p5.yaml", SRC / "pad-ring.typ", SRC / "bond-windows.def")
    die, coil = [parse(PRETTY / (name + ".kicad_mod")) for name in (DIE, COIL)]
    svg = [
        '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1260 660" role="img" aria-labelledby="title desc">',
        '<title id="title">ASS2-0P5 die bonding and NFC winding</title>',
        '<desc id="desc">Top view of the PCB landing fingers and all wirebonds. The four-turn coil and inner crossover are shown at a separate scale.</desc>',
        "<style>text{font-family:system-ui,sans-serif;fill:#172c38}.head{font-size:24px;font-weight:650}.caption{font-size:15px}.pin{font:11px monospace}</style>",
        '<rect width="1260" height="660" fill="#fafbf9"/>',
    ]

    def text(x, y, t, cls="caption", anchor="start"):
        svg.append(
            f'<text x="{x:g}" y="{y:g}" text-anchor="{anchor}" class="{cls}">{escape(str(t))}</text>'
        )

    def rect(x, y, w, h, style):
        svg.append(f'<rect x="{x:g}" y="{y:g}" width="{w:g}" height="{h:g}" {style}/>')

    def line(a, b, color, width, dash=""):
        svg.append(
            f'<line x1="{a[0]:g}" y1="{a[1]:g}" x2="{b[0]:g}" y2="{b[1]:g}" stroke="{color}" stroke-width="{width:g}" stroke-linecap="round" {dash}/>'
        )

    def circle(p, r, fill):
        svg.append(f'<circle cx="{p[0]:g}" cy="{p[1]:g}" r="{r:g}" fill="{fill}"/>')

    text(33, 48, "Die bonding · top view", "head")
    text(33, 74, "1.936 × 2.531 mm die   /   60 × 60 µm Metal5 terminal windows")
    text(666, 48, "13.56 MHz printed winding", "head")
    text(666, 74, "40 × 40 mm   /   4 turns   /   0.42 mm track   /   0.56 mm gap")
    scale = 58

    def loc(x, y):
        return 315 + x * scale, 320 + y * scale

    def padrect(p, fill):
        px, py = xy(p, "at")
        w, h = xy(p, "size")
        rect(*loc(px - w / 2, py - h / 2), w * scale, h * scale, f'fill="{fill}"')

    pads = children(die, "pad")
    ep = [p for p in pads if p[1] == "EP"]
    padrect(next(p for p in ep if p[2] == "smd"), "#ad7135")
    rect(
        *loc(-0.968, -1.2655),
        1.936 * scale,
        2.531 * scale,
        'fill="#d3ddd7" fill-opacity=".9" stroke="#536e60"',
    )
    for p in ep:
        if p[2] == "thru_hole":
            circle(loc(*xy(p, "at")), float(one(p, "drill")[1]) * scale / 2, "#a6b6ac")
    bonds = {
        xy(l, "end"): xy(l, "start")
        for l in children(die, "fp_line")
        if one(l, "layer")[1] == "Dwgs.User"
    }
    for a, b in bonds.items():
        line(loc(*b), loc(*a), "#777364", 1)
    for p in children(die, "fp_rect"):
        if one(p, "layer")[1] == "F.Fab" and xy(p, "start") != (-0.968, -1.2655):
            a, b = xy(p, "start"), xy(p, "end")
            rect(*loc(*a), (b[0] - a[0]) * scale, (b[1] - a[1]) * scale, 'fill="#754f23"')
    with (ROOT / "BOND_MAP.csv").open("w", newline="") as file:
        w = csv.writer(file)
        w.writerow(
            [
                "Pad",
                "Signal",
                "Side",
                "Side index",
                "Slot instance",
                "DEF center X um from SW",
                "DEF center Y um from SW",
                "Bond",
                "Die site X mm",
                "Die site Y mm",
                "PCB finger X mm",
                "PCB finger Y mm",
                "Projected length mm",
            ]
        )
        for num, side, index, slot, name, x, y in rows:
            lands = [p for p in pads if p[1] == str(num) and "F.Mask" in one(p, "layers")]
            for j, p in enumerate(sorted(lands, key=lambda p: xy(p, "at")), 1):
                dest = xy(p, "at")
                origin = bonds.get(dest)
                color = (
                    "#426c91"
                    if name in ("VSS", "DVSS")
                    else "#b14f43"
                    if name in ("VDD", "DVDD")
                    else "#b4bcb7"
                    if name == "n/c"
                    else "#bc813f"
                )
                padrect(p, color)
                px, py = loc(*dest)
                if side == "south":
                    py += 31
                if side == "north":
                    py -= 24
                if side == "east":
                    px += 33
                if side == "west":
                    px -= 33
                if j == 1:
                    text(px, py + 3, str(num), "pin", "middle")
                w.writerow(
                    [
                        num,
                        name,
                        side,
                        index,
                        slot,
                        x,
                        y,
                        j if origin else "OPEN",
                        *(origin if origin else ("", "")),
                        *dest,
                        round(math.dist(origin, dest), 5) if origin else "",
                    ]
                )
    text(33, 594, "Blue ground   ·   Red +5 V   ·   Gray unbonded analog")
    text(33, 620, "South 3 and 4 each use two sites and two fingers. Nine capped vias under EP.")

    def rf(x, y):
        return 952 + x * 9.7, 323 + y * 9.7

    rect(*rf(-23, -23), 46 * 9.7, 46 * 9.7, 'fill="#edf2ee" stroke="#5c7969" stroke-dasharray="6 5"')
    for p in children(coil, "pad"):
        if p[3] == "custom":
            ox, oy = xy(p, "at")
            is_back = "B.Cu" in one(p, "layers")
            for leg in children(one(p, "primitives"), "gr_line"):
                ends = [rf(ox + x, oy + y) for x, y in [xy(leg, "start"), xy(leg, "end")]]
                line(*ends, "#327794" if is_back else "#aa6936", float(one(leg, "width")[1]) * 9.7)
        elif p[2] == "thru_hole":
            circle(rf(*xy(p, "at")), 4.6, "#327794")
    line((687, 130), rf(-24, -15.87), "#327794", 1)
    text(670, 114, "2 · GND")
    line((756, 106), rf(-24.02, -19.79), "#805b3f", 1)
    text(754, 96, "1 · coil out")
    text(666, 594, "Dashed boundary   ·   46 × 46 mm L2–L4 keepout")
    text(666, 620, "Blue copper exits the inner turn on L4. Winding and die use separate scales.")
    svg.append("</svg>")
    (ROOT / "land_patterns.svg").write_text("\n".join(svg) + "\n")


if __name__ == "__main__":
    draw()
