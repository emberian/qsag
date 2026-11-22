"""Geometry in mm, top view. Source coordinates use the south-west die corner."""

import math
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SRC = ROOT / "sources"
DIE = "ASS2_0P5_COB56"
COIL = "NFC_Planar_40x40mm_4T_1u466H"


def padmap(slot, typ, placement):
    yaml = slot.read_text()
    spec = typ.read_text()
    physical = placement.read_text()
    if (
        "UNITS DISTANCE MICRONS 2000" not in physical
        or "DIEAREA ( 0 0 ) ( 3872000 5062000 )" not in physical
    ):
        raise ValueError("Unexpected DEF units or die bounds")
    if not re.search(r"DIE_AREA: \[0, 0, 1936, 2531\]", yaml):
        raise ValueError("Unexpected slot die dimensions")
    ports = {}
    for net, body in re.findall(r"^    - (\S+) \+ NET (.*?);", physical, re.M | re.S):
        boxes = re.findall(
            r"Metal5 \( -60000 -60000 \) \( 60000 60000 \)\s*\+ FIXED \( (\d+) (\d+) \) N", body
        )
        ports[net] = [(int(x) / 2000, int(y) / 2000) for x, y in boxes]
    rows = []
    for side in ("south", "east", "north", "west"):
        block = re.search(r"#let " + side + r" = (.*?\)\))", spec, re.S)[1]
        triples = re.findall(r'\("([^"]+)", "([^"]+)", "([^"]+)"\)', block)
        if side in ("east", "west"):
            triples.reverse()
        block = re.search("PAD_" + side.upper() + r": \[(.*?)\n\]", yaml, re.S)[1]
        slots = [s.strip().strip('"').replace(chr(92), "") for s in block.split(",")]
        for i, (slotname, (alias, signal, kind)) in enumerate(zip(slots, triples, strict=True)):
            if alias in ("clk", "rst_n"):
                expected, port = alias + "_pad", alias + "_PAD"
            else:
                base, num = re.fullmatch(r"([a-z]+)\[?(\d+)\]?", alias).groups()
                prefix = {"an": "analog", "b": "bidir", "in": "inputs"}.get(base, base + "_pads")
                expected = f"{prefix}[{num}].pad"
                port = {"an": "analog_PAD", "b": "bidir_PAD", "in": "input_PAD"}.get(base)
                port = f"{port}[{num}]" if port else ("VSS" if "ss" in base else "VDD")
            if slotname != expected:
                raise ValueError(f"{side} index {i}: {slotname} differs from {expected}")
            bounds = {
                "south": lambda x, y: y < 100,
                "north": lambda x, y: y > 2431,
                "east": lambda x, y: x > 1836,
                "west": lambda x, y: x < 100,
            }
            [(x, y)] = [p for p in ports[port] if bounds[side](*p)]
            rows.append((len(rows) + 1, side, i, slotname, signal, x, y))
    # Independently reconcile the numbered table (including split north and west rows).
    numbered = {}
    signal_table = {}
    for nums, side, inds, cells, sig_group in re.findall(
        r"^  \[([\d, –]+)\], \[([SENW]) ([\d., ]+)\], \[.*?\], \[(.*?)\], \[(.*?)\], \[", spec, re.M
    ):

        def expand(s):
            result = []
            for term in s.split(","):
                ends = re.split(r"–|\.\.", term.strip())
                result.extend(range(int(ends[0]), int(ends[-1]) + 1))
            return result

        signals = []
        for name in re.findall(r"`([^`]+)`", sig_group):
            group = re.fullmatch(r"(\w+)\[(\d+)(?:\.\.|:)(\d+)\]", name)
            if group:
                prefix, first, last = group.groups()
                step = 1 if int(last) >= int(first) else -1
                signals.extend(prefix + str(k) for k in range(int(first), int(last) + step, step))
            else:
                signals.append("JTAG_" + name if name in ("TMS", "TDI", "TDO") else name)
        if sig_group == "not connected":
            signals = ["n/c"] * len(expand(nums))
        for n, i, name in zip(expand(nums), expand(inds), signals, strict=True):
            signal_table[n] = name
            if n in numbered:
                raise ValueError(f"Repeated datasheet row {n}")
            numbered[n] = (side, i)
    if numbered != {n: (s[0].upper(), i) for n, s, i, *_ in rows} or len(rows) != 56:
        raise ValueError("Datasheet numbering and physical ring disagree")
    if signal_table != {n: name for n, _, _, _, name, _, _ in rows}:
        raise ValueError("Numbered pin descriptions disagree with ring signals")
    return rows


def rect(x, y, w, h, layer, stroke=0.02):
    return f'(fp_rect (start {x - w / 2:.6f} {y - h / 2:.6f}) (end {x + w / 2:.6f} {y + h / 2:.6f}) (stroke (width {stroke}) (type solid)) (fill none) (layer "{layer}"))'


def line(x, y, u, v, layer, w):
    return f'(fp_line (start {x:.6f} {y:.6f}) (end {u:.6f} {v:.6f}) (stroke (width {w}) (type solid)) (layer "{layer}"))'


def land(n, x, y, w, h):
    return f'(pad "{n}" smd rect (at {x:.6f} {y:.6f}) (size {w} {h}) (layers "F.Cu" "F.Mask") (solder_mask_margin 0))'


def drill(n, x, y, diameter, hole):
    return f'(pad "{n}" thru_hole circle (at {x:.6f} {y:.6f}) (size {diameter} {diameter}) (drill {hole}) (layers "*.Cu"))'


def write_mod(name, desc, elements, offset):
    head = f'(footprint "{name}" (version 20240108) (generator "ass2_carrier") (layer "F.Cu") (descr "{desc}")'
    for prop, value, pos, layer in [
        ("Reference", "REF**", -offset, "F.SilkS"),
        ("Value", name, offset, "F.Fab"),
    ]:
        elements.insert(
            0,
            f'(property "{prop}" "{value}" (at 0 {pos}) (layer "{layer}") (effects (font (size 0.85 0.85) (thickness 0.12))))',
        )
    (ROOT / "ass2.pretty" / (name + ".kicad_mod")).write_text(
        head + "\n  " + "\n  ".join(elements) + "\n)\n"
    )


def die_footprint(rows, finger_pitch=0.4, finger_width=0.17, finger_length=0.62):
    items = [
        rect(0, 0, 1.936, 2.531, "F.Fab"),
        land("EP", 0, 0, 2.06, 2.66),
        rect(0, 0, 9.1, 8.5, "F.CrtYd", 0.05),
    ]
    items.append(
        '(fp_circle (center -1.44 3.25) (end -1.32 3.25) (stroke (width 0.12) (type solid)) (fill solid) (layer "F.SilkS"))'
    )
    for x in (-0.55, 0, 0.55):
        for y in (-0.8, 0, 0.8):
            items.append(drill("EP", x, y, 0.60, 0.30))
    for n, side, index, slot, sig, x_um, y_um in rows:
        x, y = (x_um - 968) / 1000, (1265.5 - y_um) / 1000
        items.append(rect(x, y, 0.060, 0.060, "F.Fab", 0.006))
        along = (index - (5 if side in ("south", "north") else 8)) * finger_pitch
        if side in ("south", "north"):
            fx, fy = along, 1.92 if side == "south" else -3.18
            w, h = finger_width, finger_length
        else:
            fx, fy = (4.0 if side == "east" else -3.74), -along - (0.60 if side == "east" else 0)
            w, h = finger_length, finger_width
        # Two individually accessible fingers inside each south supply lane.
        if side == "south":
            fx = (-1.44, -1.03, -0.56, -0.005, 0.47, 0.87, 1.27, 1.67, 2.07, 2.47, 2.87)[index]
            fy = 1.92 if n in (3, 4) else 2.25
            h = 0.25
        shifts = (-0.10, 0.10) if n in (3, 4) else (0,)
        for dx in shifts:
            width = 0.13 if len(shifts) == 2 else w
            items.append(land(n, fx + dx, fy, width, h))
            if sig != "n/c":
                site_x = x + (0.014 if dx > 0 else -0.014) if len(shifts) == 2 else x
                items.append(line(site_x, y, fx + dx, fy, "Dwgs.User", 0.012))
        if len(shifts) == 2:
            items.append(f'(pad "{n}" smd rect (at {fx} {fy + 0.085}) (size 0.30 0.08) (layers "F.Cu"))')
    write_mod(
        DIE, "Top view. F.Fab die windows; Dwgs.User bonds. Capped filled paddle vias.", items, 4.0
    )


def spiral(outer=40, turns=4, width=0.42, gap=0.56):
    r = (outer - width) / 2
    pitch = width + gap
    points = [(-r, -r)]
    for k in range(turns):
        a = r - k * pitch
        points.extend([(a, -a), (a, a), (-a, a), (-a, -a + pitch)])
    return points


def zone(layers, x0, y0, x1, y1, pads):
    layers = " ".join(f'"{l}"' for l in layers)
    return f"""(zone (net 0) (net_name "") (layers {layers}) (hatch edge 0.5)
    (connect_pads (clearance 0)) (min_thickness 0.25)
    (keepout (tracks not_allowed) (vias not_allowed) (pads {pads}) (copperpour not_allowed) (footprints allowed))
    (fill (thermal_gap 0.3) (thermal_bridge_width 0.3))
    (polygon (pts (xy {x0} {y0}) (xy {x1} {y0}) (xy {x1} {y1}) (xy {x0} {y1}))))"""


def coil_footprint(outer=40, turns=4, width=0.42, gap=0.56):
    pts = spiral(outer, turns, width, gap)
    x, y = pts[-1]
    end = (x + 0.80, y)
    ox, oy = pts[0]
    primitives = []
    for (x, y), (u, v) in zip(pts, pts[1:]):
        primitives.append(
            f"(gr_line (start {x - ox:.6f} {y - oy:.6f}) (end {u - ox:.6f} {v - oy:.6f}) (width {width}))"
        )
    items = [
        "(attr smd exclude_from_pos_files)",
        '(net_tie_pad_groups "1,2")',
        f'(pad "1" smd custom (at {ox} {oy}) (size {width} {width}) (layers "F.Cu") (options (clearance outline) (anchor circle)) (primitives '
        + " ".join(primitives)
        + "))",
    ]
    x, y = pts[-1]
    ex, ey = end
    # Match the calculator's centreline-length convention including its feed allowance.
    inner = outer - 2 * turns * width - 2 * (turns - 1) * gap
    target_length = 4 * turns * (outer + inner) / 2 + 12.0
    winding_length = sum(math.dist(a, b) for a, b in zip(pts, pts[1:]))
    feed = target_length - winding_length - (ex - x) - (ex + 24)
    items += [
        f'(pad "1" smd custom (at {ox - feed:.6f} {oy:.6f}) (size {width} {width}) (layers "F.Cu") (options (clearance outline) (anchor circle)) (primitives (gr_line (start 0 0) (end {feed:.6f} 0) (width {width}))))',
        f'(pad "2" smd custom (at {x:.6f} {y:.6f}) (size {width} {width}) (layers "F.Cu") (options (clearance outline) (anchor circle)) (primitives (gr_line (start 0 0) (end {ex - x:.6f} 0) (width {width}))))',
        drill(2, ex, ey, 0.68, 0.3),
        drill(2, -24, ey, 0.8, 0.35),
        f'(pad "2" smd custom (at -24 {ey}) (size 0.42 0.42) (layers "B.Cu") (options (clearance outline) (anchor circle)) (primitives (gr_line (start 0 0) (end {ex + 24:.6f} 0) (width 0.42))))',
    ]
    # The complete window prohibits routed tracks, vias and all pours. Tiled
    # overlays prohibit pads too, except for the footprint's own crossover.
    layers = ("In1.Cu", "In2.Cu", "B.Cu")
    items.append(zone(layers, -23, -23, 23, 23, "allowed"))
    for group, left in [(layers[:2], round(ex - 0.35, 5)), (layers[2:], -23)]:
        right = round(ex + 0.35, 5)
        top, bottom = round(ey - 0.35, 5), round(ey + 0.35, 5)
        boxes = [(-23, -23, 23, top), (-23, bottom, 23, 23), (right, top, 23, bottom)]
        if left > -23:
            boxes.append((-23, top, left, bottom))
        items.extend(zone(group, *box, "not_allowed") for box in boxes)
    write_mod(
        COIL,
        "Printed 35 um copper spiral; integral B.Cu crossover; four-layer stack required",
        items,
        24.5,
    )
