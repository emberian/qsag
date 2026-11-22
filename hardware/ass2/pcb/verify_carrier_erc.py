#!/usr/bin/env python3
"""Read back KiCad geometry and connectivity. Python 3.10+, standard library only."""

import argparse
import csv
import gzip
import importlib.util
import itertools
import json
import math
import os
import re
import shutil
import subprocess
import sys
import tempfile
import xml.etree.ElementTree as ET
from collections import Counter, defaultdict
from pathlib import Path

sys.dont_write_bytecode = True
from carrier import parts, FIT, ASK, HOST, AUX, G, H, V
from geometry import ROOT, SRC, DIE, COIL, padmap

SCH = ROOT / "ass2_0p5_carrier.kicad_sch"
SYM = ROOT / "ass2_0p5.kicad_sym"
PRETTY = ROOT / "ass2.pretty"


def check(ok, problem):
    if not ok:
        raise ValueError(problem)


def parse(path):
    """Strict balanced token reader. Require exactly one complete root."""
    source = path.read_text()
    token = re.compile(r'\s+|\(|\)|"(?:\\.|[^"\\])*"|[^\s()"\\]+')
    roots, stack = [], []
    pos = 0
    while pos < len(source):
        m = token.match(source, pos)
        check(m is not None, f"{path}: malformed token at {pos}")
        word = m[0]
        pos = m.end()
        if word.isspace():
            continue
        if word == "(":
            item = []
            (stack[-1] if stack else roots).append(item)
            stack.append(item)
        elif word == ")":
            check(stack and stack[-1], f"{path}: unmatched or empty list")
            stack.pop()
        else:
            check(stack, f"{path}: atom outside root")
            stack[-1].append(json.loads(word) if word.startswith('"') else word)
    check(not stack and len(roots) == 1, f"{path}: incomplete or multiple roots")
    return roots[0]


def children(node, tag):
    return [c for c in node if isinstance(c, list) and c[0] == tag]


def one(node, tag):
    [result] = children(node, tag)
    return result


def fields(node):
    return {p[1]: p[2] for p in children(node, "property")}


def xy(node, tag):
    return tuple(round(float(v), 6) for v in one(node, tag)[1:3])


def pins(model):
    pins = {}
    for unit in children(model, "symbol"):
        for pin in children(unit, "pin"):
            number = one(pin, "number")[1]
            check(number not in pins, f"Duplicate symbol pin {number}")
            pins[number] = pin
    return pins


class Nets:
    def __init__(self):
        self.root = {}

    def find(self, p):
        parent = self.root.setdefault(p, p)
        if parent != p:
            self.root[p] = self.find(parent)
        return self.root[p]

    def join(self, a, b):
        self.root[self.find(b)] = self.find(a)


def schematic(schematic_path=SCH):
    sch, lib = parse(schematic_path), parse(SYM)
    check((sch[0], lib[0]) == ("kicad_sch", "kicad_symbol_lib"), "Wrong file roots")
    check(one(sch, "version")[1] == one(lib, "version")[1] == "20231120", "KiCad 8 format required")
    models = {s[1]: s for s in children(lib, "symbol")}
    cached = {s[1].split(":")[1]: s for s in children(one(sch, "lib_symbols"), "symbol")}
    check(models.keys() == cached.keys(), "Library and cache model sets differ")
    for k, s in models.items():
        check(s[2:] == cached[k][2:], f"Stale embedded symbol {k}")
    # Fail closed on additional electrical constructs until their semantics are supported.
    supported = {
        "version",
        "generator",
        "generator_version",
        "uuid",
        "paper",
        "title_block",
        "lib_symbols",
        "symbol",
        "wire",
        "label",
        "junction",
        "no_connect",
        "sheet_instances",
        "text",
        "polyline",
        "rectangle",
        "text_box",
    }
    check(all(c[0] in supported for c in sch[1:]), "Unsupported electrical construct in flat sheet")
    graph = Nets()
    wires = [
        tuple(tuple(float(i) for i in p[1:]) for p in one(w, "pts")[1:]) for w in children(sch, "wire")
    ]
    names = defaultdict(set)
    for n in children(sch, "label"):
        names[xy(n, "at")].add(n[1])
    nc = {xy(n, "at") for n in children(sch, "no_connect")}
    junctions = {xy(n, "at") for n in children(sch, "junction")}
    instances, locations, types, functions = {}, {}, {}, {}
    for instance in children(sch, "symbol"):
        ref = fields(instance)["Reference"]
        check(ref not in instances, "Duplicate instance " + ref)
        instances[ref] = instance
        x, y = xy(instance, "at")
        a = int(one(instance, "at")[3])
        check(
            a in (0, 90, 180, 270) and not children(instance, "mirror"),
            f"Unsupported transform at {ref}",
        )
        k = one(instance, "lib_id")[1].split(":")[1]
        pinset = pins(models[k])
        check(
            Counter(p[1] for p in children(instance, "pin")) == Counter(pinset.keys()),
            f"{ref} instance pin UUID coverage",
        )
        for n, pin in pinset.items():
            dx, dy = xy(pin, "at")
            dx, dy = {0: (dx, -dy), 90: (-dy, -dx), 180: (-dx, dy), 270: (dy, dx)}[a]
            key = (ref, n)
            locations[key] = (round(x + dx, 6), round(y + dy, 6))
            types[key] = pin[1]
            functions[key] = one(pin, "name")[1]
    points = set(locations.values()) | names.keys() | nc | junctions | {p for seg in wires for p in seg}
    wired = set()
    for a, b in wires:
        check((a[0] == b[0]) ^ (a[1] == b[1]), f"Unsupported or zero length wire {a} {b}")
        for p in points:
            if all(min(i, j) <= v <= max(i, j) for i, j, v in zip(a, b, p)):
                graph.join(a, p)
                wired.add(p)
    connected = defaultdict(set)
    for p, labels in names.items():
        check(p in wired, "Dangling label " + str(labels))
        connected[graph.find(p)].update(labels)
    for labels in connected.values():
        check(len(labels) == 1, "Short between labels " + str(sorted(labels)))
    for a, b in wires:
        check(connected[graph.find(a)], "Unlabeled wire island " + str(a))
    check(not (nc & wired), "No-connect marker on wire")
    check(nc <= set(locations.values()), "Orphan no-connect marker")
    result = {}
    for key, p in locations.items():
        labels = connected[graph.find(p)]
        if types[key] == "no_connect" or p in nc:
            check(not labels and list(locations.values()).count(p) == 1, f"NC {key} connected")
            result[key] = None
        else:
            check(len(labels) == 1, f"Unwired pin {key}")
            result[key] = next(iter(labels))
    # Compare every terminal, including the population options and disconnected pads.
    expected = {p.ref: p for p in parts}
    check(
        {ref for ref in instances if not ref.startswith("#")} == set(expected), "Part inventory differs"
    )
    for ref, p in expected.items():
        props = fields(instances[ref])
        check(
            (props["Value"], props["Footprint"], props["MPN"], props["Population"])
            == (p.value, p.fp, p.mpn, p.population),
            f"{ref}: part selection or population differs",
        )
        check((one(instances[ref], "dnp")[1] == "yes") == (p.population != FIT), f"{ref}: assembly flag")
        for (n, name, kind), net in zip(p.pins, p.nets):
            key = ref, n
            check(
                (result[key], functions[key], types[key]) == (net, name, kind),
                f"Pin contract {key}: {result[key]} vs {net}",
            )
    return result, types, functions, instances


def circuit_checks(net, types):
    def pin(ref, n):
        return net[(ref, str(n))]

    # Reconstruct possible DC bias through fitted resistors and option jumpers.
    # Tri-state buses must have independent bias even if their driver releases them.
    for host, aux, ask in itertools.product([False, True], repeat=3):
        fitted = (
            {FIT} | ({HOST} if host else set()) | ({AUX} if aux else set()) | ({ASK} if ask else set())
        )
        resist = defaultdict(set)
        driven = {V, G, "BENCH_5V"}
        if host:
            driven.add(H)
        if aux:
            driven.add("VIN_AUX")
        if ask:
            driven.add("RECT")  # RF-powered operating case
        for p in parts:
            if p.population not in fitted:
                continue
            if p.model == "R":
                a, b = pin(p.ref, 1), pin(p.ref, 2)
                resist[a].add(b)
                resist[b].add(a)
            for n, name, kind in p.pins:
                if kind in ("output", "power_out"):
                    driven.add(pin(p.ref, n))

        # ENV receives rectified RF and a DC bias resistor. Clamp and storage
        # nodes have a bleed. MOS gate inputs need a DC path when RF is absent.
        def biased(start):
            seen = set()
            todo = [start]
            while todo:
                current = todo.pop()
                if current in seen:
                    continue
                if current in driven:
                    return True
                seen.add(current)
                todo.extend(resist[current] - seen)
            return False

        for p in parts:
            if p.population not in fitted:
                continue
            for n, name, kind in p.pins:
                if kind in ("input", "power_in"):
                    check(biased(pin(p.ref, n)), f"Floating input {p.ref}.{n} ({name}) in {fitted}")
        for i in range(8):
            check(biased(pin("U1", i + 5)), f"DQ{i} lacks idle bias")
            if host:
                check(biased(pin("U4", i + 3)), f"Host-side DQ{i} lacks bias")
        if host:
            for n in range(3, 11):
                check(biased(pin("U5", n)), f"U5 A-port input {n} lacks bias")
    check(
        pin("Q1", 1) == pin("D3", 1) == pin("D4", 3)
        and pin("Q1", 2) == G
        and pin("Q1", 3) == pin("U1", 44),
        "Cold detector topology",
    )
    check(
        pin("D1", 3) == pin("D3", 3) == pin("DZ1", 1) == "RECT"
        and pin("RP1", 1) == V
        and pin("RP1", 2) == pin("U1", 44),
        "RECT or pull-up isolation",
    )
    # A hard short can exist through an unlabelled wire or a zero-ohm link.
    # The pin contract rejects added links; each fitted rectifier-side endpoint is also allowlisted.
    rect = {k for k, v in net.items() if v == "RECT" and not k[0].startswith("#")}
    check(
        rect
        == {
            ("D1", "3"),
            ("D3", "3"),
            ("DZ1", "1"),
            ("CR1", "1"),
            ("RRECT1", "1"),
            ("TP14", "1"),
            ("U7", "5"),
            ("CE3", "1"),
            ("D6", "3"),
        },
        "Unexpected path from RECT",
    )
    for pin_u1, pin_u3, name in [(36, 2, "MISO"), (37, 5, "MOSI"), (38, 6, "SCK"), (39, 1, "CS_N")]:
        n = "FRAM_" + name
        check(pin("U1", pin_u1) == pin("U3", pin_u3) == n, "FRAM bus mismatch " + n)
        check(
            all(
                ref in {"U1", "U3", "J4"} or ref.startswith(("RF", "TP"))
                for (ref, num), v in net.items()
                if v == n
            ),
            "Shared FRAM bus " + n,
        )


def verify_bom(instances):
    rows = list(csv.DictReader((ROOT / "BOM_ASS2_0P5.csv").open()))
    components = [r for r in rows if r["Footprint"] != "Mating accessory"]
    check(Counter(r["Reference"] for r in components) == Counter(p.ref for p in parts), "BOM coverage")
    for r in components:
        props = fields(instances[r["Reference"]])
        check(
            r["MPN"] == props["MPN"]
            and r["Value"] == props["Value"]
            and r["Footprint"] == props["Footprint"],
            "BOM mismatch " + r["Reference"],
        )
        pop = props["Population"]
        purchased = r["MPN"] != "PRINTED"
        check(
            int(r["Base quantity"]) == int(purchased and pop == FIT)
            and int(r["Option quantity"]) == int(purchased and pop != FIT),
            "BOM quantity " + r["Reference"],
        )
    return sum(int(r["Base quantity"]) for r in rows)


def bond_geometry(rows, net):
    doc = parse(PRETTY / (DIE + ".kicad_mod"))
    pads = defaultdict(list)
    for p in children(doc, "pad"):
        pads[p[1]].append(p)
    check(set(pads) == {str(i) for i in range(1, 57)} | {"EP"}, "COB footprint pin set")
    fab = [p for p in children(doc, "fp_rect") if one(p, "layer")[1] == "F.Fab"]
    actual = {tuple(round(v, 6) for v in xy(p, "start") + xy(p, "end")) for p in fab}
    expected = {(-0.968, -1.2655, 0.968, 1.2655)}
    lines = {
        tuple(xy(l, "start") + xy(l, "end"))
        for l in children(doc, "fp_line")
        if one(l, "layer")[1] == "Dwgs.User"
    }
    planned = set()
    side_positions = defaultdict(list)
    for n, side, i, slot, sig, x, y in rows:
        cx, cy = round((x - 968) / 1000, 6), round((1265.5 - y) / 1000, 6)
        expected.add(tuple(round(v, 6) for v in (cx - 0.03, cy - 0.03, cx + 0.03, cy + 0.03)))
        lands = [p for p in pads[str(n)] if "F.Mask" in one(p, "layers")]
        check(len(lands) == (2 if n in (3, 4) else 1), f"{n}: wedge count")
        centers = [xy(p, "at") for p in lands]
        ax = sum(v[0] for v in centers) / len(centers)
        ay = sum(v[1] for v in centers) / len(centers)
        check(
            {"south": ay > 1.2655, "north": ay < -1.2655, "west": ax < -0.968, "east": ax > 0.968}[side],
            f"Finger {n} on wrong side",
        )
        side_positions[side].append(ax if side in ("north", "south") else -ay)
        sig_net = {"VDD": V, "DVDD": V, "DVSS": G, "VSS": G, "n/c": None}.get(sig, sig)
        check(net["U1", str(n)] == sig_net, f"{n}: source pad parity")
        if sig != "n/c":
            for j, p in enumerate(sorted(lands, key=lambda p: xy(p, "at"))):
                origin = cx + (-0.014, 0.014)[j] if len(lands) == 2 else cx
                planned.add((round(origin, 6), cy, *xy(p, "at")))
    for pos in side_positions.values():
        check(
            all(a < b for a, b in zip(pos, pos[1:])), "Finger numbering reversed or swapped within side"
        )
    check(expected == actual and len(fab) == 57, "Die outline or DEF bond windows changed")
    check(planned == lines, "Incorrect bond finger destination")

    def orient(a, b, c):
        return (b[0] - a[0]) * (c[1] - a[1]) - (b[1] - a[1]) * (c[0] - a[0])

    for a, b in itertools.combinations(lines, 2):
        u, v, p, q = a[:2], a[2:], b[:2], b[2:]
        check(
            not (orient(u, v, p) * orient(u, v, q) < 0 and orient(p, q, u) * orient(p, q, v) < 0),
            f"Crossed bonds {a} {b}",
        )
    # Clip each projected bond segment against the other exposed PCB fingers.
    # Include the half width of the drawn wire at each rectangle edge.
    for leg in lines:
        origin, dest = leg[:2], leg[2:]
        for n, group in pads.items():
            if n == "EP":
                continue
            for finger in group:
                center = xy(finger, "at")
                if center == dest or "F.Mask" not in one(finger, "layers"):
                    continue
                low, high = 0.0, 1.0
                for start, stop, c, w in zip(origin, dest, center, xy(finger, "size")):
                    half = w / 2 + 0.006
                    if start == stop:
                        if abs(start - c) > half:
                            low, high = 1, 0
                            break
                    else:
                        ends = sorted(
                            ((c - half - start) / (stop - start), (c + half - start) / (stop - start))
                        )
                        low, high = max(low, ends[0]), min(high, ends[1])
                check(low > high, f"Bond {leg} passes above unrelated PCB finger {n}")
    ep = pads["EP"]
    check(
        net["U1", "EP"] == G and len(ep) == 10 and sum(p[2] == "thru_hole" for p in ep) == 9,
        "Paddle grounding/vias",
    )
    for p in ep:
        if p[2] == "thru_hole":
            x, y = xy(p, "at")
            check(
                one(p, "layers")[1:] == ["*.Cu"]
                and abs(x) <= 0.55
                and abs(y) <= 0.8
                and float(one(p, "drill")[1]) == 0.3,
                "Paddle via details",
            )
    return len(lines)


def coil_geometry(calc_path, footprint_path=PRETTY / (COIL + ".kicad_mod")):
    doc = parse(footprint_path)
    pads = children(doc, "pad")
    winding, feed = sorted(
        (p for p in pads if p[1] == "1"), key=lambda p: -len(children(one(p, "primitives"), "gr_line"))
    )
    check(
        one(winding, "layers")[1:] == ["F.Cu"] and one(doc, "net_tie_pad_groups")[1] == "1,2",
        "Winding layer/net tie",
    )
    lines = children(one(winding, "primitives"), "gr_line")
    check(len(lines) == 16, "Spiral must have sixteen winding legs")
    offset = xy(winding, "at")
    points = []

    def absolute(p):
        return tuple(round(i + j, 6) for i, j in zip(offset, p))

    for i, l in enumerate(lines):
        a, b = absolute(xy(l, "start")), absolute(xy(l, "end"))
        if i == 0:
            points.append(a)
        check(points[-1] == a, "Break in spiral")
        axis = i % 2
        check(
            a[1 - axis] == b[1 - axis] and (b[axis] - a[axis]) * (1 if i % 4 < 2 else -1) > 0,
            "Spiral direction",
        )
        points.append(b)
    widths = {float(one(l, "width")[1]) for l in lines}
    check(widths == {0.42}, "Spiral width mismatch")
    width = widths.pop()
    dimensions = [max(p[d] for p in points) - min(p[d] for p in points) + width for d in (0, 1)]
    check(all(abs(v - 40) < 1e-6 for v in dimensions), "Outer copper dimensions mismatch")
    pitches = set()
    for i in range(12):
        axis = 1 - i % 2
        pitches.add(round(abs(points[i][axis] - points[i + 4][axis]), 6))
    check(pitches == {0.98}, "Spiral pitch mismatch")
    pitch = pitches.pop()
    check(
        all(math.isclose(v, w, abs_tol=1e-8) for v, w in zip(points[-1], (-16.85, -15.87))),
        "Inner turn incomplete",
    )

    # Follow copper from the last segment across the deliberate net tie, through
    # the barrel, along L4 and up to the feed land outside the protected window.
    def trace(p):
        [l] = children(one(p, "primitives"), "gr_line")
        offset = xy(p, "at")
        return [
            tuple(round(i + j, 6) for i, j in zip(offset, xy(l, where))) for where in ("start", "end")
        ]

    top, bottom = [
        next(p for p in pads if p[1] == "2" and p[3] == "custom" and layer in one(p, "layers"))
        for layer in ("F.Cu", "B.Cu")
    ]
    a, b = trace(top)
    c, d = trace(bottom)
    holes = {xy(p, "at") for p in pads if p[1] == "2" and p[2] == "thru_hole"}
    check(a == points[-1] and b == d and c[0] < -23 and {c, d} == holes, "Open winding crossover")
    outer_terminal, join = trace(feed)
    check(join == points[0] and outer_terminal[0] < -23, "Open winding feed")
    for p in (feed, top, bottom):
        check(
            float(one(one(one(p, "primitives"), "gr_line"), "width")[1]) == width,
            "Feed width differs from winding",
        )
    copper_mm = sum(math.dist(a, b) for a, b in zip(points, points[1:])) + sum(
        math.dist(*trace(p)) for p in (feed, top, bottom)
    )
    check(
        math.isclose(copper_mm, 598.24, abs_tol=1e-6),
        "Copper centreline and calculator feed allowance differ",
    )
    zones = children(doc, "zone")
    layers = {"In1.Cu", "In2.Cu", "B.Cu"}
    full = 0
    boxes = defaultdict(list)
    for z in zones:
        k = one(z, "keepout")
        check(
            all(one(k, t)[1] == "not_allowed" for t in ("tracks", "vias", "copperpour")),
            "Incomplete antenna keepout",
        )
        corners = [tuple(map(float, p[1:])) for p in children(one(one(z, "polygon"), "pts"), "xy")]
        xs, ys = zip(*corners)
        x0, x1, y0, y1 = min(xs), max(xs), min(ys), max(ys)
        check(set(corners) == set(itertools.product([x0, x1], [y0, y1])), "Nonrectangular antenna zone")
        ls = set(one(z, "layers")[1:])
        if one(k, "pads")[1] == "allowed":
            check(
                ls == layers and (x0, x1, y0, y1) == (-23, 23, -23, 23),
                "46 mm window or layer assignment",
            )
            full += 1
        else:
            for layer in ls:
                boxes[layer].append((x0, x1, y0, y1))
    check(full == 1 and set(boxes) == layers, "Incomplete keepout layers")
    # Partition at every polygon edge and compare the union to the required
    # 46 mm square minus the one exact pad aperture on this layer.
    for layer, rects in boxes.items():
        left = d[0] - 0.35 if layer != "B.Cu" else -23
        aperture = (left, d[0] + 0.35, d[1] - 0.35, d[1] + 0.35)

        def inside(p, r):
            return r[0] < p[0] < r[1] and r[2] < p[1] < r[3]

        def midpoints(bounds):
            vals = sorted(set(round(x, 6) for x in bounds))
            return [(a + b) / 2 for a, b in zip(vals, vals[1:])]

        xr = midpoints(x for r in rects + [aperture, (-23, 23, -23, 23)] for x in r[:2])
        yr = midpoints(y for r in rects + [aperture, (-23, 23, -23, 23)] for y in r[2:])
        for pt in itertools.product(xr, yr):
            check(
                any(inside(pt, r) for r in rects)
                == (inside(pt, (-23, 23, -23, 23)) and not inside(pt, aperture)),
                f"{layer} keepout coverage at {pt}",
            )
    spec = importlib.util.spec_from_file_location("reference_coil_calc", calc_path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    layers = children(parse(ROOT / "stackup.kicad_sexpr"), "layer")
    check(
        [l[1] for l in layers if one(l, "type")[1] == "copper"] == ["F.Cu", "In1.Cu", "In2.Cu", "B.Cu"],
        "Four-layer stackup order",
    )
    thicknesses = [float(one(l, "thickness")[1]) for l in layers]
    check(math.isclose(sum(thicknesses), 1.6), "Finished stackup thickness")
    coil = module.PlanarSpiralSpec(
        cu_thickness_um=thicknesses[0] * 1000,
        d_out_mm=dimensions[0],
        n_turns=len(lines) // 4,
        trace_w_mm=width,
        trace_s_mm=round(pitch - width, 6),
    )
    check(coil.cu_thickness_um == 35, "Finished copper specification")
    res = module.calc_planar_spiral(coil)
    module.run_self_test(res, coil)
    check(res.l_nom_uh == 1.4662 and round(res.r_ac_13p56mhz_ohm, 3) == 0.988, "Coil model parity")
    return res


def standard_footprints(root):
    for p in parts:
        bank, name = p.fp.split(":")
        lib = PRETTY if bank == "ass2" else root / (bank + ".pretty")
        fp = parse(lib / (name + ".kicad_mod"))
        nums = {pad[1] for pad in children(fp, "pad") if pad[1]}
        check(nums == {n for n, _, _ in p.pins}, p.ref + " symbol/land mismatch")


def command(args):
    run = subprocess.run([str(v) for v in args], capture_output=True, text=True)
    check(run.returncode == 0, run.stdout + run.stderr)
    return run.stdout.strip()


def footprint_drc(cli, tmp):
    candidates = [
        os.getenv("KICAD_PYTHON"),
        sys.executable,
        "/usr/bin/python3",
        "/Applications/KiCad/KiCad.app/Contents/Frameworks/Python.framework/Versions/Current/bin/python3",
    ]
    python = next(
        (
            py
            for py in candidates
            if py
            and Path(py).is_file()
            and subprocess.run([py, "-B", "-c", "import pcbnew"], capture_output=True).returncode == 0
        ),
        None,
    )
    if not python:
        print("Footprint fixture DRC skipped: matching pcbnew Python module unavailable.")
        return
    for name in ("fixture", "intrusions"):
        shutil.copyfile(SCH.with_suffix(".kicad_pro"), tmp / (name + ".kicad_pro"))
    shutil.copytree(PRETTY, tmp / PRETTY.name)
    shutil.copyfile(ROOT / "fp-lib-table", tmp / "fp-lib-table")
    command([python, "-B", ROOT / "footprint_fixture.py", ROOT, tmp])
    args = [cli, "pcb", "drc", "--severity-all", "--format", "json"]
    command(args + ["--exit-code-violations", "-o", tmp / "fixture.json", tmp / "fixture.kicad_pcb"])
    command(args + ["-o", tmp / "intrusions.json", tmp / "intrusions.kicad_pcb"])
    results = json.loads((tmp / "intrusions.json").read_text())
    rejected = [v for v in results["violations"] if v["type"] == "items_not_allowed"]
    for layer in ("In1.Cu", "In2.Cu", "B.Cu"):
        check(
            any(layer in obj["description"] for v in rejected for obj in v["items"]),
            f"Native DRC missed in-window routing on {layer}",
        )
    print(
        "Four-layer footprint fixture: zero DRC violations and opens; L2, L3 and L4 intrusion controls rejected."
    )


def native(cli, net, tmp):
    # CLI 8 resolves local library tables from the absolute project path.
    version = command([cli, "version"])
    rpt = tmp / "erc.rpt"
    command([cli, "sch", "erc", "--exit-code-violations", "--severity-all", "-o", rpt, SCH])
    file = tmp / "netlist.xml"
    command([cli, "sch", "export", "netlist", "--format", "kicadxml", "-o", file, SCH])
    native_net = {}
    for n in ET.parse(file).findall("nets/net"):
        name = n.get("name").removeprefix("/")
        for node in n.findall("node"):
            k = node.get("ref"), node.get("pin")
            check(k not in native_net, "Repeated KiCad terminal " + str(k))
            native_net[k] = None if name.startswith("unconnected-(") else name
    expected = {k: v for k, v in net.items() if not k[0].startswith("#")}
    check(native_net == expected, "KiCad XML does not agree with standalone netlist")
    command([cli, "fp", "export", "svg", "-o", tmp / "footprints", PRETTY])
    footprint_drc(cli, tmp)
    print(
        f"KiCad {version}: zero ERC violations; XML agrees on all {len(expected)} physical symbol pins."
    )


def negative_controls(tmp, calc_path):
    original = SCH.read_text()

    def expect_failure(fn, message):
        try:
            fn()
        except ValueError as exc:
            check(message in str(exc), f"Unexpected negative-control failure: {exc}")
            return
        raise ValueError("Accepted injected fault: " + message)

    def trial_schematic(content, message):
        path = tmp / "mutation.kicad_sch"
        path.write_text(content)
        expect_failure(lambda: schematic(path), message)

    # Open the actual first wire and remove its orphan label.
    trial_schematic(
        re.sub(r"^  \(wire .*?\n  \(label .*?\n", "", original, count=1, flags=re.M), "Unwired pin"
    )
    doc = parse(SCH)
    labels = {l[1]: xy(l, "at") for l in children(doc, "label")}
    (a, b), (c, d) = labels["RECT"], labels["V5_CHIP"]
    path = [(a, b), (a, d), (c, d)]
    link = "".join(
        f"(wire (pts (xy {x} {y}) (xy {u} {v})))"
        for (x, y), (u, v) in zip(path, path[1:])
        if (x, y) != (u, v)
    )
    trial_schematic(original.rstrip()[:-1] + link + ")", "Short between labels")
    trial_schematic(original.replace('(label "FRAM_MISO"', '(label "FRAM_MOSI"', 1), "Pin contract")
    path = tmp / "mutation.kicad_mod"
    path.write_text(
        (PRETTY / (COIL + ".kicad_mod")).read_text().replace("(width 0.42)", "(width 0.45)", 1)
    )
    expect_failure(lambda: coil_geometry(calc_path, path), "Spiral width")
    print(
        "Negative controls rejected an open input, a rail short, a FRAM data swap and a winding-width error."
    )


def write_netlist(path, net, types, functions, instances):
    with path.open("w", newline="") as file:
        writer = csv.writer(file)
        writer.writerow(["Reference", "Pin", "Pin function", "Electrical type", "Net", "Population"])
        for (ref, n), signal in net.items():
            if not ref.startswith("#"):
                writer.writerow(
                    [
                        ref,
                        n,
                        functions[ref, n],
                        types[ref, n],
                        signal or "NC",
                        fields(instances[ref])["Population"],
                    ]
                )


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--slot", type=Path, default=SRC / "slot_0p5x0p5.yaml")
    p.add_argument("--datasheet", type=Path, default=SRC / "pad-ring.typ")
    p.add_argument(
        "--def-file",
        type=Path,
        default=SRC / "bond-windows.def",
        help="Original or extracted DEF, optionally gzipped",
    )
    p.add_argument("--calculator", type=Path, default=SRC / "planar_nfc_coil_calc.py")
    p.add_argument("--cli", help="Path to kicad-cli")
    p.add_argument("--standalone", action="store_true")
    p.add_argument("--footprints", type=Path, help="Installed KiCad .pretty library root")
    p.add_argument(
        "--self-test",
        action="store_true",
        help="Inject four faults in temporary copies and require rejection",
    )
    p.add_argument(
        "--netlist", type=Path, help="Write verified pin-level CSV for all population options"
    )
    args = p.parse_args()
    with tempfile.TemporaryDirectory(prefix="ass2-erc-") as temp:
        tmp = Path(temp)
        placement = args.def_file
        if placement.suffix == ".gz":
            text = gzip.open(placement, "rt").read()
            placement = tmp / "pins.def"
            placement.write_text(
                "\n".join(
                    re.findall(
                        r"^(?:UNITS DISTANCE[^;]+;|DIEAREA [^;]+;|PINS \d+ ;.*?^END PINS)",
                        text,
                        re.M | re.S,
                    )
                )
            )
        sources = padmap(args.slot, args.datasheet, placement)
        net, types, functions, instances = schematic()
        circuit_checks(net, types)
        qty = verify_bom(instances)
        bonds = bond_geometry(sources, net)
        res = coil_geometry(args.calculator)
        print(
            f"{len(parts)} component references, {qty} default purchased items, {len(set(net.values()) - {None})} named nets."
        )
        print(
            f"56/56 die pads, four analog NC, {bonds} wirebonds, nine EP vias; slot, datasheet and DEF agree."
        )
        print(
            f"Eight population combinations: all fitted inputs biased; RECT/V5_CHIP distinct; private FRAM SPI verified."
        )
        print(
            f"Four turns, 40.00 mm, 0.42/0.56 mm, 35 um; 46 mm keepout; {res.l_nom_uh:.4f} uH and {res.r_ac_13p56mhz_ohm:.4f} ohm."
        )
        mac = Path("/Applications/KiCad/KiCad.app/Contents")
        paths = [
            args.footprints,
            os.getenv("KICAD8_FOOTPRINT_DIR"),
            mac / "SharedSupport/footprints",
            Path("/usr/share/kicad/footprints"),
        ]
        installed = next((Path(path) for path in paths if path and Path(path).is_dir()), None)
        if args.footprints or installed:
            standard_footprints(args.footprints or installed)
            print("All symbol pin numbers match their assigned footprint pads.")
        if args.self_test:
            negative_controls(tmp, args.calculator)
        if not args.standalone:
            cli = args.cli or shutil.which("kicad-cli") or mac / "MacOS/kicad-cli"
            if args.cli or Path(cli).exists():
                native(cli, net, tmp)
            else:
                print("Native KiCad unavailable; standalone checks passed.")
        if args.netlist:
            write_netlist(args.netlist, net, types, functions, instances)
    print("PASS")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, OSError, KeyError, AssertionError) as e:
        sys.exit(f"FAIL: {e}")
