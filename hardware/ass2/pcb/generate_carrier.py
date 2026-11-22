#!/usr/bin/env python3
"""Rebuild KiCad 8 libraries, schematic and purchasing schedule deterministically."""

import csv
import json
import math
import re
import uuid
from collections import defaultdict

from carrier import parts, Part, FIT, rows
from geometry import ROOT, die_footprint, coil_footprint

PROJECT = "ass2_0p5_carrier"
LIB = "ass2_0p5"


def uid(*path):
    return str(uuid.uuid5(uuid.NAMESPACE_URL, "ass2-carrier/" + "/".join(map(str, path))))


def q(s):
    return json.dumps(str(s), ensure_ascii=False)


def f(x):
    return f"{x:.5f}".rstrip("0").rstrip(".") if x else "0"


def at(x, y, angle=0):
    return f"(at {f(x)} {f(y)} {angle})"


def effects(size=1, justify="", hide=False):
    return (
        f"(effects (font (size {size} {size})) "
        + (f"(justify {justify}) " if justify else "")
        + ("(hide yes)" if hide else "")
        + ")"
    )


def prop(name, value, x, y, hide=False):
    return f"(property {q(name)} {q(value)} {at(x, y)} {effects(hide=hide)})"


stroke = "(stroke (width 0.254) (type default))"


def poly(points):
    return (
        "(polyline (pts "
        + " ".join(f"(xy {f(x)} {f(y)})" for x, y in points)
        + f") {stroke} (fill (type none)))"
    )


def box(x, y):
    return f"(rectangle (start {f(-x)} {f(y)}) (end {f(x)} {f(-y)}) {stroke} (fill (type background)))"


def shape(part):
    count = len(part.pins)
    left = (count + 1) // 2
    special = part.model in ("R", "C")
    if special:
        pins = [(-5.08, 0, 0, 2.54), (5.08, 0, 180, 2.54)]
        if part.model == "R":
            graphics = box(2.54, 0.85)
        else:
            graphics = " ".join(
                poly(seg)
                for seg in [
                    [(-2.54, 0), (-0.45, 0)],
                    [(0.45, 0), (2.54, 0)],
                    [(-0.45, -1.5), (-0.45, 1.5)],
                    [(0.45, -1.5), (0.45, 1.5)],
                ]
            )
        return pins, graphics, 2.54
    if part.model in ("BAS70", "Zener"):
        # Both diodes face left-to-right electrically. Zener package pin 1 is K.
        a, k = (-5.08, 0, 0, 2.54), (5.08, 0, 180, 2.54)
        graphics = (
            poly([(-2.54, 0), (-1.3, 0)])
            + poly([(-1.3, -1.3), (-1.3, 1.3), (1.3, 0), (-1.3, -1.3)])
            + poly([(1.3, 0), (2.54, 0)])
        )
        bar = [(0.6, -1.6), (1.3, -1.3), (1.3, 1.3), (2, 1.6)]
        if part.model == "BAS70":
            # The electrically NC package lead is visible below the anode.
            return [a, (-5.08, -2.54, 0, 1.27), k], graphics + poly(bar), 2.54
        return [k, a], graphics + poly(bar), 2.54
    if part.model in ("Trimmer", "Printed_coil"):
        coords = [(-5.08, 0, 0, 2.54), (5.08, 0, 180, 2.54)]
        if part.model == "Trimmer":
            segs = [
                [(-2.54, 0), (-0.5, 0)],
                [(0.5, 0), (2.54, 0)],
                [(-0.5, -1.2), (-0.5, 1.2)],
                [(0.5, -1.2), (0.5, 1.2)],
                [(-1.6, -1.5), (1.6, 1.5)],
                [(1.1, 2), (2.1, 1)],
            ]
            graphic = "".join(poly(seg) for seg in segs)
        else:
            graphic = "".join(
                f"(arc (start {f(-2.54 + i * 1.27)} 0) (mid {f(-1.905 + i * 1.27)} 0.635) (end {f(-1.27 + i * 1.27)} 0) {stroke} (fill (type none)))"
                for i in range(4)
            )
        return coords, graphic, 2.54
    if part.model == "FDV301N":
        coords = [(-5.08, 0, 0, 2.54), (5.08, -2.54, 180, 2.54), (5.08, 2.54, 180, 2.54)]
        segs = [
            [(-2.54, 0), (-0.8, 0)],
            [(-0.8, -1.25), (-0.8, 1.25)],
            [(0.05, -1.55), (0.05, -0.75)],
            [(0.05, -0.4), (0.05, 0.4)],
            [(0.05, 0.75), (0.05, 1.55)],
            [(0.05, 1.1), (1.5, 1.1), (1.5, 2.54), (2.54, 2.54)],
            [(0.05, -1.1), (1.5, -1.1), (1.5, -2.54), (2.54, -2.54)],
            [(1.5, -1.1), (1.5, 0), (0.1, 0)],
            [(0.7, 0.35), (0.1, 0), (0.7, -0.35)],
        ]
        return coords, "".join(poly(seg) for seg in segs), 3.81
    if part.model == "Probe":
        return (
            [(-2.54, 0, 0, 1.27)],
            f"(circle (center -0.67 0) (radius 0.6) {stroke} (fill (type none)))",
            1.27,
        )
    if part.model == "Power_entry":
        return [(-2.54, 0, 0, 1.27)], poly([(-1.27, 0), (0, 0), (0, 1.3), (1.5, 0.85), (0, 0.45)]), 1.27
    width = 15.24 if count > 32 else 7.62 if count >= 3 else 5.08
    pins = []
    for i in range(count):
        side = -1 if i < left else 1
        row = i if side < 0 else i - left
        pins.append((side * (width + 2.54), -row * 2.54, 0 if side < 0 else 180, 2.54))
    graphic = f"(rectangle (start {f(-width)} 1.27) (end {f(width)} {f(-(left - 1) * 2.54 - 1.27)}) {stroke} (fill (type background)))"
    return pins, graphic, 1.27


def symbol(part, embedded):
    name = part.model
    idname = (LIB + ":" + name) if embedded else name
    pins, graphic, above = shape(part)
    hidden = (
        "(pin_numbers hide) (pin_names (offset 0.5) hide)"
        if name
        in ("R", "C", "BAS70", "Zener", "Probe", "FDV301N", "Trimmer", "Printed_coil", "Power_entry")
        else "(pin_names (offset 0.6))"
    )
    physical = "no" if part.ref.startswith("#") else "yes"
    items = [
        f"(symbol {q(idname)} {hidden} (exclude_from_sim no) (in_bom {physical}) (on_board {physical})",
        prop("Reference", re.sub(r"[0-9]+$", "", part.ref), 0, above + 4),
        prop("Value", name, 0, above + 2),
        prop(
            "Footprint",
            "" if part.model.startswith("Header") or name in ("R", "C") else part.fp,
            0,
            0,
            True,
        ),
        f'(symbol "{name}_0_1" {graphic})',
        f'(symbol "{name}_1_1"',
    ]
    for (n, pin, kind), (x, y, angle, length) in zip(part.pins, pins):
        items.append(
            f"(pin {kind} line {at(x, y, angle)} (length {length}) (name {q(pin)} {effects(0.92)}) (number {q(n)} {effects(0.8)}))"
        )
    return "\n    ".join(items) + "))"


def instance(part, x, y):
    coords, graphic, above = shape(part)
    dnp = part.population != FIT
    physical = "no" if part.ref.startswith("#") else "yes"
    items = [
        f'(symbol (lib_id "{LIB}:{part.model}") {at(x, y)} (unit 1) (exclude_from_sim no) (in_bom {physical}) (on_board {physical}) (dnp {"yes" if dnp else "no"}) (uuid {uid(part.ref)})',
        prop("Reference", part.ref, x, y - above - 3.81),
        prop("Value", part.value, x, y - above - 1.75),
        prop("Footprint", part.fp, x, y, True),
        prop("MPN", part.mpn, x, y, True),
        prop("Population", part.population, x, y, True),
    ]
    for n, *_ in part.pins:
        items.append(f"(pin {q(n)} (uuid {uid(part.ref, n)}))")
    items.append(
        f'(instances (project "{PROJECT}" (path "/{uid(PROJECT)}" (reference "{part.ref}") (unit 1)))))'
    )
    for (n, _, kind), net, (dx, dy, angle, length) in zip(part.pins, part.nets, coords):
        px, py = x + dx, y - dy
        if net is None:
            if kind == "no_connect":
                continue
            items.append(f"(no_connect (at {f(px)} {f(py)}) (uuid {uid(part.ref, n, 'nc')}))")
            continue
        sign = -1 if angle == 0 else 1
        end = px + sign * 16.51
        items.append(
            f"(wire (pts (xy {f(px)} {f(py)}) (xy {f(end)} {f(py)})) (stroke (width 0) (type default)) (uuid {uid(part.ref, n, 'wire')}))"
        )
        items.append(
            f"(label {q(net)} {at(end, py, angle)} {effects(0.95, ('left' if sign < 0 else 'right') + ' bottom')} (uuid {uid(part.ref, n, 'label')}))"
        )
    return "\n  ".join(items)


def main():
    die_footprint(rows)
    coil_footprint()
    design = list(parts)
    # Explicit power-entry assertions for an external feed, jumper-fed rail and rectifier.
    for i, (net, section) in enumerate(
        [
            ("GND", "Die and local power"),
            ("V5_CHIP", "Die and local power"),
            ("VIN_AUX", "Auxiliary regulator"),
            ("HOST_3V3", "3.3 V host option"),
            ("RECT", "NFC tank and cold tap"),
        ],
        1,
    ):
        design.append(
            Part(
                f"#FLG0{i}",
                "Power entry",
                "Power_entry",
                "",
                [("1", "PWR", "power_out")],
                [net],
                "",
                "",
                FIT,
                "",
                section,
            )
        )
    models = {}
    for p in design:
        if p.model in models and models[p.model].pins != p.pins:
            raise ValueError(p.model + " has inconsistent pin definitions")
        models.setdefault(p.model, p)
    (ROOT / (LIB + ".kicad_sym")).write_text(
        '(kicad_symbol_lib (version 20231120) (generator "ass2_carrier")\n  '
        + "\n  ".join(symbol(p, False) for p in models.values())
        + "\n)\n"
    )
    body = []
    groups = defaultdict(list)
    for p in design:
        groups[p.section].append(p)
    # Each circuit occupies a titled panel. Distribute devices down three lanes.
    grid = [
        ["Die and local power", "Reset, tamper and straps", "Private FRAM"],
        ["Host and expansion", "3.3 V host option", "Auxiliary regulator"],
        ["NFC tank and cold tap", "ASK evaluation", "Probe lands"],
    ]
    top = 17.78
    for row in grid:
        heights = []
        for col, title in enumerate(row):
            left = 12.7 + col * 213.36
            body.append(
                f"(text {q(title)} {at(left, top)} {effects(2.54, 'left bottom')} (uuid {uid(title)}))"
            )
            body.append(
                f"(polyline (pts (xy {f(left)} {f(top + 1.27)}) (xy {f(left + 207.01)} {f(top + 1.27)})) {stroke} (fill (type none)) (uuid {uid(title, 'rule')}))"
            )
            cursors = [top + 12.7] * 3
            for p in groups[title]:
                lane = min(range(3), key=cursors.__getitem__)
                x = left + 35.56 + lane * 69.85
                body.append(instance(p, x, cursors[lane]))
                depth = -min(c[1] for c in shape(p)[0])
                cursors[lane] += depth + 13.97
            heights.extend(cursors)
        top = max(heights) + 7.62
    sheet_height = math.ceil(top + 48)
    src = (
        f'(kicad_sch (version 20231120) (generator "ass2_carrier") (uuid {uid(PROJECT)}) (paper "User" 660 {sheet_height})\n  (title_block (title "ASS2-0P5 reference carrier") (rev "1.0") (comment 1 "Bench 5 V default | 3.3 V translation, ASK and auxiliary LDO optional"))\n  (lib_symbols\n    '
        + "\n    ".join(symbol(p, True) for p in models.values())
        + ")\n  "
        + "\n  ".join(body)
        + '\n  (sheet_instances (path "/" (page "1")))\n)\n'
    )
    (ROOT / (PROJECT + ".kicad_sch")).write_text(src)
    (ROOT / "sym-lib-table").write_text(
        f'(sym_lib_table (version 7) (lib (name "{LIB}") (type "KiCad") (uri "${{KIPRJMOD}}/{LIB}.kicad_sym") (options "") (descr "ASS2 carrier")))\n'
    )
    (ROOT / "fp-lib-table").write_text(
        '(fp_lib_table (version 7) (lib (name "ass2") (type "KiCad") (uri "${KIPRJMOD}/ass2.pretty") (options "") (descr "COB and printed coil")))\n'
    )
    with (ROOT / "BOM_ASS2_0P5.csv").open("w", newline="") as file:
        w = csv.writer(file)
        w.writerow(
            [
                "Reference",
                "Base quantity",
                "Option quantity",
                "Value",
                "Manufacturer",
                "MPN",
                "Footprint",
                "Population",
                "Circuit",
                "Notes",
            ]
        )
        for p in parts:
            if p.ref.startswith("#"):
                continue
            base = int(p.population == FIT and p.mpn != "PRINTED")
            w.writerow(
                [
                    p.ref,
                    base,
                    int(p.population != FIT),
                    p.value,
                    p.manufacturer,
                    p.mpn,
                    p.fp,
                    "PCB" if p.mpn == "PRINTED" else p.population,
                    p.section,
                    p.note.strip(),
                ]
            )
        w.writerow(
            [
                "JP1 JP2",
                2,
                0,
                "2.54 mm shunt",
                "Samtec",
                "SNT-100-BK-G",
                "Mating accessory",
                "FIT",
                "Supply selection",
                "Fit one shunt to JP1 and one to JP2 pins 1-2",
            ]
        )
        w.writerow(
            [
                "JP6",
                0,
                1,
                "2.54 mm shunt",
                "Samtec",
                "SNT-100-BK-G",
                "Mating accessory",
                "3V3 host",
                "Width select",
                "Fit for x1 only",
            ]
        )
        w.writerow(
            [
                "JP7",
                0,
                1,
                "2.54 mm shunt",
                "Samtec",
                "SNT-100-BK-G",
                "Mating accessory",
                "ASK evaluation",
                "Detector output",
                "Fit after detector commissioning",
            ]
        )


if __name__ == "__main__":
    main()
