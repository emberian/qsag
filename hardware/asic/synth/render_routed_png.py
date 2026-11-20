#!/usr/bin/env python3
"""Render a high-resolution PNG of an OpenROAD routed DEF (`routed.def`) using pure Python stdlib
(`zlib` + `struct`, zero external package dependencies).

Draws:
  - Die & core boundaries,
  - Placed standard cells & CTS clock-tree buffers (`CLKBUF_*`),
  - Routed signal & clock wires from `NETS` across `metal2..metal10` (color-coded by layer),
  - All 4 symmetric Basin-1 SRAM macros (`sram_dp_64x16384_bank`) with orientation labels and
    highlighted inward-facing pin strips,
  - Perimeter IO pins on N/S/E/W edges.
"""
import re
import struct
import sys
import zlib
from pathlib import Path


def write_png(path: Path, width: int, height: int, rgb: bytearray):
    def chunk(tag: bytes, data: bytes) -> bytes:
        return (
            struct.pack(">I", len(data))
            + tag
            + data
            + struct.pack(">I", zlib.crc32(tag + data) & 0xFFFFFFFF)
        )

    raw = bytearray()
    stride = width * 3
    for y in range(height):
        raw.append(0)
        raw.extend(rgb[y * stride:(y + 1) * stride])
    ihdr = struct.pack(">IIBBBBB", width, height, 8, 2, 0, 0, 0)
    png = b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", ihdr) + chunk(b"IDAT", zlib.compress(bytes(raw), 6)) + chunk(b"IEND", b"")
    path.write_bytes(png)


FONT_5X7 = {
    "A": ["01110", "10001", "10001", "11111", "10001", "10001", "10001"],
    "B": ["11110", "10001", "10001", "11110", "10001", "10001", "11110"],
    "C": ["01110", "10001", "10000", "10000", "10000", "10001", "01110"],
    "D": ["11100", "10010", "10001", "10001", "10001", "10010", "11100"],
    "E": ["11111", "10000", "10000", "11110", "10000", "10000", "11111"],
    "F": ["11111", "10000", "10000", "11110", "10000", "10000", "10000"],
    "G": ["01110", "10001", "10000", "10111", "10001", "10001", "01110"],
    "H": ["10001", "10001", "10001", "11111", "10001", "10001", "10001"],
    "I": ["01110", "00100", "00100", "00100", "00100", "00100", "01110"],
    "K": ["10001", "10010", "10100", "11000", "10100", "10010", "10001"],
    "L": ["10000", "10000", "10000", "10000", "10000", "10000", "11111"],
    "M": ["10001", "11011", "10101", "10101", "10001", "10001", "10001"],
    "N": ["10001", "11001", "10101", "10011", "10001", "10001", "10001"],
    "O": ["01110", "10001", "10001", "10001", "10001", "10001", "01110"],
    "P": ["11110", "10001", "10001", "11110", "10000", "10000", "10000"],
    "Q": ["01110", "10001", "10001", "10001", "10101", "10010", "01101"],
    "R": ["11110", "10001", "10001", "11110", "10100", "10010", "10001"],
    "S": ["01111", "10000", "10000", "01110", "00001", "00001", "11110"],
    "T": ["11111", "00100", "00100", "00100", "00100", "00100", "00100"],
    "U": ["10001", "10001", "10001", "10001", "10001", "10001", "01110"],
    "V": ["10001", "10001", "10001", "10001", "10001", "01010", "00100"],
    "W": ["10001", "10001", "10001", "10101", "10101", "11011", "10001"],
    "X": ["10001", "10001", "01010", "00100", "01010", "10001", "10001"],
    "Y": ["10001", "10001", "01010", "00100", "00100", "00100", "00100"],
    "0": ["01110", "10011", "10101", "10101", "11001", "10001", "01110"],
    "1": ["00100", "01100", "00100", "00100", "00100", "00100", "01110"],
    "2": ["01110", "10001", "00001", "00110", "01000", "10000", "11111"],
    "3": ["11110", "00001", "00001", "01110", "00001", "00001", "11110"],
    "4": ["00010", "00110", "01010", "10010", "11111", "00010", "00010"],
    "5": ["11111", "10000", "11110", "00001", "00001", "10001", "01110"],
    "6": ["01110", "10000", "11110", "10001", "10001", "10001", "01110"],
    "7": ["11111", "00001", "00010", "00100", "01000", "01000", "01000"],
    "8": ["01110", "10001", "10001", "01110", "10001", "10001", "01110"],
    "9": ["01110", "10001", "10001", "01111", "00001", "00001", "01110"],
    ".": ["00000", "00000", "00000", "00000", "00000", "01100", "01100"],
    "-": ["00000", "00000", "00000", "11111", "00000", "00000", "00000"],
    "_": ["00000", "00000", "00000", "00000", "00000", "00000", "11111"],
    ":": ["00000", "01100", "01100", "00000", "01100", "01100", "00000"],
    "/": ["00001", "00010", "00100", "00100", "01000", "10000", "00000"],
    "(": ["00010", "00100", "01000", "01000", "01000", "00100", "00010"],
    ")": ["01000", "00100", "00010", "00010", "00010", "00100", "01000"],
    " ": ["00000", "00000", "00000", "00000", "00000", "00000", "00000"],
}


def render_def(def_path: Path, png_path: Path, macro_w_um: float, macro_h_um: float, title: str = ""):
    W = H = 1600
    PAD = 70
    rgb = bytearray([12, 16, 24] * (W * H))

    def set_px(px: int, py: int, col, alpha: float = 1.0):
        if 0 <= px < W and 0 <= py < H:
            off = (py * W + px) * 3
            if alpha >= 0.999:
                rgb[off], rgb[off + 1], rgb[off + 2] = col
            else:
                ia = 1.0 - alpha
                rgb[off] = int(rgb[off] * ia + col[0] * alpha)
                rgb[off + 1] = int(rgb[off + 1] * ia + col[1] * alpha)
                rgb[off + 2] = int(rgb[off + 2] * ia + col[2] * alpha)

    def fill_rect(x0, y0, x1, y1, col, alpha=1.0):
        xa, xb = max(0, min(x0, x1)), min(W - 1, max(x0, x1))
        ya, yb = max(0, min(y0, y1)), min(H - 1, max(y0, y1))
        for py in range(ya, yb + 1):
            for px in range(xa, xb + 1):
                set_px(px, py, col, alpha)

    def stroke_rect(x0, y0, x1, y1, col, lw=2):
        fill_rect(x0, y0, x1, y0 + lw - 1, col)
        fill_rect(x0, y1 - lw + 1, x1, y1, col)
        fill_rect(x0, y0, x0 + lw - 1, y1, col)
        fill_rect(x1 - lw + 1, y0, x1, y1, col)

    def draw_line(x0, y0, x1, y1, col, alpha=0.45):
        if x0 == x1:
            ya, yb = max(0, min(y0, y1)), min(H - 1, max(y0, y1))
            if 0 <= x0 < W:
                for py in range(ya, yb + 1):
                    set_px(x0, py, col, alpha)
        elif y0 == y1:
            xa, xb = max(0, min(x0, x1)), min(W - 1, max(x0, x1))
            if 0 <= y0 < H:
                for px in range(xa, xb + 1):
                    set_px(px, y0, col, alpha)

    def draw_text(tx: int, ty: int, text: str, col=(235, 240, 250), scale: int = 2):
        cx = tx
        for ch in text.upper():
            glyph = FONT_5X7.get(ch, FONT_5X7[" "])
            for gy, row in enumerate(glyph):
                for gx, bit in enumerate(row):
                    if bit == "1":
                        fill_rect(cx + gx * scale, ty + gy * scale,
                                  cx + (gx + 1) * scale - 1, ty + (gy + 1) * scale - 1, col)
            cx += 6 * scale

    text = def_path.read_text()
    m_units = re.search(r"UNITS DISTANCE MICRONS\s+(\d+)", text)
    dbu = float(m_units.group(1)) if m_units else 2000.0
    m_die = re.search(r"DIEAREA\s*\(\s*(\d+)\s+(\d+)\s*\)\s*\(\s*(\d+)\s+(\d+)\s*\)", text)
    dx0, dy0, dx1, dy1 = (int(m_die.group(i)) for i in range(1, 5))
    die_w = max(1, dx1 - dx0)
    die_h = max(1, dy1 - dy0)
    scale = (W - 2 * PAD) / max(die_w, die_h)

    def to_px(x_dbu: int, y_dbu: int):
        px = int(PAD + (x_dbu - dx0) * scale)
        py = int(H - PAD - (y_dbu - dy0) * scale)
        return px, py

    # Die box
    p0x, p0y = to_px(dx0, dy0)
    p1x, p1y = to_px(dx1, dy1)
    fill_rect(p0x, p1y, p1x, p0y, (20, 26, 38))
    stroke_rect(p0x, p1y, p1x, p0y, (130, 150, 185), lw=3)

    # Core row bounds
    row_xs, row_ys = [], []
    for m in re.finditer(r"ROW\s+\S+\s+\S+\s+(\d+)\s+(\d+)\s+\S+\s+DO\s+(\d+)\s+BY\s+\d+\s+STEP\s+(\d+)", text):
        rx, ry, nx, step = (int(m.group(i)) for i in range(1, 5))
        row_xs += [rx, rx + nx * step]
        row_ys.append(ry)
    if row_xs and row_ys:
        cx0, cy0 = to_px(min(row_xs), min(row_ys))
        cx1, cy1 = to_px(max(row_xs), max(row_ys) + int(1.4 * dbu))
        stroke_rect(cx0, cy1, cx1, cy0, (70, 95, 130), lw=1)

    # Components (stdcells, CTS buffers, SRAM macros)
    comp_sec = re.search(r"COMPONENTS\s+\d+\s*;(.*?)END COMPONENTS", text, re.S)
    macros = []
    std_cnt = cts_cnt = 0
    if comp_sec:
        for m in re.finditer(r"-\s+(\S+)\s+(\S+)\s+\+\s+(?:PLACED|FIXED)\s*\(\s*(\d+)\s+(\d+)\s*\)\s*(\S+)", comp_sec.group(1)):
            inst, master, x, y, orient = m.group(1), m.group(2), int(m.group(3)), int(m.group(4)), m.group(5)
            if master == "sram_dp_64x16384_bank":
                macros.append((inst, x, y, orient))
            elif master.startswith("FILL") or master.startswith("TAP"):
                continue
            else:
                px, py = to_px(x, y)
                if "CLKBUF" in master or " cts" in inst:
                    cts_cnt += 1
                    fill_rect(px, py - 1, px + 1, py, (255, 200, 70), 0.85)
                else:
                    std_cnt += 1
                    set_px(px, py, (52, 118, 196), 0.55)

    # Routed NETS wire segments (sampled densely across all layers)
    layer_cols = {
        "metal1": (70, 130, 180),
        "metal2": (46, 204, 113),
        "metal3": (52, 152, 219),
        "metal4": (241, 196, 15),
        "metal5": (230, 126, 34),
        "metal6": (231, 76, 60),
        "metal7": (155, 89, 182),
        "metal8": (26, 188, 156),
    }
    nets_sec = re.search(r"\nNETS\s+\d+\s*;(.*?)END NETS", text, re.S)
    seg_cnt = 0
    if nets_sec:
        # Match `NEW|ROUTED <layer> ( x0 y0 ) ( x1 y1 )` where `*` means keep previous coordinate
        for m in re.finditer(r"(?:ROUTED|NEW)\s+(metal\d+|met\d+)\s+\(\s*(\d+)\s+(\d+)\s*\)\s+\(\s*(\*|\d+)\s+(\*|\d+)\s*\)", nets_sec.group(1)):
            lyr = m.group(1).replace("met", "metal")
            x0, y0 = int(m.group(2)), int(m.group(3))
            x1 = x0 if m.group(4) == "*" else int(m.group(4))
            y1 = y0 if m.group(5) == "*" else int(m.group(5))
            seg_cnt += 1
            if seg_cnt % 3 == 0:
                p0 = to_px(x0, y0)
                p1 = to_px(x1, y1)
                draw_line(p0[0], p0[1], p1[0], p1[1], layer_cols.get(lyr, (120, 180, 220)), alpha=0.28)

    # Draw the 4 SRAM macros on top so boundaries & inward pin edges are crystal clear
    mw_dbu = int(round(macro_w_um * dbu))
    mh_dbu = int(round(macro_h_um * dbu))
    for idx, (inst, x, y, orient) in enumerate(macros):
        if orient in ("R90", "R270", "MYR90", "MXR90"):
            ux, uy = x + mh_dbu, y + mw_dbu
        else:
            ux, uy = x + mw_dbu, y + mh_dbu
        bx0, by0 = to_px(x, y)
        bx1, by1 = to_px(ux, uy)
        fill_rect(bx0, by1, bx1, by0, (36, 44, 68), alpha=0.92)
        stroke_rect(bx0, by1, bx1, by0, (235, 110, 140), lw=3)
        # Highlight inward-facing pin edge (`R90` -> east edge `bx1`; `R270` -> west edge `bx0`)
        if orient == "R90":
            fill_rect(bx1 - 5, by1 + 6, bx1, by0 - 6, (80, 250, 160))
        elif orient == "R270":
            fill_rect(bx0, by1 + 6, bx0 + 5, by0 - 6, (80, 250, 160))
        else:
            fill_rect(bx0 + 6, by0 - 5, bx1 - 6, by0, (80, 250, 160))
        short = f"SRAM{idx} {orient}"
        draw_text(bx0 + 12, (by0 + by1) // 2 - 7, short, (245, 245, 255), scale=2)

    # IO pins
    pins_sec = re.search(r"\nPINS\s+\d+\s*;(.*?)END PINS", text, re.S)
    if pins_sec:
        for m in re.finditer(r"PLACED\s*\(\s*(\d+)\s+(\d+)\s*\)", pins_sec.group(1)):
            px, py = to_px(int(m.group(1)), int(m.group(2)))
            fill_rect(px - 2, py - 2, px + 2, py + 2, (255, 230, 90))

    hdr = title or f"QSAG-NI ASIC ROUTED BASIN-1 ({die_w/dbu:.0f}X{die_h/dbu:.0f} UM) - CELLS:{std_cnt} CTS:{cts_cnt} SEGS:{seg_cnt}"
    draw_text(PAD, 24, hdr, (235, 242, 255), scale=2)
    draw_text(PAD, H - 42, "GREEN EDGE: INWARD TRACK-SNAPPED M3 PINS   CYAN/GOLD/RED: ROUTED M2-M8   PINK: 4X 128KIB SRAM", (180, 200, 225), scale=2)
    write_png(png_path, W, H, rgb)
    print(f"Rendered {png_path} ({W}x{H}, std_cells={std_cnt}, cts_bufs={cts_cnt}, wire_segs={seg_cnt}, srams={len(macros)})")


if __name__ == "__main__":
    render_def(Path(sys.argv[1]), Path(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4]), sys.argv[5] if len(sys.argv) > 5 else "")
