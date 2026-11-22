"""Draw the DEF component bounding boxes emitted by inspect_def.py."""
import json
import sys
from collections import Counter
from pathlib import Path
from PIL import Image, ImageDraw, ImageFont

data = json.loads(Path(sys.argv[1]).read_text())
units = data['units']
assert units == 2000
xmax, ymax = (v / units for v in data['die'][2:])
is_0p5x1 = ymax > 4000
scale = 0.56 if is_0p5x1 else 0.68
margin, top = 70, 125
im = Image.new('RGB', (round(scale * xmax) + margin * 2, round(scale * ymax) + top + 198), '#f8f7f2')
draw = ImageDraw.Draw(im)
fontdir = Path('/System/Library/Fonts/Supplemental')


def font(size, bold=False):
    return ImageFont.truetype(str(fontdir / ('Arial Bold.ttf' if bold else 'Arial.ttf')), size)


def xy(x, y):
    return (round(margin + x * scale), round(top + (ymax - y) * scale))


def rect(coords, color, outline=None):
    x1, y1, x2, y2 = coords
    draw.rectangle([xy(x1, y2), xy(x2, y1)], fill=color, outline=outline)


def label(pos, text, size, color='#183039', bold=False):
    draw.text(pos, text, font=font(size, bold), fill=color)


def kind(n, m):
    if 'ip_sram' in m:
        return 'SRAM'
    if 'ws_ip' in m:
        return 'Wafer ID / logo'
    if '_fd_io__' in m:
        if '__fill' in m or '__cor' in m:
            return 'Ring corner / filler'
        if '__dv' in m or '__vd' in m or '__vs' in m:
            return 'Supply pad'
        return 'Signal pad'
    if any(v in m for v in ['__fill', '__endcap', '__welltap', '__antenna', '__tie']):
        return 'Tap / filler / tie / diode'
    if any(s in m for s in ['__lat', '__dff', '__sdff']):
        return 'Sequential'
    if '__clk' in m or '__icg' in m:
        return 'Clock cell'
    return 'Logic'


colors = {
    'Logic': '#76bab2',
    'Sequential': '#327c88',
    'Clock cell': '#ecaf48',
    'Tap / filler / tie / diode': '#cadbd3',
    'SRAM': '#b66c38',
    'Signal pad': '#3b536c',
    'Supply pad': '#89577a',
    'Wafer ID / logo': '#92a36d',
    'Ring corner / filler': '#c3cbd0',
}
counts = Counter()
slot_name = 'SLOT_0P5X1' if is_0p5x1 else 'SLOT_0P5X0P5'
chip_title = 'ASS2-0P5X1   /   Placed & Routed Silicon' if is_0p5x1 else 'ASS2-0P5   /   Physical placement'
label((margin, 23), chip_title, 38 if is_0p5x1 else 41, bold=True)
label((margin, 80), f'Dregg-64 Rev. 2.0    ·    GF180MCU-D 5V    ·    {slot_name}', 21)
rect([0, 0, xmax, ymax], '#e5e6df')
core_ymax = 4680 if is_0p5x1 else 2089
rect([442, 442, 1494, core_ymax], '#f8f7f0', '#666f69')
for name, master, orient, *bbox in data['instances']:
    group = kind(name, master)
    coords = [i / units for i in bbox]
    rect(coords, colors[group], '#304449' if group in ['SRAM', 'Supply pad', 'Signal pad', 'Wafer ID / logo'] else None)
    counts[group] += 1
    if group == 'SRAM':
        x, y = xy((coords[0] + coords[2]) / 2, (coords[1] + coords[3]) / 2)
        title = 'SRAM0   /   Data' if 'dsram' in name else 'SRAM1   /   Instruction'
        draw.text((x, y - 9), title, anchor='mm', font=font(20, True), fill='white')
        draw.text((x, y + 19), '512 × 8 (5 V)', anchor='mm', font=font(16), fill='white')
exp_sig = 56 if is_0p5x1 else 48
exp_sup = 16 if is_0p5x1 else 8
assert counts['Signal pad'] == exp_sig and counts['Supply pad'] == exp_sup and counts['Wafer ID / logo'] == 5, counts
base = xy(0, 0)[1] + 20
label((margin, base), f'Die {xmax:,.0f} × {ymax:,.0f} µm    ·    DEF 2,000 DBU/µm    ·    ' + sys.argv[3], 19, bold=True)
for i, (group, color) in enumerate(colors.items()):
    x = margin + (i % 3) * 380
    y = base + 44 + (i // 3) * 35
    draw.rectangle((x, y + 3, x + 18, y + 20), fill=color)
    label((x + 27, y), f'{group}  {counts[group]:,}', 17)
im.save(sys.argv[2])
