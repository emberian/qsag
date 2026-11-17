"""Minimal DEF/LEF reader for placed (unrouted or routed) designs. Pure Python, no dependencies."""
import re
from collections import defaultdict

ORGANS = [  # (prefix under i_chip_core, organ) - first match wins
    ("u_engine.u_sp", "sponge"),
    ("u_engine.u_kc", "keccak"),
    ("u_engine.u_alu", "gl64_alu"),
    ("u_engine.u_fe", "field_engine"),
    ("u_engine.u_rc", "p2_rc"),
    ("u_engine.u_gf", "gf128"),
    ("u_engine.u_vat", "captp_vat"),
    ("u_engine", "wire_engine"),
    ("u_puf", "ro_puf_bch"),
    ("u_nfc", "nfc_nco"),
    ("u_db", "distance_tdc"),
    ("u_clk.u_shield", "shield"),
    ("u_clk", "gals_clk_rst"),
    ("u_trng", "trng"),
    ("u_anchor", "anchor_spi"),
    ("u_io", "io_shell"),
]
ORGAN_NAMES = [o for _, o in ORGANS] + ["pad", "top", "physical"]
BUF_MASTER = re.compile(r"__(clk)?buf_\d+$")
AUTO_BASENAME = re.compile(
    r"^(_\d+_|fanout\d+|place\d+|wire\d+|rebuffer\d+|split\d+|clkbuf_.*|clkload\d+|hold\d+|"
    r"input\d+|output\d+|max_cap\d+|max_length\d+|load_slew\d+|use\d+|gain\d+|clone\d+)$")


def norm(name):
    return name.replace("\\", "")


def organ_of(inst, master=""):
    if master.startswith("gf180mcu_fd_io") or master.startswith("gf180mcu_ws_ip"):
        return "pad"
    if "__fill" in master or "__endcap" in master:
        return "physical"
    n = inst.replace("/", ".")
    if n.startswith("i_chip_core."):
        n = n[len("i_chip_core."):]
        for pre, org in ORGANS:
            if n == pre or n.startswith(pre + ".") or n.startswith(pre + "_"):
                return org
        return "top"
    return "top"


def basename(inst):
    return re.split(r"[./]", inst)[-1]


def read_lef(paths):
    """-> {macro: {"w":, "h":, "pins": {pin: (direction, use)}}}"""
    macros = {}
    for p in paths:
        cur = pin = None
        with open(p, errors="replace") as f:
            for line in f:
                t = line.split()
                if not t:
                    continue
                if t[0] == "MACRO":
                    cur = {"w": 0.0, "h": 0.0, "pins": {}}
                    macros[t[1]] = cur
                    pin = None
                elif cur is None:
                    continue
                elif t[0] == "SIZE" and pin is None:
                    cur["w"], cur["h"] = float(t[1]), float(t[3])
                elif t[0] == "PIN":
                    pin = t[1]
                    cur["pins"][pin] = ["INPUT", "SIGNAL"]
                elif t[0] == "DIRECTION" and pin:
                    cur["pins"][pin][0] = t[1]
                elif t[0] == "USE" and pin:
                    cur["pins"][pin][1] = t[1]
    return macros


def read_tech_layers(path):
    """-> [(name, direction, pitch_um)] for routing layers in order."""
    out, cur, typ, d, pitch = [], None, None, None, None
    with open(path, errors="replace") as f:
        for line in f:
            t = line.split()
            if not t:
                continue
            if t[0] == "LAYER" and len(t) == 2:
                cur, typ, d, pitch = t[1], None, None, None
            elif cur and t[0] == "TYPE":
                typ = t[1]
            elif cur and t[0] == "DIRECTION":
                d = t[1]
            elif cur and t[0] == "PITCH":
                pitch = float(t[1])
            elif cur and t[0] == "END" and len(t) > 1 and t[1] == cur:
                if typ == "ROUTING" and d:
                    out.append((cur, d[0], pitch))
                cur = None
    return out


class Design:
    pass


def read_def(path, macros):
    d = Design()
    d.comps = {}      # name -> dict(master, x, y, w, h, orient, fixed) (um, lower-left)
    d.nets = {}       # name -> [(inst, pin)]  inst == "PIN" for top ports
    d.die = None
    dbu = 1000.0
    section = None
    buf = []
    with open(path, errors="replace") as f:
        for line in f:
            s = line.strip()
            if not s:
                continue
            if section is None:
                if s.startswith("UNITS DISTANCE MICRONS"):
                    dbu = float(s.split()[3])
                elif s.startswith("DIEAREA"):
                    v = [int(x) for x in re.findall(r"-?\d+", s)]
                    d.die = (v[0] / dbu, v[1] / dbu, v[2] / dbu, v[3] / dbu)
                elif s.startswith("COMPONENTS "):
                    section = "C"
                elif s.startswith("NETS "):
                    section = "N"
                elif s.startswith("SPECIALNETS "):
                    section = "S"
                continue
            if s.startswith("END "):
                section = None
                buf = []
                continue
            if section == "S":
                continue
            buf.append(s)
            if not s.endswith(";"):
                continue
            stmt = " ".join(buf)
            buf = []
            t = stmt.split()
            if t[0] != "-":
                continue
            if section == "C":
                name, master = norm(t[1]), t[2]
                m = macros.get(master, {"w": 0.0, "h": 0.0})
                x = y = 0.0
                orient, fixed, placed = "N", False, False
                for i, tok in enumerate(t):
                    if tok in ("PLACED", "FIXED", "COVER") and t[i + 1] == "(":
                        x, y = int(t[i + 2]) / dbu, int(t[i + 3]) / dbu
                        orient = t[i + 5]
                        fixed = tok != "PLACED"
                        placed = True
                w, h = m["w"], m["h"]
                if orient in ("E", "W", "FE", "FW"):
                    w, h = h, w
                d.comps[name] = dict(master=master, x=x, y=y, w=w, h=h, orient=orient,
                                     fixed=fixed, placed=placed)
            elif section == "N":
                name = norm(t[1])
                pins = []
                i = 2
                while i < len(t):
                    if t[i] == "(":
                        pins.append((norm(t[i + 1]), t[i + 2]))
                        i += 4
                    elif t[i] == "+":
                        break
                    else:
                        i += 1
                d.nets[name] = pins
    d.dbu = dbu
    return d


def pin_xy(d, inst):
    """Approximate pin location: cell centre; for pads, the midpoint of the core-facing edge."""
    c = d.comps[inst]
    cx, cy = c["x"] + c["w"] / 2, c["y"] + c["h"] / 2
    if c["master"].startswith("gf180mcu_fd_io") and d.die:
        x0, y0, x1, y1 = d.die
        dist = {"W": cx - x0, "E": x1 - cx, "S": cy - y0, "N": y1 - cy}
        side = min(dist, key=dist.get)
        if side == "W":
            return c["x"] + c["w"], cy
        if side == "E":
            return c["x"], cy
        if side == "S":
            return cx, c["y"] + c["h"]
        return cx, c["y"]
    return cx, cy


def build_graph(d, macros):
    """Annotate d with organ per instance, driver/sinks per net, and buffer-collapsed logical nets."""
    d.organ = {n: organ_of(n, c["master"]) for n, c in d.comps.items()}
    d.isbuf = {n: bool(BUF_MASTER.search(c["master"])) and bool(AUTO_BASENAME.match(basename(n)))
               for n, c in d.comps.items()}
    d.drv, d.sinks = {}, {}
    inst_in = defaultdict(list)   # inst -> nets on its inputs
    inst_out = defaultdict(list)
    for net, pins in d.nets.items():
        drv, sinks = None, []
        for inst, pin in pins:
            if inst == "PIN":
                continue
            c = d.comps.get(inst)
            if c is None:
                continue
            pd = macros.get(c["master"], {}).get("pins", {}).get(pin, ["INPUT", "SIGNAL"])
            if pd[1] in ("POWER", "GROUND"):
                continue
            if pd[0] == "OUTPUT":
                drv = (inst, pin)
                inst_out[inst].append(net)
            elif pd[0] == "INOUT":
                continue
            else:
                sinks.append((inst, pin))
                inst_in[inst].append(net)
        d.drv[net], d.sinks[net] = drv, sinks
    # union nets through auto-inserted buffers
    parent = {n: n for n in d.nets}

    def find(a):
        while parent[a] != a:
            parent[a] = parent[parent[a]]
            a = parent[a]
        return a

    for inst, isb in d.isbuf.items():
        if isb and inst_in[inst] and inst_out[inst]:
            a, b = find(inst_in[inst][0]), find(inst_out[inst][0])
            if a != b:
                parent[b] = a
    groups = defaultdict(list)
    for n in d.nets:
        groups[find(n)].append(n)
    d.lnets = []
    for members in groups.values():
        root_drv, root_name, sinks, pts, nbuf = None, None, [], [], 0
        for n in members:
            dr = d.drv[n]
            if dr:
                pts.append(pin_xy(d, dr[0]))
                if not d.isbuf[dr[0]]:
                    root_drv, root_name = dr, n
                else:
                    nbuf += 1
            for s in d.sinks[n]:
                pts.append(pin_xy(d, s[0]))
                if not d.isbuf[s[0]]:
                    sinks.append(s)
        if root_name is None:
            root_name = min(members, key=len)
        d.lnets.append(dict(name=root_name, drv=root_drv, sinks=sinks, pts=pts, nbuf=nbuf,
                            members=members))
    # buffers inherit the organ of the root driver
    net2l = {}
    for ln in d.lnets:
        for n in ln["members"]:
            net2l[n] = ln
    for inst, isb in d.isbuf.items():
        if isb and inst_in[inst]:
            ln = net2l[inst_in[inst][0]]
            if ln["drv"]:
                d.organ[inst] = d.organ[ln["drv"][0]]
    # unattributed logic ("top"): owner = majority organ of what it drives, iterated; then of what drives it
    out_l = defaultdict(list)
    in_l = defaultdict(list)
    for ln in d.lnets:
        if ln["drv"]:
            out_l[ln["drv"][0]].append(ln)
        for s in ln["sinks"]:
            in_l[s[0]].append(ln)
    for direction in ("fwd", "back"):
        for _ in range(60):
            changed = 0
            for inst, org in list(d.organ.items()):
                if org != "top" or d.comps[inst]["master"].startswith("gf180mcu_fd_io"):
                    continue
                votes = defaultdict(int)
                if direction == "fwd":
                    for ln in out_l[inst]:
                        for s in ln["sinks"]:
                            o = d.organ[s[0]]
                            if o not in ("top", "pad", "physical"):
                                votes[o] += 1
                else:
                    for ln in in_l[inst]:
                        if ln["drv"]:
                            o = d.organ[ln["drv"][0]]
                            if o not in ("top", "pad", "physical"):
                                votes[o] += 1
                if votes:
                    d.organ[inst] = max(votes, key=votes.get)
                    changed += 1
            if not changed:
                break
    return d


def hpwl(pts):
    if len(pts) < 2:
        return 0.0
    xs = [p[0] for p in pts]
    ys = [p[1] for p in pts]
    return (max(xs) - min(xs)) + (max(ys) - min(ys))
