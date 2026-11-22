"""Components and assembly variants. Pin lists below are in package pin order."""

from dataclasses import dataclass
from geometry import SRC, DIE, COIL, padmap

G, V, H = "GND", "V5_CHIP", "HOST_3V3"
FIT, HOST, ASK, AUX = "FIT", "3V3 host", "ASK evaluation", "Aux LDO"
P, I, O, B, W = "passive", "input", "output", "bidirectional", "power_in"
SOT = "Package_TO_SOT_SMD:SOT-23"
SMALL = {"0603": "1608", "0805": "2012", "1206": "3216", "1210": "3225", "2010": "5025"}
rows = padmap(SRC / "slot_0p5x0p5.yaml", SRC / "pad-ring.typ", SRC / "bond-windows.def")


@dataclass
class Part:
    ref: str
    value: str
    model: str
    fp: str
    pins: list
    nets: list
    manufacturer: str
    mpn: str
    population: str
    note: str
    section: str


parts = []


def add(ref, value, model, fp, names, types, nets, maker, mpn, pop=FIT, note=""):
    pins = [(str(i), name, kind) for i, (name, kind) in enumerate(zip(names, types, strict=True), 1)]
    assert len(pins) == len(nets)
    parts.append(Part(ref, value, model, fp, pins, nets, maker, mpn, pop, note, section))


def resistor(ref, val, a, b, pop=FIT, size="0603", note=""):
    code = {
        "1M": "1M",
        "100k": "100K",
        "47k": "47K",
        "10k": "10K",
        "12k": "12K",
        "2.2k": "2K2",
        "1k": "1K",
        "470": "470R",
        "150": "150R",
        "100": "100R",
        "33": "33R",
        "4.7": "4R7",
    }[val]
    power = {"0603": "0.10", "1206": "0.25", "2010": "0.75"}[size]
    add(
        ref,
        val,
        "R",
        f"Resistor_SMD:R_{size}_{SMALL[size]}Metric",
        ["~"] * 2,
        [P] * 2,
        [a, b],
        "Yageo",
        f"RC{size}FR-07{code}L",
        pop,
        f"1%, {power} W. {note}".strip(),
    )


def cap(ref, val, a, b, pop=FIT, note=""):
    # Package, orderable code, and dielectric specification.
    size, maker, mpn, rating = {
        "100n": ("0603", "Murata", "GRM188R71H104KA93D", "X7R 50 V"),
        "4.7u": ("0805", "Murata", "GRM21BR71A475KA73L", "X7R 10 V"),
        "10n": ("0603", "Murata", "GRM188R71H103KA01D", "X7R 50 V"),
        "4.7n": ("0603", "Murata", "GRM188R71H472KA01D", "X7R 50 V"),
        "68p": ("0805", "KYOCERA AVX", "08051A680FAT2A", "C0G 1% 100 V"),
        "12p": ("0805", "KYOCERA AVX", "08051A120FAT2A", "C0G 1% 100 V"),
        "22u": ("1210", "Murata", "GRM32ER71E226KE15L", "X7R 25 V"),
        "2.2u": ("0805", "Murata", "GRM21BR71E225KA73L", "X7R 25 V"),
        "220p": ("0603", "Murata", "GRM1885C1H221JA01D", "C0G 50 V"),
    }[val]
    add(
        ref,
        val,
        "C",
        f"Capacitor_SMD:C_{size}_{SMALL[size]}Metric",
        ["~"] * 2,
        [P] * 2,
        [a, b],
        maker,
        mpn,
        pop,
        rating + ". " + note,
    )


def header(ref, title, nets, rows=1, pop=FIT, keyed=False, note=""):
    count = len(nets) // rows
    fp = f"Connector_PinHeader_2.54mm:PinHeader_{rows}x{count:02}_P2.54mm_Vertical"
    mpn = f"TSW-{count:03}-07-G-" + ("S" if rows == 1 else "D")
    # Samtec terminal strip numbering starts at 101 for one position.
    mpn = mpn.replace(f"-{count:03}-", f"-{100 + count}-")
    maker = "Samtec"
    if keyed:
        fp, maker, mpn = (
            "Connector_IDC:IDC-Header_2x05_P2.54mm_Vertical",
            "Würth Elektronik",
            "61201021621",
        )
    add(
        ref,
        title,
        f"Header_{rows}x{count}",
        fp,
        [str(i) for i in range(1, len(nets) + 1)],
        [P] * len(nets),
        nets,
        maker,
        mpn,
        pop,
        note,
    )


def fet(ref, gate, drain, pop):
    add(
        ref,
        "FDV301N",
        "FDV301N",
        SOT,
        ["G", "S", "D"],
        [I, P, "open_collector"],
        [gate, G, drain],
        "onsemi",
        "FDV301N",
        pop,
    )


def diode(ref, anode, cathode, pop=FIT):
    add(
        ref,
        "BAS70",
        "BAS70",
        SOT,
        ["A", "NC", "K"],
        [P, "no_connect", P],
        [anode, None, cathode],
        "Nexperia",
        "BAS70,215",
        pop,
    )


section = "Die and local power"
sigs = []
kinds = []
nets = []
inputs = {1, 2, 25, 35, 36, 40, 41, 42, 44, 45, 47, 50, 51, 52, 55, 56}
for n, side, idx, slot, sig, x, y in rows:
    typ = B if sig.startswith(("GPIO", "HOST_DQ")) else I if n in inputs else O
    net = sig
    if sig in ("VDD", "DVDD", "VSS", "DVSS"):
        typ, net = W, (G if "SS" in sig else V)
    if sig == "n/c":
        sig, typ, net = f"AN{slot[7]}_NC", "no_connect", None
    sigs.append(sig)
    kinds.append(typ)
    nets.append(net)
add(
    "U1",
    "ASS2-0P5",
    "ASS2_0P5",
    f"ass2:{DIE}",
    sigs + ["EP"],
    kinds + [W],
    nets + [G],
    "Project silicon",
    "ASS2-0P5",
    note="COB bare die, top view; two bonds each at 3 and 4",
)
parts[-1].pins[-1] = ("EP", "EP", W)
for i, pair in enumerate(("3/4", "20/21", "31/32", "53/54"), 1):
    cap(f"CP{i}", "100n", V, G, note="U1 pad pair " + pair + "; local GND via")
header("J1", "Bench 5 V", ["BENCH_5V", G])
header("JP1", "Measure current", ["V5_FEED", V], note="Normally shunted; remove to insert ammeter")
header(
    "JP2",
    "Supply select",
    ["BENCH_5V", "V5_FEED", "LDO_5V"],
    note="One shunt. Default 1-2 bench; 2-3 auxiliary LDO",
)
cap("CB1", "4.7u", V, G)
section = "Auxiliary regulator"
header("J8", "Aux 7 V", ["VIN_AUX", G], pop=AUX)
add(
    "U6",
    "ADM7150ARDZ-5.0",
    "ADM7150",
    "Package_SO:SOIC-8-1EP_3.9x4.9mm_P1.27mm_EP2.41x3.3mm",
    ["VREG", "VOUT", "BYP", "GND", "REF_SENSE", "REF", "EN", "VIN", "EP"],
    [O, "power_out", P, W, I, O, I, W, W],
    ["VREG", "LDO_5V", "BYP", G, "LDO_REF", "LDO_REF", "VIN_AUX", "VIN_AUX", G],
    "Analog Devices",
    "ADM7150ARDZ-5.0",
    AUX,
)
for i, (rail, val) in enumerate(
    [("VIN_AUX", "22u"), ("LDO_5V", "22u"), ("VREG", "22u"), ("LDO_REF", "2.2u"), ("BYP", "2.2u")], 1
):
    cap(f"CL{i}", val, rail, G, AUX)
section = "Reset, tamper and straps"
add(
    "U2",
    "TPS3839K50",
    "TPS3839K50",
    SOT,
    ["GND", "RESET_N", "VDD"],
    [W, O, W],
    [G, "POR_N", V],
    "Texas Instruments",
    "TPS3839K50DBZR",
)
cap("CA1", "100n", V, G, note="At U2")
resistor("RRST1", "100", "POR_N", "RST_N")
resistor("RPD1", "100k", "RST_N", G)
resistor("RT1", "10k", V, "TAMPER_ZEROIZE_N")
cap("CT4", "10n", "TAMPER_ZEROIZE_N", G)
resistor("RS1", "1k", "TAMPER_ZEROIZE_N", "CONTACT")
header("J5", "Tamper contact", ["CONTACT", G], note="Normally open external contact")
header("J6", "5 V clock", ["CLK_IN", G])
for i, (sig, default) in enumerate(
    [("CLK_IN", G), ("CLK_EXT_EN", V), ("BOOT_MODE0", G), ("BOOT_MODE1", G)], 1
):
    resistor(f"RSTR{i}", "10k", sig, default)
    if i > 1:
        header(f"JP{i + 1}", sig, [V, sig, G], note="Select 1-2 high or 2-3 low; default by pull")
section = "Private FRAM"
add(
    "U3",
    "FM25W256-G",
    "FM25W256",
    "Package_SO:SOIC-8_3.9x4.9mm_P1.27mm",
    ["CS_N", "SO", "WP_N", "VSS", "SI", "SCK", "HOLD_N", "VDD"],
    [I, "tri_state", I, W, I, I, I, W],
    ["FRAM_CS_N", "FRAM_MISO", V, G, "FRAM_MOSI", "FRAM_SCK", V, V],
    "Infineon",
    "FM25W256-G",
)
cap("CA2", "100n", V, G, note="At U3")
for i, (net, rail) in enumerate(
    [("FRAM_CS_N", V), ("FRAM_MISO", G), ("FRAM_MOSI", G), ("FRAM_SCK", G)], 1
):
    resistor(f"RF{i}", "10k" if i == 1 else "100k", net, rail)
header("J4", "Anchor probes", ["FRAM_CS_N", G, "FRAM_SCK", G, "FRAM_MOSI", G, "FRAM_MISO", G], 2)
section = "Host and expansion"
dq = [f"DQ{i}_BUS" for i in range(8)]
for i, net in enumerate(dq):
    resistor(f"RDQ{i + 1}", "33", f"HOST_DQ{i}", net)
resistor("RSCK1", "33", "SCK_BUS", "HOST_SCK")
resistor("RCS1", "10k", "HOST_CS_N", V)
resistor("RSCK2", "47k", "SCK_BUS", G)
header("J2", "SPI / 5 V", ["SCK_BUS", G, dq[0], G, dq[1], G, "HOST_CS_N", "RST_N", V, G], 2, keyed=True)
exp = (
    dq[2:]
    + ["HOST_RDY", "HOST_IRQ", "DBG_UART_TX", "DBG_UART_RX"]
    + [f"GPIO{i}" for i in range(8)]
    + [
        "VERIFY_OK",
        "FAULT",
        "JTAG_TCK",
        "JTAG_TMS",
        "JTAG_TDI",
        "JTAG_TDO",
        "NFC_CLK_IN",
        "NFC_ASK_IN",
        "NFC_LOAD_MOD",
        "CLK_MON",
        G,
        G,
    ]
)
header("J3", "Expansion / 5 V", exp, 2)
for i, name in enumerate(["JTAG_TCK", "JTAG_TMS", "JTAG_TDI", "DBG_UART_RX", "DB_CHAL_IN"], 1):
    resistor(f"RID{i}", "100k", name, V if name == "DBG_UART_RX" else G)
for i, name in enumerate(("DB_CHAL_IN", "DB_RESP_OUT"), 1):
    add(
        f"JRF{i}",
        name,
        "Coax",
        "Connector_Coaxial:SMA_Amphenol_132289_EdgeMount",
        ["CENTRE", "SHIELD"],
        [P, P],
        [name, G],
        "Amphenol RF",
        "132289",
    )
section = "3.3 V host option"
a = [f"H_DQ{i}" for i in range(8)]


def xlate(ref, dirnet, enable, aport, bport):
    names = (
        ["VCCA", "DIR"]
        + [f"A{i}" for i in range(1, 9)]
        + ["GND"] * 3
        + [f"B{i}" for i in range(8, 0, -1)]
        + ["OE_N", "VCCB", "VCCB"]
    )
    add(
        ref,
        "SN74LXC8T245PWR",
        "SN74LXC8T245",
        "Package_SO:TSSOP-24_4.4x7.8mm_P0.65mm",
        names,
        [W, I] + [B] * 8 + [W] * 3 + [B] * 8 + [I, W, W],
        [H, dirnet] + aport + [G] * 3 + bport[::-1] + [enable, V, V],
        "Texas Instruments",
        "SN74LXC8T245PWR",
        HOST,
    )


xlate("U4", "DQ_DIR", "DATA_OE_N", a, dq)
xlate(
    "U5",
    H,
    "CTRL_OE_N",
    ["H_SCK", "H_CS_N", "H_MOSI"] + ["CTRL_UNUSED"] * 5,
    ["SCK_BUS", "HOST_CS_N", "MOSI_5V"] + [None] * 5,
)
resistor("RH15", "10k", "CTRL_UNUSED", G, HOST)
header(
    "JP6",
    "x1 MOSI link",
    ["MOSI_5V", dq[0]],
    pop=HOST,
    note="Close for x1 only. Open before wide bus turnaround",
)
header(
    "J9",
    "Host / 3.3 V",
    [H, G, "H_SCK", "H_CS_N", "H_MOSI", G] + a + ["DQ_DIR", "DATA_OE_N", "CTRL_OE_N", G],
    2,
    pop=HOST,
)
for i, (name, rail) in enumerate(
    [("DQ_DIR", G), ("DATA_OE_N", H), ("CTRL_OE_N", H), ("H_SCK", G), ("H_CS_N", H), ("H_MOSI", G)]
    + [(net, G) for net in a],
    1,
):
    resistor(f"RH{i}", "47k", name, rail, HOST)
for i, n in enumerate(dq, 1):
    resistor(f"RBI{i}", "100k", n, G)
for i, net in enumerate([H, V, H, V], 1):
    cap(f"CH{i}", "100n", net, G, HOST, note="At " + ("U4" if i <= 2 else "U5"))
section = "NFC tank and cold tap"
add(
    "L1",
    "1.4662 uH",
    "Printed_coil",
    f"ass2:{COIL}",
    ["OUTER", "INNER"],
    [P, P],
    ["COIL_OUT", G],
    "PCB copper",
    "PRINTED",
    note="35 um top copper; B.Cu inner return",
)
resistor("RD1", "4.7", "COIL_OUT", "TANK")
resistor("RB1", "12k", "TANK", G)
cap("CT1", "68p", "TANK", G)
cap("CT2", "12p", "TANK", G)
add(
    "CT3",
    "3-15 pF",
    "Trimmer",
    "Capacitor_SMD:C_Trimmer_Voltronics_JR",
    ["RF", "RETURN"],
    [P, P],
    ["TANK", G],
    "Knowles Voltronics",
    "JR150",
    note="100 V; set near 8.9 pF, tune populated board",
)
resistor("RR1", "150", "TANK", "RECT_IN", size="2010")
diode("D1", "RECT_IN", "RECT")
diode("D2", G, "RECT_IN")
add(
    "DZ1",
    "BZT52C4V7",
    "Zener",
    "Diode_SMD:D_SOD-123",
    ["K", "A"],
    [P, P],
    ["RECT", G],
    "Diodes Incorporated",
    "BZT52C4V7-7-F",
)
cap("CR1", "4.7n", "RECT", G)
resistor("RRECT1", "10k", "RECT", G)
resistor("RG1", "2.2k", "TANK", "RF_GATE", size="1206")
diode("D3", "RF_GATE", "RECT")
diode("D4", G, "RF_GATE")
resistor("RGS1", "1M", "RF_GATE", G)
fet("Q1", "RF_GATE", "NFC_CLK_IN", FIT)
resistor("RP1", "470", V, "NFC_CLK_IN")
section = "ASK evaluation"
# Separate RF-powered envelope/comparator; Q2 provides the only interface to U1.
resistor("RE1", "2.2k", "TANK", "ENV_IN", ASK, size="1206")
diode("D5", "ENV_IN", "ENV_HI", ASK)
diode("D6", "ENV_FILT", "RECT", ASK)
resistor("RE2", "10k", "ENV_HI", "ENV_FILT", ASK)
resistor("RE4", "10k", "ENV_FILT", G, ASK)
cap("CE1", "220p", "ENV_FILT", G, ASK)
resistor("RE5", "47k", "ENV_FILT", "ASK_REF", ASK)
resistor("RE6", "1M", "ASK_REF", G, ASK)
cap("CE2", "10n", "ASK_REF", G, ASK)
add(
    "U7",
    "TLV3201",
    "TLV3201",
    "Package_TO_SOT_SMD:SOT-23-5",
    ["OUT", "GND", "IN+", "IN-", "VCC"],
    [O, W, I, I, W],
    ["ASK_GATE", G, "ENV_FILT", "ASK_REF", "RECT"],
    "Texas Instruments",
    "TLV3201AIDBVR",
    ASK,
)
cap("CE3", "100n", "RECT", G, ASK)
resistor("RGS2", "1M", "ASK_GATE", G, ASK)
fet("Q2", "ASK_GATE", "ASK_OD", ASK)
header(
    "JP7", "ASK enable", ["ASK_OD", "NFC_ASK_IN"], pop=ASK, note="Leave open during first carrier test"
)
resistor("RP2", "10k", V, "NFC_ASK_IN", note="Defined idle high with ASK option absent")
section = "Probe lands"
for i, n in enumerate(
    [
        "BENCH_5V",
        "V5_FEED",
        V,
        "RST_N",
        "TAMPER_ZEROIZE_N",
        "CLK_MON",
        "HOST_SCK",
        "HOST_CS_N",
        "HOST_DQ0",
        "HOST_DQ1",
        "HOST_RDY",
        "HOST_IRQ",
        "TANK",
        "RECT",
        "NFC_CLK_IN",
        "NFC_ASK_IN",
        "FRAM_CS_N",
        "FRAM_SCK",
        "FRAM_MOSI",
        "FRAM_MISO",
    ]
    + [G] * 4,
    1,
):
    add(
        f"TP{i}",
        n,
        "Probe",
        "TestPoint:TestPoint_Pad_D1.0mm",
        ["TP"],
        [P],
        [n],
        "PCB copper",
        "PRINTED",
        note=("At supply pair " + str(i - 20) if i > 20 else ""),
    )
