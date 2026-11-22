"""Create a four-layer DRC fixture using the installed KiCad Python bindings."""

from pathlib import Path
import sys
import pcbnew as pcb


def point(x, y):
    return pcb.VECTOR2I(pcb.FromMM(x), pcb.FromMM(y))


def build(root, directory):
    board = pcb.BOARD()
    board.SetCopperLayerCount(4)
    for ref, name, x in [
        ("U1", "ASS2_0P5_COB56", 20),
        ("L1", "NFC_Planar_40x40mm_4T_1u466H", 65),
    ]:
        fp = pcb.FootprintLoad(str(root / "ass2.pretty"), name)
        fp.SetFPID(pcb.LIB_ID("ass2", name))
        fp.SetReference(ref)
        fp.SetPosition(point(x, 40))
        board.Add(fp)
        # Separate nets even for supply pads sharing a rail in the schematic:
        # this detects accidental adjacent-pad copper bridges in the footprint.
        nets = {}
        for pad in fp.Pads():
            number = pad.GetNumber()
            if number not in nets:
                nets[number] = pcb.NETINFO_ITEM(board, ref + "_" + number)
                board.Add(nets[number])
            pad.SetNet(nets[number])
    edge = pcb.PCB_SHAPE()
    edge.SetShape(pcb.SHAPE_T_RECT)
    edge.SetStart(point(10, 10))
    edge.SetEnd(point(95, 70))
    edge.SetLayer(pcb.Edge_Cuts)
    edge.SetWidth(pcb.FromMM(0.05))
    board.Add(edge)

    def save(name):
        path = directory / name
        pcb.SaveBoard(str(path), board)
        s = path.read_text()
        stackup = (root / "stackup.kicad_sexpr").read_text()
        if s.count("(setup") != 1 or "(stackup" in s:
            raise ValueError("Unexpected initial board stackup")
        path.write_text(s.replace("(setup", "(setup\n" + stackup, 1))

    save("fixture.kicad_pcb")
    for i, layer in enumerate([pcb.In1_Cu, pcb.In2_Cu, pcb.B_Cu]):
        trace = pcb.PCB_TRACK(board)
        trace.SetStart(point(58 + i * 2, 38))
        trace.SetEnd(point(58 + i * 2, 42))
        trace.SetWidth(pcb.FromMM(0.25))
        trace.SetLayer(layer)
        board.Add(trace)
    save("intrusions.kicad_pcb")


if __name__ == "__main__":
    build(Path(sys.argv[1]), Path(sys.argv[2]))
