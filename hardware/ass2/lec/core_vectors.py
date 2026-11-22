"""Generate retire-by-retire vectors using the independent lane-3 ISA model."""
from pathlib import Path
import random
from contextlib import redirect_stdout
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "sim"))
import ass2_model as m


def program(seed):
    rng = random.Random(seed)
    p = []
    def set_lanes(values):
        for i, val in enumerate(values):
            p.extend(m.LI64(1, val))
            p.append(m.SPG(1, i, ra=1))
    set_lanes(range(1, 11))
    p.extend([m.GL(4, 1, 0, 1), m.GL(5, 1, 0, 1), m.GL(6, 0, 1, 0)])
    set_lanes([2, 0, 0, 1 << 63])
    p.extend([m.GF128(0, 1, 0, 1), m.GF128(1, 0, 1, 0)])
    set_lanes([*range(1, 15), 100, 200, 16, 8, 7, 0x4D524B4C474C3234,
               0, 0, 0, 0x504F5332474C3234])
    p.append(m.PERM(1))
    for i in range(7):
        p.extend([m.SPG(0, i, rd=2), m.IMM20(3, 0, 1+i+2*(8+i)+(400,800,0,0,0,0,0)[i]),
                  m.GL(1, 4+i, 2, 3)])
    set_lanes([rng.getrandbits(64) for _ in range(25)])
    p.extend([m.PERM(2), m.PERM(1), m.PERM(0, 12), m.PERM(0, 24),
              m.GF128(0, 0, 0, 1), m.GL(4, 0, 0, 4)])
    for a, b, c in [(0, 1, 0), (m.M64, m.M64, m.M64), (m.P, m.P-1, m.P+1)] + [
            tuple(rng.getrandbits(64) for _ in range(3)) for _ in range(12)]:
        p += m.LI64(1,a)+m.LI64(2,b)+m.LI64(3,c)
        p += [m.ALU(4,1,2,7),m.ALU(5,1,2,8),m.GL(0,4,1,2,3),
              m.GL(1,4,1,2),m.GL(2,4,1,2),m.GL(3,4,1)]
    p += [m.SPG(3), m.IMM20(8,0,7168), m.STORE(2,8,1,0), m.LOAD(4,8,1,0),
          m.STORE(3,8,11,1), m.LOAD(5,8,11,1), m.SPG(4,2,ra=8,off8=1),
          m.SPG(5,2,ra=8,off8=3), m.CSRW(3,5), m.CSRR(1,5), m.CSRW(2,4), m.CSRR(4,4),
          m.ZEROIZE,m.HALT]
    return p


def main():
    with redirect_stdout(sys.stderr):
        m.selftest()
    p = program(int(sys.argv[1]))
    machine = m.Ass2([(0,8192)])
    for i, w in enumerate(p):
        machine.mem.write(i*4,4,w)
    print(len(p), *(f"{w:x}" for w in p))
    while not machine.halted:
        step = machine.step()
        assert not step.trapped
        print(*(f"{v:x}" for v in [machine.pc,machine.instret,machine.cycles,
                                     *machine.r,*machine.s]))


if __name__ == "__main__":
    main()
