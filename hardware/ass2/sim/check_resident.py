"""Compare pin-level result words with the independent byte/field reference (Zero enclave secrets!)."""
import sys
from ass2_model import P, keccak_f1600, poseidon2_gl12, fp5_mul

def limbs(data):
    return [int.from_bytes(data[i:i+8], "little") for i in range(0, len(data), 8)]

def canopy():
    name = b"QSAG.ZKHEM2.TREE/v1"
    prefix = (bytes([1, 136, 1, 0, 1, 8 * len(name)]) + name).ljust(200, b"\0")
    mid = keccak_f1600(limbs(prefix), 12)
    data = b"\0" + (77).to_bytes(4, "little") + bytes(range(50, 100)) + bytes(range(50))
    block = bytearray((data + b"\x07").ljust(200, b"\0"))
    block[135] = 128
    out = keccak_f1600([a ^ b for a, b in zip(mid, limbs(block))], 12)
    return out[:6] + [out[6] & 65535]

def verify(rows):
    expected = set(["CTH", "CANOPY", "HORNER", "JIVE"])
    for line in rows:
        fields = line.split()
        if not fields or fields[0] not in expected:
            continue
        name = fields[0]
        words = list(map(int, fields[1:]))
        if name == "CANOPY":
            want = canopy()
        elif name == "HORNER":
            v = fp5_mul(list(range(11, 16)), list(range(1, 6)))
            want = [(w + 6 + i) % P for i, w in enumerate(v)]
        elif name == "JIVE":
            want = [1170443848852734659, 833485916214919520, 373819593114229865,
                    2500389336842599945, 2668122737528357675, 15131165148025152836, 573418327208874869]
        else:
            # Public-key verification of WOTS+C base-4 chain element `chain[2]` -> `pk_chain = chain[3]`!
            chain_elem, pk_chain = words[:4], words[4:]
            seed = [9, 10, 11, 12]
            tweak = [0x5153414757535450, 0x100000000010 + 2, 45, 0]
            state = poseidon2_gl12(chain_elem + seed + tweak)
            want = [(state[i] + chain_elem[i] + 2 * seed[i] + 4 * tweak[i]) % P for i in range(4)]
            words = pk_chain
        if words != want:
            raise ValueError(f"{name} expected {want}, got {words}")
        print(f"PASS {name} independent public-key/field oracle, {len(want)} words")
        expected.remove(name)
    if expected:
        raise ValueError(f"missing result: {expected}")

if __name__ == "__main__":
    with open(sys.argv[1]) as rows:
        verify(rows)
