import random, sys
words, width, mode = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
random.seed(20261116)
aw = (words - 1).bit_length()
print("`default_nettype none")
print(f"module px_rom (input wire [{aw-1}:0] a, output logic [{width-1}:0] d);")
print("  always_comb case (a)")
prev = 0
for i in range(words):
    if mode == "rand":
        v = random.getrandbits(width)
    else:
        # "ucode": sparse control fields: an op field from a small alphabet, two 7-bit row fields that mostly
        # step by small amounts, a next-address field that is mostly +1, a few flag bits mostly zero.
        op = random.choice([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19])
        ra = (prev + random.choice([0,1,1,1,2,5])) % 96; prev = ra
        rb = random.choice([ra, (ra + 1) % 96, random.randrange(96)])
        flags = sum((1 << k) for k in range(max(0, width - 5 - 7 - 7)) if random.random() < 0.12)
        v = (op | (ra << 5) | (rb << 12) | (flags << 19)) & ((1 << width) - 1)
    print(f"    {aw}'d{i}: d = {width}'h{v:x};")
print(f"    default: d = '0;")
print("  endcase")
print("endmodule")
print("`default_nettype wire")
