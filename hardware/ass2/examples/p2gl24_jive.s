; QSAG seven-limb Merkle compression. All inputs are canonical Goldilocks elements.
; A0, A1 -> left and right (56 B each), A2 -> digest (56 B), A3 and A4 = tweak limbs.
; A5 is scratch. All inputs are consumed before the first output store. All S lanes are cleared.
; Feed-forward: perm[i] + left[i] + 2*right[i] + 4*tweak[i] for i < 7, tweak[i>=2] = 0.
p2gl24_jive:
    SZERO
    SLD64   S[0], [A0+0]
    SLD64   S[1], [A0+8]
    SLD64   S[2], [A0+16]
    SLD64   S[3], [A0+24]
    SLD64   S[4], [A0+32]
    SLD64   S[5], [A0+40]
    SLD64   S[6], [A0+48]
    SLD64   S[7], [A1+0]
    SLD64   S[8], [A1+8]
    SLD64   S[9], [A1+16]
    SLD64   S[10], [A1+24]
    SLD64   S[11], [A1+32]
    SLD64   S[12], [A1+40]
    SLD64   S[13], [A1+48]
    SPUT    S[14], A3
    SPUT    S[15], A4
    MOVZ20  A5, 16
    SPUT    S[16], A5
    MOVZ20  A5, 8
    SPUT    S[17], A5
    MOVZ20  A5, 7
    SPUT    S[18], A5
    MOVZ20  A5, 0x4d52          ; Merkle domain 0x4d524b4c474c3234
    SLK16   A5, A5, 0x4b4c
    SLK16   A5, A5, 0x474c
    SLK16   A5, A5, 0x3234
    SPUT    S[19], A5
    MOVZ20  A5, 0x504f          ; permutation domain 0x504f5332474c3234
    SLK16   A5, A5, 0x5332
    SLK16   A5, A5, 0x474c
    SLK16   A5, A5, 0x3234
    SPUT    S[23], A5
    POSEIDON2.GL24              ; 216 architectural cycles
    SLD64   S[10], [A0+0]
    SLD64   S[11], [A0+8]
    SLD64   S[12], [A0+16]
    SLD64   S[13], [A0+24]
    SLD64   S[14], [A0+32]
    SLD64   S[15], [A0+40]
    SLD64   S[16], [A0+48]
    FP5.ADD E0, E0, E2          ; out[0..4] += L[0..4]
    FP5.ADD E1, E1, E3          ; out[5..6] += L[5..6]
    SLD64   S[10], [A1+0]
    SLD64   S[11], [A1+8]
    SLD64   S[12], [A1+16]
    SLD64   S[13], [A1+24]
    SLD64   S[14], [A1+32]
    SLD64   S[15], [A1+40]
    SLD64   S[16], [A1+48]
    FP5.ADD E2, E2, E2          ; double right in the field
    FP5.ADD E3, E3, E3
    FP5.ADD E0, E0, E2          ; out[0..4] += 2*R[0..4]
    FP5.ADD E1, E1, E3          ; out[5..6] += 2*R[5..6]
    GL.ADD  A3, A3, A3
    GL.ADD  A3, A3, A3
    SGET    A5, S[0]
    GL.ADD  A5, A5, A3
    SPUT    S[0], A5
    GL.ADD  A4, A4, A4
    GL.ADD  A4, A4, A4
    SGET    A5, S[1]
    GL.ADD  A5, A5, A4
    SPUT    S[1], A5
    SST64   [A2+0], S[0]
    SST64   [A2+8], S[1]
    SST64   [A2+16], S[2]
    SST64   [A2+24], S[3]
    SST64   [A2+32], S[4]
    SST64   [A2+40], S[5]
    SST64   [A2+48], S[6]
    SZERO                       ; clear all sponge lanes
    RET
