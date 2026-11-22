; QSAG seven-limb Merkle compression (`POSEIDON2.GL24` Jive):
p2gl24_jive:
    ADDI    R1, RA, 0
    ADDI    R10, A0, 0
    ADDI    R11, A4, 0
    SZERO
    CALL    sxor_14
    SPUT    S[14], A3
    SPUT    S[15], R11
    MOVZ20  A5, 16
    SPUT    S[16], A5
    MOVZ20  A5, 8
    SPUT    S[17], A5
    MOVZ20  A5, 7
    SPUT    S[18], A5
    SLD64   S[19], [ZERO+@K_JMRKL]
    SLD64   S[23], [ZERO+@K_JPERM]
    POSEIDON2.GL24
    ADDI    R4, R10, 0
    CALL    sld_e23
    FP5.ADD E0, E0, E2
    FP5.ADD E1, E1, E3
    ADDI    R4, A1, 0
    CALL    sld_e23
    CALL    add_2x_e2
    FP5.ADD E3, E3, E3
    FP5.ADD E1, E1, E3
    SPUT    S[10], A3
    SPUT    S[11], R11
    SPUT    S[12], ZERO
    SPUT    S[13], ZERO
    SPUT    S[14], ZERO
    CALL    add_4x_e2
    ADDI    R5, A2, 0
    CALL    sst_s0_s6
    SZERO
    JALR    ZERO, R1, 0
