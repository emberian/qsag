; Compact constant-time 50-byte Canopy TurboSHAKE256 node for Resident I-ROM:
;   Entry: R4=cur, R5=sib, R6=dir, R7=node_idx, R9=out.
canopy50_node:
    ADDI R1, RA, 0
    ADDI R10, R5, 0
    ADDI R14, R6, 0
    MOVZ20 R5, 0x10000
    MOVZ20 R6, 16
    CALL zero_words
    ADDI R5, R10, 0
    ADDI R6, R14, 0
    MOVZ20 R10, 0x10000
    SHLI R11, R7, 8
    ST64 [R10], R11
    MOVZ20 R11, 7
    STB [R10+105], R11
    MOVZ20 R11, 50
canopy_byte_loop:
    LDBU R7, [R4]
    LDBU R8, [R5]
    SEL R12, R7, R8, R6
    SEL R8, R8, R7, R6
    STB [R10+5], R12
    STB [R10+55], R8
    ADDI R4, R4, 1
    ADDI R5, R5, 1
    ADDI R10, R10, 1
    ADDI R11, R11, -1
    BNEZ R11, canopy_byte_loop

    SZERO
    SLD64 S[0], [ZERO+@K_CAN0]
    SLD64 S[1], [ZERO+@K_CAN1]
    SLD64 S[2], [ZERO+@K_CAN2]
    MOVZ20 R8, 0x31
    SPUT S[3], R8
    KECCAK.F1600 12

    MOVZ20 R4, 0x10000
    CALL sxor_16
    CALL padded_keccak12

    ADDI R5, R9, 0
    CALL sst_s0_s5
    SGET R8, S[6]
    ANDI R8, R8, 0xffff
    ST64 [R9+48], R8
    SZERO
    JALR ZERO, R1, 0
