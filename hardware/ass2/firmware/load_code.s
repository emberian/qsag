; Zero-Factory-Trust `0x30 CMD_LOAD_CODE` Authenticator (`I-SRAM` held non-executable while running):
verify_image:
    CALL load_anchor_eid
    ADDI R5, R2, 0
    CALL sst_s0_s3

    SZERO
    ADDI R4, R2, 0
    CALL sxor_4
    SPUT S[5], R8
    MOVZ20 R8, 0x47461
    SPUT S[4], R8
    CALL padded_keccak12
    SGET R4, S[0]
    SGET R5, S[1]

    LD64 R6, [R12+16]
    SHRI R10, R6, 26
    ANDI R10, R10, 3
    SHRI R6, R6, 8
    ANDI R6, R6, 255
    ST64 [R2+0x50], R6
    SZERO
    SPUT S[0], R4
    SPUT S[1], R5
    SPUT S[2], R6
    MOVZ20 R9, 0x1000
image_pair:
    LD64 R7, [R9]
    BEXTU R8, R7, 0, 4
    GF128.MUL P1, P1, P0
    SXOR S[2], R8
    ADDI R6, R6, -1
    BEQZ R6, image_finish
    SHRI R8, R7, 32
    GF128.MUL P1, P1, P0
    SXOR S[2], R8
    ADDI R9, R9, 8
    ADDI R6, R6, -1
    BNEZ R6, image_pair
image_finish:
    SGET R6, S[2]
    SGET R7, S[3]
    ST64 [R2+32], R6
    ST64 [R2+40], R7
    SZERO
    ADDI R4, R2, 0
    CALL sxor_6
    SPUT S[7], R8
    MOVZ20 R8, 0x494d1
    SPUT S[6], R8
    CALL padded_keccak12

    ADDI R8, R10, -2
    BEQZ R8, image_wotsc

    ADDI R4, R14, 0
    MOVZ20 R9, 0x43500
    CALL verify_cap_tok
    J success

image_wotsc:
    ADDI R5, R2, 0x40
    CALL sst_s0_s1
    MOVZ20 R4, 0x30
    CALL verify_wotsc
    CALL bump_persist_nonce
    J success
