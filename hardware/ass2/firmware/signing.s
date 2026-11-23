; Zero-Factory-Trust Cut-the-Hash + Base-4 `WOTS+C` Enclave Signing Service (`0x20 CMD_CTH_SIGN`):
signing:
    LD64 R8, [R12+96]
    SHRI R8, R8, 8
    ANDI R8, R8, 7
    ADDI R8, R8, -5
    BNEZ R8, reject
    LD64 R8, [R13]
    LD64 R9, [R13+8]
    OR R8, R8, R9
    BEQZ R8, bad_mac
    LD64 R7, [R13+48]
    LD64 R8, [ZERO+@K_AMASK]
    AND R8, R7, R8
    BNEZ R8, reject
    ADDI R5, R2, 48
    CALL consume_nonce

    CALL load_anchor_eid
    ADDI R5, R2, 8
    CALL sst_s0_s1
    CALL clear_tx_all

    ; Stage 1: `(hdr_tag, r_cth)` over `(meta7[0..6], eid[0..1], record, 0x43541)`
    CALL get_record
    SZERO
    ADDI R4, R13, 48
    CALL sxor_7
    SPUT S[11], R8
    SLD64 S[7], [R2+8]
    SLD64 S[8], [R2+16]
    SPUT S[9], R7
    MOVZ20 R8, 0x43541
    SPUT S[10], R8
    CALL padded_keccak12
    SST64 [R2+24], S[2]
    SST64 [R2+32], S[3]

    ; Stage 2: `req_id` over `(hdr_tag[0..1], azm6[0..5])` + Merkle capability check (`0x43501`)
    ADDI R5, R13, -16
    CALL sst_s0_s1
    SZERO
    ADDI R4, R13, -16
    CALL sxor_8
    SPUT S[8], R8
    CALL padded_keccak12

    SGET R6, S[0]
    SGET R7, S[1]
    SZERO
    MOVZ20 R9, 0x43501
    SPUT S[0], R9
    SPUT S[1], R6
    SPUT S[2], R7
    SLD64 S[3], [R13+104]
    SLD64 S[4], [R13+112]
    MOVZ20 R8, 31
    SPUT S[5], R8
    CALL padded_keccak12
    STB [R12+98], R8
    LD64 R4, [R12+80]
    LD64 R5, [R12+88]
    STB [R12+98], ZERO
    OR R9, R4, R5
    BEQZ R9, bad_mac
    SGET R6, S[0]
    SGET R7, S[1]
    XOR R4, R4, R6
    XOR R5, R5, R7
    OR R4, R4, R5
    BNEZ R4, bad_mac

    ; Constant-time 1-record Cut-the-Hash dual-MAC check `m == r_cth * (a * z)` over GF(2^128)
    SLD64 S[0], [R2+24]
    SLD64 S[1], [R2+32]
    SLD64 S[2], [R13+0]
    SLD64 S[3], [R13+8]
    SLD64 S[4], [R13+16]
    SLD64 S[5], [R13+24]
    SLD64 S[6], [R13+32]
    SLD64 S[7], [R13+40]
    GF128.MUL P2, P1, P2
    GF128.MUL P2, P0, P2
    GF128.XOR P3, P3, P2
    SGET R4, S[6]
    SGET R5, S[7]
    OR R4, R4, R5
    SZERO
    BNEZ R4, bad_mac

    ; Derive enclave-private `chain[0]` directly in sponge (`zero root_secret SRAM spill!`)
    CALL get_record
    LD64 R11, [R13+48]
    ANDI R14, R11, 3
    SHRI R10, R11, 4
    SHLI R10, R10, 4
    ST64 [R13+48], R10
    SZERO
    ADDI R4, R13, 48
    CALL sxor_6
    SPUT S[10], R8
    SLD64 S[6], [R12+80]
    SLD64 S[7], [R12+88]
    SPUT S[8], R7
    MOVZ20 R8, 87
    SPUT S[9], R8
    CALL padded_keccak12

    ADDI R4, R15, 0
    CALL sld_e23
    FP5.ADD E0, E0, E2
    ADDI R4, R13, 64
    ADDI R5, R2, 0x60
    CALL copy_or_4
    ADDI R7, R14, 0
    CALL upd_s17_pub

    LD64 R4, [ZERO+@K_P2DOM]
    ST64 [R2+0x80], R4
    LD64 R4, [R13+56]
    BEXTU R5, R4, 0, 4
    ST64 [R2+0x90], R5
    SHRI R4, R4, 32
    ST64 [R2+0x98], R4

chain_step:
    OR R4, R10, R6
    ST64 [R2+0x88], R4
    SZERO
    ADDI R4, R2, 0x40
    CALL sxor_12
    SPUT S[0], R11
    SPUT S[1], R12
    SPUT S[2], R14
    SPUT S[3], R9
    POSEIDON2.GL12
    SPUT S[10], R11
    SPUT S[11], R12
    SPUT S[12], R14
    SPUT S[13], R9
    SPUT S[14], ZERO
    FP5.ADD E0, E0, E2
    ADDI R4, R2, 0x60
    CALL sld_e23
    CALL add_2x_e2
    ADDI R4, R2, 0x80
    CALL sld_e23
    CALL add_4x_e2
    ADDI R6, R6, 1
    CALL upd_s17_pub
    ADDI R4, R6, -3
    BNEZ R4, chain_step
    ADDI R5, R15, 64
    CALL sst_s0_s3
    SZERO
    MOVZ20 R12, 0xffff
    SHLI R12, R12, 16

    CALL read_active_slot
    ADDI R4, R2, 0xb0
    ADDI R5, R2, 0x60
    CALL copy_or_4
    ST64 [R12+8], ZERO
    ST64 [R12+48], ZERO
    J bump_persist_done

upd_s17_pub:
    CMP R1, R7, R6, EQ
    SGET R11, S[0]
    SGET R12, S[1]
    SGET R14, S[2]
    SGET R9, S[3]
    BEQZ R1, upd_ret
    ADDI R5, R15, 32
    J sst_s0_s3
upd_ret:
    RET
