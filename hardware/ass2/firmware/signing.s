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
    LD64 R4, [R12+24]
    LD64 R5, [R12+120]
    OR R4, R4, R5
    BEQZ R4, no_key

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

    ; Stage 2: `req_id` over `(hdr_tag[0..1], azm6[0..5])`
    ADDI R5, R13, -16
    CALL sst_s0_s1
    SZERO
    ADDI R4, R13, -16
    CALL sxor_8
    SPUT S[8], R8
    CALL padded_keccak12

    ADDI R4, R13, 104
    MOVZ20 R9, 0x43501
    CALL verify_cap_tok

    SLD64 S[0], [R2+24]
    SLD64 S[1], [R2+32]
    ADDI A0, R13, 0
    MOVZ20 A1, 1
    CALL cth_dualmac
    BEQZ A0, bad_mac

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
    ADDI R5, R2, 0x40
    CALL sst_s0_s3
    ADDI R5, R15, 32
    CALL sst_s0_s3
    ADDI R4, R13, 64
    ADDI R5, R2, 0x60
    CALL copy_or_4

    LD64 R4, [ZERO+@K_P2DOM]
    ST64 [R2+0x80], R4
    LD64 R4, [R13+56]
    BEXTU R5, R4, 0, 4
    ST64 [R2+0x90], R5
    SHRI R4, R4, 32
    ST64 [R2+0x98], R4
    ADDI R7, R14, 0
    MOVZ20 R6, 0

chain_step:
    CMP R1, R7, R6, GTU
    OR R4, R10, R6
    ST64 [R2+0x88], R4
    SZERO
    ADDI R4, R2, 0x40
    CALL sxor_12
    POSEIDON2.GL12
    ADDI R4, R2, 0x40
    CALL sld_e23
    FP5.ADD E0, E0, E2
    ADDI R4, R2, 0x60
    CALL sld_e23
    CALL add_2x_e2
    ADDI R4, R2, 0x80
    CALL sld_e23
    CALL add_4x_e2
    ADDI R5, R2, 0x40
    CALL sst_s0_s3
    ADDI R8, R2, 0x40
    ADDI R9, R15, 32
    MOVZ20 R11, 4
sel_limb:
    LD64 R4, [R9]
    LD64 R5, [R8]
    SEL R4, R4, R5, R1
    ST64 [R9], R4
    ADDI R8, R8, 8
    ADDI R9, R9, 8
    ADDI R11, R11, -1
    BNEZ R11, sel_limb
    ADDI R6, R6, 1
    ADDI R4, R6, -3
    BNEZ R4, chain_step
    ADDI R5, R15, 64
    CALL sst_s0_s3
    SZERO

    CALL read_active_slot
    ADDI R4, R2, 0xb0
    ADDI R5, R2, 0x60
    CALL copy_or_4
    CALL bump_persist_nonce
    J success
