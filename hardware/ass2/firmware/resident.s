; Resident ROM entry dispatcher (`0x0000_0000`).
; R2 = 0x10000 (D-SRAM scratch), R12 = 0xFFFF_0000 (SYS_MMIO),
; R14 = 0x10100 (RX_MBOX), R15 = 0x10180 (TX_MBOX).
entry:
    MOVZ20 R14, 0x10100
    MOVZ20 R15, 0x10180
    CALL clear_tx_all
    MOVZ20 R2, 0x10000
    MOVZ20 R12, 0xffff
    SHLI R12, R12, 16
    LD64 R8, [R12+16]
    ANDI R8, R8, 255
    ADDI R5, R8, -48
    BEQZ R5, verify_image
    ADDI R5, R8, -49
    ADDI R13, R14, 0
    BNEZ R5, wire_service
    ADDI R13, R14, 8
    LD64 R7, [R14]
    ANDI R5, R7, 255
    BEQZ R5, ident
    ADDI R5, R5, -1
    BEQZ R5, lifecycle
    ADDI R5, R5, -1
    BEQZ R5, signing
    ADDI R5, R5, -1
    BEQZ R5, canopy
    ADDI R5, R5, -1
    BEQZ R5, field
reject:
    MOVZ20 A0, 13
    HALT
wire_service:
    ADDI R5, R8, -32
    BEQZ R5, signing
    J lifecycle_cmd
ident:
    SHRI R8, R7, 8
    ADDI R8, R8, -1
    BEQZ R8, bank_test
    MOVZ20 R8, 65
    CSRW R8, DBG_OUT
    CSRR R8, ARCH_ID
    CSRR R9, FEATURES
    ST64 [R15], R8
    ST64 [R15+8], R9
success:
    MOVZ20 A0, 1
    HALT
canopy:
    ADDI A0, R14, 8
    ADDI A1, R14, 64
    SHRI A2, R7, 8
    ANDI A2, A2, 1
    SHRI A3, R7, 32
    ADDI A5, R15, 0
    CALL canopy50_node
    J success
field:
    SHRI R8, R7, 8
    ANDI R8, R8, 255
    BNEZ R8, jive
    SLD64 S[5], [R14+8]
    SLD64 S[6], [R14+16]
    SLD64 S[7], [R14+24]
    SLD64 S[8], [R14+32]
    SLD64 S[9], [R14+40]
    SHRI A1, R7, 16
    ANDI A1, A1, 1
    MOVZ20 A0, 0x10130
    BEQZ A1, horner_call
    ADDI A0, A0, 40
horner_call:
    CALL fp5_horner
    ADDI R5, R15, 0
    CALL sst_s0_s4
    J success
jive:
    ADDI R8, R8, -1
    BNEZ R8, reject
    ADDI A0, R14, 8
    ADDI A1, R14, 64
    ADDI A2, R15, 0
    SHRI A3, R7, 16
    LD64 A4, [R14+120]
    CALL p2gl24_jive
    J success

; Pre-provisioning BLANK/RESET bring-up bank pattern (all 2,560 latches -> 1).
bank_test:
    LD64 R8, [R12+96]
    SHRI R8, R8, 9
    ANDI R8, R8, 3
    BNEZ R8, reject
    LD64 R8, [R12+96]
    ORI R8, R8, 1
    ST64 [R12+96], R8
    MOVS20 R1, -1
    ADDI R5, R2, 0
    MOVZ20 R6, 16
bank_fill:
    ST64 [R5], R1
    ADDI R5, R5, 8
    ADDI R6, R6, -1
    BNEZ R6, bank_fill
    ADDI R4, R2, 0
    CALL sxor_16
    SPUT S[16], R1
    SPUT S[17], R1
    SPUT S[18], R1
    SPUT S[19], R1
    SPUT S[20], R1
    SPUT S[21], R1
    SPUT S[22], R1
    SPUT S[23], R1
    SPUT S[24], R1
    MOVS20 R2, -1
    MOVS20 R3, -1
    MOVS20 R4, -1
    MOVS20 R5, -1
    MOVS20 R6, -1
    MOVS20 R7, -1
    MOVS20 R8, -1
    MOVS20 R9, -1
    MOVS20 R10, -1
    MOVS20 R11, -1
    MOVS20 R12, -1
    MOVS20 R13, -1
    MOVS20 R14, -1
    MOVS20 R15, -1
    HALT
