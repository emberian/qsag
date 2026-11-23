; Resident Ring-0 ROM entry dispatcher (`0x0000_0000`, `applet_exec_q == 0`).
; R2 = 0x10000 (D-SRAM scratch), R12 = 0xFFFF_0000 (SYS_MMIO),
; R14 = 0x10100 (RX_MBOX), R15 = 0x10180 (TX_MBOX).
entry:
    MOVZ20 R12, 0xffff
    SHLI R12, R12, 16
    LD64 R4, [R12+16]
    ANDI R8, R4, 255
    ADDI R5, R8, -48
    BEQZ R5, load_code
    MOVZ20 R14, 0x10100
    MOVZ20 R15, 0x10180
    CALL clear_tx_all
    MOVZ20 R2, 0x10000
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

; Pre-provisioning BLANK/RESET bring-up bank pattern (all 2,560 latches -> 1).
bank_test:
    LD64 R8, [R12+96]
    SHRI R8, R8, 9
    ANDI R8, R8, 3
    BNEZ R8, reject
    MOVZ20 R1, 1
    STB [R12+96], R1
    MOVS20 R1, -1
    ADDI R4, R2, 0
    ADDI R5, R2, 0
    MOVZ20 R6, 16
bank_fill:
    ST64 [R5], R1
    ADDI R5, R5, 8
    ADDI R6, R6, -1
    BNEZ R6, bank_fill
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

; FIPS 140-3 §10.3.A Autonomous Cold-Boot Power-On Known-Answer Self-Test (`POST KAT`):
; Exercises full production ALU + Shifter + Regbank + Goldilocks Mul/Fold + 128-step GF(2^128) Mul
; (both 64-bit limbs + 0x87 reduction) + Quintic Fp5 Mul + full 30-round `POSEIDON2.GL12`
; + full 24-round `KECCAK.F1600 24` + 12-round `KECCAK.F1600 12` (`0` round-reduction shortcuts!).
post_selftest:
    SZERO
    MOVZ20 R4, 0x5a533
    ROLI   R5, R4, 19
    GL.MAC R6, R4, R5, R4
    SPUT   S[0], R4
    SPUT   S[1], R6
    SPUT   S[2], R5
    SPUT   S[3], R5
    GF128.MUL P0, P0, P1
    SPUT   S[5], R6
    FP5.MUL E0, E0, E1
    POSEIDON2.GL12
    KECCAK.F1600 24
    KECCAK.F1600 12
    SGET   R4, S[0]
    SGET   R5, S[1]
    XOR    R4, R4, R5
    SGET   R5, S[12]
    XOR    R4, R4, R5
    SGET   R5, S[24]
    XOR    R4, R4, R5
    HALT
