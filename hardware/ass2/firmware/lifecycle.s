; Zero-Factory-Trust Post-Quantum Owner Authority & Dual-Slot Lifecycle (`ASS2-0P5` Rev. 2.0):
;   Uses ONLY explicit R0..R15 registers (`R3 == RA`!).
;   R2 = 0x10000, R12 = 0xFFFF_0000, R14 = 0x10100, R15 = 0x10180.
lifecycle:
    SHRI R8, R7, 8
    ANDI R8, R8, 255
lifecycle_cmd:
    LD64 R6, [R12+96]
    SHRI R6, R6, 8
    ANDI R6, R6, 7
    ADDI R5, R8, -16
    BEQZ R5, boot
    ADDI R5, R8, -17
    BEQZ R5, enrol
    ADDI R5, R8, -18
    BEQZ R5, commit
    ADDI R5, R8, -21
    BEQZ R5, lease
    ADDI R5, R8, -22
    BEQZ R5, gate
    J reject

; ---- 0x10 CMD_BOOT (LC_RESET -> LC_BLANK or LC_LEASE_PENDING) ----
boot:
    BNEZ R6, reject
    MOVZ20 R4, 0
    ADDI R5, R2, 0
    MOVZ20 R6, 128
    CALL fram_read
    LD64 R5, [R2]
    LD64 R6, [R2+64]
    MOVZ20 R7, 0x4a4e2
    CMP R8, R5, R7, EQ
    CMP R9, R6, R7, EQ
    OR R8, R8, R9
    BNEZ R8, reconstruct
    AND R5, R5, R6
    ADDI R5, R5, 1
    BNEZ R5, anchor_error
    MOVZ20 R4, 256
set_lc_ok:
    ST64 [R12+96], R4
    J success

reconstruct:
    CALL prep_anchor_args
    CALL fram_read
    MOVZ20 R10, 8
    CALL measure_puf
    CALL verify_anchor_eid
    CALL clear_tx_all
    ADDI R5, R15, 32
    CALL sst_s0_s3
    MOVZ20 R10, 0
    ADDI R5, R2, 0
    CALL inspect_slot
    ADDI R5, R2, 64
    CALL inspect_slot
    BEQZ R10, anchor_error
    ST64 [R12+56], R10
    ST64 [R15+16], R10
    CALL nonce
    MOVZ20 R4, 768
    J set_lc_ok

inspect_slot:
    ST64 [R2+240], RA
    LD64 R8, [R5]
    MOVZ20 R9, 0x4a4e2
    XOR R8, R8, R9
    BNEZ R8, slot_ret
    ADDI R11, R5, 0
    CALL journal_mac_calc
    ADDI R5, R2, 224
    CALL sst_s0_s1
    ADDI R4, R2, 224
    ADDI R5, R11, 48
    CALL xor_diff_2
    BNEZ R7, anchor_error
    LD64 R7, [R11+8]
    CMP R8, R7, R10, GTU
    SEL R10, R10, R7, R8
slot_ret:
    LD64 RA, [R2+240]
    RET

; Read & MAC-verify active FRAM journal slot `(gen & 1) << 6` into `[R2+0xa0..0xdf]`, returning `R10 = slot.record`.
read_active_slot:
    ST64 [R2+248], RA
    CALL get_record
    SHRI R4, R7, 32
    ANDI R4, R4, 1
    SHLI R4, R4, 6
    ADDI R5, R2, 0xa0
    MOVZ20 R6, 64
    CALL fram_read
    MOVZ20 R10, 0
    ADDI R5, R2, 0xa0
    CALL inspect_slot
    BEQZ R10, anchor_error
    LD64 RA, [R2+248]
    RET

; ---- 0x11 CMD_ENROL (LC_BLANK: bind Owner `pk_0`, seal helpers, return `enclave_id`) ----
enrol:
    ADDI R6, R6, -1
    BNEZ R6, reject
    ST64 [R12+24], ZERO
    ST64 [R12+120], ZERO
    ADDI R4, R14, 0
    ADDI R5, R15, 64
    CALL copy_or_4
    BEQZ R7, keyset_error
    MOVZ20 R10, 0
    CALL measure_puf
    ADDI R5, R15, 0
    CALL seal_hash_calc
    ADDI R5, R15, 96
    CALL sst_s0_s1
    CALL prep_anchor_args
    CALL fram_write
    CALL load_anchor_eid
    CALL clear_tx_all
    ADDI R5, R15, 16
    CALL sst_s0_s3
    CALL nonce
    J success

; ---- 0x12 CMD_COMMIT (LC_BLANK -> LC_PROVISIONED via PQ `WOTS+C`) ----
commit:
    ADDI R6, R6, -1
    BNEZ R6, reject
    MOVZ20 R4, 0x12
    ST64 [R2+0x50], ZERO
    CALL verify_wotsc
    MOVZ20 R7, 1
    SHLI R7, R7, 32
    CALL persist_journal
    MOVZ20 R4, 512
    J set_lc_ok

; ---- 0x15 CMD_LEASE (LC_LEASE_PENDING -> LC_READY via PQ `WOTS+C`) ----
lease:
    ADDI R6, R6, -3
    BNEZ R6, reject
    CALL get_record
    LD64 R5, [R2+0x50]
    XOR R5, R5, R7
    BNEZ R5, rollback_error
    MOVZ20 R4, 0x15
    CALL verify_wotsc
    CALL bump_persist_nonce
    MOVZ20 R4, 1280
    J set_lc_ok

; ---- 0x16 CMD_GATE (LC_READY state transition via PQ `WOTS+C`) ----
gate:
    ADDI R6, R6, -5
    BNEZ R6, reject
    MOVZ20 R4, 0x16
    CALL verify_wotsc
    CALL get_record
    LD64 R9, [R2+0x50]
    SHRI R5, R9, 32
    BEXTU R4, R7, 0, 4
    XOR R4, R4, R5
    BNEZ R4, reject
    CALL bump_gen
    SHRI R7, R7, 32
    SHLI R7, R7, 32
    BEXTU R9, R9, 0, 4
    OR R7, R7, R9
    CALL persist_journal
    J success

bump_persist_nonce:
    ST64 [R2+0x88], RA
    CALL get_record
    CALL bump_gen
    J persist_body

bump_gen:
    MOVZ20 R4, 1
    SHLI R4, R4, 32
    ADD R7, R7, R4
    SHRI R5, R7, 32
    BEQZ R5, reject
    RET

; Measure/reconstruct 4 disjoint `BCH(63,36,5)` blocks (`R10 = 0` enrol, `8` recon); helpers at `[R15+0..63]`.
measure_puf:
    ST64 [R2+248], RA
    ADDI R4, R15, 0
    ADDI R5, R2, 128
    MOVZ20 R6, 0
measure_blk:
    BEQZ R10, puf_go
    LD64 R8, [R4]
    ST64 [R12+32], R8
    LD64 R8, [R4+8]
    ST64 [R12+40], R8
puf_go:
    OR R8, R6, R10
    ORI R8, R8, 256
    ST64 [R12+16], R8
puf_wait:
    LD64 R7, [R12+56]
    ANDI R8, R7, 2
    BEQZ R8, puf_wait
    ANDI R8, R7, 4
    BNEZ R8, puf_error
    LD64 R8, [R12+48]
    ST64 [R5], R8
    BNEZ R10, puf_next
    LD64 R8, [R12+32]
    ST64 [R4], R8
    LD64 R8, [R12+40]
    ST64 [R4+8], R8
puf_next:
    ADDI R4, R4, 16
    ADDI R5, R5, 8
    ADDI R6, R6, 1
    ADDI R8, R6, -4
    BNEZ R8, measure_blk
    SZERO
    ADDI R4, R2, 128
    CALL sxor_4
    SPUT S[5], R8
    ADDI R5, R2, 128
    MOVZ20 R6, 4
    CALL zero_words
    MOVZ20 R8, 0x5254
    SPUT S[4], R8
    CALL padded_keccak12
    SST64 [R12+80], S[0]
    SST64 [R12+88], S[1]
    SZERO
    LD64 RA, [R2+248]
    RET

; Verify 16-chain base-256 `WOTS+C` (`sum == 2040`) Owner capability proof (`R4 = opcode`, `[R2+0x50] = op_value`).
verify_wotsc:
    ST64 [R15+112], RA
    ST64 [R15+120], R4
    LD64 R4, [R12+24]
    LD64 R5, [R12+120]
    ST64 [R2+48], R4
    ST64 [R2+56], R5
    OR R4, R4, R5
    BEQZ R4, no_key
    ADDI R4, R2, 0x60
    ADDI R5, R2, 0x60
    CALL copy_or_4
    BEQZ R7, keyset_error

    CALL load_anchor_eid
    ADDI R5, R2, 8
    CALL sst_s0_s3
    MOVZ20 R8, 0x574d1
    ST64 [R2+0], R8
    LD64 R8, [R15+120]
    ST64 [R2+32], R8
    CALL get_record
    ST64 [R2+40], R7
    SZERO
    ADDI R4, R2, 0
    CALL sxor_16
    CALL turbo_perm12
    ADDI R5, R2, 0
    CALL sst_s0_s1
    LD64 RA, [R15+112]
    ST64 [R2+56], RA
    LD64 R8, [R15+120]
    ST64 [R2+48], R8
    ST64 [R12+24], ZERO
    ST64 [R12+120], ZERO

    MOVZ20 R10, 0
    MOVZ20 R11, 0
    ADDI R13, R2, 0x80
    MOVZ20 R7, 0x57531
wots_chain_loop:
    ADD R4, R2, R10
    LDBU R6, [R4]
    ADD R11, R11, R6
    LD64 R8, [R13]
    LD64 R9, [R13+8]
wots_step_loop:
    ADDI R4, R6, -255
    BEQZ R4, wots_chain_done
    SZERO
    SPUT S[0], R7
    SPUT S[1], R8
    SPUT S[2], R9
    SHLI R4, R10, 8
    OR R4, R4, R6
    SPUT S[3], R4
    MOVZ20 R4, 31
    SPUT S[4], R4
    CALL padded_keccak12
    SGET R8, S[0]
    SGET R9, S[1]
    ADDI R6, R6, 1
    J wots_step_loop
wots_chain_done:
    ST64 [R13], R8
    ST64 [R13+8], R9
    ADDI R13, R13, 16
    ADDI R10, R10, 1
    ADDI R4, R10, -16
    BNEZ R4, wots_chain_loop

    ADDI R4, R11, -2040
    BNEZ R4, bad_mac

    SZERO
    ADDI R4, R2, 0x80
    CALL sxor_16
    SLD64 S[16], [R2+0x100]
    KECCAK.F1600 12
    ADDI R4, R2, 0x108
    CALL sxor_15
    MOVZ20 R8, 0x57501
    SXOR S[15], R8
    CALL turbo_perm12
    ADDI R5, R2, 0x80
    CALL sst_s0_s3

    LD64 R8, [R2+48]
    ADDI R8, R8, -18
    BNEZ R8, wots_chk_journal
    ADDI R5, R15, 64
    J wots_cmp_pk
wots_chk_journal:
    CALL read_active_slot
    ADDI R5, R2, 0xb0
wots_cmp_pk:
    ADDI R4, R2, 0x80
    CALL xor_diff_4
    BNEZ R7, bad_mac
    CALL clear_tx_all
    LD64 R8, [R2+48]
    ADDI R8, R8, -48
    BEQZ R8, wots_ret
    LD64 R8, [R2+0x40]
    ST64 [R12+8], R8
    LD64 R8, [R2+0x48]
    ST64 [R12+48], R8
wots_ret:
    LD64 RA, [R2+56]
    RET

persist_journal:
    ST64 [R2+0x88], RA
persist_body:
    ST64 [R2+8], R7
    ADDI R4, R2, 0x60
    ADDI R5, R2, 16
    CALL copy_or_4
    ADDI R5, R2, 0
    CALL journal_mac_calc
    ADDI R5, R2, 48
    CALL sst_s0_s1
    LD64 R7, [R2+8]
    SHRI R6, R7, 32
    ANDI R6, R6, 1
    SHLI R6, R6, 6
    ST64 [R2+0xf8], R6
    ST64 [R2], ZERO
    ADDI R4, R6, 0
    ADDI R5, R2, 0
    MOVZ20 R6, 64
    CALL fram_write
    MOVZ20 R8, 0x4a4e2
    ST64 [R2], R8
    LD64 R4, [R2+0xf8]
    ADDI R5, R2, 0
    MOVZ20 R6, 8
    CALL fram_write
    LD64 R7, [R2+8]
    ST64 [R12+56], R7
    ST64 [R15+16], R7
    CALL read_active_slot
    LD64 R7, [R2+8]
    XOR R7, R7, R10
    BNEZ R7, anchor_error
    CALL nonce
    LD64 RA, [R2+0x88]
    RET

prep_anchor_args:
    MOVZ20 R4, 256
    ADDI R5, R15, 0
    MOVZ20 R6, 112
    RET

load_anchor_eid:
    ADDI R1, RA, 0
    CALL prep_anchor_args
    CALL fram_read
    J verify_anchor_body
verify_anchor_eid:
    ADDI R1, RA, 0
verify_anchor_body:
    ADDI R5, R15, 0
    CALL check_anchor_seal
    ADDI R5, R15, 64
    CALL compute_enclave_id
    JALR ZERO, R1, 0

check_anchor_seal:
    ADDI R11, RA, 0
    ADDI R9, R5, 0
    CALL seal_hash_calc
    SGET R8, S[0]
    LD64 R7, [R9+96]
    XOR R8, R8, R7
    SGET R7, S[1]
    LD64 R4, [R9+104]
    XOR R7, R7, R4
    OR R8, R8, R7
    BNEZ R8, anchor_error
    JALR ZERO, R11, 0

seal_hash_calc:
    ADDI R10, RA, 0
    SZERO
    ADDI R4, R5, 0
    CALL sxor_12
    SPUT S[15], R8
    SLD64 S[12], [R12+80]
    SLD64 S[13], [R12+88]
    MOVZ20 R8, 0x534c
    SPUT S[14], R8
    CALL padded_keccak12
    JALR ZERO, R10, 0

journal_mac_calc:
    ADDI R9, RA, 0
    SZERO
    ADDI R4, R5, 8
    CALL sxor_5
    SPUT S[8], R8
    SLD64 S[5], [R12+80]
    SLD64 S[6], [R12+88]
    MOVZ20 R8, 0x4a4d
    SPUT S[7], R8
    CALL padded_keccak12
    JALR ZERO, R9, 0

compute_enclave_id:
    SZERO
    SLD64 S[0], [ZERO+@K_PUBID]
    SLD64 S[1], [R12+80]
    SLD64 S[2], [R12+88]
    SLD64 S[3], [R5+0]
    SLD64 S[4], [R5+8]
    SLD64 S[5], [R5+16]
    SLD64 S[6], [R5+24]
    MOVZ20 R8, 31
    SPUT S[7], R8
    J padded_keccak12

; Verify Merkle capability: `S[0..1]` = `leaf_id`, `[R4+0..8]` = `sibling`, `R9` = `tag` (`0x43500` or `0x43501`).
verify_cap_tok:
    ADDI R1, RA, 0
    SGET R6, S[0]
    SGET R7, S[1]
    SZERO
    SPUT S[0], R9
    SPUT S[1], R6
    SPUT S[2], R7
    SLD64 S[3], [R4+0]
    SLD64 S[4], [R4+8]
    MOVZ20 R8, 31
    SPUT S[5], R8
    CALL padded_keccak12
    LD64 R8, [R12+96]
    MOVZ20 R9, 0x10000
    OR R9, R8, R9
    ST64 [R12+96], R9
    LD64 R4, [R12+80]
    LD64 R5, [R12+88]
    ST64 [R12+96], R8
    OR R9, R4, R5
    BEQZ R9, bad_mac
    SGET R6, S[0]
    SGET R7, S[1]
    XOR R4, R4, R6
    XOR R5, R5, R7
    OR R4, R4, R5
    BNEZ R4, bad_mac
    JALR ZERO, R1, 0

clear_tx_all:
    ADDI R5, R15, 0
    MOVZ20 R6, 16
zero_words:
    ST64 [R5], ZERO
    ADDI R5, R5, 8
    ADDI R6, R6, -1
    BNEZ R6, zero_words
    RET

copy_or_4:
    MOVZ20 R6, 4
copy_or_n:
    MOVZ20 R7, 0
copy_or_loop:
    LD64 R8, [R4]
    ST64 [R5], R8
    OR R7, R7, R8
    ADDI R4, R4, 8
    ADDI R5, R5, 8
    ADDI R6, R6, -1
    BNEZ R6, copy_or_loop
    RET

xor_diff_2:
    MOVZ20 R6, 2
    J xor_diff_n
xor_diff_4:
    MOVZ20 R6, 4
xor_diff_n:
    MOVZ20 R7, 0
xor_diff_loop:
    LD64 R8, [R4]
    LD64 R9, [R5]
    XOR R8, R8, R9
    OR R7, R7, R8
    ADDI R4, R4, 8
    ADDI R5, R5, 8
    ADDI R6, R6, -1
    BNEZ R6, xor_diff_loop
    RET

sst_s0_s6:
    SST64 [R5+48], S[6]
sst_s0_s5:
    SST64 [R5+40], S[5]
sst_s0_s4:
    SST64 [R5+32], S[4]
sst_s0_s3:
    SST64 [R5+24], S[3]
    SST64 [R5+16], S[2]
sst_s0_s1:
    SST64 [R5+8], S[1]
    SST64 [R5+0], S[0]
    RET

sld_e23:
    SLD64 S[10], [R4+0]
    SLD64 S[11], [R4+8]
    SLD64 S[12], [R4+16]
    SLD64 S[13], [R4+24]
    SLD64 S[14], [R4+32]
    SLD64 S[15], [R4+40]
    SLD64 S[16], [R4+48]
    RET

add_4x_e2:
    FP5.ADD E2, E2, E2
add_2x_e2:
    FP5.ADD E2, E2, E2
    FP5.ADD E0, E0, E2
    RET

sxor_16:
    LD64 R8, [R4+120]
    SXOR S[15], R8
sxor_15:
    LD64 R8, [R4+112]
    SXOR S[14], R8
sxor_14:
    LD64 R8, [R4+104]
    SXOR S[13], R8
sxor_13:
    LD64 R8, [R4+96]
    SXOR S[12], R8
sxor_12:
    LD64 R8, [R4+88]
    SXOR S[11], R8
    LD64 R8, [R4+80]
    SXOR S[10], R8
sxor_10:
    LD64 R8, [R4+72]
    SXOR S[9], R8
    LD64 R8, [R4+64]
    SXOR S[8], R8
sxor_8:
    LD64 R8, [R4+56]
    SXOR S[7], R8
sxor_7:
    LD64 R8, [R4+48]
    SXOR S[6], R8
sxor_6:
    LD64 R8, [R4+40]
    SXOR S[5], R8
sxor_5:
    LD64 R8, [R4+32]
    SXOR S[4], R8
sxor_4:
    LD64 R8, [R4+24]
    SXOR S[3], R8
    LD64 R8, [R4+16]
    SXOR S[2], R8
    LD64 R8, [R4+8]
    SXOR S[1], R8
    LD64 R8, [R4+0]
    SXOR S[0], R8
    MOVZ20 R8, 31
    RET

get_record:
    LD64 R6, [R12+16]
    SHRI R6, R6, 32
    LD64 R7, [R12+56]
    SHRI R7, R7, 32
    SHLI R7, R7, 32
    OR R7, R7, R6
    RET

turbo_perm12:
    MOVZ20 R4, 31
    SXOR S[16], R4
padded_keccak12:
    MOVZ20 R4, 128
    SHLI R4, R4, 56
    SXOR S[16], R4
    KECCAK.F1600 12
    RET

nonce:
    SZERO
    MOVZ20 R6, 0
wait_random:
    LD64 R8, [R12+72]
    SHRI R9, R8, 33
    BNEZ R9, trng_error
    SHRI R8, R8, 30
    ANDI R8, R8, 3
    ADDI R8, R8, -3
    BNEZ R8, wait_random
    LD64 R8, [R12+64]
    BNEZ R6, nonce_second
    SPUT S[0], R8
    MOVZ20 R6, 1
    J wait_random
nonce_second:
    SPUT S[1], R8
    MOVZ20 R4, 31
    SPUT S[2], R4
    ADDI R11, RA, 0
    CALL padded_keccak12
    SST64 [R12+24], S[0]
    SST64 [R12+120], S[1]
    ADDI R5, R15, 0
    CALL sst_s0_s1
    JALR ZERO, R11, 0

no_key:
    MOVZ20 R4, 4
    HALT
bad_mac:
    MOVZ20 R4, 5
    HALT
rollback_error:
    MOVZ20 R4, 7
    HALT
anchor_error:
    MOVZ20 R4, 9
    HALT
keyset_error:
    MOVZ20 R4, 10
    HALT
trng_error:
    MOVZ20 R4, 11
    HALT
puf_error:
    MOVZ20 R4, 12
    HALT
