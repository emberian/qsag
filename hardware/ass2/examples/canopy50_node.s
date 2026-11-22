; zk-Hem v2 Canopy internal node, TurboSHAKE256 profile, 50-byte digests:
;   out = TurboSHAKE256_TREE( 0x00 || node_idx (4 bytes LE) || left (50) || right (50) )[0..49]
; with (left, right) = (cur, sib) if dir == 0, else (sib, cur).  The 105-byte input is one rate block.
; In : A0 -> cur  (7 words: 50 bytes, bytes 50..55 zero)      A1 -> sib (same layout)
;      A2 =  dir  (0 or non-zero; may be secret: it only ever reaches SEL)
;      A3 =  node_idx (heap numbering, < 2^32, public)
;      A4 -> midstate (25 words: the state after the customization block)   A5 -> out (7 words)
; Left child bytes land at message offset 5, right child bytes at offset 55, so word i of the left
; child is split 3 + 5 bytes across lanes i, i+1 and word i of the right child 1 + 7 across 6+i, 7+i.
; SP is 8-byte aligned with one writable, disjoint word below it. Cycles: 190.
canopy50_node:
    ADDI    SP, SP, -8
    ST64    [SP], T0            ; preserve the callee-saved word
    SLD64   S[0], [A4+0]
    SLD64   S[1], [A4+8]
    SLD64   S[2], [A4+16]
    SLD64   S[3], [A4+24]
    SLD64   S[4], [A4+32]
    SLD64   S[5], [A4+40]
    SLD64   S[6], [A4+48]
    SLD64   S[7], [A4+56]
    SLD64   S[8], [A4+64]
    SLD64   S[9], [A4+72]
    SLD64   S[10], [A4+80]
    SLD64   S[11], [A4+88]
    SLD64   S[12], [A4+96]
    SLD64   S[13], [A4+104]
    SLD64   S[14], [A4+112]
    SLD64   S[15], [A4+120]
    SLD64   S[16], [A4+128]
    SLD64   S[17], [A4+136]
    SLD64   S[18], [A4+144]
    SLD64   S[19], [A4+152]
    SLD64   S[20], [A4+160]
    SLD64   S[21], [A4+168]
    SLD64   S[22], [A4+176]
    SLD64   S[23], [A4+184]
    SLD64   S[24], [A4+192]
    SHLI    T0, A3, 8           ; header: tag 0x00 in byte 0, node_idx in bytes 1..4
    SXOR    S[0], T0
    LD64    A3, [A0+0]         ; word 0 of cur and of sib
    LD64    A4, [A1+0]
    SEL     T0, A3, A4, A2      ; left  word = dir ? sib : cur
    SEL     A4, A4, A3, A2      ; right word = dir ? cur : sib
    SHLI    A3, T0, 40
    SXOR    S[0], A3
    SHRI    A3, T0, 24
    SXOR    S[1], A3
    SHLI    A3, A4, 56
    SXOR    S[6], A3
    SHRI    A3, A4, 8
    SXOR    S[7], A3
    LD64    A3, [A0+8]         ; word 1 of cur and of sib
    LD64    A4, [A1+8]
    SEL     T0, A3, A4, A2      ; left  word = dir ? sib : cur
    SEL     A4, A4, A3, A2      ; right word = dir ? cur : sib
    SHLI    A3, T0, 40
    SXOR    S[1], A3
    SHRI    A3, T0, 24
    SXOR    S[2], A3
    SHLI    A3, A4, 56
    SXOR    S[7], A3
    SHRI    A3, A4, 8
    SXOR    S[8], A3
    LD64    A3, [A0+16]         ; word 2 of cur and of sib
    LD64    A4, [A1+16]
    SEL     T0, A3, A4, A2      ; left  word = dir ? sib : cur
    SEL     A4, A4, A3, A2      ; right word = dir ? cur : sib
    SHLI    A3, T0, 40
    SXOR    S[2], A3
    SHRI    A3, T0, 24
    SXOR    S[3], A3
    SHLI    A3, A4, 56
    SXOR    S[8], A3
    SHRI    A3, A4, 8
    SXOR    S[9], A3
    LD64    A3, [A0+24]         ; word 3 of cur and of sib
    LD64    A4, [A1+24]
    SEL     T0, A3, A4, A2      ; left  word = dir ? sib : cur
    SEL     A4, A4, A3, A2      ; right word = dir ? cur : sib
    SHLI    A3, T0, 40
    SXOR    S[3], A3
    SHRI    A3, T0, 24
    SXOR    S[4], A3
    SHLI    A3, A4, 56
    SXOR    S[9], A3
    SHRI    A3, A4, 8
    SXOR    S[10], A3
    LD64    A3, [A0+32]         ; word 4 of cur and of sib
    LD64    A4, [A1+32]
    SEL     T0, A3, A4, A2      ; left  word = dir ? sib : cur
    SEL     A4, A4, A3, A2      ; right word = dir ? cur : sib
    SHLI    A3, T0, 40
    SXOR    S[4], A3
    SHRI    A3, T0, 24
    SXOR    S[5], A3
    SHLI    A3, A4, 56
    SXOR    S[10], A3
    SHRI    A3, A4, 8
    SXOR    S[11], A3
    LD64    A3, [A0+40]         ; word 5 of cur and of sib
    LD64    A4, [A1+40]
    SEL     T0, A3, A4, A2      ; left  word = dir ? sib : cur
    SEL     A4, A4, A3, A2      ; right word = dir ? cur : sib
    SHLI    A3, T0, 40
    SXOR    S[5], A3
    SHRI    A3, T0, 24
    SXOR    S[6], A3
    SHLI    A3, A4, 56
    SXOR    S[11], A3
    SHRI    A3, A4, 8
    SXOR    S[12], A3
    LD64    A3, [A0+48]         ; word 6 of cur and of sib
    LD64    A4, [A1+48]
    SEL     T0, A3, A4, A2      ; left  word = dir ? sib : cur
    SEL     A4, A4, A3, A2      ; right word = dir ? cur : sib
    SHLI    A3, T0, 40
    SXOR    S[6], A3
    SHLI    A3, A4, 56
    SXOR    S[12], A3
    SHRI    A3, A4, 8
    SXOR    S[13], A3
    MOVZ20  A3, 0x700           ; TurboSHAKE domain byte 0x07 at message byte 105
    SXOR    S[13], A3
    MOVZ20  A3, 0x80            ; final padding bit: 0x80 at rate byte 135
    SHLI    A3, A3, 56
    SXOR    S[16], A3
    KECCAK.F1600 12             ; 12 cycles, in place on S[0..24]
    SST64   [A5+0], S[0]        ; squeeze 50 bytes
    SST64   [A5+8], S[1]
    SST64   [A5+16], S[2]
    SST64   [A5+24], S[3]
    SST64   [A5+32], S[4]
    SST64   [A5+40], S[5]
    SGET    A3, S[6]
    ANDI    A3, A3, 0xFFFF      ; bytes 48, 49
    ST64    [A5+48], A3
    LD64    T0, [SP]
    ST64    [SP], ZERO          ; erase the spill before releasing the slot
    ADDI    SP, SP, 8
    RET
