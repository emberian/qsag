; KECCAK (0x20): sponge over the payload, rate 136 bytes.
;   flags bit 0: 1 = Keccak-p[1600,12] (TurboSHAKE256), 0 = Keccak-f[1600] (SHAKE256, cSHAKE256)
;   arg [7:0] suffix / domain byte, arg [15:8] output words
; Also the sponge subroutines used by PRF_MSG.
.entry 0x20 keccak diag

keccak:     LDF  ARGLO
            ST   TMP                ; suffix byte
            SETX #0
            CALL absorb_pad
            LDF  ARGHI
            HDR  #255
            BR   HZ kq_end
            SETC 0 H
            SETX #0
kq_loop:    PUSH l0+X x+
            DBNZ 0 kq_more
kq_end:     END
kq_more:    BXNE #17 kq_loop
            CALL perm_sel
            SETX #0
            BR   kq_loop

; perm_sel: one permutation, 12 rounds if request flag 0 is set, else 24.
perm_sel:   LDF  FLAGS
            AND  #1
            BR   HZ perm24
            KEC  12 ret
perm24:     KEC  24 ret

; absorb_pad: XOR the rest of the payload into the rate starting at lane X, pad, permute.
;   TMP = suffix byte. Uses C0. The message length modulo 8 is that of the payload.
absorb_pad:
ab_loop:    BR   NOMORE ab_fin
            DIN
            XOR  l0+X > l0+X x+
            BXNE #17 ab_loop
            BR   MORE ab_perm        ; block full
            LDF  LEN
            AND  #7
            BR   HNZ ab_part         ; the last word was partial: its suffix byte is in this block
ab_perm:    CALL perm_sel
            SETX #0
            BR   ab_loop
ab_fin:     LDF  LEN
            AND  #7
            BR   HZ ab_align
ab_part:    SETC 0 H                 ; suffix << 8 * (length mod 8), into the last word's lane
            LD   TMP
ab_shl:     UN   SHL8
            DBNZ 0 ab_shl
            XOR  lm1+X > lm1+X
            BR   ab_last
ab_align:   LD   TMP
            XOR  l0+X > l0+X
ab_last:    LDC  C_PAD
            XOR  l16 > l16
            BR   perm_sel            ; tail call
