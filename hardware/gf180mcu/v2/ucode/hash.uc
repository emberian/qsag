; Hash subroutines shared by the signer (sign.uc) and the verifier (slh.uc).

; kdf: lanes 0, 1 <- TurboSHAKE256(K_dev || label, D = 0x23)[0..15], the label in H. Keys other than
; K_dev are not stored: each is derived here when it is used and stays in the lanes.
kdf:        WIPE #W_LANES
            ST   l4
            LD   #D_KDF
            ST   l5
            LDC  C_PAD
            ST   l16
            KMOV k_dev0 > l0
            KMOV k_dev1 > l1
            KMOV k_dev2 > l2
            KMOV k_dev3 > l3
            KEC  12 ret

; SHAKE256(PK.seed || ADRS || message)[0..15] into lanes 0, 1. The caller writes lanes 4 and 5 (ADRS
; bytes 16..31) and the message.
; ctx_lanes: PK.seed, ADRS bytes 0..15 and the padding of a 16-byte message. ctx_base: without the suffix.
ctx_lanes:  LD   #0x1F
            ST   l8
ctx_base:   LD   PK0 > l0
            LD   PK1 > l1
            LD   S0 > l2
            LD   TREE > l3
            LDC  C_PAD
            ST   l16 ret
; ctx_kec: the hash of a 16-byte message that is already in lanes 6, 7 (lanes 8..24 clear).
ctx_kec:    CALL ctx_lanes
            KEC  24 ret
; f_step: the message is the previous value in lanes 0, 1.
f_step:     LD   l0 > l6
            LD   l1 > l7
            WIPE #W_HI
            CALL ctx_lanes
            KEC  24 ret
; h_step: the message is the 32 bytes in lanes 6..9 (lanes 10..24 clear).
h_step:     LD   #0x1F
            ST   l10
            CALL ctx_base
            KEC  24 ret
; wots_fstep: one step of WOTS chain X at hash address TMP; TMP + 1 afterwards.
wots_fstep: LD   KP > l4
            LD   TMP
            UN   HSWAP > l5
            LDF  X
            XOR  l5
            UN   BE32 > l5
            LD   TMP
            ADD  #1
            ST   TMP
            BR   f_step

; next_digit: C1 and A1 <- base-16 digit of chain X; chains 32..34 take the checksum digits. Call in
; order. The digit queue is MW0, MW1 (least significant nibble first); MW2 is the digit sum.
next_digit: BXNE #16 nd_a
            LD   MW1 > MW0
nd_a:       BXNE #32 nd_b
            LD   #480                ; checksum = 32 * 15 - digit sum; its 12 bits, big-endian digits
            SUB  MW2
            UN   SHL4
            UN   BE32
            UN   SHR16
            UN   NIB > MW0
nd_b:       LD   MW0
            AND  #15
            ST   A1
            SETC 1 H
            ADD  MW2 > MW2
            LD   MW0
            UN   SHR4 > MW0 ret

; dom_kec: lanes 0, 1 <- TurboSHAKE256(lanes 0..3, D = H)[0..15].
dom_kec:    ST   l4
            LD   #0
            ST   l5
            ST   l6
            ST   l7
            WIPE #W_HI
            LDC  C_PAD
            ST   l16
            KEC  12 ret
