; Signer routines (use U1): PRF_MSG (0x42) and CTH (0x41), SLH-DSA-SHAKE with n = 16.
.entry 0x42 prfmsg keyed
.entry 0x41 cth keyed

; ---------------------------------------------------------------------------------------------
; PRF_MSG: R = SHAKE256(SK.prf || payload)[0..15], payload = opt_rand || M. flags must be 0.
; Not tagged: R is the public randomiser of a signature (README, deviations).
prfmsg:     LDF  FLAGS
            BR   HNZ e_len
            KMOV k_prf0 > l0
            KMOV k_prf1 > l1
            LD   #0x1F
            ST   TMP
            SETX #2
            CALL absorb_pad
            LD   #2
            HDR  #2
            REL  l0
            REL  l1
            END

; ---------------------------------------------------------------------------------------------
; CTH: WOTS chain values and FORS leaves from SK.seed.
;   header   flags bit 0 PUBGEN, all other bits 0; length 88
;            arg [7:0] = n (chains or leaves), arg [15:8] = first chain (WOTS)
;   payload  s0      [31:0] leaf counter, [39:32] hypertree layer
;            s1, s2  PK.seed
;            s3      ADRS bytes 8..15 (tree address)
;            s4      ADRS bytes 16..23: type (0 = WOTS, 3 = FORS) and key pair address
;            s5..s8  WOTS: s5, s6 = the 16-byte message to sign, s7 = s8 = 0
;                    FORS: up to 16 leaf indices, 16 bits each, least significant first
;            tag[2]  TurboSHAKE256(K_host || header || s0..s8, D = 0x21)[0..15]
;   WOTS: the chip derives the 32 message digits and the 3 checksum digits (FIPS 205, lg_w = 4)
;         and releases F^{d_i}(sk_i) for chains first .. first + n - 1; PUBGEN releases F^15(sk_i).
;   FORS: releases the secret leaf value at each index; PUBGEN releases F of it.
;   Counted keys (attribute KA_COUNTED, fixed when the key was provisioned): every request that is not
;         PUBGEN must be WOTS with key pair address = leaf counter, and the anchor counter is advanced
;         past the leaf before any release. The request has no say in whether the counter applies.
; Every request needs the tag, PUBGEN included. No request names a chain position.
cth:        LDF  LEN
            XOR  #88
            BR   HNZ e_len
            LDF  FLAGS
            AND  #0xFE
            BR   HNZ e_len
            KMOV k_host0 > l0        ; request tag
            KMOV k_host1 > l1
            LDF  HDRW
            ST   l2
            SETX #0
cth_in:     DIN  > t0+X
            ST   l3+X x+
            BXNE #9 cth_in
            LD   #D_REQ
            ST   l12
            LDC  C_PAD
            ST   l16
            KEC  12
            DIN
            CMPT l0
            DIN
            CMPT l1
            BR   Z e_mac
            ; request shape
            LDF  ARGLO
            BR   HZ e_len
            LD   KP
            UN   LO32
            UN   BE32
            ST   TMP                 ; address type
            LD   KP
            UN   HI32 > KP
            LD   TMP
            BR   HZ cth_wshape
            XOR  #3
            BR   HNZ e_len
            LDF  ARGLO               ; FORS: n <= 16
            SUB  #17
            BR   NC e_len
            BR   cth_state
cth_wshape: LDF  ARGHI               ; WOTS: first + n <= 35
            ST   A0
            LDF  ARGLO
            ADD  A0
            SUB  #36
            BR   NC e_len
cth_state:  LDF  FLAGS
            AND  #1
            BR   HNZ cth_go          ; PUBGEN releases public values only
            LDF  KATTR
            AND  #KA_COUNTED
            BR   HZ cth_go           ; uncounted key
            LD   TMP
            BR   HNZ e_class         ; a counted key signs with WOTS only
            LD   KP                  ; the counter guards the key pair it names: key pair address = leaf
            UN   HSWAP
            UN   BE32
            ST   A0
            LD   S0
            UN   LO32
            XOR  A0
            BR   HNZ e_class
            ; anchor: larger authentic counter of the two slots; write leaf + 1 to the other slot
            LD   #1
            CALL anchor_read
            LD   A0
            ST   A1
            LD   #0
            CALL anchor_read
            LD   A1
            UN   HI32
            BR   HZ an_use0          ; slot 1 is not a record
            LD   A1                  ; an invalid slot 0 reads as 0, so slot 1 wins the comparison
            SUB  A0
            BR   CY an_use0          ; counter 1 < counter 0
an_use1:    LD   A1
            UN   LO32 > A0           ; current counter
            LD   #0
            ST   A1                  ; slot to write
            BR   an_cur
an_use0:    LD   A0
            UN   HI32
            BR   HZ e_anchor_empty
            LD   A0
            UN   LO32 > A0
            LD   #1
            ST   A1
an_cur:     LD   ST_HWM
            UN   HI32
            BR   HZ an_leaf
            LD   A0
            SUB  ST_HWM
            BR   CY e_rollback       ; anchor below the high-water mark
an_leaf:    LD   S0
            UN   LO32
            SUB  A0
            BR   CY e_reuse          ; leaf below the counter
            LD   S0
            UN   LO32
            ADD  #1
            BR   CY e_reuse          ; counter would wrap
            ST   A0
            CALL fram_tag
            LD   A1
            CALL fram_write
            LD   A1
            CALL fram_check
            BR   Z e_anchor_io
            LD   #1
            UN   HSWAP
            XOR  A0
            ST   ST_HWM
            WIPE #W_LANES
cth_go:     LD   S0                  ; S0 <- ADRS bytes 0..7: layer, big-endian
            UN   HSWAP
            AND  #0xFF
            UN   BE32 > S0
            LDF  ARGLO
            ST   A0
            ADD  A0
            HDR  #70                 ; 2 n words
            LD   TMP
            BR   HNZ fors

; --- WOTS
            LD   MW0                 ; digit queue: least significant nibble first
            UN   NIB > MW0
            LD   MW1
            UN   NIB > MW1
            LD   #0
            ST   MW2                 ; digit sum
            SETX #0
            LDF  ARGHI
            BR   HZ w_count
            SETC 0 H
w_skip:     CALL next_digit          ; digits of chains before the first one
            INCX
            DBNZ 0 w_skip
w_count:    LDF  ARGLO
            SETC 0 H
w_chain:    CALL next_digit          ; C1 = digit of chain X
            LDF  FLAGS
            AND  #1
            BR   HZ w_start
            SETC 1 #15               ; PUBGEN: the chain end
w_start:    WIPE #W_LANES
            LD   #5                  ; WOTS_PRF
            UN   BE32
            XOR  KP
            ST   l4
            LDF  X
            UN   BE32 > l5
            CALL prf_step
            BR   C1Z w_emit
            LD   #0
            ST   TMP                 ; hash address
w_step:     LD   KP                  ; WOTS_HASH (type 0)
            ST   l4
            LD   TMP
            UN   HSWAP > l5
            LDF  X
            XOR  l5
            UN   BE32 > l5
            LD   TMP
            ADD  #1
            ST   TMP
            CALL f_step
            DBNZ 1 w_step
w_emit:     REL  l0
            REL  l1
            INCX
            DBNZ 0 w_chain
            END

; next_digit: C1 <- base-16 digit of chain X; chains 32..34 take the checksum digits. Call in order.
next_digit: BXNE #16 nd_a
            LD   MW1
            ST   MW0
nd_a:       BXNE #32 nd_b
            LD   #480                ; checksum = 32 * 15 - digit sum; its 12 bits, big-endian digits
            SUB  MW2
            UN   SHL4
            UN   BE32
            UN   SHR16
            UN   NIB > MW0
nd_b:       LD   MW0
            AND  #15
            SETC 1 H
            ADD  MW2 > MW2
            LD   MW0
            UN   SHR4 > MW0 ret

; --- FORS
fors:       SETX #0
            LDF  ARGLO
            SETC 0 H
fo_word:    SETC 1 #4
fo_slot:    WIPE #W_LANES
            LD   #6                  ; FORS_PRF
            UN   BE32
            XOR  KP
            ST   l4
            LD   MW0+X
            AND  #0xFFFF
            UN   HSWAP
            UN   BE32 > l5
            CALL prf_step
            LDF  FLAGS
            AND  #1
            BR   HZ fo_emit
            LD   #3                  ; FORS_TREE
            UN   BE32
            XOR  KP
            ST   l4
            LD   MW0+X
            AND  #0xFFFF
            UN   HSWAP
            UN   BE32 > l5
            CALL f_step
fo_emit:    REL  l0
            REL  l1
            LD   MW0+X
            UN   SHR16 > MW0+X
            DBNZ 0 fo_next
            END
fo_next:    DBNZ 1 fo_slot
            INCX
            BR   fo_word

; --- one tweakable hash: SHAKE256(PK.seed || ADRS || 16 bytes)[0..15] into lanes 0, 1.
;     Lanes 4 and 5 (ADRS bytes 16..31) are written by the caller.
; prf_step: the 16 bytes are SK.seed. Lanes must have been wiped by the caller.
prf_step:   CALL ctx_lanes
            KMOV k_seed0 > l6
            KMOV k_seed1 > l7
            KEC  24 ret
; f_step: the 16 bytes are the previous value in lanes 0, 1.
f_step:     LD   l0
            ST   l6
            LD   l1
            ST   l7
            WIPE #W_HI
            CALL ctx_lanes
            KEC  24 ret
ctx_lanes:  LD   PK0
            ST   l0
            LD   PK1
            ST   l1
            LD   S0
            ST   l2
            LD   TREE
            ST   l3
            LD   #0x1F
            ST   l8
            LDC  C_PAD
            ST   l16 ret

e_mac:      CTL  SETFM
            FAIL #E_MAC
e_anchor_empty: FAIL #E_ANCHOR_EMPTY
e_rollback: CTL  SETFA
            FAIL #E_ROLLBACK
e_reuse:    FAIL #E_REUSE
e_class:    FAIL #E_CLASS
