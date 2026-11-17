; Signer routines (use U1): PRF_MSG (0x42) and CTH (0x41), SLH-DSA-SHAKE with n = 16.
.entry 0x42 prfmsg ready
.entry 0x41 cth ready

; ---------------------------------------------------------------------------------------------
; Coprocessor mode only. SK.seed, SK.prf and K_host are derived from K_dev when used (hash.uc, kdf).
; PRF_MSG: R = SHAKE256(SK.prf || payload)[0..15], payload = opt_rand || M. flags must be 0.
; Not tagged: R is the public randomiser of a signature (README, deviations).
prfmsg:     LDF  FLAGS
            BR   HNZ e_len
            CALL copro
            LDC  C_LPRF
            CALL kdf
            LD   #0
            ST   l2
            ST   l3
            ST   l4
            ST   l5
            ST   l6
            ST   l7
            WIPE #W_HI
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
;   Counted keys (policy flag F_COUNTED, fixed at COMMIT): every request that is not PUBGEN must be WOTS
;         with key pair address = leaf counter; the leaf must not be below the use counter u of the
;         lifecycle record nor, on a leased chip, at or above the bound of this session's lease; and the
;         record with u = leaf + 1 is written and read back before any release. The request has no say
;         in whether the counter applies.
; Every request needs the tag, PUBGEN included. No request names a chain position.
cth:        LDF  LEN
            XOR  #88
            BR   HNZ e_len
            LDF  FLAGS
            AND  #0xFE
            BR   HNZ e_len
            CALL copro
            LDC  C_LHOST             ; request tag under K_host
            CALL kdf
            WIPE #W_HI
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
            LD   REC0
            UN   HSWAP
            UN   SHR16
            AND  #F_COUNTED
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
            LD   S0                  ; the leaf must not be below the use counter
            UN   LO32
            SUB  REC1
            BR   CY e_reuse
            LD   REC0
            UN   HSWAP
            UN   SHR16
            AND  #F_LEASED
            BR   HZ cth_adv
            LD   S0                  ; leased: and below the bound of this session
            UN   LO32
            SUB  LEASE
            BR   NC e_lease
cth_adv:    LD   S0
            UN   LO32
            ADD  #1
            BR   CY e_reuse          ; counter would wrap
            ST   A1
            CALL u_set               ; the record with u = leaf + 1, written and read back
            BR   Z e_record_io
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
w_start:    CALL seed_l67
            LD   #5                  ; WOTS_PRF
            UN   BE32
            XOR  KP
            ST   l4
            LDF  X
            UN   BE32 > l5
            CALL ctx_kec
            BR   C1Z w_emit
            LD   #0
            ST   TMP                 ; hash address
w_step:     CALL wots_fstep          ; WOTS_HASH (type 0)
            DBNZ 1 w_step
w_emit:     REL  l0
            REL  l1
            INCX
            DBNZ 0 w_chain
            END

; --- FORS
fors:       SETX #0
            LDF  ARGLO
            SETC 0 H
fo_word:    SETC 1 #4
fo_slot:    CALL seed_l67
            LD   #6                  ; FORS_PRF
            UN   BE32
            XOR  KP
            ST   l4
            LD   MW0+X
            AND  #0xFFFF
            UN   HSWAP
            UN   BE32 > l5
            CALL ctx_kec
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

; seed_l67: lanes 6, 7 <- SK.seed (derived); lanes 8..24 clear. The caller then writes lanes 4, 5.
seed_l67:   LDC  C_LSEED
            CALL kdf
            LD   l0 > l6
            LD   l1 > l7
            WIPE #W_HI ret

; copro: refuse unless the chip is in coprocessor mode.
copro:      LD   REC0
            UN   HSWAP
            UN   SHR16
            AND  #F_VAT
            BR   HNZ e_class
            RET

e_mac:      CTL  SETFM
            FAIL #E_MAC
e_reuse:    FAIL #E_REUSE
e_lease:    FAIL #E_LEASE
