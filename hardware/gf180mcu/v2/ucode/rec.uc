; Record range (addresses 80..287): the only addresses at which FRAM instructions decode and state rows
; are written.
;
; FRAM record 0, the helper record, is nine words in the order of state rows st0..st8 at COMMIT:
;   commit word, syndromes (2), authority root (2), check tag (2), enrolment nonce (2).
; FRAM records 1 and 2 are the lifecycle slots; the record with sequence number s is in slot 1 + s mod 2:
;   REC0, REC1, REC2, ROOT0, ROOT1, tag[2],
;   tag = TurboSHAKE256(K_dev || "DREGGREC" || the five words, D = 0x1F)[0..15].
.org KEY_END

; nonce_put: NONCE <- lanes 0, 1 (a conditioned nonce; the lanes hold no key).
nonce_put:  LD   l0
            ST   NONCE0
            LD   l1
            ST   NONCE1 ret
; nonce_clr: a nonce is spent by the first statement that uses it, accepted or not.
nonce_clr:  LD   #0
            ST   NONCE0
            ST   NONCE1 ret
; tag_in: TAG <- the next two payload words (COMMIT).
tag_in:     DIN  > TAG0
            DIN  > TAG1 ret

; hlp_read: helper record -> ARG2 (commit word), A0, A1 (syndromes), ARG0, ARG1 (root), TAG, NONCE.
hlp_read:   LD   #0
            FRAM RSTART
            FRAM RWORD > ARG2
            FRAM RWORD > A0
            FRAM RWORD > A1
            FRAM RWORD > ARG0
            FRAM RWORD > ARG1
            FRAM RWORD > TAG0
            FRAM RWORD > TAG1
            FRAM RWORD > NONCE0
            FRAM RWORD > NONCE1
            FRAM DONE ret

; hlp_write: stage the helper record in st0..st4 (TAG and NONCE hold theirs already), write it, read it
; back. Z is set on a difference.
hlp_write:  LD   ARG2
            ST   REC0
            LDF  SYN0
            ST   REC1
            LDF  SYN1
            ST   REC2
            LD   ARG0
            ST   ROOT0
            LD   ARG1
            ST   ROOT1
            LD   #0
            FRAM WSTART
            FRAM WWORD st0
            FRAM WWORD st1
            FRAM WWORD st2
            FRAM WWORD st3
            FRAM WWORD st4
            FRAM WWORD st5
            FRAM WWORD st6
            FRAM WWORD st7
            FRAM WWORD st8
            FRAM DONE
            LD   #0
            FRAM RSTART
            SETX #0
hw_chk:     FRAM RWORD
            CMP  st0+X x+
            BXNE #9 hw_chk
            FRAM DONE ret

; rec_init: the first lifecycle record from the commit word in ARG2 (u0 [31:0], gen, flags, k) and the
; root in ARG0, ARG1: seq 0, use counter u0, epoch 0, no lease.
rec_init:   LD   ARG2
            UN   HI32 > REC0
            LD   ARG2
            UN   LO32 > REC1
            LD   #0
            ST   REC2
            ST   LEASE
            LD   ARG0
            ST   ROOT0
            LD   ARG1
            ST   ROOT1 ret

; rec_tag: lanes 0, 1 <- tag of the loaded record.
rec_tag:    WIPE #W_LANES
            SETX #0
rt_in:      LD   st0+X
            ST   l5+X x+
            BXNE #5 rt_in
rec_mac:    LDC  C_LREC
            ST   l4
            LD   #D_FRAM
            ST   l10
            LDC  C_PAD
            ST   l16
            KMOV k_dev0 > l0
            KMOV k_dev1 > l1
            KMOV k_dev2 > l2
            KMOV k_dev3 > l3
            KEC  12 ret

; rec_next: sequence number + 1, then rec_store.
rec_next:   LD   REC0
            UN   HI32 > A0
            LD   REC0
            ADD  #1
            OR   A0 > REC0
; rec_store: write the loaded record to its slot and read it back. Z is set on a difference.
rec_store:  CALL rec_tag
            LD   REC0
            AND  #1
            ADD  #1
            ST   A0
            FRAM WSTART
            FRAM WWORD st0
            FRAM WWORD st1
            FRAM WWORD st2
            FRAM WWORD st3
            FRAM WWORD st4
            FRAM WWORD l0
            FRAM WWORD l1
            FRAM DONE
            LD   A0
            FRAM RSTART
            SETX #0
rs_chk:     FRAM RWORD
            CMP  st0+X x+
            BXNE #5 rs_chk
            FRAM RWORD
            CMPT l0
            FRAM RWORD
            CMPT l1
            FRAM DONE ret

; rec_load: read both slots and load the authentic record with the larger sequence number.
; H = 0 if neither slot holds an authentic record. Staging: t0..t4; A0 counts.
rec_load:   LD   #0
            ST   A0
            LD   #1
            CALL rl_slot
            LD   #2
            CALL rl_slot
            LD   A0 ret
rl_slot:    FRAM RSTART
            WIPE #W_LANES
            SETX #0
rl_in:      FRAM RWORD > t0+X
            ST   l5+X x+
            BXNE #5 rl_in
            CALL rec_mac
            CTL  CLRZ
            FRAM RWORD
            CMPT l0
            FRAM RWORD
            CMPT l1
            FRAM DONE
            BR   Z rl_ret            ; not authentic
            LD   A0
            BR   HZ rl_take          ; the first authentic record
            LD   REC0
            SUB  t0
            BR   NC rl_ret           ; the loaded sequence number is not smaller
rl_take:    SETX #0
rl_cp:      LD   t0+X
            ST   st0+X x+
            BXNE #5 rl_cp
            LD   #1
            ST   A0
rl_ret:     CTL  CLRZ ret

; u_set: use counter <- A1 (32 bits), then rec_next.
u_set:      LD   REC1
            UN   HI32
            OR   A1 > REC1
            BR   rec_next

; lease_set: ARG0 = base [31:0] | bound [63:32]. The counter jumps to the base whatever the record said.
lease_set:  LD   ARG0
            UN   HSWAP
            UN   LO32 > LEASE
            LD   ARG0
            UN   LO32 > A1
            BR   u_set

; t_epoch: epoch <- ARG0 [31:0].
t_epoch:    LD   ARG0
            UN   LO32
            UN   HSWAP > A0
            LD   REC1
            UN   LO32
            OR   A0 > REC1
            BR   rec_next
; t_retire: the retired flag.
t_retire:   LD   #F_RETIRED
            UN   HSWAP
            UN   SHL8
            UN   SHL8
            OR   REC0 > REC0
            BR   rec_next
; t_rotate: root <- ARG0, ARG1; threshold <- ARG2 [7:0]; generation + 1.
t_rotate:   LD   ARG0
            ST   ROOT0
            LD   ARG1
            ST   ROOT1
            LD   REC0
            UN   HSWAP
            AND  #0xFFFF
            ADD  #1
            AND  #0xFFFF
            ST   A0                  ; generation + 1
            LD   REC0
            UN   HSWAP
            UN   SHR16
            AND  #0xFF
            UN   SHL8
            UN   SHL8
            OR   A0 > A0             ; | flags << 16
            LD   ARG2
            AND  #0xFF
            UN   SHL8
            UN   SHL8
            UN   SHL8
            OR   A0
            UN   HSWAP > A0          ; | k << 24, moved to the upper half
            LD   REC0
            UN   LO32
            OR   A0 > REC0
            BR   rec_next
