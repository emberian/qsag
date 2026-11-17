; TRNG: pair selection, health tests and conditioning (ARCHITECTURE.md 6.5). The organ counts beats and
; accumulates statistics; every threshold and every decision is here.
; Scratch: A0, A1, TMP, MW0..MW3. Counters C0, C1.

; trng_nonce: lanes 0, 1 <- a 128-bit nonce. Z is set on failure. If the armed pair fails a health test
; the start-up runs once more.
trng_nonce: LDF  TFLAGS
            AND  #TF_ARMED
            BR   HNZ tn_gen
tn_start:   CALL t_start
            BR   HNZ tn_bad
            CALL t_gen
            BR   HNZ tn_bad
            CTL  CLRZ ret
tn_gen:     CALL t_gen
            BR   HNZ tn_start
            CTL  CLRZ ret
tn_bad:     LD   #1
            CMP  #0 ret

; t_run4: 256 counts with fresh statistics.
t_run4:     CTL  TCLR
            SETC 1 #4
tr_run:     CTL  TRUN
            DBNZ 1 tr_run
            RET

; t_health: H = 0 if the last 256 counts pass H2 (beat time-out, short count), H4 (repetition,
; proportion) and H3 (V4 <= 8 V, i.e. 85 S4 <= 168 S1 for the two sums the organ keeps).
t_health:   LDF  TFLAGS
            AND  #TF_BAD
            BR   HNZ th_ret
            LDF  TS4
            ST   TMP
            UN   SHL4
            UN   SHL1
            UN   SHL1
            ST   A0                  ; 64 S4
            LD   TMP
            UN   SHL4
            ADD  A0 > A0             ; + 16 S4
            LD   TMP
            UN   SHL1
            UN   SHL1
            ADD  A0 > A0             ; + 4 S4
            LD   TMP
            ADD  A0 > A0             ; 85 S4
            LDF  TS1
            ST   TMP
            UN   SHL8
            UN   SHR1
            ST   A1                  ; 128 S1
            LD   TMP
            UN   SHL4
            UN   SHL1
            ADD  A1 > A1             ; + 32 S1
            LD   TMP
            UN   SHL4
            UN   SHR1
            ADD  A1 > A1             ; 168 S1
            LD   A1
            SUB  A0
            BR   CY th_bad           ; 168 S1 < 85 S4: the jitter is not white
            LD   #0 ret
th_bad:     LD   #1
th_ret:     RET

; t_start: try every pair (64 counts, and 192 more unless its beats are too long); qualify those with
; clean tests, V >= 2.0 and a mean count in 400..3600; take
; the qualifying pair with the smallest mean count; then four blocks under every test with V >= 1.25.
; H = 0 on success. MW0 = pair being tried, MW1 = best pair + 1 (0: none), MW2 = its count sum.
t_start:    LD   #0
            ST   MW0
            ST   MW1
ts_pair:    LD   MW0
            CTL  TSEL
            CTL  TCLR
            CTL  TRUN
            LDF  TSUM                ; a pair whose first 64 beats are already too long is abandoned
            UN   SHR4
            UN   SHR1
            UN   SHR1
            SUB  #T_MEANHI
            BR   NC ts_next
            SETC 1 #3
            CALL tr_run
            CALL t_health
            BR   HNZ ts_next
            LDF  TS1
            SUB  #T_VSEL
            BR   CY ts_next          ; V below 2.0
            LDF  TSUM
            UN   SHR8
            SUB  #T_MEANLO
            BR   CY ts_next          ; beats too short: the pair is too far apart
            LD   MW1
            BR   HZ ts_take
            LDF  TSUM
            SUB  MW2
            BR   NC ts_next          ; not shorter than the best so far
ts_take:    LDF  TSUM
            ST   MW2
            LD   MW0
            ADD  #1
            ST   MW1
ts_next:    LD   MW0
            ADD  #1
            ST   MW0
            XOR  #T_PAIRS
            BR   HNZ ts_pair
            LD   MW1
            BR   HZ ts_none
            SUB  #1
            CTL  TSEL
            SETC 0 #4
ts_test:    CALL t_run4
            CALL t_health
            BR   HNZ ts_none
            LDF  TS1
            SUB  #T_VMIN
            BR   CY ts_none
            DBNZ 0 ts_test
            CTL  TARM
            LD   #0 ret
ts_none:    LD   #1 ret

; t_gen: lanes 0, 1 <- TurboSHAKE256(512 raw bits || counter noise of the characterisation rings,
; D = 0x28)[0..15]. H = 0 on success. H1 fails when both blocks are below V = 1.25; every other test
; fails on one block.
t_gen:      WIPE #W_LANES
            SETX #0
            LD   #0
            ST   MW3
            SETC 0 #2
tg_blk:     CTL  TCLR
            SETC 1 #4
tg_run:     CTL  TRUN
            LDF  TRAW
            XOR  l0+X > l0+X x+
            DBNZ 1 tg_run
            CALL t_health
            BR   HNZ tg_bad
            LDF  TS1
            SUB  #T_VMIN
            BR   NC tg_ok
            LD   MW3
            ADD  #1
            ST   MW3
tg_ok:      DBNZ 0 tg_blk
            LD   MW3
            XOR  #2
            BR   HZ tg_bad
            LDF  PNOISE
            ST   l8
            LD   #D_NONCE
            ST   l9
            LDC  C_PAD
            ST   l16
            KEC  12
            LD   #0 ret
tg_bad:     LD   #1 ret
