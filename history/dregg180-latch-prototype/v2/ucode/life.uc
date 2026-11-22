; Lifecycle commands (ARCHITECTURE.md 3.2, 3.3) and the gate (4.1, 4.6).
;   BOOT   0x44  RESET          payload: nothing (expecting a blank chip), or the owner root's public key
;                               (4 words) and the package of its signature over the helper record
;                               -> lifecycle state, chip id, record word 0, nonce (2)
;   ENROL  0x45  BLANK          -> syndromes (2), check tag (2), nonce (2)
;   COMMIT 0x46  BLANK          payload: check tag (2), commit word, root (2), owner key (4), package
;                               -> K_host (2; zero in vat mode). The chip then waits for a reset.
;   NONCE  0x43  ORPHAN, LEASE  -> nonce (2)
;   REINIT 0x47  ORPHAN         payload: commit word, root (2), owner key (4), package
;   LEASE  0x48  LEASE          arg = 1; payload: base | bound << 32, 0, 0, statement -> record words 0, 1
;   GATE   0x49  READY          arg = type; payload: three argument words, statement -> record word 0
; A statement is k members of the pinned committee (k = 1 with an empty path: one authority key), each:
;   index | path length << 32, public key (4), path, package, path again.
.entry 0x44 boot reset
.entry 0x45 enrol blank
.entry 0x46 commit blank
.entry 0x43 nonce orphan|lease
.entry 0x47 reinit orphan
.entry 0x48 lease lease
.entry 0x49 gate ready

; ---------------------------------------------------------------------------------------------
; BOOT
boot:       CALL hlp_read
            CALL syn_load
            LD   TAG0
            OR   TAG1
            BR   HNZ bt_rec
            LDF  LEN                 ; the helper slot is empty: BLANK
            BR   HNZ e_len
            CALL nonce_clr
            CALL lc_blank
            BR   bt_rsp
bt_rec:     LDF  LEN
            XOR  #BT_LEN
            BR   HNZ e_len
            CTL  CLRZ
            BR   own_stmt            ; the helper record is authenticated before the PUF is touched
bt_auth:    BR   Z bt_noauth
            CALL puf_key             ; reconstruct, compare the check tag, write K_dev
            BR   Z bt_nopuf
            CALL rec_load
            BR   HZ bt_orphan
            LD   REC0
            UN   HSWAP
            UN   SHR16
            ST   A0
            AND  #F_RETIRED
            BR   HNZ bt_retired
            CALL nonce_clr           ; the enrolment nonce has done its work
            LD   A0
            AND  #F_LEASED
            BR   HNZ bt_lease
            CALL lc_ready
            BR   bt_rsp
bt_lease:   CALL lc_lease
            CALL trng_nonce
            BR   Z bt_rsp            ; no entropy: LEASE_PENDING without a nonce; NONCE tries again
            CALL nonce_put
            BR   bt_rsp
bt_orphan:  CALL nonce_clr
            CALL lc_orphan
bt_rsp:     LD   #5
            HDR  #5
            LDF  LC
            PUSH H
            PUSH TAG0
            PUSH REC0
            PUSH NONCE0
            PUSH NONCE1
            END
bt_retired: CTL  ZKEY
            CALL lc_locked
            FAIL #E_RETIRED
bt_noauth:  CTL  SETFM
            CALL lc_locked
            FAIL #E_AUTH
bt_nopuf:   CTL  SETFA
            CALL lc_locked
            FAIL #E_PUF

; ---------------------------------------------------------------------------------------------
; own_stmt: the owner root's statement over (NONCE, syndromes, TAG, ARG2, ARG0, ARG1). Payload: public
; key and package. The stated key is checked against the mask-constant pin (the leaf hash of a
; committee of one) before the signature, and the root the signature leads to is checked after.
; Z is the verdict. Continues by request opcode.
own_stmt:   LD   #0
            ST   ARG3
            DIN  > PK0
            DIN  > PK1
            DIN  > NODE0
            DIN  > NODE1
            CALL mroot
            LDC  C_OWN0
            CMP  l0
            LDC  C_OWN1
            CMP  l1
            CALL stmt_own
            CALL sv
            CALL mroot
            LDC  C_OWN0
            CMP  l0
            LDC  C_OWN1
            CMP  l1
            LDF  HDRW
            UN   SHR8
            AND  #0xFF
            ST   A0
            XOR  #OP_BOOT
            BR   HZ bt_auth
            LD   A0
            XOR  #OP_COMMIT
            BR   HZ cm_auth
            BR   ri_auth

; stmt_own: lanes 0..3 <- TurboSHAKE256(label || NONCE || syndromes || TAG || commit word || root,
; D = 0x22)[0..31]; the label is "DREGG.RI" for REINIT and "DREGG.CM" for BOOT and COMMIT.
stmt_own:   WIPE #W_LANES
            LDF  HDRW
            UN   SHR8
            AND  #0xFF
            XOR  #OP_REINIT
            BR   HZ so_ri
            LDC  C_LCM
            BR   so_go
so_ri:      LDC  C_LRI
so_go:      ST   l0
            LD   NONCE0 > l1
            LD   NONCE1 > l2
            LDF  SYN0
            ST   l3
            LDF  SYN1
            ST   l4
            LD   TAG0 > l5
            LD   TAG1 > l6
            LD   ARG2 > l7
            LD   ARG0 > l8
            LD   ARG1 > l9
            LD   #D_STMT
            ST   l10
            LDC  C_PAD
            ST   l16
            KEC  12 ret

; stmt_tr: lanes 0..3 <- the transition message (ARCHITECTURE.md 4.1):
;   TurboSHAKE256("DREGG.TR" || TAG (2) || record word 0 || type || NONCE || ARG0..ARG2, D = 0x22)[0..31].
stmt_tr:    WIPE #W_LANES
            LDC  C_LTR
            ST   l0
            LD   TAG0 > l1
            LD   TAG1 > l2
            LD   REC0 > l3
            LDF  ARGLO
            ST   l4
            LD   NONCE0 > l5
            LD   NONCE1 > l6
            LD   ARG0 > l7
            LD   ARG1 > l8
            LD   ARG2 > l9
            LD   #D_STMT
            ST   l10
            LDC  C_PAD
            ST   l16
            KEC  12 ret

; mroot: lanes 0, 1 <- the committee root that member (ARG3 index, PK0, PK1, NODE0, NODE1) leads to:
;   leaf = TurboSHAKE256(index || PK.seed || PK.root, D = 0x24)[0..15], then one
;   node = TurboSHAKE256(left || right, D = 0x25)[0..15] per path value read from the payload.
mroot:      WIPE #W_LANES
            LD   ARG3
            UN   LO32 > l0
            LD   PK0 > l1
            LD   PK1 > l2
            LD   NODE0 > l3
            LD   NODE1 > l4
            LD   #D_LEAF
            ST   l5
            LDC  C_PAD
            ST   l16
            KEC  12
            LD   ARG3
            UN   LO32 > A0
            LD   ARG3
            UN   HSWAP
            UN   LO32
            BR   HZ mr_ret
            SETC 0 H
mr_lev:     LD   A0
            AND  #1
            BR   HNZ mr_right
            DIN  > l2
            DIN  > l3
            BR   mr_go
mr_right:   LD   l0 > l2
            LD   l1 > l3
            DIN  > l0
            DIN  > l1
mr_go:      LD   #D_NODE
            CALL dom_kec
            LD   A0
            UN   SHR1 > A0
            DBNZ 0 mr_lev
mr_ret:     RET

; cw_check: H = 0 if the commit word in ARG2 has a threshold of at least 1 and is not retired.
cw_check:   LD   ARG2
            UN   HSWAP
            UN   SHR16
            AND  #F_RETIRED
            BR   HNZ cw_ret
            LD   ARG2
            UN   HSWAP
            UN   SHR16
            UN   SHR8
            AND  #0xFF
            BR   HZ cw_bad
            LD   #0 ret
cw_bad:     LD   #1
cw_ret:     RET

; ---------------------------------------------------------------------------------------------
; ENROL
enrol:      LDF  LEN
            BR   HNZ e_len
            CALL trng_nonce          ; a die without a working entropy source cannot be enrolled
            BR   Z e_trng
            CALL nonce_put
            CALL puf_enrol
            LD   #6
            HDR  #6
            LDF  SYN0
            PUSH H
            LDF  SYN1
            PUSH H
            REL  l0
            REL  l1
            PUSH NONCE0
            PUSH NONCE1
            END

; COMMIT
commit:     LDF  LEN
            XOR  #CM_LEN
            BR   HNZ e_len
            LD   NONCE0
            OR   NONCE1
            BR   HZ e_state          ; ENROL first, in this power session
            CALL tag_in
            DIN  > ARG2
            DIN  > ARG0
            DIN  > ARG1
            CALL cw_check
            BR   HNZ cm_arg
            CTL  CLRZ
            BR   own_stmt
cm_auth:    BR   Z cm_fail
            CALL puf_key             ; the syndromes of ENROL must reconstruct to the tag that was signed
            BR   Z cm_puf
            CALL hlp_write           ; Z is sticky: one check after the three writes
            CALL rec_init
            CALL rec_store
            CALL rec_next
            BR   Z cm_io
            LD   #2
            HDR  #2
            LD   REC0
            UN   HSWAP
            UN   SHR16
            AND  #F_VAT
            BR   HNZ cm_done         ; vat mode has no K_host
            LDC  C_LHOST
            CALL kdf
            REL  l0
            REL  l1
cm_done:    CALL nonce_clr
            CALL lc_locked           ; provisioned: the next power session boots
            END
cm_fail:    CALL nonce_clr           ; a nonce is good for one attempt
            FAIL #E_AUTH
cm_arg:     CALL nonce_clr
            FAIL #E_ARG
cm_puf:     CALL nonce_clr
            FAIL #E_PUF
cm_io:      CTL  ZKEY
            CALL nonce_clr
            FAIL #E_RECORD_IO

; NONCE
nonce:      LDF  LEN
            BR   HNZ e_len
            CALL trng_nonce
            BR   Z e_trng
            CALL nonce_put
            LD   #2
            HDR  #2
            PUSH NONCE0
            PUSH NONCE1
            END

; REINIT
reinit:     LDF  LEN
            XOR  #RI_LEN
            BR   HNZ e_len
            LD   NONCE0
            OR   NONCE1
            BR   HZ e_state          ; NONCE first
            DIN  > ARG2
            DIN  > ARG0
            DIN  > ARG1
            CALL cw_check
            BR   HNZ cm_arg
            CTL  CLRZ
            BR   own_stmt
ri_auth:    BR   Z cm_fail
            CALL rec_init
            CALL rec_store
            CALL rec_next
            BR   Z cm_io
            CALL nonce_clr
            CALL lc_locked
            LD   #0
            HDR  #0
            END

; ---------------------------------------------------------------------------------------------
; LEASE and GATE
lease:      LDF  ARGLO
            XOR  #T_LEASE
            BR   HNZ e_arg
            LD   NONCE0
            OR   NONCE1
            BR   HZ e_state          ; no nonce: NONCE first
            BR   g_args
gate:       LDF  ARGLO
            XOR  #T_LEASE
            BR   HZ e_arg            ; a lease is not a transition of a running chip
g_args:     LDF  NWORDS
            SUB  #3
            BR   CY e_len
            DIN  > ARG0
            DIN  > ARG1
            DIN  > ARG2
            CTL  CLRZ
            LD   REC0                ; members to come: the threshold k
            UN   HSWAP
            UN   SHR16
            UN   SHR8
            AND  #0xFF               ; (a threshold of 0 is never stored; it would accept nothing here either)
            UN   HSWAP > CNT         ; and the lowest index allowed next: 0
g_member:   LDF  NWORDS
            BR   HZ g_bad
            DIN  > ARG3
            LD   ARG3
            UN   LO32
            SUB  CNT
            BR   CY g_bad            ; indices strictly increase: no member counts twice
            LD   ARG3
            UN   HSWAP
            UN   LO32
            ST   A0
            SUB  #17
            BR   NC g_bad            ; path length at most 16
            LD   A0
            UN   SHL1
            UN   SHL1
            ADD  #MB_WORDS
            ST   A0
            LDF  NWORDS
            SUB  A0
            BR   CY g_bad            ; the payload does not hold this member
            DIN  > PK0
            DIN  > PK1
            DIN  > NODE0
            DIN  > NODE1
            CALL mroot               ; the stated key is a member of the pinned committee
            LD   ROOT0
            CMP  l0
            LD   ROOT1
            CMP  l1
            CALL stmt_tr
            CALL sv
            CALL mroot               ; and the root its signature leads to is that member's
            LD   ROOT0
            CMP  l0
            LD   ROOT1
            CMP  l1
            LD   CNT
            UN   HSWAP
            UN   LO32
            SUB  #1
            UN   HSWAP > A1
            LD   ARG3
            UN   LO32
            ADD  #1
            BR   CY g_bad
            OR   A1 > CNT
            LD   A1
            BR   HNZ g_member
            BR   g_verdict
g_bad:      LD   #1
            CMP  #0
g_verdict:  CTL  VOK
            LDF  HDRW
            UN   SHR8
            AND  #0xFF
            XOR  #OP_LEASE
            BR   HZ ls_done
            BR   Z e_auth
            LDF  ARGLO
            ST   A0
            XOR  #T_EPOCH
            BR   HZ ga_epoch
            LD   A0
            XOR  #T_RETIRE
            BR   HZ ga_retire
            LD   A0
            XOR  #T_ROTATE
            BR   HZ ga_rotate
            BR   e_arg
ga_epoch:   LD   REC1                ; the epoch only moves forward
            UN   HSWAP
            UN   LO32
            SUB  ARG0
            BR   NC e_arg
            CALL t_epoch
            BR   ga_done
ga_retire:  CALL t_retire
            BR   Z e_record_io
            CTL  ZKEY                ; a retired chip holds no key
            CALL lc_locked
            BR   ga_rsp
ga_rotate:  LD   ARG2
            AND  #0xFF
            BR   HZ e_arg            ; a threshold of 0 would accept nothing
            CALL t_rotate
ga_done:    BR   Z e_record_io
ga_rsp:     LD   #1
            HDR  #1
            PUSH REC0
            END

ls_done:    BR   Z ls_fail
            LD   ARG0
            UN   HSWAP
            UN   LO32
            SUB  ARG0
            BR   CY ls_arg           ; bound below base
            CALL lease_set           ; counters jump to the granted base
            BR   Z ls_io
            CALL nonce_clr
            CALL auth_z
            CALL lc_ready
            LD   #2
            HDR  #2
            PUSH REC0
            PUSH REC1
            END
ls_fail:    CALL nonce_clr           ; a nonce is good for one attempt
            FAIL #E_AUTH
ls_arg:     CALL nonce_clr
            FAIL #E_ARG
ls_io:      CALL nonce_clr
            FAIL #E_RECORD_IO
