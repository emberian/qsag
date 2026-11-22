; Key range (addresses 1..79): the only addresses at which KEYWR, PMOV and the CTL functions LC, AUTH,
; PUFE, PUFR and SYNW decode. Everything here is a subroutine of the lifecycle commands in life.uc.

; The lifecycle register. READY needs the verdict latch and is reachable from RESET and LEASE only.
lc_blank:   CTL  LC #LC_BLANK ret
lc_orphan:  CTL  LC #LC_ORPHAN ret
lc_lease:   CTL  LC #LC_LEASE ret
lc_ready:   CTL  LC #LC_READY ret
lc_locked:  CTL  LC #LC_LOCKED ret

; auth_z: set the verdict latch if Z is clear.
auth_z:     CTL  AUTH ret

; syn_load: syndrome register <- A0, A1 (public helper data).
syn_load:   LD   A0
            CTL  SYNW #0
            LD   A1
            CTL  SYNW #1 ret

; puf_tag: lanes 0, 1 <- TurboSHAKE256(w || "DREGGPCK", D = 0x29)[0..15], w = the PUF response register.
puf_tag:    WIPE #W_LANES
            LDC  C_LPCK
            ST   l4
            LD   #D_PUFCHK
            ST   l5
            LDC  C_PAD
            ST   l16
            PMOV #0 > l0
            PMOV #1 > l1
            PMOV #2 > l2
            PMOV #3 > l3
            KEC  12 ret

; puf_enrol: measure the array; syndromes to the register; check tag in lanes 0, 1.
puf_enrol:  CTL  PUFE
            BR   Z e_puf
            BR   puf_tag

; puf_key: reconstruct with the syndrome register and compare the check tag with TAG0, TAG1 before any
; key row is written. On a match: verdict latch, and
;   K_dev = TurboSHAKE256(w || "DREGGKDV" || NONCE0, NONCE1, D = 0x2A)[0..31].
; Z is set on failure.
puf_key:    CTL  PUFR
            CALL puf_tag
            LD   TAG0
            CMPT l0
            LD   TAG1
            CMPT l1
            BR   Z pk_ret
            CTL  AUTH
            WIPE #W_LANES
            LDC  C_LKDV
            ST   l4
            LD   NONCE0
            ST   l5
            LD   NONCE1
            ST   l6
            LD   #D_KDEV
            ST   l7
            LDC  C_PAD
            ST   l16
            PMOV #0 > l0
            PMOV #1 > l1
            PMOV #2 > l2
            PMOV #3 > l3
            KEC  12
            SETX #0
pk_wr:      LD   l0+X
            KEYWR > k_dev0+X x+
            BXNE #4 pk_wr
            WIPE #W_LANES
pk_ret:     RET
