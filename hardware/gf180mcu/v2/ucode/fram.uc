; Record range (addresses 64..127): the only addresses at which FRAM instructions decode.
;
; A record is three words: counter, tag[0], tag[1], with
;   tag = TurboSHAKE256(K_dev || counter || "QSAGNIFR", D = 0x1F)[0..15].
; K_dev is the device secret (PUF-derived; never on the host link). The MACed lifecycle record of
; ARCHITECTURE.md 3.1 replaces this format in stage 3.
.org KEY_END

; fram_tag: lanes 0, 1 <- tag of the counter in A0.
fram_tag:   WIPE #W_LANES
            KMOV k_dev0 > l0
            KMOV k_dev1 > l1
            KMOV k_dev2 > l2
            KMOV k_dev3 > l3
            LD   A0
            ST   l4
            LDC  C_FRAM
            ST   l5
            LD   #D_FRAM
            ST   l6
            LDC  C_PAD
            ST   l16
            KEC  12 ret

; fram_write: record (A0, lane 0, lane 1) -> slot H[0]. Lanes 0 and 1 hold the tag (fram_tag).
fram_write: FRAM WSTART
            FRAM WWORD A0
            FRAM WWORD l0
            FRAM WWORD l1
            FRAM DONE ret

; fram_check: read slot H[0] back; Z is set if it differs from (A0, lane 0, lane 1).
fram_check: FRAM RSTART
            FRAM RWORD
            CMP  A0
            FRAM RWORD
            CMPT l0
            FRAM RWORD
            CMPT l1
            FRAM DONE ret

; anchor_read: slot H[0] -> A0 = counter | 1 << 32 if the record is authentic, else 0. Z is left clear.
anchor_read:
            FRAM RSTART
            FRAM RWORD > A0
            CALL fram_tag
            CTL  CLRZ
            FRAM RWORD
            CMPT l0
            FRAM RWORD
            CMPT l1
            FRAM DONE
            LD   A0
            UN   HI32
            CMP  #0                 ; a counter above 32 bits is not a record
            BR   Z ar_bad
            LD   #1
            UN   HSWAP
            XOR  A0 > A0 ret
ar_bad:     CTL  CLRZ
            LD   #0
            ST   A0 ret
