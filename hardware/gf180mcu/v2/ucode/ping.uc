; From here on: ordinary ROM (addresses 128 and up).
.org REC_END

; shared error exits
e_opcode:   FAIL #E_OPCODE
e_len:      FAIL #E_LEN
e_trng:     FAIL #E_TRNG
e_auth:     FAIL #E_AUTH
e_anchor_io: FAIL #E_ANCHOR_IO

; PING (0x01): chip id, status word, two reserved words. No raw TRNG word is returned.
.entry 0x01 ping diag

ping:       LDF  LEN
            BR   HNZ e_len
            LD   #4
            HDR  #4
            LDC  C_CHIPID
            PUSH H
            LDF  STATUS
            PUSH H
            LD   #0
            PUSH H
            PUSH H
            END
