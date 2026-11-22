; From here on: ordinary ROM (addresses 128 and up).
.org REC_END

; shared error exits
e_opcode:   FAIL #E_OPCODE
e_len:      FAIL #E_LEN
e_trng:     FAIL #E_TRNG
e_auth:     FAIL #E_AUTH
e_record_io: FAIL #E_RECORD_IO
e_state:    FAIL #E_STATE
e_arg:      FAIL #E_ARG
e_class:    FAIL #E_CLASS
e_puf:      FAIL #E_PUF

; PING (0x01): chip id, status word, two reserved words. No raw TRNG word is returned.
.entry 0x01 ping any

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
