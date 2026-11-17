; Provisioning range (addresses 1..63): the only addresses at which KEYWR, CTL SETKV, CTL AUTH and
; CTL NONCE decode.
;
; Stage 1 stand-in for COMMIT / REINIT of ARCHITECTURE.md 3.2: an owner-authorised key import.
;   PROVISION_NONCE (0x43): returns a fresh 128-bit nonce. Needs the entropy interface.
;   KEYLOAD (0x40): payload K_host[2], SK.seed[2], SK.prf[2], authorisation[2].
;       flags bit 0 must be 1; bit 1: initialise both anchor slots to counter 0;
;       bit 2: the key is counted (KA_COUNTED).
;       The owner root authorises (nonce, TurboSHAKE256(header || six key words, D = 0x22)[0..31]).
;       One attempt per nonce. Both commands are refused by the dispatcher once a key is valid, and
;       without the device secret.
.entry 0x43 prov_nonce prov
.entry 0x40 keyload prov

prov_nonce: LDF  LEN
            BR   HNZ e_len
            CTL  NONCE
            BR   Z e_trng
            LD   #2
            HDR  #2
            LDF  NONCE0
            PUSH H
            LDF  NONCE1
            PUSH H
            END

keyload:    LDF  LEN
            XOR  #64
            BR   HNZ e_len
            LDF  FLAGS
            AND  #0xF9
            XOR  #1
            BR   HNZ e_opcode        ; only host-imported keys in this stage
            LDF  HDRW                ; statement digest
            ST   l0
            SETX #0
kl_in:      DIN  > t0+X
            ST   l1+X x+
            BXNE #6 kl_in
            LD   #D_PROV
            ST   l7
            LDC  C_PAD
            ST   l16
            KEC  12
            CTL  AUTH                ; consumes the two authorisation words and the nonce
            BR   Z e_auth
            LDF  FLAGS
            AND  #2
            BR   HZ kl_key0
            LD   #0                  ; anchor: counter 0 in both slots, each read back, before any key is stored
            ST   A0
            CALL fram_tag
            LD   #0
            CALL fram_write
            LD   #0
            CALL fram_check
            LD   #1
            CALL fram_write
            LD   #1
            CALL fram_check
            BR   Z e_anchor_io
kl_key0:    SETX #0
kl_key:     LD   t0+X
            KEYWR > k_host0+X x+
            BXNE #6 kl_key
            LDF  FLAGS
            UN   SHR1
            UN   SHR1
            AND  #KA_COUNTED
            CTL  SETKV               ; key valid, attribute = H
            LD   #0
            HDR  #0
            END
