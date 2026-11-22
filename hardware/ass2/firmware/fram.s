; SPI mode 0 FM25W256, two-byte big-endian address. R4 address, R5 scratch pointer, R6 count.
fram_read:
    ADDI R11, RA, 0
    MOVZ20 R10, 0
    MOVZ20 R8, 3
    J fram_address
fram_write:
    ADDI R11, RA, 0
    MOVZ20 R8, 6
    CALL spi_byte
    CALL spi_cs_hi
    MOVZ20 R10, 1
    MOVZ20 R8, 2
fram_address:
    CALL spi_byte
    SHRI R8, R4, 8
    CALL spi_byte
    ANDI R8, R4, 255
    CALL spi_byte
fram_bytes:
    MOVZ20 R8, 0
    BEQZ R10, fram_clock
    LDBU R8, [R5]
fram_clock:
    CALL spi_byte
    BNEZ R10, fram_next
    STB [R5], R8
fram_next:
    ADDI R5, R5, 1
    ADDI R6, R6, -1
    BNEZ R6, fram_bytes
    CALL spi_cs_hi
    JALR ZERO, R11, 0
spi_cs_hi:
    MOVZ20 R8, 256
    ST64 [R12], R8
    RET
spi_byte:
    ORI R8, R8, 512
    ST64 [R12], R8
spi_wait:
    LD64 R9, [R12+8]
    ANDI R9, R9, 1
    BNEZ R9, spi_wait
    LD64 R8, [R12]
    RET
