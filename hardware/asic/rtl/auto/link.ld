ENTRY(_start)
SECTIONS {
  . = 0x200000;
  .firmware : { *(.text.start) *(.text .text.*) . = ALIGN(8); *(.srodata* .rodata*) . = ALIGN(8); }
  .mutable : { *(.data* .sdata* .bss* .sbss* COMMON) }
  ASSERT(SIZEOF(.mutable) == 0, "Verifier mutable data belongs on the SRAM stack")
  /DISCARD/ : { *(.comment .riscv.attributes .eh_frame*) }
}
