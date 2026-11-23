if [[ -n ${HDK_SHELL_DIR:-} ]]; then
  interfaces=$HDK_SHELL_DIR/design/interfaces
  ddr_stub=$HDK_SHELL_DIR/design/sh_ddr/sh_ddr.stub.sv
else
  interfaces=verif/hdk_stub
  ddr_stub=$interfaces/sh_ddr.stub.sv
fi
