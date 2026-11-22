# GF180MCU mapped enclave

The staged flow elaborates the physical PUF and CoSO cell instances, maps the resident ROM and core, inserts bounded fanout trees on asynchronous reset pins, and checks the delivered netlist with both foundry SRAMs in OpenSTA. It requires the build container's Yosys/Slang, ABC and OpenSTA environment and the 7T5V0 and SRAM Liberty views.

Use the reproduction commands and area accounting in the [staged report](../../../REPORT.md). The post-map gate simulation takes the same mapped file and verifies its checksum before compilation. [Synthesis and STA](run_gf180_synth_sta.sh) · [Four-state simulation](../gl/run_gl.sh)
