# PUF key array: placement and routing requirements

For the physical-design lane (`hardware/gf180mcu/v2/phys/`, in particular `floorplan/puf_array.tcl`).
Source of every number: `scratch/lanes/fable-physics-fixes.last.md` section 2 and the scripts in this
directory. Labels: [S] simulated here, [A] assumed, [D] derived.

## Why

- Random spread of one ring: sigma_f/f = 0.18 %; of a ring pair: 0.258 %; of a quad: 0.368 % [S, ngspice
  Monte Carlo with the foundry mismatch model, 512 rings].
- Any layout-determined difference between the compared rings is the same on every die and therefore
  known to an attacker. For min-entropy 0.95 bit per response bit it must stay below 0.044 sigma:
  **0.011 % of frequency = 6 aF on one ring node = 0.8 mV of supply** for a pair [S].
- Extracted with Magic from the PDK cells [S, `extract/`]: the capacitance of a `nand2_1` output node
  changes by **73 aF** when the right-hand neighbour is a filler instead of another `nand2_1`, by **128 aF**
  at a row end, by 18-30 aF when the neighbours are a buffer and a flip-flop. Each of these alone is 3 to
  20 times the budget.
- A routed wire is about 0.1-0.2 fF per um [A]: one micrometre of difference in a ring net is 15-30 times
  the budget.

So the rings must be identical by construction, including their wires and everything within a few
micrometres, and the comparison must cancel what cannot be made identical.

## R0. Changes needed outside the floorplan (for the RTL lane; listed so the floorplan can assume them)

- R0.1 Each ring gets an **output isolation buffer inside its slot** (`buf_2`, kept): today the ring node
  `osc` itself is routed to the multiplexer, so every ring carries a different wire on a ring node.
- R0.2 One response bit is taken from **four rings in one row** (a quad), not from two: with ring counts
  c1..c4 at slots 1..4 of the quad, bit = sign((c1 + c4) - (c2 + c3)). This cancels any offset that
  alternates between neighbouring slots and any linear gradient, in space and (measuring in the order
  1, 2, 3, 4) in time. 252 bits need 1008 rings. If the area cannot be found, the fallback is pairs in
  one row with five BCH blocks (630 rings) and a claim of 0.90 bit per bit; every rule below applies
  unchanged, with "quad" read as "pair".
- R0.3 **One ring enabled at a time**, same counter, same window for all four. No two rings of the array
  oscillate together (they would pull each other through the shared rail).
- R0.4 The characterisation array (decision D13) is built from the same slots, in the same block, under
  the same rules, with at least 16 quads in interior positions.

## R1. The ring slot

- R1.1 One slot = enable buffer (`buf_2`), five `nand2_1`, output buffer (`buf_2`), one well tap, in this
  order, abutted, in **one row**. 8 + 25 + 8 + 2 sites = 43 sites of 0.56 um = 24.08 um [D; adjust the tap
  width to the cell actually used]. No spacing sites inside a slot.
- R1.2 Slots abut each other at a constant pitch along the row with nothing in between (no filler, no
  gap). The tap inside the slot replaces the template's staggered taps, as the present script already
  arranges.
- R1.3 **All slots of the array have the same orientation as placed in their row, and the rings of one
  quad are in the same row.** Do not compare a ring with one in a mirrored row: mask overlay errors act
  in opposite directions on mirrored cells and bias all bits of a die together. (The present script puts
  ring A and ring B of a pair in adjacent rows, which are mirror images; this is the one placement rule
  that has to change.)
- R1.4 Rows of the array may alternate orientation as usual. A quad occupies four consecutive slots of
  one row; quads follow each other without gap.

## R2. Surroundings

- R2.1 **Dummy slots**: at both ends of every array row, two complete slots (same cells, enable tied
  low, outputs unconnected). No quad uses them.
- R2.2 **Dummy rows**: above the top row and below the bottom row of the array, one full row of the same
  slots at the same x positions (tied off). If the array is split into bands with routing channels
  between them, every band gets its own dummy rows, so that the vertical neighbour of every used slot is
  an identical slot at the same x.
- R2.3 Keep-out: no other standard cell, tap, decap or filler within the array box including its
  dummies; no macro, pad cell or I/O strap closer than 20 um to the box [A]; the array stays in the
  quiet north-west corner already chosen.
- R2.4 Metal fill: exclude the array box from automatic fill on Metal1-Metal3, or use a fill pattern that
  repeats with the slot pitch. Check after fill (R5).

## R3. Wires

- R3.1 **Ring nets are pre-routed from one template.** The five nets between consecutive `nand2_1` and
  the net from the last stage back to the first (six nets, plus the two short nets to the buffers) are
  created by script as fixed wires, identical shapes relative to the slot origin in every slot (same
  layers, same tracks, same via positions; in mirrored rows the mirrored template), and marked fixed
  before global routing. Use Metal1/Metal2 only.
- R3.2 **Obstruct Metal1, Metal2 and Metal3 for all other signal nets over the whole array box**, dummies
  included. Enable inputs and buffered outputs are reached by one vertical Metal3 stub per slot at a
  fixed x within the slot (part of the template), continued on Metal4 or above.
- R3.3 Metal4 and Metal5 over the array carry only the power straps of R4 and the enable/output
  trunks; trunks run in the row direction over the dummy rows or in channels beside the bands, not
  over used slots. Where a trunk must cross used slots, it crosses every slot of that row at the same
  relative position (a straight wire along the whole row does this).
- R3.4 No clock, no pad signal and no net that toggles during a PUF measurement is routed over or
  within 10 um of the array box on any layer [A].

## R4. Supply

- R4.1 The Metal1 rails of all array rows are continuous through used and dummy slots.
- R4.2 Vertical power straps cross the array at a pitch equal to the slot pitch or an integer multiple
  that divides the quad (one or two slots), at the same x within every slot they cross, with the same
  via stack to the rails in every row. No strap may be dropped, shifted or narrowed inside the box.
- R4.3 Target, to be checked with a static IR analysis with one ring drawing 0.25 mA [S]: the supply
  (VDD minus VSS) seen by the four rings of any quad, each measured while it alone is active, differs
  by less than **0.2 mV** [D: 0.011 sigma of a pair]. Equivalent rule of thumb: supply-path resistance
  from the strap grid to each ring equal within 0.8 ohm.
- R4.4 The enable decoder, the multiplexer and the counters sit outside the array box and its keep-out
  and take their supply from straps that do not pass through the array, as far as the grid allows.

## R5. Checks to run on the placed and routed block

1. Structural: every used slot has the same cell sequence and orientation as its row neighbours; every
   quad lies in one row; dummy slots and rows present (extend the metrics already written by
   `puf_array.tcl`).
2. Wire identity: for every slot, the set of shapes on Metal1-Metal3 inside the slot box (after routing
   and fill), translated to the slot origin, equals the template's set. Any difference is a failure.
3. Extraction: Magic `extract all` on the array with coupling, `ext2spice cthresh 0`
   (`extract/env_cap_extract.tcl` shows the commands; set `extract path` to a scratch directory, by
   default Magic writes `.ext` files next to the PDK cells). For every quad, with C(k, n) the total
   capacitance of ring node n in slot k: |C(1,n) + C(4,n) - C(2,n) - C(3,n)| <= 6 aF for every node n,
   and |C(k,n) - C(k+1,n)| <= 20 aF for neighbouring slots [D]. Then simulate the extracted rings of a
   few quads without mismatch (`run_puf_mc.py sens` shows the deck): the quad combination of the four
   frequencies must be below 0.011 % of f.
4. IR: R4.3.
5. Report per-quad numbers, not only pass/fail; the entropy account uses the worst one.

## What these rules do not cover

Across-field gradients with curvature above about 10 %/mm^2, proximity effects that differ between the
first and the fourth slot of a quad for reasons other than their neighbours, and ageing. They are bounded
on silicon with the characterisation array (report section 2.5).
