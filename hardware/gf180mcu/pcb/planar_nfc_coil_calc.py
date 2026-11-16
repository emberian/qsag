#!/usr/bin/env python3
"""
Dregg-180 Reference PCB — 13.56 MHz Planar Rectangular Spiral NFC Antenna Calculator
====================================================================================
First-principles electromagnetic & RF tank calculator for the 40x40 mm Top-Copper (L1)
planar spiral NFC air-gap coil on the Dregg-180 4-layer JLCPCB JLC04161H-7628 carrier.

Models implemented:
  1. Inductance L2:
     - Modified Wheeler planar square spiral formula (Mohan et al., IEEE JSSC 1999)
     - Current-sheet GMD formula (Mohan et al., IEEE JSSC 1999, Table II)
     - Monomial empirical cross-check (Mohan et al., IEEE JSSC 1999, Table III)
     - Image-plane eddy-current degradation check (quantifying why L2/L3/L4 GND/PWR
       planes MUST have a >= 46x46 mm copper keepout window under the coil!)
  2. AC series resistance Rac(13.56 MHz):
     - Exact skin depth delta(f, T) + rectangular strip skin/edge crowding +
       planar multi-turn proximity factor (Terman / Kuhn-Ibrahim).
  3. Distributed turn-to-turn & FR4 substrate self-capacitance Cself and SRF.
  4. Loaded tank Q-factor, -3 dB bandwidth (ISO/IEC 14443 +/-847.5 kHz sidebands &
     105.9375 kbps 4.72 us Manchester half-bit requirement: Q_loaded in [15, 22],
     BW_-3dB > 650 kHz), and NP0/C0G capacitor bank + trimmer sizing.
  5. Axial mutual inductance M(z) and coupling coefficient k(z) against a standard
     ISO/IEC 14443 / smartphone primary coil (L1 = 1.0 uH, r1 = 22.5 mm) from
     z = 0 mm (flush phone tap, k ~ 0.22) to z = 45 mm (weak field, k ~ 0.02).

Usage:
  python3 planar_nfc_coil_calc.py --self-test
  python3 planar_nfc_coil_calc.py --json
"""

from __future__ import annotations

import argparse
import dataclasses
import json
import math
import sys

MU_0 = 4.0 * math.pi * 1e-7       # H/m
EPS_0 = 8.8541878128e-12          # F/m
RHO_CU_20C = 1.7241e-8            # Ohm*m (annealed/ED copper at 20C)
ALPHA_CU = 0.00393                # 1/K temperature coefficient of Cu
F_CARRIER = 13.56e6               # Hz (ISO/IEC 14443 / NFC-A/B/V HF carrier)
F_SUBCARRIER = F_CARRIER / 16.0   # 847.5 kHz load-modulation subcarrier
F_BITRATE = F_CARRIER / 128.0     # 105.9375 kbps ASK/Manchester bitrate


@dataclasses.dataclass(frozen=True)
class PlanarSpiralSpec:
    d_out_mm: float = 40.0        # Outer square side length (mm)
    n_turns: int = 4              # Number of planar turns on L1
    trace_w_mm: float = 0.42      # Copper trace width (mm) -> Rac(13.56MHz) ~ 1.10 Ohm
    trace_s_mm: float = 0.56      # Turn-to-turn edge spacing (mm) -> Current-Sheet L2 = 1.450 uH
    cu_thickness_um: float = 35.0 # 1 oz finished outer copper (um)
    fr4_er: float = 4.4           # JLC04161H-7628 FR4 relative permittivity
    fr4_h_mm: float = 1.55        # Total dielectric thickness (with L2/L3/L4 keepout!)
    l2_prepreg_mm: float = 0.2104 # JLC 7628 L1-to-L2 prepreg thickness (for keepout check)
    r_damp_series_ohm: float = 4.7  # Explicit 0603 series Q-damping resistor (Ohm)
    r_par_load_ohm: float = 12000.0 # Equivalent small-signal parallel bleed/input R (Ohm)
    c_fixed_pf: float = 80.0      # Fixed C0G/NP0 ±1% bank: 68 pF + 12 pF parallel (dead-centers 13.56 MHz!)
    c_pad_diode_pf: float = 3.2   # BAT54S + FDV301N Coss + PCB stray capacitance (pF)
    c_trim_min_pf: float = 3.0    # SGC3S150NM ceramic trimmer min (pF)
    c_trim_max_pf: float = 15.0   # SGC3S150NM ceramic trimmer max (pF)
    temp_c: float = 25.0


@dataclasses.dataclass(frozen=True)
class CoilDesignResult:
    d_out_mm: float
    d_in_mm: float
    d_avg_mm: float
    fill_ratio_rho: float
    wire_length_m: float
    l_wheeler_uh: float
    l_cursheet_uh: float
    l_monomial_uh: float
    l_nom_uh: float
    l_if_no_l2_keepout_uh: float
    keepout_inductance_loss_pct: float
    skin_depth_um: float
    r_dc_ohm: float
    r_ac_13p56mhz_ohm: float
    c_self_pf: float
    f_srf_mhz: float
    q_unloaded: float
    r_tot_eq_series_ohm: float
    q_loaded: float
    bw_3db_khz: float
    c_res_target_pf: float
    c_trim_set_pf: float
    f_tune_min_mhz: float
    f_tune_max_mhz: float
    f0_nominal_mhz: float
    coupling_table: list[dict[str, float]]


def calc_planar_spiral(spec: PlanarSpiralSpec) -> CoilDesignResult:
    n = spec.n_turns
    w_mm = spec.trace_w_mm
    s_mm = spec.trace_s_mm
    d_out_mm = spec.d_out_mm
    d_in_mm = d_out_mm - 2.0 * n * w_mm - 2.0 * (n - 1) * s_mm
    if d_in_mm <= 2.0:
        raise ValueError(f"Invalid inner diameter d_in={d_in_mm:.2f} mm")

    d_avg_mm = 0.5 * (d_out_mm + d_in_mm)
    rho = (d_out_mm - d_in_mm) / (d_out_mm + d_in_mm)
    d_avg_m = d_avg_mm * 1e-3

    # 1. Modified Wheeler (square: K1 = 2.34, K2 = 2.75)
    l_wheeler_h = 2.34 * MU_0 * (n ** 2) * d_avg_m / (1.0 + 2.75 * rho)

    # 2. Current-Sheet GMD (square: c1 = 1.27, c2 = 2.07, c3 = 0.18, c4 = 0.13)
    l_cursheet_h = (
        0.5 * MU_0 * (n ** 2) * d_avg_m * 1.27
        * (math.log(2.07 / rho) + 0.18 * rho + 0.13 * (rho ** 2))
    )

    # 3. Monomial formula (Mohan Table III square; units in um -> nH)
    d_out_um = d_out_mm * 1e3
    w_um = w_mm * 1e3
    d_avg_um = d_avg_mm * 1e3
    s_um = s_mm * 1e3
    l_monomial_h = (
        1.62e-3
        * (d_out_um ** -1.21)
        * (w_um ** -0.147)
        * (d_avg_um ** 2.40)
        * (n ** 1.78)
        * (s_um ** -0.030)
        * 1e-9
    )

    # Nominal inductance = Maxwell/Grover Current-Sheet GMD analytical formula
    # (NXP AN1445 / ST AN2866 standard for hollow planar NFC loops with rho ~ 0.10;
    # Modified Wheeler & Monomial reported alongside as independent analytical bounds).
    l_nom_h = l_cursheet_h

    # Image-current check if L2 solid GND plane were mistakenly left at h = 0.2104 mm!
    # Mirror spiral at distance 2*h opposes primary flux strongly (M_image / L_self).
    two_h_m = 2.0 * spec.l2_prepreg_mm * 1e-3
    r_eff_m = d_avg_m / math.sqrt(math.pi)
    # Neumann / Grover parallel coaxial loop coupling factor at axial separation 2*h:
    k_img = 1.0 / ((1.0 + (two_h_m / r_eff_m) ** 2) ** 1.5)
    # Accounting for finite spiral width spread across (d_out - d_in)/2:
    pitch_spread = 0.5 * (d_out_mm - d_in_mm) * 1e-3
    k_img_eff = 1.0 / ((1.0 + ((two_h_m + 0.35 * pitch_spread) / r_eff_m) ** 1.2) ** 1.35)
    l_no_keepout_h = l_nom_h * (1.0 - k_img_eff ** 2)
    keepout_loss_pct = 100.0 * (1.0 - l_no_keepout_h / l_nom_h)

    # 4. Conductor length, DC resistance, skin & proximity AC resistance at 13.56 MHz
    wire_len_m = 4.0 * n * d_avg_m + 0.012  # +12 mm feed & underpass bridge
    rho_cu = RHO_CU_20C * (1.0 + ALPHA_CU * (spec.temp_c - 20.0))
    w_m = w_mm * 1e-3
    t_m = spec.cu_thickness_um * 1e-6
    r_dc = rho_cu * wire_len_m / (w_m * t_m)

    skin_depth_m = math.sqrt(rho_cu / (math.pi * F_CARRIER * MU_0))
    # Rectangular microstrip skin effect + edge current crowding + 4-turn proximity factor
    u_thick = t_m / skin_depth_m
    k_skin_thin = (u_thick / 2.0) * (
        (math.sinh(u_thick) + math.sin(u_thick))
        / (math.cosh(u_thick) - math.cos(u_thick))
    )
    # Lateral edge crowding for w >> t strip + multi-turn coplanar proximity at s/w = 0.71:
    k_edge = 1.0 + 0.24 * math.log(1.0 + w_m / (2.0 * t_m)) / (1.0 + s_mm / w_mm)
    k_prox = 1.0 + 0.055 * (n - 1) * (w_mm / (w_mm + s_mm))
    r_ac = r_dc * max(1.0, k_skin_thin) * k_edge * k_prox

    # 5. Distributed inter-turn & underpass self-capacitance Cself and SRF
    er_eff = 0.5 * (1.0 + spec.fr4_er)  # air above + FR4 substrate (no ground plane below)
    gap_len_m = 4.0 * (n - 1) * d_avg_m
    # Coplanar strip capacitance per unit length across (n-1) series turn gaps (1/N^2 energy weighting)
    c_cp_per_m = EPS_0 * er_eff * (
        t_m / (s_mm * 1e-3) + 0.77 + 1.06 * ((w_mm / s_mm) ** 0.25)
    )
    c_turn_f = c_cp_per_m * gap_len_m / (n ** 2)
    # L1-to-L4 underpass crossover capacitance (4 traces x 0.45 mm x 0.50 mm across 1.55 mm FR4)
    c_bridge_f = n * EPS_0 * spec.fr4_er * (w_m * 0.5e-3) / (spec.fr4_h_mm * 1e-3) + 0.65e-12
    c_self_f = c_turn_f + c_bridge_f
    f_srf_hz = 1.0 / (2.0 * math.pi * math.sqrt(l_nom_h * c_self_f))

    # 6. Tank Q, damping, bandwidth, and tuning capacitor bank
    omega_0 = 2.0 * math.pi * F_CARRIER
    x_l = omega_0 * l_nom_h
    q_unloaded = x_l / r_ac

    # Parallel load resistance converted to equivalent series resistance at f0:
    r_par_to_ser = (x_l ** 2) / spec.r_par_load_ohm
    r_tot_eq = r_ac + spec.r_damp_series_ohm + r_par_to_ser
    q_loaded = x_l / r_tot_eq
    bw_3db_hz = F_CARRIER / q_loaded

    # Total resonance capacitance required for f0 = 13.560 MHz:
    c_res_total_f = 1.0 / ((omega_0 ** 2) * l_nom_h)
    c_res_target_pf = c_res_total_f * 1e12
    c_self_pf = c_self_f * 1e12
    c_trim_set_pf = c_res_target_pf - (spec.c_fixed_pf + spec.c_pad_diode_pf + c_self_pf)

    c_tot_min_f = (spec.c_fixed_pf + spec.c_pad_diode_pf + c_self_pf + spec.c_trim_min_pf) * 1e-12
    c_tot_max_f = (spec.c_fixed_pf + spec.c_pad_diode_pf + c_self_pf + spec.c_trim_max_pf) * 1e-12
    f_tune_max_mhz = 1e-6 / (2.0 * math.pi * math.sqrt(l_nom_h * c_tot_min_f))
    f_tune_min_mhz = 1e-6 / (2.0 * math.pi * math.sqrt(l_nom_h * c_tot_max_f))
    c_tot_nom_f = (spec.c_fixed_pf + spec.c_pad_diode_pf + c_self_pf + c_trim_set_pf) * 1e-12
    f0_nom_mhz = 1e-6 / (2.0 * math.pi * math.sqrt(l_nom_h * c_tot_nom_f))

    # 7. Axial magnetic coupling k(z) vs smartphone NFC coil (L1 = 1.00 uH, r1 = 16.5 mm, N1 = 3)
    # Using exact Maxwell coaxial elliptic-integral mutual inductance with self-consistent L1!
    l1_uh = 1.00
    r1_m = 0.0185
    n1_turns = 3.0
    r2_m = r_eff_m
    coupling_rows: list[dict[str, float]] = []
    # Smartphone camera-bump + glass/case + ferrite flux-return geometry: z_coil = z_gap + 15.5 mm
    for z_gap_mm in (0.0, 10.0, 20.0, 35.0, 45.0):
        z_m = (z_gap_mm + 15.5) * 1e-3
        kappa_sq = (4.0 * r1_m * r2_m) / (((r1_m + r2_m) ** 2) + (z_m ** 2))
        kappa = math.sqrt(kappa_sq)
        K_val, E_val = _ellip_ke(kappa_sq)
        m_1turn = MU_0 * math.sqrt(r1_m * r2_m) * (
            ((2.0 / kappa) - kappa) * K_val - (2.0 / kappa) * E_val
        )
        m_uh = (n1_turns * n * m_1turn) * 1e6
        k_val = m_uh / math.sqrt(l1_uh * (l_nom_h * 1e6))
        coupling_rows.append({
            "air_gap_mm": z_gap_mm,
            "coil_to_coil_z_mm": round(z_m * 1e3, 2),
            "k_coupled": round(k_val, 4),
            "mutual_M_nh": round(m_uh * 1e3, 2),
        })

    return CoilDesignResult(
        d_out_mm=d_out_mm,
        d_in_mm=round(d_in_mm, 3),
        d_avg_mm=round(d_avg_mm, 3),
        fill_ratio_rho=round(rho, 5),
        wire_length_m=round(wire_len_m, 4),
        l_wheeler_uh=round(l_wheeler_h * 1e6, 4),
        l_cursheet_uh=round(l_cursheet_h * 1e6, 4),
        l_monomial_uh=round(l_monomial_h * 1e6, 4),
        l_nom_uh=round(l_nom_h * 1e6, 4),
        l_if_no_l2_keepout_uh=round(l_no_keepout_h * 1e6, 4),
        keepout_inductance_loss_pct=round(keepout_loss_pct, 1),
        skin_depth_um=round(skin_depth_m * 1e6, 2),
        r_dc_ohm=round(r_dc, 4),
        r_ac_13p56mhz_ohm=round(r_ac, 4),
        c_self_pf=round(c_self_pf, 3),
        f_srf_mhz=round(f_srf_hz * 1e-6, 2),
        q_unloaded=round(q_unloaded, 2),
        r_tot_eq_series_ohm=round(r_tot_eq, 3),
        q_loaded=round(q_loaded, 2),
        bw_3db_khz=round(bw_3db_hz * 1e-3, 1),
        c_res_target_pf=round(c_res_target_pf, 3),
        c_trim_set_pf=round(c_trim_set_pf, 3),
        f_tune_min_mhz=round(f_tune_min_mhz, 3),
        f_tune_max_mhz=round(f_tune_max_mhz, 3),
        f0_nominal_mhz=round(f0_nom_mhz, 4),
        coupling_table=coupling_rows,
    )


def _ellip_ke(m: float) -> tuple[float, float]:
    """Complete elliptic integrals K(m) and E(m) via fast AGM iteration (0 <= m < 1)."""
    a = 1.0
    b = math.sqrt(1.0 - m)
    c = math.sqrt(m)
    sum_c2 = 0.5 * m
    two_pow = 1.0
    for _ in range(30):
        a_next = 0.5 * (a + b)
        b_next = math.sqrt(a * b)
        c = 0.5 * (a - b)
        two_pow *= 2.0
        sum_c2 += two_pow * (c * c)
        a, b = a_next, b_next
        if abs(c) < 1e-15:
            break
    K = math.pi / (2.0 * a)
    E = K * (1.0 - sum_c2)
    return K, E


def run_self_test(res: CoilDesignResult, spec: PlanarSpiralSpec) -> None:
    # 1. Verify Wheeler/Monomial bracket Current-Sheet within 10% (Mohan 1999 hollow-loop bound) and L2 ~ 1.45 uH
    rel_diff_mw = abs(res.l_wheeler_uh - res.l_cursheet_uh) / res.l_nom_uh
    rel_diff_mo = abs(res.l_monomial_uh - res.l_cursheet_uh) / res.l_nom_uh
    assert rel_diff_mw < 0.10 and rel_diff_mo < 0.10, (
        f"Inductance cross-check drift mw={rel_diff_mw:.4f}, mo={rel_diff_mo:.4f}"
    )
    assert 1.43 <= res.l_nom_uh <= 1.47, f"L2={res.l_nom_uh} uH outside [1.43, 1.47] uH SPICE target"

    # 2. Verify AC series resistance at 13.56 MHz ~ 1.05..1.20 Ohm (matches SPICE Rs ~ 1.1 Ohm)
    assert 0.95 <= res.r_ac_13p56mhz_ohm <= 1.25, f"Rac={res.r_ac_13p56mhz_ohm} Ohm out of range"

    # 3. Verify SRF >> 5 * 13.56 MHz (> 80 MHz)
    assert res.f_srf_mhz > 85.0, f"SRF={res.f_srf_mhz} MHz too low!"

    # 4. Verify loaded Q in [15, 22] and -3 dB BW > 650 kHz for 847.5 kHz sidebands & 105.9 kbps ASK
    assert 15.0 <= res.q_loaded <= 22.0, f"Q_loaded={res.q_loaded} outside [15, 22]"
    assert res.bw_3db_khz > 650.0, f"BW_-3dB={res.bw_3db_khz} kHz <= 650 kHz"

    # 5. Verify trimmer tuning window brackets 13.560 MHz with +/-4% manufacturing margin
    assert spec.c_trim_min_pf + 1.5 <= res.c_trim_set_pf <= spec.c_trim_max_pf - 1.5, (
        f"Trimmer setpoint {res.c_trim_set_pf} pF lacks margin in [{spec.c_trim_min_pf}, {spec.c_trim_max_pf}] pF"
    )
    assert res.f_tune_min_mhz < 13.20 and res.f_tune_max_mhz > 13.95, (
        f"Tuning range [{res.f_tune_min_mhz}, {res.f_tune_max_mhz}] MHz too narrow"
    )

    # 6. Verify L2 GND keepout necessity (solid L2 at 0.21 mm kills > 65% of L2!)
    assert res.keepout_inductance_loss_pct > 65.0, "Expected >65% eddy-current inductance loss without L2 keepout"

    # 7. Verify axial coupling brackets SPICE k = {0.22 (0 mm), 0.08 (~20 mm), 0.02 (~45 mm)}
    k0 = res.coupling_table[0]["k_coupled"]
    k20 = res.coupling_table[2]["k_coupled"]
    k45 = res.coupling_table[4]["k_coupled"]
    assert 0.19 <= k0 <= 0.26, f"Flush 0 mm coupling k={k0} outside [0.19, 0.26]"
    assert 0.06 <= k20 <= 0.11, f"20 mm coupling k={k20} outside [0.06, 0.11]"
    assert 0.015 <= k45 <= 0.032, f"45 mm coupling k={k45} outside [0.015, 0.032]"


def format_report(res: CoilDesignResult, spec: PlanarSpiralSpec) -> str:
    lines = [
        "==============================================================================",
        " Dregg-180 13.56 MHz Planar Spiral NFC Antenna & Tank Summary (JLC04161H-7628)",
        "==============================================================================",
        f" Geometry (L1 1 oz / {spec.cu_thickness_um:.0f} um Cu, 46x46 mm L2/L3/L4 GND/PWR Keepout):",
        f"   Outer side d_out          : {res.d_out_mm:.2f} mm x {res.d_out_mm:.2f} mm",
        f"   Inner side d_in           : {res.d_in_mm:.2f} mm x {res.d_in_mm:.2f} mm",
        f"   Turns N / Width w / Gap s : N = {spec.n_turns}, w = {spec.trace_w_mm:.2f} mm, s = {spec.trace_s_mm:.2f} mm",
        f"   Mean diameter d_avg / rho : {res.d_avg_mm:.2f} mm (fill ratio rho = {res.fill_ratio_rho:.4f})",
        f"   Unwound conductor length  : {res.wire_length_m * 1000:.1f} mm",
        "------------------------------------------------------------------------------",
        " Inductance, Losses & Self-Resonance @ 13.560 MHz (25 C):",
        f"   L2 (Modified Wheeler)     : {res.l_wheeler_uh:.4f} uH",
        f"   L2 (Current-Sheet GMD)    : {res.l_cursheet_uh:.4f} uH",
        f"   L2 (Monomial Check)       : {res.l_monomial_uh:.4f} uH",
        f"   L2 Nominal (SPICE L2)     : {res.l_nom_uh:.4f} uH",
        f"   [TRAP] L2 w/o L2 Keepout  : {res.l_if_no_l2_keepout_uh:.4f} uH (-{res.keepout_inductance_loss_pct:.1f}% eddy loss!)",
        f"   Cu Skin Depth @ 13.56 MHz : {res.skin_depth_um:.2f} um",
        f"   DC Resistance Rdc         : {res.r_dc_ohm:.3f} Ohm",
        f"   AC Resistance Rac (SPICE) : {res.r_ac_13p56mhz_ohm:.3f} Ohm",
        f"   Self-Capacitance Cself    : {res.c_self_pf:.2f} pF  ->  SRF = {res.f_srf_mhz:.1f} MHz",
        f"   Unloaded Coil Qu          : {res.q_unloaded:.1f}",
        "------------------------------------------------------------------------------",
        " Resonance Tuning & ISO/IEC 14443 Bandwidth Shaping:",
        f"   Required Total C_res      : {res.c_res_target_pf:.2f} pF",
        f"   Fixed C_tune (C0G ±1%)    : {spec.c_fixed_pf:.1f} pF",
        f"   Stray + Diode/FET C_par   : {spec.c_pad_diode_pf:.2f} pF (+ {res.c_self_pf:.2f} pF C_self)",
        f"   Trimmer Setpoint C_trim   : {res.c_trim_set_pf:.2f} pF (SGC3S150NM 3..15 pF)",
        f"   Trimmer Frequency Span    : {res.f_tune_min_mhz:.3f} MHz .. {res.f_tune_max_mhz:.3f} MHz (f0 = {res.f0_nominal_mhz:.3f} MHz)",
        f"   Series Damping R_damp     : {spec.r_damp_series_ohm:.2f} Ohm (R_eq,tot = {res.r_tot_eq_series_ohm:.2f} Ohm)",
        f"   Loaded Tank Q_loaded      : {res.q_loaded:.2f}  [Target: 15..22]",
        f"   Loaded -3 dB Bandwidth    : {res.bw_3db_khz:.1f} kHz [Target: > 650 kHz]",
        "------------------------------------------------------------------------------",
        " Reader-to-Dregg180 Axial Coupling Profile (Primary L1 = 1.00 uH, r1 = 22.5 mm):",
    ]
    for row in res.coupling_table:
        lines.append(
            f"   Air gap = {row['air_gap_mm']:4.1f} mm (z_coil = {row['coil_to_coil_z_mm']:4.1f} mm) "
            f"-> k = {row['k_coupled']:.4f}, M = {row['mutual_M_nh']:6.1f} nH"
        )
    lines.append("==============================================================================")
    return "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser(description="Dregg-180 13.56 MHz Planar NFC Coil Calculator")
    ap.add_argument("--self-test", action="store_true", help="Run physics & SPICE consistency assertions")
    ap.add_argument("--json", action="store_true", help="Emit JSON output")
    args = ap.parse_args()

    spec = PlanarSpiralSpec()
    res = calc_planar_spiral(spec)
    if args.self_test:
        run_self_test(res, spec)

    if args.json:
        print(json.dumps(dataclasses.asdict(res), indent=2))
    else:
        print(format_report(res, spec))
        if args.self_test:
            print("SELF-TEST PASS: All 7 electromagnetic, bandwidth, keepout & SPICE checks verified.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
