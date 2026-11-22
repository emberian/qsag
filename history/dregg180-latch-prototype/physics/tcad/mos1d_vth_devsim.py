#!/usr/bin/env python3
"""Can a device simulator be fed from the open PDK?  A 1-D MOS capacitor in DEVSIM built from the only
"process" numbers the nfet_06v0 BSIM4 card discloses (toxe = 15.2 nm, ndep = 1.7e17 cm^-3, n+ poly gate,
ngate = 1e20), uniform substrate doping, equilibrium Poisson (Boltzmann carriers), 300 K.
It reports the gate voltage at which the surface electron density equals the acceptor density (classical
strong-inversion threshold) and compares it with the card's own long-channel vth0 = 0.673 V.

Run on a build box:  DEVSIM_MATH_LIBS=/usr/lib/x86_64-linux-gnu/liblapack.so.3:/usr/lib/x86_64-linux-gnu/libblas.so.3 python mos1d_vth_devsim.py
Assumed: uniform doping (the real channel has well and threshold-adjust implants that the PDK does not publish),
no interface or fixed charge, no poly depletion, no quantum correction.
"""
import math, sys
import devsim as ds
from devsim.python_packages import simple_physics as sp

def vth(na, tox_cm, quiet=True):
    dev = "mos%g" % na; mesh = "m%g" % na
    tsi = 1.0e-4
    ds.create_1d_mesh(mesh=mesh)
    ds.add_1d_mesh_line(mesh=mesh, pos=0.0, ps=tox_cm / 10, tag="gate")
    ds.add_1d_mesh_line(mesh=mesh, pos=tox_cm, ps=2e-8, tag="int")
    ds.add_1d_mesh_line(mesh=mesh, pos=tox_cm + tsi, ps=2e-6, tag="bulk")
    ds.add_1d_contact(mesh=mesh, name="gate", tag="gate", material="metal")
    ds.add_1d_contact(mesh=mesh, name="bulk", tag="bulk", material="metal")
    ds.add_1d_interface(mesh=mesh, name="int", tag="int")
    ds.add_1d_region(mesh=mesh, material="Oxide", region="ox", tag1="gate", tag2="int")
    ds.add_1d_region(mesh=mesh, material="Silicon", region="si", tag1="int", tag2="bulk")
    ds.finalize_mesh(mesh=mesh); ds.create_device(mesh=mesh, device=dev)
    sp.SetOxideParameters(dev, "ox", 300); sp.SetSiliconParameters(dev, "si", 300)
    ds.node_model(device=dev, region="si", name="Acceptors", equation="%g" % na)
    ds.node_model(device=dev, region="si", name="Donors", equation="0")
    ds.node_model(device=dev, region="si", name="NetDoping", equation="Donors-Acceptors")
    sp.CreateSiliconPotentialOnly(dev, "si"); sp.CreateOxidePotentialOnly(dev, "ox", "log_damp")
    sp.CreateSiliconPotentialOnlyContact(dev, "si", "bulk"); sp.CreateOxideContact(dev, "ox", "gate")
    sp.CreateSiliconOxideInterface(dev, "int")
    ni = ds.get_parameter(device=dev, region="si", name="n_i"); vt = ds.get_parameter(device=dev, region="si", name="V_t")
    phi_gate = 0.56                      # n+ poly Fermi level at the conduction band edge: +Eg/2 above midgap
    ds.set_parameter(device=dev, name=sp.GetContactBiasName("bulk"), value=0.0)
    out = []
    v = -1.0
    while v <= 2.0001:
        ds.set_parameter(device=dev, name=sp.GetContactBiasName("gate"), value=v + phi_gate)
        ds.solve(type="dc", absolute_error=1e3, relative_error=1e-9, maximum_iterations=60)
        n = ds.get_node_model_values(device=dev, region="si", name="IntrinsicElectrons")
        out.append((v, n[0]))
        v += 0.02
    for (v0, n0), (v1, n1) in zip(out[:-1], out[1:]):
        if n0 < na <= n1:
            return v0 + (v1 - v0) * (math.log(na / n0) / math.log(n1 / n0)), ni, vt
    return None, ni, vt

def analytic(na, tox_cm, ni, vt):
    q, es, eox = 1.602e-19, 11.7 * 8.854e-14, 3.9 * 8.854e-14
    phif = vt * math.log(na / ni)
    return -(0.56 + phif) + 2 * phif + math.sqrt(2 * es * q * na * 2 * phif) / (eox / tox_cm)

if __name__ == "__main__":
    tox = 15.2e-7
    print("nfet_06v0 card: toxe 15.2 nm, ndep 1.7e17, vth0 0.673 V (typical)")
    for na in (1.7e17, 1.0e17, 7e16, 5e16):
        v, ni, vt = vth(na, tox)
        print("uniform Na = %.1e cm^-3: DEVSIM Vth(ns = Na) = %s V, textbook formula %.3f V" % (na, "%.3f" % v if v else "n/a", analytic(na, tox, ni, vt)))
