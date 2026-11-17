#!/usr/bin/env python3
"""3-D transient electro-thermal model of a silicided-polysilicon fuse link.

Finite volumes on a non-uniform Cartesian grid, half domain (mirror symmetry
about the link axis, y = 0).  Each time step:
  1. current continuity  div(sigma(T) grad phi) = 0  on the conductor cells
     (silicide layer + polysilicon), contacts as lumped conductances;
  2. the fuse resistance sets the operating point on the driver load line
     I(R) (table from ngspice, run_prog_drive.py) or an ideal source;
  3. heat equation  C(T) dT/dt = div(k(T) grad T) + q_joule, backward Euler,
     properties lagged, adaptive step.
Melting of the poly/silicide stack is an apparent-heat-capacity phase change;
above the melt the conductor takes the liquid-silicon conductivity.

What the model does NOT contain: atomic transport (electromigration, silicide
agglomeration, dopant segregation), void formation, mechanical cracking.  It
answers "how hot, how fast, and held by what", not "what is the final
resistance".

Units SI; lengths in the geometry dictionaries in micrometres.
Pure numpy/scipy.  No project data is read except the optional drive table.
"""
import json, math, sys, time
import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as spla

UM = 1e-6
SI, OX, POLY, SIL, W, AL = range(6)

# ----------------------------------------------------------------------------
# geometries
# ----------------------------------------------------------------------------
def geom_gf180(t_sil=0.03, t_fox=0.32, t_poly=0.20, t_ild=0.71):
    """gf180mcu_fd_pr efuse_cell, from gds/efuse.gds (see gds_dump.py).
    x = 0 at the anode end of the link; anode (pin 'in', small pad) at x < 0."""
    return dict(
        name="gf180mcu efuse_cell",
        link=(0.0, 1.26, 0.09),                       # x0, x1, half width
        pads=[(-2.43, 0.0, 0.53), (1.26, 3.10, 1.13)],  # x0, x1, half width
        an_contacts=[(-0.845, -0.625, 0.125, 0.345), (-0.375, -0.155, 0.125, 0.345)],
        ca_contacts=[(1.415, 1.635, 0.125, 0.345), (1.415, 1.635, 0.595, 0.815)],
        m1=[(-4.0, -0.10, 0.405), (1.36, 4.7, 0.875)],
        xlim=(-4.0, 4.7), ymax=3.0,
        t_sil=t_sil, t_fox=t_fox, t_poly=t_poly, t_ild=t_ild, t_m1=0.55, t_top=2.2, t_sub=4.0)

def geom_generic(L, Wd, pad_an=(1.0, 0.4), pad_ca=(1.5, 0.8), t_sil=0.03, t_fox=0.30,
                 t_poly=0.15, t_ild=0.6, name="generic"):
    """A dog-bone fuse: link L x Wd, anode pad (length, half width), cathode pad."""
    la, wa = pad_an; lc, wc = pad_ca
    c = 0.11
    return dict(
        name=name, link=(0.0, L, Wd / 2),
        pads=[(-la, 0.0, wa), (L, L + lc, wc)],
        an_contacts=[(-la / 2 - c, -la / 2 + c, max(0.0, wa / 2 - c), wa / 2 + c)],
        ca_contacts=[(L + lc / 2 - c, L + lc / 2 + c, max(0.0, wc / 2 - c), wc / 2 + c)],
        m1=[(-la - 1.5, -0.1, wa), (L + 0.1, L + lc + 1.5, wc)],
        xlim=(-la - 1.5, L + lc + 1.5), ymax=2.5,
        t_sil=t_sil, t_fox=t_fox, t_poly=t_poly, t_ild=t_ild, t_m1=0.5, t_top=2.0, t_sub=4.0)

def edges(breaks, hmax):
    """Cell edges through every breakpoint, cells no larger than hmax(mid)."""
    breaks = sorted(set(round(b, 6) for b in breaks))
    out = [breaks[0]]
    for a, b in zip(breaks[:-1], breaks[1:]):
        h = hmax(0.5 * (a + b))
        n = max(1, int(math.ceil((b - a) / h - 1e-9)))
        out += list(a + (b - a) * (np.arange(1, n + 1) / n))
    return np.array(out)

# ----------------------------------------------------------------------------
# material laws
# ----------------------------------------------------------------------------
class Params:
    """Every assumed number in one place.  Sources and the reasoning behind each value:
    scratch/lanes/fable-efuse-and-process-sim.last.md (section A.3)."""
    T0 = 300.0
    rs_sil = 7.3          # ohm/sq, silicided p+ poly at 25 C (PDK rsh_ppolyf_s, typical)
    tc1 = 3.245e-3        # 1/K   (PDK ppolyf_s r_tc1, tnom 25 C; extrapolated above 175 C)
    tc2 = 3.6e-7          # 1/K^2 (PDK ppolyf_s r_tc2)
    tcr_cap = 12.0        # cap on the resistivity multiplier (assumed)
    rs_poly = 350.0       # ohm/sq, unsalicided p+ poly (PDK rsh_ppolyf_u), film without silicide
    rho_liq = 80e-8       # ohm m, liquid silicon near the melting point (literature, ~75-85 uOhm cm)
    T_melt = 1687.0       # K; 1532 K = CoSi2-Si eutectic as the other bound
    dT_melt = 100.0       # K, numerical width of the phase change (latent heat and conductivity mixing)
    L_melt = 4.2e9        # J/m^3 latent heat of silicon
    r_contact = 10.0      # ohm per contact (assumed)
    k_ox_scale = 1.0      # multiplies the oxide conductivity (0.8 for deposited ILD)
    k_poly300 = 30.0      # W/m/K heavily doped fine-grain poly at 300 K (literature range 15-45)
    lorenz = 2.44e-8
    T_boil = 3500.0       # K, silicon boiling point: the run stops here

def sig_intrinsic(T):
    """Intrinsic silicon conductivity, S/m (n_i: Misiakos & Tsamakis 1993;
    lattice mobilities ~T^-2.3).  Only matters above ~1100 K."""
    T = np.minimum(T, 1700.0)
    ni = 5.29e19 * (T / 300.0) ** 2.54 * np.exp(-6726.0 / T) * 1e6      # m^-3
    mu = (1400.0 + 450.0) * (T / 300.0) ** -2.3 * 1e-4                   # m^2/Vs
    return 1.602e-19 * ni * mu

def liquid_fraction(T, p):
    return np.clip((T - (p.T_melt - p.dT_melt / 2)) / p.dT_melt, 0.0, 1.0)

def sigma_cells(T, mat, p, g):
    """Electrical conductivity of each cell (zero for insulators)."""
    s = np.zeros_like(T)
    fl = liquid_fraction(T, p)
    dT = T - 298.15
    mult = np.clip(1 + p.tc1 * dT + p.tc2 * dT * dT, 0.3, p.tcr_cap)
    m = mat == SIL
    s_sol = 1.0 / (p.rs_sil * g["t_sil"] * UM * mult)
    s[m] = ((1 - fl) * s_sol + fl / p.rho_liq)[m]
    m = mat == POLY
    dTp = np.minimum(dT, 900.0)
    multp = np.clip(1 - 0.9e-4 * dTp + 7e-7 * dTp * dTp, 0.5, 3.0)      # PDK ppolyf_u tc1/tc2
    s_sol = 1.0 / (p.rs_poly * g["t_poly"] * UM * multp) + sig_intrinsic(T)
    s[m] = ((1 - fl) * s_sol + fl / p.rho_liq)[m]
    return s

def k_cells(T, mat, p, sig):
    k = np.empty_like(T)
    k[mat == SI] = (148.0 * (T / 300.0) ** -1.3)[mat == SI]
    kox = p.k_ox_scale * np.minimum(1.4 + 0.6 * (T - 300.0) / 1000.0, 2.2)
    k[mat == OX] = kox[mat == OX]
    fl = liquid_fraction(T, p)
    kp = np.maximum(p.k_poly300 * 300.0 / T, 12.0)
    k[mat == POLY] = ((1 - fl) * kp + fl * 56.0)[mat == POLY]
    ks = 5.0 + p.lorenz * T * sig                                         # Wiedemann-Franz + lattice
    k[mat == SIL] = ((1 - fl) * ks + fl * 56.0)[mat == SIL]
    k[mat == W] = 170.0
    k[mat == AL] = 237.0
    return k

def c_cells(T, mat, p):
    """Volumetric heat capacity incl. apparent latent heat, J/m^3/K."""
    c = np.empty_like(T)
    csi = 1.63e6 + 0.45e6 * (1 - np.exp(-(T - 300.0) / 400.0))
    cox = 1.65e6 + 1.0e6 * (1 - np.exp(-(T - 300.0) / 500.0))
    inmelt = (np.abs(T - p.T_melt) < p.dT_melt / 2)
    lat = np.where(inmelt, p.L_melt / p.dT_melt, 0.0)
    c[mat == SI] = csi[mat == SI]
    c[mat == OX] = cox[mat == OX]
    c[mat == POLY] = (csi + lat)[mat == POLY]
    c[mat == SIL] = (2.3e6 + lat)[mat == SIL]
    c[mat == W] = 2.6e6
    c[mat == AL] = 2.4e6
    return c

# ----------------------------------------------------------------------------
# model
# ----------------------------------------------------------------------------
class Fuse:
    def __init__(self, g, p=None, hlink=0.045, hpad=0.12, hfar=0.5, quiet=True):
        self.g, self.p = g, p or Params()
        g = self.g
        x0, x1, hw = g["link"]
        xb = [g["xlim"][0], g["xlim"][1], x0, x1]
        yb = [0.0, hw, g["ymax"]]
        for (a, b, w) in g["pads"]: xb += [a, b]; yb.append(w)
        for (a, b, c, d) in g["an_contacts"] + g["ca_contacts"]: xb += [a, b]; yb += [c, d]
        for (a, b, w) in g["m1"]: xb += [a, b]; yb.append(w)
        padx0 = min(a for a, b, w in g["pads"]); padx1 = max(b for a, b, w in g["pads"])
        padw = max(w for a, b, w in g["pads"])
        def hx(x):
            if x0 - 0.3 < x < x1 + 0.3: return hlink
            if padx0 < x < padx1: return hpad
            return hfar
        def hy(y):
            if y < hw: return hw / 2
            if y < hw + 0.3: return hlink * 1.5
            if y < padw: return hpad
            return hfar
        z_fox = g["t_fox"]; z_ps = z_fox + g["t_poly"] - g["t_sil"]; z_pt = z_fox + g["t_poly"]
        z_m1 = z_pt + g["t_ild"]; z_m1t = z_m1 + g["t_m1"]; z_top = z_m1t + g["t_top"]
        zb = [-g["t_sub"], -1.0, -0.3, 0.0, z_fox, z_ps, z_pt, z_m1, z_m1t, z_top]
        def hz(z):
            if z < -1.0: return 1.0
            if z < -0.3: return 0.35
            if z < 0: return 0.15
            if z < z_fox: return z_fox / 5
            if z < z_ps: return (z_ps - z_fox) / 3
            if z < z_pt: return 1.0
            if z < z_pt + 0.25: return 0.06
            if z < z_m1: return 0.16
            if z < z_m1t: return 0.3
            return 0.6
        self.xe = edges(xb, hx) * UM; self.ye = edges(yb, hy) * UM; self.ze = edges(zb, hz) * UM
        self.nx, self.ny, self.nz = len(self.xe) - 1, len(self.ye) - 1, len(self.ze) - 1
        xc = 0.5 * (self.xe[1:] + self.xe[:-1]) / UM
        yc = 0.5 * (self.ye[1:] + self.ye[:-1]) / UM
        zc = 0.5 * (self.ze[1:] + self.ze[:-1]) / UM
        X, Y, Z = np.meshgrid(xc, yc, zc, indexing="ij")
        self.X, self.Y, self.Z = X, Y, Z
        mat = np.full(X.shape, OX, dtype=np.int8)
        mat[Z < 0] = SI
        foot = (X > x0) & (X < x1) & (Y < hw)
        for (a, b, w) in g["pads"]: foot |= (X > a) & (X < b) & (Y < w)
        mat[foot & (Z > z_fox) & (Z < z_ps)] = POLY
        mat[foot & (Z > z_ps) & (Z < z_pt)] = SIL
        cont_an = np.zeros(X.shape, bool); cont_ca = np.zeros(X.shape, bool)
        for (a, b, c, d) in g["an_contacts"]: cont_an |= (X > a) & (X < b) & (Y > c) & (Y < d)
        for (a, b, c, d) in g["ca_contacts"]: cont_ca |= (X > a) & (X < b) & (Y > c) & (Y < d)
        mat[(cont_an | cont_ca) & (Z > z_pt) & (Z < z_m1)] = W
        for (a, b, w) in g["m1"]: mat[(X > a) & (X < b) & (Y < w) & (Z > z_m1) & (Z < z_m1t)] = AL
        self.mat = mat
        self.link = (X > x0) & (X < x1) & (Y < hw) & ((mat == POLY) | (mat == SIL))
        self.an_top = cont_an & (mat == SIL); self.ca_top = cont_ca & (mat == SIL)
        dx = np.diff(self.xe); dy = np.diff(self.ye); dz = np.diff(self.ze)
        self.dx, self.dy, self.dz = dx, dy, dz
        self.vol = dx[:, None, None] * dy[None, :, None] * dz[None, None, :]
        self.N = mat.size
        self.idx = np.arange(self.N).reshape(mat.shape)
        self.cond = (mat == POLY) | (mat == SIL)
        self.cidx = -np.ones(mat.shape, dtype=np.int64); self.cidx[self.cond] = np.arange(self.cond.sum())
        self.T = np.full(mat.shape, self.p.T0)
        if not quiet:
            print("grid %dx%dx%d = %d cells, %d conductor cells" % (self.nx, self.ny, self.nz, self.N, self.cond.sum()))

    # face conductances between neighbours along each axis (harmonic mean)
    def _faces(self, prop):
        dx, dy, dz = self.dx, self.dy, self.dz
        out = []
        a = dy[None, :, None] * dz[None, None, :]
        r = 0.5 * dx[:-1, None, None] / prop[:-1] + 0.5 * dx[1:, None, None] / prop[1:]
        out.append(a / r)
        a = dx[:, None, None] * dz[None, None, :]
        r = 0.5 * dy[None, :-1, None] / prop[:, :-1] + 0.5 * dy[None, 1:, None] / prop[:, 1:]
        out.append(a / r)
        a = dx[:, None, None] * dy[None, :, None]
        r = 0.5 * dz[None, None, :-1] / prop[:, :, :-1] + 0.5 * dz[None, None, 1:] / prop[:, :, 1:]
        out.append(a / r)
        return out

    def _pairs(self, idx):
        return [(idx[:-1], idx[1:]), (idx[:, :-1], idx[:, 1:]), (idx[:, :, :-1], idx[:, :, 1:])]

    def electrical(self):
        """Solve for unit anode voltage.  Returns (R_total, per-cell Joule power for 1 A)."""
        p = self.p
        sig = sigma_cells(self.T, self.mat, p, self.g)
        self.sig = sig
        sg = np.where(self.cond, sig, 1e-30)
        G = self._faces(sg)
        n = int(self.cond.sum())
        rows, cols, vals = [], [], []
        diag = np.zeros(n); rhs = np.zeros(n)
        pair_list = []
        for Gf, (ia, ib) in zip(G, self._pairs(self.cidx)):
            m = (ia >= 0) & (ib >= 0)
            a, b, gf = ia[m], ib[m], Gf[m]
            rows += [a, b]; cols += [b, a]; vals += [-gf, -gf]
            np.add.at(diag, a, gf); np.add.at(diag, b, gf)
            pair_list.append((a, b, gf))
        # contacts: conductance per contact shared over its cells by area
        gc_cells = np.zeros(n); v_cells = np.zeros(n)
        area = (self.dx[:, None, None] * self.dy[None, :, None] * np.ones(self.mat.shape))
        for mask, v, ncont in ((self.an_top, 1.0, len(self.g["an_contacts"])),
                               (self.ca_top, 0.0, len(self.g["ca_contacts"]))):
            ci = self.cidx[mask]; a = area[mask]
            gtot = ncont / p.r_contact            # half domain holds ncont contacts
            gc_cells[ci] = gtot * a / a.sum(); v_cells[ci] = v
        diag += gc_cells; rhs += gc_cells * v_cells
        A = sp.csr_matrix((np.concatenate(vals + [diag]),
                           (np.concatenate(rows + [np.arange(n)]), np.concatenate(cols + [np.arange(n)]))), shape=(n, n))
        phi = spla.spsolve(A.tocsc(), rhs)
        i_half = float(np.sum(gc_cells * (v_cells - phi) * (v_cells > 0)))
        q = np.zeros(n)                              # W per cell at 1 V applied (half domain)
        for a, b, gf in pair_list:
            pw = gf * (phi[a] - phi[b]) ** 2
            np.add.at(q, a, 0.5 * pw); np.add.at(q, b, 0.5 * pw)
        q += gc_cells * (v_cells - phi) ** 2
        R = 1.0 / (2 * i_half)                       # full device
        qfull = np.zeros(self.mat.shape); qfull[self.cond] = q
        # scale: at device current I, V = I R, cell power = q * (I R)^2
        return R, qfull * R * R

    def thermal_step(self, q, dt):
        p = self.p
        k = k_cells(self.T, self.mat, p, self.sig)
        c = c_cells(self.T, self.mat, p)
        G = self._faces(k)
        N = self.N
        diag = (c * self.vol / dt).ravel().copy()
        rhs = diag * self.T.ravel() + q.ravel()
        rows, cols, vals = [], [], []
        for Gf, (ia, ib) in zip(G, self._pairs(self.idx)):
            a, b, gf = ia.ravel(), ib.ravel(), Gf.ravel()
            rows += [a, b]; cols += [b, a]; vals += [-gf, -gf]
            np.add.at(diag, a, gf); np.add.at(diag, b, gf)
        # substrate bottom held at ambient
        gb = (k[:, :, 0] * self.dx[:, None] * self.dy[None, :] / (0.5 * self.dz[0])).ravel()
        ib = self.idx[:, :, 0].ravel()
        diag[ib] += gb; rhs[ib] += gb * p.T0
        ar = np.arange(N)
        A = sp.csc_matrix((np.concatenate(vals + [diag]),
                           (np.concatenate(rows + [ar]), np.concatenate(cols + [ar]))), shape=(N, N))
        Tn, info = spla.cg(A, rhs, x0=self.T.ravel(), rtol=1e-8, maxiter=4000,
                           M=sp.diags(1.0 / diag))
        if info != 0:
            Tn = spla.spsolve(A, rhs)
        return Tn.reshape(self.mat.shape)

    def run(self, drive, t_end=50e-6, dt0=0.5e-9, dt_max=1e-6, dT_step=60.0, log=None, stop_at_bridge=False,
            stop_steady=True, max_steps=5000):
        """drive(R, t) -> device current in A.  Returns a history dict.
        stop_steady: end the run once the temperature field has stopped changing
        (less than 1 K per step over five consecutive steps of at least 0.2 us)."""
        calm = 0
        p = self.p
        t, dt = 0.0, dt0
        H = dict(t=[], I=[], R=[], P=[], Tmax=[], Tlink=[], fmolten=[], events={})
        linkv = self.vol * self.link
        while t < t_end:
            R, q1 = self.electrical()
            I = drive(R, t)
            q = q1 * I * I
            Pf = 2 * q.sum()
            while True:
                Tn = self.thermal_step(q, dt)
                if np.max(np.abs(Tn - self.T)) <= dT_step or dt <= 2e-11: break
                dt *= 0.5
            dmax = np.max(np.abs(Tn - self.T))
            self.T = Tn; t += dt
            Tl = self.T[self.link]
            fm = float((linkv * (self.T > p.T_melt))[self.link].sum() / linkv[self.link].sum())
            H["t"].append(t); H["I"].append(I); H["R"].append(R); H["P"].append(Pf)
            H["Tmax"].append(float(self.T.max())); H["Tlink"].append(float(Tl.mean())); H["fmolten"].append(fm)
            ev = H["events"]
            for name, cond in (("T900", Tl.max() >= 900.0), ("T1150", Tl.max() >= 1150.0),
                               ("melt_onset", Tl.max() >= p.T_melt),
                               ("melt_bridge", self._bridge()), ("boil", self.T.max() >= p.T_boil)):
                if cond and name not in ev: ev[name] = t
            if log and (len(H["t"]) % 20 == 0):
                log("t=%.3e dt=%.1e I=%.2fmA R=%.1f P=%.1fmW Tmax=%.0f fm=%.2f" % (t, dt, I * 1e3, R, Pf * 1e3, self.T.max(), fm))
            if "boil" in ev or (stop_at_bridge and "melt_bridge" in ev): break
            calm = calm + 1 if (dmax < 1.0 and dt >= 0.2e-6) else 0
            if stop_steady and calm >= 5: ev["steady"] = t; break
            if len(H["t"]) >= max_steps: ev["step_cap"] = t; break
            if dmax < 0.3 * dT_step: dt = min(dt * 1.3, dt_max)
        return H

    def _bridge(self):
        """True when some cross-section of the link is molten through (all conductor cells)."""
        m = self.link
        molten = (self.T > self.p.T_melt) | ~m
        cnt = m.sum(axis=(1, 2))
        full = molten.all(axis=(1, 2)) & (cnt > 0)
        return bool(full.any())

    def r_cold(self):
        R, _ = self.electrical(); return R

# ----------------------------------------------------------------------------
# drivers
# ----------------------------------------------------------------------------
def table_drive(curve, scale=1.0):
    lr = np.log(np.array(curve["R"], float)); cur = np.array(curve["I"], float)
    return lambda R, t: scale * float(np.interp(math.log(max(R, 1.0)), lr, cur))

def limited_source(v, ilim, rser=0.0):
    """Voltage source v behind rser with a current limit ilim (an NFET in saturation)."""
    return lambda R, t: min(ilim, v / (R + rser))

def nfet_drive(vfs, rser, ron, isat):
    """Supply vfs, series rser, select NFET with triode resistance ron and saturation current isat."""
    return lambda R, t: min(isat, vfs / (R + rser + ron))

def summarize(H):
    ev = H["events"]
    return dict(R0=H["R"][0], I0=H["I"][0], P0=H["P"][0], Tmax=max(H["Tmax"]), Tend=H["Tmax"][-1],
                Rend=H["R"][-1], Iend=H["I"][-1], Pend=H["P"][-1], fm_end=H["fmolten"][-1],
                t_end=H["t"][-1], steps=len(H["t"]), **{"t_" + k: v for k, v in ev.items()})

if __name__ == "__main__":
    # smoke test: nominal gf180 cell at a fixed 20 mA
    f = Fuse(geom_gf180(), quiet=False)
    print("cold resistance %.1f ohm" % f.r_cold())
    t0 = time.time()
    H = f.run(lambda R, t: 20e-3, t_end=5e-6, log=print)
    print(json.dumps(summarize(H), indent=1), "wall %.1fs" % (time.time() - t0))
