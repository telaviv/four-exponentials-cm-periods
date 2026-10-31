"""Numerical / symbolic checks for REFEREE_HYP_MXP.md (model gmXP, mxP_K, deg2_i).

Run:  python check_mxp.py > check_mxp.out
"""
import numpy as np
import mpmath as mp
import sympy as sp

mp.mp.dps = 60
pi = mp.pi
varpi = mp.gamma(mp.mpf(1) / 4) ** 2 / (2 * mp.sqrt(2 * pi))
Om = mp.gamma(mp.mpf(1) / 3) ** 3 / (mp.mpf(2) ** (mp.mpf(4) / 3) * pi)
s3 = mp.sqrt(3)
rho = (-1 + 1j * s3) / 2
rhob = (-1 - 1j * s3) / 2
etaI = pi / varpi                       # etaLem 1 0
etaRho = 2 * pi / (s3 * Om)             # MX.etaRho

print("varpi   =", mp.nstr(varpi, 30))
print("Omega_r =", mp.nstr(Om, 30))


# ---------- 1. g2, g3 and eta1 via Eisenstein q-series ----------
def eis(tau, k, N=400):
    q = mp.exp(2j * pi * tau)
    c = {2: -24, 4: 240, 6: -504}[k]
    return 1 + c * mp.fsum(mp.mpf(n) ** (k - 1) * q ** n / (1 - q ** n) for n in range(1, N))


def invariants(w1, tau):
    g2 = (4 * pi ** 4 / 3) * eis(tau, 4) / w1 ** 4
    g3 = (8 * pi ** 6 / 27) * eis(tau, 6) / w1 ** 6
    eta1 = pi ** 2 * eis(tau, 2) / (3 * w1)   # eta(w1), zeta(z+w1)=zeta(z)+eta1
    return g2, g3, eta1


for name, w1, tau, eta_lean in [("varpi Z[i]", varpi, 1j, etaI),
                                ("Omega Z[rho]", Om, rho, etaRho)]:
    g2, g3, e1 = invariants(w1, tau)
    print(f"[{name}] g2 = {mp.nstr(g2, 25)}  g3 = {mp.nstr(g3, 25)}")
    print(f"[{name}] eta(w1) (E2 formula) - Lean value = {mp.nstr(abs(e1 - eta_lean), 5)}")

# Legendre relations (w1 eta2 - w2 eta1 = -2 pi i  <=>  eta1 w2 - eta2 w1 = 2 pi i)
eta2_i = -1j * etaI
eta2_r = rhob * etaRho
print("Legendre E_i : eta1*w2 - eta2*w1 - 2pi i =",
      mp.nstr(abs(etaI * (1j * varpi) - eta2_i * varpi - 2j * pi), 5))
print("Legendre E_r : eta1*w2 - eta2*w1 - 2pi i =",
      mp.nstr(abs(etaRho * (rho * Om) - eta2_r * Om - 2j * pi), 5))
print("etaRho_mul   : etaRho*Om - 2 sqrt3 pi/3 =", mp.nstr(abs(etaRho * Om - 2 * s3 * pi / 3), 5))


# ---------- 2. direct lattice-sum zeta, independent of the formulas above ----------
def zeta_direct(z, w1, w2, M):
    m = np.arange(-M, M + 1)
    A, B = np.meshgrid(m, m)
    lam = (A * complex(w1) + B * complex(w2)).ravel()
    lam = lam[np.abs(lam) > 0]
    return 1 / z + np.sum(1 / (z - lam) + 1 / lam + z / lam ** 2)


def eta_direct(w, w1, w2, z0=0.3 + 0.17j):
    # Richardson in M (error ~ 1/M^2)
    vals = []
    for M in (300, 600):
        vals.append(zeta_direct(z0 + complex(w), w1, w2, M) - zeta_direct(z0, w1, w2, M))
    return (4 * vals[1] - vals[0]) / 3


print("direct zeta sums (Richardson, ~1e-7 accuracy expected):")
for name, w1, w2, per, val in [
    ("E_i : eta(varpi)", varpi, 1j * varpi, varpi, etaI),
    ("E_i : eta(i varpi)", varpi, 1j * varpi, 1j * varpi, eta2_i),
    ("E_r : eta(Omega)", Om, rho * Om, Om, etaRho),
    ("E_r : eta(rho Omega)  [HP2]", Om, rho * Om, rho * Om, eta2_r),
]:
    e = eta_direct(complex(per), complex(w1), complex(w2))
    print(f"  {name}: direct = {e:.10f}, Lean = {complex(val):.10f}, |diff| = {abs(e - complex(val)):.2e}")

# g2, g3 by direct sums (fast convergence)
for name, w1, w2 in [("E_i", varpi, 1j * varpi), ("E_r", Om, rho * Om)]:
    M = 400
    m = np.arange(-M, M + 1)
    A, B = np.meshgrid(m, m)
    lam = (A * complex(w1) + B * complex(w2)).ravel()
    lam = lam[np.abs(lam) > 0]
    print(f"  {name}: direct g2 = {60 * np.sum(lam ** -4.0):.10f}, g3 = {140 * np.sum(lam ** -6.0):.10f}")

# ---------- 3. w2' = (eta_rho/varpi) w1'  (two Legendre relations) ----------
beta = mp.mpf(7) / 5 + 0.3j
w1p = (varpi, beta * Om)
w2p = (etaRho, 2 * beta / s3 * etaI)
r = etaRho / varpi
print("w2' - (eta_rho/varpi) w1' =", mp.nstr(abs(w2p[0] - r * w1p[0]) + abs(w2p[1] - r * w1p[1]), 5))

# ---------- 4. symbolic: deg2_i, the two cases ----------
c1, c2, c3, Pi, Vp, Or = sp.symbols('c1 c2 c3 Pi Vp Or', nonzero=True)
S3 = sp.sqrt(3)
etaR_s = 2 * Pi / (S3 * Or)
# case c0 = 0 (Lean): beta = sqrt3/2, X = (Vp, Pi/Vp), Y = (Or, etaR), a = 2 k c2/sqrt3, c = -k c1
k = (S3 / 2 - 1) / c3
a = 2 * k * c2 / S3
lhs = (Vp + etaR_s + a) * (S3 / 2 * Or)
rhs = (Pi / Vp + Or - k * c1) * Vp
print("deg2_i c0=0: hrelP(LHS-RHS) - k*(c1 Vp + c2 Or + c3 Vp Or) =",
      sp.simplify(sp.expand(lhs - rhs - k * (c1 * Vp + c2 * Or + c3 * Vp * Or))))
# the one-line alternative: (c1 Vp + c2 Or + c3 Vp Or) * Pi/(Vp Or) = c3 Pi + c2 eta_i + (sqrt3/2) c1 eta_rho
etaI_s = Pi / Vp
alt = (c1 * Vp + c2 * Or + c3 * Vp * Or) * Pi / (Vp * Or) - (c3 * Pi + c2 * etaI_s + S3 / 2 * c1 * etaR_s)
print("c0=0 shortcut identity residual:", sp.simplify(alt))
# case c0 != 0 (paper and Lean): beta = A, X = (Vp, Pi/Vp), Y = 0, a = C/A, b = -B, with Pi = A Vp Or + B Vp + C Or
A_, B_, C_ = sp.symbols('A B C', nonzero=True)
lhs = (Vp + C_ / A_) * (A_ * Or)
rhs = (Pi / Vp - B_) * Vp
print("deg2_i c0!=0: LHS-RHS =", sp.simplify(sp.expand(lhs - rhs)), " (vanishes iff Pi = A Vp Or + B Vp + C Or)")

# ---------- 5. PSLQ sanity (no small relations) ----------
mp.mp.dps = 80
pi = mp.pi
varpi = mp.gamma(mp.mpf(1) / 4) ** 2 / (2 * mp.sqrt(2 * pi))
Om = mp.gamma(mp.mpf(1) / 3) ** 3 / (mp.mpf(2) ** (mp.mpf(4) / 3) * pi)
s3 = mp.sqrt(3)
etaRho = 2 * pi / (s3 * Om)
vec = [pi, varpi, Om, varpi * Om, s3 * pi, s3 * varpi, s3 * Om, s3 * varpi * Om]
print("PSLQ over Q(sqrt3) on (pi, varpi, Om, varpi Om):", mp.pslq(vec, maxcoeff=10 ** 8, maxsteps=10 ** 6))
six = [1, pi, varpi, pi / varpi, Om, etaRho]
six3 = six + [s3 * x for x in six]
print("PSLQ over Q(sqrt3) on the six numbers:", mp.pslq(six3, maxcoeff=10 ** 6, maxsteps=10 ** 6))

# ---------- 6. re-check the PSLQ hit at higher precision (spurious at 80 digits?) ----------
rel = mp.pslq(six3, maxcoeff=10 ** 6, maxsteps=10 ** 6)
mp.mp.dps = 200
pi = mp.pi
varpi = mp.gamma(mp.mpf(1) / 4) ** 2 / (2 * mp.sqrt(2 * pi))
Om = mp.gamma(mp.mpf(1) / 3) ** 3 / (mp.mpf(2) ** (mp.mpf(4) / 3) * pi)
s3 = mp.sqrt(3)
etaRho = 2 * pi / (s3 * Om)
six = [1, pi, varpi, pi / varpi, Om, etaRho]
six3 = six + [s3 * x for x in six]
if rel:
    print("residual of the 80-digit PSLQ vector at 200 digits:", mp.nstr(mp.fsum(c * x for c, x in zip(rel, six3)), 5))
print("PSLQ at 200 digits, maxcoeff 1e6:", mp.pslq(six3, maxcoeff=10 ** 6, maxsteps=10 ** 6))
vec = [pi, varpi, Om, varpi * Om, s3 * pi, s3 * varpi, s3 * Om, s3 * varpi * Om]
print("PSLQ at 200 digits on (pi, varpi, Om, varpi Om) over Q(sqrt3), maxcoeff 1e10:",
      mp.pslq(vec, maxcoeff=10 ** 10, maxsteps=10 ** 6))
