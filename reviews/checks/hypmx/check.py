"""Numerical checks for REFEREE_HYP_MX: lattices, g2/g3, eta, Legendre, zeta symmetries, cocycle.
Lean definitions mirrored:
  varpi    = Gamma(1/4)^2 / (2 sqrt(2 pi))
  OmegaRho = Gamma(1/3)^3 / (2^(4/3) pi)
  lemniscatic = (varpi, i varpi); equianharmonic = (Omega, rho Omega), rho = (-1 + i sqrt3)/2
  weierstrassZeta L z = sum_l (1/(z-l) + 1/l + z/l^2) with 1/0 = 0 (so the l = 0 term is 1/z)
  etaI m n = (m - n i) pi/varpi ; etaRho = 2 pi/(sqrt3 Omega) ; etaR m n = (m + n rhoBar) etaRho
"""
import mpmath as mp
import numpy as np

mp.mp.dps = 40
pi = mp.pi
varpi = mp.gamma(mp.mpf(1)/4)**2 / (2*mp.sqrt(2*pi))
Om = mp.gamma(mp.mpf(1)/3)**3 / (mp.mpf(2)**(mp.mpf(4)/3) * pi)
s3 = mp.sqrt(3)
rho = (-1 + 1j*s3)/2
rhob = (-1 - 1j*s3)/2
print("varpi =", varpi)
print("Omega =", Om)

def eis(tau, N=200):
    q = mp.exp(2j*pi*tau)
    E2 = 1 - 24*mp.nsum(lambda n: n*q**n/(1-q**n), [1, N])
    E4 = 1 + 240*mp.nsum(lambda n: n**3*q**n/(1-q**n), [1, N])
    E6 = 1 - 504*mp.nsum(lambda n: n**5*q**n/(1-q**n), [1, N])
    return E2, E4, E6

for name, w1, tau in [("lemn", varpi, 1j), ("equi", Om, rho)]:
    E2, E4, E6 = eis(mp.mpc(tau))
    g2 = (4*pi**4/3)*E4/w1**4      # 60 G4,  G4 = 2 zeta(4) E4 / w1^4
    g3 = (8*pi**6/27)*E6/w1**6     # 140 G6, G6 = 2 zeta(6) E6 / w1^6
    eta1 = (pi**2/(3*w1))*E2       # eta(w1) for zeta(z + w1) = zeta(z) + eta(w1)
    print(f"[{name}] g2 = {mp.nstr(g2, 30)}  g3 = {mp.nstr(g3, 30)}")
    print(f"[{name}] eta(w1) = {mp.nstr(eta1, 30)}")
    if name == "lemn":
        print("   pi/varpi =", mp.nstr(pi/varpi, 30), " diff", mp.nstr(abs(eta1 - pi/varpi), 5))
        print("   E2(i) - 3/pi =", mp.nstr(abs(E2 - 3/pi), 5))
    else:
        etaRho = 2*pi/(s3*Om)
        print("   2pi/(sqrt3 Om) =", mp.nstr(etaRho, 30), " diff", mp.nstr(abs(eta1 - etaRho), 5))
        print("   E2(rho) - 2sqrt3/pi =", mp.nstr(abs(E2 - 2*s3/pi), 5))
        # Legendre for (Om, rho Om): eta(w1) w2 - eta(w2) w1 = 2 pi i, eta(w2) = rhob eta(w1)
        leg = etaRho*rho*Om - rhob*etaRho*Om
        print("   Legendre (eta1 w2 - eta2 w1) / (2 pi i) =", mp.nstr(leg/(2j*pi), 30))

# ---------- direct Lean series (double precision) ----------
R = 700
m = np.arange(-R, R+1)
M, Nn = np.meshgrid(m, m, indexing="ij")
M = M.ravel().astype(float); Nn = Nn.ravel().astype(float)

def lattice(w1, w2):
    L = M*complex(w1) + Nn*complex(w2)
    return L[(M != 0) | (Nn != 0)]

def zeta(L, z):
    return 1/z + np.sum(1/(z-L) + 1/L + z/L**2)

def wp(L, z):
    return 1/z**2 + np.sum(1/(z-L)**2 - 1/L**2)

def dwp(L, z):
    return -2/z**3 - np.sum(2/(z-L)**3)

vp = float(varpi); O = float(Om); r3 = 3**0.5
rh = complex(-0.5, r3/2); rhb = rh.conjugate()
LI = lattice(vp, 1j*vp)
LR = lattice(O, rh*O)
etaI = lambda a, b: (a - b*1j)*np.pi/vp
etaRho = 2*np.pi/(r3*O)
etaR = lambda a, b: (a + b*rhb)*etaRho

print("\n--- direct Lean-series checks, box |m|,|n| <=", R, "---")
z0 = 0.37 + 0.21j
for (a, b) in [(1, 0), (0, 1), (2, -3), (-1, 4)]:
    lam = a*vp + b*1j*vp
    d = zeta(LI, z0 + lam) - zeta(LI, z0)
    print(f"E_i  eta({a}+{b}i) direct = {d:.7f}   etaI = {etaI(a,b):.7f}")
for (a, b) in [(1, 0), (0, 1), (1, 2), (3, -2)]:
    lam = a*O + b*rh*O
    d = zeta(LR, z0 + lam) - zeta(LR, z0)
    print(f"E_rho eta({a}+{b}rho) direct = {d:.7f}   etaR = {etaR(a,b):.7f}")
print("H2 period: (1+2rho) = i sqrt3:", 1 + 2*rh, "  etaR(1,2) =", etaR(1, 2), " -i sqrt3 etaRho =", -1j*r3*etaRho)

for z in [0.37 + 0.21j, 0.9 - 0.4j]:
    print(f"z={z}:  zeta_i(iz) + i zeta_i(z) = {abs(zeta(LI, 1j*z) + 1j*zeta(LI, z)):.2e};"
          f"  zeta_rho(rho z) - rhoBar zeta_rho(z) = {abs(zeta(LR, rh*z) - rhb*zeta(LR, z)):.2e}")

# Legendre with direct etas
e1 = zeta(LI, z0 + vp) - zeta(LI, z0); e2 = zeta(LI, z0 + 1j*vp) - zeta(LI, z0)
print("E_i  Legendre eta1 w2 - eta2 w1 =", e1*1j*vp - e2*vp, " (2 pi i =", 2j*np.pi, ")")
e1 = zeta(LR, z0 + O) - zeta(LR, z0); e2 = zeta(LR, z0 + rh*O) - zeta(LR, z0)
print("E_rho Legendre eta1 w2 - eta2 w1 =", e1*rh*O - e2*O)

# curve equations via the series
for name, L, g2, g3 in [("E_i", LI, 4, 0), ("E_rho", LR, 0, 4)]:
    for z in [0.37 + 0.21j, 0.6 + 0.5j]:
        x, y = wp(L, z), dwp(L, z)
        print(f"{name}: y^2 - (4x^3 - {g2}x - {g3}) at z={z}: {abs(y**2 - (4*x**3 - g2*x - g3)):.2e}  (|y^2|={abs(y**2):.2f})")

# cocycle: zeta(u+v) - zeta(u) - zeta(v) = (1/2)(wp'(u) - wp'(v))/(wp(u) - wp(v))
for name, L in [("E_i", LI), ("E_rho", LR)]:
    u, v = 0.31 + 0.17j, -0.22 + 0.41j
    lhs = zeta(L, u + v) - zeta(L, u) - zeta(L, v)
    rhs = 0.5*(dwp(L, u) - dwp(L, v))/(wp(L, u) - wp(L, v))
    print(f"{name}: cocycle residual {abs(lhs - rhs):.2e} (|lhs| = {abs(lhs):.3f})")

# integral of wp over a period = -eta  (sign check for de Rham duality)
f = lambda t: complex(wp(LI, complex(0.3 + 0.2j + t*vp)))*vp
import scipy.integrate as si
re = si.quad(lambda t: f(t).real, 0, 1, limit=200)[0]
im = si.quad(lambda t: f(t).imag, 0, 1, limit=200)[0]
print("int_gamma wp(u) du over the period varpi =", complex(re, im), " ; -eta(varpi) =", -np.pi/vp)
