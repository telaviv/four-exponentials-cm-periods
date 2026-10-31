"""Numerical sanity checks for REFEREE_HYP_MXG.md (mpmath, 80 digits).

1. The paper's MX1 illustration: u with wp(u) = 2 on E_i (g2 = 4, g3 = 0),
   u = 0.72694593546890819853..., and  varpi*Omega_rho*zeta(u)/(pi*u) = 3.76379062156897182773...
   zeta is the Weierstrass zeta (Laurent series, valid for |z| < varpi), the same function as
   CM4E.Ext.Weierstrass.zeta (checked against the Lean series in reviews/checks/hypmx/).
2. findpoly (degree <= 8, coefficients <= 10^8) finds no algebraic relation for the numbers whose
   transcendence the named inputs assert: varpi*Omega/pi (hGamma), Omega/varpi (hM, from WuestholzMX),
   zeta(u) (LaurentZeta), and the MX1 value.  [Numerical evidence only.]
3. The trivial identities behind ker psi ∩ ker phi = 0 for ANY Q-independent theta (psi - phi, psi + phi), and the
   MX1 relation with beta = q*sqrt(3)/2, evaluated numerically.
"""
from mpmath import mp, mpf, gamma, sqrt, pi, quad, inf, findpoly, mpc

mp.dps = 80
varpi = gamma(mpf(1)/4)**2 / (2*sqrt(2*pi))
Omega = gamma(mpf(1)/3)**3 / (mpf(2)**(mpf(4)/3) * pi)
print("varpi  =", mp.nstr(varpi, 30))
print("Omega  =", mp.nstr(Omega, 30))

# Laurent coefficients of wp = 1/z^2 + sum_{k>=2} c_k z^{2k-2}
g2, g3 = mpf(4), mpf(0)
K = 400
c = [mpf(0)]*(K+1)
c[2] = g2/20; c[3] = g3/28
for k in range(4, K+1):
    c[k] = mpf(3)/((2*k+1)*(k-3)) * sum(c[m]*c[k-m] for m in range(2, k-1))
wp   = lambda z: 1/z**2 + sum(c[k]*z**(2*k-2) for k in range(2, K+1))
zeta = lambda z: 1/z - sum(c[k]*z**(2*k-1)/(2*k-1) for k in range(2, K+1))

u = quad(lambda x: 1/sqrt(4*x**3 - 4*x), [2, 10, inf])
print("u      =", mp.nstr(u, 30), " (paper: 0.72694593546890819853)")
print("wp(u)-2 =", mp.nstr(wp(u) - 2, 5))
zu = zeta(u)
V = varpi*Omega*zu/(pi*u)
print("zeta(u) =", mp.nstr(zu, 30))
print("MX1 value varpi*Omega*zeta(u)/(pi*u) =", mp.nstr(V, 30), " (paper: 3.76379062156897182773)")

# eta(Omega_rho) Legendre check used by P2 / V'': eta_rho*Omega = 2 pi/sqrt3
eta_rho = 2*pi/(sqrt(3)*Omega)
print("varpi*(2/sqrt3)*(pi/varpi) - Omega*eta_rho =", mp.nstr(varpi*(2/sqrt(3))*(pi/varpi) - Omega*eta_rho, 5))

# MX1: beta = q sqrt3/2 makes (u+a) beta eta_rho = (zeta(u)+t) varpi, here a = t = 0
q = V; beta = q*sqrt(3)/2
print("MX1 relation residual:", mp.nstr(u*beta*eta_rho - zu*varpi, 5))

for name, x in [("varpi*Omega/pi", varpi*Omega/pi), ("Omega/varpi", Omega/varpi),
                ("zeta(u)", zu), ("MX1 value", V)]:
    print("findpoly(%s, deg<=8, coeff<=1e8):" % name, findpoly(x, 8, maxcoeff=10**8))

# Lemma K for any Q-independent theta: psi(m)-phi(m) = (w - wbar) theta.v, psi(m)+phi(m) = 2 theta.u + (w + wbar) theta.v,
# so psi(m) = phi(m) = 0 forces theta.v = 0, then theta.u = 0, i.e. m = 0 (theta Q-independent; no field structure used)
import random
random.seed(1)
theta = [mpf(1), sqrt(2), mpc(0,1), mpc(0,1)*sqrt(2)]          # K = Q(i, sqrt2): rho not in K
rho = mpc(-1, sqrt(3))/2
for w in (mpc(0,1), rho):
    for _ in range(3):
        uu = [random.randint(-9, 9) for _ in theta]; vv = [random.randint(-9, 9) for _ in theta]
        m = [a + b*w for a, b in zip(uu, vv)]
        psi = sum(t*x for t, x in zip(theta, m)); phi = sum(t*x.conjugate() for t, x in zip(theta, m))
        tu = sum(t*a for t, a in zip(theta, uu)); tv = sum(t*b for t, b in zip(theta, vv))
        r1 = abs(psi + phi - 2*tu - (w + w.conjugate())*tv); r2 = abs(psi - phi - (w - w.conjugate())*tv)
        assert r1 < mpf(10)**-70 and r2 < mpf(10)**-70
print("Lemma K identities psi+-phi verified on samples (k = Q(i), Q(rho); K = Q(i, sqrt2), rho not in K)")
