"""Exact check of Lemma K for K = Q(i, sqrt3), theta = (1, i, sqrt3, i sqrt3), k = Q(i) and k = Q(rho).
(psi, phi): k^4 -> K x K, psi(m) = sum theta_j m_j, phi(m) = sum theta_j conj(m_j).
Also: the H2 / preW Psi''-images, Legendre for etaRho, and the rank of the 16 period generators."""
import sympy as sp

I, s3 = sp.I, sp.sqrt(3)
theta = [1, I, s3, I*s3]
rho = (-1 + I*s3)/2

def Kcoords(x):
    """coordinates of x in K w.r.t. theta (x = c0 + c1 i + c2 sqrt3 + c3 i sqrt3)."""
    x = sp.expand(x)
    re, im = sp.re(x), sp.im(x)
    re, im = sp.expand(re), sp.expand(im)
    c0 = re.subs(s3, 0); c2 = sp.expand((re - c0)/s3)
    c1 = im.subs(s3, 0); c3 = sp.expand((im - c1)/s3)
    out = [sp.nsimplify(c) for c in (c0, c1, c2, c3)]
    assert sp.simplify(out[0] + I*out[1] + s3*out[2] + I*s3*out[3] - x) == 0
    return out

for name, gen in [("Q(i)", I), ("Q(rho)", rho)]:
    gbar = sp.conjugate(gen)
    cols = []
    # Q-basis of k^4: e_j, gen*e_j
    for j in range(4):
        for c in (1, gen):
            cb = sp.conjugate(c)
            psi = theta[j]*c
            phi = theta[j]*cb
            cols.append(Kcoords(psi) + Kcoords(phi))
    Mx = sp.Matrix(cols).T   # 8 x 8 rational
    print(name, "det (psi,phi) =", Mx.det(), " rank =", Mx.rank())
    Mpsi = Mx[:4, :]; Mphi = Mx[4:, :]
    print("   dim_Q ker psi =", 8 - Mpsi.rank(), " dim_Q ker phi =", 8 - Mphi.rank(),
          " dim_Q (ker psi cap ker phi) =", 8 - Mx.rank())

# Legendre-type identities used by preW2 / V''
Om, vp = sp.symbols("Omega varpi", positive=True)
etaRho = 2*sp.pi/(s3*Om); etaI = sp.pi/vp
print("etaRho*Omega - 2 pi/sqrt3 =", sp.simplify(etaRho*Om - 2*sp.pi/s3))
print("varpi*(2/sqrt3)*etaI - Omega*etaRho =", sp.simplify(vp*2/s3*etaI - Om*etaRho))
print("Legendre rho: etaRho*(rho*Om) - conj(rho)*etaRho*Om - 2 pi i =",
      sp.simplify(etaRho*rho*Om - sp.conjugate(rho)*etaRho*Om - 2*sp.pi*I))
print("1 + 2 rho - i sqrt3 =", sp.simplify(1 + 2*rho - I*s3),
      "; eta((1+2rho)Om)/etaRho = 1 + 2 conj(rho) =", sp.simplify(1 + 2*sp.conjugate(rho)))
