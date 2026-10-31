"""REFEREE_HYP_MGK numerics (mpmath, 50 digits).

[A] kappa_1 = (eta(alpha w) - conj(alpha) eta(w)) / ((alpha - conj alpha) w) for latI, latRho, and two
    control lattices with kappa_1 != 0 (Z[sqrt-2], Z[(1+sqrt-7)/2]), eta from E2 and checked against a direct
    zeta-series difference.
[B] For latI: the eta0 forced by Lean's `legendre` field equals eta(w); etaL m n = eta(m w + n alpha w).
[C] Control: for a kappa_1 != 0 lattice, the lamMGnK generator (u, zeta(u)) would have conjugate-eigen
    fibre coordinate zeta(u) - kappa_1 u != zeta(u), so the stored fibre value is off by kappa_1 u.
[D] Lemma U / count table for gmMGK, gmMGnK.
"""
from mpmath import mp, mpf, mpc, pi, exp, gamma, sqrt, conj, fabs, nsum, inf

mp.dps = 50
I = mpc(0, 1)


def E2(tau, terms=400):
    q = exp(2 * pi * I * tau)
    s = mpc(0)
    qn = mpc(1)
    for n in range(1, terms):
        qn *= q
        s += n * qn / (1 - qn)
    return 1 - 24 * s


def eta_pair(w1, w2):
    """quasi-periods (eta(w1), eta(w2)) for Im(w2/w1) > 0."""
    tau = w2 / w1
    e1 = pi ** 2 / (3 * w1) * E2(tau)
    e2 = (e1 * w2 - 2 * pi * I) / w1  # Legendre
    return e1, e2


def zeta_direct(z, w1, w2, N=60):
    s = 1 / z
    for m in range(-N, N + 1):
        for n in range(-N, N + 1):
            if m == 0 and n == 0:
                continue
            l = m * w1 + n * w2
            s += 1 / (z - l) + 1 / l + z / l ** 2
    return s


varpi = gamma(mpf(1) / 4) ** 2 / (2 * sqrt(2 * pi))
omR = gamma(mpf(1) / 3) ** 3 / (mpf(2) ** (mpf(4) / 3) * pi)
rho = (-1 + I * sqrt(3)) / 2

lattices = {
    "latI  (w=varpi, a=i)": (varpi, I),
    "latRho(w=Om_rho, a=rho)": (omR, rho),
    "Z[sqrt-2] (w=1)": (mpf(1), I * sqrt(2)),
    "Z[(1+sqrt-7)/2] (w=1)": (mpf(1), (1 + I * sqrt(7)) / 2),
}

print("[A] kappa_1 per lattice")
for name, (w, a) in lattices.items():
    e1, e2 = eta_pair(w, a * w)
    k1 = (e2 - conj(a) * e1) / ((a - conj(a)) * w)
    print(f"  {name:28s} kappa_1 = {mp.nstr(k1, 15)}")

# direct check of eta for latI through the zeta series (slow-ish, low precision is enough)
mp.dps = 20
w, a = varpi, I
z0 = mpc("0.31", "0.17")
eta_w = zeta_direct(z0 + w, w, a * w) - zeta_direct(z0, w, a * w)
eta_aw = zeta_direct(z0 + a * w, w, a * w) - zeta_direct(z0, w, a * w)
print("  direct series (N=60, truncation ~1e-2 rel. on non-abs. conv. sums are symmetric):")
print("    eta(varpi) =", mp.nstr(eta_w, 8), "  pi/varpi =", mp.nstr(pi / varpi, 8))
print("    eta(i varpi) =", mp.nstr(eta_aw, 8), "  -i pi/varpi =", mp.nstr(-I * pi / varpi, 8))
mp.dps = 50

print("[B] latI: eta0 from Lean legendre field vs eta(varpi); etaL")
w, a = varpi, I
eta0 = 2 * pi * I / (w * (a - conj(a)))
e1, e2 = eta_pair(w, a * w)
print("  |eta0 - eta(w)|      =", mp.nstr(fabs(eta0 - e1), 5))
for (m, n) in [(1, 0), (0, 1), (2, -3), (-5, 7)]:
    etaL = (m + n * conj(a)) * eta0
    true = m * e1 + n * e2
    print(f"  m,n={m:3d},{n:3d}: |etaL - eta(mw+naw)| = {mp.nstr(fabs(etaL - true), 5)}")
w, a = omR, rho
eta0 = 2 * pi * I / (w * (a - conj(a)))
e1, e2 = eta_pair(w, a * w)
print("  latRho: |eta0 - eta(w)| =", mp.nstr(fabs(eta0 - e1), 5), ", |eta0 - 2pi/(sqrt3 w)| =",
      mp.nstr(fabs(eta0 - 2 * pi / (sqrt(3) * w)), 5),
      ", |eta(rho w) - conj(rho) eta(w)| =", mp.nstr(fabs(e2 - conj(a) * e1), 5))

print("[C] kappa_1 != 0 control, Z[sqrt-2]: eta0 forced by legendre vs eta(w)")
w, a = mpf(1), I * sqrt(2)
eta0 = 2 * pi * I / (w * (a - conj(a)))
e1, e2 = eta_pair(w, a * w)
k1 = (e2 - conj(a) * e1) / ((a - conj(a)) * w)
print("  eta0 (= eta*(w)) =", mp.nstr(eta0, 12), "  eta(w) =", mp.nstr(e1, 12), "  eta(w)-kappa1 w =",
      mp.nstr(e1 - k1 * w, 12))
print("  so etaL = eta* at lattice points, but LogNat's 2nd disjunct uses zeta, not zeta* = zeta - kappa1 z:")
print("  a generator (u, zeta(u)) has conjugate-eigen fibre zeta*(u) = zeta(u) - kappa1 u; offset kappa1 =",
      mp.nstr(k1, 12))

print("[D] counts (n = [K:Q])")
for n in [4, 6, 8, 12]:
    # gmMGK
    d2 = n // 2
    d = 2 * n + d2
    m = 3 * n
    kap = n
    ok54 = m > (2 * n + 2 * d2 - kap) * 1
    lemU = 2 * (d - 1) >= 2 * n + kap
    # gmMGnK
    d2n = n // 2 + 1
    dn = 2 * n + d2n
    ok54n = m > (2 * n + 2 * d2n - kap) * 1
    lemUn = 2 * (dn - 1) >= 2 * n + kap
    lemUn_worst = 2 * (dn - 1) >= 2 * n + (3 * n - 1)
    print(f"  n={n:2d}  MGK: d={d}, (5.4) {m}>{2*n+2*d2-kap}: {ok54}, LemmaU(k=n): {lemU}, "
          f"worst k=3n-1: {2*(d-1) >= 2*n+3*n-1} | MGnK: d={dn}, (5.4) {m}>{2*n+2*d2n-kap}: {ok54n}, "
          f"LemmaU(k=n): {lemUn}, worst: {lemUn_worst}")
