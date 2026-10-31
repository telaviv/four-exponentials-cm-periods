"""Checks for REFEREE_HYP_SMG.md (Theorem S: gmSMG, gmSMGn, frame2_false, NotLtilde).

1. Quasi-periods of latI, latRho: eta(omega) = pi^2 E2(tau) / (3 omega) equals the Lean eta0 (Legendre form).
2. dim_k ker psi = dim_k ker phi = n/2 for the Lean theta (exact, sympy), so d2(SMG) = n/2, d2(SMGn) = n/2 + 1.
3. The (5.4) count of frame2_false and the Lemma U range 2N >= d1 + 2 d0 + kappa, for n = 4..40.
4. PSLQ sanity (weak, [Numerical]): varpi, pi/varpi, Omega_rho, 2pi/(sqrt3 Omega_rho) are not small
   Q(i, sqrt2, sqrt3)-combinations of 1, pi, log 2, log 3, log 5.
"""
import mpmath as mp
import sympy as sp

mp.mp.dps = 60

# ---------- 1. quasi-periods ----------
def E2(tau, N=400):
    q = mp.exp(2j * mp.pi * tau)
    return 1 - 24 * mp.nsum(lambda k: k * q**k / (1 - q**k), [1, mp.inf])

varpi = mp.gamma(mp.mpf(1) / 4) ** 2 / (2 * mp.sqrt(2 * mp.pi))
omr = mp.gamma(mp.mpf(1) / 3) ** 3 / (mp.mpf(2) ** (mp.mpf(4) / 3) * mp.pi)
rho = (-1 + 1j * mp.sqrt(3)) / 2
for name, om, tau, eta0 in [("latI", varpi, 1j, mp.pi / varpi),
                            ("latRho", omr, rho, 2 * mp.pi / (mp.sqrt(3) * omr))]:
    eta = mp.pi**2 * E2(tau) / (3 * om)
    leg = om * eta0 * (tau - mp.conj(tau)) - 2j * mp.pi
    print(f"[1] {name}: |eta(omega) - eta0| = {mp.nstr(abs(eta - eta0), 5)}, |Legendre defect| = {mp.nstr(abs(leg), 5)}")

# ---------- 2. dim ker psi, ker phi (exact) ----------
I = sp.I
def kdims(bs):
    # theta(j,0) = b_j, theta(j,1) = i b_j; k = Q(i). Unknowns m = u + v i (u, v rational), n = 2r coordinates.
    th = []
    for b in bs:
        th += [b, I * b]
    n = len(th)
    u = sp.symbols(f"u0:{n}"); v = sp.symbols(f"v0:{n}")
    res = {}
    for name, conj in [("psi", False), ("phi", True)]:
        expr = sp.expand(sum(t * (uu - I * vv if conj else uu + I * vv) for t, uu, vv in zip(th, u, v)))
        # write expr in a Q-basis of Q(i, sqrt2, sqrt3): coefficients of 1, s2, s3, s6, times 1, i
        s2, s3 = sp.sqrt(2), sp.sqrt(3)
        basis = [1, s2, s3, s2 * s3]
        eqs = []
        re, im = sp.re(expr), sp.im(expr)
        for part in (re, im):
            part = sp.expand(part)
            p = sp.Poly(part.subs({s2 * s3: sp.Symbol("S6")}).subs({s2: sp.Symbol("S2"), s3: sp.Symbol("S3")}),
                        sp.Symbol("S2"), sp.Symbol("S3"), sp.Symbol("S6"))
            for mon, c in p.terms():
                eqs.append(c)
        M = sp.Matrix([[sp.diff(e, x) for x in list(u) + list(v)] for e in eqs])
        dimQ = 2 * n - M.rank()
        res[name] = sp.Rational(dimQ, 2)  # k-dimension
    return n, res

for bs in [[1, sp.sqrt(2)], [1, sp.sqrt(3)], [1, sp.sqrt(2), sp.sqrt(3), sp.sqrt(6)]]:
    n, res = kdims(bs)
    print(f"[2] b = {bs}: n = {n}, dim_k ker psi = {res['psi']}, dim_k ker phi = {res['phi']} (n/2 = {n//2});"
          f" d2(SMG) = n/2 = {n//2}, d2(SMGn) = n/2 + 1 = {n//2 + 1}")

# ---------- 3. (5.4) and Lemma U ----------
ok = True
for n in range(4, 41, 2):
    for model, d0, d2 in [("SMG", 2, n // 2), ("SMGn", 1, n // 2 + 1)]:
        d1 = 2 * n
        d = d0 + d1 + d2
        N = d - 1
        m, kappa = 3 * n, n
        # (5.4) with d - 1 - t in {0, 1}
        for e in (0, 1):
            if not (m > (d1 + 2 * d2 - kappa) * e):
                ok = False; print("  (5.4) FAILS", model, n, e)
        # Lemma U at the application (kappa = n)
        if not (2 * N >= d1 + 2 * d0 + kappa):
            ok = False; print("  Lemma U FAILS at application", model, n)
        # Lemma U over all instances: kappa <= dim_Q Omega_Q = 2n (toric) + n (G2 periods) = 3n
        bad = [k for k in range(0, 3 * n + 1) if not (2 * N >= d1 + 2 * d0 + k)]
        # instances with kappa > n have V containing a rational toric period line (the conclusion holds outright)
        if any(k <= n for k in bad):
            ok = False; print("  Lemma U fails with kappa <= n", model, n, bad)
        if n in (4, 6, 40):
            print(f"[3] {model} n={n}: d={d}, 2N={2*N}, d1+2d0+kappa(app)={d1+2*d0+kappa}, "
                  f"(5.4) margin (e=1) = {m - (d1 + 2*d2 - kappa)}, kappa values outside Lemma U: {bad}")
print("[3] all (5.4) / Lemma U checks:", "OK" if ok else "FAIL")

# ---------- 4. PSLQ sanity ----------
mp.mp.dps = 260
varpi = mp.gamma(mp.mpf(1) / 4) ** 2 / (2 * mp.sqrt(2 * mp.pi))
omr = mp.gamma(mp.mpf(1) / 3) ** 3 / (mp.mpf(2) ** (mp.mpf(4) / 3) * mp.pi)
s2, s3 = mp.sqrt(2), mp.sqrt(3)
gens = [1, mp.pi, mp.log(2), mp.log(3), mp.log(5)]
for name, x in [("varpi", varpi), ("pi/varpi", mp.pi / varpi), ("Omega_rho", omr),
                ("2pi/(sqrt3 Omega_rho)", 2 * mp.pi / (s3 * omr))]:
    vec = [x] + [c * g for c in (1, s2, s3, s2 * s3) for g in gens]
    rel = mp.pslq(vec, tol=mp.mpf(10)**-220, maxcoeff=10**3, maxsteps=10**6)
    print(f"[4] {name}: PSLQ relation over Q(sqrt2,sqrt3)*{{1,pi,log2,log3,log5}} (coeff <= 1e3): {rel}")
