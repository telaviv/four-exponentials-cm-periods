"""Checks for REFEREE_HYP_GEN.md.
Part A (exact, sympy): Lemma K / dim ker(phi), dim ker(psi), C-rank of their spans, for adapted bases
  theta = (b_j, alpha b_j) of K = k(cbrt 2), k = Q(i) and Q(rho) (n = 6, r = 3), and K = k(sqrt2, sqrt3)? (n = 8).
Part B (mpmath, 40 digits): quasi-periods via E2 for latI, latRho; Legendre in the CMLattice form
  omega*eta0*(alpha - conj alpha) = 2 pi i; eta(alpha omega) = conj(alpha) eta(omega); the sign flip when Im alpha < 0.
"""
import sympy as sp
import mpmath as mp

# ---------------- Part A ----------------
def lemmaK(alpha_p, alpha_q, gens, name):
    # k = Q(alpha), alpha^2 = p + q alpha. K = k(gens) with Q-basis of K/k given by monomials 'mons' in commuting
    # algebraic numbers gens (list of (symbol, minpoly relation exponent d, value c): g^d = c).
    a = sp.Symbol('a')
    syms = [g[0] for g in gens]
    import itertools
    mons = list(itertools.product(*[range(g[1]) for g in gens]))   # k-basis b of K
    r = len(mons)
    def reduce(e):
        e = sp.expand(e)
        changed = True
        while changed:
            changed = False
            P = sp.Poly(e, a, *syms)
            out = 0
            for monom, c in P.terms():
                ea = monom[0]; es = list(monom[1:])
                term = c
                if ea >= 2:
                    term *= a**(ea-2) * (alpha_p + alpha_q*a); changed = True
                else:
                    term *= a**ea
                for i, (s, d, cc) in enumerate(gens):
                    if es[i] >= d:
                        term *= s**(es[i]-d) * cc; changed = True
                    else:
                        term *= s**es[i]
                out += term
            e = sp.expand(out)
        return e
    def coords(e):
        e = reduce(e)
        P = sp.Poly(e, a, *syms)
        v = []
        for ea in range(2):
            for mo in mons:
                v.append(P.coeff_monomial(a**ea * sp.Mul(*[s**k for s, k in zip(syms, mo)])))
        return v
    bvals = [sp.Mul(*[s**k for s, k in zip(syms, mo)]) for mo in mons]
    theta = [bj for bj in bvals] + [a*bj for bj in bvals]      # index (j,0) then (j,1)
    n = len(theta)
    abar = alpha_q - a
    # m_j = x_j + y_j alpha ; psi(m) = sum theta_j m_j ; phi(m) = sum theta_j conj(m_j) = sum theta_j (x_j + y_j abar)
    cols_psi, cols_phi = [], []
    for j in range(n):
        cols_psi.append(coords(theta[j]));      cols_phi.append(coords(theta[j]))       # x_j
    for j in range(n):
        cols_psi.append(coords(theta[j]*a));    cols_phi.append(coords(theta[j]*abar))  # y_j
    Mpsi = sp.Matrix(cols_psi).T; Mphi = sp.Matrix(cols_phi).T
    kpsi = Mpsi.nullspace(); kphi = Mphi.nullspace()
    both = sp.Matrix.vstack(Mpsi, Mphi)
    # C-rank of span of ker phi in C^n: numeric alpha value
    if alpha_q == 0: aval = sp.sqrt(-alpha_p)*sp.I if alpha_p < 0 else None
    aval = (alpha_q + sp.sqrt(alpha_q**2 + 4*alpha_p))/2   # root with Im>0 (sqrt of negative -> I*...)
    def cvec(v):
        return [sp.N(v[j] + v[n+j]*aval, 30) for j in range(n)]
    rk = lambda vs: sp.Matrix([cvec(v) for v in vs]).rank(iszerofunc=lambda x: abs(complex(x)) < 1e-20) if vs else 0
    print(f"{name}: n={n}, det(psi,phi)={both.det()}, dim_Q ker psi={len(kpsi)}, dim_Q ker phi={len(kphi)}, "
          f"C-rank span ker psi={rk(kpsi)}, C-rank span ker phi={rk(kphi)}  (expect n, n, n/2, n/2)")

c2 = sp.Symbol('c2'); s2 = sp.Symbol('s2'); s3 = sp.Symbol('s3')
lemmaK(-1, 0, [(c2, 3, 2)], "K=Q(i, 2^(1/3))")
lemmaK(-1, -1, [(c2, 3, 2)], "K=Q(rho, 2^(1/3))")
lemmaK(-1, 0, [(s2, 2, 2), (s3, 2, 3)], "K=Q(i, sqrt2, sqrt3)")
lemmaK(-2, 0, [(s3, 2, 3)], "K=Q(sqrt-2, sqrt3)")

# ---------------- Part B ----------------
mp.mp.dps = 40
def E2(tau):
    q = mp.exp(2j*mp.pi*tau)
    s = mp.mpf(0); qn = mp.mpc(1)
    for k in range(1, 200):
        qn *= q
        s += mp.mpf(sum(d for d in range(1, k+1) if k % d == 0)) * qn
    return 1 - 24*s
def eta(w1, w2):
    """eta(w1) = zeta(z+w1)-zeta(z) for the lattice Z w1 + Z w2 (requires Im(w2/w1) > 0)."""
    tau = w2/w1
    assert mp.im(tau) > 0
    return mp.pi**2/(3*w1) * E2(tau)

varpi = mp.gamma(mp.mpf(1)/4)**2/(2*mp.sqrt(2*mp.pi))
Orho = mp.gamma(mp.mpf(1)/3)**3/(mp.mpf(2)**(mp.mpf(4)/3)*mp.pi)
rho = (-1 + 1j*mp.sqrt(3))/2
print("varpi =", mp.nstr(varpi, 20), " Omega_rho =", mp.nstr(Orho, 20))
for name, w, al, eta0 in [("latI", varpi, 1j, mp.pi/varpi), ("latRho", Orho, rho, 2*mp.pi/(mp.sqrt(3)*Orho))]:
    e1 = eta(w, al*w)                 # eta(omega)
    e2 = eta(al*w, -w)                # eta(alpha omega), basis (alpha w, -w) has Im(-1/alpha) > 0
    print(f"{name}: eta(omega) - eta0 = {mp.nstr(abs(e1-eta0), 3)};  eta(alpha omega) - conj(alpha) eta0 = "
          f"{mp.nstr(abs(e2-mp.conj(al)*eta0), 3)};  omega eta0 (alpha - conj alpha) - 2 pi i = "
          f"{mp.nstr(abs(w*eta0*(al-mp.conj(al)) - 2j*mp.pi), 3)}")
    # generic Legendre (Im(w2/w1) > 0):  eta(w1) w2 - eta(w2) w1 = 2 pi i
    print(f"   Legendre eta1 w2 - eta2 w1 - 2 pi i = {mp.nstr(abs(e1*al*w - e2*w - 2j*mp.pi), 3)}")
    # Im alpha < 0: the same lattice with alpha' = conj(alpha) (Z[alpha'] = Z[alpha]); the CMLattice field
    # 'legendre' would force eta0' = 2 pi i / (omega (alpha' - conj alpha')) = -eta(omega)
    alc = mp.conj(al)
    eta0p = 2j*mp.pi/(w*(alc - mp.conj(alc)))
    print(f"   alpha' = conj(alpha) (Im<0): forced eta0' = {mp.nstr(eta0p, 12)}, true eta(omega) = {mp.nstr(e1, 12)}")

# g2, g3 sanity (Eisenstein, 40 digits): g2 = (4 pi^4 / 3) E4 / w^4, g3 = (8 pi^6 / 27) E6 / w^6
def Ek(tau, k, c):
    q = mp.exp(2j*mp.pi*tau); s = 0; qn = mp.mpc(1)
    for m in range(1, 200):
        qn *= q
        s += mp.mpf(sum(d**(k-1) for d in range(1, m+1) if m % d == 0)) * qn
    return 1 + c*s
for name, w, al in [("latI", varpi, 1j), ("latRho", Orho, rho)]:
    g2 = 4*mp.pi**4/3*Ek(al, 4, 240)/w**4; g3 = 8*mp.pi**6/27*Ek(al, 6, -504)/w**6
    print(f"{name}: g2 = {mp.nstr(g2, 15)}, g3 = {mp.nstr(g3, 15)}")
