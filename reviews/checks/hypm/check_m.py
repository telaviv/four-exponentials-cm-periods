# Scratch checks for REFEREE_HYP_M.md (Theorem M model gmM, corollaries).
import mpmath as mp, sympy as sp
mp.mp.dps = 60
pi = mp.pi
varpi = mp.gamma(mp.mpf(1)/4)**2/(2*mp.sqrt(2*pi))
print("varpi =", varpi)

def wp(z, w1, tau, N=200):
    # Weierstrass p for lattice w1*(Z + tau Z), q-series
    q = mp.e**(2j*pi*tau)
    u = pi*z/w1
    s = mp.mpf(0); e2 = mp.mpf(1)
    for n in range(1, N):
        t = n*q**n/(1-q**n)
        e2 -= 24*t
        s += t*mp.cos(2*n*u)
    return (pi/w1)**2*(-e2/3 + 1/mp.sin(u)**2 - 8*s)

tau = 1j
f = lambda z: wp(z, varpi, tau)
z0 = mp.mpc('0.31', '0.17')
P = f(z0); dP = mp.diff(f, z0)
print("[1] lemniscatic: |wp'^2 - (4wp^3 - 4wp)| =", mp.nstr(abs(dP**2 - (4*P**3 - 4*P)), 5))
print("    |wp(z+varpi)-wp(z)| =", mp.nstr(abs(f(z0+varpi)-P), 5),
      " |wp(iz)+wp(z)| =", mp.nstr(abs(f(1j*z0)+P), 5), "(q-series valid only for |Im(z/varpi)| < 1/2)")

# [2] Corollary M arguments are never lattice points (junk value of Mathlib's wp not reached)
for name, x in [("varpi/pi (M1, c=1)", varpi/pi), ("pi*varpi (M3, c=1)", pi*varpi)]:
    print("[2]", name, "/ varpi =", mp.nstr(x/varpi, 20), "(transcendental multiple, not in Z[i])")

# [3] sanity PSLQ: wp(varpi/pi), wp(pi varpi) satisfy no small integer polynomial
for name, x in [("wp(varpi/pi)", f(varpi/pi)), ("wp(pi*varpi)", f(pi*varpi))]:
    x = mp.re(x) if abs(mp.im(x)) < mp.mpf(10)**-40 else x
    print("[3]", name, "=", mp.nstr(x, 25))
    for deg in range(1, 7):
        r = mp.findpoly(x, deg, maxcoeff=10**5)
        if r: print("    deg", deg, "relation", r); break
    else: print("    no integer polynomial of degree <= 6, coeffs <= 1e5 [sanity only]")

# [4] (M3') edge: z with varpi*z a lattice point means z in Z[i]; e^z then transcendental (HL), so hz fails.
# [5] Control of Theorem M: u = varpi/2 (2-torsion, wp(varpi/2) = 1 algebraic), l = i pi/2 (e^l = i)
print("[5] wp(varpi/2) =", mp.nstr(f(varpi/2), 20), " -> s = 1/2 satisfies i pi u = varpi l")

# [6] exact: dim_k ker psi and C-rank of its span for adapted bases (d2 = dim A'' = r)
I = sp.I
for name, alpha, b in [("Q(i,sqrt2)", I, [1, sp.sqrt(2)]), ("Q(rho,sqrt2)", (-1+sp.sqrt(3)*I)/2, [1, sp.sqrt(2)])]:
    n = 2*len(b)
    # explicit k-basis of ker psi: u_k = alpha e_(k,0) - e_(k,1) (as in finrank_Wpsi_ge); they number r = n/2
    r = n//2
    vecs = []
    for k in range(r):
        v = [0]*n; v[2*k] = alpha; v[2*k+1] = -1; vecs.append(v)
    th = []
    for bj in b: th += [bj, alpha*bj]
    ok = all(sp.simplify(sum(th[j]*v[j] for j in range(n))) == 0 for v in vecs)
    rk = sp.Matrix(vecs).rank()
    print("[6]", name, ": n =", n, " explicit k-vectors in ker psi:", r, "valid:", ok, " C-rank:", rk,
          " dim_k ker psi = n - dim_k K =", n - r, " => d2 = dim A'' =", n - (n - r), "= r; 2*d2 <= n:", 2*r <= n)

# [7] count and Lemma U range for gmM (d0 = 1, d1 = n, d2 = r = n/2, d = 3r+1, N = d-1)
for n in range(4, 41, 2):
    r = n//2; d = 3*r + 1; N = d - 1; t = d - 2; m = n + 1
    for kappa in (n,):
        assert m > (n + 2*r - kappa)*(d - 1 - t)
        assert 2*N >= n + 2*1 + kappa
    # largest kappa within Lemma U range
    assert 2*N - n - 2 == 2*n - 2
    # with G_a wrongly placed in d2: count fails
    assert not (m > (n + 2*(r+1) - n)*1)
print("[7] count n+1 > n + 2r - kappa (kappa = n) and Lemma U 3n >= 2n + 2 hold for n = 4..40;"
      " Lemma U range is kappa <= 2n-2; with G_a counted in d2 the count would be n+1 > n+2 (false)")
