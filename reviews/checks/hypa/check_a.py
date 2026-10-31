# Referee check for CM4E/AbVar/ThmA.lean (Theorem MG-A instances).
# Curves C_N : y^N = x(1-x), N = 5, 7.  [zeta]: (x, y) -> (x, zeta*y).
# 1. Holomorphic differentials: dx/y^k, k = (N+1)/2 .. N-1 (order count at 0, 1, infinity).
# 2. One closed cycle gamma (dumbbell: ccw around 1, cw around 0), y continued by nearest-root tracking.
#    Integrate dx/y^{N-m} (m = s+1) over gamma and compare with P_s = (1 - zeta^m) B(m/N, m/N).
# 3. [zeta^e]gamma: coordinates zeta^{m e} P_s  (kappa s = s + 1).
# 4. CM type, primitivity, simplicity (stabiliser), Koblitz-Ogus label of B(1/N,1/N).
# 5. Real rank of the period vectors of [zeta^e]gamma (= 2g: full lattice in T(A)).
# 6. Side identities: B(1/5,1/5) = Gamma(1/5)^2/Gamma(2/5); Gamma(4/5)^2/Gamma(3/5) * B(1/5,1/5)/pi algebraic.
import mpmath as mp
from fractions import Fraction
from math import gcd

mp.mp.dps = 60
TOL = mp.mpf(10) ** (-50)


def holo_k(N):
    ks = []
    for k in range(1, N):
        o0 = N - 1 - k          # at x = 0 (and x = 1): x ~ t^N, y ~ t
        oinf = 2 * k - N - 1    # at infinity: x ~ t^-N, y ~ t^-2 (N odd)
        if o0 >= 0 and oinf >= 0:
            ks.append(k)
    return ks


def loop_points(N, M=4000):
    """Dumbbell loop, start x=1/2 on sheet y = rho(x) > 0. Returns list of (x(tau), x'(tau)) pieces."""
    r = mp.mpf(1) / 4
    pieces = []
    # each piece: function tau in [0,1] -> (x, dx/dtau)
    pieces.append(lambda t: (mp.mpf(1) / 2 + t / 4, mp.mpf(1) / 4))                       # 1/2 -> 3/4
    pieces.append(lambda t: (1 + r * mp.expj(mp.pi + 2 * mp.pi * t),
                             r * 2j * mp.pi * mp.expj(mp.pi + 2 * mp.pi * t)))            # ccw around 1
    pieces.append(lambda t: (mp.mpf(3) / 4 - t / 2, -mp.mpf(1) / 2))                      # 3/4 -> 1/4
    pieces.append(lambda t: (r * mp.expj(-2 * mp.pi * t),
                             -r * 2j * mp.pi * mp.expj(-2 * mp.pi * t)))                  # cw around 0
    pieces.append(lambda t: (mp.mpf(1) / 4 + t / 4, mp.mpf(1) / 4))                       # 1/4 -> 1/2
    return pieces


def track_branch(N, pieces, M=3000):
    """Nearest-root continuation of y along the loop; returns, per piece, the integer sheet offsets
    c such that y = zeta^c * y_principal, where y_principal = exp((Log x + Log(1-x))/N), on a grid."""
    zeta = mp.expj(2 * mp.pi / N)
    x0 = mp.mpf(1) / 2
    y = (x0 * (1 - x0)) ** (mp.mpf(1) / N)
    tables = []
    for pc in pieces:
        tab = []
        for i in range(M + 1):
            t = mp.mpf(i) / M
            x, _ = pc(t)
            yp = mp.exp((mp.log(x) + mp.log(1 - x)) / N)
            roots = [yp * zeta ** c for c in range(N)]
            dists = [abs(rt - y) for rt in roots]
            c = min(range(N), key=lambda j: dists[j])
            srt = sorted(dists)
            assert srt[0] < srt[1] / 10, "tracking step too coarse"
            y = roots[c]
            tab.append((t, c))
        tables.append(tab)
    return tables, y


def integrate_loop(N, k, pieces, tables, shift=0):
    """Integral of dx/y^k over [zeta^shift] gamma, using the tracked sheet (piecewise constant offsets)."""
    zeta = mp.expj(2 * mp.pi / N)
    total = mp.mpc(0)
    for pc, tab in zip(pieces, tables):
        # split each piece where the sheet offset c changes (offset jumps only where principal branch jumps)
        segs = []
        start = tab[0][0]
        cur = tab[0][1]
        for (t, c) in tab[1:]:
            if c != cur:
                segs.append((start, t, cur))  # boundary approximated on grid; refine below
                start, cur = t, c
        segs.append((start, tab[-1][0], cur))
        # refine boundaries by bisection on the principal-branch jump
        refined = []
        for i, (a, b, c) in enumerate(segs):
            refined.append([a, b, c])
        for i in range(len(refined) - 1):
            # jump lies in [b - 1/M, b] of refined[i]
            M = len(tab) - 1
            lo, hi = refined[i][1] - mp.mpf(1) / M, refined[i][1]
            c_lo = refined[i][2]

            def ycont(t, c):
                x, _ = pc(t)
                return mp.exp((mp.log(x) + mp.log(1 - x)) / N) * zeta ** c
            yref = ycont(lo, c_lo)
            for _ in range(200):
                mid = (lo + hi) / 2
                # is mid still on branch c_lo continuous with yref?
                if abs(ycont(mid, c_lo) - yref) < abs(ycont(mid, refined[i + 1][2]) - yref):
                    lo = mid
                    yref = ycont(mid, c_lo)
                else:
                    hi = mid
            refined[i][1] = hi
            refined[i + 1][0] = hi
        for (a, b, c) in refined:
            def f(t, c=c):
                x, dx = pc(t)
                y = mp.exp((mp.log(x) + mp.log(1 - x)) / N) * zeta ** (c + shift)
                return y ** (-k) * dx
            total += mp.quad(f, [a, (a + b) / 2, b])
    return total


def cm_checks(N, g):
    units = [u for u in range(1, N) if gcd(u, N) == 1]
    # eigencharacter of [zeta]^* on dx/y^k is zeta^{-k}; m = N - k
    Phi = sorted({(-k) % N for k in holo_k(N)})
    neg = sorted({(-u) % N for u in Phi})
    stab = [a for a in units if sorted({(a * u) % N for u in Phi}) == Phi]
    # proper CM subfields <-> subgroups H of units not containing -1 ... primitive iff stabiliser trivial
    KO = [u for u in units
          if Fraction(u % N, N) + Fraction(u % N, N) + Fraction((u * (N - 2)) % N, N) == 1]
    return Phi, neg, stab, KO


out = []
for (N, g) in [(5, 2), (7, 3)]:
    zeta = mp.expj(2 * mp.pi / N)
    ks = holo_k(N)
    out.append(f"=== N = {N}, g = {g} ===")
    out.append(f"holomorphic dx/y^k for k = {ks}  (count {len(ks)} = g: {len(ks) == g})")
    Phi, neg, stab, KO = cm_checks(N, g)
    out.append(f"CM type (eigencharacters zeta^m of [zeta]^* on holomorphic forms): {Phi}; -Phi = {neg}; "
               f"disjoint & cover: {sorted(Phi + neg) == list(range(1, N))}")
    out.append(f"stabiliser of Phi in (Z/N)^x: {stab}  (trivial => primitive => A simple, End^0 = Q(zeta_N))")
    out.append(f"Koblitz-Ogus label Phi_(1,1): {KO}  (= Phi: {KO == Phi})")
    pieces = loop_points(N)
    tables, yend = track_branch(N, pieces)
    y0 = (mp.mpf(1) / 4) ** (mp.mpf(1) / N)
    out.append(f"loop closed: |y_end - y_start| = {mp.nstr(abs(yend - y0), 5)}")
    for s in range(g):
        m = s + 1
        k = N - m
        P = (1 - zeta ** m) * mp.beta(mp.mpf(m) / N, mp.mpf(m) / N)
        I0 = integrate_loop(N, k, pieces, tables, 0)
        out.append(f" s={s}: kappa=m={m}, form dx/y^{k}: P_s = {mp.nstr(P, 25)}")
        out.append(f"       int_gamma = {mp.nstr(I0, 25)}   |diff| = {mp.nstr(abs(I0 - P), 5)}  ok={abs(I0 - P) < TOL}")
        for e in range(1, N):
            Ie = integrate_loop(N, k, pieces, tables, e)
            pred = zeta ** (m * e) * P
            ok = abs(Ie - pred) < TOL
            if e <= 2 or not ok:
                out.append(f"       [zeta^{e}]gamma: |int - zeta^(m e) P| = {mp.nstr(abs(Ie - pred), 5)} ok={ok}")
        # check: [zeta]^*(dx/y^k) = zeta^{-k} dx/y^k = zeta^m dx/y^k
        out.append(f"       zeta^(-k) == zeta^m : {abs(zeta ** (-k) - zeta ** m) < TOL}")
    # real rank of period vectors of [zeta^e]gamma, e = 0..N-1
    rows = []
    for e in range(N):
        v = []
        for s in range(g):
            m = s + 1
            P = (1 - zeta ** m) * mp.beta(mp.mpf(m) / N, mp.mpf(m) / N)
            z = zeta ** (m * e) * P
            v += [mp.re(z), mp.im(z)]
        rows.append(v)
    Mx = mp.matrix(rows)
    sv = mp.svd_r(Mx, compute_uv=False)
    out.append(f"singular values of the {N} x {2*g} real period matrix: {[mp.nstr(x, 6) for x in sv]} "
               f"(rank 2g = {2*g} iff smallest > 0)")
    out.append(f"P_(s0)/pi = {mp.nstr((1 - zeta) * mp.beta(mp.mpf(1)/N, mp.mpf(1)/N) / mp.pi, 30)}")
    # (P/pi) low-degree algebraic test (PSLQ on powers up to degree 2N over Q(zeta) is heavy; do real part degree 8)
    B = mp.beta(mp.mpf(1) / N, mp.mpf(1) / N) / mp.pi
    rel = mp.findpoly(B, 8, maxcoeff=10**6)
    out.append(f"findpoly(B(1/N,1/N)/pi, deg 8, coeff 1e6): {rel}  (None expected)")

# side identities
B5 = mp.beta(mp.mpf(1) / 5, mp.mpf(1) / 5)
out.append("=== side identities ===")
out.append(f"B(1/5,1/5) - Gamma(1/5)^2/Gamma(2/5) = {mp.nstr(B5 - mp.gamma(mp.mpf(1)/5)**2 / mp.gamma(mp.mpf(2)/5), 5)}")
t3 = mp.gamma(mp.mpf(4) / 5) ** 2 / mp.gamma(mp.mpf(3) / 5)
ratio = t3 * B5 / mp.pi
alg = mp.sin(2 * mp.pi / 5) / mp.sin(mp.pi / 5) ** 2
out.append(f"Gamma(4/5)^2/Gamma(3/5) * B(1/5,1/5)/pi = {mp.nstr(ratio, 30)}; sin(2pi/5)/sin(pi/5)^2 = {mp.nstr(alg, 30)}; "
           f"diff {mp.nstr(ratio - alg, 5)}")
B7 = mp.beta(mp.mpf(1) / 7, mp.mpf(1) / 7)
out.append(f"B(1/7,1/7) - Gamma(1/7)^2/Gamma(2/7) = {mp.nstr(B7 - mp.gamma(mp.mpf(1)/7)**2 / mp.gamma(mp.mpf(2)/7), 5)}")
# Riemann bilinear sanity: P_sigma * P_sigmabar in pi*Qbar (second-kind slot via B((N-m)/N,(N-m)/N))
for N in (5, 7):
    zeta = mp.expj(2 * mp.pi / N)
    P1 = (1 - zeta) * mp.beta(mp.mpf(1) / N, mp.mpf(1) / N)
    Pbar = (1 - zeta ** (N - 1)) * mp.beta(mp.mpf(N - 1) / N, mp.mpf(N - 1) / N)
    out.append(f"N={N}: P_1 * P_(N-1) / pi = {mp.nstr(P1 * Pbar / mp.pi, 25)} "
               f"vs closed form 4 sin(2pi/N)/(1-2/N) = {mp.nstr(4*mp.sin(2*mp.pi/N)/(1-mp.mpf(2)/N), 25)}, "
               f"diff {mp.nstr(P1*Pbar/mp.pi - 4*mp.sin(2*mp.pi/N)/(1-mp.mpf(2)/N), 5)}")

text = "\n".join(out)
print(text)
with open("check_a.out", "w") as fh:
    fh.write(text + "\n")
