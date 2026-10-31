# Referee check for CM4E/AbVar/ThmAn.lean (Theorem MG-natural-A, instance y^5 = x(1-x)).
# Independent of checks/hypa/check_a.py: different loop (figure eight through x = 1/2:
# ccw around 0, then cw around 1), y continued by explicit continuous logarithms, and
# cross-checked by nearest-root tracking.
#
#  1. Loop integrals of dx/y^k, k = 1..4, vs  -(1 - zeta^j) B(j/5, j/5), j = 5 - k
#     (the loop L is -gamma, gamma = [0 -> 1 on sheet y0] + [1 -> 0 on sheet zeta*y0]).
#     In particular P0 (k=4), P1 (k=3) and Pbar = perB5 (k=1) come from ONE cycle.
#  2. Same integrals over gamma itself (direct real integrals with endpoint singularities).
#  3. [zeta]^* (dx/y^k) = zeta^{-k} dx/y^k  ->  eigenvalues: k=4: zeta, k=3: zeta^2, k=1: zeta^4.
#     Integral over [zeta]_* L  (y -> zeta*y along L) = zeta^{-k} * integral over L.
#  4. dx/y at infinity: pole order 4, residue 0 (5-fold big circle), so second kind, nonzero class.
#  5. beta5_mul: B(1/5,1/5) B(4/5,4/5) = rho*pi, rho = (5/3) sin(2pi/5)/sin(pi/5)^2.
#  6. C-span of the period vectors of [zeta^e]gamma~ in (z_0, z_1, w_4, w_3): rank 4 (= Lie(A^nat)).
#  7. WuestholzB5 equivalence: perB5/pi = (1 - zeta^4) rho / B(1/5,1/5) (so it is Schneider 1941).
import mpmath as mp

mp.mp.dps = 70
TOL = mp.mpf(10) ** (-55)
N = 5
zeta = mp.expj(2 * mp.pi / N)
half = mp.mpf(1) / 2
B = lambda a, b: mp.gamma(a) * mp.gamma(b) / mp.gamma(a + b)

ok_all = True


def report(name, val, ref):
    global ok_all
    err = abs(val - ref)
    ok = err < TOL
    ok_all &= ok
    print(f"{name:48s} |diff| = {mp.nstr(err, 3):>10s}  {'OK' if ok else 'FAIL'}")


# ---- loop L with continuous logs ------------------------------------------------------------
# Part 1: x = (1/2) e^{i phi}, phi: 0 -> 2pi.  log x = log(1/2) + i phi, log(1-x) principal (Re(1-x) > 0).
# Part 2: x = 1 + (1/2) e^{i phi}, phi: pi -> -pi (clockwise).  log x principal (Re x > 0) + 2 pi i carried,
#         log(1-x) = log(1/2) + i (phi - pi)   (equals log(1/2) at the start x = 1/2).
def y_part1(phi):
    x = half * mp.expj(phi)
    return x, mp.exp((mp.log(half) + 1j * phi + mp.log(1 - x)) / N), 1j * x


def y_part2(phi):
    x = 1 + half * mp.expj(phi)
    return x, mp.exp((mp.log(x) + 2j * mp.pi + mp.log(half) + 1j * (phi - mp.pi)) / N), 1j * half * mp.expj(phi)


def loop_int(k, twist=1):
    f1 = lambda p: (lambda x, y, dx: dx / (twist * y) ** k)(*y_part1(p))
    f2 = lambda p: (lambda x, y, dx: dx / (twist * y) ** k)(*y_part2(p))
    I1 = mp.quad(f1, mp.linspace(0, 2 * mp.pi, 9))
    I2 = -mp.quad(f2, mp.linspace(-mp.pi, mp.pi, 9))   # phi runs from pi down to -pi
    return I1 + I2


# consistency of the continuous-log branch: y^5 = x(1-x) and continuity at the junctions
for phi in [mp.mpf(0), mp.mpf(1), mp.pi, 2 * mp.pi]:
    x, y, _ = y_part1(phi)
    assert abs(y ** 5 - x * (1 - x)) < TOL
for phi in [mp.pi, mp.mpf(1), -mp.pi]:
    x, y, _ = y_part2(phi)
    assert abs(y ** 5 - x * (1 - x)) < TOL
y0 = (half * half) ** (mp.mpf(1) / N)
report("start of L on sheet y0", y_part1(0)[1], y0)
report("end of part 1 = start of part 2 (sheet zeta*y0)", y_part1(2 * mp.pi)[1], y_part2(mp.pi)[1])
report("end of part 1 is zeta*y0", y_part1(2 * mp.pi)[1], zeta * y0)
report("end of L back on sheet y0 (closed on curve)", y_part2(-mp.pi)[1], y0)

# nearest-root tracking cross-check of the branch along L
def track(M=4000):
    roots = [mp.exp(2j * mp.pi * c / N) for c in range(N)]
    y = y0
    worst = mp.mpf(0)
    for part, (a, b, fn) in enumerate([(0, 2 * mp.pi, y_part1), (mp.pi, -mp.pi, y_part2)]):
        for i in range(1, M + 1):
            phi = a + (b - a) * mp.mpf(i) / M
            x, ylog, _ = fn(phi)
            base = (x * (1 - x)) ** (mp.mpf(1) / N)
            cand = min((base * r for r in roots), key=lambda c: abs(c - y))
            y = cand
            worst = max(worst, abs(y - ylog))
    return worst

mp.mp.dps = 30
w = track()
mp.mp.dps = 70
print(f"{'nearest-root tracking vs continuous-log branch':48s} max |diff| = {mp.nstr(w, 3)}  {'OK' if w < 1e-20 else 'FAIL'}")
ok_all &= w < 1e-20

print()
print("1. loop integrals over L (= -gamma)")
loops = {}
for k in range(1, 5):
    j = N - k
    loops[k] = loop_int(k)
    ref = -(1 - zeta ** j) * B(mp.mpf(j) / N, mp.mpf(j) / N)
    report(f"  int_L dx/y^{k}  vs  -(1-zeta^{j}) B({j}/5,{j}/5)", loops[k], ref)

P0 = (1 - zeta) * B(mp.mpf(1) / 5, mp.mpf(1) / 5)
P1 = (1 - zeta ** 2) * B(mp.mpf(2) / 5, mp.mpf(2) / 5)
Pb = (1 - zeta ** 4) * B(mp.mpf(4) / 5, mp.mpf(4) / 5)   # perB5
report("  perA5 0 = int_gamma dx/y^4", -loops[4], P0)
report("  perA5 1 = int_gamma dx/y^3", -loops[3], P1)
report("  perB5   = int_gamma dx/y  (same gamma)", -loops[1], Pb)

print()
print("2. direct integral over gamma = [0->1, y0] + [1->0, zeta*y0]")
for k in range(1, 5):
    j = N - k
    # x = u^5 removes the endpoint singularity; the integrand is symmetric under x -> 1 - x
    real = 2 * mp.quad(lambda u: 5 * u ** (4 - k) * (1 - u ** 5) ** (-mp.mpf(k) / N), [0, half ** (mp.mpf(1) / N)])
    g = real - zeta ** (-k) * real
    report(f"  int_gamma dx/y^{k} vs (1-zeta^{j})B", g, (1 - zeta ** j) * B(mp.mpf(j) / N, mp.mpf(j) / N))

print()
print("3. CM action: int over [zeta]_*L of dx/y^k = zeta^{-k} int_L; exponent mod 5")
for k, label in [(4, "kappa=1 (s=0)"), (3, "kappa=2 (s=1)"), (1, "sigma-bar: N-1=4"), (2, "tau: 3")]:
    tw = loop_int(k, twist=zeta)
    e = (-k) % N
    report(f"  dx/y^{k}: eigenvalue zeta^{e}  [{label}]", tw, zeta ** e * loops[k])

print()
print("4. dx/y at infinity")
# x = t^-5 (1 + ...), y = c t^-2 (...): ord_inf(dx/y^k) = -6 + 2k.  k = 1: -4 (pole of order 4).
for k in range(1, 5):
    print(f"  ord_inf(dx/y^{k}) = {-6 + 2 * k}" + ("   (holomorphic)" if -6 + 2 * k >= 0 else "   (pole)"))
# residue at infinity: integral over 5 turns of |x| = R (one small loop around the single point at infinity)
R = mp.mpf(3)
def big(phi):
    x = R * mp.expj(phi)
    # continuous log(1-x): 1 - x = -x (1 - 1/x); log(-x) continuous = log R + i (phi - pi); log(1-1/x) principal
    lx = mp.log(R) + 1j * phi
    l1x = mp.log(R) + 1j * (phi - mp.pi) + mp.log(1 - 1 / x)
    y = mp.exp((lx + l1x) / N)
    return x, y, 1j * x
yA = big(0)[1]; yB = big(10 * mp.pi)[1]
report("  5 turns close up on the curve", yB, yA)
res = mp.quad(lambda p: (lambda x, y, dx: dx / y)(*big(p)), mp.linspace(0, 10 * mp.pi, 41))
report("  residue of dx/y at infinity (5-turn integral)", res, 0)
print(f"  |int_gamma dx/y| = {mp.nstr(abs(Pb), 20)} != 0, so [dx/y] != 0 in H^1_dR")

print()
print("5. beta5_mul")
rho = mp.mpf(5) / 3 * mp.sin(2 * mp.pi / 5) / mp.sin(mp.pi / 5) ** 2
report("  B(1/5,1/5) B(4/5,4/5) = rho*pi", B(mp.mpf(1) / 5, mp.mpf(1) / 5) * B(mp.mpf(4) / 5, mp.mpf(4) / 5), rho * mp.pi)
report("  B(1/5,1/5) = Gamma(1/5)^2/Gamma(2/5) (betaIntegral)",
       2 * mp.quad(lambda u: 5 * (1 - u ** 5) ** (-mp.mpf(4) / 5), [0, half ** (mp.mpf(1) / 5)]), mp.gamma(mp.mpf(1) / 5) ** 2 / mp.gamma(mp.mpf(2) / 5))
print(f"  rho = {mp.nstr(rho, 30)},  B(1/5,1/5) = {mp.nstr(B(mp.mpf(1)/5, mp.mpf(1)/5), 30)}")

print()
print("6. period vectors of [zeta^e]gamma~ in (z_0, z_1, w_4, w_3): C-rank")
P3 = (1 - zeta ** 3) * B(mp.mpf(3) / 5, mp.mpf(3) / 5)
M = mp.matrix(4, 4)
for e in range(4):
    for c, (kap, P) in enumerate([(1, P0), (2, P1), (4, Pb), (3, P3)]):
        M[e, c] = zeta ** (kap * e) * P
d = mp.det(M)
print(f"  |det| = {mp.nstr(abs(d), 12)}  {'OK (rank 4)' if abs(d) > 1e-10 else 'FAIL'}")
ok_all &= abs(d) > 1e-10

print()
print("7. WuestholzB5 reformulation")
report("  perB5/pi = (1-zeta^4) rho / B(1/5,1/5)", Pb / mp.pi, (1 - zeta ** 4) * rho / B(mp.mpf(1) / 5, mp.mpf(1) / 5))
report("  P0 * perB5 = |1-zeta|^2 rho pi", P0 * Pb, abs(1 - zeta) ** 2 * rho * mp.pi)
# the Lean conversion constant: c' perB5/pi with c' = (c (1-zeta^4) rho)^-1 inverts to c B(1/5,1/5)
c = mp.mpf(7) / 3 + 2j
cp = 1 / (c * (1 - zeta ** 4) * rho)
report("  (c' perB5/pi)^-1 = c B(1/5,1/5)  (c = 7/3+2i)", 1 / (cp * Pb / mp.pi), c * B(mp.mpf(1) / 5, mp.mpf(1) / 5))

print()
print("ALL OK" if ok_all else "SOME CHECK FAILED")
