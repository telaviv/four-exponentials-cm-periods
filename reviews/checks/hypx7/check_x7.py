"""Numerical soundness checks for the X7 group model (REFEREE_HYP_X7.md).

(a) one closed cycle gamma on C: y^7 = x(1-x) with int_gamma dx/y^(7-j) = perA j, j = 1,2,3 simultaneously,
    by numerical integration along an explicit closed loop (y continued analytically along the loop);
(b) direction of the CM action: pushing the loop by y -> zeta y multiplies the j-th integral by zeta^j;
    the six cycles [zeta^e]gamma give a rank-6 lattice in C^3 (type {1,2,3} is a CM type);
(c) the lattice Omega*Z[alpha], Omega = B(1/7,2/7), alpha = (-1+sqrt(-7))/2, has algebraic g2, g3
    (Eisenstein series), j = -3375, and is homothetic by an algebraic factor to y^2 = 4x^3 - 140x - 392;
(d) the algebra used by Lean: relation_R, mu7, zp/zq table, multipliers 1,4,5, k-independence of
    {zeta^e b_j}; Cor. X7(c) Gamma forms.
"""
import mpmath as mp

mp.mp.dps = 60
pi = mp.pi
I = mp.mpc(0, 1)
z = mp.exp(2 * pi * I / 7)
alpha = z + z**2 + z**4
B = lambda a, b: mp.gamma(a) * mp.gamma(b) / mp.gamma(a + b)
P = {j: (1 - z**j) * B(mp.mpf(j) / 7, mp.mpf(j) / 7) for j in (1, 2, 3)}
Om = B(mp.mpf(1) / 7, mp.mpf(2) / 7)

def rep(name, val):
    print(f"{name}: {mp.nstr(val, 12)}")

print("=== (a) closed loop integration ===")
# Loop: circle around x=1 counterclockwise from x=1/2 (y starts real positive), then circle around x=0
# clockwise from x=1/2.  Contracting the circles: [0,1] on sheet y>0 minus [0,1] on sheet zeta*y>0 = gamma.
y0 = mp.root(mp.mpf(1) / 4, 7)

def loop_integral(k, twist=1):
    # piece 1: x = 1 - e^{i phi}/2, phi in [0, 2pi]; y = x^{1/7} (principal, Re x >= 1/2) * (1/2)^{1/7} e^{i phi/7}
    def f1(phi):
        x = 1 - mp.exp(I * phi) / 2
        dx = -I * mp.exp(I * phi) / 2
        y = twist * mp.power(x, mp.mpf(1) / 7) * mp.root(mp.mpf(1) / 2, 7) * mp.exp(I * phi / 7)
        return dx / y**k
    # piece 2: x = e^{-i psi}/2, psi in [0, 2pi]; y = zeta * (1/2)^{1/7} e^{-i psi/7} * (1-x)^{1/7}
    def f2(psi):
        x = mp.exp(-I * psi) / 2
        dx = -I * mp.exp(-I * psi) / 2
        y = twist * z * mp.root(mp.mpf(1) / 2, 7) * mp.exp(-I * psi / 7) * mp.power(1 - x, mp.mpf(1) / 7)
        return dx / y**k
    # continuity checks
    e1 = abs(twist * mp.power(mp.mpf(1)/2, mp.mpf(1)/7) * mp.root(mp.mpf(1)/2, 7) * mp.exp(2*pi*I/7) - twist * z * y0)
    e2 = abs(twist * z * mp.root(mp.mpf(1)/2, 7) * mp.exp(-2*pi*I/7) * mp.power(mp.mpf(1)/2, mp.mpf(1)/7) - twist * y0)
    assert e1 < mp.mpf(10)**-50 and e2 < mp.mpf(10)**-50, (e1, e2)
    return mp.quad(f1, mp.linspace(0, 2 * pi, 9)) + mp.quad(f2, mp.linspace(0, 2 * pi, 9))

# sanity: y^7 = x(1-x) along both pieces
for phi in [mp.mpf('0.3'), mp.mpf('4.1')]:
    x = 1 - mp.exp(I * phi) / 2
    y = mp.power(x, mp.mpf(1) / 7) * mp.root(mp.mpf(1) / 2, 7) * mp.exp(I * phi / 7)
    assert abs(y**7 - x * (1 - x)) < mp.mpf(10)**-55
    x = mp.exp(-I * phi) / 2
    y = z * mp.root(mp.mpf(1) / 2, 7) * mp.exp(-I * phi / 7) * mp.power(1 - x, mp.mpf(1) / 7)
    assert abs(y**7 - x * (1 - x)) < mp.mpf(10)**-55
print("y^7 = x(1-x) on the loop, and continuity at the junctions: OK")

L = {}
for j in (1, 2, 3):
    L[j] = loop_integral(7 - j)
    rep(f"loop int dx/y^{7-j}", L[j])
    rep(f"perA {j}           ", P[j])
    print(f"   |diff| = {mp.nstr(abs(L[j] - P[j]), 3)}")
# real-segment form of the Beta integral (tanh-sinh, endpoint singularities)
for j in (1, 2, 3):
    k = 7 - j
    seg = mp.quad(lambda x: x**(-mp.mpf(k) / 7) * (1 - x)**(-mp.mpf(k) / 7), [0, mp.mpf(1)/2, 1])
    print(f"j={j}: int_0^1 (x(1-x))^(-{k}/7) dx - B(j/7,j/7) = {mp.nstr(abs(seg - B(mp.mpf(j)/7, mp.mpf(j)/7)), 3)}")

print("\n=== (b) CM action direction ===")
for j in (1, 2, 3):
    Lt = loop_integral(7 - j, twist=z)  # pushforward of the loop by y -> zeta*y
    print(f"j={j}: int_{{[zeta]gamma}} dx/y^{7-j} / perA j = {mp.nstr(Lt / P[j], 15)};  zeta^{j} = {mp.nstr(z**j, 15)};"
          f"  |diff| = {mp.nstr(abs(Lt / P[j] - z**j), 3)}")
# rank-6 lattice: vectors (zeta^{(s+1)e} P_{s+1})_s, e = 0..5, as real 6-vectors
M = mp.matrix(6, 6)
for e in range(6):
    for s in range(3):
        c = z**((s + 1) * e) * P[s + 1]
        M[e, 2 * s] = mp.re(c)
        M[e, 2 * s + 1] = mp.im(c)
print("det of the 6x6 real period matrix of [zeta^e]gamma, e<6:", mp.nstr(mp.det(M), 15))
# for comparison: a non-CM-type choice {1,6,2} would give det 0
M2 = mp.matrix(6, 6)
for e in range(6):
    for s, sig in enumerate((1, 6, 2)):
        c = z**(sig * e) * P[1]
        M2[e, 2 * s] = mp.re(c)
        M2[e, 2 * s + 1] = mp.im(c)
print("(control) same with embeddings {1,6,2}: det =", mp.nstr(mp.det(M2), 5))

print("\n=== (c) the lattice Omega*Z[alpha] ===")
tau = alpha
print("alpha =", mp.nstr(alpha, 20), " Im alpha > 0:", mp.im(alpha) > 0)
q = mp.exp(2 * pi * I * tau)
def E(kk, N=400):
    c = {4: 240, 6: -504}[kk]
    s = mp.mpc(0)
    for n in range(1, N):
        s += mp.mpf(n)**(kk - 1) * q**n / (1 - q**n)
    return 1 + c * s
E4, E6 = E(4), E(6)
g2 = (4 * pi**4 / 3) * E4 / Om**4
g3 = (8 * pi**6 / 27) * E6 / Om**6
rep("g2(Omega Z[alpha])", g2)
rep("g3(Omega Z[alpha])", g3)
jinv = 1728 * g2**3 / (g2**3 - 27 * g3**2)
rep("j", jinv)
lam_m2 = (g3 / 392) / (g2 / 140)  # lambda^{-2} if Omega Z[alpha] = lambda * L_E, E: y^2 = 4x^3 - 140x - 392
rep("lambda^-2 := (g3/392)/(g2/140)", lam_m2)
print("consistency g2/140 - (lambda^-2)^2 =", mp.nstr(abs(g2 / 140 - lam_m2**2), 3))
# identify g2, g3, lambda^-2 as algebraic numbers
for name, val in [("g2", g2), ("g3", g3), ("lambda^-2", lam_m2)]:
    print(name, "imag part:", mp.nstr(mp.im(val), 3))
    with mp.workdps(60):
        poly = mp.findpoly(mp.re(val), 6, maxcoeff=10**12)
    print(f"  minimal polynomial (deg <= 6, coeffs <= 1e12) of Re {name}:", poly)
    if poly:
        print("   residual:", mp.nstr(mp.polyval(poly, mp.re(val)), 3))
# cross-check with a direct (truncated) lattice sum for g2
def latsum(kk, N=60):
    s = mp.mpc(0)
    for m in range(-N, N + 1):
        for n in range(-N, N + 1):
            if m == 0 and n == 0:
                continue
            w = (m + n * alpha) * Om
            s += 1 / w**kk
    return s
with mp.workdps(20):
    print("direct lattice sum 60*G4 (N=60):", mp.nstr(60 * latsum(4), 10), " vs g2:", mp.nstr(g2, 10))
    print("direct lattice sum 140*G6 (N=60):", mp.nstr(140 * latsum(6), 10), " vs g3:", mp.nstr(g3, 10))

print("\n=== (d) algebra used in Lean ===")
mu = 1 + z + z**6
print("mu7 - sin(3pi/7)/sin(pi/7):", mp.nstr(abs(mu - mp.sin(3*pi/7)/mp.sin(pi/7)), 3))
mup = (1 - z) * (1 - z**2) * mu / (1 - z**3)
print("relation_R residual |P1 P2 - mu' P3 Omega|:", mp.nstr(abs(P[1] * P[2] - mup * P[3] * Om), 3))
print("alpha^2+alpha+2:", mp.nstr(abs(alpha**2 + alpha + 2), 3), "; alpha - (-1+sqrt(-7))/2:",
      mp.nstr(abs(alpha - (-1 + mp.sqrt(7) * I) / 2), 3))
zp = [[1, 0, 0], [0, 1, 0], [0, 0, 1], [1, 1, 0], [0, -1, -1], [-1, -1, -1]]
zq = [[0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 1, 1], [1, 0, 0], [0, 0, -1]]
for e in range(6):
    rhs = sum((zp[e][f] + zq[e][f] * alpha) * z**f for f in range(3))
    print(f"zeta^{e} - sum (zp+zq alpha) zeta^e' : {mp.nstr(abs(z**e - rhs), 3)}")
print("multipliers: 2*4 mod 7 =", (2 * 4) % 7, ", 3*5 mod 7 =", (3 * 5) % 7)
# k-independence of 1, zeta, zeta^2 over k = Q(alpha): real 6x6 matrix of {1, alpha} x {1, zeta, zeta^2} over Q
# is the Q-basis {zeta^e', alpha zeta^e'} of F; check it has full rank via the 6 embeddings
emb = [mp.exp(2 * pi * I * t / 7) for t in range(1, 7)]
rows = []
for f in range(3):
    for a in (0, 1):
        rows.append([(w + w**2 + w**4)**a * w**f for w in emb])
Mk = mp.matrix(rows)
print("|det| of [alpha^a zeta^e'] over the 6 embeddings (nonzero => {1,zeta,zeta^2} is a k-basis of F):",
      mp.nstr(abs(mp.det(Mk)), 10))
# Cor X7(c) Gamma forms
g = lambda k: mp.gamma(mp.mpf(k) / 7)
print("B(2/7,2/7) - G(2/7)^2 G(3/7) sin(3pi/7)/pi:", mp.nstr(abs(B(mp.mpf(2)/7, mp.mpf(2)/7) - g(2)**2 * g(3) * mp.sin(3*pi/7) / pi), 3))
print("B(3/7,3/7) - G(3/7)^2 G(1/7) sin(pi/7)/pi:", mp.nstr(abs(B(mp.mpf(3)/7, mp.mpf(3)/7) - g(3)**2 * g(1) * mp.sin(pi/7) / pi), 3))
