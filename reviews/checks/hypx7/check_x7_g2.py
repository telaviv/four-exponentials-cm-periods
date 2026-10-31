"""Higher-precision confirmation (120 digits) that g2, g3 of Omega*Z[alpha] are roots of the cubics found by
check_x7.py, and that the cubics are cyclic over Q (splitting field Q(zeta7)^+)."""
import mpmath as mp, sympy as sp
mp.mp.dps = 120
pi = mp.pi; I = mp.mpc(0, 1)
z = mp.exp(2*pi*I/7); alpha = z + z**2 + z**4
Om = mp.gamma(mp.mpf(1)/7)*mp.gamma(mp.mpf(2)/7)/mp.gamma(mp.mpf(3)/7)
q = mp.exp(2*pi*I*alpha)
def E(k, N=700):
    c = {4: 240, 6: -504}[k]
    return 1 + c*mp.fsum(mp.mpf(n)**(k-1)*q**n/(1-q**n) for n in range(1, N))
g2 = (4*pi**4/3)*E(4)/Om**4; g3 = (8*pi**6/27)*E(6)/Om**6
x = sp.symbols('x')
p2 = -1075648*x**3 + 384160*x**2 - 14700*x + 125   # mpmath.findpoly order: highest degree first
p3 = -60236288*x**3 + 2612288*x**2 - 3920*x + 1
for name, val, p in [("g2", g2, p2), ("g3", g3, p3)]:
    c = [int(t) for t in sp.Poly(p, x).all_coeffs()]
    print(name, "=", mp.nstr(val, 30), " |p(val)| =", mp.nstr(abs(mp.polyval(c, val)), 3),
          " disc =", sp.factorint(sp.discriminant(p, x)), " irreducible:", sp.Poly(p, x).is_irreducible)
# compare with the real cyclotomic cubic: c = 2cos(2pi/7) satisfies x^3+x^2-2x-1
c7 = 2*mp.cos(2*pi/7)
print("2cos(2pi/7) root of x^3+x^2-2x-1:", mp.nstr(abs(c7**3+c7**2-2*c7-1), 3))
