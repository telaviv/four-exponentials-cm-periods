# Sanity check of TorsionTriple's exponent convention on a known torsion point.
# O = (0,0) (branch point), Q = (1/2, 4^(-1/7)); real path [0,1/2] on the sheet y>0.
# z_s = int_0^{1/2} dx / y^{6-s}, s = 0,1,2  (dx/y^6, dx/y^5, dx/y^4).
# Claim: z_s = sigma_{s+1}(x) * perA(s+1) with x = 1/(2(1-zeta)) in F, sigma_k(zeta) = zeta^k.
import mpmath as mp
import sympy as sp
mp.mp.dps = 40
zeta = mp.exp(2j*mp.pi/7)
def B(a, b): return mp.gamma(a)*mp.gamma(b)/mp.gamma(a+b)
def perA(j): return (1 - zeta**j)*B(mp.mpf(j)/7, mp.mpf(j)/7)
# x = 1/(2(1-Z)) written in the Q-basis 1, Z, ..., Z^5 of Q(zeta_7)
Z = sp.symbols('Z')
Phi = sp.Poly(sum(Z**k for k in range(7)), Z)
inv = sp.invert(sp.Poly(2*(1 - Z), Z), Phi)   # polynomial representing 1/(2(1-Z)) mod Phi_7
q = [sp.Rational(c) for c in reversed(sp.Poly(inv, Z).all_coeffs())]
q += [0]*(6 - len(q))
print("q_e =", q)
for s in range(3):
    k = 6 - s
    # substitution x = t^7 removes the endpoint singularity
    z = mp.quad(lambda t: 7*t**(6-k)*(1-t**7)**(-mp.mpf(k)/7), [0, mp.mpf(2)**(-mp.mpf(1)/7)])
    tt = sum(mp.mpf(q[e].p)/q[e].q * zeta**((s+1)*e) for e in range(6)) * perA(s+1)
    tt_opp = sum(mp.mpf(q[e].p)/q[e].q * zeta**(-(s+1)*e) for e in range(6)) * perA(s+1)
    print(f"s={s}: z_s = {mp.nstr(z, 25)}  B/2 = {mp.nstr(B(mp.mpf(s+1)/7, mp.mpf(s+1)/7)/2, 25)}  "
          f"|z - TorsionTriple(q)| = {mp.nstr(abs(z - tt), 5)}  |z - opposite convention(q)| = {mp.nstr(abs(z - tt_opp), 5)}")
