# Sanity numerics for NotLtildeA at P = (1 - zeta5) B(1/5,1/5) and the corA2_beta5 rewriting.
from mpmath import mp, mpf, gamma, beta, pi, log, sqrt, exp, pslq, mpc, quad
mp.dps = 120
z = exp(2j*pi/5)
B = beta(mpf(1)/5, mpf(1)/5)
print("B(1/5,1/5) =", mp.nstr(B, 30))
print("Gamma form diff:", mp.nstr(abs(B - gamma(mpf(1)/5)**2/gamma(mpf(2)/5)), 5))
# Mathlib betaIntegral = int_0^1 x^(u-1)(1-x)^(v-1): check the integral numerically at 40 digits
mp.dps = 40
Bi = quad(lambda t: (t*(1-t))**(mpf(-4)/5), [0, mpf(1)/2, 1])
print("integral vs B:", mp.nstr(abs(Bi - beta(mpf(1)/5, mpf(1)/5)), 5))
mp.dps = 120
P = (1 - z)*B
# corA2_beta5 rewriting: b*pi*B = (b/(1-z))*pi*P ; c*pi^2/B = (c(1-z))*pi^2/P
b, c = mpc(2, 3), mpc(-1, 0.5)
print("rewrite diffs:", mp.nstr(abs(b*pi*B - (b/(1-z))*pi*P), 5), mp.nstr(abs(c*pi**2/B - c*(1-z)*pi**2/P), 5))
# PSLQ: B against 1, sqrt5, pi, sqrt5*pi, log2, log3, log5, log(golden), sqrt5*log(golden), sqrt5*log2
phi = (1+sqrt(5))/2
basis = [B, mpf(1), sqrt(5), pi, sqrt(5)*pi, log(2), log(3), log(5), log(phi), sqrt(5)*log(phi), sqrt(5)*log(2),
         sqrt(5)*log(5), sqrt(10+2*sqrt(5))*pi, sqrt(10-2*sqrt(5))*pi]
rel = pslq(basis, maxcoeff=10**8, maxsteps=10**6)
print("pslq relation for B over Q(sqrt5)-span of {1, pi, logs}:", rel)
# B/pi against the same (WuestholzA5 form)
rel2 = pslq([B/pi, mpf(1), sqrt(5), sqrt(10+2*sqrt(5)), sqrt(10-2*sqrt(5))], maxcoeff=10**10, maxsteps=10**6)
print("pslq relation for B/pi over Q(zeta5)^+ real span:", rel2)
# re-run at 400 digits (the 120-digit hit above is at the precision limit: 14 terms x 8 digits)
mp.dps = 400
B = beta(mpf(1)/5, mpf(1)/5); phi = (1+sqrt(5))/2
basis = [B, mpf(1), sqrt(5), pi, sqrt(5)*pi, log(2), log(3), log(5), log(phi), sqrt(5)*log(phi), sqrt(5)*log(2),
         sqrt(5)*log(5), sqrt(10+2*sqrt(5))*pi, sqrt(10-2*sqrt(5))*pi]
print("residual of 120-digit 'relation' at 400 digits:",
      mp.nstr(abs(sum(r*x for r, x in zip(rel, basis))), 5))
rel3 = pslq(basis, maxcoeff=10**12, maxsteps=10**7)
print("pslq at 400 digits, maxcoeff 1e12:", rel3)
