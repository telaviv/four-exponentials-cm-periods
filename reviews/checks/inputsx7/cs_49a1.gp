/* Chowla-Selberg check: periods of E = 49a1 (CM by Z[(1+sqrt-7)/2], j=-3375) vs B(1/7,2/7) */
\p 300
E = ellinit([1,-1,0,-2,-1]);
print("j(49a1) = ", E.j);
w = E.omega;
B12 = gamma(1/7)*gamma(2/7)/gamma(3/7);
r = real(w[1]/B12); print("w1/B(1/7,2/7) = ", r);
p = algdep(r, 3); print("algdep(r,3) = ", p, "   residual = ", subst(p,x,r));
print("tau = w2/w1, algdep = ", algdep(w[2]/w[1], 2));
/* the Lean lattice Omega*Z[alpha], Omega = B(1/7,2/7), alpha = (-1+sqrt-7)/2 */
al = (-1+sqrt(-7))/2;
g2 = real(elleisnum([B12, al*B12], 4, 1)); g3 = real(elleisnum([B12, al*B12], 6, 1));
p2 = algdep(g2, 3); p3 = algdep(g3, 3);
print("g2 = ", g2); print("  algdep(g2,3) = ", p2, "  residual = ", subst(p2,x,g2), "  polisirreducible = ", polisirreducible(p2), "  disc = ", factor(poldisc(p2)));
print("g3 = ", g3); print("  algdep(g3,3) = ", p3, "  residual = ", subst(p3,x,g3), "  polisirreducible = ", polisirreducible(p3));
print("j(Omega Z[alpha]) = ", 1728*g2^3/(g2^3-27*g3^2));
quit;
