/* Sanity checks for WuestholzBeta7 (lean_mstar CM4E/AbVar/X7.lean). Numerical only: lindep (PSLQ/LLL)
   cannot prove independence; a null result only rules out relations of small height in the tested field. */
\p 600
z = exp(2*Pi*I/7);
Bt(a,b) = gamma(a)*gamma(b)/gamma(a+b);
B11 = Bt(1/7,1/7); B22 = Bt(2/7,2/7); B33 = Bt(3/7,3/7); B12 = Bt(1/7,2/7);
P1 = (1-z)*B11; P2 = (1-z^2)*B22; P3 = (1-z^3)*B33; Om = B12;
mu = 1+z+z^6; mup = (1-z)*(1-z^2)*mu/(1-z^3);
print("relation_R residual |P1 P2 - mu' P3 Om| = ", abs(P1*P2 - mup*P3*Om));
print("mu - sin(3pi/7)/sin(pi/7) = ", abs(mu - sin(3*Pi/7)/sin(Pi/7)));
/* contour integral: int_0^1 x^(j/7-1)(1-x)^(j/7-1) dx = B(j/7,j/7)   (low precision) */
default(realprecision, 38);
for(j=1,3, a=j/7; Ival = intnum(t=[0,a-1],[1,a-1], t^(a-1)*(1-t)^(a-1)); print("j=",j,"  int - B(j/7,j/7) = ", Ival - Bt(a,a)));
default(realprecision, 600);
z = exp(2*Pi*I/7); B11 = Bt(1/7,1/7); B22 = Bt(2/7,2/7); B33 = Bt(3/7,3/7); B12 = Bt(1/7,2/7);
xs = [1, B11, B22, B33, B12];
c = cos(2*Pi/7); s7 = sqrt(7); t7 = 7^(1/4);
mk(v, bas) = my(w = List()); for(i=1,#v, for(k=1,#bas, listput(w, v[i]*bas[k]))); Vec(w);
report(lab, v, dig) = { my(r, old = default(realprecision)); default(realprecision, dig);
  r = lindep(precision(v, dig)); default(realprecision, old);
  printf("%-38s n=%2d digits=%4d  max|coef| of LLL vector = %.3g   residual = %.3g\n", lab, #v, dig,
         vecmax(apply(abs, r)), abs(v*r)); }
report("Q: 1,B11,B22,B33,B12", xs, 120);
report("Q(cos2pi/7)", mk(xs, [1,c,c^2]), 300);
report("Q(sqrt7)", mk(xs, [1,s7]), 200);
report("Q(cos2pi/7,sqrt7)", mk(xs, [1,c,c^2,s7,s7*c,s7*c^2]), 500);
report("Q(cos2pi/7,7^(1/4))", mk(xs, [1,c,c^2,t7,t7*c,t7*c^2,t7^2,t7^2*c,t7^2*c^2,t7^3,t7^3*c,t7^3*c^2]), 600);
report("Q(cos2pi/7) with pi", mk([1,Pi,B11,B22,B33,B12], [1,c,c^2]), 400);
/* controls: true relations ARE found */
report("control: B11B22, B12B33 over Q(c) [true]", mk([B11*B22, B12*B33], [1,c,c^2]), 120);
report("control: Om_49a1 vs B12 over Q(c) [true]", mk([real(ellinit([1,-1,0,-2,-1]).omega[1]), B12], [1,c,c^2]), 120);
quit;
