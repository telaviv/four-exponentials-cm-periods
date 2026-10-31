import mpmath as mp, numpy as np
mp.mp.dps = 40
vp = mp.gamma(mp.mpf(1)/4)**2/(2*mp.sqrt(2*mp.pi))
print("varpi", vp)
q = mp.e**(-2*mp.pi)
sig = lambda n,k: sum(d**k for d in range(1,n+1) if n%d==0)
E2 = 1 - 24*mp.fsum(sig(n,1)*q**n for n in range(1,60))
E4 = 1 + 240*mp.fsum(sig(n,3)*q**n for n in range(1,60))
E6 = 1 - 504*mp.fsum(sig(n,5)*q**n for n in range(1,60))
print("E2(i) - 3/pi", E2 - 3/mp.pi)
eta = (mp.pi**2/3)*E2/vp
print("eta(varpi) - pi/varpi", eta - mp.pi/vp)
print("g2", (4*mp.pi**4/3)*E4/vp**4, " g3", (8*mp.pi**6/27)*E6/vp**6)
# direct Weierstrass zeta, double precision, symmetric box
N=400
a=np.arange(-N,N+1)
A,B=np.meshgrid(a,a)
W=(A+1j*B)*float(vp)
W=W[(A!=0)|(B!=0)]
def zeta(z): return 1/z + np.sum(1/(z-W)+1/W+z/W**2)
z=0.31+0.17j
v=float(vp)
e1=zeta(z+v)-zeta(z); e2=zeta(z+1j*v)-zeta(z)
print("eta(varpi) direct", e1, " pi/varpi", float(mp.pi/vp))
print("eta(i varpi) direct", e2, " expected -i pi/varpi", -1j*float(mp.pi/vp))
print("Legendre eta1*w2 - eta2*w1 =", e1*(1j*v)-e2*v, " 2pi i =", 2j*np.pi)
# check eta((m+ni)varpi) = (m-ni) pi/varpi for m=2,n=-3
m,n=2,-3
e=zeta(z+(m+1j*n)*v)-zeta(z)
print("eta((2-3i)varpi)", e, " expected", (m-1j*n)*float(mp.pi/vp))
# sign: int_z^{z+varpi} wp(u) du = -eta ; wp = -zeta'
def wp(u): return 1/u**2 + np.sum(1/(u-W)**2-1/W**2)
us=np.linspace(0,1,2001); path=z+us*v
vals=np.array([wp(p) for p in path[::4]])
integ=np.trapezoid(vals, path[::4])
print("int wp du over period ~", integ, "(compare -eta =", -e1, ")")
# wp' ^2 = 4wp^3 - g2 wp check at z
h=1e-5
d=(wp(z+h)-wp(z-h))/(2*h); p=wp(z)
print("wp'^2 - (4wp^3-4wp)", d*d-(4*p**3-4*p))
