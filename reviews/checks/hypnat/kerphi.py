import sympy as sp
I=sp.I; r2=sp.sqrt(2)
th=[1,I,r2,I*r2]; th1=[1,-I,r2,-I*r2]; th2=[1,-I,-r2,I*r2]
xs=sp.symbols('a0:4'); ys=sp.symbols('b0:4')
m=[xs[j]+I*ys[j] for j in range(4)]
phi=sp.expand(sum(th[j]*sp.conjugate(m[j]) for j in range(4)).subs({sp.conjugate(s):s for s in xs+ys}))
# phi = 0 : rational coefficients of 1, i, r2, i r2 vanish
re_im=[]
expr=phi
c={}
P=sp.Poly(sp.expand(expr), *(xs+ys))
eqs=[]
for basis in [(1,0),(0,1)]:
    pass
# split expr into coefficients of 1,I,r2,I*r2
e=sp.expand(expr)
e=e.subs(I,sp.Symbol('II')).subs(r2,sp.Symbol('R'))
e=sp.expand(e).subs(sp.Symbol('II')**2,-1).subs(sp.Symbol('R')**2,2)
e=sp.expand(e)
II,R=sp.Symbol('II'),sp.Symbol('R')
eqs=[e.coeff(II,0).coeff(R,0), e.coeff(II,1).coeff(R,0), e.coeff(II,0).coeff(R,1), e.coeff(II,1).coeff(R,1)]
M=sp.Matrix([[sp.diff(q,v) for v in xs+ys] for q in eqs])
ns=M.nullspace()
print("dim_Q ker phi =",len(ns))
for v in ns:
    mm=[v[j]+I*v[4+j] for j in range(4)]
    l1=sp.simplify(sum(th1[j]*mm[j] for j in range(4)))
    l2=sp.simplify(sum(th2[j]*mm[j] for j in range(4)))
    ph=sp.simplify(sum(th[j]*sp.conjugate(mm[j]) for j in range(4)))
    print(ph, l1, l2)
# check ker phi is a Q(i)-subspace: i*v in ker
for v in ns:
    mm=[I*(v[j]+I*v[4+j]) for j in range(4)]
    print("i*v:",sp.simplify(sum(th[j]*sp.conjugate(mm[j]) for j in range(4))), end=" ")
print()
# rank over C of ker phi tensor C (complex span of the m's)
Mc=sp.Matrix([[v[j]+I*v[4+j] for j in range(4)] for v in ns])
print("C-rank of span(ker phi) =", Mc.rank())
print("rank of [th1; th2] =", sp.Matrix([th1,th2]).rank())
