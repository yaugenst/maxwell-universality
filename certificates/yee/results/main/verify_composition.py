#!/usr/bin/env python3
"""Exact finite falsification checks for the exposed composition identities.

These do not replace the all-dimension algebraic proofs. No stored PASS
record is read as evidence. Uses only Python's standard library.
"""
from fractions import Fraction as F
from pathlib import Path
import json

def eye(n): return [[F(i == j) for j in range(n)] for i in range(n)]
def tr(a): return list(map(list, zip(*a)))
def mul(a,b): return [[sum((x*y for x,y in zip(row,col)),F()) for col in zip(*b)] for row in a]
def add(a,b): return [[x+y for x,y in zip(ar,br)] for ar,br in zip(a,b)]
def neg(a): return [[-x for x in row] for row in a]
def sub(a,b): return add(a,neg(b))
def scale(a,t): return [[x*t for x in row] for row in a]
def inv(a):
    n=len(a); v=[list(map(F,r))+e for r,e in zip(a,eye(n))]
    for j in range(n):
        p=next(i for i in range(j,n) if v[i][j])
        v[j],v[p]=v[p],v[j]
        q=v[j][j]; v[j]=[x/q for x in v[j]]
        for i in range(n):
            if i != j:
                q=v[i][j]; v[i]=[x-q*y for x,y in zip(v[i],v[j])]
    return [r[n:] for r in v]
def select(a,rows,cols): return [[a[i][j] for j in cols] for i in rows]
def zeros(n,m): return [[F() for _ in range(m)] for _ in range(n)]

checks={}
gamma=[[F(2),F(1),F(0)],[F(1),F(-1),F(1)],[F(0),F(1),F(3)]]
alpha=F(1,32); pairs=[(0,1),(1,2)]; betas=[F(-3,7),F(4,9)]
T=zeros(5,5)
for i in range(3):
    T[i][i]=alpha*(gamma[i][i]-sum(i in e for e in pairs))
for j,((a,b),beta) in enumerate(zip(pairs,betas),3):
    T[a][j]=T[j][a]=T[b][j]=T[j][b]=beta
    T[j][j]=-beta*beta/alpha
B=select(T,range(3),range(3)); E=select(T,range(3),range(3,5)); D=select(T,range(3,5),range(3,5))
checks['signed_mediator_schur']=sub(B,mul(mul(E,inv(D)),tr(E)))==scale(gamma,alpha)

# Indefinite background, two scalar defect blocks, rational square roots.
n=4
K=[[F(5),F(1),F(1,3),F(0)],
   [F(1),F(-4),F(0),F(1,5)],
   [F(1,3),F(0),F(6),F(1)],
   [F(0),F(1,5),F(1),F(-3)]]
W= zeros(n,n); Wroot=zeros(n,n); Winvroot=zeros(n,n); V=zeros(n,n)
for i,(w,v) in enumerate(zip([F(1),F(1,4),F(1),F(1,4)], [F(2),F(2),F(3),F(3)])):
    W[i][i]=w; Wroot[i][i]=F(1) if w==1 else F(1,2)
    Winvroot[i][i]=1/Wroot[i][i]; V[i][i]=v*w
U=[[F(1),F(0)],[F(0),F(0)],[F(0),F(1)],[F(0),F(0)]]
Z=[[F(0),F(0)],[F(1),F(0)],[F(0),F(0)],[F(0),F(1)]]
Ki=inv(K); A=sub(K,V)
M=mul(mul(Wroot,sub(inv(V),Ki)),Wroot)
bright=mul(mul(tr(U),M),U)
cross=mul(mul(tr(U),M),Z)
dark=mul(mul(tr(Z),M),Z)
Sb=sub(bright,mul(mul(cross,inv(dark)),tr(cross)))
g=[[F(2)],[F(-1)]]; y=[[F(1,7)],[F(3,4)],[F(-2,9)],[F(5,6)]]
source=scale(mul(mul(mul(K,Winvroot),U),g),alpha)
r=sub(mul(A,y),source)
z=mul(mul(mul(tr(U),Winvroot),V),y)
left=mul(Sb,z)
resmap=mul(mul(sub(tr(U),mul(mul(cross,inv(dark)),tr(Z))),Wroot),Ki)
right=add(scale(g,alpha),mul(resmap,r))
checks['exact_source_readout_identity_indefinite']=left==right
Ai=add(Ki,mul(mul(mul(mul(Ki,Wroot),inv(M)),Wroot),Ki))
checks['woodbury_weighted_identity']=mul(A,Ai)==eye(n)

# Rational finite sample of the boundary shift counting inequality.
m=2; n=3; tau=F(1,64); Jgrid=512; L=16*(m+n)**2/tau
eigenvalues=[F(1,4096),F(31,4096),F(63,4096)]
bad=sum(any(abs((F(j)+F(1,2))*tau/Jgrid-lam)<1/L for lam in eigenvalues) for j in range(Jgrid))
checks['finite_shift_count']=F(bad,Jgrid)<=F(2*n,1)/(L*tau)+F(n,Jgrid)<F(1,m)

# Root-independent exact scalar checks for the analytic H2 proof.
g0=F(1,4096); J=16; beta=g0*g0/16
low=F(157,1000)-F(11,70)**3/6
checks['h2_sine_lower']=low==F(12871,82320) and low>F(5,32)
checks['h2_sine_upper']=8*F(11,70)**2<F(1,5)
checks['h2_L_constant']=(45312*J/g0)**2==8818329545368141824
err=F(1024,45312)
checks['h2_cutoff_margin']=F(320,59)-err==F(956,177)
rp=(beta/64)/(g0*(g0-beta/64))
checks['h2_perturbation_margin']=rp<F(1,512) and F(956,177)-rp>F(16,3)
checks['h2_headroom']=12+beta+12+8*g0<F(49,2)
checks['sampling']=F(25,64)<F(157,50)**2/25

assert all(checks.values()),checks
result={'scope':'exact finite identity and scalar checks; not an all-input numerical proof','checks':checks}
print(json.dumps(result,indent=2))
