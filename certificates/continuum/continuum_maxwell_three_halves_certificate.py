#!/usr/bin/env python3
"""Exact finite algebra for the local-band continuum construction.

Checks only the finite corner-cluster algebra, its Hessian coefficients,
integer placement, and elementary rational margins. It does not certify
the continuum theorem by itself. No floating-point arithmetic is used.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import product
from math import isqrt
import argparse
import json

if not __debug__:
    raise RuntimeError("Certificate checks require assertions; do not run Python with -O.")

@dataclass(frozen=True)
class Q19:
    a: F = F(0)
    b: F = F(0)
    def __post_init__(self):
        object.__setattr__(self, 'a', F(self.a))
        object.__setattr__(self, 'b', F(self.b))
    @staticmethod
    def co(x): return x if isinstance(x, Q19) else Q19(F(x))
    def __add__(self, x):
        x=self.co(x); return Q19(self.a+x.a,self.b+x.b)
    __radd__=__add__
    def __neg__(self): return Q19(-self.a,-self.b)
    def __sub__(self,x): return self+-self.co(x)
    def __rsub__(self,x): return self.co(x)+-self
    def __mul__(self,x):
        x=self.co(x); return Q19(self.a*x.a+19*self.b*x.b,self.a*x.b+self.b*x.a)
    __rmul__=__mul__
    def inv(self):
        d=self.a*self.a-19*self.b*self.b
        if d==0: raise ZeroDivisionError
        return Q19(self.a/d,-self.b/d)
    def __truediv__(self,x): return self*self.co(x).inv()
    def __rtruediv__(self,x): return self.co(x)*self.inv()
    def __bool__(self): return self.a!=0 or self.b!=0
    def pair(self): return [str(self.a),str(self.b)]

@dataclass(frozen=True)
class I:
    lo: F
    hi: F
    def __post_init__(self):
        object.__setattr__(self,'lo',F(self.lo)); object.__setattr__(self,'hi',F(self.hi))
        assert self.lo<=self.hi
    @staticmethod
    def co(x): return x if isinstance(x,I) else I(F(x),F(x))
    def __add__(self,x):
        x=self.co(x); return I(self.lo+x.lo,self.hi+x.hi)
    __radd__=__add__
    def __neg__(self): return I(-self.hi,-self.lo)
    def __sub__(self,x): return self+-self.co(x)
    def __rsub__(self,x): return self.co(x)+-self
    def __mul__(self,x):
        x=self.co(x); vals=[a*b for a in (self.lo,self.hi) for b in (x.lo,x.hi)]
        return I(min(vals),max(vals))
    __rmul__=__mul__
    def inv(self):
        assert self.lo>0 or self.hi<0
        return I(1/self.hi,1/self.lo)
    def __truediv__(self,x): return self*self.co(x).inv()
    def __rtruediv__(self,x): return self.co(x)*self.inv()
    def sqrt(self,bits=220):
        assert self.lo>=0
        scale=1<<bits
        def lower(q):
            return isqrt((q.numerator*scale*scale)//q.denominator)
        return I(F(lower(self.lo),scale),F(lower(self.hi)+1,scale))
    def record(self): return {'lower':str(self.lo),'upper':str(self.hi)}

def arctan(x,n=128):
    s=sum(((-1)**j*x**(2*j+1)/(2*j+1) for j in range(n)),F(0))
    err=abs(x)**(2*n+1)/(2*n+1)
    return I(s-err,s+err)

def log_rational(x,n=128):
    x=F(x); z=(x-1)/(x+1)
    s=2*sum((z**(2*j+1)/(2*j+1) for j in range(n)),F(0))
    e=2*abs(z)**(2*n+1)/((2*n+1)*(1-z*z))
    return I(s-e,s+e)

def matmul(A,B):
    return [[sum((A[i][k]*B[k][j] for k in range(len(B))),Q19())
             for j in range(len(B[0]))] for i in range(len(A))]

def transpose(A): return [list(x) for x in zip(*A)]

def inv(A):
    n=len(A); a=[[Q19.co(x) for x in row]+[Q19(int(i==j)) for j in range(n)]
                for i,row in enumerate(A)]
    for j in range(n):
        k=next(i for i in range(j,n) if a[i][j])
        a[j],a[k]=a[k],a[j]
        v=a[j][j]; a[j]=[x/v for x in a[j]]
        for i in range(n):
            if i!=j:
                v=a[i][j]; a[i]=[x-v*y for x,y in zip(a[i],a[j])]
    return [row[n:] for row in a]

def run():
    pi=16*arctan(F(1,5))-4*arctan(F(1,239))
    root=I(19,19).sqrt()
    qi=lambda x: I(x.a,x.a)+x.b*root
    lam=Q19(F(5,6),F(1,3))
    eigen_intervals=[]
    for signs in product((-1,1),repeat=3):
        b=[F(a*p) for a,p in zip((1,2,4),signs)]
        s=sum(b); D=sum(x*x for x in b)-sum(b[i]*b[j] for i in range(3) for j in range(i))
        rd=I(D,D).sqrt()
        vals=[-I(s,s)/6-rd/3,-I(s,s)/6+rd/3]
        eigen_intervals.append((signs,vals))
    top=qi(lam)
    other=[v for signs,vs in eigen_intervals for j,v in enumerate(vs)
           if not(signs==(1,-1,-1) and j==1)]
    second_hi=max(v.hi for v in other)
    assert top.lo-second_hi>F(1,20)
    a=[[1/(Q19(d)-lam)] for d in (F(7,2),F(1,2),F(-3,2))]
    assert sum(row[0] for row in a)==Q19()
    norm=matmul(transpose(a),a)[0][0]
    assert norm==Q19(F(361,225),F(-28,225))
    P=[[Q19(F(int(i==j))-F(1,3)) for j in range(3)] for i in range(3)]
    def block(b):
        D=[[Q19(b[i] if i==j else 0) for j in range(3)] for i in range(3)]
        Z=matmul(matmul(P,D),P); ss=sum(b)
        return [[Z[i][j]-ss*P[i][j]/2 for j in range(3)] for i in range(3)]
    # Each parity block has one zero eigenvalue on the normal direction.
    # Its two transverse roots are checked through trace and trace-square.
    for parity in product((-1,1),repeat=3):
        bb=[F(a*b) for a,b in zip((1,2,4),parity)]
        KK=block(bb); KK2=matmul(KK,KK)
        tr=sum((KK[i][i] for i in range(3)),Q19())
        tr2=sum((KK2[i][i] for i in range(3)),Q19())
        ss=sum(bb)
        disc=sum(x*x for x in bb)-sum(bb[i]*bb[j] for i in range(3) for j in range(i))
        assert tr==Q19(-ss/3)
        assert tr2==Q19(ss*ss/F(18)+F(2,9)*disc)
    K=block([1,-2,-4])
    assert matmul(K,a)==[[lam*row[0]] for row in a]
    expected=[Q19(F(47,31),F(352,589)),Q19(2,F(11,38)),Q19(F(1,8),F(11,152))]
    ts=[]
    for j in range(3):
        b=[1,-2,-4]; b[j]=-b[j]; K=block(b)
        R=inv([[lam*int(i==k)-K[i][k] for k in range(3)] for i in range(3)])
        t=matmul(matmul(transpose(a),R),a)[0][0]/norm
        assert t==expected[j]
        ts.append(t)
    delta=F(1,1<<100)
    B=[7180532256056349,6388184103869743,2347449745487106]
    A0=[]; b_intervals=[]
    for tj,b in zip(ts,B):
        aj=pi*pi*qi(tj); A0.append(aj)
        bj=(aj/delta).sqrt(); b_intervals.append(bj)
        assert F(b-1)<bj.lo<=bj.hi<F(b)
        err=F(1,1<<60)
        assert delta*b*b>F(99,100)**2*(aj.hi+err)
        assert delta*b*b<F(101,100)**2*(aj.lo-err)
    # Rebuild the actual 24-component corner cluster, not merely its listed roots.
    # The eight wavevectors are kappa*s; every block is projected to s-perp.
    signs8=list(product((-1,1),repeat=3))
    idx={s:i for i,s in enumerate(signs8)}
    P24=[[Q19() for _ in range(24)] for _ in range(24)]
    K24=[[Q19() for _ in range(24)] for _ in range(24)]
    for ii,ss in enumerate(signs8):
        Ps=[[Q19(F(int(a==b))-F(ss[a]*ss[b],3)) for b in range(3)] for a in range(3)]
        for a0 in range(3):
            for b0 in range(3): P24[3*ii+a0][3*ii+b0]=Ps[a0][b0]
        for j,weight in enumerate((1,2,4)):
            tt=list(ss);tt[j]*=-1;tt=tuple(tt);jj=idx[tt]
            Pt=[[Q19(F(int(a==b))-F(tt[a]*tt[b],3)) for b in range(3)] for a in range(3)]
            zz=matmul(Ps,Pt)
            for a0 in range(3):
                for b0 in range(3):K24[3*ii+a0][3*jj+b0]=-F(weight,2)*zz[a0][b0]
    assert matmul(P24,P24)==P24
    assert transpose(K24)==K24
    parity_embeddings=[]
    for parity in product((-1,1),repeat=3):
        V=[]
        for ss in signs8:
            factor=1
            for j in range(3):
                if ss[j]<0: factor*=parity[j]
            V.extend([[Q19(factor*ss[a0]*int(a0==b0)) for b0 in range(3)] for a0 in range(3)])
        VP=matmul(V,P)
        parity_embeddings.append(VP)
        assert matmul(P24,VP)==VP
        assert matmul(K24,VP)==matmul(V,block([a*b for a,b in zip((1,2,4),parity)]))
        assert matmul(transpose(V),V)==[[Q19(8*int(i==j)) for j in range(3)] for i in range(3)]
    zero3=[[Q19() for _ in range(3)] for _ in range(3)]
    for i,Vi in enumerate(parity_embeddings):
        for Vj in parity_embeddings[:i]:
            assert matmul(transpose(Vi),Vj)==zero3
    # The velocity maps the selected parity into the parity with one sign flipped.
    pp=(1,-1,-1)
    vec=[]
    for ss in signs8:
        factor=1
        for j in range(3):
            if ss[j]<0:factor*=pp[j]
        vec.extend([Q19(factor*ss[j])*a[j][0] for j in range(3)])
    norm24=sum((x*x for x in vec),Q19())
    for j in range(3):
        dj=[2*ss[j]*vec[3*ii+a0] for ii,ss in enumerate(signs8) for a0 in range(3)]
        assert sum((vec[i]*dj[i] for i in range(24)),Q19())==Q19()
        for k in range(3):
            dk=[2*ss[k]*vec[3*ii+a0] for ii,ss in enumerate(signs8) for a0 in range(3)]
            assert sum((dj[i]*dk[i] for i in range(24)),Q19())==4*int(j==k)*norm24
    # Uniform finite-contour inequalities used in the analytic perturbation proof.
    dt=3*pi.hi*F(1,1<<12)
    assert dt<F(1,400)
    assert F(100)/(1-100*dt)<140
    assert (F(2)/(2**16*delta)+2048)*delta*256<F(1,16)
    assert 2**40*delta<F(1,1000)
    assert 2*(pi.lo*pi.lo/4)/7-2**40*delta>F(1,2)
    assert 80*(pi.hi*pi.hi/4)+2**40*delta<256
    radius=delta*F(1,1<<40); Rq=delta*F(1,1<<12)
    M4=4*delta/(Rq**4)
    assert M4*(4*radius)**2<F(1,1000000)/delta
    log2=log_rational(2); log3=log_rational(3)
    assert log2.lo>F(69,100) and log3.hi<F(11,10)
    upper_rate=2*F(99,100)**2/F(7,4)
    lower_rate=2*F(101,100)**2
    assert upper_rate>log3.hi
    assert 3*log2.lo-lower_rate>F(1,50)
    assert F(1,3)**2<F(1,8)
    # Verify the fixed-majorant logarithmic inequality using only small integers.
    fact32=1
    for n in range(2,33): fact32*=n
    ledger_log_upper=1024*(4*fact32.bit_length()+16384*33**2)
    assert ledger_log_upper<2**35<2**40
    return {
      'scope':'Finite corner-cluster algebra and placement only; not the continuum proof.',
      'delta':str(delta),'pi':pi.record(),'lambda_top':top.record(),
      'gap_lower':str(top.lo-second_hi),
      'hessian_coefficients_tj_in_Q_sqrt19':[x.pair() for x in ts],
      'A0_diagonal_intervals':[x.record() for x in A0],
      'placement_B_diagonal':B,'placement_square_root_intervals':[x.record() for x in b_intervals],
      'chart_radius':str(radius),'decay_r':'1/3','useful_a':'1/8',
      'corner_cluster_reconstructed':True,'velocity_gram_verified':True,
      'parity_root_trace_identities_verified':True,
      'parity_direct_sum_orthogonality_verified':True,
      'majorant_log2_upper_integer':ledger_log_upper,
      'checks':'ALL EXACT-RATIONAL CHECKS PASSED'}

def main():
    p=argparse.ArgumentParser();p.add_argument('--output',default='certificate.json');args=p.parse_args()
    receipt=run()
    with open(args.output,'w',encoding='utf-8') as f: json.dump(receipt,f,indent=2); f.write('\n')
    print(receipt['checks'])
if __name__=='__main__': main()
