"""Exact geometry primitives independently developed by defect_coupling.
Frozen from results/defects/verify_outside_l_cover.py for portable acceptance.

Independent exact geometry audit for the shifted outside-L Bloch cover.

This program uses rational polytope vertices, not the pilot's greedy
feasibility implementation. Pending/uncovered leaves always prevent PASS.
Matrix receipts are checked for consistency and current hashes, but do not
constitute a fresh matrix replay. Use --replay-matrices for that final gate.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import product,combinations
from functools import lru_cache
from collections import Counter
import json,hashlib,argparse,sys,subprocess,os

if not __debug__:
    raise RuntimeError('Exact acceptance requires assertions; do not run with -O or PYTHONOPTIMIZE.')

ROOT=Path(__file__).resolve().parent
SHIFT=F(157,16384);SIGMA=F(1,1<<24);RHO=F(1023,1<<26)
WEDGE_ROWS=[(1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1),(-1,1,0),(0,-1,1),(1,1,1)]
MATRIX_SOURCES={'verify_pilot_batch.py','interval_kernel.cpp','interval_tools.py','verify_point.py','exact_geometry.py'}
MATRIX_MARGINS={'negative_margin','positive_diagonal_margin','gradient_margin','positive_determinant_margin'}

def det(a):
    return a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])-a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])+a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0])

VERTICES=[]
for chosen in combinations(range(9),3):
    a=[WEDGE_ROWS[i] for i in chosen];d=det(a)
    if not d:continue
    # Explicit 2x2 cofactors are simpler and independently check the inverse.
    cofactor=[]
    for i in range(3):
        row=[]
        for j in range(3):
            rr=[r for r in range(3) if r!=i];cc=[c for c in range(3) if c!=j]
            row.append((-1)**(i+j)*(a[rr[0]][cc[0]]*a[rr[1]][cc[1]]-a[rr[0]][cc[1]]*a[rr[1]][cc[0]]))
        cofactor.append(row)
    adj=[[cofactor[j][i] for j in range(3)] for i in range(3)]
    assert all(sum(a[i][k]*adj[k][j] for k in range(3))==d*(i==j) for i in range(3) for j in range(3))
    if d<0:d=-d;adj=[[-x for x in row] for row in adj]
    VERTICES.append((chosen,d,adj))

def key_from_box(center,halfwidth,depth):
    assert isinstance(depth,int) and 0<=depth<=30
    h=F(halfwidth);assert h==F(1,1<<(depth+1))
    index=[]
    for c in center:
        z=(F(c)-h)*(1<<depth)
        assert z.denominator==1 and 0<=z<1<<depth
        index.append(int(z))
    assert len(index)==3
    return depth,tuple(index)

def endpoints(key):
    d,idx=key;s=1<<d
    return tuple(F(i,s) for i in idx),tuple(F(i+1,s) for i in idx)

@lru_cache(None)
def feasible(key):
    depth,idx=key
    # Scale coordinates by 2^(depth+1), making all nine RHS values integers.
    lo=tuple(2*i for i in idx);hi=tuple(x+2 for x in lo)
    bounds=[hi[0],-lo[0],hi[1],-lo[1],hi[2],-lo[2],0,0,3*(1<<depth)]
    for chosen,d,adj in VERTICES:
        rhs=[bounds[i] for i in chosen]
        numerator=[sum(a*b for a,b in zip(row,rhs)) for row in adj]
        if all(sum(a*x for a,x in zip(row,numerator))<=bound*d for row,bound in zip(WEDGE_ROWS,bounds)):
            return True
    return False

def in_gamma(key):return max(endpoints(key)[1])<=F(1,8)
def in_l_ball(key):
    lo,hi=endpoints(key)
    return sum(max((a-F(1,2))**2,(b-F(1,2))**2) for a,b in zip(lo,hi))<=F(1,400)

def analytic_gamma():
    signed_l=set(product([-1,1],repeat=3));classes=[]
    while signed_l:
        center=min(signed_l)
        equivalent={p for p in signed_l if len({((p[j]-center[j])//2)%2 for j in range(3)})==1}
        assert equivalent=={center,tuple(-x for x in center)}
        classes.append(sorted(equivalent));signed_l-=equivalent
    assert len(classes)==4
    def atan(q):
        s=sum(F((-1)**j,(2*j+1)*q**(2*j+1)) for j in range(8))
        tail=F(1,17*q**17)
        return s,s+tail
    a,b=atan(5);c,d=atan(239)
    pi_lo=16*a-4*d;pi_hi=16*b-4*c
    assert F(3)<pi_lo<pi_hi<F(22,7)
    x0=pi_hi/160;x1=7*pi_lo/160;x2=15*pi_lo/160
    assert 0<x0<x1<x2<F(1,2)
    # sin(x)<=x; sin(x)>=x-x^3/6 on this interval. The latter polynomial
    # is increasing here, so evaluating it at a lower angle is safe.
    low=12*x0*x0
    high_odd=12*(x1-x1**3/6)**2
    high_even=4*(x2-x2**3/6)**2
    t=F(1,64)
    margins={'low':t-SIGMA-low,'high_odd':high_odd-13*(t+SIGMA),'high_even':high_even-13*(t+SIGMA)}
    assert all(v>0 for v in margins.values())
    assert F(12)+64*SHIFT<13 and RHO<F(1,4096)
    threshold=SHIFT+SIGMA-RHO
    assert threshold==F(642053,1<<26)
    # The separate fresh exact point checker proves this named rational bound;
    # no saved acceptance JSON is read as evidence here.
    upper=F(23913,2500000)
    assert threshold-upper>F(1,500000)
    return {'gamma_margins_exact':{k:str(v) for k,v in margins.items()},
            'four_inequivalent_L_classes_in_doubled_coordinates':classes,
            'perturbed_positive_band_threshold':str(threshold),
            'threshold_above_lowest_L_upper_interval_by_more_than':'1/500000',
            'point_interval_dependency':'fresh exact point residual/inertia verification certifies E_L++- <23913/2500000; required separately'}
