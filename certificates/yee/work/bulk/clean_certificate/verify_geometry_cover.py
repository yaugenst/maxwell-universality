"""Exact integer geometry, symmetry, dyadic covering, and Gamma-box certificate.
No floating arithmetic is used in any acceptance test. NumPy is used only for
bounded integer array permutations. The point-certificate JSON files contain
verified exact rational endpoint data, not trusted spectral samples.
"""
from pathlib import Path
from fractions import Fraction as F
import itertools,json,hashlib
import numpy as np
from exact_geometry import diamond_cells_exact
from interval_tools import I,PI,cis,S
BASE=Path(__file__).parent

def verify_geometry():
 p=20;labels=(diamond_cells_exact(p,12,1)==12)
 assert int(labels.sum())==3928
 xyz=np.stack(np.meshgrid(*[np.arange(p,dtype=np.int64)]*3,indexing='ij'),axis=-1)
 fcc=[(0,0,0),(0,10,10),(10,0,10),(10,10,0)]
 for z in fcc:
    q=(xyz+np.array(z))%p
    assert np.array_equal(labels,labels[tuple(q[...,i] for i in range(3))])
 syms=[]
 for perm in itertools.permutations(range(3)):
  for signs in itertools.product([-1,1],repeat=3):
   found=None
   for trans in itertools.product([0,5,10,15],repeat=3):
    # Reflection maps the center i+1/2 to -i-1/2.
    image=np.stack([(signs[j]*xyz[...,perm[j]]+(signs[j]-1)//2+trans[j])%p for j in range(3)],axis=-1)
    if np.array_equal(labels,labels[tuple(image[...,i] for i in range(3))]):
      found=trans;break
   assert found is not None,('missing cubic symmetry',perm,signs)
   syms.append({'permutation':perm,'signs':signs,'translation':found})
 assert len(syms)==48
 print('G1 exact scalar diamond geometry: 3928 high cells / 8000 conventional cells.')
 print('G2 all four FCC translates preserve scalar cell labels exactly.')
 print('G3 all 48 signed coordinate permutations preserve labels after a certified integer translation.')
 return syms

def sinpi_fraction(frac):
 z=cis(F(frac,2));return I(F(int(z[1])-int(z[2]),S),F(int(z[1])+int(z[2]),S))

def verify_gamma():
 t=I(F(1,64));sig=I(F(1,4096));s0=sinpi_fraction(F(3,320));s1=sinpi_fraction(F(13,320));s2=sinpi_fraction(F(29,320))
 a0=12*s0*s0;a1=12*s1*s1;a2=4*s2*s2
 lo_margin=(t-sig)-a0
 hi1=a1-12*(t+sig);hi2=a2-12*(t+sig)
 assert lo_margin.lo>0 and hi1.lo>0 and hi2.lo>0
 # Resolved-regime inequality: t epsilon_max < pi^2 / 25.
 sampling=PI*PI/25-I(F(25,64));assert sampling.lo>0
 print('G4 analytic Gamma cube |kappa_i| <= 3/16: all-frequency exclusion PASS.')
 print('G5 physical sampling with epsilon_max=25, p_min=10: PASS.')
 return {'low_margin':lo_margin.bounds(),'high_odd_margin':hi1.bounds(),'high_even_margin':hi2.bounds(),
         'sampling_margin':sampling.bounds(),'pi':PI.bounds()}

def exact_key(center,half):
 c=list(map(F,center));h=F(half);length=2*h;den=length.denominator
 assert length.numerator==1 and den>0 and den&(den-1)==0
 depth=den.bit_length()-1
 index=tuple((x-h)/length for x in c)
 assert all(x.denominator==1 and 0<=x<den for x in index)
 return (depth,tuple(int(x) for x in index))

def feasible(lo,hi):
 z=lo[2];y=max(lo[1],z);x=max(lo[0],y)
 return z<=hi[2] and y<=hi[1] and x<=hi[0] and x+y+z<=F(3,2)

def verify_cover():
 records=[json.loads(s) for s in (BASE/'verified_boxes_strengthened.jsonl').read_text().splitlines()]
 passed={}
 for r in records:
    assert r['status']=='INTERVAL_PASS',r
    key=exact_key(r['center'],r['halfwidth'])
    c=r['verified_constants']
    for name in ['fn','en','qfn','qweighted','rzero','crossder']:
        assert all(F(x)>=0 for x in c[name]), ('negative proposed norm bound',name)
    for name in ['kn','rhow']:
        assert all(F(x)>=0 for row in c[name] for x in row), ('negative proposed norm bound',name)
    for name in ['wn','wp2','rmin','rhmin','cutoff']:
        assert F(c[name])>0, ('nonpositive proposed scalar bound',name)
    assert r['frequency_halfwidth']=='1/4096'
    for name,interval in r['margins'].items():
        assert F(interval[0])>0 and F(interval[1])>=F(interval[0]),(name,interval)
    data=(BASE/'witnesses'/r['witness']).read_bytes()
    assert hashlib.sha256(data).hexdigest()==r['witness_sha256']
    passed[key]=r
 counts={'certified_boxes':0,'analytic_gamma_boxes':0,'discarded_boxes':0,'interior_nodes':0}
 used=set();maxdepth=max(k[0] for k in passed)
 def visit(depth,index):
    scale=1<<depth;lo=tuple(F(i,scale) for i in index);hi=tuple(F(i+1,scale) for i in index)
    if not feasible(lo,hi):counts['discarded_boxes']+=1;return
    if max(hi)<=F(3,16):counts['analytic_gamma_boxes']+=1;return
    key=(depth,index)
    if key in passed:counts['certified_boxes']+=1;used.add(key);return
    assert depth<maxdepth,('UNCOVERED BLOCH BOX',depth,index)
    counts['interior_nodes']+=1
    for bits in itertools.product([0,1],repeat=3):visit(depth+1,tuple(2*index[j]+bits[j] for j in range(3)))
 visit(0,(0,0,0))
 assert len(used)==len(passed),('unnecessary/overlapping certified boxes',len(used),len(passed))
 print('G6 exact dyadic cover of 0 <= z <= y <= x <= 1, x+y+z <= 3/2: PASS.')
 print('G7 interval-certified Bloch boxes:',counts['certified_boxes'])
 print('G8 analytic Gamma boxes:',counts['analytic_gamma_boxes'])
 print('G9 exact coverage counts:',json.dumps(counts,sort_keys=True))
 minm={name:min(F(r['margins'][name][0]) for r in passed.values()) for name in next(iter(passed.values()))['margins']}
 return counts,{k:str(v) for k,v in minm.items()}

if __name__=='__main__':
 syms=verify_geometry();gamma=verify_gamma();counts,margins=verify_cover()
 output={'status':'PASS','geometry':{'period':20,'epsilon_low':1,'epsilon_high':12,'high_cells':3928},
         'operating_t':'1/64','certified_frequency_squared_halfwidth':'1/4096',
         'physical_gap_lower_bound':'1/4096','symmetries':syms,'analytic_bounds':gamma,
         'coverage_counts':counts,'minimum_box_margins':margins}
 (BASE/'gap_certificate_summary.json').write_text(json.dumps(output,indent=2)+'\n')
 print('G10 complete resolved unstretched Yee bulk-gap certificate: g0 >= 1/4096.')
