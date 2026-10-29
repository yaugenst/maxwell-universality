"""Exact dyadic residual and inversion certificates at the four L fibers.

Each PASS proves two disjoint intervals containing same-parity eigenvalues.
Combining with the separately verified two-mode inertia brackets proves these
are the only eigenvalues in the bracket and are simple. This script does not
prove a global band minimum or a neighborhood curvature bound.
"""
import json,argparse
from pathlib import Path
from fractions import Fraction as F
import numpy as np
from exact_edge_arithmetic import ExactFiber,COORDS,quantize,dot,fstr

if not __debug__:
    raise RuntimeError('Exact acceptance requires assertions; do not run with -O or PYTHONOPTIMIZE.')

here=Path(__file__).resolve().parent
parser=argparse.ArgumentParser()
parser.add_argument('--output',type=Path,default=here/'inversion_point_residual_acceptance.json')
args=parser.parse_args()
witness=np.load(here/'make_inversion_point_witnesses.npz')
perturb=witness['perturbation_numerators'].tolist()
candidate=json.loads((here/'inversion_edge_material.json').read_text())
assert candidate['period']==20 and candidate['perturbation_denominator']==2**21
assert candidate['full_conventional_shape']==[20,20,20]
assert candidate['full_conventional_perturbation_numerators']==perturb
assert candidate['primitive_perturbation_numerators']==[perturb[x][y][z] for x,y,z in COORDS]
points={'L+++':(1,1,1),'L++-':(1,1,0),'L+-+':(1,0,1),'L-++':(-1,0,0)}
assert {tuple(x%2 for x in k) for k in points.values()}=={(1,1,1),(1,1,0),(1,0,1),(1,0,0)}
results={};intervals={}
for label,k2 in points.items():
    model=ExactFiber(k2,perturb)
    vec=witness[label+'_eigenvectors'];records=[];intervals[label]=[]
    assert vec.shape==(6000,2) and np.isfinite(vec).all() and np.isrealobj(vec)
    parity=-1 if label=='L+++' else 1
    for a in range(2):
        u=model.project(quantize(vec[:,a]),parity)
        assert model.invert(u)==[parity*x for x in u]
        norm=F(dot(u,u),1<<202)
        assert F(999,1000)<norm<F(1001,1000)
        result=model.eigen_residual(u)
        assert F(239,25000)<result['lower']<result['upper']<F(957,100000)
        intervals[label].append((result['lower'],result['upper']))
        records.append({
            'interval_exact':[fstr(result['lower']),fstr(result['upper'])],
            'center_decimal':float(result['center']),
            'residual_bound_exact':fstr(result['radius']),
            'residual_dyadic_exponent':result['residual_dyadic_exponent'],
            'inversion_parity_exact':parity,
            'primitive_k_twice_modulo_2':[x%2 for x in k2],
            'norm_squared_exact':fstr(norm)})
    assert intervals[label][0][1]<intervals[label][1][0]
    assert intervals[label][1][1]-intervals[label][0][0]<F(1,1<<20)
    results[label]=records
    print(label,'PASS: exact same-parity residual intervals',[(float(a),float(b)) for a,b in intervals[label]],flush=True)
lowest=intervals['L++-'][0]
assert lowest[1]<F(23913,2500000)
competitors=[intervals[k][0][0] for k in intervals if k!='L++-']
margin=min(competitors)-lowest[1]
assert margin>F(33,10**9)

# The only cross-module analytic inputs needed for point isolation are the
# original crystal's inertia counts and Weyl's inequality. Check their scalar
# transfer exactly, without treating a JSON status flag as proof of the inputs.
perturb_norm=F(1023,1<<26)
bracket_lower=F(1,256)
bracket_upper=F(5,256)-perturb_norm
tracked_lower=F(239,25000);tracked_upper=F(957,100000)
assert min(tracked_lower-bracket_lower,bracket_upper-tracked_upper)>F(11,2000)

output={
    'status':'PASS',
    'scope':'exact finite-fiber eigenvalue inclusion and inversion parity; simplicity and complete pair isolation use separately verified inertia brackets',
    'material_matches_canonical_full_integer_table':True,
    'points':results,'lowest_L_label':'L++-',
    'gap_to_other_L_lower_branches_exact':fstr(margin),
    'gap_to_other_L_lower_branches_lower_bound':'33/1000000000',
    'lowest_L_value_upper_bound':'23913/2500000',
    'complement_gap_transfer_lower_bound':'11/2000',
    'each_doublet_split_upper_bound':'1/1048576',
    'unproved_here':['continuous-neighborhood monotonicity','global exclusion of lower positive-band values']}
args.output.write_text(json.dumps(output,indent=2)+'\n')
print('PASS: L++- lower branch is uniquely lowest among the four L points by >33/10^9.')
print('PASS: exact Weyl scalar transfer gives complementary gap >11/2000, conditional only on the independent inertia certificates.')
print('NO CLAIM: this does not establish a unique global minimum on the Bloch torus.')
