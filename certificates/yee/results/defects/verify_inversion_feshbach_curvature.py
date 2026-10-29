"""Exact a posteriori two-mode Feshbach curvature certificate at L++-.

The imported mathematical premise is the independently interval-verified
two-mode isolation in (1/256,5/256), with complementary gap >11/2000.
All witness residuals, parity identities, error budgets and final LDL tests
in this file use integer/Fraction arithmetic. Floating arrays are witnesses.
"""
import json,math,argparse
from pathlib import Path
from fractions import Fraction as F
import numpy as np
from exact_edge_arithmetic import ExactFiber,COORDS,quantize,dot,apply_rows,ldl_positive,fstr

if not __debug__:
    raise RuntimeError('Exact acceptance requires assertions; do not run with -O or PYTHONOPTIMIZE.')

here=Path(__file__).resolve().parent
parser=argparse.ArgumentParser()
parser.add_argument('--stem',default='explore_inversion_edge_feshbach',choices=['explore_inversion_edge_feshbach','inversion_feshbach_lppp','inversion_feshbach_lpmp','inversion_feshbach_lmpp'])
parser.add_argument('--output',type=Path,default=None)
args=parser.parse_args()
w=np.load(here/(args.stem+'.npz'))
candidate=json.loads((here/'inversion_edge_material.json').read_text())
assert candidate['period']==20 and candidate['perturbation_denominator']==2**21
assert candidate['full_conventional_shape']==[20,20,20]
assert candidate['full_conventional_perturbation_numerators']==w['perturbation_numerators'].tolist()
assert candidate['primitive_perturbation_numerators']==[int(w['perturbation_numerators'][x,y,z]) for x,y,z in COORDS]
assert w['k_twice'].shape==(3,) and np.isfinite(w['k_twice']).all()
k_twice=tuple(int(x) for x in w['k_twice'])
assert all(k_twice[j]==w['k_twice'][j] for j in range(3))
expected_k={'explore_inversion_edge_feshbach':(1,1,0),'inversion_feshbach_lppp':(1,1,1),'inversion_feshbach_lpmp':(1,0,1),'inversion_feshbach_lmpp':(1,0,0)}[args.stem]
assert tuple(x%2 for x in k_twice)==expected_k
parity=int(w['pair_parity'])
assert parity==(-1 if args.stem=='inversion_feshbach_lppp' else 1)
model=ExactFiber(k_twice,w['perturbation_numerators'].tolist())
vec=w['inversion_perturbed_eigenvectors']
assert vec.shape==(6000,2) and np.isfinite(vec).all() and np.isrealobj(vec)
u=[model.project(quantize(vec[:,a]),parity) for a in range(2)]
den=1<<101
for x in u:assert model.invert(x)==[parity*a for a in x]
g=[[F(dot(a,b),den*den) for b in u] for a in u]
gram_error=F(1,10**12)
for sign in [-1,1]:
    ldl_positive([[F(i==j)*gram_error+sign*(g[i][j]-F(i==j)) for j in range(2)] for i in range(2)])
eig=[model.eigen_residual(x) for x in u]
assert eig[0]['upper']<eig[1]['lower']
assert eig[1]['upper']-eig[0]['lower']<F(1,1<<20)
assert all(F(239,25000)<e['lower']<e['upper']<F(957,100000) for e in eig)
lambda_bits=80;znum=eig[0]['lambda_numerator'];z=F(znum,1<<lambda_bits)
eigen_residual_bound=F(1,10**13)
residual_squared=sum(F(e['residual_squared_numerator'],den*den*(1<<(2*lambda_bits))) for e in eig)
assert residual_squared<=eigen_residual_bound**2

# The physical first derivative equals i*(pi/20)*B_i. Divide that known
# factor out of the floating solve to create an entirely rational witness.
sol=w['inversion_perturbed_complement_solutions']
assert sol.shape==(6000,6) and np.isfinite(sol).all()
y=[]
for i in range(3):
    yi=[]
    for a in range(2):
        values=np.imag(sol[:,2*i+a])/(math.pi/20)
        v=model.project(quantize(values),-parity)
        assert model.invert(v)==[-parity*x for x in v]
        yi.append(v)
    y.append(yi)
bu=[[apply_rows(model.B[i],x) for x in u] for i in range(3)]
solve_squared=F(0)
for i in range(3):
    for a in range(2):
        ay=model.apply_mass_scaled(y[i][a])
        r=[(aa<<(lambda_bits-29))-znum*yy-(bb<<lambda_bits) for aa,yy,bb in zip(ay,y[i][a],bu[i][a])]
        solve_squared+=F(dot(r,r),den*den*(1<<(2*lambda_bits)))
solve_residual_bound=F(1,1<<35)
assert solve_squared<=solve_residual_bound**2

# Machin's identity and alternating rational arctangent bounds enclose pi.
def atan_bounds(q,n=80):
    partial=sum(F((-1)**j,(2*j+1)*q**(2*j+1)) for j in range(n))
    following=F((-1)**n,(2*n+1)*q**(2*n+1))
    return min(partial,partial+following),max(partial,partial+following)
a,b=atan_bounds(5);c,d=atan_bounds(239)
raw_pi_lower=16*a-4*d;raw_pi_upper=16*b-4*c
pi_scale=10**25
pi_lower=F((raw_pi_lower*pi_scale).numerator//(raw_pi_lower*pi_scale).denominator,pi_scale)
pi_upper=F(-((-raw_pi_upper*pi_scale).numerator//(-raw_pi_upper*pi_scale).denominator),pi_scale)
assert pi_lower<=raw_pi_lower<raw_pi_upper<=pi_upper
assert F(3141592653589793238,10**18)<pi_lower<pi_upper<F(3141592653589793239,10**18)
alpha2_lo=pi_lower*pi_lower/400;alpha2_hi=pi_upper*pi_upper/400

flat_y=[v for block in y for v in block]
ygram=[[F(dot(a,b),den*den) for b in flat_y] for a in flat_y]
ldl_positive([[F(19*19*(i==j))-ygram[i][j] for j in range(6)] for i in range(6)])
assert pi_upper*19/20<F(3)
ldl_positive([[F(2909,1000)**2*F(i==j)-alpha2_hi*ygram[i][j] for j in range(6)] for i in range(6)])

tensor=[[None]*3 for _ in range(3)]
rounded=[[F(0)]*6 for _ in range(6)]
rounding_error=F(1,10**11)
for i in range(3):
    for j in range(3):
        du=[apply_rows(model.D[i][j],v) for v in u]
        block=[]
        for a in range(2):
            row=[]
            for b in range(2):
                value=F(dot(u[a],du[b])-dot(bu[i][a],y[j][b])-dot(bu[j][a],y[i][b]),den*den)
                lo,hi=sorted([value*alpha2_lo,value*alpha2_hi])
                scaled=(lo+hi)*10**12/2
                mid=F((2*scaled.numerator+scaled.denominator)//(2*scaled.denominator),10**12)
                assert mid-rounding_error<=lo<=hi<=mid+rounding_error
                row.append(mid);rounded[2*i+a][2*j+b]=mid
            block.append(row)
        tensor[i][j]=block
for i in range(6):
    for j in range(6):assert rounded[i][j]==rounded[j][i]

# A posteriori replacement of U by an exact orthonormal cluster basis Phi.
gap=F(11,2000)
projection_error=eigen_residual_bound/gap
basis_error=F(1,10**10)
assert projection_error+2*(gram_error+projection_error**2)<basis_error
energy_error=eigen_residual_bound
assert energy_error>=eig[0]['radius']
b_norm=max(sum(abs(v) for v in row.values()) for b in model.B for row in b)
d_norm=max(sum(abs(v) for v in row.values()) for dr in model.D for d in dr for row in d)
form_norm=alpha2_hi*(d_norm+2*F(b_norm*b_norm)/gap)
basis_form_error=basis_error*(2+basis_error)*form_norm
solve_form_error=2*alpha2_hi*b_norm*(1+gram_error)*solve_residual_bound/gap
energy_form_error=2*alpha2_hi*b_norm*b_norm*energy_error/(gap*gap)
# In this term the resolvent is changed from z to E with the exact
# orthonormal Phi held fixed. The separate basis term then changes Phi to U
# at z, so no ||U||^2 factor belongs in energy_form_error.
entry_error=F(1,10**5)
assert rounding_error+basis_form_error+solve_form_error+energy_form_error<entry_error

# Entry error <=epsilon gives 6x6 operator error <=6epsilon.
target=F(1,25)
pivots=ldl_positive([[rounded[i][j]-F(i==j)*(target+6*entry_error) for j in range(6)] for i in range(6)])
ldl_positive([[F(i==j)*(1-6*entry_error)-rounded[i][j] for j in range(6)] for i in range(6)])

# Full quadratic residual T_ij=(A_ij U-A_i Y_j-A_j Y_i)/2.
# In rational units A_i=i*alpha*B_i and Y_j=i*alpha*y_j, so the
# numerator is D_ij U+B_i y_j+B_j y_i with denominator 2*den.
traw=[[None]*3 for _ in range(3)]
for i in range(3):
    for j in range(3):
        traw[i][j]=[]
        for a in range(2):
            du=apply_rows(model.D[i][j],u[a])
            biyj=apply_rows(model.B[i],y[j][a]);bjyi=apply_rows(model.B[j],y[i][a])
            traw[i][j].append([aa+bb+cc for aa,bb,cc in zip(du,biyj,bjyi)])
raw_gram=[[F(0)]*6 for _ in range(6)]
for j in range(3):
    for k in range(3):
        for a in range(2):
            for b in range(2):
                raw_gram[2*j+a][2*k+b]=F(sum(dot(traw[i][j][a],traw[i][k][b]) for i in range(3)),4*den*den)
gram=[[alpha2_hi**2*x for x in row] for row in raw_gram]
ldl_positive([[F(4*(i==j))-gram[i][j] for j in range(6)] for i in range(6)])

# Compare true Gram and Hessian with rational witnesses. The three-by-three
# block matrix W has columns indexed by (direction, polarization), with
# G=W*W. A uniform block error eT gives ||Delta W||<=3eT.
total_hessian_error=rounding_error+basis_form_error+solve_form_error+energy_form_error
t_block_error=F(1,2)*form_norm*basis_error+alpha2_hi*b_norm*(solve_residual_bound/gap+energy_error*b_norm*(1+gram_error)/(gap*gap))
w_error=3*t_block_error
gram_error_bound=(4+w_error)*w_error
relative_constant=F(18,5)
relative_error=gram_error_bound+relative_constant*3*total_hessian_error
relative_margin=F(1,10000)
assert relative_error<relative_margin
relative_pivots=ldl_positive([[relative_constant*rounded[i][j]/2-gram[i][j]-F(i==j)*relative_margin for j in range(6)] for i in range(6)])
physical_y_error=pi_upper/20*(solve_residual_bound/gap+energy_error*b_norm*(1+gram_error)/(gap*gap)+b_norm*basis_error/gap)*2
assert F(2909,1000)+physical_y_error<F(291,100)

result={
    'status':'PASS',
    'point_primitive_k_twice':k_twice,
    'pair_parity':parity,
    'material_matches_common_exact_integer_candidate':True,
    'spectral_dependency':'independent original-L inertia certificates at shifts 1/256 and 5/256, transferred by exact scalar Weyl bounds',
    'conclusion':'the exact two-mode Feshbach Hessian 6x6 block is greater than (1/25) I; the simple lower-band Hessian is positive definite',
    'scope':'a genuine strict local Morse minimum, with no claim of a certified radius or global minimum',
    'eigen_residual_frobenius_bound':fstr(eigen_residual_bound),
    'solve_residual_frobenius_bound':fstr(solve_residual_bound),
    'cluster_basis_distance_bound':fstr(basis_error),
    'entrywise_total_error_bound':fstr(entry_error),
    'physical_derivative_solution_operator_norm_upper_bound':'291/100',
    'full_quadratic_residual_gram_relative_constant':'18/5',
    'feshbach_hessian_upper_bound':'1',
    'relative_gram_error_bound':fstr(relative_error),
    'relative_gram_ldl_pivots':[fstr(x) for x in relative_pivots],
    'integer_first_derivative_row_norm':b_norm,
    'integer_second_derivative_row_norm':d_norm,
    'rounded_hessian_block':[[fstr(x) for x in row] for row in rounded],
    'ldl_pivots':[fstr(x) for x in pivots],
    'exact_scalar_error_budget':{
        'basis':fstr(basis_form_error),'solve':fstr(solve_form_error),
        'energy':fstr(energy_form_error),'rounding':fstr(rounding_error)}}
out='inversion_feshbach_curvature_acceptance' if args.stem=='explore_inversion_edge_feshbach' else args.stem+'_curvature_acceptance'
output_path=args.output or here/(out+'.json')
output_path.write_text(json.dumps(result,indent=2)+'\n')
print('PASS: exact signed-permutation inversion, opposite-parity solve residuals, and cluster-basis error bounds.')
print('PASS: exact 6x6 rational LDL proves Feshbach Hessian > (1/25) I.')
print('PASS: exact residual Gram <= (18/5)*(half Hessian), Hessian < I, and ||Y||<291/100.')
print('PASS (using the independent spectral isolation certificates): this L point is a simple strict local Morse minimum.')
print('NO CLAIM: a radius-.05 local inequality or a global band minimum is not proved here.')
