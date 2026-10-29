"""Floating-point inversion/parity and two-mode Feshbach prototype.

No spectral interval, gap, curvature, or global-minimum certificate is claimed.
The center-based Bloch gauge has small derivatives and constant inversion.
"""
import sys,time,json,argparse
from pathlib import Path
import numpy as np
from scipy.sparse import coo_matrix,bmat,diags,csc_matrix
from scipy.sparse.linalg import eigsh,splu
from scipy.linalg import eigvalsh as generalized_eigvalsh
from threadpoolctl import threadpool_limits
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'work/defects/maxwell_round6'))
import yee_primitive as yp
from yee_bands import edge_epsilon
from exact_geometry import diamond_cells_exact
yp.diamond_cells=lambda p,radius=.25,eps_hi=12.:diamond_cells_exact(p,eps_hi)
parser=argparse.ArgumentParser()
parser.add_argument('--point',choices=['lppp','lppm','lpmp','lmpp'],default=None)
parser.add_argument('--skip-original',action='store_true')
args=parser.parse_args()
cartesian={'lppp':(.5,.5,.5),'lppm':(.5,.5,-.5),'lpmp':(.5,-.5,.5),'lmpp':(-.5,.5,.5)}[args.point or 'lppm']
stem=Path(__file__).with_name('inversion_feshbach_'+args.point) if args.point else Path(__file__).with_suffix('')
model=yp.FCCYee(20,eps_hi=12.)
coords=np.stack(np.meshgrid(*[np.arange(20)]*3,indexing='ij'),axis=-1).reshape(-1,3)
idx,_=model.reduce(coords)
primitive=np.random.default_rng(20261027).integers(0,1024,size=model.n)
raw=primitive[idx].reshape(20,20,20)
perturb_numerator=raw+raw[::-1,::-1,::-1]
assert np.array_equal(model.cells,model.cells[::-1,::-1,::-1])
assert np.array_equal(perturb_numerator,perturb_numerator[::-1,::-1,::-1])
n=model.n;qx,qy,qz=cartesian;k=np.array([qx,(qx+qy)/2,(qx+qz)/2]);kappa=2*np.pi/20
identity=diags(np.ones(n),format='csc')
shifts=[]
for ids,translations in model.maps:
    integers=np.rint(2*(translations@k)).astype(int)
    assert np.max(abs(2*(translations@k)-integers))==0
    shifts.append(coo_matrix(((-1.)**integers,(np.arange(n),ids)),shape=(n,n)).tocsc())

def curl_derivative(axes):
    dd=[]
    for axis,shift in enumerate(shifts):
        if axes and any(a!=axis for a in axes):
            dd.append(csc_matrix((n,n),dtype=complex))
        else:
            power=len(axes)
            dd.append((1j*kappa/2)**power*shift-(-1j*kappa/2)**power*identity)
    dx,dy,dz=dd
    return bmat([[None,-dz,dy],[dz,None,-dx],[-dy,dx,None]],format='csc')

# Polar-vector inversion sends an electric edge (r,j) to (-r-e_j,j).
inv_cols=[];inv_vals=[]
for j in range(3):
    target=-model.coords.copy();target[:,j]-=1
    ids,translations=model.reduce(target)
    exponent=np.rint(2*(translations@k)).astype(int)
    assert np.max(abs(2*(translations@k)-exponent))==0
    inv_cols.extend((ids+j*n).tolist());inv_vals.extend((-(-1.)**exponent).tolist())
inversion=coo_matrix((inv_vals,(np.arange(3*n),inv_cols)),shape=(3*n,3*n)).tocsc()
assert (inversion@inversion-diags(np.ones(3*n))).nnz==0
c=curl_derivative([]).real.tocsc()
cs=[curl_derivative([j]) for j in range(3)]
ais=[(v.conj().T@c+c.T@v).tocsc() for v in cs]
aijs=[[None]*3 for _ in range(3)]
for i in range(3):
    for j in range(3):
        cij=curl_derivative([i,j])
        aijs[i][j]=(cij.conj().T@c+cs[i].conj().T@cs[j]+cs[j].conj().T@cs[i]+c.T@cij).tocsc()

def sparse_norm_upper(x):
    return float(np.sqrt(np.max(abs(x).sum(axis=0))*np.max(abs(x).sum(axis=1))))

results={'certified':False,'cartesian_point':cartesian,
         'material_denominator':2**21,'material_numerator_max':int(perturb_numerator.max()),
         'inversion_square_exact':True,
         'first_derivative_inversion_anticommutator_norms':
             [sparse_norm_upper(inversion@v+v@inversion) for v in ais]}
archive={'perturbation_numerators':perturb_numerator,'denominator':2**21,
         'k_twice':np.rint(2*k).astype(int),'cartesian_point':np.array(cartesian),
         'pair_parity':-1 if args.point=='lppp' else 1}
with threadpool_limits(limits=1):
    for label in (['inversion_perturbed'] if args.skip_original else ['original','inversion_perturbed']):
        start=time.monotonic()
        cells=model.cells if label=='original' else model.cells+perturb_numerator/2**21
        eps=edge_epsilon(cells)[:,:10,:10].reshape(-1,3).T.ravel()
        a=(c.T@c-diags(eps/64)).tocsc()
        inv_comm=inversion@a-a@inversion
        assert inv_comm.nnz==0,(label,sparse_norm_upper(inv_comm))
        eig,vec=eigsh(a,k=2,sigma=.009565,tol=1e-12)
        order=np.argsort(eig);eig=eig[order];vec=vec[:,order]
        # Deflate the entire pair: the inverse only depends on its complement gap.
        z=float(eig[0]);forcing=np.column_stack([v@vec for v in ais])
        forcing-=vec@(vec.T@forcing)
        border=bmat([[a-z*diags(np.ones(3*n)),csc_matrix(vec)],
                     [csc_matrix(vec.T),None]],format='csc')
        rhs=np.vstack([forcing,np.zeros((2,6))])
        lu=splu(border.astype(complex));solution=lu.solve(rhs);derivative=solution[:-2]
        tensor=np.empty((3,3,2,2),complex)
        for i in range(3):
            for j in range(3):
                tensor[i,j]=vec.T@(aijs[i][j]@vec)
                tensor[i,j]-=forcing[:,2*i:2*i+2].conj().T@derivative[:,2*j:2*j+2]
                tensor[i,j]-=forcing[:,2*j:2*j+2].conj().T@derivative[:,2*i:2*i+2]
        tensor=(tensor+tensor.transpose(1,0,3,2).conj())/2
        trial_quadratic=[];trial_quadratic_perp=[]
        for i in range(3):
            for j in range(3):
                block2=.5*(aijs[i][j]@vec-ais[i]@derivative[:,2*j:2*j+2]-ais[j]@derivative[:,2*i:2*i+2])
                trial_quadratic.append(block2)
                trial_quadratic_perp.append(block2-vec@(vec.T@block2))
        block=tensor.transpose(0,2,1,3).reshape(6,6)
        quadratic_gram=np.empty((6,6),complex)
        for j in range(3):
            for k2 in range(3):
                quadratic_gram[2*j:2*j+2,2*k2:2*k2+2]=sum(trial_quadratic_perp[3*i+j].conj().T@trial_quadratic_perp[3*i+k2] for i in range(3))
        eigH=np.linalg.eigvalsh(tensor[:,:,0,0].real)
        # Deterministic unit-sphere survey is candidate data only.
        directions=np.random.default_rng(92).normal(size=(20000,3))
        directions/=np.linalg.norm(directions,axis=1)[:,None]
        quadratic=np.einsum('ni,nj,ijab->nab',directions,directions,tensor)
        vals=np.linalg.eigvalsh(quadratic)
        result={
            'eigenvalues':eig.tolist(),
            'eigen_residuals':np.linalg.norm(a@vec-vec*eig,axis=0).tolist(),
            'inversion_commutator_exact_zero':True,
            'pair_inversion_matrix':(vec.T@(inversion@vec)).tolist(),
            'pair_inversion_plus_residuals':np.linalg.norm(inversion@vec-vec,axis=0).tolist(),
            'pair_inversion_minus_residuals':np.linalg.norm(inversion@vec+vec,axis=0).tolist(),
            'pair_first_derivative_matrices_real':[np.real(vec.T@(v@vec)).tolist() for v in ais],
            'pair_first_derivative_matrices_imag':[np.imag(vec.T@(v@vec)).tolist() for v in ais],
            'feshbach_hessian_tensor_real':tensor.real.tolist(),
            'feshbach_hessian_tensor_imag_norm':float(np.linalg.norm(tensor.imag)),
            'feshbach_hessian_block_eigenvalues':np.linalg.eigvalsh(block).tolist(),
            'sampled_directional_min_eigenvalue':float(vals[:,0].min()),
            'sampled_directional_minimizer':directions[np.argmin(vals[:,0])].tolist(),
            'lowest_branch_hessian':tensor[:,:,0,0].real.tolist(),
            'lowest_branch_hessian_eigenvalues':eigH.tolist(),
            'forcing_norm':float(np.linalg.norm(forcing,2)),
            'complement_solve_norm':float(np.linalg.norm(derivative,2)),
            'trial_quadratic_stacked_norm':float(np.linalg.norm(np.column_stack(trial_quadratic),2)),
            'trial_quadratic_perp_stacked_norm':float(np.linalg.norm(np.column_stack(trial_quadratic_perp),2)),
            'trial_quadratic_gram_over_half_hessian_eigenvalues':generalized_eigvalsh(quadratic_gram,.5*block).tolist(),
            'bordered_solve_residual':float(np.linalg.norm(border@solution-rhs)),
            'seconds':time.monotonic()-start}
        results[label]=result
        archive[label+'_eigenvalues']=eig;archive[label+'_eigenvectors']=vec
        archive[label+'_feshbach_tensor']=tensor;archive[label+'_complement_solutions']=derivative
        archive[label+'_trial_quadratic_gram']=quadratic_gram
        print(label,json.dumps(result,indent=2),flush=True)
stem.with_suffix('.json').write_text(json.dumps(results,indent=2)+'\n')
np.savez(stem.with_suffix('.npz'),**archive)
