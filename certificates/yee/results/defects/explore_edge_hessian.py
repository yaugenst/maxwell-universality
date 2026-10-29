"""Analytic Bloch derivative Hessian evaluated in floating point; NOT a certificate."""
import sys,time,json
from pathlib import Path
import numpy as np
from scipy.sparse import coo_matrix,bmat,diags,csc_matrix
from scipy.sparse.linalg import eigsh,splu
from threadpoolctl import threadpool_limits
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'work/defects/maxwell_round6'))
import yee_primitive as yp
from yee_bands import edge_epsilon
from exact_geometry import diamond_cells_exact
yp.diamond_cells=lambda p,radius=.25,eps_hi=12.:diamond_cells_exact(p,eps_hi)
model=yp.FCCYee(20,eps_hi=12.)
coords=np.stack(np.meshgrid(*[np.arange(20)]*3,indexing='ij'),axis=-1).reshape(-1,3)
idx,_=model.reduce(coords);rng=np.random.default_rng(20261027)
primitive=rng.integers(0,1024,size=model.n);perturb=primitive[idx].reshape(20,20,20)/2**20
model.cells+=perturb;ep=edge_epsilon(model.cells)[:,:10,:10]
model.eps=ep.reshape(-1,3).T.ravel();model.epsilon=diags(model.eps,format='csc')
# cartesian reciprocal coordinates q=(1/2,1/2,-1/2), primitive fractions(.5,.5,0)
k=np.array([.5,.5,0.]);n=model.n
jac=np.array([[1,0,0],[.5,.5,0],[.5,0,.5]])

def curl_derivative(axes):
 dd=[]
 for ids,translations in model.maps:
  integers=np.rint(2*(translations@k)).astype(int)
  assert np.max(abs(2*(translations@k)-integers))<1e-12
  values=(-1.)**integers
  if axes:
   values=values.astype(complex)
   for axis in axes: values*=2j*np.pi*(translations@jac[:,axis])
   dd.append(coo_matrix((values,(np.arange(n),ids)),shape=(n,n)).tocsc())
  else:
   dd.append(coo_matrix((np.r_[values,-np.ones(n)],(np.r_[np.arange(n),np.arange(n)],np.r_[ids,np.arange(n)])),shape=(n,n)).tocsc())
 dx,dy,dz=dd
 return bmat([[None,-dz,dy],[dz,None,-dx],[-dy,dx,None]],format='csc')
with threadpool_limits(limits=1):
 start=time.monotonic();c=curl_derivative([]);a=(c.T@c-model.epsilon/64).tocsc()
 eig,vec=eigsh(a,k=2,sigma=.009565,tol=1e-12)
 order=np.argsort(eig);eig=eig[order];vec=vec[:,order];lam=eig[0];u=vec[:,0]
 cs=[curl_derivative([j]) for j in range(3)]
 ais=[(v.conj().T@c+c.T@v).tocsc() for v in cs]
 forcing=np.column_stack([v@u-u*np.vdot(u,v@u) for v in ais])
 border=bmat([[a-lam*diags(np.ones(3*n)),csc_matrix(u[:,None])],[csc_matrix(u[None,:]),None]],format='csc')
 lu=splu(border.astype(complex));solution=lu.solve(np.vstack([forcing,np.zeros((1,3))]));derivative=solution[:-1]
 hessian=np.empty((3,3))
 for i in range(3):
  for j in range(3):
   cij=curl_derivative([i,j]);aij=cij.conj().T@c+cs[i].conj().T@cs[j]+cs[j].conj().T@cs[i]+c.T@cij
   hessian[i,j]=(np.vdot(u,aij@u)-np.vdot(forcing[:,i],derivative[:,j])-np.vdot(forcing[:,j],derivative[:,i])).real
 hessian=(hessian+hessian.T)/2
 result={'certified':False,'cartesian_point':[.5,.5,-.5],'eigenvalues':eig.tolist(),'eigen_residual':np.linalg.norm(a@vec-vec*eig,axis=0).tolist(),'hessian_in_cartesian_reciprocal_coordinates':hessian.tolist(),'hessian_eigenvalues':np.linalg.eigvalsh(hessian).tolist(),'bordered_solve_residual':float(np.linalg.norm(border@solution-np.vstack([forcing,np.zeros((1,3))]))),'gradient':[float(np.vdot(u,v@u).real) for v in ais],'seconds':time.monotonic()-start}
 print(json.dumps(result,indent=2),flush=True)
 Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
 np.savez(Path(__file__).with_suffix('.npz'),eigenvalues=eig,eigenvectors=vec,hessian=hessian,derivative=derivative,primitive_perturbation_numerators=primitive,denominator=2**20)
