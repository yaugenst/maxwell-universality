"""Exploratory inversion-symmetric dyadic scalar perturbation at four FCC L points; NOT certified."""
import sys,time,json
from pathlib import Path
import numpy as np
from scipy.sparse import diags
from scipy.sparse.linalg import eigsh
from threadpoolctl import threadpool_limits
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'work/defects/maxwell_round6'))
import yee_primitive as yp
from yee_bands import edge_epsilon
from exact_geometry import diamond_cells_exact
yp.diamond_cells=lambda p,radius=.25,eps_hi=12.:diamond_cells_exact(p,eps_hi)
model=yp.FCCYee(20,eps_hi=12.)
coords=np.stack(np.meshgrid(*[np.arange(20)]*3,indexing='ij'),axis=-1).reshape(-1,3)
idx,_=model.reduce(coords)
rng=np.random.default_rng(20261027);primitive=rng.integers(0,1024,size=model.n)
raw=primitive[idx].reshape(20,20,20)
perturb=(raw+raw[::-1,::-1,::-1])/2**21
model.cells+=perturb
ep=edge_epsilon(model.cells)[:,:10,:10]
model.eps=ep.reshape(-1,3).T.ravel();model.epsilon=diags(model.eps,format='csc')
points={'L+++':(.5,.5,.5),'L++-':(.5,.5,-.5),'L+-+':(.5,-.5,.5),'L-++':(-.5,.5,.5)}
results={}
with threadpool_limits(limits=1):
 for label,cart in points.items():
  x,y,z=cart;k=np.array([x,(x+y)/2,(x+z)/2]);st=time.monotonic()
  a=model.electric_matrix(k,1/64);eig,vec=eigsh(a,k=2,sigma=.009565,tol=1e-11)
  order=np.argsort(eig);eig=eig[order];vec=vec[:,order]
  record={'cart':cart,'eig':eig.tolist(),'residual':np.linalg.norm(a@vec-vec*eig,axis=0).tolist(),'seconds':time.monotonic()-st,'certified':False}
  results[label]=record;print(label,json.dumps(record),flush=True)
  Path(__file__).with_suffix('.json').write_text(json.dumps(results,indent=2)+'\n')
np.savez(Path(__file__).with_suffix('.npz'),original_primitive_numerators=primitive,full_perturbation_numerators=raw+raw[::-1,::-1,::-1],denominator=2**21,full_perturbation=perturb)
