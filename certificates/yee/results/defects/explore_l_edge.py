"""Targeted L-edge curvature/splitting exploration. All assertions numerical."""
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
points={'L':(.5,.5,.5),'L+x':(.51,.5,.5),'L+111':(.51,.51,.51),'L+1-10':(.51,.49,.5),'L+half111':(.505,.505,.505),'L+half1-10':(.505,.495,.5)}
results={}
with threadpool_limits(limits=1):
 for label,cart in points.items():
  x,y,z=cart;k=np.array([x,(x+y)/2,(x+z)/2]);start=time.monotonic()
  a=model.electric_matrix(k,1/64)
  eig,vec=eigsh(a,k=4,sigma=.00957,tol=1e-11)
  order=np.argsort(eig);eig=eig[order];vec=vec[:,order]
  res=np.linalg.norm(a@vec-vec*eig,axis=0)
  record={'cart':cart,'eig':eig.tolist(),'residual':res.tolist(),'seconds':time.monotonic()-start,'certified':False}
  results[label]=record;print(label,json.dumps(record),flush=True)
 # A fixed dyadic scalar-cell perturbation, FCC-periodic by exact reduction.
 coords=np.stack(np.meshgrid(*[np.arange(20)]*3,indexing='ij'),axis=-1).reshape(-1,3)
 idx,_=model.reduce(coords)
 rng=np.random.default_rng(20261027)
 primitive=rng.integers(0,1024,size=model.n)
 perturb=(primitive[idx].reshape(20,20,20)/2**20)
 model.cells+=perturb
 ep=edge_epsilon(model.cells)[:,:10,:10]
 model.eps=ep.reshape(-1,3).T.ravel();model.epsilon=diags(model.eps,format='csc')
 for label,cart in {'pert_L':(.5,.5,.5),'pert_L+x':(.501,.5,.5),'pert_L-x':(.499,.5,.5)}.items():
  x,y,z=cart;k=np.array([x,(x+y)/2,(x+z)/2]);start=time.monotonic()
  a=model.electric_matrix(k,1/64);eig,vec=eigsh(a,k=4,sigma=.00957,tol=1e-11)
  order=np.argsort(eig);eig=eig[order];vec=vec[:,order]
  res=np.linalg.norm(a@vec-vec*eig,axis=0)
  record={'cart':cart,'eig':eig.tolist(),'residual':res.tolist(),'seconds':time.monotonic()-start,'certified':False}
  results[label]=record;print(label,json.dumps(record),flush=True)
np.savez(Path(__file__).with_suffix('.npz'),cell_perturbation=perturb,primitive_integers=primitive)
Path(__file__).with_suffix('.json').write_text(json.dumps(results,indent=2)+'\n')
