"""Exploratory symmetry-point electric band values; NOT certification."""
import sys,time,json
from pathlib import Path
import numpy as np
from scipy.sparse.linalg import eigsh
from threadpoolctl import threadpool_limits
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'work/defects/maxwell_round6'))
import yee_primitive as yp
from exact_geometry import diamond_cells_exact
yp.diamond_cells=lambda p,radius=.25,eps_hi=12.:diamond_cells_exact(p,eps_hi)
model=yp.FCCYee(20,eps_hi=12.)
points={'Gamma':(0,0,0),'X':(0,1,0),'L':(.5,.5,.5),'W':(.5,1,0),'K':(.75,.75,0),'U':(.25,1,.25)}
results={}
with threadpool_limits(limits=1):
 for label,cart in points.items():
  x,y,z=cart; k=np.array([x,(x+y)/2,(x+z)/2]); start=time.monotonic()
  a=model.electric_matrix(k,1/64)
  eig,vec=eigsh(a,k=10,sigma=0,tol=1e-10)
  order=np.argsort(eig);eig=eig[order];vec=vec[:,order]
  residual=np.linalg.norm(a@vec-vec*eig,axis=0)
  record={'cart':cart,'primitive_frac':k.tolist(),'eigenvalues':eig.tolist(),'residuals':residual.tolist(),'seconds':time.monotonic()-start,'certified':False}
  results[label]=record
  print(label,json.dumps(record),flush=True)
Path(__file__).with_suffix('.json').write_text(json.dumps(results,indent=2)+'\n')
