"""Generate floating witnesses for a separate exact integer residual checker."""
import sys,json,time
from pathlib import Path
import numpy as np
from scipy.sparse import coo_matrix,bmat,diags
from scipy.sparse.linalg import eigsh
from threadpoolctl import threadpool_limits
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'work/defects/maxwell_round6'))
import yee_primitive as yp
from yee_bands import edge_epsilon
from exact_geometry import diamond_cells_exact
yp.diamond_cells=lambda p,radius=.25,eps_hi=12.:diamond_cells_exact(p,eps_hi)
model=yp.FCCYee(20,eps_hi=12.)
material=np.load(Path(__file__).with_name('explore_inversion_l_points.npz'))
perturb=material['full_perturbation_numerators']
model.cells+=perturb/2**21
eps=edge_epsilon(model.cells)[:,:10,:10].reshape(-1,3).T.ravel()
n=model.n
points={'L+++':(.5,.5,.5),'L++-':(.5,.5,-.5),'L+-+':(.5,-.5,.5),'L-++':(-.5,.5,.5)}
archive={'perturbation_numerators':perturb,'denominator':2**21}
summary={}
with threadpool_limits(limits=1):
    for label,cart in points.items():
        start=time.monotonic();x,y,z=cart
        k=np.array([x,(x+y)/2,(x+z)/2]);dd=[]
        for ids,translations in model.maps:
            exponent=np.rint(2*(translations@k)).astype(int)
            assert np.max(abs(2*(translations@k)-exponent))==0
            shift=coo_matrix(((-1.)**exponent,(np.arange(n),ids)),shape=(n,n)).tocsc()
            dd.append(shift-diags(np.ones(n)))
        dx,dy,dz=dd
        c=bmat([[None,-dz,dy],[dz,None,-dx],[-dy,dx,None]],format='csc')
        a=(c.T@c-diags(eps/64)).tocsc()
        eig,vec=eigsh(a,k=2,sigma=.009565,tol=1e-12)
        order=np.argsort(eig);eig=eig[order];vec=vec[:,order]
        archive[label+'_eigenvalues']=eig;archive[label+'_eigenvectors']=vec
        summary[label]={'cart':cart,'eigenvalues':eig.tolist(),'residuals':np.linalg.norm(a@vec-vec*eig,axis=0).tolist(),'seconds':time.monotonic()-start}
        print(label,json.dumps(summary[label]),flush=True)
np.savez(Path(__file__).with_suffix('.npz'),**archive)
Path(__file__).with_suffix('.json').write_text(json.dumps({'certified':False,'points':summary},indent=2)+'\n')
