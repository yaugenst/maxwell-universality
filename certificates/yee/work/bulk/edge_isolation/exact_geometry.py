"""Exact integer membership for diamond spheres, radius P/4.
Material labels are exact; floating spectral calculations remain non-rigorous.
"""
import numpy as np

def diamond_cells_exact(p=20,eps_hi=11.56,eps_lo=1.):
    xyz=np.stack(np.meshgrid(*[8*np.arange(p,dtype=np.int64)+4]*3,indexing='ij'),axis=-1)
    fcc=np.array([[0,0,0],[0,4*p,4*p],[4*p,0,4*p],[4*p,4*p,0]],dtype=np.int64)
    centers=np.concatenate([fcc+p,fcc-p])%(8*p)
    dist=np.full((p,p,p),np.iinfo(np.int64).max,dtype=np.int64)
    for c in centers:
        d=(xyz-c+4*p)%(8*p)-4*p
        dist=np.minimum(dist,np.sum(d*d,axis=-1))
    mask=dist<=4*p*p
    return np.where(mask,eps_hi,eps_lo)
