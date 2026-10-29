# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Freeze untrusted actual global-center arithmetic for later Lean acceptance.

The canonical record/witness and native sources are read only. Native interval
results only propose rectangles; no native success is imported as a theorem.
"""
from pathlib import Path
from fractions import Fraction
import argparse, hashlib, importlib.util, json, os, sys, time
os.environ['OPENBLAS_NUM_THREADS']='1'
os.environ['OMP_NUM_THREADS']='1'
import numpy as np
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT.parent/'certificates/yee'
BASE=SOURCE/'work/bulk/global_certificate'
SNAPSHOT=SOURCE/'work/bulk/global_certificate'
OUT=ROOT/'evidence/global_center_proposals'
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def load_module(name,path):
 spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def main():
 parser=argparse.ArgumentParser();parser.add_argument('index',type=int);parser.add_argument('--derivatives',action='store_true');args=parser.parse_args()
 OUT.mkdir(exist_ok=True)
 proposal=BASE/'cover_proposals.json';records=json.loads(proposal.read_text())['accepted'];record=records[args.index]
 v=load_module('global_interval_proposals',SNAPSHOT/'interval_tools.py')
 geo=load_module('global_exact_geometry',BASE/'exact_geometry.py')
 base=geo.diamond_cells_exact(20,12,1).astype(np.int32)
 den=[]
 for axis in range(3):
  a,b=[j for j in range(3) if j!=axis]
  den.append(base+np.roll(base,1,a)+np.roll(base,1,b)+np.roll(np.roll(base,1,a),1,b))
 den=np.ascontiguousarray(64*np.stack(den,axis=-1)[:,:10,:10].reshape(2000,3)+157)
 witness=BASE/'witnesses'/record['witness'];start=time.monotonic()
 with np.load(witness,allow_pickle=False) as w:
  low=np.ascontiguousarray(w['low'],dtype=np.int32)
  raw=np.concatenate([w['F'],w['Fpos']],axis=2).astype(np.complex128)
 d=v.make_d(record['center']);lap=v.laplacian(d);input_field=v.witness(raw);field=v.project(input_field,d)
 curl=v.curl(d,field,True);inverse=v.fft(curl,True);spatial=v.material(inverse,den);weighted=v.fft(spatial)
 applied=v.add(v.curl(d,weighted),v.rat(field,1,64),True);compression=v.gram(field,applied)
 p0=v.I(Fraction(1023,1024))
 arrays={'low':low,'raw':input_field,'d':d,'lap':lap,'field':field,'curl':curl,'inverse':inverse,
  'spatial':spatial,'weighted':weighted,'applied':applied,'compression':compression,'material_den':den,
  'negative':v.shifted_identity(np.ascontiguousarray(compression[:2,:2]),-p0,-1),
  'positive':v.shifted_identity(np.ascontiguousarray(compression[2:,2:]),-p0,1)}
 if args.derivatives:
  gradient=v.gradient(d,low);arrays['gradient']=gradient
  theta=v.cb(0,2*v.PI/20)
  for axis in range(3):
   dp=np.zeros_like(d);plus=np.ascontiguousarray(d[:,axis,:]);plus[:,0]+=v.S
   dp[:,axis,:]=v.mul(plus,np.broadcast_to(theta,plus.shape));dp=np.ascontiguousarray(dp)
   ep=v.curl(dp,field,True);inv=v.fft(ep,True);sp=v.material(inv,den);ewp=v.fft(sp)
   db=v.add(v.curl(dp,weighted),v.curl(d,ewp));pp=v.pprime(d,dp,field);da=v.add(db,v.rat(pp,1,32))
   egp=v.curl(dp,gradient,True);ginv=v.fft(egp,True);gsp=v.material(ginv,den);gweight=v.fft(gsp)
   bgp=v.curl(d,gweight);gp=v.gprime_raw(d,dp,low);cross=v.add(bgp,v.rat(gp,1,32))
   for key,value in [('d',dp),('curl',ep),('inverse',inv),('spatial',sp),('weighted',ewp),('magnetic',db),('projection',pp),('auxiliary',da),('gradient_curl',egp),('gradient_inverse',ginv),('gradient_spatial',gsp),('gradient_weighted',gweight),('gradient_magnetic',bgp),('gradient_first',gp),('cross',cross)]:
    arrays[f'axis{axis}_{key}']=value
 path=OUT/f'record{args.index:04d}.npz';np.savez_compressed(path,**arrays)
 meta={'index':args.index,'record':record,'precision':v.B,'source_sha256':{str(p.relative_to(SOURCE)):sha(p) for p in [proposal,witness,BASE/'exact_geometry.py',SNAPSHOT/'interval_tools.py',SNAPSHOT/'interval_kernel.so']},'output_sha256':sha(path),'arrays':{k:list(a.shape) for k,a in arrays.items()},'seconds':time.monotonic()-start,'proof_status':'untrusted proposals; Lean arithmetic and operator bindings required'}
 (OUT/f'record{args.index:04d}.json').write_text(json.dumps(meta,indent=2)+'\n');print(json.dumps({'index':args.index,'bytes':path.stat().st_size,'seconds':meta['seconds'],'sha256':meta['output_sha256']}),flush=True)
if __name__=='__main__':main()
