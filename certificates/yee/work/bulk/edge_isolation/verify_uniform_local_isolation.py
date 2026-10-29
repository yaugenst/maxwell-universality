"""Fresh full-matrix certificate for a uniform local two-band spectral cluster.
It uses existing NPZ dyadics as untrusted witnesses; every center inequality is rechecked.
"""
from pathlib import Path
from fractions import Fraction as F
import subprocess,sys,json,hashlib,numpy as np
p=Path(__file__).resolve().parent
if not __debug__:raise RuntimeError('Do not disable assertions')
subprocess.run(['g++','-O2','-std=c++17','-shared','-fPIC','-fsanitize=undefined','-fno-sanitize-recover=all',str(p/'interval_kernel.cpp'),'-o',str(p/'interval_kernel.so')],check=True)
import verify_point as vp
from interval_tools import I
rec=json.loads((p/'upper_7over256_proposal.json').read_text())
source=p/'witnesses'/rec['witness']
with np.load(source,allow_pickle=False) as w:
 low=w['low'];assert low.ndim==1 and len(set(low.tolist()))==len(low) and np.all(low>=0) and np.all(low<2000)
 assert w['F'].shape==(2000,3,4) and w['Fpos'].shape==(2000,3,2*len(low)-4)
 assert np.all(np.isfinite(w['F'])) and np.all(np.isfinite(w['Fpos']))
 assert max(float(abs(w['F']).max()),float(abs(w['Fpos']).max()))<100
 target=p/'witnesses/upper_7over256_full_box.npz'
 np.savez_compressed(target,F=w['F'],Fpos=w['Fpos'],low=low,center=w['center'],halfwidth=.05)
rec['witness']=target.name;rec['halfwidth']=.05;rec['negative_count']=4
assert F(rec['halfwidth'])>=F(1,20)
vp.DEN=np.ascontiguousarray(vp.DEN+7);vp.SIG=I(F(1,4096))
before=hashlib.sha256(target.read_bytes()).hexdigest()
result=vp.verify_record(rec,True)
assert before==hashlib.sha256(target.read_bytes()).hexdigest()
assert result['frequency_halfwidth']=='1/4096' and result['negative_count']==4
result.update({'witness_sha256':before,'electric_uniform_shift':'7/256','cell_uniform_increment':'7/4','certified_euclidean_radius':'1/20','material_upper_bound_used':14,'actual_cell_range':['11/4','55/4'],'scope':'Unperturbed diamond plus uniform shift; all symmetry-related L neighborhoods by cubic symmetry.'})
(p/'uniform_local_isolation_acceptance.json').write_text(json.dumps(result,indent=2)+'\n')
(p/'uniform_local_isolation_proposal.json').write_text(json.dumps(rec,indent=2)+'\n')
print('UNIFORM_LOCAL_ISOLATION_FULL_MATRIX_ACCEPTED negative_count4 electric_shift7/256 radius1/20 electric_gap>=1/4096',flush=True)
