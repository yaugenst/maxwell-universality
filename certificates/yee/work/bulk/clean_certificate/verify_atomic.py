"""Canonical fresh H1 replay with one closed atomic evidence file per point.
The old frozen kernel, verifier and604 witnesses are imported unchanged.
No stored PASS record substitutes for a fresh matrix check.
"""
from __future__ import annotations
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor,as_completed
import json,hashlib,time,argparse,uuid
import reproduce as frozen
BASE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def atomic_bytes(path,data):
 tmp=path.with_name(path.name+'.tmp-'+uuid.uuid4().hex)
 with tmp.open('xb') as f:f.write(data);f.flush();os.fsync(f.fileno())
 os.replace(tmp,path)
 if path.read_bytes()!=data:raise RuntimeError('Atomic evidence readback mismatch: '+str(path))
 return hashlib.sha256(data).hexdigest()
def atomic_json(path,data):return atomic_bytes(path,(json.dumps(data,sort_keys=True)+'\n').encode())
def work(r,out,driver_hash,manifest_hash):
 a=frozen.verify_one(r)
 a['atomic_driver_sha256']=driver_hash;a['atomic_manifest_sha256']=manifest_hash
 path=Path(out)/'points'/(r['witness']+'.json');digest=atomic_json(path,a)
 check=json.loads(path.read_text());assert check==a and sha(path)==digest
 return r['witness'],digest
def main():
 if not __debug__:raise RuntimeError('Do not disable assertions')
 ap=argparse.ArgumentParser();ap.add_argument('--workers',type=int,default=6);ap.add_argument('--output',type=Path,default=BASE/'verification_atomic_final');a=ap.parse_args();assert a.workers>=1
 out=a.output.resolve();(out/'points').mkdir(parents=True,exist_ok=True)
 driver_hash=sha(Path(__file__));manifest_hash=sha(BASE/'atomic_driver_manifest.json');manifest=json.loads((BASE/'atomic_driver_manifest.json').read_text())
 assert manifest['atomic_driver_sha256']==driver_hash
 assert manifest['frozen_evidence_manifest_sha256']==sha(BASE/'evidence_manifest.json')
 records=frozen.proposals();sources=frozen.source_hashes();frozen.compile_kernel(out)
 started=time.monotonic();receipts={}
 print('ATOMIC_FULL_REPLAY_START',len(records),'workers',a.workers,flush=True)
 with ProcessPoolExecutor(max_workers=a.workers) as pool:
  for i,f in enumerate(as_completed([pool.submit(work,r,str(out),driver_hash,manifest_hash) for r in records]),1):
   name,digest=f.result();assert name not in receipts;receipts[name]=digest
   if i%10==0 or i==len(records):print('ATOMIC_FULL_MATRIX_CHECKS',i,'/',len(records),'seconds',time.monotonic()-started,flush=True)
 assert len(receipts)==len(records)==604 and frozen.source_hashes()==sources
 actual=[]
 for r in records:
  path=out/'points'/(r['witness']+'.json');assert sha(path)==receipts[r['witness']]
  x=json.loads(path.read_text());assert x['center']==r['center'] and x['halfwidth']==r['halfwidth'] and x['witness']==r['witness']
  assert x['atomic_driver_sha256']==driver_hash and x['atomic_manifest_sha256']==manifest_hash
  assert x['witness_sha256']==sha(BASE/'witnesses'/r['witness'])
  actual.append(x)
 for i in range(11):
  subset=actual[len(actual)*i//11:len(actual)*(i+1)//11]
  path=out/f'shard_{i:02d}.jsonl';data=(''.join(json.dumps(x)+'\n' for x in subset)).encode();digest=atomic_bytes(path,data)
  reread=[json.loads(x) for x in path.read_text().splitlines()];assert reread==subset
  atomic_json(out/f'shard_{i:02d}.metadata.json',{'index':i,'shards':11,'count':len(subset),'source_sha256':sources,'records_sha256':digest,'elapsed_seconds':time.monotonic()-started,'status':'FRESH_FULL_MATRIX_CHECKS_COMPLETED','atomic_driver_sha256':driver_hash,'atomic_manifest_sha256':manifest_hash})
 atomic_json(out/'atomic_point_receipts.json',{'points':receipts,'count':604,'atomic_driver_sha256':driver_hash,'atomic_manifest_sha256':manifest_hash})
 frozen.finalize(records,11,out)
 summary=json.loads((out/'reproduction_summary.json').read_text());summary.update({'atomic_driver_sha256':driver_hash,'atomic_manifest_sha256':manifest_hash,'evidence_logging':'one atomic closed file per point with immediate readback/hash; aggregate written atomically and reread','elapsed_seconds':time.monotonic()-started})
 atomic_json(out/'reproduction_summary.json',summary)
 print('ATOMIC_ALL_604_FULL_REPRODUCTION_COMPLETE',time.monotonic()-started,flush=True)
if __name__=='__main__':main()
