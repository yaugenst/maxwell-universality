# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Direct kernel builds for the six actual point low-space Schur proposals."""
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import subprocess
import time

ROOT=Path(__file__).resolve().parent
OUT=ROOT/'evidence/point_inertia_schur_compile'
OUT.mkdir(exist_ok=True)


def compile_matrix(item):
    name,n=item
    modules=[name+'Data']
    for i in reversed(range(n)):
        if n-i>18:
            modules.extend(f'{name}Step{i:02d}Row{j:02d}' for j in range(n-i-1))
        modules.append(f'{name}Step{i:02d}')
    modules.append(name)
    receipt=OUT/f'{name}.json'
    previous={r['module']:r for r in json.loads(receipt.read_text())} if receipt.exists() else {}
    checks=[]
    for mod in modules:
        src=ROOT/f'Maxwell/Certificate/PointInertia/{mod}.lean'
        obj=ROOT/f'.lake/build/lib/lean/Maxwell/Certificate/PointInertia/{mod}.olean'
        old=previous.get(mod)
        if old and old['exit_code']==0 and obj.exists() and old['source_sha256']==hashlib.sha256(src.read_bytes()).hexdigest() and old.get('object_sha256')==hashlib.sha256(obj.read_bytes()).hexdigest():
            checks.append({**old,'reused_verified_artifact':True})
            receipt.write_text(json.dumps(checks,indent=2)+'\n')
            continue
        start=time.monotonic()
        cmd=['nice','-n10','/usr/bin/time','-v','-o',str(OUT/f'{mod}.time'),
             str(Path.home()/'.elan/bin/lake'),'env','lean','-j1','-M4500',
             '-DwarningAsError=true','-o',str(obj),str(src)]
        with (OUT/f'{mod}.log').open('w') as log:
            result=subprocess.run(cmd,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
        row={'module':mod,'exit_code':result.returncode,'seconds':time.monotonic()-start,
             'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest()}
        if result.returncode==0:
            row['object_sha256']=hashlib.sha256(obj.read_bytes()).hexdigest()
        checks.append(row)
        (OUT/f'{name}.json').write_text(json.dumps(checks,indent=2)+'\n')
        if result.returncode:
            raise RuntimeError(f'{mod} failed: {OUT/mod}.log')
    print(f'{name}: all {n} Schur pivots and updates checked.',flush=True)
    return checks


with ThreadPoolExecutor(max_workers=1) as pool:
    results=list(pool.map(compile_matrix,[('LowerNegative',2),('LowerPositive',26),
                  ('LowerLowGram',28),('UpperNegative',4),('UpperPositive',24),('UpperLowGram',28)]))
(OUT/'receipt.json').write_text(json.dumps(results,indent=2)+'\n')
