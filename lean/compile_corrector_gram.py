# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Check only owned corrector Gram modules without rebuilding shared imports."""
import hashlib
import json
from pathlib import Path
import subprocess
import time
ROOT=Path(__file__).resolve().parent
OUT=ROOT/'evidence/corrector_gram_compile';OUT.mkdir(exist_ok=True)
modules=[f'Dot{i}{j}' for i in range(6) for j in range(i,6)]+['Gram','GramBound']
checks=[]
for mod in modules:
    src=ROOT/f'Maxwell/Certificate/CorrectorWitness/{mod}.lean'
    obj=ROOT/f'.lake/build/lib/lean/Maxwell/Certificate/CorrectorWitness/{mod}.olean'
    cmd=['nice','-n10','/usr/bin/time','-v','-o',str(OUT/f'{mod}.time'),str(Path.home()/'.elan/bin/lake'),'env','lean','-j1','-M4000','-DwarningAsError=true','-o',str(obj),str(src)]
    start=time.monotonic()
    with (OUT/f'{mod}.log').open('w') as log:r=subprocess.run(cmd,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
    checks.append({'module':mod,'exit_code':r.returncode,'seconds':time.monotonic()-start,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest()})
    (OUT/'receipt.json').write_text(json.dumps(checks,indent=2)+'\n')
    if r.returncode:raise SystemExit(f'{mod} failed; see {OUT/mod}.log')
print('All21 exactdotproducts andactual6x6Gram bound kernelchecked.')
