# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Kernel-check the six actual derivative actions with bounded concurrency."""
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'evidence/bpoint_action_compile'
OUT.mkdir(exist_ok=True)
checks = []


def compile_module(mod):
    src = ROOT / f'Maxwell/Certificate/BPointWitness/{mod}.lean'
    obj = ROOT / f'.lake/build/lib/lean/Maxwell/Certificate/BPointWitness/{mod}.olean'
    obj.parent.mkdir(parents=True, exist_ok=True)
    command = ['nice', '-n10', '/usr/bin/time', '-v', '-o', str(OUT / f'{mod}.time'),
               str(Path.home() / '.elan/bin/lake'), 'env', 'lean', '-j1', '-M4000',
               '-DwarningAsError=true', '-o', str(obj), str(src)]
    start = time.monotonic()
    with (OUT / f'{mod}.log').open('w') as log:
        result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    row = {'module': mod, 'exit_code': result.returncode,
           'seconds': time.monotonic() - start,
           'source_sha256': hashlib.sha256(src.read_bytes()).hexdigest()}
    if result.returncode == 0:
        row['object_sha256'] = hashlib.sha256(obj.read_bytes()).hexdigest()
    return row


def record(row):
    checks.append(row)
    (OUT / 'receipt.json').write_text(json.dumps(checks, indent=2) + '\n')
    if row['exit_code']:
        raise RuntimeError(f"{row['module']} failed; inspect its log")


for j in range(6):
    record(compile_module(f'Rhs{j}'))
for j in range(6):
    modules = [f'Action{j}D{d}X{x:02d}' for d in range(3) for x in range(20)]
    with ThreadPoolExecutor(max_workers=2) as pool:
        for row in pool.map(compile_module, modules):
            record(row)
    record(compile_module(f'Action{j}'))
    print(f'Column {j}: all 6000 derivative action entries verified.', flush=True)
