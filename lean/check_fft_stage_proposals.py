#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Run generated FFT certificate modules with one Lean kernel worker.

This runner records successful compiler exits; the proof objects in .olean
files are the acceptance evidence. It never uses native_decide or a native
acceptance oracle. Resume keys include each source and its transitive local
imports, so changing a table invalidates all dependent saved checks.
"""
from __future__ import annotations
import argparse
from functools import lru_cache
from hashlib import sha256
import json
from pathlib import Path
import re
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parent
EVIDENCE = ROOT / 'evidence/fft_stage_proposals'
MODULE_ROOT = 'Maxwell.Certificate.FFTWitness.'


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--limit', type=int)
    parser.add_argument('--module', help='Check only this FFTWitness module; dependencies must already exist')
    parser.add_argument('--resume', action='store_true')
    parser.add_argument('--module-list', type=Path, help='An ordered JSON list of fully qualified modules')
    parser.add_argument('--offset', type=int, default=0)
    parser.add_argument('--status-path', type=Path, help='Separate receipt ledger for a disjoint worker')
    parser.add_argument('--log-dir', type=Path, help='Separate log directory for a disjoint worker')
    args = parser.parse_args()
    manifest = json.loads((EVIDENCE/'manifest.json').read_text())
    names = [args.module] if args.module else (
        json.loads(args.module_list.read_text()) if args.module_list else manifest['modules'])
    names = names[args.offset:]
    if args.limit is not None:
        names = names[:args.limit]
    logs = args.log_dir or EVIDENCE/'logs'
    logs.mkdir(parents=True, exist_ok=True)
    status_path = args.status_path or EVIDENCE/'kernel_checks.json'
    status_path.parent.mkdir(parents=True, exist_ok=True)
    status = json.loads(status_path.read_text()) if status_path.exists() else {'modules': {}}

    stop_requested = False

    def request_stop(signum, frame):
        nonlocal stop_requested
        stop_requested = True
        print('Graceful stop requested; completing the current Lean module.', flush=True)

    signal.signal(signal.SIGUSR1, request_stop)

    @lru_cache(None)
    def fingerprint(module):
        source = ROOT / (module.replace('.', '/')+'.lean')
        data = source.read_bytes()
        imports = re.findall(r'^import\s+(Maxwell\.[\w.]+)', data.decode(), re.MULTILINE)
        return sha256(data+b''.join(fingerprint(m).encode() for m in imports)).hexdigest()

    for index, name in enumerate(names):
        if stop_requested:
            print('Stopped at a completed module boundary.', flush=True)
            return
        module = name if name.startswith('Maxwell.') else MODULE_ROOT+name
        name = module.removeprefix(MODULE_ROOT) if module.startswith(MODULE_ROOT) else module
        source = ROOT/(module.replace('.', '/')+'.lean')
        output = ROOT/'.lake/build/lib/lean'/(module.replace('.', '/')+'.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        key = fingerprint(module)
        previous = status['modules'].get(name, {})
        if args.resume and previous.get('fingerprint') == key and previous.get('exit_code') == 0 and output.exists():
            print(f'{index+1}/{len(names)} {name}: previously kernel-checked', flush=True)
            continue
        command = ['lake', 'env', 'lean', '-j1', '-M4500',
                   '-DwarningAsError=true', '-o', str(output), str(source)]
        start = time.monotonic()
        result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
        elapsed = time.monotonic()-start
        (logs/f'{name}.log').write_text(result.stdout+result.stderr)
        # A bounded prototype may run while a parent queue is paused. Retain
        # those separately completed records when the parent resumes.
        if status_path.exists():
            status['modules'].update(json.loads(status_path.read_text())['modules'])
        status['modules'][name] = {'fingerprint': key, 'exit_code': result.returncode,
                                  'seconds': elapsed, 'command': command,
                                  'source_sha256': sha256(source.read_bytes()).hexdigest()}
        temporary_status = status_path.with_suffix('.json.tmp')
        temporary_status.write_text(json.dumps(status, indent=2)+'\n')
        temporary_status.replace(status_path)
        print(f'{index+1}/{len(names)} {name}: exit={result.returncode}, {elapsed:.2f}s', flush=True)
        if result.returncode:
            print(result.stdout+result.stderr, flush=True)
            raise SystemExit(result.returncode)


if __name__ == '__main__':
    main()
