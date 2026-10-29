# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Strictly kernel-check generated leaves in the manifest's dependency order."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parent


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('manifest', type=Path)
    parser.add_argument('receipt', type=Path)
    parser.add_argument('--checker', type=Path, action='append', default=[])
    args = parser.parse_args()
    manifest = json.loads(args.manifest.read_text())
    inputs = manifest.get('inputs', {})
    if 'input' in manifest:
        inputs[manifest['input']] = manifest['input_sha256']
    inputs.update({str(p): digest(p) for p in args.checker})
    assert inputs == {p: digest(p) for p in inputs}
    prior = json.loads(args.receipt.read_text()) if args.receipt.exists() else {}
    old = prior.get('checks', {}) if prior.get('inputs') == inputs else {}
    result = {'status': 'running', 'inputs': inputs, 'checks': {}}
    for name, expected in manifest['outputs'].items():
        src = ROOT/name
        assert digest(src) == expected, f'changed proposal: {name}'
        out = ROOT/'.lake/build/lib/lean'/Path(name).with_suffix('.olean')
        out.parent.mkdir(parents=True, exist_ok=True)
        entry = old.get(name)
        if entry and entry['exit_code'] == 0 and entry['source_sha256'] == expected and out.exists() and entry['olean_sha256'] == digest(out):
            result['checks'][name] = entry
            continue
        start = time.monotonic()
        run = subprocess.run(['lake', 'env', 'lean', '-j1', '-M3000',
            '-DwarningAsError=true', '-o', str(out), str(src)], cwd=ROOT,
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        entry = {'exit_code': run.returncode, 'source_sha256': expected,
                 'seconds': round(time.monotonic()-start, 3), 'output': run.stdout}
        result['checks'][name] = entry
        if run.returncode:
            result['status'] = 'failed'
            args.receipt.write_text(json.dumps(result, indent=2)+'\n')
            raise SystemExit(f'{name}: {run.stdout}')
        assert digest(src) == expected
        entry['olean_sha256'] = digest(out)
        args.receipt.write_text(json.dumps(result, indent=2)+'\n')
        print(f'{name}: kernel PASS ({entry["seconds"]}s)', flush=True)
    assert inputs == {p: digest(p) for p in inputs}
    result['status'] = 'all leaves kernel checked'
    args.receipt.write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    main()
