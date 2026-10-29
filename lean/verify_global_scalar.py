# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Run strict, single-threaded kernel checks for the generated scalar leaves."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parent
LAKE = Path('lake')
MANIFEST = ROOT / 'evidence/global_scalar_proposals_0000_2056.json'
RECEIPT = ROOT / 'evidence/global_scalar_kernel_checks.json'


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    manifest = json.loads(MANIFEST.read_text())
    inputs = {name: digest(Path(name)) for name in manifest['inputs']}
    assert inputs == manifest['inputs'], 'input changed after proposal generation'
    core = ROOT / 'Maxwell/Certificate/GlobalScalarCore.lean'
    checker = ROOT / 'Maxwell/Certificate/ScalarExpression.lean'
    checker_hashes = {str(p.relative_to(ROOT)): digest(p) for p in (core, checker)}
    previous = json.loads(RECEIPT.read_text()) if RECEIPT.exists() else {}
    old = previous.get('checks', {}) if previous.get('checker_hashes') == checker_hashes else {}
    result = {'status': 'running', 'inputs': inputs, 'checker_hashes': checker_hashes,
              'checks': {}, 'command_options': ['-j1', '-M3000', '-DwarningAsError=true']}
    for name, expected in sorted(manifest['outputs'].items()):
        src = ROOT / name
        assert digest(src) == expected, f'changed proposal: {name}'
        out = ROOT / '.lake/build/lib/lean' / Path(name).with_suffix('.olean')
        entry = old.get(name)
        if entry and entry['source_sha256'] == expected and out.exists() and entry['olean_sha256'] == digest(out):
            result['checks'][name] = entry
            continue
        started = time.monotonic()
        run = subprocess.run([str(LAKE), 'env', 'lean', '-j1', '-M3000',
            '-DwarningAsError=true', '-o', str(out), str(src)], cwd=ROOT,
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        entry = {'source_sha256': expected, 'exit_code': run.returncode,
                 'seconds': round(time.monotonic()-started, 3), 'output': run.stdout}
        result['checks'][name] = entry
        if run.returncode:
            result['status'] = 'failed'
            RECEIPT.write_text(json.dumps(result, indent=2)+'\n')
            raise SystemExit(f'{name}: {run.stdout}')
        assert digest(src) == expected, f'proposal changed during check: {name}'
        entry['olean_sha256'] = digest(out)
        RECEIPT.write_text(json.dumps(result, indent=2)+'\n')
        print(f'{name}: kernel PASS ({entry["seconds"]}s)', flush=True)
    assert inputs == {name: digest(Path(name)) for name in inputs}
    assert checker_hashes == {name: digest(ROOT/name) for name in checker_hashes}
    result['status'] = 'all leaves kernel checked'
    result['records'] = len(manifest['records'])
    RECEIPT.write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    main()
