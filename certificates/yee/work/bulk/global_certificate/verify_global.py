"""Fresh, fail-closed replay of the fixed 2056-box outside-L comparator.

Floating point arrays are witness proposals only.  Every matrix inequality
is recomputed by the rational interval kernel, with C++ assertions and UBSan.
Receipts are closed, fsynced, atomically renamed, and immediately reread.
Stored acceptance receipts never substitute for computation in this program.
"""
from __future__ import annotations
import os
os.environ['OPENBLAS_NUM_THREADS'] = '1'
os.environ['OMP_NUM_THREADS'] = '1'
from pathlib import Path
from fractions import Fraction as F
from concurrent.futures import ProcessPoolExecutor, as_completed
from itertools import product
from collections import Counter
import argparse, hashlib, json, platform, re, subprocess, sys, time, traceback, uuid
import numpy as np
import verify_cover as geometry

BASE = Path(__file__).resolve().parent
SOURCES = ['verify_global.py', 'verify_cover.py', 'interval_kernel.cpp',
           'interval_tools.py', 'verify_point.py', 'exact_geometry.py']
MARGINS = {'negative_margin', 'positive_diagonal_margin',
           'gradient_margin', 'positive_determinant_margin'}
EXPECTED = 2056

def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as stream:
        for block in iter(lambda: stream.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()

def record_sha(record):
    return hashlib.sha256(json.dumps(record, sort_keys=True,
                         separators=(',', ':'), allow_nan=False).encode()).hexdigest()

def atomic_bytes(path, data):
    path = Path(path)
    tmp = path.with_name(path.name + '.tmp-' + uuid.uuid4().hex)
    with tmp.open('xb') as stream:
        stream.write(data)
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(tmp, path)
    assert path.read_bytes() == data, ('atomic readback', str(path))
    digest = hashlib.sha256(data).hexdigest()
    assert sha(path) == digest, ('atomic hash readback', str(path))
    return digest

def atomic_json(path, value):
    return atomic_bytes(path, (json.dumps(value, sort_keys=True,
                                         allow_nan=False) + '\n').encode())

def source_hashes():
    return {name: sha(BASE / name) for name in SOURCES}

def validate_record(record):
    name = record['witness']
    assert isinstance(name, str) and re.fullmatch(r'[0-9_]+\.npz', name)
    assert Path(name).name == name
    assert len(record['center']) == 3
    assert all(np.isfinite(x) for x in record['center'])
    assert np.isfinite(record['halfwidth']) and record['halfwidth'] > 0
    geometry.key_from_box(record['center'], record['halfwidth'], record['depth'])
    # The proposed scalar tests are not evidence, but the intended record
    # schema must be unambiguous before a fresh matrix check is attempted.
    assert record['scalar_screen_pass'] is True
    assert isinstance(record['constants'], dict)
    assert len(record['constants']['rzero']) == 3
    assert all(F(x) > 0 for x in record['constants']['rzero'][:2])
    record_sha(record)  # rejects non-finite JSON constants

def validate_witness(record, path):
    with np.load(path, allow_pickle=False) as witness:
        assert set(witness.files) == {'F', 'Fpos', 'low', 'center', 'halfwidth'}
        low = witness['low']
        assert low.ndim == 1 and np.issubdtype(low.dtype, np.integer)
        assert 1 <= len(low) <= 2000
        assert len(set(low.tolist())) == len(low)
        assert np.all(low >= 0) and np.all(low < 2000)
        assert witness['F'].shape == (2000, 3, 2)
        assert witness['Fpos'].shape == (2000, 3, 2 * len(low) - 2)
        for name in ('F', 'Fpos'):
            value = witness[name]
            assert np.issubdtype(value.dtype, np.complexfloating)
            assert np.isfinite(value).all()
            assert value.size == 0 or float(abs(value).max()) < 1000
        center = witness['center']
        half = witness['halfwidth']
        assert center.shape == (3,) and np.isfinite(center).all()
        assert half.shape == () and np.isfinite(half).all()
        assert all(F(float(a)) == F(b) for a, b in zip(center, record['center']))
        assert F(float(half)) == F(record['halfwidth'])
        return {'low_dimension': len(low), 'F_shape': list(witness['F'].shape),
                'Fpos_shape': list(witness['Fpos'].shape),
                'F_dtype': str(witness['F'].dtype),
                'Fpos_dtype': str(witness['Fpos'].dtype)}

def audit_geometry(data):
    assert F(data['uniform_shift']) == geometry.SHIFT
    assert F(data['frequency_halfwidth']) == geometry.SIGMA
    assert F(data['L_ball_radius']) == F(1, 20)
    assert F(data['gamma_cube_radius']) == F(1, 8)
    assert data['pending'] == []
    leaves = {}
    names = set()
    for record in data['accepted']:
        validate_record(record)
        key = geometry.key_from_box(record['center'], record['halfwidth'], record['depth'])
        assert key not in leaves and record['witness'] not in names
        leaves[key] = 'matrix'
        names.add(record['witness'])
    assert len(names) == EXPECTED
    for field, kind in [('analytic_gamma_boxes', 'gamma'), ('excluded_L_boxes', 'L_ball')]:
        for center, half, depth in data[field]:
            key = geometry.key_from_box(center, half, depth)
            assert key not in leaves
            assert geometry.in_gamma(key) if kind == 'gamma' else geometry.in_l_ball(key)
            leaves[key] = kind
    ancestors = set()
    for depth, idx in leaves:
        for a in range(depth):
            key = (a, tuple(i >> (depth - a) for i in idx))
            assert key not in leaves, ('overlapping leaves', key)
            ancestors.add(key)
    counts = Counter()
    used = set()
    def visit(key):
        if not geometry.feasible(key):
            counts['empty_polytope_leaves'] += 1
            return
        if key in leaves:
            counts[leaves[key]] += 1
            used.add(key)
            return
        assert key in ancestors, ('uncovered feasible box', key)
        counts['internal_nodes'] += 1
        depth, idx = key
        for bits in product([0, 1], repeat=3):
            visit((depth + 1, tuple(2 * idx[j] + bits[j] for j in range(3))))
    visit((0, (0, 0, 0)))
    assert used == set(leaves), ('unused listed leaves', set(leaves) - used)
    assert counts['matrix'] == EXPECTED
    return {'status': 'EXACT_COVER_AND_ANALYTIC_COMPARATOR_PASS',
            'counts': dict(counts), 'pending': 0, 'uncovered': 0,
            'analytic_comparator': geometry.analytic_gamma(),
            'feasibility_method': 'all nonsingular triples of nine rational polytope halfspaces'}

def verified_constants_match(proposal, actual):
    assert set(proposal) == set(actual)
    for key in proposal:
        if key != 'rzero':
            assert proposal[key] == actual[key], ('changed constant', key)
            continue
        assert len(proposal[key]) == len(actual[key]) == 3
        for initial, final in zip(proposal[key], actual[key]):
            initial, final = F(initial), F(final)
            assert 0 <= initial <= final <= F(1, 128)
            if initial == 0:
                assert final == 0
            else:
                quotient = final / initial
                assert quotient.denominator == 1
                n = quotient.numerator
                assert n > 0 and n & (n - 1) == 0

def verify_one(record, out, snapshot, witness_entry):
    path = BASE / 'witnesses' / record['witness']
    before = sha(path)
    assert before == witness_entry['sha256']
    assert path.stat().st_size == witness_entry['bytes']
    metadata = validate_witness(record, path)
    assert metadata == witness_entry['metadata']
    out = Path(out)
    atomic_json(out / 'started_points' / (record['witness'] + '.json'),
                {'witness': record['witness'], 'record_sha256': record_sha(record),
                 'witness_before_sha256': before, 'snapshot': snapshot})
    try:
        from verify_point import verify_record
        accepted = verify_record(record)
        assert accepted['status'] == 'INTERVAL_PASS'
        assert accepted['frequency_halfwidth'] == '1/16777216'
        assert accepted['center'] == record['center']
        assert accepted['halfwidth'] == record['halfwidth']
        assert accepted['witness'] == record['witness']
        assert set(accepted['margins']) == MARGINS
        assert all(F(b[1]) >= F(b[0]) > 0 for b in accepted['margins'].values())
        verified_constants_match(record['constants'], accepted['verified_constants'])
        after = sha(path)
        assert after == before
        accepted.update(snapshot)
        accepted.update({'record_sha256': record_sha(record),
                         'witness_sha256': before,
                         'witness_before_sha256': before,
                         'witness_after_sha256': after,
                         'witness_metadata': metadata,
                         'electric_uniform_shift': '157/16384',
                         'cell_shift': '157/256', 'kernel_fractional_bits': 48,
                         'negative_count': 2, 'depth': record['depth'],
                         'fresh_matrix_check': True})
        receipt = out / 'accepted_points' / (record['witness'] + '.json')
        digest = atomic_json(receipt, accepted)
        assert json.loads(receipt.read_text()) == accepted
        return record['witness'], digest
    except BaseException as error:
        atomic_json(out / 'rejected_points' / (record['witness'] + '.json'),
                    {'status': 'REJECTED', 'record_sha256': record_sha(record),
                     'witness': record['witness'], 'witness_before_sha256': before,
                     'error': repr(error), 'traceback': traceback.format_exc(),
                     'snapshot': snapshot})
        raise

def compile_kernel(out):
    command = ['g++', '-O2', '-std=c++17', '-shared', '-fPIC',
               '-fsanitize=undefined', '-fno-sanitize-recover=all',
               str(BASE / 'interval_kernel.cpp'), '-o', str(BASE / 'interval_kernel.so')]
    built = subprocess.run(command, text=True, capture_output=True)
    atomic_bytes(out / 'compiler.log', (built.stdout + built.stderr).encode())
    assert built.returncode == 0, ('compiler failed', built.returncode)
    atomic_json(out / 'runtime.json',
                {'command': command, 'compiler': subprocess.check_output(['g++', '--version'], text=True),
                 'python': sys.version, 'numpy': np.__version__,
                 'platform': platform.platform(), 'assertions_enabled': __debug__,
                 'sanitizer': 'undefined, no recover; all matrix operations',
                 'shared_library_sha256': sha(BASE / 'interval_kernel.so')})

def main():
    if not __debug__:
        raise RuntimeError('Do not disable assertions with -O or PYTHONOPTIMIZE')
    parser = argparse.ArgumentParser()
    parser.add_argument('--workers', type=int, default=6)
    parser.add_argument('--output', type=Path, default=BASE / 'verification_final')
    args = parser.parse_args()
    assert args.workers >= 1
    out = args.output.resolve()
    assert not out.exists() or not any(out.iterdir()), 'Fresh replay requires an empty output directory'
    for name in ['accepted_points', 'rejected_points', 'started_points']:
        (out / name).mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    manifest_path = BASE / 'frozen_manifest.json'
    manifest_sha = sha(manifest_path)
    manifest = json.loads(manifest_path.read_text())
    assert manifest['format'] == 'outside-L-comparator-frozen-v1'
    assert manifest['matrix_boxes'] == EXPECTED
    sources = source_hashes()
    assert manifest['source_sha256'] == sources
    proposal_path = BASE / 'cover_proposals.json'
    proposal_sha = sha(proposal_path)
    assert proposal_sha == manifest['proposal_sha256']
    data = json.loads(proposal_path.read_text())
    cover = audit_geometry(data)
    records = data['accepted']
    assert set(manifest['witnesses']) == {r['witness'] for r in records}
    snapshot = {'source_sha256': sources, 'proposal_sha256': proposal_sha,
                'frozen_manifest_sha256': manifest_sha}
    atomic_json(out / 'geometry_acceptance.json', dict(cover, **snapshot))
    compile_kernel(out)
    atomic_json(out / 'run_started.json',
                {'status': 'FRESH_REPLAY_STARTED', 'matrix_boxes': EXPECTED,
                 'workers': args.workers, **snapshot})
    print('GLOBAL_FRESH_REPLAY_START', EXPECTED, 'workers', args.workers, flush=True)
    receipts = {}
    with ProcessPoolExecutor(max_workers=args.workers) as pool:
        futures = [pool.submit(verify_one, record, str(out), snapshot,
                               manifest['witnesses'][record['witness']]) for record in records]
        for i, future in enumerate(as_completed(futures), 1):
            name, digest = future.result()
            assert name not in receipts
            receipts[name] = digest
            if i % 25 == 0 or i == EXPECTED:
                print('GLOBAL_FRESH_MATRIX_CHECKS', i, '/', EXPECTED,
                      'seconds', time.monotonic() - started, flush=True)
    assert len(receipts) == EXPECTED
    assert len(list((out / 'accepted_points').glob('*.json'))) == EXPECTED
    assert not list((out / 'rejected_points').iterdir())
    minima = {name: None for name in MARGINS}
    accepted_records = []
    for record in records:
        name = record['witness']
        receipt = out / 'accepted_points' / (name + '.json')
        assert sha(receipt) == receipts[name]
        accepted = json.loads(receipt.read_text())
        assert accepted['fresh_matrix_check'] is True
        assert accepted['record_sha256'] == record_sha(record)
        assert accepted['source_sha256'] == sources
        assert accepted['proposal_sha256'] == proposal_sha
        assert accepted['frozen_manifest_sha256'] == manifest_sha
        assert accepted['witness_sha256'] == accepted['witness_before_sha256'] == accepted['witness_after_sha256']
        assert accepted['witness_sha256'] == sha(BASE / 'witnesses' / name) == manifest['witnesses'][name]['sha256']
        verified_constants_match(record['constants'], accepted['verified_constants'])
        for key, bounds in accepted['margins'].items():
            lower = F(bounds[0])
            assert F(bounds[1]) >= lower > 0
            minima[key] = lower if minima[key] is None else min(minima[key], lower)
        accepted_records.append(accepted)
    assert source_hashes() == sources
    assert sha(proposal_path) == proposal_sha and sha(manifest_path) == manifest_sha
    assert audit_geometry(json.loads(proposal_path.read_text())) == cover
    atomic_json(out / 'point_receipts.json', {'count': EXPECTED, 'points': receipts, **snapshot})
    aggregate = ''.join(json.dumps(r, sort_keys=True, allow_nan=False) + '\n' for r in accepted_records).encode()
    aggregate_sha = atomic_bytes(out / 'all_verified_boxes.jsonl', aggregate)
    assert [json.loads(line) for line in (out / 'all_verified_boxes.jsonl').read_text().splitlines()] == accepted_records
    summary = {'status': 'ALL_2056_FULL_MATRIX_CERTIFICATES_REPRODUCED',
               'outside_L_comparator': 'CERTIFIED_WITH_EXACT_COVER',
               'global_spectral_edge_certified': False,
               'scope': 'Outside radius-1/20 L balls only; unique global Morse edge additionally requires independent local certificates and analytic composition',
               'matrix_checks': EXPECTED, 'geometry': cover,
               'electric_uniform_shift': '157/16384', 'cell_shift': '157/256',
               'squared_frequency': '1/64', 'frequency_halfwidth': '1/16777216',
               'kernel_fractional_bits': 48, 'negative_count': 2,
               'minimum_margins': {k: str(v) for k, v in minima.items()},
               'all_before_after_witness_hashes_equal': True,
               'all_current_witness_hashes_equal': True,
               'all_source_and_proposal_hashes_unchanged': True,
               'all_receipts_atomic_readback_verified': True,
               'aggregate_sha256': aggregate_sha,
               'undefined_behavior_sanitizer': 'all 2056 matrix checks',
               'elapsed_seconds': time.monotonic() - started,
               'formal_verification': False, **snapshot}
    atomic_json(out / 'reproduction_summary.json', summary)
    print('GLOBAL_ALL_2056_FRESH_MATRIX_CHECKS_AND_EXACT_COVER_PASS',
          time.monotonic() - started, flush=True)

if __name__ == '__main__':
    main()
