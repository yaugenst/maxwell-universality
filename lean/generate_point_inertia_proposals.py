# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5", "scipy", "threadpoolctl"]
# ///
"""Read-only source reuse to propose low-space witnesses at the actual TRIM110.

All output is untrusted certificate input.  Native interval outputs are not
proofs; the Lean entry-containment and Schur checks must accept them separately.
"""
import os
os.environ['OPENBLAS_NUM_THREADS'] = '1'
os.environ['OMP_NUM_THREADS'] = '1'
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time
import numpy as np
from threadpoolctl import threadpool_limits

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT.parent / 'certificates/yee'
BASE = SOURCE / 'work/bulk/edge_isolation'
SNAPSHOT = SOURCE / 'work/bulk/edge_isolation'
OUT = ROOT / 'evidence/point_inertia_proposals'
OUT.mkdir(exist_ok=True)
sys.path.insert(0, str(BASE))
import point_bounds as pb
import primitive_fourier as pf
import yee_primitive as yp
from exact_geometry import diamond_cells_exact

spec = importlib.util.spec_from_file_location('interval_tools', SNAPSHOT / 'interval_tools.py')
v = importlib.util.module_from_spec(spec)
spec.loader.exec_module(v)
base = diamond_cells_exact(20, 12, 1)
den = []
for axis in range(3):
    a, b = [i for i in range(3) if i != axis]
    den.append(base + np.roll(base, 1, a) + np.roll(base, 1, b)
               + np.roll(np.roll(base, 1, a), 1, b))
base_den = np.ascontiguousarray(np.stack(den, axis=-1)[:, :10, :10].reshape(2000, 3), dtype=np.int32)
center = [0.5, 0.5, -0.5]
manifest = {'center': center, 'primitive_trim': [1, 1, 0], 'inputs': {}, 'records': []}
for name in ['point_bounds.py', 'primitive_fourier.py', 'yee_primitive.py', 'exact_geometry.py']:
    manifest['inputs'][name] = hashlib.sha256((BASE / name).read_bytes()).hexdigest()

for shift, negative, label in [(0.25, 2, 'lower'), (1.25, 4, 'upper')]:
    start = time.monotonic()
    cell = base + shift
    pf.diamond_cells_exact = lambda *args, **kwargs: cell.copy()
    yp.diamond_cells = lambda *args, **kwargs: cell.copy()
    with threadpool_limits(limits=1):
        proposed = pb.PointBound(center, eps_hi=14, nnegative=negative)
    raw = np.concatenate([proposed.Ff[0], proposed.Ff[1]], axis=2).astype(np.complex128)
    d = v.make_d(center)
    field = v.project(v.witness(raw), d)
    ef = v.curl(d, field, True)
    material_den = np.ascontiguousarray(base_den + int(4*shift))
    weighted = v.fft(v.material(v.fft(ef, True), material_den))
    af = v.add(v.curl(d, weighted), v.rat(field, 1, 64), True)
    compression = v.gram(field, af)
    p0 = v.I(1) - v.I(1/1024)
    negative_matrix = v.shifted_identity(np.ascontiguousarray(compression[:negative, :negative]), -p0, -1)
    positive_matrix = v.shifted_identity(np.ascontiguousarray(compression[negative:, negative:]), -p0, 1)
    low_gram = v.gram(np.ascontiguousarray(field[proposed.low]), power=20)
    path = OUT / f'{label}.npz'
    np.savez_compressed(path, raw=raw, low=proposed.low, d=d, lap=v.laplacian(d),
                        field=field, curl=ef, weighted=weighted, applied=af,
                        compression=compression, negative=negative_matrix,
                        positive=positive_matrix, low_gram=low_gram, material_den=material_den)
    record = {'label': label, 'negative_count': negative, 'cell_shift': shift,
              'denominator': v.S, 'low_count': len(proposed.low),
              'seconds': time.monotonic() - start,
              'output_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
              'floating_high_residual_norms': proposed.rzero,
              'floating_low_schur_eigenvalues': proposed.sev.tolist()}
    manifest['records'].append(record)
    (OUT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(json.dumps(record), flush=True)
