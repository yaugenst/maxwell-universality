"""Independent rejection exercises; does not replace the complete exact replay."""
from pathlib import Path
from fractions import Fraction
import argparse, copy, hashlib, json, os, sys, tempfile
os.environ['OPENBLAS_NUM_THREADS'] = '1'
os.environ['OMP_NUM_THREADS'] = '1'
import numpy as np

ROOT = Path(__file__).resolve().parents[2]

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--certificate-dir', type=Path,
                        default=ROOT / 'work/bulk/global_certificate')
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_suffix('.json'))
    args = parser.parse_args()
    base = args.certificate_dir.resolve()
    sys.path.insert(0, str(base))
    import verify_global as verifier
    import verify_point
    data = json.loads((base / 'cover_proposals.json').read_text())
    results = []
    def reject(name, function):
        try:
            function()
        except (AssertionError, ValueError, TypeError, OverflowError) as error:
            results.append({'case': name, 'status': 'CORRECTLY_REJECTED',
                            'exception': type(error).__name__, 'detail': str(error)})
        else:
            raise RuntimeError('Malformed input was accepted: ' + name)

    verifier.audit_geometry(data)
    for name, change in [
        ('missing_matrix_box', lambda x: x['accepted'].pop(0)),
        ('duplicate_matrix_box', lambda x: x['accepted'].append(copy.deepcopy(x['accepted'][0]))),
        ('pending_leaf', lambda x: x['pending'].append([[0.5, 0.5, 0.5], 0.5, 0])),
        ('wrong_uniform_shift', lambda x: x.update(uniform_shift='158/16384')),
        ('false_L_exclusion', lambda x: x['excluded_L_boxes'].append([[0.5, 0.5, 0.5], 0.5, 0])),
        ('false_Gamma_exclusion', lambda x: x['analytic_gamma_boxes'].append([[0.5, 0.5, 0.5], 0.5, 0]))]:
        bad = copy.deepcopy(data)
        change(bad)
        reject(name, lambda bad=bad: verifier.audit_geometry(bad))

    original = copy.deepcopy(data['accepted'][0])
    for name, change in [
        ('zero_negative_residual_bound', lambda r: r['constants']['rzero'].__setitem__(0, 0)),
        ('zero_positive_residual_bound', lambda r: r['constants']['rzero'].__setitem__(1, 0)),
        ('witness_path_traversal', lambda r: r.update(witness='../escaped.npz')),
        ('non_dyadic_box_halfwidth', lambda r: r.update(halfwidth=0.03))]:
        bad = copy.deepcopy(original)
        change(bad)
        reject(name, lambda bad=bad: verifier.validate_record(bad))

    with np.load(base / 'witnesses' / original['witness'], allow_pickle=False) as saved:
        clean = {key: saved[key].copy() for key in saved.files}
    test_parent = ROOT / 'work/bulk/falsification'
    test_parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='global-', dir=test_parent) as temp:
        temp = Path(temp)
        for name, change in [
            ('duplicate_low_index', lambda w: w['low'].__setitem__(1, w['low'][0])),
            ('low_index_out_of_range', lambda w: w['low'].__setitem__(0, 2000)),
            ('wrong_witness_center', lambda w: w['center'].__setitem__(0, w['center'][0] + 1 / 65536)),
            ('wrong_witness_halfwidth', lambda w: w.update(halfwidth=np.array(1 / 64))),
            ('nonfinite_witness_value', lambda w: w['F'].__setitem__((0, 0, 0), np.nan)),
            ('excessive_witness_value', lambda w: w['F'].__setitem__((0, 0, 0), 1000)),
            ('wrong_witness_shape', lambda w: w.update(F=w['F'][:, :, :1]))]:
            bad = {key: value.copy() for key, value in clean.items()}
            change(bad)
            path = temp / (name + '.npz')
            np.savez_compressed(path, **bad)
            reject(name, lambda path=path: verifier.validate_witness(original, path))

        # A well-formed zero witness gets past input validation but must fail
        # the actual exact low-basis Gram/LDL check, not a stored PASS lookup.
        (temp / 'witnesses').mkdir()
        zero = {key: value.copy() for key, value in clean.items()}
        zero['F'].fill(0)
        zero['Fpos'].fill(0)
        zero_path = temp / 'witnesses' / original['witness']
        np.savez_compressed(zero_path, **zero)
        verifier.validate_witness(original, zero_path)
        old_base = verify_point.BASE
        try:
            verify_point.BASE = temp
            reject('zero_witness_exact_matrix_rank', lambda: verify_point.verify_record(original))
        finally:
            verify_point.BASE = old_base

        # A false proposed norm bound must fail after recomputing the actual
        # nonzero center matrices with the intact accepted candidate arrays.
        bad = copy.deepcopy(original)
        bad['constants']['fn'][0] = 0
        reject('false_norm_bound_exact_matrix_check', lambda: verify_point.verify_record(bad))

    assert len(results) == 19
    result = {'status': 'ALL_19_FALSIFICATION_ATTEMPTS_CORRECTLY_REJECTED',
              'count': len(results), 'cases': results,
              'certificate_manifest_sha256': verifier.sha(base / 'frozen_manifest.json'),
              'source_sha256': verifier.source_hashes(),
              'scope': 'supplementary falsification exercises; complete all2056 replay required separately'}
    verifier.atomic_json(args.output, result)
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
