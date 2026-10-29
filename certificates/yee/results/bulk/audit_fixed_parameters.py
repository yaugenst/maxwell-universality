"""Exact norm-bound sign premises for H1, local isolation and global inputs.

This is an additional finite-input predicate.  It does not alter any frozen
kernel, witness or matrix receipt, and does not replace matrix verification.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse, hashlib, json

ROOT = Path(__file__).resolve().parents[2]
KEYS = ['fn', 'en', 'kn', 'rhow', 'crossder', 'wn', 'wp2', 'qfn',
        'qweighted', 'rmin', 'rhmin', 'rzero', 'cutoff']

def flatten(value):
    if isinstance(value, list):
        for entry in value:
            yield from flatten(entry)
    else:
        yield F(value)

def audit(path):
    raw = path.read_bytes()
    data = json.loads(raw)
    records = data['accepted'] if 'accepted' in data else [data]
    assert records
    count = 0
    for record in records:
        constants = record['constants']
        for key in KEYS:
            values = list(flatten(constants[key]))
            assert values and all(value >= 0 for value in values), (str(path), record['center'], key)
            count += len(values)
        assert len(constants['fn']) == 3 and all(F(x) > 0 for x in constants['fn'])
        assert F(constants['rmin']) > 0 and F(constants['rhmin']) > 0
        assert len(constants['rzero']) == 3 and all(F(x) > 0 for x in constants['rzero'][:2])
        assert F(constants['cutoff']) > 0
    return {'path': str(path), 'records': len(records), 'parameters': count,
            'sha256': hashlib.sha256(raw).hexdigest(),
            'status': 'ALL_NONNEGATIVE_WITH_REQUIRED_STRICT_POSITIVITY'}

def main():
    if not __debug__:
        raise RuntimeError('Do not disable assertions')
    parser = argparse.ArgumentParser()
    parser.add_argument('--bulk-dir', type=Path, default=ROOT / 'work/bulk')
    parser.add_argument('--proposal', action='append', type=Path,
                        help='Check only these files; repeat to audit several explicit proposals')
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('all_fixed_parameter_sign_audit.json'))
    args = parser.parse_args()
    if args.proposal:
        paths = args.proposal
    else:
        paths = [args.bulk_dir / 'clean_certificate/cover_screen_complete.json',
                 args.bulk_dir / 'edge_isolation/lower_1over256_proposal.json',
                 args.bulk_dir / 'edge_isolation/upper_5over256_proposal.json',
                 args.bulk_dir / 'edge_isolation/upper_3over128_proposal.json',
                 args.bulk_dir / 'edge_isolation/upper_7over256_proposal.json',
                 args.bulk_dir / 'edge_isolation/uniform_local_isolation_proposal.json',
                 args.bulk_dir / 'global_certificate/cover_proposals.json']
    records = [audit(path.resolve()) for path in paths]
    result = {'status': 'PASS_NONNEGATIVE_FIXED_PARAMETERS', 'files': records,
              'records': sum(x['records'] for x in records),
              'parameters': sum(x['parameters'] for x in records),
              'scope': 'finite input sign predicates only; no matrix acceptance inferred'}
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'], result['parameters'], 'parameters in', result['records'], 'records')

if __name__ == '__main__':
    main()
