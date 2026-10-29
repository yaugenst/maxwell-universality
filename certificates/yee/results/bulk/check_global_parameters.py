"""Exact sign audit for every fixed norm/radius parameter in the global cover."""
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

def main():
    if not __debug__:
        raise RuntimeError('Do not disable assertions')
    parser = argparse.ArgumentParser()
    parser.add_argument('--proposal', type=Path,
                        default=ROOT / 'work/bulk/global_certificate/cover_proposals.json')
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('global_parameter_sign_audit.json'))
    args = parser.parse_args()
    data = json.loads(args.proposal.read_text())
    minimum, maximum, count = {}, {}, 0
    for record in data['accepted']:
        for key in KEYS:
            values = list(flatten(record['constants'][key]))
            assert values and all(x >= 0 for x in values), (record['witness'], key)
            minimum[key] = min(minimum.get(key, values[0]), *values)
            maximum[key] = max(maximum.get(key, values[0]), *values)
            count += len(values)
        assert all(F(x) > 0 for x in record['constants']['fn'])
        assert F(record['constants']['rmin']) > 0 and F(record['constants']['rhmin']) > 0
    assert len(data['accepted']) == 2056 and count == 84296
    result = {'status': 'ALL_FIXED_NORM_AND_RADIUS_PARAMETERS_NONNEGATIVE',
              'records': len(data['accepted']), 'scalar_parameters_checked': count,
              'minimum': {k: str(v) for k, v in minimum.items()},
              'maximum': {k: str(v) for k, v in maximum.items()},
              'proposal_sha256': hashlib.sha256(args.proposal.read_bytes()).hexdigest()}
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(result['status'], count, 'parameters across', len(data['accepted']), 'records')

if __name__ == '__main__':
    main()
