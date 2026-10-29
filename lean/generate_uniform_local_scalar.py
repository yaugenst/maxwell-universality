# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Propose the single uniform local-count scalar certificate.

The saved receipt supplies rational proposals only. Lean checks each
arithmetic step and every strict inequality independently.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

from generate_global_scalar import SOURCE, proposal, expressions, record_text

ROOT = Path(__file__).resolve().parent
source = SOURCE / 'work/bulk/edge_isolation/uniform_local_isolation_acceptance.json'
record = json.loads(source.read_text())
assert record['center'] == [.5, .5, .5]
assert record['negative_count'] == 4
assert record['frequency_halfwidth'] == '1/4096'
assert Q(record['halfwidth']) >= Q(1, 20)
p = proposal(record)
b, roots = expressions(p, sigma=Q(1, 4096), rho=Q(14))
text = '''import Maxwell.Certificate.UniformLocalScalarCore

namespace Maxwell.Certificate.UniformLocalScalar.Frozen
open ScalarExpression
set_option maxRecDepth 100000
set_option maxHeartbeats 0

''' + record_text(0, p, b, roots, checked_record=False) + '''
end Maxwell.Certificate.UniformLocalScalar.Frozen
'''
output = ROOT / 'Maxwell/Certificate/UniformLocalScalar/Data.lean'
output.parent.mkdir(exist_ok=True)
output.write_text(text)
manifest = {
    'status': 'untrusted proposal; Lean kernel acceptance required',
    'inputs': {str(source): hashlib.sha256(source.read_bytes()).hexdigest()},
    'outputs': {str(output.relative_to(ROOT)): hashlib.sha256(text.encode()).hexdigest()},
    'root_lower_bounds': {key: str(b.nodes[index].lo) for key, index in roots.items()},
    'nodes': len(b.nodes),
}
(ROOT / 'evidence/uniform_local_scalar_proposals.json').write_text(json.dumps(manifest, indent=2)+'\n')
print(json.dumps({'nodes': len(b.nodes), 'lower_bounds': manifest['root_lower_bounds']}))
