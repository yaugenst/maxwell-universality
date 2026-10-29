# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Propose exact negative-block scalar checks for the 604 original boxes."""
from fractions import Fraction as Q
from hashlib import sha256
import json
from pathlib import Path

from generate_global_scalar import Builder, PI_UPPER, SQRT3_UPPER, ceil_grid, qlean, vector

ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent / 'certificates/yee/work/bulk/clean_certificate'
CANONICAL = BASE/'cover_screen_complete.json'
RECEIPTS = BASE/'verified_boxes_strengthened.jsonl'
OUT = ROOT/'Maxwell/Certificate/NegativeScalar'


def main():
    records = json.loads(CANONICAL.read_text())['accepted']
    receipts = {r['witness']: r for r in map(json.loads, RECEIPTS.read_text().splitlines())}
    assert len(records) == len(receipts) == 604
    OUT.mkdir(exist_ok=True)
    batches = {}
    manifest = []
    minimum = None
    for i, original in enumerate(records):
        rec = receipts[original['witness']]
        assert original['center'] == rec['center'] and original['halfwidth'] == rec['halfwidth']
        c = rec['verified_constants']
        half = Q(rec['halfwidth'])
        p = dict(half=half, s=ceil_grid(PI_UPPER/10*SQRT3_UPPER*half),
                 r=Q(c['rmin']), fn=Q(c['fn'][0]), en=Q(c['en'][0]),
                 kn=[Q(x) for x in c['kn'][0]], wn=Q(c['wn']))
        b = Builder()
        r, add, sub, mul, div, sq = b.rat, b.add, b.sub, b.mul, b.div, b.sq
        dot = add(add(mul(r(p['half']), r(p['kn'][0])), mul(r(p['half']), r(p['kn'][1]))),
                  mul(r(p['half']), r(p['kn'][2])))
        loss = add(add(add(dot, mul(sq(r(p['s'])), add(mul(r(p['fn']), r(p['en'])), sq(r(p['fn']))))),
                       div(mul(mul(mul(r(2), r(Q(1,64))), sq(r(p['s']))), r(p['wn'])),
                           sq(sub(r(1), div(r(p['s']), r(p['r'])))))),
                   mul(r(Q(1,4096)), sq(r(p['fn']))))
        roots = dict(margin=sub(r(Q(1023,1024)), loss), small=sub(r(p['r']), r(p['s'])))
        for name, index in roots.items():
            assert b.nodes[index].lo > 0, (i, rec['witness'], name)
        margin = b.nodes[roots['margin']].lo
        minimum = margin if minimum is None else min(minimum, margin)
        lines = [f'def proposal{i:04d} : Proposal where']
        lines += [f'  {name} := {vector(value) if name == "kn" else qlean(value)}' for name,value in p.items()]
        lines.append('')
        prefix = f'n{i:04d}_'
        for j, node in enumerate(b.nodes):
            if node.op == 'rat':
                rhs = f'.rat {qlean(node.args[0])}'
            else:
                args = ' '.join(prefix+str(k) for k in node.args)
                rhs = f'.{node.op} {args} (enclosure {qlean(node.lo)} {qlean(node.hi)})'
            lines.append(f'private def {prefix}{j} : ScalarExpression.Certificate := {rhs}')
        lines += ['', f'def evidence{i:04d} : Evidence where']
        lines += [f'  {name} := {prefix}{j}' for name,j in roots.items()]
        lines += ['', f'theorem checked{i:04d} : accepts proposal{i:04d} evidence{i:04d} = true := by decide +kernel',
                  f'def record{i:04d} : VerifiedProposal := ⟨proposal{i:04d}, evidence{i:04d}, checked{i:04d}⟩', '']
        text = '\n'.join(lines)
        batches.setdefault(i//8, []).append(text)
        manifest.append(dict(index=i, witness=rec['witness'], nodes=len(b.nodes),
                             record_sha256=sha256(text.encode()).hexdigest()))
    outputs = {}
    for batch, parts in batches.items():
        path = OUT/f'Batch{batch:03d}.lean'
        text = ('import Maxwell.Certificate.NegativeScalarCore\n\n'
                'namespace Maxwell.Certificate.NegativeScalar.Frozen\n\n'
                'open ScalarExpression\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n'+
                '\n'.join(parts)+'\nend Maxwell.Certificate.NegativeScalar.Frozen\n')
        path.write_text(text)
        outputs[str(path.relative_to(ROOT))] = sha256(text.encode()).hexdigest()
    m = dict(outputs=outputs, records=manifest, minimum_lower_margin=str(minimum),
             inputs={str(p): sha256(p.read_bytes()).hexdigest() for p in [CANONICAL, RECEIPTS]},
             status='untrusted proposals; Lean acceptance required')
    (ROOT/'evidence/negative_scalar_proposals.json').write_text(json.dumps(m, indent=2)+'\n')
    print(json.dumps(dict(records=len(records), nodes=sum(x['nodes'] for x in manifest), minimum_lower_margin=str(minimum))))


if __name__ == '__main__':
    main()
