# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Propose the exact 604-box cover used for the original negative trials."""
from collections import Counter
from fractions import Fraction as Q
from hashlib import sha256
from itertools import product
import json
from pathlib import Path

from generate_cover import box, empty_wedge, endpoints, key, lookup, rat

ROOT = Path(__file__).resolve().parent
PROPOSAL = ROOT.parent / 'certificates/yee/work/bulk/clean_certificate/cover_screen_complete.json'
OUT = ROOT / 'Maxwell/Certificate/NegativeCover'


def main():
    raw = PROPOSAL.read_bytes()
    records = json.loads(raw)['accepted']
    assert len(records) == 604
    keys = [key(r['center'], r['halfwidth'], r['depth']) for r in records]
    tags = {k: i+2 for i, k in enumerate(keys)}
    assert len(tags) == 604
    OUT.mkdir(exist_ok=True)
    header = ('-- Generated exact cover proposal; every leaf is kernel checked.\n'
              f'-- Canonical input SHA-256: {sha256(raw).hexdigest()}\n')
    outputs = {}

    def save(name, text):
        path = OUT / (name+'.lean')
        path.write_text(header+text)
        outputs[str(path.relative_to(ROOT))] = sha256(path.read_bytes()).hexdigest()

    save('Data', 'import Maxwell.Certificate.NegativeCoverSemantics\n\n'
         'namespace Maxwell.Certificate.FrozenNegativeCover\n\n'+
         '\n'.join(f'def matrixBox{i:04d} : Box := {box(k)}' for i, k in enumerate(keys))+
         '\n\nprivate def matrixBoxLookup (i : Nat) : Box :=\n  '+lookup(0, 604)+
         '\n\ndef matrixBoxes (i : Fin 604) : Box := matrixBoxLookup i.val\n\n'
         'end Maxwell.Certificate.FrozenNegativeCover\n')
    seen = set()
    counts = Counter()

    def tree(k):
        if empty_wedge(k):
            counts['empty'] += 1
            return '(.leaf 0)'
        if max(endpoints(k)[1]) <= Q(3, 16):
            counts['gamma'] += 1
            return '(.leaf 1)'
        if k in tags:
            seen.add(k)
            counts['matrix'] += 1
            return f'(.leaf {tags[k]})'
        depth, index = k
        assert depth < 4, ('uncovered', k)
        counts['octree_internal'] += 1
        middle = tuple(Q(2*i+1, 2**(depth+1)) for i in index)
        children = {bits: tree((depth+1, tuple(2*i+b for i,b in zip(index,bits))))
                    for bits in product(range(2), repeat=3)}

        def split(axis, prefix):
            if axis == 3:
                return children[prefix]
            return (f'(.split {axis} {rat(middle[axis])}\n'
                    f'  {split(axis+1, prefix+(0,))}\n'
                    f'  {split(axis+1, prefix+(1,))})')
        return split(0, ())

    names = []
    for indices in product(range(4), repeat=3):
        name = ''.join(map(str, indices))
        names.append(name)
        x, y, z = indices
        save('Cube'+name, 'import Maxwell.Certificate.NegativeCover.Data\n'
             'import Maxwell.Certificate.CoverPartition\n\n'
             'namespace Maxwell.Certificate.FrozenNegativeCover\n'
             'open FrozenCover\n\nset_option maxRecDepth 8192\nset_option maxHeartbeats 0\n\n'
             f'def tree{name} : CoverTree :=\n  {tree((2, indices))}\n\n'
             f'theorem checked{name} : (tree{name}).check (leafCheck matrixBoxes)\n'
             f'    (quarterBox {x} {y} {z}) = true := by decide +kernel\n\n'
             f'theorem covers{name} (x : Fin 3 → ℝ)\n'
             f'    (hx : (quarterBox {x} {y} {z}).Contains x)\n'
             '    (hw : Box.Wedge x) : Region matrixBoxes x :=\n'
             f'  check_sound matrixBoxes tree{name} _ checked{name} x hx hw\n\n'
             'end Maxwell.Certificate.FrozenNegativeCover\n')
    assert seen == set(keys), ('unused', set(keys)-seen)
    save('Complete', '\n'.join(f'import Maxwell.Certificate.NegativeCover.Cube{n}' for n in names)+
         '\n\nnamespace Maxwell.Certificate.FrozenNegativeCover\nopen FrozenCover\n\n'
         '/-- The original negative-trial boxes and the Gamma cube cover the whole wedge. -/\n'
         'theorem coverage (x : Fin 3 → ℝ)\n'
         '    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hw : Box.Wedge x) :\n'
         '    Gamma x ∨ ∃ i : Fin 604, (matrixBoxes i).Contains x := by\n'
         '  have hr : rootBox.Contains x := by\n'
         '    intro i\n'
         '    fin_cases i <;> simpa [rootBox] using hx _\n'
         '  obtain ⟨ix, iy, iz, hq⟩ := root_to_quarters hr\n'
         '  fin_cases ix <;> fin_cases iy <;> fin_cases iz\n'+
         '\n'.join(f'  · exact covers{n} x hq hw' for n in names)+
         '\n\nend Maxwell.Certificate.FrozenNegativeCover\n')
    assert PROPOSAL.read_bytes() == raw
    manifest = {'input': str(PROPOSAL), 'input_sha256': sha256(raw).hexdigest(),
                'outputs': outputs, 'counts': dict(counts), 'scope': 'geometric cover only',
                'records': [{'index': i, 'witness': r['witness']} for i,r in enumerate(records)]}
    (ROOT/'evidence/negative_cover_proposals.json').write_text(json.dumps(manifest, indent=2)+'\n')
    print(json.dumps(dict(counts)))


if __name__ == '__main__':
    main()
