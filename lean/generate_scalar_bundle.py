# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Assemble checked scalar records and bind widths to the canonical cover."""
import argparse
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def lookup(lo, hi):
    if hi-lo == 1:
        return f'record{lo:04d}'
    mid = (lo+hi)//2
    return f'(if i < {mid} then {lookup(lo,mid)} else {lookup(mid,hi)})'


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('kind', choices=['global', 'negative'])
    args = parser.parse_args()
    stem, count, cover, cover_ns = ('GlobalScalar', 2056, 'CoverData', 'FrozenCover') if args.kind == 'global' else (
        'NegativeScalar', 604, 'NegativeCover.Data', 'FrozenNegativeCover')
    out = ROOT/'Maxwell/Certificate'/stem
    ns = f'Maxwell.Certificate.{stem}.Frozen'
    text = '\n'.join(f'import Maxwell.Certificate.{stem}.Batch{i:03d}' for i in range((count+7)//8))
    text += (f'\n\nnamespace {ns}\n\n'
             'private def recordLookup (i : Nat) : VerifiedProposal :=\n  '+lookup(0,count)+'\n\n'
             '/-- Checked records in the exact canonical cover order. -/\n'
             f'def record (i : Fin {count}) : VerifiedProposal := recordLookup i.val\n'
             f'def proposal (i : Fin {count}) : Proposal := (record i).proposal\n'
             f'def evidence (i : Fin {count}) : Evidence := (record i).evidence\n\n'
             f'theorem checked (i : Fin {count}) : accepts (proposal i) (evidence i) = true :=\n'
             '  (record i).checked\n\n'
             f'end {ns}\n')
    (out/'Data.lean').write_text(text)
    (out/'GeometryBinding.lean').write_text(
        f'import Maxwell.Certificate.{stem}.Data\nimport Maxwell.Certificate.{cover}\n\n'
        f'namespace {ns}\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n'
        '/-- The arithmetic records use exactly the half-widths of the canonical geometric boxes. -/\n'
        f'theorem half_binding : ∀ (i : Fin {count}) (j : Fin 3),\n'
        f'    (proposal i).half = (({cover_ns}.matrixBoxes i).hi j-({cover_ns}.matrixBoxes i).lo j)/2 :=\n'
        '  by decide +kernel\n\n'
        f'end {ns}\n')


if __name__ == '__main__':
    main()
