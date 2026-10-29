# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Emit bounded dyadic Schur proposals; Lean checks all rational operations."""
from fractions import Fraction as Q
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'Maxwell/Certificate/PointInertia'
OUT.mkdir(exist_ok=True)
BITS = 52
SCALE = 2**BITS


def add(a, b):
    return a[0]+b[0], a[1]+b[1]


def neg(a):
    return -a[0], a[1]


def mul(a, b):
    return a[0]*b[0], abs(a[0])*b[1]+abs(b[0])*a[1]+a[1]*b[1]


def cmul(a, b):
    return add(mul(a[0],b[0]),neg(mul(a[1],b[1]))), add(mul(a[0],b[1]),mul(a[1],b[0]))


def rounded(a):
    lo = ((a[0]-a[1])*SCALE).__floor__()
    hi = ((a[0]+a[1])*SCALE).__ceil__()
    return Q(lo+hi,2*SCALE), Q(hi-lo,2*SCALE)


def schur(a):
    c,r = a[0][0][0]
    assert c-r > 0
    lo,hi = 1/(c+r),1/(c-r)
    inverse = ((lo+hi)/2,(hi-lo)/2)
    result=[]
    for row in range(1,len(a)):
        line=[]
        for col in range(1,len(a)):
            prod=cmul(a[row][0],(a[col][0][0],neg(a[col][0][1])))
            prod=(mul(prod[0],inverse),mul(prod[1],inverse))
            line.append(tuple(rounded(add(a[row][col][i],neg(prod[i]))) for i in range(2)))
        result.append(line)
    return result


def rat(q):
    return str(q.numerator) if q.denominator==1 else f'({q.numerator}/{q.denominator})'


def rect(z):
    return f'rectangle {rat(z[0][0])} {rat(z[0][1])} {rat(z[1][0])} {rat(z[1][1])}'


for label in ['lower','upper']:
    with np.load(ROOT/f'evidence/point_inertia_proposals/{label}.npz') as data:
        for key in ['negative','positive','low_gram']:
            raw=data[key]
            a=[[((Q(int(z[0]),SCALE),Q(int(z[2]),SCALE)),
                 (Q(int(z[1]),SCALE),Q(int(z[2]),SCALE))) for z in row] for row in raw]
            # The source certifier reads only the lower triangle.
            a=[[a[i][j] if j<=i else (a[j][i][0],neg(a[j][i][1])) for j in range(len(a))] for i in range(len(a))]
            name=label.title()+''.join(w.title() for w in key.split('_'))
            body=['import Maxwell.Certificate.IntervalMatrix\nimport Mathlib.LinearAlgebra.Matrix.Notation\n',
                  f'namespace Maxwell.Certificate.PointInertia.{name}\nopen Maxwell.Certificate.IntervalMatrix\n',
                  'open scoped ComplexOrder\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n',
                  'private def rectangle (r rr i ir : ℚ) (hr : 0 ≤ rr := by norm_num) (hi : 0 ≤ ir := by norm_num) : ComplexRectangle := ⟨⟨r,rr,hr⟩,⟨i,ir,hi⟩⟩\n']
            n=len(a)
            for step in range(n):
                literal='!!['+'; '.join(', '.join(rect(z) for z in row) for row in a)+']'
                body.append(f'def enclosure{step} : Enclosure {len(a)} := {literal}\n')
                a=schur(a)
            body.append(f'def enclosure{n} : Enclosure 0 := fun i => Fin.elim0 i\n')
            proposal='.empty'
            for step in reversed(range(1,n+1)):
                proposal=f'(.next enclosure{step} {proposal})'
            body.append(f'def proposal : Proposal {n} := {proposal}\n')
            body.append(f'end Maxwell.Certificate.PointInertia.{name}\n')
            (OUT/f'{name}Data.lean').write_text('\n'.join(body))
            for step in reversed(range(n)):
                imports=f'import Maxwell.Certificate.IntervalMatrixRows\nimport Maxwell.Certificate.PointInertia.{name}Data\n'
                if step+1<n:
                    imports+=f'import Maxwell.Certificate.PointInertia.{name}Step{step+1:02d}\n'
                tail='.empty'
                for k in reversed(range(step+1,n+1)):
                    tail=f'(.next enclosure{k} {tail})'
                previous='rfl' if step+1==n else f'accepted{step+1}'
                tactic='decide +kernel'
                if n-step>18:
                    for row in range(n-step-1):
                        rowname=f'{name}Step{step:02d}Row{row:02d}'
                        imports+=f'import Maxwell.Certificate.PointInertia.{rowname}\n'
                        rowbody=f'''import Maxwell.Certificate.PointInertia.{name}Data
namespace Maxwell.Certificate.PointInertia.{name}
open Maxwell.Certificate.IntervalMatrix Maxwell.Certificate.Trigonometric
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem step{step}_row{row} : ∀ j : Fin {n-step-1},
    rectangleSubsetCheck (step enclosure{step} (by decide +kernel) {row} j) (enclosure{step+1} {row} j) = true := by
  decide +kernel
end Maxwell.Certificate.PointInertia.{name}
'''
                        (OUT/f'{rowname}.lean').write_text(rowbody)
                    tactic='apply subsetCheck_of_rows\n  intro i j\n  fin_cases i\n'
                    tactic+='\n'.join(f'  · exact step{step}_row{row} j' for row in range(n-step-1))
                check=imports+f'''namespace Maxwell.Certificate.PointInertia.{name}
open Maxwell.Certificate.IntervalMatrix
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem pivot{step}_positive : 0 < pivotLower enclosure{step} := by decide +kernel
theorem step{step}_checked : subsetCheck (step enclosure{step} pivot{step}_positive) enclosure{step+1} = true := by
  {tactic}
theorem accepted{step} : accepts enclosure{step} {tail} = true := by
  rw [accepts, dite_eq_left pivot{step}_positive]
  exact Bool.and_eq_true_iff.mpr ⟨step{step}_checked, {previous}⟩
end Maxwell.Certificate.PointInertia.{name}
'''
                (OUT/f'{name}Step{step:02d}.lean').write_text(check)
            final=f'''import Maxwell.Certificate.PointInertia.{name}Step00
namespace Maxwell.Certificate.PointInertia.{name}
open Maxwell.Certificate.IntervalMatrix
open scoped ComplexOrder
theorem accepted : accepts enclosure0 proposal = true := accepted0
theorem sound {{A : Matrix (Fin {n}) (Fin {n}) ℂ}} (hA : A.IsHermitian)
    (ha : Contains enclosure0 A) : A.PosSemidef := accepts_sound proposal accepted hA ha
end Maxwell.Certificate.PointInertia.{name}
'''
            (OUT/f'{name}.lean').write_text(final)
            print(name,n,flush=True)
