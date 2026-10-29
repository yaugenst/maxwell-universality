# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Freeze actual point difference-symbol proposals; Lean accepts the arithmetic."""
from pathlib import Path
import importlib.util
from fractions import Fraction
import numpy as np
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT.parent/'certificates/yee'
SNAP=SOURCE/'work/bulk/edge_isolation/interval_tools.py'
spec=importlib.util.spec_from_file_location('interval_tools',SNAP)
v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
with np.load(ROOT/'evidence/point_inertia_proposals/lower.npz') as data:
    d=data['d'].copy();lap=data['lap'].copy()
q=np.array([(x,(2*y-x)%20,(2*z-x)%20) for x in range(20) for y in range(10) for z in range(10)])
table=[[d[np.flatnonzero(q[:,j]==i)[0],j] for i in range(20)] for j in range(3)]
phase=[v.cis(Fraction(1,40)),v.cis(Fraction(-1,40))]
def rect(r):return '⟨'+', '.join(str(int(x)) for x in r)+'⟩'
def vector(r):return '!['+', '.join(rect(x) for x in r)+']'
body='''import Maxwell.Certificate.FFTWitness.ConstantsData
namespace Maxwell.Certificate.PointInertia
open Maxwell.Certificate
def center : Fin 3 → ℚ := ![1/2,1/2,-1/2]
'''
body+='def sourceRoots : Fin 20 → DyadicRectangle := '+vector(v.ROOTS)+'\n'
body+=f'def phasePlus : DyadicRectangle := {rect(phase[0])}\n'
body+=f'def phaseMinus : DyadicRectangle := {rect(phase[1])}\n'
body+='def phase : Fin 3 → DyadicRectangle := ![phasePlus,phasePlus,phaseMinus]\n'
body+='def symbols : Fin 3 → Fin 20 → DyadicRectangle := !['+',\n'.join(vector(row) for row in table)+']\n'
body+='def one52 : DyadicRectangle := ⟨4503599627370496,0,0⟩\n'
body+='end Maxwell.Certificate.PointInertia\n'
(ROOT/'Maxwell/Certificate/PointInertia/SymbolsData.lean').write_text(body)
