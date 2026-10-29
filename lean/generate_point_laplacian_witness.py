# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Freeze actual scalar laplacian and low-frequency index proposals."""
from pathlib import Path
import numpy as np
ROOT=Path(__file__).resolve().parent
with np.load(ROOT/'evidence/point_inertia_proposals/lower.npz') as data:
    lap=data['lap'].reshape(20,10,10,3);low=list(map(int,data['low']))
def rect(r):return '⟨'+', '.join(str(int(x)) for x in r)+'⟩'
def vec(r):return '!['+', '.join(rect(x) for x in r)+']'
s='''import Maxwell.Certificate.PointInertia.Symbols
namespace Maxwell.Certificate.PointInertia
open Maxwell.Spectral.PrimitiveYee FourierBinding DyadicRectangle
set_option maxRecDepth 100000
set_option maxHeartbeats 0
'''
for x in range(20):s+=f'def laplacian{x} : Fin 10 → Fin 10 → DyadicRectangle := !['+',\n'.join(vec(row) for row in lap[x])+']\n'
s+='def lapEnclosure (f : Frequency) : DyadicRectangle := (!['+','.join(f'laplacian{x}' for x in range(20))+']) f.1 f.2.1 f.2.2\n'
s+='def lowFrequencies : Finset Frequency := {'+', '.join(f'({q//100},{q//10%10},{q%10})' for q in low)+'}\n'
s+='theorem lowFrequencies_card : lowFrequencies.card = 14 := by decide +kernel\n'
s+='def lapCheck (f : Frequency) : Bool :=\n  dotCheck 52 52 (fun j => (symbolEnclosure f j).conjugate) (symbolEnclosure f) (lapEnclosure f) &&\n  decide (729*(2:ℤ)^52 ≤ 10000*((lapEnclosure f).re-(lapEnclosure f).radius)) &&\n  if f ∈ lowFrequencies then decide (100*((lapEnclosure f).re+(lapEnclosure f).radius) ≤ 51*(2:ℤ)^52)\n  else decide (6241*(2:ℤ)^52 ≤ 10000*((lapEnclosure f).re-(lapEnclosure f).radius))\n'
s+='end Maxwell.Certificate.PointInertia\n'
(ROOT/'Maxwell/Certificate/PointInertia/LaplacianData.lean').write_text(s)
