# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Emit actual global symbol proposals, all accepted by kernel arithmetic."""
from pathlib import Path
from fractions import Fraction
import importlib.util,json
import numpy as np
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT.parent/'certificates/yee'
SNAPSHOT=SOURCE/'work/bulk/global_certificate'
OUT=ROOT/'Maxwell/Certificate/GlobalWitness';OUT.mkdir(exist_ok=True)
spec=importlib.util.spec_from_file_location('global_intervals',SNAPSHOT/'interval_tools.py');v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
def rect(a):return '⟨'+', '.join(str(int(x)*16) for x in a)+'⟩'
def vec(xs):return '!['+', '.join(xs)+']'
roots=vec([rect(a) for a in v.ROOTS])
s='import Maxwell.Certificate.GlobalSymbol\nnamespace Maxwell.Certificate.GlobalWitness\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
s+=f'def roots : Fin 20 → DyadicRectangle := {roots}\n'
for j in range(20):s+=f'theorem root{j:02d}_checked : Trigonometric.cisCheck (({j}:ℚ)/20) ((roots {j}).toRectangle 52) = true := by decide +kernel\n'
s+='theorem roots_checked (n : Fin 20) : Trigonometric.cisCheck ((n.val:ℚ)/20) ((roots n).toRectangle 52) = true := by\n  fin_cases n\n'+''.join(f'  · exact root{j:02d}_checked\n' for j in range(20))
s+='end Maxwell.Certificate.GlobalWitness\n';(OUT/'Roots.lean').write_text(s)
meta=json.loads((ROOT/'evidence/global_center_proposals/record0000.json').read_text());rec=meta['record']
with np.load(ROOT/'evidence/global_center_proposals/record0000.npz') as a:d=a['d']
coords=np.array([(x,y,z) for x in range(20) for y in range(10) for z in range(10)])
indices=np.stack([coords[:,0],2*coords[:,1]-coords[:,0],2*coords[:,2]-coords[:,0]],axis=1)%20
table=[[d[np.flatnonzero(indices[:,j]==n)[0],j] for n in range(20)] for j in range(3)]
phases=[v.cis(Fraction(c)/20) for c in rec['center']]
s='import Maxwell.Certificate.GlobalWitness.Roots\nimport Maxwell.Certificate.GlobalGeometry\nnamespace Maxwell.Certificate.GlobalWitness\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
s+='def phases0000 : Fin 3 → DyadicRectangle := '+vec([rect(a) for a in phases])+'\n'
s+='def symbols0000 : Fin 3 → Fin 20 → DyadicRectangle := '+vec([vec([rect(a) for a in row]) for row in table])+'\n'
s+='theorem phases0000_checked : ∀ j, Trigonometric.cisCheck (FrozenGlobal.centerQ 0 j/20) ((phases0000 j).toRectangle 52) = true := by decide +kernel\n'
s+='theorem symbols0000_checked : ∀ j n, GlobalSymbol.symbolCheck roots phases0000 symbols0000 j n = true := by decide +kernel\n'
s+='theorem symbols0000_contains (f : FourierBinding.Frequency) (j : Fin 3) : (GlobalSymbol.enclosure symbols0000 f j).Contains 52 (FourierBinding.symbol (FrozenGlobal.center 0) f j) := GlobalSymbol.enclosure_contains (FrozenGlobal.centerQ 0) roots phases0000 symbols0000 roots_checked phases0000_checked symbols0000_checked f j\n'
s+='end Maxwell.Certificate.GlobalWitness\n';(OUT/'Symbols0000.lean').write_text(s)
(ROOT/'evidence/global_center_proposals/symbol_modules.json').write_text(json.dumps(['Maxwell.Certificate.GlobalWitness.Roots','Maxwell.Certificate.GlobalWitness.Symbols0000'],indent=2)+'\n')
