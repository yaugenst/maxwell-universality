# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Propose exact material denominator binding and scalar inverse-mass checks."""
from pathlib import Path
import hashlib,json
import numpy as np
ROOT=Path(__file__).resolve().parent
OUT=ROOT/'Maxwell/Certificate/MaterialWitness';OUT.mkdir(exist_ok=True)
def vec(a):return '!['+', '.join(a)+']'
a=np.load(ROOT/'evidence/point_inertia_proposals/lower.npz')['material_den']-1
b=np.load(ROOT/'evidence/point_inertia_proposals/upper.npz')['material_den']-5
assert np.array_equal(a,b);a=a.reshape(20,10,10,3)
s='import Maxwell.Certificate.PointInertia.MaterialDenominator\nnamespace Maxwell.Certificate.MaterialWitness\nopen Maxwell.Spectral.PrimitiveYee\nset_option maxRecDepth 100000\n'
for x in range(20):s+=f'noncomputable def baseDenX{x} : Fin 3 → Fin 10 → Fin 10 → ℤ := '+vec([vec([vec([str(int(a[x,y,z,j])) for z in range(10)]) for y in range(10)]) for j in range(3)])+'\n'
s+='noncomputable def baseDen (e : Electric) : ℤ := '+vec([f'baseDenX{x}' for x in range(20)])+' e.2.1 e.1 e.2.2.1 e.2.2.2\nend Maxwell.Certificate.MaterialWitness\n';(OUT/'BaseData.lean').write_text(s)
s='import Maxwell.Certificate.MaterialWitness.BaseData\nnamespace Maxwell.Certificate.MaterialWitness\nopen PointInertia Maxwell.Spectral.PrimitiveYee\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
for j in range(3):
 for x in range(20):s+=f'theorem baseDen_j{j}x{x} : ∀ y z : Fin 10, baseEdgeInteger ({j},{x},y,z) = baseDen ({j},{x},y,z) := by decide +kernel\n'
s+='theorem baseDen_binding (e : Electric) : baseEdgeInteger e = baseDen e := by\n  rcases e with ⟨j,x,y,z⟩\n  fin_cases j <;> fin_cases x\n'+''.join(f'  · exact baseDen_j{j}x{x} y z\n' for j in range(3) for x in range(20))
s+='end Maxwell.Certificate.MaterialWitness\n';(OUT/'BaseChecked.lean').write_text(s)
modules=['Maxwell.Certificate.MaterialWitness.BaseData','Maxwell.Certificate.MaterialWitness.BaseChecked','Maxwell.Certificate.MaterialWitness.FastSound']
for label,shift in [('Lower',1),('Upper',5)]:
 for j in range(3):
  for col in range(28):
   name=f'{label}D{j}C{col:02d}';inp=name+'Native';out=f'{label}ForwardD{j}C{col:02d}Input'
   s=f'import Maxwell.Certificate.MaterialWitness.FastSound\nimport Maxwell.Certificate.FFTWitness.{inp}\nimport Maxwell.Certificate.FFTWitness.{out}\nnamespace Maxwell.Certificate.MaterialWitness\nopen DyadicRectangle FourierBinding FFTWitness Maxwell.Spectral.PrimitiveYee\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
   s+=f'noncomputable def {name}Check (f : Frequency) : Bool := scaleCheck 4 (baseDen ({j},f)+{shift}) ({inp} f) ({out} f)\n'
   for x in range(20):s+=f'theorem {name}CheckX{x} : ∀ y z : Fin 10, {name}Check ({x},y,z) = true := by decide +kernel\n'
   s+=f'theorem {name}Check_all (f : Frequency) : {name}Check f = true := by\n  rcases f with ⟨x,y,z⟩\n  fin_cases x\n'+''.join(f'  · exact {name}CheckX{x} y z\n' for x in range(20))
   s+=f'theorem {name}_contains (v : Cell → ℂ) (hv : DyadicFFT.Contains 52 {inp} v) :\n    DyadicFFT.Contains 52 {out} (fun f => v f / (edgeAverage (fun r => Maxwell.Spectral.Concrete.baseMaterial r + ({shift}:ℝ)/4) ({j},f) : ℂ)) := by\n  intro f\n  have h := scale_check_sound (shift:={shift}) (e:=({j},f)) ({name}Check_all f) (hv f)\n  norm_num only [Int.cast_ofNat] at h\n  exact h\n'
   s+='end Maxwell.Certificate.MaterialWitness\n';(OUT/f'{name}.lean').write_text(s);modules.append(f'Maxwell.Certificate.MaterialWitness.{name}')
(ROOT/'evidence/point_inertia_proposals/material_modules.json').write_text(json.dumps(modules,indent=2)+'\n')
