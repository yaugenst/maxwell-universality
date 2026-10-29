# /// script
# requires-python = ">=3.11"
# ///
"""Compose every accepted point action into the actual base magnetic fiber."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
OUT=ROOT/'Maxwell/Certificate/PointActionWitness';modules=[]
for label,shift in [('Lower',1),('Upper',5)]:
 for col in range(28):
  name=f'{label}C{col:02d}'
  s=f'import Maxwell.Certificate.PointActionWitness.Pipeline\nimport Maxwell.Certificate.PointActionWitness.{name}\nimport Maxwell.Certificate.CurlWitness.{name}\n'
  for j in range(3):
   p=f'{label}D{j}C{col:02d}';fp=f'{label}ForwardD{j}C{col:02d}'
   s+=f'import Maxwell.Certificate.FFTWitness.{p}ListComplete\nimport Maxwell.Certificate.MaterialWitness.{p}\nimport Maxwell.Certificate.FFTWitness.{fp}ListComplete\n'
  s+='namespace Maxwell.Certificate.PointActionWitness\nopen DyadicRectangle FourierBinding PointInertia ProjectionWitness AppliedWitness FFTWitness\n'
  s+=f'noncomputable def {name}Inverse (f : Frequency) : Fin 3 → DyadicRectangle := !['+', '.join(f'{label}D{j}C{col:02d}Native f' for j in range(3))+']\n'
  s+=f'noncomputable def {name}Material (f : Frequency) : Fin 3 → DyadicRectangle := !['+', '.join(f'{label}ForwardD{j}C{col:02d}Input f' for j in range(3))+']\n'
  s+=f'theorem {name}Weighted_contains (f : Frequency) (j : Fin 3) :\n    ({name}Weighted f j).Contains 52 (weightedField {shift} (projectedField {label}Raw{col}) (j,f)) := by\n'
  s+=f'  apply weightedField_contains {shift} {label}Raw{col} CurlWitness.{name}Output {name}Inverse {name}Material {name}Weighted CurlWitness.{name}Output_contains\n'
  for kind in ['inverse','material','forward']:
   s+='  · intro k v hv\n    fin_cases k\n'
   for j in range(3):
    decl=f'{label}D{j}C{col:02d}_list_native_inverse_contains' if kind=='inverse' else f'MaterialWitness.{label}D{j}C{col:02d}_contains' if kind=='material' else f'{label}ForwardD{j}C{col:02d}_list_native_forward_contains'
    s+=f'    · intro f\n      change ({label}ForwardD{j}C{col:02d}Input f).Contains 52 (v f / (Maxwell.Spectral.PrimitiveYee.edgeAverage (shiftedBaseMaterial {shift}) ({j},f) : ℂ))\n      have hs : shiftedBaseMaterial {shift} = (fun r => Maxwell.Spectral.Concrete.baseMaterial r + ({shift}:ℝ)/4) := by\n        funext r\n        change _ + (({shift}:ℤ):ℝ)/4 = _\n        norm_num\n      rw [hs]\n      exact {decl} v hv f\n' if kind=='material' else f'    · exact {decl} v hv\n'
  s+=f'theorem {name}_actual_action_contains (f : Frequency) (j : Fin 3) :\n    ({label}Applied{col} f j).Contains 52\n      (((pointBaseMagneticMatrix ({shift}/256)).toEuclideanLin (projectedField {label}Raw{col})) (j,f)) := by\n'
  s+=f'  have h := {name}Applied_contains {name}Weighted_contains f j\n  rw [shifted_magnetic_eq] at h\n  norm_num only [Int.cast_ofNat] at h\n  exact h\nend Maxwell.Certificate.PointActionWitness\n'
  (OUT/f'{name}Complete.lean').write_text(s);modules.append(f'Maxwell.Certificate.PointActionWitness.{name}Complete')
(ROOT/'evidence/point_inertia_proposals/action_complete_modules.json').write_text(json.dumps(modules,indent=2)+'\n')
