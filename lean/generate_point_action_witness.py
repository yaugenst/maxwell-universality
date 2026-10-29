# /// script
# requires-python = ">=3.11"
# ///
"""Propose checked final Fourier magnetic actions from frozen intermediates."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
OUT=ROOT/'Maxwell/Certificate/PointActionWitness';OUT.mkdir(exist_ok=True)
modules=[]
for label,shift in [('Lower',1),('Upper',5)]:
 for col in range(28):
  prefix=f'{label}C{col:02d}';parts=[f'{label}ForwardD{j}C{col:02d}Native' for j in range(3)]
  s='import Maxwell.Certificate.PointActionWitness.Sound\n'
  s+=f'import Maxwell.Certificate.ProjectionWitness.{label}Check{col:02d}\nimport Maxwell.Certificate.AppliedWitness.{label}Applied{col}\n'
  s+=''.join(f'import Maxwell.Certificate.FFTWitness.{x}\n' for x in parts)
  s+='namespace Maxwell.Certificate.PointActionWitness\nopen DyadicRectangle FourierBinding PointInertia ProjectionWitness AppliedWitness FFTWitness\nopen Matrix\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
  s+=f'noncomputable def {prefix}Weighted (f : Frequency) : Fin 3 → DyadicRectangle := !['+', '.join(f'{x} f' for x in parts)+']\n'
  s+=f'noncomputable def {prefix}Check (f : Frequency) : Bool := magneticCheck (symbolEnclosure f) ({prefix}Weighted f) ({label}Result{col} f) ({label}Applied{col} f)\n'
  for x in range(20):s+=f'theorem {prefix}CheckX{x} : ∀ y z : Fin 10, {prefix}Check ({x},y,z) = true := by decide +kernel\n'
  s+=f'theorem {prefix}Check_all (f : Frequency) : {prefix}Check f = true := by\n  rcases f with ⟨x,y,z⟩\n  fin_cases x\n'+''.join(f'  · exact {prefix}CheckX{x} y z\n' for x in range(20))
  s+=f'theorem {prefix}Applied_contains\n    (hw : ∀ f j, ({prefix}Weighted f j).Contains 52 (weightedField {shift} (projectedField {label}Raw{col}) (j,f)))\n    (f : Frequency) (j : Fin 3) :\n    ({label}Applied{col} f j).Contains 52\n      (((shiftedMagneticFourier (shiftedBaseMaterial {shift}) pointMomentum (1/64)).toEuclideanLin (projectedField {label}Raw{col})) (j,f)) :=\n  result_contains {shift} {label}Raw{col} {label}Result{col} {prefix}Weighted {label}Applied{col} {label}Result{col}_contains hw {prefix}Check_all f j\n'
  s+='end Maxwell.Certificate.PointActionWitness\n';(OUT/f'{prefix}.lean').write_text(s);modules.append(f'Maxwell.Certificate.PointActionWitness.{prefix}')
(ROOT/'evidence/point_inertia_proposals/action_modules.json').write_text(json.dumps(modules,indent=2)+'\n')
