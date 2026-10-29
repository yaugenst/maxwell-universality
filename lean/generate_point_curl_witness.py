# /// script
# requires-python = ">=3.11"
# ///
"""Generate actual point curl checks without modifying any proposal tables."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent
OUT=ROOT/'Maxwell/Certificate/CurlWitness'; OUT.mkdir(exist_ok=True)
modules=[]
for label in ['Lower','Upper']:
 for col in range(28):
  prefix=f'{label}C{col:02d}'
  parts=[f'{label}D{j}C{col:02d}Input' for j in range(3)]
  s='import Maxwell.Certificate.CurlWitness.Sound\n'
  s+=f'import Maxwell.Certificate.ProjectionWitness.{label}Check{col:02d}\n'
  s+=''.join(f'import Maxwell.Certificate.FFTWitness.{x}\n' for x in parts)
  s+='namespace Maxwell.Certificate.CurlWitness\nopen DyadicRectangle FourierBinding PointInertia ProjectionWitness FFTWitness\nopen Matrix\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
  s+=f'noncomputable def {prefix}Output (f : Frequency) : Fin 3 → DyadicRectangle := !['+', '.join(f'{x} f' for x in parts)+']\n'
  s+=f'noncomputable def {prefix}Check (f : Frequency) : Bool := curlCheck 52 true (symbolEnclosure f) ({label}Result{col} f) ({prefix}Output f)\n'
  for x in range(20): s+=f'theorem {prefix}CheckX{x} : ∀ y z : Fin 10, {prefix}Check ({x},y,z) = true := by decide +kernel\n'
  s+=f'theorem {prefix}Check_all (f : Frequency) : {prefix}Check f = true := by\n  rcases f with ⟨x,y,z⟩\n  fin_cases x\n'+''.join(f'  · exact {prefix}CheckX{x} y z\n' for x in range(20))
  s+=f'theorem {prefix}Output_contains (f : Frequency) (j : Fin 3) :\n    ({prefix}Output f j).Contains 52 (((frequencyCurl pointMomentum).conjTranspose *ᵥ projectedField {label}Raw{col}) (j,f)) :=\n  adjoint_result_contains {label}Raw{col} {label}Result{col} {prefix}Output {label}Result{col}_contains {prefix}Check_all f j\n'
  s+='end Maxwell.Certificate.CurlWitness\n'
  (OUT/f'{prefix}.lean').write_text(s)
  modules.append(f'Maxwell.Certificate.CurlWitness.{prefix}')
(ROOT/'evidence/point_inertia_proposals/curl_modules.json').write_text(json.dumps(modules,indent=2)+'\n')
