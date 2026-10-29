# /// script
# requires-python = ">=3.11"
# ///
"""Bind extracted 42-row data to the full frozen field/action tables."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent;OUT=ROOT/'Maxwell/Certificate/LowCompressionWitness';modules=[]
for label in ['Lower','Upper']:
 s=f'import Maxwell.Certificate.LowCompressionWitness.{label}Data\nimport Maxwell.Certificate.PointInertia.LowCoordinates\nnamespace Maxwell.Certificate.LowCompressionWitness\nopen PointInertia\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
 s+=f'theorem {label}LowIndex_mem : ∀ i, ({label}LowIndex i).2 ∈ lowFrequencies := by decide +kernel\n'
 s+=f'theorem {label}LowIndex_injective : Function.Injective {label}LowIndex := by decide +kernel\n'
 s+='end Maxwell.Certificate.LowCompressionWitness\n';(OUT/f'{label}Index.lean').write_text(s);modules.append(f'Maxwell.Certificate.LowCompressionWitness.{label}Index')
 for col in range(28):
  name=f'{label}LiteralBinding{col:02d}'
  s=f'import Maxwell.Certificate.LowCompressionWitness.{label}Data\nimport Maxwell.Certificate.ProjectionWitness.{label}Result{col}\nimport Maxwell.Certificate.AppliedWitness.{label}Applied{col}\nnamespace Maxwell.Certificate.LowCompressionWitness\nopen ProjectionWitness AppliedWitness\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
  s+=f'theorem {label}LowField_col{col} : ∀ k : Fin 42, {label}LowField k {col} = {label}Result{col} ({label}LowIndex k).2 ({label}LowIndex k).1 := by decide +kernel\n'
  s+=f'theorem {label}LowApplied_col{col} : ∀ k : Fin 42, {label}LowApplied k {col} = {label}Applied{col} ({label}LowIndex k).2 ({label}LowIndex k).1 := by decide +kernel\n'
  s+='end Maxwell.Certificate.LowCompressionWitness\n';(OUT/f'{name}.lean').write_text(s);modules.append(f'Maxwell.Certificate.LowCompressionWitness.{name}')
(ROOT/'evidence/point_inertia_proposals/low_binding_modules.json').write_text(json.dumps(modules,indent=2)+'\n')
