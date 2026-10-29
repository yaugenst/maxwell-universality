# /// script
# requires-python = ">=3.11"
# ///
"""Bind the low compression intervals to the already accepted signed Schur inputs."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent;OUT=ROOT/'Maxwell/Certificate/LowCompressionWitness';modules=[]
for label,nn in [('Lower',2),('Upper',4)]:
 for kind,n,offset,negative in [('Negative',nn,0,'true'),('Positive',28-nn,nn,'false')]:
  name=label+kind
  s=f'import Maxwell.Certificate.LowCompressionWitness.SignedSound\nimport Maxwell.Certificate.LowCompressionWitness.{label}Data\nimport Maxwell.Certificate.PointInertia.{name}\nnamespace Maxwell.Certificate.LowCompressionWitness\nopen Matrix DyadicRectangle PointInertia\nopen scoped ComplexOrder\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
  s+=f'def {name}Select (i : Fin {n}) : Fin 28 := ⟨i.val+{offset},by omega⟩\n'
  s+=f'noncomputable def {name}ShiftCheck (i j : Fin {n}) : Bool := Trigonometric.rectangleSubsetCheck\n    ((shiftedEntry {negative} ({label}Compression ({name}Select i) ({name}Select j)) i j).toRectangle 52) (PointInertia.{name}.enclosure0 i j)\n'
  for i in range(n):s+=f'theorem {name}ShiftRow{i} : ∀ j : Fin {n}, {name}ShiftCheck {i} j = true := by decide +kernel\n'
  s+=f'theorem {name}ShiftCheck_all (i j : Fin {n}) : {name}ShiftCheck i j = true := by\n  fin_cases i\n'+''.join(f'  · exact {name}ShiftRow{i} j\n' for i in range(n))
  s+=f'theorem {name}_selected_psd (F A : Matrix (Fin 42) (Fin 28) ℂ)\n    (hc : ∀ i j, ({label}Compression i j).Contains 52 (HermitianCompression.matrix F A i j)) :\n    (signedMatrix {negative} (HermitianCompression.matrix (F.submatrix id {name}Select) (A.submatrix id {name}Select))).PosSemidef :=\n  selected_psd_of_check F A {label}Compression {name}Select {negative} PointInertia.{name}.enclosure0\n    PointInertia.{name}.proposal PointInertia.{name}.accepted hc {name}ShiftCheck_all\n'
  s+='end Maxwell.Certificate.LowCompressionWitness\n';(OUT/f'{name}Signed.lean').write_text(s);modules.append(f'Maxwell.Certificate.LowCompressionWitness.{name}Signed')
(ROOT/'evidence/point_inertia_proposals/low_signed_modules.json').write_text(json.dumps(modules,indent=2)+'\n')
