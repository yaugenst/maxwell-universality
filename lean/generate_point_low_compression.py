# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Propose 42-coordinate point compressions inside the accepted Schur inputs."""
from pathlib import Path
import hashlib,json
import numpy as np
ROOT=Path(__file__).resolve().parent
OUT=ROOT/'Maxwell/Certificate/LowCompressionWitness';OUT.mkdir(exist_ok=True)
def rect(a):return '⟨'+', '.join(str(int(v)) for v in a)+'⟩'
def mat(a):return '!!['+';\n'.join(', '.join(rect(z) for z in row) for row in a)+']'
modules=[];manifest=[]
for label in ['lower','upper']:
 path=ROOT/f'evidence/point_inertia_proposals/{label}.npz';a=np.load(path)
 name=label.title();F=a['field'][a['low']].reshape(42,28,3);A=a['applied'][a['low']].reshape(42,28,3);C=a['compression'].copy()
 for i in range(28):
  for j in range(i+1,28): C[i,j]=C[j,i]*(1,-1,1)
 s='import Maxwell.Certificate.DyadicRectangle\nimport Maxwell.Certificate.FourierBinding\nnamespace Maxwell.Certificate.LowCompressionWitness\nopen Matrix FourierBinding Maxwell.Spectral.PrimitiveYee\nset_option maxRecDepth 100000\n'
 s+=f'noncomputable def {name}LowField : Matrix (Fin 42) (Fin 28) DyadicRectangle := {mat(F)}\n'
 s+=f'noncomputable def {name}LowApplied : Matrix (Fin 42) (Fin 28) DyadicRectangle := {mat(A)}\n'
 s+=f'noncomputable def {name}Compression : Matrix (Fin 28) (Fin 28) DyadicRectangle := {mat(C)}\n'
 index=[]
 for f in a['low']:
  x,y,z=int(f)//100,(int(f)//10)%10,int(f)%10
  for j in range(3):index.append(f'({j},{x},{y},{z})')
 s+=f'def {name}LowIndex : Fin 42 → Electric := !['+', '.join(index)+']\n'
 s+=f'noncomputable def {name}DotCheck (i j : Fin 28) : Bool :=\n  DyadicRectangle.dotCheck 52 52 (fun k => ({name}LowField k i).conjugate) (fun k => {name}LowApplied k j) ({name}Compression i j) &&\n  DyadicRectangle.dotCheck 52 52 (fun k => ({name}LowField k j).conjugate) (fun k => {name}LowApplied k i) ({name}Compression i j).conjugate\n'
 s+='end Maxwell.Certificate.LowCompressionWitness\n';(OUT/f'{name}Data.lean').write_text(s);modules.append(f'Maxwell.Certificate.LowCompressionWitness.{name}Data')
 for i in range(28):
  namei=f'{name}Row{i:02d}'
  s=f'import Maxwell.Certificate.LowCompressionWitness.{name}Data\nnamespace Maxwell.Certificate.LowCompressionWitness\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\ntheorem {name}DotCheck_row{i} : ∀ j : Fin 28, {name}DotCheck {i} j = true := by decide +kernel\nend Maxwell.Certificate.LowCompressionWitness\n'
  (OUT/f'{namei}.lean').write_text(s);modules.append(f'Maxwell.Certificate.LowCompressionWitness.{namei}')
 s=''.join(f'import Maxwell.Certificate.LowCompressionWitness.{name}Row{i:02d}\n' for i in range(28))
 s+=f'namespace Maxwell.Certificate.LowCompressionWitness\ntheorem {name}DotCheck_all (i j : Fin 28) : {name}DotCheck i j = true := by\n  fin_cases i\n'+''.join(f'  · exact {name}DotCheck_row{i} j\n' for i in range(28))+'end Maxwell.Certificate.LowCompressionWitness\n'
 (OUT/f'{name}Checked.lean').write_text(s);modules.append(f'Maxwell.Certificate.LowCompressionWitness.{name}Checked')
 manifest.append({'label':label,'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'rows':42,'columns':28,'compression':'original lower-triangle rectangles, completed by conjugation','proof_status':'Requires generated kernel checks and actual field/action containment'})
(ROOT/'evidence/point_inertia_proposals/low_compression_manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
(ROOT/'evidence/point_inertia_proposals/low_compression_modules.json').write_text(json.dumps(modules,indent=2)+'\n')
