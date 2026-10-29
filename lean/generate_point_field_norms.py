# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Propose exact high-frequency field/action square sums, checked in Lean."""
from pathlib import Path
import hashlib,json
import numpy as np
ROOT=Path(__file__).resolve().parent
OUT=ROOT/'Maxwell/Certificate/FieldNormWitness';OUT.mkdir(exist_ok=True)
DATA=ROOT/'Maxwell/Certificate/AppliedWitness';DATA.mkdir(exist_ok=True)
def vec(xs):return '!['+', '.join(xs)+']'
def rect(a):return '⟨'+', '.join(str(int(v)) for v in a)+'⟩'
def norm(a):
 x,y,r=map(int,a);return (abs(x)+r)**2+(abs(y)+r)**2
modules=[];records=[]
for label in ['lower','upper']:
 path=ROOT/f'evidence/point_inertia_proposals/{label}.npz'
 with np.load(path) as saved: a={key:saved[key] for key in ['low','field','applied']}
 name=label.title();low=set(map(int,a['low']))
 for col in range(28):
  d=a['applied'][:,:,col].reshape(20,10,10,3,3);tag=f'{name}Applied{col}'
  s='import Maxwell.Certificate.DyadicRectangle\nimport Maxwell.Certificate.FourierBinding\nnamespace Maxwell.Certificate.AppliedWitness\nopen FourierBinding\nset_option maxRecDepth 100000\n'
  for x in range(20):
   s+=f'noncomputable def {tag}X{x} : Fin 3 → Fin 10 → Fin 10 → DyadicRectangle := '+vec([vec([vec([rect(d[x,y,z,j]) for z in range(10)]) for y in range(10)]) for j in range(3)])+'\n'
  s+=f'noncomputable def {tag} (f : Frequency) : Fin 3 → DyadicRectangle := fun j => '+vec([f'{tag}X{x}' for x in range(20)])+' f.1 j f.2.1 f.2.2\nend Maxwell.Certificate.AppliedWitness\n'
  (DATA/f'{tag}.lean').write_text(s);modules.append(f'Maxwell.Certificate.AppliedWitness.{tag}')
 for kind,key,ns,suffix,target in [('Field','field','ProjectionWitness','Result',256*2**104),('Applied','applied','AppliedWitness','Applied',2**58)]:
  sums=[]
  for col in range(28):
   tag=f'{name}{suffix}{col}';prefix=f'{name}{kind}{col:02d}'
   rows=[sum(norm(a[key][f,j,col]) for f in range(100*x,100*x+100) if f not in low for j in range(3)) for x in range(20)]
   total=sum(rows);sums.append(total)
   s=f'import Maxwell.Certificate.{ns}.{tag}\nimport Maxwell.Certificate.PointInertia.FieldNorm\nnamespace Maxwell.Certificate.FieldNormWitness\nopen DyadicRectangle FourierBinding PointInertia {ns}\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
   s+=f'def {prefix}Rows : Fin 20 → ℤ := '+vec(list(map(str,rows)))+'\n'
   for x in range(20):s+=f'theorem {prefix}X{x} : highNormUpperX {tag} {x} = {prefix}Rows {x} := by decide +kernel\n'
   s+=f'theorem {prefix}_rows (x : Fin 20) : highNormUpperX {tag} x = {prefix}Rows x := by\n  fin_cases x\n'+''.join(f'  · exact {prefix}X{x}\n' for x in range(20))
   s+=f'theorem {prefix}_bound : highNormUpper {tag} ≤ {total} :=\n  highNormUpper_le_of_rows {tag} {prefix}Rows {total} {prefix}_rows (by decide +kernel)\n'
   s+='end Maxwell.Certificate.FieldNormWitness\n';(OUT/f'{prefix}.lean').write_text(s);modules.append(f'Maxwell.Certificate.FieldNormWitness.{prefix}')
  assert sum(sums)<=target
  s='import Maxwell.Certificate.PointInertia.FieldNorm\nnamespace Maxwell.Certificate.FieldNormWitness\nset_option maxRecDepth 100000\n'
  s+=f'def {name}{kind}Bounds : Fin 28 → ℤ := '+vec(list(map(str,sums)))+'\n'
  s+=f'theorem {name}{kind}Bounds_sum : ∑ i, {name}{kind}Bounds i ≤ {target} := by decide +kernel\nend Maxwell.Certificate.FieldNormWitness\n'
  (OUT/f'{name}{kind}Bounds.lean').write_text(s);modules.append(f'Maxwell.Certificate.FieldNormWitness.{name}{kind}Bounds')
  records.append({'label':label,'kind':kind,'upper_square_sum':str(sum(sums)),'accepted_target':str(target),'scale':2**104,'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
(ROOT/'evidence/point_inertia_proposals/field_norm_modules.json').write_text(json.dumps(modules,indent=2)+'\n')
(ROOT/'evidence/point_inertia_proposals/field_norm_manifest.json').write_text(json.dumps(records,indent=2)+'\n')
