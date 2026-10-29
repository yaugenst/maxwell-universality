# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Generate exact integer projection proposals; Lean checks every operation."""
from pathlib import Path
import hashlib,json
import numpy as np
ROOT=Path(__file__).resolve().parent
OUT=ROOT/'Maxwell/Certificate/ProjectionWitness';OUT.mkdir(exist_ok=True)
S=2**52

def trunc(x,d):return x//d if x>=0 else -((-x)//d)
def add(a,b):return tuple(int(x)+int(y) for x,y in zip(a,b))
def mul(a,b):
    x,y,r=map(int,a);u,v,s=map(int,b)
    err=(abs(x)+abs(y))*s+(abs(u)+abs(v))*r+2*r*s
    return trunc(x*u-y*v,S),trunc(x*v+y*u,S),(err+S-1)//S+1
def div(a,b):
    x,y,r=map(int,a);u,v,s=map(int,b);assert v==0 and u>s
    mids=[trunc(x*S,u),trunc(y*S,u)];radius=0
    for m,mid in zip([x,y],mids):
        lo=min((m-r)*S//(u-s),(m-r)*S//(u+s))
        hi=max(-((-(m+r)*S)//(u-s)),-((-(m+r)*S)//(u+s)))
        radius=max(radius,mid-lo,hi-mid)
    return *mids,radius

def rect(r):return '⟨'+', '.join(str(int(x)) for x in r)+'⟩'
def vec(xs):return '!['+', '.join(xs)+']'
def emit(name,a):
    a=np.array(a).reshape(20,10,10,-1,3)
    m=a.shape[-2]
    s='import Maxwell.Certificate.PointInertia.LaplacianData\nimport Maxwell.Certificate.DyadicProjection\n'
    s+='namespace Maxwell.Certificate.ProjectionWitness\nopen Maxwell.Certificate FourierBinding\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
    for x in range(20):
        s+=f'noncomputable def {name}X{x} : Fin {m} → Fin 10 → Fin 10 → DyadicRectangle := '+vec([vec([vec([rect(a[x,y,z,j]) for z in range(10)]) for y in range(10)]) for j in range(m)])+'\n'
    s+=f'noncomputable def {name} (f : Frequency) : Fin {m} → DyadicRectangle := fun j => '+vec([f'{name}X{x}' for x in range(20)])+' f.1 j f.2.1 f.2.2\n'
    s+='end Maxwell.Certificate.ProjectionWitness\n'
    (OUT/f'{name}.lean').write_text(s)

records=[]
for label in ['lower','upper']:
    path=ROOT/f'evidence/point_inertia_proposals/{label}.npz'
    with np.load(path) as d:
        raw=d['raw'];symbols=d['d'];lap=d['lap'];field=d['field']
    rawi=np.zeros(raw.shape+(3,),dtype=np.int64)
    rawi[...,0]=np.rint(raw.real*S).astype(np.int64)
    rawi[...,1]=np.rint(raw.imag*S).astype(np.int64)
    dots=np.zeros((2000,28,3),dtype=np.int64);quot=np.zeros_like(dots)
    for f in range(2000):
      for col in range(28):
        dot=(0,0,0)
        for j in range(3):dot=add(dot,mul(symbols[f,j],rawi[f,j,col]))
        dots[f,col]=dot;quot[f,col]=div(dot,lap[f])
        for j in range(3):
            symbol=symbols[f,j];product=mul((symbol[0],-symbol[1],symbol[2]),quot[f,col])
            result=add(rawi[f,j,col],(-product[0],-product[1],product[2]))
            assert tuple(field[f,j,col])==result,(label,f,j,col)
    target=ROOT/f'evidence/point_inertia_proposals/{label}_projection.npz'
    np.savez_compressed(target,raw=rawi,dot=dots,quotient=quot,field=field)
    records.append({'label':label,'source_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'projection_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'exact_native_projection_match':True})
    for col in range(28):
        for tag,a in [('Raw',rawi[:,:,col]),('Result',field[:,:,col]),('Dot',dots[:,col]),('Quotient',quot[:,col])]:emit(f'{label.title()}{tag}{col}',a)
(ROOT/'evidence/point_inertia_proposals/projection_manifest.json').write_text(json.dumps(records,indent=2)+'\n')

modules=[]
for label in ['Lower','Upper']:
  for col in range(28):
    parts=[f'{label}{tag}{col}' for tag in ['Raw','Result','Dot','Quotient']]
    modules.extend(f'Maxwell.Certificate.ProjectionWitness.{x}' for x in parts)
    checkname=f'{label}Check{col:02d}'
    s='import Maxwell.Certificate.ProjectionWitness.Sound\n'+''.join(f'import Maxwell.Certificate.ProjectionWitness.{x}\n' for x in parts)
    s+='namespace Maxwell.Certificate.ProjectionWitness\nopen DyadicRectangle FourierBinding PointInertia\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
    s+=f'noncomputable def {label}Proposal{col} (f : Frequency) : ProjectionProposal := ⟨{label}Dot{col} f 0, {label}Quotient{col} f 0, {label}Result{col} f⟩\n'
    s+=f'noncomputable def {label}Check{col} (f : Frequency) : Bool := projectionCheck 52 (symbolEnclosure f) ({label}Raw{col} f) (lapEnclosure f) ({label}Proposal{col} f)\n'
    for x in range(20):s+=f'theorem {label}Check{col}X{x} : ∀ y z : Fin 10, {label}Check{col} ({x},y,z) = true := by decide +kernel\n'
    s+=f'theorem {label}Check{col}_all (f : Frequency) : {label}Check{col} f = true := by\n  rcases f with ⟨x,y,z⟩\n  fin_cases x\n'+''.join(f'  · exact {label}Check{col}X{x} y z\n' for x in range(20))
    s+=f'theorem {label}Result{col}_contains (f : Frequency) (j : Fin 3) : ({label}Result{col} f j).Contains 52 (projectedPolarization {label}Raw{col} f j) := result_contains {label}Raw{col} {label}Proposal{col} {label}Check{col}_all f j\n'
    s+='end Maxwell.Certificate.ProjectionWitness\n'
    (OUT/f'{checkname}.lean').write_text(s)
    modules.append(f'Maxwell.Certificate.ProjectionWitness.{checkname}')
(ROOT/'evidence/point_inertia_proposals/projection_modules.json').write_text(json.dumps(modules,indent=2)+'\n')
