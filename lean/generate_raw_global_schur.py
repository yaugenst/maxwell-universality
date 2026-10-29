# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Propose bounded integer Schur steps for frozen global matrix rectangles.

The generator only proposes rounded intermediates. Lean checks every multiply,
division, enclosure inclusion, and positive pivot using the raw integer core.
"""
from pathlib import Path
import argparse
import json
from hashlib import sha256
import numpy as np
from generate_fft_stage_proposals import round_dot, conjugate

ROOT = Path(__file__).resolve().parent
OUT = ROOT/'Maxwell/Certificate/GlobalSchurWitness'
S = 2**52

def quotient(a,b):
    ar,ai,ae = map(int,a)
    br,_,be = map(int,b)
    assert br > be
    values=[]
    for c in [ar,ai]:
        lows=[((c-ae)*S)//d for d in (br-be,br+be)]
        highs=[-((-(c+ae)*S)//d) for d in (br-be,br+be)]
        values.append((min(lows),max(highs)))
    mids=[(lo+hi)//2 for lo,hi in values]
    radius=max(max(mid-lo,hi-mid) for mid,(lo,hi) in zip(mids,values))
    return mids[0],mids[1],radius

def rectangle(z):
    return '⟨'+','.join(str(int(x)) for x in z)+'⟩'

def matrix(name,a):
    n=len(a)
    values=','.join('#['+','.join(rectangle(z) for z in row)+']' for row in a)
    return (f'noncomputable def {name}Data : Array (Array Rectangle) := #[{values}]\n'
            f'noncomputable def {name} (i j : Fin {n}) : Rectangle :=\n'
            f'  ((({name}Data[i.val]?).getD #[])[j.val]?).getD zero\n')

def main():
    p=argparse.ArgumentParser()
    p.add_argument('index',type=int)
    p.add_argument('--key',choices=['negative','positive'],default='positive')
    args=p.parse_args()
    OUT.mkdir(exist_ok=True)
    source=ROOT/f'evidence/global_center_proposals/record{args.index:04d}.npz'
    with np.load(source) as data:
        raw=np.array(data[args.key],dtype=object)*16
    a=[[tuple(map(int,z)) for z in row] for row in raw]
    # The native routine consumes the lower triangle. Complete it explicitly.
    a=[[a[i][j] if j<=i else conjugate(a[j][i]) for j in range(len(a))]
       for i in range(len(a))]
    prefix=f'Record{args.index:04d}{args.key.title()}'
    n=len(a)
    text=('import Maxwell.Certificate.DyadicKernelSchur\n'
          f'namespace Maxwell.Certificate.GlobalSchurWitness.{prefix}\n'
          'open DyadicKernel\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n')
    for step in range(n):
        m=len(a)
        text+=matrix(f'enclosure{step}',a)
        assert a[0][0][0]>a[0][0][2],(step,a[0][0])
        products=[[round_dot([(a[i][0],conjugate(a[j][0]))])
                   for j in range(1,m)] for i in range(1,m)]
        quotients=[[quotient(z,a[0][0]) for z in row] for row in products]
        b=[[(a[i][j][0]-quotients[i-1][j-1][0],
             a[i][j][1]-quotients[i-1][j-1][1],
             a[i][j][2]+quotients[i-1][j-1][2])
            for j in range(1,m)] for i in range(1,m)]
        text+=matrix(f'products{step}',products)
        text+=matrix(f'quotients{step}',quotients)
        a=b
    text+='def enclosure'+str(n)+' : Enclosure 0 := fun i => nomatch i\n'
    for step in reversed(range(n)):
        tail='.empty' if step+1==n else f'proposal{step+1}'
        text+=f'noncomputable def proposal{step} : SchurProposal {n-step} := .next enclosure{step+1} products{step} quotients{step} {tail}\n'
        text+=(f'theorem pivot{step} : decide (0 < (enclosure{step} 0 0).re - '
               f'((enclosure{step} 0 0).radius : Int)) = true := by decide +kernel\n')
        text+=(f'theorem step{step} : decide (∀ i j : Fin {n-step-1}, '
               f'schurEntryCheck 52 (enclosure{step} i.succ j.succ) '
               f'(enclosure{step} i.succ 0) (enclosure{step} j.succ 0) '
               f'(enclosure{step} 0 0) (products{step} i j) '
               f'(quotients{step} i j) (enclosure{step+1} i j) = true) = true := by decide +kernel\n')
        tailproof='rfl' if step+1==n else f'accepted{step+1}'
        text+=(f'theorem accepted{step} : schurAccepts 52 enclosure{step} proposal{step} = true :=\n'
               f'  Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨pivot{step},step{step}⟩,{tailproof}⟩\n')
    text+=f'end Maxwell.Certificate.GlobalSchurWitness.{prefix}\n'
    path=OUT/f'{prefix}Raw.lean'
    path.write_text(text)
    sound=(f'import Maxwell.Certificate.GlobalSchurWitness.{prefix}Raw\n'
           'import Maxwell.Certificate.DyadicKernelSchurSound\n'
           f'namespace Maxwell.Certificate.GlobalSchurWitness.{prefix}\n'
           'open DyadicKernel\nopen scoped ComplexOrder\n'
           f'theorem sound {{A : Matrix (Fin {n}) (Fin {n}) ℂ}} (hA : A.IsHermitian)\n'
           f'    (ha : MatrixContains 52 enclosure0 A) : A.PosDef :=\n'
           '  schurAccepts_posDef proposal0 accepted0 hA ha\n'
           f'end Maxwell.Certificate.GlobalSchurWitness.{prefix}\n')
    (OUT/f'{prefix}.lean').write_text(sound)
    evidence=ROOT/'evidence/global_schur_proposals'
    evidence.mkdir(exist_ok=True)
    meta={'input_sha256':sha256(source.read_bytes()).hexdigest(),
          'source_sha256':sha256(path.read_bytes()).hexdigest(),'dimension':n,
          'modules':[f'Maxwell.Certificate.GlobalSchurWitness.{prefix}Raw',
                     f'Maxwell.Certificate.GlobalSchurWitness.{prefix}'],
          'scope':'Untrusted proposals; generated Lean arithmetic acceptance required.'}
    (evidence/f'{prefix}.json').write_text(json.dumps(meta,indent=2)+'\n')
    (evidence/f'{prefix}_modules.json').write_text(json.dumps(meta['modules'],indent=2)+'\n')
    print(prefix,n,flush=True)

if __name__=='__main__':
    main()
