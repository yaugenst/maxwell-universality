#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Emit shared-literal-list proofs for the existing frozen FFT stages.

The proposed values are unchanged. Each input list is kernel-bound to the
original coordinate table once, then reused by every output on that line.
"""
from pathlib import Path
import argparse
import json
import numpy as np

ROOT=Path(__file__).resolve().parent
OUT=ROOT/'Maxwell/Certificate/FFTWitness'
EVIDENCE=ROOT/'evidence/fft_stage_proposals'
FORWARD=False

def mapping(axis):
    return ({'X':('Input','First',20),'Y':('Second','Third',10),'Z':('Third','Result',10)} if FORWARD else
            {'X':('Third','Result',20),'Y':('First','Second',10),'Z':('Input','First',10)})[axis]

def constants_name(): return 'ForwardListConstants' if FORWARD else 'ListConstants'
def coefficients_name(): return 'forwardCoefficients' if FORWARD else 'inverseCoefficients'


def lit(a):return f'⟨{int(a[0])}, {int(a[1])}, {int(a[2])}⟩'
def vec(a):return '!['+', '.join(a)+']'
def lst(a):return '['+', '.join(lit(x) for x in a)+']'


def constants():
    data=json.loads((EVIDENCE/'coefficients.json').read_text())['normalized_root_tables']
    s='import Maxwell.Certificate.FFTWitness.ConstantsData\nimport Maxwell.Certificate.DyadicListRows\n\nnamespace Maxwell.Certificate.FFTWitness\nset_option maxRecDepth 100000\n\n'
    for n in [10,20]:
        k=data[str(n)]
        rows=[[(k[(20//n)*a*b%20][0],(1 if FORWARD else -1)*k[(20//n)*a*b%20][1],k[(20//n)*a*b%20][2]) for b in range(n)] for a in range(n)]
        s+=f'noncomputable def {coefficients_name()}{n} : Fin {n} → List DyadicRectangle := {vec([lst(row) for row in rows])}\n\n'
        s+=f'''theorem {coefficients_name()}{n}_binding (a : Fin {n}) : {coefficients_name()}{n} a =
    List.ofFn (fun b : Fin {n} => {'kernel'+str(n)+' a b' if FORWARD else '(kernel'+str(n)+' b a).conjugate'}) := by
  revert a
  decide +kernel

'''
    s+='end Maxwell.Certificate.FFTWitness\n'
    (OUT/f'{constants_name()}.lean').write_text(s)


def input_lists(prefix,axis,field,data):
    name=f'{prefix}ListInput{axis}'
    before=mapping(axis)[0]
    if axis=='X':
        a,b,n=10,10,20
        values=[[data[:,i,j,:] for j in range(b)] for i in range(a)]
        point='(j,a,b)'
    elif axis=='Y':
        a,b,n=20,10,10
        values=[[data[i,:,j,:] for j in range(b)] for i in range(a)]
        point='(a,j,b)'
    else:
        a,b,n=20,10,10
        values=[[data[i,j,:,:] for j in range(b)] for i in range(a)]
        point='(a,b,j)'
    table=vec([vec([lst(row) for row in block]) for block in values])
    s=f'''import Maxwell.Certificate.FFTWitness.{prefix}{before}
import Maxwell.Certificate.FFTWitness.{constants_name()}

namespace Maxwell.Certificate.FFTWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def {name} : Fin {a} → Fin {b} → List DyadicRectangle :=
  {table}

theorem {name}_binding (a : Fin {a}) (b : Fin {b}) :
    {name} a b = List.ofFn (fun j : Fin {n} => {prefix}{before} {point}) := by
  revert a b
  decide +kernel

end Maxwell.Certificate.FFTWitness
'''
    (OUT/f'{name}.lean').write_text(s)
    return name


def checks(prefix,axis):
    before,after,n=mapping(axis)
    input_name=f'{prefix}ListInput{axis}'
    name=f'{prefix}ListCheck{axis}Blocks'
    s=f'''import Maxwell.Certificate.FFTWitness.{input_name}
import Maxwell.Certificate.FFTWitness.{prefix}{after}

namespace Maxwell.Certificate.FFTWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0

'''
    for x in range(20):
        args={'X':'y z','Y':f'{x} z','Z':f'{x} y'}[axis]
        row={'X':str(x),'Y':'y','Z':'z'}[axis]
        src={'X':'(j,y,z)','Y':f'({x},j,z)','Z':f'({x},y,j)'}[axis]
        nm=f'{prefix}ListCheck{axis}X{x:02}'
        s+=f'''theorem {nm}_literal (y z : Fin 10) :
    DyadicRectangle.listDotCheck 52 52
      (({input_name} {args}).zip ({coefficients_name()}{n} {row}))
      ({prefix}{after} ({x},y,z)) = true := by
  revert y z
  decide +kernel

theorem {nm}_accepted (y z : Fin 10) :
    DyadicRectangle.dotCheck 52 52 (fun j : Fin {n} => {prefix}{before} {src})
      (fun j => {'kernel'+str(n)+' '+row+' j' if FORWARD else '(kernel'+str(n)+' j '+row+').conjugate'}) ({prefix}{after} ({x},y,z)) = true :=
  DyadicRectangle.dotCheck_of_zip ({input_name}_binding {args})
    ({coefficients_name()}{n}_binding {row}) ({nm}_literal y z)

'''
    s+='end Maxwell.Certificate.FFTWitness\n'
    (OUT/f'{name}.lean').write_text(s)
    return name


def complete(prefix):
    old=(OUT/f'{prefix}Complete.lean').read_text()
    s=old
    for axis in ['X','Y','Z']:
        s=s.replace(f'{prefix}Check{axis}',f'{prefix}ListCheck{axis}')
    s=s.replace(f'{prefix}Proposal',f'{prefix}ListProposal')
    s=s.replace(f'{prefix}_accepted',f'{prefix}_list_accepted')
    s=s.replace(f'{prefix}_inverse_contains',f'{prefix}_list_inverse_contains')
    s=s.replace(f'{prefix}_native_inverse_contains',f'{prefix}_list_native_inverse_contains')
    s=s.replace(f'{prefix}_forward_contains',f'{prefix}_list_forward_contains')
    s=s.replace(f'{prefix}_native_forward_contains',f'{prefix}_list_native_forward_contains')
    name=f'{prefix}ListComplete'
    (OUT/f'{name}.lean').write_text(s)
    return name


def main():
    global FORWARD
    parser=argparse.ArgumentParser()
    parser.add_argument('--forward',action='store_true')
    FORWARD=parser.parse_args().forward
    constants()
    modules=[constants_name()]
    for label in ['Lower','Upper']:
        data=np.load(EVIDENCE/f"{label.lower()}{'_forward' if FORWARD else ''}.npz")
        for d in range(3):
            for c in range(28):
                prefix=f"{label}{'Forward' if FORWARD else ''}D{d}C{c:02}"
                modules.extend(f'{prefix}{field}' for field in ['Input','First','Second','Third','Result','Native'])
                modules.append(f'{prefix}NativeCheck')
                for axis in (['X','Y','Z'] if FORWARD else ['Z','Y','X']):
                    field=mapping(axis)[0].lower()
                    modules.append(input_lists(prefix,axis,field,data[field][:,d,c,:].reshape(20,10,10,3)))
                    modules.append(checks(prefix,axis))
                modules.append(f'{prefix}CheckTBlocks')
                modules.append(complete(prefix))
    if FORWARD:
        (EVIDENCE/'forward_list_modules.json').write_text(json.dumps([f'Maxwell.Certificate.FFTWitness.{m}' for m in modules],indent=2)+'\n')
        print(f'Generated {len(modules)} forward list-based modules.')
        return
    s=(OUT/'InverseComplete.lean').read_text()
    for label in ['Lower','Upper']:
        for d in range(3):
            for c in range(28):
                prefix=f"{label}{'Forward' if FORWARD else ''}D{d}C{c:02}"
                s=s.replace(f'{prefix}Complete',f'{prefix}ListComplete')
                s=s.replace(f'{prefix}_native_inverse_contains',f'{prefix}_list_native_inverse_contains')
    s=s.replace(f'{prefix}_forward_contains',f'{prefix}_list_forward_contains')
    s=s.replace(f'{prefix}_native_forward_contains',f'{prefix}_list_native_forward_contains')
    s=s.replace('curlInput','listCurlInput').replace('inverseCurl','listInverseCurl').replace('PointLabel','ListPointLabel')
    (OUT/'InverseListComplete.lean').write_text(s)
    modules.append('InverseListComplete')
    (EVIDENCE/'list_modules.json').write_text(json.dumps([f'Maxwell.Certificate.FFTWitness.{m}' for m in modules],indent=2)+'\n')
    print(f'Generated {len(modules)} list-based modules; proposed stage values unchanged.')


if __name__=='__main__': main()
