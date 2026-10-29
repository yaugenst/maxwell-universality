#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Propose actual mixed-radix stages; Lean decides every integer check."""
from pathlib import Path
import argparse,json
import numpy as np
import generate_fft_stage_proposals as g

co=json.loads((g.EVIDENCE/'coefficients.json').read_text())
roots=co['roots']; norms={int(n):v for n,v in co['normalizations'].items()}

def neg(a):return [-int(a[0]),-int(a[1]),int(a[2])]
def conj(a):return [int(a[0]),-int(a[1]),int(a[2])]
def transform10(a,sign):
    ev=[g.round_dot([(a[2*j],roots[(4*sign*k*j)%20]) for j in range(5)]) for k in range(5)]
    od=[g.round_dot([(a[2*j+1],roots[(4*sign*k*j)%20]) for j in range(5)]) for k in range(5)]
    out=[g.round_dot([(ev[k%5],[2**52,0,0]),(neg(od[k%5]) if k>=5 else od[k%5],roots[2*sign*(k%5)%20])]) for k in range(10)]
    return ev,od,out

def transform20(a,sign):
    ev=transform10(a[::2],sign);od=transform10(a[1::2],sign)
    out=[g.round_dot([(ev[2][k%10],[2**52,0,0]),(neg(od[2][k%10]) if k>=10 else od[2][k%10],roots[sign*(k%10)%20])]) for k in range(20)]
    return ev,od,out

def axis(a,ax,sign):
    b=np.empty_like(a);n=a.shape[ax];proposals={}
    for i in np.ndindex(*(a.shape[j] for j in range(3) if j!=ax)):
        sl=list(i);sl.insert(ax,slice(None));sl=tuple(sl)
        t=(transform10 if n==10 else transform20)(a[sl],sign)
        proposals[i]=t
        b[sl]=[g.round_dot([(x,norms[n])]) for x in t[2]]
    return b,proposals

def vec(xs):return '!['+', '.join(xs)+']'
def rect(x):return f'⟨{int(x[0])}, {int(x[1])}, {int(x[2])}⟩'
def ten(t):return '⟨'+', '.join(vec([rect(x) for x in a]) for a in t)+'⟩'
def twenty(t):return f'⟨{ten(t[0])}, {ten(t[1])}, {vec([rect(x) for x in t[2]])}⟩'

def emit_axis(prefix,ax,before,after,proposals,sign):
    letter='XYZ'[ax];n=20 if ax==0 else 10;outer=10 if ax==0 else 20
    typename='TwentyProposal' if ax==0 else 'TenProposal';printer=twenty if ax==0 else ten
    name=f'{prefix}Proposal{letter}';check=f'{prefix}Check{letter}'
    source=vec([vec([printer(proposals[a,b]) for b in range(10)]) for a in range(outer)])
    s=f'''import Maxwell.Certificate.FFTWitness.{prefix}{before}
import Maxwell.Certificate.FFTWitness.{prefix}{after}
import Maxwell.Certificate.DyadicButterflyFFT
namespace Maxwell.Certificate.FFTWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def {name} : Fin {outer} → Fin 10 → DyadicButterfly.{typename} :=
  {source}
end Maxwell.Certificate.FFTWitness
'''
    (g.OUT/f'{name}.lean').write_text(s)
    s=f'''import Maxwell.Certificate.FFTWitness.{name}
namespace Maxwell.Certificate.FFTWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
'''
    point=['(j,a,b)','(a,j,b)','(a,b,j)'][ax];stem='twenty' if ax==0 else 'ten'
    for a in range(outer):
        fixedpoint=point.replace('a',str(a))
        s+=f'''
theorem {check}{a:02}_accepted (b : Fin 10) :
    DyadicButterfly.{stem}NormalizedCheck 52 ({sign})
      (fun j => {prefix}{before} {fixedpoint}) ({name} {a} b)
      (fun j => {prefix}{after} {fixedpoint}) = true := by
  revert b
  decide +kernel
'''
    s+=f'''
theorem {check}_contains (v : Maxwell.Spectral.PrimitiveYee.Cell → ℂ)
    (hv : DyadicFFT.Contains 52 {prefix}{before} v) :
    DyadicFFT.Contains 52 {prefix}{after}
      (Matrix.mulVec (FourierBinding.axis{letter} ((FourierBinding.cyclicFourier {n}){'.conjTranspose' if sign==1 else ''})) v) := by
  apply DyadicButterflyFFT.axis{letter}{'Inverse' if sign==1 else 'Forward'}_sound {name} hv
  intro a b
  fin_cases a
'''
    s+=''.join(f'  · exact {check}{a:02}_accepted b\n' for a in range(outer))
    s+='end Maxwell.Certificate.FFTWitness\n'
    (g.OUT/f'{check}.lean').write_text(s)
    return [name,check]

def emit_complete(prefix,forward):
    before,after=('First','Second') if forward else ('Second','Third')
    name=prefix+'CheckT';mode='forward' if forward else 'inverse'
    tw='twiddle' if forward else 'DyadicFFT.conjugate twiddle'
    s=f"import Maxwell.Certificate.FFTWitness.{prefix}{before}\nimport Maxwell.Certificate.FFTWitness.{prefix}{after}\nimport Maxwell.Certificate.DyadicFFTRows\nnamespace Maxwell.Certificate.FFTWitness\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
    for x in range(20):
        t=f'(twiddle ({x},y,z))' if forward else f'((twiddle ({x},y,z)).conjugate)'
        s+=f"theorem {name}{x:02} (y z : Fin 10) : DyadicRectangle.rescaleCheck 52 52 (DyadicRectangle.mulExact ({prefix}{before} ({x},y,z)) {t}) ({prefix}{after} ({x},y,z)) = true := by\n  revert y z\n  decide +kernel\n"
    s+=f"theorem {name}_accepted : DyadicFFT.diagonalCheck 52 52 ({tw}) {prefix}{before} {prefix}{after} = true := by\n  apply DyadicFFT.diagonalCheck_of_rows\n  rintro ⟨x,y,z⟩\n  fin_cases x\n"
    s+=''.join(f'  · exact {name}{x:02} y z\n' for x in range(20))
    s+='end Maxwell.Certificate.FFTWitness\n';(g.OUT/f'{name}.lean').write_text(s)
    complete=prefix+'Complete'
    s=''.join(f'import Maxwell.Certificate.FFTWitness.{prefix}Check{a}\n' for a in ['X','Y','Z','T'])
    s+=f'import Maxwell.Certificate.FFTWitness.{prefix}NativeCheck\nnamespace Maxwell.Certificate.FFTWitness\nopen Matrix FourierBinding Maxwell.Spectral.PrimitiveYee\n'
    target='(transform 0).conjTranspose' if forward else 'transform 0'
    s+=f"theorem {prefix}_{mode}_contains (v : Cell → ℂ) (hv : DyadicFFT.Contains 52 {prefix}Input v) :\n    DyadicFFT.Contains 52 {prefix}Result (({target}) *ᵥ v) :=\n  DyadicButterflyFFT.{mode}_compose hv\n"
    if forward:s+=f'    {prefix}CheckX_contains {prefix}CheckT_accepted {prefix}CheckY_contains {prefix}CheckZ_contains\n'
    else:s+=f'    {prefix}CheckZ_contains {prefix}CheckY_contains {prefix}CheckT_accepted {prefix}CheckX_contains\n'
    s+=f"theorem {prefix}_native_{mode}_contains (v : Cell → ℂ) (hv : DyadicFFT.Contains 52 {prefix}Input v) :\n    DyadicFFT.Contains 52 {prefix}Native (({target}) *ᵥ v) := by\n  intro r\n  exact DyadicRectangle.subsetCheck_sound ({prefix}NativeCheck_accepted r.1 r.2.1 r.2.2)\n    ({prefix}_{mode}_contains v hv r)\nend Maxwell.Certificate.FFTWitness\n"
    (g.OUT/f'{complete}.lean').write_text(s)
    return [name,complete]

def main():
    p=argparse.ArgumentParser();p.add_argument('--forward',action='store_true');p.add_argument('--label',default='Lower');p.add_argument('--direction',type=int,default=0);p.add_argument('--column',type=int,default=0)
    args=p.parse_args();sign=-1 if args.forward else 1
    base=f"{args.label}{'Forward' if args.forward else ''}D{args.direction}C{args.column:02}";prefix=base+'Butterfly'
    data=np.load(g.EVIDENCE/f"{args.label.lower()}{'_forward' if args.forward else ''}.npz")
    a=data['input'][:,args.direction,args.column,:].reshape(20,10,10,3)
    modules=[]
    for field in ['Input','Native']:
        (g.OUT/f'{prefix}{field}.lean').write_text(f'import Maxwell.Certificate.FFTWitness.{base}{field}\nnamespace Maxwell.Certificate.FFTWitness\nnoncomputable def {prefix}{field} := {base}{field}\nend Maxwell.Certificate.FFTWitness\n')
        modules.append(prefix+field)
    if args.forward:
        first,px=axis(a,0,sign)
        second=np.empty_like(a)
        for x,y,z in np.ndindex(20,10,10):second[x,y,z]=g.round_dot([(first[x,y,z],roots[x*(y+z)%20])])
        third,py=axis(second,1,sign);result,pz=axis(third,2,sign)
        stages=[(0,'Input','First',px),(1,'Second','Third',py),(2,'Third','Result',pz)]
    else:
        first,pz=axis(a,2,sign);second,py=axis(first,1,sign);third=np.empty_like(a)
        for x,y,z in np.ndindex(20,10,10):third[x,y,z]=g.round_dot([(second[x,y,z],conj(roots[x*(y+z)%20]))])
        result,px=axis(third,0,sign)
        stages=[(2,'Input','First',pz),(1,'First','Second',py),(0,'Third','Result',px)]
    np.savez_compressed(g.EVIDENCE/f'{prefix}.npz',input=a,first=first,second=second,third=third,result=result)
    for field,values in zip(['First','Second','Third','Result'],[first,second,third,result]):
        modules.append(g.emit_field(prefix,field,values))
    modules.append(g.emit_native_check(prefix))
    for ax,before,after,prop in stages:modules+=emit_axis(prefix,ax,before,after,prop,sign)
    modules+=emit_complete(prefix,args.forward)
    target=data['native'][:,args.direction,args.column,:].reshape(20,10,10,3)
    needed=np.max(np.abs(result[...,:2]-target[...,:2]),axis=-1)+result[...,2]
    summary={'prefix':prefix,'included':int((needed<=target[...,2]).sum()),'total':2000,'min_slack':int((target[...,2]-needed).min())}
    (g.EVIDENCE/(prefix+'_modules.json')).write_text(json.dumps(['Maxwell.Certificate.FFTWitness.'+m for m in modules],indent=2)+'\n')
    print(json.dumps(summary))

if __name__=='__main__':main()
