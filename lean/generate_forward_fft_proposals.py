#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Freeze forward-FFT inputs from material division and existing weighted outputs.

All intermediate data are proposals; generated integer checks provide the
acceptance evidence. This does not invoke or assume native acceptance.
"""
import importlib.util,json
from pathlib import Path
import numpy as np
import generate_fft_stage_proposals as g

ROOT=g.ROOT
OUT=g.OUT
EVIDENCE=g.EVIDENCE


def forward_stages(a, roots, kernels):
    k20=[[kernels[20][i*j%20] for j in range(20)] for i in range(20)]
    k10=[[kernels[10][2*i*j%20] for j in range(10)] for i in range(10)]
    first=g.axis_stage(a,0,k20)
    second=np.empty_like(a)
    for x in range(20):
        for y in range(10):
            for z in range(10):
                second[x,y,z]=g.round_dot([(first[x,y,z],roots[x*(y+z)%20])])
    third=g.axis_stage(second,1,k10)
    result=g.axis_stage(third,2,k10)
    return first,second,third,result


def checks(prefix):
    modules=[]
    for axis,before,after,n in [('X','Input','First',20),('T','First','Second',1),
                              ('Y','Second','Third',10),('Z','Third','Result',10)]:
        name=f'{prefix}Check{axis}Blocks'
        s=f'''import Maxwell.Certificate.FFTWitness.{prefix}{before}
import Maxwell.Certificate.FFTWitness.{prefix}{after}
namespace Maxwell.Certificate.FFTWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0

'''
        for x in range(20):
            point=f'({x},y,z)'
            if axis=='T':
                expression=f'DyadicRectangle.rescaleCheck 52 52 (DyadicRectangle.mulExact ({prefix}{before} {point}) (twiddle {point})) ({prefix}{after} {point})'
            else:
                row={'X':str(x),'Y':'y','Z':'z'}[axis]
                src={'X':'(j,y,z)','Y':f'({x},j,z)','Z':f'({x},y,j)'}[axis]
                expression=f'DyadicRectangle.dotCheck 52 52 (fun j : Fin {n} => {prefix}{before} {src}) (fun j => kernel{n} {row} j) ({prefix}{after} {point})'
            s+=f'''theorem {prefix}Check{axis}X{x:02}_accepted (y z : Fin 10) :
    {expression} = true := by
  revert y z
  decide +kernel

'''
        s+='end Maxwell.Certificate.FFTWitness\n'
        (OUT/f'{name}.lean').write_text(s)
        modules.append(name)
    return modules


def complete(prefix):
    name=f'{prefix}Complete'
    s='import Maxwell.Certificate.FFTWitness.Constants\nimport Maxwell.Certificate.DyadicFFTRows\n'
    s+=''.join(f'import Maxwell.Certificate.FFTWitness.{prefix}Check{a}Blocks\n' for a in ['X','T','Y','Z'])
    s+=f'import Maxwell.Certificate.FFTWitness.{prefix}NativeCheck\n'
    s+=f'''
namespace Maxwell.Certificate.FFTWitness
open Matrix FourierBinding Maxwell.Spectral.PrimitiveYee
noncomputable def {prefix}Proposal : DyadicFFT.Proposal :=
  ⟨{prefix}First,{prefix}Second,{prefix}Third,{prefix}Result⟩

theorem {prefix}_accepted : DyadicFFT.forwardCheck 52 52 kernel20 kernel10 twiddle
    {prefix}Input {prefix}Proposal = true := by
  apply DyadicFFT.forwardCheck_of_stages
'''
    for axis in ['X','T','Y','Z']:
        lemma='diagonalCheck_of_rows' if axis=='T' else f'axis{axis}Check_of_rows'
        s+=f'  · apply DyadicFFT.{lemma}\n    rintro ⟨x,y,z⟩\n    fin_cases x\n'
        s+=''.join(f'    · exact {prefix}Check{axis}X{x:02}_accepted y z\n' for x in range(20))
    s+=f'''
theorem {prefix}_forward_contains (v : Cell → ℂ)
    (hv : DyadicFFT.Contains 52 {prefix}Input v) :
    DyadicFFT.Contains 52 {prefix}Result ((transform 0).conjTranspose *ᵥ v) :=
  checked_forward _ _ _ hv {prefix}_accepted

theorem {prefix}_native_forward_contains (v : Cell → ℂ)
    (hv : DyadicFFT.Contains 52 {prefix}Input v) :
    DyadicFFT.Contains 52 {prefix}Native ((transform 0).conjTranspose *ᵥ v) := by
  intro r
  exact DyadicRectangle.subsetCheck_sound ({prefix}NativeCheck_accepted r.1 r.2.1 r.2.2)
    ({prefix}_forward_contains v hv r)
end Maxwell.Certificate.FFTWitness
'''
    (OUT/f'{name}.lean').write_text(s)
    return name


def main():
    co=json.loads((EVIDENCE/'coefficients.json').read_text())
    roots=co['roots']
    kernels={int(n):v for n,v in co['normalized_root_tables'].items()}
    native_path=ROOT.parent/'certificates/yee/work/bulk/edge_isolation/interval_tools.py'
    spec=importlib.util.spec_from_file_location('interval_tools',native_path)
    native=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(native)
    modules=[]
    summary=[]
    for label in ['Lower','Upper']:
        source=np.load(ROOT/f'evidence/point_inertia_proposals/{label.lower()}.npz')
        inverse=np.load(EVIDENCE/f'{label.lower()}.npz')['native']
        material=native.material(inverse,source['material_den'])
        saved={name:np.zeros_like(material) for name in ['input','first','second','third','result']}
        saved['native']=source['weighted']
        for d in range(3):
            for col in range(28):
                prefix=f'{label}ForwardD{d}C{col:02}'
                a=material[:,d,col,:].reshape(20,10,10,3)
                for name,values in zip(['input','first','second','third','result'],(a,*forward_stages(a,roots,kernels)),strict=True):
                    saved[name][:,d,col,:]=values.reshape(2000,3)
                    modules.append(g.emit_field(prefix,name.title(),values))
                modules.append(g.emit_field(prefix,'Native',source['weighted'][:,d,col,:].reshape(20,10,10,3)))
                modules.append(g.emit_native_check(prefix))
                modules.extend(checks(prefix))
                modules.append(complete(prefix))
        target=EVIDENCE/f'{label.lower()}_forward.npz'
        np.savez_compressed(target,**saved)
        needed=np.max(np.abs(saved['result'][...,:2]-saved['native'][...,:2]),axis=-1)+saved['result'][...,2]
        summary.append({'label':label,'included_count':int((needed<=saved['native'][...,2]).sum()),
                        'total':needed.size,'max_radius_shortfall':int((needed-saved['native'][...,2]).max())})
    (EVIDENCE/'forward_modules.json').write_text(json.dumps([f'Maxwell.Certificate.FFTWitness.{m}' for m in modules],indent=2)+'\n')
    (EVIDENCE/'forward_comparison.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))


if __name__=='__main__': main()
