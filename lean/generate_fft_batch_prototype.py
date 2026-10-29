#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Propose list-streaming direct FFT checks with no repeated cell lookup."""
import json,numpy as np
import generate_fft_stage_proposals as g
co=json.loads((g.EVIDENCE/'coefficients.json').read_text())['normalized_root_tables']
def lit(a):return f'⟨{int(a[0])}, {int(a[1])}, {int(a[2])}⟩'
def lst(xs):return '['+', '.join(xs)+']'
s='import Maxwell.Certificate.FFTWitness.ConstantsData\nimport Maxwell.Certificate.DyadicFFTBatch\nnamespace Maxwell.Certificate.FFTWitness\nset_option maxRecDepth 100000\n'
for n in [10,20]:
 k=co[str(n)];rows=[lst([lit([k[(20//n)*a*b%20][0],-k[(20//n)*a*b%20][1],k[(20//n)*a*b%20][2]]) for b in range(n)]) for a in range(n)]
 s+=f'''noncomputable def inverseBatch{n} : List (List DyadicRectangle) := {lst(rows)}
theorem inverseBatch{n}_binding : inverseBatch{n} =
    List.ofFn (fun a : Fin {n} => List.ofFn (fun b : Fin {n} => (kernel{n} b a).conjugate)) := by
  decide +kernel
'''
s+='end Maxwell.Certificate.FFTWitness\n';(g.OUT/'BatchConstants.lean').write_text(s)
mods=['BatchConstants'];prefix='LowerD0C00';data=np.load(g.EVIDENCE/'lower.npz')
for axis,before,after,n,ax in [('X','Third','Result',20,0),('Y','First','Second',10,1),('Z','Input','First',10,2)]:
 outer=10 if ax==0 else 20;name=prefix+'BatchRows'+axis;check=prefix+'BatchCheck'+axis
 arrays=[data[field.lower()][:,0,0,:].reshape(20,10,10,3) for field in [before,after]]
 blocks=[]
 for a in range(outer):
  lines=[]
  for b in range(10):
   sl=[a,b];sl.insert(ax,slice(None));lines.append('('+', '.join(lst([lit(r) for r in arr[tuple(sl)]]) for arr in arrays)+')')
  blocks.append(lst(lines))
 point=['(j,a,b)','(a,j,b)','(a,b,j)'][ax]
 s=f'''import Maxwell.Certificate.FFTWitness.{prefix}{before}
import Maxwell.Certificate.FFTWitness.{prefix}{after}
import Maxwell.Certificate.FFTWitness.BatchConstants
namespace Maxwell.Certificate.FFTWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def {name}Blocks : Fin {outer} → List DyadicRectangle.LineData :=
  ![{', '.join(blocks)}]
noncomputable def {name} : List (List DyadicRectangle.LineData) := List.ofFn {name}Blocks
theorem {name}_binding : {name} =
    List.ofFn (fun a : Fin {outer} => List.ofFn (fun b : Fin 10 =>
      (List.ofFn (fun j : Fin {n} => {prefix}{before} {point}),
       List.ofFn (fun j : Fin {n} => {prefix}{after} {point})))) := by
  decide +kernel
end Maxwell.Certificate.FFTWitness
'''
 (g.OUT/f'{name}.lean').write_text(s);mods.append(name)
 xyz=['y z x','x z y','x y z'][ax]
 s=f'''import Maxwell.Certificate.FFTWitness.{name}
import Maxwell.Certificate.FFTWitness.Constants
import Maxwell.Certificate.DyadicFFTRows
namespace Maxwell.Certificate.FFTWitness
set_option maxRecDepth 100000
set_option maxHeartbeats 0

{''.join(f'theorem {check}Block{i:02} : DyadicRectangle.blockCheck 52 52 inverseBatch{n} ({name}Blocks {i}) = true := by\n  decide +kernel\n' for i in range(outer))}
theorem {check}_literal : DyadicRectangle.batchCheck 52 52 inverseBatch{n} {name} = true := by
  apply DyadicRectangle.batchCheck_of_blocks
  intro i
  fin_cases i
{''.join(f'  · exact {check}Block{i:02}\n' for i in range(outer))}
theorem {check}_accepted : DyadicFFT.axis{axis}Check 52 52 (DyadicFFT.adjoint kernel{n})
    {prefix}{before} {prefix}{after} = true := by
  apply DyadicFFT.axis{axis}Check_of_rows
  rintro ⟨x,y,z⟩
  exact DyadicRectangle.batchCheck_sound {name}_binding inverseBatch{n}_binding
    {check}_literal {xyz}
end Maxwell.Certificate.FFTWitness
'''
 (g.OUT/f'{check}.lean').write_text(s);mods.append(check)
(g.EVIDENCE/'batch_prototype_modules.json').write_text(json.dumps(['Maxwell.Certificate.FFTWitness.'+m for m in mods],indent=2)+'\n')
print('Generated7 list-streaming prototype modules.')
