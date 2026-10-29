#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Share frozen input/output lines across five-point Fourier sums."""
import json
import numpy as np
import generate_fft_butterfly_prototype as g
prefix='LowerD0C00Butterfly'
data=np.load(g.g.EVIDENCE/f'{prefix}.npz')
mods=[]
for ax,before,after in [(2,'Input','First'),(1,'First','Second'),(0,'Third','Result')]:
    letter='XYZ'[ax];outer=10 if ax==0 else 20;n=20 if ax==0 else 10
    name=prefix+'Lines'+letter;check=prefix+'LineCheck'+letter
    point=['(j,a,b)','(a,j,b)','(a,b,j)'][ax]
    s=f'import Maxwell.Certificate.FFTWitness.{prefix}Proposal{letter}\nnamespace Maxwell.Certificate.FFTWitness\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
    for kind,field in [('Input',before),('Output',after)]:
        arr=data[field.lower()];rows=[]
        for a in range(outer):
            row=[]
            for b in range(10):
                sl=[a,b];sl.insert(ax,slice(None));row.append(g.vec([g.rect(x) for x in arr[tuple(sl)]]))
            rows.append(g.vec(row))
        nm=name+kind
        s+=f'noncomputable def {nm} : Fin {outer} → Fin 10 → Fin {n} → DyadicRectangle :=\n  {g.vec(rows)}\n'
        s+=f'''theorem {nm}_entries (a : Fin {outer}) (b : Fin 10) (j : Fin {n}) :
    {nm} a b j = {prefix}{field} {point} := by
  revert a b j
  decide +kernel

theorem {nm}_binding (a : Fin {outer}) (b : Fin 10) :
    {nm} a b = fun j => {prefix}{field} {point} :=
  funext ({nm}_entries a b)
'''
    s+='end Maxwell.Certificate.FFTWitness\n';(g.g.OUT/f'{name}.lean').write_text(s);mods.append(name)
    stem='twenty' if n==20 else 'ten'
    s=f'import Maxwell.Certificate.FFTWitness.{name}\nnamespace Maxwell.Certificate.FFTWitness\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
    for a in range(outer):
        s+=f'''theorem {check}{a:02}_literal (b : Fin 10) :
    DyadicButterfly.{stem}NormalizedCheck 52 1
      ({name}Input {a} b) ({prefix}Proposal{letter} {a} b)
      ({name}Output {a} b) = true := by
  revert b
  decide +kernel
'''
    s+=f'''theorem {check}_contains (v : Maxwell.Spectral.PrimitiveYee.Cell → ℂ)
    (hv : DyadicFFT.Contains 52 {prefix}{before} v) :
    DyadicFFT.Contains 52 {prefix}{after}
      (Matrix.mulVec (FourierBinding.axis{letter} (FourierBinding.cyclicFourier {n}).conjTranspose) v) := by
  apply DyadicButterflyFFT.axis{letter}Inverse_sound {prefix}Proposal{letter} hv
  intro a b
  apply DyadicButterflyFFT.{stem}NormalizedCheck_transfer
    ({name}Input_binding a b) ({name}Output_binding a b)
  fin_cases a
'''
    s+=''.join(f'  · exact {check}{a:02}_literal b\n' for a in range(outer))
    s+='end Maxwell.Certificate.FFTWitness\n';(g.g.OUT/f'{check}.lean').write_text(s);mods.append(check)
(g.g.EVIDENCE/'butterfly_lines_modules.json').write_text(json.dumps(['Maxwell.Certificate.FFTWitness.'+m for m in mods],indent=2)+'\n')
print('Generated shared per-line prototype modules.')
