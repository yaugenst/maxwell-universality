# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Actual first-global inverse-X arithmetic using dependency-free definitions."""
from pathlib import Path
import json
import numpy as np
from generate_fft_stage_proposals import inverse_stages,conjugate
ROOT=Path(__file__).resolve().parent
coeff=json.loads((ROOT/'evidence/fft_stage_proposals/coefficients.json').read_text());roots=coeff['roots'];kernels={int(k):v for k,v in coeff['normalized_root_tables'].items()}
with np.load(ROOT/'evidence/global_center_proposals/record0000.npz') as a:
 source=np.array(a['curl'][:,0,0],dtype=object).reshape(20,10,10,3)*16
stages=inverse_stages(source,roots,kernels);before=stages[2];after=stages[3]
def rect(a):return '⟨'+','.join(str(int(v)) for v in a)+'⟩'
def seq(a):return '['+','.join(a)+']'
s='import Maxwell.Certificate.DyadicKernel\nnamespace Maxwell.Certificate.DyadicKernelPrototype\nopen DyadicKernel\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
s+='noncomputable def coefficients : List (List Rectangle) := '+seq([seq([rect(conjugate(kernels[20][i*j%20])) for j in range(20)]) for i in range(20)])+'\n'
for row in range(100):
 y,z=divmod(row,10)
 s+=f'noncomputable def input{row} : List Rectangle := '+seq([rect(before[x,y,z]) for x in range(20)])+'\n'
 s+=f'noncomputable def output{row} : List Rectangle := '+seq([rect(after[x,y,z]) for x in range(20)])+'\n'
 s+=f'theorem checked{row} : (coefficients.zip output{row}).all (fun co => dotCheck 52 (input{row}.zip co.1) co.2) = true := by decide +kernel\n'
s+='end Maxwell.Certificate.DyadicKernelPrototype\n'
(ROOT/'Maxwell/Certificate/DyadicKernelPrototype.lean').write_text(s)
