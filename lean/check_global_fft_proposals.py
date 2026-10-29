# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy==2.3.5"]
# ///
"""Diagnostic only: regenerate first-record FFTs at verified p52 precision."""
import json,time
from pathlib import Path
import numpy as np
from generate_fft_stage_proposals import inverse_stages
from generate_forward_fft_proposals import forward_stages
ROOT=Path(__file__).resolve().parent
coeff=json.loads((ROOT/'evidence/fft_stage_proposals/coefficients.json').read_text())
roots=coeff['roots'];kernels={int(k):v for k,v in coeff['normalized_root_tables'].items()}
records=[]
with np.load(ROOT/'evidence/global_center_proposals/record0000.npz') as saved:
 for prefix in ['', 'axis0_', 'axis0_gradient_']:
  for inverse,inp,out in [(True,prefix+'curl',prefix+'inverse'),(False,prefix+'spatial',prefix+'weighted')]:
   start=time.monotonic();a=np.array(saved[inp][:,0,0],dtype=object).reshape(20,10,10,3)*16
   target=np.array(saved[out][:,0,0],dtype=object).reshape(20,10,10,3)*16
   result=(inverse_stages if inverse else forward_stages)(a,roots,kernels)[-1]
   slack=np.minimum(target[...,2]-np.abs(result[...,0]-target[...,0])-result[...,2],target[...,2]-np.abs(result[...,1]-target[...,1])-result[...,2])
   records.append({'input':inp,'output':out,'minimum_dyadic_slack':int(slack.min()),'contained_rows':int((slack>=0).sum()),'seconds':time.monotonic()-start})
   print(json.dumps(records[-1]),flush=True)
(ROOT/'evidence/global_center_proposals/fft_prototype_diagnostic.json').write_text(json.dumps({'proof_status':'untrusted diagnostic; kernel checks still required','results':records},indent=2)+'\n')
