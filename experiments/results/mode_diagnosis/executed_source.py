#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=2,<3", "scipy>=1.14,<2", "threadpoolctl>=3,<4"]
# ///
"""Separate direct interactions and discarded defect modes using saved full data."""
import argparse
import json
from pathlib import Path

import numpy as np
from scipy.linalg import eigh, solve
from threadpoolctl import threadpool_limits

from maxwell import write_json


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case",type=Path,required=True)
    parser.add_argument("--tuned",type=Path,required=True)
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    args.output.mkdir(parents=True,exist_ok=False)
    (args.output/"executed_source.py").write_bytes(Path(__file__).read_bytes())
    arrays=np.load(args.case/"modal_data.npz")
    measured=json.loads((args.case/"modal_comparison.json").read_text())
    tuning=json.loads((args.tuned/"tuning.json").read_text())
    s,u=arrays["compressed"],arrays["modes"]
    n=len(s)//3
    if 3*n!=len(s):
        raise ValueError("Diagnostic requires the equal-support three-defect data")
    bases=[]
    with threadpool_limits(2):
        for site in range(3):
            lo,hi=site*n,(site+1)*n
            vals,vecs=eigh(s[lo:hi,lo:hi])
            port=int(np.argmax(abs(vecs.T@u[lo:hi,site])))
            order=[port]+[int(k) for k in np.argsort(-abs(vals)) if k!=port]
            vecs[:,port]*=np.sign(vecs[:,port]@u[lo:hi,site])
            bases.append(vecs[:,order])
        transformed=np.block([[bases[i].T@s[i*n:(i+1)*n,j*n:(j+1)*n]@bases[j]
                               for j in range(3)] for i in range(3)])
        rows=[]
        for label,strengths in (("local_design",measured["strengths"]),("calibrated_device",tuning["strengths"])):
            v=np.array(strengths)
            full=-s.copy()
            full.flat[::len(full)+1]+=np.repeat(1/v,n)
            exact=u.T@solve(full,u,assume_a="sym",overwrite_a=True,check_finite=False)
            effective=np.linalg.inv(exact)
            one_mode=np.diag(1/v)-u.T@s@u
            nearest=one_mode.copy()
            nearest[0,2]=nearest[2,0]=0
            direct_error=(nearest-one_mode)@exact
            discarded_error=(one_mode-effective)@exact
            context={"name":label,"strengths":v.tolist(),
                     "direct_contribution_three_port_equation_norm":float(np.linalg.norm(direct_error,2)),
                     "discarded_modes_contribution_three_port_equation_norm":float(np.linalg.norm(discarded_error,2)),
                     "combined_three_port_equation_norm":float(np.linalg.norm(direct_error+discarded_error,2)),
                     "discarded_mode_self_energy":(one_mode-effective).tolist(),"ranks":[]}
            for rank in (1,2,4,8,16,32,64,128,256,512,1024,n):
                if rank>n:
                    continue
                selected=np.concatenate([np.arange(rank)+i*n for i in range(3)])
                tr=-transformed[np.ix_(selected,selected)].copy()
                tr.flat[::len(tr)+1]+=np.repeat(1/v,rank)
                rhs=np.zeros((3*rank,3))
                rhs[np.arange(3)*rank,np.arange(3)]=1
                predicted=rhs.T@solve(tr,rhs,assume_a="sym",overwrite_a=True,check_finite=False)
                terminals=np.ix_([0,2],[0,2])
                alpha=measured["alpha"]
                gamma=np.array(measured["terminal_target_matrix"])
                item={"modes_per_defect":rank,"relative_three_port_response_error":float(np.linalg.norm(predicted-exact,2)/np.linalg.norm(exact,2)),
                      "terminal_equation_prediction_error":float(np.linalg.norm(alpha*gamma@(predicted-exact)[terminals],2)),
                      "model_terminal_equation_residual":float(np.linalg.norm(alpha*gamma@predicted[terminals]-np.eye(2),2))}
                context["ranks"].append(item)
                print(json.dumps({"design":label,**item}),flush=True)
            rows.append(context)
            write_json(args.output/"diagnosis.json",rows)


if __name__=="__main__":
    main()
