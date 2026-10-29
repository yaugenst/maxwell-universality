#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=2,<3", "scipy>=1.14,<2", "threadpoolctl>=3,<4"]
# ///
"""Refine material tuning by full Maxwell solves, keeping source and decoder fixed."""
import argparse
from dataclasses import replace
import json
from pathlib import Path
import shutil

import numpy as np
from threadpoolctl import threadpool_limits

from device import frozen_probes, spectral_probes, verify_device
from maxwell import Config, Experiment, write_json


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--background",type=Path,required=True)
    p.add_argument("--design",type=Path,nargs="+",required=True)
    p.add_argument("--output",type=Path,required=True)
    p.add_argument("--calibration-h",type=float,default=1/6)
    p.add_argument("--verify-h",type=float,nargs="+",default=[2/13,1/7])
    p.add_argument("--source-interpolation",choices=("cubic","spectral"),default="cubic")
    p.add_argument("--order",type=int,choices=(8,10,12))
    args=p.parse_args()
    args.output.mkdir(parents=True,exist_ok=False)
    for source in (Path(__file__),Path(__file__).with_name("maxwell.py"),Path(__file__).with_name("device.py")):
        (args.output/f"executed_{source.name}").write_bytes(source.read_bytes())
    cfg=Config(**json.loads((args.background/"metadata.json").read_text())["config"])
    if cfg.order==2 or cfg.absorption:
        raise ValueError("Material-gradient calibration requires a real, directly sampled scalar medium")
    reference=Experiment(cfg,args.output/"source_reference")
    operator_cfg=replace(cfg,order=args.order or cfg.order)
    model=np.load(args.background/"background.npz")
    sample_probes=spectral_probes if args.source_interpolation=="spectral" else frozen_probes
    rows=[]
    with threadpool_limits(2):
        for path in args.design:
            design=json.loads(path.read_text())
            target=np.array(design["target"])
            nominal=np.array(design["strengths"])
            alpha=design["alpha"]
            terminals=list(range(len(target)))
            ex=Experiment(replace(operator_cfg,h=args.calibration_h),args.output/design["name"]/"calibration")
            probes=sample_probes(ex,reference,model["background_modes"],model["eigenvalues"])
            maximum=(25-(7+ex.mode.ec-cfg.detuning+7*cfg.rho))*np.e
            history=[]

            def evaluate(v):
                name=f"evaluation_{len(history)}"
                result=verify_device(ex,probes,v,alpha,target,terminals,
                                     nominal_strengths=nominal,name=name)
                field=np.load(ex.output/f"{name}_fields.npz")["fields"]
                error=target@np.array(result["decoded_response_real"])-np.eye(len(target))
                history.append({"name":name,"strengths":v.tolist(),
                                "equation_operator_error":result["worst_relative_equation_residual"],
                                "frobenius_equation_error":float(np.linalg.norm(error))})
                print(json.dumps({"target_name":design["name"],**history[-1]}),flush=True)
                return result,field,error,name

            strengths=nominal.copy()
            measured,fields,error,name=evaluate(strengths)
            reason="Maximum of eight material Newton steps reached"
            for step_number in range(8):
                if np.linalg.norm(error,2)<1e-7:
                    reason="Full Maxwell calibration reached 1e-7 equation tolerance"
                    break
                jac=np.column_stack([(target@(fields.T@(w[:,None]*fields))/alpha).ravel()
                                     for w in ex.edge_wells])
                step=np.linalg.lstsq(jac,-error.ravel(),rcond=None)[0]
                step*=min(1.,.1/max(1e-30,float(max(abs(step)/np.maximum(strengths,1.)))))
                for fraction in (1.,.5,.25,.125,.0625):
                    candidate=strengths+fraction*step
                    if min(candidate)<=0 or max(candidate)>=maximum:
                        continue
                    trial,trial_fields,trial_error,trial_name=evaluate(candidate)
                    if np.linalg.norm(trial_error)<np.linalg.norm(error):
                        strengths=candidate
                        measured,fields,error,name=trial,trial_fields,trial_error,trial_name
                        break
                else:
                    reason="No material-admissible improving Newton step in the declared line search"
                    break
            converged=measured["worst_relative_equation_residual"]<1e-7
            if converged:
                reason="Full Maxwell calibration reached 1e-7 equation tolerance"
            record={"name":design["name"],"target":target.tolist(),"target_condition":float(np.linalg.cond(target)),
                    "source_design":str(path),"alpha":alpha,"strengths":strengths.tolist(),
                    "nominal_source_decoder_strengths":nominal.tolist(),"history":history,
                    "calibration_converged":converged,"calibration_outcome":reason,
                    "source_reference_h":cfg.h,"calibration_h":args.calibration_h,
                    "source_interpolation":args.source_interpolation,
                    "operator_order":operator_cfg.order,
                    "scope":"Full Maxwell material-only calibration. The source profiles, drive gain, decoder and reference-grid interpolation data remain fixed throughout tuning and verification.",
                    "verification":[measured]}
            shutil.copyfile(ex.output/f"{name}.json",ex.output/"verification.json")
            shutil.copyfile(ex.output/f"{name}_fields.npz",ex.output/"verification_fields.npz")
            write_json(ex.output.parent/"design.json",record)
            # Every best admissible candidate is independently checked, even if
            # it missed the optimization tolerance; retain both outcomes.
            for h in args.verify_h:
                fine=Experiment(replace(operator_cfg,h=h),ex.output.parent/f"h{h:.8g}")
                fixed_probes=sample_probes(fine,reference,model["background_modes"],model["eigenvalues"])
                result=verify_device(fine,fixed_probes,strengths,alpha,target,terminals,
                                     nominal_strengths=nominal)
                record["verification"].append(result)
                print(json.dumps({"stage":"frozen_verification","target_name":design["name"],**result}),flush=True)
            rows.append(record)
            write_json(args.output/"summary.json",rows)


if __name__=="__main__":
    main()
