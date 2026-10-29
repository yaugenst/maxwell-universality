#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=2,<3", "scipy>=1.14,<2", "threadpoolctl>=3,<4"]
# ///
"""Joint finite-precision inputs and adversarial full-field residual checks."""
import argparse
from dataclasses import replace
import json
from pathlib import Path

import numpy as np
from threadpoolctl import threadpool_limits

from device import frozen_probes, verify_device
from maxwell import Config, Experiment, solve_system, write_json


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--device",type=Path,required=True)
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    args.output.mkdir(parents=True,exist_ok=False)
    for source in (Path(__file__),Path(__file__).with_name("device.py")):
        (args.output/f"executed_{source.name}").write_bytes(source.read_bytes())
    data=np.load(args.device/"frozen_device.npz")
    tuning=json.loads((args.device/"tuning.json").read_text())
    cfg=Config(**json.loads((args.device/"reference"/"metadata.json").read_text())["config"])
    cfg.solver="cudss"
    reference=Experiment(cfg,args.output/"reference")
    gamma=np.array(tuning["target"])
    v=data["strengths"]
    alpha=float(data["alpha"])
    rows=[]
    with threadpool_limits(2):
        # All profile samples, material amplitudes, and the drive gain use the
        # same absolute fixed-point spacing. Geometry and analytic background
        # cosines/bump definitions are held exact in this parameter test.
        physical_samples=data["background_modes"]/(np.sqrt(cfg.h**3)*data["eigenvalues"])
        for bits in (8,10,12,16):
            unit=2.**-bits
            strengths=np.rint(v/unit)*unit
            scale=round(alpha/unit)*unit
            constant=round((7+reference.mode.ec-cfg.detuning)/unit)*unit
            samples=np.rint(physical_samples/unit)*unit
            ex=Experiment(replace(cfg,h=1/6,detuning=7+reference.mode.ec-constant),
                          args.output/f"all_inputs_bits_{bits}")
            probes=frozen_probes(ex,reference,samples*np.sqrt(cfg.h**3),np.ones(3))
            result=verify_device(ex,probes,strengths,scale,gamma,[0,2])
            result.update(fractional_bits=bits,coefficient_step=unit,
                          rounded_parameters="Background constant, all defect strengths, alpha drive gain, and all physical spline sample values defining source/readout profiles. Geometry, bump/cosine function definitions, and solver arithmetic unchanged.")
            rows.append(result)
            write_json(args.output/"joint_rounding.json",rows)
            print(json.dumps({"stage":"joint_rounding",**result}),flush=True)

        probes=frozen_probes(reference,reference,data["background_modes"],data["eigenvalues"])
        nominal=verify_device(reference,probes,v,alpha,gamma,[0,2])
        saved=np.load(reference.output/"verification_fields.npz")
        fields,sources=saved["fields"],saved["sources"]
        recovery=gamma@fields.T/alpha
        values,vectors=np.linalg.eigh(recovery@recovery.T)
        direction=recovery.T@vectors[:,-1]/np.sqrt(values[-1])
        _,right=np.linalg.eigh(sources.T@sources)
        b=right[:,-1]
        a,_,_,_=reference.operator(v)
        perturbation,info=solve_system(a,direction[:,None],cfg.solver)
        perturbation=perturbation[:,0]
        unit_solve_residual=float(np.linalg.norm(a@perturbation-direction))
        base=fields@b
        f=sources@b
        nominal_ports=v[[0,2]]
        baseline_x=alpha*nominal_ports*b+nominal_ports*(probes[:,[0,2]].T@base)
        samples=[]
        for eta in (1e-2,1e-3,1e-4,1e-6):
            changed=base+eta*np.linalg.norm(f)*perturbation
            decoded=alpha*nominal_ports*b+nominal_ports*(probes[:,[0,2]].T@changed)
            actual_eta=float(np.linalg.norm(a@changed-f)/np.linalg.norm(f))
            increment=float(np.linalg.norm(gamma@(decoded-baseline_x)))
            expected=eta*nominal["full_field_relative_residual_amplification_bound"]
            if abs(increment-expected)>1e-8*max(expected,1e-8):
                raise RuntimeError("Residual amplification check disagrees with its independently derived norm")
            samples.append({"requested_relative_maxwell_residual":eta,"measured_relative_maxwell_residual":actual_eta,
                            "equation_error_increment":increment,"norm_prediction":expected,
                            "total_equation_error":float(np.linalg.norm(gamma@decoded-b))})
        result={"scope":"Adversarial residual direction over all full-field coordinates, at the reference discretization. Explicitly perturbed fields are checked by applying the full Maxwell matrix and physical decoder.",
                "residual_gain":nominal["full_field_relative_residual_amplification_bound"],
                "right_hand_side":b.tolist(),"perturbation_solve_residual":unit_solve_residual,
                "samples":samples,**info}
        write_json(args.output/"adversarial_residual.json",result)
        np.savez_compressed(args.output/"adversarial_residual_fields.npz",b=b,base=base,f=f,
                            perturbation=perturbation,residual_direction=direction,probes=probes[:,[0,2]])
        print(json.dumps({"stage":"adversarial_residual",**result}),flush=True)


if __name__=="__main__":
    main()
