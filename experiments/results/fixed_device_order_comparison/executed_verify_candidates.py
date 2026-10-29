#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=2,<3", "scipy>=1.14,<2", "threadpoolctl>=3,<4"]
# ///
"""Forward-check saved candidates, including imperfect calibration outcomes."""
import argparse
from dataclasses import replace
import json
from pathlib import Path

import numpy as np
from threadpoolctl import threadpool_limits

from device import frozen_probes, spectral_probes, verify_device
from maxwell import Config, Experiment, write_json


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--background",type=Path,required=True)
    p.add_argument("--design",type=Path,nargs="+",required=True)
    p.add_argument("--output",type=Path,required=True)
    p.add_argument("--h",type=float,nargs="+",default=[.2,1/6,2/13])
    p.add_argument("--order",type=int,choices=(8,12))
    args=p.parse_args()
    args.output.mkdir(parents=True,exist_ok=False)
    for source in (Path(__file__),Path(__file__).with_name("maxwell.py"),Path(__file__).with_name("device.py")):
        (args.output/f"executed_{source.name}").write_bytes(source.read_bytes())
    cfg=Config(**json.loads((args.background/"metadata.json").read_text())["config"])
    reference=Experiment(cfg,args.output/"source_reference")
    model=np.load(args.background/"background.npz")
    rows=[]
    with threadpool_limits(2):
        for path in args.design:
            design=json.loads(path.read_text())
            sampler=spectral_probes if design.get("source_interpolation","cubic")=="spectral" else frozen_probes
            nominal=np.array(design.get("nominal_source_decoder_strengths",design["strengths"]))
            operator_cfg=replace(cfg,order=args.order or design.get("operator_order",cfg.order))
            result={"source_calibration":str(path),"calibration":design,"verification":[]}
            for h in args.h:
                ex=Experiment(replace(operator_cfg,h=h),args.output/design["name"]/f"h{h:.8g}")
                probes=sampler(ex,reference,model["background_modes"],model["eigenvalues"])
                measured=verify_device(ex,probes,np.array(design["strengths"]),design["alpha"],
                                       np.array(design["target"]),list(range(len(design["target"]))),
                                       nominal_strengths=nominal)
                result["verification"].append(measured)
                print(json.dumps({"design_name":design["name"],**measured}),flush=True)
            rows.append(result)
            write_json(args.output/"summary.json",rows)


if __name__=="__main__":
    main()
