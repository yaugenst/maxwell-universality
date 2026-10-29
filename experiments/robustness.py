#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=2,<3", "scipy>=1.14,<2", "threadpoolctl>=3,<4"]
# ///
"""Frozen-device manufacturing, precision, loss and cavity-size controls."""
import argparse
from dataclasses import replace
import json
from pathlib import Path
import time

import numpy as np
from threadpoolctl import threadpool_limits

from device import frozen_probes, verify_device
from maxwell import Config, Experiment, write_json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--device", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    for source in (Path(__file__), Path(__file__).with_name("device.py")):
        (args.output/f"executed_{source.name}").write_bytes(source.read_bytes())
    data = np.load(args.device/"frozen_device.npz")
    tuning = json.loads((args.device/"tuning.json").read_text())
    meta = json.loads((args.device/"reference"/"metadata.json").read_text())
    cfg = Config(**meta["config"])
    cfg.solver = "cudss"
    reference = Experiment(cfg, args.output/"source_reference")
    v = data["strengths"]
    cases = [("nominal", cfg, v, {"kind": "nominal"})]
    constant = 7+reference.mode.ec-cfg.detuning
    for bits in (4, 6, 8, 10, 12, 16):
        quantized = np.rint(v*2**bits)/2**bits
        rounded_constant = round(constant*2**bits)/2**bits
        cases.append((f"material_bits_{bits}", replace(cfg, detuning=7+reference.mode.ec-rounded_constant),
                      quantized, {"kind": "material_rounding", "fractional_bits": bits,
                                  "coefficient_step": 2.**-bits,
                                  "rounded_coefficients": "background constant and all defect strengths; smooth geometry, rho, frequency and nominal source/decoder remain fixed"}))
    for relative in (-.01, -.001, .001, .01):
        cases.append((f"uniform_strength_{relative:+.3g}", cfg, v*(1+relative),
                      {"kind": "uniform_strength", "relative_change": relative}))
    # Deterministic directions fixed before measurements; each component has
    # exactly the listed relative amplitude, including mixed-sign errors.
    for index, signs in enumerate(((1,-1,1),(-1,1,-1),(1,1,-1),(-1,-1,1))):
        for amplitude in (.001, .01):
            cases.append((f"mixed_strength_{index}_{amplitude:g}", cfg,
                          v*(1+amplitude*np.array(signs)),
                          {"kind": "mixed_strength", "relative_change": (amplitude*np.array(signs)).tolist()}))
    for shift in (.01, .025):
        centers = [(x+shift, y, z) for x,y,z in reference.centers]
        cases.append((f"material_shift_x_{shift:g}", replace(cfg, centers=centers), v,
                      {"kind": "common_material_displacement", "distance": shift,
                       "source_readout_positions": "fixed nominal positions"}))
    for relative in (-.001, -.01):
        cases.append((f"radius_{relative:+.3g}", replace(cfg, radius=cfg.radius*(1+relative)), v,
                      {"kind": "radius_error", "relative_change": relative,
                       "source_readout_profiles": "fixed nominal profiles"}))
    for absorption in (.0001, .001, .01):
        cases.append((f"absorption_{absorption:g}", replace(cfg, absorption=absorption), v,
                      {"kind": "uniform_absorption", "imaginary_permittivity": absorption,
                       "scope": "Dissipative robustness control outside the lossless theorem"}))
    for label, lengths in (("longitudinal", (6.,6.,14.)), ("transverse", (8.,8.,10.))):
        cases.append((f"buffer_{label}", replace(cfg, lengths=lengths), v,
                      {"kind": "changed_cavity", "scope": "Different PEC device, not a continuum refinement"}))
    write_json(args.output/"planned_cases.json", [{"name": n, **details} for n,c,w,details in cases])
    rows=[]
    with threadpool_limits(2):
        for name, config, strengths, details in cases:
            start=time.perf_counter()
            ex=Experiment(config, args.output/name)
            probes=frozen_probes(ex, reference, data["background_modes"], data["eigenvalues"])
            measured=verify_device(ex, probes, strengths, float(data["alpha"]), tuning["target"],
                                   [0,2], nominal_strengths=v, save_fields=name=="nominal")
            row={"name":name, **details, **measured, "wall_seconds":time.perf_counter()-start}
            rows.append(row)
            write_json(args.output/"robustness.json", rows)
            print(json.dumps(row), flush=True)


if __name__ == "__main__":
    main()
