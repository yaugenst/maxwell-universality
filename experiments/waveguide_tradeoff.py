#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=2,<3", "scipy>=1.14,<2", "threadpoolctl>=3,<4"]
# ///
"""Measure spacing and material-rounding tradeoffs in the exact TE10 channel.

These are fine one-dimensional channel solves, distinct from the archived
full-vector three-dimensional Maxwell verification. Source and decoder remain
fixed when material strengths are rounded.
"""
import argparse
import json
from pathlib import Path

import numpy as np
from scipy import sparse
from scipy.sparse.linalg import splu
from threadpoolctl import threadpool_limits

from maxwell import derivative, write_json
from waveguide_control import Template, designs, well


def measure(reference, output, spacing=None):
    output.mkdir(parents=True, exist_ok=False)
    (output / "executed_source.py").write_bytes(Path(__file__).read_bytes())
    calibration = json.loads((reference / "calibration.json").read_text())
    template = Template(np.load(reference / "template.npz"))
    rows = []
    for separation in (2., 2.5, 3., 3.5, 4.):
        component = dict(calibration)
        component["separation"] = separation
        component["coupling"] *= np.exp(-calibration["kappa"]*(separation-calibration["separation"]))
        for name in ("chain4", "mediator2"):
            design = next(d for d in designs(component) if d["name"] == name)
            v = np.array(design["strengths"])
            ports = np.array(design["ports"])
            target = np.array(design["target"])
            centers = (np.arange(len(v))-(len(v)-1)/2)*separation
            length = calibration["local_box_length"]+(len(v)-1)*separation
            h = calibration["reference_spacing"] if spacing is None else spacing
            n = round(length/h)
            z = np.arange(1, n)*h-length/2
            d = derivative(n, h, order=12)
            a0 = (d.T@d+sparse.eye(n-1)*(np.pi**2-1)).tocsc()
            wells = np.column_stack([well(z-c, template.radius) for c in centers])
            b = np.sqrt(h)*np.column_stack([template.source(z-centers[p]) for p in ports])
            sources = design["alpha"]*b*v[ports]
            for bits in (None, 8, 12, 16, 20, 24, 28):
                actual_v = v if bits is None else np.rint(v*2**bits)/2**bits
                a = a0-sparse.diags(wells@actual_v)
                fields = splu(a.tocsc()).solve(sources)
                decoded = design["alpha"]*np.diag(v[ports])+v[ports, None]*(b.T@fields)
                row = {"name": name, "separation": separation, "coupling": component["coupling"],
                       "fractional_bits": bits, "channel_spacing": h, "nominal_strengths": v.tolist(),
                       "actual_strengths": actual_v.tolist(),
                       "equation_error": float(np.linalg.norm(target@decoded-np.eye(len(ports)), 2)),
                       "relative_pde_residual": float(np.linalg.norm(a@fields-sources)/np.linalg.norm(sources)),
                       "decoder": "Frozen nominal gains and fixed continuous source functions",
                       "scope": "Fine TE10 channel; only material strengths are quantized"}
                rows.append(row)
    write_json(output / "tradeoff.json", rows)
    print(json.dumps(rows), flush=True)


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--reference", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--spacing", type=float)
    args = p.parse_args()
    with threadpool_limits(2):
        measure(args.reference, args.output, args.spacing)
