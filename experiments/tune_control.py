#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=2,<3", "scipy>=1.14,<2", "threadpoolctl>=3,<4"]
# ///
"""Full-cavity tuning control, followed by a fixed-device refinement test.

This deliberately uses the entire compressed background response for calibration.
It tests a small physical device, not scalable local compilation.
"""
import argparse
from dataclasses import replace
import json
from pathlib import Path
import time

import numpy as np
from scipy.linalg import solve
from scipy.ndimage import map_coordinates
from threadpoolctl import threadpool_limits

from maxwell import Config, Experiment, Grid, solve_system, write_json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--from-case", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--refine", type=float, nargs="+", default=[1/6])
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    (args.output/"executed_control.py").write_bytes(Path(__file__).read_bytes())
    metadata = json.loads((args.from_case/"metadata.json").read_text())
    measured = json.loads((args.from_case/"modal_comparison.json").read_text())
    cfg = Config(**metadata["config"])
    if cfg.order != 8 or cfg.absorption:
        raise ValueError("This control is defined for the eighth-order lossless study")
    reference = Experiment(cfg, args.output/"reference")
    arrays = np.load(args.from_case/"modal_data.npz")
    s, u, original_probes = arrays["compressed"], arrays["modes"], arrays["probes"]
    terminals = [0, 2]
    support_site = np.argmax(np.array(reference.edge_wells)[:, arrays["indices"]], axis=0)
    ut = u[:, terminals]
    alpha = measured["alpha"]
    gamma = np.array([[3., 1.], [1., 3.]])
    min_inverse = 1/((25-(7+metadata["bloch_probe"]["ec"]-cfg.detuning+7*cfg.rho))*np.e)
    initial = 1/np.array(measured["strengths"])
    parameters = initial[[0, 1]]
    history = []

    def evaluate(p, derivatives=False):
        diagonal = np.where(support_site == 1, p[1], p[0])
        t = -s.copy()
        t.flat[::len(t)+1] += diagonal
        c = solve(t, ut, assume_a="sym", check_finite=False)
        k = np.linalg.inv(ut.T@c)
        residual = np.array([k[0, 0]-3*alpha, k[0, 1]-alpha])/alpha
        if not derivatives:
            return residual, k
        jac = np.empty((2, 2))
        for j, mask in enumerate((support_site != 1, support_site == 1)):
            deriv = k@(c[mask].T@c[mask])@k
            jac[:, j] = [deriv[0, 0]/alpha, deriv[0, 1]/alpha]
        return residual, k, jac

    start = time.perf_counter()
    with threadpool_limits(limits=2):
        for iteration in range(12):
            residual, k, jac = evaluate(parameters, True)
            history.append({"iteration": iteration, "inverse_strengths": parameters.tolist(),
                            "relative_schur_entry_residual": residual.tolist()})
            print(json.dumps(history[-1]), flush=True)
            if np.linalg.norm(residual) < 1e-9:
                break
            step = np.linalg.solve(jac, -residual)
            for fraction in (1., .5, .25, .125, .0625, .03125, .015625):
                candidate = parameters+fraction*step
                if min(candidate) <= min_inverse:
                    continue
                trial, _ = evaluate(candidate)
                if np.linalg.norm(trial) < np.linalg.norm(residual):
                    parameters = candidate
                    break
            else:
                raise RuntimeError("Full-cavity tuning did not find an admissible improving step")
        else:
            raise RuntimeError("Full-cavity tuning exhausted its bounded iteration count")
        strengths = 1/parameters[[0, 1, 0]]
        write_json(args.output/"tuning.json", {
            "scope": "Full-cavity calibration control; not the proof's local or uniform encoder",
            "source_case": str(args.from_case), "target": gamma.tolist(), "alpha": alpha,
            "strengths": strengths.tolist(), "history": history,
            "calibration_seconds": time.perf_counter()-start})
        a0, _, _, _ = reference.operator([0., 0., 0.])
        background_modes, _ = solve_system(a0, original_probes, cfg.solver)
        eigenvalues = np.array([m["eigenvalue"] for m in measured["local_modes"]])
        reconstructed = np.column_stack([w*background_modes[:, i]/eigenvalues[i]
                                         for i, w in enumerate(reference.edge_wells)])
        reconstruction_error = np.linalg.norm(reconstructed-original_probes)/np.linalg.norm(original_probes)
        if reconstruction_error > 1e-8:
            raise RuntimeError(f"Continuous probe reconstruction inconsistent: {reconstruction_error}")
        np.savez_compressed(args.output/"frozen_device.npz", background_modes=background_modes,
                            eigenvalues=eigenvalues, strengths=strengths, alpha=alpha,
                            reference_h=cfg.h, reference_lengths=cfg.lengths)
        rhs_targets = np.array([[1., 0., 1., 1.], [0., 1., -1., 1.]])
        drive = np.zeros((3, 4))
        drive[terminals] = alpha*rhs_targets
        v = np.diag(strengths)
        results = []
        for h in [cfg.h, *args.refine]:
            ex = reference if h == cfg.h else Experiment(replace(cfg, h=h), args.output/f"refine_h{h:.8g}")
            # A single continuous source definition: w times the cubic cardinal-spline
            # interpolant of the reference background mode, divided by its eigenvalue.
            # Both material strengths and this source/readout definition remain fixed.
            probes = np.zeros((ex.grid.size, 3))
            for site in range(3):
                source_components = reference.grid.unpack(background_modes[:, site]/np.sqrt(cfg.h**3))
                for component in range(3):
                    lo, hi = ex.grid.offsets[component:component+2]
                    well = ex.edge_wells[site][lo:hi]
                    inside = well > 0
                    coordinates = np.array([(xyz.ravel()[inside]-axis[0])/cfg.h
                                            for xyz, axis in zip(ex.grid.xyz[component], reference.grid.axes[component])])
                    interpolated = map_coordinates(source_components[component], coordinates,
                                                   order=3, mode="constant", cval=0., prefilter=True)
                    probes[lo:hi, site][inside] = np.sqrt(h**3)*well[inside]*interpolated/eigenvalues[site]
            a, cells, lower, upper = ex.operator(strengths)
            sources = probes@v@drive
            fields, info = solve_system(a, sources, cfg.solver)
            decoded = (v@drive+v@probes.T@fields)[terminals]
            equation_residuals = np.linalg.norm(gamma@decoded-rhs_targets, axis=0)/np.linalg.norm(rhs_targets, axis=0)
            pde_residuals = np.linalg.norm(a@fields-sources, axis=0)/np.linalg.norm(sources, axis=0)
            data = {"h": h, "unknowns": ex.grid.size, "strengths": strengths.tolist(),
                    "material_continuous_enclosure": [lower, upper],
                    "source_definition": "Fixed reference cubic cardinal-spline background modes times the analytic bump, divided by fixed modal eigenvalues",
                    "source_reconstruction_relative_error_at_reference": float(reconstruction_error),
                    "target": gamma.tolist(), "right_hand_sides": rhs_targets.tolist(),
                    "decoded_solutions": decoded.tolist(), "decoded_relative_residuals": equation_residuals.tolist(),
                    "discrete_pde_relative_residuals": pde_residuals.tolist(), **info}
            write_json(ex.output/"decoded.json", data)
            np.savez_compressed(ex.output/"decoded_fields.npz", fields=fields, probes=probes, eps_cells=cells,
                                shape=ex.grid.n, h=h, lengths=cfg.lengths)
            results.append(data)
            print(json.dumps(data), flush=True)
            if max(pde_residuals) > 1e-8:
                raise RuntimeError("Independent Maxwell verification failed")
        write_json(args.output/"fixed_device_refinement.json", results)


if __name__ == "__main__":
    main()
