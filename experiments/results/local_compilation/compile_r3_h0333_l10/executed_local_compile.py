#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=2,<3", "scipy>=1.14,<2", "threadpoolctl>=3,<4"]
# ///
"""Compile prescribed two-port targets using only single and pair devices.

The pair component is solved with all Maxwell degrees of freedom. Its two-port
inverse and exact material derivatives define an additive three-site model.
The three-site cavity never participates in parameter selection.
"""
from __future__ import annotations

import argparse
from dataclasses import replace
import json
from pathlib import Path
import time

import numpy as np
from scipy.optimize import least_squares
from threadpoolctl import threadpool_limits

from maxwell import Experiment, solve_system, write_json
from local_transfer import Template, measure


def terminal_schur(k):
    return k[np.ix_([0, 2], [0, 2])] - np.outer(k[[0, 2], 1], k[1, [0, 2]]) / k[1, 1]


def compile_targets(template, output, separation, diagonals, spacings, backend, max_evaluations):
    output.mkdir(parents=True, exist_ok=False)
    for name in ("local_compile.py", "local_transfer.py", "maxwell.py"):
        (output / f"executed_{name}").write_bytes(Path(__file__).with_name(name).read_bytes())
    cfg = replace(template.config, solver=backend)
    pair_cfg = replace(cfg, centers=((0., 0., -separation/2), (0., 0., separation/2)),
                       lengths=(cfg.lengths[0], cfg.lengths[1], cfg.lengths[2]+separation))
    pair = Experiment(pair_cfg, output / "pair_component")
    probes = template.probes(pair)
    _, _, _, upper = pair.operator([0., 0.])
    vmax = (25-upper)*np.e
    evaluation_rows = []
    cache = {}

    def evaluate(v):
        key = tuple(v)
        if key in cache:
            return cache[key]
        start = time.perf_counter()
        a, _, _, _ = pair.operator(v)
        fields, info = solve_system(a, probes, backend)
        residual = np.linalg.norm(a@fields-probes)/np.linalg.norm(probes)
        if residual > 1e-8:
            raise RuntimeError("Pair calibration failed the Maxwell residual check")
        g = probes.T@fields
        response = np.diag(v)+v[:, None]*g*v[None, :]
        k = np.linalg.inv(response)
        derivative = []
        for site in range(2):
            ds = fields.T@(pair.edge_wells[site][:, None]*fields)
            dr = v[:, None]*ds*v[None, :]
            dr[site, site] += 1.
            dr[site, :] += g[site, :]*v
            dr[:, site] += v*g[:, site]
            derivative.append(-k@dr@k)
        derivative = np.array(derivative)
        cache[key] = (k, derivative)
        evaluation_rows.append({"strengths": list(v), "inverse": k.tolist(),
                                "derivative": derivative.tolist(), "pde_residual": float(residual),
                                "seconds": time.perf_counter()-start, **info})
        write_json(output / "pair_evaluations.json", evaluation_rows)
        print(json.dumps({"pair_evaluation": len(evaluation_rows), "strengths": list(v),
                          "inverse": k.tolist(), "seconds": evaluation_rows[-1]["seconds"]}), flush=True)
        return k, derivative

    # A deterministic isolated-pair measurement sets the common response scale.
    # All target matrices are specified before any assembled device is solved.
    baseline_v = np.full(2, 1/(1.1*template.mu))
    baseline, baseline_jac = evaluate(baseline_v)
    alpha = abs(baseline[0, 1])
    if alpha < 1e-9:
        raise ValueError("Pair coupling is below the planned useful-coupling floor")
    targets = [np.array([[d, 1.], [1., d]]) for d in diagonals]
    write_json(output / "targets.json", {
        "targets": [t.tolist() for t in targets], "alpha": alpha,
        "source_reference": str(template.reference), "mode": template.mode,
        "policy": "Only the isolated single component and two-component cavity determine material parameters. No assembled-device response can enter the fit.",
        "verification_spacings": spacings,
        "acceptance": "At most 1% all-right-hand-side equation error at both independent finer verification meshes; calibration fit alone is insufficient."})
    # Independent directional finite differences check the adjoint derivative.
    direction = np.array([.6, -.8])
    step = 1e-5
    plus, _ = evaluate(baseline_v+step*direction)
    minus, _ = evaluate(baseline_v-step*direction)
    analytic = np.einsum("j,jab->ab", direction, baseline_jac)
    numeric = (plus-minus)/(2*step)
    derivative_error = np.linalg.norm(analytic-numeric)/np.linalg.norm(numeric)
    write_json(output / "derivative_check.json", {"relative_error": float(derivative_error),
               "step": step, "analytic": analytic.tolist(), "finite_difference": numeric.tolist()})
    if derivative_error > 1e-5:
        raise RuntimeError("Pair derivative failed its independent finite-difference check")
    compiled = []
    for target in targets:
        d = float(target[0, 0])

        def objective(v):
            k, dk = evaluate(v)
            middle = 2*k[1, 1]-(1/v[1]-template.mu)
            f = np.array([k[0, 0]-alpha*(d-1), middle+k[0, 1]**2/alpha])/alpha
            jac = np.array([[dk[j, 0, 0],
                             2*dk[j, 1, 1]+(1/v[1]**2 if j == 1 else 0.)
                             +2*k[0, 1]*dk[j, 0, 1]/alpha] for j in range(2)]).T/alpha
            return f, jac

        initial = 1/(template.mu+alpha*np.array([d-1, -1.]))
        initial = np.clip(initial, .01, vmax*.999)
        fit = least_squares(lambda v: objective(v)[0], initial,
                            jac=lambda v: objective(v)[1], bounds=(.001, vmax*.9999),
                            max_nfev=max_evaluations, ftol=1e-12, xtol=1e-12, gtol=1e-10,
                            x_scale="jac")
        v = fit.x
        k, _ = evaluate(v)
        predicted = np.array([[k[0, 0], k[0, 1], 0.],
                              [k[1, 0], 2*k[1, 1]-(1/v[1]-template.mu), k[0, 1]],
                              [0., k[1, 0], k[0, 0]]])
        schur = terminal_schur(predicted)
        model_error = float(np.linalg.norm(target@(alpha*np.linalg.inv(schur))-np.eye(2), 2))
        record = {"target": target.tolist(), "alpha": alpha,
                  "strengths": [float(v[0]), float(v[1]), float(v[0])],
                  "predicted_inverse": predicted.tolist(), "predicted_terminal_schur": schur.tolist(),
                  "local_model_equation_error": model_error,
                  "fit_objective_norm": float(np.linalg.norm(fit.fun)),
                  "fit_evaluations": fit.nfev, "fit_message": fit.message,
                  "verification": []}
        compiled.append(record)
        # Write the final design before accessing any three-component solution.
        write_json(output / "compiled_targets.json", compiled)
        print(json.dumps({"compiled_target": target.tolist(), "strengths": record["strengths"],
                          "local_model_error": model_error}), flush=True)
        if model_error > 1e-4:
            continue
        for h in spacings:
            triple_cfg = replace(cfg, h=h,
                                 centers=((0., 0., -separation), (0., 0., 0.), (0., 0., separation)),
                                 lengths=(cfg.lengths[0], cfg.lengths[1], cfg.lengths[2]+2*separation))
            row = measure(template, triple_cfg, record["strengths"],
                          output / f"target_{d:g}_h{h:.8f}", save_fields=True)
            g = np.array(row["response"])
            decoded = alpha*g[np.ix_([0, 2], [0, 2])]
            row["decoded_terminal_response"] = decoded.tolist()
            row["prescribed_target_equation_error"] = float(np.linalg.norm(target@decoded-np.eye(2), 2))
            row["predicted_three_port_equation_error"] = float(np.linalg.norm(predicted@g-np.eye(3), 2))
            record["verification"].append(row)
            write_json(output / "compiled_targets.json", compiled)
            print(json.dumps({"target_diagonal": d, "h": h,
                              "equation_error": row["prescribed_target_equation_error"]}), flush=True)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--reference", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--mode", type=int, default=0)
    p.add_argument("--separation", type=float, required=True)
    p.add_argument("--diagonals", type=float, nargs="+", default=(3., 4.))
    p.add_argument("--h", type=float, nargs="+", required=True)
    p.add_argument("--max-evaluations", type=int, default=45)
    p.add_argument("--solver", choices=("direct", "cudss"), default="cudss")
    args = p.parse_args()
    if args.separation % 4:
        raise ValueError("Component spacing must preserve the periodic background phase")
    with threadpool_limits(2):
        compile_targets(Template(args.reference, args.mode), args.output,
                        args.separation, args.diagonals, args.h, args.solver, args.max_evaluations)


if __name__ == "__main__":
    main()
