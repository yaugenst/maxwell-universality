#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=2,<3", "scipy>=1.14,<2", "threadpoolctl>=3,<4"]
# ///
"""Search and transfer isolated Maxwell components, without whole-device fitting.

The screen enumerates every material-admissible positive eigenvalue of the
finite-grid single-defect Birman--Schwinger matrix. Sources are generated in
blocks to avoid storing the full volume-by-support Green matrix.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
from dataclasses import asdict
import json
from pathlib import Path
import resource
import time

import numpy as np
from scipy.linalg import eigh
from scipy.sparse.linalg import splu
from threadpoolctl import threadpool_limits

from maxwell import Config, Experiment, write_json


@contextmanager
def factor(a, backend, columns):
    start = time.perf_counter()
    if backend == "direct":
        lu = splu(a)
        info = {"factor_nnz": int(lu.L.nnz + lu.U.nnz),
                "factor_seconds": time.perf_counter() - start}
        yield lu.solve, info
    else:
        from nvmath.sparse.advanced import DirectSolver
        with DirectSolver(a.tocsr(), np.zeros((a.shape[0], columns), order="F")) as solver:
            solver.plan()
            raw = solver.factorize()
            info = {"factor_nnz": int(raw.lu_nnz),
                    "factor_seconds": time.perf_counter() - start}
            solver.solution_config.ir_num_steps = 5

            def solve(b):
                solver.reset_operands(b=np.asfortranarray(b))
                return solver.solve()

            yield solve, info


def screen(config, output, batch=128, save_modes=12):
    start = time.perf_counter()
    ex = Experiment(config, output)
    (ex.output / "executed_local_library.py").write_bytes(Path(__file__).read_bytes())
    a, _, _, upper = ex.operator([0.])
    well = (ex.grid.edge_average(ex.wells[0]) if config.order == 2 else ex.edge_wells[0])
    indices = np.flatnonzero(well > 0)
    q = np.sqrt(well[indices])
    size = len(indices)
    if size > 13_000:
        raise ValueError("Dense support screen exceeds the planned 13000-coordinate cap")
    batch = min(batch, size)
    s = np.empty((size, size))
    residuals = []
    print(json.dumps({"stage": "screen", "config": asdict(config),
                      "unknowns": ex.grid.size, "support_coordinates": size,
                      "dense_support_gib": 8 * size**2 / 2**30}), flush=True)
    with factor(a, config.solver, batch) as (solve, info):
        for j in range(0, size, batch):
            count = min(batch, size-j)
            rhs = np.zeros((ex.grid.size, batch), order="F")
            rhs[indices[j:j+count], np.arange(count)] = q[j:j+count]
            fields = solve(rhs)
            residuals.append(float(np.linalg.norm(a @ fields - rhs) / np.linalg.norm(rhs)))
            s[:, j:j+count] = q[:, None] * fields[indices, :count]
        symmetry = float(np.linalg.norm(s-s.T) / np.linalg.norm(s))
        if max(residuals) > 1e-8 or symmetry > 1e-8:
            raise RuntimeError("Compressed background failed residual or symmetry check")
        maximum_strength = (25-upper) * np.e
        print(json.dumps({"stage": "diagonalize", "seconds": time.perf_counter()-start}), flush=True)
        values, vectors = eigh((s+s.T)/2, subset_by_value=(1/maximum_strength, np.inf))
        del s
        print(json.dumps({"stage": "recover", "admissible_modes": len(values),
                          "seconds": time.perf_counter()-start}), flush=True)
        rows, retained = [], []
        for j in range(0, len(values), batch):
            count = min(batch, len(values)-j)
            rhs = np.zeros((ex.grid.size, batch), order="F")
            rhs[indices, :count] = q[:, None] * vectors[:, j:j+count]
            fields = solve(rhs)[:, :count]
            energy = np.sum(fields**2, axis=0)
            fractions = np.sum(fields[indices]**2, axis=0)/energy
            for k in range(count):
                idx = j+k
                strength = 1/values[idx]
                f = fields[:, k]
                residual = np.linalg.norm(a @ f - strength*well*f)/np.linalg.norm(f)
                row = {"eigenvalue": float(values[idx]), "strength": float(strength),
                       "inside_fraction": float(fractions[k]),
                       "bloch_overlap_squared": float((ex.b[:, 0] @ f)**2/energy[k]),
                       "absolute_eigen_residual": float(residual), "index": idx}
                rows.append(row)
                retained.append((float(fractions[k]), idx, f.copy()))
            retained.sort(key=lambda x: x[0], reverse=True)
            retained = retained[:save_modes]
    rows.sort(key=lambda x: x["inside_fraction"], reverse=True)
    result = {"scope": "Complete admissible finite-grid single-defect mode enumeration; not a continuum or infinite-medium certificate.",
              "config": asdict(config), "support_coordinates": size, "unknowns": ex.grid.size,
              "maximum_strength": float(maximum_strength), "modes": rows,
              "background_relative_residual": max(residuals), "symmetry_error": symmetry,
              "wall_seconds": time.perf_counter()-start,
              "peak_rss_gib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/2**20,
              **info}
    write_json(ex.output / "screen.json", result)
    selected = [item[1] for item in retained]
    if selected:
        np.savez_compressed(ex.output / "local_modes.npz", indices=indices,
                            vectors=vectors[:, selected], values=values[selected],
                            fields=np.column_stack([item[2] for item in retained]),
                            q=q, h=config.h, lengths=config.lengths)
    print(json.dumps({"stage": "complete", "output": str(output),
                      "best_modes": rows[:5], "wall_seconds": result["wall_seconds"]}), flush=True)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--radius", type=float, required=True)
    p.add_argument("--length", type=float, required=True)
    p.add_argument("--h", type=float, default=.5)
    p.add_argument("--detuning", type=float)
    p.add_argument("--rho", type=float, default=.5)
    p.add_argument("--order", type=int, default=8, choices=(2, 4, 6, 8, 12))
    p.add_argument("--solver", choices=("direct", "cudss"), default="direct")
    p.add_argument("--batch", type=int, default=128)
    p.add_argument("--save-modes", type=int, default=12)
    args = p.parse_args()
    config = Config(lengths=(args.length,)*3, h=args.h, radius=args.radius, rho=args.rho,
                    detuning=args.detuning if args.detuning is not None else .3/args.radius**2,
                    order=args.order, solver=args.solver, centers=((0., 0., 0.),))
    with threadpool_limits(2):
        screen(config, args.output, args.batch, args.save_modes)


if __name__ == "__main__":
    main()
