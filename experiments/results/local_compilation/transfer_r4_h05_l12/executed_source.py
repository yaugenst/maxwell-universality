#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=2,<3", "scipy>=1.14,<2", "threadpoolctl>=3,<4"]
# ///
"""Freeze an isolated component, test new cavities and predict a three-site chain.

All sources are translates of one fixed C-infinity compact function. Single-
and pair-component measurements precede the triple test. No triple response
is used in the predictor and no material is retuned after assembly.
"""
from __future__ import annotations

import argparse
from dataclasses import replace
import json
from pathlib import Path
import time

import numpy as np
from scipy.fft import dct, dst
from threadpoolctl import threadpool_limits

from maxwell import Config, Experiment, bump, solve_system, write_json


class Template:
    def __init__(self, reference, mode):
        self.reference = Path(reference)
        self.mode = mode
        info = json.loads((self.reference / "metadata.json").read_text())
        self.config = Config(**info["config"])
        data = np.load(self.reference / "local_modes.npz")
        self.mu = float(data["values"][mode])
        self.n = np.rint(np.array(self.config.lengths) / self.config.h).astype(int)
        shapes = [tuple(self.n - (np.arange(3) != component)) for component in range(3)]
        offsets = np.r_[0, np.cumsum([np.prod(s) for s in shapes])]
        self.coefficients = []
        for component in range(3):
            field = data["fields"][offsets[component]:offsets[component+1], mode]
            field = field.reshape(shapes[component]) / np.sqrt(self.config.h**3)
            coefficient = dct(field, type=2, axis=component, norm="ortho")
            for axis in range(3):
                if axis != component:
                    coefficient = dst(coefficient, type=1, axis=axis, norm="ortho")
            self.coefficients.append(coefficient)

    def probes(self, ex):
        result = np.zeros((ex.grid.size, len(ex.centers)))
        for site, center in enumerate(ex.centers):
            for component in range(3):
                factors = []
                for axis, (points, length, n) in enumerate(zip(
                        ex.grid.axes[component], self.config.lengths, self.n)):
                    t = (points-center[axis]+length/2)/length
                    if axis == component:
                        f = np.cos(np.pi*np.outer(t, np.arange(n)))*np.sqrt(2/n)
                        f[:, 0] /= np.sqrt(2)
                    else:
                        f = np.sin(np.pi*np.outer(t, np.arange(1, n)))*np.sqrt(2/n)
                    factors.append(f)
                field = np.einsum("xa,yb,zc,abc->xyz", *factors,
                                  self.coefficients[component], optimize=True)
                well = bump(ex.grid.xyz[component], center, self.config.radius)
                lo, hi = ex.grid.offsets[component:component+2]
                result[lo:hi, site] = (np.sqrt(ex.config.h**3)*well*field/self.mu).ravel()
        return result


def measure(template, config, strengths, output, save_fields=False):
    start = time.perf_counter()
    ex = Experiment(config, output)
    b = template.probes(ex)
    a, cells, lower, upper = ex.operator(strengths)
    field, info = solve_system(a, b, config.solver)
    residual = np.linalg.norm(a @ field-b, axis=0)/np.linalg.norm(b, axis=0)
    v = np.array(strengths)
    response = np.diag(v) + v[:, None]*(b.T @ field)*v[None, :]
    inverse = np.linalg.inv(response)
    data = {"strengths": list(strengths), "h": config.h,
            "lengths": config.lengths, "centers": config.centers,
            "reference": str(template.reference), "mode": template.mode,
            "mu": template.mu, "unknowns": ex.grid.size,
            "response": response.tolist(), "inverse": inverse.tolist(),
            "pde_relative_residuals": residual.tolist(),
            "material_continuous_enclosure": [lower, upper],
            "source_norms_squared": np.sum(b*b, axis=0).tolist(),
            "inside_all_supports_fractions": (np.sum(field[np.any(ex.supports, axis=1)]**2, axis=0)
                                               /np.sum(field**2, axis=0)).tolist(),
            "seconds": time.perf_counter()-start, **info}
    write_json(output / "measurement.json", data)
    if max(residual) > 1e-8:
        raise RuntimeError("Full Maxwell solve failed its residual check")
    if save_fields:
        np.savez_compressed(output / "fields.npz", fields=field, probes=b,
                            eps_cells=cells, h=config.h, lengths=config.lengths)
    print(json.dumps({"case": str(output), "inverse": data["inverse"],
                      "pde_residual": float(max(residual)), "seconds": data["seconds"]}), flush=True)
    return data


def transfer(template, output, spacings, fractions, separation, backend):
    output.mkdir(parents=True, exist_ok=False)
    (output / "executed_source.py").write_bytes(Path(__file__).read_bytes())
    (output / "executed_maxwell.py").write_bytes(Path(__file__).with_name("maxwell.py").read_bytes())
    cfg = replace(template.config, solver=backend)
    rows = []
    # Freeze the physical source and material before every cavity/mesh test.
    for fraction in fractions:
        strength = 1/(template.mu*(1+fraction))
        expected_inverse = template.mu*fraction
        for h in spacings:
            for change in (0., 4.):
                length = cfg.lengths[0]+change
                config = replace(cfg, h=h, lengths=(length,)*3)
                case = output / f"single_f{fraction:g}_h{h:.8f}_l{length:g}"
                row = measure(template, config, [strength], case)
                response = row["response"][0][0]
                row["frozen_single_equation_error"] = abs(expected_inverse*response-1)
                row["fractional_inverse_detuning"] = fraction
                rows.append(row)
                write_json(output / "transfer.json", rows)
        # Pair coefficients are calibrated in the smallest two-site box.
        pair_centers = ((0., 0., -separation/2), (0., 0., separation/2))
        pair_cfg = replace(cfg, centers=pair_centers,
                           lengths=(cfg.lengths[0], cfg.lengths[1], cfg.lengths[2]+separation))
        pair = measure(template, pair_cfg, [strength]*2, output / f"pair_f{fraction:g}")
        kp = np.array(pair["inverse"])
        predicted = np.array([[kp[0, 0], kp[0, 1], 0.],
                              [kp[1, 0], kp[0, 0]+kp[1, 1]-expected_inverse, kp[0, 1]],
                              [0., kp[1, 0], kp[1, 1]]])
        # This matrix is a prospective physical-response prediction, not a
        # prescribed sparse-system target or a general compiler success.
        write_json(output / f"pair_prediction_f{fraction:g}.json", {
            "prediction": predicted.tolist(), "singleton_inverse": expected_inverse,
            "pair": pair, "policy": "Frozen before the triple solve; nearest-pair additive corrections only."})
        triples = []
        for h in spacings:
            triple_cfg = replace(cfg, h=h,
                                 centers=((0., 0., -separation), (0., 0., 0.), (0., 0., separation)),
                                 lengths=(cfg.lengths[0], cfg.lengths[1], cfg.lengths[2]+2*separation))
            triple = measure(template, triple_cfg, [strength]*3,
                             output / f"triple_f{fraction:g}_h{h:.8f}")
            g = np.array(triple["response"])
            k = np.array(triple["inverse"])
            triple["predicted_equation_error"] = float(np.linalg.norm(predicted@g-np.eye(3), 2))
            triple["relative_inverse_error"] = float(np.linalg.norm(predicted-k, 2)/np.linalg.norm(k, 2))
            triple["bypass_ratio"] = float(abs(k[0, 2])/np.sqrt(abs(k[0, 1]*k[1, 2])))
            triples.append(triple)
            write_json(output / f"assembly_f{fraction:g}.json", triples)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--reference", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--mode", type=int, default=0)
    p.add_argument("--h", type=float, nargs="+", required=True)
    p.add_argument("--fractions", type=float, nargs="+", default=(.1, .5))
    p.add_argument("--separation", type=float, required=True)
    p.add_argument("--solver", choices=("direct", "cudss"), default="cudss")
    args = p.parse_args()
    if args.separation % 4:
        raise ValueError("Use separations divisible by four so every site has the same periodic background phase")
    with threadpool_limits(2):
        template = Template(args.reference, args.mode)
        transfer(template, args.output, args.h, args.fractions, args.separation, args.solver)


if __name__ == "__main__":
    main()
