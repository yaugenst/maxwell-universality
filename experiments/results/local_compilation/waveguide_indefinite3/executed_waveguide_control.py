#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=2,<3", "scipy>=1.14,<2", "threadpoolctl>=3,<4"]
# ///
"""A local-compilation positive control in a cutoff rectangular waveguide.

This changes the physical platform: transverse-uniform scalar dielectric in a
1 x 0.5 PEC waveguide. Its invariant TE10 channel has an exact one-dimensional
continuum reduction. It tests chain composition, not arbitrary sparse graphs
or the paper's three-dimensional periodic construction. Verification assembles
and solves the full three-component Maxwell operator without a mode filter.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
import time

import numpy as np
from scipy import sparse
from scipy.fft import dst
from scipy.linalg import eigh
from scipy.sparse.linalg import splu
from threadpoolctl import threadpool_limits

from maxwell import Grid, derivative, solve_system, write_json


def well(z, radius=1.):
    r2 = (z/radius)**2
    value = np.zeros_like(z)
    inside = r2 < 1
    value[inside] = np.exp(-1/(1-r2[inside]))
    return value


class Template:
    def __init__(self, data):
        self.mu = float(data["mu"])
        self.coefficients = data["coefficients"]
        self.length = float(data["length"])
        self.n = int(data["n"])
        self.radius = float(data["radius"])

    def source(self, z):
        # Fixed continuous C-infinity compact source; no mesh renormalization.
        basis = np.sqrt(2/self.n)*np.sin(np.pi*np.outer(
            (np.asarray(z)+self.length/2)/self.length, np.arange(1, self.n)))
        return well(np.asarray(z), self.radius)*(basis@self.coefficients)/self.mu


def calibrate(output, spacing=.005, length=12., radius=1., separation=4.):
    output.mkdir(parents=True, exist_ok=False)
    (output / "executed_source.py").write_bytes(Path(__file__).read_bytes())
    start = time.perf_counter()
    n = round(length/spacing)
    z = np.arange(1, n)*spacing-length/2
    w = well(z, radius)
    kappa = np.sqrt(np.pi**2-1)
    d = derivative(n, spacing, order=12)
    a = (d.T@d+sparse.eye(n-1)*kappa**2).tocsc()
    indices = np.flatnonzero(w > 0)
    q = np.sqrt(w[indices])
    rhs = np.zeros((n-1, len(indices)))
    rhs[indices, np.arange(len(indices))] = q
    fields = splu(a).solve(rhs)
    compressed = q[:, None]*fields[indices]
    values, vectors = eigh((compressed+compressed.T)/2)
    mu = values[-1]
    u = vectors[:, -1]
    u *= np.sign(u.sum())
    field = fields@u
    coefficients = dst(field/np.sqrt(spacing), type=1, norm="ortho")
    np.savez_compressed(output / "template.npz", coefficients=coefficients, mu=mu,
                        length=length, radius=radius, n=n, spacing=spacing,
                        z=z, field=field, source=well(z, radius)*field/mu)
    template = Template(np.load(output / "template.npz"))
    b = template.source(z)
    moment_plus = spacing*np.sum(b*np.exp(kappa*z))
    moment_minus = spacing*np.sum(b*np.exp(-kappa*z))
    coupling = float(moment_plus*moment_minus*np.exp(-kappa*separation)/(2*kappa))
    # Verify the analytic free-space pair coupling in a separate two-site box.
    pair_length = length+separation
    pn = round(pair_length/spacing)
    pz = np.arange(1, pn)*spacing-pair_length/2
    pd = derivative(pn, spacing, order=12)
    pa = (pd.T@pd+sparse.eye(pn-1)*kappa**2).tocsc()
    pb = np.sqrt(spacing)*np.column_stack([template.source(pz-c) for c in (-separation/2, separation/2)])
    pf = splu(pa).solve(pb)
    pair_s = pb.T@pf
    material_upper = 1+1/(np.e*mu)
    if material_upper > 25:
        raise ValueError("The isolated resonance exceeds the material bound")
    result = {"platform": "Cutoff PEC waveguide; separable TE10 chain control, not the periodic construction",
              "cross_section": [1., .5], "reference_spacing": spacing,
              "local_box_length": length, "radius": radius, "separation": separation,
              "mu": float(mu), "next_local_eigenvalue": float(values[-2]),
              "resonant_strength": float(1/mu), "kappa": float(kappa),
              "coupling": coupling, "coupling_over_local_mode_gap": float(coupling/(mu-values[-2])),
              "inside_fraction": float(np.sum(field[indices]**2)/np.sum(field**2)),
              "material_enclosure_at_resonance": [1., float(material_upper)],
              "local_eigen_residual": float(np.linalg.norm(a@field-w*field/mu)/np.linalg.norm(field)),
              "pair_projected_background": pair_s.tolist(),
              "pair_coupling_relative_check": float(abs(pair_s[0, 1]/coupling-1)),
              "pair_diagonal_relative_change": float(np.max(abs(np.diag(pair_s)/mu-1))),
              "seconds": time.perf_counter()-start}
    write_json(output / "calibration.json", result)
    print(json.dumps(result), flush=True)


def designs(calibration):
    mu, alpha = calibration["mu"], calibration["coupling"]
    result = []
    for name, diagonal in (("chain3", [3., 3., 3.]),
                           ("nonuniform3", [2.5, 3., 4.]),
                           ("indefinite3", [1., 1., 1.]),
                           ("chain4", [3., 3., 3., 3.])):
        n = len(diagonal)
        target = np.diag(diagonal)-np.diag(np.ones(n-1), 1)-np.diag(np.ones(n-1), -1)
        strengths = 1/(mu+alpha*np.array(diagonal))
        result.append({"name": name, "target": target.tolist(), "strengths": strengths.tolist(),
                       "ports": list(range(n)), "alpha": alpha,
                       "target_condition": float(np.linalg.cond(target))})
    # A mediator with negative reduced diagonal produces a positive terminal link.
    result.append({"name": "mediator2", "target": [[3., 1.], [1., 3.]],
                   "strengths": (1/(mu+alpha*np.array([2., -1., 2.]))).tolist(),
                   "ports": [0, 2], "alpha": alpha, "target_condition": 2.})
    return result


def verify(reference, output, name, spacings, solver, order=12, buffer_extra=0.):
    output.mkdir(parents=True, exist_ok=False)
    for filename in ("waveguide_control.py", "maxwell.py"):
        (output / f"executed_{filename}").write_bytes(Path(__file__).with_name(filename).read_bytes())
    calibration = json.loads((reference / "calibration.json").read_text())
    template = Template(np.load(reference / "template.npz"))
    design = next(d for d in designs(calibration) if d["name"] == name)
    v = np.array(design["strengths"])
    target, ports = np.array(design["target"]), np.array(design["ports"])
    centers = (np.arange(len(v))-(len(v)-1)/2)*calibration["separation"]
    lengths = (1., .5, calibration["local_box_length"]
               +(len(v)-1)*calibration["separation"]+buffer_extra)
    if v.max()/np.e+1 > 25 or min(v) < 0:
        raise ValueError("Compiled material exceeds [1,25]")
    write_json(output / "frozen_design.json", {**design, "centers": centers.tolist(),
               "lengths": lengths, "order": order, "spacings": spacings,
               "template_sha256": sha256((reference / "template.npz").read_bytes()).hexdigest(),
               "policy": "Only isolated-component calibration and analytic nearest-pair coupling; no optimization or assembled response enters the design.",
               "acceptance": "Equation operator norm below 1% on both finer full-Maxwell grids."})
    rows = []
    for h in spacings:
        start = time.perf_counter()
        grid = Grid(lengths, h, order=order, max_unknowns=400_000)
        material = grid.flatten([1+sum(s*well(xyz[2]-c, template.radius)
                                       for s, c in zip(v, centers)) for xyz in grid.xyz])
        a = grid.stiffness-sparse.diags(material, format="csc")
        b = np.zeros((grid.size, len(ports)))
        lo, hi = grid.offsets[1:3]
        transverse = np.sqrt(2/(lengths[0]*lengths[1]))*np.sin(np.pi*(grid.axes[1][0]+.5))
        for column, site in enumerate(ports):
            profile = template.source(grid.axes[1][2]-centers[site])
            b[lo:hi, column] = (np.sqrt(h**3)*transverse[:, None, None]
                               *np.ones(grid.shapes[1][1])[None, :, None]
                               *profile[None, None, :]).ravel()
        sources = design["alpha"]*b*v[ports]
        fields, info = solve_system(a, sources, solver)
        decoded = design["alpha"]*np.diag(v[ports])+v[ports, None]*(b.T@fields)
        error = np.linalg.norm(target@decoded-np.eye(len(ports)), 2)
        residual = np.linalg.norm(a@fields-sources, axis=0)/np.linalg.norm(sources, axis=0)
        off_polarization = np.sqrt((np.sum(fields[:lo]**2)+np.sum(fields[hi:]**2))/np.sum(fields**2))
        # Independent continuum-channel reference at the same frozen design,
        # with a much finer longitudinal grid and exact transverse wavenumber.
        ch = calibration["reference_spacing"]
        cn = round(lengths[2]/ch)
        cz = np.arange(1, cn)*ch-lengths[2]/2
        cd = derivative(cn, ch, order=12)
        ceps = 1+sum(s*well(cz-c, template.radius) for s, c in zip(v, centers))
        ca = (cd.T@cd+sparse.diags(np.pi**2-ceps)).tocsc()
        cb = np.sqrt(ch)*np.column_stack([template.source(cz-centers[p]) for p in ports])
        cf = splu(ca).solve(design["alpha"]*cb*v[ports])
        continuum_decoded = design["alpha"]*np.diag(v[ports])+v[ports, None]*(cb.T@cf)
        row = {"name": name, "h": h, "order": order, "unknowns": grid.size,
               "lengths": lengths, "target": design["target"], "strengths": design["strengths"],
               "decoded_response": decoded.tolist(), "equation_error": float(error),
               "fine_channel_equation_error": float(np.linalg.norm(target@continuum_decoded-np.eye(len(ports)), 2)),
               "full_vs_fine_channel_response_error": float(np.linalg.norm(decoded-continuum_decoded, 2)/np.linalg.norm(continuum_decoded, 2)),
               "pde_relative_residuals": residual.tolist(), "off_polarization_field_fraction": float(off_polarization),
               "material_continuous_enclosure": [1., float(1+max(v)/np.e)],
               "hostname": platform.node(), "seconds": time.perf_counter()-start, **info}
        rows.append(row)
        write_json(output / "verification.json", rows)
        if max(residual) > 1e-8:
            raise RuntimeError("Full Maxwell verification failed its algebraic residual check")
        if h == min(spacings):
            np.savez_compressed(output / "fields.npz", fields=fields, sources=sources,
                                probes=b, material=material, lengths=lengths, h=h,
                                centers=centers, decoded=decoded, target=target)
        print(json.dumps(row), flush=True)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="command", required=True)
    cal = sub.add_parser("calibrate")
    cal.add_argument("--spacing", type=float, default=.005)
    cal.add_argument("--separation", type=float, default=4.)
    cal.add_argument("--output", type=Path, required=True)
    val = sub.add_parser("verify")
    val.add_argument("--reference", type=Path, required=True)
    val.add_argument("--output", type=Path, required=True)
    val.add_argument("--name", choices=("chain3", "nonuniform3", "indefinite3", "chain4", "mediator2"), required=True)
    val.add_argument("--h", type=float, nargs="+", default=(1/16, 1/20, 1/22))
    val.add_argument("--solver", choices=("direct", "cudss"), default="cudss")
    val.add_argument("--order", type=int, choices=(8, 12), default=12)
    val.add_argument("--buffer-extra", type=float, default=0.)
    args = p.parse_args()
    with threadpool_limits(2):
        if args.command == "calibrate":
            calibrate(args.output, args.spacing, separation=args.separation)
        else:
            verify(args.reference, args.output, args.name, args.h, args.solver, args.order, args.buffer_extra)


if __name__ == "__main__":
    main()
