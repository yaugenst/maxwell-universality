#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=2,<3", "scipy>=1.14,<2", "threadpoolctl>=3,<4"]
# ///
"""Full-vector PEC Maxwell experiment. See README.md for scope and conventions.

Examples:
  uv run --script maxwell.py validate --output results/validation
  uv run --script maxwell.py screen --output results/screen
  uv run --script maxwell.py gadget --strength 16 --output results/gadget
"""
from __future__ import annotations

import argparse
from dataclasses import asdict, dataclass
from hashlib import sha256
from itertools import product
import json
import os
from pathlib import Path
import platform
import resource
import time

import numpy as np
import scipy
from scipy import sparse
from scipy.linalg import eigh
from scipy.sparse.linalg import splu
from threadpoolctl import threadpool_limits


def write_json(path, data):
    Path(path).write_text(json.dumps(data, indent=2, allow_nan=False) + "\n")


def kron3(a, b, c):
    return sparse.kron(sparse.kron(a, b, format="csr"), c, format="csr")


def solve_system(a, rhs, backend):
    start = time.perf_counter()
    if backend == "direct":
        factor = splu(a, permc_spec="COLAMD")
        factor_seconds = time.perf_counter() - start
        fields = factor.solve(rhs.astype(a.dtype))
        factor_nnz = factor.L.nnz + factor.U.nnz
        backend_version = scipy.__version__
    else:
        import nvmath
        from nvmath.sparse.advanced import DirectSolver
        with DirectSolver(a.tocsr(), np.asfortranarray(rhs.astype(a.dtype))) as solver:
            solver.plan()
            fac_info = solver.factorize()
            factor_seconds = time.perf_counter() - start
            solver.solution_config.ir_num_steps = 5
            fields = solver.solve()
            factor_nnz = int(fac_info.lu_nnz)
        backend_version = nvmath.__version__
    return fields, {"factor_seconds": factor_seconds, "factor_nnz": factor_nnz,
                    "solver": backend, "backend_version": backend_version}


def derivative(n, h, order=2):
    """Interior nodal values -> cell-centred derivative, zero endpoint values."""
    width = order // 2
    distances = np.arange(width) + .5
    moments = np.array([2*distances**(2*j+1) for j in range(width)])
    weights = np.linalg.solve(moments, np.eye(width)[0])
    rows, cols, data = [], [], []
    for i in range(n):
        for j, weight in enumerate(weights):
            for node, sign in ((i+1+j, 1), (i-j, -1)):
                # Odd continuation of tangential E through a PEC wall.
                if node < 0:
                    node, sign = -node, -sign
                if node > n:
                    node, sign = 2*n-node, -sign
                if 0 < node < n:
                    rows.append(i)
                    cols.append(node-1)
                    data.append(sign*weight/h)
    return sparse.coo_matrix((data, (rows, cols)), shape=(n, n-1)).tocsr()


class Grid:
    def __init__(self, lengths, h, order=2, max_unknowns=180_000):
        self.h = h
        self.lengths = np.array(lengths, float)
        self.n = np.rint(self.lengths / h).astype(int)
        if np.max(abs(self.n * h - self.lengths)) > 1e-10 or min(self.n) < max(2, order//2):
            raise ValueError("Each box length must contain an integer number of cells, at least half the derivative order.")
        nx, ny, nz = self.n
        self.shapes = [(nx, ny - 1, nz - 1), (nx - 1, ny, nz - 1), (nx - 1, ny - 1, nz)]
        self.offsets = np.r_[0, np.cumsum([np.prod(s) for s in self.shapes])]
        self.size = int(self.offsets[-1])
        # A single sparse factorization can dominate memory. Increase only after inspecting cost.
        if self.size > max_unknowns:
            raise ValueError(f"{self.size} unknowns exceeds this run's {max_unknowns}-unknown resource cap")
        dn = [derivative(n, h, order) for n in self.n]
        ident = [sparse.eye(n, format="csr") for n in self.n]
        interior = [sparse.eye(n - 1, format="csr") for n in self.n]
        dx, dy, dz = dn
        ix, iy, iz = ident
        jx, jy, jz = interior
        self.curl = sparse.bmat([
            [None, -kron3(jx, iy, dz), kron3(jx, dy, iz)],
            [kron3(ix, jy, dz), None, -kron3(dx, jy, iz)],
            [-kron3(ix, dy, jz), kron3(dx, iy, jz), None],
        ], format="csr")
        self.stiffness = (self.curl.T @ self.curl).tocsc()
        self.gradient = sparse.vstack([kron3(dx, jy, jz), kron3(jx, dy, jz),
                                       kron3(jx, jy, dz)], format="csr")
        self.axes = []
        for component in range(3):
            self.axes.append([
                (np.arange(n) + .5) * h - length / 2 if j == component
                else np.arange(1, n) * h - length / 2
                for j, (n, length) in enumerate(zip(self.n, self.lengths))])
        self.xyz = [np.meshgrid(*axes, indexing="ij") for axes in self.axes]
        self.cells = np.meshgrid(*[(np.arange(n) + .5) * h - l / 2
                                  for n, l in zip(self.n, self.lengths)], indexing="ij")

    def edge_average(self, cells):
        """One scalar cell material, averaged over four cells incident on each edge."""
        result = []
        for component in range(3):
            v = cells
            for axis in range(3):
                if axis != component:
                    a, b = [slice(None)] * 3, [slice(None)] * 3
                    a[axis], b[axis] = slice(None, -1), slice(1, None)
                    v = (v[tuple(a)] + v[tuple(b)]) / 2
            result.append(v.ravel())
        return np.concatenate(result)

    def flatten(self, values):
        return np.concatenate([v.ravel() for v in values])

    def unpack(self, v):
        return [v[self.offsets[j]:self.offsets[j + 1]].reshape(self.shapes[j]) for j in range(3)]


def bump(xyz, center, radius, square_root=False):
    r2 = sum(((x - c) / radius) ** 2 for x, c in zip(xyz, center))
    v = np.zeros_like(r2)
    inside = r2 < 1
    v[inside] = np.exp(-(.5 if square_root else 1.) / (1 - r2[inside]))
    return v


class BlochMode:
    """Finite plane-wave approximation at k*; used only to define local probes.

    The physical Maxwell solve below contains the entire Yee field space.
    Symmetric antiperiodic alias sets preserve real standing-wave parity.
    """
    def __init__(self, rho, cutoff=3, q=(0., 0., 0.)):
        self.cutoff, self.rho = cutoff, rho
        self.ns = np.array(list(product(range(-cutoff, cutoff), repeat=3)))
        self.p = np.pi * (self.ns + .5) + np.array(q)
        size = len(self.ns)
        a = np.zeros((3 * size, 3 * size))
        lookup = {tuple(n): i for i, n in enumerate(self.ns)}
        for i, (n, p) in enumerate(zip(self.ns, self.p)):
            a[3*i:3*i+3, 3*i:3*i+3] = (p @ p - 7) * np.eye(3) - np.outer(p, p)
            for j, weight in enumerate((rho/2, rho, 2*rho)):
                for sign in (-1, 1):
                    m = n.copy()
                    m[j] += sign
                    other = lookup.get(tuple(m))
                    if other is not None:
                        a[3*i:3*i+3, 3*other:3*other+3] -= weight * np.eye(3)
        values, vectors = eigh(a)
        e0 = 3 * np.pi**2 / 4 - 7
        cluster = np.flatnonzero(abs(values - e0) < 4*rho)
        if len(cluster) != 16:
            raise ValueError(f"Expected 16 corner-cluster eigenvalues, got {len(cluster)}")
        idx = cluster[-1]
        self.ec = float(values[idx])
        self.gap = float(values[idx] - values[cluster[-2]])
        self.coeff = vectors[:, idx].reshape(2*cutoff, 2*cutoff, 2*cutoff, 3)
        self.eigen_residual = float(np.linalg.norm(a @ vectors[:, idx] - self.ec * vectors[:, idx]))
        # For the selected parity, the physical standing wave is purely imaginary.
        # Fix a reproducible global sign without using the later device response.
        largest = np.unravel_index(np.argmax(abs(self.coeff)), self.coeff.shape)
        self.coeff *= np.sign(self.coeff[largest])

    def component(self, axes, component):
        p = np.pi * (np.arange(-self.cutoff, self.cutoff) + .5)
        factors = [np.exp(1j * np.outer(x, p)) for x in axes]
        field = np.einsum("xa,yb,zc,abc->xyz", *factors, self.coeff[..., component], optimize=True)
        if np.linalg.norm(field.real) > 1e-8 * max(1., np.linalg.norm(field.imag)):
            raise ValueError("Selected Bloch mode did not have expected real standing-wave parity")
        return field.imag

    def metadata(self):
        return {"rho": self.rho, "cutoff": self.cutoff, "ec": self.ec,
                "corner_gap": self.gap, "eigen_residual": self.eigen_residual}


@dataclass
class Config:
    lengths: tuple = (6., 6., 10.)
    h: float = .5
    rho: float = .5
    detuning: float = .3
    radius: float = 1.
    separation: float = 2.
    strength: float = 16.
    absorption: float = 0.
    order: int = 2
    solver: str = "direct"
    centers: tuple | None = None


class Experiment:
    def __init__(self, config, output):
        self.config = config
        self.output = Path(output)
        self.output.mkdir(parents=True, exist_ok=False)
        (self.output / "executed_source.py").write_bytes(Path(__file__).read_bytes())
        self.mode = BlochMode(config.rho)
        self.grid = Grid(config.lengths, config.h, config.order,
                         max_unknowns=400_000 if config.solver == "cudss" else 180_000)
        self.centers = (config.centers if config.centers is not None else
                        [(0., 0., z) for z in (-config.separation, 0., config.separation)])
        centers = np.asarray(self.centers, dtype=float)
        if centers.ndim != 2 or centers.shape[1] != 3 or len(centers) == 0:
            raise ValueError("Defect centres must be a nonempty list of three-dimensional coordinates")
        if any(np.linalg.norm(a-b) < 2*config.radius-1e-12
               for i, a in enumerate(centers) for b in centers[i+1:]):
            raise ValueError("The defect supports must not overlap")
        if np.any(abs(centers)+config.radius >= np.array(config.lengths)/2):
            raise ValueError("Defects must be strictly inside the PEC box")
        cell_xyz = self.grid.cells
        self.base = 7 + self.mode.ec - config.detuning + config.rho * sum(
            2**j * np.cos(np.pi * x) for j, x in enumerate(cell_xyz))
        self.wells = [bump(cell_xyz, c, config.radius) for c in self.centers]
        self.edge_base = self.grid.flatten([
            7 + self.mode.ec - config.detuning + config.rho*sum(2**j*np.cos(np.pi*x) for j, x in enumerate(xyz))
            for xyz in self.grid.xyz])
        self.edge_wells = [self.grid.flatten([bump(xyz, c, config.radius) for xyz in self.grid.xyz])
                           for c in self.centers]
        phi = [self.mode.component(axes, j) for j, axes in enumerate(self.grid.axes)]
        probes, masks = [], []
        for center in self.centers:
            q = [bump(xyz, center, config.radius, square_root=True) for xyz in self.grid.xyz]
            probes.append(self.grid.flatten([a*b for a, b in zip(phi, q)]))
            masks.append(self.grid.flatten([v > 0 for v in q]).astype(bool))
        # Euclidean coordinates represent sqrt(h^3) times physical field values.
        # B columns then approximate orthonormal L2 source/readout templates.
        self.b = np.column_stack(probes)
        self.b /= np.linalg.norm(self.b, axis=0)
        self.supports = np.column_stack(masks)
        gram = self.b.T @ self.b
        if np.linalg.norm(gram - np.eye(len(centers))) > 1e-10:
            raise ValueError("The normalized local probes are not orthogonal")
        write_json(self.output / "metadata.json", {
            "config": asdict(config), "bloch_probe": self.mode.metadata(),
            "unknowns": self.grid.size, "curl_nnz": self.grid.curl.nnz,
            "matrix_nnz": self.grid.stiffness.nnz, "centers": self.centers,
            "probe_gram": gram.tolist(), "python": platform.python_version(),
            "numpy": np.__version__, "scipy": scipy.__version__, "threads": 2,
            "hostname": platform.node(), "cuda_visible_devices": os.environ.get("CUDA_VISIBLE_DEVICES"),
            "code_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
            "scope": "Numerical compact-parameter continuum experiment via Yee refinement; no proof certificate or physical momentum filter",
            "material_sampling": "four-cell average" if config.order == 2 else "continuous scalar material at each electric edge",
        })

    def operator(self, strengths):
        if len(strengths) != len(self.centers):
            raise ValueError("One scalar strength is required for each defect")
        cells = self.base + sum(v*w for v, w in zip(strengths, self.wells))
        # These analytic extrema enclose the continuous material, not only grid samples.
        lower = 7 + self.mode.ec - self.config.detuning - 7*self.config.rho
        upper = 7 + self.mode.ec - self.config.detuning + 7*self.config.rho + max(strengths)/np.e
        if min(strengths) < 0 or lower < 1 or upper > 25:
            raise ValueError(f"Continuous scalar material outside [1,25]: enclosure [{lower}, {upper}]")
        eps = (self.grid.edge_average(cells) if self.config.order == 2 else
               self.edge_base + sum(v*w for v, w in zip(strengths, self.edge_wells)))
        if self.config.absorption:
            eps = eps.astype(complex) + 1j*self.config.absorption
        a = self.grid.stiffness - sparse.diags(eps, format="csc")
        return a, cells, lower, upper

    def solve(self, strengths, name, save_fields=False):
        start = time.perf_counter()
        a, cells, lower, upper = self.operator(strengths)
        fields, solver_info = solve_system(a, self.b, self.config.solver)
        relative = np.linalg.norm(a @ fields - self.b, axis=0)
        response = self.b.T @ fields
        energy = np.sum(abs(fields)**2, axis=0)
        outside = np.sum(abs(fields[~np.any(self.supports, axis=1)])**2, axis=0) / energy
        off_template = 1 - np.sum(abs(response)**2, axis=0)/energy
        inverse = np.linalg.inv(response)
        data = {
            "strengths": list(strengths), "material_continuous_enclosure": [lower, upper],
            "material_sampled_range": [float(cells.min()), float(cells.max())],
            "discrete_relative_residuals": relative.tolist(),
            "response_real": response.real.tolist(), "response_imag": response.imag.tolist(),
            "inverse_response_real": inverse.real.tolist(), "inverse_response_imag": inverse.imag.tolist(),
            "response_condition": float(np.linalg.cond(response)),
            "reciprocity_relative_error": float(np.linalg.norm(response - response.T)/np.linalg.norm(response)),
            "response_column_norms": np.sqrt(energy).tolist(),
            "outside_all_probe_supports_energy_fraction": outside.tolist(),
            "off_template_energy_fraction": off_template.tolist(),
            **solver_info, "total_seconds": time.perf_counter() - start,
            "peak_rss_gib": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 2**20,
        }
        write_json(self.output / f"{name}.json", data)
        if save_fields:
            np.savez_compressed(self.output / f"{name}_fields.npz", fields=fields,
                                probes=self.b, eps_cells=cells, supports=self.supports,
                                shape=self.grid.n, h=self.config.h, lengths=self.config.lengths)
        print(json.dumps({"case": name, "dof": self.grid.size, "seconds": round(data["total_seconds"], 2),
                          "residual": float(max(relative)), "outside_center": float(outside[1]),
                          "response_center": float(response[1, 1].real), "rss_gib": data["peak_rss_gib"]}), flush=True)
        if max(relative) > 1e-8:
            raise RuntimeError(f"Unacceptable linear solve residual in {name}: {relative}")
        return response, data


def single_defect_modes(experiment):
    """Enumerate admissible central-defect resonances of the finite discretization.

    S = Q A_background^-1 Q; each positive eigenvalue mu gives strength 1/mu.
    This full-background calculation is independent of the initial Bloch probe.
    """
    start = time.perf_counter()
    if experiment.config.absorption:
        raise ValueError("The self-adjoint mode diagnostic requires zero absorption")
    a, _, _, upper = experiment.operator([0., 0., 0.])
    well = (experiment.grid.edge_average(experiment.wells[1]) if experiment.config.order == 2
            else experiment.edge_wells[1])
    indices = np.flatnonzero(well > 0)
    q = np.sqrt(well[indices])
    rhs = np.zeros((experiment.grid.size, len(indices)), order="F")
    rhs[indices, np.arange(len(indices))] = q
    response, solver_info = solve_system(a, rhs, experiment.config.solver)
    relative = np.linalg.norm(a @ response-rhs) / np.linalg.norm(rhs)
    compressed = q[:, None] * response[indices]
    symmetry = np.linalg.norm(compressed-compressed.T)/np.linalg.norm(compressed)
    values, vectors = eigh((compressed+compressed.T)/2)
    np.savez_compressed(experiment.output / "compressed_resolvent.npz",
                        compressed=compressed, eigenvalues=values, eigenvectors=vectors, indices=indices)
    maximum_strength = (25-upper)*np.e
    admissible = np.flatnonzero(values >= 1/maximum_strength)
    full_modes = response @ vectors[:, admissible]
    mode_energy = np.sum(full_modes**2, axis=0)
    local_fraction = np.sum(full_modes[indices]**2, axis=0)/mode_energy
    rows = []
    for j, idx in enumerate(admissible):
        strength = 1/values[idx]
        field = full_modes[:, j]
        residual = a @ field-strength*well*field
        rows.append({"eigenvalue": float(values[idx]), "resonant_strength": float(strength),
                     "inside_single_defect_energy_fraction": float(local_fraction[j]),
                     "bloch_probe_overlap_squared": float(abs(experiment.b[:, 1] @ field)**2/mode_energy[j]),
                     "absolute_residual_per_unit_field": float(np.linalg.norm(residual)/np.linalg.norm(field))})
    rows.sort(key=lambda x: x["inside_single_defect_energy_fraction"], reverse=True)
    result = {"scope": "Numerically enumerated positive central-defect resonances within the conservative material-strength interval for this finite grid and cavity; not an infinite-medium or continuum certificate",
              "compressed_dimension": len(indices), "maximum_strength": float(maximum_strength),
              "background_solve_relative_residual": float(relative), "compressed_symmetry_error": float(symmetry),
              "modes": rows, "total_seconds": time.perf_counter()-start, **solver_info}
    write_json(experiment.output / "single_modes.json", result)
    if len(admissible):
        best = int(np.argmax(local_fraction))
        np.savez_compressed(experiment.output / "best_mode.npz", field=full_modes[:, best],
                            source=rhs @ vectors[:, admissible[best]], shape=experiment.grid.n,
                            h=experiment.config.h, lengths=experiment.config.lengths)
    print(json.dumps(result), flush=True)
    if relative > 1e-8 or symmetry > 1e-8:
        raise RuntimeError("Full-background compressed-resolvent calculation failed its residual check")


def modal_gadget(experiment):
    """Calibrate the actual defect-polarization Schur model of the construction.

    Full compressed inverse: T = V^-1 - Q A_background^-1 Q.
    Exact physical identity: U.T T^-1 U = V + V (B.T A_device^-1 B) V,
    where B = Q U and U contains one normalized mode per support.
    No modal projection enters the actual Maxwell solve.
    """
    start = time.perf_counter()
    if experiment.config.absorption:
        raise ValueError("Modal calibration requires the lossless background")
    a0, _, _, upper = experiment.operator([0., 0., 0.])
    wells = ([experiment.grid.edge_average(w) for w in experiment.wells]
             if experiment.config.order == 2 else experiment.edge_wells)
    indices = [np.flatnonzero(w > 0) for w in wells]
    offsets = np.r_[0, np.cumsum([len(i) for i in indices])]
    all_indices = np.concatenate(indices)
    q = np.sqrt(np.concatenate([w[i] for w, i in zip(wells, indices)]))
    rhs = np.zeros((experiment.grid.size, len(q)), order="F")
    rhs[all_indices, np.arange(len(q))] = q
    y, background_info = solve_system(a0, rhs, experiment.config.solver)
    background_residual = np.linalg.norm(a0@y-rhs)/np.linalg.norm(rhs)
    s = q[:, None]*y[all_indices]
    symmetry = np.linalg.norm(s-s.T)/np.linalg.norm(s)
    s = (s+s.T)/2
    vmax = (25-upper)*np.e
    u = np.zeros((len(q), 3))
    local_modes = []
    for i in range(3):
        lo, hi = offsets[i:i+2]
        values, vectors = eigh(s[lo:hi, lo:hi])
        admissible = np.flatnonzero(values > 1/vmax)
        if not len(admissible):
            write_json(experiment.output / "modal_comparison.json", {
                "status": "no_admissible_single_defect_resonance", "site": i,
                "max_eigenvalue": float(values[-1]), "required_minimum": float(1/vmax)})
            return
        overlaps = abs(vectors[:, admissible].T @ experiment.b[indices[i], i])**2
        idx = admissible[np.argmax(overlaps)]
        u[lo:hi, i] = vectors[:, idx]
        local_modes.append({"eigenvalue": float(values[idx]),
                            "probe_mode_overlap_squared": float(max(overlaps)),
                            "gap": float(np.min(abs(np.delete(values, idx)-values[idx])))})
    projected = u.T@s@u
    # Fix the two intended off-diagonals to positive signs by local port signs.
    for i in (0, 2):
        u[:, i] *= -np.sign(projected[i, 1])
    projected = u.T@s@u
    useful = np.sqrt(abs(projected[0, 1]*projected[1, 2]))
    # Choose tunings so eliminating the mediator gives alpha * [[3,1],[1,3]].
    # Half the available central tuning margin is used, preserving epsilon <= 25.
    alpha = 2*useful**2/(projected[1, 1]-1/vmax)
    if alpha <= 0:
        raise RuntimeError("No positive tuning margin or useful neighbor coupling")
    target_diagonal = np.array([alpha*(3-projected[0, 1]**2/useful**2),
                                -useful**2/alpha,
                                alpha*(3-projected[2, 1]**2/useful**2)])
    strengths = 1/(np.diag(projected)+target_diagonal)
    v = np.diag(strengths)
    t_full_modes = np.diag(1/strengths)-projected
    target = t_full_modes.copy()
    target[0, 2] = target[2, 0] = 0
    probes = rhs@u
    actual_a, cells, lower, material_upper = experiment.operator(strengths)
    fields, physical_info = solve_system(actual_a, probes, experiment.config.solver)
    physical_residual = np.linalg.norm(actual_a@fields-probes)/np.linalg.norm(probes)
    physical_g = probes.T@fields
    measured_t_inverse = v+v@physical_g@v
    measured_t = np.linalg.inv(measured_t_inverse)
    # Independent full-support Woodbury check, retaining every defect coordinate.
    full_t = np.diag(np.repeat(1/strengths, np.diff(offsets)))-s
    exact_projected_inverse = u.T@np.linalg.solve(full_t, u)
    identity_error = np.linalg.norm(exact_projected_inverse-measured_t_inverse)/np.linalg.norm(measured_t_inverse)
    terminal = [0, 2]
    predicted_schur, measured_schur = schur_terminals(target), schur_terminals(measured_t)
    gamma = np.array([[3., 1.], [1., 3.]])
    right_hand_sides = np.array([[1., 0., 1., 1.], [0., 1., -1., 1.]])
    # Physical source is B V r; decoder is (V r + V B.T E)_terminals.
    # This is direct source programming and volume readout, with no target solve.
    drive = np.zeros((3, 4))
    drive[terminal] = alpha*right_hand_sides
    decoded = (v@drive+v@physical_g@v@drive)[terminal]
    decoded_residuals = np.linalg.norm(gamma@decoded-right_hand_sides, axis=0)/np.linalg.norm(right_hand_sides, axis=0)
    energy = np.sum(abs(fields)**2, axis=0)
    mask = np.any(experiment.supports, axis=1)
    result = {
        "status": "computed", "model": "Defect-polarization Birman-Schwinger matrix; full physical solve without a momentum or modal filter",
        "mode_selection": "Maximum overlap with the fixed Bloch-envelope probe among positive single-site eigenvalues with material-admissible resonances",
        "local_modes": local_modes, "compressed_dimension": len(q), "strengths": strengths.tolist(),
        "material_continuous_enclosure": [lower, material_upper], "alpha": float(alpha),
        "projected_background": projected.tolist(), "target_nearest_neighbor_matrix": target.tolist(),
        "measured_effective_matrix": measured_t.tolist(),
        "predicted_terminal_schur": predicted_schur.tolist(), "measured_terminal_schur": measured_schur.tolist(),
        "terminal_target_matrix": gamma.tolist(), "test_right_hand_sides": right_hand_sides.tolist(),
        "decoded_solutions": decoded.tolist(), "decoded_relative_equation_residuals": decoded_residuals.tolist(),
        "source_and_decoder": "r_terminals=alpha*b, r_mediator=0; f=B*V*r; x=(V*r+V*B.T*E)_terminals",
        "target_schur_identity_error": float(np.linalg.norm(predicted_schur-alpha*gamma)/(alpha*np.linalg.norm(gamma))),
        "direct_to_neighbor_background_coupling_ratio": float(abs(projected[0, 2])/useful),
        "nearest_neighbor_worst_equation_residual": float(np.linalg.norm(target@measured_t_inverse-np.eye(3), 2)),
        "all_pair_single_mode_worst_equation_residual": float(np.linalg.norm(t_full_modes@measured_t_inverse-np.eye(3), 2)),
        "worst_terminal_equation_residual": float(np.linalg.norm(predicted_schur@measured_t_inverse[np.ix_(terminal, terminal)]-np.eye(2), 2)),
        "relative_terminal_schur_error": float(np.linalg.norm(predicted_schur-measured_schur, 2)/np.linalg.norm(measured_schur, 2)),
        "outside_supports_energy_fraction": (np.sum(abs(fields[~mask])**2, axis=0)/energy).tolist(),
        "background_solve_residual": float(background_residual), "physical_solve_residual": float(physical_residual),
        "compressed_symmetry_error": float(symmetry), "woodbury_identity_relative_error": float(identity_error),
        "background_solver": background_info, "physical_solver": physical_info,
        "total_seconds": time.perf_counter()-start,
    }
    write_json(experiment.output / "modal_comparison.json", result)
    np.savez_compressed(experiment.output / "modal_data.npz", compressed=s, modes=u, indices=all_indices,
                        fields=fields, probes=probes, eps_cells=cells, supports=experiment.supports,
                        shape=experiment.grid.n, h=experiment.config.h, lengths=experiment.config.lengths)
    print(json.dumps(result), flush=True)
    if max(background_residual, physical_residual, symmetry, identity_error) > 1e-8:
        raise RuntimeError("Full operator/modal measurement consistency check failed")


def schur_terminals(k):
    t = [0, 2]
    return k[np.ix_(t, t)] - np.outer(k[t, 1], k[1, t]) / k[1, 1]


def gadget(experiment):
    v = experiment.config.strength
    single = []
    for i in range(3):
        strengths = [0., 0., 0.]
        strengths[i] = v
        g, _ = experiment.solve(strengths, f"single_{i}")
        single.append(1/g[i, i])
    prediction = np.diag(single)
    pair_data = []
    for i, j in ((0, 1), (1, 2)):
        strengths = [0., 0., 0.]
        strengths[i] = strengths[j] = v
        g, _ = experiment.solve(strengths, f"pair_{i}{j}")
        kp = np.linalg.inv(g[np.ix_([i, j], [i, j])])
        # Add independently measured pair corrections to the isolated site values.
        prediction[i, i] += kp[0, 0] - single[i]
        prediction[j, j] += kp[1, 1] - single[j]
        prediction[i, j], prediction[j, i] = kp[0, 1], kp[1, 0]
        pair_data.append(kp)
    actual_g, data = experiment.solve([v, v, v], "triple", save_fields=True)
    actual_k = np.linalg.inv(actual_g)
    predicted_g = np.linalg.inv(prediction)
    pt, at = schur_terminals(prediction), schur_terminals(actual_k)
    bypass = abs(actual_k[0, 2]) / np.sqrt(abs(actual_k[0, 1]*actual_k[1, 2]))
    metrics = {
        "prediction_source": "Single and nearest-pair devices only; no fit to triple response",
        "single_inverse_real": np.real(single).tolist(),
        "predicted_inverse_real": prediction.real.tolist(), "predicted_inverse_imag": prediction.imag.tolist(),
        "actual_inverse_real": actual_k.real.tolist(), "actual_inverse_imag": actual_k.imag.tolist(),
        "predicted_terminal_schur_real": pt.real.tolist(), "predicted_terminal_schur_imag": pt.imag.tolist(),
        "actual_terminal_schur_real": at.real.tolist(), "actual_terminal_schur_imag": at.imag.tolist(),
        "relative_inverse_prediction_error": float(np.linalg.norm(prediction-actual_k, 2)/np.linalg.norm(actual_k, 2)),
        "relative_response_prediction_error": float(np.linalg.norm(predicted_g-actual_g, 2)/np.linalg.norm(actual_g, 2)),
        "relative_terminal_schur_error": float(np.linalg.norm(pt-at, 2)/np.linalg.norm(at, 2)),
        "worst_case_three_port_equation_residual": float(np.linalg.norm(prediction @ actual_g-np.eye(3), 2)),
        "worst_case_terminal_equation_residual": float(np.linalg.norm(pt @ actual_g[np.ix_([0, 2], [0, 2])]-np.eye(2), 2)),
        "direct_terminal_to_neighbor_inverse_ratio": float(bypass),
        "discrete_relative_residuals": data["discrete_relative_residuals"],
    }
    write_json(experiment.output / "comparison.json", metrics)
    print(json.dumps(metrics), flush=True)


def validate(output, order=2):
    output = Path(output)
    output.mkdir(parents=True, exist_ok=False)
    rows = []
    for h in (.5, 1/3, .25, .2, 1/6):
        grid = Grid((2., 2., 2.), h, order)
        p = np.array([np.pi/2]*3)
        amplitude = np.array([1., -1., 0.])
        e = []
        for j, xyz in enumerate(grid.xyz):
            trigs = [np.cos(p[k]*(x+1)) if k == j else np.sin(p[k]*(x+1)) for k, x in enumerate(xyz)]
            e.append(amplitude[j] * trigs[0]*trigs[1]*trigs[2])
        exact = grid.flatten(e)
        eps = grid.flatten([2+.2*np.cos(np.pi*xyz[0])+.3*np.cos(np.pi*xyz[1])+.4*np.cos(np.pi*xyz[2])
                            for xyz in grid.xyz])
        rhs = (p@p - eps)*exact
        a = grid.stiffness - sparse.diags(eps, format="csc")
        computed = splu(a).solve(rhs)
        cg = grid.curl @ grid.gradient
        row = {"h": h, "unknowns": grid.size,
               "relative_solution_error": float(np.linalg.norm(computed-exact)/np.linalg.norm(exact)),
               "relative_solve_residual": float(np.linalg.norm(a@computed-rhs)/np.linalg.norm(rhs)),
               "curl_gradient_max": float(max(abs(cg.data), default=0.)),
               "symmetry_max": float(max(abs((a-a.T).data), default=0.))}
        rows.append(row)
    observed_order = np.log(rows[-2]["relative_solution_error"]/rows[-1]["relative_solution_error"])/np.log(rows[-2]["h"]/rows[-1]["h"])
    modes = [BlochMode(.5, cutoff=n).metadata() for n in (2, 3, 4)]
    passed = (order-.2 < observed_order < order+.3 and max(r["relative_solve_residual"] for r in rows) < 1e-10
              and max(r["curl_gradient_max"] for r in rows) < 1e-10
              and abs(modes[-1]["ec"]-modes[-2]["ec"]) < 2e-6)
    result = {"discretization_order": order, "manufactured_solution": rows, "last_observed_order": float(observed_order),
              "bloch_cutoff_convergence": modes, "passed": bool(passed)}
    write_json(output / "validation.json", result)
    print(json.dumps(result, indent=2), flush=True)
    if not passed:
        raise RuntimeError("Independent Maxwell/PEC validation failed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("validate", "screen", "gadget", "triple", "modes", "modal"))
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--h", type=float, default=.5)
    parser.add_argument("--lengths", type=float, nargs=3, default=(6., 6., 10.))
    parser.add_argument("--rho", type=float, default=.5)
    parser.add_argument("--detuning", type=float, default=.3)
    parser.add_argument("--radius", type=float, default=1.)
    parser.add_argument("--separation", type=float, default=2.)
    parser.add_argument("--strength", type=float, default=16.)
    parser.add_argument("--strengths", type=float, nargs="+", default=(0., 4., 8., 16., 24., 32.))
    parser.add_argument("--absorption", type=float, default=0.)
    parser.add_argument("--order", type=int, choices=(2, 4, 6, 8), default=2)
    parser.add_argument("--solver", choices=("direct", "cudss"), default="direct")
    args = parser.parse_args()
    with threadpool_limits(limits=2):
        if args.command == "validate":
            validate(args.output, args.order)
        else:
            cfg = Config(tuple(args.lengths), args.h, args.rho, args.detuning, args.radius,
                         args.separation, args.strength, args.absorption, args.order, args.solver)
            experiment = Experiment(cfg, args.output)
            if args.command == "screen":
                for v in args.strengths:
                    experiment.solve([0., v, 0.], f"strength_{v:g}")
            elif args.command == "gadget":
                gadget(experiment)
            elif args.command == "modes":
                single_defect_modes(experiment)
            elif args.command == "modal":
                modal_gadget(experiment)
            else:
                experiment.solve([cfg.strength]*3, "triple", save_fields=True)


if __name__ == "__main__":
    main()
