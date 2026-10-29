"""Fixed continuous sources and full-Maxwell verification shared by experiments."""
import numpy as np
from scipy.ndimage import map_coordinates

from maxwell import bump, solve_system, write_json


def frozen_probes(experiment, reference, background_modes, eigenvalues):
    """Sample the same compact cubic-spline source functions on another grid."""
    grid, original = experiment.grid, reference.grid
    probes = np.zeros((grid.size, len(experiment.centers)))
    for site in range(len(experiment.centers)):
        components = original.unpack(background_modes[:, site]/np.sqrt(original.h**3))
        # Source supports remain at their reference positions even when the
        # manufactured material is displaced; such tests pass nominal wells.
        for component in range(3):
            lo, hi = grid.offsets[component:component+2]
            well = bump(grid.xyz[component], reference.centers[site],
                        reference.config.radius).ravel()
            inside = well > 0
            coordinates = np.array([(xyz.ravel()[inside]-axis[0])/original.h
                                    for xyz, axis in zip(grid.xyz[component], original.axes[component])])
            interpolated = map_coordinates(components[component], coordinates, order=3,
                                           mode="constant", cval=0., prefilter=True)
            probes[lo:hi, site][inside] = (np.sqrt(grid.h**3)*well[inside]*interpolated
                                          /eigenvalues[site])
    return probes


def verify_device(experiment, probes, strengths, alpha, target, terminals,
                  nominal_strengths=None, name="verification", save_fields=True):
    """Solve basis sources; the operator norm then covers every right-hand side.

    No inverse/solve of the target matrix enters physical source or decoding.
    A changed material can use the original source/decoder strengths explicitly.
    """
    target = np.asarray(target)
    terminals = np.asarray(terminals)
    nominal = np.asarray(strengths if nominal_strengths is None else nominal_strengths)[terminals]
    port_probes = probes[:, terminals]
    sources = alpha*port_probes*nominal
    a, cells, lower, upper = experiment.operator(strengths)
    fields, info = solve_system(a, sources, experiment.config.solver)
    response = alpha*np.diag(nominal)+nominal[:, None]*(port_probes.T@fields)
    error = target@response-np.eye(len(target))
    pde_residuals = np.linalg.norm(a@fields-sources, axis=0)/np.linalg.norm(sources, axis=0)
    # Reciprocity gives Gamma D A^-1 = Gamma fields.T / alpha.
    # This measures sensitivity to an arbitrary full-field residual, including
    # channels outside the source/probe span, at this finite discretization.
    adjoint_gram = target@(fields.T@fields.conj())@target.T/alpha**2
    source_gram = sources.conj().T@sources
    residual_gain = np.sqrt(max(0., np.linalg.eigvalsh(adjoint_gram)[-1])
                            *max(0., np.linalg.eigvalsh(source_gram)[-1]))
    data = {"target": target.tolist(), "terminals": terminals.tolist(), "alpha": float(alpha),
            "strengths": np.asarray(strengths).tolist(), "nominal_source_decoder_strengths": nominal.tolist(),
            "h": experiment.config.h, "unknowns": experiment.grid.size,
            "lengths": experiment.config.lengths, "material_continuous_enclosure": [lower, upper],
            "decoded_response_real": response.real.tolist(), "decoded_response_imag": response.imag.tolist(),
            "worst_relative_equation_residual": float(np.linalg.norm(error, 2)),
            "per_basis_relative_equation_residuals": np.linalg.norm(error, axis=0).tolist(),
            "discrete_pde_relative_residuals": pde_residuals.tolist(),
            "full_field_relative_residual_amplification_bound": float(residual_gain),
            "residual_bound_scope": "Finite matrix: equation error <= exact-device error + gain * relative Maxwell residual. The product norm bound covers arbitrary field residual directions and every right-hand side; no continuum or asymptotic conditioning claim.",
            **info}
    write_json(experiment.output/f"{name}.json", data)
    if save_fields:
        np.savez_compressed(experiment.output/f"{name}_fields.npz", fields=fields, probes=port_probes,
                            sources=sources, eps_cells=cells, shape=experiment.grid.n,
                            lengths=experiment.config.lengths, h=experiment.config.h)
    if max(pde_residuals) > 1e-8:
        raise RuntimeError(f"Unacceptable full Maxwell solve: {pde_residuals}")
    return data
