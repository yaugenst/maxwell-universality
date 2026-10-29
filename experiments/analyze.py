#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=2,<3", "matplotlib>=3.9,<4"]
# ///
"""Generate source-traced plots, numerical summary and report from saved receipts."""
import argparse
import csv
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Circle
import numpy as np


def read(path):
    return json.loads(Path(path).read_text())


def response(path):
    d = read(path / "triple.json")
    return np.array(d["response_real"])+1j*np.array(d["response_imag"])


def rel(a, b):
    return float(np.linalg.norm(a-b)/np.linalg.norm(b))


def cell_intensity(saved, column=0):
    n = saved["shape"]
    shapes = [(n[0], n[1]-1, n[2]-1), (n[0]-1, n[1], n[2]-1), (n[0]-1, n[1]-1, n[2])]
    offsets = np.r_[0, np.cumsum([np.prod(s) for s in shapes])]
    intensity = np.zeros(n)
    for component in range(3):
        v = saved["fields"][offsets[component]:offsets[component+1], column].reshape(shapes[component])
        for axis in range(3):
            if axis == component:
                continue
            pad = [(0, 0)]*3
            pad[axis] = (1, 1)
            v = np.pad(v, pad)
            a, b = [slice(None)]*3, [slice(None)]*3
            a[axis], b[axis] = slice(None, -1), slice(1, None)
            v = (v[tuple(a)]+v[tuple(b)])/2
        intensity += abs(v)**2
    return intensity


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--results", type=Path, default=Path("results"))
    parser.add_argument("--output", type=Path, default=Path("report"))
    args = parser.parse_args()
    root, out = args.results, args.output
    out.mkdir(exist_ok=True)
    base = root/"gpu_suite/gadget_o8_h02"
    fine = root/"followup/gadget_o8_h0167"
    gbase, gfine = response(base), response(fine)
    comparison_base = read(base/"comparison.json")
    comparison_fine = read(fine/"comparison.json")
    buffer_changes = {name: rel(response(root/"gpu_suite"/name), gbase)
                      for name in ("buffer_z_h02", "buffer_xy_h02")}
    perturbations = {name: rel(response(root/"gpu_suite"/name), gbase)
                     for name in ("strength_low_h02", "strength_high_h02", "absorption001_h02", "absorption01_h02")}
    mode_names = ("modes_o8_h025", "modes_o8_h02", "modes_radius2_h0333")
    mode_results = {n: read(root/"followup"/n/"single_modes.json") for n in mode_names}
    modal_names = ("modal_h025", "modal_h02", "modal_radius2_h0333")
    modal = {n: read(root/"modal"/n/"modal_comparison.json") for n in modal_names}
    control = read(root/"tuned_control/fixed_device_refinement.json")
    control_worst = [float(np.linalg.norm(np.array(d["target"])@np.array(d["decoded_solutions"])[:, :2]-np.eye(2), 2)) for d in control]
    if max(control_worst[1:]) >= .001 or any(d["worst_terminal_equation_residual"] <= .1 for d in modal.values()):
        raise ValueError("The saved results no longer support this report's stated outcomes; revise the interpretation.")
    summary = {
        "cpu_gpu_response_difference": read(root/"cpu_gpu_comparison.json"),
        "fixed_device_response_change_h02_to_h0167": rel(gbase, gfine),
        "fixed_device_inverse_response_change_h02_to_h0167": rel(np.linalg.inv(gbase), np.linalg.inv(gfine)),
        "fixed_device_bypass_ratio_change_h02_to_h0167": abs(comparison_base["direct_terminal_to_neighbor_inverse_ratio"]/comparison_fine["direct_terminal_to_neighbor_inverse_ratio"]-1),
        "buffer_relative_response_changes": buffer_changes,
        "perturbation_relative_response_changes": perturbations,
        "best_single_defect_inside_L2_squared_fraction": {n: max(m["inside_single_defect_energy_fraction"] for m in d["modes"]) for n, d in mode_results.items()},
        "modal_decoded_relative_residuals": {n: d["decoded_relative_equation_residuals"] for n, d in modal.items()},
        "modal_worst_terminal_residuals": {n: d["worst_terminal_equation_residual"] for n, d in modal.items()},
        "modal_full_support_identity_errors": {n: d["woodbury_identity_relative_error"] for n, d in modal.items()},
        "full_cavity_control_grid_spacings": [d["h"] for d in control],
        "full_cavity_control_worst_measured_equation_residual": control_worst,
        "gate": "Local compilation gate FAIL; a separately calibrated full-cavity device solves the fixed two-variable target with sub-0.1-percent residual on two finer grids",
    }
    (out/"summary.json").write_text(json.dumps(summary, indent=2)+"\n")
    with (out/"case_metrics.csv").open("w") as f:
        writer = csv.writer(f)
        writer.writerow(["case", "order", "h", "unknowns", "solver", "max_discrete_residual", "accepted_discrete_solve", "outside_supports_center_L2_squared_fraction", "elapsed_seconds"])
        for meta in sorted(root.rglob("metadata.json")):
            result = meta.with_name("triple.json")
            if not result.exists():
                continue
            m, d = read(meta), read(result)
            writer.writerow([str(meta.parent.relative_to(root)), m["config"].get("order", 2), m["config"]["h"], m["unknowns"],
                             d.get("solver", "direct"), max(d["discrete_relative_residuals"]), max(d["discrete_relative_residuals"]) < 1e-8,
                             d["outside_all_probe_supports_energy_fraction"][1], d["total_seconds"]])

    plt.rcParams.update({"font.size": 10, "axes.spines.top": False, "axes.spines.right": False,
                         "savefig.dpi": 180, "font.family": "DejaVu Sans"})
    fig, axes = plt.subplots(3, 2, figsize=(12, 12), constrained_layout=True)
    saved = np.load(root/"modal/modal_h02/modal_data.npz")
    lengths, n = saved["lengths"], saved["shape"]
    extent = [-lengths[2]/2, lengths[2]/2, -lengths[0]/2, lengths[0]/2]
    center_rows = slice(n[1]//2-1, n[1]//2+1)
    material = saved["eps_cells"][:, center_rows, :].mean(axis=1)
    intensity = cell_intensity(saved)[:, center_rows, :].mean(axis=1)
    for ax in axes[0]:
        ax.set_xlabel("z (length units; frequency = 1)")
        ax.set_ylabel("x")
        for z in (-2, 0, 2):
            ax.add_patch(Circle((z, 0), 1, fill=False, color="white", linewidth=1, linestyle="--"))
    im = axes[0, 0].imshow(material, origin="lower", extent=extent, aspect="equal", cmap="viridis")
    fig.colorbar(im, ax=axes[0, 0], label="Scalar permittivity")
    axes[0, 0].set_title("a  Medium from the local three-mode design", loc="left", weight="bold")
    im = axes[0, 1].imshow(np.log10(np.maximum(intensity/intensity.max(), 1e-6)), origin="lower",
                           extent=extent, aspect="equal", cmap="magma", vmin=-4, vmax=0)
    fig.colorbar(im, ax=axes[0, 1], label="log₁₀ relative |E|²")
    axes[0, 1].set_title("b  Full Maxwell field, left terminal input", loc="left", weight="bold")

    ax = axes[1, 0]
    coarse = [root/"gadget_h05", root/"gadget_h0333", root/"gadget_h025"]
    high = [root/"triple_o8_h05", root/"triple_o8_h0333", root/"gpu_suite/gadget_o8_h025", base]
    for paths, label, color in ((coarse, "Second order", "#888888"), (high, "Eighth order", "#2166ac")):
        hs = [read(p/"metadata.json")["config"]["h"] for p in paths]
        ax.loglog(hs, [rel(response(p), gfine) for p in paths], "o-", label=label, color=color)
    ax.axhline(.05, color="#b2182b", linestyle=":", label="5% criterion")
    ax.set(xlabel="Grid spacing h", ylabel="Relative response difference",
           title="c  Fixed-strength baseline refinement (v = 24)")
    ax.legend(fontsize=9)

    ax = axes[1, 1]
    x = np.arange(4)
    for i, name in enumerate(modal_names[:2]):
        ax.bar(x+(i-.5)*.35, modal[name]["decoded_relative_equation_residuals"], .32,
               label=f"h = {read(root/'modal'/name/'metadata.json')['config']['h']}")
    ax.axhline(.1, color="#b2182b", linestyle=":", label="10% criterion")
    ax.set_xticks(x, ["(1, 0)", "(0, 1)", "(1, −1)", "(1, 1)"])
    ax.set(xlabel="Programmed right-hand side b", ylabel="‖Γx − b‖ / ‖b‖",
           title="d  Decoded target: Γ = [[3, 1], [1, 3]]")
    ax.legend(fontsize=9)

    ax = axes[2, 0]
    ax.bar(["Longitudinal buffer", "Transverse buffer"], list(buffer_changes.values()), color=["#4393c3", "#2166ac"])
    ax.axhline(.05, color="#b2182b", linestyle=":")
    ax.set(ylabel="Relative response change", title="e  Fixed-strength baseline: cavity sensitivity")
    ax.text(.03, .94, "Defects and probes unchanged; PEC walls moved", transform=ax.transAxes, va="top", fontsize=9)

    ax = axes[2, 1]
    for name, label, marker in zip(mode_names, ["R=1, h=0.25", "R=1, h=0.2", "R=2, h=1/3 (exploratory)"], ["o", "+", "^"]):
        rows = mode_results[name]["modes"]
        ax.scatter([d["resonant_strength"] for d in rows], [100*d["inside_single_defect_energy_fraction"] for d in rows], label=label, marker=marker)
    ax.set(xlabel="Defect strength at a cavity resonance", ylabel="Electric L² norm squared inside defect (%)",
           title="f  Full-background single-defect mode search")
    ax.legend(fontsize=8)
    fig.suptitle("The local three-mode approximation fails at the tested compact parameters", fontsize=14, weight="bold")
    fig.savefig(out/"three_defect_results.png")
    fig.savefig(out/"three_defect_results.pdf")
    plt.close(fig)

    fig, ax = plt.subplots(2, 2, figsize=(12, 8), constrained_layout=True)
    control_saved = np.load(root/"tuned_control"/f"refine_h{control[-1]['h']:.8g}"/"decoded_fields.npz")
    ny = int(control_saved["shape"][1])
    mid = slice(ny//2, ny//2+1) if ny % 2 else slice(ny//2-1, ny//2+1)
    eps = control_saved["eps_cells"][:, mid, :].mean(axis=1)
    intensity = cell_intensity(control_saved)[:, mid, :].mean(axis=1)
    for a in ax[0]:
        a.set(xlabel="z", ylabel="x")
        for z in (-2, 0, 2):
            a.add_patch(Circle((z, 0), 1, fill=False, color="white", linewidth=1, linestyle="--"))
    im = ax[0, 0].imshow(eps, origin="lower", extent=extent, cmap="viridis", aspect="equal")
    fig.colorbar(im, ax=ax[0, 0], label="Scalar permittivity")
    ax[0, 0].set_title("a  Fixed dielectric after full-cavity calibration", loc="left")
    im = ax[0, 1].imshow(np.log10(np.maximum(intensity/intensity.max(), 1e-6)), origin="lower",
                         extent=extent, cmap="magma", vmin=-4, vmax=0, aspect="equal")
    fig.colorbar(im, ax=ax[0, 1], label="log₁₀ relative |E|²")
    ax[0, 1].set_title("b  Full Maxwell field for b = (1, 0)", loc="left")
    a = ax[1, 0]
    decoded = np.array(control[-1]["decoded_solutions"])
    expected = np.linalg.solve(np.array(control[-1]["target"]), np.array(control[-1]["right_hand_sides"]))
    rows = [[b, f"{expected[0,i]:.3f}", f"{expected[1,i]:.3f}", f"{decoded[0,i]:.6f}", f"{decoded[1,i]:.6f}"]
            for i, b in enumerate(["(1, 0)", "(0, 1)", "(1, −1)", "(1, 1)"])]
    a.axis("off")
    table = a.table(cellText=rows, colLabels=["b", "Exact x₁", "Exact x₂", "Field x₁", "Field x₂"], cellLoc="center", loc="center")
    table.auto_set_font_size(False)
    table.set_fontsize(10)
    table.scale(1, 2.1)
    a.set_title("c  Γx = b, Γ = [[3, 1], [1, 3]]", loc="left")
    a.text(.02, .08, "Same medium, source kernels and decoder for every input.\nValues shown on the finest verification grid (h = 2/13).", transform=a.transAxes, fontsize=9)
    a = ax[1, 1]
    for i, d in enumerate(control[1:]):
        a.bar(np.arange(4)+(i-.5)*.35, 100*np.array(d["decoded_relative_residuals"]), .32,
              label="h = 1/6" if i == 0 else "h = 2/13")
    a.set_xticks(np.arange(4), ["(1, 0)", "(0, 1)", "(1, −1)", "(1, 1)"])
    a.set(xlabel="Right-hand side b", ylabel="Relative equation residual (%)",
          title="d  Verification on finer grids, without retuning")
    a.legend()
    fig.suptitle("Full Maxwell simulation of a calibrated two-variable solver", fontsize=15, weight="bold")
    fig.savefig(out/"calibrated_device.png")
    fig.savefig(out/"calibrated_device.pdf")
    plt.close(fig)

    modal_rows = "\n".join(f"| {name} | {', '.join(f'{v:.5g}' for v in d['strengths'])} | {max(d['decoded_relative_equation_residuals']):.4g} | {d['direct_to_neighbor_background_coupling_ratio']:.4g} | {d['woodbury_identity_relative_error']:.2e} |" for name, d in modal.items())
    report = f"""# Three-defect Maxwell feasibility experiment — 29 October 2026

The full vector implementation and first numerical study are complete. **A three-defect dielectric, calibrated against the full cavity response, solves a fixed two-variable system with less than 0.1% relative equation residual on finer grids without retuning.** The simple local-gadget approximation fails at these compact parameters. These are distinct findings: the first is a numerical small-device demonstration; the second identifies an obstacle to reusable local compilation. Neither is a certificate for the continuum theorem. No manuscript files were changed.

![Calibrated device and independent refinement](calibrated_device.png)

## Positive control: a fixed physical device

The target is `Γ = [[3,1],[1,3]]`. Full-cavity calibration changes only the three scalar defect strengths to `{control[-1]['strengths']}`. The continuous material lies within `{control[-1]['material_continuous_enclosure']}`. Source programming and decoding remain local linear operations; no target solve is used during those operations.

Calibration uses the entire finite-support background response and therefore **does not establish the theorem's scalable local encoder**. It takes five Newton updates to fit the target Schur complement. An independent full Maxwell solve then verifies the device. The near-machine-precision residual on its calibration grid is not treated as independent continuum evidence.

For that evidence, the material, source functions and decoder are frozen. Each source/readout function is explicitly defined as the analytic compact bump times a fixed cubic cardinal-spline interpolant of its reference background mode. The two verification grids have {control[1]['unknowns']:,} and {control[2]['unknowns']:,} electric unknowns. Their worst-case residuals for the measured linear two-port response are **{100*control_worst[1]:.4f}% and {100*control_worst[2]:.4f}%**, respectively. This is numerical refinement evidence for a small calibrated continuum device, not a rigorous continuum error enclosure or a hardware demonstration. Fabrication tolerance and buffer robustness of this specifically retuned device have not been established by the baseline controls below.

## Local-gadget diagnostics

![Measured experiment](three_defect_results.png)

Panels a, b and d use the local three-mode design. Panels c and e use the separate fixed-strength baseline (`v_i=24`) and Bloch-envelope probes; panel c uses the eighth-order `h=1/6` result as its numerical reference. Panel f searches single-defect resonances. None of these baseline sensitivity measurements is a measurement of the separately retuned device above.

## What was actually implemented

The physical solve is `(curl curl - epsilon) E = f` at frequency and permeability one, with real scalar positive dielectric and PEC boundaries. All vector components, gradient modes and other wave channels are present. The original compatible second-order Yee implementation is retained as a comparison; the production study uses an eighth-order compatible staggered curl and point evaluation of the same smooth scalar material. No selected-band filter or three-mode operator replaces the full Maxwell solve.

The baseline has a `6 x 6 x 10` cavity, radius-one defects at `(0,0,-2)`, `(0,0,0)`, `(0,0,2)`, background modulation 0.5 and detuning 0.3. Fixed-strength measurements use strength 24. The calibrated modal experiment chooses three strengths from independent single-defect background modes; its resulting material bounds are saved in each receipt.

Two distinct reduced models are tested. The initial `gadget` command predicts the operational volume-moment response from single and pair devices. That is a portability diagnostic, **not** the proof's defect-polarization matrix. The `modal` command uses the appropriate matrix `T = V^-1 - Q A_background^-1 Q`, calibrates the actual full-background single-defect modes, and then tunes the intended nearest-neighbour three-mode Schur complement to `alpha * Γ`, where `Γ = [[3,1],[1,3]]`.

For each of four right-hand sides, it programs `r_terminals = alpha*b`, `r_mediator = 0`, drives the physical source `f = B V r`, and decodes `x = (V r + V B^T E)_terminals`. Here `B = Q U` consists of compact volume templates. **No solve of Γ is used in source programming or decoding.** The same material handles all four right-hand sides by linear superposition of separately computed full-field responses. Calibration solves the background Maxwell problem and is fully included in the recorded computation; this is a three-site experiment, not the uniform arbitrary-matrix compiler.

## Measured outcome

| Modal case | Programmed strengths (left, middle, right) | Largest decoded relative residual | Direct / neighbour background coupling | Full-support identity error |
| --- | --- | ---: | ---: | ---: |
{modal_rows}

Each modal receipt also compares the nearest-neighbour approximation with the model retaining all three pair interactions. The actual Maxwell response is independently checked against the **full-support** compressed resolvent, including every defect coordinate. Agreement there separates numerical/algebraic correctness from failure of the single-mode and locality approximations.

For the fixed-strength baseline (`v_i=24`, original Bloch-envelope probes), changing only the longitudinal cavity buffer changes the response by {buffer_changes['buffer_z_h02']:.3g} times its original norm; changing the transverse buffer changes it by {buffer_changes['buffer_xy_h02']:.3g}. These are different lossless cavities. The measurement tests whether their response near the same defects is insensitive to distant walls; it is not.

The full-background central-defect search numerically enumerates every positive compressed-resolvent eigenvalue whose resonant strength lies in the conservative material-admissible interval. At radius one, the most confined computed mode has only **{100*summary['best_single_defect_inside_L2_squared_fraction']['modes_o8_h02']:.2f}% of `||E||_2^2` inside the defect**, versus {100*summary['best_single_defect_inside_L2_squared_fraction']['modes_o8_h025']:.2f}% on the preceding mesh. This diagnostic does not depend on selecting the initial Bloch readout template. The exploratory radius-two search reaches {100*summary['best_single_defect_inside_L2_squared_fraction']['modes_radius2_h0333']:.2f}%, but changes radius, cavity size and detuning together and has not completed a refinement study. It does not isolate the effect of radius alone. These fractions are **unweighted electric-field L2 norms squared**, not total electromagnetic energy or radiated-power fractions.

## Numerical checks and their limits

- The analytic, variable-material PEC cavity test gives observed order {read(root/'validation_order8/validation.json')['last_observed_order']:.3f}; `curl grad = 0` and operator symmetry are checked. Second-order validation is also retained.
- CPU SuperLU and GPU cuDSS response matrices agree to {summary['cpu_gpu_response_difference']['relative_response_difference']:.2e} relative error on the same coarse matrix. All accepted physical solves meet the `1e-8` discrete residual threshold. The failed low-order-preconditioned GMRES experiment is retained in `results/triple_o8_gmres_h05` and excluded from physical conclusions; its source snapshot preserves the attempted method.
- The fixed-strength baseline response changes by {100*summary['fixed_device_response_change_h02_to_h0167']:.3g}% between `h=0.2` and `h=1/6`. Its inverse response changes by {100*summary['fixed_device_inverse_response_change_h02_to_h0167']:.3g}%, and the extracted bypass ratio by {100*summary['fixed_device_bypass_ratio_change_h02_to_h0167']:.3g}%. Thus the response is substantially better resolved than on the initial meshes, but not every interaction metric meets the prospective 5% refinement gate.
- Modal designs are recalibrated on each mesh; those rows are consistency checks of the calibration, not a fixed-material convergence proof. The radius-two and changed-detuning variants are exploratory. Small residuals certify solutions of the discretized systems, not rigorous continuum error bounds.
- Uniform ±1% strength changes and absorption diagnostics are recorded in `summary.json`. Absorbing media are separate controls outside the lossless theorem.

## Consequence for the implementation effort

The infrastructure now generates a scalar medium, calibrates modes and couplings, programs sources, solves the full field, reads volume moments, and decodes a concrete two-variable target. The full-cavity control succeeds for that target; the simpler local construction does not. The diagnostics distinguish wall sensitivity, direct bypass and discarded-mode effects. Scaling up a compiler on the local approximation would not yet be justified.

The next useful research step is to obtain a physically useful single-defect mode and interaction hierarchy at manageable scales, then repeat this protocol. Larger, smoother defects and a better-separated practical band regime are candidates. A different language alone would not fix the measured locality problem. The original theorem's sufficient constants, its asymptotic bounds, an arbitrary sparse-system compiler, fabrication, and hardware speed or energy advantage remain outside this experiment.

## Reproduction and artifacts

See [the protocol](../README.md), [solver](../maxwell.py), and [sequential GPU suite](../run_suite.py). [Summary JSON](summary.json) and [case table](case_metrics.csv) are generated directly from result receipts. Each recent run retains its exact executed source and dependency versions; process receipts contain commands and exit status. Each job used one GPU, with two host numerical-library threads and no concurrent experiment jobs. Timings are resource records, not a solver performance benchmark. Run `uv run --script analyze.py` to regenerate this report and its [vector figure](three_defect_results.pdf).
"""
    (out/"REPORT.md").write_text(report)
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
