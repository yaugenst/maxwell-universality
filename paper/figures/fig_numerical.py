#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["matplotlib>=3.9,<4", "numpy>=2,<3"]
# ///
"""Numerical illustrations from archived Maxwell solutions.

Run ``uv run --script figures/fig_numerical.py`` from the paper directory.
The bundled figure data are sufficient. To re-extract them from the large
simulation archive, add ``--refresh-data --experiment-root PATH``; PATH is
the three_defect directory. No Maxwell solve or fitting is performed here.
"""
from __future__ import annotations

import argparse
from ast import literal_eval
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.colors import LinearSegmentedColormap
from matplotlib.patches import Circle, Polygon
import numpy as np

sys.dont_write_bytecode = True
import figstyle as st

HERE = Path(__file__).resolve().parent
DATA = HERE / "data"
NAMES = {"chain3": "Three-site chain", "nonuniform3": "Unequal diagonals",
         "chain4": "Four-site chain", "mediator2": "Two terminals + mediator",
         "indefinite3": "Indefinite chain"}
DIVERGING = LinearSegmentedColormap.from_list("signed", [st.RED, st.SURFACE, st.BLUE])


def read(path):
    return json.loads(path.read_text())


def portable_record(value):
    """Keep numerical/resource receipts without host identity."""
    if isinstance(value, list):
        return [portable_record(item) for item in value]
    if isinstance(value, dict):
        result = {key: portable_record(item) for key, item in value.items() if key != "hostname"}
        if "solver" in result:
            result["solver"] = {"cudss": "gpu_direct", "direct": "cpu_direct"}.get(result["solver"], result["solver"])
        return result
    return value


def centered_section(values, n, h, component):
    """Interpolate one staggered component to y=0, for display only."""
    shapes = [tuple(n - (np.arange(3) != j)) for j in range(3)]
    offsets = np.r_[0, np.cumsum([np.prod(s) for s in shapes])]
    v = values[offsets[component]:offsets[component + 1]].reshape(
        (*shapes[component], values.shape[1])) / h**1.5
    for axis in range(3):
        if axis == component:
            continue
        pad = [(0, 0)] * 4
        pad[axis] = (1, 1)
        v = np.pad(v, pad)
        a, b = [slice(None)] * 4, [slice(None)] * 4
        a[axis], b[axis] = slice(None, -1), slice(1, None)
        v = (v[tuple(a)] + v[tuple(b)]) / 2
    mid = n[1] // 2
    return (v[:, mid - 1] + v[:, mid]) / 2


def extract(root):
    """Keep full-precision readouts separate from display interpolation."""
    hashes = {}

    def source(relative):
        path = root / relative
        hashes[relative] = sha256(path.read_bytes()).hexdigest()
        return path

    periodic = "results/direct_refinement_a/signed_spd"
    fine = f"{periodic}/h0.14285714"
    verification = read(source(f"{fine}/verification.json"))
    metadata = read(source(f"{fine}/metadata.json"))
    raw = np.load(source(f"{fine}/verification_fields.npz"))
    target = np.array(verification["target"])
    gains = np.array(verification["nominal_source_decoder_strengths"])
    alpha = verification["alpha"]
    response = alpha * np.diag(gains) + gains[:, None] * (raw["probes"].T @ raw["fields"])
    assert np.linalg.norm(response - verification["decoded_response_real"]) < 1e-12
    assert np.linalg.norm(raw["sources"] - alpha * raw["probes"] * gains) < 1e-12
    error = float(np.linalg.norm(target @ response - np.eye(len(target)), 2))
    assert abs(error - verification["worst_relative_equation_residual"]) < 1e-12
    h, n = float(raw["h"]), raw["shape"]
    arrays = {"periodic_ez": centered_section(raw["fields"], n, h, 2)[:, :, 0],
              "periodic_x": (np.arange(n[0]) + .5) * h - 4,
              "periodic_z": (np.arange(n[2]) + .5) * h - 4}
    periodic_data = {"target": target.tolist(), "response": response.tolist(),
                     "operator_error": error, "h": h, "unknowns": len(raw["fields"]),
                     "lengths": raw["lengths"].tolist(), "centers": metadata["centers"],
                     "strengths": verification["strengths"],
                     "material_enclosure": verification["material_continuous_enclosure"],
                     "calibration": read(source(f"{periodic}/design.json")),
                     "intermediate_refinement": read(source(f"{periodic}/h0.15384615/verification.json"))}

    local = "results/local_compilation"
    calibration = read(source(f"{local}/waveguide_calibration/calibration.json"))
    template = np.load(source(f"{local}/waveguide_calibration/template.npz"))
    arrays.update(local_z=template["z"], local_field=template["field"] / np.sqrt(float(template["spacing"])))
    waves = {name: read(source(f"{local}/waveguide_{name}/verification.json")) for name in NAMES}
    checks = {}
    for name in ("chain3", "chain4", "mediator2"):
        folder = f"{local}/waveguide_{name}"
        design = read(source(f"{folder}/frozen_design.json"))
        raw = np.load(source(f"{folder}/fields.npz"))
        h, lengths = float(raw["h"]), raw["lengths"]
        n = np.rint(lengths / h).astype(int)
        shapes = [tuple(n - (np.arange(3) != j)) for j in range(3)]
        offsets = np.r_[0, np.cumsum([np.prod(s) for s in shapes])]
        v, ports = np.array(design["strengths"]), np.array(design["ports"])
        alpha = design["alpha"]
        response = alpha * np.diag(v[ports]) + v[ports, None] * (raw["probes"].T @ raw["fields"])
        source_error = np.linalg.norm(raw["sources"] - alpha * raw["probes"] * v[ports]) / np.linalg.norm(raw["sources"])
        assert np.linalg.norm(response - raw["decoded"]) < 1e-12 and source_error < 1e-12
        error = float(np.linalg.norm(raw["target"] @ response - np.eye(len(ports)), 2))
        assert abs(error - waves[name][-1]["equation_error"]) < 1e-12
        ey = raw["fields"][offsets[1]:offsets[2], 0].reshape(shapes[1]) / h**1.5
        ix, iy = (n[0] - 2) // 2, n[1] // 2
        arrays[f"{name}_z"] = np.arange(1, n[2]) * h - lengths[2] / 2
        arrays[f"{name}_ey"] = ey[ix, iy]
        arrays[f"{name}_response"] = response
        arrays[f"{name}_centers"] = raw["centers"]
        checks[name] = {"source_programming_relative_error": float(source_error),
                        "response_reconstruction_error": float(np.linalg.norm(response - raw["decoded"])),
                        "design": design}

    # Independent controls retain their original verification data.
    wall = read(source(f"{local}/waveguide_buffer/verification.json"))
    wall_changes = []
    for row in wall:
        original = next(r for r in waves["chain3"] if r["h"] == row["h"])
        old, new = np.array(original["decoded_response"]), np.array(row["decoded_response"])
        wall_changes.append({"h": row["h"], "relative_response_change": float(np.linalg.norm(new - old, 2) / np.linalg.norm(old, 2))})
    compiled = []
    for radius, reference in ((3, "r3_h0333_l10"), (4, "r4_h05_l12"), (5, "r5_h05_l14")):
        for row in read(source(f"{local}/compile_{reference}/compiled_targets.json")):
            compiled.append({"radius": radius, **row})
    tradeoff = read(source(f"{local}/waveguide_tradeoff/tradeoff.json"))
    tradeoff_check = read(source(f"{local}/waveguide_tradeoff_check/tradeoff.json"))
    calibration_check = read(source(f"{local}/waveguide_calibration_check/calibration.json"))
    plan = read(source("results/h0143_memory_plan.json"))
    planned_bytes = literal_eval(plan["memory_estimates"])[1]
    data = {"periodic": periodic_data, "waveguide_calibration": calibration,
            "waveguide_cases": waves, "raw_grid_checks": checks,
            "waveguide_wall_changes": wall_changes,
            "waveguide_d3_chain4": read(source(f"{local}/waveguide_chain4_d3/verification.json")),
            "periodic_prescribed_targets": compiled, "material_rounding": tradeoff,
            "channel_refinement_max_error_change": max(abs(a["equation_error"] - b["equation_error"]) for a, b in zip(tradeoff, tradeoff_check)),
            "calibration_mu_refinement_change": abs(calibration["mu"] - calibration_check["mu"]),
            "computational_resources": {"local_calibration_backend": "CPU",
                                        "full_vector_backend": "GPU direct",
                                        "floating_point_precision": "64-bit",
                                        "host_numerical_library_threads": 2,
                                        "concurrent_jobs_per_gpu": 1,
                                        "periodic_plan_unknowns": plan["unknowns"],
                                        "periodic_plan_peak_device_memory_bytes": planned_bytes,
                                        "memory_scope": "Factorization-plan estimate for this backend and matrix; not a measured peak or a lower bound for other solvers."},
            "provenance": {"files_sha256": hashes, "field_convention": "Frequency-domain electric phasors; discrete arrays carry sqrt(cell volume).",
                           "readout": "Original full-grid fields and probes; no display interpolation enters the decoded response.",
                           "periodic_display": "Cell-centered Ez interpolated to y=0.",
                           "waveguide_display": "Saved Ey centerline at x=0; y is immaterial in the invariant transverse channel."}}
    DATA.mkdir(parents=True, exist_ok=True)
    (DATA / "numerical_illustrations.json").write_text(json.dumps(portable_record(data), indent=2) + "\n")
    np.savez_compressed(DATA / "numerical_illustrations.npz", **arrays)


def matrix(ax, values):
    ax.imshow(values, cmap=DIVERGING, vmin=-max(abs(values).ravel()), vmax=max(abs(values).ravel()))
    for (i, j), value in np.ndenumerate(values):
        ax.text(j, i, f"{value:g}".replace("-", "−"), ha="center", va="center", fontsize=7,
                color=st.SURFACE if abs(value) > .55 * abs(values).max() else st.INK)
    ax.set(xticks=[], yticks=[])
    for spine in ax.spines.values():
        spine.set_visible(False)


def answer(ax, target, response):
    observed = response[:, 0]
    expected = np.linalg.solve(target, np.eye(len(target))[:, 0])  # Posthoc comparison only.
    y = np.arange(len(target))
    ax.axvline(0, color=st.AXIS, lw=.6)
    ax.hlines(y, 0, observed, color=[st.BLUE if v >= 0 else st.RED for v in observed], lw=2)
    ax.scatter(observed, y, marker="o", s=24, facecolors=[st.BLUE if v >= 0 else st.RED for v in observed],
               edgecolors=st.SURFACE, linewidths=.5, zorder=3, label="field readout")
    ax.scatter(expected, y, marker="|", s=70, color=st.INK, linewidths=.9, zorder=4, label="target solution")
    for i, value in enumerate(observed):
        ax.text(value, i - .15, f"{value:+.4f}", fontsize=7, va="bottom", ha="center")
    ax.set(yticks=y, yticklabels=[f"$x_{i+1}$" for i in y], ylim=(len(y) - .5, -.65),
           xlim=(-.1, .55), xticks=[0, .2, .4], xlabel="decoded answer")
    ax.spines["left"].set_visible(False)
    ax.tick_params(axis="y", length=0)


def main_figure(data, arrays):
    fig = plt.figure(figsize=(st.WIDTH_MM * st.MM, 108 * st.MM))
    fig.text(.035, .972, "Whole-cavity calibration", weight="bold", va="top")
    fig.text(.035, .486, "Local component assembly", weight="bold", va="top")
    st.panel_label(fig, "a", .005, .98)
    st.panel_label(fig, "b", .745, .98)
    st.panel_label(fig, "c", .005, .493)
    st.panel_label(fig, "d", .745, .493)
    periodic = data["periodic"]
    gamma = np.array(periodic["target"])
    ax = fig.add_axes([.015, .665, .21, .25])
    matrix(ax, gamma)
    ax.text(.5, 1.07, r"target $\Gamma$", transform=ax.transAxes, ha="center")
    ax.text(.5, -.18, r"$b=(1,0,0)$", transform=ax.transAxes, ha="center", fontsize=7)
    ax = fig.add_axes([.258, .55, .443, .36])
    ax.set(xlim=(-5.3, 5.3), ylim=(-5.2, 5.2), aspect="equal")
    ax.axis("off")

    def project(x, y, z):
        return np.array([x + .32 * y, z + .2 * y])

    ez = arrays["periodic_ez"]
    ax.pcolormesh(arrays["periodic_x"], arrays["periodic_z"], ez.T / abs(ez).max(),
                  cmap=DIVERGING, vmin=-1, vmax=1, shading="nearest", rasterized=True)
    vertices = np.array(list(product([-4, 4], [-3, 3], [-4, 4])))
    for p, q in combinations(vertices, 2):
        if np.count_nonzero(p != q) == 1:
            ax.plot(*np.stack([project(*p), project(*q)]).T, color=st.AXIS, lw=.6)
    for i, center in enumerate(periodic["centers"]):
        x, _, z = center
        ax.add_patch(Circle((x, z), 1, fc="none", ec=st.INK2, lw=.65,
                            ls="-" if i < 3 else (0, (2, 2))))
        ax.text(x, z + 1.15, f"T{i+1}" if i < 3 else f"A{i-2}", ha="center", fontsize=6.5,
                bbox={"fc": st.SURFACE, "ec": "none", "pad": .4, "alpha": .88})
    ax.text(.5, -.02, r"$8\times6\times8$ PEC cavity; $E_z$ at $y=0$", ha="center", transform=ax.transAxes, fontsize=7)
    ax = fig.add_axes([.80, .645, .19, .26])
    answer(ax, gamma, np.array(periodic["response"]))
    ax.text(.5, 1.12, "signed readout", transform=ax.transAxes, ha="center")
    ax.text(.5, -.45, f"all-input error: {100 * periodic['operator_error']:.4f}%", transform=ax.transAxes, ha="center", fontsize=7)

    gamma = np.array(data["waveguide_cases"]["chain4"][-1]["target"])
    ax = fig.add_axes([.015, .185, .21, .25])
    matrix(ax, gamma)
    ax.text(.5, 1.02, r"target $\Gamma$", transform=ax.transAxes, ha="center")
    ax.text(.5, -.18, r"$b=(1,0,0,0)$", transform=ax.transAxes, ha="center", fontsize=7)
    ax = fig.add_axes([.276, .255, .44, .17])

    def project_wave(z, x, y):
        return np.array([z + 1.5 * x, .55 * x + 2.8 * y])

    vertices = np.array(list(product([-12, 12], [-.5, .5], [-.25, .25])))
    for c in arrays["chain4_centers"]:
        front = [(c - 1, -.5, -.25), (c + 1, -.5, -.25), (c + 1, -.5, .25), (c - 1, -.5, .25)]
        top = [(c - 1, -.5, .25), (c + 1, -.5, .25), (c + 1, .5, .25), (c - 1, .5, .25)]
        for points in (front, top):
            ax.add_patch(Polygon([project_wave(*p) for p in points], facecolor=st.BLUE_100, ec=st.BLUE_250, lw=.5))
    for p, q in combinations(vertices, 2):
        if np.count_nonzero(p != q) == 1:
            ax.plot(*np.stack([project_wave(*p), project_wave(*q)]).T, color=st.AXIS, lw=.6)
    for i, c in enumerate(arrays["chain4_centers"]):
        ax.text(c, 1.12, f"T{i+1}", ha="center", fontsize=7)
    ax.set(xlim=(-13, 13), ylim=(-1.1, 2.3))
    ax.axis("off")
    ax.text(.5, 1.02, r"$v_i=(\mu+t\Gamma_{ii})^{-1}$", transform=ax.transAxes, ha="center")
    ax.text(.5, -.13, "1 × 0.5 × 24; transverse scale enlarged", transform=ax.transAxes, ha="center", va="top", fontsize=6.5)
    ax = fig.add_axes([.305, .104, .385, .10])
    z, ey = arrays["chain4_z"], arrays["chain4_ey"]
    for c in arrays["chain4_centers"]:
        ax.axvspan(c - 1, c + 1, fc=st.BLUE_100, alpha=.45, lw=0)
    ax.plot(z, ey / abs(ey).max(), color=st.BLUE, lw=1)
    ax.set(xlim=(-12, 12), ylim=(-.06, 1.12), xticks=[-12, -6, 0, 6, 12], yticks=[0, 1], xlabel="$z$")
    ax.set_ylabel(r"$E_y$ / peak", labelpad=2, fontsize=7)
    ax = fig.add_axes([.80, .19, .19, .24])
    answer(ax, gamma, arrays["chain4_response"])
    ax.text(.5, 1.12, "signed readout", transform=ax.transAxes, ha="center")
    error = data["waveguide_cases"]["chain4"][-1]["equation_error"]
    ax.text(.5, -.49, f"all-input error: {100 * error:.4f}%", transform=ax.transAxes, ha="center", fontsize=7)
    # A common signed color scale applies only to the periodic field section.
    cb = fig.add_axes([.326, .516, .17, .012])
    gradient = np.linspace(-1, 1, 128)[None, :]
    cb.imshow(gradient, aspect="auto", cmap=DIVERGING, extent=(-1, 1, 0, 1), vmin=-1, vmax=1)
    cb.set(yticks=[], xticks=[-1, 0, 1], xticklabels=["−1", "0", "+1"])
    cb.tick_params(length=0, pad=1, labelsize=6.5)
    for spine in cb.spines.values():
        spine.set_visible(False)
    fig.text(.511, .517, r"$E_z$ / peak", va="center", fontsize=7)
    fig.text(.745, .027, "● field readout   | target solution", fontsize=6.5)
    st.save(fig, HERE / "fig_numerical", {"Title": "Numerical dielectric linear-system illustrations"})
    plt.close(fig)


def supplementary_figure(data, arrays):
    fig = plt.figure(figsize=(st.WIDTH_MM * st.MM, 116 * st.MM))
    axes = [fig.add_axes(bounds) for bounds in ([.085, .61, .385, .325], [.60, .61, .38, .325],
                                               [.085, .105, .385, .325], [.60, .105, .38, .325])]
    for letter, x, y in (("a", .005, .985), ("b", .515, .985), ("c", .005, .48), ("d", .515, .48)):
        st.panel_label(fig, letter, x, y)
    ax = axes[0]
    z, e = arrays["local_z"], abs(arrays["local_field"])
    e = e / e.max()
    ax.axvspan(-1, 1, fc=st.BLUE_100, alpha=.55, lw=0)
    ax.semilogy(z, e, color=st.BLUE, lw=1.2, label="isolated mode")
    tail = np.linspace(1, 4, 100)
    ax.semilogy(tail, np.interp(1, z, e) * np.exp(-data["waveguide_calibration"]["kappa"] * (tail - 1)),
                color=st.ORANGE, ls="--", lw=1, label=r"$\exp(-\kappa z)$ tail")
    ax.set(xlim=(-4, 4), ylim=(1e-5, 2), xticks=[-4, -2, 0, 2, 4], xlabel="distance from well center",
           ylabel="field amplitude / peak")
    ax.text(.03, .97, "99.00% inside the well", va="top", transform=ax.transAxes, fontsize=7)
    ax.legend(loc="lower center", fontsize=7)

    ax = axes[1]
    colors = [st.BLUE, st.ORANGE, st.AQUA, st.VIOLET, st.MAGENTA]
    markers = ["o", "s", "^", "D", "v"]
    short = ["3 sites", "unequal", "4 sites", "mediator", "indefinite"]
    for (name, rows), color, marker, label in zip(data["waveguide_cases"].items(), colors, markers, short):
        ax.semilogy([1 / r["h"] for r in rows], [100 * r["equation_error"] for r in rows],
                    marker=marker, color=color, ms=3.3, lw=.8, mfc="white", mew=.75, label=label)
    ax.axhline(1, color=st.INK2, ls=(0, (3, 2)), lw=.7)
    ax.text(16.2, 1.04, "1%", fontsize=7, va="bottom", color=st.INK2)
    ax.set(xlim=(15.6, 24.4), ylim=(.1, 3.7), xticks=[16, 20, 22, 24],
           xlabel=r"grid resolution $1/h$", ylabel="equation error (%)")
    ax.set_yticks([.1, .3, 1, 3], labels=["0.1", "0.3", "1", "3"])
    ax.yaxis.set_minor_formatter(matplotlib.ticker.NullFormatter())
    ax.legend(loc="upper right", ncol=2, fontsize=6.5, columnspacing=.8, handlelength=1)

    ax = axes[2]
    for j, row in enumerate(data["periodic_prescribed_targets"]):
        if row["verification"]:
            value = 100 * row["verification"][-1]["prescribed_target_equation_error"]
            ax.bar(j, value, width=.6, fc=st.ORANGE, ec=st.ORANGE, lw=.6)
            ax.text(j, value + 4, f"{value:.1f}", ha="center", fontsize=6.5)
        else:
            ax.text(j, 28, "local fit\nfailed", ha="center", fontsize=6.5, color=st.INK2)
    ax.set(xticks=range(6), xticklabels=[f"{r['radius']}, {r['target'][0][0]:g}" for r in data["periodic_prescribed_targets"]],
           xlim=(-.65, 5.65), ylim=(0, 213), yticks=[0, 50, 100, 150, 200],
           xlabel=r"periodic defect radius $R$, target diagonal $a$", ylabel="assembled equation error (%)")
    ax.text(.03, .97, r"target: $\Gamma_{11}=\Gamma_{22}=a$, $\Gamma_{12}=1$", transform=ax.transAxes,
            va="top", fontsize=6.5)

    ax = axes[3]
    for bits, label, color, marker, line in ((None, "nominal", st.BLUE, "o", "-"),
                                           (16, "16 fractional bits", st.AQUA, "s", "--"),
                                           (12, "12 fractional bits", st.ORANGE, "^", "-.")):
        selected = [r for r in data["material_rounding"] if r["name"] == "chain4" and r["fractional_bits"] == bits]
        ax.semilogy([r["separation"] for r in selected], [100 * r["equation_error"] for r in selected],
                    marker=marker, ls=line, color=color, ms=3.3, mfc="white", mew=.75, lw=1, label=label)
    ax.axhline(1, color=st.AXIS, ls=(0, (3, 2)), lw=.7)
    ax.set(xlim=(1.9, 4.1), ylim=(.01, 20), xticks=[2, 2.5, 3, 3.5, 4],
           xlabel="well separation", ylabel="equation error (%)")
    ax.legend(loc="lower left", fontsize=7)
    for ax in axes:
        ax.grid(axis="y", color=st.GRID, lw=.4, zorder=0)
        ax.set_axisbelow(True)
    st.save(fig, HERE / "si/numerical_controls", {"Title": "Confinement, refinement, locality and precision controls"})
    plt.close(fig)


def write_table(data):
    rows = [r"\begin{tabular}{@{}lccccc@{}}", r"\toprule",
            r"Target & $(h_1^{-1},h_2^{-1},h_3^{-1})$ & $h_1$ & $h_2$ & $h_3$ & Fine channel \\", r"\midrule"]
    for name, entries in data["waveguide_cases"].items():
        grid = ",".join(f"{1 / r['h']:g}" for r in entries)
        errors = " & ".join(f"{100 * r['equation_error']:.4f}" for r in entries)
        rows.append(f"{NAMES[name]} & $({grid})$ & {errors} & {100 * entries[-1]['fine_channel_equation_error']:.4f} " + r"\\")
    rows += [r"\bottomrule", r"\end{tabular}"]
    (DATA / "waveguide_errors.tex").write_text("\n".join(rows) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--refresh-data", action="store_true")
    parser.add_argument("--experiment-root", type=Path)
    args = parser.parse_args()
    if args.refresh_data:
        if args.experiment_root is None:
            parser.error("--refresh-data requires --experiment-root")
        extract(args.experiment_root)
    data = read(DATA / "numerical_illustrations.json")
    arrays = np.load(DATA / "numerical_illustrations.npz")
    st.apply()
    main_figure(data, arrays)
    supplementary_figure(data, arrays)
    write_table(data)
    print("Generated the two numerical figures and refinement table from archived data.")


if __name__ == "__main__":
    main()
