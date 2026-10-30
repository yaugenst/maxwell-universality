#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["matplotlib>=3.9,<4", "numpy>=2,<3"]
# ///
"""Numerical illustrations from archived Maxwell solutions.

Run ``uv run --script figures/fig_numerical.py`` from the paper directory.
The bundled figure data are sufficient. To re-extract them from the large
simulation archive, add ``--refresh-data --experiment-root PATH``; PATH is
the repository's ``experiments/`` directory (``../experiments`` from the paper
directory). No Maxwell solve or fitting is performed here.
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
from matplotlib.lines import Line2D
from matplotlib.patches import Circle, Polygon, Rectangle
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


PITCH, CELL = 7.0, 6.5  # mm per matrix row; readout rows use the same pitch


def signed(value, fmt):
    return format(value, fmt).replace("-", "−")


class Sheet:
    """Millimetre layout: x from the left edge, u downward from the top edge."""

    def __init__(self, height):
        self.w, self.h = st.WIDTH_MM, height
        self.fig = plt.figure(figsize=(self.w * st.MM, height * st.MM))
        self.canvas = self.fig.add_axes([0, 0, 1, 1], xlim=(0, self.w), ylim=(height, 0), zorder=10)
        self.canvas.axis("off")

    def axes(self, x, u, w, h):
        return self.fig.add_axes([x / self.w, 1 - (u + h) / self.h, w / self.w, h / self.h])

    def text(self, x, u, s, **kw):
        self.canvas.text(x, u, s, **kw)

    def panel(self, letter, x, u, title=None):
        self.text(x + .3, u, letter, fontsize=9, weight="bold", va="top")
        if title:
            self.text(x + 4, u, title, weight="bold", va="top")


def system(sheet, x, u, gamma, b):
    """Gamma, x = and b as signed cells on the PITCH grid, as in Fig. 1a."""
    n = len(gamma)

    def cell(cx, i, value, scale):
        if value == 0:
            face, ink = st.GRAY_WASH, st.MUTED
        else:
            face = DIVERGING(.5 + .5 * value / scale)
            ink = st.SURFACE if abs(value) > .55 * scale else st.INK
        top = u + i * PITCH + (PITCH - CELL) / 2
        sheet.canvas.add_patch(Rectangle((cx, top), CELL, CELL, fc=face, ec="none"))
        sheet.text(cx + CELL / 2, top + CELL / 2, signed(value, "g"), fontsize=7, color=ink,
                   ha="center", va="center")

    for (i, j), value in np.ndenumerate(gamma):
        cell(x + j * PITCH, i, value, abs(gamma).max())
    xb = x + n * PITCH + 7.5
    for i, value in enumerate(b):
        cell(xb, i, value, 1)
    middle, bottom = u + n * PITCH / 2, u + n * PITCH + 1.2
    sheet.text(xb - 3.9, middle, r"$x\,=$", ha="center", va="center")
    sheet.text(x + (n * PITCH - .5) / 2, bottom, r"$\Gamma$", ha="center", va="top")
    sheet.text(xb + CELL / 2, bottom, r"$b$", ha="center", va="top")
    sheet.text((x + xb + CELL) / 2, u - 2, "target system", ha="center", va="bottom")


def readout(sheet, x, u, w, target, response, error):
    """Decoded answer for b = e_1 (circles) against the target solution (ticks)."""
    observed = response[:, 0]
    expected = np.linalg.solve(target, np.eye(len(target))[:, 0])  # Posthoc comparison only.
    n = len(target)
    ax = sheet.axes(x, u, w, n * PITCH)
    y = np.arange(n)
    colors = [st.BLUE if v >= 0 else st.RED for v in observed]
    ax.axvline(0, color=st.AXIS, lw=.6, zorder=1)
    ax.hlines(y, 0, observed, color=colors, lw=2, zorder=2)
    ax.scatter(observed, y, s=24, c=colors, edgecolors=st.SURFACE, linewidths=.5, zorder=3)
    ax.scatter(expected, y, marker="|", s=70, color=st.INK, linewidths=.9, zorder=4)
    ax.set(xlim=(-.1, .45), xticks=[0, .2, .4], xticklabels=["0", "0.2", "0.4"], ylim=(n - .5, -.5),
           yticks=y, yticklabels=[f"$x_{i + 1}$" for i in y])
    ax.set_xlabel("$x_i$", labelpad=2)
    ax.spines["left"].set_visible(False)
    ax.tick_params(axis="y", length=0, pad=3)
    for i, value in enumerate(observed):
        sheet.text(st.WIDTH_MM - .5, u + (i + .5) * PITCH, signed(value, "+.4f"), fontsize=7,
                   ha="right", va="center")
    sheet.text(x + w / 2, u - 2, "signed readout", ha="center", va="bottom")
    sheet.text(x + w / 2, u + n * PITCH + 9.3, f"all-input error {100 * error:.4f}%", fontsize=7,
               ha="center", va="top")


def cavity(sheet, x, u, scale, periodic, arrays):
    """Oblique view of the 8 x 6 x 8 cavity with the y = 0 field section in place."""
    lo, hi = np.array([-4.96, -4.6]), np.array([4.96, 4.6])
    w, h = scale * (hi - lo)
    ax = sheet.axes(x, u, w, h)
    ax.set(xlim=(lo[0], hi[0]), ylim=(lo[1], hi[1]))
    ax.axis("off")

    def project(p):
        return np.array([p[0] + .32 * p[1], p[2] + .2 * p[1]])

    ez = arrays["periodic_ez"]
    ax.pcolormesh(arrays["periodic_x"], arrays["periodic_z"], ez.T / abs(ez).max(),
                  cmap=DIVERGING, vmin=-1, vmax=1, shading="nearest", rasterized=True, zorder=2)
    vertices = np.array(list(product([-4, 4], [-3, 3], [-4, 4])), float)
    for p, q in combinations(vertices, 2):
        if np.count_nonzero(p != q) != 1:
            continue
        if p[1] != q[1]:  # depth edge: the half with y < 0 lies in front of the section
            mid = (p + q) / 2
            pieces = [(p, mid, 3 if p[1] < 0 else 1), (mid, q, 3 if q[1] < 0 else 1)]
        else:
            pieces = [(p, q, 3 if p[1] < 0 else 1)]
        for a, c, z in pieces:
            ax.plot(*np.stack([project(a), project(c)]).T, color=st.AXIS, lw=.6, zorder=z)
    for i, (cx, _, cz) in enumerate(periodic["centers"]):
        ax.add_patch(Circle((cx, cz), 1, fc="none", ec=st.INK2, lw=.65, zorder=4,
                            ls="-" if i < 3 else (0, (2, 1.6))))
        ax.text(cx, cz, f"T{i + 1}" if i < 3 else f"A{i - 2}", fontsize=6.5, ha="center", va="center",
                zorder=5, bbox={"boxstyle": "round,pad=0.15", "fc": st.SURFACE, "ec": "none", "alpha": .85})
    return w, h


def colorbar(sheet, x, u, w, h, label):
    ax = sheet.axes(x, u, w, h)
    ax.imshow(np.linspace(1, -1, 128)[:, None], aspect="auto", cmap=DIVERGING, extent=(0, 1, -1, 1),
              vmin=-1, vmax=1)
    ax.set(xticks=[], yticks=[-1, 0, 1], yticklabels=["−1", "0", "+1"])
    ax.yaxis.tick_right()
    ax.tick_params(length=0, pad=1.5)
    for spine in ax.spines.values():
        spine.set_visible(False)
    sheet.text(x + w / 2, u - 1.5, label, fontsize=7, ha="center", va="bottom")


def waveguide(sheet, x, u, w, centers):
    """Oblique waveguide with the front face on the same z scale as the field profile below."""
    scale = w / 24
    depth, rise, height = 1.5, .55, 5.2 / scale  # drawing units; transverse dimensions enlarged

    def project(z, a, b):  # a: depth fraction 0 (front) to 1, b: height fraction
        return np.array([z + depth * a, height * b + rise * a])

    top = height + rise
    ax = sheet.axes(x, u, w, (top + .2) * scale)
    ax.set(xlim=(-12, 12), ylim=(-.1, top + .1))
    ax.axis("off")
    box = np.array(list(product([-12, 12], [0, 1], [0, 1])), float)
    for p, q in combinations(box, 2):
        if np.count_nonzero(p != q) != 1:
            continue
        hidden = (p[1] == q[1] == 1 and p[2] == q[2] == 0) or \
                 (p[0] == q[0] == -12 and (p[1] == q[1] == 1 or p[2] == q[2] == 0))
        ax.plot(*np.stack([project(*p), project(*q)]).T, color=st.AXIS, lw=.6,
                zorder=1 if hidden else 3, clip_on=False)
    style = {"facecolor": st.BLUE_100, "ec": st.BLUE_250, "lw": .5, "zorder": 2, "clip_on": False}
    for c in centers:
        for face in ([(c - 1, 0, 0), (c + 1, 0, 0), (c + 1, 0, 1), (c - 1, 0, 1)],
                     [(c - 1, 0, 1), (c + 1, 0, 1), (c + 1, 1, 1), (c - 1, 1, 1)],
                     [(c + 1, 0, 0), (c + 1, 1, 0), (c + 1, 1, 1), (c + 1, 0, 1)]):
            ax.add_patch(Polygon([project(*p) for p in face], **style))
    return (top + .2) * scale


def main_figure(data, arrays):
    sheet = Sheet(104)
    c1, c3, w3 = 3.0, 124.0, 23.0  # matrix and readout column origins, readout width (mm)

    # Whole-cavity calibration: one header line, content top-aligned below it
    periodic = data["periodic"]
    gamma = np.array(periodic["target"])
    row = 12.0
    sheet.panel("a", 0, 1, "Whole-cavity calibration")
    sheet.panel("b", c3 - 7, 1)
    system(sheet, c1, row, gamma, [1, 0, 0])
    xc = 61.0
    w, h = cavity(sheet, xc, row, 3.8, periodic, arrays)
    sheet.text(xc + w / 2, row - 2, "8 × 6 × 8 PEC cavity, $E_z$ at $y$ = 0", ha="center", va="bottom")
    colorbar(sheet, xc + w + 4, row + h / 2 - 7, 1.6, 16, "$E_z$ / peak")
    readout(sheet, c3, row, w3, gamma, np.array(periodic["response"]), periodic["operator_error"])
    handles = [Line2D([], [], ls="", marker="o", ms=5, mfc=st.BLUE, mec=st.SURFACE, mew=.5,
                      label="decoded answer"),
               Line2D([], [], ls="", marker="|", ms=8, mec=st.INK, mew=.9, label="target solution")]
    sheet.canvas.legend(handles=handles, loc="upper center", bbox_to_anchor=(c3 + w3 / 2, row + 3 * PITCH + 13),
                        bbox_transform=sheet.canvas.transData, ncol=2, fontsize=7, borderaxespad=0,
                        borderpad=0, handletextpad=.2, columnspacing=1.0)

    # Local component assembly
    case = data["waveguide_cases"]["chain4"][-1]
    gamma = np.array(case["target"])
    top = 52.5
    row = top + 11
    sheet.panel("c", 0, top, "Local component assembly")
    sheet.panel("d", c3 - 7, top)
    system(sheet, c1, row, gamma, [1, 0, 0, 0])
    readout(sheet, c3, row, w3, gamma, arrays["chain4_response"], case["equation_error"])
    xw, ww = 58.0, 52.0
    sheet.text(xw + ww / 2, row - 2, r"1 × 0.5 × 24 PEC waveguide, $v_i=(\mu+t\,\Gamma_{ii})^{-1}$",
               ha="center", va="bottom")
    hw = waveguide(sheet, xw, row + 4, ww, arrays["chain4_centers"])
    for i, c in enumerate(arrays["chain4_centers"]):
        sheet.text(xw + ww * (c + 12) / 24, row + 3.2, f"T{i + 1}", fontsize=7, ha="center", va="bottom")
    ax = sheet.axes(xw, row + 4 + hw + 3, ww, row + 4 * PITCH - (row + 4 + hw + 3))
    z, ey = arrays["chain4_z"], arrays["chain4_ey"]
    for c in arrays["chain4_centers"]:
        ax.axvspan(c - 1, c + 1, fc=st.BLUE_100, alpha=.6, lw=0)
    ax.plot(z, ey / abs(ey).max(), color=st.BLUE, lw=1)
    ax.set(xlim=(-12, 12), ylim=(-.06, 1.12), xticks=[-12, -6, 0, 6, 12], yticks=[0, 1])
    ax.set_xlabel("$z$", labelpad=2)
    ax.set_ylabel("$E_y$ / peak", labelpad=3)
    st.save(sheet.fig, HERE / "fig_numerical", {"Title": "Numerical dielectric linear-system illustrations"})
    plt.close(sheet.fig)


def one_percent(ax, x):
    """The 1% equation-error criterion, drawn identically in every log panel."""
    ax.axhline(1, color=st.MUTED, ls=(0, (3, 2)), lw=.7, zorder=1)
    ax.text(x, 1.07, "1%", fontsize=7, color=st.INK2, va="bottom")


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
    ax.semilogy(z, e, color=st.BLUE, lw=1.2)
    tail = np.linspace(1, 4, 100)
    ax.semilogy(tail, np.interp(1, z, e) * np.exp(-data["waveguide_calibration"]["kappa"] * (tail - 1)),
                color=st.ORANGE, ls="--", lw=1)
    ax.text(-2.95, 10**-3.85, "isolated\nmode", fontsize=7, color=st.BLUE, ha="left", va="center")
    ax.text(2.95, 10**-3.85, "$\\exp(-\\kappa z)$\ntail", fontsize=7, color=st.ORANGE, ha="right", va="center")
    ax.set(xlim=(-4, 4), ylim=(1e-5, 2), xticks=[-4, -2, 0, 2, 4], xlabel="distance from well center",
           ylabel="field amplitude / peak")
    ax.text(.03, .97, "99.00% inside\nthe well", va="top", transform=ax.transAxes, fontsize=7)

    ax = axes[1]
    colors = [st.BLUE, st.ORANGE, st.AQUA, st.VIOLET, st.MAGENTA]
    markers = ["o", "s", "^", "D", "v"]
    short = ["3 sites", "unequal", "4 sites", "mediator", "indefinite"]
    for (name, rows), color, marker, label in zip(data["waveguide_cases"].items(), colors, markers, short):
        ax.semilogy([1 / r["h"] for r in rows], [100 * r["equation_error"] for r in rows],
                    marker=marker, color=color, ms=3.3, lw=.9, mfc="white", mew=.75, label=label)
    one_percent(ax, 15.75)
    ax.set(xlim=(15.6, 24.4), ylim=(.1, 4.2), xticks=[16, 20, 22, 24],
           xlabel=r"grid resolution $1/h$", ylabel="equation error (%)")
    ax.set_yticks([.1, .3, 1, 3], labels=["0.1", "0.3", "1", "3"])
    ax.legend(loc="upper right", ncol=3, columnspacing=1.0, handlelength=1.4, borderaxespad=.2)

    ax = axes[2]
    for j, row in enumerate(data["periodic_prescribed_targets"]):
        if row["verification"]:
            value = 100 * row["verification"][-1]["prescribed_target_equation_error"]
            ax.bar(j, value, width=.6, fc=st.ORANGE, ec=st.ORANGE, lw=.6)
            ax.text(j, value + 4, f"{value:.1f}", ha="center", fontsize=7)
        else:
            ax.text(j, 28, "local fit\nfailed", ha="center", fontsize=7, color=st.INK2)
    ax.set(xticks=range(6), xticklabels=[f"{r['radius']}, {r['target'][0][0]:g}" for r in data["periodic_prescribed_targets"]],
           xlim=(-.65, 5.65), ylim=(0, 213), yticks=[0, 50, 100, 150, 200],
           xlabel=r"periodic defect radius $R$, target diagonal $a$", ylabel="assembled equation error (%)")
    ax.text(.03, .97, r"target: $\Gamma_{11}=\Gamma_{22}=a$, $\Gamma_{12}=1$", transform=ax.transAxes,
            va="top", fontsize=7)

    ax = axes[3]
    for bits, label, color, marker, line in ((None, "nominal", st.BLUE, "o", "-"),
                                           (16, "16 fractional bits", st.AQUA, "s", "--"),
                                           (12, "12 fractional bits", st.ORANGE, "^", "-.")):
        selected = [r for r in data["material_rounding"] if r["name"] == "chain4" and r["fractional_bits"] == bits]
        ax.semilogy([r["separation"] for r in selected], [100 * r["equation_error"] for r in selected],
                    marker=marker, ls=line, color=color, ms=3.3, mfc="white", mew=.75, lw=.9, label=label)
    one_percent(ax, 1.94)
    ax.set(xlim=(1.9, 4.1), ylim=(.01, 20), xticks=[2, 2.5, 3, 3.5, 4],
           xlabel="well separation $d$", ylabel="equation error (%)")
    ax.set_yticks([.01, .1, 1, 10], labels=["0.01", "0.1", "1", "10"])
    ax.legend(loc="lower left")
    for ax in axes:
        ax.yaxis.set_minor_locator(matplotlib.ticker.NullLocator())
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
