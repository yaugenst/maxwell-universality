#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=2,<3", "matplotlib>=3.9,<4"]
# ///
"""Regenerate local-compilation figures and tables from archived receipts."""
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


ROOT = Path(__file__).parent
DATA = ROOT / "results/local_compilation"
OUT = ROOT / "report/local_compilation"
NAMES = {"chain3": "3-site chain", "nonuniform3": "Unequal diagonals",
         "chain4": "4-site chain", "mediator2": "2 ports + mediator",
         "indefinite3": "Indefinite chain"}


def read(path):
    return json.loads(path.read_text())


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    screens = [read(DATA / f"r{r}_h05_l{2*r+4}/screen.json") for r in range(1, 6)]
    screen_fine = read(DATA / "r3_h0333_l10/screen.json")
    compiled = []
    for radius, reference in ((3, "r3_h0333_l10"), (4, "r4_h05_l12"), (5, "r5_h05_l14")):
        for row in read(DATA / f"compile_{reference}/compiled_targets.json"):
            compiled.append({"radius": radius, **row})
    waves = {name: read(DATA / f"waveguide_{name}/verification.json") for name in NAMES}
    calibration = read(DATA / "waveguide_calibration/calibration.json")
    calibration_check = read(DATA / "waveguide_calibration_check/calibration.json")
    buffer = read(DATA / "waveguide_buffer/verification.json")
    compact = read(DATA / "waveguide_chain4_d3/verification.json")
    tradeoff = read(DATA / "waveguide_tradeoff/tradeoff.json")
    tradeoff_check = read(DATA / "waveguide_tradeoff_check/tradeoff.json")
    wall_changes = []
    for row in buffer:
        original = next(r for r in waves["chain3"] if r["h"] == row["h"])
        old, new = np.array(original["decoded_response"]), np.array(row["decoded_response"])
        wall_changes.append({"h": row["h"], "relative_response_change": float(np.linalg.norm(new-old, 2)/np.linalg.norm(old, 2))})
    summary = {"periodic_screen": screens, "periodic_refined_screen": screen_fine,
               "periodic_prescribed_targets": compiled,
               "waveguide_calibration": calibration, "waveguide_cases": waves,
               "waveguide_wall_changes": wall_changes, "waveguide_d3_chain4": compact,
               "waveguide_material_rounding": tradeoff,
               "channel_refinement_max_absolute_equation_error_change": max(
                   abs(a["equation_error"]-b["equation_error"]) for a, b in zip(tradeoff, tradeoff_check)),
               "isolated_calibration_refinement_mu_change_over_coupling":
                   abs(calibration["mu"]-calibration_check["mu"])/calibration["coupling"],
               "waveguide_pass_both_finer_grids": [name for name, rows in waves.items()
                                                  if max(r["equation_error"] for r in rows[-2:]) < .01]}
    (OUT / "summary.json").write_text(json.dumps(summary, indent=2)+"\n")

    plt.rcParams.update({"font.size": 10, "axes.titlesize": 11,
                         "axes.spines.top": False, "axes.spines.right": False,
                         "savefig.facecolor": "white", "figure.facecolor": "white"})
    fig, axes = plt.subplots(2, 2, figsize=(12.8, 8.6), layout="constrained")
    ax = axes[0, 0]
    ax.plot(range(1, 6), [100*s["modes"][0]["inside_fraction"] for s in screens], "o-", color="#586b94", label="Periodic medium; coarse screen")
    ax.plot(3, 100*screen_fine["modes"][0]["inside_fraction"], "s", mfc="white", color="#263c64", label="Radius 3, finer screen")
    ax.axhline(100*calibration["inside_fraction"], color="#137c66", ls="--", label="Waveguide control, radius 1")
    ax.set(xlabel="Defect radius in periodic-medium sweep", ylabel="Field norm squared inside defect (%)",
           ylim=(0, 106), xticks=range(1, 6), title="a  Confinement improves; locality needs a separate test")
    ax.legend(fontsize=8, loc="center left")
    ax.text(.03, .84, "Box size and detuning also vary in this sweep.", transform=ax.transAxes, fontsize=8, color="#555555")

    ax = axes[0, 1]
    for j, row in enumerate(compiled):
        if row["verification"]:
            value = 100*row["verification"][-1]["prescribed_target_equation_error"]
            ax.bar(j, value, color="#bb6553", width=.65)
            ax.text(j, value*1.07, f"{value:.1f}%", ha="center", fontsize=8)
        else:
            ax.text(j, 25, "Local fit\nfailed", ha="center", fontsize=8, color="#8a493d")
    ax.axhline(1, color="#444444", ls="--", lw=1)
    ax.set(xticks=range(len(compiled)), xticklabels=[f"R={r['radius']}\na={r['target'][0][0]:g}" for r in compiled],
           ylabel="Prescribed target equation error (%)", ylim=(0, 215), xlim=(-.6, 5.6),
           title="b  Periodic devices fail after pair-only calibration")
    ax.text(.03, .91, "Γ = [[a, 1], [1, a]]; finest tested mesh", transform=ax.transAxes, fontsize=8)

    ax = axes[1, 0]
    colors = ["#137c66", "#2479aa", "#7a60a8", "#bb7930", "#a84f78"]
    for (name, rows), color in zip(waves.items(), colors):
        ax.semilogy([1/r["h"] for r in rows], [100*r["equation_error"] for r in rows],
                    "o-", color=color, label=NAMES[name], ms=4)
    ax.axhline(1, color="#444444", ls="--", lw=1, label="1% acceptance criterion")
    ax.set(xlabel="Grid resolution 1/h (larger is finer)", ylabel="Prescribed target equation error (%)",
           title="c  One component library, five frozen waveguide designs")
    ax.legend(fontsize=8, ncol=2)

    ax = axes[1, 1]
    for bits, label, color, marker in ((None, "Unrounded material", "#137c66", "o"),
                                      (16, "16 fractional bits", "#2479aa", "s"),
                                      (12, "12 fractional bits", "#bb7930", "^")):
        selected = [r for r in tradeoff if r["name"] == "chain4" and r["fractional_bits"] == bits]
        ax.semilogy([r["separation"] for r in selected], [100*r["equation_error"] for r in selected],
                    marker+"-", color=color, label=label, ms=4)
    ax.axhline(1, color="#444444", ls="--", lw=1)
    ax.set(xlabel="Waveguide resonator spacing", ylabel="Prescribed target equation error (%)",
           title="d  Less crosstalk trades against material precision")
    ax.legend(fontsize=8)
    ax.text(.03, .02, "Fine 1D channel; sources and decoder frozen.\nRounding results are not worst-case tolerance bounds.",
            transform=ax.transAxes, fontsize=8, color="#555555")
    for a in axes.flat:
        a.grid(axis="y", alpha=.15)
    fig.savefig(OUT / "local_compilation_results.png", dpi=180)
    fig.savefig(OUT / "local_compilation_results.pdf")
    plt.close(fig)

    arrays = np.load(DATA / "waveguide_chain4/fields.npz")
    last = waves["chain4"][-1]
    h, lengths = last["h"], np.array(last["lengths"])
    n = np.rint(lengths/h).astype(int)
    shapes = [tuple(n-(np.arange(3) != j)) for j in range(3)]
    offsets = np.r_[0, np.cumsum([np.prod(s) for s in shapes])]
    ey = arrays["fields"][offsets[1]:offsets[2], 0].reshape(shapes[1])/h**1.5
    eps = arrays["material"][offsets[1]:offsets[2]].reshape(shapes[1])
    z = np.arange(1, n[2])*h-lengths[2]/2
    ix, iy = (n[0]-2)//2, n[1]//2
    profile = ey[ix, iy]
    target = arrays["target"]
    observed = arrays["decoded"][:, 0]
    expected = np.linalg.solve(target, np.eye(len(target))[:, 0])
    fig = plt.figure(figsize=(12.8, 7.4), layout="constrained")
    gs = fig.add_gridspec(2, 2, width_ratios=(3., 1.2), height_ratios=(1., 1.3))
    material_ax = fig.add_subplot(gs[0, :])
    im = material_ax.imshow(np.repeat(eps[ix, iy][None, :], 15, axis=0), aspect="auto", origin="lower",
                            extent=(-lengths[2]/2, lengths[2]/2, -.25, .25), cmap="YlGnBu", vmin=1, vmax=14)
    for i, center in enumerate(arrays["centers"]):
        material_ax.text(center, 0, f"Site {i+1}", color="white", fontsize=10, ha="center", va="center",
                         bbox=dict(boxstyle="round,pad=.2", facecolor="#173f5f", alpha=.85, edgecolor="none"))
    material_ax.set(xlabel="z (dimensionless)", yticks=[],
                    title="One frozen component, repeated four times inside a 1 × 0.5 × 24 PEC waveguide\nTransverse scale expanded for visibility; dielectric fills the cross-section")
    for spine in material_ax.spines.values():
        spine.set_visible(True)
        spine.set_linewidth(2)
    fig.colorbar(im, ax=material_ax, label="Scalar permittivity ε", shrink=.7, pad=.02)
    field_ax = fig.add_subplot(gs[1, 0])
    field_ax.plot(z, profile, color="#137c66", lw=1.7)
    for center in arrays["centers"]:
        field_ax.axvspan(center-1, center+1, color="#137c66", alpha=.08)
    field_ax.set(xlabel="z (dimensionless)", ylabel="Signed electric field Ey",
                 title="Full Maxwell field when only site 1 is driven")
    field_ax.grid(alpha=.15)
    field_ax.text(.98, .94, "Evanescent intervals suppress distant interactions.\nOther sites respond through their coupling.",
                  transform=field_ax.transAxes, va="top", ha="right", fontsize=9)
    answer_ax = fig.add_subplot(gs[1, 1])
    x = np.arange(4)
    answer_ax.bar(x-.17, expected, width=.32, color="#c8d1da", label="Target solution")
    answer_ax.bar(x+.17, observed, width=.32, color="#137c66", label="Local field readout")
    answer_ax.set(xticks=x, xticklabels=["x1", "x2", "x3", "x4"], ylabel="Decoded component",
                  title=f"Input b = (1, 0, 0, 0)\nAll-input equation error: {100*last['equation_error']:.3f}%")
    answer_ax.legend(fontsize=8)
    fig.savefig(OUT / "waveguide_device.png", dpi=180)
    fig.savefig(OUT / "waveguide_device.pdf")
    plt.close(fig)

    table = ["| Design | Target condition | Error at finer grid 1 | Error at finer grid 2 | Fine channel reference |",
             "|---|---:|---:|---:|---:|"]
    for name, rows in waves.items():
        a, b = rows[-2:]
        condition = np.linalg.cond(rows[-1]["target"])
        table.append(f"| {NAMES[name]} | {condition:.3f} | {100*a['equation_error']:.4f}% | {100*b['equation_error']:.4f}% | {100*b['fine_channel_equation_error']:.4f}% |")
    (OUT / "verification_table.md").write_text("\n".join(table)+"\n")
    print(json.dumps({"passes": summary["waveguide_pass_both_finer_grids"],
                      "wall_changes": wall_changes, "output": str(OUT)}))


if __name__ == "__main__":
    main()
