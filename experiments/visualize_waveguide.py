#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy>=2,<3", "matplotlib>=3.9,<4"]
# ///
"""Illustrate the frozen local compiler using archived full-vector Maxwell fields.

No PDE solves or fitting occur here. Target inverses are comparison data only.
The interactive section uses the measured TE10 separability, checked below;
all numeric readouts are recomputed on the original three-component grid.
"""
import argparse
from hashlib import sha256
from itertools import combinations, product
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
import numpy as np

ROOT = Path(__file__).resolve().parent
DATA = ROOT / "results/local_compilation"
OUT = ROOT / "report/local_compilation/walkthrough"
NAMES = {"chain3": "3-site chain", "nonuniform3": "Unequal diagonals",
         "chain4": "4-site chain", "mediator2": "2 ports + mediator",
         "indefinite3": "Indefinite chain", "chain4_d3": "Closer 4-site chain"}
INK, BLUE, ORANGE, GREEN = "#233448", "#246da4", "#bf6d35", "#187e70"


def read(path):
    return json.loads(path.read_text())


def rounded(values):
    a = np.asarray(values)
    return np.array([float(f"{q:.7g}") for q in a.ravel()]).reshape(a.shape).tolist()


def well(z):
    out = np.zeros_like(z, dtype=float)
    inside = np.abs(z) < 1
    out[inside] = np.exp(-1 / (1 - z[inside]**2))
    return out


def collect():
    caldir = DATA / "waveguide_calibration"
    cal = read(caldir / "calibration.json")
    local = np.load(caldir / "template.npz")
    keep = (abs(local["z"]) <= 6)
    ii = np.flatnonzero(keep)[::4]
    calibration = {k: cal[k] for k in ("mu", "coupling", "kappa", "resonant_strength", "inside_fraction")}
    calibration.update(z=rounded(local["z"][ii]), field=rounded(local["field"][ii] / np.sqrt(float(local["spacing"]))),
                       source=rounded(local["source"][ii] / np.sqrt(float(local["spacing"]))),
                       peak_epsilon=cal["material_enclosure_at_resonance"][1])
    cases, evidence = {}, {}
    for name, label in NAMES.items():
        folder = DATA / f"waveguide_{name}"
        design = read(folder / "frozen_design.json")
        verification = read(folder / "verification.json")
        a = np.load(folder / "fields.npz")
        h, lengths = float(a["h"]), a["lengths"]
        n = np.rint(lengths / h).astype(int)
        shapes = [tuple(n - (np.arange(3) != j)) for j in range(3)]
        offsets = np.r_[0, np.cumsum([np.prod(s) for s in shapes])]
        v, ports = np.array(design["strengths"]), np.array(design["ports"])
        alpha, target = design["alpha"], a["target"]
        fields, sources, probes = a["fields"], a["sources"], a["probes"]
        response = alpha * np.diag(v[ports]) + v[ports, None] * (probes.T @ fields)
        response_error = np.linalg.norm(response - a["decoded"])
        source_error = np.linalg.norm(sources - alpha * probes * v[ports]) / np.linalg.norm(sources)
        operator_error = np.linalg.norm(target @ response - np.eye(len(ports)), 2)
        assert response_error < 1e-12 and source_error < 1e-12
        assert abs(operator_error - verification[-1]["equation_error"]) < 1e-12
        shape = (*shapes[1], len(ports))
        ey = fields[offsets[1]:offsets[2]].reshape(shape) / h**1.5
        fy = sources[offsets[1]:offsets[2]].reshape(shape) / h**1.5
        by = probes[offsets[1]:offsets[2]].reshape(shape) / h**1.5
        ix, iy = (n[0] - 2) // 2, n[1] // 2
        z = np.arange(1, n[2]) * h - lengths[2] / 2
        x = np.arange(1, n[0]) * h - lengths[0] / 2
        eyline, fyline = ey[ix, iy], fy[ix, iy]
        sine = np.sin(np.pi * (x + .5))
        reconstructed = sine[:, None, None, None] * eyline[None, None, :, :]
        separability_error = np.linalg.norm(ey - reconstructed) / np.linalg.norm(ey)
        source_separability_error = np.linalg.norm(fy - sine[:, None, None, None] * fyline[None, None, :, :]) / np.linalg.norm(fy)
        assert separability_error < 1e-9 and source_separability_error < 1e-12
        # Signed central-section density; numeric integration never uses this display data.
        density = (by[ix, iy] @ v[ports])[:, None] * eyline
        eps = a["material"][offsets[1]:offsets[2]].reshape(shapes[1])[ix, iy]
        mu = cal["mu"]
        diagonal = (1 / v - mu) / alpha
        cases[name] = dict(label=label, h=h, lengths=lengths.tolist(), centers=a["centers"].tolist(),
                           strengths=v.tolist(), ports=ports.tolist(), alpha=alpha, diagonal=diagonal.tolist(),
                           target=target.tolist(), response=response.tolist(), reference=np.linalg.inv(target).tolist(),
                           operator_error=operator_error, finest_unknowns=len(fields),
                           refinements=[dict(h=r["h"], error=r["equation_error"]) for r in verification],
                           z=rounded(z), field=rounded(eyline.T), source=rounded(fyline.T),
                           density=rounded(density.T), epsilon=rounded(eps))
        evidence[name] = dict(raw_fields_sha256=sha256((folder / "fields.npz").read_bytes()).hexdigest(),
                              frozen_design_sha256=sha256((folder / "frozen_design.json").read_bytes()).hexdigest(),
                              response_reconstruction_error=float(response_error),
                              source_programming_relative_error=float(source_error),
                              TE10_field_reconstruction_relative_error=float(separability_error),
                              TE10_source_reconstruction_relative_error=float(source_separability_error),
                              operator_error=float(operator_error),
                              reference_use="Posthoc comparison only; never used in source, device or decoder")
    return dict(calibration=calibration, cases=cases), evidence, local


def save(fig, name):
    for ext in ("png", "pdf"):
        fig.savefig(OUT / f"{name}.{ext}", dpi=190, bbox_inches="tight", facecolor="white")
    plt.close(fig)


def figures(data, local):
    plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 11, "axes.titlesize": 12,
                         "axes.labelsize": 11, "text.color": INK, "axes.labelcolor": INK,
                         "axes.spines.top": False, "axes.spines.right": False,
                         "axes.titleweight": "medium"})
    case = data["cases"]["chain4"]
    cal = data["calibration"]
    fig = plt.figure(figsize=(12.8, 7.5), layout="constrained")
    gs = fig.add_gridspec(2, 2, height_ratios=(.65, 1))
    ax = fig.add_subplot(gs[0, :])
    L = case["lengths"][2]
    def project(z, x, y):
        return np.array([z+1.6*x, 2.5*y+.8*x+.025*z])
    def face(points, alpha):
        ax.add_patch(Polygon([project(*p) for p in points], facecolor=BLUE, edgecolor="none", alpha=alpha))
    vertices = np.array(list(product([-L/2, L/2], [-.5, .5], [-.25, .25])))
    z = np.linspace(-L/2, L/2, 600)
    x = np.linspace(-.5, .5, 25)
    zz, xx = np.meshgrid(z, x)
    field = np.interp(z, case["z"], case["field"][0])[None, :] * np.sin(np.pi*(xx+.5))
    scaled = field / abs(field).max()
    ax.pcolormesh(zz+1.6*xx, .8*xx+.025*zz, scaled, cmap="RdBu_r", vmin=-1, vmax=1,
                  shading="nearest", rasterized=True)
    for i, c in enumerate(case["centers"]):
        for s in np.arange(-1, 1, .04):
            lo, hi = c+s, c+s+.04
            opacity = .5 * float(well(np.array([s+.02]))[0]) / np.exp(-1)
            face([(lo,-.5,-.25),(hi,-.5,-.25),(hi,-.5,.25),(lo,-.5,.25)], opacity)
            face([(lo,-.5,.25),(hi,-.5,.25),(hi,.5,.25),(lo,.5,.25)], opacity*.6)
        ax.text(*project(c, 0, .6), f"T{i+1}", ha="center", color=INK, fontsize=11)
        e = np.interp(c, case["z"], case["field"][0]) / abs(field).max()
        ax.annotate("", xy=project(c,0,.22*e), xytext=project(c,0,-.16*e),
                    arrowprops=dict(arrowstyle="-|>", color=ORANGE, lw=1.5))
    for p, q in combinations(vertices, 2):
        if np.count_nonzero(p != q) == 1:
            ax.plot(*np.stack([project(*p),project(*q)]).T, color="#8b99a8", lw=.8, alpha=.8)
    ax.set(xlim=(-L/2-1.5, L/2+1.5), ylim=(-2.6, 2.2)); ax.axis("off")
    ax.annotate("", xy=(11,-1.7), xytext=(-11,-1.7), arrowprops=dict(arrowstyle="<->", color=INK, lw=.8))
    ax.text(0,-1.96,"Longitudinal length 24 · cross-section 1 × 0.5 · z →",ha="center",fontsize=10)
    ax.set_title("a  Four copied resonators in a closed PEC waveguide; drive T1 only", loc="left", pad=4)
    ax.text(.02, .01, "Scalar dielectric slabs fill the cross-section; smooth edges along z.  Transverse scale enlarged.\n"
              "Colored middle section: computed signed Ey.  Vertical arrows: electric polarization, not propagation.",
              transform=ax.transAxes, fontsize=10)

    ax = fig.add_subplot(gs[1, 0])
    z = local["z"]
    e = abs(local["field"]) / abs(local["field"]).max()
    ax.axvspan(-1, 1, color=BLUE, alpha=.10, label="Dielectric well")
    ax.semilogy(z, e, color=BLUE, lw=2, label="Isolated component field")
    outside = np.linspace(1, 4, 100)
    prediction = np.interp(1, z, e) * np.exp(-cal["kappa"] * (outside - 1))
    ax.semilogy(outside, prediction, "--", color=ORANGE, lw=1.5, label="Cutoff decay: exp(−κz)")
    ax.set(xlim=(-4, 4), ylim=(1e-5, 1.5), xlabel="z from resonator center (dimensionless)",
           ylabel="Field amplitude / peak (log scale)", title="b  A reusable component needs a confined field")
    ax.text(.04, .08, "99.00% of electric-field norm squared\nis inside the well; κ = 2.978.", transform=ax.transAxes, fontsize=10)
    ax.legend(loc="upper right", fontsize=9, frameon=False); ax.grid(alpha=.15)

    ax = fig.add_subplot(gs[1, 1])
    z = np.array(case["z"])
    for c in case["centers"]:
        ax.axvspan(c-1, c+1, color=BLUE, alpha=.08)
    field = np.array(case["field"])[0]
    ax.plot(z, field / max(abs(field)), color=BLUE, lw=2)
    for i, c in enumerate(case["centers"]):
        value = np.interp(c, z, field) / max(abs(field))
        ax.annotate(f"T{i+1}", xy=(c, value), xytext=(c, value+.11), ha="center", fontsize=11)
    ax.set(xlim=(-10, 10), ylim=(-.06, 1.25), xlabel="z along assembled device (dimensionless)",
           ylabel="Centerline Ey / peak", title="c  Weak tails couple the repeated resonators")
    ax.text(.97, .88, "Only T1 is driven.\nT2–T4 respond through coupling.", transform=ax.transAxes,
            ha="right", va="top", fontsize=10)
    ax.grid(alpha=.15)
    save(fig, "waveguide_mechanism")

    fig, axes = plt.subplots(1, 2, figsize=(12.8, 5.0), layout="constrained")
    mediator = data["cases"]["mediator2"]
    ax = axes[0]
    z, e = np.array(mediator["z"]), np.array(mediator["field"])[0]
    for c in mediator["centers"]:
        ax.axvspan(c-1, c+1, color=BLUE, alpha=.08)
    ax.plot(z, e / max(abs(e)), color=BLUE, lw=2)
    ax.axhline(0, color="#85909d", lw=.8)
    for c, label in zip(mediator["centers"], ("T1 · driven", "A · no source", "T2 · readout")):
        ax.text(c, 1.1, label, ha="center", fontsize=10)
    ax.text(.98, .80, "Reduced three-site diagonal: (2, −1, 2)\nNearest-neighbor entries: −1\n\nEliminate A → terminal Γ = [[3, 1], [1, 3]]",
            transform=ax.transAxes, ha="right", va="top", fontsize=10)
    observed = np.array(mediator["response"])[:, 0]
    ax.text(.03, .03, f"Measured x = ({observed[0]:+.5f}, {observed[1]:+.5f})\n"
            "Target x = (+0.37500, −0.12500)", transform=ax.transAxes, fontsize=10)
    ax.set(xlim=(-8, 8), ylim=(-1.05, 1.30), xlabel="z (dimensionless)", ylabel="Signed centerline Ey / peak",
           title="a  A positive terminal coupling via a mediator")
    ax.grid(alpha=.15)
    ax = axes[1]
    tradeoff = read(DATA / "waveguide_tradeoff/tradeoff.json")
    for bits, label, color, marker in ((None, "Unrounded strengths", GREEN, "o"),
                                      (16, "16 fractional bits", BLUE, "s"),
                                      (12, "12 fractional bits", ORANGE, "^")):
        rows = [r for r in tradeoff if r["name"] == "chain4" and r["fractional_bits"] == bits]
        ax.semilogy([r["separation"] for r in rows], [100*r["equation_error"] for r in rows],
                    marker+"-", color=color, label=label, lw=1.8, ms=5)
    ax.axhline(1, color="#72808d", ls="--", lw=1)
    ax.text(2.02, 1.12, "1%", fontsize=10)
    ax.set(xlabel="Center-to-center separation d (dimensionless)", ylabel="All-input equation error (%)",
           title="b  Isolation improves; material tolerance tightens", ylim=(.01, 20))
    ax.legend(loc="upper center", fontsize=9, frameon=False)
    ax.text(.03, .03, "Fine TE10 channel; only material strengths rounded.\nSources / readout fixed. These are not worst-case bounds.",
            transform=ax.transAxes, fontsize=9)
    ax.grid(alpha=.15)
    save(fig, "waveguide_sign_and_precision")


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--inline-output", type=Path, required=True)
    args = p.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    data, evidence, local = collect()
    figures(data, local)
    payload = json.dumps(data, separators=(",", ":"))
    (OUT / "waveguide_data.json").write_text(payload)
    template = (ROOT / "waveguide_walkthrough.html").read_text()
    assert template.count("__WAVEGUIDE_DATA__") == 1
    fragment = template.replace("__WAVEGUIDE_DATA__", payload)
    assert len(fragment.encode()) < 1_000_000
    args.inline_output.parent.mkdir(parents=True, exist_ok=True)
    args.inline_output.write_text(fragment)
    (OUT / "visualization_evidence.json").write_text(json.dumps(evidence, indent=2)+"\n")
    print(json.dumps({"inline_bytes": len(fragment.encode()), "cases": list(data["cases"]),
                      "maximum_field_reconstruction_error": max(e["TE10_field_reconstruction_relative_error"] for e in evidence.values()),
                      "output": str(OUT)}, indent=2))


if __name__ == "__main__":
    main()
