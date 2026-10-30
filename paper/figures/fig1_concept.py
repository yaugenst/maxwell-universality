#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["matplotlib>=3.9,<4", "numpy>=2,<3"]
# ///
"""Figure 1: the two-way correspondence between sparse linear algebra and a dielectric cavity.

a: the input system (the actual 2 x 2 example compiled by the logical compiler);
b: the compiled logical network, exactly as routed into its integer grid box by the compiler
   (data: logical_translation_*.{json,json.gz} written by si/logical_translation.py);
c: readout moments and the decoded answer of that example (exact logical decoding).

Run from the paper directory:
    FIGS1_DATA_DIR=build/logical uv run --script figures/si/logical_translation.py
    FIGS1_DATA_DIR=build/logical uv run --script figures/fig1_concept.py
"""
from __future__ import annotations

import gzip
import json
import os
import sys
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.patches import FancyArrowPatch, Rectangle
from mpl_toolkits.mplot3d.art3d import Line3DCollection, Poly3DCollection

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as st

HERE = Path(__file__).resolve().parent
SRC = Path(os.environ["FIGS1_DATA_DIR"])  # written by si/logical_translation.py
Z_COMPRESS = 6          # routing axis compressed for display (stated in the caption)

data = json.loads((SRC / "logical_translation_data.json").read_text())
routes = json.loads(gzip.decompress((SRC / "logical_translation_routes.json.gz").read_bytes()))["routes"]
labels = data["labels"]
counts = data["counts"]
res = data["residual_check"]

KIND_COLOR = {"output_equation": st.BLUE, "gate_equation": st.BLUE,
              "input_variable": st.AQUA, "gate_variable": st.AQUA,
              "sign_mediator": st.ORANGE}


def draw():
    st.apply()
    fig = plt.figure(figsize=(st.WIDTH_MM * st.MM, 96 * st.MM))
    axa = fig.add_axes([0.015, 0.30, 0.195, 0.52])
    axb = fig.add_axes([0.20, 0.20, 0.585, 0.71], projection="3d", computed_zorder=False)
    axc = fig.add_axes([0.79, 0.30, 0.20, 0.52])
    for letter, x, y in (("a", 0.012, 0.985), ("b", 0.235, 0.985), ("c", 0.775, 0.985)):
        st.panel_label(fig, letter, x, y)

    # ------------------------------------------------------------------ a: the system
    axa.set_xlim(0, 1); axa.set_ylim(0, 1); axa.set_axis_off()
    M = [[2, -1], [1, 2]]
    bvec = [1, 0]
    cw, ch = 0.19, 0.19
    x0, y0 = 0.06, 0.40
    for i in range(2):
        for j in range(2):
            v = M[i][j]
            col = st.BLUE if v > 0 else st.RED
            axa.add_patch(Rectangle((x0 + j * (cw + 0.02), y0 + (1 - i) * (ch + 0.02)), cw, ch,
                                    facecolor=col, edgecolor="none"))
            axa.text(x0 + j * (cw + 0.02) + cw / 2, y0 + (1 - i) * (ch + 0.02) + ch / 2,
                     f"{v:d}".replace("-", "−"), color="white", fontsize=8, ha="center", va="center")
    xb = x0 + 2 * (cw + 0.02) + 0.24
    for i in range(2):
        v = bvec[i]
        axa.add_patch(Rectangle((xb, y0 + (1 - i) * (ch + 0.02)), cw, ch,
                                facecolor=st.BLUE if v else st.GRAY_WASH, edgecolor="none"))
        axa.text(xb + cw / 2, y0 + (1 - i) * (ch + 0.02) + ch / 2, f"{v:d}",
                 color="white" if v else st.MUTED, fontsize=8, ha="center", va="center")
    ymid = y0 + ch + 0.01
    axa.text(x0 + 2 * (cw + 0.02) + 0.12, ymid, r"$x\,=$", fontsize=8, ha="center", va="center")
    axa.text(x0 + cw + 0.01, y0 - 0.06, r"$M$", fontsize=8, ha="center", va="top")
    axa.text(xb + cw / 2, y0 - 0.06, r"$b$", fontsize=8, ha="center", va="top")
    axa.text(0.5, 0.99, r"$Mx = b$", fontsize=9, ha="center", va="top")
    axa.text(0.5, 0.20, "signed, nonsymmetric,\n$m = 4$ nonzeros", fontsize=7,
             color=st.INK2, ha="center", va="top", linespacing=1.3)
    axa.text(0.5, 0.0, r"$x = (2/5,\ {-}1/5)$", fontsize=7, color=st.INK2, ha="center", va="bottom")

    # ------------------------------------------------------------------ b: the routed network
    zs = 1.0 / Z_COMPRESS
    segs = []
    for r in routes:
        c = np.array(r["corners"], float)
        c[:, 2] *= zs
        segs.append(c)
    lo = np.array(counts["lattice_min"], float); hi = np.array(counts["lattice_max"], float)
    lo[2] *= zs; hi[2] *= zs
    X0, Y0, Z0 = lo; X1, Y1, Z1 = hi
    faces = [[(X0, Y0, Z0), (X1, Y0, Z0), (X1, Y1, Z0), (X0, Y1, Z0)],       # floor
             [(X0, Y1, Z0), (X1, Y1, Z0), (X1, Y1, Z1), (X0, Y1, Z1)],       # back wall (y = Y1)
             [(X0, Y0, Z0), (X0, Y1, Z0), (X0, Y1, Z1), (X0, Y0, Z1)]]       # left wall (x = X0)
    axb.add_collection3d(Poly3DCollection(faces, facecolors=["#ecebe6", "#f6f6f3", "#f6f6f3"],
                                          edgecolors="none", zorder=0))
    axb.add_collection3d(Line3DCollection(segs, colors="#6da7ec", linewidths=0.2, alpha=0.7, zorder=2))
    coords = np.array([l["coordinate"] for l in labels], float)
    coords[:, 2] *= zs
    cols = [KIND_COLOR[l["kind"]] for l in labels]
    axb.scatter(coords[:, 0], coords[:, 1], coords[:, 2], c=cols, s=8, depthshade=False,
                edgecolors="white", linewidths=0.3, zorder=5)
    special = [i for i, l in enumerate(labels) if l["kind"] in ("input_variable", "output_equation")]
    axb.scatter(coords[special, 0], coords[special, 1], coords[special, 2], s=22, facecolors="none",
                edgecolors=st.INK, linewidths=0.6, depthshade=False, zorder=6)
    for i in (0, 1):
        for j in (0, 1):
            axb.plot([X0, X1], [Y0 + i * (Y1 - Y0)] * 2, [Z0 + j * (Z1 - Z0)] * 2, color=st.AXIS, lw=0.5, zorder=1)
            axb.plot([X0 + i * (X1 - X0)] * 2, [Y0, Y1], [Z0 + j * (Z1 - Z0)] * 2, color=st.AXIS, lw=0.5, zorder=1)
            axb.plot([X0 + i * (X1 - X0)] * 2, [Y0 + j * (Y1 - Y0)] * 2, [Z0, Z1], color=st.AXIS, lw=0.5, zorder=1)
    axb.set_xlim(X0, X1); axb.set_ylim(Y0, Y1); axb.set_zlim(Z0, Z1)
    axb.set_box_aspect((X1 - X0, Y1 - Y0, Z1 - Z0), zoom=1.08)
    axb.set_proj_type("ortho")
    axb.view_init(elev=24, azim=-61)
    axb.set_axis_off()
    handles = [plt.Line2D([], [], marker="o", ls="", ms=4, mfc=c, mec="none", label=l)
               for c, l in ((st.BLUE, "equation site"), (st.AQUA, "variable site"), (st.ORANGE, "sign mediator"))]
    handles.append(plt.Line2D([], [], marker="o", ls="", ms=5, mfc="none", mec=st.INK, mew=0.6,
                              label="source $b_i$ and answer $x_i$ sites"))
    handles.append(plt.Line2D([], [], color="#6da7ec", lw=1.0, label="routed path"))
    fig.legend(handles=handles, loc="center", bbox_to_anchor=(0.4925, 0.175), ncol=5,
               handletextpad=0.4, columnspacing=1.0, borderaxespad=0)

    # ------------------------------------------------------------------ c: readout and decoding
    axc.set_xlim(0, 1); axc.set_ylim(0, 1); axc.set_axis_off()
    axc.text(0.5, 0.99, r"$\langle E, a_i\rangle \;\mapsto\; \hat x$", fontsize=9, ha="center", va="top")
    axc.text(0.5, 0.86, "round, rescale", fontsize=7, color=st.INK2, ha="center", va="top")
    decoded = [819 / 2048, -205 / 1024]
    names = [r"$\hat x_1$", r"$\hat x_2$"]
    for i in range(2):
        y = 0.62 - i * 0.26
        axc.plot([0.12, 0.88], [y, y], color=st.AXIS, lw=0.5)
        for xv in (-0.5, 0, 0.5):
            xx = 0.5 + 0.76 * xv
            axc.plot([xx, xx], [y - 0.02, y + 0.02], color=st.AXIS, lw=0.5)
        axc.plot([0.5 + 0.76 * decoded[i]], [y], marker="o", ms=5, mfc=st.BLUE if decoded[i] > 0 else st.RED,
                 mec="white", mew=0.5)
        axc.text(0.5 + 0.76 * decoded[i], y + 0.045, f"{names[i]} = {decoded[i]:.4f}".replace("-", "−"),
                 fontsize=7, ha="center", va="bottom")
    for xv, lab in ((-0.5, "−0.5"), (0, "0"), (0.5, "0.5")):
        axc.text(0.5 + 0.76 * xv, 0.29, lab, fontsize=6.5, color=st.INK2, ha="center", va="top")
    axc.text(0.5, 0.0, r"$\|M\hat x - b\| = 2^{-11}\|b\| \leq \eta\|b\|$", fontsize=7, color=st.INK2,
             ha="center", va="bottom")

    # ------------------------------------------------------------------ the two readings
    arrow_kw = dict(arrowstyle="-|>", mutation_scale=9, lw=0.9, color=st.INK, shrinkA=0, shrinkB=0)
    fig.add_artist(FancyArrowPatch((0.05, 0.915), (0.225, 0.915), transform=fig.transFigure, **arrow_kw))
    fig.text(0.1375, 0.932, "compile", fontsize=8, ha="center", va="bottom")
    fig.add_artist(FancyArrowPatch((0.775, 0.915), (0.95, 0.915), transform=fig.transFigure, **arrow_kw))
    fig.text(0.8625, 0.932, "read out", fontsize=8, ha="center", va="bottom")
    fig.add_artist(FancyArrowPatch((0.95, 0.078), (0.05, 0.078), transform=fig.transFigure, **arrow_kw))
    fig.text(0.50, 0.095, "simulate", fontsize=8, ha="center", va="bottom")
    fig.text(0.50, 0.058, r"a Maxwell solver of cost $N^{\theta}$ on this family solves $Mx=b$ in "
             r"$\widetilde O(m^{3/2} + m^{3\theta/2})$", fontsize=7, color=st.INK2, ha="center", va="top")

    st.save(fig, HERE / "fig1_concept", {"Title": "Equations, compiled network, readout"})
    plt.close(fig)


if __name__ == "__main__":
    draw()
    print("fig1 done:", {k: counts[k] for k in ("Gplus_vertices", "Gplus_edges", "box_sites", "min_path_length", "max_path_length")})
