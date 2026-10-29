#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["matplotlib>=3.9,<4", "numpy>=2,<3"]
# ///
"""Figure 3: what a uniform Maxwell solver would imply for sparse linear solving.

a: the implied sparse-solver exponent max{3/2, 3 theta/2} against the Maxwell-solver exponent
   theta on the constructed family, with known sparse-solver upper bounds and grid-solver
   reference exponents.
b: the conditional exclusion theta < 2 gamma / 3 under a hardness exponent gamma in (3/2, 2].

Reference exponents (see NOTES.md): m = O~(n), polynomial condition number.
  2        Kelner 2026 (arXiv:2609.38101), O~(mn log(kappa/eps)) bit operations: best known
  2.2716   Nie, STOC 2022: O~(n^{(3w-4)/(w-1)}) with w < 2.37286 (superseded)
  2.3316   Peng & Vempala, SODA 2021 / J. ACM 2025: O(n^{(5w-4)/(w+1)}) with w < 2.372864 (superseded)
  (conjugate gradients in exact arithmetic, O(mn), is a Real-RAM bound and is not drawn)
  theta=2  nested dissection on 3D grids (George 1973; Lipton, Rose, Tarjan 1979)
  theta=1  reading the N-cell instance
Run: uv run --script fig3_consequence.py
"""
from __future__ import annotations

import sys
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.patches import Polygon

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as st

HERE = Path(__file__).resolve().parent
OMEGA = 2.372864
PV = (5 * OMEGA - 4) / (OMEGA + 1)       # 2.331645
NIE = (3 * OMEGA - 4) / (OMEGA - 1)      # 2.27160
BEST = 2.0


def slope_angle(ax, x0, y0, x1, y1):
    p0 = ax.transData.transform((x0, y0)); p1 = ax.transData.transform((x1, y1))
    return np.degrees(np.arctan2(p1[1] - p0[1], p1[0] - p0[0]))


def draw():
    st.apply()
    fig = plt.figure(figsize=(st.WIDTH_MM * st.MM, 70 * st.MM))
    axa = fig.add_axes([0.075, 0.165, 0.555, 0.755])
    axb = fig.add_axes([0.75, 0.165, 0.235, 0.755])
    st.panel_label(fig, "a", 0.005, 0.985)
    st.panel_label(fig, "b", 0.668, 0.985)

    # ---------------------------------------------------------------- a
    th = np.linspace(0.8, 2.3, 400)
    implied = np.maximum(1.5, 1.5 * th)
    theta_cross = BEST / 1.5                                   # 4/3
    axa.set_xlim(0.8, 2.3); axa.set_ylim(1.2, 3.1)
    axa.axvspan(1.0, theta_cross, facecolor=st.BLUE_100, lw=0, zorder=0)
    axa.axvspan(0.8, 1.0, facecolor=st.GRAY_WASH, edgecolor="white", hatch="////", lw=0, zorder=0)
    axa.axhline(BEST, color=st.INK2, lw=0.8, zorder=1)
    axa.text(2.29, BEST + 0.02, r"Kelner 2026: $m^{2}$ (best known, $m = \widetilde O(n)$)", fontsize=7,
             color=st.INK2, ha="right", va="bottom", zorder=6)
    axa.axhline(NIE, color=st.AXIS, lw=0.6, ls=(0, (3, 2)), zorder=1)
    axa.text(2.29, NIE - 0.02, f"Nie 2022: $m^{{{NIE:.2f}}}$", fontsize=7, color=st.MUTED, ha="right", va="top", zorder=6)
    axa.axhline(PV, color=st.AXIS, lw=0.6, ls=(0, (3, 2)), zorder=1)
    axa.text(2.29, PV + 0.02, f"Peng & Vempala 2021: $m^{{{PV:.2f}}}$", fontsize=7, color=st.MUTED, ha="right", va="bottom", zorder=6)
    axa.axvline(1.0, color=st.AXIS, lw=0.6, ls=(0, (1.5, 1.5)), zorder=1)
    axa.axvline(2.0, color=st.AXIS, lw=0.6, ls=(0, (1.5, 1.5)), zorder=1)
    axa.text(0.9, 2.35, "reads the instance", fontsize=7, color=st.INK2, ha="center", va="center", rotation=90, zorder=6,
             bbox=dict(facecolor="white", edgecolor="none", pad=1.5))
    axa.text(2.03, 2.62, "nested dissection\n(3D direct solve)", fontsize=7, color=st.INK2, ha="left", va="bottom",
             zorder=6, linespacing=1.25)
    axa.plot(th, implied, color=st.BLUE, lw=1.6, zorder=4)
    axa.plot([theta_cross], [BEST], marker="o", ms=5, mfc="white", mec=st.BLUE, mew=1.2, zorder=5)
    axa.plot([2.0], [3.0], marker="o", ms=4, mfc=st.BLUE, mec="white", mew=0.6, zorder=5)
    axa.text(theta_cross + 0.03, BEST - 0.04, r"$\theta = 4/3$", fontsize=7, color=st.BLUE, ha="left", va="top")
    axa.text(2.03, 3.0, r"$m^{3}$", fontsize=7, color=st.BLUE, ha="left", va="center")
    ang = slope_angle(axa, 1.6, 2.4, 1.8, 2.7)
    axa.text(1.735, 1.5 * 1.735 + 0.05, r"$\max\{3/2,\ 3\theta/2\}$", fontsize=8, color=st.BLUE,
             ha="center", va="bottom", rotation=ang, rotation_mode="anchor")
    axa.text(1.0 + 0.5 * (theta_cross - 1.0), 1.5, "floor 3/2", fontsize=7, color=st.BLUE, ha="center", va="top")
    axa.text(1.0 + 0.5 * (theta_cross - 1.0), 2.55, "would beat the\nbest known\nsparse solver", fontsize=7,
             color=st.BLUE_600, ha="center", va="center", linespacing=1.25)
    axa.set_xticks([1, 4 / 3, 1.5, 2])
    axa.set_xticklabels(["1", "4/3", "3/2", "2"])
    axa.set_yticks([1.5, 2, 2.5, 3]); axa.set_yticklabels(["3/2", "2", "5/2", "3"])
    axa.set_xlabel(r"Maxwell-solver exponent $\theta$ (cost $N^{\theta}$ on the constructed family)")
    axa.set_ylabel("implied sparse-solver exponent")

    # ---------------------------------------------------------------- b
    g = np.linspace(1.5, 2.0, 50)
    axb.add_patch(Polygon([(1.5, 0.8), (2.0, 0.8), (2.0, 4 / 3), (1.5, 1.0)], closed=True,
                          facecolor=st.ORANGE_WASH, edgecolor="none", zorder=0))
    axb.plot(g, 2 * g / 3, color=st.ORANGE, lw=1.4, zorder=3)
    axb.axhline(1.0, color=st.AXIS, lw=0.6, ls=(0, (1.5, 1.5)), zorder=1)
    axb.text(1.75, 0.95, "excluded if sparse\nsolving needs $m^{\\gamma}$", fontsize=7, color=st.INK2,
             ha="center", va="center", linespacing=1.25)
    axb.text(1.52, 1.55, r"$\theta < 2\gamma/3$", fontsize=8, color=st.ORANGE, ha="left", va="top")
    axb.text(1.98, 4 / 3 + 0.03, "4/3", fontsize=7, color=st.ORANGE, ha="right", va="bottom")
    axb.set_xlim(1.5, 2.0); axb.set_ylim(0.8, 1.6)
    axb.set_xticks([1.5, 1.75, 2.0]); axb.set_xticklabels(["3/2", "7/4", "2"])
    axb.set_yticks([1.0, 4 / 3, 1.5]); axb.set_yticklabels(["1", "4/3", "3/2"])
    axb.set_xlabel(r"hardness exponent $\gamma$")
    axb.set_ylabel(r"Maxwell-solver exponent $\theta$")

    st.save(fig, HERE / "fig3_consequence", {"Title": "Exponent transfer from Maxwell solvers to sparse solvers"})
    plt.close(fig)


if __name__ == "__main__":
    draw()
    print(f"PV={PV:.6f} NIE={NIE:.6f}")
