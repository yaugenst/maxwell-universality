#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.11"
# dependencies = ["matplotlib>=3.9,<4", "numpy>=2,<3"]
# ///
"""Figure 2: mechanism. Computed band structure of the continuum background and the
proven coupling-rate hierarchy.

Panel a: Bloch eigenvalues of H = curl curl - eps(x), eps = 7 + delta[cos(pi x1) + 2 cos(pi x2)
         + 4 cos(pi x3)] (period 2), along k = k* + q1 e1 through k* = (pi/2, pi/2, pi/2),
         vector plane-wave expansion, delta exaggerated to 0.5.
Panel b: the selected branch near k* in scaled variables t = q/delta, (lambda - E_c)/delta,
         at delta = 2^-8 (the small-delta regime of the paper), against the paper's exact
         leading-order Hessian A0 = pi^2 diag(t1, t2, t3).
Panel c: the proven exponential rate bounds for defect couplings versus separation d.
Panel d: the terminal-mediator-terminal Schur elimination.

Band data are cached in fig2_band_data.json (delete it or pass --recompute to redo).
Run: uv run --script fig2_mechanism.py
"""
from __future__ import annotations

import json
import sys
import time
from itertools import product
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.patches import Circle, FancyArrowPatch

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import figstyle as st

HERE = Path(__file__).resolve().parent
CACHE = HERE / "fig2_band_data.json"

KAPPA = np.pi / 2
KSTAR = np.array([KAPPA, KAPPA, KAPPA])
E0 = 3 * KAPPA ** 2 - 7                                   # free corner energy
LAM_STAR = (5 + 2 * np.sqrt(19)) / 6                      # top cluster root
T_COEF = np.array([47 / 31 + 352 * np.sqrt(19) / 589,
                   2 + 11 * np.sqrt(19) / 38,
                   1 / 8 + 11 * np.sqrt(19) / 152])
A0 = np.pi ** 2 * T_COEF                                  # paper: A = A0 / delta
DELTA_A = 0.5
DELTA_B = 2.0 ** -8
NCUT = 3


# ----------------------------------------------------------------------------- plane waves
def fiber(k, delta, N):
    """Hermitian matrix of curl curl - eps on Bloch fields e^{i(k+pi n).x}, |n_j| <= N."""
    rng = range(-N, N + 1)
    ns = np.array(list(product(rng, rng, rng)), int)
    index = {tuple(n): i for i, n in enumerate(ns)}
    M = len(ns)
    H = np.zeros((3 * M, 3 * M))
    p = k[None, :] + np.pi * ns
    for i in range(M):
        pi_ = p[i]
        H[3 * i:3 * i + 3, 3 * i:3 * i + 3] = pi_ @ pi_ * np.eye(3) - np.outer(pi_, pi_) - 7 * np.eye(3)
    weights = (delta / 2, delta, 2 * delta)               # cos(pi x1), 2 cos(pi x2), 4 cos(pi x3)
    for i, n in enumerate(ns):
        for j in range(3):
            for s in (-1, 1):
                m = n.copy(); m[j] += s
                jj = index.get(tuple(m))
                if jj is not None:
                    H[3 * i:3 * i + 3, 3 * jj:3 * jj + 3] -= weights[j] * np.eye(3)
    return H


def eigs(k, delta, N=NCUT):
    return np.linalg.eigvalsh(fiber(k, delta, N))


def cluster(ev, delta):
    """The 16 transverse branches of the corner cluster (window E0 +- 4 delta at k*)."""
    return ev[(ev > E0 - 4 * delta) & (ev < E0 + 4 * delta)]


def selected(k, delta, N=NCUT):
    return cluster(eigs(k, delta, N), delta).max()


def compute():
    t_start = time.time()
    data = {"conventions": {
        "operator": "H(k) = curl curl - eps(x) on Bloch fields; eigenvalue parameter lambda",
        "eps": "7 + delta [cos(pi x1) + 2 cos(pi x2) + 4 cos(pi x3)], period 2, reciprocal lattice pi Z^3",
        "kstar": [KAPPA] * 3, "E0": E0, "lambda_star": LAM_STAR, "A0_diag": A0.tolist(),
        "plane_wave_cutoff": NCUT, "matrix_dimension": 3 * (2 * NCUT + 1) ** 3}}

    # Panel a: delta = 0.5, q1 in [-1, 1]
    q1 = np.linspace(-1.0, 1.0, 161)
    all_ev = []
    for q in q1:
        ev = eigs(KSTAR + np.array([q, 0, 0]), DELTA_A)
        all_ev.append(ev[ev < 9.0].tolist())
    Ec_a = selected(KSTAR, DELTA_A)
    data["a"] = {"delta": DELTA_A, "q1": q1.tolist(), "eigenvalues_below_9": all_ev, "Ec": Ec_a}

    # Panel b: delta = 2^-8, scaled chart along three axes, all 16 cluster branches
    t = np.linspace(-0.06, 0.06, 97)
    Ec_b = selected(KSTAR, DELTA_B)
    branches = {}
    for j in range(3):
        rows = []
        for tt in t:
            q = np.zeros(3); q[j] = DELTA_B * tt
            rows.append(((cluster(eigs(KSTAR + q, DELTA_B), DELTA_B) - Ec_b) / DELTA_B).tolist())
        branches[f"e{j + 1}"] = rows
    data["b"] = {"delta": DELTA_B, "t": t.tolist(), "Ec": Ec_b, "scaled_cluster_branches": branches}

    # Checks: cutoff convergence, Hessian, small-delta scaling collapse, gradient band extent
    checks = {}
    for name, delta in (("a", DELTA_A), ("b", DELTA_B)):
        checks[f"Ec_vs_cutoff_{name}"] = {str(N): selected(KSTAR, delta, N) for N in (1, 2, 3, 4)}
    hess = {}
    for delta in (2.0 ** -6, DELTA_B, 2.0 ** -10):
        Ec = selected(KSTAR, delta)
        h = 1e-3 * delta
        diag = []
        for j in range(3):
            q = np.zeros(3); q[j] = h
            diag.append((selected(KSTAR + q, delta) + selected(KSTAR - q, delta) - 2 * Ec) / (2 * h * h))
        q = np.array([h, h, 0]); qm = np.array([h, -h, 0])
        mixed = (selected(KSTAR + q, delta) + selected(KSTAR - q, delta)
                 - selected(KSTAR + qm, delta) - selected(KSTAR - qm, delta)) / (8 * h * h)
        hess[str(delta)] = {"Ec": Ec, "(Ec-E0)/delta": (Ec - E0) / delta,
                            "delta*A_diag": (np.array(diag) * delta).tolist(),
                            "delta*A_diag/A0": (np.array(diag) * delta / A0).tolist(),
                            "delta*A_12": mixed * delta}
    checks["hessian_finite_difference_N3"] = hess
    collapse = {}
    for delta in (2.0 ** -6, 2.0 ** -10):
        Ec = selected(KSTAR, delta)
        vals = []
        for j in range(3):
            q = np.zeros(3); q[j] = delta * 0.03
            vals.append((selected(KSTAR + q, delta) - Ec) / delta)
        collapse[str(delta)] = vals
    vals = []
    for j in range(3):
        q = np.zeros(3); q[j] = DELTA_B * 0.03
        vals.append((selected(KSTAR + q, DELTA_B) - Ec_b) / DELTA_B)
    collapse[str(DELTA_B)] = vals
    checks["scaled_branch_at_t_0.03_vs_delta"] = collapse
    grad = {}
    for N in (2, 3, 4):
        ev = eigs(KSTAR, DELTA_A, N)
        low = ev[ev < -2.0]
        cl = cluster(ev, DELTA_A)
        grad[str(N)] = {"min": float(low.min()), "max": float(low.max()), "count": int(len(low)),
                        "cluster_min": float(cl.min()), "cluster_count": int(len(cl))}
    checks["gradient_band_at_kstar_delta_a"] = grad
    checks["cluster_gap_scaled_at_kstar"] = {
        "delta_b": float(np.sort(cluster(eigs(KSTAR, DELTA_B), DELTA_B))[-1] -
                         np.sort(cluster(eigs(KSTAR, DELTA_B), DELTA_B))[-2]) / DELTA_B,
        "paper_lambda_star_minus_next": LAM_STAR - (0.5 + np.sqrt(3))}
    checks["wall_time_s"] = time.time() - t_start
    data["checks"] = checks
    CACHE.write_text(json.dumps(data, indent=1))
    return data


# ----------------------------------------------------------------------------- figure
def draw(data):
    st.apply()
    fig = plt.figure(figsize=(st.WIDTH_MM * st.MM, 118 * st.MM))
    axa = fig.add_axes([0.075, 0.585, 0.40, 0.355])
    axb = fig.add_axes([0.60, 0.585, 0.385, 0.355])
    axc = fig.add_axes([0.075, 0.085, 0.40, 0.355])
    axd = fig.add_axes([0.545, 0.085, 0.44, 0.355])
    for letter, x, y in (("a", 0.005, 0.985), ("b", 0.515, 0.985), ("c", 0.005, 0.485), ("d", 0.515, 0.485)):
        st.panel_label(fig, letter, x, y)

    # --- a: band structure along q1 through k*
    a = data["a"]
    q1 = np.array(a["q1"]); Ec = a["Ec"]; delta = a["delta"]
    # the 16 transverse branches of the corner cluster are the 16 highest eigenvalues below 9
    cl = np.array([sorted(row)[-16:] for row in a["eigenvalues_below_9"]])          # (nq, 16)
    # curl-free fields contribute the band lambda = -eps(x); the finite-cutoff eigenvalues lie inside it
    band_lo, band_hi = -7 - 7 * delta, -7 + 7 * delta
    grad = np.array([v for row in a["eigenvalues_below_9"] for v in sorted(row)[:-16]])
    assert grad.min() >= band_lo and grad.max() <= band_hi and cl.min() > band_hi
    axa.fill_between([-1, 1], band_lo, band_hi, color=st.GRAY_WASH, lw=0, zorder=1)
    for b in range(cl.shape[1] - 1):
        axa.plot(q1, cl[:, b], color=st.MUTED, lw=0.55, zorder=3)
    axa.plot(q1, cl[:, -1], color=st.BLUE, lw=1.4, zorder=5)
    axa.axhline(Ec, color=st.BLUE, lw=0.5, ls=(0, (2, 2)), zorder=4)
    axa.text(0.985, Ec, r"$E_c$", color=st.BLUE, fontsize=7, ha="right", va="bottom", zorder=6)
    axa.annotate("selected branch", xy=(0.52, float(np.interp(0.52, q1, cl[:, -1]))), xytext=(0.22, 5.9),
                 fontsize=7, color=st.BLUE, ha="left", va="center",
                 arrowprops=dict(arrowstyle="-", color=st.BLUE, lw=0.5, shrinkA=0, shrinkB=2))
    i_lead = int(np.argmin(np.abs(q1 + 0.42)))
    axa.annotate("15 other branches of the corner cluster", xy=(q1[i_lead], cl[i_lead, 9]), xytext=(-0.97, 7.45),
                 fontsize=7, color=st.INK2, ha="left", va="top",
                 arrowprops=dict(arrowstyle="-", color=st.MUTED, lw=0.5, shrinkA=1, shrinkB=1.5))
    axa.text(0.0, 0.5 * (band_lo + band_hi), r"curl-free fields: $\lambda = -\varepsilon(r)$", fontsize=7,
             color=st.INK2, ha="center", va="center")
    axa.set_xlim(-1, 1); axa.set_ylim(-11.5, 7.6)
    axa.set_xticks([-1, -0.5, 0, 0.5, 1]); axa.set_xticklabels(["−1", "−0.5", r"$k_*$", "0.5", "1"])
    axa.set_yticks([-10, -5, 0, 5])
    axa.set_xlabel(r"Bloch wavevector offset $q_1$ along $(1,0,0)$")
    axa.set_ylabel(r"eigenvalue $\lambda$ of $\nabla\!\times\!\nabla\!\times - \varepsilon$")
    axa.text(-0.96, band_hi - 0.5, rf"$\varrho = {delta}$", fontsize=7, color=st.INK2, ha="left", va="top")

    # --- b: scaled chart near k* at small delta
    b = data["b"]
    t = np.array(b["t"])
    cols = {"e1": st.BLUE, "e2": st.ORANGE, "e3": st.AQUA}
    names = {"e1": r"$q \parallel (1,0,0)$", "e2": r"$q \parallel (0,1,0)$", "e3": r"$q \parallel (0,0,1)$"}
    tt = np.linspace(-0.06, 0.06, 301)
    for j, key in enumerate(("e1", "e2", "e3")):
        rows = np.array(b["scaled_cluster_branches"][key])       # (nt, 16), sorted ascending
        for col in range(rows.shape[1] - 1):
            axb.plot(t, rows[:, col], color=st.GRID, lw=0.5, zorder=1)
        axb.plot(tt, A0[j] * tt ** 2, color=cols[key], lw=0.8, ls=(0, (2.2, 1.6)), zorder=3)
        axb.plot(t, rows[:, -1], color=cols[key], lw=1.3, zorder=4, label=names[key])
    axb.set_xlim(-0.045, 0.045); axb.set_ylim(-0.075, 0.075)
    axb.set_xticks([-0.04, -0.02, 0, 0.02, 0.04]); axb.set_xticklabels(["−0.04", "−0.02", "0", "0.02", "0.04"])
    axb.set_yticks([-0.05, 0, 0.05]); axb.set_yticklabels(["−0.05", "0", "0.05"])
    axb.set_xlabel(r"scaled offset $q_j/\varrho$")
    axb.set_ylabel(r"$(\lambda - E_c)/\varrho$")
    axb.legend(loc="upper center", ncol=1, bbox_to_anchor=(0.5, 1.0), handlelength=1.4, borderaxespad=0.1)
    axb.text(0.03, 0.03, rf"$\varrho = 2^{{-8}}$" "\n" r"dashed: $q^{T}\!H_0\,q/\varrho$", transform=axb.transAxes,
             fontsize=7, color=st.INK2, va="bottom", ha="left")
    axb.text(0.985, 0.37, "next cluster branches", transform=axb.transAxes, fontsize=7, color=st.INK2,
             ha="right", va="top")

    # --- c: proven rate bounds vs separation
    dd = np.linspace(1, 12, 200)
    axc.fill_between(dd, 8.0 ** -dd, 3.0 ** -dd, color=st.BLUE_100, lw=0, zorder=1)
    axc.plot(dd, 3.0 ** -dd, color=st.BLUE, lw=0.8, ls=(0, (2.2, 1.6)), zorder=3)
    axc.plot(dd, 8.0 ** -dd, color=st.BLUE, lw=1.3, zorder=4)
    axc.plot(dd, 9.0 ** -dd, color=st.ORANGE, lw=1.3, zorder=4)
    axc.set_yscale("log")
    axc.set_xlim(1, 14.6); axc.set_ylim(1e-12, 3)
    axc.set_xticks([2, 4, 6, 8, 10, 12])
    axc.set_yticks([1, 1e-3, 1e-6, 1e-9, 1e-12])
    axc.set_xlabel(r"defect separation $d$ on the placement lattice")
    axc.set_ylabel("coupling bound (prefactors dropped)")
    axc.text(8.0, 3e-2, r"every block: $\leq 3^{-d\,\|\nu\|_1}$", color=st.BLUE, fontsize=7, ha="center", va="center")
    axc.text(9.9, 4.0e-7, "useful coupling\n$h_j(d)$ lies here", color=st.BLUE_600, fontsize=7,
             ha="center", va="center", linespacing=1.25)
    axc.text(9.3, 1.2e-10, r"$\geq 8^{-d}$", color=st.BLUE, fontsize=7, ha="center", va="center")
    axc.text(3.4, 1e-8, "unwanted,\n$\\|\\nu\\|_1 \\geq 2$:\n$\\leq 9^{-d}$", color=st.ORANGE, fontsize=7,
             ha="left", va="center", linespacing=1.25)
    axc.annotate("", xy=(12.4, 9.0 ** -12.4), xytext=(12.4, 8.0 ** -12.4),
                 arrowprops=dict(arrowstyle="-", color=st.INK2, lw=0.7, shrinkA=0, shrinkB=0))
    axc.text(12.6, np.sqrt(9.0 ** -12.4 * 8.0 ** -12.4), r"gap $(8/9)^d$", color=st.INK2, fontsize=7, ha="left", va="center")

    # --- d: terminal-mediator-terminal Schur elimination (sketch)
    bb = axd.get_position(); H = bb.height * 118 / (bb.width * st.WIDTH_MM)      # axes height in x-units
    axd.set_xlim(0, 1); axd.set_ylim(0, H); axd.set_aspect("equal"); axd.set_axis_off()
    r = 0.045
    y1, y2 = 0.47, 0.13
    nodes = [(0.17, y1, st.BLUE, r"$z_i$"), (0.50, y1, st.ORANGE, r"$u$"), (0.83, y1, st.BLUE, r"$z_j$")]
    for x, y, c, lab in nodes:
        axd.add_patch(Circle((x, y), r, facecolor=c, edgecolor="none", zorder=3))
        axd.text(x, y, lab, color="white", fontsize=8, ha="center", va="center", zorder=4)
    axd.plot([0.17 + r, 0.50 - r], [y1, y1], color=st.INK2, lw=1.0, zorder=2)
    axd.plot([0.50 + r, 0.83 - r], [y1, y1], color=st.INK2, lw=1.0, zorder=2)
    axd.text(0.335, y1 + 0.03, r"$\beta_j$", fontsize=8, ha="center", va="bottom")
    axd.text(0.665, y1 + 0.03, r"$\beta_j$", fontsize=8, ha="center", va="bottom")
    axd.text(0.17, y1 - r - 0.02, "terminal", fontsize=7, color=st.INK2, ha="center", va="top")
    axd.text(0.50, y1 - r - 0.02, "mediator", fontsize=7, color=st.INK2, ha="center", va="top")
    axd.text(0.83, y1 - r - 0.02, "terminal", fontsize=7, color=st.INK2, ha="center", va="top")
    axd.text(0.50, y1 + r + 0.035, r"$\Theta_{uu} = -\beta_j^{2}/\alpha$", fontsize=7.5, ha="center", va="bottom", color=st.INK2)
    axd.add_patch(FancyArrowPatch((0.50, y1 - r - 0.065), (0.50, y2 + r + 0.075), arrowstyle="-|>", mutation_scale=8,
                                  lw=0.8, color=st.INK2, zorder=2))
    axd.text(0.53, 0.5 * (y1 + y2), "eliminate the mediator\n(Schur complement)", fontsize=7,
             color=st.INK2, ha="left", va="center", linespacing=1.25)
    for x in (0.17, 0.83):
        axd.add_patch(Circle((x, y2), r, facecolor=st.BLUE, edgecolor="none", zorder=3))
    axd.text(0.17, y2, r"$z_i$", color="white", fontsize=8, ha="center", va="center", zorder=4)
    axd.text(0.83, y2, r"$z_j$", color="white", fontsize=8, ha="center", va="center", zorder=4)
    axd.plot([0.17 + r, 0.83 - r], [y2, y2], color=st.INK2, lw=1.0, zorder=2)
    axd.text(0.50, y2 + 0.03, r"$-\beta_j\,\Theta_{uu}^{-1}\beta_j = \alpha$", fontsize=8, ha="center", va="bottom")
    axd.text(0.50, y2 - r - 0.02, r"effective network $\alpha\,\Gamma$: unit edges, tuned diagonals",
             fontsize=7, color=st.INK2, ha="center", va="top")

    st.save(fig, HERE / "fig2_mechanism",
            {"Title": "Mechanism: computed local band minimum and proven coupling rates"})
    plt.close(fig)


if __name__ == "__main__":
    if CACHE.exists() and "--recompute" not in sys.argv:
        data = json.loads(CACHE.read_text())
    else:
        data = compute()
    draw(data)
    print(json.dumps(data["checks"], indent=1))
