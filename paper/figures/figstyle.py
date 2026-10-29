"""Shared style for the main-text figures (imported by the fig*_*.py scripts).

Palette: the validated categorical order blue, orange, aqua, yellow, ... from the
dataviz reference instance; diverging pair blue/red; chrome in warm grays.
Sizes: 160 mm text block, 8 pt base, 7 pt ticks, 9 pt bold panel labels.
"""
from pathlib import Path

import matplotlib as mpl

MM = 1 / 25.4
WIDTH_MM = 160.0

INK = "#0b0b0b"
INK2 = "#52514e"
MUTED = "#898781"
GRID = "#e1e0d9"
AXIS = "#c3c2b7"
SURFACE = "#ffffff"

BLUE = "#2a78d6"
ORANGE = "#eb6834"
AQUA = "#1baf7a"
YELLOW = "#eda100"
MAGENTA = "#e87ba4"
GREEN = "#008300"
VIOLET = "#6250d6"
RED = "#e34948"

BLUE_100 = "#cde2fb"
BLUE_250 = "#86b6ef"
BLUE_600 = "#184f95"
ORANGE_WASH = "#fbe1d6"
RED_WASH = "#fadada"
GRAY_WASH = "#f0efec"


def apply():
    mpl.rcParams.update({
        "font.family": "sans-serif",
        # TrueType fonts first: matplotlib embeds them cleanly as Type 42 (OTF/CFF fonts trigger
        # "font type mismatch" warnings in poppler and some submission checkers)
        "font.sans-serif": ["Helvetica", "Arial", "Liberation Sans", "TeX Gyre Heros",
                            "Nimbus Sans", "DejaVu Sans"],
        "mathtext.fontset": "stixsans",
        "font.size": 8,
        "axes.titlesize": 8,
        "axes.labelsize": 8,
        "xtick.labelsize": 7,
        "ytick.labelsize": 7,
        "legend.fontsize": 7,
        "text.color": INK,
        "axes.labelcolor": INK,
        "axes.edgecolor": AXIS,
        "axes.linewidth": 0.5,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "xtick.color": MUTED,
        "ytick.color": MUTED,
        "xtick.labelcolor": INK2,
        "ytick.labelcolor": INK2,
        "xtick.major.width": 0.5,
        "ytick.major.width": 0.5,
        "xtick.major.size": 2.5,
        "ytick.major.size": 2.5,
        "xtick.direction": "out",
        "ytick.direction": "out",
        "lines.linewidth": 1.0,
        "lines.solid_capstyle": "round",
        "lines.solid_joinstyle": "round",
        "legend.frameon": False,
        "legend.handlelength": 1.6,
        "legend.handletextpad": 0.5,
        "figure.facecolor": SURFACE,
        "axes.facecolor": SURFACE,
        "savefig.facecolor": SURFACE,
        "pdf.fonttype": 42,
        "ps.fonttype": 42,
        "svg.fonttype": "none",
    })


def panel_label(fig_or_ax, letter, x, y, transform=None):
    """Bold lowercase panel label at (x, y) in the given transform (default: figure)."""
    fig = fig_or_ax.figure if hasattr(fig_or_ax, "figure") and transform is not None else fig_or_ax
    if transform is None:
        transform = fig.transFigure
    fig.text(x, y, letter, fontsize=9, fontweight="bold", ha="left", va="top",
             transform=transform, color=INK)


def save(fig, stem: Path, metadata=None):
    meta = {"Creator": "matplotlib", "CreationDate": None}
    if metadata:
        meta.update(metadata)
    fig.savefig(stem.with_suffix(".pdf"), metadata=meta)
    fig.savefig(stem.with_suffix(".png"), dpi=300)
