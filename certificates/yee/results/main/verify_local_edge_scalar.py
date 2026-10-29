"""Exact scalar closure for the radius-1/20 local band-minimum lemma.

The finite matrix hypotheses (parity, true eigenspace, Y, K2, residual Gram,
and uniform inertia) are NOT proved by this script. They require the
separate local spectral certificates. This checks their stated implication.
"""
from fractions import Fraction as F
from math import factorial
import json
import sys

if not __debug__:
    raise RuntimeError("Do not disable assertions")

r = F(1, 20)
theta = F(11, 70)  # pi/20 < (22/7)/20
Y = F(3)


def a(j):
    assert j >= 1
    return F(4 * 2**j + 6, factorial(j)) * theta**j


# Every even-step tail ratio is bounded by this common geometric ratio.
ratio = (2 * theta * r)**2 / 12
assert ratio < F(1, 40000)
tail = 1 / (1 - F(1, 40000))
K4 = (a(4) + 2 * Y * a(3) + Y**2 * a(2)) * tail
R3 = (a(3) + Y * a(2)) * tail
R4 = (a(4) + Y * a(3)) * tail
assert K4 < F(13, 5)
assert R3 < F(17, 20)
assert R4 < F(2, 25)

kmin, kmax = F(1, 50), F(1)
c2 = F(18, 5)
delta = F(1, 2**20)
b = F(7, 256)
Elo, Ehi = F(239, 25000), F(957, 100000)
Blo, Bhi = b - Ehi, b - Elo
k4, c3, c4 = F(13, 5), F(17, 20), F(2, 25)
# sqrt(c2/kmin)=sqrt(180)<27/2.
assert c2 / kmin < F(27, 2)**2
lower = (Blo - 2 * delta * kmax / kmin - c2 * r**2
         - Bhi * k4 / kmin * r**2 - 2 * delta * c4 / kmin * r**2
         - (27 * c4 + c3**2 / kmin) * r**4
         - c4**2 / kmin * r**6)
assert lower > F(1, 400)
assert delta < Blo
g_coercivity = F(1, 400) * kmin
trial_norm_square = 1 + Y**2 * r**2
band_coercivity = g_coercivity / trial_norm_square / b
assert band_coercivity > F(1, 600)

print(json.dumps({
    "scope": "Exact scalar implication only; finite matrix hypotheses separate",
    "radius": str(r), "tail_ratio_bound": str(ratio),
    "K4_upper": str(K4), "R3_upper": str(R3), "R4_upper": str(R4),
    "g_relative_coefficient_lower": str(lower),
    "g_relative_target": "1/400",
    "band_coercivity_lower": str(band_coercivity),
    "band_coercivity_target": "1/600", "assertions_enabled": __debug__,
    "python": sys.version,
}, indent=2))
