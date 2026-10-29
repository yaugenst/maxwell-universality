#!/usr/bin/env python3
"""Exact arithmetic-only checks in the independent H2 analytic review."""
from fractions import Fraction as F
import json

if not __debug__:
    raise RuntimeError("Assertions are required; do not use -O.")

g = F(1, 4096)
t = F(1, 64)
J = 16
beta = g * g / 16
sin_lower = F(157, 1000) - F(11, 70) ** 3 / 6
assert sin_lower == F(12871, 82320) > F(5, 32)
assert 8 * F(5, 32) ** 2 == F(25, 128)
assert 8 * F(11, 70) ** 2 == F(242, 1225) < F(1, 5)
L = (45312 * J / g) ** 2
assert L == 8818329545368141824
assert F(1024, 45312) == F(4, 177)
rayleigh_lower = F(320, 59) - F(4, 177)
assert rayleigh_lower == F(956, 177)
margin = rayleigh_lower - F(1, 512) - F(16, 3)
assert margin == F(1989, 30208) > 0
shift = t * beta
assert shift == g * g / 1024 < g / 2
assert shift / (g * (g - shift)) < F(1, 512)
assert 24 + beta + 8 * g < F(49, 2)
print(json.dumps({
    "status": "PASS: exact scalar inequalities only; H1 remains assumed",
    "L": str(L),
    "sin_lower": str(sin_lower),
    "rayleigh_lower": str(rayleigh_lower),
    "mu_margin_above_16_over_3": str(margin),
    "maximum_permittivity_bound": str(24 + beta + 8 * g),
}, indent=2))
