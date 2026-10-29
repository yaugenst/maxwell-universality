"""Exact arithmetic checks for constants in h2_existential_replacement.md.

This checks only the displayed rational inequalities, not H1 and not H3.
The H2 proof is analytic; the constructive parameter search is not run.
"""
from fractions import Fraction as F

if not __debug__:
    raise RuntimeError('Exact acceptance requires assertions; do not run with -O or PYTHONOPTIMIZE.')

g = F(1, 4096)
J = F(16)
t = F(1, 64)
pi_lower = F(157, 50)
pi_upper = F(22, 7)
# The classical pi bounds and sine inequalities are analytic premises.
sin_lower = pi_lower / 20 - (pi_upper / 20) ** 3 / 6
assert sin_lower == F(12871, 82320)
assert sin_lower > F(5, 32)
assert 8 * (pi_upper / 20) ** 2 == F(242, 1225)
assert F(242, 1225) < F(1, 5)
assert 8 * F(5, 32) ** 2 - F(3, 16) == F(1, 128)
assert F(1, 5) - F(1, 64) == F(59, 320)
sqrt_L = 45312 * J / g
assert sqrt_L.denominator == 1
L = sqrt_L**2
assert L == 8818329545368141824
assert 1024 * J / (g * sqrt_L) == F(4, 177)
assert F(320, 59) - F(4, 177) == F(956, 177)
beta = g**2 / (1024 * t)
assert beta == F(1, 2**28)
operator_shift = t * beta
assert operator_shift < g / 2
resolvent_error = operator_shift / (g * (g - operator_shift))
assert resolvent_error < F(1, 512)
assert F(956, 177) - F(1, 512) > F(16, 3)
assert 12 + beta + 12 + 8 * g < F(49, 2)
assert pi_lower > F(25, 8)
assert F(25, 64) < 4 * pi_lower**2 / 100
print("PASS: displayed H2 rational inequalities")
print("NOT CHECKED HERE: original H1 certificate; H3; termination run for fixed data")
print(f"L={L}, beta={beta}, resolvent_error={resolvent_error}")
