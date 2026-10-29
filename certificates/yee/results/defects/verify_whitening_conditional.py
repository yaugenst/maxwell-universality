"""Exact whitening inequalities conditional on a future Hessian enclosure.

The script proves a 3x3 rational implication. It does NOT verify that the
actual Yee band Hessian lies in the stated entrywise interval box.
"""
from fractions import Fraction as F

if not __debug__:
    raise RuntimeError('Exact acceptance requires assertions; do not run with -O or PYTHONOPTIMIZE.')

B = [[49, 22, -22], [22, 56, -19], [-22, -19, 58]]
H0 = [[F(x) for x in row] for row in [
    ["0.335091505105", "0.276600470410", "-0.273554991442"],
    ["0.276600470410", "0.401090571372", "-0.264859129497"],
    ["-0.273554991442", "-0.264859129497", "0.424203777389"],
]]
entry_radius = F(1, 100000)
spectral_radius = 3 * entry_radius
BBt = [[sum(B[i][k] * B[j][k] for k in range(3))
        for j in range(3)] for i in range(3)]


def positive_definite(a):
    m = [row[:] for row in a]
    pivots = []
    for k in range(len(m)):
        pivot = m[k][k]
        assert pivot > 0
        pivots.append(pivot)
        for i in range(k + 1, len(m)):
            for j in range(k + 1, len(m)):
                m[i][j] -= m[i][k] * m[k][j] / pivot
    return pivots


lo = [[BBt[i][j] - 9500 * (H0[i][j] + (spectral_radius if i == j else 0))
       for j in range(3)] for i in range(3)]
hi = [[10500 * (H0[i][j] - (spectral_radius if i == j else 0)) - BBt[i][j]
       for j in range(3)] for i in range(3)]
positive_definite([[H0[i][j] - (spectral_radius if i == j else 0)
                    for j in range(3)] for i in range(3)])
lower_pivots = positive_definite(lo)
upper_pivots = positive_definite(hi)
det_B = (B[0][0] * (B[1][1] * B[2][2] - B[1][2] * B[2][1])
         - B[0][1] * (B[1][0] * B[2][2] - B[1][2] * B[2][0])
         + B[0][2] * (B[1][0] * B[2][1] - B[1][1] * B[2][0]))
assert det_B == 104679
assert F(10500, 9500) < F(4, 3)
print("PASS: for every symmetric H in the specified entrywise radius 1e-5 box,")
print("      9500 H < B B^T < 10500 H and H is positive definite.")
print("      Consequently spectrum(B^T H^-1 B) is contained in (9500,10500).")
print("NOT CHECKED: actual Yee Hessian membership in that interval box.")
print("det B:", det_B)
print("lower LDL pivots:", list(map(str, lower_pivots)))
print("upper LDL pivots:", list(map(str, upper_pivots)))
