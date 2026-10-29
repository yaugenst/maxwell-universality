"""Independent pure-integer check of the supplied finite defect geometry.

Uses doubled physical coordinates, whereas supplied exact_geometry.py uses
eightfold coordinates. No supplied geometry or incidence code is imported.
This verifies finite geometry/counts only, not spectral hypotheses H1-H3.
"""
from collections import Counter
from fractions import Fraction
from itertools import product
import json

if not __debug__:
    raise RuntimeError('Exact acceptance requires assertions; do not run with -O or PYTHONOPTIMIZE.')

PERIOD = 20
fcc_doubled = [(0, 0, 0), (0, 20, 20), (20, 0, 20), (20, 20, 0)]
centers = [tuple((v + sign * 5) % 40 for v in f)
           for f in fcc_doubled for sign in (-1, 1)]


def high(cell):
    point = tuple(2 * (v % PERIOD) + 1 for v in cell)
    for center in centers:
        d = tuple((a - b + 20) % 40 - 20 for a, b in zip(point, center))
        if sum(v * v for v in d) <= 100:
            return True
    return False


all_cells = list(product(range(PERIOD), repeat=3))
assert sum(map(high, all_cells)) == 3928
defect = [c for c in product(range(7, 14), range(6, 14), range(6, 15))
          if not high(c)]
assert len(defect) == 392
counts = Counter()
for cell in defect:
    for direction in range(3):
        others = [j for j in range(3) if j != direction]
        for offsets in product((0, 1), repeat=2):
            anchor = list(cell)
            for j, offset in zip(others, offsets):
                anchor[j] += offset
            counts[tuple(anchor) + (direction,)] += 1
assert len(counts) == 1588
assert set(counts.values()) == {1, 2, 3, 4}

edge_materials = set()
for anchor in all_cells:
    for direction in range(3):
        others = [j for j in range(3) if j != direction]
        total = 0
        for offsets in product((0, -1), repeat=2):
            cell = list(anchor)
            for j, offset in zip(others, offsets):
                cell[j] += offset
            total += 12 if high(tuple(cell)) else 1
        edge_materials.add(Fraction(total, 4))
assert edge_materials == set(map(Fraction, [1, 12])) | {
    Fraction(15, 4), Fraction(13, 2), Fraction(37, 4)}

report = {
    "verified": "finite geometry only; no spectrum/coupling claim",
    "high_cells_per_conventional_period": 3928,
    "air_cells_in_defect": len(defect),
    "affected_electric_edges": len(counts),
    "changed_incidence_histogram": dict(sorted(Counter(counts.values()).items())),
    "edge_material_values": list(map(str, sorted(edge_materials))),
    "changed_incidence_total": sum(counts.values()),
}
assert report["changed_incidence_total"] == 12 * len(defect)
print(json.dumps(report, indent=2))
print("PASS: independent exact scalar geometry and edge-incidence counts")
