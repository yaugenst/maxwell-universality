# /// script
# requires-python = ">=3.11"
# dependencies = ["numpy"]
# ///
"""Propose exact dyadic point witnesses; all finite claims are checked in Lean."""
from pathlib import Path
import importlib.util
import json
import numpy as np

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT.parent / "certificates/yee" / "results" / "defects"
OUT = ROOT / "Maxwell" / "Certificate" / "PointWitness"
OUT.mkdir(exist_ok=True)
spec = importlib.util.spec_from_file_location("exact_edge_arithmetic", SOURCE / "exact_edge_arithmetic.py")
arithmetic = importlib.util.module_from_spec(spec)
spec.loader.exec_module(arithmetic)
doc = json.loads((SOURCE / "inversion_edge_material.json").read_text())
model = arithmetic.ExactFiber((1, 1, 0), doc["full_conventional_perturbation_numerators"])
with np.load(SOURCE / "explore_inversion_edge_feshbach.npz", allow_pickle=False) as data:
    vectors = data["inversion_perturbed_eigenvectors"]
    proposals = [model.project(arithmetic.quantize(vectors[:, a]), 1) for a in range(2)]
images = [model.apply_mass_scaled(v) for v in proposals]


def vector(v):
    return "![" + ", ".join(v) + "]"


def emit_table(name, values):
    out = ["import Maxwell.Certificate.IntegerAction\n", "namespace Maxwell.Certificate.PointWitness\n",
           "open Maxwell.Spectral.PrimitiveYee\n", "set_option maxRecDepth 100000\n", "set_option maxHeartbeats 0\n"]
    for j in range(3):
        for x in range(20):
            rows = [vector([str(int(values[j * 2000 + x * 100 + y * 10 + z])) for z in range(10)]) for y in range(10)]
            out.append(f"def {name}_{j}_{x} : Fin 10 → Fin 10 → ℤ := {vector(rows)}\n")
    rows = [vector([f"{name}_{j}_{x}" for x in range(20)]) for j in range(3)]
    out.append(f"def {name} (e : Electric) : ℤ := ({vector(rows)}) e.1 e.2.1 e.2.2.1 e.2.2.2\n")
    out.append("end Maxwell.Certificate.PointWitness\n")
    (OUT / f"{name.title()}.lean").write_text("\n".join(out))

for a in range(2):
    emit_table(f"numerator{a}", proposals[a])
    emit_table(f"imageNumerator{a}", images[a])
parts = [f"import Maxwell.Certificate.PointWitness.{name.title()}\n" for name in ("numerator0", "imageNumerator0", "numerator1", "imageNumerator1")]
parts.extend(["namespace Maxwell.Certificate.PointWitness\n", "open Maxwell.Spectral.PrimitiveYee\n",
    "def momentum : Translation := ![1,1,0]\n",
    "noncomputable def vector0 (e : Electric) : ℚ := (numerator0 e : ℚ) / 2^101\n",
    "noncomputable def image0 (e : Electric) : ℚ := (imageNumerator0 e : ℚ) / 2^130\n",
    "end Maxwell.Certificate.PointWitness\n"])
(OUT / "Data.lean").write_text("\n".join(parts))
