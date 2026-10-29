# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Render exact archived finite data as kernel-checkable Lean certificates.

This generator is not trusted by the Lean theorems. It proposes literal data
and LDL factors; Lean checks every rational identity and positivity premise.
"""
from fractions import Fraction as Q
from pathlib import Path
import json
import argparse

ROOT = Path(__file__).resolve().parent
RESEARCH = ROOT.parent / "certificates/yee"
OUT = ROOT / "Maxwell" / "Certificate"
CHECK = False


def emit(path, content):
    if CHECK:
        if not path.exists() or path.read_text() != content:
            raise SystemExit(f"Generated Lean data differs: {path.relative_to(ROOT)}")
    else:
        path.write_text(content)


def rational(x):
    x = Q(x)
    return f"({x.numerator} / {x.denominator})" if x.denominator != 1 else str(x.numerator)


def vec(xs):
    return "![" + ", ".join(xs) + "]"


def mat(a):
    return "!![" + "; ".join(", ".join(rational(x) for x in row) for row in a) + "]"


def ldl(a):
    n = len(a)
    ll = [[Q(i == j) for j in range(n)] for i in range(n)]
    dd = [Q(0)] * n
    for j in range(n):
        dd[j] = a[j][j] - sum(ll[j][k]**2 * dd[k] for k in range(j))
        assert dd[j] > 0
        for i in range(j + 1, n):
            ll[i][j] = (a[i][j] - sum(ll[i][k] * ll[j][k] * dd[k] for k in range(j))) / dd[j]
    return ll, dd


def hessian():
    folder = OUT / "FrozenHessian"
    folder.mkdir(exist_ok=True)
    header = "noncomputable section\nnamespace Maxwell.Certificate.FrozenHessian\nopen Matrix\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n"
    data_parts = ["import Maxwell.Certificate.Matrix\n", header]
    imports = []
    for tag, stem in [("lppm", "inversion_feshbach"), ("lppp", "inversion_feshbach_lppp"), ("lpmp", "inversion_feshbach_lpmp"), ("lmpp", "inversion_feshbach_lmpp")]:
        source = RESEARCH / "results/defects" / (stem + "_curvature_acceptance.json")
        doc = json.loads(source.read_text())
        hh = [[Q(x) for x in row] for row in doc["rounded_hessian_block"]]
        data_parts.append(f"/-- Literal rounded Hessian from `{source.relative_to(RESEARCH)}`. -/\ndef {tag} : Matrix (Fin 6) (Fin 6) ℝ := {mat(hh)}\n")
        for suffix, a in [("lower", [[hh[i][j] - Q(i == j) * Q(2003, 50000) for j in range(6)] for i in range(6)]), ("upper", [[Q(i == j) * Q(49997,50000) - hh[i][j] for j in range(6)] for i in range(6)])]:
            ll, dd = ldl(a)
            name = tag + "_" + suffix
            module = tag.capitalize() + suffix.capitalize()
            imports.append(f"import Maxwell.Certificate.FrozenHessian.{module}")
            expr = f"{tag} - (2003/50000 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ)" if suffix == "lower" else f"(49997/50000 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ) - {tag}"
            parts = [
                "import Maxwell.Certificate.FrozenHessian.Data\n", header,
                f"private def {name}_L : Matrix (Fin 6) (Fin 6) ℝ := {mat(ll)}\n",
                f"private def {name}_D : Fin 6 → ℝ := {vec([rational(x) for x in dd])}\n",
                f"theorem {name}_psd : ({expr}).PosSemidef := by\n",
                f"  apply real_ldl_sound _ {name}_L {name}_D\n",
                f"  · ext i j\n    simp only [ldl_apply]\n    fin_cases i <;> fin_cases j <;> norm_num [{tag}, {name}_L, {name}_D, Fin.sum_univ_succ, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.vecHead, Matrix.vecTail]\n",
                f"  · intro i\n    fin_cases i <;> norm_num [{name}_D]\n",
                "end Maxwell.Certificate.FrozenHessian\n",
            ]
            emit(folder / (module + ".lean"), "\n".join(parts))
    data_parts.append("end Maxwell.Certificate.FrozenHessian\n")
    emit(folder / "Data.lean", "\n".join(data_parts))
    emit(OUT / "FrozenHessian.lean", "\n".join(imports) + "\n")


def material():
    doc = json.loads((RESEARCH / "results/defects/inversion_edge_material.json").read_text())
    data = doc["full_conventional_perturbation_numerators"]
    assert doc["perturbation_denominator"] == 2**21
    assert len(data) == 20 and all(len(p) == 20 and all(len(r) == 20 for r in p) for p in data)
    literal = vec([vec([vec([str(x) for x in row]) for row in plane]) for plane in data])
    pp = doc['primitive_perturbation_numerators']
    primitive_literal = vec([vec([vec([str(pp[x*100+y*10+z]) for z in range(10)]) for y in range(10)]) for x in range(20)])
    text = '''import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

namespace Maxwell.Certificate.Material
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Exact full-conventional integer table from inversion_edge_material.json.
Its entries are source data, not asserted spectral acceptance. -/
def numerator : Fin 20 → Fin 20 → Fin 20 → ℕ := LITERAL

theorem numerator_bounds : ∀ x y z, numerator x y z ≤ 2046 := by
  intro x
  fin_cases x <;> decide +kernel

/-- The independently stored primitive table, rendered from its own JSON field. -/
def primitiveNumerator : Fin 20 → Fin 10 → Fin 10 → ℕ := PRIMITIVE

theorem primitive_binding : ∀ x y z,
    primitiveNumerator x y z = numerator x (y.castLE (by decide)) (z.castLE (by decide)) := by
  intro x
  fin_cases x <;> decide +kernel

def halfShift (x : Fin 20) : Fin 20 := ⟨(x.val + 10) % 20, Nat.mod_lt _ (by decide)⟩
def invertCell (x : Fin 20) : Fin 20 := ⟨19 - x.val, by omega⟩

theorem numerator_inversion : ∀ x y z,
    numerator (invertCell x) (invertCell y) (invertCell z) = numerator x y z := by
  intro x
  fin_cases x <;> decide +kernel

theorem numerator_fcc_periodicity : ∀ x y z,
    numerator x (halfShift y) (halfShift z) = numerator x y z ∧
    numerator (halfShift x) y (halfShift z) = numerator x y z ∧
    numerator (halfShift x) (halfShift y) z = numerator x y z := by
  intro x
  fin_cases x <;> decide +kernel

/-- The same periodic diamond membership predicate used by ExactFiber.base_cell.
Coordinates and all periodic-distance comparisons are integers. -/
def doubledDistance (r c : Fin 3 → ℤ) (offset : ℤ) : ℤ :=
  ∑ j : Fin 3, (((2 * r j + 1 - c j - offset + 20) % 40 - 20)^2)

def fccCenters : List (Fin 3 → ℤ) :=
  [![0,0,0], ![0,20,20], ![20,0,20], ![20,20,0]]

def inDiamond (r : Fin 3 → Fin 20) : Prop :=
  ∃ c ∈ fccCenters, doubledDistance (fun j => (r j).val) c (-5) ≤ 100 ∨
    doubledDistance (fun j => (r j).val) c 5 ≤ 100

instance (r : Fin 3 → Fin 20) : Decidable (inDiamond r) := by
  unfold inDiamond
  infer_instance

def baseValue (r : Fin 3 → Fin 20) : ℚ := if inDiamond r then 12 else 1

def cellValue (r : Fin 3 → Fin 20) : ℚ :=
  baseValue r + (numerator (r 0) (r 1) (r 2) : ℚ) / 2097152

theorem cellValue_bounds (r : Fin 3 → Fin 20) : 1 ≤ cellValue r ∧ cellValue r < 13 := by
  have hn : (numerator (r 0) (r 1) (r 2) : ℚ) ≤ 2046 := by
    exact_mod_cast numerator_bounds (r 0) (r 1) (r 2)
  have hz : (0 : ℚ) ≤ numerator (r 0) (r 1) (r 2) := Nat.cast_nonneg _
  unfold cellValue baseValue
  split <;> constructor <;> linarith

end Maxwell.Certificate.Material
'''.replace('LITERAL', literal).replace('PRIMITIVE', primitive_literal)
    emit(OUT / "Material.lean", text)
    symmetry = 'import Maxwell.Certificate.Material\n\nnamespace Maxwell.Certificate.Material\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\ntheorem base_inversion : ∀ x y z,\n    baseValue ![invertCell x, invertCell y, invertCell z] = baseValue ![x,y,z] := by\n  intro x\n  fin_cases x <;> decide +kernel\n\ntheorem base_fcc_periodicity : ∀ x y z,\n    baseValue ![x, halfShift y, halfShift z] = baseValue ![x,y,z] ∧\n    baseValue ![halfShift x, y, halfShift z] = baseValue ![x,y,z] ∧\n    baseValue ![halfShift x, halfShift y, z] = baseValue ![x,y,z] := by\n  intro x\n  fin_cases x <;> decide +kernel\n\ntheorem cellValue_inversion (x y z : Fin 20) :\n    cellValue ![invertCell x, invertCell y, invertCell z] = cellValue ![x,y,z] := by\n  simp only [cellValue, base_inversion, Matrix.cons_val_zero, Matrix.cons_val_one,\n    Matrix.cons_val_two, numerator_inversion]\n\ntheorem cellValue_fcc_periodicity (x y z : Fin 20) :\n    cellValue ![x, halfShift y, halfShift z] = cellValue ![x,y,z] ∧\n    cellValue ![halfShift x, y, halfShift z] = cellValue ![x,y,z] ∧\n    cellValue ![halfShift x, halfShift y, z] = cellValue ![x,y,z] := by\n  have hb := base_fcc_periodicity x y z\n  have hn := numerator_fcc_periodicity x y z\n  simp only [cellValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]\n  rw [hb.1, hb.2.1, hb.2.2, hn.1, hn.2.1, hn.2.2]\n  exact ⟨rfl, rfl, rfl⟩\n\n\nend Maxwell.Certificate.Material\n'
    symmetry = symmetry.replace("intro x\n  fin_cases x <;> decide +kernel", "intro x y\n  fin_cases x <;> fin_cases y <;> decide +kernel")
    split_at = symmetry.index("theorem cellValue_inversion")
    base_symmetry = symmetry[:split_at] + "end Maxwell.Certificate.Material\n"
    emit(OUT / "MaterialBaseSymmetry.lean", base_symmetry)
    short = "import Maxwell.Certificate.MaterialBaseSymmetry\n\nnamespace Maxwell.Certificate.Material\n" + symmetry[split_at:]
    short = short.replace("simp only [cellValue, base_inversion, Matrix.cons_val_zero, Matrix.cons_val_one,\n    Matrix.cons_val_two, numerator_inversion]", "simp [cellValue, base_inversion, numerator_inversion]")
    start = short.index("  simp only [cellValue, Matrix.cons_val_zero", short.index("theorem cellValue_fcc_periodicity"))
    short = short[:start] + "  simp [cellValue, hb.1, hb.2.1, hb.2.2, hn.1, hn.2.1, hn.2.2]\n\nend Maxwell.Certificate.Material\n"
    emit(OUT / "MaterialSymmetry.lean", short)

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    CHECK = parser.parse_args().check
    hessian()
    material()
