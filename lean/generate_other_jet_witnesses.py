#!/usr/bin/env -S uv run --script
# /// script
# requires-python = "==3.12.*"
# dependencies = ["numpy==2.3.5"]
# ///
"""Propose actual other-L jet witnesses and their separate Lean kernel checks.

All vectors come from the canonical Feshbach archive for that point. The
already-generated point tables are compared coordinate by coordinate before
any new proposal is written. This script never launches a Lean worker.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
import json
import math
from pathlib import Path
import re

import numpy as np

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT.parent / "certificates/yee/results/defects"
BASE = "Maxwell.Certificate.OtherJetWitness"
POINTS = {"Lppp": ((1, 1, 1), -1), "Lpmp": ((1, 0, 1), 1), "Lmpp": ((-1, 0, 0), 1)}
PAIRS = [(i, j, a) for i in range(3) for j in range(i, 3) for a in range(2)]


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def vec(xs):
    return "![" + ", ".join(map(str, xs)) + "]"


def rat(q):
    q = F(q)
    return str(q.numerator) if q.denominator == 1 else f"({q.numerator} / {q.denominator})"


def mat(xs):
    return "!![" + "; ".join(", ".join(rat(q) for q in row) for row in xs) + "]"


def action(rows, v):
    return [sum(c * v[e] for e, c in row.items()) for row in rows]


def ldl(a):
    n = len(a)
    lower, diagonal = [[F(i == j) for j in range(n)] for i in range(n)], []
    for i in range(n):
        diagonal.append(a[i][i] - sum(lower[i][k] ** 2 * diagonal[k] for k in range(i)))
        assert diagonal[-1] > 0, f"nonpositive proposed LDL pivot {i}"
        for j in range(i + 1, n):
            lower[j][i] = (a[j][i] - sum(lower[j][k] * lower[i][k] * diagonal[k]
                                       for k in range(i))) / diagonal[i]
    assert all(a[i][j] == sum(lower[i][k] * diagonal[k] * lower[j][k] for k in range(n))
               for i in range(n) for j in range(n))
    return lower, diagonal


def read_table(path, name):
    """Read literal coordinates only; do not evaluate Lean or trust a filename."""
    rows = {}
    pattern = re.compile(rf"^def {re.escape(name)}_(\d+)_(\d+) .* := (.*)$")
    for line in path.read_text().splitlines():
        match = pattern.match(line)
        if match:
            key = tuple(map(int, match.group(1, 2)))
            assert key not in rows
            rows[key] = [int(x) for x in re.findall(r"-?\d+", match.group(3))]
            assert len(rows[key]) == 100
    assert set(rows) == {(d, x) for d in range(3) for x in range(20)}
    return [v for d in range(3) for x in range(20) for v in rows[d, x]]


@dataclass
class Witness:
    stem: str
    momentum: tuple[int, int, int]
    parity: int
    model: object
    u: list[list[int]]
    y: list[list[int]]
    ay: list[list[int]]
    bu: list[list[int]]
    center: int
    frozen: list[list[F]]
    inputs: dict[str, str]

    @property
    def point(self):
        return f"OtherPointWitness.{self.stem}"

    @property
    def k(self):
        return vec(self.momentum)


def load(stem):
    momentum, parity = POINTS[stem]
    spec = importlib.util.spec_from_file_location("other_jet_exact_arithmetic", SOURCE / "exact_edge_arithmetic.py")
    arithmetic = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(arithmetic)
    material_file = SOURCE / "inversion_edge_material.json"
    archive = SOURCE / f"inversion_feshbach_{stem.lower()}.npz"
    acceptance = SOURCE / f"inversion_feshbach_{stem.lower()}_curvature_acceptance.json"
    point_files = [ROOT / f"Maxwell/Certificate/OtherPointWitness/{stem}/Numerator{a}.lean" for a in range(2)]
    center_file = ROOT / f"Maxwell/Certificate/OtherPointWitness/{stem}/Residual0.lean"
    inputs = [Path(__file__), material_file, archive, acceptance, SOURCE / "exact_edge_arithmetic.py",
              SOURCE / "verify_inversion_feshbach_curvature.py", center_file, *point_files,
              ROOT / "Maxwell/Certificate/CurvatureWitness/Bindings.lean"]
    hashes = {str(p): digest(p) for p in inputs}
    material = json.loads(material_file.read_text())
    assert material["period"] == 20 and material["perturbation_denominator"] == 2**21
    perturb = material["full_conventional_perturbation_numerators"]
    model = arithmetic.ExactFiber(momentum, perturb)
    with np.load(archive, allow_pickle=False) as data:
        assert tuple(data["k_twice"]) == momentum
        assert int(data["pair_parity"]) == parity
        assert data["perturbation_numerators"].tolist() == perturb
        vectors = data["inversion_perturbed_eigenvectors"]
        solutions = data["inversion_perturbed_complement_solutions"]
        assert vectors.shape == (6000, 2) and np.isrealobj(vectors) and np.isfinite(vectors).all()
        assert solutions.shape == (6000, 6) and np.isfinite(solutions).all()
        u = [model.project(arithmetic.quantize(vectors[:, a]), parity) for a in range(2)]
        y = [model.project(arithmetic.quantize(np.imag(solutions[:, j]) / (math.pi / 20)), -parity)
             for j in range(6)]
    assert all(read_table(p, f"numerator{a}") == u[a] for a, p in enumerate(point_files))
    assert all(model.invert(v) == [parity * n for n in v] for v in u)
    assert all(model.invert(v) == [-parity * n for n in v] for v in y)
    center = model.eigen_residual(u[0])["lambda_numerator"]
    declared_center = re.search(r"def lambdaNumerator0 : ℤ := (-?\d+)", center_file.read_text())
    assert declared_center and int(declared_center.group(1)) == center
    frozen = [[F(q) for q in row] for row in json.loads(acceptance.read_text())["rounded_hessian_block"]]
    ay = [model.apply_mass_scaled(v) for v in y]
    bu = [action(model.B[i], u[a]) for i in range(3) for a in range(2)]
    return Witness(stem, momentum, parity, model, u, y, ay, bu, center, frozen, hashes)


class Generator:
    def __init__(self, witness):
        self.w = witness
        self.root = ROOT / "Maxwell/Certificate/OtherJetWitness" / witness.stem
        self.modules = []

    def ns(self, group):
        return f"{BASE}.{self.w.stem}.{group}"

    def short(self, group):
        return f"OtherJetWitness.{self.w.stem}.{group}"

    def emit(self, group, name, imports, body, kind, **metadata):
        folder = self.root / group
        folder.mkdir(parents=True, exist_ok=True)
        source = "-- Generated by generate_other_jet_witnesses.py; requires separate kernel acceptance.\n"
        imports = ["Maxwell.Certificate.PointWitness.NormDefs", *imports]
        source += "\n".join("import " + imp for imp in dict.fromkeys(imports)) + "\n\n"
        source += f"namespace {self.ns(group)}\n"
        source += "open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee\n"
        source += "open Maxwell.Certificate.PointWitness Maxwell.Certificate.PrimitiveBinding\n"
        source += "noncomputable section\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n"
        source += body + f"\nend\nend {self.ns(group)}\n"
        path = folder / (name + ".lean")
        path.write_text(source)
        self.modules.append({"module": self.ns(group) + "." + name, "source": str(path.relative_to(ROOT)),
                             "source_sha256": digest(path), "kind": kind, **metadata})

    def table(self, group, module, name, values):
        assert len(values) == 6000
        body = []
        for d in range(3):
            for x in range(20):
                rows = [vec(values[d * 2000 + x * 100 + yy * 10:d * 2000 + x * 100 + (yy + 1) * 10])
                        for yy in range(10)]
                body.append(f"def {name}_{d}_{x} : Fin 10 → Fin 10 → ℤ := {vec(rows)}")
        rows = [vec(f"{name}_{d}_{x}" for x in range(20)) for d in range(3)]
        body.append(f"def {name} (e : Electric) : ℤ := ({vec(rows)}) e.1 e.2.1 e.2.2.1 e.2.2.2")
        self.emit(group, module, ["Maxwell.Certificate.DerivativeInteger", "Maxwell.Certificate.PointWitness.NormDefs"],
                  "\n".join(body), "table", coordinates=6000)

    def coordinate_action(self, group, prefix, theorem, imports, expression, result):
        chunks = []
        for d in range(3):
            for x in range(20):
                module = f"{prefix}D{d}X{x:02}"
                chunks.append(self.ns(group) + "." + module)
                e = f"({d}, ({x}, y, z))"
                body = ("open Maxwell.Certificate.DerivativeBinding\n\n"
                        f"theorem {theorem}_{d}_{x:02} (y z : Fin 10) :\n"
                        f"    {expression.format(e=e)} = {result.format(e=e)} := by\n"
                        "  fin_cases y <;> fin_cases z <;> decide +kernel\n")
                self.emit(group, module, imports, body, "action_chunk", coordinates=100)
        body = ("open Maxwell.Certificate.DerivativeBinding\n\n"
                f"theorem {theorem} (e : Electric) :\n"
                f"    {expression.format(e='e')} = {result.format(e='e')} := by\n"
                "  rcases e with ⟨d, x, y, z⟩\n  fin_cases d <;> fin_cases x\n")
        body += "\n".join(f"  · exact {theorem}_{d}_{x:02} y z" for d in range(3) for x in range(20))
        self.emit(group, prefix + "Complete", chunks, body, "action_complete")

    def dot(self, group, name, theorem, imports, left, right, v, w, split=False, prelude="",
            footer="", zero_directions=()):
        blocks = [[sum(v[e] * w[e] for e in range(d * 2000 + x * 100, d * 2000 + (x + 1) * 100))
                   for x in range(20)] for d in range(3)]
        total = sum(map(sum, blocks))
        body = prelude + f"def {theorem}Blocks : Fin 3 → Fin 20 → ℤ := {vec(map(vec, blocks))}\n\n"
        imports = [*imports, "Maxwell.Certificate.PointWitness.DotDefs"]
        if split:
            self.emit(group, name + "Data", imports, body, "dot_data")
            for d in range(3):
                if d in zero_directions:
                    assert all(z == 0 for z in blocks[d])
                    proof = (f"  have hz (p : Cell) : {right} ({d}, p) = 0 := by\n"
                             "    apply CurvatureWitness.DFormI_zero_direction\n    decide\n"
                             "  simp only [blockDotI, hz, mul_zero, Finset.sum_const_zero]\n"
                             "  fin_cases x <;> rfl\n")
                else:
                    proof = "  fin_cases x <;> decide +kernel\n"
                chunk = prelude + (f"theorem {theorem}BlocksD{d} (x : Fin 20) :\n"
                    f"    blockDotI {left} {right} {d} x = {theorem}Blocks {d} x := by\n"
                    + proof)
                self.emit(group, name + f"D{d}", [self.ns(group) + "." + name + "Data"], chunk,
                          "dot_chunk", summands=2000)
            imports = [self.ns(group) + "." + name + f"D{d}" for d in range(3)]
            body = prelude
            proof = "  fin_cases d\n" + "\n".join(f"  · exact {theorem}BlocksD{d} x" for d in range(3)) + "\n"
        else:
            proof = "  fin_cases d <;> fin_cases x <;> decide +kernel\n"
        body += (f"theorem {theorem}Blocks_checked (d : Fin 3) (x : Fin 20) :\n"
                 f"    blockDotI {left} {right} d x = {theorem}Blocks d x := by\n" + proof +
                 f"\ntheorem {theorem}_checked : dotI {left} {right} = {total} := by\n"
                 f"  unfold dotI\n  simp_rw [{theorem}Blocks_checked]\n  decide +kernel\n")
        body += footer.replace("TOTAL", str(total))
        self.emit(group, name, imports, body, "dot", summands=6000)
        return total

    def corrector_and_bpoint(self):
        w = self.w
        for j in range(6):
            self.table("Corrector", f"Numerator{j}", f"numerator{j}", w.y[j])
            self.table("Corrector", f"Imagenumerator{j}", f"imageNumerator{j}", w.ay[j])
            self.coordinate_action("Corrector", f"Action{j}", f"numerator{j}_action",
                [self.ns("Corrector") + f".Numerator{j}", self.ns("Corrector") + f".Imagenumerator{j}"],
                f"fiberActionI {w.k} numerator{j} {{e}}", f"imageNumerator{j} {{e}}")
            self.coordinate_action("Corrector", f"Parity{j}", f"numerator{j}_parity",
                [self.ns("Corrector") + f".Numerator{j}", "Maxwell.Certificate.InversionInteger"],
                f"electricInversionActionI {w.k} numerator{j} {{e}}", f"({-w.parity} : ℤ) * numerator{j} {{e}}")
            self.table("BPoint", f"Rhs{j}", f"rhs{j}", w.bu[j])
            self.coordinate_action("BPoint", f"Action{j}", f"rhs{j}_action",
                [self.ns("BPoint") + f".Rhs{j}", f"Maxwell.Certificate.{w.point}.Numerator{j % 2}"],
                f"BActionI {w.k} {j // 2} {w.point}.numerator{j % 2} {{e}}", f"rhs{j} {{e}}")
        self.corrector_residuals()
        self.corrector_gram()

    def corrector_residuals(self):
        w = self.w
        totals = []
        for j in range(6):
            values = [aa * 2**51 - w.center * yy - bb * 2**80 for aa, yy, bb in zip(w.ay[j], w.y[j], w.bu[j])]
            imports = [self.ns("Corrector") + f".Numerator{j}", self.ns("Corrector") + f".Imagenumerator{j}",
                       self.ns("BPoint") + f".Rhs{j}"]
            definition = (f"def residual{j} (e : Electric) : ℤ :=\n"
                          f"  imageNumerator{j} e * 2^51 - {w.center} * numerator{j} e - "
                          f"{self.short('BPoint')}.rhs{j} e * 2^80\n\n")
            total = self.dot("Corrector", f"Residual{j}", f"residual{j}", imports,
                             f"residual{j}", f"residual{j}", values, values, prelude=definition)
            totals.append(total)
            body = ("open Maxwell.Certificate.DerivativeBinding\n\n"
                    f"theorem residual{j}_binding :\n"
                    "    Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)\n"
                    f"      (PrimitiveYee.fiber Concrete.material (timeReversalMomentum {w.k}))\n"
                    f"      (integerVector numerator{j} (2^101)) -\n"
                    f"      (({w.center} : ℂ) / 2^80) • integerVector numerator{j} (2^101) -\n"
                    f"      BOperator {w.k} {j // 2} (integerVector {w.point}.numerator{j % 2} (2^101)) =\n"
                    f"      integerVector residual{j} (2^181) := by\n"
                    f"  exact integerVector_corrector_residual {w.k} {j // 2}\n"
                    f"    {w.point}.numerator{j % 2} numerator{j} imageNumerator{j} {self.short('BPoint')}.rhs{j}\n"
                    f"    {w.center} (funext numerator{j}_action) (funext {self.short('BPoint')}.rhs{j}_action)\n")
            self.emit("Corrector", f"Computed{j}", [self.ns("Corrector") + f".Action{j}Complete",
                      self.ns("Corrector") + f".Residual{j}", self.ns("BPoint") + f".Action{j}Complete",
                      "Maxwell.Certificate.DerivativeVector"], body, "residual_binding")
        assert sum(totals) <= 2**292
        body = f"def residuals : Fin 6 → Electric → ℤ := {vec(f'residual{j}' for j in range(6))}\n\n"
        body += ("theorem residual_frobenius_sq :\n"
                 "    ∑ j : Fin 6, ‖integerVector (residuals j) (2^181)‖^2 ≤ (1 / 2^35 : ℝ)^2 := by\n"
                 "  have hn (v : Electric → ℤ) : squareNormI v = dotI v v := rfl\n"
                 "  simp only [integerVector_norm_sq, hn]\n"
                 "  norm_num [Fin.sum_univ_succ, residuals,\n    " +
                 ", ".join(f"residual{j}_checked" for j in range(6)) + "]\n")
        self.emit("Corrector", "ResidualBound", [self.ns("Corrector") + f".Residual{j}" for j in range(6)] +
                  ["Maxwell.Certificate.PointWitness.Vector"], body, "residual_bound")

    def corrector_gram(self):
        w = self.w
        checks = []
        for p in range(6):
            for q in range(p, 6):
                name = f"Dot{p}{q}"
                self.dot("Corrector", name, f"dot{p}{q}",
                         [self.ns("Corrector") + f".Numerator{j}" for j in {p, q}],
                         f"numerator{p}", f"numerator{q}", w.y[p], w.y[q])
                checks.append(self.ns("Corrector") + "." + name)
        gram = [[F(sum(a*b for a, b in zip(v, z)), 2**202) for z in w.y] for v in w.y]
        body = ""
        for p in range(6):
            for q in range(p + 1, 6):
                body += (f"theorem dot{q}{p}_checked : dotI numerator{q} numerator{p} = {int(gram[p][q] * 2**202)} := by\n"
                         f"  have h : dotI numerator{q} numerator{p} = dotI numerator{p} numerator{q} := by\n"
                         "    simp only [dotI_eq_sum, mul_comm]\n"
                         f"  rw [h, dot{p}{q}_checked]\n\n")
        body += f"def numerators : Fin 6 → Electric → ℤ := {vec(f'numerator{j}' for j in range(6))}\n"
        body += f"def gram : Matrix (Fin 6) (Fin 6) ℝ := {mat(gram)}\n\n"
        body += ("theorem gram_binding (i j : Fin 6) :\n"
                 "    inner ℂ (integerVector (numerators i) (2^101))\n"
                 "      (integerVector (numerators j) (2^101)) = (gram i j : ℂ) := by\n"
                 "  rw [integerVector_inner]\n"
                 "  fin_cases i <;> fin_cases j <;>\n"
                 "    norm_num [numerators, gram, " +
                 ", ".join(f"dot{p}{q}_checked" for p in range(6) for q in range(6)) + "]\n")
        self.emit("Corrector", "Gram", checks + ["Maxwell.Certificate.PointWitness.Inner", "Maxwell.Certificate.Matrix"],
                  body, "gram_binding")
        lower, diagonal = ldl([[F(361 * (i == j)) - gram[i][j] for j in range(6)] for i in range(6)])
        body = f"open Matrix\n\nprivate def lower : Matrix (Fin 6) (Fin 6) ℝ := {mat(lower)}\n"
        body += f"private def pivots : Fin 6 → ℝ := {vec(map(rat, diagonal))}\n\n"
        body += ("theorem gram_bound_psd : ((361 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ) - gram).PosSemidef := by\n"
                 "  apply real_ldl_sound _ lower pivots\n"
                 "  · ext i j\n    simp only [ldl_apply]\n"
                 "    fin_cases i <;> fin_cases j <;> norm_num [gram, lower, pivots,\n"
                 "      Fin.sum_univ_succ, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.vecHead, Matrix.vecTail]\n"
                 "  · intro i\n    fin_cases i <;> norm_num [pivots]\n")
        self.emit("Corrector", "GramBound", [self.ns("Corrector") + ".Gram"], body, "gram_psd")
        alpha = F(314159265358979323847, 10**20)**2 / 400
        lower, diagonal = ldl([[F(2909, 1000)**2 * (i == j) - alpha * gram[i][j]
                               for j in range(6)] for i in range(6)])
        body = f"open Matrix\n\nprivate def lower : Matrix (Fin 6) (Fin 6) ℝ := {mat(lower)}\n"
        body += f"private def pivots : Fin 6 → ℝ := {vec(map(rat, diagonal))}\n\n"
        body += ("theorem physical_gram_bound_psd :\n"
            "    (((2909/1000 : ℝ)^2) • (1 : Matrix (Fin 6) (Fin 6) ℝ) -\n"
            "      CurvatureWitness.alphaUpper • gram).PosSemidef := by\n"
            "  apply real_ldl_sound _ lower pivots\n"
            "  · ext i j\n    simp only [ldl_apply]\n"
            "    fin_cases i <;> fin_cases j <;> norm_num [gram, lower, pivots, CurvatureWitness.alphaUpper,\n"
            "      Fin.sum_univ_succ, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.vecHead, Matrix.vecTail]\n"
            "  · intro i\n    fin_cases i <;> norm_num [pivots]\n")
        self.emit("Corrector", "PhysicalGramBound", [self.ns("Corrector") + ".Gram",
            "Maxwell.Certificate.CurvatureWitness.Rounding"], body, "physical_corrector_gram_psd")

    def curvature(self):
        w = self.w
        ku = [[action(w.model.K[i], w.u[a]) for a in range(2)] for i in range(3)]
        lu = [[action(w.model.L[i], w.u[a]) for a in range(2)] for i in range(3)]
        cu = [action(w.model.C, w.u[a]) for a in range(2)]
        ddot, bydot, modules = {}, {}, []
        for i in range(3):
            for j in range(i, 3):
                for a in range(2):
                    for b in range(a, 2):
                        suffix = f"{i}{j}{a}{b}"
                        form = [ku[i][a][e] * ku[j][b][e] + ku[j][a][e] * ku[i][b][e]
                                - (lu[i][a][e] * cu[b][e] + cu[a][e] * lu[i][b][e] if i == j else 0)
                                for e in range(6000)]
                        du = action(w.model.D[i][j], w.u[b])
                        assert sum(form) == sum(v * z for v, z in zip(w.u[a], du))
                        footer = (f"\ntheorem dotD{suffix}_checked :\n"
                            f"    dotI {w.point}.numerator{a} (DActionI {w.k} {i} {j} {w.point}.numerator{b}) = TOTAL := by\n"
                            f"  rw [dotI_D_form, dotD{suffix}Form_checked]\n")
                        if a != b:
                            footer += (f"\ntheorem dotD{i}{j}{b}{a}_checked :\n"
                                f"    dotI {w.point}.numerator{b} (DActionI {w.k} {i} {j} {w.point}.numerator{a}) = TOTAL := by\n"
                                f"  rw [dotI_D_symmetric, dotD{suffix}_checked]\n")
                        if i != j:
                            for aa, bb in sorted({(a, b), (b, a)}):
                                footer += (f"\ntheorem dotD{j}{i}{aa}{bb}_checked :\n"
                                    f"    dotI {w.point}.numerator{aa} (DActionI {w.k} {j} {i} {w.point}.numerator{bb}) = TOTAL := by\n"
                                    f"  have h : DActionI {w.k} {j} {i} {w.point}.numerator{bb} =\n"
                                    f"      DActionI {w.k} {i} {j} {w.point}.numerator{bb} :=\n"
                                    f"    funext (DActionI_comm {w.k} {j} {i} {w.point}.numerator{bb})\n"
                                    f"  rw [h, dotD{i}{j}{aa}{bb}_checked]\n")
                        imports = [f"Maxwell.Certificate.{w.point}.Numerator{v}" for v in sorted({a, b})]
                        imports += ["Maxwell.Certificate.CurvatureWitness.ZeroDirection"]
                        total = self.dot("Curvature", f"DotD{suffix}", f"dotD{suffix}Form", imports,
                            "(fun _ => 1)", f"(DFormI {w.k} {i} {j} {w.point}.numerator{a} {w.point}.numerator{b})",
                            [1] * 6000, form, split=True,
                            prelude="open Maxwell.Certificate.DerivativeBinding Maxwell.Certificate.CurvatureWitness\n\n",
                            footer=footer, zero_directions={i, j})
                        for ii, jj in {(i, j), (j, i)}:
                            for aa, bb in {(a, b), (b, a)}:
                                ddot[ii, jj, aa, bb] = total
                        modules.append(self.ns("Curvature") + f".DotD{suffix}")
        for p in range(6):
            for q in range(6):
                bydot[p, q] = self.dot("Curvature", f"DotBY{p}{q}", f"dotBY{p}{q}",
                    [self.ns("BPoint") + f".Rhs{p}", self.ns("Corrector") + f".Numerator{q}"],
                    f"{self.short('BPoint')}.rhs{p}", f"{self.short('Corrector')}.numerator{q}", w.bu[p], w.y[q])
                modules.append(self.ns("Curvature") + f".DotBY{p}{q}")
        raw = [[F(ddot[p // 2, q // 2, p % 2, q % 2] - bydot[p, q]
                  - bydot[2 * (q // 2) + p % 2, 2 * (p // 2) + q % 2], 2**202)
                for q in range(6)] for p in range(6)]
        self.emit("Curvature", "Data", ["Maxwell.Certificate.FrozenHessian.Data", "Mathlib.Analysis.Real.Pi.Bounds"],
            f"def raw : Matrix (Fin 6) (Fin 6) ℚ := {mat(raw)}\n\n"
            "def hessianApprox : Matrix (Fin 6) (Fin 6) ℝ :=\n"
            "  fun p q => Real.pi ^ 2 / 400 * (raw p q : ℝ)\n", "curvature_data")
        # The selected binding proof is algebraic and contains no selected numeric
        # premises. Parameterize only its three vector namespaces and momentum.
        template = (ROOT / "Maxwell/Certificate/CurvatureWitness/Bindings.lean").read_text()
        body = template[template.index("def pointNumerators"):template.rindex("\nend\nend ")]
        body = body.replace("PointWitness.numerator", w.point + ".numerator")
        body = body.replace("CorrectorWitness.", self.short("Corrector") + ".")
        body = body.replace("BPointWitness.", self.short("BPoint") + ".")
        body = body.replace("![1,1,0]", w.k)
        assert "![1,1,0]" not in body and "CorrectorWitness." not in body
        self.emit("Curvature", "Bindings", modules + [self.ns("Curvature") + ".Data",
            "Maxwell.Certificate.DerivativeAction", "Maxwell.Certificate.PointWitness.Inner"] +
            [self.ns("BPoint") + f".Action{j}Complete" for j in range(6)],
            "open Maxwell.Certificate.DerivativeBinding\n\n" + body, "curvature_binding")
        alpha_lo = F(314159265358979323846, 10**20)**2 / 400
        alpha_hi = F(314159265358979323847, 10**20)**2 / 400
        assert all(abs(alpha * raw[i][j] - w.frozen[i][j]) <= F(1, 10**11)
                   for alpha in (alpha_lo, alpha_hi) for i in range(6) for j in range(6))
        frozen = f"FrozenHessian.{w.stem.lower()}"
        body = ("theorem endpoint_rounding (p q : Fin 6) :\n"
            f"    |CurvatureWitness.alphaLower * (raw p q : ℝ) - {frozen} p q| ≤ 1 / 10^11 ∧\n"
            f"    |CurvatureWitness.alphaUpper * (raw p q : ℝ) - {frozen} p q| ≤ 1 / 10^11 := by\n"
            "  fin_cases p <;> fin_cases q <;>\n"
            f"    norm_num [CurvatureWitness.alphaLower, CurvatureWitness.alphaUpper, raw, {frozen}]\n\n"
            "theorem entry_rounding_error (p q : Fin 6) :\n"
            f"    |hessianApprox p q - {frozen} p q| ≤ 1 / 10^11 :=\n"
            "  CurvatureWitness.between_endpoints_close _ _ _ _ _ _ CurvatureWitness.alpha_enclosed\n"
            "    (endpoint_rounding p q).1 (endpoint_rounding p q).2\n")
        self.emit("Curvature", "Rounding", [self.ns("Curvature") + ".Data",
                  "Maxwell.Certificate.CurvatureWitness.Rounding"], body, "curvature_rounding")

    def quadratic(self):
        w = self.w
        by = {(i, j, a): action(w.model.B[i], w.y[2*j+a])
              for i in range(3) for j in range(3) for a in range(2)}
        values = {}
        for i, j, a in PAIRS:
            suffix = f"{i}{j}{a}"
            du = action(w.model.D[i][j], w.u[a])
            values[i, j, a] = values[j, i, a] = [x+y+z for x, y, z in zip(du, by[i, j, a], by[j, i, a])]
            self.table("Quadratic", "Numerator" + suffix, "numerator" + suffix, values[i, j, a])
            imports = [self.ns("Quadratic") + ".Numerator" + suffix,
                       f"Maxwell.Certificate.{w.point}.Numerator{a}"]
            imports += [self.ns("Corrector") + f".Numerator{v}" for v in sorted({2*j+a, 2*i+a})]
            self.coordinate_action("Quadratic", "Action" + suffix, "numerator" + suffix + "_action", imports,
                f"DActionI {w.k} {i} {j} {w.point}.numerator{a} {{e}} +\n"
                f"      BActionI {w.k} {i} {self.short('Corrector')}.numerator{2*j+a} {{e}} +\n"
                f"      BActionI {w.k} {j} {self.short('Corrector')}.numerator{2*i+a} {{e}}", f"numerator{suffix} {{e}}")
        tensor = vec(vec(vec(f"numerator{min(i,j)}{max(i,j)}{a}" for a in range(2))
                         for j in range(3)) for i in range(3))
        self.emit("Quadratic", "Data", [self.ns("Quadratic") + f".Numerator{i}{j}{a}" for i, j, a in PAIRS],
            "def numerators : Fin 3 → Fin 3 → Fin 2 → Electric → ℤ := " + tensor + "\n", "quadratic_data")
        body = ("open Maxwell.Certificate.DerivativeBinding Maxwell.Certificate.CurvatureWitness\n\n"
            "theorem numerators_action (i j : Fin 3) (a : Fin 2) (e : Electric) :\n"
            f"    DActionI {w.k} i j ({self.short('Curvature')}.pointNumerators a) e +\n"
            f"      BActionI {w.k} i ({self.short('Curvature')}.correctorNumerators j a) e +\n"
            f"      BActionI {w.k} j ({self.short('Curvature')}.correctorNumerators i a) e = numerators i j a e := by\n"
            "  fin_cases i <;> fin_cases j <;> fin_cases a\n")
        for i in range(3):
            for j in range(3):
                for a in range(2):
                    if i <= j:
                        body += f"  · exact numerator{i}{j}{a}_action e\n"
                    else:
                        body += (f"  · change DActionI {w.k} {i} {j} {w.point}.numerator{a} e +\n"
                            f"      BActionI {w.k} {i} {self.short('Corrector')}.numerator{2*j+a} e +\n"
                            f"      BActionI {w.k} {j} {self.short('Corrector')}.numerator{2*i+a} e = numerator{j}{i}{a} e\n"
                            f"    rw [DActionI_comm {w.k} {i} {j}]\n"
                            f"    simpa only [add_right_comm] using numerator{j}{i}{a}_action e\n")
        self.emit("Quadratic", "ActionComplete", [self.ns("Quadratic") + f".Action{i}{j}{a}Complete" for i, j, a in PAIRS] +
            [self.ns("Quadratic") + ".Data", self.ns("Curvature") + ".Bindings"], body, "quadratic_binding")
        self.quadratic_gram(values)

    def quadratic_gram(self, values):
        def key(i, p):
            j, a = divmod(p, 2)
            return min(i, j), max(i, j), a
        def suffix(k):
            return "".join(map(str, k))
        pairs = sorted({tuple(sorted((key(i, p), key(i, q))))
                        for i in range(3) for p in range(6) for q in range(p, 6)})
        totals, checks, modules = {}, [], []
        for left, right in pairs:
            x, y = suffix(left), suffix(right)
            footer = ""
            checks.append(f"dot{x}_{y}_checked")
            if x != y:
                footer = (f"\ntheorem dot{y}_{x}_checked : dotI numerator{y} numerator{x} = TOTAL := by\n"
                          f"  have h : dotI numerator{y} numerator{x} = dotI numerator{x} numerator{y} := by\n"
                          "    simp only [dotI_eq_sum, mul_comm]\n"
                          f"  rw [h, dot{x}_{y}_checked]\n")
                checks.append(f"dot{y}_{x}_checked")
            total = self.dot("Quadratic", f"Dot{x}_{y}", f"dot{x}_{y}",
                [self.ns("Quadratic") + ".Numerator" + z for z in sorted({x, y})],
                "numerator" + x, "numerator" + y, values[left], values[right], footer=footer)
            totals[left, right] = totals[right, left] = total
            modules.append(self.ns("Quadratic") + f".Dot{x}_{y}")
        raw = [[F(sum(totals[key(i, p), key(i, q)] for i in range(3)), 2**204)
                for q in range(6)] for p in range(6)]
        alpha = F(314159265358979323847, 10**20)**2 / 400
        upper = [[alpha**2 * z for z in row] for row in raw]
        self.emit("Quadratic", "GramData", ["Maxwell.Certificate.CurvatureWitness.Rounding"],
            f"def rawGram : Matrix (Fin 6) (Fin 6) ℝ := {mat(raw)}\n\n"
            "def gramUpper : Matrix (Fin 6) (Fin 6) ℝ := CurvatureWitness.alphaUpper^2 • rawGram\n", "quadratic_gram_data")
        body = ("def direction (p : Fin 6) : Fin 3 := ⟨p.val / 2, by omega⟩\n"
            "def column (p : Fin 6) : Fin 2 := ⟨p.val % 2, by omega⟩\n"
            "def rawColumn (i : Fin 3) (p : Fin 6) := integerVector (numerators i (direction p) (column p)) (2^102)\n\n"
            "theorem rawGram_binding (p q : Fin 6) :\n"
            "    (∑ i : Fin 3, inner ℂ (rawColumn i p) (rawColumn i q)) = (rawGram p q : ℂ) := by\n"
            "  simp only [rawColumn, integerVector_inner]\n"
            "  fin_cases p <;> fin_cases q <;>\n"
            "    norm_num [direction, column, numerators, rawGram, Fin.sum_univ_three,\n      " + ", ".join(checks) + "]\n")
        self.emit("Quadratic", "Gram", modules + [self.ns("Quadratic") + ".Data", self.ns("Quadratic") + ".GramData",
                  "Maxwell.Certificate.PointWitness.Inner"], body, "quadratic_gram_binding")
        frozen = "FrozenHessian." + self.w.stem.lower()
        for name, theorem, target, expression in [
            ("GramNorm", "gram_norm_psd", [[4*F(i == j)-upper[i][j] for j in range(6)] for i in range(6)],
             "((4 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ) - gramUpper)"),
            ("GramRelative", "gram_relative_psd", [[F(9, 5)*self.w.frozen[i][j]-upper[i][j]-F(i == j, 10000)
                                                   for j in range(6)] for i in range(6)],
             f"((9/5 : ℝ) • {frozen} - gramUpper - (1/10000 : ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℝ))")]:
            lower, diagonal = ldl(target)
            body = f"open Matrix\n\nprivate def lower : Matrix (Fin 6) (Fin 6) ℝ := {mat(lower)}\n"
            body += f"private def pivots : Fin 6 → ℝ := {vec(map(rat, diagonal))}\n\n"
            body += (f"theorem {theorem} : {expression}.PosSemidef := by\n"
                "  apply real_ldl_sound _ lower pivots\n"
                "  · ext i j\n    simp only [ldl_apply]\n"
                "    fin_cases i <;> fin_cases j <;>\n"
                f"      norm_num [lower, pivots, rawGram, gramUpper, CurvatureWitness.alphaUpper, {frozen},\n"
                "        Fin.sum_univ_succ, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.vecHead, Matrix.vecTail]\n"
                "  · intro i\n    fin_cases i <;> norm_num [pivots]\n")
            self.emit("Quadratic", name, [self.ns("Quadratic") + ".GramData"], body, "quadratic_gram_psd")

    def verified(self):
        w = self.w
        c, h, t = (self.short(g) for g in ("Corrector", "Curvature", "Quadratic"))
        body = f"""open Maxwell.Spectral.YeeTaylor
open Maxwell.Spectral.PeriodicYee (Momentum)
open Maxwell.Certificate.DerivativeBinding Maxwell.Certificate.CurvatureTransfer

abbrev columns (j : Fin 6) := integerVector ({c}.numerators j) (2^101)
abbrev residualColumns (j : Fin 6) := integerVector ({c}.residuals j) (2^181)
abbrev savedY (q : Momentum) := OtherJetWitness.savedCorrector columns q
abbrev physicalW := QuadraticWitness.physicalWOf {t}.numerators

theorem savedY_norm (q : Momentum) : ‖savedY q‖ ≤ (2909/1000 : ℝ)*radius q :=
  OtherJetWitness.savedCorrector_norm_le columns {c}.gram {c}.gram_binding
    {c}.physical_gram_bound_psd q

theorem columns_parity (j : Fin 6) :
    YeeInversion.electricIsometry {w.k} (columns j) = ({-w.parity} : ℂ) • columns j := by
  have hp := integerVector_parity {w.k} ({c}.numerators j) (2^101) ({-w.parity}) (by
    intro e
    fin_cases j <;> simp only [{c}.numerators] <;>
      first | exact {c}.numerator0_parity e | exact {c}.numerator1_parity e |
        exact {c}.numerator2_parity e | exact {c}.numerator3_parity e |
        exact {c}.numerator4_parity e | exact {c}.numerator5_parity e)
  simpa only [columns, {'Int.cast_neg, ' if -w.parity < 0 else ''}Int.cast_one] using hp

variable (D : GenericPoint.Data) (hk : D.k = {w.k})
variable (hc : D.center 0 = ({w.center} : ℝ) / 2^80)
variable (hu : ∀ a, integerVector ({h}.pointNumerators a) (2^101) = D.vector a)

include hk hu in
theorem point_parity (a : Fin 2) : D.inversion (D.vector a) = ({w.parity} : ℂ) • D.vector a := by
  rw [← hu a]
  change YeeInversion.electricIsometry D.k _ = _
  rw [hk]
  have hp := integerVector_parity {w.k} ({h}.pointNumerators a) (2^101) ({w.parity}) (by
    intro e
    fin_cases a <;> simp only [{h}.pointNumerators] <;>
      first | exact {w.point}.numerator0_parity e | exact {w.point}.numerator1_parity e)
  simpa only [{'Int.cast_neg, ' if w.parity < 0 else ''}Int.cast_one] using hp

include hk in
theorem savedY_parity (q : Momentum) : HasParity D.inversion (-({w.parity} : ℂ)) (savedY q) := by
  apply OtherJetWitness.savedCorrector_parity
  intro j
  simpa [GenericPoint.Data.inversion, hk] using columns_parity j

include hk hc hu in
theorem residual_columns_binding (j : Fin 6) :
    D.shiftedOperator (D.center 0) (columns j) - OtherJetWitness.derivativeColumns D j =
      residualColumns j := by
  simp only [GenericPoint.Data.shiftedOperator, GenericPoint.Data.continuousOperator,
    OtherJetWitness.derivativeColumns, hk, hc, _root_.sub_apply, _root_.smul_apply,
    ContinuousLinearMap.id_apply, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat]
  simp_rw [← hu]
  fin_cases j <;> simp only [columns, residualColumns, {c}.numerators, {c}.residuals,
    {h}.pointNumerators]
  · exact {c}.residual0_binding
  · exact {c}.residual1_binding
  · exact {c}.residual2_binding
  · exact {c}.residual3_binding
  · exact {c}.residual4_binding
  · exact {c}.residual5_binding

include hk hc hu in
theorem savedY_residual (q : Momentum) :
    ‖D.savedCorrectorResidual q (savedY q)‖ ≤ (1/10^11 : ℝ)*radius q :=
  OtherJetWitness.savedCorrector_residual_bound D columns residualColumns
    (residual_columns_binding D hk hc hu) {c}.residual_frobenius_sq q

include hk hu in
theorem effective_binding (q : Momentum) :
    D.savedEffectiveCoefficient q (savedY q) = directionalHalf {h}.hessianApprox q := by
  apply OtherJetWitness.savedEffectiveCoefficient_binding_integer D {h}.pointNumerators
    {c}.numerators hu {h}.hessianApprox
  intro i j a b
  have hy (k : Fin 3) (e : Fin 2) :
      {c}.numerators (OtherJetWitness.slot k e) = {h}.correctorNumerators k e := by
    fin_cases k <;> fin_cases e <;> rfl
  simp only [hk, hy]
  simpa only [OtherJetWitness.slot, {h}.index] using {h}.hessianApprox_binding_index i j a b

include hk hu in
theorem quadratic_binding (q : Momentum) :
    D.savedQuadraticResidual q (savedY q) = QuadraticTransfer.contraction physicalW q := by
  apply OtherJetWitness.savedQuadraticResidual_eq_of_actions D {h}.pointNumerators
    {c}.numerators hu {t}.numerators
  intro i j a e
  have hy (k : Fin 3) (b : Fin 2) :
      {c}.numerators (OtherJetWitness.slot k b) = {h}.correctorNumerators k b := by
    fin_cases k <;> fin_cases b <;> rfl
  simpa only [hk, hy] using {t}.numerators_action i j a e

theorem physical_gram_bound (x : EuclideanSpace ℂ (Fin 6)) :
    (∑ i, ‖physicalW i x‖^2) ≤ Complex.re (inner ℂ x (realMatrixOperator {t}.gramUpper x)) :=
  QuadraticWitness.physicalWOf_gram_bound {t}.numerators {t}.rawGram {t}.rawGram_binding x

include hk hc hu in
theorem corrector_close (hgap : D.ComplementGap)
    (hρ : D.residualRadius ≤ OtherPointBudgets.residualRadius)
    (hε : D.gramRadius ≤ OtherPointBudgets.frameEpsilon)
    (hg : OtherPointBudgets.spectralGap ≤ D.gap) (q : Momentum) :
    ‖D.corrector hgap q - savedY q‖ ≤ OtherPointBudgets.correctorError * radius q :=
  D.corrector_saved_close hgap {w.parity} (by norm_num) (point_parity D hk hu)
    hρ hε hg q (savedY q) (savedY_parity D hk q) (savedY_norm q) (savedY_residual D hk hc hu q)

include hk hc hu in
theorem corrector_norm (hgap : D.ComplementGap)
    (hρ : D.residualRadius ≤ OtherPointBudgets.residualRadius)
    (hε : D.gramRadius ≤ OtherPointBudgets.frameEpsilon)
    (hg : OtherPointBudgets.spectralGap ≤ D.gap) (q : Momentum) :
    ‖D.corrector hgap q‖ ≤ 3*radius q :=
  D.corrector_norm_le hgap q (savedY q) (savedY_norm q) (corrector_close D hk hc hu hgap hρ hε hg q)

include hk hc hu in
theorem finiteJetBounds (hgap : D.ComplementGap)
    (hρ : D.residualRadius ≤ OtherPointBudgets.residualRadius)
    (hε : D.gramRadius ≤ OtherPointBudgets.frameEpsilon)
    (hg : OtherPointBudgets.spectralGap ≤ D.gap) (q : Momentum)
    (hwidth : D.width ≤ 7/256-D.energy) :
    FiniteJetBounds (D.taylorCoefficient q) (D.exactIsometry hgap).toContinuousLinearMap
      (D.corrector hgap q) (radius q) D.width D.energy := by
  have he := corrector_close D hk hc hu hgap hρ hε hg q
  have hy := corrector_norm D hk hc hu hgap hρ hε hg q
  exact D.finiteJetBounds_of_finite hgap {w.parity} (by norm_num) (point_parity D hk hu) q hwidth
    (savedY q) (D.savedQuadraticResidual q (savedY q)) physicalW
    FrozenHessian.{w.stem.lower()} {h}.hessianApprox {t}.gramUpper
    FrozenHessian.{w.stem.lower()}_lower_psd FrozenHessian.{w.stem.lower()}_upper_psd
    {h}.entry_rounding_error (effective_binding D hk hu q) (quadratic_binding D hk hu q)
    physical_gram_bound {t}.gram_norm_psd {t}.gram_relative_psd
    (by simpa only [show (10 : ℝ)^6 = 1000000 by norm_num] using
      D.effectiveCoefficient_saved_error_other hgap hε q (savedY q) hy he)
    (by simpa only [show (10 : ℝ)^6 = 1000000 by norm_num] using
      D.quadraticResidual_saved_error_other hgap hε q (savedY q) he)

include hk hc hu in
theorem local_band_gap (hgap : D.ComplementGap)
    (hρ : D.residualRadius ≤ OtherPointBudgets.residualRadius)
    (hε : D.gramRadius ≤ OtherPointBudgets.frameEpsilon)
    (hg : OtherPointBudgets.spectralGap ≤ D.gap) (q : Momentum)
    (hr0 : 0 < radius q) (hr : radius q ≤ 1/20)
    (hw : D.width ≤ 1/2^20) (hEl : 239/25000 ≤ D.energy) (hEu : D.energy ≤ 957/100000)
    (hinertia : (Finset.univ.filter fun i =>
      0 < (YeeTaylorRemainder.centeredOperator_symmetric D.k q).eigenvalues rfl i ∧
      (YeeTaylorRemainder.centeredOperator_symmetric D.k q).eigenvalues rfl i < 7/256).card ≤ 2) :
    ∀ i : GenericPoint.Index,
      0 < (YeeTaylorRemainder.centeredOperator_symmetric D.k q).eigenvalues rfl i →
      (YeeTaylorRemainder.centeredOperator_symmetric D.k q).eigenvalues rfl i < 7/256 →
      radius q^2/600 < (YeeTaylorRemainder.centeredOperator_symmetric D.k q).eigenvalues rfl i-D.energy := by
  have he := corrector_close D hk hc hu hgap hρ hε hg q
  have hy := corrector_norm D hk hc hu hgap hρ hε hg q
  exact D.local_band_gap_of_finite hgap {w.parity} (by norm_num) (point_parity D hk hu) q hr0 hr hw hEl hEu hy
    (savedY q) (D.savedQuadraticResidual q (savedY q)) physicalW
    FrozenHessian.{w.stem.lower()} {h}.hessianApprox {t}.gramUpper
    FrozenHessian.{w.stem.lower()}_lower_psd FrozenHessian.{w.stem.lower()}_upper_psd
    {h}.entry_rounding_error (effective_binding D hk hu q) (quadratic_binding D hk hu q)
    physical_gram_bound {t}.gram_norm_psd {t}.gram_relative_psd
    (by simpa only [show (10 : ℝ)^6 = 1000000 by norm_num] using
      D.effectiveCoefficient_saved_error_other hgap hε q (savedY q) hy he)
    (by simpa only [show (10 : ℝ)^6 = 1000000 by norm_num] using
      D.quadraticResidual_saved_error_other hgap hε q (savedY q) he) hinertia
"""
        imports = ["Maxwell.Certificate.OtherJetWitness.Assembly", "Maxwell.Certificate.QuadraticWitness.GramTransfer",
            "Maxwell.Certificate.GenericPoint.GramTransfer", f"Maxwell.Certificate.FrozenHessian.{w.stem}Lower",
            f"Maxwell.Certificate.FrozenHessian.{w.stem}Upper", self.ns("Curvature") + ".Rounding",
            self.ns("Corrector") + ".PhysicalGramBound", self.ns("Corrector") + ".ResidualBound",
            self.ns("Curvature") + ".Bindings", self.ns("Quadratic") + ".ActionComplete",
            self.ns("Quadratic") + ".Gram", self.ns("Quadratic") + ".GramNorm", self.ns("Quadratic") + ".GramRelative"]
        imports += [self.ns("Corrector") + f".Computed{j}" for j in range(6)]
        imports += [self.ns("Corrector") + f".Parity{j}Complete" for j in range(6)]
        imports += [f"Maxwell.Certificate.{w.point}.Parity{a}Complete" for a in range(2)]
        self.emit("Verified", "Complete", imports, body, "verified_binding")

    def finish(self):
        audit_targets = [
            ("Corrector.ResidualBound", "Corrector.residual_frobenius_sq"),
            ("Corrector.PhysicalGramBound", "Corrector.physical_gram_bound_psd"),
            ("Curvature.Bindings", "Curvature.hessianApprox_binding"),
            ("Curvature.Rounding", "Curvature.entry_rounding_error"),
            ("Quadratic.ActionComplete", "Quadratic.numerators_action"),
            ("Quadratic.Gram", "Quadratic.rawGram_binding"),
            ("Quadratic.GramNorm", "Quadratic.gram_norm_psd"),
            ("Quadratic.GramRelative", "Quadratic.gram_relative_psd"),
            ("Verified.Complete", "Verified.effective_binding"),
            ("Verified.Complete", "Verified.quadratic_binding"),
            ("Verified.Complete", "Verified.corrector_close"),
            ("Verified.Complete", "Verified.finiteJetBounds"),
            ("Verified.Complete", "Verified.local_band_gap"),
        ]
        self.emit("Audit", "Complete", [f"{BASE}.{self.w.stem}.{m}" for m, _ in audit_targets],
            "\n".join(f"#print axioms {BASE}.{self.w.stem}.{t}" for _, t in audit_targets), "audit")
        for path, expected in self.w.inputs.items():
            assert digest(Path(path)) == expected, f"input changed during generation: {path}"
        evidence = ROOT / "evidence/other_jet_witnesses" / self.w.stem
        evidence.mkdir(parents=True, exist_ok=True)
        by_name = {m["module"]: m for m in self.modules}
        assert len(by_name) == len(self.modules)
        for m in self.modules:
            m["imports"] = re.findall(r"^import (\S+)", (ROOT / m["source"]).read_text(), re.MULTILINE)
            assert not any(token in (ROOT / m["source"]).read_text() for token in ("sorry", "native_decide"))
        ordered, visited, active = [], set(), set()
        def visit(name):
            if name in visited:
                return
            assert name not in active, f"cyclic dependency: {name}"
            active.add(name)
            for dep in by_name[name]["imports"]:
                if dep in by_name:
                    visit(dep)
            active.remove(name)
            visited.add(name)
            ordered.append(by_name[name])
        for name in by_name:
            visit(name)
        result = {"status": "PROPOSED_NOT_KERNEL_ACCEPTED", "point": self.w.stem,
                  "momentum": self.w.momentum, "point_parity": self.w.parity,
                  "corrector_parity": -self.w.parity, "denominator_power": 101,
                  "canonical_center_numerator": self.w.center, "input_sha256": self.w.inputs,
                  "modules": ordered, "audit_targets": [f"{BASE}.{self.w.stem}.{t}" for _, t in audit_targets]}
        (evidence / "manifest.json").write_text(json.dumps(result, indent=2) + "\n")
        print(f"{self.w.stem}: proposed {len(self.modules)} modules; no Lean checks launched.", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--point", choices=POINTS, action="append")
    args = parser.parse_args()
    for stem in args.point or POINTS:
        generator = Generator(load(stem))
        generator.corrector_and_bpoint()
        generator.curvature()
        generator.quadratic()
        generator.verified()
        generator.finish()


if __name__ == "__main__":
    main()
