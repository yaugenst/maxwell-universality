import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Dedup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# Finite data interfaces and the scalar-cell averaging convention

This module formalizes finite rational input storage, fixed-point output
access, and the retained electric-edge material convention in Sections 1 and
4 of `source_proof/theorem_and_proof.md`. In particular, each retained edge
has four incident physical cells, including edges adjacent to the boundary.

It does not define the face-edge curl matrix, identify an assembled operator
with a Yee implementation, prove a spectral certificate, or implement the
paper's encoder. The coordinate readout below records a finite access
interface; it is not a proof of the paper's residual-transfer theorem.
-/

namespace Maxwell

/-- Canonical sparse storage: coordinates cannot repeat, and stored entries
are nonzero. Row and column indices are bounded by their types. -/
structure SparseRationalMatrix (rows cols : ℕ) where
  support : Finset (Fin rows × Fin cols)
  coefficient : {p // p ∈ support} → ℚ
  coefficient_ne_zero : ∀ p, coefficient p ≠ 0

namespace SparseRationalMatrix

def nnz {rows cols : ℕ} (M : SparseRationalMatrix rows cols) : ℕ :=
  M.support.card

/-- Exact rational densification, with zero precisely off the stored support. -/
def toMatrix {rows cols : ℕ} (M : SparseRationalMatrix rows cols) :
    Matrix (Fin rows) (Fin cols) ℚ :=
  fun i j => if h : (i, j) ∈ M.support then M.coefficient ⟨(i, j), h⟩ else 0

theorem coordinates_nodup {rows cols : ℕ} (M : SparseRationalMatrix rows cols) :
    M.support.toList.Nodup := M.support.nodup_toList

theorem toMatrix_at_stored {rows cols : ℕ} (M : SparseRationalMatrix rows cols)
    (i : Fin rows) (j : Fin cols) (h : (i, j) ∈ M.support) :
    M.toMatrix i j = M.coefficient ⟨(i, j), h⟩ := by
  simp [toMatrix, h]

theorem toMatrix_ne_zero_iff {rows cols : ℕ} (M : SparseRationalMatrix rows cols)
    (i : Fin rows) (j : Fin cols) :
    M.toMatrix i j ≠ 0 ↔ (i, j) ∈ M.support := by
  by_cases h : (i, j) ∈ M.support
  · simp [toMatrix, h, M.coefficient_ne_zero]
  · simp [toMatrix, h]

end SparseRationalMatrix

/-- A source has one exact rational value per matrix row. -/
abbrev RationalSource (rows : ℕ) := Fin rows → ℚ

/-- Number of magnitude bits, taking zero to need no magnitude bits. -/
def unsignedBitLength (n : ℕ) : ℕ := if n = 0 then 0 else Nat.log2 n + 1

/-- This convention includes one sign bit, even for zero. -/
def signedBitLength (n : ℤ) : ℕ := unsignedBitLength n.natAbs + 1

/-- A representation-size measure for a reduced rational numerator and
denominator. This is not a bit-operation cost model. -/
def rationalBitLength (r : ℚ) : ℕ :=
  signedBitLength r.num + unsignedBitLength r.den

/-- A fixed-point value whose denominator is exactly `2^precision` in its
representation, even if the represented rational can be reduced. -/
structure Dyadic (precision : ℕ) where
  numerator : ℤ
  deriving DecidableEq

namespace Dyadic

def value {precision : ℕ} (d : Dyadic precision) : ℚ :=
  (d.numerator : ℚ) / (2 : ℚ) ^ precision

def numeratorBits {precision : ℕ} (d : Dyadic precision) : ℕ :=
  signedBitLength d.numerator

theorem denominator_ne_zero (precision : ℕ) : (2 : ℚ) ^ precision ≠ 0 := by
  positivity

theorem denominator_bitLength (precision : ℕ) :
    unsignedBitLength (2 ^ precision) = precision + 1 := by
  simp [unsignedBitLength, Nat.log2_eq_log_two, Nat.log_pow]

theorem value_add {precision : ℕ} (a b : Dyadic precision) :
    (Dyadic.mk (a.numerator + b.numerator) : Dyadic precision).value =
      a.value + b.value := by
  simp [value, add_div]

end Dyadic

/-- Scalar cells of a finite rectangular box. Zero side lengths are allowed
as empty finite types; no nonexistent boundary cells are manufactured. -/
abbrev Cell (nx ny nz : ℕ) := Fin nx × Fin ny × Fin nz

/-- A transverse interior vertex at coordinate `v+1` has adjacent cell
indices `v` and `v+1`. -/
def interiorLower {n : ℕ} (v : Fin (n - 1)) : Fin n :=
  ⟨v.val, by have := v.isLt; omega⟩

def interiorUpper {n : ℕ} (v : Fin (n - 1)) : Fin n :=
  ⟨v.val + 1, by have := v.isLt; omega⟩

theorem interiorUpper_positive {n : ℕ} (v : Fin (n - 1)) :
    0 < (interiorUpper v).val := by simp [interiorUpper]

theorem interiorLower_ne_upper {n : ℕ} (v : Fin (n - 1)) :
    interiorLower v ≠ interiorUpper v := by
  intro h
  have hval := congrArg Fin.val h
  simp [interiorLower, interiorUpper] at hval

/-- Tangential boundary electric edges are omitted. For x-edges, for
example, the physical transverse coordinates are `j+1` and `k+1`, so
`1 ≤ j+1 < ny` and `1 ≤ k+1 < nz`. The other directions are cyclic. -/
abbrev RetainedEdge (nx ny nz : ℕ) :=
  (Fin nx × Fin (ny - 1) × Fin (nz - 1)) ⊕
    ((Fin (nx - 1) × Fin ny × Fin (nz - 1)) ⊕
      (Fin (nx - 1) × Fin (ny - 1) × Fin nz))

theorem retainedEdge_card (nx ny nz : ℕ) :
    Fintype.card (RetainedEdge nx ny nz) =
      nx * (ny - 1) * (nz - 1) + (nx - 1) * ny * (nz - 1) +
        (nx - 1) * (ny - 1) * nz := by
  simp [RetainedEdge, Fintype.card_sum, Fintype.card_prod]
  ring

/-- The finite base-case geometry really has one retained electric edge.
The associated curl value `Cᵀ C = 4` is outside this module's scope. -/
theorem retainedEdge_card_one_by_two_by_two :
    Fintype.card (RetainedEdge 1 2 2) = 1 := by
  norm_num [retainedEdge_card]

/-- All four cells are inside the physical box, including for edges next
to a PEC boundary. The four-cell order has no effect on averaging. -/
def incidentCells {nx ny nz : ℕ} (e : RetainedEdge nx ny nz) :
    Fin 4 → Cell nx ny nz :=
  match e with
  | .inl (i, j, k) =>
      ![(i, interiorLower j, interiorLower k),
        (i, interiorUpper j, interiorLower k),
        (i, interiorLower j, interiorUpper k),
        (i, interiorUpper j, interiorUpper k)]
  | .inr (.inl (i, j, k)) =>
      ![(interiorLower i, j, interiorLower k),
        (interiorUpper i, j, interiorLower k),
        (interiorLower i, j, interiorUpper k),
        (interiorUpper i, j, interiorUpper k)]
  | .inr (.inr (i, j, k)) =>
      ![(interiorLower i, interiorLower j, k),
        (interiorUpper i, interiorLower j, k),
        (interiorLower i, interiorUpper j, k),
        (interiorUpper i, interiorUpper j, k)]

theorem incidentCells_injective {nx ny nz : ℕ} (e : RetainedEdge nx ny nz) :
    Function.Injective (incidentCells e) := by
  rcases e with (⟨i, j, k⟩ | (⟨i, j, k⟩ | ⟨i, j, k⟩)) <;>
    intro a b h <;> fin_cases a <;> fin_cases b <;>
    simp [incidentCells, Fin.ext_iff, interiorLower, interiorUpper] at h ⊢

def edgeAverage {nx ny nz : ℕ} (material : Cell nx ny nz → ℚ)
    (e : RetainedEdge nx ny nz) : ℚ :=
  (material (incidentCells e 0) + material (incidentCells e 1) +
    material (incidentCells e 2) + material (incidentCells e 3)) / 4

/-- The paper's real scalar interval, restricted to the rational output
representation. No tensor or complex material is encoded here. -/
structure ScalarMaterial (nx ny nz : ℕ) where
  value : Cell nx ny nz → ℚ
  bounds : ∀ c, 1 ≤ value c ∧ value c ≤ 25

theorem edgeAverage_bounds {nx ny nz : ℕ} (material : ScalarMaterial nx ny nz)
    (e : RetainedEdge nx ny nz) :
    1 ≤ edgeAverage material.value e ∧ edgeAverage material.value e ≤ 25 := by
  have h0 := material.bounds (incidentCells e 0)
  have h1 := material.bounds (incidentCells e 1)
  have h2 := material.bounds (incidentCells e 2)
  have h3 := material.bounds (incidentCells e 3)
  dsimp [edgeAverage]
  constructor <;> linarith

theorem edgeAverage_constant {nx ny nz : ℕ} (a : ℚ)
    (e : RetainedEdge nx ny nz) : edgeAverage (fun _ => a) e = a := by
  dsimp [edgeAverage]
  ring

theorem edgeAverage_uniform_shift {nx ny nz : ℕ}
    (material : Cell nx ny nz → ℚ) (a : ℚ) (e : RetainedEdge nx ny nz) :
    edgeAverage (fun c => material c + a) e = edgeAverage material e + a := by
  dsimp [edgeAverage]
  ring

/-- The mass-diagonal shift used in the paper, with `t = 1/64`. This
identity alone makes no claim about the unformalized curl matrix. -/
theorem mass_diagonal_uniform_shift {nx ny nz : ℕ}
    (material : Cell nx ny nz → ℚ) (u : ℚ) (e : RetainedEdge nx ny nz) :
    -(1 / 64 : ℚ) * edgeAverage (fun c => material c + 64 * u) e =
      -(1 / 64 : ℚ) * edgeAverage material e - u := by
  rw [edgeAverage_uniform_shift]
  ring

/-- A decoder reads only a fixed finite coordinate list at a fixed binary
precision and rescales those samples by an explicit rational scalar. -/
structure FiniteDecoderPlan (physicalDim decodedDim : ℕ) where
  coordinate : Fin decodedDim → Fin physicalDim
  precision : ℕ
  scale : ℚ

namespace FiniteDecoderPlan

abbrev Samples {physicalDim decodedDim : ℕ}
    (plan : FiniteDecoderPlan physicalDim decodedDim) :=
  Fin decodedDim → Dyadic plan.precision

def decode {physicalDim decodedDim : ℕ}
    (plan : FiniteDecoderPlan physicalDim decodedDim) (samples : plan.Samples) :
    Fin decodedDim → ℚ := fun i => plan.scale * (samples i).value

/-- The accuracy requirement on finite prefixes of an arbitrary real
physical vector. Existence or acquisition cost is not assumed proved. -/
def Accurate {physicalDim decodedDim : ℕ}
    (plan : FiniteDecoderPlan physicalDim decodedDim) (samples : plan.Samples)
    (y : Fin physicalDim → ℝ) : Prop :=
  ∀ i, |((samples i).value : ℝ) - y (plan.coordinate i)| ≤
    1 / (2 : ℝ) ^ plan.precision

theorem decode_error {physicalDim decodedDim : ℕ}
    (plan : FiniteDecoderPlan physicalDim decodedDim) (samples : plan.Samples)
    (y : Fin physicalDim → ℝ) (h : plan.Accurate samples y) (i : Fin decodedDim) :
    |((plan.decode samples i : ℚ) : ℝ) -
        (plan.scale : ℝ) * y (plan.coordinate i)| ≤
      |(plan.scale : ℝ)| / (2 : ℝ) ^ plan.precision := by
  have hi := h i
  have hscaled := mul_le_mul_of_nonneg_left hi (abs_nonneg (plan.scale : ℝ))
  simpa [decode, Rat.cast_mul, ← mul_sub, abs_mul, div_eq_mul_inv] using hscaled

end FiniteDecoderPlan

end Maxwell
