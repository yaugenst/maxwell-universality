import Maxwell.Defect.RankOneConjugation
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Data.Finset.Lattice.Fold

/-! Exact finite spectral-block elimination for the rank-one perturbation. -/
namespace Maxwell.Defect

open Matrix

variable {ι : Type*}

/-- The spectral blocks selected by the possibly repeated eigenvalue `lam`. -/
noncomputable def spectralBlockPart (d : ι → ℝ) (lam : ℝ) (B : Matrix ι ι ℝ) :
    Matrix ι ι ℝ := by
  classical
  exact fun i j => if d i = lam ↔ d j = lam then B i j else 0

/-- The skew generator cancels precisely the cross-block first-order entries.
Within either block it is zero, so repeated eigenvalues never cause division
by their zero separation. -/
noncomputable def spectralBlockGenerator (d : ι → ℝ) (lam : ℝ) (B : Matrix ι ι ℝ) :
    Matrix ι ι ℝ := by
  classical
  exact fun i j => if d i = lam ↔ d j = lam then 0 else B i j / (d j - d i)

theorem spectralBlockGenerator_skew (d : ι → ℝ) (lam : ℝ)
    (B : Matrix ι ι ℝ) (hB : B.IsSymm) :
    (spectralBlockGenerator d lam B).transpose = -spectralBlockGenerator d lam B := by
  classical
  ext i j
  by_cases h : d i = lam ↔ d j = lam
  · simp only [transpose_apply, Matrix.neg_apply, spectralBlockGenerator,
      ite_eq_left h, ite_eq_left h.symm, neg_zero]
  · have h' : ¬ (d j = lam ↔ d i = lam) := fun hh => h hh.symm
    simp only [transpose_apply, Matrix.neg_apply, spectralBlockGenerator,
      ite_eq_right h, ite_eq_right h']
    rw [hB.apply i j, show d i - d j = -(d j - d i) by ring, div_neg]

/-- Exact cancellation of the first-order off-diagonal blocks. -/
theorem spectralBlockGenerator_cancel [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (lam : ℝ) (B : Matrix ι ι ℝ) :
    B + (diagonal d * spectralBlockGenerator d lam B -
      spectralBlockGenerator d lam B * diagonal d) = spectralBlockPart d lam B := by
  classical
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, diagonal_mul, mul_diagonal]
  by_cases h : d i = lam ↔ d j = lam
  · simp only [spectralBlockGenerator, spectralBlockPart, ite_eq_left h,
      mul_zero, zero_mul, sub_zero, add_zero]
  · have hd : d j - d i ≠ 0 := by
      intro he
      have hij := sub_eq_zero.mp he
      apply h
      rw [hij]
    simp only [spectralBlockGenerator, spectralBlockPart, ite_eq_right h]
    field_simp
    ring

/-- Projection of a coordinate vector onto a selected diagonal eigenspace. -/
noncomputable def spectralPart (d : ι → ℝ) (lam : ℝ) (w : ι → ℝ) : ι → ℝ := by
  classical
  exact fun i => if d i = lam then w i else 0

/-- The complementary coordinate vector. -/
noncomputable def spectralComplement (d : ι → ℝ) (lam : ℝ) (w : ι → ℝ) : ι → ℝ :=
  w - spectralPart d lam w

/-- A rank-one perturbation becomes the sum of its two within-block rank-one
parts after the exact commutator cancellation. -/
theorem spectralBlockPart_rankOne (d : ι → ℝ) (lam c : ℝ) (w : ι → ℝ) :
    spectralBlockPart d lam (-c • vecMulVec w w) =
      -c • (vecMulVec (spectralPart d lam w) (spectralPart d lam w) +
        vecMulVec (spectralComplement d lam w) (spectralComplement d lam w)) := by
  classical
  ext i j
  by_cases hi : d i = lam <;> by_cases hj : d j = lam <;>
    simp [spectralBlockPart, spectralPart, spectralComplement, hi, hj, vecMulVec]

/-- A finite diagonal spectrum has a strictly positive gap away from any
chosen eigenvalue. If its complement is empty the bound is vacuous. -/
theorem exists_spectral_complement_gap [Fintype ι] [Nonempty ι]
    (d : ι → ℝ) (lam : ℝ) :
    ∃ G : ℝ, 0 < G ∧ ∀ i, d i ≠ lam → G ≤ |d i - lam| := by
  classical
  let f : ι → ℝ := fun i => if d i = lam then 1 else |d i - lam|
  let G := Finset.univ.inf' Finset.univ_nonempty f
  have hg : 0 < G := by
    apply (Finset.lt_inf'_iff Finset.univ_nonempty).mpr
    intro i _
    by_cases hi : d i = lam
    · simp [f, hi]
    · simpa [f, hi] using abs_pos.mpr (sub_ne_zero.mpr hi)
  refine ⟨G, hg, ?_⟩
  intro i hi
  simpa [f, hi] using (Finset.inf'_le (f := f) (Finset.mem_univ i))

end Maxwell.Defect
