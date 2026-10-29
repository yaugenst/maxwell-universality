import Maxwell.Defect.FiniteStencil
import Maxwell.TargetLattice

/-! Norm-controlled finite coordinate compression of the exact rational
inverse polynomial. The coordinate injection is the genuine Hilbert-space
isometry, rather than an assumed matrix approximation interface. -/

namespace Maxwell.Defect.FiniteStencil

open Spectral Spectral.Lattice
open scoped Matrix

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def compressionOperator (edges : ι ↪ Edge) (T : Field →L[ℂ] Field) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  (Target.sequenceRestriction edges).comp
    (T.comp (Target.sequenceExtension edges).toContinuousLinearMap)

def rationalCompressionOperator (edges : ι ↪ Edge) (m : Edge → ℚ)
    (z s : ℚ) (N : ℕ) : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι :=
  Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
    ((compression (coordinateBasis edges) m z s N).map ((↑) : ℚ → ℂ))

theorem rationalCompressionOperator_binding (edges : ι ↪ Edge) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K) (z s : ℚ) (N : ℕ) :
    rationalCompressionOperator edges m z s N =
      compressionOperator edges (inversePolynomial (operator m K hK hm z) (s : ℂ) N) := by
  apply ContinuousLinearMap.ext
  intro x
  ext i
  change (∑ j, (compression (coordinateBasis edges) m z s N i j : ℂ) * x j) = _
  change _ = Target.sequenceRestriction edges
    (inversePolynomial (operator m K hK hm z) (s : ℂ) N
      (Target.sequenceExtension edges x)) i
  rw [Target.sequenceRestriction_apply]
  change _ = inversePolynomial (operator m K hK hm z) (s : ℂ) N
    (∑ j, lp.single 2 (edges j) (x j)) (edges i)
  rw [map_sum]
  simp only [lp.coeFn_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [coordinate_compression_entry m K hK hm]
  have hs : lp.single (E := fun _ : Edge => ℂ) 2 (edges j) (x j) =
      x j • lp.single 2 (edges j) (1 : ℂ) := by
    simpa using lp.single_smul (E := fun _ : Edge => ℂ) 2 (edges j) (x j) (1 : ℂ)
  rw [hs, map_smul]
  change _ = x j * _
  exact mul_comm _ _

theorem compressionOperator_sub (edges : ι ↪ Edge) (S T : Field →L[ℂ] Field) :
    compressionOperator edges (S - T) =
      compressionOperator edges S - compressionOperator edges T := by
  ext x i
  simp [compressionOperator]

theorem compressionOperator_norm_le (edges : ι ↪ Edge) (T : Field →L[ℂ] Field) :
    ‖compressionOperator edges T‖ ≤ ‖T‖ := by
  let Q := (Target.sequenceExtension edges).toContinuousLinearMap
  let R := Target.sequenceRestriction edges
  have hQ : ‖Q‖ ≤ 1 := Target.sequenceExtension_norm_le edges
  have hR : ‖R‖ ≤ 1 := Target.sequenceRestriction_norm_le edges
  change ‖R.comp (T.comp Q)‖ ≤ ‖T‖
  calc
    _ ≤ ‖R‖ * ‖T.comp Q‖ := ContinuousLinearMap.opNorm_comp_le R _
    _ ≤ 1 * (‖T‖ * 1) := mul_le_mul hR
      ((ContinuousLinearMap.opNorm_comp_le T Q).trans
        (mul_le_mul_of_nonneg_left hQ (norm_nonneg T))) (norm_nonneg _) (by norm_num)
    _ = ‖T‖ := by ring

/-- Compression cannot amplify the polynomial inverse error. -/
theorem rationalCompressionOperator_error (edges : ι ↪ Edge) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K) (z s : ℚ) (N : ℕ)
    (X : Field →L[ℂ] Field) :
    ‖compressionOperator edges X - rationalCompressionOperator edges m z s N‖ ≤
      ‖X - inversePolynomial (operator m K hK hm z) (s : ℂ) N‖ := by
  rw [rationalCompressionOperator_binding edges m K hK hm,
    ← compressionOperator_sub]
  exact compressionOperator_norm_le edges _

theorem inversePolynomial_real_cast (H : Field →L[ℂ] Field) (s : ℚ) (N : ℕ) :
    inversePolynomial H (s : ℝ) N = inversePolynomial H (s : ℂ) N := by
  have hs (T : Field →L[ℂ] Field) : (s : ℝ) • T = (s : ℂ) • T := by
    simpa using RCLike.real_smul_eq_coe_smul (K := ℂ) (s : ℝ) T
  simp only [inversePolynomial, hs]

end
end Maxwell.Defect.FiniteStencil
