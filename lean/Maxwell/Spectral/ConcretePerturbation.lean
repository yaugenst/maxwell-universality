import Maxwell.Spectral.Concrete
import Maxwell.Spectral.Perturbation
import Mathlib.Analysis.InnerProductSpace.Positive

namespace Maxwell.Spectral

noncomputable section

open scoped ComplexOrder

/-- Exact matrix Loewner bounds imply ordered spectral comparison in the
Euclidean Hilbert norm, including multiplicities. -/
theorem matrix_eigenvalues_of_increment_order {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (δ : ℝ) (hlo : (A - B).PosSemidef)
    (hhi : ((δ : ℂ) • (1 : Matrix n n ℂ) - (A - B)).PosSemidef)
    (i : Fin (Module.finrank ℂ (EuclideanSpace ℂ n))) :
    let sA := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
    let sB := Matrix.isSymmetric_toEuclideanLin_iff.mpr hB
    sB.eigenvalues rfl i ≤ sA.eigenvalues rfl i ∧
      sA.eigenvalues rfl i ≤ sB.eigenvalues rfl i + δ := by
  let sA := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  let sB := Matrix.isSymmetric_toEuclideanLin_iff.mpr hB
  have hl (x : EuclideanSpace ℂ n) :
      Complex.re (inner ℂ x (B.toEuclideanLin x)) ≤
        Complex.re (inner ℂ x (A.toEuclideanLin x)) := by
    have h := (Matrix.isPositive_toEuclideanLin_iff.mpr hlo).re_inner_nonneg_right x
    simp only [map_sub, LinearMap.sub_apply, inner_sub_right, map_sub,
      RCLike.re_to_complex] at h
    linarith
  have hh (x : EuclideanSpace ℂ n) :
      Complex.re (inner ℂ x (A.toEuclideanLin x)) ≤
        Complex.re (inner ℂ x (B.toEuclideanLin x)) + δ * ‖x‖ ^ 2 := by
    have h := (Matrix.isPositive_toEuclideanLin_iff.mpr hhi).re_inner_nonneg_right x
    simp only [map_sub, map_smul, Matrix.toLpLin_one, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, inner_sub_right, inner_smul_right,
      map_sub, RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] at h
    have hn : Complex.re (inner ℂ x x) = ‖x‖ ^ 2 :=
      (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
    rw [hn] at h
    linarith
  exact ⟨eigenvalues_mono_of_quadratic_le sB sA hl i,
    eigenvalues_le_of_quadratic_le_add sA sB δ hh i⟩

namespace Concrete

/-- The actual frozen nonconstant material perturbation decreases every
ordered Bloch eigenvalue by at most the proved material bound. -/
theorem fiber_eigenvalue_comparison (k : PeriodicYee.Momentum)
    (i : Fin (Module.finrank ℂ (EuclideanSpace ℂ PeriodicYee.Electric20))) :
    let sBase := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (PeriodicYee.fiber_hermitian baseMaterial k)
    let sFrozen := Matrix.isSymmetric_toEuclideanLin_iff.mpr (fiber_hermitian k)
    sFrozen.eigenvalues rfl i ≤ sBase.eigenvalues rfl i ∧
      sBase.eigenvalues rfl i ≤ sFrozen.eigenvalues rfl i + 1023 / 2 ^ 26 := by
  exact matrix_eigenvalues_of_increment_order
    (PeriodicYee.fiber baseMaterial k) (fiber k)
    (PeriodicYee.fiber_hermitian baseMaterial k) (fiber_hermitian k)
    (1023 / 2 ^ 26) (operator_increment_order k).1 (operator_increment_order k).2 i

end Concrete
end
end Maxwell.Spectral
