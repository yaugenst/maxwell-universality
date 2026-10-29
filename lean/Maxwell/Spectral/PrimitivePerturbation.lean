import Maxwell.Spectral.ConcretePerturbation
import Maxwell.Spectral.PrimitiveYee

namespace Maxwell.Spectral.Concrete

noncomputable section
open PeriodicYee PrimitiveYee
open scoped ComplexOrder

theorem primitive_averaged_increment_bounds (e : PrimitiveYee.Electric) :
    0 ≤ PrimitiveYee.edgeAverage material e - PrimitiveYee.edgeAverage baseMaterial e ∧
      PrimitiveYee.edgeAverage material e - PrimitiveYee.edgeAverage baseMaterial e ≤ 1023 / 2 ^ 20 := by
  rw [PrimitiveYee.edgeAverage_binding, PrimitiveYee.edgeAverage_binding]
  exact averaged_increment_bounds _

theorem primitive_increment_diagonal (k : Momentum) :
    PrimitiveYee.fiber baseMaterial k - PrimitiveYee.fiber material k =
      Matrix.diagonal (fun e : PrimitiveYee.Electric =>
        (((PrimitiveYee.edgeAverage material e - PrimitiveYee.edgeAverage baseMaterial e) / 64 : ℝ) : ℂ)) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [PrimitiveYee.fiber, PrimitiveYee.mass]
    ring
  · simp [PrimitiveYee.fiber, PrimitiveYee.mass, h]

theorem primitive_increment_order (k : Momentum) :
    (PrimitiveYee.fiber baseMaterial k - PrimitiveYee.fiber material k).PosSemidef ∧
      (((1023 / 2 ^ 26 : ℝ) : ℂ) • (1 : Matrix PrimitiveYee.Electric PrimitiveYee.Electric ℂ) -
        (PrimitiveYee.fiber baseMaterial k - PrimitiveYee.fiber material k)).PosSemidef := by
  rw [primitive_increment_diagonal]
  constructor
  · apply Matrix.PosSemidef.diagonal
    intro e
    apply RCLike.ofReal_nonneg.mpr
    exact div_nonneg (primitive_averaged_increment_bounds e).1 (by norm_num)
  · have heq :
        ((1023 / 2 ^ 26 : ℝ) : ℂ) • (1 : Matrix PrimitiveYee.Electric PrimitiveYee.Electric ℂ) -
          Matrix.diagonal (fun e : PrimitiveYee.Electric =>
            (((PrimitiveYee.edgeAverage material e - PrimitiveYee.edgeAverage baseMaterial e) / 64 : ℝ) : ℂ)) =
        Matrix.diagonal (fun e : PrimitiveYee.Electric =>
          (((1023 / 2 ^ 26 -
            (PrimitiveYee.edgeAverage material e - PrimitiveYee.edgeAverage baseMaterial e) / 64 : ℝ)) : ℂ)) := by
      ext i j
      by_cases h : i = j
      · subst j
        simp
      · simp [h]
    rw [heq]
    apply Matrix.PosSemidef.diagonal
    intro e
    apply RCLike.ofReal_nonneg.mpr
    change (0 : ℝ) ≤ 1023 / 2 ^ 26 -
      (PrimitiveYee.edgeAverage material e - PrimitiveYee.edgeAverage baseMaterial e) / 64
    have h := (primitive_averaged_increment_bounds e).2
    linarith

theorem primitive_eigenvalue_comparison (k : Momentum)
    (i : Fin (Module.finrank ℂ (EuclideanSpace ℂ PrimitiveYee.Electric))) :
    let sBase := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (PrimitiveYee.fiber_hermitian baseMaterial k)
    let sFrozen := Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (PrimitiveYee.fiber_hermitian material k)
    sFrozen.eigenvalues rfl i ≤ sBase.eigenvalues rfl i ∧
      sBase.eigenvalues rfl i ≤ sFrozen.eigenvalues rfl i + 1023 / 2 ^ 26 := by
  exact matrix_eigenvalues_of_increment_order
    (PrimitiveYee.fiber baseMaterial k) (PrimitiveYee.fiber material k)
    (PrimitiveYee.fiber_hermitian baseMaterial k) (PrimitiveYee.fiber_hermitian material k)
    (1023 / 2 ^ 26) (primitive_increment_order k).1 (primitive_increment_order k).2 i

end
end Maxwell.Spectral.Concrete
