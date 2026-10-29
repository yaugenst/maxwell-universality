import Maxwell.Certificate.GenericPoint.ExactFrame
import Maxwell.Spectral.PrimitivePerturbation
import Maxwell.Spectral.InertiaGap

namespace Maxwell.Certificate.GenericPoint.Data
open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee
noncomputable section
variable (D : GenericPoint.Data)

def baseOperator : Space →ₗ[ℂ] Space :=
  (PrimitiveYee.fiber Concrete.baseMaterial (timeReversalMomentum D.k)).toEuclideanLin

theorem baseOperator_symmetric : D.baseOperator.IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (PrimitiveYee.fiber_hermitian _ _)

def BaseInertia : Prop :=
  (Finset.univ.filter fun i : Index => D.baseOperator_symmetric.eigenvalues rfl i < 1/256).card = 2002 ∧
  (Finset.univ.filter fun i : Index => D.baseOperator_symmetric.eigenvalues rfl i < 5/256).card = 2004

theorem eigenvalue_comparison (i : Index) :
    (operator_symmetric D.k).eigenvalues rfl i ≤ D.baseOperator_symmetric.eigenvalues rfl i ∧
    D.baseOperator_symmetric.eigenvalues rfl i ≤
      (operator_symmetric D.k).eigenvalues rfl i+1023/2^26 :=
  Concrete.primitive_eigenvalue_comparison (timeReversalMomentum D.k) i

/-- Rational center margins and the actual base inertia imply isolation for
any of the frozen-material point witnesses. -/
theorem complementGap_of_base_inertia (hcounts : D.BaseInertia)
    (hlo : ∀ j, D.gap ≤ D.center j-1/256)
    (hhi : ∀ j, D.gap ≤ 5/256-1023/2^26-D.center j) : D.ComplementGap := by
  have hins (j : Fin 2) : 1/256 < (operator_symmetric D.k).eigenvalues rfl (D.index j) ∧
      (operator_symmetric D.k).eigenvalues rfl (D.index j) < 5/256-1023/2^26 := by
    have hi := abs_le.mp (D.interval j)
    have hl := hlo j
    have hh := hhi j
    have hg := D.gap_gt
    constructor <;> linarith
  intro i hi j
  have hout : (operator_symmetric D.k).eigenvalues rfl i ≤ 1/256 ∨
      5/256-1023/2^26 ≤ (operator_symmetric D.k).eigenvalues rfl i := by
    apply outside_pair_of_threshold_counts (D.baseOperator_symmetric.eigenvalues rfl)
      ((operator_symmetric D.k).eigenvalues rfl) (1/256) (5/256) (1023/2^26)
      (by norm_num) D.eigenvalue_comparison (by rw [hcounts.1,hcounts.2])
      (D.index 0) (D.index 1) D.distinct (hins 0) (hins 1) i
    · intro h
      apply hi
      simp [cluster,h]
    · intro h
      apply hi
      simp [cluster,h]
  rcases hout with hl | hh
  · apply le_trans _ (neg_le_abs _)
    linarith [hlo j]
  · apply le_trans _ (le_abs_self _)
    linarith [hhi j]

end
end Maxwell.Certificate.GenericPoint.Data
