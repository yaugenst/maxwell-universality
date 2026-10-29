import Maxwell.Certificate.PointWitness.ExactFrame
import Maxwell.Spectral.PrimitivePerturbation
import Maxwell.Spectral.InertiaGap

/-!
# From the base-fiber threshold counts to the actual point-cluster gap

The only inputs of the final theorem are the two base-material negative
eigenvalue counts.  The perturbation comparison, the two retained eigenvalue
locations, and the numerical gap margins are proved for the actual stored
material and point witnesses.  This module does not assert the two counts.
-/

namespace Maxwell.Certificate.PointWitness

open Maxwell.Spectral Maxwell.Spectral.PrimitiveYee

noncomputable section

def basePointFiber : Matrix Electric Electric ℂ :=
  PrimitiveYee.fiber Concrete.baseMaterial (timeReversalMomentum ![1,1,0])

def basePointOperator : PointSpace →ₗ[ℂ] PointSpace := basePointFiber.toEuclideanLin

theorem basePointOperator_symmetric : basePointOperator.IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (PrimitiveYee.fiber_hermitian _ _)

/-- The exact finite endpoint certificates needed for point isolation. -/
def PointBaseInertia : Prop :=
  (Finset.univ.filter fun i : PointIndex =>
    basePointOperator_symmetric.eigenvalues rfl i < 1 / 256).card = 2002 ∧
  (Finset.univ.filter fun i : PointIndex =>
    basePointOperator_symmetric.eigenvalues rfl i < 5 / 256).card = 2004

theorem point_eigenvalue_comparison (i : PointIndex) :
    pointOperator_symmetric.eigenvalues rfl i ≤
      basePointOperator_symmetric.eigenvalues rfl i ∧
    basePointOperator_symmetric.eigenvalues rfl i ≤
      pointOperator_symmetric.eigenvalues rfl i + 1023 / 2^26 := by
  exact Concrete.primitive_eigenvalue_comparison (timeReversalMomentum ![1,1,0]) i

private theorem pointIndex0_inside_thresholds :
    1 / 256 < pointOperator_symmetric.eigenvalues rfl pointIndex0 ∧
    pointOperator_symmetric.eigenvalues rfl pointIndex0 < 5 / 256 - 1023 / 2^26 := by
  have h := abs_le.mp pointIndex0_interval
  have hr := pointCenter0_range
  constructor <;> norm_num at * <;> linarith

private theorem pointIndex1_inside_thresholds :
    1 / 256 < pointOperator_symmetric.eigenvalues rfl pointIndex1 ∧
    pointOperator_symmetric.eigenvalues rfl pointIndex1 < 5 / 256 - 1023 / 2^26 := by
  have h := abs_le.mp pointIndex1_interval
  have hr := pointCenter1_range
  constructor <;> norm_num at * <;> linarith

theorem point_other_eigenvalue_outside_thresholds (hcounts : PointBaseInertia)
    (i : PointIndex) (hi : i ∉ pointCluster) :
    pointOperator_symmetric.eigenvalues rfl i ≤ 1 / 256 ∨
      5 / 256 - 1023 / 2^26 ≤ pointOperator_symmetric.eigenvalues rfl i := by
  apply outside_pair_of_threshold_counts
    (basePointOperator_symmetric.eigenvalues rfl)
    (pointOperator_symmetric.eigenvalues rfl)
    (1/256) (5/256) (1023/2^26) (by norm_num) point_eigenvalue_comparison
    (by rw [hcounts.1, hcounts.2]) pointIndex0 pointIndex1 pointIndices_distinct
    pointIndex0_inside_thresholds pointIndex1_inside_thresholds i
  · intro h
    apply hi
    simp [pointCluster, h]
  · intro h
    apply hi
    simp [pointCluster, h]

theorem pointClusterComplementGap_of_base_inertia (hcounts : PointBaseInertia) :
    PointClusterComplementGap := by
  intro i hi j
  have hout := point_other_eigenvalue_outside_thresholds hcounts i hi
  have hc0 := pointCenter0_range
  have hc1 := pointCenter1_range
  fin_cases j <;> dsimp only [pointCenters, Matrix.cons_val] <;>
    rcases hout with hlo | hhi
  · apply le_trans _ (neg_le_abs _)
    norm_num at *
    linarith
  · apply le_trans _ (le_abs_self _)
    norm_num at *
    linarith
  · apply le_trans _ (neg_le_abs _)
    norm_num at *
    linarith
  · apply le_trans _ (le_abs_self _)
    norm_num at *
    linarith

end
end Maxwell.Certificate.PointWitness
