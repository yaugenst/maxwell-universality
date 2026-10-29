import Maxwell.Continuum.FiberL1Eigenvector
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Cauchy--Schwarz on the literal eight central aliases sharpens the
finite-cluster absolute Fourier bound, preserving both polarizations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.CellBandFourier

open FreeFiber ClusterComplement FiberL1

theorem clusterLift_norm_le_three (u : FiberSpace) :
    ‖clusterLift u‖ ≤ 3 * ‖ClusterComplement.clusterProjection u‖ := by
  have heq : ‖clusterLift u‖ =
      ∑ ν ∈ centralFinset, ‖ClusterComplement.clusterProjection u ν‖ := by
    rw [norm_eq_tsum]
    apply tsum_eq_sum
    intro ν hν
    have hn : ¬IsCentralAlias ν := by simpa only [mem_centralFinset] using hν
    change ‖ClusterComplement.clusterProjection u ν‖ = 0
    rw [ClusterComplement.clusterProjection_apply, clusterBlock_noncentral ν hn,
      zero_apply, norm_zero]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq centralFinset
    (fun _ : Alias => (1 : ℝ)) (fun ν => ‖ClusterComplement.clusterProjection u ν‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, centralFinset_card,
    Nat.cast_ofNat, mul_one] at hcs
  have hs : (∑ ν ∈ centralFinset, ‖ClusterComplement.clusterProjection u ν‖ ^ 2) ≤
      ‖ClusterComplement.clusterProjection u‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.sum_rpow_le_norm_rpow (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)
        (ClusterComplement.clusterProjection u) centralFinset
  rw [heq]
  have hn := Finset.sum_nonneg (fun ν (_ : ν ∈ centralFinset) =>
    norm_nonneg (ClusterComplement.clusterProjection u ν))
  nlinarith [norm_nonneg (ClusterComplement.clusterProjection u)]

theorem l1_schurLift_complement_bound (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8) (u : FiberSpace) :
    ‖FiberL1.schurLift t e ht he u - clusterLift u‖ ≤
      48 * backgroundAmplitude * ‖ClusterComplement.clusterProjection u‖ := by
  change ‖clusterLift u - FiberL1.complementInverse t e ht he
    (FiberL1.rightCoupling t (totalEnergy e) ht (clusterLift u)) - clusterLift u‖ ≤ _
  rw [sub_sub_cancel_left, norm_neg]
  have hR := (FiberL1.complementInverse t e ht he).le_opNorm
    (FiberL1.rightCoupling t (totalEnergy e) ht (clusterLift u))
  have hB := (FiberL1.rightCoupling t (totalEnergy e) ht).le_opNorm (clusterLift u)
  calc
    _ ≤ 2 * ‖FiberL1.rightCoupling t (totalEnergy e) ht (clusterLift u)‖ :=
      hR.trans (mul_le_mul_of_nonneg_right (FiberL1.complementInverse_norm_le t e ht he)
        (norm_nonneg _))
    _ ≤ 2 * ((8 * backgroundAmplitude) * ‖clusterLift u‖) :=
      mul_le_mul_of_nonneg_left
        (hB.trans (mul_le_mul_of_nonneg_right
          (FiberL1.rightCoupling_norm_le t (totalEnergy e) ht) (norm_nonneg _))) (by norm_num)
    _ ≤ 2 * ((8 * backgroundAmplitude) * (3 * ‖ClusterComplement.clusterProjection u‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (clusterLift_norm_le_three u)
        (mul_nonneg (by norm_num) backgroundAmplitude_pos.le)) (by norm_num)
    _ = _ := by ring

#print axioms clusterLift_norm_le_three
#print axioms l1_schurLift_complement_bound

end Maxwell.Continuum.CellBandFourier
