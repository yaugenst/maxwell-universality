import Maxwell.Continuum.PeriodicTubeShift

/-! Nondegeneracy of the actual optimal displacement. -/

noncomputable section

namespace Maxwell.Continuum.PeriodicBand

theorem dualHessianEnergy_pos {R : Corner.Vec} (hR : R ≠ 0) :
    0 < dualHessianEnergy R := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, R j ≠ 0 := by
    by_contra! hn
    exact hR (funext hn)
  exact (div_pos (sq_pos_of_ne_zero hj) (hessian_diagonal_positive j)).trans_le
    (Finset.single_le_sum
      (fun k _ => div_nonneg (sq_nonneg (R k)) (hessian_diagonal_positive k).le)
      (Finset.mem_univ j))

theorem dualHessianDistance_pos {R : Corner.Vec} (hR : R ≠ 0) :
    0 < dualHessianDistance R := Real.sqrt_pos.mpr (dualHessianEnergy_pos hR)

theorem optimalTubeShift_ne_zero {h : ℝ} (hh : 0 < h)
    {R : Corner.Vec} (hR : R ≠ 0) : optimalTubeShift h R ≠ 0 := by
  intro he
  have hp := optimalTubeShift_phase h R
  rw [he, zero_dotProduct] at hp
  exact (ne_of_gt (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 99 / 100) hh)
    (dualHessianDistance_pos hR))) hp.symm

end Maxwell.Continuum.PeriodicBand
