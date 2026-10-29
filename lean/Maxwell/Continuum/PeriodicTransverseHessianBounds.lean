import Maxwell.Continuum.PeriodicImaginaryBand

/-! Actual second transverse Taylor coefficients at a shifted coordinate
axis. Their error from the physical central Hessian follows from the proved
quartic remainder by Cauchy's estimate on a disk of the shift's radius. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Set Metric

attribute [local irreducible] dielectricBand hessian

theorem physicalQuadratic_diagonal (q : Momentum) :
    physicalQuadratic q = ∑ j : Fin 3, (hessian j j : ℂ) * (q j) ^ 2 := by
  unfold physicalQuadratic
  rw [bandQuadratic_diagonal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h := physicalQuadratic_basis j
  change (backgroundAmplitude : ℂ)⁻¹ * bandQuadratic (basisVector j) =
    (hessian j j : ℂ) at h
  rw [← h]
  ring

theorem physicalQuadratic_two_axes (j k : Fin 3) (hjk : j ≠ k) (c ζ : ℂ) :
    physicalQuadratic (c • basisVector j + ζ • basisVector k) =
      (hessian j j : ℂ) * c ^ 2 + (hessian k k : ℂ) * ζ ^ 2 := by
  rw [physicalQuadratic_diagonal]
  have he (i : Fin 3) :
      (c • basisVector j + ζ • basisVector k) i ^ 2 =
        (if i = j then c ^ 2 else 0) + (if i = k then ζ ^ 2 else 0) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, basisVector_apply]
    split_ifs <;> simp_all
  simp_rw [he, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

def transverseBand (j k : Fin 3) (c ζ : ℂ) : ℂ :=
  dielectricBand (c • basisVector j + ζ • basisVector k)

def transverseCoefficient (j k : Fin 3) (c : ℂ) : ℂ :=
  EvenTaylor.coefficient (transverseBand j k c) 2

theorem two_axes_norm_le (j k : Fin 3) (c ζ : ℂ) :
    ‖c • basisVector j + ζ • basisVector k‖ ≤ ‖c‖ + ‖ζ‖ := by
  simpa only [norm_smul, basisVector_norm, mul_one] using
    norm_add_le (c • basisVector j) (ζ • basisVector k)

theorem transverseBand_analyticAt (j k : Fin 3) {c ζ : ℂ}
    (hcζ : ‖c‖ + ‖ζ‖ < analyticRadius) : AnalyticAt ℂ (transverseBand j k c) ζ := by
  have hq : c • basisVector j + ζ • basisVector k ∈ physicalChart := by
    intro i
    exact (norm_le_pi_norm _ i).trans_lt ((two_axes_norm_le j k c ζ).trans_lt hcζ)
  have hm : AnalyticAt ℂ (fun w : ℂ => c • basisVector j + w • basisVector k) ζ :=
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  exact AnalyticAt.comp (f := fun w : ℂ => c • basisVector j + w • basisVector k)
    (dielectricBand_analytic _ hq) hm

theorem transverseCoefficient_error (j k : Fin 3) (hjk : j ≠ k) {c : ℂ}
    (hc0 : 0 < ‖c‖) (hc : ‖c‖ ≤ analyticRadius / 4) :
    ‖transverseCoefficient j k c - (hessian k k : ℂ)‖ ≤
      16 * quarticConstant * ‖c‖ ^ 2 := by
  let P : ℂ → ℂ := fun ζ => dielectricBand 0 + (hessian j j : ℂ) * c ^ 2 +
    (hessian k k : ℂ) * ζ ^ 2
  let f : ℂ → ℂ := fun ζ => transverseBand j k c ζ - P ζ
  have hf0 : AnalyticAt ℂ (transverseBand j k c) 0 :=
    transverseBand_analyticAt j k (by simp only [norm_zero, add_zero]; linarith [analyticRadius_pos])
  have hP (ζ : ℂ) : AnalyticAt ℂ P ζ :=
    analyticAt_const.add (analyticAt_const.mul (analyticAt_id.pow 2))
  have hf : AnalyticOnNhd ℂ f (ball 0 ‖c‖) := by
    intro ζ hζ
    have hz : ‖ζ‖ < ‖c‖ := by simpa only [mem_ball, dist_zero_right] using hζ
    exact (transverseBand_analyticAt j k (by linarith [analyticRadius_pos])).sub (hP ζ)
  have hbound : ∀ ζ ∈ ball (0 : ℂ) ‖c‖, ‖f ζ‖ ≤ quarticConstant * (2 * ‖c‖) ^ 4 := by
    intro ζ hζ
    have hz : ‖ζ‖ < ‖c‖ := by simpa only [mem_ball, dist_zero_right] using hζ
    have hnorm := two_axes_norm_le j k c ζ
    have hq : ‖c • basisVector j + ζ • basisVector k‖ ≤ analyticRadius / 2 := by linarith
    have hb := physical_quartic hq
    rw [physicalQuadratic_two_axes j k hjk] at hb
    have he : f ζ = dielectricBand (c • basisVector j + ζ • basisVector k) -
        dielectricBand 0 - ((hessian j j : ℂ) * c ^ 2 + (hessian k k : ℂ) * ζ ^ 2) := by
      dsimp only [f, P, transverseBand]
      ring
    rw [he]
    exact hb.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (by linarith :
        ‖c • basisVector j + ζ • basisVector k‖ ≤ 2 * ‖c‖) 4) quarticConstant_nonneg)
  have hcP : EvenTaylor.coefficient P 2 = (hessian k k : ℂ) := by
    unfold EvenTaylor.coefficient P
    rw [iteratedDeriv_const_add (by norm_num : (0 : ℕ) < 2),
      iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
    norm_num
    ring
  have hcf : EvenTaylor.coefficient f 2 =
      transverseCoefficient j k c - (hessian k k : ℂ) := by
    have hsub := iteratedDeriv_fun_sub (n := 2) hf0.contDiffAt (hP 0).contDiffAt
    change iteratedDeriv 2 f 0 = iteratedDeriv 2 (transverseBand j k c) 0 -
      iteratedDeriv 2 P 0 at hsub
    unfold EvenTaylor.coefficient at hcP
    unfold EvenTaylor.coefficient transverseCoefficient
    rw [hsub, mul_sub, hcP]
    rfl
  have hb := EvenTaylor.coefficient_norm_le hf hbound hc0 2
  rw [hcf] at hb
  exact hb.trans_eq (by field_simp; ring)

end Maxwell.Continuum.PeriodicBand
