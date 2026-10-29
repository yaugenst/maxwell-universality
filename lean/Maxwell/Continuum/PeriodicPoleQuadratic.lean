import Maxwell.Continuum.PeriodicTransversePole
import Maxwell.Continuum.PeriodicTransverseHessian
import Maxwell.Continuum.AnalyticCoordinateQuadratic

/-! The actual transverse second coefficient of the scaled denominator.
Coordinate reflections eliminate mixed terms; scaling by the physical
inverse length cancels exactly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric Filter
open scoped Topology

attribute [local irreducible] poleDenominator imaginaryPole dielectricBand poleSlope
  transverseBand transverseCoefficient

theorem secondCoefficient_affine (f : ℂ → ℂ) (a b : ℂ) :
    EvenTaylor.coefficient (fun ζ => a * (f ζ - b)) 2 =
      a * EvenTaylor.coefficient f 2 := by
  have he : (fun ζ => a * (f ζ - b)) = fun ζ => a * (-b + f ζ) := by
    funext ζ
    ring
  rw [he]
  unfold EvenTaylor.coefficient
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_const_add (by norm_num)]
  ring

theorem secondCoefficient_scale {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (a : ℂ) :
    EvenTaylor.coefficient (fun ζ => f (a * ζ)) 2 =
      a^2 * EvenTaylor.coefficient f 2 := by
  have he := AnalyticLineCoefficients.coefficient_smul hf a 1 2
  simpa only [smul_eq_mul, mul_one, mul_comm] using he

theorem poleDenominator_second_axis {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j k : Fin 3) :
    EvenTaylor.coefficient (fun ζ : ℂ => poleDenominator D hh j (ζ • basisVector k)) 2 =
      transverseCoefficient j k ((imaginaryPole D hh j : ℂ) * Complex.I) := by
  have hc : ‖(imaginaryPole D hh j : ℂ) * Complex.I‖ < analyticRadius := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
      abs_of_pos (imaginaryPole_pos D hh j)]
    exact (imaginaryPole_mem_small D hh j).2.trans_lt
      ((imaginary_scale_bounds D.h_pos.le hh).1.trans_lt (by linarith only [analyticRadius_pos]))
  have ha := transverseBand_analyticAt j k (ζ := 0)
    (by simpa only [norm_zero, add_zero] using hc)
  have he : (fun ζ : ℂ => poleDenominator D hh j (ζ • basisVector k)) =
      fun ζ => ((h : ℂ)^2)⁻¹ * (transverseBand j k
        ((imaginaryPole D hh j : ℂ) * Complex.I) ((h : ℂ) * ζ) - (z : ℂ)) :=
    funext (poleDenominator_line D hh j k)
  rw [he, secondCoefficient_affine, secondCoefficient_scale ha]
  unfold transverseCoefficient
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr D.h_pos.ne')), one_mul]

def poleTransverseDenominator {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (w : Momentum) : ℂ :=
  poleDenominator D hh j (poleOffset j w 0)

theorem poleOffset_smul (j : Fin 3) (a : ℂ) (w : Momentum) :
    poleOffset j (a • w) 0 = a • poleOffset j w 0 := by
  funext k
  simp only [poleOffset, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp only [mul_zero]

theorem poleOffset_basis_same (j : Fin 3) : poleOffset j (basisVector j) 0 = 0 := by
  funext k
  simp only [poleOffset, basisVector_apply, Pi.zero_apply]
  split_ifs <;> rfl

theorem poleOffset_basis_other (j k : Fin 3) (hjk : j ≠ k) :
    poleOffset j (basisVector k) 0 = basisVector k := by
  funext l
  simp only [poleOffset, basisVector_apply]
  split_ifs <;> simp_all

theorem poleTransverseDenominator_analytic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    AnalyticOnNhd ℂ (poleTransverseDenominator D hh j) (ball 0 1) := by
  intro w hw
  have hw' : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw
  have ho := (poleOffset_analytic j (w, 0)).comp
    (f := fun v : Momentum => (v, (0 : ℂ))) (analyticAt_id.prod analyticAt_const)
  have ha := poleDenominator_analytic D hh j (poleOffset j w 0)
    (by rw [mem_ball, dist_zero_right]; exact (poleOffset_zero_norm_le j w).trans_lt hw')
  convert! ha.comp (f := fun v : Momentum => poleOffset j v 0) ho using 1

theorem poleOffset_reflect (j k : Fin 3) (w : Momentum) :
    poleOffset j (FiberReflection.momentum k w) 0 =
      FiberReflection.momentum k (poleOffset j w 0) := by
  funext l
  simp only [poleOffset, FiberReflection.momentum]
  split_ifs <;> simp only [mul_zero]

theorem poleOffset_reflect_same (j : Fin 3) (w : Momentum) :
    poleOffset j (FiberReflection.momentum j w) 0 = poleOffset j w 0 := by
  funext k
  simp only [poleOffset, FiberReflection.momentum, FiberReflection.coordinateSign]
  split_ifs <;> simp_all

theorem poleTransverseDenominator_reflect {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j k : Fin 3) {w : Momentum} (hw : ‖w‖ ≤ 1) :
    poleTransverseDenominator D hh j (FiberReflection.momentum k w) =
      poleTransverseDenominator D hh j w := by
  by_cases hjk : j = k
  · subst k
    unfold poleTransverseDenominator
    rw [poleOffset_reflect_same]
  · have hq := poleMomentum_mem_chart D hh j ((poleOffset_zero_norm_le j w).trans hw)
    have he : poleMomentum D hh j (poleOffset j (FiberReflection.momentum k w) 0) =
        FiberReflection.momentum k (poleMomentum D hh j (poleOffset j w 0)) := by
      unfold poleMomentum poleCenter
      rw [reflection_add, reflection_smul, reflection_smul,
        reflect_basis_other k j (Ne.symm hjk), poleOffset_reflect]
    unfold poleTransverseDenominator poleDenominator
    rw [he, dielectricBand_reflect hq k]

theorem poleTransverseDenominator_reflect_eventually {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    ∀ k, (fun w => poleTransverseDenominator D hh j (FiberReflection.momentum k w)) =ᶠ[𝓝 0]
      poleTransverseDenominator D hh j := by
  intro k
  filter_upwards [ball_mem_nhds (0 : Momentum) (by norm_num : (0 : ℝ) < 1)] with w hw
  exact poleTransverseDenominator_reflect D hh j k
    (le_of_lt (by simpa only [mem_ball, dist_zero_right] using hw))

def poleQuadratic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (w : Momentum) : ℂ :=
  ∑ k : Fin 3, if k = j then 0 else
    transverseCoefficient j k ((imaginaryPole D hh j : ℂ) * Complex.I) * w k ^ 2

theorem poleTransverseDenominator_second {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (w : Momentum) :
    EvenTaylor.coefficient (fun ζ : ℂ => poleTransverseDenominator D hh j (ζ • w)) 2 =
      poleQuadratic D hh j w := by
  rw [AnalyticCoordinateQuadratic.diagonal
    (poleTransverseDenominator_analytic D hh j 0 (by simp))
    (poleTransverseDenominator_reflect_eventually D hh j)]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hkj : k = j
  · subst k
    simp only [ite_true]
    have he : (fun ζ : ℂ => poleTransverseDenominator D hh j (ζ • basisVector j)) = fun _ => 0 := by
      funext ζ
      simp only [poleTransverseDenominator, poleOffset_smul, poleOffset_basis_same,
        smul_zero, poleDenominator_zero]
    rw [he]
    simp only [EvenTaylor.coefficient, iteratedDeriv_const]
    norm_num
  · rw [ite_eq_right hkj]
    congr 1
    have he : (fun ζ : ℂ => poleTransverseDenominator D hh j (ζ • basisVector k)) =
        fun ζ => poleDenominator D hh j (ζ • basisVector k) := by
      funext ζ
      simp only [poleTransverseDenominator, poleOffset_smul, poleOffset_basis_other j k (Ne.symm hkj)]
    rw [he, poleDenominator_second_axis]

end Maxwell.Continuum.PeriodicBand
