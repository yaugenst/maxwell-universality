import Maxwell.Continuum.PeriodicImaginaryPole

/-! Exact coordinate symmetry at the constructed imaginary pole. In
particular, each transverse derivative of the literal band vanishes. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Filter
open scoped Topology

theorem physicalChart_isOpen : IsOpen physicalChart := by
  change IsOpen {q : Momentum | ∀ j, ‖q j‖ < analyticRadius}
  simpa only [ofPred_forall] using
    (isOpen_iInter_of_finite (fun j : Fin 3 =>
      isOpen_lt (continuous_apply j).norm continuous_const))

theorem dielectricBand_reflect {q : Momentum} (hq : q ∈ physicalChart) (j : Fin 3) :
    dielectricBand (FiberReflection.momentum j q) = dielectricBand q := by
  have hu : unscale (FiberReflection.momentum j q) =
      FiberReflection.momentum j (unscale q) := by
    unfold unscale
    rw [reflection_smul]
  rw [dielectricBand_formula, dielectricBand_formula, hu,
    scaledBand_reflect (unscale_mem_chart hq) j]

theorem transverse_slice_even (j k : Fin 3) (hjk : j ≠ k) {c : ℂ}
    (hc : ‖c‖ < analyticRadius) :
    (fun ζ : ℂ => dielectricBand (c • basisVector j + (-ζ) • basisVector k)) =ᶠ[𝓝 0]
      (fun ζ : ℂ => dielectricBand (c • basisVector j + ζ • basisVector k)) := by
  have ho : IsOpen {ζ : ℂ | c • basisVector j + ζ • basisVector k ∈ physicalChart} :=
    physicalChart_isOpen.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have hzero : (0 : ℂ) ∈ {ζ : ℂ | c • basisVector j + ζ • basisVector k ∈ physicalChart} := by
    change c • basisVector j + (0 : ℂ) • basisVector k ∈ physicalChart
    simpa only [zero_smul, add_zero] using coordinate_mem_physicalChart j hc
  filter_upwards [ho.mem_nhds hzero] with ζ hζ
  have he := dielectricBand_reflect hζ k
  rw [reflection_add, reflection_smul, reflection_smul, reflect_basis_other k j hjk.symm,
    reflect_basis_same, smul_neg, ← neg_smul] at he
  exact he

theorem transverse_band_derivative_zero (j k : Fin 3) (hjk : j ≠ k) {c : ℂ}
    (hc : ‖c‖ < analyticRadius) :
    deriv (fun ζ : ℂ => dielectricBand (c • basisVector j + ζ • basisVector k)) 0 = 0 := by
  simpa only [Nat.mul_zero, zero_add, iteratedDeriv_one] using
    EvenTaylor.odd_deriv_zero (transverse_slice_even j k hjk hc) 0

theorem imaginaryPole_transverse_derivative {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j k : Fin 3) (hjk : j ≠ k) :
    deriv (fun ζ : ℂ => dielectricBand
      (((imaginaryPole D hh j : ℂ) * Complex.I) • basisVector j + ζ • basisVector k)) 0 = 0 := by
  apply transverse_band_derivative_zero j k hjk
  have hp := imaginaryPole_mem_small D hh j
  have hs := imaginary_scale_bounds D.h_pos.le hh
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
    abs_of_nonneg hp.1] using
    hp.2.trans_lt (lt_of_le_of_lt hs.1 (by linarith [analyticRadius_pos]))

end Maxwell.Continuum.PeriodicBand
