import Maxwell.Continuum.AuxiliaryEnergy
import Maxwell.Continuum.EvenTaylorImaginary
import Maxwell.Continuum.PlacementMetric

/-! Literal coordinate slices of the physical dielectric band. Their
imaginary values are real, and their leading coefficient is Hjj. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric Filter
open scoped Topology

def coordinateBand (j : Fin 3) (ζ : ℂ) : ℂ := dielectricBand (ζ • basisVector j)

def imaginaryRise (j : Fin 3) (β : ℝ) : ℝ :=
  centerEnergy - (coordinateBand j ((β : ℂ) * Complex.I)).re

theorem basisVector_norm (j : Fin 3) : ‖basisVector j‖ = 1 := by
  simp only [basisVector, Pi.norm_single, norm_one]

theorem realMomentum_single (j : Fin 3) :
    realMomentum (Pi.single j (1 : ℝ)) = basisVector j := by
  funext k
  simp only [realMomentum, basisVector, Pi.single_apply]
  split_ifs <;> norm_num

theorem coordinate_mem_physicalChart (j : Fin 3) {ζ : ℂ}
    (hζ : ‖ζ‖ < analyticRadius) : ζ • basisVector j ∈ physicalChart := by
  intro k
  exact (norm_le_pi_norm (ζ • basisVector j) k).trans_lt
    (by simpa only [norm_smul, basisVector_norm, mul_one] using hζ)

theorem coordinateBand_analytic (j : Fin 3) :
    AnalyticOnNhd ℂ (coordinateBand j) (ball 0 analyticRadius) := by
  intro ζ hζ
  exact AnalyticAt.comp (f := fun w : ℂ => w • basisVector j)
    (dielectricBand_analytic _ (coordinate_mem_physicalChart j (by simpa using hζ)))
    (analyticAt_id.smul analyticAt_const)

theorem dielectricBand_neg {q : Momentum} (hq : q ∈ physicalChart) :
    dielectricBand (-q) = dielectricBand q := by
  rw [dielectricBand_formula, dielectricBand_formula]
  simp only [unscale, smul_neg]
  have hn := scaledBand_neg (unscale_mem_chart hq)
  change scaledBand (-((backgroundAmplitude : ℂ)⁻¹ • q)) =
    scaledBand ((backgroundAmplitude : ℂ)⁻¹ • q) at hn
  rw [hn]

theorem coordinateBand_even (j : Fin 3) :
    (fun ζ => coordinateBand j (-ζ)) =ᶠ[𝓝 0] coordinateBand j := by
  filter_upwards [ball_mem_nhds (0 : ℂ) analyticRadius_pos] with ζ hζ
  change dielectricBand ((-ζ) • basisVector j) = dielectricBand (ζ • basisVector j)
  rw [neg_smul]
  exact dielectricBand_neg (coordinate_mem_physicalChart j (by simpa using hζ))

theorem coordinateBand_real (j : Fin 3) {x : ℝ} (hx : |x| < analyticRadius) :
    (coordinateBand j (x : ℂ)).im = 0 := by
  have he : (x : ℂ) • basisVector j = realMomentum (x • Pi.single j (1 : ℝ)) := by
    rw [realMomentum_smul, realMomentum_single]
  change (dielectricBand ((x : ℂ) • basisVector j)).im = 0
  rw [he]
  exact dielectricBand_im_zero (x • Pi.single j 1) (by
    rw [← he]
    exact coordinate_mem_physicalChart j (by simpa using hx))

theorem coordinateBand_real_eventually (j : Fin 3) :
    ∀ᶠ x : ℝ in 𝓝 0, (coordinateBand j (x : ℂ)).im = 0 := by
  have ho : IsOpen {x : ℝ | |x| < analyticRadius} :=
    isOpen_lt continuous_abs continuous_const
  filter_upwards [ho.mem_nhds (by simpa using analyticRadius_pos)] with x hx
  exact coordinateBand_real j hx

theorem coordinateBand_imaginary_real (j : Fin 3) {β : ℝ}
    (hβ : |β| < analyticRadius) :
    (coordinateBand j ((β : ℂ) * Complex.I)).im = 0 :=
  EvenTaylor.imaginary_im_zero (coordinateBand_analytic j) analyticRadius_pos
    (coordinateBand_even j) (coordinateBand_real_eventually j) hβ

theorem coordinateBand_zero (j : Fin 3) : coordinateBand j 0 = dielectricBand 0 := by
  simp only [coordinateBand, zero_smul]

theorem physicalQuadratic_basis (j : Fin 3) :
    physicalQuadratic (basisVector j) = (hessian j j : ℂ) := by
  have h := physicalQuadratic_real_form (Pi.single j (1 : ℝ))
  rw [realMomentum_single] at h
  simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using h

theorem physicalQuadratic_coordinate (j : Fin 3) (ζ : ℂ) :
    physicalQuadratic (ζ • basisVector j) = (hessian j j : ℂ) * ζ^2 := by
  have h := physicalQuadratic_basis j
  simp only [physicalQuadratic, bandQuadratic_smul] at h ⊢
  rw [← h]
  ring

theorem coordinateBand_quartic (j : Fin 3) {ζ : ℂ}
    (hζ : ‖ζ‖ ≤ analyticRadius / 2) :
    ‖coordinateBand j ζ - coordinateBand j 0 - (hessian j j : ℂ) * ζ^2‖ ≤
      quarticConstant * ‖ζ‖^4 := by
  have ht (k : Fin 3) : ‖basisVector j k‖ ≤ 1 :=
    (norm_le_pi_norm _ k).trans_eq (basisVector_norm j)
  simpa only [coordinateBand, zero_smul, physicalQuadratic_coordinate] using
    physical_line_quartic ht hζ

theorem hessian_diagonal_bounds (j : Fin 3) :
    (2 * backgroundAmplitude)⁻¹ ≤ hessian j j ∧
      hessian j j ≤ 256 / backgroundAmplitude := by
  simpa [dotProduct, Matrix.mulVec, Pi.single_apply] using
    hessian_bounds (Pi.single j (1 : ℝ))

theorem hessian_diagonal_ge_one (j : Fin 3) : 1 ≤ hessian j j :=
  (by norm_num [backgroundAmplitude] : (1 : ℝ) ≤ (2 * backgroundAmplitude)⁻¹).trans
    (hessian_diagonal_bounds j).1

theorem sqrt_hessian_diagonal_ge_one (j : Fin 3) : 1 ≤ Real.sqrt (hessian j j) := by
  have h := Real.sqrt_le_sqrt (hessian_diagonal_ge_one j)
  simpa only [Real.sqrt_one] using h

theorem imaginaryRise_quartic (j : Fin 3) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ : β ≤ analyticRadius / 2) :
    |imaginaryRise j β - hessian j j * β^2| ≤ quarticConstant * β^4 := by
  have hn : ‖(β : ℂ) * Complex.I‖ = β := by simp [abs_of_nonneg hβ0]
  have hb := coordinateBand_quartic j (ζ := (β : ℂ) * Complex.I) (by rwa [hn])
  rw [hn] at hb
  have he : (coordinateBand j ((β : ℂ) * Complex.I) - coordinateBand j 0 -
      (hessian j j : ℂ) * ((β : ℂ) * Complex.I)^2).re =
      -(imaginaryRise j β - hessian j j * β^2) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      coordinateBand_zero, imaginaryRise, centerEnergy, Complex.neg_re,
      Complex.one_re, Complex.neg_im, Complex.one_im]
    ring
  have hr := (Complex.abs_re_le_norm _).trans hb
  rwa [he, abs_neg] at hr

end Maxwell.Continuum.PeriodicBand
