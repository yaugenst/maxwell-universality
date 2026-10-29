import Maxwell.Spectral.BoxMagnetic
import Maxwell.Spectral.BoxFourierProjection

/-! Cartesian box geometry and positivity of the actual moved Fourier symbols. -/

noncomputable section

namespace Maxwell.Spectral.BoxGeometry

open Maxwell.Certificate.FourierBinding Maxwell.Spectral.PeriodicYee
open BoxSymbols BoxMagnetic BoxFourierProjection

theorem momentumNorm_le_of_coordinate_bounds (q half : Momentum)
    (hq : ∀ j, |q j| ≤ half j) : momentumNorm q ≤ momentumNorm half := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change momentumNorm q^2 ≤ momentumNorm half^2
  rw [momentumNorm_sq, momentumNorm_sq]
  apply Finset.sum_le_sum
  intro j _
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (q j)) (hq j) 2

theorem displacementSize_le_of_coordinate_bounds (q half : Momentum)
    (hq : ∀ j, |q j| ≤ half j) :
    displacementSize q ≤ phaseScale*momentumNorm half :=
  mul_le_mul_of_nonneg_left (momentumNorm_le_of_coordinate_bounds q half hq) phaseScale_pos.le

theorem displacementSize_le_of_box_radius (q half : Momentum) (s : ℝ)
    (hq : ∀ j, |q j| ≤ half j) (hs : phaseScale*momentumNorm half ≤ s) :
    displacementSize q ≤ s := (displacementSize_le_of_coordinate_bounds q half hq).trans hs

theorem longitudinal_norm_shift_lower (c q : Momentum) (f : Frequency) (s : ℝ)
    (hq : displacementSize q ≤ s) :
    ‖longitudinalVector c f‖-s ≤ ‖longitudinalVector (c+q) f‖ := by
  have h := BoxProjection.norm_add_lower (longitudinalVector c f)
    (longitudinalVector (c+q) f-longitudinalVector c f) s
    ((longitudinal_increment_bound c q f).trans hq)
  simpa only [add_sub_cancel] using h

theorem longitudinal_norm_shift_lower_uniform (c q : Momentum) (f : Frequency) (s r : ℝ)
    (hq : displacementSize q ≤ s) (hr : r ≤ ‖longitudinalVector c f‖) :
    r-s ≤ ‖longitudinalVector (c+q) f‖ :=
  (sub_le_sub_right hr s).trans (longitudinal_norm_shift_lower c q f s hq)

/-- The accepted shifted lower denominator is a strict lower bound for
every actual high-frequency magnetic weight throughout the box. -/
theorem shifted_high_weight_pos (c q : Momentum) (support : Finset Frequency)
    (ρ t t' σ s r : ℝ) (hρ : 0 < ρ) (hq : displacementSize q ≤ s) (hsr : s < r)
    (hr : ∀ f ∈ support, r ≤ ‖longitudinalVector c f‖)
    (ht' : t' ≤ t+σ) (hshift : 0 < (r-s)^2/ρ-t-σ) :
    ∀ f ∈ support, 0 < laplacianSymbol (c+q) f/ρ-t' := by
  intro f hf
  have hlower := longitudinal_norm_shift_lower_uniform c q f s r hq (hr f hf)
  have hsq := pow_le_pow_left₀ (sub_nonneg.mpr hsr.le) hlower 2
  rw [longitudinalVector_norm_sq] at hsq
  have hdiv := div_le_div_of_nonneg_right hsq hρ.le
  linarith

theorem shifted_longitudinalVector_ne_zero (c q : Momentum) (s r : ℝ)
    (hq : displacementSize q ≤ s) (hsr : s < r)
    (hr : ∀ f, r ≤ ‖longitudinalVector c f‖) :
    ∀ f, longitudinalVector (c+q) f ≠ 0 := by
  intro f
  exact norm_pos_iff.mp ((sub_pos.mpr hsr).trans_le
    (longitudinal_norm_shift_lower_uniform c q f s r hq (hr f)))

theorem shifted_laplacianSymbol_pos (c q : Momentum) (s r : ℝ)
    (hq : displacementSize q ≤ s) (hsr : s < r)
    (hr : ∀ f, r ≤ ‖longitudinalVector c f‖) :
    ∀ f, 0 < laplacianSymbol (c+q) f := by
  intro f
  rw [← longitudinalVector_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr (shifted_longitudinalVector_ne_zero c q s r hq hsr hr f))

theorem shifted_laplacianSymbol_ne_zero (c q : Momentum) (s r : ℝ)
    (hq : displacementSize q ≤ s) (hsr : s < r)
    (hr : ∀ f, r ≤ ‖longitudinalVector c f‖) :
    ∀ f, laplacianSymbol (c+q) f ≠ 0 :=
  fun f => ne_of_gt (shifted_laplacianSymbol_pos c q s r hq hsr hr f)

end Maxwell.Spectral.BoxGeometry
