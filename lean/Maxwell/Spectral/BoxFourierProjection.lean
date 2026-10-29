import Maxwell.Spectral.BoxProjection
import Maxwell.Spectral.BoxSymbols
import Maxwell.Spectral.BoxWeights
import Maxwell.Certificate.FourierTransverse

namespace Maxwell.Spectral.BoxFourierProjection

open Maxwell.Certificate.FourierBinding Maxwell.Spectral.PeriodicYee
open BoxProjection BoxSymbols
open scoped ComplexConjugate

noncomputable section

theorem longitudinalVector_norm_sq (c : Momentum) (f : Frequency) :
    ‖longitudinalVector c f‖^2 = laplacianSymbol c f := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [longitudinalVector, laplacianSymbol,
    Complex.norm_conj, Complex.normSq_eq_norm_sq]

/-- The projector used by the verifier is exactly the Hilbert orthogonal
projection controlled in `BoxProjection`. -/
theorem gradientProjection_eq_projection (c : Momentum) (f : Frequency) (u : Polarization) :
    gradientProjection c f u = projection (longitudinalVector c f) u := by
  rw [gradientProjection_apply]
  change (divergenceSymbol c f u / (laplacianSymbol c f : ℂ)) • longitudinalVector c f =
    inner ℂ (longitudinalVector c f) u • ((1/‖longitudinalVector c f‖)^2 • longitudinalVector c f)
  rw [longitudinal_inner, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul,
    ← longitudinalVector_norm_sq]
  congr 1
  push_cast
  simp only [div_eq_mul_inv, one_mul, inv_pow]
  rfl

def longitudinalLinear (c q : Momentum) (f : Frequency) : Polarization :=
  WithLp.toLp 2 (fun j => conj (linearSymbol c q f j))

theorem longitudinal_increment_norm (c q : Momentum) (f : Frequency) :
    ‖longitudinalVector (c+q) f-longitudinalVector c f‖ = ‖incrementVector c q f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, PiLp.sub_apply, longitudinalVector,
    incrementVector, ← map_sub, Complex.norm_conj]

theorem longitudinal_increment_bound (c q : Momentum) (f : Frequency) :
    ‖longitudinalVector (c+q) f-longitudinalVector c f‖ ≤ phaseScale*momentumNorm q := by
  rw [longitudinal_increment_norm]
  exact incrementVector_norm c q f

theorem longitudinal_remainder_norm (c q : Momentum) (f : Frequency) :
    ‖longitudinalVector (c+q) f-longitudinalVector c f-longitudinalLinear c q f‖ =
      ‖incrementVector c q f-linearVector c q f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, PiLp.sub_apply, longitudinalVector,
    longitudinalLinear, incrementVector, linearVector,
    ← map_sub, Complex.norm_conj]

theorem longitudinal_remainder_bound (c q : Momentum) (f : Frequency) :
    ‖longitudinalVector (c+q) f-longitudinalVector c f-longitudinalLinear c q f‖ ≤
      phaseScale^2*momentumNorm q^2/2 := by
  rw [longitudinal_remainder_norm]
  exact incrementVector_linear_remainder c q f

/-- Actual changed-momentum gradient leakage of a center-transverse vector. -/
theorem transverse_projection_bound (c q : Momentum) (f : Frequency)
    (u : Polarization) (hu : u ∈ transversePolarization c f)
    (s : ℝ) (hs : 0 ≤ s) (hq : phaseScale*momentumNorm q ≤ s)
    (hsmall : s < ‖longitudinalVector c f‖) :
    ‖gradientProjection (c+q) f u‖ ≤ s/(‖longitudinalVector c f‖-s)*‖u‖ := by
  rw [gradientProjection_eq_projection]
  have h := projection_transverse_bound (longitudinalVector c f)
    (longitudinalVector (c+q) f-longitudinalVector c f) u s hs
    ((longitudinal_increment_bound c q f).trans hq) hsmall
    (by rw [longitudinal_inner]; exact hu)
  simpa only [add_sub_cancel] using h

/-- The actual longitudinal projection remainder has the rational
frequency coefficient used by `verify_scalar`. -/
theorem transverse_projection_remainder (c q : Momentum) (f : Frequency)
    (u : Polarization) (hu : u ∈ transversePolarization c f)
    (s : ℝ) (hs : 0 ≤ s) (hq : phaseScale*momentumNorm q ≤ s)
    (hsmall : s < ‖longitudinalVector c f‖) :
    ‖gradientProjection (c+q) f u-
      transverseLinearTerm (longitudinalVector c f) (longitudinalLinear c q f) u‖ ≤
      s^2*(1/(2*‖longitudinalVector c f‖)+
        (3+s/‖longitudinalVector c f‖)/(‖longitudinalVector c f‖-s)^2)*‖u‖ := by
  rw [gradientProjection_eq_projection]
  have hrem : ‖longitudinalVector (c+q) f-longitudinalVector c f-
      longitudinalLinear c q f‖ ≤ s^2/2 := by
    apply (longitudinal_remainder_bound c q f).trans
    have hsq := pow_le_pow_left₀
      (mul_nonneg phaseScale_pos.le (norm_nonneg _)) hq 2
    rw [mul_pow] at hsq
    change phaseScale^2*momentumNorm q^2 ≤ s^2 at hsq
    linarith
  have h := transverse_remainder_bound (longitudinalVector c f)
    (longitudinalVector (c+q) f-longitudinalVector c f) (longitudinalLinear c q f) u s hs
    ((longitudinal_increment_bound c q f).trans hq) hsmall hrem
    (by rw [longitudinal_inner]; exact hu)
  simpa only [add_sub_cancel] using h

theorem transverse_projection_remainder_uniform (c q : Momentum) (f : Frequency)
    (u : Polarization) (hu : u ∈ transversePolarization c f)
    (s r : ℝ) (hs : 0 ≤ s) (hq : phaseScale*momentumNorm q ≤ s)
    (hsr : s < r) (hrf : r ≤ ‖longitudinalVector c f‖) :
    ‖gradientProjection (c+q) f u-
      transverseLinearTerm (longitudinalVector c f) (longitudinalLinear c q f) u‖ ≤
      s^2*((r/2+3+s/r)/(r-s)^2)*‖u‖ := by
  apply (transverse_projection_remainder c q f u hu s hs hq (hsr.trans_le hrf)).trans
  gcongr
  exact (BoxWeights.projector_remainder_enlargement s _ hs (hsr.trans_le hrf)).trans
    (BoxWeights.projector_remainder_coefficient s r _ hs hsr hrf)

theorem longitudinal_projection_lower (c q : Momentum) (f : Frequency)
    (s : ℝ) (_hs : 0 ≤ s) (hq : phaseScale*momentumNorm q ≤ s) :
    laplacianSymbol c f-s^2 ≤
      ‖gradientProjection (c+q) f (longitudinalVector c f)‖^2 := by
  have h := gradient_projection_lower (longitudinalVector c f)
    (longitudinalVector (c+q) f-longitudinalVector c f)
  simp only [add_sub_cancel, ← gradientProjection_eq_projection,
    longitudinalVector_norm_sq] at h
  have hinc := (longitudinal_increment_bound c q f).trans hq
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hinc 2
  linarith

/-- A fixed center-transverse vector acquires only the explicitly weighted
longitudinal component appearing in the negative-block certificate. -/
theorem transverse_projection_weighted (c q : Momentum) (f : Frequency)
    (u : Polarization) (hu : u ∈ transversePolarization c f)
    (s r : ℝ) (hs : 0 ≤ s) (hq : phaseScale*momentumNorm q ≤ s)
    (hsr : s < r) (hrf : r ≤ ‖longitudinalVector c f‖) :
    ‖gradientProjection (c+q) f u‖ ≤
      (s/(1-s/r))*(‖u‖/‖longitudinalVector c f‖) := by
  have hr : 0 < r := hs.trans_lt hsr
  have hf : 0 < ‖longitudinalVector c f‖ := hr.trans_le hrf
  have hratio : 0 < 1-s/r := sub_pos.mpr ((div_lt_one hr).mpr hsr)
  have hd : ‖longitudinalVector c f‖*(1-s/r) ≤ ‖longitudinalVector c f‖-s := by
    have h := mul_le_mul_of_nonneg_left hrf hs
    have hd' : s ≤ s*‖longitudinalVector c f‖/r := (le_div_iff₀ hr).mpr (by nlinarith)
    simp only [div_eq_mul_inv] at hd' ⊢
    nlinarith
  calc
    _ ≤ s/(‖longitudinalVector c f‖-s)*‖u‖ :=
      transverse_projection_bound c q f u hu s hs hq (hsr.trans_le hrf)
    _ ≤ s/(‖longitudinalVector c f‖*(1-s/r))*‖u‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg u)
      exact div_le_div_of_nonneg_left hs (mul_pos hf hratio) hd
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

def normalizedGradient (c : Momentum) (f : Frequency) : Polarization :=
  ((8 : ℂ)/(‖longitudinalVector c f‖ : ℂ)) • longitudinalVector c f

def normalizedGradientLinear (c q : Momentum) (f : Frequency) : Polarization :=
  ((8 : ℂ)/(‖longitudinalVector c f‖ : ℂ)) • longitudinalLinear c q f

theorem normalizedGradient_norm (c : Momentum) (f : Frequency)
    (hv : longitudinalVector c f ≠ 0) : ‖normalizedGradient c f‖ = 8 := by
  have hn : ‖longitudinalVector c f‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  rw [normalizedGradient, norm_smul, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), show ‖(8 : ℂ)‖ = (8 : ℝ) by norm_num]
  exact div_mul_cancel₀ _ hn

theorem normalizedGradient_transverse_bound (c q : Momentum) (f : Frequency)
    (s r : ℝ) (hs : 0 ≤ s) (hq : phaseScale*momentumNorm q ≤ s)
    (hr : 0 < r) (hrf : r ≤ ‖longitudinalVector c f‖) :
    ‖normalizedGradient c f-gradientProjection (c+q) f (normalizedGradient c f)‖ ≤
      8*s/r := by
  have hb := gradient_transverse_bound (longitudinalVector c f)
    (longitudinalVector (c+q) f-longitudinalVector c f)
  simp only [add_sub_cancel, ← gradientProjection_eq_projection] at hb
  have h := hb.trans ((longitudinal_increment_bound c q f).trans hq)
  rw [normalizedGradient, map_smul, ← smul_sub, norm_smul, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    show ‖(8 : ℂ)‖ = (8 : ℝ) by norm_num]
  calc
    _ ≤ (8/‖longitudinalVector c f‖)*s := mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ (8/r)*s := by gcongr
    _ = _ := by ring

/-- This is the actual mixed gradient derivative (`gprime_raw`), paired
with a transverse witness. The remainder retains its inverse-Laplacian weight. -/
theorem normalizedGradient_mixed_remainder
    (c q : Momentum) (f : Frequency) (u : Polarization)
    (hu : u ∈ transversePolarization c f) (s r R : ℝ)
    (hs : 0 ≤ s) (hq : phaseScale*momentumNorm q ≤ s)
    (hsr : s < r) (hrf : r ≤ ‖longitudinalVector c f‖)
    (hfR : ‖longitudinalVector c f‖ ≤ R) :
    ‖inner ℂ u (gradientProjection (c+q) f (normalizedGradient c f)-
      normalizedGradientLinear c q f)‖ ≤
      8*s^2*((3+s/r)/(1-s/r)^2+(1/2)*R/(1-s/r))*
        (‖u‖/‖longitudinalVector c f‖^2) := by
  have hv : 0 < ‖longitudinalVector c f‖ := hs.trans_lt (hsr.trans_le hrf)
  have hrem : ‖longitudinalVector (c+q) f-longitudinalVector c f-
      longitudinalLinear c q f‖ ≤ s^2/2 := by
    apply (longitudinal_remainder_bound c q f).trans
    have hsq := pow_le_pow_left₀
      (mul_nonneg phaseScale_pos.le (norm_nonneg _)) hq 2
    rw [mul_pow] at hsq
    change phaseScale^2*momentumNorm q^2 ≤ s^2 at hsq
    linarith
  have hb := mixed_remainder_bound_sharp (longitudinalVector c f)
    (longitudinalVector (c+q) f-longitudinalVector c f) (longitudinalLinear c q f) u s hs
    ((longitudinal_increment_bound c q f).trans hq) (hsr.trans_le hrf) hrem
    (by rw [longitudinal_inner]; exact hu)
  simp only [add_sub_cancel, ← gradientProjection_eq_projection] at hb
  rw [normalizedGradient, normalizedGradientLinear, map_smul, ← smul_sub,
    inner_smul_right, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)]
  rw [show ‖(8 : ℂ)‖ = (8 : ℝ) by norm_num]
  calc
    _ ≤ (8/‖longitudinalVector c f‖)*
        (s^2*(1/(‖longitudinalVector c f‖*(‖longitudinalVector c f‖-s))+
          1/(2*‖longitudinalVector c f‖))*‖u‖*‖longitudinalVector c f‖) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 8*s^2*(1/(‖longitudinalVector c f‖*(‖longitudinalVector c f‖-s))+
          1/(2*‖longitudinalVector c f‖))*‖u‖ := by field_simp
    _ ≤ 8*s^2*(((3+s/r)/(1-s/r)^2+(1/2)*R/(1-s/r))/
        ‖longitudinalVector c f‖^2)*‖u‖ := by
      gcongr
      exact BoxWeights.low_projector_cross_coefficient s r R _ hs hsr hrf hfR
    _ = _ := by ring

end
end Maxwell.Spectral.BoxFourierProjection
