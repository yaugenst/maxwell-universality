import Maxwell.Spectral.BoxProjectionAssembly
import Maxwell.Spectral.BoxHighCoercivity

namespace Maxwell.Spectral.BoxGradient

open Maxwell.Certificate.FourierBinding Maxwell.Spectral.PeriodicYee
open Maxwell.Spectral.PrimitiveYee BoxFourierProjection BoxSymbols BoxProjectionAssembly

noncomputable section

abbrev Coefficients := EuclideanSpace ℂ Frequency

def gradient (c : Momentum) (low : Finset Frequency) (g : Coefficients) : FourierSpace :=
  WithLp.toLp 2 (fun e => if e.2 ∈ low then g e.2*normalizedGradient c e.2 e.1 else 0)

def gradientLinear (c q : Momentum) (low : Finset Frequency) (g : Coefficients) : FourierSpace :=
  WithLp.toLp 2 (fun e => if e.2 ∈ low then g e.2*normalizedGradientLinear c q e.2 e.1 else 0)

def lowInverseLaplacian (c : Momentum) (low : Finset Frequency) : Frequency → ℝ :=
  fun f => if f ∈ low then 1/‖longitudinalVector c f‖^2 else 0

theorem gradient_component (c : Momentum) (low : Finset Frequency) (g : Coefficients)
    (f : Frequency) : frequencyComponent f (gradient c low g) =
      if f ∈ low then g f • normalizedGradient c f else 0 := by
  ext j
  change (if f ∈ low then g f*normalizedGradient c f j else 0) = _
  by_cases hf : f ∈ low <;> simp [hf]

theorem gradientLinear_component (c q : Momentum) (low : Finset Frequency) (g : Coefficients)
    (f : Frequency) : frequencyComponent f (gradientLinear c q low g) =
      if f ∈ low then g f • normalizedGradientLinear c q f else 0 := by
  ext j
  change (if f ∈ low then g f*normalizedGradientLinear c q f j else 0) = _
  by_cases hf : f ∈ low <;> simp [hf]

theorem inner_eq_sum_components (x y : FourierSpace) :
    inner ℂ x y = ∑ f, inner ℂ (frequencyComponent f x) (frequencyComponent f y) := by
  change (∑ e : Electric, y e*star (x e)) =
    ∑ f : Frequency, ∑ j : Direction, y (j,f)*star (x (j,f))
  rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem weighted_cauchy (x : FourierSpace) (g : Coefficients) :
    (∑ f, ‖frequencyComponent f x‖*‖g f‖) ≤ ‖x‖*‖g‖ := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun f => ‖frequencyComponent f x‖) (fun f => ‖g f‖)
  rw [← BoxCrossNorm.frequency_norm_sq_eq_sum,
    ← EuclideanSpace.norm_sq_eq, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h
  exact h

theorem gradient_norm_sq (c : Momentum) (low : Finset Frequency) (g : Coefficients)
    (hv : ∀ f ∈ low, longitudinalVector c f ≠ 0)
    (hg : ∀ f, f ∉ low → g f = 0) :
    ‖gradient c low g‖^2 = 64*‖g‖^2 := by
  rw [BoxCrossNorm.frequency_norm_sq_eq_sum, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [gradient_component]
  by_cases hf : f ∈ low
  · rw [ite_eq_left hf, norm_smul, normalizedGradient_norm c f (hv f hf)]
    ring
  · simp [hf, hg f hf]

theorem gradient_transverse_norm
    (c q : Momentum) (low : Finset Frequency) (g : Coefficients) (s r : ℝ)
    (hs : 0 ≤ s) (hq : phaseScale*momentumNorm q ≤ s) (hr : 0 < r)
    (hrf : ∀ f ∈ low, r ≤ ‖longitudinalVector c f‖) :
    ‖gradient c low g-projector (c+q) (gradient c low g)‖ ≤ (8*s/r)*‖g‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg _))).mp
  rw [BoxCrossNorm.frequency_norm_sq_eq_sum, mul_pow, EuclideanSpace.norm_sq_eq,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro f _
  rw [map_sub, projector_component, gradient_component]
  by_cases hf : f ∈ low
  · rw [ite_eq_left hf, map_smul, ← smul_sub, norm_smul]
    have hb := normalizedGradient_transverse_bound c q f s r hs hq hr (hrf f hf)
    have h := mul_le_mul_of_nonneg_left hb (norm_nonneg (g f))
    have hsq := pow_le_pow_left₀ (by positivity) h 2
    simpa only [mul_pow, mul_comm] using hsq
  · simp only [hf, ite_false, map_zero, sub_zero, norm_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    positivity

/-- This is the normalized low-gradient loss `2s²/r²` after multiplication
by `2t=1/32`; no approximate gradient basis is used. -/
theorem gradient_projection_lower
    (c q : Momentum) (low : Finset Frequency) (g : Coefficients) (s r : ℝ)
    (hs : 0 ≤ s) (hq : phaseScale*momentumNorm q ≤ s) (hr : 0 < r)
    (hrf : ∀ f ∈ low, r ≤ ‖longitudinalVector c f‖)
    (hg : ∀ f, f ∉ low → g f = 0) :
    (64-64*s^2/r^2)*‖g‖^2 ≤ ‖projector (c+q) (gradient c low g)‖^2 := by
  have hn := gradient_norm_sq c low g
    (fun f hf => norm_pos_iff.mp (hr.trans_le (hrf f hf))) hg
  have ht := pow_le_pow_left₀ (norm_nonneg _)
    (gradient_transverse_norm c q low g s r hs hq hr hrf) 2
  have hp := projector_pythagorean (c+q) (gradient c low g)
  rw [hn] at hp
  have heq : ((8*s/r)*‖g‖)^2 = (64*s^2/r^2)*‖g‖^2 := by ring
  rw [heq] at ht
  nlinarith

/-- The actual normalized gradient block satisfies the exact scalar loss
`lossg=2s²/r²+64σ` used by the global box certificate. -/
theorem auxiliary_gradient_lower
    (material : Cell20 → ℝ) (hm : ∀ e, 0 < PrimitiveYee.edgeAverage material e)
    (c q : Momentum) (low : Finset Frequency) (g : Coefficients) (s r σ t' : ℝ)
    (hs : 0 ≤ s) (hq : phaseScale*momentumNorm q ≤ s) (hr : 0 < r)
    (hrf : ∀ f ∈ low, r ≤ ‖longitudinalVector c f‖)
    (hg : ∀ f, f ∉ low → g f = 0) (ht' : t' ≤ 1/64+σ) :
    (1-(2*s^2/r^2+64*σ))*‖g‖^2 ≤
      (inner ℂ (gradient c low g)
        ((auxiliaryMagneticFourier material (c+q) (1/64) t').toEuclideanLin
          (gradient c low g))).re := by
  have hproj := gradient_projection_lower c q low g s r hs hq hr hrf hg
  have hn := gradient_norm_sq c low g
    (fun f hf => norm_pos_iff.mp (hr.trans_le (hrf f hf))) hg
  have haux := BoxHighCoercivity.auxiliary_projection_lower material (c+q) (1/64) t'
    hm (gradient c low g)
  rw [hn] at haux
  have ht := mul_le_mul_of_nonneg_right ht' (by positivity : 0 ≤ 64*‖g‖^2)
  have hid : (1/32 : ℝ)*((64-64*s^2/r^2)*‖g‖^2) - (1/64+σ)*(64*‖g‖^2) =
      (1-(2*s^2/r^2+64*σ))*‖g‖^2 := by ring
  nlinarith

/-- The low-frequency mixed projection error is controlled by the actual
weighted positive witness, with no loss depending on the number of modes. -/
theorem mixed_projection_remainder
    (c q : Momentum) (low : Finset Frequency) (x : FourierSpace) (g : Coefficients)
    (hx : x ∈ transverseSubspace c) (s r R : ℝ)
    (hs : 0 ≤ s) (hq : phaseScale*momentumNorm q ≤ s) (hsr : s < r)
    (hr : ∀ f ∈ low, r ≤ ‖longitudinalVector c f‖)
    (hR : ∀ f ∈ low, ‖longitudinalVector c f‖ ≤ R) (hR0 : 0 ≤ R) :
    ‖inner ℂ x (projector (c+q) (gradient c low g)-gradientLinear c q low g)‖ ≤
      8*s^2*((3+s/r)/(1-s/r)^2+(1/2)*R/(1-s/r))*
        ‖scalarWeight (lowInverseLaplacian c low) x‖*‖g‖ := by
  let K := 8*s^2*((3+s/r)/(1-s/r)^2+(1/2)*R/(1-s/r))
  have hr0 : 0 < r := hs.trans_lt hsr
  have hratio : 0 < 1-s/r := sub_pos.mpr ((div_lt_one hr0).mpr hsr)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpoint (f : Frequency) :
      ‖inner ℂ (frequencyComponent f x)
        (frequencyComponent f (projector (c+q) (gradient c low g)-gradientLinear c q low g))‖ ≤
      K*‖frequencyComponent f (scalarWeight (lowInverseLaplacian c low) x)‖*‖g f‖ := by
    rw [map_sub, projector_component, gradient_component, gradientLinear_component]
    by_cases hf : f ∈ low
    · rw [ite_eq_left hf, ite_eq_left hf, map_smul, ← smul_sub, inner_smul_right, norm_mul]
      have hb := normalizedGradient_mixed_remainder c q f (frequencyComponent f x)
        (hx f) s r R hs hq hsr (hr f hf) (hR f hf)
      have hw : ‖frequencyComponent f (scalarWeight (lowInverseLaplacian c low) x)‖ =
          ‖frequencyComponent f x‖/‖longitudinalVector c f‖^2 := by
        rw [scalarWeight_component, norm_smul, Complex.norm_real, Real.norm_eq_abs]
        simp only [lowInverseLaplacian, ite_eq_left hf]
        rw [abs_of_nonneg (by positivity)]
        ring
      rw [hw]
      have h := mul_le_mul_of_nonneg_left hb (norm_nonneg (g f))
      simpa only [K, mul_comm, mul_left_comm, mul_assoc] using h
    · simp only [hf, ite_false, map_zero, sub_zero, inner_zero_right, norm_zero]
      positivity
  rw [inner_eq_sum_components]
  calc
    _ ≤ ∑ f, ‖inner ℂ (frequencyComponent f x)
        (frequencyComponent f (projector (c+q) (gradient c low g)-gradientLinear c q low g))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ f, K*‖frequencyComponent f (scalarWeight (lowInverseLaplacian c low) x)‖*‖g f‖ :=
      Finset.sum_le_sum (fun f _ => hpoint f)
    _ = K*(∑ f, ‖frequencyComponent f (scalarWeight (lowInverseLaplacian c low) x)‖*‖g f‖) := by
      simp only [mul_assoc, Finset.mul_sum]
    _ ≤ K*(‖scalarWeight (lowInverseLaplacian c low) x‖*‖g‖) :=
      mul_le_mul_of_nonneg_left (weighted_cauchy _ g) hK
    _ = _ := by dsimp [K]; ring

end
end Maxwell.Spectral.BoxGradient
