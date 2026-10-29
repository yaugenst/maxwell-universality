import Maxwell.Spectral.BoxFourierProjection
import Maxwell.Spectral.BoxCrossNorm
import Maxwell.Certificate.FourierAuxiliaryInertia

namespace Maxwell.Spectral.BoxProjectionAssembly

open Maxwell.Certificate.FourierBinding Maxwell.Spectral.PeriodicYee
open Maxwell.Spectral.PrimitiveYee BoxFourierProjection BoxSymbols BoxProjection

noncomputable section

def scalarWeightLinear (w : Frequency → ℝ) : FourierSpace →ₗ[ℂ] FourierSpace where
  toFun x := WithLp.toLp 2 (fun e => (w e.2 : ℂ)*x e)
  map_add' x y := by
    ext e
    change (w e.2 : ℂ)*(x e+y e) = (w e.2 : ℂ)*x e+(w e.2 : ℂ)*y e
    ring
  map_smul' a x := by
    ext e
    change (w e.2 : ℂ)*(a*x e) = a*((w e.2 : ℂ)*x e)
    ring

def scalarWeight (w : Frequency → ℝ) : FourierSpace →L[ℂ] FourierSpace :=
  (scalarWeightLinear w).toContinuousLinearMap

theorem scalarWeight_component (w : Frequency → ℝ) (x : FourierSpace) (f : Frequency) :
    frequencyComponent f (scalarWeight w x) = (w f : ℂ) • frequencyComponent f x := rfl

def projector (c : Momentum) : FourierSpace →L[ℂ] FourierSpace :=
  Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ) (longitudinalProjectionMatrix c)

theorem projector_component (c : Momentum) (x : FourierSpace) (f : Frequency) :
    frequencyComponent f (projector c x) = gradientProjection c f (frequencyComponent f x) :=
  longitudinalProjection_component c f x

theorem projector_pythagorean (c : Momentum) (x : FourierSpace) :
    ‖x‖^2 = ‖projector c x‖^2+‖x-projector c x‖^2 := by
  rw [BoxCrossNorm.frequency_norm_sq_eq_sum, BoxCrossNorm.frequency_norm_sq_eq_sum,
    BoxCrossNorm.frequency_norm_sq_eq_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro f _
  rw [map_sub, projector_component, gradientProjection_eq_projection]
  exact projection_pythagorean (longitudinalVector c f) (frequencyComponent f x)

def linearProjectorLinear (c q : Momentum) : FourierSpace →ₗ[ℂ] FourierSpace where
  toFun x := WithLp.toLp 2 (fun e =>
    transverseLinearTerm (longitudinalVector c e.2) (longitudinalLinear c q e.2)
      (frequencyComponent e.2 x) e.1)
  map_add' x y := by ext e; simp [map_add]
  map_smul' a x := by ext e; simp [map_smul]

def linearProjector (c q : Momentum) : FourierSpace →L[ℂ] FourierSpace :=
  (linearProjectorLinear c q).toContinuousLinearMap

theorem linearProjector_component (c q : Momentum) (x : FourierSpace) (f : Frequency) :
    frequencyComponent f (linearProjector c q x) =
      transverseLinearTerm (longitudinalVector c f) (longitudinalLinear c q f)
        (frequencyComponent f x) := rfl

theorem norm_le_of_component_bounds (u v : FourierSpace)
    (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ f, ‖frequencyComponent f u‖ ≤ B*‖frequencyComponent f v‖) :
    ‖u‖ ≤ B*‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))).mp
  rw [BoxCrossNorm.frequency_norm_sq_eq_sum, mul_pow,
    BoxCrossNorm.frequency_norm_sq_eq_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro f _
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (h f) 2

theorem scalarWeight_norm_bound (w : Frequency → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hw : ∀ f, |w f| ≤ B) (x : FourierSpace) :
    ‖scalarWeight w x‖ ≤ B*‖x‖ := by
  apply norm_le_of_component_bounds _ _ _ hB
  intro f
  rw [scalarWeight_component, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hw f) (norm_nonneg _)

theorem scalarWeight_comparison (w v : Frequency → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hw : ∀ f, |w f| ≤ B*|v f|) (x : FourierSpace) :
    ‖scalarWeight w x‖ ≤ B*‖scalarWeight v x‖ := by
  apply norm_le_of_component_bounds _ _ _ hB
  intro f
  rw [scalarWeight_component, scalarWeight_component, norm_smul, norm_smul,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
  have h := mul_le_mul_of_nonneg_right (hw f) (norm_nonneg (frequencyComponent f x))
  simpa only [mul_assoc] using h

/-- Component estimates assemble in the actual Fourier Hilbert norm,
including arbitrary scalar weights and their zero-frequency masks. -/
theorem weighted_of_component_bounds (w : Frequency → ℝ) (u v : FourierSpace)
    (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ f, w f ≠ 0 → ‖frequencyComponent f u‖ ≤ B*‖frequencyComponent f v‖) :
    ‖scalarWeight w u‖ ≤ B*‖scalarWeight w v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))).mp
  rw [BoxCrossNorm.frequency_norm_sq_eq_sum, mul_pow,
    BoxCrossNorm.frequency_norm_sq_eq_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro f _
  rw [scalarWeight_component, scalarWeight_component, norm_smul, norm_smul]
  by_cases hw : w f = 0
  · simp [hw]
  · have hf := mul_le_mul_of_nonneg_left (h f hw) (norm_nonneg (w f : ℂ))
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ ‖(w f : ℂ)‖*‖frequencyComponent f u‖) hf 2
    convert hs using 1; ring

/-- The high-frequency weighted projector remainder has exactly the
frequency-independent coefficient used by the scalar verifier. -/
theorem weighted_transverse_projection_remainder
    (c q : Momentum) (w : Frequency → ℝ) (x : FourierSpace)
    (hx : x ∈ transverseSubspace c) (s r : ℝ)
    (hs : 0 ≤ s) (hq : phaseScale*momentumNorm q ≤ s) (hsr : s < r)
    (hr : ∀ f, w f ≠ 0 → r ≤ ‖longitudinalVector c f‖) :
    ‖scalarWeight w (projector (c+q) x-linearProjector c q x)‖ ≤
      s^2*((r/2+3+s/r)/(r-s)^2)*‖scalarWeight w x‖ := by
  apply weighted_of_component_bounds
  · have hr0 : 0 < r := hs.trans_lt hsr
    positivity
  · intro f hf
    rw [map_sub, projector_component, linearProjector_component]
    exact transverse_projection_remainder_uniform c q f (frequencyComponent f x)
      (hx f) s r hs hq hsr (hr f hf)

theorem weighted_transverse_projection_bound
    (c q : Momentum) (w : Frequency → ℝ) (x : FourierSpace)
    (hx : x ∈ transverseSubspace c) (s r : ℝ)
    (hs : 0 ≤ s) (hq : phaseScale*momentumNorm q ≤ s) (hsr : s < r)
    (hr : ∀ f, w f ≠ 0 → r ≤ ‖longitudinalVector c f‖) :
    ‖scalarWeight w (projector (c+q) x)‖ ≤ (s/(r-s))*‖scalarWeight w x‖ := by
  apply weighted_of_component_bounds w _ _ _ (div_nonneg hs (sub_pos.mpr hsr).le)
  intro f hf
  rw [projector_component]
  apply (transverse_projection_bound c q f (frequencyComponent f x)
    (hx f) s hs hq (hsr.trans_le (hr f hf))).trans
  gcongr
  exact hr f hf

/-- The center inverse-Laplacian weight is retained exactly. Its certified
Gram bound is `wn` in the negative-block test. -/
theorem transverse_projection_weighted_norm
    (c q : Momentum) (x : FourierSpace) (hx : x ∈ transverseSubspace c)
    (s r : ℝ) (hs : 0 ≤ s) (hq : phaseScale*momentumNorm q ≤ s) (hsr : s < r)
    (hr : ∀ f, r ≤ ‖longitudinalVector c f‖) :
    ‖projector (c+q) x‖ ≤ (s/(1-s/r))*
      ‖scalarWeight (fun f => 1/‖longitudinalVector c f‖) x‖ := by
  have hr0 : 0 < r := hs.trans_lt hsr
  have hratio : 0 < 1-s/r := sub_pos.mpr ((div_lt_one hr0).mpr hsr)
  apply norm_le_of_component_bounds _ _ _ (div_nonneg hs hratio.le)
  intro f
  rw [projector_component, scalarWeight_component, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1/‖longitudinalVector c f‖)]
  have h := transverse_projection_weighted c q f (frequencyComponent f x) (hx f)
    s r hs hq hsr (hr f)
  simpa only [div_eq_mul_inv, one_mul, mul_comm] using h

end
end Maxwell.Spectral.BoxProjectionAssembly
