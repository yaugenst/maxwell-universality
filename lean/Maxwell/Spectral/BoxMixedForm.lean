import Maxwell.Spectral.BoxMagnetic
import Maxwell.Spectral.BoxGradient
import Maxwell.Spectral.BoxLinear

/-! The actual positive/gradient mixed block of the auxiliary box operator.
The spectral shift cancels by exact center orthogonality. -/

noncomputable section

namespace Maxwell.Spectral.BoxMixedForm

set_option maxRecDepth 4000

open Maxwell.Certificate.FourierBinding Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Direction Momentum Cell20)
open BoxMagnetic BoxGradient BoxFourierProjection BoxProjectionAssembly

def gradientOperator (c : Momentum) (low : Finset Frequency) : Coefficients →L[ℂ] Field :=
  LinearMap.toContinuousLinearMap {
    toFun := gradient c low
    map_add' := by
      intro g h
      ext e
      simp only [gradient, PiLp.add_apply]
      change (if e.2 ∈ low then (g e.2+h e.2)*_ else 0) =
        (if e.2 ∈ low then g e.2*_ else 0)+(if e.2 ∈ low then h e.2*_ else 0)
      split_ifs <;> ring
    map_smul' := by
      intro a g
      ext e
      change (if e.2 ∈ low then (a*g e.2)*_ else 0) =
        a*(if e.2 ∈ low then g e.2*_ else 0)
      split_ifs <;> ring }

def gradientLinearOperator (c q : Momentum) (low : Finset Frequency) :
    Coefficients →L[ℂ] Field :=
  LinearMap.toContinuousLinearMap {
    toFun := gradientLinear c q low
    map_add' := by
      intro g h
      ext e
      change (if e.2 ∈ low then (g e.2+h e.2)*_ else 0) =
        (if e.2 ∈ low then g e.2*_ else 0)+(if e.2 ∈ low then h e.2*_ else 0)
      split_ifs <;> ring
    map_smul' := by
      intro a g
      ext e
      change (if e.2 ∈ low then (a*g e.2)*_ else 0) =
        a*(if e.2 ∈ low then g e.2*_ else 0)
      split_ifs <;> ring }

theorem gradientOperator_apply (c : Momentum) (low : Finset Frequency) (g : Coefficients) :
    gradientOperator c low g = gradient c low g := rfl

theorem gradientLinearOperator_apply (c q : Momentum) (low : Finset Frequency)
    (g : Coefficients) : gradientLinearOperator c q low g = gradientLinear c q low g := rfl

theorem normalizedGradient_norm_le (c : Momentum) (f : Frequency) :
    ‖normalizedGradient c f‖ ≤ 8 := by
  by_cases hv : longitudinalVector c f = 0
  · simp [normalizedGradient, hv]
  · exact (normalizedGradient_norm c f hv).le

theorem gradientOperator_norm (c : Momentum) (low : Finset Frequency) :
    ‖gradientOperator c low‖ ≤ 8 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro g
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 8*‖g‖)).mp
  rw [gradientOperator_apply, BoxCrossNorm.frequency_norm_sq_eq_sum,
    mul_pow, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro f _
  rw [gradient_component]
  by_cases hf : f ∈ low
  · rw [ite_eq_left hf, norm_smul]
    have h := mul_le_mul_of_nonneg_left (normalizedGradient_norm_le c f) (norm_nonneg (g f))
    have hsq := pow_le_pow_left₀ (by positivity) h 2
    simpa only [mul_pow, mul_comm] using hsq
  · simp only [hf, ite_false, norm_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    positivity

theorem gradient_inner_zero (c : Momentum) (low : Finset Frequency)
    (x : FourierSpace) (hx : x ∈ transverseSubspace c) (g : Coefficients) :
    inner ℂ x (gradient c low g) = 0 := by
  rw [inner_eq_sum_components]
  apply Finset.sum_eq_zero
  intro f _
  rw [gradient_component]
  by_cases hf : f ∈ low
  · rw [ite_eq_left hf, inner_smul_right, normalizedGradient, inner_smul_right]
    have hz : inner ℂ (frequencyComponent f x) (longitudinalVector c f) = 0 := by
      rw [← inner_conj_symm, longitudinal_inner, show divergenceSymbol c f
        (frequencyComponent f x) = 0 from hx f, map_zero]
    rw [hz, mul_zero, mul_zero]
  · simp [hf]

theorem gradient_mem_orthogonal (c : Momentum) (low : Finset Frequency) (g : Coefficients) :
    gradient c low g ∈ (transverseSubspace c)ᗮ := by
  rw [Submodule.mem_orthogonal]
  exact fun x hx => gradient_inner_zero c low x hx g

theorem gradient_center_curl_zero (c : Momentum) (low : Finset Frequency) :
    appliedCurl c (gradientOperator c low) = 0 := by
  apply ContinuousLinearMap.ext
  intro g
  have hz := frequencyCurl_adjoint_longitudinal c
    ⟨gradient c low g, gradient_mem_orthogonal c low g⟩
  change (curlOperator c).adjoint (gradient c low g) = 0
  change (star (Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ) (frequencyCurl c))) _ = 0
  rw [← map_star]
  exact hz

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem gradient_cross_zero (c : Momentum) (low : Finset Frequency) (F : V →L[ℂ] Field)
    (htrans : ∀ x, F x ∈ transverseSubspace c) :
    F.adjoint.comp (gradientOperator c low) = 0 := by
  apply ContinuousLinearMap.ext
  intro g
  apply ext_inner_left ℂ
  intro x
  rw [zero_apply, inner_zero_right]
  change inner ℂ x (F.adjoint (gradient c low g)) = 0
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact gradient_inner_zero c low (F x) (htrans x) g

def mixedFirstCompression (material : Cell20 → ℝ) (c q : Momentum) (t : ℝ)
    (low : Finset Frequency) (F : V →L[ℂ] Field) : Coefficients →L[ℂ] V :=
  firstCompression material c q F (gradientOperator c low) +
    (2*t : ℂ) • F.adjoint.comp (gradientLinearOperator c q low)

theorem gradientLinearOperator_expansion (c q : Momentum) (low : Finset Frequency) :
    gradientLinearOperator c q low =
      ∑ j, (q j : ℂ) • gradientLinearOperator c (BoxLinear.axis j) low := by
  apply ContinuousLinearMap.ext
  intro g
  ext e
  change (if e.2 ∈ low then g e.2*normalizedGradientLinear c q e.2 e.1 else 0) =
    ∑ j, (q j : ℂ)*(if e.2 ∈ low then
      g e.2*normalizedGradientLinear c (BoxLinear.axis j) e.2 e.1 else 0)
  by_cases hf : e.2 ∈ low
  · simp only [hf, ite_true, normalizedGradientLinear, BoxFourierProjection.longitudinalLinear,
      PiLp.smul_apply, smul_eq_mul]
    rw [BoxLinear.linearSymbol_expansion]
    simp only [map_sum, map_mul, Complex.conj_ofReal]
    simp only [Fin.sum_univ_three]
    ring
  · simp [hf]

theorem mixedFirstCompression_expansion (material : Cell20 → ℝ) (c q : Momentum) (t : ℝ)
    (low : Finset Frequency) (F : V →L[ℂ] Field) :
    mixedFirstCompression material c q t low F =
      ∑ j, (q j : ℂ) • mixedFirstCompression material c (BoxLinear.axis j) t low F := by
  unfold mixedFirstCompression
  rw [BoxLinear.firstCompression_expansion, gradientLinearOperator_expansion]
  simp only [Fin.sum_univ_three, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_smul, smul_add, smul_smul]
  module

theorem mixedFirstCompression_box_bound (material : Cell20 → ℝ) (c q : Momentum) (t : ℝ)
    (low : Finset Frequency) (F : V →L[ℂ] Field) (h k : Direction → ℝ)
    (hh : ∀ j, |q j| ≤ h j)
    (hk : ∀ j, ‖mixedFirstCompression material c (BoxLinear.axis j) t low F‖ ≤ k j) :
    ‖mixedFirstCompression material c q t low F‖ ≤ ∑ j, h j*k j := by
  rw [mixedFirstCompression_expansion]
  exact BoxLinear.linear_combination_bound _ q h k hh hk

theorem center_compression_zero (material : Cell20 → ℝ) (c : Momentum) (t : ℝ)
    (low : Finset Frequency) (F : V →L[ℂ] Field)
    (htrans : ∀ x, F x ∈ transverseSubspace c) :
    compression material c t F (gradientOperator c low) = 0 := by
  rw [compression_sandwich, gradient_center_curl_zero, gradient_cross_zero c low F htrans]
  simp [BoxCompression.sandwich]

def projectionCrossCoefficient (s r R : ℝ) : ℝ :=
  (3+s/r)/(1-s/r)^2+(1/2)*R/(1-s/r)

theorem projectionCrossCoefficient_nonneg (s r R : ℝ)
    (hs : 0 ≤ s) (hsr : s < r) (hR : 0 ≤ R) :
    0 ≤ projectionCrossCoefficient s r R := by
  have hr : 0 < r := hs.trans_lt hsr
  have hd : 0 < 1-s/r := sub_pos.mpr ((div_lt_one hr).mpr hsr)
  unfold projectionCrossCoefficient
  positivity

omit [CompleteSpace V] in
theorem pairing_norm_le {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (T : W →L[ℂ] V) (b : ℝ) (hT : ‖T‖ ≤ b) (x : V) (g : W) :
    ‖inner ℂ x (T g)‖ ≤ b*‖x‖*‖g‖ := by
  calc
    _ ≤ ‖x‖*‖T g‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖*(‖T‖*‖g‖) := mul_le_mul_of_nonneg_left (T.le_opNorm g) (norm_nonneg _)
    _ ≤ ‖x‖*(b*‖g‖) := by gcongr
    _ = _ := by ring

theorem auxiliary_pairing (material : Cell20 → ℝ) (c : Momentum) (t t' : ℝ)
    (F : V →L[ℂ] Field) (y : Field) (x : V) :
    inner ℂ (F x) ((auxiliaryMagneticFourier material c t t').toEuclideanLin y) =
      inner ℂ x (F.adjoint ((shiftedMagneticFourier material c t').toEuclideanLin y)) +
        (2*t : ℂ)*inner ℂ (F x) (projector c y) := by
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp only [auxiliaryMagneticFourier, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, inner_add_right, inner_smul_right]
  rfl

/-- This identity has no spectral-shift remainder: the center compression
vanishes for every threshold, by exact transverse/gradient orthogonality. -/
theorem mixed_remainder_identity (material : Cell20 → ℝ) (c q : Momentum) (t t' : ℝ)
    (low : Finset Frequency) (F : V →L[ℂ] Field) (x : V) (g : Coefficients) :
    inner ℂ (F x) ((auxiliaryMagneticFourier material (c+q) t t').toEuclideanLin
        (gradient c low g)) =
      inner ℂ x (mixedFirstCompression material c q t low F g) +
      inner ℂ x ((compression material (c+q) t' F (gradientOperator c low) -
        firstCompression material c q F (gradientOperator c low)) g) +
      (2*t : ℂ)*inner ℂ (F x)
        (projector (c+q) (gradient c low g)-gradientLinear c q low g) := by
  rw [auxiliary_pairing]
  have hc : inner ℂ x (compression material (c+q) t' F (gradientOperator c low) g) =
      inner ℂ (F x) ((shiftedMagneticFourier material (c+q) t').toEuclideanLin
        (gradient c low g)) :=
    ContinuousLinearMap.adjoint_inner_right F x _
  simp only [mixedFirstCompression, add_apply, smul_apply, sub_apply,
    ContinuousLinearMap.comp_apply, gradientLinearOperator_apply,
    inner_add_right, inner_smul_right, inner_sub_right,
    ContinuousLinearMap.adjoint_inner_right]
  rw [hc]
  ring

/-- The exact source coefficient for the mixed positive/gradient block.
Only the combined first derivative and the center inverse-Laplacian
weighted witness norm remain as finite certificate inputs. -/
theorem auxiliary_mixed_norm
    (material : Cell20 → ℝ) (hm : ∀ edge, 1 ≤ edgeAverage material edge)
    (c q : Momentum) (t t' : ℝ) (low : Finset Frequency) (F : V →L[ℂ] Field)
    (s r R ν e wp2 dotcrossder : ℝ)
    (ht : 0 ≤ t) (hs : 0 ≤ s) (hq : displacementSize q ≤ s) (hsr : s < r)
    (hr : ∀ f ∈ low, r ≤ ‖longitudinalVector c f‖)
    (hR : ∀ f ∈ low, ‖longitudinalVector c f‖ ≤ R) (hR0 : 0 ≤ R)
    (hF : ‖F‖ ≤ ν) (hcenter : ‖appliedCurl c F‖ ≤ e)
    (htrans : ∀ x, F x ∈ transverseSubspace c)
    (hw : ‖(scalarWeight (lowInverseLaplacian c low)).comp F‖ ≤ wp2)
    (hfirst : ‖mixedFirstCompression material c q t low F‖ ≤ dotcrossder)
    (x : V) (g : Coefficients) :
    ‖inner ℂ (F x) ((auxiliaryMagneticFourier material (c+q) t t').toEuclideanLin
      (gradient c low g))‖ ≤
      (dotcrossder+s^2*(8*(e/2+ν)+16*t*projectionCrossCoefficient s r R*wp2))*‖x‖*‖g‖ := by
  have hν : 0 ≤ ν := (norm_nonneg _).trans hF
  have he : 0 ≤ e := (norm_nonneg _).trans hcenter
  have hq0 := displacementSize_nonneg q
  have hcp := projectionCrossCoefficient_nonneg s r R hs hsr hR0
  have hmag := BoxMagnetic.mixed_remainder_bound material hm c q t' F
    (gradientOperator c low) ν e 8 hν he (by norm_num) hF
    (gradientOperator_norm c low) hcenter (gradient_center_curl_zero c low)
  rw [center_compression_zero material c t' low F htrans, sub_zero] at hmag
  have hmag' : ‖compression material (c+q) t' F (gradientOperator c low)-
      firstCompression material c q F (gradientOperator c low)‖ ≤ 8*s^2*(e/2+ν) := by
    apply hmag.trans
    gcongr
  have hmagPair := pairing_norm_le _ _ hmag' x g
  have hlinear := pairing_norm_le _ _ hfirst x g
  have hp := mixed_projection_remainder c q low (F x) g (htrans x)
    s r R hs hq hsr hr hR hR0
  have hwx : ‖scalarWeight (lowInverseLaplacian c low) (F x)‖ ≤ wp2*‖x‖ :=
    ((scalarWeight (lowInverseLaplacian c low)).comp F).le_opNorm x |>.trans
      (mul_le_mul_of_nonneg_right hw (norm_nonneg _))
  have hp' : ‖inner ℂ (F x)
      (projector (c+q) (gradient c low g)-gradientLinear c q low g)‖ ≤
      8*s^2*projectionCrossCoefficient s r R*wp2*‖x‖*‖g‖ := by
    apply hp.trans
    change 8*s^2*projectionCrossCoefficient s r R* _ * _ ≤ _
    calc
      _ ≤ 8*s^2*projectionCrossCoefficient s r R*(wp2*‖x‖)*‖g‖ := by gcongr
      _ = _ := by ring
  have hscaled := mul_le_mul_of_nonneg_left hp' (by positivity : 0 ≤ 2*t)
  have htnorm : ‖(2*t : ℂ)‖ = 2*t := by
    rw [norm_mul, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  rw [mixed_remainder_identity]
  calc
    _ ≤ (‖inner ℂ x (mixedFirstCompression material c q t low F g)‖ +
        ‖inner ℂ x ((compression material (c+q) t' F (gradientOperator c low)-
          firstCompression material c q F (gradientOperator c low)) g)‖) +
        ‖(2*t : ℂ)*inner ℂ (F x)
          (projector (c+q) (gradient c low g)-gradientLinear c q low g)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ dotcrossder*‖x‖*‖g‖ + (8*s^2*(e/2+ν))*‖x‖*‖g‖ +
        (2*t)*(8*s^2*projectionCrossCoefficient s r R*wp2*‖x‖*‖g‖) := by
      rw [norm_mul, htnorm]
      exact add_le_add (add_le_add hlinear hmagPair) hscaled
    _ = _ := by ring

theorem auxiliary_mixed_form
    (material : Cell20 → ℝ) (hm : ∀ edge, 1 ≤ edgeAverage material edge)
    (c q : Momentum) (t t' : ℝ) (low : Finset Frequency) (F : V →L[ℂ] Field)
    (s r R ν e wp2 dotcrossder : ℝ)
    (ht : 0 ≤ t) (hs : 0 ≤ s) (hq : displacementSize q ≤ s) (hsr : s < r)
    (hr : ∀ f ∈ low, r ≤ ‖longitudinalVector c f‖)
    (hR : ∀ f ∈ low, ‖longitudinalVector c f‖ ≤ R) (hR0 : 0 ≤ R)
    (hF : ‖F‖ ≤ ν) (hcenter : ‖appliedCurl c F‖ ≤ e)
    (htrans : ∀ x, F x ∈ transverseSubspace c)
    (hw : ‖(scalarWeight (lowInverseLaplacian c low)).comp F‖ ≤ wp2)
    (hfirst : ‖mixedFirstCompression material c q t low F‖ ≤ dotcrossder)
    (x : V) (g : Coefficients) :
    |(inner ℂ (F x) ((auxiliaryMagneticFourier material (c+q) t t').toEuclideanLin
      (gradient c low g))).re| ≤
      (dotcrossder+s^2*(8*(e/2+ν)+16*t*projectionCrossCoefficient s r R*wp2))*‖x‖*‖g‖ :=
  (Complex.abs_re_le_norm _).trans
    (auxiliary_mixed_norm material hm c q t t' low F s r R ν e wp2 dotcrossder
      ht hs hq hsr hr hR hR0 hF hcenter htrans hw hfirst x g)

end Maxwell.Spectral.BoxMixedForm
