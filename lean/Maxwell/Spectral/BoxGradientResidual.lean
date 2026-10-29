import Maxwell.Spectral.BoxResidual
import Maxwell.Spectral.BoxResidualTransfer
import Maxwell.Spectral.BoxMixedForm

/-! The actual low-gradient high residual has no projector or spectral-shift
loss. Its dual high norm has no longitudinal leakage term. -/

noncomputable section

namespace Maxwell.Spectral.BoxGradientResidual

open Maxwell.Certificate.FourierBinding Maxwell.Spectral.PrimitiveYee
open Maxwell.Spectral.PeriodicYee (Direction Momentum Cell20)
open BoxMagnetic BoxGradient BoxMixedForm BoxProjectionAssembly
open BoxResidual BoxWeightAssembly BoxHighCoercivity

theorem gradient_restriction_zero (c : Momentum) (low support : Finset Frequency)
    (hdisjoint : Disjoint support low) (g : Coefficients) :
    frequencyRestriction support (gradient c low g) = 0 := by
  ext e
  change (if e.2 ∈ support then
    (if e.2 ∈ low then g e.2*BoxFourierProjection.normalizedGradient c e.2 e.1 else 0)
      else 0) = 0
  by_cases he : e.2 ∈ support
  · have hn : e.2 ∉ low := Finset.disjoint_left.mp hdisjoint he
    simp [he, hn]
  · simp [he]

theorem gradient_restrictOperator_zero (c : Momentum) (low support : Finset Frequency)
    (hdisjoint : Disjoint support low) :
    (restrictOperator support).comp (gradientOperator c low) = 0 := by
  apply ContinuousLinearMap.ext
  intro g
  exact gradient_restriction_zero c low support hdisjoint g

/-- Every longitudinal projector is frequency diagonal, even away from
the center momentum used to define the gradient columns. -/
theorem gradient_projector_restriction_zero (c k : Momentum) (low support : Finset Frequency)
    (hdisjoint : Disjoint support low) (g : Coefficients) :
    frequencyRestriction support (projector k (gradient c low g)) = 0 := by
  change frequencyRestriction support (longitudinalPart k (gradient c low g)) = 0
  rw [← longitudinalPart_restriction, gradient_restriction_zero c low support hdisjoint, map_zero]

theorem gradient_weight_zero (c : Momentum) (low support : Finset Frequency)
    (hdisjoint : Disjoint support low) (w : Frequency → ℝ)
    (hw : ∀ f, f ∉ support → w f = 0) :
    (scalarWeight w).comp (gradientOperator c low) = 0 := by
  rw [← scalarWeight_comp_restrict support w hw, ContinuousLinearMap.comp_assoc,
    gradient_restrictOperator_zero c low support hdisjoint, ContinuousLinearMap.comp_zero]

theorem gradient_projector_weight_zero (c k : Momentum) (low support : Finset Frequency)
    (hdisjoint : Disjoint support low) (w : Frequency → ℝ)
    (hw : ∀ f, f ∉ support → w f = 0) :
    (scalarWeight w).comp ((projector k).comp (gradientOperator c low)) = 0 := by
  have hz : (restrictOperator support).comp ((projector k).comp (gradientOperator c low)) = 0 := by
    apply ContinuousLinearMap.ext
    intro g
    exact gradient_projector_restriction_zero c k low support hdisjoint g
  rw [← scalarWeight_comp_restrict support w hw, ContinuousLinearMap.comp_assoc,
    hz, ContinuousLinearMap.comp_zero]

theorem gradient_center_magnetic_zero (material : Cell20 → ℝ) (c : Momentum)
    (low : Finset Frequency) : magneticAction material c (gradientOperator c low) = 0 := by
  simp only [magneticAction, gradient_center_curl_zero, ContinuousLinearMap.comp_zero]

theorem weighted_gradient_auxiliary_eq (material : Cell20 → ℝ) (c k : Momentum) (t t' : ℝ)
    (low support : Finset Frequency) (hdisjoint : Disjoint support low)
    (w : Frequency → ℝ) (hw : ∀ f, f ∉ support → w f = 0) :
    (scalarWeight w).comp (auxiliaryAction material k t t' (gradientOperator c low)) =
      (scalarWeight w).comp (magneticAction material k (gradientOperator c low)) := by
  rw [auxiliaryAction_eq]
  simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_smul,
    gradient_projector_weight_zero c k low support hdisjoint w hw,
    gradient_weight_zero c low support hdisjoint w hw]
  module

theorem weighted_gradient_first_box_bound (material : Cell20 → ℝ) (c q : Momentum)
    (low : Finset Frequency) (W : Field →L[ℂ] Field) (h k : Direction → ℝ)
    (hh : ∀ j, |q j| ≤ h j)
    (hk : ∀ j, ‖W.comp (firstMagneticAction material c (BoxLinear.axis j)
      (gradientOperator c low))‖ ≤ k j) :
    ‖W.comp (firstMagneticAction material c q (gradientOperator c low))‖ ≤ ∑ j, h j*k j := by
  have hb := BoxLinear.linear_combination_bound _ q h k hh hk
  rw [firstMagneticAction_expansion]
  simpa only [Fin.sum_univ_three, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_smul] using hb

/-- The fixed-weight gradient residual consists of the three checked
magnetic derivatives and the actual curl-sandwich remainder. -/
theorem weighted_gradient_box_bound
    (material : Cell20 → ℝ) (hm : ∀ e, 1 ≤ edgeAverage material e)
    (c q : Momentum) (t t' s ν e wmax curlmax : ℝ)
    (low support : Finset Frequency) (hdisjoint : Disjoint support low)
    (w : Frequency → ℝ) (hw : ∀ f, f ∉ support → w f = 0)
    (h k : Direction → ℝ) (hh : ∀ j, |q j| ≤ h j)
    (hk : ∀ j, ‖(scalarWeight w).comp
      (firstMagneticAction material c (BoxLinear.axis j) (gradientOperator c low))‖ ≤ k j)
    (hs : displacementSize q ≤ s) (hν : 8 ≤ ν) (he : 0 ≤ e)
    (hW : ‖scalarWeight w‖ ≤ wmax)
    (hWC : ‖(scalarWeight w).comp (curlOperator c)‖ ≤ curlmax) :
    ‖(scalarWeight w).comp (auxiliaryAction material (c+q) t t' (gradientOperator c low))‖ ≤
      (∑ j, h j*k j)+s^2*(wmax*e/2+(curlmax/2+wmax)*ν) := by
  have hcenter : ‖appliedCurl c (gradientOperator c low)‖ ≤ e := by
    rw [gradient_center_curl_zero, norm_zero]
    exact he
  have hmag := BoxMagneticWeighted.actual_weighted_remainder_bound_of_displacement
    material hm c q (gradientOperator c low) (scalarWeight w) s ν e wmax curlmax hs
    ((gradientOperator_norm c low).trans hν) hcenter hW hWC
  change ‖(scalarWeight w).comp (magneticAction material (c+q) (gradientOperator c low))-
    (scalarWeight w).comp (magneticAction material c (gradientOperator c low))-
    ((scalarWeight w).comp ((linearCurlOperator c q).comp
      ((inverseMaterial material).comp (appliedCurl c (gradientOperator c low))))+
      (scalarWeight w).comp ((curlOperator c).comp
        ((inverseMaterial material).comp (appliedLinear c q (gradientOperator c low)))))‖ ≤ _ at hmag
  have hr : ‖(scalarWeight w).comp (magneticAction material (c+q) (gradientOperator c low))-
      (scalarWeight w).comp (firstMagneticAction material c q (gradientOperator c low))‖ ≤
        s^2*(wmax*e/2+(curlmax/2+wmax)*ν) := by
    simpa only [firstMagneticAction, ContinuousLinearMap.comp_add,
      gradient_center_magnetic_zero, ContinuousLinearMap.comp_zero, sub_zero] using hmag
  have hfirst := weighted_gradient_first_box_bound material c q low (scalarWeight w) h k hh hk
  rw [weighted_gradient_auxiliary_eq material c (c+q) t t' low support hdisjoint w hw]
  have hid : (scalarWeight w).comp (magneticAction material (c+q) (gradientOperator c low)) =
      (scalarWeight w).comp (firstMagneticAction material c q (gradientOperator c low))+
      ((scalarWeight w).comp (magneticAction material (c+q) (gradientOperator c low))-
        (scalarWeight w).comp (firstMagneticAction material c q (gradientOperator c low))) := by module
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add hfirst hr)

/-- The source gradient residual bound with the exact moving-weight factor.
All operator inputs are the three finite center derivative norms. -/
theorem moving_gradient_box_bound
    (material : Cell20 → ℝ) (hm : ∀ e, 1 ≤ edgeAverage material e)
    (c q : Momentum) (ρ t t' σ s r ν e : ℝ)
    (low support : Finset Frequency) (hdisjoint : Disjoint support low)
    (h k : Direction → ℝ) (hh : ∀ j, |q j| ≤ h j)
    (hk : ∀ j, ‖(scalarWeight (inverseWeight support c ρ t)).comp
      (firstMagneticAction material c (BoxLinear.axis j) (gradientOperator c low))‖ ≤ k j)
    (hρ : 0 < ρ) (ht : 0 ≤ t) (hσ : 0 ≤ σ) (hs : 0 ≤ s)
    (hq : displacementSize q ≤ s) (hsr : s < r)
    (hr : ∀ f ∈ support, r ≤ ‖longitudinalVector c f‖)
    (ht' : t' ≤ t+σ) (hbase : 0 < r^2/ρ-t) (hnew : 0 < (r-s)^2/ρ-t-σ)
    (hν : 8 ≤ ν) (he : 0 ≤ e) :
    let wmax := 1/Real.sqrt (r^2/ρ-t)
    let curlmax := r/Real.sqrt (r^2/ρ-t)
    ‖(scalarWeight (inverseWeight support (c+q) ρ t')).comp
      (auxiliaryAction material (c+q) t t' (gradientOperator c low))‖ ≤
      Real.sqrt ((r^2/ρ-t)/((r-s)^2/ρ-t-σ))*
        ((∑ j, h j*k j)+s^2*(wmax*e/2+(curlmax/2+wmax)*ν)) := by
  dsimp only
  apply moving_weight_bound support c q ρ t σ s r t' _ _
    hρ ht hσ hs hq hsr hr ht' hnew
  exact weighted_gradient_box_bound material hm c q t t' s ν e
    (1/Real.sqrt (r^2/ρ-t)) (r/Real.sqrt (r^2/ρ-t)) low support hdisjoint
    (inverseWeight support c ρ t) (by intro f hf; simp [inverseWeight, hf]) h k hh hk hq hν he
    (inverseWeight_norm support c ρ t r hρ (hs.trans_lt hsr) hbase hr)
    (inverseWeight_curl_norm support c ρ t r hρ ht (hs.trans_lt hsr) hbase hr)

/-- If the input has no high-frequency coordinates, the exact auxiliary
residual has no high longitudinal part. No transverse hypothesis on the
input is needed. -/
theorem dual_residual_norm_le_of_restriction_zero
    (material : Cell20 → ℝ) (c : Momentum) (support : Finset Frequency) (ρ t t' : ℝ)
    (ha : 0 < 2*t-t') (x : FourierSpace) (hx : frequencyRestriction support x = 0) :
    ‖inverseWeightedParts c (highWeight support c ρ t') (2*t-t')
      (frequencyRestriction support ((auxiliaryMagneticFourier material c t t').toEuclideanLin x))‖ ≤
    ‖scalarWeight (inverseWeight support c ρ t')
      ((auxiliaryMagneticFourier material c t t').toEuclideanLin x)‖ := by
  have hid := inverseWeightedParts_residual_norm_sq material c support
    (highWeight support c ρ t') t t' ha x
  rw [hx, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hid
  have heq := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hid
  rw [heq]
  exact BoxResidualTransfer.transverse_residual_norm_le support c ρ t' _

theorem gradient_dual_residual_bound
    (material : Cell20 → ℝ) (c k : Momentum) (low support : Finset Frequency)
    (hdisjoint : Disjoint support low) (ρ t t' rw : ℝ) (ha : 0 < 2*t-t')
    (hR : ‖(scalarWeight (inverseWeight support k ρ t')).comp
      (auxiliaryAction material k t t' (gradientOperator c low))‖ ≤ rw)
    (g : Coefficients) :
    ‖inverseWeightedParts k (highWeight support k ρ t') (2*t-t')
      (frequencyRestriction support ((auxiliaryMagneticFourier material k t t').toEuclideanLin
        (gradient c low g)))‖ ≤ rw*‖g‖ := by
  apply (dual_residual_norm_le_of_restriction_zero material k support ρ t t' ha _
    (gradient_restriction_zero c low support hdisjoint g)).trans
  exact (((scalarWeight (inverseWeight support k ρ t')).comp
    (auxiliaryAction material k t t' (gradientOperator c low))).le_opNorm g).trans
      (mul_le_mul_of_nonneg_right hR (norm_nonneg g))

/-- The actual gradient/high Schur coupling has coefficient `rw`, exactly:
the zero high support eliminates the additional longitudinal leakage loss. -/
theorem gradient_high_coupling_of_scalarWeight
    (material : Cell20 → ℝ) (c k : Momentum) (low support : Finset Frequency)
    (hdisjoint : Disjoint support low) (ρ t t' rw : ℝ) (ha : 0 < 2*t-t')
    (hw : ∀ f ∈ support, 0 < laplacianSymbol k f/ρ-t')
    (hR : ‖(scalarWeight (inverseWeight support k ρ t')).comp
      (auxiliaryAction material k t t' (gradientOperator c low))‖ ≤ rw)
    (g : Coefficients) (y : FourierSpace)
    (hy : ∀ f, f ∉ support → ∀ j, y (j,f) = 0) :
    |(inner ℂ (gradient c low g)
      ((auxiliaryMagneticFourier material k t t').toEuclideanLin y)).re| ≤
      rw*‖g‖*‖weightedParts k (highWeight support k ρ t') (2*t-t') y‖ :=
  auxiliary_high_coupling material k support (highWeight support k ρ t') t t' rw ‖g‖
    (highWeight_pos support k ρ t' hw) ha _ y hy
    (gradient_dual_residual_bound material c k low support hdisjoint ρ t t' rw ha hR g)

end Maxwell.Spectral.BoxGradientResidual
