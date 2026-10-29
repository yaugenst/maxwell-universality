import Maxwell.Spectral.BoxMagneticWeighted
import Maxwell.Spectral.BoxWeightAssembly
import Maxwell.Spectral.BoxLinear

namespace Maxwell.Spectral.BoxResidual

open Maxwell.Certificate.FourierBinding Maxwell.Spectral.PeriodicYee
open Maxwell.Spectral.PrimitiveYee BoxMagnetic BoxProjectionAssembly
open BoxFourierProjection BoxLinear BoxSymbols

noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def magneticAction (material : Cell20 → ℝ) (c : Momentum) (F : V →L[ℂ] Field) : V →L[ℂ] Field :=
  (curlOperator c).comp ((inverseMaterial material).comp (appliedCurl c F))

def firstMagneticAction (material : Cell20 → ℝ) (c q : Momentum)
    (F : V →L[ℂ] Field) : V →L[ℂ] Field :=
  (linearCurlOperator c q).comp ((inverseMaterial material).comp (appliedCurl c F)) +
    (curlOperator c).comp ((inverseMaterial material).comp (appliedLinear c q F))

def auxiliaryAction (material : Cell20 → ℝ) (c : Momentum) (t t' : ℝ)
    (F : V →L[ℂ] Field) : V →L[ℂ] Field :=
  (Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
    (auxiliaryMagneticFourier material c t t')).comp F

theorem auxiliaryAction_eq (material : Cell20 → ℝ) (c : Momentum) (t t' : ℝ)
    (F : V →L[ℂ] Field) :
    auxiliaryAction material c t t' F = magneticAction material c F +
      (2*t : ℂ) • (projector c).comp F-(t' : ℂ) • F := by
  have hs := compression_sandwich material c t'
    (1 : Field →L[ℂ] Field) F
  simp only [compression, appliedCurl, BoxCompression.sandwich,
    ContinuousLinearMap.adjoint_id, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
    ContinuousLinearMap.comp_id, ContinuousLinearMap.adjoint_adjoint] at hs
  unfold auxiliaryAction auxiliaryMagneticFourier
  rw [map_add, map_smul, ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp, hs]
  simp only [magneticAction, appliedCurl, projector]
  module

def firstAuxiliaryAction (material : Cell20 → ℝ) (c q : Momentum) (t : ℝ)
    (F : V →L[ℂ] Field) : V →L[ℂ] Field :=
  firstMagneticAction material c q F+(2*t : ℂ) • (linearProjector c q).comp F

theorem longitudinalLinear_expansion (c q : Momentum) (f : Frequency) :
    longitudinalLinear c q f = ∑ j, (q j : ℂ) • longitudinalLinear c (axis j) f := by
  ext a
  change (starRingEnd ℂ) (linearSymbol c q f a) =
    ∑ j, (q j : ℂ)*(starRingEnd ℂ) (linearSymbol c (axis j) f a)
  rw [linearSymbol_expansion c q f a]
  simp only [map_sum, map_mul, Complex.conj_ofReal]

theorem linearProjector_expansion (c q : Momentum) :
    linearProjector c q = ∑ j, (q j : ℂ) • linearProjector c (axis j) := by
  apply ContinuousLinearMap.ext
  intro x
  ext e
  change (BoxProjection.transverseLinearTerm (longitudinalVector c e.2)
    (longitudinalLinear c q e.2) (frequencyComponent e.2 x)) e.1 =
    ∑ j, (q j : ℂ)*(BoxProjection.transverseLinearTerm (longitudinalVector c e.2)
      (longitudinalLinear c (axis j) e.2) (frequencyComponent e.2 x)) e.1
  rw [longitudinalLinear_expansion c q e.2]
  simp only [BoxProjection.transverseLinearTerm_apply, Fin.sum_univ_three, inner_add_left,
    inner_smul_left, Complex.conj_ofReal, PiLp.smul_apply, smul_eq_mul]
  ring

theorem firstMagneticAction_expansion (material : Cell20 → ℝ) (c q : Momentum)
    (F : V →L[ℂ] Field) :
    firstMagneticAction material c q F =
      ∑ j, (q j : ℂ) • firstMagneticAction material c (axis j) F := by
  unfold firstMagneticAction
  rw [linearCurlOperator_expansion c q, appliedLinear_expansion c q F]
  simp only [Fin.sum_univ_three, ContinuousLinearMap.add_comp,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_smul]
  module

theorem firstAuxiliaryAction_expansion (material : Cell20 → ℝ) (c q : Momentum) (t : ℝ)
    (F : V →L[ℂ] Field) :
    firstAuxiliaryAction material c q t F =
      ∑ j, (q j : ℂ) • firstAuxiliaryAction material c (axis j) t F := by
  unfold firstAuxiliaryAction
  rw [firstMagneticAction_expansion material c q F, linearProjector_expansion c q]
  simp only [Fin.sum_univ_three, ContinuousLinearMap.add_comp,
    ContinuousLinearMap.smul_comp]
  module

theorem weighted_firstAuxiliaryAction_box_bound (material : Cell20 → ℝ)
    (c q : Momentum) (t : ℝ) (F : V →L[ℂ] Field) (W : Field →L[ℂ] Field)
    (h k : Direction → ℝ) (hh : ∀ j, |q j| ≤ h j)
    (hk : ∀ j, ‖W.comp (firstAuxiliaryAction material c (axis j) t F)‖ ≤ k j) :
    ‖W.comp (firstAuxiliaryAction material c q t F)‖ ≤ ∑ j, h j*k j := by
  have hb := linear_combination_bound _ q h k hh hk
  rw [firstAuxiliaryAction_expansion material c q t F]
  simpa only [Fin.sum_univ_three, ContinuousLinearMap.comp_add,
    ContinuousLinearMap.comp_smul] using hb

def restrictOperator (support : Finset Frequency) : Field →L[ℂ] Field :=
  (frequencyRestriction support).toContinuousLinearMap

theorem scalarWeight_comp_restrict (support : Finset Frequency) (w : Frequency → ℝ)
    (hw : ∀ f, f ∉ support → w f = 0) :
    (scalarWeight w).comp (restrictOperator support) = scalarWeight w := by
  apply ContinuousLinearMap.ext
  intro x
  ext e
  change (w e.2 : ℂ)*(if e.2 ∈ support then x e else 0) = (w e.2 : ℂ)*x e
  by_cases he : e.2 ∈ support
  · simp [he]
  · simp [he, hw e.2 he]

theorem weighted_restriction_bound (support : Finset Frequency) (w : Frequency → ℝ)
    (hw : ∀ f, f ∉ support → w f = 0) (F : V →L[ℂ] Field)
    (wmax qfn : ℝ) (hW : ‖scalarWeight w‖ ≤ wmax)
    (hF : ‖(restrictOperator support).comp F‖ ≤ qfn) :
    ‖(scalarWeight w).comp F‖ ≤ wmax*qfn := by
  rw [← scalarWeight_comp_restrict support w hw, ContinuousLinearMap.comp_assoc]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  exact mul_le_mul hW hF (norm_nonneg _) ((norm_nonneg _).trans hW)

theorem projector_comp_zero (c : Momentum) (F : V →L[ℂ] Field)
    (hF : ∀ x, F x ∈ transverseSubspace c) : (projector c).comp F = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  exact longitudinalProjection_transverse c (F x) (hF x)

theorem auxiliary_remainder_identity
    (material : Cell20 → ℝ) (c q : Momentum) (t t' : ℝ) (F : V →L[ℂ] Field)
    (hF : ∀ x, F x ∈ transverseSubspace c) :
    auxiliaryAction material (c+q) t t' F-auxiliaryAction material c t t F-
      firstAuxiliaryAction material c q t F =
    (magneticAction material (c+q) F-magneticAction material c F-
      firstMagneticAction material c q F) +
      (2*t : ℂ) • ((projector (c+q)).comp F-(linearProjector c q).comp F) -
      ((t'-t : ℝ) : ℂ) • F := by
  rw [auxiliaryAction_eq, auxiliaryAction_eq, projector_comp_zero c F hF]
  simp only [firstAuxiliaryAction]
  push_cast
  module

theorem weighted_auxiliary_remainder_bound
    (material : Cell20 → ℝ) (hm : ∀ e, 1 ≤ PrimitiveYee.edgeAverage material e)
    (c q : Momentum) (t t' σ s ν e wmax curlmax pR qw : ℝ)
    (F : V →L[ℂ] Field) (W : Field →L[ℂ] Field)
    (htrans : ∀ x, F x ∈ transverseSubspace c)
    (ht : 0 ≤ t) (hshift : |t'-t| ≤ σ) (hs : displacementSize q ≤ s)
    (hF : ‖F‖ ≤ ν) (hcenter : ‖appliedCurl c F‖ ≤ e)
    (hW : ‖W‖ ≤ wmax) (hWC : ‖W.comp (curlOperator c)‖ ≤ curlmax)
    (hP : ‖W.comp ((projector (c+q)).comp F-(linearProjector c q).comp F)‖ ≤ s^2*pR)
    (hWF : ‖W.comp F‖ ≤ qw) :
    ‖W.comp (auxiliaryAction material (c+q) t t' F-auxiliaryAction material c t t F-
      firstAuxiliaryAction material c q t F)‖ ≤
      s^2*(wmax*e/2+(curlmax/2+wmax)*ν+2*t*pR)+σ*qw := by
  have hmag := BoxMagneticWeighted.actual_weighted_remainder_bound_of_displacement
    material hm c q F W s ν e wmax curlmax hs hF hcenter hW hWC
  change ‖W.comp (magneticAction material (c+q) F)-W.comp (magneticAction material c F)-
    (W.comp ((linearCurlOperator c q).comp ((inverseMaterial material).comp (appliedCurl c F)))+
      W.comp ((curlOperator c).comp ((inverseMaterial material).comp (appliedLinear c q F))))‖ ≤ _ at hmag
  have hmag' : ‖W.comp (magneticAction material (c+q) F-magneticAction material c F-
      firstMagneticAction material c q F)‖ ≤
      s^2*(wmax*e/2+(curlmax/2+wmax)*ν) := by
    simpa only [firstMagneticAction, ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_add] using hmag
  rw [auxiliary_remainder_identity material c q t t' F htrans,
    ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul]
  calc
    _ ≤ ‖W.comp (magneticAction material (c+q) F-magneticAction material c F-
        firstMagneticAction material c q F)‖+
        ‖(2*t : ℂ) • W.comp ((projector (c+q)).comp F-(linearProjector c q).comp F)‖+
        ‖W.comp (((t'-t : ℝ) : ℂ) • F)‖ :=
      (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ ≤ s^2*(wmax*e/2+(curlmax/2+wmax)*ν)+(2*t)*(s^2*pR)+σ*qw := by
      gcongr
      · rw [norm_smul, show (2*t : ℂ) = ((2*t : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact mul_le_mul_of_nonneg_left hP (by positivity)
      · rw [ContinuousLinearMap.comp_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul hshift hWF (norm_nonneg _) ((abs_nonneg _).trans hshift)
    _ = _ := by ring

theorem weighted_projector_remainder_bound
    (c q : Momentum) (support : Finset Frequency) (w : Frequency → ℝ)
    (hw : ∀ f, f ∉ support → w f = 0) (F : V →L[ℂ] Field)
    (htrans : ∀ x, F x ∈ transverseSubspace c)
    (s r wmax qfn : ℝ) (hs : 0 ≤ s) (hq : displacementSize q ≤ s)
    (hsr : s < r) (hr : ∀ f ∈ support, r ≤ ‖longitudinalVector c f‖)
    (hW : ‖scalarWeight w‖ ≤ wmax)
    (hF : ‖(restrictOperator support).comp F‖ ≤ qfn) :
    ‖(scalarWeight w).comp ((projector (c+q)).comp F-(linearProjector c q).comp F)‖ ≤
      s^2*(wmax*((r/2+3+s/r)/(r-s)^2)*qfn) := by
  have hr0 : 0 < r := hs.trans_lt hsr
  have hw0 : 0 ≤ wmax := (norm_nonneg _).trans hW
  have hqf0 : 0 ≤ qfn := (norm_nonneg _).trans hF
  have hc : 0 ≤ (r/2+3+s/r)/(r-s)^2 := by positivity
  have hWF := weighted_restriction_bound support w hw F wmax qfn hW hF
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have h := weighted_transverse_projection_remainder c q w (F x) (htrans x)
    s r hs hq hsr (by
      intro f hf
      by_contra hn
      exact hf (hw f (fun hm => hn (hr f hm))))
  change ‖scalarWeight w (projector (c+q) (F x)-linearProjector c q (F x))‖ ≤ _
  apply h.trans
  have hFx : ‖scalarWeight w (F x)‖ ≤ (wmax*qfn)*‖x‖ :=
    (ContinuousLinearMap.le_opNorm ((scalarWeight w).comp F) x).trans
      (mul_le_mul_of_nonneg_right hWF (norm_nonneg _))
  have hb := mul_le_mul_of_nonneg_left hFx (mul_nonneg (sq_nonneg s) hc)
  convert hb using 1
  ring

/-- The stored center residual, three coordinate residual derivatives and
actual Taylor remainder control the fixed-weight residual on the entire box. -/
theorem weighted_auxiliary_box_bound
    (material : Cell20 → ℝ) (hm : ∀ e, 1 ≤ PrimitiveYee.edgeAverage material e)
    (c q : Momentum) (t t' σ s r ν e wmax curlmax qfn qw rzero : ℝ)
    (support : Finset Frequency) (w : Frequency → ℝ)
    (hw : ∀ f, f ∉ support → w f = 0) (F : V →L[ℂ] Field)
    (htrans : ∀ x, F x ∈ transverseSubspace c)
    (h k : Direction → ℝ) (hh : ∀ j, |q j| ≤ h j)
    (hk : ∀ j, ‖(scalarWeight w).comp (firstAuxiliaryAction material c (axis j) t F)‖ ≤ k j)
    (ht : 0 ≤ t) (hshift : |t'-t| ≤ σ) (hs0 : 0 ≤ s) (hs : displacementSize q ≤ s)
    (hsr : s < r) (hr : ∀ f ∈ support, r ≤ ‖longitudinalVector c f‖)
    (hF : ‖F‖ ≤ ν) (hcenter : ‖appliedCurl c F‖ ≤ e)
    (hW : ‖scalarWeight w‖ ≤ wmax)
    (hWC : ‖(scalarWeight w).comp (curlOperator c)‖ ≤ curlmax)
    (hhigh : ‖(restrictOperator support).comp F‖ ≤ qfn)
    (hWF : ‖(scalarWeight w).comp F‖ ≤ qw)
    (hzero : ‖(restrictOperator support).comp (auxiliaryAction material c t t F)‖ ≤ rzero) :
    ‖(scalarWeight w).comp (auxiliaryAction material (c+q) t t' F)‖ ≤
      wmax*rzero+(∑ j, h j*k j)+
      s^2*(wmax*e/2+(curlmax/2+wmax)*ν+
        2*t*wmax*((r/2+3+s/r)/(r-s)^2)*qfn)+σ*qw := by
  have h0 := weighted_restriction_bound support w hw
    (auxiliaryAction material c t t F) wmax rzero hW hzero
  have h1 := weighted_firstAuxiliaryAction_box_bound material c q t F (scalarWeight w) h k hh hk
  have h2 := weighted_auxiliary_remainder_bound material hm c q t t' σ s ν e wmax curlmax
    (wmax*((r/2+3+s/r)/(r-s)^2)*qfn) qw F (scalarWeight w) htrans ht hshift hs hF hcenter hW hWC
    (weighted_projector_remainder_bound c q support w hw F htrans s r wmax qfn hs0 hs hsr hr hW hhigh) hWF
  have he : (scalarWeight w).comp (auxiliaryAction material (c+q) t t' F) =
      (scalarWeight w).comp (auxiliaryAction material c t t F)+
      (scalarWeight w).comp (firstAuxiliaryAction material c q t F)+
      (scalarWeight w).comp (auxiliaryAction material (c+q) t t' F-
        auxiliaryAction material c t t F-firstAuxiliaryAction material c q t F) := by
    simp only [ContinuousLinearMap.comp_sub]
    module
  rw [he]
  apply (norm_add_le _ _).trans
  apply (add_le_add_left (norm_add_le _ _) _).trans
  have hb := add_le_add (add_le_add h0 h1) h2
  convert hb using 1
  ring

/-- The moving inverse weight is controlled by the fixed center weight,
including the exact square-root factor used in the verified scalar test. -/
theorem moving_weight_bound (support : Finset Frequency) (c q : Momentum)
    (ρ t σ s r t' B : ℝ) (A : V →L[ℂ] Field)
    (hρ : 0 < ρ) (ht : 0 ≤ t) (hσ : 0 ≤ σ) (hs : 0 ≤ s)
    (hq : displacementSize q ≤ s) (hsr : s < r)
    (hr : ∀ f ∈ support, r ≤ ‖longitudinalVector c f‖)
    (ht' : t' ≤ t+σ) (hshift : 0 < (r-s)^2/ρ-t-σ)
    (hA : ‖(scalarWeight (BoxWeightAssembly.inverseWeight support c ρ t)).comp A‖ ≤ B) :
    ‖(scalarWeight (BoxWeightAssembly.inverseWeight support (c+q) ρ t')).comp A‖ ≤
      Real.sqrt ((r^2/ρ-t)/((r-s)^2/ρ-t-σ))*B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans hA
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have h := BoxWeightAssembly.inverseWeight_shift_comparison support c q ρ t σ s r t'
    hρ ht hσ hs hq hsr hr ht' hshift (A x)
  apply h.trans
  have hAx := (ContinuousLinearMap.le_opNorm
    ((scalarWeight (BoxWeightAssembly.inverseWeight support c ρ t)).comp A) x).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  simpa only [ContinuousLinearMap.comp_apply, mul_assoc] using
    mul_le_mul_of_nonneg_left hAx
      (Real.sqrt_nonneg ((r^2/ρ-t)/((r-s)^2/ρ-t-σ)))

/-- The complete high residual bound for a center-transverse block. Every
remaining operator premise is a finite center or coordinate-derivative bound. -/
theorem moving_auxiliary_box_bound
    (material : Cell20 → ℝ) (hm : ∀ e, 1 ≤ PrimitiveYee.edgeAverage material e)
    (c q : Momentum) (ρ t t' σ s r ν e qfn qw rzero : ℝ)
    (support : Finset Frequency) (F : V →L[ℂ] Field)
    (htrans : ∀ x, F x ∈ transverseSubspace c)
    (h k : Direction → ℝ) (hh : ∀ j, |q j| ≤ h j)
    (hk : ∀ j, ‖(scalarWeight (BoxWeightAssembly.inverseWeight support c ρ t)).comp
      (firstAuxiliaryAction material c (axis j) t F)‖ ≤ k j)
    (hρ : 0 < ρ) (ht : 0 ≤ t) (hσ : 0 ≤ σ) (hshift : |t'-t| ≤ σ)
    (hs0 : 0 ≤ s) (hs : displacementSize q ≤ s) (hsr : s < r)
    (hr : ∀ f ∈ support, r ≤ ‖longitudinalVector c f‖)
    (hbase : 0 < r^2/ρ-t) (hnew : 0 < (r-s)^2/ρ-t-σ)
    (hF : ‖F‖ ≤ ν) (hcenter : ‖appliedCurl c F‖ ≤ e)
    (hhigh : ‖(restrictOperator support).comp F‖ ≤ qfn)
    (hWF : ‖(scalarWeight (BoxWeightAssembly.inverseWeight support c ρ t)).comp F‖ ≤ qw)
    (hzero : ‖(restrictOperator support).comp (auxiliaryAction material c t t F)‖ ≤ rzero) :
    let wmax := 1/Real.sqrt (r^2/ρ-t)
    let curlmax := r/Real.sqrt (r^2/ρ-t)
    ‖(scalarWeight (BoxWeightAssembly.inverseWeight support (c+q) ρ t')).comp
      (auxiliaryAction material (c+q) t t' F)‖ ≤
      Real.sqrt ((r^2/ρ-t)/((r-s)^2/ρ-t-σ)) *
        (wmax*rzero+(∑ j, h j*k j)+s^2*(wmax*e/2+(curlmax/2+wmax)*ν+
          2*t*wmax*((r/2+3+s/r)/(r-s)^2)*qfn)+σ*qw) := by
  dsimp only
  apply moving_weight_bound support c q ρ t σ s r t' _ _
    hρ ht hσ hs0 hs hsr hr (by have hh := (abs_le.mp hshift).2; linarith) hnew
  exact weighted_auxiliary_box_bound material hm c q t t' σ s r ν e
    (1/Real.sqrt (r^2/ρ-t)) (r/Real.sqrt (r^2/ρ-t)) qfn qw rzero
    support (BoxWeightAssembly.inverseWeight support c ρ t)
    (by intro f hf; simp [BoxWeightAssembly.inverseWeight, hf]) F htrans h k hh hk
    ht hshift hs0 hs hsr hr hF hcenter
    (BoxWeightAssembly.inverseWeight_norm support c ρ t r hρ (hs0.trans_lt hsr) hbase hr)
    (BoxWeightAssembly.inverseWeight_curl_norm support c ρ t r hρ ht (hs0.trans_lt hsr) hbase hr)
    hhigh hWF hzero

end
end Maxwell.Spectral.BoxResidual
