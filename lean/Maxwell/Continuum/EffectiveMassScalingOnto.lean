import Maxwell.Continuum.EffectiveMassScalingL2

/-! The literal momentum dilation is onto, not merely an isometric
embedding. This discharges the scaling factor in the selected-band Gram identity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory Bloch
open scoped ENNReal InnerProduct

theorem forwardDilation_memLp {h : ℝ} (hh : 0 < h) (f : AngularL2) :
    MemLp (fun p : Space => f (h • p)) 2 volume := by
  have hf := (Lp.memLp f).comp_measurePreserving (inverseDilation_measurePreserving hh).symm
  change MemLp (fun p : Space => f (h • p)) 2
    (ENNReal.ofReal (scaledDensity h) • (volume : Measure Space)) at hf
  have hc0 : ENNReal.ofReal (scaledDensity h) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (scaledDensity_pos hh)).ne'
  have hs := hf.smul_measure (ENNReal.inv_ne_top.mpr hc0)
  simpa only [smul_smul, ENNReal.inv_mul_cancel hc0 ENNReal.ofReal_ne_top, one_smul] using hs

theorem scaledAngular_surjective {h : ℝ} (hh : 0 < h) :
    Function.Surjective (scaledAngular hh) := by
  intro g
  have hm := (forwardDilation_memLp hh g).const_mul ((amplitudeFactor h : ℂ)⁻¹)
  let f : ScalarL2 := hm.toLp (fun p : Space => (amplitudeFactor h : ℂ)⁻¹ * g (h • p))
  refine ⟨f, Lp.ext ?_⟩
  have hf := inverseDilation_ae hh hm.coeFn_toLp
  filter_upwards [scaledAngular_ae hh f, hf] with q hg hq
  rw [hg, hq]
  rw [smul_smul, mul_inv_cancel₀ hh.ne', one_smul]
  have ha : (amplitudeFactor h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (amplitudeFactor_pos hh).ne'
  rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]

def scaledAngularEquiv {h : ℝ} (hh : 0 < h) : ScalarL2 ≃ₗᵢ[ℂ] AngularL2 :=
  LinearIsometryEquiv.ofSurjective (scaledAngularIsometry hh) (scaledAngular_surjective hh)

@[simp] theorem scaledAngularEquiv_apply {h : ℝ} (hh : 0 < h) (f : ScalarL2) :
    scaledAngularEquiv hh f = scaledAngular hh f := rfl

theorem scaledAngular_comp_adjoint {h : ℝ} (hh : 0 < h) :
    (scaledAngularIsometry hh).toContinuousLinearMap.comp
      (((scaledAngularIsometry hh).toContinuousLinearMap)†) = ContinuousLinearMap.id ℂ AngularL2 := by
  change (scaledAngularEquiv hh).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((scaledAngularEquiv hh).toContinuousLinearEquiv.toContinuousLinearMap)†) = _
  rw [(scaledAngularEquiv hh).adjoint_eq_symm]
  apply ContinuousLinearMap.ext
  intro f
  exact (scaledAngularEquiv hh).apply_symm_apply f

end Maxwell.Continuum.EffectiveMass
