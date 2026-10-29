import Maxwell.Continuum.EffectiveMassScalingMeasure

/-! The exact L² isometry from angular p to rescaled angular q=hp.
The amplitude factor is derived from the literal measures. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory Bloch
open scoped ENNReal

abbrev AngularL2 := Lp ℂ 2 angularMeasure

theorem inverseDilation_ae {h : ℝ} (hh : 0 < h) {f g : Space → ℂ}
    (hfg : f =ᵐ[volume] g) :
    (fun q => f (h⁻¹ • q)) =ᵐ[angularMeasure] fun q => g (h⁻¹ • q) := by
  exact (inverseDilation_measurePreserving hh).quasiMeasurePreserving.ae_eq_comp
    (Measure.ae_smul_measure hfg (ENNReal.ofReal (scaledDensity h)))

theorem scaledAngular_memLp {h : ℝ} (hh : 0 < h) (f : ScalarL2) :
    MemLp (fun q => (amplitudeFactor h : ℂ) * f (h⁻¹ • q)) 2 angularMeasure := by
  have hm := ((Lp.memLp f).smul_measure (ENNReal.ofReal_ne_top)).comp_measurePreserving
    (inverseDilation_measurePreserving hh)
  exact hm.const_mul _

def scaledAngular {h : ℝ} (hh : 0 < h) (f : ScalarL2) : AngularL2 :=
  (scaledAngular_memLp hh f).toLp _

theorem scaledAngular_ae {h : ℝ} (hh : 0 < h) (f : ScalarL2) :
    scaledAngular hh f =ᵐ[angularMeasure]
      fun q => (amplitudeFactor h : ℂ) * f (h⁻¹ • q) := MemLp.coeFn_toLp _

theorem scaledAngular_norm_sq {h : ℝ} (hh : 0 < h) (f : ScalarL2) :
    ‖scaledAngular hh f‖^2 = ‖f‖^2 := by
  rw [complexL2_norm_sq]
  have he : (fun q => ‖scaledAngular hh f q‖^2) =ᵐ[angularMeasure]
      fun q => ‖(amplitudeFactor h : ℂ) * f (h⁻¹ • q)‖^2 :=
    (scaledAngular_ae hh f).fun_comp (fun z => ‖z‖^2)
  rw [integral_congr_ae he]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (amplitudeFactor_pos hh), mul_pow]
  rw [integral_const_mul]
  have hi := (inverseDilation_measurePreserving hh).integral_comp'
    (fun p => ‖f p‖^2)
  change (∫ q, ‖f (h⁻¹ • q)‖^2 ∂angularMeasure) = _ at hi
  rw [hi, integral_smul_measure, ENNReal.toReal_ofReal (scaledDensity_pos hh).le]
  change amplitudeFactor h ^ 2 * (scaledDensity h * (∫ p, ‖f p‖^2)) = _
  rw [← mul_assoc, amplitudeFactor_square hh, one_mul, ← complexL2_norm_sq]

theorem scaledAngular_norm {h : ℝ} (hh : 0 < h) (f : ScalarL2) :
    ‖scaledAngular hh f‖ = ‖f‖ := by
  have he := scaledAngular_norm_sq hh f
  nlinarith [norm_nonneg (scaledAngular hh f), norm_nonneg f]

def scaledAngularLinear {h : ℝ} (hh : 0 < h) : ScalarL2 →ₗ[ℂ] AngularL2 where
  toFun := scaledAngular hh
  map_add' f g := by
    apply Lp.ext
    filter_upwards [scaledAngular_ae hh (f+g), scaledAngular_ae hh f,
      scaledAngular_ae hh g, inverseDilation_ae hh (Lp.coeFn_add f g),
      Lp.coeFn_add (scaledAngular hh f) (scaledAngular hh g)] with q hfg hf hg ha hb
    simp only [hfg, hb, ha, Pi.add_apply, hf, hg, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [scaledAngular_ae hh (c • f), scaledAngular_ae hh f,
      inverseDilation_ae hh (Lp.coeFn_smul c f),
      Lp.coeFn_smul c (scaledAngular hh f)] with q hcf hf ha hb
    change scaledAngular hh (c • f) q = (c • scaledAngular hh f) q
    simp only [hcf, hb, ha, Pi.smul_apply, hf, smul_eq_mul]
    ring

def scaledAngularIsometry {h : ℝ} (hh : 0 < h) : ScalarL2 →ₗᵢ[ℂ] AngularL2 where
  toLinearMap := scaledAngularLinear hh
  norm_map' := scaledAngular_norm hh

#print axioms scaledAngularIsometry

end Maxwell.Continuum.EffectiveMass
