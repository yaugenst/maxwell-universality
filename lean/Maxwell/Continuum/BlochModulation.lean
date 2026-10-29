import Maxwell.Continuum.BlochUnitary

/-! Literal physical phase multiplication and frequency translation on L². -/

noncomputable section

namespace Maxwell.Continuum.Bloch

open MeasureTheory FourierTransform
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

def phase (a x : Space) : ℂ := Real.fourierChar (inner ℝ x a)

theorem phase_norm (a x : Space) : ‖phase a x‖ = 1 := Circle.norm_coe _

theorem phase_continuous (a : Space) : Continuous (phase a) := by
  exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp
    (continuous_id.inner continuous_const))

theorem phase_temperate (a : Space) : (phase a).HasTemperateGrowth := by
  unfold phase
  simp only [Real.fourierChar_apply]
  exact Complex.hasTemperateGrowth_exp_mul_I.comp
    ((Function.HasTemperateGrowth.const (2 * Real.pi)).mul
      (Function.hasTemperateGrowth_inner_left a))

theorem phaseProduct_memLp (a : Space) (f : ScalarL2) :
    MemLp (fun x => phase a x * f x) 2 (volume : Measure Space) := by
  apply (Lp.memLp f).congr_norm
    ((phase_continuous a).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  exact Filter.Eventually.of_forall fun x => by
    change ‖f x‖ = ‖phase a x * f x‖
    rw [norm_mul, phase_norm, one_mul]

def phaseProduct (a : Space) (f : ScalarL2) : ScalarL2 :=
  (phaseProduct_memLp a f).toLp _

theorem phaseProduct_ae (a : Space) (f : ScalarL2) :
    phaseProduct a f =ᵐ[volume] (fun x => phase a x * f x) := MemLp.coeFn_toLp _

def phaseLinear (a : Space) : ScalarL2 →ₗ[ℂ] ScalarL2 where
  toFun := phaseProduct a
  map_add' f g := by
    apply Lp.ext
    filter_upwards [phaseProduct_ae a (f + g), phaseProduct_ae a f, phaseProduct_ae a g,
      Lp.coeFn_add f g, Lp.coeFn_add (phaseProduct a f) (phaseProduct a g)]
      with x hfg hf hg ha hb
    rw [hfg, hb, ha]
    simp only [Pi.add_apply, hf, hg, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [phaseProduct_ae a (c • f), phaseProduct_ae a f,
      Lp.coeFn_smul c f, Lp.coeFn_smul c (phaseProduct a f)] with x hc hf hs ht
    change phaseProduct a (c • f) x = (c • phaseProduct a f : ScalarL2) x
    rw [hc, ht, hs]
    simp only [Pi.smul_apply, hf, smul_eq_mul]
    ring

theorem phaseProduct_norm (a : Space) (f : ScalarL2) : ‖phaseProduct a f‖ = ‖f‖ := by
  simp only [Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [phaseProduct_ae a f] with x hx
  rw [hx, norm_mul, phase_norm, one_mul]

def modulation (a : Space) : ScalarL2 →ₗᵢ[ℂ] ScalarL2 where
  toLinearMap := phaseLinear a
  norm_map' := phaseProduct_norm a

theorem modulation_ae (a : Space) (f : ScalarL2) :
    modulation a f =ᵐ[volume] (fun x => phase a x * f x) := phaseProduct_ae a f

def translation (a : Space) : ScalarL2 →ₗᵢ[ℂ] ScalarL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : Space => x + a) (measurePreserving_add_right volume a)

theorem translation_ae (a : Space) (f : ScalarL2) :
    translation a f =ᵐ[volume] (fun x => f (x + a)) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume a)

theorem modulation_toLp (a : Space) (f : SchwartzMap Space ℂ) :
    modulation a (f.toLp 2) = (SchwartzMap.smulLeftCLM ℂ (phase a) f).toLp 2 := by
  apply Lp.ext
  filter_upwards [modulation_ae a (f.toLp 2), f.coeFn_toLp 2,
    (SchwartzMap.smulLeftCLM ℂ (phase a) f).coeFn_toLp 2] with x hm hf hg
  rw [hm, hf, hg, SchwartzMap.smulLeftCLM_apply_apply (phase_temperate a)]
  rfl

theorem fourier_phase_schwartz (a ξ : Space) (f : SchwartzMap Space ℂ) :
    𝓕 (SchwartzMap.smulLeftCLM ℂ (phase a) f) ξ = 𝓕 f (ξ - a) := by
  change 𝓕 (fun x => (SchwartzMap.smulLeftCLM ℂ (phase a) f) x) ξ = 𝓕 (fun x => f x) (ξ - a)
  rw [Real.fourier_eq, Real.fourier_eq]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [SchwartzMap.smulLeftCLM_apply_apply (phase_temperate a)]
    simp only [phase, Circle.smul_def, smul_eq_mul, inner_sub_right]
    rw [← mul_assoc, ← Circle.coe_mul, ← Real.fourierChar.map_add_eq_mul]
    rw [show -inner ℝ x ξ + inner ℝ x a = -(inner ℝ x ξ - inner ℝ x a) by ring]

theorem fourier_modulation_schwartz (a : Space) (f : SchwartzMap Space ℂ) :
    𝓕 (modulation a (f.toLp 2)) = translation (-a) (𝓕 (f.toLp 2)) := by
  rw [modulation_toLp, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  have h := (measurePreserving_add_right (volume : Measure Space) (-a)).quasiMeasurePreserving.ae_eq_comp
    (SchwartzMap.coeFn_toLp (𝓕 f) 2)
  filter_upwards [(𝓕 (SchwartzMap.smulLeftCLM ℂ (phase a) f)).coeFn_toLp 2,
    translation_ae (-a) ((𝓕 f).toLp 2), h] with ξ hf ht hs
  dsimp only [Function.comp_apply] at hs
  rw [hf, ht, hs]
  simpa only [sub_eq_add_neg] using fourier_phase_schwartz a ξ f

/-- Fourier modulation holds on all of L² by actual Schwartz density. -/
theorem fourier_modulation (a : Space) (f : ScalarL2) :
    𝓕 (modulation a f) = translation (-a) (𝓕 f) := by
  apply DenseRange.induction_on
    (p := fun f : ScalarL2 => 𝓕 (modulation a f) = translation (-a) (𝓕 f))
    (SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq
      (continuous_fourier.comp (modulation a).continuous)
      ((translation (-a)).continuous.comp continuous_fourier)
  · exact fourier_modulation_schwartz a

end Maxwell.Continuum.Bloch
