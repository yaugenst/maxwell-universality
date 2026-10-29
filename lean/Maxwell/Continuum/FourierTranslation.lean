import Maxwell.Continuum.BlochAliasShift

/-! Actual physical L² translation and its exact Plancherel phase. -/

noncomputable section

namespace Maxwell.Continuum.Bloch

open MeasureTheory FourierTransform

def fieldTranslation (a : Space) : FieldL2 ≃ₗᵢ[ℂ] FieldL2 :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin 3 =>
    measureEquivL2 (MeasurableEquiv.addRight a) (measurePreserving_add_right volume a))

@[simp] theorem fieldTranslation_apply (a : Space) (f : FieldL2) (i : Fin 3) :
    fieldTranslation a f i = translation a (f i) := rfl

theorem fieldTranslation_ae (a : Space) (f : FieldL2) (i : Fin 3) :
    fieldTranslation a f i =ᵐ[volume] (fun x => f i (x + a)) := translation_ae a (f i)

theorem translation_neg_apply (a : Space) (f : ScalarL2) :
    translation a (translation (-a) f) = f := by
  apply Lp.ext
  have h := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae_eq_comp
    (translation_ae (-a) f)
  filter_upwards [translation_ae a (translation (-a) f), h] with x ha hb
  dsimp only [Function.comp_apply] at hb
  rw [ha, hb]
  simp only [add_neg_cancel_right]

theorem fieldTranslation_neg_apply (a : Space) (f : FieldL2) :
    fieldTranslation a (fieldTranslation (-a) f) = f := by
  apply PiLp.ext
  intro i
  exact translation_neg_apply a (f i)

def translationSchwartz (a : Space) : SchwartzMap Space ℂ →L[ℂ] SchwartzMap Space ℂ :=
  SchwartzMap.compSubConstCLM ℂ (-a)

@[simp] theorem translationSchwartz_apply (a : Space) (f : SchwartzMap Space ℂ) (x : Space) :
    translationSchwartz a f x = f (x + a) := by
  simp only [translationSchwartz, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]

theorem translation_toLp (a : Space) (f : SchwartzMap Space ℂ) :
    translation a (f.toLp 2) = (translationSchwartz a f).toLp 2 := by
  apply Lp.ext
  have h := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae_eq_comp
    (f.coeFn_toLp 2)
  filter_upwards [translation_ae a (f.toLp 2), (translationSchwartz a f).coeFn_toLp 2,
    h] with x ht hs hf
  dsimp only [Function.comp_apply] at hf
  rw [ht, hf, hs, translationSchwartz_apply]

theorem fourier_translationSchwartz (a ξ : Space) (f : SchwartzMap Space ℂ) :
    𝓕 (translationSchwartz a f) ξ = phase a ξ * 𝓕 f ξ := by
  have h := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
    (volume : Measure Space) (innerₗ Space) (f : Space → ℂ) a) ξ
  change 𝓕 (fun x => f (x + a)) ξ =
    (Real.fourierChar (inner ℝ a ξ) : ℂ) * 𝓕 f ξ at h
  change 𝓕 (fun x => translationSchwartz a f x) ξ = _
  simp only [translationSchwartz_apply]
  simpa only [phase, Circle.smul_def, smul_eq_mul, real_inner_comm] using h

theorem fourier_translation_schwartz (a : Space) (f : SchwartzMap Space ℂ) :
    𝓕 (translation a (f.toLp 2)) = modulation a (𝓕 (f.toLp 2)) := by
  rw [translation_toLp, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (translationSchwartz a f)).coeFn_toLp 2,
    modulation_ae a ((𝓕 f).toLp 2), (𝓕 f).coeFn_toLp 2] with ξ ht hm hf
  rw [ht, hm, hf]
  exact fourier_translationSchwartz a ξ f

theorem fourier_translation (a : Space) (f : ScalarL2) :
    𝓕 (translation a f) = modulation a (𝓕 f) := by
  apply DenseRange.induction_on
    (p := fun f : ScalarL2 => 𝓕 (translation a f) = modulation a (𝓕 f))
    (SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq (continuous_fourier.comp (translation a).continuous)
      ((modulation a).continuous.comp continuous_fourier)
  · exact fourier_translation_schwartz a

theorem unitary_fieldTranslation_coordinate_ae (a : Space) (f : FieldL2) :
    ∀ᵐ q ∂quasiMeasure, ∀ n : Alias, ∀ j : Fin 3,
      unitary (fieldTranslation a f) q n j =
        phase a (quasiFrequencyJoin (q,n)) * unitary f q n j := by
  have h (j : Fin 3) := modulation_ae a (𝓕 (f j))
  simp only [← fourier_translation] at h
  have hj := ae_all_iff.mpr fun j : Fin 3 =>
    product_ae_all_alias
      (quasiFrequencyJoin_measurePreserving.quasiMeasurePreserving.ae_eq_comp (h j))
  filter_upwards [unitary_coordinate_ae (fieldTranslation a f), unitary_coordinate_ae f, hj]
    with q ht hf hm
  intro n j
  rw [ht n j, hf n j]
  exact hm j n

end Maxwell.Continuum.Bloch
