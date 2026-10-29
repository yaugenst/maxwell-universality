import Maxwell.Continuum.AngularFourier

/-! Constant vector embeddings in actual L² commute with the unitary Fourier
transforms. The proof passes through Schwartz functions and density. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.L2CoefficientMap

open MeasureTheory FourierTransform
open scoped SchwartzMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def embedding (v : H) : L2Dilation.L2 (H := ℂ) →L[ℂ] L2Dilation.L2 (H := H) :=
  (ContinuousLinearMap.toSpanSingleton ℂ v).compLpL 2 volume

omit [CompleteSpace H] in
theorem embedding_ae (v : H) (f : L2Dilation.L2 (H := ℂ)) :
    embedding v f =ᵐ[volume] fun x => f x • v :=
  ContinuousLinearMap.coeFn_compLpL _ f

omit [CompleteSpace H] in
theorem embedding_schwartz (v : H) (f : 𝓢(Space, ℂ)) :
    embedding v (f.toLp 2) = (f.postcompCLM (ContinuousLinearMap.toSpanSingleton ℂ v)).toLp 2 := by
  apply Lp.ext
  filter_upwards [embedding_ae v (f.toLp 2), f.coeFn_toLp 2,
    (f.postcompCLM (ContinuousLinearMap.toSpanSingleton ℂ v)).coeFn_toLp 2] with x he hf hg
  simp only [he, hf, hg, SchwartzMap.postcompCLM_apply,
    ContinuousLinearMap.toSpanSingleton_apply]

theorem fourier_postcomp (v : H) (f : 𝓢(Space, ℂ)) :
    𝓕 (f.postcompCLM (ContinuousLinearMap.toSpanSingleton ℂ v)) =
      (𝓕 f).postcompCLM (ContinuousLinearMap.toSpanSingleton ℂ v) := by
  ext p
  change 𝓕 (fun x => (ContinuousLinearMap.toSpanSingleton ℂ v) (f x)) p =
    (ContinuousLinearMap.toSpanSingleton ℂ v) (𝓕 (f : Space → ℂ) p)
  rw [Real.fourier_eq, Real.fourier_eq]
  rw [← (ContinuousLinearMap.toSpanSingleton ℂ v).integral_comp_comm
    ((Real.fourierIntegral_convergent_iff p).2 f.integrable)]
  congr 1
  funext x
  simp only [ContinuousLinearMap.map_smul_of_tower]

theorem fourier_embedding (v : H) (f : L2Dilation.L2 (H := ℂ)) :
    𝓕 (embedding v f) = embedding v (𝓕 f) := by
  let P := fun f : L2Dilation.L2 (H := ℂ) =>
    𝓕 (embedding v f) = embedding v (𝓕 f)
  apply DenseRange.induction_on (p := P)
    (SchwartzMap.denseRange_toLpCLM (p := 2) ENNReal.ofNat_ne_top) f
  · exact isClosed_eq
      (continuous_fourier.comp (embedding v).continuous)
      ((embedding v).continuous.comp continuous_fourier)
  intro g
  change 𝓕 (embedding v (g.toLp 2)) = embedding v (𝓕 (g.toLp 2))
  rw [embedding_schwartz, SchwartzMap.toLp_fourier_eq, fourier_postcomp,
    SchwartzMap.toLp_fourier_eq, embedding_schwartz]

omit [CompleteSpace H] in
theorem dilation_embedding (v : H) {a : ℝ} (ha : 0 < a)
    (f : L2Dilation.L2 (H := ℂ)) :
    L2Dilation.equiv ha (embedding v f) = embedding v (L2Dilation.equiv ha f) := by
  apply Lp.ext
  filter_upwards [L2Dilation.equiv_ae ha (embedding v f),
    L2Dilation.inverse_ae ha (embedding_ae v f), embedding_ae v (L2Dilation.equiv ha f),
    L2Dilation.equiv_ae ha f] with x hd he ho hf
  rw [hd, he, ho, hf]
  simp only [smul_smul, smul_eq_mul]

theorem angular_embedding (v : H) (f : L2Dilation.L2 (H := ℂ)) :
    angularFourier H (embedding v f) = embedding v (angularFourier ℂ f) := by
  change L2Dilation.equiv (a := 2 * Real.pi) (by positivity) (𝓕 (embedding v f)) =
    embedding v (L2Dilation.equiv (a := 2 * Real.pi) (by positivity) (𝓕 f))
  rw [fourier_embedding, dilation_embedding]

theorem angular_inverse_embedding (v : H) (f : L2Dilation.L2 (H := ℂ)) :
    (angularFourier H).symm (embedding v f) = embedding v ((angularFourier ℂ).symm f) := by
  apply (angularFourier H).injective
  rw [(angularFourier H).apply_symm_apply, angular_embedding,
    (angularFourier ℂ).apply_symm_apply]

end Maxwell.Continuum.L2CoefficientMap
