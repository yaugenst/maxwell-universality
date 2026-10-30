import Maxwell.Continuum.FiniteAuxiliarySourceEncoding
import Maxwell.Continuum.FieldRealProjection

/-! Physical reality of the finite emitted source and contraction of
template errors after taking the literal real tensor coefficients. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.FiniteAuxiliary

open Maxwell.Composition Maxwell.Logical MeasureTheory EffectiveMass Auxiliary

theorem fieldConjugation_real_smul (c : ℝ) (f : FieldL2) :
    fieldConjugation ((c : ℂ) • f) = (c : ℂ) • fieldConjugation f := by
  change fieldConjugation ((algebraMap ℝ ℂ c) • f) = (algebraMap ℝ ℂ c) • fieldConjugation f
  rw [algebraMap_smul ℂ c f, map_smul, algebraMap_smul ℂ c (fieldConjugation f)]

theorem fieldRealProjection_real_smul (c : ℝ) (f : FieldL2) :
    fieldRealProjection ((c : ℂ) • f) = (c : ℂ) • fieldRealProjection f := by
  change fieldRealProjection ((algebraMap ℝ ℂ c) • f) = (algebraMap ℝ ℂ c) • fieldRealProjection f
  rw [algebraMap_smul ℂ c f, map_smul, algebraMap_smul ℂ c (fieldRealProjection f)]

theorem siteInsertion_conjugation (h : ℝ) (r : Space) (f : FieldL2) :
    fieldConjugation (siteInsertion h r f) = siteInsertion h r (fieldConjugation f) := by
  change fieldConjugation (Bloch.fieldTranslation (-r) (Qh h f)) = _
  rw [← Bloch.fieldTranslation_conjugation, Qh_conjugation]
  rfl

theorem ideal_template_real {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (r : Space) :
    fieldConjugation (siteInsertion h r (realMode D hh)) = siteInsertion h r (realMode D hh) := by
  rw [siteInsertion_conjugation, realMode_real D hh]

theorem real_template_error {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (r : Space) (a : FieldL2) :
    ‖fieldRealProjection a-siteInsertion h r (realMode D hh)‖ ≤
      ‖a-siteInsertion h r (realMode D hh)‖ :=
  fieldRealProjection_error a (ideal_template_real D hh r)

variable (S : Source.SparseSystem) (precision : ℕ)

theorem emittedSource_real (P : ℕ) (ĉ : ℚ)
    (a : SourceDecoration.Vertex S precision → FieldL2)
    (ha : ∀ i, fieldConjugation (a i) = a i) :
    fieldConjugation (emittedSource S precision P ĉ a) = emittedSource S precision P ĉ a := by
  rw [emittedSource_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [fieldConjugation_real_smul, ha]

theorem emittedSource_real_projection (P : ℕ) (ĉ : ℚ)
    (a : SourceDecoration.Vertex S precision → FieldL2) :
    emittedSource S precision P ĉ (fun i => fieldRealProjection (a i)) =
      fieldRealProjection (emittedSource S precision P ĉ a) := by
  rw [emittedSource_sum, emittedSource_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (fieldRealProjection_real_smul _ _).symm

theorem projected_emittedSource_real (P : ℕ) (ĉ : ℚ)
    (a : SourceDecoration.Vertex S precision → FieldL2) :
    fieldConjugation (emittedSource S precision P ĉ (fun i => fieldRealProjection (a i))) =
      emittedSource S precision P ĉ (fun i => fieldRealProjection (a i)) :=
  emittedSource_real S precision P ĉ _ (fun _ => fieldRealProjection_real _)

theorem ideal_routed_source_real {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (r : SourceDecoration.Vertex S precision → Space) (α : ℝ) :
    fieldConjugation (idealSource D hh r α (routedForcing S precision)) =
      idealSource D hh r α (routedForcing S precision) := by
  rw [idealSource_templateSynthesis, templateSynthesis_routed, fieldConjugation_real_smul]
  congr 1
  rw [templateSynthesis_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change fieldConjugation (((Source.rationalVector (Normalization.normalizedSource S) i : ℝ) : ℂ) •
    siteInsertion h (r (sourceInputSite S precision i)) (realMode D hh)) = _
  rw [fieldConjugation_real_smul, ideal_template_real]
  rfl

theorem projected_emittedSource_error (P : ℕ) (ĉ : ℚ)
    (a : SourceDecoration.Vertex S precision → FieldL2)
    {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (r : SourceDecoration.Vertex S precision → Space) (α : ℝ) :
    ‖emittedSource S precision P ĉ (fun i => fieldRealProjection (a i))-
      idealSource D hh r α (routedForcing S precision)‖ ≤
      ‖emittedSource S precision P ĉ a-idealSource D hh r α (routedForcing S precision)‖ := by
  rw [emittedSource_real_projection]
  exact fieldRealProjection_error _ (ideal_routed_source_real S precision D hh r α)

theorem emittedSource_real_ae (P : ℕ) (ĉ : ℚ)
    (a : SourceDecoration.Vertex S precision → FieldL2)
    (ha : ∀ i, fieldConjugation (a i) = a i) (k : Fin 3) :
    ∀ᵐ x ∂(volume : Measure Space), (emittedSource S precision P ĉ a k x).im = 0 :=
  field_real_ae (emittedSource_real S precision P ĉ a ha) k

theorem emittedSource_real_formula (P : ℕ) (ĉ : ℚ)
    (a : SourceDecoration.Vertex S precision → FieldL2)
    (τ : SourceDecoration.Vertex S precision → Fin 3 → Space → ℝ)
    (ha : ∀ i k, a i k =ᵐ[volume] fun x => (τ i k x : ℂ)) (k : Fin 3) :
    emittedSource S precision P ĉ a k =ᵐ[volume] fun x =>
      ((∑ i : Fin S.n, ((sourceAmplitude S P ĉ i).value : ℝ)*
        τ (sourceInputSite S precision i) k x : ℝ) : ℂ) := by
  have he : emittedSource S precision P ĉ a k = ∑ i : Fin S.n,
      (((sourceAmplitude S P ĉ i).value : ℝ) : ℂ) • a (sourceInputSite S precision i) k := by
    rw [emittedSource_sum]
    simp only [WithLp.ofLp_sum, Finset.sum_apply]
    rfl
  rw [he]
  have hi : ∀ i : Fin S.n, ∀ᵐ x ∂(volume : Measure Space),
      ((((sourceAmplitude S P ĉ i).value : ℝ) : ℂ) • a (sourceInputSite S precision i) k : ScalarL2) x =
        ((((sourceAmplitude S P ĉ i).value : ℝ)*τ (sourceInputSite S precision i) k x : ℝ) : ℂ) := by
    intro i
    filter_upwards [ha (sourceInputSite S precision i) k,
      Lp.coeFn_smul (((sourceAmplitude S P ĉ i).value : ℝ) : ℂ)
        (a (sourceInputSite S precision i) k)] with x ht hs
    rw [hs, Pi.smul_apply, ht, smul_eq_mul, Complex.ofReal_mul]
  filter_upwards [ae_all_iff.mpr hi,
    Lp.coeFn_finsetSum Finset.univ (fun i : Fin S.n =>
      (((sourceAmplitude S P ĉ i).value : ℝ) : ℂ) • a (sourceInputSite S precision i) k)]
      with x hx hs
  rw [hs, Finset.sum_apply, Complex.ofReal_sum]
  exact Finset.sum_congr rfl (fun i _ => hx i)

#print axioms real_template_error
#print axioms emittedSource_real
#print axioms projected_emittedSource_error
#print axioms emittedSource_real_formula

end Maxwell.Continuum.FiniteAuxiliary
