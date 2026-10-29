import Maxwell.Continuum.CompactTransportIntegral

/-! Uniform compact spatial support discharges the Fubini integrability
condition in the contour transport identity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.AlmostAnalytic

open MeasureTheory Set

variable {F : Type*} [NormedAddCommGroup F]

theorem compact_parameter_integrable (D : ℝ → Space → F) {K : Set Space}
    (hK : IsCompact K)
    (hc : ContinuousOn (Function.uncurry D) (Icc (0 : ℝ) 1 ×ˢ K))
    (hz : ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∉ K, D s q = 0) :
    Integrable (Function.uncurry D) ((volume.restrict (uIoc (0 : ℝ) 1)).prod volume) := by
  have hcompact : IsCompact (Icc (0 : ℝ) 1 ×ˢ K) := isCompact_Icc.prod hK
  have hi0 : Integrable ((Icc (0 : ℝ) 1 ×ˢ K).indicator (Function.uncurry D))
      ((volume : Measure ℝ).prod (volume : Measure Space)) :=
    (hc.integrableOn_compact hcompact).integrable_indicator hcompact.measurableSet
  have hi : Integrable ((Icc (0 : ℝ) 1 ×ˢ K).indicator (Function.uncurry D))
      ((volume.restrict (uIoc (0 : ℝ) 1)).prod volume) :=
    hi0.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have ha : ∀ᵐ p : ℝ × Space ∂((volume.restrict (uIoc (0 : ℝ) 1)).prod volume),
      p.1 ∈ Icc (0 : ℝ) 1 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    apply Filter.Eventually.of_forall
    intro q
    have hs' : s ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
    exact ⟨hs'.1.le, hs'.2⟩
  apply hi.congr
  filter_upwards [ha] with p hp
  by_cases hq : p.2 ∈ K
  · exact indicator_of_mem (show p ∈ Icc (0 : ℝ) 1 ×ˢ K from ⟨hp, hq⟩) _
  · rw [indicator_of_notMem (fun hm => hq hm.2)]
    exact (hz p.1 hp p.2 hq).symm

end Maxwell.Continuum.AlmostAnalytic
