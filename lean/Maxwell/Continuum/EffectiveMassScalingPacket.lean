import Maxwell.Continuum.EffectiveMassScalingL2
import Maxwell.Continuum.EffectiveMassWell

/-! The scaled physical band packet, as an actual continuous map between
the angular-amplitude L² space and physical Maxwell fields. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory Bloch BandWavePacket
open scoped ENNReal

theorem angularToQuasi_memLp (f : AngularL2) :
    MemLp (fun q : QuasiCell => f q.val) 2 quasiMeasure :=
  ((Lp.memLp f).restrict quasiCell).comp_measurePreserving quasi_coe_measurePreserving

def angularToQuasi (f : AngularL2) : Lp ℂ 2 quasiMeasure :=
  (angularToQuasi_memLp f).toLp _

theorem angularToQuasi_ae (f : AngularL2) :
    angularToQuasi f =ᵐ[quasiMeasure] fun q => f q.val := MemLp.coeFn_toLp _

theorem quasi_coe_ae {f g : Space → ℂ} (hfg : f =ᵐ[angularMeasure] g) :
    (fun q : QuasiCell => f q.val) =ᵐ[quasiMeasure] fun q => g q.val :=
  quasi_coe_measurePreserving.quasiMeasurePreserving.ae_eq_comp (ae_restrict_of_ae hfg)

theorem angularToQuasi_norm_le (f : AngularL2) : ‖angularToQuasi f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (angularToQuasi_ae f)]
  apply ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top
  change eLpNorm ((f : Space → ℂ) ∘ Subtype.val) 2 quasiMeasure ≤ _
  rw [eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable f).restrict
    quasi_coe_measurePreserving]
  exact eLpNorm_mono_measure f Measure.restrict_le_self

def angularToQuasiLinear : AngularL2 →ₗ[ℂ] Lp ℂ 2 quasiMeasure where
  toFun := angularToQuasi
  map_add' f g := by
    apply Lp.ext
    filter_upwards [angularToQuasi_ae (f+g), angularToQuasi_ae f,
      angularToQuasi_ae g, quasi_coe_ae (Lp.coeFn_add f g),
      Lp.coeFn_add (angularToQuasi f) (angularToQuasi g)] with q hfg hf hg ha hb
    simp only [hfg, hb, ha, Pi.add_apply, hf, hg]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [angularToQuasi_ae (c • f), angularToQuasi_ae f,
      quasi_coe_ae (Lp.coeFn_smul c f), Lp.coeFn_smul c (angularToQuasi f)]
      with q hcf hf ha hb
    change angularToQuasi (c • f) q = (c • angularToQuasi f) q
    simp only [hcf, hb, ha, Pi.smul_apply, hf]

def angularToQuasiCLM : AngularL2 →L[ℂ] Lp ℂ 2 quasiMeasure :=
  angularToQuasiLinear.mkContinuous 1 (fun f => by
    change ‖angularToQuasi f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using angularToQuasi_norm_le f)

def scalarMask : SectionData (H := ℂ) quasiMeasure region where
  value := region.indicator (fun _ => 1)
  measurable := aestronglyMeasurable_const.indicator region_isOpen.measurableSet
  unit := fun q hq => by rw [Set.indicator_of_mem hq]; exact norm_one
  zero := fun q hq => Set.indicator_of_notMem hq _

theorem scalarMask_analysis_ae (f : Lp ℂ 2 quasiMeasure) :
    (scalarMask.analysis f).val =ᵐ[quasiMeasure] region.indicator f := by
  filter_upwards [scalarMask.coefficient_ae f] with q hq
  change scalarMask.coefficient f q = region.indicator f q
  rw [hq]
  by_cases h : q ∈ region
  · change inner ℂ (region.indicator (fun _ => (1 : ℂ)) q) (f q) = _
    rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    simp
  · change inner ℂ (region.indicator (fun _ => (1 : ℂ)) q) (f q) = _
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, inner_zero_left]

def scaledAmplitude {h : ℝ} (hh : 0 < h) : ScalarL2 →L[ℂ] Amplitude :=
  scalarMask.analysis.comp (angularToQuasiCLM.comp (scaledAngularIsometry hh).toContinuousLinearMap)

theorem scaledAmplitude_ae {h : ℝ} (hh : 0 < h) (f : ScalarL2) :
    (scaledAmplitude hh f).val =ᵐ[quasiMeasure]
      region.indicator (fun q => (amplitudeFactor h : ℂ) * f (h⁻¹ • q.val)) := by
  filter_upwards [scalarMask_analysis_ae (angularToQuasi (scaledAngular hh f)),
    angularToQuasi_ae (scaledAngular hh f), quasi_coe_ae (scaledAngular_ae hh f)]
    with q hm hq hs
  change (scalarMask.analysis (angularToQuasi (scaledAngular hh f))).val q = _
  rw [hm]
  by_cases hr : q ∈ region
  · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr, hq, hs]
  · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr]

theorem scaledAmplitude_norm_le {h : ℝ} (hh : 0 < h) (f : ScalarL2) :
    ‖scaledAmplitude hh f‖ ≤ ‖f‖ := by
  change ‖scalarMask.coefficient (angularToQuasi (scaledAngular hh f))‖ ≤ _
  exact (scalarMask.coefficient_norm_le _).trans
    ((angularToQuasi_norm_le _).trans (scaledAngular_norm hh f).le)

/-- The paper's fixed factor i multiplies the genuine physical band embedding. -/
def Uh {h : ℝ} (hh : 0 < h) : ScalarL2 →L[ℂ] FieldL2 :=
  Complex.I • (physicalEmbedding.toContinuousLinearMap.comp (scaledAmplitude hh))

theorem Uh_norm_le {h : ℝ} (hh : 0 < h) (f : ScalarL2) : ‖Uh hh f‖ ≤ ‖f‖ := by
  change ‖Complex.I • physicalEmbedding (scaledAmplitude hh f)‖ ≤ _
  rw [norm_smul, Complex.norm_I, one_mul, physicalEmbedding_norm]
  exact scaledAmplitude_norm_le hh f

theorem Uh_unitary {h : ℝ} (hh : 0 < h) (f : ScalarL2) :
    unitary (Uh hh f) = Complex.I • fiberEmbedding (scaledAmplitude hh f) := by
  change unitary (Complex.I • physicalEmbedding (scaledAmplitude hh f)) = _
  rw [map_smul, unitary_physicalEmbedding]

#print axioms scaledAmplitude_ae
#print axioms Uh_norm_le
#print axioms Uh_unitary

end Maxwell.Continuum.EffectiveMass
