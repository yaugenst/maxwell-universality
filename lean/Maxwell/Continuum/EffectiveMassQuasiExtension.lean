import Maxwell.Continuum.EffectiveMassScalingPacket

/-! The adjoint of actual quasi-cell restriction is literal extension by
zero. No surjectivity or coisometry of restriction is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory Bloch
open scoped ENNReal InnerProduct

def quasiExtendFunction (f : QuasiCell → ℂ) : Space → ℂ :=
  Function.extend (Subtype.val : QuasiCell → Space) f (fun _ => 0)

theorem quasiExtendFunction_coe (f : QuasiCell → ℂ) (q : QuasiCell) :
    quasiExtendFunction f q.val = f q :=
  Function.Injective.extend_apply Subtype.val_injective _ _ _

theorem quasiExtendFunction_zero (f : QuasiCell → ℂ) {q : Space} (hq : q ∉ quasiCell) :
    quasiExtendFunction f q = 0 := by
  apply Function.extend_apply'
  rintro ⟨y, hy⟩
  exact hq (hy ▸ y.property)

theorem quasiExtendFunction_indicator (f : QuasiCell → ℂ) :
    quasiCell.indicator (quasiExtendFunction f) = quasiExtendFunction f := by
  funext q
  by_cases hq : q ∈ quasiCell
  · rw [Set.indicator_of_mem hq]
  · rw [Set.indicator_of_notMem hq, quasiExtendFunction_zero f hq]

theorem quasiExtendFunction_eLpNorm (f : QuasiCell → ℂ) :
    eLpNorm (quasiExtendFunction f) 2 angularMeasure = eLpNorm f 2 quasiMeasure := by
  rw [← quasiExtendFunction_indicator f, eLpNorm_indicator_eq_eLpNorm_restrict quasiCell_measurable,
    ← quasi_coe_measurePreserving.map_eq]
  rw [(MeasurableEmbedding.subtype_coe quasiCell_measurable).eLpNorm_map_measure]
  congr 1
  funext q
  exact quasiExtendFunction_coe f q

theorem quasiExtendFunction_ae_congr {f g : QuasiCell → ℂ} (hfg : f =ᵐ[quasiMeasure] g) :
    quasiExtendFunction f =ᵐ[angularMeasure] quasiExtendFunction g := by
  have hr : quasiExtendFunction f =ᵐ[angularMeasure.restrict quasiCell] quasiExtendFunction g := by
    rw [← quasi_coe_measurePreserving.map_eq]
    apply (MeasurableEmbedding.subtype_coe quasiCell_measurable).ae_map_iff.mpr
    filter_upwards [hfg] with q hq
    simpa only [quasiExtendFunction_coe] using hq
  filter_upwards [(ae_restrict_iff' quasiCell_measurable).mp hr] with q hq
  by_cases hc : q ∈ quasiCell
  · exact hq hc
  · rw [quasiExtendFunction_zero f hc, quasiExtendFunction_zero g hc]

def quasiExtend (f : Lp ℂ 2 quasiMeasure) : AngularL2 :=
  (show MemLp (quasiExtendFunction f) 2 angularMeasure from by
    change eLpNorm (quasiExtendFunction f) 2 angularMeasure < ∞
    rw [quasiExtendFunction_eLpNorm]
    exact Lp.memLp f).toLp _

theorem quasiExtend_ae (f : Lp ℂ 2 quasiMeasure) :
    quasiExtend f =ᵐ[angularMeasure] quasiExtendFunction f := MemLp.coeFn_toLp _

theorem quasiExtend_norm (f : Lp ℂ 2 quasiMeasure) : ‖quasiExtend f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (quasiExtend_ae f), quasiExtendFunction_eLpNorm]

def quasiExtendLinear : Lp ℂ 2 quasiMeasure →ₗ[ℂ] AngularL2 where
  toFun := quasiExtend
  map_add' f g := by
    apply Lp.ext
    filter_upwards [quasiExtend_ae (f+g), quasiExtend_ae f, quasiExtend_ae g,
      quasiExtendFunction_ae_congr (Lp.coeFn_add f g),
      Lp.coeFn_add (quasiExtend f) (quasiExtend g)] with q hfg hf hg ha hb
    rw [hfg, hb, ha]
    change quasiExtendFunction (fun x => f x + g x) q = quasiExtend f q + quasiExtend g q
    rw [hf, hg]
    by_cases hq : q ∈ quasiCell
    · change quasiExtendFunction (fun x => f x + g x) (⟨q,hq⟩ : QuasiCell).val = _
      rw [quasiExtendFunction_coe, quasiExtendFunction_coe f ⟨q,hq⟩,
        quasiExtendFunction_coe g ⟨q,hq⟩]
    · rw [quasiExtendFunction_zero _ hq, quasiExtendFunction_zero _ hq, quasiExtendFunction_zero _ hq]
      exact (zero_add 0).symm
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [quasiExtend_ae (c • f), quasiExtend_ae f,
      quasiExtendFunction_ae_congr (Lp.coeFn_smul c f), Lp.coeFn_smul c (quasiExtend f)]
      with q hcf hf ha hb
    change quasiExtend (c • f) q = (c • quasiExtend f) q
    rw [hcf, hb, ha]
    change quasiExtendFunction (fun x => c * f x) q = c * quasiExtend f q
    rw [hf]
    by_cases hq : q ∈ quasiCell
    · change quasiExtendFunction (fun x => c * f x) (⟨q,hq⟩ : QuasiCell).val = _
      rw [quasiExtendFunction_coe, quasiExtendFunction_coe f ⟨q,hq⟩]
    · rw [quasiExtendFunction_zero _ hq, quasiExtendFunction_zero _ hq, mul_zero]

def quasiExtendIsometry : Lp ℂ 2 quasiMeasure →ₗᵢ[ℂ] AngularL2 where
  toLinearMap := quasiExtendLinear
  norm_map' := quasiExtend_norm

theorem angularToQuasi_extend (f : Lp ℂ 2 quasiMeasure) : angularToQuasi (quasiExtend f) = f := by
  apply Lp.ext
  filter_upwards [angularToQuasi_ae (quasiExtend f), quasi_coe_ae (quasiExtend_ae f)] with q ha hb
  rw [ha, hb, quasiExtendFunction_coe]

theorem quasiExtend_pairing (f : Lp ℂ 2 quasiMeasure) (g : AngularL2) :
    inner ℂ (quasiExtend f) g = inner ℂ f (angularToQuasi g) := by
  rw [L2.inner_def, L2.inner_def]
  have he : (fun q => inner ℂ (quasiExtend f q) (g q)) =ᵐ[angularMeasure]
      quasiCell.indicator (fun q => inner ℂ (quasiExtendFunction f q) (g q)) := by
    filter_upwards [quasiExtend_ae f] with q hq
    rw [hq]
    by_cases hc : q ∈ quasiCell
    · rw [Set.indicator_of_mem hc]
    · rw [Set.indicator_of_notMem hc, quasiExtendFunction_zero f hc, inner_zero_left]
  rw [integral_congr_ae he, integral_indicator quasiCell_measurable]
  have hi := quasi_coe_measurePreserving.integral_comp
    (MeasurableEmbedding.subtype_coe quasiCell_measurable) (fun q => inner ℂ (quasiExtendFunction f q) (g q))
  rw [← hi]
  apply integral_congr_ae
  filter_upwards [angularToQuasi_ae g] with q hq
  rw [quasiExtendFunction_coe, hq]

theorem quasiExtend_eq_adjoint :
    quasiExtendIsometry.toContinuousLinearMap = angularToQuasiCLM† := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  exact quasiExtend_pairing

theorem angularToQuasi_comp_adjoint :
    angularToQuasiCLM.comp (angularToQuasiCLM†) = ContinuousLinearMap.id ℂ (Lp ℂ 2 quasiMeasure) := by
  rw [← quasiExtend_eq_adjoint]
  apply ContinuousLinearMap.ext
  exact angularToQuasi_extend

end Maxwell.Continuum.EffectiveMass
