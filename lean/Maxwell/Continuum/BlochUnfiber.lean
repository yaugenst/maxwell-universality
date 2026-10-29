import Maxwell.Continuum.BlochFubini

/-! The reverse, literal ungrouping of an L² field of infinite Bloch fibers. -/

noncomputable section

namespace Maxwell.Continuum.Bloch

open MeasureTheory Set Filter
open scoped ENNReal Topology

set_option backward.isDefEq.respectTransparency false

theorem polarization_component_summable (u : FreeFiber.FiberSpace) (i : Fin 3) :
    Summable (fun n : Alias => ‖u n i‖ ^ 2) := by
  have hs : Summable (fun n : Alias => ‖u n‖ ^ 2) := by
    have h := (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mp u.property
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun n =>
    pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (u n) i) 2) hs

theorem polarization_component_integrable (u : FreeFiber.FiberSpace) (i : Fin 3) :
    Integrable (fun n : Alias => ‖u n i‖ ^ 2) Measure.count := by
  rw [integrable_count_iff]
  simpa only [norm_pow, norm_norm] using polarization_component_summable u i

theorem polarization_component_energy_le (u : FreeFiber.FiberSpace) (i : Fin 3) :
    ∫ n : Alias, ‖u n i‖ ^ 2 ∂Measure.count ≤ ‖u‖ ^ 2 := by
  rw [integral_countable (polarization_component_integrable u i)]
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  have hn := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) u
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hn
  rw [hn]
  apply Summable.tsum_le_tsum (fun n =>
    pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (u n) i) 2)
    (polarization_component_summable u i)
  have h := (memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)).mp u.property
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

def unfiberValue (w : FiberL2) (i : Fin 3) (qn : QuasiCell × Alias) : ℂ := w qn.1 qn.2 i

theorem unfiberValue_stronglyMeasurable (w : FiberL2) (i : Fin 3) :
    StronglyMeasurable (unfiberValue w i) := by
  apply Measurable.stronglyMeasurable
  apply measurable_from_prod_countable_left
  intro n
  exact ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 3 => ℂ) i).comp
    (lp.evalCLM ℂ (fun _ : Alias => FreeFiber.Polarization) 2 n).continuous).comp_stronglyMeasurable
      (Lp.stronglyMeasurable w) |>.measurable

theorem unfiberValue_norm_sq_integrable (w : FiberL2) (i : Fin 3) :
    Integrable (fun qn => ‖unfiberValue w i qn‖ ^ 2) (quasiMeasure.prod Measure.count) := by
  have hm := (unfiberValue_stronglyMeasurable w i).norm.pow 2
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall fun q => polarization_component_integrable (w q) i
  · simp only [Pi.pow_apply, norm_pow, norm_norm]
    apply ((Lp.memLp w).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).mono'
      hm.integral_prod_right'.aestronglyMeasurable
    exact Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
      exact polarization_component_energy_le (w q) i

theorem unfiberValue_memLp (w : FiberL2) (i : Fin 3) :
    MemLp (unfiberValue w i) 2 (quasiMeasure.prod Measure.count) :=
  (memLp_two_iff_integrable_sq_norm
    (unfiberValue_stronglyMeasurable w i).aestronglyMeasurable).mpr
      (unfiberValue_norm_sq_integrable w i)

/-- Every Hilbert-valued fiber field gives an actual product-measure L² field. -/
def fromFiberL2 (w : FiberL2) : QuasiAliasFieldL2 :=
  WithLp.toLp 2 (fun i => (unfiberValue_memLp w i).toLp (unfiberValue w i))

theorem fromFiberL2_ae (w : FiberL2) (i : Fin 3) :
    fromFiberL2 w i =ᵐ[quasiMeasure.prod Measure.count] unfiberValue w i :=
  (unfiberValue_memLp w i).coeFn_toLp

theorem product_ae_all_alias {p : QuasiCell × Alias → Prop}
    (h : ∀ᵐ qn ∂quasiMeasure.prod Measure.count, p qn) :
    ∀ᵐ q ∂quasiMeasure, ∀ n : Alias, p (q, n) := by
  simpa only [Measure.ae_count_iff] using Measure.ae_ae_of_ae_prod h

theorem toFiberL2_coordinate_ae (v : QuasiAliasFieldL2) :
    ∀ᵐ q ∂quasiMeasure, ∀ n : Alias, ∀ i : Fin 3, toFiberL2 v q n i = v i (q, n) := by
  filter_upwards [toFiberL2_ae v, fiber_apply_ae v] with q hq hv
  intro n i
  rw [hq, hv]
  rfl

theorem toFiberL2_fromFiberL2 (w : FiberL2) : toFiberL2 (fromFiberL2 w) = w := by
  apply Lp.ext
  have h := ae_all_iff.mpr (fun i : Fin 3 =>
    product_ae_all_alias (fromFiberL2_ae w i))
  filter_upwards [toFiberL2_coordinate_ae (fromFiberL2 w), h] with q hq hi
  apply lp.ext
  funext n
  apply PiLp.ext
  intro i
  exact (hq n i).trans (hi i n)

end Maxwell.Continuum.Bloch
