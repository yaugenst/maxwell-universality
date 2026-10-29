import Maxwell.Continuum.BlochFiber

/-! Fubini's norm identity for the actual Hilbert-valued Bloch fibers. -/

noncomputable section

namespace Maxwell.Continuum.Bloch

open MeasureTheory Set Filter
open scoped ENNReal Topology

set_option backward.isDefEq.respectTransparency false

theorem complexL2_norm_sq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : Lp ℂ 2 μ) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq f]
  change (∫ x, inner ℝ (f x) (f x) ∂μ) = _
  simp only [real_inner_self_eq_norm_sq]

theorem scalar_fiber_integrable (f : QuasiAliasL2) :
    ∀ᵐ q ∂quasiMeasure, Integrable (fun n : Alias => ‖f (q, n)‖ ^ 2) Measure.count :=
  ((Lp.memLp f).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).prod_right_ae

theorem scalar_fiber_energy_integrable (f : QuasiAliasL2) :
    Integrable (fun q => ∫ n : Alias, ‖f (q, n)‖ ^ 2 ∂Measure.count) quasiMeasure :=
  ((Lp.memLp f).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).integral_prod_left

theorem scalar_fubini_norm (f : QuasiAliasL2) :
    ∫ q, ∫ n : Alias, ‖f (q, n)‖ ^ 2 ∂Measure.count ∂quasiMeasure = ‖f‖ ^ 2 := by
  rw [complexL2_norm_sq]
  exact (integral_prod _ ((Lp.memLp f).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0))).symm

theorem fiber_norm_sq_ae (v : QuasiAliasFieldL2) :
    ∀ᵐ q ∂quasiMeasure, ‖fiber v q‖ ^ 2 =
      ∑ i : Fin 3, ∫ n : Alias, ‖v i (q, n)‖ ^ 2 ∂Measure.count := by
  have hmem := polarization_fiber_memℓp v
  have hs := ae_all_iff.mpr (fun i : Fin 3 => scalar_fiber_summable (v i))
  have hi := ae_all_iff.mpr (fun i : Fin 3 => scalar_fiber_integrable (v i))
  filter_upwards [hmem, hs, hi] with q hq hsq hiq
  have hn := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal) (fiber v q)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hn
  rw [hn]
  have hv : ∀ n, fiber v q n = polarizationValue v q n := by
    rw [fiber_eq v q hq]
    exact fun _ => rfl
  simp only [hv, polarizationValue_norm_sq]
  rw [Summable.tsum_finsetSum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hsq i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_countable (hiq i)]
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]

theorem fiber_norm_sq_integrable (v : QuasiAliasFieldL2) :
    Integrable (fun q => ‖fiber v q‖ ^ 2) quasiMeasure := by
  apply (integrable_finsetSum Finset.univ
    (fun i _ => scalar_fiber_energy_integrable (v i))).congr
  filter_upwards [fiber_norm_sq_ae v] with q hq using hq.symm

theorem fiber_memLp (v : QuasiAliasFieldL2) : MemLp (fiber v) 2 quasiMeasure :=
  (memLp_two_iff_integrable_sq_norm (fiber_aestronglyMeasurable v)).mpr
    (fiber_norm_sq_integrable v)

theorem fiber_fubini_norm (v : QuasiAliasFieldL2) :
    ∫ q, ‖fiber v q‖ ^ 2 ∂quasiMeasure = ‖v‖ ^ 2 := by
  rw [integral_congr_ae (fiber_norm_sq_ae v)]
  rw [integral_finsetSum Finset.univ (fun i _ => scalar_fiber_energy_integrable (v i))]
  simp only [scalar_fubini_norm]
  exact (PiLp.norm_sq_eq_of_L2 _ v).symm

abbrev FiberL2 := Lp FreeFiber.FiberSpace 2 quasiMeasure

/-- Genuine Hilbert-valued L² regrouping, not a formal direct-integral symbol. -/
def toFiberL2 (v : QuasiAliasFieldL2) : FiberL2 := (fiber_memLp v).toLp (fiber v)

theorem toFiberL2_ae (v : QuasiAliasFieldL2) :
    toFiberL2 v =ᵐ[quasiMeasure] fiber v := (fiber_memLp v).coeFn_toLp

theorem toFiberL2_norm (v : QuasiAliasFieldL2) : ‖toFiberL2 v‖ = ‖v‖ := by
  have h : ‖toFiberL2 v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq (toFiberL2 v)]
    change (∫ q, inner ℝ (toFiberL2 v q) (toFiberL2 v q) ∂quasiMeasure) = _
    simp only [real_inner_self_eq_norm_sq]
    exact (integral_congr_ae ((toFiberL2_ae v).fun_comp (fun z => ‖z‖ ^ 2))).trans
      (fiber_fubini_norm v)
  nlinarith [norm_nonneg (toFiberL2 v), norm_nonneg v]

end Maxwell.Continuum.Bloch
