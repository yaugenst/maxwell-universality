import Maxwell.Continuum.BlochQuasimomentum
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! Actual square-summable Bloch fibers, obtained by Fubini from the
measure-preserving alias regrouping. -/

noncomputable section

namespace Maxwell.Continuum.Bloch

open MeasureTheory Set Filter
open scoped ENNReal Topology

set_option backward.isDefEq.respectTransparency false

theorem scalar_fiber_summable (f : QuasiAliasL2) :
    ∀ᵐ q ∂quasiMeasure, Summable (fun n : Alias => ‖f (q, n)‖ ^ 2) := by
  have h := ((Lp.memLp f).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).prod_right_ae
  filter_upwards [h] with q hq
  simpa only [integrable_count_iff, norm_pow, norm_norm] using hq

/-- All three components at one alias, with the actual Euclidean polarization norm. -/
def polarizationValue (v : QuasiAliasFieldL2) (q : QuasiCell) (n : Alias) :
    FreeFiber.Polarization := WithLp.toLp 2 (fun i => v i (q, n))

@[simp] theorem polarizationValue_apply (v : QuasiAliasFieldL2) (q : QuasiCell)
    (n : Alias) (i : Fin 3) : polarizationValue v q n i = v i (q, n) := rfl

theorem polarizationValue_norm_sq (v : QuasiAliasFieldL2) (q : QuasiCell) (n : Alias) :
    ‖polarizationValue v q n‖ ^ 2 = ∑ i : Fin 3, ‖v i (q, n)‖ ^ 2 :=
  EuclideanSpace.norm_sq_eq _

theorem polarization_fiber_summable (v : QuasiAliasFieldL2) :
    ∀ᵐ q ∂quasiMeasure, Summable (fun n : Alias => ‖polarizationValue v q n‖ ^ 2) := by
  have h := ae_all_iff.mpr (fun i : Fin 3 => scalar_fiber_summable (v i))
  filter_upwards [h] with q hq
  simp only [polarizationValue_norm_sq]
  exact summable_sum fun i _ => hq i

theorem polarization_fiber_memℓp (v : QuasiAliasFieldL2) :
    ∀ᵐ q ∂quasiMeasure, Memℓp (polarizationValue v q) 2 := by
  filter_upwards [polarization_fiber_summable v] with q hq
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ENNReal).toReal)]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hq

/-- The actual infinite alias fiber. The series converges almost everywhere
by Fubini; its value on the null exceptional set is immaterial. -/
def fiber (v : QuasiAliasFieldL2) (q : QuasiCell) : FreeFiber.FiberSpace :=
  ∑' n : Alias, lp.single 2 n (polarizationValue v q n)

theorem fiber_eq (v : QuasiAliasFieldL2) (q : QuasiCell)
    (hq : Memℓp (polarizationValue v q) 2) :
    fiber v q = (⟨polarizationValue v q, hq⟩ : FreeFiber.FiberSpace) :=
  (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤)
    (⟨polarizationValue v q, hq⟩ : FreeFiber.FiberSpace)).tsum_eq

theorem fiber_apply_ae (v : QuasiAliasFieldL2) :
    ∀ᵐ q ∂quasiMeasure, ∀ n : Alias, fiber v q n = polarizationValue v q n := by
  filter_upwards [polarization_fiber_memℓp v] with q hq
  rw [fiber_eq v q hq]
  exact fun _ => rfl

theorem polarizationValue_stronglyMeasurable (v : QuasiAliasFieldL2) (n : Alias) :
    StronglyMeasurable (fun q => polarizationValue v q n) := by
  apply Measurable.stronglyMeasurable
  exact (WithLp.measurable_toLp 2 (Fin 3 → ℂ)).comp (Measurable.of_eval fun i =>
    (Lp.stronglyMeasurable (v i)).measurable.comp (measurable_id.prodMk measurable_const))

theorem fiber_aestronglyMeasurable (v : QuasiAliasFieldL2) :
    AEStronglyMeasurable (fiber v) quasiMeasure := by
  classical
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset Alias))
    (f := fun s q => ∑ n ∈ s, lp.single 2 n (polarizationValue v q n))
  · intro s
    apply StronglyMeasurable.aestronglyMeasurable
    apply Finset.stronglyMeasurable_fun_sum
    intro n _
    exact (lp.singleContinuousLinearMap ℂ (fun _ : Alias => FreeFiber.Polarization) 2 n).continuous.comp_stronglyMeasurable
      (polarizationValue_stronglyMeasurable v n)
  · filter_upwards [polarization_fiber_memℓp v] with q hq
    rw [fiber_eq v q hq]
    exact lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤)
      (⟨polarizationValue v q, hq⟩ : FreeFiber.FiberSpace)

end Maxwell.Continuum.Bloch
