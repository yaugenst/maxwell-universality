import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-! The integrable boundary singularity in the three-dimensional Green calculation.

The majorant is proved integrable with respect to three-dimensional Lebesgue
measure. The boundary passage then needs only measurability, the pointwise
resolvent limit away from the origin, and the inverse-square spectral bound.
-/

noncomputable section

namespace Maxwell.Green

open MeasureTheory Filter Set Metric
open scoped Topology

abbrev Momentum := EuclideanSpace ℝ (Fin 3)

/-- The singular part of the boundary-contour majorant. Its value at the origin
is immaterial, since a singleton has three-dimensional Lebesgue measure zero. -/
def inverseSquare (q : Momentum) : ℝ := ‖q‖ ^ (-2 : ℝ)

theorem inverseSquare_nonneg (q : Momentum) : 0 ≤ inverseSquare q :=
  Real.rpow_nonneg (norm_nonneg q) _

theorem inverseSquare_measurable : Measurable inverseSquare := by
  unfold inverseSquare
  fun_prop

/-- A positive quadratic lower bound on the real part of the spectral
denominator gives the required inverse-square bound on its reciprocal. -/
theorem norm_inv_le_inverseSquare (c : ℝ) (hc : 0 < c)
    (q : Momentum) (hq : q ≠ 0) (z : ℂ)
    (hz : c * ‖q‖ ^ 2 ≤ z.re) :
    ‖z⁻¹‖ ≤ c⁻¹ * inverseSquare q := by
  have hqnorm : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have hpositive : 0 < c * ‖q‖ ^ 2 := mul_pos hc (sq_pos_of_pos hqnorm)
  have hle : c * ‖q‖ ^ 2 ≤ ‖z‖ := hz.trans (Complex.re_le_norm z)
  have hinv := one_div_le_one_div_of_le hpositive hle
  simpa [one_div, norm_inv, inverseSquare, Real.rpow_neg (norm_nonneg q),
    Real.rpow_two, mul_inv_rev, mul_comm] using hinv

/-- The inverse-square singularity is integrable on every finite-radius ball
in three dimensions; the exponent criterion is the strict inequality `2 < 3`. -/
theorem inverseSquare_integrableOn_ball (r : ℝ) :
    IntegrableOn inverseSquare (ball (0 : Momentum) r) volume := by
  refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := 2)
    (by norm_num [Momentum]) (by norm_num [Momentum]) ?_
    inverseSquare_measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun q => by
    rw [Real.norm_of_nonneg (inverseSquare_nonneg q)]
    simp only [inverseSquare, one_mul, le_refl]

/-- The full spectral bound used in the boundary-contour passage. -/
def boundaryMajorant (C : ℝ) (q : Momentum) : ℝ := C * (1 + inverseSquare q)

/-- A simple spectral pole plus a bounded regular part has the integrable
majorant used below. This also applies to finite matrix-valued resolvents. -/
theorem norm_simplePole_le_boundaryMajorant
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (A B c : ℝ) (hc : 0 < c) (q : Momentum) (hq : q ≠ 0)
    (z : ℂ) (hz : c * ‖q‖ ^ 2 ≤ z.re)
    (a b : V) (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) :
    ‖z⁻¹ • a + b‖ ≤ boundaryMajorant (A * c⁻¹ + B) q := by
  have hA : 0 ≤ A := (norm_nonneg a).trans ha
  have hB : 0 ≤ B := (norm_nonneg b).trans hb
  have hInv : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have ht : 0 ≤ inverseSquare q := inverseSquare_nonneg q
  calc
    ‖z⁻¹ • a + b‖ ≤ ‖z⁻¹ • a‖ + ‖b‖ := norm_add_le _ _
    _ = ‖z⁻¹‖ * ‖a‖ + ‖b‖ := by rw [norm_smul]
    _ ≤ (c⁻¹ * inverseSquare q) * A + B :=
      add_le_add (mul_le_mul (norm_inv_le_inverseSquare c hc q hq z hz)
        ha (norm_nonneg a) (mul_nonneg hInv ht)) hb
    _ ≤ boundaryMajorant (A * c⁻¹ + B) q := by
      unfold boundaryMajorant
      nlinarith [mul_nonneg (mul_nonneg hA hInv) ht, mul_nonneg hB ht,
        mul_nonneg hA hInv]

theorem boundaryMajorant_integrableOn_ball (C r : ℝ) :
    IntegrableOn (boundaryMajorant C) (ball (0 : Momentum) r) volume := by
  exact ((integrableOn_const (C := (1 : ℝ)) measure_ball_lt_top.ne).add
    (inverseSquare_integrableOn_ball r)).const_mul C

/-- Every bounded integration domain, including a fundamental cube of the
Brillouin torus, inherits the integrable inverse-square majorant. -/
theorem boundaryMajorant_integrableOn (C : ℝ) {s : Set Momentum}
    (hs : Bornology.IsBounded s) : IntegrableOn (boundaryMajorant C) s volume := by
  obtain ⟨r, _, hr⟩ := hs.exists_pos_norm_lt
  exact (boundaryMajorant_integrableOn_ball C r).mono_set fun q hq =>
    mem_ball_zero_iff.mpr (hr q hq)

/-- Dominated boundary passage on a bounded momentum domain. A pointwise limit
at the singular momentum is not required. No integrability assumption on the
majorant is hidden among the premises: it follows from dimension three. -/
theorem tendsto_boundary_integral
    {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {l : Filter ι} [l.IsCountablyGenerated]
    {s : Set Momentum} (hs : MeasurableSet s) (hbounded : Bornology.IsBounded s)
    {F : ι → Momentum → V} {f : Momentum → V} (C : ℝ)
    (hmeas : ∀ᶠ a in l, AEStronglyMeasurable (F a) (volume.restrict s))
    (hbound : ∀ᶠ a in l, ∀ q ∈ s, q ≠ 0 → ‖F a q‖ ≤ boundaryMajorant C q)
    (hlim : ∀ q ∈ s, q ≠ 0 → Tendsto (fun a => F a q) l (𝓝 (f q))) :
    Tendsto (fun a => ∫ q in s, F a q) l (𝓝 (∫ q in s, f q)) := by
  apply tendsto_integral_filter_of_dominated_convergence (boundaryMajorant C) hmeas
  · filter_upwards [hbound] with a ha
    filter_upwards [self_mem_ae_restrict hs,
      ae_restrict_of_ae (volume.ae_ne (0 : Momentum))] with q hqs hq
    exact ha q hqs hq
  · exact boundaryMajorant_integrableOn C hbounded
  · filter_upwards [self_mem_ae_restrict hs,
      ae_restrict_of_ae (volume.ae_ne (0 : Momentum))] with q hqs hq
    exact hlim q hqs hq

end Maxwell.Green
