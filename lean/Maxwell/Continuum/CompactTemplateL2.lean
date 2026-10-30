import Maxwell.Continuum.CompactTemplate
import Maxwell.Continuum.FiniteSupportKernel
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Physical placement of the finite templates and actual L2 error control. -/

namespace Maxwell.Continuum.Profile

open MeasureTheory Set Metric

theorem scalar_ball_norm_bound (f : ScalarL2) (r : Space) {L C : ℝ} (hL : 1≤L)
    (hC : 0≤C) (hf : ∀ᵐ x ∂(volume : Measure Space), ‖f x‖≤C ∧ (L≤‖x-r‖ → f x=0)) :
    ‖f‖≤3*L^2*C := by
  have hn := KernelIntegral.norm_le_of_indicator_bound (measurableSet_closedBall (x := r) (ε := L))
    (isCompact_closedBall r L).measure_ne_top f (C := C)
  have hi : ∀ᵐ x ∂(volume : Measure Space), ‖f x‖≤(closedBall r L).indicator (fun _ => C) x := by
    filter_upwards [hf] with x hx
    by_cases hb : x ∈ closedBall r L
    · simpa only [Set.indicator_of_mem hb] using hx.1
    · rw [Set.indicator_of_notMem hb, hx.2]
      · simp
      · simp only [mem_closedBall, dist_eq_norm, not_le] at hb
        exact hb.le
  have hn := hn hi
  have hv : (volume : Measure Space).real (closedBall r L)=Real.pi*4/3*L^3 := by
    rw [measureReal_def, EuclideanSpace.volume_closedBall_fin_three,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity)]
    ring
  have hs : Real.sqrt ((volume : Measure Space).real (closedBall r L))≤3*L^2 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · rw [hv]
      have hpow : L^3≤L^4 := pow_le_pow_right₀ hL (by decide)
      have hpi : Real.pi*4/3≤8 := by linarith [Real.pi_lt_four]
      have hm := mul_le_mul_of_nonneg_right hpi (pow_nonneg (by linarith : 0≤L) 3)
      nlinarith only [hpow,hm, pow_nonneg (by linarith : 0≤L) 4]
  exact hn.trans (by nlinarith only [mul_le_mul_of_nonneg_left hs hC])

variable {ι : Type*} {B : ℕ}

noncomputable def encodedPlacedTemplate (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → ComplexDyadic B) (Q N : ℕ) (L : ℝ) (r x : Space) : ℂ :=
  encodedTemplate s q a Q N (L⁻¹ • (x-r))

noncomputable def idealPlacedTemplate (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → ComplexDyadic B) (L : ℝ) (r x : Space) : ℂ :=
  idealFiniteTemplate s q a (L⁻¹ • (x-r))

theorem scaled_outside_unit {L : ℝ} (hL : 0<L) (r x : Space) (hx : L≤‖x-r‖) :
    1≤‖L⁻¹ • (x-r)‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hL]
  have he : L⁻¹*L=1 := inv_mul_cancel₀ hL.ne'
  rw [← he]
  exact mul_le_mul_of_nonneg_left hx (inv_pos.mpr hL).le

theorem encodedPlacedTemplate_zero (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → ComplexDyadic B) (Q N : ℕ) {L : ℝ} (hL : 0<L) (r x : Space)
    (hx : L≤‖x-r‖) : encodedPlacedTemplate s q a Q N L r x=0 :=
  encodedTemplate_zero s q a Q N (scaled_outside_unit hL r x hx)

theorem idealPlacedTemplate_zero (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → ComplexDyadic B) {L : ℝ} (hL : 0<L) (r x : Space)
    (hx : L≤‖x-r‖) : idealPlacedTemplate s q a L r x=0 :=
  idealFiniteTemplate_zero s q a (scaled_outside_unit hL r x hx)

theorem encodedPlacedTemplate_memLp (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → ComplexDyadic B) (Q N : ℕ) {L : ℝ} (hL : 0<L) (r : Space) :
    MemLp (encodedPlacedTemplate s q a Q N L r) 2 (volume : Measure Space) := by
  have hc : Continuous (encodedPlacedTemplate s q a Q N L r) :=
    (encodedTemplate_continuous s q a Q N).comp ((continuous_id.sub continuous_const).const_smul L⁻¹)
  apply hc.memLp_of_hasCompactSupport
  apply HasCompactSupport.intro (isCompact_closedBall r L)
  intro x hx
  apply encodedPlacedTemplate_zero s q a Q N hL r x
  simp only [mem_closedBall, dist_eq_norm, not_le] at hx
  exact hx.le

theorem idealPlacedTemplate_memLp (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → ComplexDyadic B) {L : ℝ} (hL : 0<L) (r : Space) :
    MemLp (idealPlacedTemplate s q a L r) 2 (volume : Measure Space) := by
  have hc : Continuous (idealPlacedTemplate s q a L r) :=
    (idealFiniteTemplate_continuous s q a).comp ((continuous_id.sub continuous_const).const_smul L⁻¹)
  apply hc.memLp_of_hasCompactSupport
  apply HasCompactSupport.intro (isCompact_closedBall r L)
  intro x hx
  apply idealPlacedTemplate_zero s q a hL r x
  simp only [mem_closedBall, dist_eq_norm, not_le] at hx
  exact hx.le

noncomputable def encodedTemplateL2 (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → ComplexDyadic B) (Q N : ℕ) {L : ℝ} (hL : 0<L) (r : Space) : ScalarL2 :=
  (encodedPlacedTemplate_memLp s q a Q N hL r).toLp (encodedPlacedTemplate s q a Q N L r)

noncomputable def idealTemplateL2 (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → ComplexDyadic B) {L : ℝ} (hL : 0<L) (r : Space) : ScalarL2 :=
  (idealPlacedTemplate_memLp s q a hL r).toLp (idealPlacedTemplate s q a L r)

theorem templateL2_error (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → ComplexDyadic B) (Q N : ℕ) (hq : ∀ ν ∈ s, ∀ i, |q ν i|≤Q)
    {L : ℝ} (hL : 1≤L) (r : Space) :
    ‖idealTemplateL2 s q a (zero_lt_one.trans_le hL) r-
      encodedTemplateL2 s q a Q N (zero_lt_one.trans_le hL) r‖≤
      3*L^2*(∑ ν ∈ s, ‖complexDyadicValue (a ν)‖)*(1/2 : ℝ)^(N+22) := by
  have hp : 0<L := zero_lt_one.trans_le hL
  have hi : idealTemplateL2 s q a hp r =ᵐ[volume] idealPlacedTemplate s q a L r := MemLp.coeFn_toLp _
  have he : encodedTemplateL2 s q a Q N hp r =ᵐ[volume] encodedPlacedTemplate s q a Q N L r := MemLp.coeFn_toLp _
  have hn := scalar_ball_norm_bound
    (idealTemplateL2 s q a hp r-encodedTemplateL2 s q a Q N hp r) r hL
    (by positivity : 0≤(∑ ν ∈ s, ‖complexDyadicValue (a ν)‖)*(1/2 : ℝ)^(N+22))
  rw [mul_assoc (3*L^2)]
  apply hn
  filter_upwards [hi,he,Lp.coeFn_sub (idealTemplateL2 s q a hp r) (encodedTemplateL2 s q a Q N hp r)] with x hix hex hs
  simp only [hs,Pi.sub_apply,hix,hex]
  constructor
  · exact encodedTemplate_error s q a Q N hq (L⁻¹ • (x-r))
  · intro hx
    rw [idealPlacedTemplate_zero s q a hp r x hx, encodedPlacedTemplate_zero s q a Q N hp r x hx, sub_self]

#print axioms templateL2_error

end Maxwell.Continuum.Profile
