import Maxwell.Continuum.SourceNumeratorSupport
import Maxwell.Continuum.PhysicalFiberL1Analytic
import Maxwell.Continuum.EffectiveMassDenominator

/-! Exact imaginary-momentum phases and physical reality of the compact source.
The exponential bounds use the Euclidean physical norm. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FreeFiber CellBandFourier PeriodicBand FiberNormalization

def sourceImaginary (q : Momentum) : Space := WithLp.toLp 2 (fun j => (q j).im)

theorem sourcePhase_norm (q : Momentum) (x : Space) :
    ‖spatialPhase q x‖ = Real.exp (-inner ℝ (sourceImaginary q) x) := by
  rw [spatialPhase, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_sub, sourceImaginary, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Fin.sum_univ_three, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero]
  ring

theorem sourcePhase_norm_le (q : Momentum) (x : Space) :
    ‖spatialPhase q x‖ ≤ Real.exp (‖sourceImaginary q‖ * ‖x‖) := by
  rw [sourcePhase_norm]
  apply Real.exp_le_exp.mpr
  exact (neg_le_abs _).trans (by simpa only [Real.norm_eq_abs] using
    (norm_inner_le_norm (𝕜 := ℝ) (sourceImaginary q) x))

theorem sourcePhase_norm_on_support {h : ℝ} (_hh : 0 < h) (q : Momentum)
    {x : Space} (hx : ‖x‖ ≤ h⁻¹) :
    ‖spatialPhase q x‖ ≤ Real.exp (‖sourceImaginary q‖ / h) := by
  apply (sourcePhase_norm_le q x).trans
  apply Real.exp_le_exp.mpr
  simpa only [div_eq_mul_inv] using
    mul_le_mul_of_nonneg_left hx (norm_nonneg (sourceImaginary q))

theorem sourceImaginary_imaginary (β : Space) :
    sourceImaginary (Complex.I • physicalMomentum β) = β := by
  apply PiLp.ext
  intro j
  simp only [sourceImaginary, PiLp.toLp_apply, Pi.smul_apply, smul_eq_mul,
    physicalMomentum, realMomentum, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]

theorem sourcePhase_imaginary (β x : Space) :
    spatialPhase (Complex.I • physicalMomentum β) x =
      (Real.exp (-inner ℝ β x) : ℂ) := by
  rw [spatialPhase, Complex.ofReal_exp]
  congr 1
  simp only [Pi.smul_apply, smul_eq_mul, physicalMomentum, realMomentum,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    Complex.ofReal_neg, Complex.ofReal_sum, Complex.ofReal_mul]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = (Complex.I * Complex.I) * ((x j : ℂ) * (β j : ℂ)) := by ring
    _ = _ := by rw [Complex.I_mul_I, neg_one_mul]

theorem sourcePhase_imaginary_bounds {h : ℝ} (hh : 0 < h)
    {β x : Space} (hβ : ‖β‖ ≤ h) (hx : ‖x‖ ≤ h⁻¹) :
    (1/4 : ℝ) ≤ Real.exp (-inner ℝ β x) ∧ Real.exp (-inner ℝ β x) ≤ 4 := by
  have hd : |inner ℝ β x| ≤ 1 := by
    have hi : |inner ℝ β x| ≤ ‖β‖ * ‖x‖ := by
      simpa only [Real.norm_eq_abs] using (norm_inner_le_norm (𝕜 := ℝ) β x)
    apply hi.trans
    calc
      ‖β‖ * ‖x‖ ≤ h * h⁻¹ := mul_le_mul hβ hx (norm_nonneg _) hh.le
      _ = 1 := mul_inv_cancel₀ hh.ne'
  have he : Real.exp 1 < (4 : ℝ) := Real.exp_one_lt_three.trans (by norm_num)
  constructor
  · have hl : Real.exp (-1) ≤ Real.exp (-inner ℝ β x) :=
      Real.exp_le_exp.mpr (by linarith [(abs_le.mp hd).2])
    apply le_trans _ hl
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos _) he.le
  · exact (Real.exp_le_exp.mpr (by linarith [(abs_le.mp hd).1])).trans he.le

theorem sourcePhase_star {q : Momentum} (hq : star q = -q) (x : Space) :
    star (spatialPhase q x) = spatialPhase q x := by
  rw [spatialPhase_star, hq, neg_neg]

theorem sourceCell_real {q : Momentum} (hq : q ∈ physicalChart) (hi : star q = -q) (x : Space) :
    star (cellEigenfunction (unscale q) x) = cellEigenfunction (unscale q) x := by
  apply cellEigenfunction_real_imaginary (unscale_mem_chart hq)
  simp only [unscale, star_smul, star_inv₀, Complex.star_def,
    Complex.conj_ofReal, hi, smul_neg]

theorem sourceValue_real {h : ℝ} {u : FieldL2} (hu : fieldConjugation u = u) :
    ∀ᵐ x ∂(volume : Measure Space), star (sourceValue h u x) = sourceValue h u x := by
  have hs := sourceMode_real h hu
  filter_upwards [ae_all_iff.mpr (fun j => scalarConjugation_ae (sourceMode h u j))] with x hx
  apply PiLp.ext
  intro j
  have he : scalarConjugation (sourceMode h u j) = sourceMode h u j :=
    congrArg (fun v : FieldL2 => v j) hs
  have hj := hx j
  rw [he] at hj
  exact hj.symm

#print axioms sourcePhase_imaginary_bounds
#print axioms sourceValue_real

end Maxwell.Continuum.EffectiveMass
