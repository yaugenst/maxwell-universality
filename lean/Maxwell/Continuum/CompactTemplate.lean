import Maxwell.Continuum.FourierTensorEncoding
import Maxwell.Continuum.ProfileEncoded
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! The actual finite source template: radial polynomial times tensor polynomial. -/

namespace Maxwell.Continuum.Profile

open MeasureTheory Set Metric

variable {ι : Type*} {B : ℕ}

noncomputable def idealFiniteTemplate (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → ComplexDyadic B) (y : Space) : ℂ :=
  (Well.qw y : ℂ)*finiteFourier s q a (fun i => y i)

noncomputable def encodedTemplate (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → ComplexDyadic B) (Q N : ℕ) (y : Space) : ℂ :=
  (encodedRoot N y : ℂ)*fourierTensor s q a Q N (fun i => y i)

theorem encodedTemplate_zero (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → ComplexDyadic B) (Q N : ℕ) {y : Space} (hy : 1≤‖y‖) :
    encodedTemplate s q a Q N y=0 := by
  rw [encodedTemplate, encodedRoot_zero hy, Complex.ofReal_zero, zero_mul]

theorem idealFiniteTemplate_zero (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → ComplexDyadic B) {y : Space} (hy : 1≤‖y‖) :
    idealFiniteTemplate s q a y=0 := by
  rw [idealFiniteTemplate, (Well.qw_zero_iff y).mpr hy, Complex.ofReal_zero, zero_mul]

theorem encodedTemplate_error (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → ComplexDyadic B) (Q N : ℕ) (hq : ∀ ν ∈ s, ∀ i, |q ν i|≤Q)
    (y : Space) :
    ‖idealFiniteTemplate s q a y-encodedTemplate s q a Q N y‖≤
      (∑ ν ∈ s, ‖complexDyadicValue (a ν)‖)*(1/2 : ℝ)^(N+22) := by
  by_cases hy : 1≤‖y‖
  · rw [idealFiniteTemplate_zero s q a hy, encodedTemplate_zero s q a Q N hy, sub_self, norm_zero]
    positivity
  have hy1 : ‖y‖≤1 := (lt_of_not_ge hy).le
  have hx (i : Fin 3) : y i ∈ Icc (-1 : ℝ) 1 := by
    apply abs_le.mp
    exact (show |y i|≤‖y‖ from PiLp.norm_apply_le y i).trans hy1
  have hf := fourierTensor_error s q a Q N hq hx
  have hg := fourierTensor_norm s q a Q N hq hx
  have hr := encodedRoot_error N y
  have hw : |Well.qw y|≤1 := by rw [abs_of_nonneg (Well.qw_nonneg y)]; exact Well.qw_le_one y
  calc
    _ = ‖(Well.qw y : ℂ)*(finiteFourier s q a (fun i => y i)-fourierTensor s q a Q N (fun i => y i))+
      ((Well.qw y : ℂ)-(encodedRoot N y : ℂ))*fourierTensor s q a Q N (fun i => y i)‖ := by
        unfold idealFiniteTemplate encodedTemplate
        congr 1
        ring
    _ ≤ ‖(Well.qw y : ℂ)*(finiteFourier s q a (fun i => y i)-fourierTensor s q a Q N (fun i => y i))‖+
      ‖((Well.qw y : ℂ)-(encodedRoot N y : ℂ))*fourierTensor s q a Q N (fun i => y i)‖ := norm_add_le _ _
    _ ≤ 1*((∑ ν ∈ s, ‖complexDyadicValue (a ν)‖)*(1/2 : ℝ)^(N+23))+
      (1/2 : ℝ)^(N+24)*(2*∑ ν ∈ s, ‖complexDyadicValue (a ν)‖) := by
      simp only [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact add_le_add
        (mul_le_mul hw hf (norm_nonneg _) zero_le_one)
        (mul_le_mul hr hg (norm_nonneg _) (by positivity))
    _ = _ := by
      rw [show N+24=(N+22)+2 by omega, show N+23=(N+22)+1 by omega, pow_add, pow_add]
      ring

theorem encodedTemplate_continuous (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → ComplexDyadic B) (Q N : ℕ) : Continuous (encodedTemplate s q a Q N) := by
  exact (Complex.continuous_ofReal.comp (encodedRoot_contDiff N).continuous).mul
    ((fourierTensor_continuous s q a Q N).comp (continuous_pi (fun i => PiLp.continuous_apply 2 _ i)))

theorem idealFiniteTemplate_continuous (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → ComplexDyadic B) : Continuous (idealFiniteTemplate s q a) := by
  have hf : Continuous (finiteFourier s q a) := by
    unfold finiteFourier
    apply continuous_finsetSum
    intro ν _
    apply continuous_const.mul
    unfold spatialPlaneWave
    apply Complex.continuous_exp.comp
    apply continuous_const.mul
    apply Complex.continuous_ofReal.comp
    apply continuous_const.mul
    apply continuous_finsetSum
    intro i _
    exact continuous_const.mul (continuous_apply i)
  exact (Complex.continuous_ofReal.comp Well.qw_contDiff.continuous).mul
    (hf.comp (continuous_pi (fun i => PiLp.continuous_apply 2 _ i)))

theorem encodedTemplate_compactSupport (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → ComplexDyadic B) (Q N : ℕ) : HasCompactSupport (encodedTemplate s q a Q N) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Space) 1)
  intro y hy
  apply encodedTemplate_zero s q a Q N
  simp only [mem_closedBall, dist_zero_right, not_le] at hy
  exact hy.le

theorem idealFiniteTemplate_compactSupport (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → ComplexDyadic B) : HasCompactSupport (idealFiniteTemplate s q a) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Space) 1)
  intro y hy
  apply idealFiniteTemplate_zero s q a
  simp only [mem_closedBall, dist_zero_right, not_le] at hy
  exact hy.le

theorem encodedTemplate_memLp (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → ComplexDyadic B) (Q N : ℕ) :
    MemLp (encodedTemplate s q a Q N) 2 (volume : Measure Space) :=
  (encodedTemplate_continuous s q a Q N).memLp_of_hasCompactSupport
    (encodedTemplate_compactSupport s q a Q N)

theorem idealFiniteTemplate_memLp (s : Finset ι) (q : ι → Fin 3 → ℚ)
    (a : ι → ComplexDyadic B) : MemLp (idealFiniteTemplate s q a) 2 (volume : Measure Space) :=
  (idealFiniteTemplate_continuous s q a).memLp_of_hasCompactSupport
    (idealFiniteTemplate_compactSupport s q a)

#print axioms encodedTemplate_error
#print axioms encodedTemplate_memLp

end Maxwell.Continuum.Profile
