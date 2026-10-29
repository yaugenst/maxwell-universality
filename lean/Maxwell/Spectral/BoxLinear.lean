import Maxwell.Spectral.BoxMagnetic
import Maxwell.Spectral.BoxProjectionAssembly

namespace Maxwell.Spectral.BoxLinear

open Maxwell.Certificate.FourierBinding Maxwell.Spectral.PeriodicYee
open Maxwell.Spectral.PrimitiveYee BoxSymbols BoxCrossNorm BoxMagnetic

noncomputable section

def axis (j : Direction) : Momentum := Pi.single j 1

theorem linearSymbol_expansion (c q : Momentum) (f : Frequency) (a : Direction) :
    linearSymbol c q f a = ∑ j : Direction, (q j : ℂ)*linearSymbol c (axis j) f a := by
  fin_cases a <;> simp [linearSymbol, axis, Pi.single_apply, Fin.sum_univ_three] <;> ring

theorem linearFrequencyCurl_expansion (c q : Momentum) :
    linearFrequencyCurl c q = ∑ j : Direction, (q j : ℂ) • linearFrequencyCurl c (axis j) := by
  apply Matrix.ext
  intro a b
  change linearFrequencyCurl c q a b =
    ∑ j : Direction, (q j : ℂ)*linearFrequencyCurl c (axis j) a b
  by_cases hf : a.2 = b.2
  · obtain ⟨a, f⟩ := a
    obtain ⟨b, g⟩ := b
    change f = g at hf
    subst g
    fin_cases a <;> fin_cases b <;>
      simp [linearFrequencyCurl, blockMatrix, directSumMatrix, crossMatrix,
        linearSymbol, axis, Pi.single_apply, Fin.sum_univ_three] <;> ring
  · simp [linearFrequencyCurl, blockMatrix, directSumMatrix, hf]

theorem linearCurlOperator_expansion (c q : Momentum) :
    linearCurlOperator c q = ∑ j : Direction, (q j : ℂ) • linearCurlOperator c (axis j) := by
  unfold linearCurlOperator
  rw [linearFrequencyCurl_expansion, map_sum]
  simp only [map_smul]

variable {V W : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem appliedLinear_expansion (c q : Momentum) (F : V →L[ℂ] Field) :
    appliedLinear c q F = ∑ j : Direction, (q j : ℂ) • appliedLinear c (axis j) F := by
  unfold appliedLinear
  rw [linearCurlOperator_expansion c q]
  simp only [Fin.sum_univ_three,
    map_add, map_smulₛₗ, Complex.conj_ofReal, ContinuousLinearMap.add_comp,
    ContinuousLinearMap.smul_comp]

theorem firstCompression_expansion [CompleteSpace V]
    (material : Cell20 → ℝ) (c q : Momentum)
    (F : V →L[ℂ] Field) (G : W →L[ℂ] Field) :
    firstCompression material c q F G =
      ∑ j : Direction, (q j : ℂ) • firstCompression material c (axis j) F G := by
  rw [firstCompression, appliedLinear_expansion c q F, appliedLinear_expansion c q G]
  simp only [firstCompression, BoxCompression.sandwich, Fin.sum_univ_three, map_add, map_smulₛₗ, Complex.conj_ofReal,
    ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul]
  module

/-- Finite bounds for the three coordinate derivatives control their
actual directional linear term throughout the whole Cartesian box. -/
theorem linear_combination_bound
    {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℂ V]
    (T : Direction → V) (q h k : Direction → ℝ)
    (hh : ∀ j, |q j| ≤ h j) (hk : ∀ j, ‖T j‖ ≤ k j) :
    ‖∑ j, (q j : ℂ) • T j‖ ≤ ∑ j, h j*k j := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul (hh j) (hk j) (norm_nonneg _) ((abs_nonneg _).trans (hh j))

theorem firstCompression_box_bound [CompleteSpace V]
    (material : Cell20 → ℝ) (c q : Momentum)
    (F : V →L[ℂ] Field) (G : W →L[ℂ] Field) (h k : Direction → ℝ)
    (hh : ∀ j, |q j| ≤ h j)
    (hk : ∀ j, ‖firstCompression material c (axis j) F G‖ ≤ k j) :
    ‖firstCompression material c q F G‖ ≤ ∑ j, h j*k j := by
  rw [firstCompression_expansion]
  exact linear_combination_bound _ q h k hh hk

end
end Maxwell.Spectral.BoxLinear
