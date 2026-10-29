import Maxwell.Spectral.ResidualCertificate
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach

namespace Maxwell.Spectral.SeparatedInverse

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [FiniteDimensional ℂ H]

def shifted (T : H →L[ℂ] H) (c : ℝ) : H →L[ℂ] H :=
  T - (c : ℂ) • ContinuousLinearMap.id ℂ H

theorem norm_lower (T : H →L[ℂ] H) (hT : T.toLinearMap.IsSymmetric)
    (c g : ℝ) (hg : 0 ≤ g)
    (hgap : ∀ i, g ≤ |hT.eigenvalues rfl i - c|) (v : H) :
    g * ‖v‖ ≤ ‖shifted T c v‖ := by
  have hsq : g ^ 2 * ‖v‖ ^ 2 ≤ ‖shifted T c v‖ ^ 2 := by
    change _ ≤ ‖T v - (c : ℂ) • v‖ ^ 2
    have hres := shifted_norm_sq_spectral T.toLinearMap hT c v
    change ‖T v - (c : ℂ) • v‖ ^ 2 = _ at hres
    rw [hres]
    have hn : ∑ i, ‖(hT.eigenvectorBasis rfl).repr v i‖ ^ 2 = ‖v‖ ^ 2 := by
      simpa only [OrthonormalBasis.repr_apply_apply] using
        (hT.eigenvectorBasis rfl).sum_sq_norm_inner_right v
    rw [← hn, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hi := hgap i
    nlinarith only [hi, hg, abs_nonneg (hT.eigenvalues rfl i - c),
      sq_abs (hT.eigenvalues rfl i - c)]
  nlinarith only [hsq, mul_nonneg hg (norm_nonneg v), norm_nonneg (shifted T c v)]

theorem shifted_injective (T : H →L[ℂ] H) (hT : T.toLinearMap.IsSymmetric)
    (c g : ℝ) (hg : 0 < g)
    (hgap : ∀ i, g ≤ |hT.eigenvalues rfl i - c|) :
    Function.Injective (shifted T c) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have h := norm_lower T hT c g hg.le hgap v
  change shifted T c v = 0 at hv
  rw [hv, norm_zero] at h
  apply norm_eq_zero.mp
  nlinarith only [h, hg, norm_nonneg v]

variable [CompleteSpace H]

/-- The real spectral separation constructs the full shifted inverse. -/
def equiv (T : H →L[ℂ] H) (hT : T.toLinearMap.IsSymmetric)
    (c g : ℝ) (hg : 0 < g)
    (hgap : ∀ i, g ≤ |hT.eigenvalues rfl i - c|) : H ≃L[ℂ] H :=
  ContinuousLinearEquiv.ofBijective (shifted T c)
    (LinearMap.ker_eq_bot.mpr (shifted_injective T hT c g hg hgap))
    (LinearMap.range_eq_top.mpr
      ((shifted T c).toLinearMap.injective_iff_surjective.mp
        (shifted_injective T hT c g hg hgap)))

theorem inverse_norm_le (T : H →L[ℂ] H) (hT : T.toLinearMap.IsSymmetric)
    (c g : ℝ) (hg : 0 < g)
    (hgap : ∀ i, g ≤ |hT.eigenvalues rfl i - c|) :
    ‖(equiv T hT c g hg hgap).symm.toContinuousLinearMap‖ ≤ g⁻¹ := by
  apply (equiv T hT c g hg hgap).symm.toContinuousLinearMap.opNorm_le_bound
    (inv_nonneg.mpr hg.le)
  intro v
  have h := norm_lower T hT c g hg.le hgap ((equiv T hT c g hg hgap).symm v)
  have he : shifted T c ((equiv T hT c g hg hgap).symm v) = v :=
    (equiv T hT c g hg hgap).apply_symm_apply v
  rw [he] at h
  change ‖(equiv T hT c g hg hgap).symm v‖ ≤ g⁻¹ * ‖v‖
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ hg).mpr (by nlinarith only [h])

end
end Maxwell.Spectral.SeparatedInverse
