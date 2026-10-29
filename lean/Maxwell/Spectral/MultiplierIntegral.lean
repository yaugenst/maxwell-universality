import Maxwell.Spectral.SpectrumUnion

/-!
# Integral matrix elements of the continuous matrix multiplier

The L² matrix element is the integral of the pointwise finite-dimensional
matrix element. Integrability follows from the L² inner-product estimate.
-/

namespace Maxwell.Spectral

open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator

noncomputable section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]
variable {n : Type*} [Fintype n]

theorem matrixMultiplier_inner_integral (f : C(X, Matrix n n ℂ))
    (u v : MatrixL2 (n := n) μ) :
    inner ℂ u (matrixMultiplier μ f v) =
      ∫ t, ∑ i, star (u i t) * (f t).mulVec (fun j => v j t) i ∂μ := by
  rw [PiLp.inner_apply]
  simp_rw [L2.inner_def]
  rw [← integral_finsetSum Finset.univ
    (fun i _ => L2.integrable_inner (𝕜 := ℂ) (u i) (matrixMultiplier μ f v i))]
  apply integral_congr_ae
  filter_upwards [Filter.eventually_all.mpr (fun i => matrixMultiplier_ae μ f v i)]
    with t ht
  apply Finset.sum_congr rfl
  intro i _
  rw [ht i, RCLike.inner_apply']
  rfl

end
end Maxwell.Spectral
