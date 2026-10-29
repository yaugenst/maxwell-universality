import Maxwell.Defect.FiniteCompression
import Maxwell.Defect.InverseContraction
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

namespace Maxwell.Defect.FiniteStencil

open Spectral Spectral.Lattice

/-- The finite rational matrix has the spectral inverse error bound of the
actual infinite operator. The gap and norm premises are exactly those needed
by the independently proved spectral estimate. -/
theorem rationalCompressionOperator_spectral_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (edges : ι ↪ Edge) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K) (z M : ℚ)
    (δ : ℝ) (N : ℕ) (hδ : 0 < δ) (hM : 0 < (M : ℝ)) (hδM : δ ≤ (M : ℝ))
    (hnorm : ‖operator m K hK hm z‖ ≤ (M : ℝ))
    (hgap : ∀ x ∈ spectrum ℝ (operator m K hK hm z), δ ≤ |x|) :
    ‖compressionOperator edges (Ring.inverse (operator m K hK hm z)) -
        rationalCompressionOperator edges m z ((M ^ 2)⁻¹) N‖ ≤
      δ⁻¹ * (1 - δ ^ 2 / (M : ℝ) ^ 2) ^ (N + 1) := by
  let : IsometricContinuousFunctionalCalculus ℝ (Field →L[ℂ] Field) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
  let : Nontrivial Field := by
    refine ⟨⟨lp.single 2 ((0 : Direction), (0 : Site)) (1 : ℂ), 0, ?_⟩⟩
    intro h
    have he := congrArg (fun f : Field => f ((0 : Direction), (0 : Site))) h
    simp at he
  apply (rationalCompressionOperator_error edges m K hK hm z ((M ^ 2)⁻¹) N _).trans
  rw [← inversePolynomial_real_cast]
  convert
    inversePolynomial_spectral_error (operator m K hK hm z)
      (operator_selfAdjoint m K hK hm z) δ (M : ℝ) N hδ hM hδM hnorm hgap using 1
  simp only [Rat.cast_inv, Rat.cast_pow]
  rfl

end Maxwell.Defect.FiniteStencil
