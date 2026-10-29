import Maxwell.Composition.PeriodicBackground

/-! The actual periodic inverse has opposite-displacement adjoint blocks;
the calibrated same-mode scalar coupling is therefore even. -/
noncomputable section
namespace Maxwell.Composition
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Defect
open Maxwell.Composition.TranslationBlocks Maxwell.Green.PhysicalCompression
open scoped InnerProduct

theorem weightedBlock_adjoint {N : ℕ} (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (T : Field →L[ℂ] Field) (hT : IsSelfAdjoint T)
    (hcomm : ∀ n, Commute (shift n) T) (n : Site) :
    (weightedBlock edges W T n).adjoint = weightedBlock edges W T (-n) := by
  have h1 := placedBlock_eq_weightedBlock edges W T hcomm n 0
  have h2 := placedBlock_eq_weightedBlock edges W T hcomm 0 n
  simp only [sub_zero] at h1
  simp only [zero_sub] at h2
  rw [← h1, ← h2]
  have ht : T.adjoint = T := hT
  simp only [placedBlock, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, ht,
    ContinuousLinearMap.comp_assoc]

theorem real_same_mode_adjoint {N : ℕ}
    (A : EuclideanSpace ℂ (Fin N) →L[ℂ] EuclideanSpace ℂ (Fin N))
    (u : EuclideanSpace ℝ (Fin N)) :
    inner ℝ u (realPartOperator A.adjoint u) = inner ℝ u (realPartOperator A u) := by
  change inner ℝ u (realCoordinatePart (A.adjoint (realCoordinateEmbedding u))) =
    inner ℝ u (realCoordinatePart (A (realCoordinateEmbedding u)))
  rw [realCoordinatePart_inner_right, realCoordinatePart_inner_right,
    ContinuousLinearMap.adjoint_inner_right]
  exact inner_re_symm (𝕜 := ℂ) _ _

namespace PhysicalPlatform

theorem bulk_inverse_selfAdjoint (P : PhysicalPlatform) :
    IsSelfAdjoint (P.bulk.symm : Field →L[ℂ] Field) := by
  rw [PeriodicScalarBackground.bulk_inverse_eq]
  exact (electricOperator_selfAdjoint (periodicCoefficient P.background.edgeMaterial) 25
    (by norm_num) P.background.edge_bound).ringInverse

theorem bulk_inverse_commutes (P : PhysicalPlatform) (n : Site) :
    Commute (shift n) (P.bulk.symm : Field →L[ℂ] Field) := by
  rw [PeriodicScalarBackground.bulk_inverse_eq]
  exact commute_ringInverse _ _ (shift_commutes_electric n P.background.edgeMaterial 25
    (by norm_num) P.background.edge_bound)

theorem same_mode_even (P : PhysicalPlatform) (n : Site) :
    inner ℝ P.mode (physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field) (-n) P.mode) =
      inner ℝ P.mode (physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field) n P.mode) := by
  unfold physicalGreenBlock
  rw [← weightedBlock_adjoint (ScalarDefect.edgeEmbedding P.defect)
    (ScalarDefect.coordinateWeight P.defect) _ P.bulk_inverse_selfAdjoint P.bulk_inverse_commutes n]
  exact real_same_mode_adjoint _ _

end PhysicalPlatform
end Maxwell.Composition
