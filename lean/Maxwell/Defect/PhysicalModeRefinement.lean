import Maxwell.Defect.CertifiedModeRefinement
import Maxwell.Defect.FixedDefectSelection
import Maxwell.Green.BinaryCompression

/-! A successful finite physical defect check supplies an executable
binary-precision refinement of that same actual mode. -/
namespace Maxwell.Defect
open InnerProductSpace Module.End Spectral Spectral.Lattice

def scalarBinaryCompression (D : Finset Site) (m : Edge → ℚ) (z M δ : ℚ)
    (hδ : 0 < δ) (hM : 0 < M) (hδM : δ ≤ M) (b : ℕ) :
    Matrix (Fin (ScalarDefect.edges D).card) (Fin (ScalarDefect.edges D).card) ℚ :=
  FiniteStencil.binaryCompressionMatrix (ScalarDefect.edgeEmbedding D) m z δ M
    hδ hM hδM (ScalarDefect.coordinateWeight D) b

set_option maxHeartbeats 800000 in
theorem scalarModeBudgetCheck_refinement (D : Finset Site) (m : Edge → ℚ)
    (K : ℝ) (hK : 0 ≤ K) (hm : ∀ e, |(m e : ℝ)| ≤ K) (z M δ threshold budget : ℚ)
    (hδ : 0 < δ) (hM : 0 < M) (hδM : δ ≤ M)
    (hnorm : ‖FiniteStencil.operator m K hK hm z‖ ≤ (M : ℝ))
    (hgap : ∀ x ∈ spectrum ℝ (FiniteStencil.operator m K hK hm z), (δ : ℝ) ≤ |x|)
    (w : EuclideanSpace ℝ (Fin (ScalarDefect.edges D).card))
    (q : ℕ → Fin (ScalarDefect.edges D).card → ℚ) (β : ℕ → ℚ) (sourceBound : ℚ)
    (hq : ∀ k, ‖w - rationalVector (q k)‖ ≤ (β k : ℝ))
    (hw : ‖w‖ ≤ (sourceBound : ℝ)) (stage : ℕ)
    (hcheck : scalarModeBudgetCheck D m z M δ threshold budget q β sourceBound stage = true) :
    ∃ μ : ℝ, ∃ u : EuclideanSpace ℝ (Fin (ScalarDefect.edges D).card),
      ‖u‖ = 1 ∧ FiniteStencil.weightedInverseCompression (ScalarDefect.edgeEmbedding D)
        m K hK hm z (ScalarDefect.coordinateWeight D) u = μ • u ∧
      (threshold : ℝ) < μ ∧ Module.finrank ℝ (eigenspace
        (FiniteStencil.weightedInverseCompression (ScalarDefect.edgeEmbedding D)
          m K hK hm z (ScalarDefect.coordinateWeight D)).toLinearMap μ) = 1 ∧
      (budget : ℝ) < |inner ℝ w u| ^ 2 ∧
      ∃ P : ModeRefinementPlan (ScalarDefect.edges D).card, ∀ b,
        ‖rationalVector (P.approximation (scalarBinaryCompression D m z M δ hδ hM hδM)
          (1 + 2 * δ⁻¹) b)‖ ≤ 1 ∧
        ‖rationalVector (P.approximation (scalarBinaryCompression D m z M δ hδ hM hδM)
          (1 + 2 * δ⁻¹) b) - u‖ ≤ (1 / 2 : ℝ)^b := by
  unfold scalarModeBudgetCheck modeBudgetCheck at hcheck
  split at hcheck
  · simp at hcheck
  · rename_i c a hca
    apply modeBudget_refinement c a _ _ threshold _ _ sourceBound budget _ w
      (FiniteStencil.weightedInverseCompression_symmetric _ m K hK hm z _)
      _ (hq _) hw hcheck (scalarBinaryCompression D m z M δ hδ hM hδM)
      (1 + 2 * δ⁻¹) (by positivity)
    · intro b
      rw [norm_sub_rev]
      have hh := FiniteStencil.binaryCompressionMatrix_error (ScalarDefect.edgeEmbedding D)
        m K hK hm z δ M hδ hM hδM (ScalarDefect.coordinateWeight D)
        (fun i => le_trans (by norm_num) (ScalarDefect.coordinateWeight_bounds D i).1)
        (fun i => (ScalarDefect.coordinateWeight_bounds D i).2) hnorm hgap b
      simpa only [scalarBinaryCompression, Rat.cast_add, Rat.cast_one, Rat.cast_mul,
        Rat.cast_ofNat, Rat.cast_inv] using hh
    · rw [norm_sub_rev]
      exact FiniteStencil.effectiveCompressionMatrix_error _ m K hK hm z M δ _ _ _ _
        hδ hM hδM hnorm hgap

end Maxwell.Defect
