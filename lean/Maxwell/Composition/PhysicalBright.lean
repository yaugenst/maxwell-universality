import Maxwell.Composition.PhysicalBright.Nearest
import Maxwell.Composition.PhysicalCore

/-! The raw bright error of the literal finite PEC core. The coefficient five
is the sum of one diagonal rounding error, three incidence calibration errors,
and one full-union finite Green error. -/
noncomputable section
namespace Maxwell.Composition.PhysicalBright
open Matrix Maxwell.Spectral Maxwell.Spectral.Lattice

variable (P : PhysicalPlatform) (S : Source.SparseSystem) (precision d : ℕ)
local instance : DecidableEq (SourceIncidence.V S precision) := Classical.decEq _

def targetMatrix (α : ℝ) (β : Direction → ℚ) :=
  (SourceIncidence.graph S precision).targetMatrix α
    (fun e => (β (SourceIncidence.axis S precision e) : ℝ)) (SourceMediator.diagonal S precision)

theorem targetOperator_split (α : ℝ) (β : Direction → ℚ) :
    SourceMediator.operator S precision α (fun e => (β (SourceIncidence.axis S precision e) : ℝ)) =
      blockDiagonal (fun i => targetMatrix S precision α β i i) +
        Matrix.toEuclideanCLM (𝕜 := ℝ) (incidenceMatrix (SourceIncidence.graph S precision)
          (fun e => (β (SourceIncidence.axis S precision e) : ℝ))) := by
  unfold SourceMediator.operator SignedIncidence.targetOperator
  rw [targetMatrix_split, map_add]
  congr 1
  ext x i
  rw [Matrix.ofLp_toEuclideanCLM, blockDiagonal_apply]
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal, targetMatrix]

/-- The calibrated scalar diagonal contributes one copy of the tolerance. -/
theorem diagonal_calibration_bound (v : SourceDecoration.Vertex S precision → ℚ)
    (α : ℝ) (β : Direction → ℚ) (R : ℝ) (hR : 0 ≤ R)
    (hv : ∀ i, |(v i : ℝ)⁻¹ - (P.eigenvalue + targetMatrix S precision α β i i)| ≤ R) :
    ‖blockDiagonal (fun i => (v i : ℝ)⁻¹ - P.eigenvalue) -
      blockDiagonal (fun i => targetMatrix S precision α β i i)‖ ≤ R := by
  have h : blockDiagonal (fun i => (v i : ℝ)⁻¹ - P.eigenvalue) -
      blockDiagonal (fun i => targetMatrix S precision α β i i) =
        blockDiagonal (fun i => (v i : ℝ)⁻¹ -
          (P.eigenvalue + targetMatrix S precision α β i i)) := by
    ext x i
    simp only [_root_.sub_apply, PiLp.sub_apply, blockDiagonal_apply]
    ring
  rw [h]
  exact blockDiagonal_norm_le _ R hR hv

variable (ζ : ℚ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
variable (hd : P.spacing.minimumDistance ≤ d) (hm : 0 < S.nnz)
variable (J : ℕ) (j : Fin J) (hj : j.val ∉ PhysicalGram.bad P S precision d ζ hζ hζ1 J)

/-- A single finite-background good event and the actual scalar calibration
certificates imply the complete raw bright estimate for the actual target. -/
theorem raw_bright_error_bound (v : SourceDecoration.Vertex S precision → ℚ)
    (α : ℝ) (β : Direction → ℚ)
    (hζd : (ζ : ℝ) = (P.spacing.r : ℝ) ^ d) (hhalf : (ζ : ℝ) ≤ 1 / 2)
    (hβ : ∀ k, |(β k : ℝ) + axial P d k| ≤ (ζ : ℝ) ^ 2)
    (hv : ∀ i, |(v i : ℝ)⁻¹ - (P.eigenvalue + targetMatrix S precision α β i i)| ≤
      (ζ : ℝ) ^ 2) :
    ‖(blockInjection P.mode).adjoint.comp
      ((PhysicalCore.core P S precision d ζ hζ hζ1 hd hm J j hj v).comp (blockInjection P.mode)) -
        SourceMediator.operator S precision α
          (fun e => (β (SourceIncidence.axis S precision e) : ℝ))‖ ≤
      (256 * (P.greenConstant : ℝ) + 5) * (ζ : ℝ) ^ 2 := by
  let U := blockInjection (ι := SourceDecoration.Vertex S precision) P.mode
  let B := fun A : EuclideanSpace ℝ (SourceDecoration.Vertex S precision × PhysicalCore.K P) →L[ℝ]
      EuclideanSpace ℝ (SourceDecoration.Vertex S precision × PhysicalCore.K P) =>
    U.adjoint.comp (A.comp U)
  let D := blockDiagonal (fun i => (v i : ℝ)⁻¹ - P.eigenvalue) -
    blockDiagonal (fun i => targetMatrix S precision α β i i)
  let N := -B (interactionOperator (near P S precision d)) -
    Matrix.toEuclideanCLM (𝕜 := ℝ) (incidenceMatrix (SourceIncidence.graph S precision)
      (fun e => (β (SourceIncidence.axis S precision e) : ℝ)))
  let F := B (interactionOperator (PhysicalInteractions.far P S precision d))
  let E := B (PhysicalGram.finiteGram P S precision d ζ hζ hζ1 hd hm J j hj -
    PhysicalGram.infiniteGram P S precision d)
  have hD : ‖D‖ ≤ (ζ : ℝ) ^ 2 :=
    diagonal_calibration_bound P S precision v α β _ (sq_nonneg _) hv
  have hN : ‖N‖ ≤ 3 * (ζ : ℝ) ^ 2 :=
    near_calibration_bound P S precision d β _ (sq_nonneg _) hβ
  have hF : ‖F‖ ≤ 256 * (P.greenConstant : ℝ) * (ζ : ℝ) ^ 2 := by
    apply (contractive_sandwich_norm_le _ _ _ (modeAdjoint_norm_le (ι := SourceDecoration.Vertex S precision) P.mode P.mode_unit)
      (modeInjection_norm_le (ι := SourceDecoration.Vertex S precision) P.mode P.mode_unit)).trans
    simpa only [← hζd] using PhysicalInteractions.far_bound P S precision d hd (hζd ▸ hhalf)
  have hE : ‖E‖ ≤ (ζ : ℝ) ^ 2 :=
    (contractive_sandwich_norm_le _ _ _ (modeAdjoint_norm_le (ι := SourceDecoration.Vertex S precision) P.mode P.mode_unit)
      (modeInjection_norm_le (ι := SourceDecoration.Vertex S precision) P.mode P.mode_unit)).trans
      (PhysicalGram.finiteGram_error P S precision d ζ hζ hζ1 hd hm J j hj)
  have heq :
      (blockInjection P.mode).adjoint.comp
        ((PhysicalCore.core P S precision d ζ hζ hζ1 hd hm J j hj v).comp
          (blockInjection P.mode)) -
        SourceMediator.operator S precision α
          (fun e => (β (SourceIncidence.axis S precision e) : ℝ)) = D + N - F - E := by
    rw [PhysicalCore.core_eq_baseline, ContinuousLinearMap.sub_comp,
      ContinuousLinearMap.comp_sub, P.modeBaseline_bright, targetOperator_split]
    dsimp only [PhysicalCore.interactionError]
    rw [offdiag_near_far]
    simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
    dsimp only [D, N, F, E, B, U]
    abel
  rw [heq]
  calc
    ‖D + N - F - E‖ ≤ (‖D‖ + ‖N‖) + ‖F‖ + ‖E‖ := by
      calc
        _ ≤ ‖D + N - F‖ + ‖E‖ := norm_sub_le _ _
        _ ≤ (‖D + N‖ + ‖F‖) + ‖E‖ := add_le_add (norm_sub_le (D + N) F) le_rfl
        _ ≤ _ := add_le_add (add_le_add (norm_add_le D N) le_rfl) le_rfl
    _ ≤ ((ζ : ℝ)^2 + 3*(ζ : ℝ)^2) +
        256*(P.greenConstant : ℝ)*(ζ : ℝ)^2 + (ζ : ℝ)^2 :=
      add_le_add (add_le_add (add_le_add hD hN) hF) hE
    _ = _ := by ring

end Maxwell.Composition.PhysicalBright
