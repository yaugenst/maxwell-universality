import Maxwell.Composition.PhysicalGram
import Maxwell.Composition.ModePerturbation
import Maxwell.Composition.Bright

/-! The complementary inverse and mixed-block bounds of the literal finite
weighted core, derived from the local certificate and the actual full-union
Green approximation. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Maxwell.Composition
open Maxwell.Spectral Maxwell.Spectral.Lattice

theorem contractive_sandwich_norm_le {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (L : G →L[ℝ] H) (A : F →L[ℝ] G) (R : E →L[ℝ] F)
    (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) : ‖L.comp (A.comp R)‖ ≤ ‖A‖ := by
  calc
    _ ≤ ‖L‖ * (‖A‖ * ‖R‖) := (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖A‖ * 1) := by gcongr
    _ = _ := by ring

theorem interactionOperator_diagonal_split {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (A : ι → ι → EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ) :
    interactionOperator A = diagonalBlocks (fun i => A i i) +
      interactionOperator (fun i j => if i = j then 0 else A i j) := by
  ext x ⟨i, k⟩
  change (∑ j, A i j (blockCoordinate x j)) k =
    (A i i (blockCoordinate x i)) k +
      (∑ j, (if i = j then 0 else A i j) (blockCoordinate x j)) k
  have he : (∑ j, A i j (blockCoordinate x j)) =
      (∑ j, if i = j then A i j (blockCoordinate x j) else 0) +
        ∑ j, (if i = j then 0 else A i j) (blockCoordinate x j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i = j <;> simp [h]
  simpa using congrArg (fun z : EuclideanSpace ℝ κ => z k) he

theorem modeBaseline_eq_diagonal {ι κ : Type*} [Fintype ι] [Fintype κ]
    (v : ι → ℝ) (G : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ) :
    modeBaseline v G = blockDiagonal (fun ij : ι × κ => v ij.1) - diagonalBlocks (fun _ => G) := by
  ext x ⟨i, j⟩
  rfl

namespace PhysicalCore

variable (P : PhysicalPlatform) (S : Source.SparseSystem) (precision d : ℕ)
variable (ζ : ℚ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
variable (hd : P.spacing.minimumDistance ≤ d) (hm : 0 < S.nnz)
variable (J : ℕ) (j : Fin J) (hj : j.val ∉ PhysicalGram.bad P S precision d ζ hζ hζ1 J)
local instance : DecidableEq (SourceDecoration.Vertex S precision) := Classical.decEq _

abbrev V := SourceDecoration.Vertex S precision
abbrev K := Fin (Maxwell.Defect.ScalarDefect.edges P.defect).card

def core (v : V S precision → ℚ) : EuclideanSpace ℝ (V S precision × K P) →L[ℝ]
    EuclideanSpace ℝ (V S precision × K P) :=
  blockDiagonal (fun ij => (v ij.1 : ℝ)⁻¹) - PhysicalGram.finiteGram P S precision d ζ hζ hζ1 hd hm J j hj

def interactionError : EuclideanSpace ℝ (V S precision × K P) →L[ℝ]
    EuclideanSpace ℝ (V S precision × K P) :=
  interactionOperator (PhysicalInteractions.offdiag P S precision d) +
    (PhysicalGram.finiteGram P S precision d ζ hζ hζ1 hd hm J j hj - PhysicalGram.infiniteGram P S precision d)

theorem infinite_split : PhysicalGram.infiniteGram P S precision d =
    diagonalBlocks (fun _ : V S precision => physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field) 0) +
      interactionOperator (PhysicalInteractions.offdiag P S precision d) := by
  rw [PhysicalGram.infiniteGram, interactionOperator_diagonal_split]
  have he : (fun i : V S precision => PhysicalInteractions.block P S precision d i i) =
      (fun _ : V S precision => physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field) 0) := by
    funext i
    simp only [PhysicalInteractions.block, sub_self, Matrix.mulVec_zero, smul_zero]
  rw [he]
  rfl

theorem core_eq_baseline (v : V S precision → ℚ) :
    core P S precision d ζ hζ hζ1 hd hm J j hj v =
      modeBaseline (fun i => (v i : ℝ)⁻¹)
        (physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field) 0) -
          interactionError P S precision d ζ hζ hζ1 hd hm J j hj := by
  rw [modeBaseline_eq_diagonal]
  unfold core interactionError
  rw [infinite_split]
  abel

theorem interactionError_bound (hζd : (ζ : ℝ) = (P.spacing.r : ℝ)^d)
    (hhalf : (ζ : ℝ) ≤ 1/2) :
    ‖interactionError P S precision d ζ hζ hζ1 hd hm J j hj‖ ≤
      64*(P.greenConstant : ℝ)*(ζ : ℝ) + (ζ : ℝ)^2 := by
  exact (norm_add_le _ _).trans (add_le_add
    (by simpa only [← hζd] using PhysicalInteractions.offdiag_bound P S precision d hd (hζd ▸ hhalf))
    (PhysicalGram.finiteGram_error P S precision d ζ hζ hζ1 hd hm J j hj))

theorem bright_complement_bound (v : V S precision → ℚ)
    (hζd : (ζ : ℝ) = (P.spacing.r : ℝ)^d) (hhalf : (ζ : ℝ) ≤ 1/2) :
    ‖(blockInjection P.mode).adjoint.comp
      ((core P S precision d ζ hζ hζ1 hd hm J j hj v).comp (modeComplementInclusion P.mode))‖ ≤
        (64*(P.greenConstant : ℝ)+1)*(ζ : ℝ) := by
  rw [core_eq_baseline]
  have hmixed := modePerturbation_upper P.mode P.mode_unit
    (physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field) 0) P.local_symmetric
    P.eigenvalue P.mode_equation (fun i => (v i : ℝ)⁻¹)
    (interactionError P S precision d ζ hζ hζ1 hd hm J j hj)
  have he := interactionError_bound P S precision d ζ hζ hζ1 hd hm J j hj hζd hhalf
  have hζR : (0 : ℝ) ≤ ζ := by exact_mod_cast hζ.le
  have h1 : (ζ : ℝ) ≤ 1 := by exact_mod_cast hζ1
  exact hmixed.trans (he.trans (by nlinarith))

theorem complement_bright_bound (v : V S precision → ℚ)
    (hζd : (ζ : ℝ) = (P.spacing.r : ℝ)^d) (hhalf : (ζ : ℝ) ≤ 1/2) :
    ‖(modeComplementProjection P.mode).comp
      ((core P S precision d ζ hζ hζ1 hd hm J j hj v).comp (blockInjection P.mode))‖ ≤
        (64*(P.greenConstant : ℝ)+1)*(ζ : ℝ) := by
  rw [core_eq_baseline]
  have hmixed := modePerturbation_lower P.mode P.mode_unit
    (physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field) 0)
    P.eigenvalue P.mode_equation (fun i => (v i : ℝ)⁻¹)
    (interactionError P S precision d ζ hζ hζ1 hd hm J j hj)
  have he := interactionError_bound P S precision d ζ hζ hζ1 hd hm J j hj hζd hhalf
  have hζR : (0 : ℝ) ≤ ζ := by exact_mod_cast hζ.le
  have h1 : (ζ : ℝ) ≤ 1 := by exact_mod_cast hζ1
  exact hmixed.trans (he.trans (by nlinarith))

theorem exists_complement_inverse (v : V S precision → ℚ)
    (hζd : (ζ : ℝ) = (P.spacing.r : ℝ)^d) (hhalf : (ζ : ℝ) ≤ 1/2)
    (t : ℝ) (ht : 0 ≤ t) (hv : ∀ i, |(v i : ℝ)⁻¹ - P.eigenvalue| ≤ t)
    (hsmall : t + 64*(P.greenConstant : ℝ)*(ζ : ℝ) + (ζ : ℝ)^2 ≤ (P.defectGap : ℝ)/2) :
    ∃ Dc : ModeComplement (ι := V S precision) P.mode ≃L[ℝ] ModeComplement (ι := V S precision) P.mode,
      (Dc : ModeComplement (ι := V S precision) P.mode →L[ℝ] ModeComplement (ι := V S precision) P.mode) =
        (modeComplementProjection P.mode).comp
          ((core P S precision d ζ hζ hζ1 hd hm J j hj v).comp (modeComplementInclusion P.mode)) ∧
      ‖(Dc.symm : ModeComplement (ι := V S precision) P.mode →L[ℝ] ModeComplement (ι := V S precision) P.mode)‖ ≤
        2/(P.defectGap : ℝ) := by
  rw [core_eq_baseline]
  apply modePerturbation_complement_inverse P.mode
    (physicalGreenBlock P.defect (P.bulk.symm : Field →L[ℂ] Field) 0)
    P.eigenvalue P.complement P.complement_operator (P.defectGap : ℝ)
    (by exact_mod_cast P.defectGap_pos) P.complement_inverse_bound
    (fun i => (v i : ℝ)⁻¹) t ht hv
  have he := interactionError_bound P S precision d ζ hζ hζ1 hd hm J j hj hζd hhalf
  linarith

end PhysicalCore
end Maxwell.Composition
