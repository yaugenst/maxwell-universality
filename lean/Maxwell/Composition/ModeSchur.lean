import Maxwell.Composition.OrthogonalModes
import Maxwell.Composition.Complement

/-! Actual repeated local-mode decomposition inserted into complementary
block inversion. The remaining invertibility inputs are exactly the local
complementary block and the physical bright Schur block. -/

noncomputable section

namespace Maxwell.Composition

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def modeSchur (q : EuclideanSpace ℝ κ)
    (M : EuclideanSpace ℝ (ι × κ) →L[ℝ] EuclideanSpace ℝ (ι × κ))
    (Dc : ModeComplement (ι := ι) q ≃L[ℝ] ModeComplement (ι := ι) q) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  brightSchurOperator M (blockInjection (ι := ι) q) (modeComplementInclusion (ι := ι) q)
    (blockInjection (ι := ι) q).adjoint (modeComplementProjection (ι := ι) q) Dc

def modeComplementaryEquiv (q : EuclideanSpace ℝ κ) (hq : ‖q‖ = 1)
    (M : EuclideanSpace ℝ (ι × κ) →L[ℝ] EuclideanSpace ℝ (ι × κ))
    (Dc : ModeComplement (ι := ι) q ≃L[ℝ] ModeComplement (ι := ι) q)
    (S : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι)
    (hDc : ∀ c, modeComplementProjection (ι := ι) q (M (modeComplementInclusion (ι := ι) q c)) = Dc c)
    (hS : (S : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) = modeSchur q M Dc) :
    EuclideanSpace ℝ (ι × κ) ≃L[ℝ] EuclideanSpace ℝ (ι × κ) :=
  complementaryEquiv M (blockInjection (ι := ι) q) (modeComplementInclusion (ι := ι) q)
    (blockInjection (ι := ι) q).adjoint (modeComplementProjection (ι := ι) q) Dc S
    (modeCoordinate_decomposition (ι := ι) q hq) hDc hS
    (blockInjection_adjoint_cancel (ι := ι) q hq) (modeAdjoint_inclusion (ι := ι) q)
    (modeComplementProjection_injection (ι := ι) q hq)
    (modeComplementProjection_inclusion (ι := ι) q)

@[simp] theorem modeComplementaryEquiv_operator (q : EuclideanSpace ℝ κ) (hq : ‖q‖ = 1)
    (M : EuclideanSpace ℝ (ι × κ) →L[ℝ] EuclideanSpace ℝ (ι × κ))
    (Dc : ModeComplement (ι := ι) q ≃L[ℝ] ModeComplement (ι := ι) q)
    (S : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι)
    (hDc : ∀ c, modeComplementProjection (ι := ι) q (M (modeComplementInclusion (ι := ι) q c)) = Dc c)
    (hS : (S : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) = modeSchur q M Dc) :
    (modeComplementaryEquiv q hq M Dc S hDc hS :
      EuclideanSpace ℝ (ι × κ) →L[ℝ] EuclideanSpace ℝ (ι × κ)) = M := rfl

theorem modeComplementaryEquiv_inverse_norm_le
    (q : EuclideanSpace ℝ κ) (hq : ‖q‖ = 1)
    (M : EuclideanSpace ℝ (ι × κ) →L[ℝ] EuclideanSpace ℝ (ι × κ))
    (Dc : ModeComplement (ι := ι) q ≃L[ℝ] ModeComplement (ι := ι) q)
    (S : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι)
    (hDc : ∀ c, modeComplementProjection (ι := ι) q (M (modeComplementInclusion (ι := ι) q c)) = Dc c)
    (hS : (S : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) = modeSchur q M Dc)
    (hleft : ‖(Dc.symm : ModeComplement (ι := ι) q →L[ℝ] ModeComplement (ι := ι) q).comp
      ((modeComplementProjection (ι := ι) q).comp (M.comp (blockInjection (ι := ι) q)))‖ ≤ 1)
    (hright : ‖((blockInjection (ι := ι) q).adjoint.comp (M.comp (modeComplementInclusion (ι := ι) q))).comp
      (Dc.symm : ModeComplement (ι := ι) q →L[ℝ] ModeComplement (ι := ι) q)‖ ≤ 1) :
    ‖((modeComplementaryEquiv q hq M Dc S hDc hS).symm :
      EuclideanSpace ℝ (ι × κ) →L[ℝ] EuclideanSpace ℝ (ι × κ))‖ ≤
      4 * (‖(S.symm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)‖ +
        ‖(Dc.symm : ModeComplement (ι := ι) q →L[ℝ] ModeComplement (ι := ι) q)‖) := by
  exact complementary_full_inverse_norm_le M (blockInjection (ι := ι) q) (modeComplementInclusion (ι := ι) q)
    (blockInjection (ι := ι) q).adjoint (modeComplementProjection (ι := ι) q) Dc S
    (modeCoordinate_decomposition (ι := ι) q hq) hDc hS
    (blockInjection_adjoint_cancel (ι := ι) q hq) (modeAdjoint_inclusion (ι := ι) q)
    (modeComplementProjection_injection (ι := ι) q hq)
    (modeComplementProjection_inclusion (ι := ι) q)
    (modeInjection_norm_le (ι := ι) q hq) (modeComplementInclusion_norm_le (ι := ι) q)
    (modeAdjoint_norm_le (ι := ι) q hq) (modeComplementProjection_norm_le (ι := ι) q)
    hleft hright

end Maxwell.Composition
