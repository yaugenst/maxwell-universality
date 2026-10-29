import Maxwell.Continuum.SelfAdjointResolvent

/-!
# Real shifts of unbounded self-adjoint operators

The lower-bound hypothesis is an estimate on the actual partial operator
`A - σ I`. Its inverse, surjectivity, and residual-error bound are conclusions.
Identification of this lower bound with a distance to the spectrum is not
part of this module.
-/

noncomputable section

namespace Maxwell.Continuum.SelfAdjointResolvent

open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency false

variable {𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- A real scalar shift preserving the full operator domain. -/
def shift (A : H →ₗ.[𝕜] H) (σ : ℝ) : H →ₗ.[𝕜] H :=
  FormPerturbation.addBounded A (-(σ : 𝕜) • ContinuousLinearMap.id 𝕜 H)

omit [CompleteSpace H] in
@[simp] theorem shift_domain (A : H →ₗ.[𝕜] H) (σ : ℝ) :
    (shift A σ).domain = A.domain := rfl

omit [CompleteSpace H] in
@[simp] theorem shift_apply (A : H →ₗ.[𝕜] H) (σ : ℝ) (x : (shift A σ).domain) :
    shift A σ x = A x - (σ : 𝕜) • (x : H) := by
  change A x + (-(σ : 𝕜)) • (x : H) = A x - (σ : 𝕜) • (x : H)
  rw [neg_smul, sub_eq_add_neg]

theorem shift_selfAdjoint (A : H →ₗ.[𝕜] H) (σ : ℝ) (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (shift A σ) := by
  apply FormPerturbation.addBounded_selfAdjoint _ _ hA
  intro x y
  change inner 𝕜 (-(σ : 𝕜) • x) y = inner 𝕜 x (-(σ : 𝕜) • y)
  simp only [inner_smul_left, inner_smul_right, map_neg, RCLike.conj_ofReal]

variable (A : H →ₗ.[𝕜] H) (σ : ℝ) (hA : IsSelfAdjoint A)
variable {δ : ℝ} (hδ : 0 < δ)
variable (hbound : ∀ x : A.domain, δ * ‖(x : H)‖ ≤ ‖A x - (σ : 𝕜) • (x : H)‖)

include hδ hbound

def shiftInverse : H →L[𝕜] H :=
  inverse (shift A σ) hδ (by intro x; simpa only [shift_apply] using hbound x)
    (shift_selfAdjoint A σ hA)

theorem shiftInverse_mem_domain (f : H) : shiftInverse A σ hA hδ hbound f ∈ A.domain :=
  inverse_mem_domain (shift A σ) hδ _ (shift_selfAdjoint A σ hA) f

theorem apply_shiftInverse (f : H) :
    A ⟨shiftInverse A σ hA hδ hbound f, shiftInverse_mem_domain A σ hA hδ hbound f⟩ -
      (σ : 𝕜) • shiftInverse A σ hA hδ hbound f = f := by
  have h := apply_inverse (shift A σ) hδ
    (by intro x; simpa only [shift_apply] using hbound x) (shift_selfAdjoint A σ hA) f
  simpa only [shiftInverse, shift_apply] using h

theorem shiftInverse_apply (x : A.domain) :
    shiftInverse A σ hA hδ hbound (A x - (σ : 𝕜) • (x : H)) = (x : H) := by
  have h := inverse_apply (shift A σ) hδ
    (by intro y; simpa only [shift_apply] using hbound y) (shift_selfAdjoint A σ hA) x
  simpa only [shiftInverse, shift_apply] using h

theorem shiftInverse_opNorm_le : ‖shiftInverse A σ hA hδ hbound‖ ≤ δ⁻¹ :=
  inverse_opNorm_le (shift A σ) hδ _ (shift_selfAdjoint A σ hA)

theorem shiftInverse_residual_bound (x : A.domain) (f : H) :
    ‖(x : H) - shiftInverse A σ hA hδ hbound f‖ ≤
      δ⁻¹ * ‖A x - (σ : 𝕜) • (x : H) - f‖ := by
  have h := residual_bound (shift A σ) hδ
    (by intro y; simpa only [shift_apply] using hbound y) (shift_selfAdjoint A σ hA) x f
  simpa only [shiftInverse, shift_apply] using h

end Maxwell.Continuum.SelfAdjointResolvent
