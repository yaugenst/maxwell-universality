import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! Exact Birman--Schwinger correspondence. The ambient field space need
not be finite dimensional. In applications `L` is the adjoint of `K`. -/

namespace Maxwell.Defect

noncomputable section

variable {𝕜 E U : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup U] [Module 𝕜 U]

def compressed (H : E ≃ₗ[𝕜] E) (K : U →ₗ[𝕜] E) (L : E →ₗ[𝕜] U) : U →ₗ[𝕜] U :=
  L.comp (H.symm.toLinearMap.comp K)

def defectOperator (H : E ≃ₗ[𝕜] E) (K : U →ₗ[𝕜] E) (L : E →ₗ[𝕜] U)
    (μ : 𝕜) : E →ₗ[𝕜] E :=
  H.toLinearMap - μ⁻¹ • K.comp L

theorem defect_mode_of_compressed (H : E ≃ₗ[𝕜] E)
    (K : U →ₗ[𝕜] E) (L : E →ₗ[𝕜] U) {μ : 𝕜} (hμ : μ ≠ 0)
    {u : U} (hu : compressed H K L u = μ • u) :
    defectOperator H K L μ (H.symm (K u)) = 0 := by
  change H (H.symm (K u)) - μ⁻¹ • K (L (H.symm (K u))) = 0
  change L (H.symm (K u)) = μ • u at hu
  rw [H.apply_symm_apply, hu, map_smul, smul_smul, inv_mul_cancel₀ hμ, one_smul, sub_self]

theorem compressed_mode_of_defect (H : E ≃ₗ[𝕜] E)
    (K : U →ₗ[𝕜] E) (L : E →ₗ[𝕜] U) {μ : 𝕜} (hμ : μ ≠ 0)
    {y : E} (hy : defectOperator H K L μ y = 0) :
    compressed H K L (L y) = μ • L y := by
  change H y - μ⁻¹ • K (L y) = 0 at hy
  have hHy := sub_eq_zero.mp hy
  have hrecover : H.symm (K (L y)) = μ • y := by
    apply H.injective
    rw [H.apply_symm_apply, map_smul, hHy, smul_smul, mul_inv_cancel₀ hμ, one_smul]
  change L (H.symm (K (L y))) = μ • L y
  rw [hrecover, map_smul]

/-- The full eigenspace is linearly equivalent to the physical defect
kernel, so simplicity transfers without assuming it for the physical mode. -/
def birmanSchwingerEquiv (H : E ≃ₗ[𝕜] E)
    (K : U →ₗ[𝕜] E) (L : E →ₗ[𝕜] U) (μ : 𝕜) (hμ : μ ≠ 0) :
    Module.End.eigenspace (compressed H K L) μ ≃ₗ[𝕜]
      LinearMap.ker (defectOperator H K L μ) where
  toFun u := ⟨H.symm (K u), defect_mode_of_compressed H K L hμ
    (Module.End.mem_eigenspace_iff.mp u.property)⟩
  invFun y := ⟨μ⁻¹ • L y, by
    apply Module.End.mem_eigenspace_iff.mpr
    rw [map_smul, compressed_mode_of_defect H K L hμ y.property]
    exact smul_comm μ⁻¹ μ (L y)⟩
  left_inv u := by
    apply Subtype.ext
    change μ⁻¹ • L (H.symm (K u)) = u
    have hu := Module.End.mem_eigenspace_iff.mp u.property
    change L (H.symm (K u)) = μ • (u : U) at hu
    rw [hu, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  right_inv y := by
    apply Subtype.ext
    change H.symm (K (μ⁻¹ • L y)) = y
    have hy : H y = μ⁻¹ • K (L y) := sub_eq_zero.mp y.property
    apply H.injective
    rw [H.apply_symm_apply, map_smul, hy]
  map_add' u v := by
    apply Subtype.ext
    simp
  map_smul' a u := by
    apply Subtype.ext
    simp

/-- Simplicity transfers from the finite compression to the infinite
physical defect kernel through the exact correspondence. -/
theorem birmanSchwinger_simple_kernel (H : E ≃ₗ[𝕜] E)
    (K : U →ₗ[𝕜] E) (L : E →ₗ[𝕜] U) (μ : 𝕜) (hμ : μ ≠ 0)
    (hsimple : Module.finrank 𝕜 (Module.End.eigenspace (compressed H K L) μ) = 1) :
    Module.finrank 𝕜 (LinearMap.ker (defectOperator H K L μ)) = 1 := by
  rw [← (birmanSchwingerEquiv H K L μ hμ).finrank_eq]
  exact hsimple

theorem defect_mode_ne_zero (H : E ≃ₗ[𝕜] E)
    (K : U →ₗ[𝕜] E) (L : E →ₗ[𝕜] U) {μ : 𝕜} (hμ : μ ≠ 0)
    {u : U} (hu0 : u ≠ 0) (hu : compressed H K L u = μ • u) :
    H.symm (K u) ≠ 0 := by
  intro hz
  have hzero : μ • u = 0 := by
    rw [← hu]
    change L (H.symm (K u)) = 0
    rw [hz, map_zero]
  exact hu0 ((smul_eq_zero.mp hzero).resolve_left hμ)

end

end Maxwell.Defect
