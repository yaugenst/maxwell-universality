import Maxwell.Continuum.PECGradientSchur
import Maxwell.Continuum.PECTransverse
import Maxwell.Continuum.FormOrder

/-! The actual unbounded transverse Schur operator and its order estimates. -/

noncomputable section

namespace Maxwell.Continuum

set_option backward.isDefEq.respectTransparency false

open TopologicalSpace

namespace ScalarDielectric

variable (ε : ScalarDielectric) (Ω : Opens Space)

theorem transverseSchurPart_symmetric (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell) :
    LinearMap.IsSymmetric (𝕜 := ℂ) (E := transverseSpace Ω)
      (ε.transverseSchurPart Ω ell hell).toLinearMap :=
  GradientSchur.boundedPart_symmetric (G := gradientSpace Ω) (T := transverseSpace Ω)
    _ _ (ε.gradientMaterial_symmetric Ω) _ (ε.transverseMaterial_symmetric Ω) _ ell hell

/-- C_t−ε_tt−ell+ε_tg(ε_gg+ell)⁻¹ε_gt, on exactly D(C_t). -/
def schurOperator (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell) :
    transverseSpace Ω →ₗ.[ℂ] transverseSpace Ω :=
  FormPerturbation.addBounded (transverseCurlCurl Ω) (ε.transverseSchurPart Ω ell hell)

@[simp] theorem schurOperator_domain (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell) :
    (ε.schurOperator Ω ell hell).domain = (transverseCurlCurl Ω).domain := rfl

@[simp] theorem schurOperator_apply (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell)
    (u : (transverseCurlCurl Ω).domain) :
    ε.schurOperator Ω ell hell u =
      transverseCurlCurl Ω u + ε.transverseSchurPart Ω ell hell u := rfl

theorem schurOperator_selfAdjoint (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell) :
    IsSelfAdjoint (ε.schurOperator Ω ell hell) :=
  FormPerturbation.addBounded_selfAdjoint _ _ (transverseCurlCurl_selfAdjoint Ω)
    (ε.transverseSchurPart_symmetric Ω ell hell)

theorem schurOperator_closed (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell) :
    (ε.schurOperator Ω ell hell).IsClosed := (ε.schurOperator_selfAdjoint Ω ell hell).isClosed

theorem schurOperator_lower (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell) (hell' : ell ≤ 1 / 4)
    (u : (transverseCurlCurl Ω).domain) :
    (inner ℂ (u : transverseSpace Ω) (transverseCurlCurl Ω u)).re -
      26 * ‖(u : transverseSpace Ω)‖ ^ 2 ≤
        (inner ℂ (u : transverseSpace Ω) (ε.schurOperator Ω ell hell u)).re :=
  FormOrder.lower (H := transverseSpace Ω) (transverseCurlCurl Ω)
    (ε.transverseSchurPart Ω ell hell) 26 (ε.transverseSchurPart_lower Ω ell hell hell') u

theorem schurOperator_strict_antitone (ell μ : ℝ)
    (hell : -(1 / 4 : ℝ) ≤ ell) (hμ : -(1 / 4 : ℝ) ≤ μ) (hle : ell ≤ μ)
    (u : (transverseCurlCurl Ω).domain) :
    (inner ℂ (u : transverseSpace Ω) (ε.schurOperator Ω μ hμ u)).re ≤
      (inner ℂ (u : transverseSpace Ω) (ε.schurOperator Ω ell hell u)).re -
        (μ - ell) * ‖(u : transverseSpace Ω)‖ ^ 2 :=
  FormOrder.shifted_order (H := transverseSpace Ω) (transverseCurlCurl Ω)
    (ε.transverseSchurPart Ω ell hell) (ε.transverseSchurPart Ω μ hμ) (μ - ell)
    (ε.transverseSchurPart_strict_antitone Ω ell μ hell hμ hle) u

theorem gradient_material_blocks (u : testL2Closure Ω) :
    gradientProjection Ω (ε.domainMultiplier Ω u) =
      ε.gradientMaterial Ω (gradientProjection Ω u) +
        ε.materialCoupling Ω (transverseProjection Ω u) := by
  have h := congrArg (fun v => gradientProjection Ω (ε.domainMultiplier Ω v))
    (kernel_decomposition Ω u)
  simpa only [map_add, gradientMaterial, materialCoupling, Compression.compress,
    Compression.offDiagonal, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    gradientProjection] using h.symm

theorem materialCoupling_adjoint (g : gradientSpace Ω) :
    ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := transverseSpace Ω) (F := gradientSpace Ω)
      (ε.materialCoupling Ω) g = transverseProjection Ω (ε.domainMultiplier Ω g) :=
  Compression.offDiagonal_adjoint (gradientSpace Ω) (ε.domainMultiplier Ω)
    (ε.domainMultiplier_symmetric Ω) g

theorem transverse_material_blocks (u : testL2Closure Ω) :
    transverseProjection Ω (ε.domainMultiplier Ω u) =
      ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := transverseSpace Ω) (F := gradientSpace Ω)
        (ε.materialCoupling Ω) (gradientProjection Ω u) +
        ε.transverseMaterial Ω (transverseProjection Ω u) := by
  rw [materialCoupling_adjoint]
  have h := congrArg (fun v => transverseProjection Ω (ε.domainMultiplier Ω v))
    (kernel_decomposition Ω u)
  simpa only [map_add, transverseMaterial, Compression.compress,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, transverseProjection] using h.symm

end ScalarDielectric

end Maxwell.Continuum
