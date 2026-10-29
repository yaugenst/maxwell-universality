import Maxwell.Continuum.Operator
import Maxwell.Continuum.PECKernel
import Maxwell.Continuum.Compression
import Maxwell.Continuum.GradientSchur

/-!
# The actual dielectric blocks in the PEC kernel decomposition

The abstract positive-inverse estimates are instantiated with the literal
scalar multiplier on the physical L² space and the actual curl-curl kernel.
The infinite gradient block is not counted as finitely many free modes.
-/

noncomputable section

namespace Maxwell.Continuum

set_option backward.isDefEq.respectTransparency false

open TopologicalSpace

namespace ScalarDielectric

variable (ε : ScalarDielectric) (Ω : Opens Space)

def gradientMaterial : gradientSpace Ω →L[ℂ] gradientSpace Ω :=
  Compression.compress (gradientSpace Ω) (ε.domainMultiplier Ω)

def transverseMaterial : transverseSpace Ω →L[ℂ] transverseSpace Ω :=
  Compression.compress (transverseSpace Ω) (ε.domainMultiplier Ω)

def materialCoupling : transverseSpace Ω →L[ℂ] gradientSpace Ω :=
  Compression.offDiagonal (gradientSpace Ω) (ε.domainMultiplier Ω)

theorem gradientMaterial_symmetric :
    LinearMap.IsSymmetric (𝕜 := ℂ) (E := gradientSpace Ω) (ε.gradientMaterial Ω).toLinearMap :=
  Compression.compress_symmetric _ _ (ε.domainMultiplier_symmetric Ω)

theorem gradientMaterial_coercive :
    CoerciveInverse.Coercive (H := gradientSpace Ω) (ε.gradientMaterial Ω) 1 := by
  apply Compression.compress_coercive
  intro x
  simpa only [one_mul] using ε.domainMultiplier_inner_lower Ω x

theorem gradientMaterial_upper (x : gradientSpace Ω) :
    (inner ℂ x (ε.gradientMaterial Ω x)).re ≤ 25 * ‖x‖ ^ 2 :=
  Compression.compress_upper _ _ (ε.domainMultiplier_inner_upper Ω) x

theorem transverseMaterial_symmetric : (ε.transverseMaterial Ω).IsSymmetric :=
  Compression.compress_symmetric _ _ (ε.domainMultiplier_symmetric Ω)

theorem transverseMaterial_upper (x : transverseSpace Ω) :
    (inner ℂ x (ε.transverseMaterial Ω x)).re ≤ 25 * ‖x‖ ^ 2 :=
  Compression.compress_upper _ _ (ε.domainMultiplier_inner_upper Ω) x

theorem materialCoupling_norm_le : ‖ε.materialCoupling Ω‖ ≤ 25 :=
  (Compression.offDiagonal_norm_le _ _).trans (ε.domainMultiplier_norm_le Ω)

def gradientResolvent (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell) :
    gradientSpace Ω →L[ℂ] gradientSpace Ω :=
  GradientSchur.gradientInverse (G := gradientSpace Ω) (ε.gradientMaterial Ω) (ε.gradientMaterial_coercive Ω) ell hell

theorem gradientResolvent_norm_le (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell) :
    ‖ε.gradientResolvent Ω ell hell‖ ≤ 4 / 3 :=
  GradientSchur.gradientInverse_norm_le (G := gradientSpace Ω) _ _ ell hell

theorem gradientResolvent_left (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell)
    (x : gradientSpace Ω) :
    ε.gradientMaterial Ω (ε.gradientResolvent Ω ell hell x) +
      (ell : ℂ) • ε.gradientResolvent Ω ell hell x = x :=
  GradientSchur.shift_gradientInverse (G := gradientSpace Ω) _ _ _ _ _

theorem gradientResolvent_right (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell)
    (x : gradientSpace Ω) :
    ε.gradientResolvent Ω ell hell (ε.gradientMaterial Ω x + (ell : ℂ) • x) = x :=
  GradientSchur.gradientInverse_shift (G := gradientSpace Ω) _ _ _ _ _

def transverseSchurPart (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell) :
    transverseSpace Ω →L[ℂ] transverseSpace Ω :=
  GradientSchur.boundedPart (G := gradientSpace Ω) (T := transverseSpace Ω) (ε.gradientMaterial Ω) (ε.gradientMaterial_coercive Ω)
    (ε.transverseMaterial Ω) (ε.materialCoupling Ω) ell hell

theorem transverseSchurPart_lower (ell : ℝ) (hell : -(1 / 4 : ℝ) ≤ ell)
    (hell' : ell ≤ 1 / 4) (x : transverseSpace Ω) :
    -26 * ‖x‖ ^ 2 ≤ (inner ℂ x (ε.transverseSchurPart Ω ell hell x)).re :=
  GradientSchur.boundedPart_lower (G := gradientSpace Ω) (T := transverseSpace Ω) _ _ _ (ε.transverseMaterial_upper Ω) _ _ _ hell' x

theorem transverseSchurPart_strict_antitone (ell μ : ℝ)
    (hell : -(1 / 4 : ℝ) ≤ ell) (hμ : -(1 / 4 : ℝ) ≤ μ) (hle : ell ≤ μ)
    (x : transverseSpace Ω) :
    (inner ℂ x (ε.transverseSchurPart Ω μ hμ x)).re ≤
      (inner ℂ x (ε.transverseSchurPart Ω ell hell x)).re - (μ - ell) * ‖x‖ ^ 2 :=
  GradientSchur.boundedPart_strict_antitone (G := gradientSpace Ω) (T := transverseSpace Ω) _ _ (ε.gradientMaterial_symmetric Ω)
    _ _ _ _ _ _ hle x

end ScalarDielectric

end Maxwell.Continuum
