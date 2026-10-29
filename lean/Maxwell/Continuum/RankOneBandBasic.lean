import Maxwell.Continuum.CoerciveInverse
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! Literal rank-one / orthogonal-complement decomposition for an isolated
simple eigenvector of a bounded self-adjoint operator. -/

noncomputable section
namespace Maxwell.Continuum.RankOneBand

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

abbrev highSpace (u : H) : Submodule ℂ H := (ℂ ∙ u)ᗮ

instance highSpace_completeSpace [CompleteSpace H] (u : H) : CompleteSpace (highSpace u) := by
  dsimp [highSpace]
  infer_instance

def coefficient (u : H) : H →L[ℂ] ℂ := innerSL ℂ u

def project (u : H) : H →L[ℂ] highSpace u := (highSpace u).orthogonalProjectionOnto

def embed (u : H) : highSpace u →L[ℂ] H := (highSpace u).subtypeL

structure Data (K : H →L[ℂ] H) (u : H) (ell : ℝ) : Prop where
  unit_norm : ‖u‖ = 1
  symmetric : K.IsSymmetric
  eigenvector : K u = (ell : ℂ) • u
  gap : ∀ x : H, inner ℂ u x = 0 →
    (1 / 20 : ℝ) * ‖x‖ ^ 2 ≤ (inner ℂ x ((ell : ℂ) • x - K x)).re

variable {K : H →L[ℂ] H} {u : H} {ell : ℝ}

theorem project_norm_le : ‖project u‖ ≤ 1 := (highSpace u).orthogonalProjectionOnto_norm_le

theorem embed_norm_le : ‖embed u‖ ≤ 1 := (highSpace u).norm_subtypeL_le

@[simp] theorem embed_norm (x : highSpace u) : ‖embed u x‖ = ‖x‖ := rfl

@[simp] theorem project_embed (x : highSpace u) : project u (embed u x) = x :=
  (highSpace u).orthogonalProjectionOnto_mem_subspace_eq_self x

@[simp] theorem coefficient_embed (x : highSpace u) : coefficient u (embed u x) = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property

@[simp] theorem project_self : project u u = 0 :=
  Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero u

namespace Data

variable (D : Data K u ell)

include D in
@[simp] theorem coefficient_self : coefficient u u = 1 := by
  change inner ℂ u u = 1
  rw [inner_self_eq_norm_sq_to_K, D.unit_norm]
  norm_num

include D in
theorem coefficient_norm_le (x : H) : ‖coefficient u x‖ ≤ ‖x‖ := by
  have h := norm_inner_le_norm (𝕜 := ℂ) u x
  rwa [D.unit_norm, one_mul] at h

include D in
theorem embed_project (x : H) : embed u (project u x) = x - coefficient u x • u := by
  change (highSpace u).starProjection x = _
  change ((ℂ ∙ u)ᗮ).starProjection x = _
  rw [Submodule.starProjection_orthogonal]
  change x - (ℂ ∙ u).starProjection x = _
  rw [Submodule.starProjection_unit_singleton ℂ D.unit_norm]
  rfl

include D in
theorem decomposition (x : H) : coefficient u x • u + embed u (project u x) = x := by
  rw [D.embed_project]
  abel

include D in
theorem coefficient_K (x : H) : coefficient u (K x) = (ell : ℂ) * coefficient u x := by
  have h := D.symmetric u x
  change inner ℂ (K u) x = inner ℂ u (K x) at h
  rw [D.eigenvector, inner_smul_left, Complex.conj_ofReal] at h
  exact h.symm

include D in
theorem K_mem_high (x : highSpace u) : K (embed u x) ∈ highSpace u := by
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
  change coefficient u (K (embed u x)) = 0
  rw [D.coefficient_K, coefficient_embed, mul_zero]

include D in
theorem embed_project_K (x : highSpace u) : embed u (project u (K (embed u x))) = K (embed u x) :=
  (highSpace u).starProjection_eq_self_iff.mpr (D.K_mem_high x)

end Data

def compress (u : H) (A : H →L[ℂ] H) : highSpace u →L[ℂ] highSpace u :=
  (project u).comp (A.comp (embed u))

theorem compress_norm_le (u : H) (A : H →L[ℂ] H) : ‖compress u A‖ ≤ ‖A‖ := by
  calc
    _ ≤ ‖project u‖ * (‖A‖ * ‖embed u‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖A‖ * 1) := mul_le_mul project_norm_le
      (mul_le_mul_of_nonneg_left embed_norm_le (norm_nonneg A))
      (by positivity) (by positivity)
    _ = ‖A‖ := by ring

def baseHigh (K : H →L[ℂ] H) (u : H) (ell : ℝ) : highSpace u →L[ℂ] highSpace u :=
  compress u ((ell : ℂ) • (1 : H →L[ℂ] H) - K)

namespace Data

variable (D : Data K u ell)

include D in
theorem baseHigh_coercive : CoerciveInverse.Coercive (baseHigh K u ell) (1 / 20) := by
  intro x
  change (1 / 20 : ℝ) * ‖x‖ ^ 2 ≤
    (inner ℂ x ((highSpace u).orthogonalProjectionOnto ((ell : ℂ) • (x : H) - K x))).re
  rw [(highSpace u).inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact D.gap x (Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property)

variable [CompleteSpace H]

def baseInverse : highSpace u →L[ℂ] highSpace u :=
  CoerciveInverse.inverse (baseHigh K u ell) (by norm_num : (0 : ℝ) < 1 / 20) D.baseHigh_coercive

theorem baseInverse_norm_le : ‖D.baseInverse‖ ≤ 20 := by
  simpa only [baseInverse, inv_div, one_div_one, mul_one, div_one] using
    CoerciveInverse.norm_inverse (baseHigh K u ell) (by norm_num : (0 : ℝ) < 1 / 20) D.baseHigh_coercive

#print axioms decomposition
#print axioms baseInverse_norm_le

end Data
end Maxwell.Continuum.RankOneBand
