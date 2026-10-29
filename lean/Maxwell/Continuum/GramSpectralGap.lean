import Maxwell.Continuum.GramSpectralBasic

/-! The quantitative complementary norm bound transfers between actual
Gram operators. This does not assume compactness or a spectral decomposition. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.GramSpectral

open scoped InnerProduct

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

def orthogonalPart (u : Y) : Y →L[ℂ] Y := ((ℂ ∙ u)ᗮ).starProjection

theorem orthogonalPart_adjoint (u : Y) : (orthogonalPart u)† = orthogonalPart u :=
  ((ℂ ∙ u)ᗮ).starProjection_isSymmetric.clm_adjoint_eq

omit [CompleteSpace Y] in
theorem orthogonalPart_inner (u x : Y) : inner ℂ u (orthogonalPart u x) = 0 :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.mp
    (((ℂ ∙ u)ᗮ).starProjection_apply_mem x)

omit [CompleteSpace Y] in
theorem orthogonalPart_norm (u x : Y) : ‖orthogonalPart u x‖ ≤ ‖x‖ :=
  ((ℂ ∙ u)ᗮ).norm_starProjection_apply_le x

omit [CompleteSpace Y] in
theorem orthogonalPart_fixed (u x : Y) (hx : inner ℂ u x = 0) :
    orthogonalPart u x = x :=
  ((ℂ ∙ u)ᗮ).starProjection_eq_self_iff.mpr
    (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hx)

theorem gram_norm_equal (A : X →L[ℂ] Y) : ‖(A†).comp A‖ = ‖A.comp (A†)‖ := by
  calc
    _ = ‖A‖ * ‖A‖ := ContinuousLinearMap.norm_adjoint_comp_self A
    _ = ‖A†‖ * ‖A†‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
    _ = ‖(A††).comp (A†)‖ := (ContinuousLinearMap.norm_adjoint_comp_self (A†)).symm
    _ = _ := by rw [ContinuousLinearMap.adjoint_adjoint]

theorem gram_complement (A : X →L[ℂ] Y) (u : Y) {mu c : ℝ} (hm : 0 < mu)
    (hc : 0 ≤ c)
    (hcomp : ∀ y : Y, inner ℂ u y = 0 → ‖A ((A†) y)‖ ≤ c * ‖y‖)
    (f : X) (hf : inner ℂ (vector A mu u) f = 0) :
    ‖(A†) (A f)‖ ≤ c * ‖f‖ := by
  let J := orthogonalPart u
  let D : X →L[ℂ] Y := J.comp A
  have hJ : J† = J := orthogonalPart_adjoint u
  have hD : D† = (A†).comp J := by
    change (J.comp A)† = (A†).comp J
    rw [ContinuousLinearMap.adjoint_comp, hJ]
  have hDD : ‖D.comp (D†)‖ ≤ c := by
    apply ContinuousLinearMap.opNorm_le_bound _ hc
    intro x
    rw [ContinuousLinearMap.comp_apply, hD]
    change ‖J (A ((A†) (J x)))‖ ≤ c * ‖x‖
    calc
      _ ≤ ‖A ((A†) (J x))‖ := orthogonalPart_norm u _
      _ ≤ c * ‖J x‖ := hcomp (J x) (orthogonalPart_inner u x)
      _ ≤ c * ‖x‖ := mul_le_mul_of_nonneg_left (orthogonalPart_norm u x) hc
  have hAf : J (A f) = A f := orthogonalPart_fixed u (A f) (image_orthogonal A u hm f hf)
  have heq : ((D†).comp D) f = (A†) (A f) := by
    rw [ContinuousLinearMap.comp_apply, hD]
    change (A†) (J (J (A f))) = _
    rw [hAf, hAf]
  rw [← heq]
  exact ((D†).comp D).le_of_opNorm_le ((gram_norm_equal D).trans_le hDD) f

end Maxwell.Continuum.GramSpectral
