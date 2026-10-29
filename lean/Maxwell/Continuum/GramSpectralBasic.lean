import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic.Linarith

/-! Exact transport of a positive eigenpair between the two Gram operators
of a bounded map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.GramSpectral

open scoped InnerProduct

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

def vector (A : X →L[ℂ] Y) (mu : ℝ) (u : Y) : X :=
  ((Real.sqrt mu)⁻¹ : ℂ) • (A†) u

theorem adjoint_norm_square (A : X →L[ℂ] Y) (u : Y) (hu : ‖u‖ = 1)
    (mu : ℝ) (he : A ((A†) u) = (mu : ℂ) • u) :
    ‖(A†) u‖^2 = mu := by
  have hi := A.adjoint_inner_left ((A†) u) u
  rw [he, inner_self_eq_norm_sq_to_K, inner_smul_right,
    inner_self_eq_norm_sq_to_K, hu] at hi
  simp only [one_pow, RCLike.ofReal_one, mul_one, ← RCLike.ofReal_pow] at hi
  exact Complex.ofReal_injective hi

theorem adjoint_norm (A : X →L[ℂ] Y) (u : Y) (hu : ‖u‖ = 1)
    {mu : ℝ} (hm : 0 < mu) (he : A ((A†) u) = (mu : ℂ) • u) :
    ‖(A†) u‖ = Real.sqrt mu := by
  have hs := adjoint_norm_square A u hu mu he
  nlinarith [Real.sq_sqrt hm.le, Real.sqrt_nonneg mu, norm_nonneg ((A†) u)]

theorem vector_norm (A : X →L[ℂ] Y) (u : Y) (hu : ‖u‖ = 1)
    {mu : ℝ} (hm : 0 < mu) (he : A ((A†) u) = (mu : ℂ) • u) :
    ‖vector A mu u‖ = 1 := by
  rw [vector, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.mpr hm), adjoint_norm A u hu hm he,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr hm).ne']

theorem adjoint_vector (A : X →L[ℂ] Y) (u : Y) {mu : ℝ} (hm : 0 < mu) :
    (A†) u = (Real.sqrt mu : ℂ) • vector A mu u := by
  rw [vector, smul_smul, mul_inv_cancel₀
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hm).ne'), one_smul]

theorem vector_image (A : X →L[ℂ] Y) (u : Y) {mu : ℝ} (hm : 0 < mu)
    (he : A ((A†) u) = (mu : ℂ) • u) :
    A (vector A mu u) = (Real.sqrt mu : ℂ) • u := by
  rw [vector, map_smul, he, smul_smul]
  congr 1
  have hs : (Real.sqrt mu)⁻¹ * mu = Real.sqrt mu := by
    calc
      _ = (Real.sqrt mu)⁻¹ * (Real.sqrt mu)^2 :=
        congrArg (fun t : ℝ => (Real.sqrt mu)⁻¹ * t) (Real.sq_sqrt hm.le).symm
      _ = _ := by rw [pow_two, ← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.mpr hm).ne', one_mul]
  exact_mod_cast hs

theorem vector_eigen (A : X →L[ℂ] Y) (u : Y) {mu : ℝ} (hm : 0 < mu)
    (he : A ((A†) u) = (mu : ℂ) • u) :
    (A†) (A (vector A mu u)) = (mu : ℂ) • vector A mu u := by
  rw [vector_image A u hm he, map_smul, adjoint_vector A u hm, smul_smul,
    ← pow_two, ← Complex.ofReal_pow, Real.sq_sqrt hm.le]

theorem image_orthogonal (A : X →L[ℂ] Y) (u : Y) {mu : ℝ} (hm : 0 < mu)
    (f : X) (hf : inner ℂ (vector A mu u) f = 0) : inner ℂ u (A f) = 0 := by
  rw [← A.adjoint_inner_left f u, adjoint_vector A u hm,
    inner_smul_left, hf, mul_zero]

end Maxwell.Continuum.GramSpectral
