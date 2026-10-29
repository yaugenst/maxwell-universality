import Maxwell.Continuum.RankOneBandResolvent

/-! Explicit scalar Schur map and quantitative bounds for its actual
high-space eigenvector correction. -/

noncomputable section
namespace Maxwell.Continuum.RankOneBand

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : H →L[ℂ] H} {u : H} {ell : ℝ}

def correctionVector (K : H →L[ℂ] H) (u : H) (ell : ℝ) (V : H →L[ℂ] H) (e : ℂ) : H :=
  embed u (highInverse K u ell V e (project u (V u)))

def eigenvectorLift (K : H →L[ℂ] H) (u : H) (ell : ℝ) (V : H →L[ℂ] H) (e : ℂ) : H :=
  u + correctionVector K u ell V e

def rootMap (K : H →L[ℂ] H) (u : H) (ell : ℝ) (V : H →L[ℂ] H) (e : ℂ) : ℂ :=
  (ell : ℂ) + coefficient u (V u) + coefficient u (V (correctionVector K u ell V e))

namespace Data

variable (D : Data K u ell)

omit [CompleteSpace H] in
include D in
theorem norm_apply_unit (V : H →L[ℂ] H) : ‖V u‖ ≤ ‖V‖ := by
  simpa only [D.unit_norm, mul_one] using V.le_opNorm u

include D in
theorem correctionVector_norm_le (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) :
    ‖correctionVector K u ell V e‖ ≤ 40 * ‖V‖ := by
  change ‖embed u (highInverse K u ell V e (project u (V u)))‖ ≤ _
  rw [embed_norm]
  calc
    _ ≤ ‖highInverse K u ell V e‖ * ‖project u (V u)‖ := (highInverse K u ell V e).le_opNorm _
    _ ≤ 40 * ‖V u‖ := mul_le_mul (D.highInverse_norm_le V e hV he)
      ((highSpace u).norm_orthogonalProjectionOnto_apply_le (V u)) (norm_nonneg _) (by norm_num)
    _ ≤ 40 * ‖V‖ := mul_le_mul_of_nonneg_left (D.norm_apply_unit V) (by norm_num)

include D in
theorem eigenvectorLift_norm_le (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) :
    ‖eigenvectorLift K u ell V e‖ ≤ 2 := by
  have h := norm_add_le u (correctionVector K u ell V e)
  rw [D.unit_norm] at h
  change ‖eigenvectorLift K u ell V e‖ ≤ _ at h
  nlinarith [D.correctionVector_norm_le V e hV he]

include D in
theorem rootMap_center_bound (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) :
    ‖rootMap K u ell V e - (ell : ℂ)‖ ≤ 1 / 200 := by
  have hfirst : ‖coefficient u (V u)‖ ≤ 1 / 256 :=
    ((D.coefficient_norm_le _).trans (D.norm_apply_unit V)).trans hV
  have hc : ‖correctionVector K u ell V e‖ ≤ 40 / 256 := by
    linarith [D.correctionVector_norm_le V e hV he]
  have hsecond : ‖coefficient u (V (correctionVector K u ell V e))‖ ≤ (1 / 256) * (40 / 256) :=
    ((D.coefficient_norm_le _).trans (V.le_opNorm _)).trans
      (mul_le_mul hV hc (norm_nonneg _) (by norm_num))
  have heq : rootMap K u ell V e - (ell : ℂ) =
      coefficient u (V u) + coefficient u (V (correctionVector K u ell V e)) := by
    unfold rootMap
    ring
  rw [heq]
  exact (norm_add_le _ _).trans (by linarith)

end Data
end Maxwell.Continuum.RankOneBand
