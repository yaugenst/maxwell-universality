import Maxwell.Continuum.RankOneBandInverseBounds

/-! The explicit normalized rank-one projection associated with the frozen
operator kernel. For an energy-dependent pencil this is distinct from its
resolvent residue. -/

noncomputable section
namespace Maxwell.Continuum.RankOneBand

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {K : H →L[ℂ] H} {u : H} {ell : ℝ}

def normalizedProjection (K : H →L[ℂ] H) (u : H) (ell : ℝ) (V : H →L[ℂ] H) (e : ℂ) : H →L[ℂ] H :=
  (numerator K u ell V e (eigenvectorLift K u ell V e))⁻¹ • rankOneNumerator K u ell V e

namespace Data

variable (D : Data K u ell)

include D in
theorem scaledRankOne_range (V : H →L[ℂ] H) (e a : ℂ) (ha : a ≠ 0) :
    (a • rankOneNumerator K u ell V e).range = ℂ ∙ eigenvectorLift K u ell V e := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine Submodule.mem_span_singleton.mpr ⟨a * numerator K u ell V e y, ?_⟩
    change (a * numerator K u ell V e y) • eigenvectorLift K u ell V e =
      a • (numerator K u ell V e y • eigenvectorLift K u ell V e)
    exact mul_smul _ _ _
  · intro hx
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hx
    refine ⟨(a⁻¹ * b) • u, ?_⟩
    change a • (numerator K u ell V e ((a⁻¹ * b) • u) • eigenvectorLift K u ell V e) = x
    rw [map_smul, D.numerator_self, smul_eq_mul, mul_one, smul_smul,
      ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
    exact hb

include D in
theorem scaledRankOne_finrank (V : H →L[ℂ] H) (e a : ℂ) (ha : a ≠ 0) :
    Module.finrank ℂ (a • rankOneNumerator K u ell V e).range = 1 := by
  rw [D.scaledRankOne_range V e a ha]
  exact finrank_span_singleton (D.eigenvectorLift_ne_zero V e)

variable [CompleteSpace H]

include D in
theorem numerator_lift_sub_one (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) :
    ‖numerator K u ell V e (eigenvectorLift K u ell V e) - 1‖ ≤ 1 / 4 := by
  rw [numerator_apply, D.coefficient_eigenvectorLift, add_sub_cancel_left]
  have hh : ‖highSolve K u ell V e (eigenvectorLift K u ell V e)‖ ≤ 40 * (3 / 2) :=
    ((highSolve K u ell V e).le_opNorm _).trans (mul_le_mul (D.highSolve_norm_le V e hV he)
      (D.eigenvectorLift_norm_le_three_halves V e hV he) (norm_nonneg _) (by norm_num))
  have hv : ‖V (highSolve K u ell V e (eigenvectorLift K u ell V e))‖ ≤ (1 / 256) * (40 * (3 / 2)) :=
    (V.le_opNorm _).trans (mul_le_mul hV hh (norm_nonneg _) (by norm_num))
  exact (D.coefficient_norm_le _).trans (hv.trans (by norm_num))

include D in
theorem numerator_lift_ne_zero (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) :
    numerator K u ell V e (eigenvectorLift K u ell V e) ≠ 0 := by
  intro hz
  have h := D.numerator_lift_sub_one V e hV he
  rw [hz, zero_sub, norm_neg, norm_one] at h
  norm_num at h

include D in
theorem normalizedProjection_lift (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) :
    normalizedProjection K u ell V e (eigenvectorLift K u ell V e) = eigenvectorLift K u ell V e := by
  change (numerator K u ell V e (eigenvectorLift K u ell V e))⁻¹ •
    (numerator K u ell V e (eigenvectorLift K u ell V e) • eigenvectorLift K u ell V e) = _
  rw [smul_smul, inv_mul_cancel₀ (D.numerator_lift_ne_zero V e hV he), one_smul]

include D in
theorem normalizedProjection_idempotent (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) :
    normalizedProjection K u ell V e * normalizedProjection K u ell V e =
      normalizedProjection K u ell V e := by
  apply ContinuousLinearMap.ext
  intro x
  change normalizedProjection K u ell V e
    ((numerator K u ell V e (eigenvectorLift K u ell V e))⁻¹ •
      (numerator K u ell V e x • eigenvectorLift K u ell V e)) = _
  rw [map_smul, map_smul, D.normalizedProjection_lift V e hV he]
  rfl

include D in
theorem normalizedProjection_range (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) :
    (normalizedProjection K u ell V e).range = ℂ ∙ eigenvectorLift K u ell V e :=
  D.scaledRankOne_range V e _ (inv_ne_zero (D.numerator_lift_ne_zero V e hV he))

include D in
theorem normalizedProjection_range_eq_kernel (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100)
    (hg : rootMap K u ell V e = e) :
    (normalizedProjection K u ell V e).range = (operator K V e).ker := by
  rw [D.normalizedProjection_range V e hV he, D.kernel_eq_span V e hV he hg]

#print axioms normalizedProjection_idempotent
#print axioms normalizedProjection_range_eq_kernel

end Data
end Maxwell.Continuum.RankOneBand
