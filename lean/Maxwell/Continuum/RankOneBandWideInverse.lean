import Maxwell.Continuum.RankOneBandInverse

/-! The actual high-space inverse on the larger energy disk of radius
`1/50`. This extends the exclusion window without changing the disk used
to construct the analytic band. -/

noncomputable section
namespace Maxwell.Continuum.RankOneBand

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {K : H →L[ℂ] H} {u : H} {ell : ℝ}

theorem highPerturbation_norm_le_wide (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 50) :
    ‖highPerturbation u ell V e‖ ≤ 1 / 40 := by
  let _ : NormSMulClass ℂ (highSpace u →L[ℂ] highSpace u) :=
    NormedSpace.toNormSMulClass (𝕜 := ℂ) (E := highSpace u →L[ℂ] highSpace u)
  have hid : ‖(1 : highSpace u →L[ℂ] highSpace u)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hmul := mul_le_mul he hid (norm_nonneg (1 : highSpace u →L[ℂ] highSpace u))
    (by norm_num : (0 : ℝ) ≤ 1 / 50)
  have h := norm_sub_le ((e - (ell : ℂ)) • (1 : highSpace u →L[ℂ] highSpace u)) (compress u V)
  rw [norm_smul] at h
  change ‖highPerturbation u ell V e‖ ≤ _ at h
  linarith [compress_norm_le u V]

namespace Data

variable (D : Data K u ell)

include D in
theorem highOperator_coercive_wide (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 50) :
    CoerciveInverse.Coercive (highOperator K u ell V e) (1 / 40) := by
  intro x
  have hbase := D.baseHigh_coercive x
  have hp := inner_operator_re_lower (highPerturbation u ell V e) x
  have hnorm := mul_le_mul_of_nonneg_right
    (highPerturbation_norm_le_wide (u := u) V e hV he) (sq_nonneg ‖x‖)
  change (1 / 40 : ℝ) * ‖x‖ ^ 2 ≤
    (inner ℂ x (baseHigh K u ell x + highPerturbation u ell V e x)).re
  rw [inner_add_right, Complex.add_re]
  linarith

variable [CompleteSpace H]

include D in
theorem highOperator_isUnit_wide (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 50) :
    IsUnit (highOperator K u ell V e) :=
  CoerciveInverse.isUnit _ (by norm_num : (0 : ℝ) < 1 / 40)
    (D.highOperator_coercive_wide V e hV he)

include D in
theorem highOperator_inverse_apply_wide (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 50) (x : highSpace u) :
    highOperator K u ell V e (highInverse K u ell V e x) = x :=
  congrArg (fun T : highSpace u →L[ℂ] highSpace u => T x)
    (Ring.mul_inverse_cancel _ (D.highOperator_isUnit_wide V e hV he))

include D in
theorem highInverse_operator_apply_wide (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 50) (x : highSpace u) :
    highInverse K u ell V e (highOperator K u ell V e x) = x :=
  congrArg (fun T : highSpace u →L[ℂ] highSpace u => T x)
    (Ring.inverse_mul_cancel _ (D.highOperator_isUnit_wide V e hV he))

include D in
theorem highInverse_norm_le_wide (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 50) :
    ‖highInverse K u ell V e‖ ≤ 40 := by
  have heq : highInverse K u ell V e = CoerciveInverse.inverse (highOperator K u ell V e)
      (by norm_num : (0 : ℝ) < 1 / 40) (D.highOperator_coercive_wide V e hV he) := by
    apply ContinuousLinearMap.ext
    intro x
    apply (ContinuousLinearMap.isUnit_iff_bijective.mp (D.highOperator_isUnit_wide V e hV he)).1
    rw [D.highOperator_inverse_apply_wide V e hV he, CoerciveInverse.apply_inverse]
  rw [heq]
  simpa using CoerciveInverse.norm_inverse (highOperator K u ell V e)
    (by norm_num : (0 : ℝ) < 1 / 40) (D.highOperator_coercive_wide V e hV he)

end Data
end Maxwell.Continuum.RankOneBand
