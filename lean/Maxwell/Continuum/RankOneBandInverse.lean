import Maxwell.Continuum.RankOneBandBasic
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! A genuine inverse of the full high compression at complex energy.
Quantitative complex coercivity constructs the inverse; no spectral or
inverse-existence premise is introduced. -/

noncomputable section
namespace Maxwell.Continuum.RankOneBand

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {K : H →L[ℂ] H} {u : H} {ell : ℝ}

def highPerturbation (u : H) (ell : ℝ) (V : H →L[ℂ] H) (e : ℂ) :
    highSpace u →L[ℂ] highSpace u :=
  (e - (ell : ℂ)) • (1 : highSpace u →L[ℂ] highSpace u) - compress u V

def highOperator (K : H →L[ℂ] H) (u : H) (ell : ℝ) (V : H →L[ℂ] H) (e : ℂ) :
    highSpace u →L[ℂ] highSpace u := baseHigh K u ell + highPerturbation u ell V e

def highInverse (K : H →L[ℂ] H) (u : H) (ell : ℝ) (V : H →L[ℂ] H) (e : ℂ) :
    highSpace u →L[ℂ] highSpace u := Ring.inverse (highOperator K u ell V e)

theorem highPerturbation_norm_le (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) :
    ‖highPerturbation u ell V e‖ ≤ 1 / 50 := by
  let _ : NormSMulClass ℂ (highSpace u →L[ℂ] highSpace u) :=
    NormedSpace.toNormSMulClass (𝕜 := ℂ) (E := highSpace u →L[ℂ] highSpace u)
  have hid : ‖(1 : highSpace u →L[ℂ] highSpace u)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hmul := mul_le_mul he hid (norm_nonneg (1 : highSpace u →L[ℂ] highSpace u))
    (by norm_num : (0 : ℝ) ≤ 1 / 100)
  have h := norm_sub_le ((e - (ell : ℂ)) • (1 : highSpace u →L[ℂ] highSpace u)) (compress u V)
  rw [norm_smul] at h
  change ‖highPerturbation u ell V e‖ ≤ _
  change ‖highPerturbation u ell V e‖ ≤ _ at h
  linarith [compress_norm_le u V]

theorem inner_operator_re_lower (B : H →L[ℂ] H) (x : H) :
    -(‖B‖ * ‖x‖ ^ 2) ≤ (inner ℂ x (B x)).re := by
  have h := (Complex.abs_re_le_norm (inner ℂ x (B x))).trans
    ((norm_inner_le_norm (𝕜 := ℂ) x (B x)).trans
      (mul_le_mul_of_nonneg_left (B.le_opNorm x) (norm_nonneg x)))
  have hneg := (abs_le.mp h).1
  nlinarith

namespace Data

variable (D : Data K u ell)

include D in
theorem highOperator_coercive (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) :
    CoerciveInverse.Coercive (highOperator K u ell V e) (1 / 40) := by
  intro x
  have hbase := D.baseHigh_coercive x
  have hp := inner_operator_re_lower (highPerturbation u ell V e) x
  have hnorm := mul_le_mul_of_nonneg_right
    (highPerturbation_norm_le (u := u) V e hV he) (sq_nonneg ‖x‖)
  change (1 / 40 : ℝ) * ‖x‖ ^ 2 ≤
    (inner ℂ x (baseHigh K u ell x + highPerturbation u ell V e x)).re
  rw [inner_add_right, Complex.add_re]
  nlinarith [sq_nonneg ‖x‖]

variable [CompleteSpace H]

include D in
theorem highOperator_isUnit (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) :
    IsUnit (highOperator K u ell V e) :=
  CoerciveInverse.isUnit _ (by norm_num : (0 : ℝ) < 1 / 40) (D.highOperator_coercive V e hV he)

include D in
theorem highOperator_mul_inverse (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) :
    highOperator K u ell V e * highInverse K u ell V e = 1 :=
  Ring.mul_inverse_cancel _ (D.highOperator_isUnit V e hV he)

include D in
theorem highInverse_mul_operator (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) :
    highInverse K u ell V e * highOperator K u ell V e = 1 :=
  Ring.inverse_mul_cancel _ (D.highOperator_isUnit V e hV he)

include D in
theorem highOperator_inverse_apply (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) (x : highSpace u) :
    highOperator K u ell V e (highInverse K u ell V e x) = x :=
  congrArg (fun T : highSpace u →L[ℂ] highSpace u => T x) (D.highOperator_mul_inverse V e hV he)

include D in
theorem highInverse_operator_apply (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) (x : highSpace u) :
    highInverse K u ell V e (highOperator K u ell V e x) = x :=
  congrArg (fun T : highSpace u →L[ℂ] highSpace u => T x) (D.highInverse_mul_operator V e hV he)

include D in
theorem highInverse_eq_coercive (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) :
    highInverse K u ell V e = CoerciveInverse.inverse (highOperator K u ell V e)
      (by norm_num : (0 : ℝ) < 1 / 40) (D.highOperator_coercive V e hV he) := by
  apply ContinuousLinearMap.ext
  intro x
  apply (ContinuousLinearMap.isUnit_iff_bijective.mp (D.highOperator_isUnit V e hV he)).1
  rw [D.highOperator_inverse_apply V e hV he, CoerciveInverse.apply_inverse]

include D in
theorem highInverse_norm_le (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) :
    ‖highInverse K u ell V e‖ ≤ 40 := by
  rw [D.highInverse_eq_coercive V e hV he]
  simpa using CoerciveInverse.norm_inverse (highOperator K u ell V e)
    (by norm_num : (0 : ℝ) < 1 / 40) (D.highOperator_coercive V e hV he)

#print axioms highOperator_isUnit
#print axioms highInverse_norm_le

end Data
end Maxwell.Continuum.RankOneBand
