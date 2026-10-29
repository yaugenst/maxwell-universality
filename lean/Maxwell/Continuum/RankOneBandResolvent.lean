import Maxwell.Continuum.RankOneBandInverse

/-! Quantitative resolvent identities for the literal high operator. -/

noncomputable section
namespace Maxwell.Continuum.RankOneBand

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {K : H →L[ℂ] H} {u : H} {ell : ℝ}

def compression (u : H) : (H →L[ℂ] H) →L[ℂ] (highSpace u →L[ℂ] highSpace u) :=
  ((ContinuousLinearMap.compL ℂ (highSpace u) H (highSpace u)).flip (embed u)).comp
    (ContinuousLinearMap.compL ℂ H H (highSpace u) (project u))

@[simp] theorem compression_apply (A : H →L[ℂ] H) : compression u A = compress u A := rfl

theorem highOperator_sub (V W : H →L[ℂ] H) (e f : ℂ) :
    highOperator K u ell V e - highOperator K u ell W f =
      (e - f) • (1 : highSpace u →L[ℂ] highSpace u) - compress u (V - W) := by
  apply ContinuousLinearMap.ext
  intro x
  change (baseHigh K u ell x + ((e - (ell : ℂ)) • x - project u (V (embed u x)))) -
    (baseHigh K u ell x + ((f - (ell : ℂ)) • x - project u (W (embed u x)))) =
    (e - f) • x - project u (V (embed u x) - W (embed u x))
  simp only [map_sub, sub_smul]
  abel

theorem highOperator_sub_norm_le (V W : H →L[ℂ] H) (e f : ℂ) :
    ‖highOperator K u ell V e - highOperator K u ell W f‖ ≤ ‖e - f‖ + ‖V - W‖ := by
  let _ : NormSMulClass ℂ (highSpace u →L[ℂ] highSpace u) :=
    NormedSpace.toNormSMulClass (𝕜 := ℂ) (E := highSpace u →L[ℂ] highSpace u)
  rw [highOperator_sub]
  have h := norm_sub_le ((e - f) • (1 : highSpace u →L[ℂ] highSpace u)) (compress u (V - W))
  rw [norm_smul] at h
  have hi := mul_le_mul_of_nonneg_left
    (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := highSpace u)) (norm_nonneg (e - f))
  change ‖e - f‖ * ‖(1 : highSpace u →L[ℂ] highSpace u)‖ ≤ ‖e - f‖ * 1 at hi
  linarith [compress_norm_le u (V - W)]

namespace Data

variable [CompleteSpace H]

variable (D : Data K u ell)

include D in
theorem highInverse_sub (V W : H →L[ℂ] H) (e f : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (hW : ‖W‖ ≤ 1 / 256)
    (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) (hf : ‖f - (ell : ℂ)‖ ≤ 1 / 100) :
    highInverse K u ell V e - highInverse K u ell W f =
      highInverse K u ell V e * (highOperator K u ell W f - highOperator K u ell V e) *
        highInverse K u ell W f := by
  rw [mul_sub, sub_mul, mul_assoc _ (highOperator K u ell W f) _,
    D.highOperator_mul_inverse W f hW hf, D.highInverse_mul_operator V e hV he,
    mul_one, one_mul]

include D in
theorem highInverse_sub_norm_le (V W : H →L[ℂ] H) (e f : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (hW : ‖W‖ ≤ 1 / 256)
    (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) (hf : ‖f - (ell : ℂ)‖ ≤ 1 / 100) :
    ‖highInverse K u ell V e - highInverse K u ell W f‖ ≤
      1600 * (‖e - f‖ + ‖V - W‖) := by
  have hA : ‖highOperator K u ell W f - highOperator K u ell V e‖ ≤ ‖e - f‖ + ‖V - W‖ := by
    simpa only [norm_sub_rev f e, norm_sub_rev W V] using
      highOperator_sub_norm_le (K := K) (u := u) (ell := ell) W V f e
  have hmul := norm_mul_le
    (highInverse K u ell V e * (highOperator K u ell W f - highOperator K u ell V e))
    (highInverse K u ell W f)
  have hinner := norm_mul_le (highInverse K u ell V e)
    (highOperator K u ell W f - highOperator K u ell V e)
  rw [D.highInverse_sub V W e f hV hW he hf]
  calc
    _ ≤ (‖highInverse K u ell V e‖ *
          ‖highOperator K u ell W f - highOperator K u ell V e‖) *
          ‖highInverse K u ell W f‖ :=
      hmul.trans (mul_le_mul_of_nonneg_right hinner (norm_nonneg (highInverse K u ell W f)))
    _ ≤ (40 * (‖e - f‖ + ‖V - W‖)) * 40 := mul_le_mul
      (mul_le_mul (D.highInverse_norm_le V e hV he) hA
        (norm_nonneg (highOperator K u ell W f - highOperator K u ell V e)) (by norm_num))
      (D.highInverse_norm_le W f hW hf) (norm_nonneg (highInverse K u ell W f))
      (mul_nonneg (by norm_num) (add_nonneg (norm_nonneg _) (norm_nonneg _)))
    _ = _ := by ring

#print axioms highInverse_sub
#print axioms highInverse_sub_norm_le

end Data
end Maxwell.Continuum.RankOneBand
