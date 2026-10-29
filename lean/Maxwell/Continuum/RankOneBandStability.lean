import Maxwell.Continuum.RankOneBandBounds

/-! The same scalar Schur map is quantitatively stable in both energy and
the full perturbing operator. No entrywise estimates or dimension factors. -/

noncomputable section
namespace Maxwell.Continuum.RankOneBand.Data

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : H →L[ℂ] H} {u : H} {ell : ℝ} (D : Data K u ell)

include D in
theorem correctionVector_sub_norm_le (V W : H →L[ℂ] H) (e f : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (hW : ‖W‖ ≤ 1 / 256)
    (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) (hf : ‖f - (ell : ℂ)‖ ≤ 1 / 100) :
    ‖correctionVector K u ell V e - correctionVector K u ell W f‖ ≤
      40 * ‖V - W‖ + (1600 * (‖e - f‖ + ‖V - W‖)) / 256 := by
  have heq : correctionVector K u ell V e - correctionVector K u ell W f =
      embed u (highInverse K u ell V e (project u ((V - W) u))) +
      embed u ((highInverse K u ell V e - highInverse K u ell W f) (project u (W u))) := by
    simp only [correctionVector, sub_apply, map_sub]
    abel
  rw [heq]
  have hfirst : ‖embed u (highInverse K u ell V e (project u ((V - W) u)))‖ ≤ 40 * ‖V - W‖ := by
    rw [embed_norm]
    exact ((highInverse K u ell V e).le_opNorm _).trans (mul_le_mul
      (D.highInverse_norm_le V e hV he)
      (((highSpace u).norm_orthogonalProjectionOnto_apply_le _).trans (D.norm_apply_unit (V - W)))
      (norm_nonneg _) (by norm_num))
  have hsecond : ‖embed u ((highInverse K u ell V e - highInverse K u ell W f) (project u (W u)))‖ ≤
      (1600 * (‖e - f‖ + ‖V - W‖)) / 256 := by
    rw [embed_norm]
    have hp : ‖project u (W u)‖ ≤ 1 / 256 :=
      (((highSpace u).norm_orthogonalProjectionOnto_apply_le _).trans (D.norm_apply_unit W)).trans hW
    have h := ((highInverse K u ell V e - highInverse K u ell W f).le_opNorm _).trans
      (mul_le_mul (D.highInverse_sub_norm_le V W e f hV hW he hf) hp (norm_nonneg _)
        (mul_nonneg (by norm_num) (add_nonneg (norm_nonneg _) (norm_nonneg _))))
    simpa only [mul_one_div] using h
  exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)

include D in
theorem rootMap_sub_norm_le (V W : H →L[ℂ] H) (e f : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (hW : ‖W‖ ≤ 1 / 256)
    (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) (hf : ‖f - (ell : ℂ)‖ ≤ 1 / 100) :
    ‖rootMap K u ell V e - rootMap K u ell W f‖ ≤
      2 * ‖V - W‖ + (1 / 32) * ‖e - f‖ := by
  have heq : rootMap K u ell V e - rootMap K u ell W f =
      coefficient u ((V - W) u) +
      coefficient u ((V - W) (correctionVector K u ell V e)) +
      coefficient u (W (correctionVector K u ell V e - correctionVector K u ell W f)) := by
    simp only [rootMap, sub_apply, map_sub]
    ring
  rw [heq]
  have hfirst : ‖coefficient u ((V - W) u)‖ ≤ ‖V - W‖ :=
    (D.coefficient_norm_le _).trans (D.norm_apply_unit (V - W))
  have hc : ‖correctionVector K u ell V e‖ ≤ 40 / 256 := by
    linarith [D.correctionVector_norm_le V e hV he]
  have hsecond : ‖coefficient u ((V - W) (correctionVector K u ell V e))‖ ≤
      ‖V - W‖ * (40 / 256) :=
    ((D.coefficient_norm_le _).trans ((V - W).le_opNorm _)).trans
      (mul_le_mul_of_nonneg_left hc (norm_nonneg _))
  have hthird : ‖coefficient u (W (correctionVector K u ell V e - correctionVector K u ell W f))‖ ≤
      (1 / 256) * (40 * ‖V - W‖ + (1600 * (‖e - f‖ + ‖V - W‖)) / 256) :=
    ((D.coefficient_norm_le _).trans (W.le_opNorm _)).trans
      (mul_le_mul hW (D.correctionVector_sub_norm_le V W e f hV hW he hf)
        (norm_nonneg _) (by norm_num))
  have htri := norm_add_le
    (coefficient u ((V - W) u) + coefficient u ((V - W) (correctionVector K u ell V e)))
    (coefficient u (W (correctionVector K u ell V e - correctionVector K u ell W f)))
  have hpair := norm_add_le (coefficient u ((V - W) u))
    (coefficient u ((V - W) (correctionVector K u ell V e)))
  nlinarith [norm_nonneg (V - W), norm_nonneg (e - f)]

#print axioms correctionVector_sub_norm_le
#print axioms rootMap_sub_norm_le

end Maxwell.Continuum.RankOneBand.Data
