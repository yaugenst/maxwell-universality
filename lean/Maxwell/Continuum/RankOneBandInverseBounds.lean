import Maxwell.Continuum.RankOneBandInverseFormula
import Maxwell.Continuum.RankOneBandFamily

/-! Dimension-free resolvent estimates measured by distance to the actual
constructed band root. -/

noncomputable section
namespace Maxwell.Continuum.RankOneBand.Data

set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped NNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : H →L[ℂ] H} {u : H} {ell : ℝ} (D : Data K u ell)

include D in
theorem highSolve_norm_le (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) :
    ‖highSolve K u ell V e‖ ≤ 40 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [highSolve_apply, embed_norm]
  exact ((highInverse K u ell V e).le_opNorm _).trans
    (mul_le_mul (D.highInverse_norm_le V e hV he)
      ((highSpace u).norm_orthogonalProjectionOnto_apply_le x) (norm_nonneg _) (by norm_num))

include D in
theorem numerator_norm_le (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) :
    ‖numerator K u ell V e‖ ≤ 3 / 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [numerator_apply]
  have hh : ‖highSolve K u ell V e x‖ ≤ 40 * ‖x‖ :=
    ((highSolve K u ell V e).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (D.highSolve_norm_le V e hV he) (norm_nonneg x))
  have hv : ‖V (highSolve K u ell V e x)‖ ≤ (1 / 256) * (40 * ‖x‖) :=
    (V.le_opNorm _).trans (mul_le_mul hV hh (norm_nonneg _) (by norm_num))
  have h := norm_add_le (coefficient u x) (coefficient u (V (highSolve K u ell V e x)))
  nlinarith [D.coefficient_norm_le x, D.coefficient_norm_le (V (highSolve K u ell V e x)), norm_nonneg x]

include D in
theorem eigenvectorLift_norm_le_three_halves (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) :
    ‖eigenvectorLift K u ell V e‖ ≤ 3 / 2 := by
  have h := norm_add_le u (correctionVector K u ell V e)
  rw [D.unit_norm] at h
  change ‖eigenvectorLift K u ell V e‖ ≤ _ at h
  linarith [D.correctionVector_norm_le V e hV he]

include D in
theorem rankOneNumerator_norm_le (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) :
    ‖rankOneNumerator K u ell V e‖ ≤ 9 / 4 := by
  rw [rankOneNumerator, ContinuousLinearMap.norm_smulRight_apply]
  have h := mul_le_mul (D.numerator_norm_le V e hV he)
    (D.eigenvectorLift_norm_le_three_halves V e hV he) (norm_nonneg _) (by norm_num)
  norm_num at h
  exact h

include D in
theorem resolvent_norm_le_residual (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) :
    ‖resolvent K u ell V e‖ ≤ (9 / 4) / ‖scalarResidual K u ell V e‖ + 40 := by
  have h := norm_sub_le ((scalarResidual K u ell V e)⁻¹ • rankOneNumerator K u ell V e)
    (highSolve K u ell V e)
  rw [norm_smul, norm_inv] at h
  change ‖resolvent K u ell V e‖ ≤ _ at h
  have hr : ‖scalarResidual K u ell V e‖⁻¹ * ‖rankOneNumerator K u ell V e‖ ≤
      (9 / 4) / ‖scalarResidual K u ell V e‖ := by
    calc
      _ ≤ ‖scalarResidual K u ell V e‖⁻¹ * (9 / 4) :=
        mul_le_mul_of_nonneg_left (D.rankOneNumerator_norm_le V e hV he)
          (inv_nonneg.mpr (norm_nonneg (scalarResidual K u ell V e)))
      _ = _ := by rw [div_eq_mul_inv]; ring
  linarith [D.highSolve_norm_le V e hV he]

variable {E : Type*} {V : E → ℂ → H →L[ℂ] H} {U : Set E}
variable (P : PerturbationData V U ell)

theorem scalarResidual_lower (p : E) (hp : p ∈ U) (e : ℂ)
    (he : e ∈ closedBall (ell : ℂ) (1 / 100)) :
    (3 / 4) * ‖e - D.bandRoot P p‖ ≤ ‖scalarResidual K u ell (V p e) e‖ := by
  have hl := ((D.contractionData P).lipschitz p hp).dist_le_mul
    e he (D.bandRoot P p) (D.bandRoot_mem P p hp)
  change dist (rootMap K u ell (V p e) e)
    (rootMap K u ell (V p (D.bandRoot P p)) (D.bandRoot P p)) ≤ _ at hl
  rw [D.bandRoot_fixed P p hp, dist_eq_norm, dist_eq_norm] at hl
  have ht := dist_triangle e (rootMap K u ell (V p e) e) (D.bandRoot P p)
  simp only [dist_eq_norm] at ht
  rw [norm_sub_rev e (rootMap K u ell (V p e) e)] at ht
  change ‖e - D.bandRoot P p‖ ≤ ‖scalarResidual K u ell (V p e) e‖ + _ at ht
  norm_num at hl
  linarith

theorem scalarResidual_ne_zero (p : E) (hp : p ∈ U) (e : ℂ)
    (he : e ∈ closedBall (ell : ℂ) (1 / 100)) (hne : e ≠ D.bandRoot P p) :
    scalarResidual K u ell (V p e) e ≠ 0 := by
  have hd := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have h := D.scalarResidual_lower P p hp e he
  intro hz
  rw [hz, norm_zero] at h
  linarith

theorem resolvent_norm_le_bandRoot (p : E) (hp : p ∈ U) (e : ℂ)
    (he : e ∈ closedBall (ell : ℂ) (1 / 100)) (hne : e ≠ D.bandRoot P p) :
    ‖resolvent K u ell (V p e) e‖ ≤ 3 / ‖e - D.bandRoot P p‖ + 40 := by
  have hd := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hg := norm_pos_iff.mpr (D.scalarResidual_ne_zero P p hp e he hne)
  have hlow := D.scalarResidual_lower P p hp e he
  have hdiv : (9 / 4) / ‖scalarResidual K u ell (V p e) e‖ ≤ 3 / ‖e - D.bandRoot P p‖ :=
    (div_le_div_iff₀ hg hd).mpr (by linarith)
  exact (D.resolvent_norm_le_residual (V p e) e (P.small p hp e he) (by
    simpa only [mem_closedBall, dist_eq_norm] using he)).trans (add_le_add hdiv le_rfl)

#print axioms scalarResidual_lower
#print axioms resolvent_norm_le_bandRoot

end Maxwell.Continuum.RankOneBand.Data
