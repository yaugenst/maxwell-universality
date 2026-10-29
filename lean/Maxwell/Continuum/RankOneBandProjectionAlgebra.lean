import Maxwell.Continuum.RankOneBandProjection

/-! The explicit finite projection commutes with the frozen operator at
its simple root. Both products vanish there. -/

noncomputable section
namespace Maxwell.Continuum.RankOneBand.Data

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : H →L[ℂ] H} {u : H} {ell : ℝ} (D : Data K u ell)

include D in
theorem highSolve_operator (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) (x : H) :
    highSolve K u ell V e (operator K V e x) =
      coefficient u x • correctionVector K u ell V e - embed u (project u x) := by
  rw [highSolve_apply, D.project_operator, map_sub, map_smul,
    D.highInverse_operator_apply V e hV he, map_sub, map_smul]
  rfl

include D in
theorem numerator_operator (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) (x : H) :
    numerator K u ell V e (operator K V e x) = scalarResidual K u ell V e * coefficient u x := by
  rw [numerator_apply, D.coefficient_operator, D.highSolve_operator V e hV he,
    map_sub, map_smul, map_sub, map_smul]
  have hdec := congrArg (fun y => coefficient u (V y)) (D.decomposition x)
  simp only [map_add, map_smul] at hdec
  rw [← hdec]
  change ((ell : ℂ) - e) * coefficient u x +
    (coefficient u x * coefficient u (V u) + coefficient u (V (embed u (project u x)))) +
    (coefficient u x * coefficient u (V (correctionVector K u ell V e)) -
      coefficient u (V (embed u (project u x)))) = _
  unfold scalarResidual rootMap
  ring

include D in
theorem normalizedProjection_operator_zero (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100)
    (hg : rootMap K u ell V e = e) :
    normalizedProjection K u ell V e * operator K V e = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  change (numerator K u ell V e (eigenvectorLift K u ell V e))⁻¹ •
    (numerator K u ell V e (operator K V e x) • eigenvectorLift K u ell V e) = 0
  rw [D.numerator_operator V e hV he, scalarResidual, hg, sub_self, zero_mul, zero_smul, smul_zero]

include D in
theorem operator_normalizedProjection_zero (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100)
    (hg : rootMap K u ell V e = e) :
    operator K V e * normalizedProjection K u ell V e = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  change operator K V e ((numerator K u ell V e (eigenvectorLift K u ell V e))⁻¹ •
    (numerator K u ell V e x • eigenvectorLift K u ell V e)) = 0
  rw [map_smul, map_smul, D.operator_eigenvectorLift V e hV he, hg, sub_self,
    zero_smul, smul_zero, smul_zero]

#print axioms numerator_operator
#print axioms normalizedProjection_operator_zero
#print axioms operator_normalizedProjection_zero

end Maxwell.Continuum.RankOneBand.Data
