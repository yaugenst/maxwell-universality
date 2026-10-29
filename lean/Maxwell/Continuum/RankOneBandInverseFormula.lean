import Maxwell.Continuum.RankOneBandKernel

/-! The actual rank-one Schur inverse of `K + V - e`, with both inverse
identities. Its finite-rank term and high solve are literal bounded maps. -/

noncomputable section
namespace Maxwell.Continuum.RankOneBand

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {K : H →L[ℂ] H} {u : H} {ell : ℝ}

def highSolve (K : H →L[ℂ] H) (u : H) (ell : ℝ) (V : H →L[ℂ] H) (e : ℂ) : H →L[ℂ] H :=
  (embed u).comp ((highInverse K u ell V e).comp (project u))

def numerator (K : H →L[ℂ] H) (u : H) (ell : ℝ) (V : H →L[ℂ] H) (e : ℂ) : H →L[ℂ] ℂ :=
  coefficient u + (coefficient u).comp (V.comp (highSolve K u ell V e))

def rankOneNumerator (K : H →L[ℂ] H) (u : H) (ell : ℝ) (V : H →L[ℂ] H) (e : ℂ) : H →L[ℂ] H :=
  (numerator K u ell V e).smulRight (eigenvectorLift K u ell V e)

def scalarResidual (K : H →L[ℂ] H) (u : H) (ell : ℝ) (V : H →L[ℂ] H) (e : ℂ) : ℂ :=
  rootMap K u ell V e - e

def resolvent (K : H →L[ℂ] H) (u : H) (ell : ℝ) (V : H →L[ℂ] H) (e : ℂ) : H →L[ℂ] H :=
  (scalarResidual K u ell V e)⁻¹ • rankOneNumerator K u ell V e - highSolve K u ell V e

@[simp] theorem highSolve_apply (V : H →L[ℂ] H) (e : ℂ) (x : H) :
    highSolve K u ell V e x = embed u (highInverse K u ell V e (project u x)) := rfl

@[simp] theorem numerator_apply (V : H →L[ℂ] H) (e : ℂ) (x : H) :
    numerator K u ell V e x = coefficient u x + coefficient u (V (highSolve K u ell V e x)) := rfl

@[simp] theorem coefficient_highSolve (V : H →L[ℂ] H) (e : ℂ) (x : H) :
    coefficient u (highSolve K u ell V e x) = 0 := coefficient_embed _

@[simp] theorem project_highSolve (V : H →L[ℂ] H) (e : ℂ) (x : H) :
    project u (highSolve K u ell V e x) = highInverse K u ell V e (project u x) := project_embed _

@[simp] theorem highSolve_self (V : H →L[ℂ] H) (e : ℂ) : highSolve K u ell V e u = 0 := by
  simp [highSolve_apply]

theorem resolvent_apply (V : H →L[ℂ] H) (e : ℂ) (x : H) :
    resolvent K u ell V e x =
      (numerator K u ell V e x / scalarResidual K u ell V e) • eigenvectorLift K u ell V e -
        highSolve K u ell V e x := by
  change (scalarResidual K u ell V e)⁻¹ •
    (numerator K u ell V e x • eigenvectorLift K u ell V e) - _ = _
  rw [smul_smul, div_eq_mul_inv, mul_comm]
  rfl

namespace Data

variable (D : Data K u ell)

include D in
@[simp] theorem numerator_self (V : H →L[ℂ] H) (e : ℂ) : numerator K u ell V e u = 1 := by
  simp [numerator_apply, D.coefficient_self]

variable [CompleteSpace H]

include D in
theorem operator_highSolve (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) (x : H) :
    operator K V e (highSolve K u ell V e x) =
      coefficient u (V (highSolve K u ell V e x)) • u - embed u (project u x) := by
  have hc := D.coefficient_operator V e (highSolve K u ell V e x)
  rw [coefficient_highSolve, mul_zero, zero_add] at hc
  have hp := D.project_operator V e (highSolve K u ell V e x)
  rw [coefficient_highSolve, zero_smul, project_highSolve,
    D.highOperator_inverse_apply V e hV he, zero_sub] at hp
  calc
    _ = coefficient u (operator K V e (highSolve K u ell V e x)) • u +
      embed u (project u (operator K V e (highSolve K u ell V e x))) := (D.decomposition _).symm
    _ = _ := by rw [hc, hp, map_neg, sub_eq_add_neg]

include D in
theorem operator_resolvent_apply (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100)
    (hg : scalarResidual K u ell V e ≠ 0) (x : H) :
    operator K V e (resolvent K u ell V e x) = x := by
  rw [resolvent_apply, map_sub, map_smul, D.operator_eigenvectorLift V e hV he,
    D.operator_highSolve V e hV he, smul_smul]
  change ((numerator K u ell V e x / scalarResidual K u ell V e) *
    scalarResidual K u ell V e) • u -
    (coefficient u (V (highSolve K u ell V e x)) • u - embed u (project u x)) = x
  rw [div_mul_cancel₀ _ hg, numerator_apply, add_smul]
  calc
    _ = coefficient u x • u + embed u (project u x) := by abel
    _ = x := D.decomposition x

include D in
theorem operator_injective (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100)
    (hg : scalarResidual K u ell V e ≠ 0) : Function.Injective (operator K V e) := by
  intro x y hxy
  by_contra hne
  apply hg
  apply sub_eq_zero.mpr
  apply (D.kernel_nonzero_iff_fixed V e hV he).mp
  refine ⟨x - y, sub_ne_zero.mpr hne, ?_⟩
  rw [map_sub, hxy, sub_self]

include D in
theorem resolvent_operator_apply (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100)
    (hg : scalarResidual K u ell V e ≠ 0) (x : H) :
    resolvent K u ell V e (operator K V e x) = x := by
  apply D.operator_injective V e hV he hg
  exact D.operator_resolvent_apply V e hV he hg _

include D in
theorem operator_isUnit (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100)
    (hg : scalarResidual K u ell V e ≠ 0) : IsUnit (operator K V e) := by
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  exact ⟨D.operator_injective V e hV he hg,
    fun x => ⟨resolvent K u ell V e x, D.operator_resolvent_apply V e hV he hg x⟩⟩

include D in
theorem resolvent_eq_ringInverse (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100)
    (hg : scalarResidual K u ell V e ≠ 0) :
    resolvent K u ell V e = Ring.inverse (operator K V e) := by
  apply ContinuousLinearMap.ext
  intro x
  apply D.operator_injective V e hV he hg
  rw [D.operator_resolvent_apply V e hV he hg]
  exact (congrArg (fun T : H →L[ℂ] H => T x)
    (Ring.mul_inverse_cancel _ (D.operator_isUnit V e hV he hg))).symm

#print axioms operator_resolvent_apply
#print axioms resolvent_operator_apply
#print axioms resolvent_eq_ringInverse

end Data
end Maxwell.Continuum.RankOneBand
