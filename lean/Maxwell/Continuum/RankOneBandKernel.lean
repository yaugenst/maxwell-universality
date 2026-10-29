import Maxwell.Continuum.RankOneBandBounds

/-! Exact full-operator eigenvector lifting and kernel reconstruction for
the scalar Schur equation, including its one-dimensional kernel. -/

noncomputable section
namespace Maxwell.Continuum.RankOneBand

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {K : H →L[ℂ] H} {u : H} {ell : ℝ}

def operator (K V : H →L[ℂ] H) (e : ℂ) : H →L[ℂ] H := K + V - e • 1

theorem highOperator_apply (V : H →L[ℂ] H) (e : ℂ) (x : highSpace u) :
    highOperator K u ell V e x =
      e • x - project u (K (embed u x)) - project u (V (embed u x)) := by
  change project u ((ell : ℂ) • embed u x - K (embed u x)) +
    ((e - (ell : ℂ)) • x - project u (V (embed u x))) = _
  simp only [map_sub, map_smul, project_embed, sub_smul]
  abel

namespace Data

variable (D : Data K u ell)

include D in
theorem coefficient_operator (V : H →L[ℂ] H) (e : ℂ) (x : H) :
    coefficient u (operator K V e x) =
      ((ell : ℂ) - e) * coefficient u x + coefficient u (V x) := by
  change coefficient u (K x + V x - e • x) = _
  rw [map_sub, map_add, map_smul, D.coefficient_K]
  change (ell : ℂ) * coefficient u x + coefficient u (V x) - e * coefficient u x = _
  ring

include D in
theorem project_operator (V : H →L[ℂ] H) (e : ℂ) (x : H) :
    project u (operator K V e x) = coefficient u x • project u (V u) -
      highOperator K u ell V e (project u x) := by
  have hK := congrArg (fun y => project u (K y)) (D.decomposition x)
  simp only [map_add, map_smul, D.eigenvector, project_self, smul_zero, zero_add] at hK
  have hV := congrArg (fun y => project u (V y)) (D.decomposition x)
  simp only [map_add, map_smul] at hV
  change project u (K x + V x - e • x) = _
  rw [map_sub, map_add, map_smul, ← hK, ← hV, highOperator_apply]
  abel

include D in
@[simp] theorem coefficient_eigenvectorLift (V : H →L[ℂ] H) (e : ℂ) :
    coefficient u (eigenvectorLift K u ell V e) = 1 := by
  change coefficient u (u + embed u (highInverse K u ell V e (project u (V u)))) = 1
  rw [map_add, D.coefficient_self, coefficient_embed, add_zero]

@[simp] theorem project_eigenvectorLift (V : H →L[ℂ] H) (e : ℂ) :
    project u (eigenvectorLift K u ell V e) = highInverse K u ell V e (project u (V u)) := by
  change project u (u + embed u (highInverse K u ell V e (project u (V u)))) = _
  rw [map_add, project_self, project_embed, zero_add]

include D in
theorem eigenvectorLift_ne_zero (V : H →L[ℂ] H) (e : ℂ) :
    eigenvectorLift K u ell V e ≠ 0 := by
  intro h
  have hh := D.coefficient_eigenvectorLift V e
  rw [h, map_zero] at hh
  exact zero_ne_one hh

include D in
theorem coefficient_operator_lift (V : H →L[ℂ] H) (e : ℂ) :
    coefficient u (operator K V e (eigenvectorLift K u ell V e)) = rootMap K u ell V e - e := by
  rw [D.coefficient_operator, D.coefficient_eigenvectorLift, mul_one]
  change (ell : ℂ) - e + coefficient u (V (u + correctionVector K u ell V e)) = _
  rw [map_add, map_add]
  unfold rootMap
  ring

variable [CompleteSpace H]

include D in
theorem operator_eigenvectorLift (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) :
    operator K V e (eigenvectorLift K u ell V e) = (rootMap K u ell V e - e) • u := by
  have hproj : project u (operator K V e (eigenvectorLift K u ell V e)) = 0 := by
    rw [D.project_operator, D.coefficient_eigenvectorLift, project_eigenvectorLift,
      D.highOperator_inverse_apply V e hV he, one_smul, sub_self]
  have h := D.decomposition (operator K V e (eigenvectorLift K u ell V e))
  rw [D.coefficient_operator_lift, hproj, map_zero, add_zero] at h
  exact h.symm

include D in
theorem kernel_reconstruction (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100)
    (x : H) (hx : operator K V e x = 0) :
    x = coefficient u x • eigenvectorLift K u ell V e := by
  have hp := congrArg (project u) hx
  rw [D.project_operator, map_zero] at hp
  have heq := congrArg (highInverse K u ell V e) (sub_eq_zero.mp hp).symm
  rw [D.highInverse_operator_apply V e hV he, map_smul] at heq
  calc
    x = coefficient u x • u + embed u (project u x) := (D.decomposition x).symm
    _ = coefficient u x • eigenvectorLift K u ell V e := by
      rw [heq, map_smul, ← smul_add]
      rfl

include D in
theorem kernel_nonzero_iff_fixed (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100) :
    (∃ x : H, x ≠ 0 ∧ operator K V e x = 0) ↔ rootMap K u ell V e = e := by
  constructor
  · rintro ⟨x, hx0, hx⟩
    have hrec := D.kernel_reconstruction V e hV he x hx
    have hc : coefficient u x ≠ 0 := by
      intro h
      rw [h, zero_smul] at hrec
      exact hx0 hrec
    have h := congrArg (coefficient u) hx
    rw [hrec, map_smul, map_smul, D.coefficient_operator_lift, map_zero] at h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hc)
  · intro hroot
    refine ⟨eigenvectorLift K u ell V e, D.eigenvectorLift_ne_zero V e, ?_⟩
    rw [D.operator_eigenvectorLift V e hV he, hroot, sub_self, zero_smul]

include D in
theorem kernel_eq_span (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100)
    (hroot : rootMap K u ell V e = e) :
    (operator K V e).ker = ℂ ∙ eigenvectorLift K u ell V e := by
  ext x
  constructor
  · intro hx
    exact Submodule.mem_span_singleton.mpr
      ⟨coefficient u x, (D.kernel_reconstruction V e hV he x hx).symm⟩
  · intro hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    change operator K V e (a • eigenvectorLift K u ell V e) = 0
    rw [map_smul, D.operator_eigenvectorLift V e hV he, hroot, sub_self, zero_smul, smul_zero]

include D in
theorem kernel_finrank_one (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 100)
    (hroot : rootMap K u ell V e = e) : Module.finrank ℂ (operator K V e).ker = 1 := by
  rw [D.kernel_eq_span V e hV he hroot]
  exact finrank_span_singleton (D.eigenvectorLift_ne_zero V e)

#print axioms operator_eigenvectorLift
#print axioms kernel_nonzero_iff_fixed
#print axioms kernel_finrank_one

end Data
end Maxwell.Continuum.RankOneBand
