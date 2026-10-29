import Maxwell.Continuum.RankOneBandWideInverse
import Maxwell.Continuum.RankOneBandFamily

/-! No extra eigenvalue can enter the wider `1/50` disk. A kernel vector
forces the literal scalar Schur root within `1/200` of the unperturbed
eigenvalue, where the already constructed narrow-band uniqueness applies. -/

noncomputable section
namespace Maxwell.Continuum.RankOneBand.Data

set_option backward.isDefEq.respectTransparency false

open Set Metric

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : H →L[ℂ] H} {u : H} {ell : ℝ} (D : Data K u ell)

include D in
theorem correctionVector_norm_le_wide (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 50) :
    ‖correctionVector K u ell V e‖ ≤ 40 * ‖V‖ := by
  change ‖embed u (highInverse K u ell V e (project u (V u)))‖ ≤ _
  rw [embed_norm]
  calc
    _ ≤ ‖highInverse K u ell V e‖ * ‖project u (V u)‖ := (highInverse K u ell V e).le_opNorm _
    _ ≤ 40 * ‖V u‖ := mul_le_mul (D.highInverse_norm_le_wide V e hV he)
      ((highSpace u).norm_orthogonalProjectionOnto_apply_le (V u)) (norm_nonneg _) (by norm_num)
    _ ≤ 40 * ‖V‖ := mul_le_mul_of_nonneg_left (D.norm_apply_unit V) (by norm_num)

include D in
theorem rootMap_center_bound_wide (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 50) :
    ‖rootMap K u ell V e - (ell : ℂ)‖ ≤ 1 / 200 := by
  have hfirst : ‖coefficient u (V u)‖ ≤ 1 / 256 :=
    ((D.coefficient_norm_le _).trans (D.norm_apply_unit V)).trans hV
  have hc : ‖correctionVector K u ell V e‖ ≤ 40 / 256 := by
    linarith [D.correctionVector_norm_le_wide V e hV he]
  have hsecond : ‖coefficient u (V (correctionVector K u ell V e))‖ ≤ (1 / 256) * (40 / 256) :=
    ((D.coefficient_norm_le _).trans (V.le_opNorm _)).trans
      (mul_le_mul hV hc (norm_nonneg _) (by norm_num))
  have heq : rootMap K u ell V e - (ell : ℂ) =
      coefficient u (V u) + coefficient u (V (correctionVector K u ell V e)) := by
    unfold rootMap
    ring
  rw [heq]
  exact (norm_add_le _ _).trans (by linarith)

include D in
theorem kernel_reconstruction_wide (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 50)
    (x : H) (hx : operator K V e x = 0) :
    x = coefficient u x • eigenvectorLift K u ell V e := by
  have hp := congrArg (project u) hx
  rw [D.project_operator, map_zero] at hp
  have heq := congrArg (highInverse K u ell V e) (sub_eq_zero.mp hp).symm
  rw [D.highInverse_operator_apply_wide V e hV he, map_smul] at heq
  calc
    x = coefficient u x • u + embed u (project u x) := (D.decomposition x).symm
    _ = coefficient u x • eigenvectorLift K u ell V e := by
      rw [heq, map_smul, ← smul_add]
      rfl

include D in
theorem kernel_energy_center_bound_wide (V : H →L[ℂ] H) (e : ℂ)
    (hV : ‖V‖ ≤ 1 / 256) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 50)
    (hker : ∃ x : H, x ≠ 0 ∧ operator K V e x = 0) :
    ‖e - (ell : ℂ)‖ ≤ 1 / 200 := by
  obtain ⟨x, hx0, hx⟩ := hker
  have hrec := D.kernel_reconstruction_wide V e hV he x hx
  have hc : coefficient u x ≠ 0 := by
    intro h
    rw [h, zero_smul] at hrec
    exact hx0 hrec
  have h := congrArg (coefficient u) hx
  rw [hrec, map_smul, map_smul, D.coefficient_operator_lift, map_zero] at h
  have hroot := sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hc)
  rw [← hroot]
  exact D.rootMap_center_bound_wide V e hV he

variable {E : Type*} {V : E → ℂ → H →L[ℂ] H} {U : Set E}

include D in
theorem kernel_nonzero_iff_bandRoot_wide (P : PerturbationData V U ell)
    (p : E) (hp : p ∈ U) (e : ℂ) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 50)
    (hV : ‖V p e‖ ≤ 1 / 256) :
    (∃ x : H, x ≠ 0 ∧ operator K (V p e) e x = 0) ↔ e = D.bandRoot P p := by
  constructor
  · intro hker
    have hsmall : e ∈ closedBall (ell : ℂ) (1 / 100) := by
      rw [mem_closedBall, dist_eq_norm]
      exact (D.kernel_energy_center_bound_wide (V p e) e hV he hker).trans (by norm_num)
    exact (D.kernel_nonzero_iff_bandRoot P p hp e hsmall).mp hker
  · rintro rfl
    exact ⟨D.bandVector P p, D.bandVector_ne_zero P p, D.bandVector_kernel P p hp⟩

include D in
theorem operator_injective_wide (P : PerturbationData V U ell)
    (p : E) (hp : p ∈ U) (e : ℂ) (he : ‖e - (ell : ℂ)‖ ≤ 1 / 50)
    (hV : ‖V p e‖ ≤ 1 / 256) (hne : e ≠ D.bandRoot P p) :
    Function.Injective (operator K (V p e) e) := by
  intro x y hxy
  by_contra hne'
  apply hne
  apply (D.kernel_nonzero_iff_bandRoot_wide P p hp e he hV).mp
  refine ⟨x - y, sub_ne_zero.mpr hne', ?_⟩
  rw [map_sub, hxy, sub_self]

end Maxwell.Continuum.RankOneBand.Data
