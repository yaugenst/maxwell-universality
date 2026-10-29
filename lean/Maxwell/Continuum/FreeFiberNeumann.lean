import Maxwell.Continuum.FreeFiberPotential
import Maxwell.Continuum.SelfAdjointResolventData
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Bounded Neumann inverses without a common unbounded domain

The inverse of `A+B` is assembled as `R (I+B R)⁻¹`, where `R` is a genuine
bounded inverse of the partial operator `A`. Its image lies in the actual
domain of `A` because the left factor is `R`. Both inverse identities are
verified on that domain. The final specialization uses the literal free
Maxwell inverse and the six-neighbor material convolution.
-/

noncomputable section

namespace Maxwell.Continuum.FreeFiber

open SelfAdjointResolvent

namespace Neumann

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def series (T : H →L[ℂ] H) : H →L[ℂ] H := ∑' n : ℕ, T ^ n

theorem series_left (T : H →L[ℂ] H) (hT : ‖T‖ < 1) (u : H) :
    series T u - T (series T u) = u := by
  have h := congrArg (fun L : H →L[ℂ] H => L u) (mul_neg_geom_series T hT)
  exact h

theorem series_right (T : H →L[ℂ] H) (hT : ‖T‖ < 1) (u : H) :
    series T (u - T u) = u := by
  have h := congrArg (fun L : H →L[ℂ] H => L u) (geom_series_mul_neg T hT)
  exact h

omit [CompleteSpace H] in
theorem series_norm_le (T : H →L[ℂ] H) (hT : ‖T‖ < 1) :
    ‖series T‖ ≤ (1 - ‖T‖)⁻¹ := by
  have h := tsum_geometric_le_of_norm_lt_one T hT
  have hone : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  change ‖series T‖ ≤ _ at h
  linarith

/-- Bounded perturbation inverse, with domain membership and both laws proved. -/
def perturbationInverse (A : H →ₗ.[ℂ] H) (R : BoundedInverse A) (B : H →L[ℂ] H)
    (hBR : ‖B * R.map‖ < 1) : BoundedInverse (FormPerturbation.addBounded A B) where
  map := R.map * series (-(B * R.map))
  mem_domain f := R.mem_domain (series (-(B * R.map)) f)
  apply_map f := by
    change A ⟨R.map (series (-(B * R.map)) f), _⟩ +
      B (R.map (series (-(B * R.map)) f)) = f
    rw [R.apply_map]
    have h := series_left (-(B * R.map)) (by simpa only [norm_neg] using hBR) f
    change series (-(B * R.map)) f - -(B (R.map (series (-(B * R.map)) f))) = f at h
    simpa only [sub_neg_eq_add] using h
  map_apply u := by
    change R.map (series (-(B * R.map)) (A u + B u.val)) = u.val
    have h := series_right (-(B * R.map)) (by simpa only [norm_neg] using hBR) (A u)
    change series (-(B * R.map)) (A u - -(B (R.map (A u)))) = A u at h
    rw [sub_neg_eq_add, R.map_apply] at h
    exact (congrArg R.map h).trans (R.map_apply u)

theorem perturbationInverse_norm_le (A : H →ₗ.[ℂ] H) (R : BoundedInverse A)
    (B : H →L[ℂ] H) (hBR : ‖B * R.map‖ < 1) :
    ‖(perturbationInverse A R B hBR).map‖ ≤
      ‖R.map‖ * (1 - ‖B * R.map‖)⁻¹ := by
  calc
    ‖R.map * series (-(B * R.map))‖ ≤ ‖R.map‖ * ‖series (-(B * R.map))‖ := norm_mul_le _ _
    _ ≤ ‖R.map‖ * (1 - ‖B * R.map‖)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [norm_neg] using
        series_norm_le (-(B * R.map)) (by simpa only [norm_neg] using hBR)

end Neumann

/-- Package the explicit free-fiber inverse in the shared genuine-inverse interface. -/
def freeInverseData (q : Momentum) (E : ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ν, ‖inverseBlock (aliasMomentum q ν) E‖ ≤ C) (hE : E ≠ 0)
    (hp : ∀ ν, momentumSquare (aliasMomentum q ν) - E ≠ 0) :
    BoundedInverse (operator q E) where
  map := boundedInverse q E hC hbound
  mem_domain := boundedInverse_mem_domain q E hC hbound hE hp
  apply_map := operator_boundedInverse q E hC hbound hE hp
  map_apply := boundedInverse_operator q E hC hbound hE hp

theorem material_product_norm_le (q : Momentum) (E : ℂ) (ρ : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ν, ‖inverseBlock (aliasMomentum q ν) E‖ ≤ C) :
    ‖(-(ρ : ℂ) • potential) * boundedInverse q E hC hbound‖ ≤ |ρ| * 7 * C := by
  calc
    ‖(-(ρ : ℂ) • potential) * boundedInverse q E hC hbound‖ ≤
        ‖-(ρ : ℂ) • potential‖ * ‖boundedInverse q E hC hbound‖ := norm_mul_le _ _
    _ = |ρ| * ‖potential‖ * ‖boundedInverse q E hC hbound‖ := by
      rw [norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ |ρ| * 7 * C := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left potential_norm_le (abs_nonneg ρ)
      · exact boundedInverse_norm_le q E hC hbound
      · exact norm_nonneg _
      · positivity

/-- The actual complex material fiber has a bounded inverse under the explicit
free-block bound and the quantitative Neumann smallness condition. -/
def materialInverseData (q : Momentum) (E : ℂ) (ρ : ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ ν, ‖inverseBlock (aliasMomentum q ν) E‖ ≤ C) (hE : E ≠ 0)
    (hp : ∀ ν, momentumSquare (aliasMomentum q ν) - E ≠ 0)
    (hsmall : |ρ| * 7 * C < 1) : BoundedInverse (materialFiber q E ρ) :=
  Neumann.perturbationInverse (operator q E) (freeInverseData q E hC hbound hE hp)
    (-(ρ : ℂ) • potential) ((material_product_norm_le q E ρ hC hbound).trans_lt hsmall)

end Maxwell.Continuum.FreeFiber
