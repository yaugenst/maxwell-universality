import Maxwell.Continuum.FreeFiberSelfAdjoint
import Maxwell.Continuum.FormPerturbation
import Mathlib.Tactic.FinCases

/-!
# Actual bounded material convolution in alias space

The Fourier coefficients of `cos(πx₁)+2cos(πx₂)+4cos(πx₃)` produce the
six shifts below, with coefficients `1/2`, `1`, and `2`. Their sum is a
bounded self-adjoint operator of norm at most seven. Adding this operator
leaves the actual maximal free-fiber domain unchanged.
-/

noncomputable section

namespace Maxwell.Continuum.FreeFiber

open scoped InnerProductSpace

/-- Reindexing a Hilbert sum by an actual index equivalence. -/
def hilbertReindex {ι κ E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : ι ≃ κ) : HilbertSum κ E ≃ₗᵢ[ℂ] HilbertSum ι E where
  toFun u := ⟨fun i => u (e i), by
    apply memℓp_gen
    exact e.summable_iff.mpr ((lp.memℓp u).summable (by norm_num))⟩
  invFun u := ⟨fun i => u (e.symm i), by
    apply memℓp_gen
    exact e.symm.summable_iff.mpr ((lp.memℓp u).summable (by norm_num))⟩
  left_inv u := by apply Subtype.ext; funext i; simp
  right_inv u := by apply Subtype.ext; funext i; simp
  map_add' u v := by apply Subtype.ext; funext i; rfl
  map_smul' c u := by apply Subtype.ext; funext i; rfl
  norm_map' u := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.tsum_eq (fun i : κ => ‖u i‖ ^ (2 : ENNReal).toReal)

def aliasTranslation (a : Alias) : Alias ≃ Alias where
  toFun ν := ν + a
  invFun ν := ν - a
  left_inv ν := add_sub_cancel_right ν a
  right_inv ν := sub_add_cancel ν a

def shift (a : Alias) : FiberSpace →L[ℂ] FiberSpace :=
  (hilbertReindex (E := Polarization) (aliasTranslation a)).toLinearIsometry.toContinuousLinearMap

@[simp]
theorem shift_apply (a : Alias) (u : FiberSpace) (ν : Alias) : shift a u ν = u (ν + a) := rfl

theorem shift_norm (a : Alias) (u : FiberSpace) : ‖shift a u‖ = ‖u‖ :=
  (hilbertReindex (E := Polarization) (aliasTranslation a)).norm_map u

theorem shift_norm_le (a : Alias) : ‖shift a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  simp only [shift_norm, one_mul, le_refl]

theorem shift_inner (a : Alias) (u v : FiberSpace) :
    inner ℂ (shift a u) v = inner ℂ u (shift (-a) v) := by
  change inner ℂ ((hilbertReindex (E := Polarization) (aliasTranslation a)) u) v = _
  rw [LinearIsometryEquiv.inner_map_eq_flip]
  congr 1

def unitAlias (j : Fin 3) : Alias := Pi.single j 1

def potentialWeight (j : Fin 3) : ℝ := ![1 / 2, 1, 2] j

def potential : FiberSpace →L[ℂ] FiberSpace :=
  ∑ j : Fin 3, (potentialWeight j : ℂ) • (shift (unitAlias j) + shift (-unitAlias j))

/-- The literal six-neighbor stencil on every integer alias. -/
theorem potential_apply (u : FiberSpace) (ν : Alias) :
    potential u ν = ∑ j : Fin 3,
      (potentialWeight j : ℂ) • (u (ν + unitAlias j) + u (ν - unitAlias j)) := by
  simp only [potential, sum_apply, smul_apply,
    add_apply, lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
    Pi.smul_apply, lp.coeFn_add, Pi.add_apply, shift_apply, sub_eq_add_neg]

theorem potentialWeight_nonneg (j : Fin 3) : 0 ≤ potentialWeight j := by
  fin_cases j <;> norm_num [potentialWeight]

theorem potential_norm_le : ‖potential‖ ≤ 7 := by
  calc
    ‖potential‖ ≤ ∑ j : Fin 3,
        ‖(potentialWeight j : ℂ) • (shift (unitAlias j) + shift (-unitAlias j))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j : Fin 3, potentialWeight j * (1 + 1) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (potentialWeight_nonneg j)]
      exact mul_le_mul_of_nonneg_left
        ((norm_add_le _ _).trans (add_le_add (shift_norm_le _) (shift_norm_le _)))
        (potentialWeight_nonneg j)
    _ = 7 := by norm_num [Fin.sum_univ_succ, potentialWeight]

theorem potential_isSymmetric : potential.IsSymmetric := by
  intro u v
  change inner ℂ (potential u) v = inner ℂ u (potential v)
  simp only [potential, sum_apply, smul_apply,
    add_apply, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal, inner_add_left, inner_add_right]
  apply Finset.sum_congr rfl
  intro j _
  rw [shift_inner, shift_inner, neg_neg, add_comm]

theorem potential_selfAdjoint : IsSelfAdjoint potential :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr potential_isSymmetric

/-- The complete free-plus-material Bloch fiber on its actual maximal domain. -/
def materialFiber (q : Momentum) (E : ℂ) (ρ : ℝ) : FiberSpace →ₗ.[ℂ] FiberSpace :=
  FormPerturbation.addBounded (operator q E) (-(ρ : ℂ) • potential)

@[simp]
theorem materialFiber_domain (q : Momentum) (E : ℂ) (ρ : ℝ) :
    (materialFiber q E ρ).domain = (operator q E).domain := rfl

theorem materialFiber_apply (q : Momentum) (E : ℂ) (ρ : ℝ)
    (u : (materialFiber q E ρ).domain) :
    materialFiber q E ρ u = operator q E u - (ρ : ℂ) • potential u.val := by
  change operator q E u + (-(ρ : ℂ)) • potential u.val = _
  rw [neg_smul, sub_eq_add_neg]

/-- Real momentum and real dielectric amplitude give a self-adjoint full fiber. -/
theorem real_materialFiber_selfAdjoint (q : Fin 3 → ℝ) (E ρ : ℝ) :
    IsSelfAdjoint (materialFiber (realMomentum q) E ρ) := by
  apply FormPerturbation.addBounded_selfAdjoint _ _ (real_operator_selfAdjoint q E)
  intro u v
  change inner ℂ ((-(ρ : ℂ)) • potential u) v = inner ℂ u ((-(ρ : ℂ)) • potential v)
  rw [inner_smul_left, inner_smul_right, map_neg, Complex.conj_ofReal]
  exact congrArg (fun z : ℂ => -(ρ : ℂ) * z) (potential_isSymmetric u v)

end Maxwell.Continuum.FreeFiber
