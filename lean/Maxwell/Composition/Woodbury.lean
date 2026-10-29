import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Full-operator Woodbury composition

The hypotheses are invertibility of the background and mediator diagonal, and
invertibility of the *small* Schur core. The full operator's invertibility and
operator-norm bound are conclusions. The spaces may be finite dimensional, but
no choice of coordinate norm or matrix-to-operator conversion is hidden here.
-/

namespace Maxwell.Composition

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The full physical operator after a finite mediator coupling. -/
def coupledOperator (A : E ≃L[𝕜] E) (D : F ≃L[𝕜] F)
    (U : F →L[𝕜] E) (V : E →L[𝕜] F) : E →L[𝕜] E :=
  (A : E →L[𝕜] E) - U.comp ((D.symm : F →L[𝕜] F).comp V)

/-- The small core whose local invertibility suffices for the full problem. -/
def woodburyCore (A : E ≃L[𝕜] E) (D : F ≃L[𝕜] F)
    (U : F →L[𝕜] E) (V : E →L[𝕜] F) : F →L[𝕜] F :=
  (D : F →L[𝕜] F) - V.comp ((A.symm : E →L[𝕜] E).comp U)

/-- Explicit full inverse, composed only from the two local inverses. -/
def woodburyInverse (A : E ≃L[𝕜] E) (S : F ≃L[𝕜] F)
    (U : F →L[𝕜] E) (V : E →L[𝕜] F) : E →L[𝕜] E :=
  (A.symm : E →L[𝕜] E) + (A.symm : E →L[𝕜] E).comp
    (U.comp ((S.symm : F →L[𝕜] F).comp (V.comp (A.symm : E →L[𝕜] E))))

/-- The full operator times the explicit Woodbury expression is the identity. -/
theorem coupled_comp_woodbury (A : E ≃L[𝕜] E) (D S : F ≃L[𝕜] F)
    (U : F →L[𝕜] E) (V : E →L[𝕜] F)
    (hS : (S : F →L[𝕜] F) = woodburyCore A D U V) :
    (coupledOperator A D U V).comp (woodburyInverse A S U V) =
      ContinuousLinearMap.id 𝕜 E := by
  ext x
  have hcore : D (S.symm (V (A.symm x))) -
      V (A.symm (U (S.symm (V (A.symm x))))) = V (A.symm x) := by
    have h := congrArg (fun T : F →L[𝕜] F => T (S.symm (V (A.symm x)))) hS
    simpa [woodburyCore] using h.symm
  have hcancel := congrArg (fun y => U (D.symm y)) hcore
  simp only [map_sub, ContinuousLinearEquiv.symm_apply_apply] at hcancel
  simp only [coupledOperator, woodburyInverse, ContinuousLinearMap.comp_apply,
    sub_apply, add_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.id_apply, map_add,
    ContinuousLinearEquiv.apply_symm_apply]
  rw [hcancel]
  abel

/-- The explicit Woodbury expression times the full operator is the identity. -/
theorem woodbury_comp_coupled (A : E ≃L[𝕜] E) (D S : F ≃L[𝕜] F)
    (U : F →L[𝕜] E) (V : E →L[𝕜] F)
    (hS : (S : F →L[𝕜] F) = woodburyCore A D U V) :
    (woodburyInverse A S U V).comp (coupledOperator A D U V) =
      ContinuousLinearMap.id 𝕜 E := by
  ext x
  have hcore : S (D.symm (V x)) =
      V x - V (A.symm (U (D.symm (V x)))) := by
    have h := congrArg (fun T : F →L[𝕜] F => T (D.symm (V x))) hS
    simpa [woodburyCore] using h
  simp only [coupledOperator, woodburyInverse, ContinuousLinearMap.comp_apply,
    sub_apply, add_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.id_apply, map_sub,
    ContinuousLinearEquiv.symm_apply_apply]
  have hcancel := congrArg (fun y => A.symm (U (S.symm y))) hcore
  simp only [map_sub, ContinuousLinearEquiv.symm_apply_apply] at hcancel
  have cancel (p q r : E) (h : q = p - r) : x + p - (q + r) = x := by
    rw [h]
    abel
  exact cancel _ _ _ hcancel

/-- Full invertibility is constructed, rather than assumed. -/
def woodburyEquiv (A : E ≃L[𝕜] E) (D S : F ≃L[𝕜] F)
    (U : F →L[𝕜] E) (V : E →L[𝕜] F)
    (hS : (S : F →L[𝕜] F) = woodburyCore A D U V) : E ≃L[𝕜] E :=
  ContinuousLinearEquiv.equivOfInverse' (coupledOperator A D U V)
    (woodburyInverse A S U V) (coupled_comp_woodbury A D S U V hS)
    (woodbury_comp_coupled A D S U V hS)

@[simp] theorem woodburyEquiv_toContinuousLinearMap
    (A : E ≃L[𝕜] E) (D S : F ≃L[𝕜] F)
    (U : F →L[𝕜] E) (V : E →L[𝕜] F)
    (hS : (S : F →L[𝕜] F) = woodburyCore A D U V) :
    (woodburyEquiv A D S U V hS : E →L[𝕜] E) = coupledOperator A D U V := rfl

/-- The inverse of the full equivalence has the explicit Woodbury formula. -/
@[simp] theorem woodburyEquiv_symm_toContinuousLinearMap
    (A : E ≃L[𝕜] E) (D S : F ≃L[𝕜] F)
    (U : F →L[𝕜] E) (V : E →L[𝕜] F)
    (hS : (S : F →L[𝕜] F) = woodburyCore A D U V) :
    ((woodburyEquiv A D S U V hS).symm : E →L[𝕜] E) =
      woodburyInverse A S U V := rfl

/-- Quantitative operator-norm control on the constructed full inverse. -/
theorem woodbury_full_inverse_norm_le (A : E ≃L[𝕜] E) (D S : F ≃L[𝕜] F)
    (U : F →L[𝕜] E) (V : E →L[𝕜] F)
    (hS : (S : F →L[𝕜] F) = woodburyCore A D U V) :
    ‖((woodburyEquiv A D S U V hS).symm : E →L[𝕜] E)‖ ≤
      ‖(A.symm : E →L[𝕜] E)‖ + ‖(A.symm : E →L[𝕜] E)‖ ^ 2 *
        ‖U‖ * ‖(S.symm : F →L[𝕜] F)‖ * ‖V‖ := by
  rw [woodburyEquiv_symm_toContinuousLinearMap, woodburyInverse]
  refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
  calc
    _ ≤ ‖(A.symm : E →L[𝕜] E)‖ * ‖U.comp
        ((S.symm : F →L[𝕜] F).comp (V.comp (A.symm : E →L[𝕜] E)))‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖(A.symm : E →L[𝕜] E)‖ * (‖U‖ *
        ‖(S.symm : F →L[𝕜] F).comp (V.comp (A.symm : E →L[𝕜] E))‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ ‖(A.symm : E →L[𝕜] E)‖ * (‖U‖ *
        (‖(S.symm : F →L[𝕜] F)‖ * ‖V.comp (A.symm : E →L[𝕜] E)‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
        (norm_nonneg _)
    _ ≤ ‖(A.symm : E →L[𝕜] E)‖ * (‖U‖ *
        (‖(S.symm : F →L[𝕜] F)‖ * (‖V‖ * ‖(A.symm : E →L[𝕜] E)‖))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
          (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

/-- The physical full-inverse bound, for contractive weighted insertion and
restriction and a certified small-core inverse. No factor depending on the
number of defects or full-space dimension is introduced. -/
theorem physical_full_inverse_norm_le
    (A : E ≃L[𝕜] E) (D S : F ≃L[𝕜] F)
    (U : F →L[𝕜] E) (V : E →L[𝕜] F)
    (hS : (S : F →L[𝕜] F) = woodburyCore A D U V)
    (L QM : ℝ) (hA : ‖(A.symm : E →L[𝕜] E)‖ ≤ L)
    (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1)
    (hcore : ‖(S.symm : F →L[𝕜] F)‖ ≤ QM) :
    ‖((woodburyEquiv A D S U V hS).symm : E →L[𝕜] E)‖ ≤ L + L ^ 2 * QM := by
  have hL : 0 ≤ L := (norm_nonneg _).trans hA
  have hQM : 0 ≤ QM := (norm_nonneg _).trans hcore
  calc
    _ ≤ ‖(A.symm : E →L[𝕜] E)‖ + ‖(A.symm : E →L[𝕜] E)‖ ^ 2 *
        ‖U‖ * ‖(S.symm : F →L[𝕜] F)‖ * ‖V‖ :=
      woodbury_full_inverse_norm_le A D S U V hS
    _ ≤ L + L ^ 2 * 1 * QM * 1 := by gcongr
    _ = L + L ^ 2 * QM := by ring

section Perturbation

variable [CompleteSpace E]

/-- A norm-small physical perturbation preserves invertibility. The inverse is
constructed from a convergent Neumann series in the operator algebra. -/
noncomputable def perturbationEquiv (A : E ≃L[𝕜] E) (Δ : E →L[𝕜] E)
    (hsmall : ‖(A.symm : E →L[𝕜] E)‖ * ‖Δ‖ < 1) : E ≃L[𝕜] E :=
  ContinuousLinearEquiv.ofUnit (A.toUnit * Units.oneSub
    (-((A.symm : E →L[𝕜] E) * Δ)) (by
      rw [norm_neg]
      exact (norm_mul_le _ _).trans_lt hsmall))

@[simp] theorem perturbationEquiv_toContinuousLinearMap
    (A : E ≃L[𝕜] E) (Δ : E →L[𝕜] E)
    (hsmall : ‖(A.symm : E →L[𝕜] E)‖ * ‖Δ‖ < 1) :
    (perturbationEquiv A Δ hsmall : E →L[𝕜] E) = (A : E →L[𝕜] E) + Δ := by
  ext x
  simp [perturbationEquiv, ContinuousLinearEquiv.ofUnit, ContinuousLinearEquiv.toUnit,
    Units.oneSub, sub_eq_add_neg]

/-- The perturbation estimate bounds the inverse of the actual full operator,
including its perturbation, in the continuous-operator norm. -/
theorem perturbation_full_inverse_norm_le
    (A : E ≃L[𝕜] E) (Δ : E →L[𝕜] E)
    (hsmall : ‖(A.symm : E →L[𝕜] E)‖ * ‖Δ‖ < 1) :
    ‖((perturbationEquiv A Δ hsmall).symm : E →L[𝕜] E)‖ ≤
      ‖(A.symm : E →L[𝕜] E)‖ / (1 - ‖(A.symm : E →L[𝕜] E)‖ * ‖Δ‖) := by
  have hden : 0 < 1 - ‖(A.symm : E →L[𝕜] E)‖ * ‖Δ‖ := sub_pos.mpr hsmall
  apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (norm_nonneg _) hden.le)
  intro x
  let y := (perturbationEquiv A Δ hsmall).symm x
  have heq : A y + Δ y = x := by
    change ((A : E →L[𝕜] E) + Δ) y = x
    rw [← perturbationEquiv_toContinuousLinearMap A Δ hsmall]
    exact (perturbationEquiv A Δ hsmall).apply_symm_apply x
  have hy : y = A.symm x - A.symm (Δ y) := by
    apply eq_sub_iff_add_eq.mpr
    simpa only [map_add, ContinuousLinearEquiv.symm_apply_apply] using
      congrArg A.symm heq
  have hnorm : ‖y‖ ≤ ‖(A.symm : E →L[𝕜] E)‖ * ‖x‖ +
      ‖(A.symm : E →L[𝕜] E)‖ * ‖Δ‖ * ‖y‖ := by
    calc
      ‖y‖ = ‖A.symm x - A.symm (Δ y)‖ := congrArg norm hy
      _ ≤ ‖A.symm x‖ + ‖A.symm (Δ y)‖ := norm_sub_le _ _
      _ ≤ ‖(A.symm : E →L[𝕜] E)‖ * ‖x‖ +
          ‖(A.symm : E →L[𝕜] E)‖ * ‖Δ y‖ :=
        add_le_add ((A.symm : E →L[𝕜] E).le_opNorm x)
          ((A.symm : E →L[𝕜] E).le_opNorm (Δ y))
      _ ≤ ‖(A.symm : E →L[𝕜] E)‖ * ‖x‖ +
          ‖(A.symm : E →L[𝕜] E)‖ * ‖Δ‖ * ‖y‖ := by
        rw [mul_assoc]
        exact add_le_add_right
          (mul_le_mul_of_nonneg_left (Δ.le_opNorm y) (norm_nonneg _)) _
  change ‖y‖ ≤ _
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hden).mpr
  nlinarith only [hnorm]

end Perturbation

end Maxwell.Composition
