import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! Norm preservation under iterated differentiation and quantitative
evaluation of higher derivatives in fixed directions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_iterated (f : E → F) (m j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ m (iteratedFDeriv ℝ j f) x‖ = ‖iteratedFDeriv ℝ (m+j) f x‖ := by
  induction j generalizing m with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, Nat.add_zero]
  | succ j ih =>
    rw [iteratedFDeriv_succ_eq_comp_left]
    have he := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => E) F).symm
      |>.norm_iteratedFDeriv_comp_left (fderiv ℝ (iteratedFDeriv ℝ j f)) x m
    rw [he, norm_iteratedFDeriv_fderiv, ih]
    congr 1
    omega

theorem multilinearEvaluation_norm (j : ℕ) (v : Fin j → E) :
    ‖ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => E) F v‖ ≤ ∏ i, ‖v i‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro A
  exact (A.le_opNorm v).trans_eq (mul_comm _ _)

theorem norm_iteratedFDeriv_evaluation (f : E → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (m j : ℕ) (x : E) (v : Fin j → E) :
    ‖iteratedFDeriv ℝ m (fun y => iteratedFDeriv ℝ j f y v) x‖ ≤
      (∏ i, ‖v i‖) * ‖iteratedFDeriv ℝ (m+j) f x‖ := by
  let A := ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => E) F v
  have hd : ContDiff ℝ (⊤ : ℕ∞) (iteratedFDeriv ℝ j f) :=
    hf.iteratedFDeriv_right (by exact_mod_cast (show (⊤ : ℕ∞)+j ≤ ⊤ from le_top))
  have he := A.norm_iteratedFDeriv_comp_left (hd.contDiffAt (x := x)) (n := m) (by simp)
  change ‖iteratedFDeriv ℝ m (fun y => iteratedFDeriv ℝ j f y v) x‖ ≤
    ‖A‖*‖iteratedFDeriv ℝ m (iteratedFDeriv ℝ j f) x‖ at he
  rw [norm_iteratedFDeriv_iterated] at he
  exact he.trans (mul_le_mul_of_nonneg_right (multilinearEvaluation_norm j v) (norm_nonneg _))

#print axioms norm_iteratedFDeriv_evaluation

end Maxwell.Continuum
