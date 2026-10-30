import Maxwell.Continuum.BoxCutoffFrechet

/-! The concrete Schwartz cutoff satisfies the coordinate derivative
bounds needed in the physical curl-curl commutator. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.BoxCutoff

open LineDeriv
open scoped SchwartzMap

theorem schwartz_frechet_norm (N : Fin 3 → ℝ) (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (schwartz N) x‖ = ‖iteratedFDeriv ℝ n (value N) x‖ :=
  Complex.ofRealLI.norm_iteratedFDeriv_comp_left (value_contDiff N).contDiffAt (by simp)

theorem coordinateDirection_norm (j : Fin 3) : ‖coordinateDirection j‖ = 1 := by
  simp only [coordinateDirection, PiLp.norm_single, norm_one]

theorem partialSchwartz_norm_le (θ : SchwartzMap Space ℂ) (j : Fin 3) (x : Space) :
    ‖partialSchwartz j θ x‖ ≤ ‖iteratedFDeriv ℝ 1 θ x‖ := by
  change ‖fderiv ℝ θ x (coordinateDirection j)‖ ≤ _
  rw [norm_iteratedFDeriv_one]
  simpa only [coordinateDirection_norm, mul_one] using (fderiv ℝ θ x).le_opNorm (coordinateDirection j)

theorem second_partialSchwartz_norm_le (θ : SchwartzMap Space ℂ) (j k : Fin 3) (x : Space) :
    ‖partialSchwartz j (partialSchwartz k θ) x‖ ≤ ‖iteratedFDeriv ℝ 2 θ x‖ := by
  let m : Fin 2 → Space := ![coordinateDirection j, coordinateDirection k]
  have he : partialSchwartz j (partialSchwartz k θ) x = iteratedFDeriv ℝ 2 θ x m := by
    rw [← SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
    rfl
  rw [he]
  have h := (iteratedFDeriv ℝ 2 θ x).le_opNorm m
  simpa only [Fin.prod_univ_two, m, Matrix.cons_val_zero, Matrix.cons_val_one,
    coordinateDirection_norm, one_mul, mul_one] using h

theorem schwartz_first (N : Fin 3 → ℝ) (j : Fin 3) (x : Space) :
    ‖partialSchwartz j (schwartz N) x‖ ≤ 96 :=
  (partialSchwartz_norm_le _ j x).trans
    ((schwartz_frechet_norm N 1 x).le.trans (value_frechet_bounds N x).1)

theorem schwartz_second (N : Fin 3 → ℝ) (j k : Fin 3) (x : Space) :
    ‖partialSchwartz j (partialSchwartz k (schwartz N)) x‖ ≤ 84480 :=
  (second_partialSchwartz_norm_le _ j k x).trans
    ((schwartz_frechet_norm N 2 x).le.trans (value_frechet_bounds N x).2)

theorem schwartz_commutator_coefficients (N : Fin 3 → ℝ) :
    (∀ j x, ‖partialSchwartz j (schwartz N) x‖ ≤ (2 : ℝ)^19) ∧
    (∀ j k x, ‖partialSchwartz j (partialSchwartz k (schwartz N)) x‖ ≤ (2 : ℝ)^19) :=
  ⟨fun j x => (schwartz_first N j x).trans (by norm_num),
    fun j k x => (schwartz_second N j k x).trans (by norm_num)⟩

#print axioms schwartz_commutator_coefficients

end Maxwell.Continuum.BoxCutoff
