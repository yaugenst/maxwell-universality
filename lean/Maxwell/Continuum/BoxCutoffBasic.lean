import Maxwell.Continuum.BoxIntervalCutoff
import Maxwell.Continuum.BoxModesCutoffTest

/-! The literal smooth real box cutoff and its compact Schwartz
representative. Its support stays one unit inside every face. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.BoxCutoff

open Set BoxModes

def value (N : Fin 3 → ℝ) (x : Space) : ℝ := ∏ j : Fin 3, interval (N j) (x j)

theorem value_nonneg (N : Fin 3 → ℝ) (x : Space) : 0 ≤ value N x :=
  Finset.prod_nonneg fun _ _ => interval_nonneg _ _

theorem value_le_one (N : Fin 3 → ℝ) (x : Space) : value N x ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => interval_nonneg _ _) (fun _ _ => interval_le_one _ _)

theorem value_one (N : Fin 3 → ℝ) {x : Space}
    (hx : ∀ j, 2 ≤ x j ∧ x j ≤ N j-2) : value N x = 1 :=
  Finset.prod_eq_one fun j _ => interval_one _ (hx j).1 (hx j).2

theorem value_zero_left (N : Fin 3 → ℝ) {x : Space} (j : Fin 3) (hx : x j ≤ 1) : value N x = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ j) (interval_zero_left _ hx)

theorem value_zero_right (N : Fin 3 → ℝ) {x : Space} (j : Fin 3) (hx : N j-1 ≤ x j) : value N x = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ j) (interval_zero_right _ hx)

theorem value_contDiff (N : Fin 3 → ℝ) : ContDiff ℝ (⊤ : ℕ∞) (value N) := by
  apply contDiff_prod
  intro j _
  exact (interval_contDiff (N j)).comp (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j : Space →L[ℝ] ℝ).contDiff

theorem value_tsupport (N : Fin 3 → ℝ) : tsupport (value N) ⊆ innerClosedBox N 1 := by
  apply closure_minimal ?_ (isCompact_innerClosedBox N 1).isClosed
  intro x hx j _
  constructor
  · by_contra h
    exact hx (value_zero_left N j (le_of_not_ge h))
  · by_contra h
    exact hx (value_zero_right N j (le_of_not_ge h))

theorem value_compact (N : Fin 3 → ℝ) : HasCompactSupport (value N) :=
  (isCompact_innerClosedBox N 1).of_isClosed_subset isClosed_closure (value_tsupport N)

def schwartz (N : Fin 3 → ℝ) : SchwartzMap Space ℂ :=
  ((value_compact N).comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (value_contDiff N))

theorem schwartz_apply (N : Fin 3 → ℝ) (x : Space) : schwartz N x = (value N x : ℂ) := rfl

theorem schwartz_compact (N : Fin 3 → ℝ) : HasCompactSupport (schwartz N) :=
  (value_compact N).comp_left Complex.ofReal_zero

theorem schwartz_tsupport (N : Fin 3 → ℝ) : tsupport (schwartz N) ⊆ innerClosedBox N 1 :=
  (tsupport_comp_subset Complex.ofReal_zero (value N)).trans (value_tsupport N)

theorem schwartz_interior (N : Fin 3 → ℝ) : tsupport (schwartz N) ⊆ boxDomain N :=
  (schwartz_tsupport N).trans (innerClosedBox_subset_openBox N (by norm_num))

theorem schwartz_norm (N : Fin 3 → ℝ) (x : Space) : ‖schwartz N x‖ ≤ 1 := by
  rw [schwartz_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (value_nonneg N x)]
  exact value_le_one N x

theorem schwartz_one (N : Fin 3 → ℝ) {x : Space}
    (hx : ∀ j, 2 ≤ x j ∧ x j ≤ N j-2) : schwartz N x = 1 := by
  rw [schwartz_apply, value_one N hx, Complex.ofReal_one]

#print axioms schwartz_interior

end Maxwell.Continuum.BoxCutoff
