import Maxwell.Continuum.PeriodicPoleContourGeometry
import Maxwell.Continuum.AlmostAnalyticCutoffLedger
import Maxwell.Continuum.OperatorGevrey

/-! Uniform first-order-through-thirty-two directional derivatives of
the literal shifted cutoff after the physical rescaling q=h k. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary AlmostAnalytic OperatorFourier

def scaledPoleCutoff {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space) : ℂ :=
  cutoffTaylor (cutoffOrder (poleContourShift D hh j)) smallRadius
    (h • k) (poleContourShift D hh j) 1

theorem scaledPoleCutoff_contDiff {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (scaledPoleCutoff D hh j) := by
  apply (cutoffTaylor_contDiff _ _ _).comp
  exact (h • ContinuousLinearMap.id ℝ Space).contDiff

theorem line_iteratedDeriv_norm_le {F : Space → ℂ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (k v : Space) (hv : ‖v‖ ≤ 1) (n : ℕ) :
    ‖iteratedDeriv n (fun t : ℝ => F (k+t • v)) 0‖ ≤ ‖iteratedFDeriv ℝ n F k‖ := by
  rw [← directionalDerivative_eq_line n F hF k v]
  apply ((iteratedFDeriv ℝ n F k).le_opNorm (fun _ => v)).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hv)

theorem scaledPoleCutoff_derivative {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k v : Space)
    (hv : ‖v‖ ≤ 1) {n : ℕ} (hn : n ≤ 32) :
    ‖iteratedDeriv n (fun t : ℝ => scaledPoleCutoff D hh j (k+t • v)) 0‖ ≤ (2 : ℝ)^5261 := by
  have hh1 : h ≤ 1 := hh.trans (div_le_self (by norm_num) (one_le_pow₀ (by norm_num)))
  have hw : ‖h • v‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos D.h_pos]
    exact (mul_le_mul_of_nonneg_left hv D.h_pos.le).trans (by simpa only [mul_one] using hh1)
  have he : (fun t : ℝ => scaledPoleCutoff D hh j (k+t • v)) =
      (fun t : ℝ => cutoffTaylor (cutoffOrder (poleContourShift D hh j)) smallRadius
        (h • k+t • (h • v)) (poleContourShift D hh j) 1) := by
    funext t
    unfold scaledPoleCutoff
    congr 1
    simp only [smul_add, smul_smul]
    rw [mul_comm h t]
  rw [he]
  exact (line_iteratedDeriv_norm_le (cutoffTaylor_contDiff _ _ _)
    (h • k) (h • v) hw n).trans
    (cutoffTaylor_frechet_32_le (poleContourShift_ne_zero D hh j) hn (h • k) (by norm_num))

end Maxwell.Continuum.PeriodicBand
