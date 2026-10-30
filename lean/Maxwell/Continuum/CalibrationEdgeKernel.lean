import Maxwell.Continuum.CalibrationEdgeHigh
import Maxwell.Continuum.CalibrationKernel
import Maxwell.Continuum.PeriodicBandSlices

/-! The actual periodic band supplies the top zero of the full 24-coordinate
calibration Schur complement. The negative complement is proved, not assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration

open FreeFiber PeriodicBand CornerBridge
open scoped InnerProductSpace

def edgeScaled : ℝ := (scaledBand 0).re

theorem edgeScaled_complex : (edgeScaled : ℂ) = scaledBand 0 := by
  have hzero : realMomentum (0 : Fin 3 → ℝ) = 0 := by
    funext j
    simp only [realMomentum, Pi.zero_apply, Complex.ofReal_zero]
  have hi := scaledBand_real (0 : Fin 3 → ℝ) (by rw [hzero]; exact chart_zero)
  rw [hzero] at hi
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using hi.symm

theorem edgeScaled_abs : |edgeScaled| ≤ 8 := by
  have h := (Complex.abs_re_le_norm (scaledBand 0)).trans (scaledBand_norm_le chart_zero)
  change |edgeScaled| ≤ 3 at h
  exact h.trans (by norm_num)

theorem edgeScaled_window : |edgeScaled-Corner.lambdaStar| ≤ 1/100 := by
  have h := (Complex.abs_re_le_norm (scaledBand 0-(Corner.lambdaStar : ℂ))).trans
    (scaledBand_center_bound chart_zero)
  simp only [Complex.sub_re, Complex.ofReal_re] at h
  exact h.trans (by norm_num)

theorem edgeSchur_kernel : ∃ w : centralSpace, w ≠ 0 ∧
    calibrationFiniteSchur 0 edgeScaled edgeParameterBound (edgeEnergyBound edgeScaled_abs) w = 0 := by
  obtain ⟨f, hf, hgraph⟩ := actual_band_eigenvector chart_zero
  rw [← edgeScaled_complex, LinearPMap.mem_graph_iff] at hgraph
  obtain ⟨u, hu, hAu⟩ := hgraph
  dsimp only at hu hAu
  have hu0 : u.val ≠ 0 := by rwa [hu]
  let w := centralProjectionToSpace u.val
  have hw0 : w ≠ 0 := by
    intro hw
    have hp : centralAliasProjection u.val = 0 := congrArg Subtype.val hw
    have hr := calibration_kernel_reconstruction 0 (edgeScaled : ℂ) edgeParameterBound
      (edgeEnergyBound edgeScaled_abs) u hAu
    rw [← calibrationLift_central_input 0 (edgeScaled : ℂ) edgeParameterBound
      (edgeEnergyBound edgeScaled_abs) u.val, hp, map_zero] at hr
    exact hu0 hr
  refine ⟨w, hw0, ?_⟩
  apply Subtype.ext
  exact calibration_kernel_projects 0 (edgeScaled : ℂ) edgeParameterBound
    (edgeEnergyBound edgeScaled_abs) u hAu

private theorem quadratic_nonpositive_of_gap_kernel
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →L[ℂ] H) (hA : A.IsSymmetric) (l : H →ₗ[ℂ] ℂ)
    (c : ℝ) (hc : 0 < c)
    (hgap : ∀ x : H, l x = 0 → (inner ℂ x (A x)).re ≤ -c*‖x‖^2)
    (w : H) (hw : w ≠ 0) (hAw : A w = 0) (x : H) :
    (inner ℂ x (A x)).re ≤ 0 := by
  have hlw : l w ≠ 0 := by
    intro hl
    have h := hgap w hl
    rw [hAw, inner_zero_right, Complex.zero_re] at h
    have hn : 0 < ‖w‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hw)
    nlinarith only [h, mul_pos hc hn]
  let a := l x / l w
  let y := x-a • w
  have hly : l y = 0 := by
    change l (x-a • w) = 0
    rw [map_sub, map_smul]
    change l x - (l x / l w)*l w = 0
    rw [div_mul_cancel₀ _ hlw, sub_self]
  have hAy : A y = A x := by
    change A (x-a • w) = _
    rw [map_sub, map_smul, hAw, smul_zero, sub_zero]
  have hwx : inner ℂ w (A x) = 0 := by
    have hsym := hA w x
    change inner ℂ (A w) x = inner ℂ w (A x) at hsym
    rw [← hsym, hAw, inner_zero_left]
  have hform : inner ℂ y (A y) = inner ℂ x (A x) := by
    rw [hAy]
    change inner ℂ (x-a • w) (A x) = _
    rw [inner_sub_left, inner_smul_left, hwx, mul_zero, sub_zero]
  have hg := hgap y hly
  rw [hform] at hg
  exact hg.trans (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (sq_nonneg ‖y‖))

theorem edgeSchur_at_edge_nonpositive (u : centralSpace) :
    (inner ℂ u
      (calibrationFiniteSchur 0 edgeScaled edgeParameterBound (edgeEnergyBound edgeScaled_abs) u)).re ≤ 0 := by
  obtain ⟨w, hw, hAw⟩ := edgeSchur_kernel
  let l : centralSpace →ₗ[ℂ] ℂ :=
    (innerSL ℂ topState.val).toLinearMap.comp centralSpace.subtype
  apply quadratic_nonpositive_of_gap_kernel _ (edgeSchur_isSymmetric edgeScaled edgeScaled_abs)
    l (backgroundAmplitude/100) (div_pos backgroundAmplitude_pos (by norm_num)) ?_ w hw hAw u
  intro x hx
  have h := edgeSchur_top_high edgeScaled edgeScaled_abs edgeScaled_window x hx
  simpa only [neg_div] using h

#print axioms edgeSchur_kernel
#print axioms edgeSchur_at_edge_nonpositive

end Maxwell.Continuum.Calibration
