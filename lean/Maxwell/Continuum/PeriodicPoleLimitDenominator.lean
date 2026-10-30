import Maxwell.Continuum.PeriodicShiftedCurvature
import Maxwell.Continuum.PeriodicPoleTransition

/-! The selected denominator along the actual contour approaching its
axial pole. At zero detuning there are no earlier zeros, and the only
zero on the limiting contour is the origin. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set

attribute [local irreducible] imaginaryPole dielectricBand imaginaryRise coordinateBand hessianEnergy

def axialPoleShift {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (s : ℝ) : Corner.Vec :=
  s • Pi.single j (imaginaryPole D hh j)

theorem shiftedMomentum_zero_single_smul (s x : ℝ) (j : Fin 3) :
    shiftedMomentum 0 (s • Pi.single j x) =
      (((s * x : ℝ) : ℂ) * Complex.I) • basisVector j := by
  funext k
  by_cases hkj : k = j
  · subst k
    simp [shiftedMomentum, realMomentum, basisVector, mul_comm]
  · simp [shiftedMomentum, realMomentum, basisVector, hkj]

theorem axialPoleShift_energy {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    hessianEnergy (axialPoleShift D hh j s) ≤ 4 * h^2 :=
  (hessianEnergy_segment_le _ hs).trans (imaginaryPole_hessianEnergy D hh j)

theorem axialPoleShift_small {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖realMomentum (axialPoleShift D hh j s)‖ ≤ smallRadius :=
  (wide_tube_shift_norm_le D.h_pos.le _ (axialPoleShift_energy D hh j hs)).trans
    (twice_inverse_scale_le_smallRadius hh)

theorem pole_path_real_difference {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (s : ℝ) :
    (dielectricBand (shiftedMomentum 0 (axialPoleShift D hh j s))).re - z =
      imaginaryRise j (imaginaryPole D hh j) - imaginaryRise j (s * imaginaryPole D hh j) := by
  have hr : (coordinateBand j (((imaginaryPole D hh j : ℝ) : ℂ) * Complex.I)).re = z := by
    simpa only [coordinateBand, Complex.ofReal_re] using
      congrArg Complex.re (imaginaryPole_equation D hh j)
  rw [axialPoleShift, shiftedMomentum_zero_single_smul]
  unfold imaginaryRise
  rw [hr]
  unfold coordinateBand
  ring

theorem pole_path_axial_nonneg {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    0 ≤ (dielectricBand (shiftedMomentum 0 (axialPoleShift D hh j s))).re - z := by
  rw [pole_path_real_difference]
  have hp := imaginaryPole_mem_small D hh j
  have hsp : s * imaginaryPole D hh j ≤ imaginaryPole D hh j := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs.2 hp.1
  have hm := (imaginaryRise_strictMonoOn D.h_pos hh j).monotoneOn
    (show s * imaginaryPole D hh j ∈ Icc (0 : ℝ) (2*h) from
      ⟨mul_nonneg hs.1 hp.1, hsp.trans hp.2⟩) hp hsp
  exact sub_nonneg.mpr hm

theorem pole_path_axial_pos {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    0 < (dielectricBand (shiftedMomentum 0 (axialPoleShift D hh j s))).re - z := by
  rw [pole_path_real_difference]
  have hp := imaginaryPole_mem_small D hh j
  have hsp : s * imaginaryPole D hh j < imaginaryPole D hh j := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right hs.2 (imaginaryPole_pos D hh j)
  have hm := imaginaryRise_strictMonoOn D.h_pos hh j
    (show s * imaginaryPole D hh j ∈ Icc (0 : ℝ) (2*h) from
      ⟨mul_nonneg hs.1 hp.1, hsp.le.trans hp.2⟩) hp hsp
  exact sub_pos.mpr hm

theorem pole_path_denominator_lower {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) :
    hessianEnergy q / 2 ≤
      (dielectricBand (shiftedMomentum q (axialPoleShift D hh j s)) - (z : ℂ)).re := by
  have hc := shifted_band_curvature_lower q _ hq (axialPoleShift_small D hh j hs)
  have ha := pole_path_axial_nonneg D hh j hs
  simp only [Complex.sub_re, Complex.ofReal_re]
  linarith

theorem hessianEnergy_pos {q : Corner.Vec} (hq : q ≠ 0) : 0 < hessianEnergy q := by
  classical
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, q j ≠ 0 := by
    by_contra! hn
    exact hq (funext hn)
  rw [hessianEnergy_diagonal]
  exact (mul_pos (hessian_diagonal_positive j) (sq_pos_of_ne_zero hj)).trans_le
    (Finset.single_le_sum (fun k _ => mul_nonneg (hessian_diagonal_positive k).le (sq_nonneg _))
      (Finset.mem_univ j))

theorem pole_path_denominator_ne_zero {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) (hq0 : q ≠ 0) :
    dielectricBand (shiftedMomentum q (axialPoleShift D hh j s)) - (z : ℂ) ≠ 0 := by
  intro he
  have hl := pole_path_denominator_lower D hh j hs q hq
  rw [he, Complex.zero_re] at hl
  linarith [hessianEnergy_pos hq0]

theorem pole_path_denominator_ne_zero_before {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) :
    dielectricBand (shiftedMomentum q (axialPoleShift D hh j s)) - (z : ℂ) ≠ 0 := by
  intro he
  have hc := shifted_band_curvature_lower q _ hq (axialPoleShift_small D hh j ⟨hs.1, hs.2.le⟩)
  have ha := pole_path_axial_pos D hh j hs
  have hz := congrArg Complex.re he
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hz
  linarith [hessianEnergy_nonneg q]

theorem pole_limit_zero_iff {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) :
    dielectricBand (shiftedMomentum q (axialPoleShift D hh j 1)) - (z : ℂ) = 0 ↔ q = 0 := by
  constructor
  · intro he
    by_contra hq0
    exact pole_path_denominator_ne_zero D hh j (by constructor <;> norm_num) q hq hq0 he
  · intro he
    subst q
    rw [axialPoleShift, shiftedMomentum_zero_single_smul, one_mul, imaginaryPole_equation, sub_self]

end Maxwell.Continuum.PeriodicBand
