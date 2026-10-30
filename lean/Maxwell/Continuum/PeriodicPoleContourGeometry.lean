import Maxwell.Continuum.PeriodicPoleLimitIntegral
import Maxwell.Continuum.PeriodicTubeLattice

/-! Geometric joins for the limiting pole contour: its actual size,
the fixed transition-shell bound, and the phase in a placement-lattice
coordinate direction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary AlmostAnalytic CellGauge Set MeasureTheory
open scoped Topology

attribute [local irreducible] imaginaryPole fullCellSymbol

theorem poleContourShift_norm {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    ‖poleContourShift D hh j‖ = imaginaryPole D hh j := by
  change ‖(PiLp.single 2 j (imaginaryPole D hh j) : Space)‖ = _
  rw [PiLp.norm_single, Real.norm_eq_abs, abs_of_pos (imaginaryPole_pos D hh j)]

theorem poleContourShift_norm_le {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) : ‖poleContourShift D hh j‖ ≤ h := by
  rw [poleContourShift_norm]
  exact imaginaryPole_le_inverse_scale D hh j

theorem poleContour_transition_bound {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (q : Space) (hq0 : smallRadius ≤ ‖q‖) (hq : ‖q‖ ≤ 4*smallRadius) :
    ‖fullCellSymbol z 0 (AlmostAnalytic.shiftedMomentum q (poleContourShift D hh j) s)‖ ≤
      (2 : ℝ)^196 := by
  rw [poleContourShift_momentum]
  exact imaginaryPole_transition_cell_norm_le D hh le_rfl (by positivity)
    j q.ofLp hq0 (poleContour_chart hq) hs

def poleAxialDisplacement (h d : ℝ) (j : Fin 3) : Space :=
  PiLp.single 2 j (2*h⁻¹*d*(placementDiagonal j : ℝ))

theorem poleAxialDisplacement_eq_placed (h d : ℝ) (j : Fin 3) :
    poleAxialDisplacement h d j =
      WithLp.toLp 2 (placedDisplacement h⁻¹ d (PiLp.single 2 j (1 : ℝ))) := by
  apply PiLp.ext
  intro k
  change (Pi.single j (2*h⁻¹*d*(placementDiagonal j : ℝ)) : Corner.Vec) k =
    placedDisplacement h⁻¹ d (PiLp.single 2 j (1 : ℝ)) k
  simp only [placedDisplacement, realPlacementMatrix, Matrix.mulVec_diagonal,
    Pi.smul_apply, smul_eq_mul, PiLp.single_apply, Pi.single_apply]
  split_ifs with hkj
  · subst k
    ring
  · ring

theorem poleContourShift_axial_phase {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (d : ℝ) :
    inner ℝ (poleContourShift D hh j) (poleAxialDisplacement h d j) =
      poleAction D hh j*d := by
  change inner ℝ (PiLp.single 2 j (imaginaryPole D hh j) : Space)
    (PiLp.single 2 j (2*h⁻¹*d*(placementDiagonal j : ℝ)) : Space) = _
  rw [EuclideanSpace.inner_single_left]
  simp only [starRingEnd_apply, star_trivial, PiLp.single_apply, ↓reduceIte]
  unfold poleAction
  ring

theorem poleContourShift_axial_phase_nonneg {h z d : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (hd : 0 ≤ d) :
    0 ≤ inner ℝ (poleContourShift D hh j) (poleAxialDisplacement h d j) := by
  rw [poleContourShift_axial_phase]
  exact mul_nonneg (poleAction_pos D hh j).le hd

theorem poleAxial_integral_tendsto {h z d : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (hd : 0 ≤ d) :
    Filter.Tendsto (fun s : ℝ => ∫ q, poleContourIntegrand D hh j
      (poleAxialDisplacement h d j) s q) (𝓝[<] (1 : ℝ))
      (𝓝 (∫ q, poleContourIntegrand D hh j (poleAxialDisplacement h d j) 1 q)) :=
  poleContour_integral_tendsto D hh j _ (poleContourShift_axial_phase_nonneg D hh j hd)

end Maxwell.Continuum.PeriodicBand
