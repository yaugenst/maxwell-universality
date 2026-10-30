import Maxwell.Continuum.PeriodicPoleLocalMeasurable
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi

/-! The literal volume-preserving coordinate decomposition into the
two transverse coordinates and the chosen longitudinal coordinate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber MeasureTheory TransverseGaussian

def poleSpaceCoordinates (j : Fin 3) : Space ≃ᵐ Plane × ℝ :=
  (((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) j)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)))).trans MeasurableEquiv.prodComm

def poleCoordinateSpace (j : Fin 3) (x : Plane) (u : ℝ) : Space :=
  WithLp.toLp 2 (j.insertNth u x.ofLp)

theorem poleSpaceCoordinates_measurePreserving (j : Fin 3) :
    MeasurePreserving (poleSpaceCoordinates j) := by
  exact (((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).trans
    (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) j)).trans
      ((MeasurePreserving.id volume : MeasurePreserving (id : ℝ → ℝ)).prod
        (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).symm)).trans
          Measure.measurePreserving_swap

theorem poleSpaceCoordinates_symm_apply (j : Fin 3) (x : Plane) (u : ℝ) :
    (poleSpaceCoordinates j).symm (x,u) = poleCoordinateSpace j x u := rfl

@[simp] theorem poleCoordinateSpace_same (j : Fin 3) (x : Plane) (u : ℝ) :
    poleCoordinateSpace j x u j = u := by
  exact Fin.insertNth_apply_same (α := fun _ : Fin 3 => ℝ) j u x.ofLp

@[simp] theorem poleCoordinateSpace_other (j : Fin 3) (x : Plane) (u : ℝ) (k : Fin 2) :
    poleCoordinateSpace j x u (j.succAbove k) = x k := by
  exact Fin.insertNth_apply_succAbove (α := fun _ : Fin 3 => ℝ) j u x.ofLp k

theorem poleCoordinateSpace_norm_sq (j : Fin 3) (x : Plane) (u : ℝ) :
    ‖poleCoordinateSpace j x u‖^2 = ‖x‖^2+u^2 := by
  rw [EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_succAbove (fun k => (poleCoordinateSpace j x u k)^2) j]
  simp only [poleCoordinateSpace_same, poleCoordinateSpace_other]
  rw [EuclideanSpace.real_norm_sq_eq, add_comm]

theorem poleCoordinateSpace_realMomentum (j : Fin 3) (x : Plane) (u : ℝ) :
    realMomentum (poleCoordinateSpace j x u).ofLp = realPoleCoordinates j (x,u) := by
  ext k
  by_cases hk : k = j
  · subst k
    simp only [realMomentum, realPoleCoordinates, poleOffset_same, poleCoordinateSpace_same]
  · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hk
    simp only [realMomentum, realPoleCoordinates, poleOffset_other j _ (Fin.succAbove_ne _ _),
      poleCoordinateSpace_other, transverseMomentum_other]

theorem poleCoordinateSpace_cutoff (j : Fin 3) (x : Plane) (u : ℝ) :
    poleChartCutoff j (poleCoordinateSpace j x u) =
      scaledPsi poleLongitudinalScale u*poleTransverseCutoff x := by
  simp only [poleChartCutoff, poleLongitudinalCutoff, poleCoordinateSpace_same,
    poleCoordinateSpace_other, poleTransverseCutoff]

theorem poleSpace_integral (j : Fin 3) (f : Space → ℂ) (hf : Integrable f) :
    (∫q : Space, f q) = ∫x : Plane, ∫u : ℝ, f (poleCoordinateSpace j x u) := by
  have hm := (poleSpaceCoordinates_measurePreserving j).symm
  have hi : Integrable (fun y : Plane × ℝ => f ((poleSpaceCoordinates j).symm y)) :=
    hm.integrable_comp_of_integrable hf
  calc
    _ = ∫y : Plane × ℝ, f ((poleSpaceCoordinates j).symm y) := (hm.integral_comp' f).symm
    _ = ∫x : Plane, ∫u : ℝ, f ((poleSpaceCoordinates j).symm (x,u)) :=
      integral_prod _ hi
    _ = _ := by simp only [poleSpaceCoordinates_symm_apply]

#print axioms poleSpace_integral

end Maxwell.Continuum.PeriodicBand
