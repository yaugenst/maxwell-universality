import Maxwell.Continuum.CellSpatialTiling

/-! The paper's [0,2) convention and the torus's (0,2] convention
give exactly the same physical L² cell projections. -/

noncomputable section

namespace Maxwell.Continuum.CellGauge

open Bloch MeasureTheory Set

def paperBox (a : Bloch.Alias) : Set Space :=
  {x | ∀ j, 2 * (a j : ℝ) ≤ x j ∧ x j < 2 * (a j : ℝ) + 2}

theorem spatialBox_ae_paperBox (a : Bloch.Alias) :
    spatialBox a =ᵐ[(volume : Measure Space)] paperBox a := by
  let l : Fin 3 → ℝ := fun j => 2 * (a j : ℝ)
  let u : Fin 3 → ℝ := fun j => l j + 2
  have hi : (Set.pi Set.univ fun j => Ioc (l j) (u j)) =ᵐ[volume]
      (Set.pi Set.univ fun j => Ico (l j) (u j)) :=
    (Measure.pi_Ioc_ae_eq_pi_Icc (μ := fun _ : Fin 3 => (volume : Measure ℝ))).trans
      (Measure.pi_Ico_ae_eq_pi_Icc (μ := fun _ : Fin 3 => (volume : Measure ℝ))).symm
  have hp := (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp hi
  filter_upwards [hp] with x hx
  have hx' : (∀ j, 2 * (a j : ℝ) < x j ∧ x j ≤ 2 * (a j : ℝ) + 2) ↔
      (∀ j, 2 * (a j : ℝ) ≤ x j ∧ x j < 2 * (a j : ℝ) + 2) := by
    simpa only [Function.comp_apply, Set.mem_pi, Set.mem_univ, forall_true_left,
      Set.mem_Ioc, Set.mem_Ico, l, u] using Iff.of_eq hx
  exact propext ((spatialBox_mem a x).trans hx')

theorem cellProjection_paperBox_ae (a : Bloch.Alias) (f : FieldL2) (j : Fin 3) :
    cellProjection a f j =ᵐ[volume] (paperBox a).indicator (fun x => f j x) :=
  (cellProjection_ae a f j).trans (indicator_ae_eq_of_ae_eq_set (spatialBox_ae_paperBox a))

#print axioms cellProjection_paperBox_ae

end Maxwell.Continuum.CellGauge
