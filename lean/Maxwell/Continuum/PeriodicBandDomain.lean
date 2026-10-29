import Maxwell.Continuum.PeriodicPerturbation
import Maxwell.Continuum.CornerRoots
import Maxwell.Continuum.FiberReflectionGraph

/-! The literal scaled momentum chart and isolated energy disk used for the
periodic band. All disk inclusions are proved with fixed numerical margins. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber FiberAnalytic Metric Set

def chart : Set Momentum := {t | ∀ j, ‖t j‖ < ((2 : ℝ) ^ 12)⁻¹}

def energyDisk : Set ℂ := closedBall (Corner.lambdaStar : ℂ) (1 / 100)

theorem chart_isOpen : IsOpen chart := by
  have h : chart = ⋂ j : Fin 3, {t : Momentum | ‖t j‖ < ((2 : ℝ) ^ 12)⁻¹} := by
    ext t
    simp only [chart, mem_ofPred_eq, mem_iInter]
  rw [h]
  exact isOpen_iInter_of_finite (fun j => isOpen_lt (continuous_apply j).norm continuous_const)

theorem chart_zero : (0 : Momentum) ∈ chart := by
  intro j
  change ‖(0 : ℂ)‖ < ((2 : ℝ) ^ 12)⁻¹
  norm_num

theorem chart_closed_bounds {t : Momentum} (ht : t ∈ chart) :
    ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹ := fun j => (ht j).le

theorem chart_reflect {t : Momentum} (ht : t ∈ chart) (j : Fin 3) :
    FiberReflection.momentum j t ∈ chart := by
  intro k
  rw [FiberReflection.momentum_coordinate_norm]
  exact ht k

theorem chart_neg {t : Momentum} (ht : t ∈ chart) : -t ∈ chart := by
  intro j
  change ‖-t j‖ < ((2 : ℝ) ^ 12)⁻¹
  rw [norm_neg]
  exact ht j

theorem lambdaStar_le : Corner.lambdaStar ≤ 5 / 2 := by
  have h := Corner.sqrt_nineteen_bounds.2
  unfold Corner.lambdaStar
  linarith

theorem energy_norm_le {e : ℂ} (he : e ∈ energyDisk) : ‖e‖ ≤ 3 := by
  have hd : ‖e - (Corner.lambdaStar : ℂ)‖ ≤ 1 / 100 := by
    simpa only [energyDisk, mem_closedBall, dist_eq_norm] using he
  have hc : ‖(Corner.lambdaStar : ℂ)‖ ≤ 5 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Corner.lambdaStar_pos]
    exact lambdaStar_le
  have hsum := norm_add_le (e - (Corner.lambdaStar : ℂ)) (Corner.lambdaStar : ℂ)
  rw [sub_add_cancel] at hsum
  linarith

theorem energyDisk_subset_four : energyDisk ⊆ closedBall 0 4 := by
  intro e he
  rw [mem_closedBall, dist_zero_right]
  exact (energy_norm_le he).trans (by norm_num)

theorem chart_energy_inBox {t : Momentum} {e : ℂ}
    (ht : t ∈ chart) (he : e ∈ energyDisk) : InBox (t, e) :=
  ⟨chart_closed_bounds ht, (energy_norm_le he).trans (by norm_num)⟩

theorem chart_energy_analytic :
    AnalyticOnNhd ℂ PeriodicPerturbation.perturbation (chart ×ˢ energyDisk) :=
  fun z hz => PeriodicPerturbation.analyticAt_perturbation z (chart_energy_inBox hz.1 hz.2)

end Maxwell.Continuum.PeriodicBand
