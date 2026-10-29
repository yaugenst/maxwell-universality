import Maxwell.Continuum.AliasSeparation
import Maxwell.Continuum.EffectiveMassFiberVariation
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! Absolute convergence and a uniform bound for the actual off-diagonal
alias sum in the scaled well kernel. Both Fourier modes include all aliases. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.EffectiveMass

open FreeFiber PeriodicBand

theorem scaledFiber_fourier_l1 {h : ℝ} (hh : 0 ≤ h) (p : Space)
    (hp : h * ‖p‖ ≤ 4 * smallRadius) :
    Summable (fun ν => ‖scaledFiber h p ν‖) ∧
      ∑' ν, ‖scaledFiber h p ν‖ ≤ 32 := by
  apply FiberNormalization.normalizedFiberVector_fourier_l1
  apply unscale_mem_chart
  apply small_momentum_mem_physicalChart
  have hn := physicalMomentum_norm_le (h • p)
  rw [scaled_norm hh] at hn
  exact hn.trans hp

def aliasWeight (h : ℝ) (p p' : Space) (a : Alias × Alias) : ℝ :=
  ‖scaledFiber h p a.1‖ * ‖scaledFiber h p' a.2‖

theorem aliasWeight_sum {h : ℝ} (hh : 0 ≤ h) (p p' : Space)
    (hp : h * ‖p‖ ≤ 4 * smallRadius) (hp' : h * ‖p'‖ ≤ 4 * smallRadius) :
    Summable (aliasWeight h p p') ∧ ∑' a, aliasWeight h p p' a ≤ 1024 := by
  have hf := scaledFiber_fourier_l1 hh p hp
  have hg := scaledFiber_fourier_l1 hh p' hp'
  have hs := hf.1.mul_of_nonneg hg.1 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  refine ⟨hs, ?_⟩
  change ∑' a : Alias × Alias, ‖scaledFiber h p a.1‖ * ‖scaledFiber h p' a.2‖ ≤ _
  rw [← hf.1.tsum_mul_tsum hg.1 hs]
  have hm := mul_le_mul hf.2 hg.2 (tsum_nonneg fun _ => norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 32)
  norm_num at hm ⊢
  exact hm

def offAliasTerm (h : ℝ) (p p' : Space) (a : Alias × Alias) : ℂ :=
  if a.1 = a.2 then 0 else
    inner ℂ (scaledFiber h p a.1) (scaledFiber h p' a.2) *
      Well.physicalFourier Well.w (aliasTransfer h p p' a.1 a.2)

def offAliasKernel (h : ℝ) (p p' : Space) : ℂ :=
  ∑' a, offAliasTerm h p p' a

theorem offAliasTerm_bound {h : ℝ} (hh : 0 < h) (p p' : Space)
    (hp : h * ‖p‖ ≤ 4 * smallRadius) (hp' : h * ‖p'‖ ≤ 4 * smallRadius)
    (a : Alias × Alias) :
    ‖offAliasTerm h p p' a‖ ≤ aliasWeight h p p' a *
      ((2 : ℝ)^20 * Real.exp (-1 / (512 * Real.sqrt h))) := by
  unfold offAliasTerm
  split_ifs with ha
  · simp only [norm_zero]
    unfold aliasWeight
    positivity
  rw [norm_mul]
  exact mul_le_mul (norm_inner_le_norm _ _) (off_alias_fourier_bound hh p p' hp hp' ha)
    (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem offAliasTerm_summable {h : ℝ} (hh : 0 < h) (p p' : Space)
    (hp : h * ‖p‖ ≤ 4 * smallRadius) (hp' : h * ‖p'‖ ≤ 4 * smallRadius) :
    Summable (offAliasTerm h p p') :=
  ((aliasWeight_sum hh.le p p' hp hp').1.mul_right _).of_norm_bounded
    (offAliasTerm_bound hh p p' hp hp')

theorem offAliasKernel_bound {h : ℝ} (hh : 0 < h) (p p' : Space)
    (hp : h * ‖p‖ ≤ 4 * smallRadius) (hp' : h * ‖p'‖ ≤ 4 * smallRadius) :
    ‖offAliasKernel h p p'‖ ≤ (2 : ℝ)^30 * Real.exp (-1 / (512 * Real.sqrt h)) := by
  have hw := aliasWeight_sum hh.le p p' hp hp'
  have hm := tsum_of_norm_bounded
    (hw.1.hasSum.mul_right ((2 : ℝ)^20 * Real.exp (-1 / (512 * Real.sqrt h))))
    (offAliasTerm_bound hh p p' hp hp')
  change ‖offAliasKernel h p p'‖ ≤
    (∑' a, aliasWeight h p p' a) *
      ((2 : ℝ)^20 * Real.exp (-1 / (512 * Real.sqrt h))) at hm
  calc
    _ ≤ _ := hm
    _ ≤ 1024 * ((2 : ℝ)^20 * Real.exp (-1 / (512 * Real.sqrt h))) :=
      mul_le_mul_of_nonneg_right hw.2 (by positivity)
    _ = _ := by ring

end Maxwell.Continuum.EffectiveMass
