import Maxwell.Continuum.FiberAnalyticSchur
import Maxwell.Continuum.CauchyBounds
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Actual finite periodic perturbation and its quantitative analytic bounds.
The energy dependence comes from the full infinite alias complement inverse. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.PeriodicPerturbation

open FreeFiber ClusterComplement FiberAnalytic Metric

local instance : NormSMulClass ℂ ClusterMap :=
  NormedSpace.toNormSMulClass (𝕜 := ℂ) (E := ClusterMap)
local instance : IsBoundedSMul ℂ ClusterMap :=
  NormedSpace.toIsBoundedSMul (𝕜 := ℂ) (E := ClusterMap)

def finiteK : ClusterMap := compressionCLM clusterPotential

def finiteVelocity (t : Momentum) : ClusterMap := compressionCLM (clusterVelocity t)

def perturbation (z : Parameter) : ClusterMap :=
  finiteVelocity z.1 + (backgroundAmplitude : ℂ) • finiteCorrectionExtension z

theorem analyticAt_perturbation (z : Parameter) (hz : InBox z) :
    AnalyticAt ℂ perturbation z := by
  have hv : AnalyticAt ℂ (fun w : Parameter => finiteVelocity w.1) z :=
    AnalyticAt.comp (f := fun w : Parameter => clusterVelocity w.1)
      (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := FiberMap) (F := ClusterMap)
        compressionCLM (clusterVelocity z.1)) (analyticAt_clusterVelocity z)
  exact hv.add ((analyticAt_const (v := (backgroundAmplitude : ℂ))).smul
    (analyticAt_finiteCorrectionExtension z hz))

theorem finiteCorrection_energy_analytic (t : Momentum)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) :
    AnalyticOnNhd ℂ (fun e => finiteCorrectionExtension (t, e)) (closedBall 0 8) := by
  intro e he
  have he' : ‖e‖ ≤ 8 := by simpa only [mem_closedBall, dist_zero_right] using he
  exact (analyticAt_finiteCorrectionExtension (t, e) ⟨ht, he'⟩).comp
    ((analyticAt_const (v := t)).prod analyticAt_id)

theorem finiteCorrection_energy_lipschitz (t : Momentum)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) :
    LipschitzOnWith 256 (fun e => finiteCorrectionExtension (t, e)) (closedBall 0 4) := by
  apply CauchyBounds.correction_lipschitz (finiteCorrection_energy_analytic t ht)
  intro e he
  exact finiteCorrectionExtension_norm_le_256 (t, e)
    ⟨ht, by simpa only [mem_closedBall, dist_zero_right] using he⟩

theorem finiteCorrection_energy_sub_le (t : Momentum)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (e d : ℂ)
    (he : ‖e‖ ≤ 4) (hd : ‖d‖ ≤ 4) :
    ‖finiteCorrectionExtension (t, e) - finiteCorrectionExtension (t, d)‖ ≤
      256 * ‖e - d‖ := by
  simpa only [dist_eq_norm, NNReal.coe_ofNat] using
    (finiteCorrection_energy_lipschitz t ht).dist_le_mul e
      (by simpa only [mem_closedBall, dist_zero_right] using he) d
      (by simpa only [mem_closedBall, dist_zero_right] using hd)

theorem velocityBlock_norm_le_box (t : Momentum)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (ν : CentralAlias) :
    ‖velocityBlock t ν.val‖ ≤ 3 / 1024 := by
  have hs (j : Fin 3) : ‖realMomentum (cornerSigns ν.val) j‖ = 1 := by
    rcases ν.property j with h | h <;> norm_num [realMomentum, cornerSigns, h]
  have hdot : ‖bilinearDot (realMomentum (cornerSigns ν.val)) t‖ ≤ 3 / 4096 := by
    calc
      _ ≤ ∑ j : Fin 3, ‖realMomentum (cornerSigns ν.val) j * t j‖ := norm_sum_le _ _
      _ = ∑ j : Fin 3, ‖t j‖ := by simp only [norm_mul, hs, one_mul]
      _ ≤ ∑ _ : Fin 3, ((2 : ℝ) ^ 12)⁻¹ := Finset.sum_le_sum (fun j _ => ht j)
      _ = 3 / 4096 := by norm_num
  rw [velocityBlock, norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  have hb := mul_le_mul (mul_le_mul_of_nonneg_left hdot Real.pi_pos.le)
    (clusterBlock_norm_le ν.val) (norm_nonneg _) (by positivity : 0 ≤ Real.pi * (3 / 4096))
  nlinarith [Real.pi_lt_four]

theorem finiteVelocity_norm_le (t : Momentum)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) : ‖finiteVelocity t‖ ≤ 3 / 1024 := by
  have hc : ‖clusterVelocity t‖ ≤ 3 / 1024 := by
    rw [clusterVelocity_eq_centralFamily]
    exact (centralFamilyMap_norm_le _).trans
      ((pi_norm_le_iff_of_nonneg (by norm_num)).mpr (velocityBlock_norm_le_box t ht))
  exact (compress_norm_le _).trans hc

theorem correction_scaled_norm_le (z : Parameter) (hz : InBox z) :
    ‖(backgroundAmplitude : ℂ) • finiteCorrectionExtension z‖ ≤ 256 * backgroundAmplitude := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos backgroundAmplitude_pos]
  exact (mul_le_mul_of_nonneg_left (finiteCorrectionExtension_norm_le_256 z hz)
    backgroundAmplitude_pos.le).trans_eq (by ring)

theorem perturbation_norm_le (z : Parameter) (hz : InBox z) :
    ‖perturbation z‖ ≤ 1 / 256 := by
  have h := (norm_add_le (finiteVelocity z.1)
    ((backgroundAmplitude : ℂ) • finiteCorrectionExtension z)).trans
      (add_le_add (finiteVelocity_norm_le z.1 hz.1) (correction_scaled_norm_le z hz))
  change ‖perturbation z‖ ≤ _ at h
  have hρ : 256 * backgroundAmplitude ≤ 1 / 1024 := by norm_num [backgroundAmplitude]
  linarith

theorem perturbation_energy_sub_le (t : Momentum)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (e d : ℂ)
    (he : ‖e‖ ≤ 4) (hd : ‖d‖ ≤ 4) :
    ‖perturbation (t, e) - perturbation (t, d)‖ ≤ (1 / 1024 : ℝ) * ‖e - d‖ := by
  have heq : perturbation (t, e) - perturbation (t, d) = (backgroundAmplitude : ℂ) •
      (finiteCorrectionExtension (t, e) - finiteCorrectionExtension (t, d)) := by
    calc
      _ = (backgroundAmplitude : ℂ) • finiteCorrectionExtension (t, e) -
          (backgroundAmplitude : ℂ) • finiteCorrectionExtension (t, d) := by
        unfold perturbation
        abel
      _ = _ := (smul_sub (backgroundAmplitude : ℂ)
        (finiteCorrectionExtension (t, e)) (finiteCorrectionExtension (t, d))).symm
  rw [heq, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos backgroundAmplitude_pos]
  have h := mul_le_mul_of_nonneg_left (finiteCorrection_energy_sub_le t ht e d he hd)
    backgroundAmplitude_pos.le
  have hρ : backgroundAmplitude * 256 ≤ 1 / 1024 := by norm_num [backgroundAmplitude]
  exact h.trans (by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hρ (norm_nonneg _))

theorem perturbation_energy_lipschitz (t : Momentum)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) :
    LipschitzOnWith (1 / 1024) (fun e => perturbation (t, e)) (closedBall 0 4) := by
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro e he d hd
  exact perturbation_energy_sub_le t ht e d
    (by simpa only [mem_closedBall, dist_zero_right] using he)
    (by simpa only [mem_closedBall, dist_zero_right] using hd)

theorem perturbation_sub_velocity (z : Parameter) :
    perturbation z - finiteVelocity z.1 = (backgroundAmplitude : ℂ) • finiteCorrectionExtension z := by
  exact add_sub_cancel_left (finiteVelocity z.1)
    ((backgroundAmplitude : ℂ) • finiteCorrectionExtension z)

theorem perturbation_sub_velocity_norm_le (z : Parameter) (hz : InBox z) :
    ‖perturbation z - finiteVelocity z.1‖ ≤ 256 * backgroundAmplitude := by
  rw [perturbation_sub_velocity]
  exact correction_scaled_norm_le z hz

theorem compression_projection : compressionCLM clusterProjection = 1 := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  change clusterProjection (clusterProjection u.val) = u.val
  rw [clusterProjection_idempotent]
  exact (mem_clusterSpace_iff u.val).mp u.property

theorem finiteSchurExtension_expansion (z : Parameter) :
    finiteSchurExtension z = finiteK + perturbation z - z.2 • (1 : ClusterMap) := by
  change compressionCLM (leadingCluster z.1 z.2 +
    (backgroundAmplitude : ℂ) • schurCorrectionExtension z) = _
  rw [map_add, map_smul, leadingCluster, map_sub, map_add, map_smul, compression_projection]
  change finiteK + finiteVelocity z.1 - z.2 • (1 : ClusterMap) +
    (backgroundAmplitude : ℂ) • finiteCorrectionExtension z = _
  simp only [perturbation]
  abel

end Maxwell.Continuum.PeriodicPerturbation
