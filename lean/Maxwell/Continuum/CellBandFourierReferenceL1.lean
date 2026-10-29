import Maxwell.Continuum.CellBandFourierL1Sharp
import Maxwell.Continuum.CellBandFourierReferenceL2

/-! The selected actual zero-momentum state is close to the certified
eight-alias corner state in the genuine full Fourier ℓ¹ norm. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.CellBandFourier

open FreeFiber ClusterComplement FiberAnalytic PeriodicPerturbation CornerBridge
  PeriodicBand FiberNormalization

attribute [local irreducible] perturbation finiteK topState RankOneBand.Data.bandRoot
  scaledBand clusterVector fiberVector normalizedFiberVector

def referenceL1 : FiberL1.Space := FiberL1.clusterLift topState.val

def rawZeroL1 : FiberL1.Space :=
  FiberL1.schurLift 0 (scaledBand 0) (chart_closed_bounds chart_zero)
    (chart_energy_inBox chart_zero (scaledBand_mem chart_zero)).2 (clusterVector 0).val

def normalizedZeroL1 : FiberL1.Space := (‖fiberVector 0‖ : ℂ)⁻¹ • rawZeroL1

theorem inclusion_referenceL1 : FiberL1.inclusion referenceL1 = topState.val := by
  rw [referenceL1, FiberL1.inclusion_clusterLift]
  exact (mem_clusterSpace_iff _).mp topState.property

theorem inclusion_rawZeroL1 : FiberL1.inclusion rawZeroL1 = fiberVector 0 := by
  rw [rawZeroL1, FiberL1.inclusion_schurLift]
  exact (fiberVector_eq chart_zero).symm

theorem inclusion_normalizedZeroL1 :
    FiberL1.inclusion normalizedZeroL1 = normalizedFiberVector 0 := by
  rw [normalizedZeroL1, map_smul, inclusion_rawZeroL1, normalizedFiberVector_zero_eq]

theorem referenceL1_apply (ν : Alias) : referenceL1 ν = topState.val ν :=
  congrArg (fun u : FiberSpace => u ν) inclusion_referenceL1

theorem normalizedZeroL1_apply (ν : Alias) : normalizedZeroL1 ν = normalizedFiberVector 0 ν :=
  congrArg (fun u : FiberSpace => u ν) inclusion_normalizedZeroL1

theorem referenceL1_norm_le : ‖referenceL1‖ ≤ 3 := by
  have h := clusterLift_norm_le_three topState.val
  rw [(mem_clusterSpace_iff _).mp topState.property,
    show ‖topState.val‖ = 1 from topState_norm, mul_one] at h
  exact h

theorem rawZeroL1_sub_reference_bound :
    ‖rawZeroL1 - referenceL1‖ ≤ 30816 * backgroundAmplitude := by
  have hP := (mem_clusterSpace_iff _).mp (clusterVector 0).property
  have hT := (mem_clusterSpace_iff _).mp topState.property
  have hc := l1_schurLift_complement_bound 0 (scaledBand 0)
    (chart_closed_bounds chart_zero)
    (chart_energy_inBox chart_zero (scaledBand_mem chart_zero)).2 (clusterVector 0).val
  rw [hP] at hc
  change ‖rawZeroL1 - FiberL1.clusterLift (clusterVector 0).val‖ ≤
    48 * backgroundAmplitude * ‖clusterVector 0‖ at hc
  have hh := clusterLift_norm_le_three ((clusterVector 0).val - topState.val)
  simp only [map_sub, hP, hT] at hh
  change ‖FiberL1.clusterLift (clusterVector 0).val - referenceL1‖ ≤
    3 * ‖clusterVector 0 - topState‖ at hh
  have ht := norm_add_le (rawZeroL1 - FiberL1.clusterLift (clusterVector 0).val)
    (FiberL1.clusterLift (clusterVector 0).val - referenceL1)
  rw [sub_add_sub_cancel] at ht
  have hn := clusterVector_norm_le chart_zero
  have hs := clusterVector_zero_sub_top_bound
  have hc' : 48 * backgroundAmplitude * ‖clusterVector 0‖ ≤ 96 * backgroundAmplitude := by
    nlinarith [backgroundAmplitude_pos]
  linarith

theorem normalizedZeroL1_sub_reference_bound :
    ‖normalizedZeroL1 - referenceL1‖ ≤ 61632 * backgroundAmplitude := by
  have heq : normalizedZeroL1 - referenceL1 =
      (‖fiberVector 0‖ : ℂ)⁻¹ • (rawZeroL1 - referenceL1) +
      ((‖fiberVector 0‖ : ℂ)⁻¹ - 1) • referenceL1 := by
    simp only [normalizedZeroL1, smul_sub, sub_smul, one_smul]
    abel
  rw [heq]
  have h1 : ‖(‖fiberVector 0‖ : ℂ)⁻¹ • (rawZeroL1 - referenceL1)‖ ≤
      30816 * backgroundAmplitude := by
    rw [norm_smul]
    exact (mul_le_mul inverse_norm_zero_le rawZeroL1_sub_reference_bound
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have h2 : ‖((‖fiberVector 0‖ : ℂ)⁻¹ - 1) • referenceL1‖ ≤
      30816 * backgroundAmplitude := by
    rw [norm_smul]
    exact (mul_le_mul inverse_norm_zero_sub_one_bound referenceL1_norm_le
      (norm_nonneg _) (mul_nonneg (by norm_num) backgroundAmplitude_pos.le)).trans_eq (by ring)
  exact (norm_add_le _ _).trans (by linarith)

theorem normalizedFiberVector_zero_fourier_reference :
    Summable (fun ν => ‖normalizedFiberVector 0 ν - topState.val ν‖) ∧
      ∑' ν, ‖normalizedFiberVector 0 ν - topState.val ν‖ ≤ 2^16 * backgroundAmplitude := by
  have hs := FiberL1.summable_norm (normalizedZeroL1 - referenceL1)
  have heq (ν : Alias) : (normalizedZeroL1 - referenceL1) ν =
      normalizedFiberVector 0 ν - topState.val ν := by
    change normalizedZeroL1 ν - referenceL1 ν = _
    rw [normalizedZeroL1_apply, referenceL1_apply]
  simp only [heq] at hs
  refine ⟨hs, ?_⟩
  have hn := normalizedZeroL1_sub_reference_bound
  rw [FiberL1.norm_eq_tsum] at hn
  simp only [heq] at hn
  exact hn.trans (by nlinarith [backgroundAmplitude_pos])

#print axioms normalizedFiberVector_zero_fourier_reference

end Maxwell.Continuum.CellBandFourier
