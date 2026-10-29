import Maxwell.Continuum.BandWavePacketPhysical

/-! The actual bounded band-energy multiplier on local Bloch amplitudes.
The physical Maxwell graph intertwining is proved from the full fiber graph. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.BandWavePacket

open MeasureTheory FreeFiber FiberNormalization PeriodicBand Bloch

attribute [local irreducible] PeriodicPerturbation.perturbation PeriodicPerturbation.finiteK
  CornerBridge.topState RankOneBand.Data.bandRoot scaledBand clusterVector
  fiberVector normalizedFiberVector

def energyCore (q : QuasiCell) : ℂ := totalEnergy (scaledBand (parameter q)) - 7
def energyValue : QuasiCell → ℂ := region.indicator energyCore

theorem energyCore_eq (q : QuasiCell) : energyCore q = dielectricBand (quasiMomentum q) := rfl

theorem energyCore_continuousOn : ContinuousOn energyCore region := by
  have hb := scaledBand_analytic.continuousOn.comp parameter_continuous.continuousOn
    (show Set.MapsTo parameter region chart from fun _ hq => hq)
  exact (continuousOn_const.add (continuousOn_const.mul hb)).sub continuousOn_const

theorem energyValue_measurable : AEStronglyMeasurable energyValue quasiMeasure :=
  (aestronglyMeasurable_indicator_iff region_isOpen.measurableSet).mpr
    (energyCore_continuousOn.aestronglyMeasurable region_isOpen.measurableSet)

theorem energyCore_norm_le {q : QuasiCell} (hq : q ∈ region) : ‖energyCore q‖ ≤ 32 := by
  have he := scaledBand_norm_le hq
  have hρ := backgroundAmplitude_le
  have hρ0 := backgroundAmplitude_pos
  have hπ := Real.pi_lt_four
  have hπ0 := Real.pi_pos
  have ht := norm_add_le (((3 * Real.pi ^ 2 / 4 : ℝ) : ℂ))
    ((backgroundAmplitude : ℂ) * scaledBand (parameter q))
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs] at ht
  rw [abs_of_pos hρ0, abs_of_nonneg (by positivity : 0 ≤ 3 * Real.pi ^ 2 / 4)] at ht
  have hs := norm_sub_le (totalEnergy (scaledBand (parameter q))) (7 : ℂ)
  norm_num only [Complex.norm_ofNat] at hs
  change ‖energyCore q‖ ≤ ‖totalEnergy (scaledBand (parameter q))‖ + 7 at hs
  change ‖totalEnergy (scaledBand (parameter q))‖ ≤ _ at ht
  nlinarith

theorem energyValue_norm_le (q : QuasiCell) : ‖energyValue q‖ ≤ 32 := by
  by_cases hq : q ∈ region
  · rw [energyValue, Set.indicator_of_mem hq]
    exact energyCore_norm_le hq
  · rw [energyValue, Set.indicator_of_notMem hq, norm_zero]
    norm_num

theorem energyProduct_memLp (f : Amplitude) :
    MemLp (fun q => energyValue q * f.val q) 2 quasiMeasure := by
  apply (Lp.memLp f.val).of_le_mul (c := 32)
    (energyValue_measurable.mul (Lp.aestronglyMeasurable f.val))
  exact Filter.Eventually.of_forall fun q => by
    change ‖energyValue q * f.val q‖ ≤ 32 * ‖f.val q‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (energyValue_norm_le q) (norm_nonneg _)

def energyProduct (f : Amplitude) : Lp ℂ 2 quasiMeasure := (energyProduct_memLp f).toLp _

theorem energyProduct_ae (f : Amplitude) :
    energyProduct f =ᵐ[quasiMeasure] fun q => energyValue q * f.val q := MemLp.coeFn_toLp _

theorem energyProduct_supported (f : Amplitude) : energyProduct f ∈ amplitudes quasiMeasure region := by
  change ∀ᵐ q ∂quasiMeasure, q ∉ region → energyProduct f q = 0
  filter_upwards [energyProduct_ae f, f.property] with q he hf
  intro hq
  rw [he, hf hq, mul_zero]

def energyLinear : Amplitude →ₗ[ℂ] Amplitude where
  toFun f := ⟨energyProduct f, energyProduct_supported f⟩
  map_add' f g := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [energyProduct_ae (f+g), energyProduct_ae f, energyProduct_ae g,
      Lp.coeFn_add f.val g.val, Lp.coeFn_add (energyProduct f) (energyProduct g)] with q hfg hf hg ha hb
    change energyProduct (f+g) q = (energyProduct f + energyProduct g) q
    rw [hfg, hb]
    change energyValue q * (f.val + g.val) q = _
    rw [ha]
    simp only [Pi.add_apply, hf, hg, mul_add]
  map_smul' c f := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [energyProduct_ae (c • f), energyProduct_ae f,
      Lp.coeFn_smul c f.val, Lp.coeFn_smul c (energyProduct f)] with q hcf hf ha hb
    change energyProduct (c • f) q = (c • energyProduct f) q
    rw [hcf, hb]
    change energyValue q * (c • f.val) q = _
    rw [ha]
    simp only [Pi.smul_apply, hf, smul_eq_mul]
    ring

theorem energyProduct_norm_le (f : Amplitude) : ‖energyProduct f‖ ≤ 32 * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [energyProduct_ae f] with q hq
  rw [hq, norm_mul]
  exact mul_le_mul_of_nonneg_right (energyValue_norm_le q) (norm_nonneg _)

def energyOperator : Amplitude →L[ℂ] Amplitude :=
  energyLinear.mkContinuous 32 (fun f => by
    change ‖energyProduct f‖ ≤ 32 * ‖f‖
    exact energyProduct_norm_le f)

theorem energyOperator_ae (f : Amplitude) :
    (energyOperator f).val =ᵐ[quasiMeasure] fun q => energyValue q * f.val q := energyProduct_ae f

theorem sectionValue_energy_graph (q : QuasiCell) :
    (sectionValue q, energyValue q • sectionValue q) ∈
      (materialFiber (quasiMomentum q) 7 backgroundAmplitude).graph := by
  by_cases hq : q ∈ region
  · have h := material_graph_energy_shift (quasiMomentum q)
      (dielectricBand (quasiMomentum q) + 7) 7 backgroundAmplitude _ _ (sectionValue_graph hq)
    simpa only [zero_add, add_sub_cancel_right, energyValue, Set.indicator_of_mem hq,
      energyCore_eq] using h
  · rw [sectionValue_zero hq, smul_zero]
    exact Submodule.zero_mem _

theorem fiberEmbedding_energy_graph (f : Amplitude) :
    ∀ᵐ q ∂quasiMeasure, (fiberEmbedding f q, fiberEmbedding (energyOperator f) q) ∈
      (materialFiber (quasiMomentum q) 7 backgroundAmplitude).graph := by
  filter_upwards [fiberEmbedding_ae f, fiberEmbedding_ae (energyOperator f), energyOperator_ae f]
    with q hf he hm
  rw [hf, he, hm]
  have h := (materialFiber (quasiMomentum q) 7 backgroundAmplitude).graph.smul_mem
    (f.val q) (sectionValue_energy_graph q)
  have heq : (f.val q • sectionValue q, (energyValue q * f.val q) • sectionValue q) =
      f.val q • (sectionValue q, energyValue q • sectionValue q) := by
    apply Prod.ext
    · rfl
    · change (energyValue q * f.val q) • sectionValue q = f.val q • energyValue q • sectionValue q
      rw [smul_smul, mul_comm]
  rw [heq]
  exact h

theorem physicalEmbedding_intertwining (f : Amplitude) :
    WeakPeriodicEquation (physicalEmbedding f) (physicalEmbedding (energyOperator f)) := by
  rw [weakPeriodicEquation_iff_fiber_graph, unitary_physicalEmbedding, unitary_physicalEmbedding]
  exact fiberEmbedding_energy_graph f

#print axioms energyOperator
#print axioms physicalEmbedding_intertwining

end Maxwell.Continuum.BandWavePacket
